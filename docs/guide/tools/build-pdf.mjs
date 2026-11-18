// Builds the companion guide (docs/guide/*.md) into a single PDF.
//
//   cd docs/guide/tools && npm install && node build-pdf.mjs [--format=ebook|a4] [--chrome=/path/to/chrome]
//
// Markdown is converted with markdown-it, Mermaid diagrams are rendered by Mermaid in
// headless Chrome, and Chrome prints the result. Links between the guide's files become
// links inside the PDF, and the PDF gets a clickable outline (bookmarks).
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import MarkdownIt from 'markdown-it';
import GithubSlugger from 'github-slugger';
import puppeteer from 'puppeteer-core';
import { PDFDocument, PDFName, PDFDict, PDFHexString } from 'pdf-lib';

const here = path.dirname(fileURLToPath(import.meta.url));
const guideDir = path.resolve(here, '..');
const args = Object.fromEntries(process.argv.slice(2).map((a) => {
  const [k, v] = a.replace(/^--/, '').split('=');
  return [k, v ?? true];
}));
const format = args.format ?? 'ebook';
const chrome = args.chrome ?? ['/usr/bin/google-chrome', '/usr/bin/chromium', '/usr/bin/chromium-browser']
  .find((p) => fs.existsSync(p));
if (!chrome) throw new Error('No Chrome/Chromium found; pass --chrome=/path/to/chrome');

// Page geometry. "ebook" is a 3:4 page that e-ink readers (6"-8") display without
// zooming; "a4" is for printing.
const pages = {
  ebook: { width: '100mm', height: '133mm', margin: '5mm', font: '9.6pt', small: '7.6pt', code: '7.2pt' },
  a4: { width: '210mm', height: '297mm', margin: '16mm', font: '10.5pt', small: '9pt', code: '8.5pt' },
};
const page = pages[format];
if (!page) throw new Error(`unknown format ${format}`);
// Printable area (the bottom margin is 4 mm taller, for the page number).
const mm = (v) => parseFloat(v);
const contentWmm = mm(page.width) - 2 * mm(page.margin);
const contentHmm = mm(page.height) - 2 * mm(page.margin) - 5;
const contentW = `${contentWmm}mm`;
const contentH = `${contentHmm}mm`;

const files = fs.readdirSync(guideDir).filter((f) => /^\d\d-.*\.md$/.test(f)).sort();
const order = ['README.md', ...files];
const idOf = (file) => (file === 'README.md' ? 'f00' : `f${file.slice(0, 2)}`);

const md = new MarkdownIt({ html: false, linkify: false, typographer: false });

// Fenced ```mermaid blocks become <pre class="mermaid"> for Mermaid to render.
const defaultFence = md.renderer.rules.fence;
md.renderer.rules.fence = (tokens, idx, options, env, self) => {
  const t = tokens[idx];
  if (t.info.trim() === 'mermaid') return `<pre class="mermaid">${md.utils.escapeHtml(t.content)}</pre>\n`;
  // One block per source line, with a hanging indent: on a narrow page a wrapped line
  // continues indented instead of looking like a new line.
  const lines = t.content.replace(/\n$/, '').split('\n')
    .map((l) => `<span class="ln">${l ? md.utils.escapeHtml(l) : '&#8203;'}</span>`).join('');
  return `<pre class="code"><code>${lines}</code></pre>\n`;
};

// Images: the guide writes "img/x.svg"; the HTML is written in tools/, one level down.
const defaultImage = md.renderer.rules.image;
md.renderer.rules.image = (tokens, idx, options, env, self) => {
  const t = tokens[idx];
  const src = t.attrGet('src');
  if (src && src.startsWith('img/')) t.attrSet('src', '../' + src);
  t.attrSet('style', 'max-width:100%');
  return defaultImage(tokens, idx, options, env, self);
};

// Inline code: allow line breaks after _ . / , :: so that long identifiers in narrow
// table columns break at sensible places instead of letter by letter.
md.renderer.rules.code_inline = (tokens, idx) => {
  const esc = md.utils.escapeHtml(tokens[idx].content);
  return `<code>${esc.replace(/([_./,]|::)(?=\S)/g, '$1<wbr>')}</code>`;
};

// Heading ids: GitHub-style slugs, prefixed per file so that they are unique.
md.core.ruler.push('ids', (state) => {
  const { prefix, slugger } = state.env;
  for (let i = 0; i < state.tokens.length; i++) {
    const t = state.tokens[i];
    if (t.type !== 'heading_open') continue;
    const text = state.tokens[i + 1].children.filter((c) => c.type === 'text' || c.type === 'code_inline')
      .map((c) => c.content).join('');
    t.attrSet('id', `${prefix}-${slugger.slug(text)}`);
    headingTitles.push(text);
  }
});

// Links: "#x" -> "#fNN-x", "0N-file.md#x" -> "#f0N-x", "0N-file.md" -> "#f0N".
md.core.ruler.push('links', (state) => {
  const { prefix } = state.env;
  const walk = (tokens) => {
    for (const t of tokens) {
      if (t.children) walk(t.children);
      if (t.type !== 'link_open') continue;
      const href = t.attrGet('href') ?? '';
      let m;
      if (href.startsWith('#')) t.attrSet('href', `#${prefix}-${href.slice(1)}`);
      else if ((m = href.match(/^(\d\d-[\w-]+\.md|README\.md)(#(.*))?$/)))
        t.attrSet('href', m[3] ? `#${idOf(m[1])}-${m[3]}` : `#${idOf(m[1])}`);
    }
  };
  walk(state.tokens);
});

const headingTitles = ['CrossCheck', 'Contents'];
let body = '';
for (const file of order) {
  const src = fs.readFileSync(path.join(guideDir, file), 'utf8');
  const prefix = idOf(file);
  const html = md.render(src, { prefix, slugger: new GithubSlugger() });
  body += `<section class="part" id="${prefix}">${html}</section>\n`;
}

const date = new Date().toISOString().slice(0, 10);
const mermaidJs = pathToFileURL(path.join(here, 'node_modules/mermaid/dist/mermaid.min.js')).href;
const htmlDoc = `<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<title>CrossCheck — Companion Guide</title>
<style>
  @page { size: ${page.width} ${page.height}; margin: ${page.margin} ${page.margin} calc(${page.margin} + 4mm) ${page.margin}; }
  html { font-family: "DejaVu Serif", "STIX Two Text", "STIX", serif; font-size: ${page.font};
         line-height: 1.38; color: #000; background: #fff; }
  body { margin: 0; }
  h1, h2, h3, h4 { font-family: "DejaVu Sans", sans-serif; line-height: 1.2; break-after: avoid; }
  h1 { font-size: 1.55em; margin: 0 0 .6em; }
  h2 { font-size: 1.22em; margin: 1.2em 0 .4em; border-bottom: .4pt solid #555; padding-bottom: .1em; }
  h3 { font-size: 1.06em; margin: 1em 0 .3em; }
  h4 { font-size: 1em; margin: .8em 0 .2em; }
  p, li { orphans: 2; widows: 2; }
  ul, ol { padding-left: 1.3em; }
  a { color: #000; text-decoration: underline; text-decoration-thickness: .3pt; }
  code, pre { font-family: "DejaVu Sans Mono", "Noto Sans Mono", monospace; }
  code { font-size: .86em; overflow-wrap: break-word; }
  pre { font-size: ${page.code}; line-height: 1.3; white-space: pre-wrap; overflow-wrap: anywhere;
        border: .4pt solid #888; background: #f3f3f3; padding: .4em .5em; break-inside: auto; }
  pre.code .ln { display: block; padding-left: 2.2em; text-indent: -2.2em; }
  pre code { font-size: 1em; }
  blockquote { margin: .6em 0; padding: .2em .7em; border-left: 2pt solid #444; background: #f3f3f3; }
  table { border-collapse: collapse; width: 100%; font-size: ${page.small}; line-height: 1.25; margin: .5em 0; }
  th, td { border: .4pt solid #777; padding: .15em .3em; vertical-align: top; text-align: left;
           overflow-wrap: break-word; hyphens: manual; }
  th { background: #e4e4e4; }
  tr { break-inside: avoid; }
  pre.mermaid { background: none; border: none; padding: 0; text-align: center; break-inside: avoid; }
  pre.mermaid svg { max-width: 100% !important; height: auto; max-height: calc(${page.height} - 3 * ${page.margin} - 8mm); }
  .part { break-before: page; }
  /* Wide diagrams get a page of their own, rotated to landscape. */
  .landscape { width: ${contentW}; height: ${contentH}; break-before: page; break-after: page;
               position: relative; overflow: hidden; }
  .landscape > .rot { position: absolute; top: 0; left: 0; width: ${contentH}; height: ${contentW};
               transform-origin: top left; transform: translateX(${contentW}) rotate(90deg);
               display: flex; align-items: center; justify-content: center; }
  .landscape svg, .fullpage svg { max-width: 100% !important; max-height: 100% !important; width: 100%; height: 100%; }
  .fullpage { width: ${contentW}; height: ${contentH}; break-before: page; break-after: page;
              display: flex; align-items: center; justify-content: center; }
  .cover { break-after: page; display: flex; flex-direction: column; justify-content: center;
           min-height: calc(${page.height} - 3 * ${page.margin} - 6mm); text-align: center; }
  .cover h1 { font-size: 1.9em; border: none; }
  .cover p { margin: .3em 0; }
  .toc { break-before: page; }
  .toc ol { list-style: none; padding: 0; }
  .toc li { margin: .45em 0; }
</style></head><body>
<div class="cover">
  <h1>CrossCheck</h1>
  <p style="font-size:1.25em">Companion Guide</p>
  <p>Concepts, paper walkthrough, bibliography, Clang plugin, Lean&nbsp;4</p>
  <p style="margin-top:2em;font-size:.85em">Built ${date} from <code>docs/guide/</code>.<br>
  Written with an AI assistant; see <code>AI_USAGE.md</code>.<br>
  Summaries of cited papers come from the model's general knowledge (Part 3).</p>
</div>
<nav class="toc"><h1>Contents</h1><ol>
${order.map((f) => {
  const title = (fs.readFileSync(path.join(guideDir, f), 'utf8').match(/^# (.+)$/m) ?? [, f])[1];
  return `<li><a href="#${idOf(f)}">${md.utils.escapeHtml(title)}</a></li>`;
}).join('\n')}
</ol></nav>
${body}
<script src="${mermaidJs}"></script>
</body></html>`;

const htmlPath = path.join(here, 'guide.html');
fs.writeFileSync(htmlPath, htmlDoc);

const browser = await puppeteer.launch({ executablePath: chrome, headless: true,
  args: ['--allow-file-access-from-files', '--no-sandbox'] });
try {
  const tab = await browser.newPage();
  await tab.goto(pathToFileURL(htmlPath).href, { waitUntil: 'load' });
  const failures = await tab.evaluate(async (W, H) => {
    // eslint-disable-next-line no-undef
    mermaid.initialize({ startOnLoad: false, theme: 'neutral', securityLevel: 'loose',
      flowchart: { useMaxWidth: true, htmlLabels: true }, sequence: { useMaxWidth: true },
      class: { useMaxWidth: true }, state: { useMaxWidth: true } });
    let bad = 0;
    // eslint-disable-next-line no-undef
    try { await mermaid.run({ querySelector: 'pre.mermaid' }); } catch (e) { bad++; }
    const failed = document.querySelectorAll('pre.mermaid:not([data-processed])').length;
    // Large diagrams get a page of their own, in the orientation that makes them biggest
    // (W x H is the printable area in mm; 1 mm is about 3.78 CSS px).
    for (const pre of document.querySelectorAll('pre.mermaid')) {
      const svg = pre.querySelector('svg');
      const vb = svg && svg.viewBox && svg.viewBox.baseVal;
      if (!vb) continue;
      const inline = Math.min(W * 3.78 / vb.width, 1);          // scale when left inline
      const portrait = Math.min(W / vb.width, H / vb.height);
      const landscape = Math.min(H / vb.width, W / vb.height);
      if (inline * 3.78 >= 0.75 * portrait * 3.78 && vb.height < H * 3.78 * 0.6) continue;
      const box = document.createElement('div');
      svg.removeAttribute('style');
      if (landscape > portrait * 1.1) {
        box.className = 'landscape';
        const rot = document.createElement('div');
        rot.className = 'rot';
        rot.appendChild(svg);
        box.appendChild(rot);
      } else {
        box.className = 'fullpage';
        box.appendChild(svg);
      }
      pre.replaceWith(box);
    }
    return bad + failed;
  }, contentWmm, contentHmm);
  if (failures) throw new Error(`${failures} Mermaid diagram(s) failed to render`);
  await tab.evaluateHandle('document.fonts.ready');
  const out = path.join(guideDir, `crosscheck-guide-${format}.pdf`);
  await tab.pdf({
    path: out, width: page.width, height: page.height, printBackground: true,
    preferCSSPageSize: true, outline: true, tagged: true,
    displayHeaderFooter: true, headerTemplate: '<span></span>',
    footerTemplate: `<div style="width:100%;text-align:center;font-size:6.5pt;font-family:DejaVu Sans,sans-serif;color:#444"><span class="pageNumber"></span> / <span class="totalPages"></span></div>`,
  });
  await fixOutline(out);
  console.log(`wrote ${out}`);
} finally {
  await browser.close();
}

// Chrome builds the bookmarks from the laid-out headings and drops the space where a
// heading wraps ("fromzero"). Replace each bookmark title by the heading text it comes
// from, matched while ignoring whitespace.
async function fixOutline(file) {
  const squash = (t) => t.replace(/\s+/g, '');
  const byKey = new Map(headingTitles.map((t) => [squash(t), t]));
  const doc = await PDFDocument.load(fs.readFileSync(file));
  const outlines = doc.catalog.lookupMaybe(PDFName.of('Outlines'), PDFDict);
  if (!outlines) return;
  let fixed = 0;
  const visit = (ref) => {
    while (ref) {
      const item = doc.context.lookup(ref, PDFDict);
      const title = item.lookup(PDFName.of('Title'));
      if (title && title.decodeText) {
        const good = byKey.get(squash(title.decodeText()));
        if (good && good !== title.decodeText()) {
          item.set(PDFName.of('Title'), PDFHexString.fromText(good));
          fixed++;
        }
      }
      visit(item.get(PDFName.of('First')));
      ref = item.get(PDFName.of('Next'));
    }
  };
  visit(outlines.get(PDFName.of('First')));
  fs.writeFileSync(file, await doc.save());
  console.log(`bookmark titles fixed: ${fixed}`);
}
