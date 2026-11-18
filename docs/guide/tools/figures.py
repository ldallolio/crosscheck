#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Draws the figures of the companion guide as SVG files in docs/guide/img/ (no external
package: plain SVG text).

    python3 docs/guide/tools/figures.py
"""
import math
import pathlib

OUT = pathlib.Path(__file__).resolve().parent.parent / "img"
W, H = 640, 400
L, R, T, B = 70, 30, 40, 60          # margins
COLORS = ["#1f6fb2", "#d1495b", "#2a9d5b", "#e0a100", "#7b4bb7", "#555555"]


def esc(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


class Plot:
    def __init__(self, xmin, xmax, ymin, ymax, title, xlabel, ylabel, w=W, h=H, legend_at="tr"):
        self.legend_at = legend_at
        self.x0, self.x1, self.y0, self.y1 = xmin, xmax, ymin, ymax
        self.w, self.h = w, h
        self.items = []
        self.title, self.xlabel, self.ylabel = title, xlabel, ylabel
        self.legend = []

    def X(self, x):
        return L + (x - self.x0) / (self.x1 - self.x0) * (self.w - L - R)

    def Y(self, y):
        return self.h - B - (y - self.y0) / (self.y1 - self.y0) * (self.h - T - B)

    def line(self, pts, color=0, width=2.2, dash=None, label=None, step=False):
        if step:
            q = []
            for k, (x, y) in enumerate(pts):
                if k:
                    q.append((x, pts[k - 1][1]))
                q.append((x, y))
            pts = q
        d = " ".join(f"{'M' if k == 0 else 'L'}{self.X(x):.1f},{self.Y(y):.1f}" for k, (x, y) in enumerate(pts))
        da = f' stroke-dasharray="{dash}"' if dash else ""
        self.items.append(f'<path d="{d}" fill="none" stroke="{COLORS[color]}" stroke-width="{width}"{da}/>')
        if label:
            self.legend.append((label, color, dash))

    def dots(self, pts, color=0, r=3.5, label=None):
        for x, y in pts:
            self.items.append(f'<circle cx="{self.X(x):.1f}" cy="{self.Y(y):.1f}" r="{r}" fill="{COLORS[color]}"/>')
        if label:
            self.legend.append((label, color, "dot"))

    def text(self, x, y, s, color=5, size=13, anchor="start"):
        self.items.append(f'<text x="{self.X(x):.1f}" y="{self.Y(y):.1f}" font-size="{size}" '
                          f'fill="{COLORS[color]}" text-anchor="{anchor}">{esc(s)}</text>')

    def poly(self, pts, color=0, opacity=0.18):
        d = " ".join(f"{self.X(x):.1f},{self.Y(y):.1f}" for x, y in pts)
        self.items.append(f'<polygon points="{d}" fill="{COLORS[color]}" fill-opacity="{opacity}" stroke="none"/>')

    def hband(self, y0, y1, color=1, opacity=0.08):
        self.poly([(self.x0, y0), (self.x1, y0), (self.x1, y1), (self.x0, y1)], color, opacity)

    def arrow(self, x0, y0, x1, y1, color=5):
        self.items.append(f'<line x1="{self.X(x0):.1f}" y1="{self.Y(y0):.1f}" x2="{self.X(x1):.1f}" '
                          f'y2="{self.Y(y1):.1f}" stroke="{COLORS[color]}" stroke-width="1.6" marker-end="url(#ah)"/>')

    def svg(self, xticks, yticks):
        o = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {self.w} {self.h}" '
             f'font-family="Helvetica, Arial, sans-serif">',
             '<defs><marker id="ah" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto">'
             '<path d="M0,0 L8,4 L0,8 z" fill="#555"/></marker></defs>',
             f'<rect width="{self.w}" height="{self.h}" fill="white"/>',
             f'<text x="{self.w / 2}" y="24" font-size="16" text-anchor="middle" font-weight="bold">{esc(self.title)}</text>']
        # grid and ticks
        for x in xticks:
            o.append(f'<line x1="{self.X(x):.1f}" y1="{self.Y(self.y0):.1f}" x2="{self.X(x):.1f}" '
                     f'y2="{self.Y(self.y1):.1f}" stroke="#eee"/>')
            o.append(f'<text x="{self.X(x):.1f}" y="{self.h - B + 18}" font-size="12" text-anchor="middle">{x:g}</text>')
        for y in yticks:
            o.append(f'<line x1="{self.X(self.x0):.1f}" y1="{self.Y(y):.1f}" x2="{self.X(self.x1):.1f}" '
                     f'y2="{self.Y(y):.1f}" stroke="#eee"/>')
            o.append(f'<text x="{L - 8}" y="{self.Y(y) + 4:.1f}" font-size="12" text-anchor="end">{y:g}</text>')
        o.append(f'<line x1="{L}" y1="{self.Y(self.y0):.1f}" x2="{self.w - R}" y2="{self.Y(self.y0):.1f}" stroke="#333"/>')
        o.append(f'<line x1="{L}" y1="{T}" x2="{L}" y2="{self.h - B}" stroke="#333"/>')
        o.append(f'<text x="{(L + self.w - R) / 2}" y="{self.h - 16}" font-size="13" text-anchor="middle">{esc(self.xlabel)}</text>')
        o.append(f'<text x="16" y="{(T + self.h - B) / 2}" font-size="13" text-anchor="middle" '
                 f'transform="rotate(-90 16 {(T + self.h - B) / 2})">{esc(self.ylabel)}</text>')
        o += self.items
        # legend
        lx = {"tr": self.w - R - 250, "tl": L + 12, "br": self.w - R - 250, "bl": L + 12}[self.legend_at]
        ly = T + 10 if self.legend_at[0] == "t" else self.h - B - 12 - 18 * len(self.legend)
        if self.legend:
            o.append(f'<rect x="{lx - 6}" y="{ly - 12}" width="250" height="{18 * len(self.legend) + 6}" '
                     f'fill="white" fill-opacity="0.85" stroke="#ccc"/>')
        for label, c, dash in self.legend:
            if dash == "dot":
                o.append(f'<circle cx="{lx + 10}" cy="{ly}" r="4" fill="{COLORS[c]}"/>')
            else:
                da = f' stroke-dasharray="{dash}"' if dash else ""
                o.append(f'<line x1="{lx}" y1="{ly}" x2="{lx + 24}" y2="{ly}" '
                         f'stroke="{COLORS[c]}" stroke-width="2.5"{da}/>')
            o.append(f'<text x="{lx + 30}" y="{ly + 4}" font-size="12">{esc(label)}</text>')
            ly += 18
        o.append("</svg>")
        return "\n".join(o)


def save(name, s):
    OUT.mkdir(exist_ok=True)
    (OUT / name).write_text(s + "\n")


def countdown():
    """for (i = 0; i < 10; i++): the potential V = 10 − i along the run."""
    p = Plot(0, 11, -1, 11, "Potential V = 10 − i along a run of  for (i = 0; i < 10; i++)",
             "iterations done so far", "value of V before the test", legend_at="tr")
    p.hband(-1, 0.999, 1, 0.07)
    p.text(0.3, 0.2, "V < 1: the loop test fails, the loop has stopped", 1, 12)
    pts = [(k, 10 - k) for k in range(11)]
    p.line(pts, 0, label="V = 10 − i (drops by 1 per iteration)", step=True)
    p.dots(pts, 0)
    p.line([(0, 10), (11, 10)], 2, 1.6, "6,4", label="V at the start: the bound K = 10")
    p.text(0.4, 4.2, "each iteration: V decreases by at least 1", 5, 12)
    p.text(0.4, 3.4, "while the loop runs: V ≥ 1", 5, 12)
    p.text(0.4, 2.6, "so at most 10 iterations", 5, 12)
    save("potential-countdown.svg", p.svg(range(0, 12), range(0, 11, 2)))


def uneven():
    """A body that sometimes makes a big step: the potential only needs to drop by at least 1."""
    p = Plot(0, 8, -1, 21, "A data-dependent body: V = n − i drops by 1 or by 3",
             "iterations done so far", "value of V = 20 − i")
    p.hband(-1, 0.999, 1, 0.07)
    seq = [20, 19, 16, 15, 12, 9, 8, 5, 4]
    pts = [(k, v) for k, v in enumerate(seq)]
    p.line(pts, 0, label="an actual run (steps of 1 or 3)", step=True)
    p.dots(pts, 0)
    worst = [(k, 20 - k) for k in range(9)]
    p.line(worst, 1, 1.8, "6,4", label="worst case assumed: drop of exactly 1")
    p.text(0.3, 1.2, "bound: V(start) = 20 iterations at most; this run stops earlier", 5, 12)
    save("potential-uneven.svg", p.svg(range(0, 9), range(0, 21, 5)))


def dominance():
    """Exact cost of a triangular nest vs the product bound vs the amortised bound."""
    p = Plot(0, 20, 0, 420, "Cost envelopes for  for i < n: for j < i: body",
             "n (size of the input)", "number of inner iterations", legend_at="tl")
    exact = [(n, n * (n - 1) / 2) for n in range(0, 21)]
    p.dots(exact, 0, 3, label="exact count n(n−1)/2")
    p.line([(n, n * n) for n in range(0, 21)], 1, 2.2, label="product bound n·n (timing schema)")
    p.line([(n, n * (n - 1) / 2) for n in range(0, 21)], 2, 1.8, "6,4", label="amortised bound Σ i (summation)")
    p.line([(n, 5 * n) for n in range(0, 21)], 3, 1.6, "2,4", label="a linear guess 5·n: NOT a bound")
    p.text(11.3, 40, "5·n falls below the dots from n = 12", 3, 12)
    p.text(12.5, 300, "an envelope must stay above", 5, 12)
    p.text(12.5, 282, "every dot (soundness)", 5, 12)
    save("dominance.svg", p.svg(range(0, 21, 2), range(0, 421, 50)))


def logpot():
    """while (x > 0) x /= 2 : x and the logarithmic potential."""
    p = Plot(0, 11, 0, 1100, "Halving loop  while (x > 0) x = x / 2  from x = 1000",
             "iterations done so far", "value of x")
    xs = [1000]
    while xs[-1] > 0:
        xs.append(xs[-1] // 2)
    pts = list(enumerate(xs))
    p.line(pts, 0, label="x along the run (halves each time)", step=True)
    p.dots(pts, 0)
    p.text(3.5, 760, "an affine potential (x itself, dropping by ≥ 1)", 1, 12)
    p.text(3.5, 710, "proves only 1000 iterations;", 1, 12)
    p.text(3.5, 620, "the logarithmic potential floor(log2 x) + 1", 0, 12)
    p.text(3.5, 570, "drops by 1 per iteration: 10 iterations", 0, 12)
    save("log-potential.svg", p.svg(range(0, 12), range(0, 1101, 200)))


def farkas():
    """Two premises and a goal: x ≤ 10, y − x ≤ 0 imply y ≤ 10 (1·first + 1·second)."""
    p = Plot(-2, 14, -2, 14, "Farkas: from  x ≤ 10  and  y ≤ x,  derive  y ≤ 10",
             "x", "y", legend_at="tl")
    p.poly([(-2, -2), (10, -2), (10, 10), (-2, -2)], 0, 0.20)
    p.line([(10, -2), (10, 14)], 0, 2, label="premise 1:  x − 10 ≤ 0")
    p.line([(-2, -2), (14, 14)], 2, 2, label="premise 2:  y − x ≤ 0")
    p.line([(-2, 10), (14, 10)], 1, 2, "6,4", label="goal:  y − 10 ≤ 0")
    p.text(4.0, 2.5, "states allowed by", 0, 12)
    p.text(4.0, 1.7, "both premises", 0, 12)
    p.text(10.4, 6.5, "1·(x − 10) + 1·(y − x)", 5, 12)
    p.text(10.4, 5.7, "= y − 10 ≤ 0", 5, 12)
    save("farkas.svg", p.svg(range(-2, 15, 2), range(-2, 15, 2)))


def intervals():
    """Calling contexts: argument intervals at three call sites and their hull."""
    p = Plot(0, 110, 0, 5, "Calling context of f(n): the interval of n over all calls",
             "value of the argument n", "")
    for k, (a, b, lab) in enumerate([(4, 10, "call 1: f(k), 4 ≤ k ≤ 10"),
                                    (16, 16, "call 2: f(16)"),
                                    (0, 8, "call 3: f(m), 0 ≤ m < 9")]):
        y = 4 - k * 0.8
        p.line([(a, y), (b + 0.3, y)], k, 7)
        p.text(b + 2, y - 0.08, lab, k, 12)
    p.line([(0, 1.0), (16.3, 1.0)], 4, 9)
    p.text(18, 0.92, "hull: 0 ≤ n ≤ 16, the context in which f is bounded", 4, 12)
    p.text(30, 0.3, "(without context, n ranges over all ints: no bound)", 5, 12)
    save("intervals.svg", p.svg(range(0, 111, 10), []))


def widening():
    """Abstract interpretation of i = 0; while (i < 10) i++: the interval of i at the head."""
    p = Plot(0, 7, -1, 14, "Interval of i at the loop head, iteration by iteration",
             "round of the analysis", "interval [low, high] of i")
    rounds = [(0, 0, 0.15), (1, 0, 1), (2, 0, 2), (3, 0, 14), (4, 0, 10), (5, 0, 10)]
    for k, lo_, hi_ in rounds:
        p.line([(k, lo_), (k, hi_)], 0 if k != 3 else 1, 8)
    p.text(3, 13.3, "+∞", 1, 14, "middle")
    p.text(0.2, 2.6, "0, 1, 2: grows by one", 5, 12)
    p.text(3.15, 12.2, "3: widening jumps to +∞", 1, 12)
    p.text(3.15, 11.4, "(or to the next threshold)", 1, 12)
    p.text(4.15, 10.6, "4-5: narrowing with the test", 2, 12)
    p.text(4.15, 9.8, "i < 10 gives back [0, 10]", 2, 12)
    save("widening.svg", p.svg(range(0, 7), range(0, 15, 2)))


def telescoping():
    """IPET dual: potentials on the nodes of a loop graph; each edge pays its cost."""
    p = Plot(0, 7, 0, 75, "Potentials of a cycle certificate (scale D = 1)",
             "instruction (in execution order)", "potential π", legend_at="tr")
    pts = [(0, 68), (1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 0)]
    p.dots(pts, 0, 5, label="potential of each instruction")
    for (x, y), lab in zip(pts, ["entry 68", "cmp 7", "bge 6", "adds 5", "b 4", "bx 3", "exit 0"]):
        p.text(x + 0.1, y + 2, lab, 0, 11)
    p.text(1.2, 42, "edge u→v accepted if  cost(e) + π(v) − π(u) ≤ multiplier terms", 5, 12)
    p.text(1.2, 36, "the back edge borrows 6 cycles from the loop row (multiplier 6)", 5, 12)
    p.text(1.2, 30, "summing along any run: cost ≤ π(entry) − π(exit) = 68", 5, 12)
    save("telescoping.svg", p.svg(range(0, 7), range(0, 76, 10)))


def wcet_distribution():
    """Measured execution times, the true worst case, and a guaranteed bound."""
    import random
    rnd = random.Random(3)
    p = Plot(0, 130, 0, 60, "Execution times of one function, and its bounds",
             "execution time (µs)", "number of runs", legend_at="tr")
    bins = {}
    for _ in range(600):
        t = min(max(rnd.gauss(45, 9), 20), 78)
        b = int(t // 3) * 3
        bins[b] = bins.get(b, 0) + 1
    top = max(bins.values())
    for b, n in sorted(bins.items()):
        h = n * 45 / top
        p.poly([(b, 0), (b + 2.6, 0), (b + 2.6, h), (b, h)], 0, 0.55)
    mx = max(bins) + 3
    p.line([(mx, 0), (mx, 52)], 2, 2, "4,3", label=f"largest measured time ({mx})")
    p.line([(96, 0), (96, 52)], 1, 2.2, label="true worst case (unknown, 96)")
    p.line([(112, 0), (112, 52)], 4, 2.6, label="guaranteed upper bound (112)")
    p.text(18, 49, "measured runs (tests)", 0, 12)
    p.text(mx + 2, 30, "never observed", 1, 12)
    p.text(98, 20, "safety margin", 4, 12)
    save("wcet-distribution.svg", p.svg(range(0, 131, 10), range(0, 61, 10)))


if __name__ == "__main__":
    countdown()
    uneven()
    dominance()
    logpot()
    farkas()
    intervals()
    widening()
    telescoping()
    wcet_distribution()
    print("figures written to", OUT)
