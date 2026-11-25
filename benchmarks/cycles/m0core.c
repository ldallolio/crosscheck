/* Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
 *
 * The interpreter of m0.py (`Machine.call`, `Machine.execute`) in C, for long runs. It is
 * not a second specification: m0.py decodes the code (`m0.decode`, its table is given here
 * as arrays), and every instruction this file does not execute exactly as `execute` does
 * (a call of a function without code, an access outside the memory, an instruction that
 * reads or writes the PC through ADD/MOV/BX, an unknown or stopping instruction) is handed
 * back to m0.py before any state changes (status FALLBACK), which executes it and resumes.
 * The observations of run_cycles.py during a run (the cycles of each call, the lowest
 * stack pointer of each activation, the back edges of each loop against its bound) are
 * made here too (`mon_step`, the same rules as `m0.Watch.step`). Registers are 32 bits.
 * test_m0core.py compares the two interpreters instruction by instruction and on whole
 * runs; run_qemu.py compares m0.py with QEMU.
 *
 *     cc -O2 -shared -fPIC m0core.c -o m0core.so        (m0.py builds it when needed)
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* operations, in the order of `m0_op_names` (m0.py maps the names of m0.decode to these) */
enum {
    OP_FALLBACK, OP_LSLI, OP_LSRI, OP_ASRI, OP_ADDR, OP_SUBR, OP_ADDI3, OP_SUBI3, OP_MOVI,
    OP_CMPI, OP_ADDI8, OP_SUBI8, OP_AND, OP_EOR, OP_LSLR, OP_LSRR, OP_ASRR, OP_ADC, OP_SBC,
    OP_ROR, OP_TST, OP_NEG, OP_CMP, OP_CMN, OP_ORR, OP_MUL, OP_BIC, OP_MVN, OP_ADDHI,
    OP_CMPHI, OP_MOVHI, OP_LDRLIT, OP_STRR, OP_STRHR, OP_STRBR, OP_LDRSBR, OP_LDRR, OP_LDRHR,
    OP_LDRBR, OP_LDRSHR, OP_STRI, OP_LDRI, OP_STRBI, OP_LDRBI, OP_STRHI, OP_LDRHI, OP_STRSP,
    OP_LDRSP, OP_ADR, OP_ADDSPI, OP_ADDSP, OP_SUBSP, OP_SXTH, OP_SXTB, OP_UXTH, OP_UXTB,
    OP_PUSH, OP_POP, OP_REV, OP_REV16, OP_REVSH, OP_STM, OP_LDM, OP_NOP, OP_BCOND, OP_B,
    OP_BL, OP_BX, OP_BLX, OP_COUNT
};

const char *m0_op_names[] = {
    "fallback", "lsli", "lsri", "asri", "addr", "subr", "addi3", "subi3", "movi",
    "cmpi", "addi8", "subi8", "and", "eor", "lslr", "lsrr", "asrr", "adc", "sbc",
    "ror", "tst", "neg", "cmp", "cmn", "orr", "mul", "bic", "mvn", "addhi",
    "cmphi", "movhi", "ldrlit", "strr", "strhr", "strbr", "ldrsbr", "ldrr", "ldrhr",
    "ldrbr", "ldrshr", "stri", "ldri", "strbi", "ldrbi", "strhi", "ldrhi", "strsp",
    "ldrsp", "adr", "addspi", "addsp", "subsp", "sxth", "sxtb", "uxth", "uxtb",
    "push", "pop", "rev", "rev16", "revsh", "stm", "ldm", "nop", "bcond", "b",
    "bl", "bx", "blx", 0
};

enum { K_SEQ, K_CALL, K_RET, K_OTHER };         /* kinds that matter to the observations */
enum { ST_HALT, ST_FALLBACK, ST_LIMIT };

#define HALT 0xFFFFFFF0u

typedef struct {
    uint32_t r[16];
    uint32_t n, z, c, v;
    uint64_t cyc, max_cycles;
    uint32_t pc;
    uint8_t *mem;
    uint64_t mem_len;
    /* the decoded code, one entry per halfword of [lo, hi) */
    uint32_t lo, hi;
    const uint8_t *op, *kind, *size, *cond;
    const int32_t *a0, *a1, *a2;
    const uint32_t *target, *cyt, *cyn;
    const uint16_t *regs;                      /* register lists (bit 14: LR, 15: PC) */
} M0;

/* the observations (m0.Watch) */
typedef struct {
    int32_t *fn_of;                            /* halfword of [lo, hi) -> function, or -1 */
    int32_t nfn;
    uint64_t *obs; uint8_t *obs_seen;          /* cycles of the longest call of a function */
    int64_t *sobs; uint8_t *sobs_seen;         /* bytes of stack of its deepest activation */
    /* calls in progress, and their frames (frame 0: the run itself) */
    int64_t ncs, ccap;
    int32_t *cs_fn; uint64_t *cs_start; uint32_t *cs_ret;
    int64_t nfr, fcap;
    uint32_t *fr_at, *fr_low;
    /* two sets of loops (0: bounds of the schema, 1: certified bounds) */
    int32_t *hdr[2];                           /* halfword -> loop, or -1 */
    int64_t *body_off[2];                      /* loop -> start in body_addr (n + 1 entries) */
    uint32_t *body_addr[2];                    /* sorted addresses of the bodies */
    int64_t *bound[2];
    uint64_t *count[2], *worst[2];
    uint8_t *worst_seen[2];
    /* bound exceeded: (set, loop, count), in order */
    int64_t nviol, vcap;
    int32_t *viol_set, *viol_loop; uint64_t *viol_count;
    int failed;                                /* out of memory */
} Mon;

static inline uint32_t nz(M0 *m, uint32_t v) {
    m->n = v >> 31;
    m->z = v == 0;
    return v;
}

static inline uint32_t addc(M0 *m, uint32_t a, uint32_t b, uint32_t carry) {
    uint64_t u = (uint64_t)a + b + carry;
    uint32_t res = (uint32_t)u;
    m->c = u > 0xFFFFFFFFull;
    m->v = (((a ^ res) & (b ^ res)) >> 31) & 1;
    return nz(m, res);
}

static inline int cond(M0 *m, int c) {
    uint32_t n = m->n, z = m->z, cc = m->c, v = m->v;
    switch (c) {
    case 0: return z;
    case 1: return !z;
    case 2: return cc;
    case 3: return !cc;
    case 4: return n;
    case 5: return !n;
    case 6: return v;
    case 7: return !v;
    case 8: return cc && !z;
    case 9: return !cc || z;
    case 10: return n == v;
    case 11: return n != v;
    case 12: return !z && n == v;
    default: return z || n != v;
    }
}

static inline uint32_t rd32(M0 *m, uint64_t a) {
    uint32_t v;
    memcpy(&v, m->mem + a, 4);
    return v;                                  /* little-endian host (x86, Arm) */
}

static inline void wr32(M0 *m, uint64_t a, uint32_t v) { memcpy(m->mem + a, &v, 4); }

/* capacity of the parallel arrays of the calls, of the frames, of the violations */
static int grow_calls(Mon *w, int64_t need) {
    if (need <= w->ccap)
        return 1;
    int64_t c = w->ccap ? w->ccap * 2 : 64;
    while (c < need)
        c *= 2;
    int32_t *f = realloc(w->cs_fn, (size_t)c * sizeof *f);
    if (!f) return 0;
    w->cs_fn = f;
    uint64_t *st = realloc(w->cs_start, (size_t)c * sizeof *st);
    if (!st) return 0;
    w->cs_start = st;
    uint32_t *rt = realloc(w->cs_ret, (size_t)c * sizeof *rt);
    if (!rt) return 0;
    w->cs_ret = rt;
    w->ccap = c;
    return 1;
}

static int grow_frames(Mon *w, int64_t need) {
    if (need <= w->fcap)
        return 1;
    int64_t c = w->fcap ? w->fcap * 2 : 64;
    while (c < need)
        c *= 2;
    uint32_t *at = realloc(w->fr_at, (size_t)c * sizeof *at);
    if (!at) return 0;
    w->fr_at = at;
    uint32_t *lo = realloc(w->fr_low, (size_t)c * sizeof *lo);
    if (!lo) return 0;
    w->fr_low = lo;
    w->fcap = c;
    return 1;
}

static int grow_viol(Mon *w, int64_t need) {
    if (need <= w->vcap)
        return 1;
    int64_t c = w->vcap ? w->vcap * 2 : 64;
    while (c < need)
        c *= 2;
    int32_t *s = realloc(w->viol_set, (size_t)c * sizeof *s);
    if (!s) return 0;
    w->viol_set = s;
    int32_t *l = realloc(w->viol_loop, (size_t)c * sizeof *l);
    if (!l) return 0;
    w->viol_loop = l;
    uint64_t *n = realloc(w->viol_count, (size_t)c * sizeof *n);
    if (!n) return 0;
    w->viol_count = n;
    w->vcap = c;
    return 1;
}

static int in_body(Mon *w, int s, int32_t id, uint32_t addr) {
    int64_t lo = w->body_off[s][id], hi = w->body_off[s][id + 1];
    while (lo < hi) {
        int64_t mid = (lo + hi) / 2;
        uint32_t x = w->body_addr[s][mid];
        if (x == addr)
            return 1;
        if (x < addr)
            lo = mid + 1;
        else
            hi = mid;
    }
    return 0;
}

/* After an instruction (`has` = 0: a function without code returned to `nxt`); the rules
 * of m0.Watch.step. */
void mon_step(M0 *m, Mon *w, int has, int kind, uint32_t addr, uint32_t target, uint32_t nxt) {
    uint32_t sp = m->r[13];
    if (w->nfr > 0 && sp < w->fr_low[w->nfr - 1])
        w->fr_low[w->nfr - 1] = sp;
    if (has && kind == K_CALL) {
        int32_t fn = -1;
        if (target >= m->lo && target < m->hi && !((target - m->lo) & 1))
            fn = w->fn_of[(target - m->lo) >> 1];
        if (!grow_calls(w, w->ncs + 1) || !grow_frames(w, w->nfr + 1)) { w->failed = 1; return; }
        w->cs_fn[w->ncs] = fn;
        w->cs_start[w->ncs] = m->cyc;
        w->cs_ret[w->ncs] = addr + 4;
        w->ncs++;
        w->fr_at[w->nfr] = sp;
        w->fr_low[w->nfr] = sp;
        w->nfr++;
    } else if (w->ncs > 0 && nxt == w->cs_ret[w->ncs - 1] && (!has || kind == K_RET)) {
        w->ncs--;
        int32_t fn = w->cs_fn[w->ncs];
        uint64_t start = w->cs_start[w->ncs];
        w->nfr--;
        uint32_t at = w->fr_at[w->nfr], low = w->fr_low[w->nfr];
        if (w->nfr > 0 && low < w->fr_low[w->nfr - 1])
            w->fr_low[w->nfr - 1] = low;
        if (fn >= 0) {
            uint64_t d = m->cyc - start;
            if (!w->obs_seen[fn] || d > w->obs[fn])
                w->obs[fn] = d;
            w->obs_seen[fn] = 1;
            int64_t s = (int64_t)at - (int64_t)low;
            if (!w->sobs_seen[fn] || s > w->sobs[fn])
                w->sobs[fn] = s;
            w->sobs_seen[fn] = 1;
        }
    }
    if (!has || nxt < m->lo || nxt >= m->hi || ((nxt - m->lo) & 1))
        return;
    uint32_t hx = (nxt - m->lo) >> 1;
    for (int s = 0; s < 2; s++) {
        if (!w->hdr[s])
            continue;
        int32_t id = w->hdr[s][hx];
        if (id < 0)
            continue;
        if (in_body(w, s, id, addr)) {
            uint64_t c = ++w->count[s][id];
            if ((int64_t)c > w->bound[s][id]) {
                if (!grow_viol(w, w->nviol + 1)) { w->failed = 1; return; }
                w->viol_set[w->nviol] = s;
                w->viol_loop[w->nviol] = id;
                w->viol_count[w->nviol] = c;
                w->nviol++;
            }
            if (s == 0) {
                if (!w->worst_seen[0][id] || c > w->worst[0][id])
                    w->worst[0][id] = c;
                w->worst_seen[0][id] = 1;
            }
        } else {
            w->count[s][id] = 0;
        }
    }
}

void mon_free(Mon *w) {
    free(w->cs_fn); free(w->cs_start); free(w->cs_ret);
    free(w->fr_at); free(w->fr_low);
    free(w->viol_set); free(w->viol_loop); free(w->viol_count);
    w->cs_fn = 0; w->cs_start = 0; w->cs_ret = 0; w->fr_at = 0; w->fr_low = 0;
    w->viol_set = 0; w->viol_loop = 0; w->viol_count = 0;
    w->ccap = w->fcap = w->vcap = 0;
}

/* the frames of the observations, set from m0.py before a run (frame 0) */
int mon_push_frame(Mon *w, uint32_t at, uint32_t low) {
    if (!grow_frames(w, w->nfr + 1))
        return 0;
    w->fr_at[w->nfr] = at;
    w->fr_low[w->nfr] = low;
    w->nfr++;
    return 1;
}

#define MEMOK(a, k) ((a) + (k) <= m->mem_len)
#define FALL do { m->pc = pc; return ST_FALLBACK; } while (0)

/* Runs from m->pc until HALT (ST_HALT), an instruction left to m0.py (ST_FALLBACK, nothing
 * changed, m->pc at it), or more than max_cycles (ST_LIMIT, after the instruction and its
 * observation, as m0.py raises its Stop). */
int m0_run(M0 *m, Mon *w) {
    uint32_t pc = m->pc;
    uint32_t *r = m->r;
    while (pc != HALT) {
        if (pc < m->lo || pc >= m->hi || ((pc - m->lo) & 1))
            FALL;
        uint32_t x = (pc - m->lo) >> 1;
        int op = m->op[x];
        int32_t a0 = m->a0[x], a1 = m->a1[x], a2 = m->a2[x];
        uint32_t nxt = pc + m->size[x];
        int taken = 1;
        uint64_t ad;
        switch (op) {
        case OP_FALLBACK:
            FALL;
        case OP_BCOND:
            taken = cond(m, m->cond[x]);
            if (taken)
                nxt = m->target[x];
            break;
        case OP_B:
            nxt = m->target[x];
            break;
        case OP_BL:
            r[14] = (pc + 4) | 1;
            nxt = m->target[x];
            break;
        case OP_BX:
        case OP_BLX: {
            if (a0 == 15)
                FALL;
            uint32_t t = r[a0];
            if (op == OP_BLX)
                r[14] = (pc + 2) | 1;
            nxt = t & ~1u;
            break;
        }
        case OP_PUSH: {
            uint16_t L = m->regs[x];
            int k = __builtin_popcount(L);
            uint64_t sp = (uint64_t)r[13] - 4u * k;
            if (r[13] < 4u * k || !MEMOK(sp, 4u * k))
                FALL;
            int j = 0;
            for (int reg = 0; reg < 16; reg++)
                if (L >> reg & 1)
                    wr32(m, sp + 4u * j++, r[reg]);
            r[13] = (uint32_t)sp;
            break;
        }
        case OP_POP: {
            uint16_t L = m->regs[x];
            int k = __builtin_popcount(L);
            uint64_t sp = r[13];
            if (!MEMOK(sp, 4u * k))
                FALL;
            int j = 0;
            for (int reg = 0; reg < 16; reg++)
                if (L >> reg & 1) {
                    uint32_t val = rd32(m, sp + 4u * j++);
                    if (reg == 15)
                        nxt = val & ~1u;
                    else
                        r[reg] = val;
                }
            r[13] = (uint32_t)(sp + 4u * k);
            break;
        }
        case OP_LSLI: {
            uint32_t v = r[a1];
            if (a2) {
                m->c = (v >> (32 - a2)) & 1;
                v <<= a2;
            }
            r[a0] = nz(m, v);
            break;
        }
        case OP_LSRI: {
            int imm = a2 ? a2 : 32;
            uint32_t v = r[a1];
            m->c = (v >> (imm - 1)) & 1;
            r[a0] = nz(m, imm < 32 ? v >> imm : 0);
            break;
        }
        case OP_ASRI: {
            int imm = a2 ? a2 : 32;
            int32_t v = (int32_t)r[a1];
            m->c = (uint32_t)(v >> (imm - 1)) & 1;
            r[a0] = nz(m, imm < 32 ? (uint32_t)(v >> imm) : (v < 0 ? 0xFFFFFFFFu : 0));
            break;
        }
        case OP_ADDR: r[a0] = addc(m, r[a1], r[a2], 0); break;
        case OP_SUBR: r[a0] = addc(m, r[a1], ~r[a2], 1); break;
        case OP_ADDI3: r[a0] = addc(m, r[a1], (uint32_t)a2, 0); break;
        case OP_SUBI3: r[a0] = addc(m, r[a1], ~(uint32_t)a2, 1); break;
        case OP_MOVI: r[a0] = nz(m, (uint32_t)a1); break;
        case OP_CMPI: addc(m, r[a0], ~(uint32_t)a1, 1); break;
        case OP_ADDI8: r[a0] = addc(m, r[a0], (uint32_t)a1, 0); break;
        case OP_SUBI8: r[a0] = addc(m, r[a0], ~(uint32_t)a1, 1); break;
        case OP_AND: r[a0] = nz(m, r[a0] & r[a1]); break;
        case OP_TST: nz(m, r[a0] & r[a1]); break;
        case OP_EOR: r[a0] = nz(m, r[a0] ^ r[a1]); break;
        case OP_ORR: r[a0] = nz(m, r[a0] | r[a1]); break;
        case OP_BIC: r[a0] = nz(m, r[a0] & ~r[a1]); break;
        case OP_MVN: r[a0] = nz(m, ~r[a1]); break;
        case OP_MUL: r[a0] = nz(m, r[a0] * r[a1]); break;
        case OP_LSLR: {
            uint32_t s = r[a1] & 0xFF, v = r[a0];
            if (s == 0) {
            } else if (s < 32) {
                m->c = (v >> (32 - s)) & 1;
                v <<= s;
            } else if (s == 32) {
                m->c = v & 1;
                v = 0;
            } else {
                m->c = 0;
                v = 0;
            }
            r[a0] = nz(m, v);
            break;
        }
        case OP_LSRR: {
            uint32_t s = r[a1] & 0xFF, v = r[a0];
            if (s == 0) {
            } else if (s < 32) {
                m->c = (v >> (s - 1)) & 1;
                v >>= s;
            } else if (s == 32) {
                m->c = v >> 31;
                v = 0;
            } else {
                m->c = 0;
                v = 0;
            }
            r[a0] = nz(m, v);
            break;
        }
        case OP_ASRR: {
            uint32_t s = r[a1] & 0xFF, v = r[a0];
            int32_t sv = (int32_t)v;
            if (s == 0) {
            } else if (s < 32) {
                m->c = (uint32_t)(sv >> (s - 1)) & 1;
                v = (uint32_t)(sv >> s);
            } else {
                m->c = (uint32_t)(sv >> 31) & 1;
                v = sv < 0 ? 0xFFFFFFFFu : 0;
            }
            r[a0] = nz(m, v);
            break;
        }
        case OP_ROR: {
            uint32_t s = r[a1] & 0xFF, v = r[a0];
            if (s) {
                uint32_t k = s & 31;
                if (k)
                    v = (v >> k) | (v << (32 - k));
                m->c = v >> 31;
            }
            r[a0] = nz(m, v);
            break;
        }
        case OP_ADC: r[a0] = addc(m, r[a0], r[a1], m->c); break;
        case OP_SBC: r[a0] = addc(m, r[a0], ~r[a1], m->c); break;
        case OP_NEG: r[a0] = addc(m, 0, ~r[a1], 1); break;
        case OP_CMP: addc(m, r[a0], ~r[a1], 1); break;
        case OP_CMN: addc(m, r[a0], r[a1], 0); break;
        case OP_ADDHI:
            if (a0 == 15 || a1 == 15)
                FALL;
            r[a0] = r[a0] + r[a1];
            break;
        case OP_MOVHI:
            if (a0 == 15 || a1 == 15)
                FALL;
            r[a0] = r[a1];
            break;
        case OP_CMPHI:
            if (a0 == 15 || a1 == 15)
                FALL;
            addc(m, r[a0], ~r[a1], 1);
            break;
        case OP_LDRLIT:
            ad = (uint64_t)((pc + 4) & ~3u) + (uint32_t)a1;
            if (!MEMOK(ad, 4))
                FALL;
            r[a0] = rd32(m, ad);
            break;
        case OP_ADR: r[a0] = ((pc + 4) & ~3u) + (uint32_t)a1; break;
        case OP_ADDSPI: r[a0] = r[13] + (uint32_t)a1; break;
        case OP_ADDSP: r[13] += (uint32_t)a0; break;
        case OP_SUBSP:
            if (r[13] < (uint32_t)a0)
                FALL;                          /* m0.py's value would be negative */
            r[13] -= (uint32_t)a0;
            break;
        case OP_STRSP:
            ad = (uint64_t)r[13] + (uint32_t)a1;
            if (!MEMOK(ad, 4))
                FALL;
            wr32(m, ad, r[a0]);
            break;
        case OP_LDRSP:
            ad = (uint64_t)r[13] + (uint32_t)a1;
            if (!MEMOK(ad, 4))
                FALL;
            r[a0] = rd32(m, ad);
            break;
        /* loads and stores with a register or an immediate offset (m0.py `access`) */
        case OP_STRR: case OP_STRHR: case OP_STRBR: case OP_LDRSBR: case OP_LDRR:
        case OP_LDRHR: case OP_LDRBR: case OP_LDRSHR:
        case OP_STRI: case OP_LDRI: case OP_STRBI: case OP_LDRBI: case OP_STRHI: case OP_LDRHI: {
            int reg = op <= OP_LDRSHR;
            ad = (uint32_t)(r[a1] + (reg ? r[a2] : (uint32_t)a2));
            int k;
            switch (op) {
            case OP_STRR: case OP_LDRR: case OP_STRI: case OP_LDRI: k = 4; break;
            case OP_STRHR: case OP_LDRHR: case OP_LDRSHR: case OP_STRHI: case OP_LDRHI: k = 2; break;
            default: k = 1;
            }
            if (!MEMOK(ad, k))
                FALL;
            uint8_t *p = m->mem + ad;
            switch (op) {
            case OP_STRR: case OP_STRI: wr32(m, ad, r[a0]); break;
            case OP_STRHR: case OP_STRHI: p[0] = r[a0] & 0xFF; p[1] = (r[a0] >> 8) & 0xFF; break;
            case OP_STRBR: case OP_STRBI: p[0] = r[a0] & 0xFF; break;
            case OP_LDRR: case OP_LDRI: r[a0] = rd32(m, ad); break;
            case OP_LDRHR: case OP_LDRHI: r[a0] = p[0] | (uint32_t)p[1] << 8; break;
            case OP_LDRBR: case OP_LDRBI: r[a0] = p[0]; break;
            case OP_LDRSHR: r[a0] = (uint32_t)(int32_t)(int16_t)(p[0] | (uint32_t)p[1] << 8); break;
            default: r[a0] = (uint32_t)(int32_t)(int8_t)p[0]; break;   /* OP_LDRSBR */
            }
            break;
        }
        case OP_SXTH: r[a0] = (uint32_t)(int32_t)(int16_t)(r[a1] & 0xFFFF); break;
        case OP_SXTB: r[a0] = (uint32_t)(int32_t)(int8_t)(r[a1] & 0xFF); break;
        case OP_UXTH: r[a0] = r[a1] & 0xFFFF; break;
        case OP_UXTB: r[a0] = r[a1] & 0xFF; break;
        case OP_REV: {
            uint32_t v = r[a1];
            r[a0] = (v >> 24) | ((v >> 8) & 0xFF00) | ((v << 8) & 0xFF0000) | (v << 24);
            break;
        }
        case OP_REV16: {
            uint32_t v = r[a1];
            r[a0] = ((v >> 8) & 0x00FF00FF) | ((v << 8) & 0xFF00FF00);
            break;
        }
        case OP_REVSH: {
            uint32_t v = r[a1];
            r[a0] = (uint32_t)(int32_t)(int16_t)(((v >> 8) & 0xFF) | ((v & 0xFF) << 8));
            break;
        }
        case OP_STM: {
            uint16_t L = m->regs[x];
            int k = __builtin_popcount(L);
            uint64_t base = r[a0];
            if (!MEMOK(base, 4u * k))
                FALL;
            int j = 0;
            for (int reg = 0; reg < 8; reg++)
                if (L >> reg & 1)
                    wr32(m, base + 4u * j++, r[reg]);
            r[a0] = (uint32_t)(base + 4u * k);
            break;
        }
        case OP_LDM: {
            uint16_t L = m->regs[x];
            int k = __builtin_popcount(L);
            uint64_t base = r[a0];
            if (!MEMOK(base, 4u * k))
                FALL;
            int j = 0;
            for (int reg = 0; reg < 8; reg++)
                if (L >> reg & 1)
                    r[reg] = rd32(m, base + 4u * j++);
            if (!(L >> a0 & 1))
                r[a0] = (uint32_t)(base + 4u * k);
            break;
        }
        case OP_NOP:
            break;
        default:
            FALL;
        }
        m->cyc += taken ? m->cyt[x] : m->cyn[x];
        if (w)
            mon_step(m, w, 1, m->kind[x], pc, m->target[x], nxt);
        if (m->cyc > m->max_cycles) {
            m->pc = nxt;
            return ST_LIMIT;
        }
        pc = nxt;
    }
    m->pc = pc;
    return ST_HALT;
}
