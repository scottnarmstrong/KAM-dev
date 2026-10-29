#!/usr/bin/env python3
r"""SO-ADVCOUNT: simulate ONE advice-checked Kronecker-packed real product (design Revision 5, decision 16, A-E §B').

Given two real integer factors (Fourier key -> mantissa at scales 2^-SA, 2^-SB) this builds exactly what the
checker and the generator would build:
  * the dense box layout `PackLayout` (rows = first key coordinate, row stride = the no-wrap minimum
    `colsA + colsB - 1`, `blockRows` = 32), the factor blocks A_i, B_j;
  * every output shard s: the exact window sum T_s = sum_{i+j=s} conv(A_i, B_j) (Kronecker: one big-integer
    product per block pair, here with Python/GMP integers, positive/negative parts packed separately);
  * the design-B advice: a target box, the rounding scale U (result mantissas at 2^-Pout, Pout = SA + SB - U),
    the rounded in-box window values r_s = round(T_s / 2^U), and outLog (log-bound of every out-of-box slot);
    box, Pout and outLog are chosen as the smallest ones whose strip remainder
        in-box  2^-Pout * sum_{box} W(|k|)  +  out-of-box  2^(outLog + 1 - SA - SB) * sum_{window \ box} W(|k|)
    meets the caller's budget (the remainder `CertPoly.mulPacked` puts into the radius);
  * the advice volume (decimal and hex list literals, exact digit counts), shard / block / pair counts, and the
    kernel and elaboration estimates of SO-REPLAY2's measured model.
Untrusted tooling.
"""
import math
from fractions import Fraction as F
import numpy as np

R = 32                                   # blockRows (SO-REPLAY2, design §5)
WB = 64                                  # weight-table scale bits (rotlib.WB)

# ---- SO-REPLAY2 cost model (kernel = Lean "type checking took", LEAN_NUM_THREADS=1; +-30 % machine load)
# per-slot packing + slot-bound decoding of a 16384-slot window at w = 896: 2.35 s + 2.5 s
WIN_S_PER_SLOT = (4.85 / 16384 * 0.9, 4.85 / 16384 * 1.1)
MUL_S_PER_PAIR = (0.2, 0.5)              # one 8192-slot x 8192-slot literal multiplication incl. assembly, w = 896
TIE_S_PER_BLOCK = (0.15, 0.4)            # tie of one 8192-slot factor literal, w = 896
LIN_S_PER_SLOT = 80e-6                   # linear pass (decode / mantCheck / ofDyadic / radius), 880-bit slots
ELAB_S_PER_MB = 18.0                     # data elaboration, s per MB of source
REF_SLOTS, REF_W = 8192, 896


def fw(w):
    """SO-REPLAY2's width factor (per-slot cost 0.05 + 0.1 w/896 ms, normalized at w = 896)."""
    return (0.05 + 0.1 * w / REF_W) / 0.15


def bitlen(x):
    return int(abs(int(x))).bit_length()


class Layout:
    def __init__(self, keys_a, keys_b):
        ka = [k for k, _ in keys_a]; la = [l for _, l in keys_a]
        kb = [k for k, _ in keys_b]; lb = [l for _, l in keys_b]
        self.ka0, self.ka1, self.la0, self.la1 = min(ka), max(ka), min(la), max(la)
        self.kb0, self.kb1, self.lb0, self.lb1 = min(kb), max(kb), min(lb), max(lb)
        self.ca = self.la1 - self.la0 + 1
        self.cb = self.lb1 - self.lb0 + 1
        self.st = self.ca + self.cb - 1                 # no-wrap stride (PackLayout.compat)
        self.ra = self.ka1 - self.ka0 + 1
        self.rb = self.kb1 - self.kb0 + 1
        self.na = -(-self.ra // R)
        self.nb = -(-self.rb // R)
        self.block_slots = R * self.st
        self.k0 = self.ka0 + self.kb0                   # product key of output row 0
        self.l0 = self.la0 + self.lb0


def _pack(vals, wb):
    """sum vals[i] 2^(8 wb i) for NONNEGATIVE vals < 2^(8 wb) (bytes, little endian)."""
    return int.from_bytes(b"".join(int(v).to_bytes(wb, "little") for v in vals), "little")


def _unpack(x, n, wb):
    bs = x.to_bytes(n * wb, "little")
    return [int.from_bytes(bs[i * wb:(i + 1) * wb], "little") for i in range(n)]


def blocks(d, L, which):
    """dense factor blocks (lists of R * st signed slots) of the factor dict d."""
    k0, l0, nblk = (L.ka0, L.la0, L.na) if which == "a" else (L.kb0, L.lb0, L.nb)
    out = [[0] * L.block_slots for _ in range(nblk)]
    for (k, l), v in d.items():
        r = k - k0
        out[r // R][(r % R) * L.st + (l - l0)] = int(v)
    return out


def shard_windows(A, B, L, w):
    """exact T_s for every shard s, as dicts {window slot: value} (nonzero only), via packed big-int products."""
    wb = -(-w // 8)
    def pn(blk):
        return (_pack([v if v > 0 else 0 for v in blk], wb), _pack([-v if v < 0 else 0 for v in blk], wb))
    PA = [pn(b) for b in A]; PB = [pn(b) for b in B]
    nwin = 2 * L.block_slots - 1
    T = []
    for s in range(L.na + L.nb - 1):
        pos = neg = 0
        for i in range(max(0, s - L.nb + 1), min(L.na, s + 1)):
            j = s - i
            (ap, an), (bp, bn) = PA[i], PB[j]
            pos += ap * bp + an * bn
            neg += ap * bn + an * bp
        P = _unpack(pos, nwin, wb) if pos else [0] * nwin
        N = _unpack(neg, nwin, wb) if neg else [0] * nwin
        T.append({m: p - q for m, (p, q) in enumerate(zip(P, N)) if p != q})
    return T


def window_key(L, s, m):
    """product key of slot m of shard window s."""
    return (L.k0 + R * s + m // L.st, L.l0 + m % L.st)


def simulate(a, b, SA, SB, Wt, budget, pout_min=None, label="", combined_check=None):
    """a, b: {(k, l): int} real mantissas at 2^-SA, 2^-SB.  Wt: rotlib.Weights.  budget: allowed strip remainder of
    the packed product (absolute).  Returns a stats dict."""
    a = {k: v for k, v in a.items() if v}
    b = {k: v for k, v in b.items() if v}
    if not a or not b:
        return dict(label=label, empty=True)
    L = Layout(list(a), list(b))
    maxa = max(abs(v) for v in a.values()); maxb = max(abs(v) for v in b.values())
    w_fit = bitlen(2 * min(len(a), len(b)) * maxa * maxb) + 1      # convFits
    w_design = bitlen(maxa) + bitlen(maxb) + 16                    # w = 2 bits + 16
    w = max(w_fit, w_design)
    A = blocks(a, L, "a"); B = blocks(b, L, "b")
    T = shard_windows(A, B, L, w)
    S2 = SA + SB
    # combined product (overlap-add) and per-window slot keys
    comb = {}
    for s, Ts in enumerate(T):
        for m, v in Ts.items():
            key = window_key(L, s, m)
            comb[key] = comb.get(key, 0) + v
    if combined_check is not None:
        assert {k: v for k, v in comb.items() if v} == {k: v for k, v in combined_check.items() if v}, label
    Wn = Wt.W
    def wgt(key):
        return int(Wn[abs(key[0]) + abs(key[1])])
    # product window extent (all slots any shard window covers)
    prow = L.ra + L.rb - 1
    # ---- choose the target box: bounding box of {bitlen(|c| W) >= top - e}, e swept up until the out-of-box
    #      bound (from the WINDOW partial sums: each window's out-of-box slots must pass |T_s| <= 2^outLog) fits
    ck = np.array([k for k in comb], dtype=np.int64).reshape(-1, 2)
    cm = np.array([bitlen(abs(v) * wgt(k)) if v else 0 for k, v in comb.items()], dtype=np.int64)
    wk, wl, wbits = [], [], []
    for s, Ts in enumerate(T):
        for m, v in Ts.items():
            kk = window_key(L, s, m)
            wk.append(kk[0]); wl.append(kk[1]); wbits.append(bitlen(v))
    wk = np.array(wk, dtype=np.int64); wl = np.array(wl, dtype=np.int64); wbits = np.array(wbits, dtype=np.int64)
    def in_box(bx, key):
        return bx[0] <= key[0] <= bx[1] and bx[2] <= key[1] <= bx[3]
    def wsum_box(bx):
        kk = np.arange(bx[0], bx[1] + 1); ll = np.arange(bx[2], bx[3] + 1)
        n = (np.abs(kk)[:, None] + np.abs(ll)[None, :]).ravel()
        return int(Wn[n].sum())
    win_box = (L.k0, L.k0 + prow - 1, L.l0, L.l0 + L.st - 1)
    wsum_all = wsum_box(win_box)
    best = None
    top = int(cm.max())
    for e in range(0, top + 8, 2):
        sel = cm >= top - e
        bx = (int(ck[sel, 0].min()), int(ck[sel, 0].max()), int(ck[sel, 1].min()), int(ck[sel, 1].max()))
        out = ~((wk >= bx[0]) & (wk <= bx[1]) & (wl >= bx[2]) & (wl <= bx[3]))
        outlog = int(wbits[out].max()) if out.any() else 0
        wb_ = wsum_box(bx)
        rad_out = F((2 << outlog) * (wsum_all - wb_), 1 << (S2 + WB)) if out.any() else F(0)
        if rad_out <= F(budget) / 2:
            best = (bx, outlog, rad_out, wb_)
            break
    assert best is not None, label
    bx, outlog, rad_out, wbox = best
    # ---- rounding scale: smallest Pout (>= pout_min) with in-box rounding <= budget/2  (|conv - 2^U r| <= 2^U)
    pout = pout_min or 0
    while F(wbox, 1 << (pout + WB)) > F(budget) / 2:
        pout += 1
    U = S2 - pout
    rad_in = F(wbox, 1 << (pout + WB))
    # ---- advice: rounded in-box values of every window (exact digit counts)
    nslots = dec = hexc = zeros = 0
    rows_per_window = []
    for s, Ts in enumerate(T):
        r_lo = max(bx[0], L.k0 + R * s); r_hi = min(bx[1], L.k0 + R * s + 2 * R - 1)
        if r_hi < r_lo:
            rows_per_window.append(0)
            continue
        rows = r_hi - r_lo + 1
        rows_per_window.append(rows)
        cols = bx[3] - bx[2] + 1
        n = rows * cols
        nslots += n
        half = (1 << (U - 1)) if U > 0 else 0
        nz = 0
        for m, v in Ts.items():
            key = window_key(L, s, m)
            if in_box(bx, key):
                r = (v + half) >> U if U > 0 else v << (-U)
                if r:
                    nz += 1
                    dec += len(str(r)) + 2
                    zz = 2 * r if r >= 0 else -2 * r - 1
                    hexc += len(format(zz, "x")) + 4
        zeros += n - nz
        dec += 3 * (n - nz)                          # "0, "
        hexc += 3 * (n - nz)                         # "0, " (a zero needs no 0x)
    # ---- counts and the cost model
    nshards = L.na + L.nb - 1
    npairs = L.na * L.nb
    win_slots = 2 * L.block_slots
    f = fw(w)
    msc = L.block_slots * w / (REF_SLOTS * REF_W)    # multiplication size relative to the measured one
    k_lo = nshards * win_slots * WIN_S_PER_SLOT[0] * f + npairs * MUL_S_PER_PAIR[0] * msc \
        + (L.na + L.nb) * TIE_S_PER_BLOCK[0] * msc + (len(a) + len(b) + nslots) * LIN_S_PER_SLOT * f
    k_hi = nshards * win_slots * WIN_S_PER_SLOT[1] * f + npairs * MUL_S_PER_PAIR[1] * msc \
        + (L.na + L.nb) * TIE_S_PER_BLOCK[1] * msc + (len(a) + len(b) + nslots) * LIN_S_PER_SLOT * f
    nz_out = sum(1 for v in comb.values() if v)
    return dict(label=label, empty=False, terms_a=len(a), terms_b=len(b), bits_a=bitlen(maxa), bits_b=bitlen(maxb),
                SA=SA, SB=SB, box_a=[L.ka0, L.ka1, L.la0, L.la1], box_b=[L.kb0, L.kb1, L.lb0, L.lb1],
                rows_a=L.ra, rows_b=L.rb, stride=L.st, block_slots=L.block_slots, blocks_a=L.na, blocks_b=L.nb,
                shards=nshards, pairs=npairs, window_slots=win_slots, w_fit=w_fit, w_design=w_design, w=w,
                product_terms=nz_out, product_rows=prow,
                target_box=list(bx), target_slots=(bx[1] - bx[0] + 1) * (bx[3] - bx[2] + 1),
                pout=pout, scale_U=U, outLog=outlog, rad_in=float(rad_in), rad_out=float(rad_out),
                budget=float(budget), advice_slots=nslots, advice_zero_slots=zeros,
                advice_dec_bytes=dec, advice_hex_bytes=hexc,
                advice_fixedwidth_hex_bytes=nslots * (-(-pout // 4) + 4),
                kernel_s=[k_lo, k_hi], elab_s=ELAB_S_PER_MB * min(dec, hexc) / 1e6,
                rows_per_window=rows_per_window)
