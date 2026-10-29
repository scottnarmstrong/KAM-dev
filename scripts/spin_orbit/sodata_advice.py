#!/usr/bin/env python3
r"""SO-DATA-PY: build the design-B advice of one model product in the EXACT `PackedAdvice` layout of design
Revision 7 (A-E §B'), and verify it with the Python mirror of the checker (sodata_packed.py).

A complex model product `a · b` (both factors sparse integer Fourier data at mantissa scales 2^-SA, 2^-SB, with a
definite parity: coefficients i^ph · v) becomes `ProductAdvice.packed P rr ii ri ir` with P = max(SA, SB): the four
real products re·re, im·im, re·im, im·re of the mantissas at scale 2^-P (`CertPoly.toMants dec P`).  Exactly one
of the four is nonzero (parity).  For each real product this module chooses

  * the factor layouts `la`, `lb`: the key boxes of the factors, rows = first key coordinate, the no-wrap stride
    `colsA + colsB - 1` (`compat`), `blockRows` = 32;
  * the target box, `outLog` and the rounding `scale` (>= 1): the smallest box and `outLog` whose out-of-box
    remainder `2^(outLog + 1 - 2P) Σ_{non-box product slots} W(|k|)` is <= budget/2, then the largest scale with
    in-box remainder `2^(scale - 2P) Σ_box W(|k|)` <= budget/2 (`CertPoly.mulPacked`'s radius, W >= e^{2πρ|k|});
  * the rounded advice windows `r_s = round(T_s / 2^scale)` on in-box slots, zero elsewhere, from the exact
    shard window sums `T_s = shardConv L A B s` (Kronecker, one big-integer product per block pair);
  * the slot width `w`: the least one with every `shardFits` and every `reconFits` (the anti-carry guards).

Zero parts (Revision 7 empty-factor policy: an empty raw factor is rejected):
  * policy 'support' (DEFAULT; the signatures' docstrings as written, `toMants` keeping every key with its zero
    part): the zero part is laid out on the polynomial's own key box with all-zero slots; its product has a
    one-slot target, scale 1, outLog 0, width 2 and all-zero advice windows;
  * policy 'minimal': the zero part is the one-slot box at key 0 with raw factor [0] (needs `dense` to ignore
    zero entries, a proposed variant): far fewer shards.
Untrusted tooling.
"""
import math
from fractions import Fraction as F

import numpy as np

import sodata_packed as SP
from sodata_packed import PackLayout, PackedAdvice

R = 32          # blockRows (design §5, SO-REPLAY2)
WB = 64         # rotlib weight-table scale bits: W[n] / 2^WB >= exp(2 pi rho n)


def _lg(v):
    """the least g >= 0 with |v| <= 2^g."""
    a = abs(v)
    return 0 if a <= 1 else (a - 1).bit_length()


def box_of(keys):
    ks = [k for k, _ in keys]
    ls = [l for _, l in keys]
    return (min(ks), min(ls)), (max(ks) - min(ks) + 1, max(ls) - min(ls) + 1)


def layouts(box_a, box_b, width=0):
    """`la`, `lb` for two key boxes ((lo0, lo1), (rows, cols)), shared no-wrap stride (cols_a + cols_b - 1, 1)."""
    (loa, da), (lob, db) = box_a, box_b
    st = (da[1] + db[1] - 1, 1)
    return (PackLayout(tuple(loa), tuple(da), st, width, R), PackLayout(tuple(lob), tuple(db), st, width, R))


def with_width(L, w):
    return PackLayout(L.lo, L.dims, L.stride, w, L.blockRows)


def _windows(A, B, L, w):
    """exact T_s (balanced digits of the packed shard sums at a width w that fits every shard)."""
    PA = [SP.pack_sum(w, x) for x in A]
    PB = [SP.pack_sum(w, x) for x in B]
    T = []
    for s in range(len(A) + len(B) - 1):
        X = 0
        for i in range(max(0, s - len(B) + 1), min(len(A), s + 1)):
            X += PA[i] * PB[s - i]
        e = SP.balanced_digits(w, 2 * L - 1, X)
        assert e is not None
        T.append(e)
    return T


def build_real(da, db, la, lb, P, Wt, budget, zero=False):
    """The `PackedAdvice` of one real product of the raw dense factors `da`, `db` (layouts `la`, `lb`, width
    unset) at mantissa scale P with strip-remainder budget `budget`.  Returns (adv, info)."""
    L = la.blockRows * la.stride[0]
    adv0 = PackedAdvice(la, lb, la, 1, [], 0)
    A, B = SP.cut(adv0, da), SP.cut(adv0, db)
    ns = len(A) + len(B) - 1
    mA = max(SP.max_abs(x) for x in A)
    mB = max(SP.max_abs(x) for x in B)
    plen = len(da) + len(db) - 1
    r0, c0 = la.lo[0] + lb.lo[0], la.lo[1] + lb.lo[1]
    st = la.stride[0]
    win_rows = la.dims[0] + lb.dims[0] - 1
    win_cols = la.dims[1] + lb.dims[1] - 1
    if mA == 0 or mB == 0:
        # identically zero product: one-slot target at the window corner, scale 1, outLog 0
        target = PackLayout((r0, c0), (1, 1), la.stride, 0, R)
        adv = PackedAdvice(la, lb, target, 1, [[0] * (2 * L - 1) for _ in range(ns)], 0)
        box = SP.InBoxTable(adv)
        w = 0
        for s in range(ns):
            w = max(w, SP.shard_fits_min_width(L, mA, mB, s))
            logs = SP.shard_logs_list(adv, s, box)
            w = max(w, max((2 * (1 << g)).bit_length() for g in logs))
        adv = PackedAdvice(with_width(la, w), with_width(lb, w), with_width(target, w), 1, adv.rounded, 0)
        return adv, dict(zero=True, w=w, shards=ns, blockLen=L, scale=1, outLog=0, rad_in=0.0, rad_out=0.0,
                         target=[list(target.lo), list(target.dims)], advice_nonzero=0)
    w0 = max(SP.shard_fits_min_width(L, mA, mB, s) for s in range(ns))
    T = _windows(A, B, L, w0)
    # weights of every product slot q < plen (its prodKey), and the combined exact product
    q = np.arange(plen, dtype=np.int64)
    qk = r0 + q // st
    ql = c0 + q % st
    n1 = np.abs(qk) + np.abs(ql)
    assert n1.max() <= Wt.nmax
    Wf = np.array([float(x) for x in Wt.W[: int(n1.max()) + 1]])[n1]       # float weights (sweep only)
    comb = [0] * plen
    for s, Ts in enumerate(T):
        base = s * L
        for i, v in enumerate(Ts):
            if v and base + i < plen:
                comb[base + i] += v
    nzq = np.array([i for i, v in enumerate(comb) if v], dtype=np.int64)
    mag = np.array([math.log2(abs(comb[i])) + math.log2(Wf[i]) for i in nzq])
    # window slot values per (s, i) with their product slot (for outLog)
    wq, wl = [], []
    for s, Ts in enumerate(T):
        for i, v in enumerate(Ts):
            if v:
                wq.append(s * L + i)
                wl.append(_lg(v))
    wq = np.array(wq, dtype=np.int64)
    wl = np.array(wl, dtype=np.int64)
    wqk, wql = r0 + wq // st, c0 + wq % st
    top = float(mag.max())
    two2P = 2 * P
    half_budget = F(budget) / 2
    chosen = None
    for e in np.arange(0.0, top + 2000.0, 1.0):
        sel = mag >= top - e
        qs = nzq[sel]
        kk, ll = r0 + qs // st, c0 + qs % st
        bx = (int(kk.min()), int(kk.max()), int(ll.min()), int(ll.max()))
        out = ~((wqk >= bx[0]) & (wqk <= bx[1]) & (wql >= bx[2]) & (wql <= bx[3]) & (wq < plen))
        outlog = int(wl[out].max()) if out.any() else 0
        inb = (qk >= bx[0]) & (qk <= bx[1]) & (ql >= bx[2]) & (ql <= bx[3])
        wout = float(Wf[~inb].sum())
        if math.log2(max(wout, 1e-300)) + outlog + 1 - two2P - WB <= math.log2(float(half_budget)) - 1e-9 \
                or not (~inb).any():
            # exact confirmation
            wout_exact = sum(int(Wt.W[int(x)]) for x in n1[~inb])
            if F((1 << (outlog + 1)) * wout_exact, 1 << (two2P + WB)) <= half_budget:
                chosen = (bx, outlog, wout_exact, inb)
                break
    assert chosen is not None, "no target box meets the budget"
    bx, outlog, wout_exact, inb = chosen
    win_exact = sum(int(Wt.W[int(x)]) for x in n1[inb])
    # largest scale >= 1 with 2^(scale - 2P) win_exact / 2^WB <= budget / 2
    scale = 1
    if F((1 << 1) * win_exact, 1 << (two2P + WB)) > half_budget:
        raise ValueError("budget below the resolution 2^(1-2P): raise P")
    while F((1 << (scale + 1)) * win_exact, 1 << (two2P + WB)) <= half_budget:
        scale += 1
    rad_in = F((1 << scale) * win_exact, 1 << (two2P + WB))
    rad_out = F((1 << (outlog + 1)) * wout_exact, 1 << (two2P + WB))
    assert rad_in + rad_out <= F(budget)
    target = PackLayout((bx[0], bx[2]), (bx[1] - bx[0] + 1, bx[3] - bx[2] + 1), la.stride, 0, R)
    assert bx[0] >= r0 and bx[1] < r0 + win_rows and bx[2] >= c0 and bx[3] < c0 + win_cols
    adv = PackedAdvice(la, lb, target, scale, [], outlog)
    box = SP.InBoxTable(adv)
    half = 1 << (scale - 1)
    rounded = []
    nz = 0
    for s, Ts in enumerate(T):
        base = s * L
        r = [((v + half) >> scale) if box(base + i) else 0 for i, v in enumerate(Ts)]
        nz += sum(1 for x in r if x)
        rounded.append(r)
    adv.rounded = rounded
    # least width with every shardFits and reconFits
    w = w0
    for s in range(ns):
        logs = SP.shard_logs_list(adv, s, box)
        for x, g in zip(rounded[s], logs):
            w = max(w, (2 * ((abs(x) << scale) + (1 << g))).bit_length())
    adv = PackedAdvice(with_width(la, w), with_width(lb, w), with_width(target, w), scale, rounded, outlog)
    info = dict(zero=False, w=w, w_fit=w0, shards=ns, blockLen=L, blocks=[len(A), len(B)], scale=scale,
                pout=two2P - scale, outLog=outlog, rad_in=float(rad_in), rad_out=float(rad_out),
                target=[list(target.lo), list(target.dims)], target_slots=target.dims[0] * target.dims[1],
                advice_nonzero=nz, maxbits=[mA.bit_length(), mB.bit_length()], prodLen=plen,
                product_window=[[r0, c0], [win_rows, win_cols]])
    return adv, info


def complex_parts(fa, fb, policy="support", P=None):
    """The four real products of a complex product.  fa, fb: (keys [(k, l)], vals [int], S, ph).  Returns
    (P, [(name, entries_a, entries_b, nonzero)]) with entries at scale 2^-P (default P = max(SA, SB))."""
    (ka, va, SA, pa), (kb, vb, SB, pb) = fa, fb
    P = max(SA, SB) if P is None else P
    ea = [(tuple(k), int(v) << (P - SA)) for k, v in zip(ka, va)]
    eb = [(tuple(k), int(v) << (P - SB)) for k, v in zip(kb, vb)]
    za = [(k, 0) for k, _ in ea]
    zb = [(k, 0) for k, _ in eb]
    re_a, im_a = (ea, za) if pa == 0 else (za, ea)
    re_b, im_b = (eb, zb) if pb == 0 else (zb, eb)
    parts = [("rr", re_a, re_b), ("ii", im_a, im_b), ("ri", re_a, im_b), ("ir", im_a, re_b)]
    return P, [(nm, x, y, any(v for _, v in x) and any(v for _, v in y)) for nm, x, y in parts]


def factor_layout(entries, policy):
    """(box, skip_zero) of one real factor under the zero-part policy."""
    if policy == "minimal" and not any(v for _, v in entries):
        return ((0, 0), (1, 1)), True
    return box_of([k for k, _ in entries]), policy == "minimal"


def build_complex(fa, fb, Wt, budget, policy="support", verify=True, log=None):
    """`ProductAdvice.packed P rr ii ri ir` of a complex product, each part checked by the mirror.
    Returns (P, [(name, adv, da, db, info)])."""
    P = max(fa[2], fb[2])
    while True:
        try:
            return _build_complex_at(fa, fb, Wt, budget, policy, verify, P)
        except ValueError:
            P += 8                       # the budget is below the resolution 2^(1 - 2P): finer mantissas


def _build_complex_at(fa, fb, Wt, budget, policy, verify, P):
    P, parts = complex_parts(fa, fb, policy, P)
    out = []
    for nm, xa, xb, nonzero in parts:
        bxa, ska = factor_layout(xa, policy)
        bxb, skb = factor_layout(xb, policy)
        la, lb = layouts(bxa, bxb)
        da = SP.layout_dense(la, xa, skip_zero=ska)
        db = SP.layout_dense(lb, xb, skip_zero=skb)
        assert da is not None and db is not None
        adv, info = build_real(da, db, la, lb, P, Wt, budget if nonzero else budget * 1e-6)
        if verify:
            why = []
            ok = SP.check_packed_product(adv, da, db, why=why)
            assert ok, (nm, why)
            assert SP.check_sound_conclusion(adv, da, db), nm
            info["checked"] = True
        out.append((nm, adv, da, db, info))
    return P, out
