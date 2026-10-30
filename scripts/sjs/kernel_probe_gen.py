#!/usr/bin/env python3
"""SJS-FEAS kernel-cost probes: generators of throwaway Lean probes (written under .drafts/, never committed).

Subcommands (each writes ONE probe `.lean` and a sidecar `.json` with the sizes):

  micro  VARIANT --n N --bits B [--seed S]
      In-kernel synthetic data (no literals): `dat n B seed` is a list of n pseudo-random signed B-bit integers
      computed by the kernel itself (`rnd`). Variants (slot width w = 2B + ceil(log2 n) + 3):
        gen        forcing the data only (baseline);
        Lpack      landed `packShift w` of the list (linear accumulator);
        Lmul       landed packing of two lists and ONE big-integer product;
        Ldec       landed `intSlotsBound w (2n-1)` of that product (linear Int slot peel);
        Ppack      prototype balanced offset-Nat packing (`packBalN`, shift tree);
        Pmul       prototype packing of two lists and the product;
        Pdec       prototype divide-and-conquer mask/shift decode (`decBal`) of that product.

  packed VARIANT --dim D --shape box|diamond --K K --bits B --rows R [--seed S]
      Literal synthetic factors (S terms, keys of the box/diamond of radius K in D dimensions, random B-bit signed
      integer coefficients), the landed layout (`PackLayout`, row-major strides with no wrap), the EXACT design-B
      advice (nearest rounding at scale = B per shard window, target = whole product window), emitted as chunked
      `noncomputable def`s (<= 512 list elements per def, as the SO emitter does). Variants:
        data       data only (elaboration baseline; the theorem is `True`);
        dense      `PackLayout.dense` of both factors (spine forced);
        pack       landed `packShift` of every factor block;
        mul        landed shard sums `shardPacked` of every shard;
        full       `checkPackedProduct adv da db = true`;
        prr        `packedRealProduct` forced through the target terms and the remainder bound.

The Lean prototypes (`packBalN`, `decBal`) are measurement devices only (no soundness proof; never landed).
Untrusted tooling.
"""
import argparse
import json
import math
import os
import random
import sys
from fractions import Fraction as F

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DRAFTS = os.path.join(ROOT, ".drafts")

HEAD = """import KAM.Certificate.Poly.MulPacked
open KAM.Certificate
set_option profiler true
set_option profiler.threshold %d
"""

MICRO_DEFS = r"""
/-- pseudo-random signed `B`-bit integers computed by the kernel -/
def rnd (B seed i : Nat) : Int :=
  (((i + seed) * 6364136223846793005 + 1442695040888963407) ^ 5 % 2 ^ B : Nat) - ((2 ^ (B - 1) : Nat) : Int)

def dat (n B seed : Nat) : List Int := (List.range n).map (rnd B seed)

/-- offset digit `c + 2^(w-1)` (a natural number when `|c| ≤ 2^(w-1)`) -/
def offs (w : Nat) (c : Int) : Nat := (c + ((2 ^ (w - 1) : Nat) : Int)).toNat

/-- prototype: balanced shift-tree packing of the first `n` entries (fuel `f`) -/
def packBalN (w : Nat) : Nat → Nat → List Nat → Nat
  | 0, _, l => l.headD 0
  | f + 1, n, l => if n ≤ 1 then l.headD 0 else
      packBalN w f (n / 2) l + (packBalN w f (n - n / 2) (l.drop (n / 2)) <<< (w * (n / 2)))

/-- the packed offset `Σ_{i<n} 2^(w-1) 2^(w i)` -/
def offPack (w n : Nat) : Nat := (2 ^ (w - 1)) * (((1 <<< (w * n)) - 1) / ((1 <<< w) - 1))

/-- prototype signed packing: offset-Nat shift tree minus the packed offset -/
def packBal (w f n : Nat) (l : List Int) : Int := (packBalN w f n (l.map (offs w)) : Int) - (offPack w n : Int)

/-- prototype: divide-and-conquer mask/shift decode of the offset value `Y` into `n` slots, each
`|digit - 2^(w-1)| ≤ 2^g` (fuel `f`) -/
def decBalN (w g : Nat) : Nat → Nat → Nat → Bool
  | 0, _, Y => decide (((Y : Int) - ((2 ^ (w - 1) : Nat) : Int)).natAbs ≤ 2 ^ g)
  | f + 1, n, Y => if n ≤ 1 then decide (((Y : Int) - ((2 ^ (w - 1) : Nat) : Int)).natAbs ≤ 2 ^ g) else
      decBalN w g f (n / 2) (Y &&& ((1 <<< (w * (n / 2))) - 1)) &&
        decBalN w g f (n - n / 2) (Y >>> (w * (n / 2)))

/-- prototype decode of a signed packed value: offset, range, then the tree -/
def decBal (w g f n : Nat) (X : Int) : Bool :=
  let Y := X + (offPack w n : Int)
  decide (0 ≤ Y) && (Y.toNat >>> (w * n) == 0) && decBalN w g f n Y.toNat
"""


def clog2(n):
    return max(1, (n - 1).bit_length())


def micro(a):
    n, B, seed = a.n, a.bits, a.seed
    w = 2 * B + clog2(n) + 3
    f = clog2(n) + 2
    f2 = clog2(2 * n) + 2
    g = w - 2
    v = a.variant
    body = {
        "gen": "theorem probe : ((dat %d %d %d).foldl (· + ·) 0 != 7) = true := by decide +kernel" % (n, B, seed),
        "Lpack": "theorem probe : (packShift %d (dat %d %d %d) != 7) = true := by decide +kernel" % (w, n, B, seed),
        "Lmul": ("theorem probe : (packShift %d (dat %d %d %d) * packShift %d (dat %d %d %d) != 7) = true := by "
                 "decide +kernel") % (w, n, B, seed, w, n, B, seed + 1),
        "Ldec": ("theorem probe : intSlotsBound %d %d (fun _ => %d) (packShift %d (dat %d %d %d) * "
                 "packShift %d (dat %d %d %d)) = true := by decide +kernel")
        % (w, 2 * n - 1, g, w, n, B, seed, w, n, B, seed + 1),
        "Ppack": "theorem probe : (packBal %d %d %d (dat %d %d %d) != 7) = true := by decide +kernel"
        % (w, f, n, n, B, seed),
        "Pmul": ("theorem probe : (packBal %d %d %d (dat %d %d %d) * packBal %d %d %d (dat %d %d %d) != 7) = true := "
                 "by decide +kernel") % (w, f, n, n, B, seed, w, f, n, n, B, seed + 1),
        "Pdec": ("theorem probe : decBal %d %d %d %d (packBal %d %d %d (dat %d %d %d) * packBal %d %d %d "
                 "(dat %d %d %d)) = true := by decide +kernel")
        % (w, g, f2, 2 * n - 1, w, f, n, n, B, seed, w, f, n, n, B, seed + 1),
    }[v]
    txt = HEAD % 50 + MICRO_DEFS + "\n" + body + "\n"
    name = a.out or os.path.join(DRAFTS, "kpm_%s_n%d_b%d.lean" % (v, n, B))
    with open(name, "w") as fh:
        fh.write(txt)
    meta = dict(kind="micro", variant=v, n=n, bits=B, w=w, packed_bits=n * w, product_bits=(2 * n - 1) * w)
    with open(name[:-5] + ".json", "w") as fh:
        json.dump(meta, fh)
    print(os.path.relpath(name, ROOT))



FAST_DEFS = r"""
/-! Prototype "fixed" shard check (measurement device only; no soundness proof, never landed):
term-driven sparse block packing (pairwise shift rounds), dense offset shift-tree packing of the advice window,
one big product per block pair, and either a divide-and-conquer mask/shift slot decode (`decBal`) or a
mask-and-compare test (`maskOK`, a constant number of big-integer operations per window). -/

def offs (w : Nat) (c : Int) : Nat := (c + ((2 ^ (w - 1) : Nat) : Int)).toNat

def packBalN (w : Nat) : Nat → Nat → List Nat → Nat
  | 0, _, l => l.headD 0
  | f + 1, n, l => if n ≤ 1 then l.headD 0 else
      packBalN w f (n / 2) l + (packBalN w f (n - n / 2) (l.drop (n / 2)) <<< (w * (n / 2)))

def rep (w n : Nat) : Nat := ((1 <<< (w * n)) - 1) / ((1 <<< w) - 1)

def packBal (w f n : Nat) (l : List Int) : Int :=
  (packBalN w f n (l.map (offs w)) : Int) - ((2 ^ (w - 1) * rep w n : Nat) : Int)

def decBalN (w g : Nat) : Nat → Nat → Nat → Bool
  | 0, _, Y => decide (((Y : Int) - ((2 ^ (w - 1) : Nat) : Int)).natAbs ≤ 2 ^ g)
  | f + 1, n, Y => if n ≤ 1 then decide (((Y : Int) - ((2 ^ (w - 1) : Nat) : Int)).natAbs ≤ 2 ^ g) else
      decBalN w g f (n / 2) (Y &&& ((1 <<< (w * (n / 2))) - 1)) &&
        decBalN w g f (n - n / 2) (Y >>> (w * (n / 2)))

def decBal (w g f n : Nat) (X : Int) : Bool :=
  let Y := X + ((2 ^ (w - 1) * rep w n : Nat) : Int)
  decide (0 ≤ Y) && (Y.toNat >>> (w * n) == 0) && decBalN w g f n Y.toNat

def maskOK (w g n : Nat) (X : Int) : Bool :=
  let Y := X + ((2 ^ g * rep w n : Nat) : Int)
  decide (0 ≤ Y) && (Y.toNat >>> (w * n) == 0) &&
    (Y.toNat &&& (((1 <<< w) - (1 <<< (g + 2))) * rep w n) == 0)

def pairUp (w : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | a :: b :: rest => (a.1, a.2 + (b.2 <<< (w * (b.1 - a.1)))) :: pairUp w rest
  | l => l

def roundsUp (w : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, l => l
  | r + 1, l => match l with
    | [] => []
    | [a] => [a]
    | _ => roundsUp w r (pairUp w l)

def packSp (w base : Nat) (l : List (Nat × Nat)) : Nat :=
  match roundsUp w 48 l with
  | (s, v) :: _ => v <<< (w * (s - base))
  | [] => 0

def packSpI (w base : Nat) (l : List (Nat × Int)) : Int :=
  (packSp w base (l.filterMap fun t => if 0 ≤ t.2 then some (t.1, t.2.toNat) else none) : Int) -
    (packSp w base (l.filterMap fun t => if t.2 < 0 then some (t.1, (-t.2).toNat) else none) : Int)

def slotted (lay : PackLayout) (ts : List (List Int × Int)) : List (Nat × Int) :=
  ts.filterMap fun t => (packSlotAux t.1 lay.lo lay.dims lay.stride).map fun p => (p, t.2)

def splitBlocks (L : Nat) : Nat → Nat → List (Nat × Int) → List (List (Nat × Int))
  | 0, _, _ => []
  | f + 1, b, l => (l.takeWhile fun t => t.1 < (b + 1) * L) ::
      splitBlocks L f (b + 1) (l.dropWhile fun t => t.1 < (b + 1) * L)

def blockPacks (w L nb : Nat) (l : List (Nat × Int)) : List Int :=
  ((splitBlocks L nb 0 l).zip (List.range nb)).map fun p => packSpI w (p.2 * L) p.1

def shardX (w sc f n : Nat) (PA PB : List Int) (R : List (List Int)) (s : Nat) : Int :=
  ((List.range (s + 1)).map fun i => PA.getD i 0 * PB.getD (s - i) 0).sum -
    ((2 ^ sc : Nat) : Int) * packBal w f n (R.getD s [])
"""

# ------------------------------------------------------------------------------------------------ literal data
CHUNK = 512          # list elements per `def` (the SO emitter's chunk; the elaborator fails near 4096)
GROUP = 16           # chunks joined per right-nested append group
TCHUNK = 128         # (key, coefficient) terms per `def` (512 terms exceed the default heartbeats)


def lit(v):
    """an `Int` literal in constructor form (`Int.ofNat n` / `Int.negSucc n`): 5x cheaper to elaborate than
    `-0x...` (no `Neg`/`OfNat` instance problems; measured 0.18 vs 0.9 ms per 200-bit element)."""
    return ("Int.negSucc %d" % (-v - 1)) if v < 0 else ("Int.ofNat %d" % v)


def wrap(items, indent="  ", cols=100):
    lines, cur = [], indent
    for k, it in enumerate(items):
        piece = it + ("," if k + 1 < len(items) else "")
        if len(cur) + len(piece) + 1 > cols and cur.strip():
            lines.append(cur.rstrip())
            cur = indent
        cur += piece + " "
    if cur.strip():
        lines.append(cur.rstrip())
    return lines


def emit_list(out, name, typ, items, chunk=CHUNK):
    """`name : typ` as chunk defs of <= chunk items joined by right-nested appends (groups of GROUP)."""
    chunks = [items[i:i + chunk] for i in range(0, len(items), chunk)] or [[]]
    names = []
    for c, ch in enumerate(chunks):
        nm = "%s_c%d" % (name, c)
        names.append(nm)
        if ch:
            out.append("noncomputable def %s : %s := [" % (nm, typ))
            body = wrap(ch)
            body[-1] += "]"
            out.extend(body)
        else:
            out.append("noncomputable def %s : %s := []" % (nm, typ))
    level = 0
    while len(names) > 1:
        grouped = []
        for g in range(0, len(names), GROUP):
            part = names[g:g + GROUP]
            nm = "%s_g%d_%d" % (name, level, g // GROUP)
            expr = part[-1]
            for p in reversed(part[:-1]):
                expr = "%s ++ (%s)" % (p, expr)
            out.append("noncomputable def %s : %s := %s" % (nm, typ, expr))
            grouped.append(nm)
        names = grouped
        level += 1
    out.append("noncomputable def %s : %s := %s" % (name, typ, names[0]))


def emit_listlist(out, name, rows, elem_typ="Int"):
    """`name : List (List elem)`: every row an `unzero`-coded list (emit_list), rows joined <= 64 per literal."""
    rnames = []
    for r, row in enumerate(rows):
        toks = rle_tokens(row)
        nm = "%s_r%d" % (name, r)
        emit_list(out, nm + "t", "List %s" % elem_typ, [lit(t) for t in toks])
        out.append("noncomputable def %s : List %s := unzero %st" % (nm, elem_typ, nm))
        rnames.append(nm)
    groups = []
    for g in range(0, len(rnames), 64):
        nm = "%s_h%d" % (name, g // 64)
        out.append("noncomputable def %s : List (List %s) := [%s]" % (nm, elem_typ, ", ".join(rnames[g:g + 64])))
        groups.append(nm)
    expr = groups[-1] if groups else "[]"
    for p in reversed(groups[:-1]):
        expr = "%s ++ (%s)" % (p, expr)
    out.append("noncomputable def %s : List (List %s) := %s" % (name, elem_typ, expr))


def rle_tokens(full):
    toks, i, n = [], 0, len(full)
    while i < n:
        if full[i] == 0:
            j = i
            while j < n and full[j] == 0:
                j += 1
            toks += [0, j - i]
            i = j
        else:
            toks.append(full[i])
            i += 1
    return toks


UNZERO = r"""
/-- run-length decoder of advice windows (a zero is followed by its run length; the SO data format) -/
def unzero : List Int → List Int
  | [] => []
  | 0 :: n :: t => List.replicate n.toNat 0 ++ unzero t
  | v :: t => v :: unzero t
"""


# ------------------------------------------------------------------------------------------------ packed products
def support(dim, shape, K):
    import itertools
    keys = []
    for k in itertools.product(range(-K, K + 1), repeat=dim):
        if shape == "box" or sum(abs(x) for x in k) <= K:
            keys.append(k)
    return keys          # lexicographic = slot order (row-major, lo = -K)


def pack_sum(w, cs):
    n = len(cs)
    if n == 0:
        return 0
    if n <= 32:
        x = 0
        for c in reversed(cs):
            x = (x << w) + c
        return x
    h = n // 2
    return pack_sum(w, cs[:h]) + (pack_sum(w, cs[h:]) << (w * h))


def udigits(Y, w, n):
    if n <= 64:
        mask = (1 << w) - 1
        out = []
        for _ in range(n):
            out.append(Y & mask)
            Y >>= w
        return out
    h = n // 2
    return udigits(Y & ((1 << (w * h)) - 1), w, h) + udigits(Y >> (w * h), w, n - h)


def balanced_digits(w, n, X):
    half = 1 << (w - 1)
    Y = X + pack_sum(w, [half] * n)
    assert 0 <= Y < (1 << (w * n))
    return [u - half for u in udigits(Y, w, n)]


def packed_case(dim, shape, K, B, R, seed):
    rng = random.Random(seed)
    keys = support(dim, shape, K)
    S = len(keys)
    ta = [(k, rng.randrange(-(1 << B) + 1, 1 << B)) for k in keys]
    tb = [(k, rng.randrange(-(1 << B) + 1, 1 << B)) for k in keys]
    dims = [2 * K + 1] * dim
    ext = [4 * K + 1] * dim
    st = [1] * dim
    for j in range(dim - 2, -1, -1):
        st[j] = st[j + 1] * ext[j + 1]
    dlen = 1 + sum((d - 1) * s for d, s in zip(dims, st))

    def slot(k):
        return sum((x + K) * s for x, s in zip(k, st))
    da, db = [0] * dlen, [0] * dlen
    for k, c in ta:
        da[slot(k)] = c
    for k, c in tb:
        db[slot(k)] = c
    L = R * st[0]
    cut = lambda d: [d[i:i + L] + [0] * (L - len(d[i:i + L])) for i in range(0, len(d), L)]
    Ab, Bb = cut(da), cut(db)
    na, nb = len(Ab), len(Bb)
    ns = na + nb - 1
    plen = 2 * dlen - 1
    mA = [max(abs(c) for c in x) for x in Ab]
    mB = [max(abs(c) for c in x) for x in Bb]
    w0 = (2 * ns * L * max(mA) * max(mB)).bit_length() + 2
    PA = [pack_sum(w0, x) for x in Ab]
    PB = [pack_sum(w0, x) for x in Bb]
    scale = B
    half = 1 << (scale - 1)
    rounded = []
    wneed = 1
    runA = runB = 0
    for s in range(ns):
        X = 0
        for i in range(max(0, s - nb + 1), min(na, s + 1)):
            X += PA[i] * PB[s - i]
        T = balanced_digits(w0, 2 * L - 1, X)
        r = [((v + half) >> scale) if (s * L + i < plen) else 0 for i, v in enumerate(T)]
        for i, (v, c) in enumerate(zip(T, r)):
            res = v - (c << scale)
            g = scale - 1 if s * L + i < plen else 0
            assert abs(res) <= (1 << g), (s, i, v, c)
            wneed = max(wneed, (2 * ((abs(c) << scale) + (1 << g))).bit_length() + 1)
        rounded.append(r)
        if s < na:
            runA = max(runA, mA[s])
        if s < nb:
            runB = max(runB, mB[s])
        wneed = max(wneed, (2 * (s + 1) * L * runA * runB).bit_length() + 1)
    w = wneed
    info = dict(dim=dim, shape=shape, K=K, bits=B, rows=R, S=S, denseLen=dlen, prodLen=plen, blockLen=L,
                blocks=[na, nb], shards=ns, w=w, scale=scale, stride=st,
                factor_bits=dlen * w, window_bits=(2 * L - 1) * w, block_bits=L * w,
                pairs=na * nb, advice_slots=ns * (2 * L - 1),
                advice_nonzero=sum(1 for r in rounded for c in r if c),
                prod_nonzero_est=None)
    return dict(ta=ta, tb=tb, dims=dims, st=st, K=K, w=w, R=R, scale=scale, rounded=rounded, prodext=ext,
                info=info, da=da, db=db)


WEIGHT = "⟨1 / 70, 1093911494604498852667681312417 / 1000000000000000000000000000000⟩"


def remainder_float(case, P2):
    """log2 of the landed remainderBound (float estimate) for the probe's weight."""
    K, dim = case["K"], len(case["dims"])
    lw = math.log2(1093911494604498852667681312417 / 1e30)
    tot = 0.0
    import itertools
    for k in itertools.product(range(-2 * K, 2 * K + 1), repeat=dim):
        tot += 2.0 ** (case["scale"] + lw * sum(abs(x) for x in k))
    return math.log2(tot) - P2


def packed(a):
    case = packed_case(a.dim, a.shape, a.K, a.bits, a.rows, a.seed)
    info = case["info"]
    if a.perturb:                       # negative control: one in-box advice slot off by +2
        s0 = info["shards"] // 2
        case["rounded"][s0][info["blockLen"] // 2] += 2
        info["perturbed"] = True
    K, dim, w, R = case["K"], len(case["dims"]), case["w"], case["R"]
    lo = ", ".join(["-%d" % K] * dim)
    plo = ", ".join(["-%d" % (2 * K)] * dim)
    st = ", ".join(map(str, case["st"]))
    out = [HEAD % 100, UNZERO]
    if a.variant.startswith("F"):
        out.append(FAST_DEFS)
    out.append("noncomputable def layA : PackLayout := ⟨[%s], [%s], [%s], %d, %d⟩" % (
        lo, ", ".join(map(str, case["dims"])), st, w, R))
    out.append("noncomputable def layT : PackLayout := ⟨[%s], [%s], [%s], %d, %d⟩" % (
        plo, ", ".join(map(str, case["prodext"])), st, w, R))

    def term(t):
        return "([%s], %s)" % (", ".join(lit(x) for x in t[0]), lit(t[1]))
    emit_list(out, "tA", "List (List Int × Int)", [term(t) for t in case["ta"]], TCHUNK)
    emit_list(out, "tB", "List (List Int × Int)", [term(t) for t in case["tb"]], TCHUNK)
    v = a.variant
    if v not in ("data", "dense", "Fpack", "Fmul"):
        rows = case["rounded"]
        if v in ("Fshard", "Lshard"):          # only the middle window is read; the others are empty
            rows = [r if i == info["shards"] // 2 else [] for i, r in enumerate(rows)]
        emit_listlist(out, "advR", rows)
        out.append("noncomputable def adv : PackedAdvice := ⟨layA, layA, layT, %d, advR, 0⟩" % case["scale"])
    out.append("noncomputable def da : List Int := (layA.dense tA).getD []")
    out.append("noncomputable def db : List Int := (layA.dense tB).getD []")
    ns = info["shards"]
    s0 = ns // 2
    L, (na, nb), sc = info["blockLen"], info["blocks"], case["scale"]
    fw = clog2(2 * L) + 2
    P2 = 2 * a.bits + 64
    body = {
        "data": "theorem probe : True := trivial",
        "dense": ("theorem probe : (da.length == %d && db.length == %d) = true := by decide +kernel"
                  % (info["denseLen"], info["denseLen"])),
        "pack": "theorem probe : ((adv.cut da).all fun x => packShift %d x != 7) = true := by decide +kernel" % w,
        "mul": ("theorem probe : ((List.range %d).all fun s => shardPacked %d (adv.cut da) (adv.cut db) s != 7) = "
                "true := by decide +kernel") % (ns, w),
        "full": "theorem probe : checkPackedProduct adv da db = true := by decide +kernel",
        "shape": "theorem probe : adv.shapeOK = true := by decide +kernel",
        "guards": ("theorem probe : ((List.range %d).all fun s => (adv.cut da).all (fun x => packLenEq x adv.blockLen) &&\n"
                   "    (adv.cut db).all (fun x => packLenEq x adv.blockLen) &&\n"
                   "    packLenEq (adv.rounded.getD s []) (2 * adv.blockLen - 1) &&\n"
                   "    shardFits adv.la.width adv.blockLen (adv.cut da) (adv.cut db) s &&\n"
                   "    reconFitsAux adv.la.width adv.scale (adv.shardLogs s) 0 (adv.rounded.getD s [])) = true := by\n"
                   "  decide +kernel") % ns,
        "decode": ("theorem probe : ((List.range %d).all fun s => intSlotsBound adv.la.width (2 * adv.blockLen - 1)\n"
                   "    (adv.shardLogs s) (shardPacked adv.la.width (adv.cut da) (adv.cut db) s -\n"
                   "      ((2 ^ adv.scale : Nat) : Int) * packShift adv.la.width (adv.rounded.getD s []))) = true := by\n"
                   "  decide +kernel") % ns,
        "Fpack": ("theorem probe : ((blockPacks %d %d %d (slotted layA tA)).all (· != 7) &&\n"
                  "    (blockPacks %d %d %d (slotted layA tB)).all (· != 7)) = true := by decide +kernel")
        % (w, L, na, w, L, nb),
        "Fmul": ("theorem probe : (let PA := blockPacks %d %d %d (slotted layA tA)\n"
                 "  let PB := blockPacks %d %d %d (slotted layA tB)\n"
                 "  (List.range %d).all fun s => ((List.range (s + 1)).map fun i => PA.getD i 0 * PB.getD (s - i) 0).sum"
                 " != 7) = true := by decide +kernel") % (w, L, na, w, L, nb, ns),
        "Fdec": ("theorem probe : (let PA := blockPacks %d %d %d (slotted layA tA)\n"
                 "  let PB := blockPacks %d %d %d (slotted layA tB)\n"
                 "  (List.range %d).all fun s => decBal %d %d %d %d (shardX %d %d %d %d PA PB advR s)) = true := by\n"
                 "  decide +kernel") % (w, L, na, w, L, nb, ns, w, sc - 1, fw, 2 * L - 1, w, sc, fw, 2 * L - 1),
        "Fmask": ("theorem probe : (let PA := blockPacks %d %d %d (slotted layA tA)\n"
                  "  let PB := blockPacks %d %d %d (slotted layA tB)\n"
                  "  (List.range %d).all fun s => maskOK %d %d %d (shardX %d %d %d %d PA PB advR s)) = true := by\n"
                  "  decide +kernel") % (w, L, na, w, L, nb, ns, w, sc - 1, 2 * L - 1, w, sc, fw, 2 * L - 1),
        "Fshard": ("theorem probe : (let PA := blockPacks %d %d %d (slotted layA tA)\n"
                   "  let PB := blockPacks %d %d %d (slotted layA tB)\n"
                   "  decBal %d %d %d %d (shardX %d %d %d %d PA PB advR %d)) = true := by\n"
                   "  decide +kernel") % (w, L, na, w, L, nb, w, sc - 1, fw, 2 * L - 1, w, sc, fw, 2 * L - 1, s0),
        "Lshard": "theorem probe : checkShard adv (adv.cut da) (adv.cut db) %d = true := by decide +kernel" % s0,
        "Fadv": ("theorem probe : ((List.range %d).all fun s => packBal %d %d %d (advR.getD s []) != 7) = true := by\n"
                 "  decide +kernel") % (ns, w, fw, 2 * L - 1),
        "fits": ("theorem probe : ((List.range %d).all fun s =>\n"
                 "    shardFits adv.la.width adv.blockLen (adv.cut da) (adv.cut db) s) = true := by decide +kernel") % ns,
        "prr": ("theorem probe : (match packedRealProduct adv %s %d tA tB with\n"
                "    | some (ts, r) => ts.length != 0 && decide (r ≤ 1)\n"
                "    | none => false) = true := by decide +kernel") % (WEIGHT, P2),
    }[v]
    if v == "prr":
        lr = remainder_float(case, P2)
        assert lr < -1, lr
        info["log2_remainder"] = lr
    out.append(body)
    txt = "\n".join(out) + "\n"
    name = a.out or os.path.join(DRAFTS, "kpp_%s_d%d%s_K%d_b%d_r%d.lean" % (v, dim, a.shape[0], K, a.bits, R))
    with open(name, "w") as fh:
        fh.write(txt)
    info.update(kind="packed", variant=v, bytes=len(txt))
    with open(name[:-5] + ".json", "w") as fh:
        json.dump(info, fh)
    print(os.path.relpath(name, ROOT))



# ------------------------------------------------------------------------------------------------ model passes
MODEL_HEAD = """import KAM.Certificate.Model.Ops
import KAM.CertificateSharp.Corner.SupBound
open KAM.Certificate KAM.CertificateSharp CertArith
set_option profiler true
set_option profiler.threshold 100
"""
PE = "⟨⟨6710401180212168915155840974220003240804194089427148950727106424351713218671805380099500388914039⟩, ⟨5⟩, 72, 21⟩"


def model(a):
    rng = random.Random(a.seed)
    keys = support(a.dim, a.shape, a.K)
    S = len(keys)
    P = a.prec
    Wt = WEIGHT if a.weight == "prod" else "⟨1 / 100, 11 / 10⟩"
    out = [MODEL_HEAD]
    out.append("abbrev Fx := CertFixed %d" % P)
    out.append("noncomputable def W : CertWeight := %s" % Wt)
    out.append("noncomputable def pe : PiEnclosure Fx := %s" % PE)

    def coef():
        return rng.randrange(-(1 << (P - 2)), 1 << (P - 2))

    def term(k, re, im):
        return "([%s], ⟨⟨%s⟩, ⟨%s⟩⟩)" % (", ".join(lit(x) for x in k), lit(re), lit(im))
    emit_list(out, "pA", "List (List Int × CC Fx)", [term(k, coef(), 0) for k in keys], TCHUNK)
    v = a.variant
    if v in ("add",):
        emit_list(out, "pB", "List (List Int × CC Fx)", [term(k, coef(), 0) for k in keys], TCHUNK)
    out.append("noncomputable def mA : CertModel Fx := ⟨0, ⟨pA⟩, ofInt 0⟩")
    if v == "add":
        out.append("noncomputable def mB : CertModel Fx := ⟨0, ⟨pB⟩, ofInt 0⟩")
    body = {
        "data": "theorem probe : True := trivial",
        "length": "theorem probe : (pA.length != 7) = true := by decide +kernel",
        "wnorm": "theorem probe : ((CertPoly.weightedNormUp W ⟨pA⟩ : Fx).m != 7) = true := by decide +kernel",
        "supnorm": "theorem probe : ((CertPoly.supNormUp W ⟨pA⟩ : Fx).m != 7) = true := by decide +kernel",
        "corner": ("theorem probe : cornerLeq W (wloOf W 30) %d mA (ofInt (10 ^ 80)) = true := by decide +kernel"
                   % a.dim),
        "add": ("theorem probe : (let m := CertModel.add W mA mB\n"
                "  m.poly.terms.length != 7 && m.rad.m != 7) = true := by decide +kernel"),
        "todeg": ("theorem probe : (let m := CertModel.toDeg W pe 1 mA\n"
                  "  m.poly.terms.length != 7 && m.rad.m != 7) = true := by decide +kernel"),
        "mants": ("theorem probe : (CertPoly.toMants (CertFixed.toMant %d) %d ⟨pA⟩).isSome = true := by "
                  "decide +kernel") % (P, P),
    }[v]
    out.append(body)
    txt = "\n".join(out) + "\n"
    name = a.out or os.path.join(DRAFTS, "kpo_%s_d%d%s_K%d_P%d_%s.lean" % (v, a.dim, a.shape[0], a.K, P, a.weight))
    with open(name, "w") as fh:
        fh.write(txt)
    info = dict(kind="model", variant=v, dim=a.dim, shape=a.shape, K=a.K, S=S, prec=P, weight=a.weight,
                bytes=len(txt))
    with open(name[:-5] + ".json", "w") as fh:
        json.dump(info, fh)
    print(os.path.relpath(name, ROOT))


# ------------------------------------------------------------------------------------------------ compose
COMPOSE_HEAD = """import KAM.Certificate.Expr.Compose
open KAM.Certificate CertArith
set_option profiler true
set_option profiler.threshold 100

/-! C7 pruning (copied verbatim from sharp-c7 `KAM/CertificateSharp/Kernel/Prune.lean`, definitions only). -/
namespace C7
def opDeps : SlpOp → List ℕ
  | .add a b => [a, b]
  | .mul a b => [a, b]
  | .exp a => [a]
  | .inv a => [a]
  | _ => []
def nopOp : SlpOp := .const 0 0 0
def liveStep (ops : List SlpOp) (S : List ℕ) (k : ℕ) : List ℕ :=
  if S.contains k then ((opDeps (ops.getD k nopOp)).filter fun j => !S.contains j) ++ S else S
def liveSet (ops : List SlpOp) (wanted : List ℕ) : List ℕ :=
  (List.range ops.length).reverse.foldl (liveStep ops) wanted
def liveClosed (ops : List SlpOp) (S : List ℕ) : Bool :=
  (List.range ops.length).all fun i =>
    !S.contains i || (opDeps (ops.getD i nopOp)).all fun j => decide (i ≤ j) || S.contains j
def pruneOps (ops : List SlpOp) (S : List ℕ) : List SlpOp :=
  (List.range ops.length).map fun i => if S.contains i then ops.getD i nopOp else nopOp
def pruneOk (ops : List SlpOp) (wanted S : List ℕ) : Bool :=
  liveClosed ops S && wanted.all fun i => S.contains i
def keepFlagged {β : Type} (l : List β) (flags : List Bool) : List β :=
  (l.zip flags).filterMap fun x => if x.2 then some x.1 else none
def expFlags (ops : List SlpOp) (S : List ℕ) : List Bool :=
  (List.range ops.length).filterMap fun i =>
    match ops.getD i nopOp with
    | .exp _ => some (S.contains i)
    | _ => none
def invFlags (ops : List SlpOp) (S : List ℕ) : List Bool :=
  (List.range ops.length).filterMap fun i =>
    match ops.getD i nopOp with
    | .inv _ => some (S.contains i)
    | _ => none
def prune {α : Type} (p : Slp) (wit : Witnesses α) (wanted : List ℕ) : Slp × Witnesses α :=
  let S := liveSet p.ops wanted
  if pruneOk p.ops wanted S then
    (⟨pruneOps p.ops S⟩, ⟨keepFlagged wit.expWit (expFlags p.ops S),
      keepFlagged wit.invWit (invFlags p.ops S), wit.charWit⟩)
  else (p, wit)
def composePruned {α : Type} [CertArith α] (n : ℕ) (p : Slp) (K : CertEmbedding α)
    (wit : Witnesses α) (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α)
    (wanted : List ℕ) : Option (List (CertModel α)) :=
  match prune p wit wanted with
  | (p', wit') => Slp.compose n p' K wit' W cfg pe wanted
end C7
"""


def synth_program(Ls, Le, Li, Ld):
    """slots: 0 const 0, 1 action 0, 2 action 1, 3 const 1/3, 4 const 2/7; a shared chain of Ls steps, then
    branches E (Le steps), I (Li steps) and a dead branch D (Ld steps) from the chain end. One step from x:
    y = mul(3, x); x' = add(y, 1) (two model ops: a scalar product and a sorted merge)."""
    ops = [("C", "0"), ("A", 0), ("A", 1), ("C", "1 / 3"), ("C", "2 / 7")]

    def step(x, c):
        ops.append(("M", c, x))
        ops.append(("+", len(ops) - 1, 1 if c == 3 else 2))
        return len(ops) - 1
    x = 2
    for _ in range(Ls):
        x = step(x, 3)
    shared = x
    e = shared
    for _ in range(Le):
        e = step(e, 4)
    i = shared
    for _ in range(Li):
        i = step(i, 3)
    d = shared
    for _ in range(Ld):
        d = step(d, 4)
    return ops, e, i, d


def op_lean(o):
    if o[0] == "C":
        return ".const (%s) 0 0" % o[1]
    if o[0] == "A":
        return ".action %d" % o[1]
    if o[0] == "M":
        return ".mul %d %d" % (o[1], o[2])
    return ".add %d %d" % (o[1], o[2])


def compose(a):
    rng = random.Random(a.seed)
    P = a.prec
    K = a.K
    half = [k for k in support(2, "box", K) if k > (0, 0)]       # lexicographically positive, ascending
    S = 2 * len(half) + 1
    out = [COMPOSE_HEAD]
    out.append("abbrev Fx := CertFixed %d" % P)
    out.append("noncomputable def W : CertWeight := %s" % WEIGHT)
    out.append("noncomputable def pe : PiEnclosure Fx := %s" % PE)
    out.append("noncomputable def cfg : ModelConfig Fx := ⟨100000, 30, 12, CertFixed.toMant %d, []⟩" % P)

    def coef():
        return rng.randrange(-(1 << (P - 8)), 1 << (P - 8))

    def term(k):
        return "([%s], ⟨⟨%s⟩, ⟨%s⟩⟩)" % (", ".join(lit(x) for x in k), lit(coef()), lit(coef()))
    emit_list(out, "h0", "List (List Int × CC Fx)", [term(k) for k in half], TCHUNK)
    emit_list(out, "h1", "List (List Int × CC Fx)", [term(k) for k in half], TCHUNK)
    out.append("noncomputable def K : CertEmbedding Fx := ⟨[0, 0], [], [0, 0], [⟨⟨%s⟩, h0⟩, ⟨⟨%s⟩, h1⟩]⟩"
               % (lit(coef()), lit(coef())))
    out.append("noncomputable def wit : Witnesses Fx := ⟨[], [], []⟩")
    ops, e, i, d = synth_program(a.Ls, a.Le, a.Li, a.Ld)
    out.append("noncomputable def prog : Slp := ⟨[%s]⟩" % ",\n  ".join(op_lean(o) for o in ops))
    out.append("noncomputable def force (r : Option (List (CertModel Fx))) : Bool :=\n"
               "  match r with\n  | some ms => ms.all fun m => m.rad.m != 7 && m.poly.terms.length != 7\n"
               "  | none => false")
    cE = "force (Slp.compose 2 prog K wit W cfg pe [%d])" % e
    cI = "force (Slp.compose 2 prog K wit W cfg pe [%d])" % i
    v = a.variant
    body = {
        "data": "theorem probe : True := trivial",
        "E": "theorem probe : %s = true := by decide +kernel" % cE,
        "I": "theorem probe : %s = true := by decide +kernel" % cI,
        "EI": "theorem probe : (%s && %s) = true := by decide +kernel" % (cE, cI),
        "shared": "theorem probe : force (Slp.compose 2 prog K wit W cfg pe [%d, %d]) = true := by decide +kernel"
        % (e, i),
        "pruned": ("theorem probe : force (C7.composePruned 2 prog K wit W cfg pe [%d, %d]) = true := by "
                   "decide +kernel") % (e, i),
        "all": ("theorem probe : force (Slp.compose 2 prog K wit W cfg pe (List.range %d)) = true := by "
                "decide +kernel") % len(ops),
        "pruneonly": ("theorem probe : (C7.liveSet prog.ops [%d, %d]).length != 7 && C7.pruneOk prog.ops [%d, %d] "
                      "(C7.liveSet prog.ops [%d, %d]) = true := by decide +kernel") % (e, i, e, i, e, i),
    }[v]
    out.append(body)
    txt = "\n".join(out) + "\n"
    name = a.out or os.path.join(DRAFTS, "kpc_%s_K%d_P%d_%d_%d_%d_%d.lean" % (v, K, P, a.Ls, a.Le, a.Li, a.Ld))
    with open(name, "w") as fh:
        fh.write(txt)
    info = dict(kind="compose", variant=v, K=K, S=S, prec=P, Ls=a.Ls, Le=a.Le, Li=a.Li, Ld=a.Ld,
                ops=len(ops), slots=dict(E=e, I=i, D=d), bytes=len(txt))
    with open(name[:-5] + ".json", "w") as fh:
        json.dump(info, fh)
    print(os.path.relpath(name, ROOT))


# ------------------------------------------------------------------------------------------------ pruning cost
def prune_probe(a):
    """C7 `liveSet` + `pruneOk` on a planetary-type jet program (scripts/sjs/jet_counts.py), no models."""
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import jet_counts
    import adv_jet
    if a.which == "lunar":
        _, J, *_ = adv_jet.report()
    else:
        e, _ = jet_counts.planetary(a.M)
        J = adv_jet.jet(4, e)
    prog = J["prog"]

    def q(x):
        x = F(x)
        return "(%d / %d)" % (x.numerator, x.denominator) if x.denominator != 1 else "(%d)" % x.numerator

    def op(o):
        t = o[0]
        if t == "const":
            return ".const %s %s %d" % (q(o[1]), q(o[2]), o[3])
        if t == "action":
            return ".action %d" % o[1]
        if t == "char":
            return ".char [%s]" % ", ".join(str(x) for x in o[1])
        return ".%s %d %d" % (t, o[1], o[2])
    wanted = [J["v0"]] + [x for x in J["d1"] if x]
    out = [COMPOSE_HEAD]
    emit_list(out, "ops", "List SlpOp", [op(o) for o in prog], 256)
    out.append("theorem probe : (C7.pruneOk ops [%s] (C7.liveSet ops [%s])) = true := by decide +kernel"
               % (", ".join(map(str, wanted)), ", ".join(map(str, wanted))))
    txt = "\n".join(out) + "\n"
    name = a.out or os.path.join(DRAFTS, "kpr_%s_M%d.lean" % (a.which, a.M))
    with open(name, "w") as fh:
        fh.write(txt)
    info = dict(kind="prune", which=a.which, M=a.M, ops=len(prog), wanted=len(wanted),
                live=len(adv_jet.closure(prog, wanted)))
    with open(name[:-5] + ".json", "w") as fh:
        json.dump(info, fh)
    print(os.path.relpath(name, ROOT))


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    m = sub.add_parser("micro")
    m.add_argument("variant")
    m.add_argument("--n", type=int, required=True)
    m.add_argument("--bits", type=int, default=200)
    m.add_argument("--seed", type=int, default=1)
    m.add_argument("--out", default=None)
    p = sub.add_parser("packed")
    p.add_argument("variant")
    p.add_argument("--dim", type=int, default=2)
    p.add_argument("--shape", default="box")
    p.add_argument("--K", type=int, required=True)
    p.add_argument("--bits", type=int, default=200)
    p.add_argument("--rows", type=int, default=1)
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--out", default=None)
    p.add_argument("--perturb", action="store_true")
    o = sub.add_parser("model")
    o.add_argument("variant")
    o.add_argument("--dim", type=int, default=2)
    o.add_argument("--shape", default="box")
    o.add_argument("--K", type=int, required=True)
    o.add_argument("--prec", type=int, default=300)
    o.add_argument("--weight", default="prod")
    o.add_argument("--seed", type=int, default=1)
    o.add_argument("--out", default=None)
    c = sub.add_parser("compose")
    c.add_argument("variant")
    c.add_argument("--K", type=int, required=True)
    c.add_argument("--prec", type=int, default=300)
    c.add_argument("--Ls", type=int, default=3)
    c.add_argument("--Le", type=int, default=1)
    c.add_argument("--Li", type=int, default=1)
    c.add_argument("--Ld", type=int, default=3)
    c.add_argument("--seed", type=int, default=1)
    c.add_argument("--out", default=None)
    r = sub.add_parser("prune")
    r.add_argument("--which", default="planetary")
    r.add_argument("--M", type=int, default=4)
    r.add_argument("--out", default=None)
    a = ap.parse_args()
    if a.cmd == "prune":
        prune_probe(a)
    if a.cmd == "compose":
        compose(a)
    if a.cmd == "model":
        model(a)
    if a.cmd == "micro":
        micro(a)
    elif a.cmd == "packed":
        packed(a)


if __name__ == "__main__":
    main()
