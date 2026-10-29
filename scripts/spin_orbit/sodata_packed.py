#!/usr/bin/env python3
r"""SO-DATA-PY: a Python mirror of the advice-checked packed products of design Revision 7 (A-E §B').

Every function here mirrors ONE declaration of `.drafts/design/SOSignatures.lean` (§B') under the same name
(snake case).  Where the Lean body is still `sorry` (SO-POLY-B), the docstring of the signature is followed and the
concrete reading chosen here is stated in the function's docstring ("PROPOSED BODY"); the report
docs/tracks/SO/studies/SO-DATA-PY.md collects these readings so that SO-POLY-B can adopt them (or the generator
can follow SO-POLY-B's choices, which are isolated in this one file).  Where the Lean body is LANDED
(`KAM/Certificate/Poly/Packed.lean`: `packSum`, `packShift`, `listConv`, `maxAbs`, `slotRep`, `intSlotsBound`)
the mirror is literal; a fast but equivalent implementation is used for the big cases and is tested against the
literal one (sodata_test.py).

Data conventions (as in Lean): a `PackLayout` is (lo, dims, stride, width, blockRows), a `PackedAdvice` is
(la, lb, target, scale, rounded, outLog); keys are tuples of ints; every list is a Python list of ints.
Untrusted tooling.
"""
from dataclasses import dataclass, field
from typing import List, Optional, Tuple

Key = Tuple[int, ...]


# ------------------------------------------------------------------------------------------ landed (SO-POLY-A)
def pack_sum(w: int, cs: List[int]) -> int:
    """`packSum w cs = Σ_i cs_i 2^(w i)` (divide and conquer; exact)."""
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


def pack_shift(w: int, cs: List[int]) -> int:
    """`packShift` (kernel packing by shifts); equal to `packSum` (`packShift_eq`, landed)."""
    return pack_sum(w, cs)


def list_conv(a: List[int], b: List[int]) -> List[int]:
    """`listConv a b` (empty if a factor is empty), by the literal double loop.  For small inputs only."""
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def max_abs(cs: List[int]) -> int:
    """`maxAbs` (landed): the largest |c| (0 on the empty list)."""
    return max((abs(c) for c in cs), default=0)


def slot_rep(m: int, r: int) -> int:
    """`slotRep m r = if 2 r < m then r else r - m` (landed)."""
    return r if 2 * r < m else r - m


def int_slots_bound_literal(w: int, length: int, logs, X: int) -> bool:
    """`intSlotsBound w len logs X`, LITERALLY the landed loop `intSlotsBoundAux` (quadratic; tests only).
    Lean's `Int.emod` / `Int.ediv` (`%`, `/` on ℤ with positive divisor) agree with Python's `%`, `//` here."""
    m = 1 << w
    for i in range(length):
        e = slot_rep(m, X % m)
        if not abs(e) <= (1 << logs(i)):
            return False
        X = (X - e) // m
    return X == 0


def _udigits(Y: int, w: int, n: int) -> List[int]:
    """the n unsigned base-2^w digits of 0 <= Y < 2^(w n) (divide and conquer)."""
    if n <= 64:
        mask = (1 << w) - 1
        out = []
        for _ in range(n):
            out.append(Y & mask)
            Y >>= w
        return out
    h = n // 2
    return _udigits(Y & ((1 << (w * h)) - 1), w, h) + _udigits(Y >> (w * h), w, n - h)


def balanced_digits(w: int, length: int, X: int) -> Optional[List[int]]:
    """The digits e_0..e_{len-1} the landed loop computes (balanced, in [-2^(w-1), 2^(w-1))), or None when the
    loop's final remainder is nonzero.  Equivalent to the loop: X = Σ e_i m^i + m^len X_rest with balanced e_i is
    unique, and the loop peels exactly these digits (tested against `int_slots_bound_literal`)."""
    if w == 0:
        return [0] * length if X == 0 else None
    half = 1 << (w - 1)
    H = pack_sum(w, [half] * length)
    Y = X + H
    if Y < 0 or Y >> (w * length):
        return None
    return [u - half for u in _udigits(Y, w, length)]


def int_slots_bound(w: int, length: int, logs, X: int) -> bool:
    """`intSlotsBound w len logs X` (fast equivalent of the landed loop)."""
    e = balanced_digits(w, length, X)
    if e is None:
        return False
    return all(abs(x) <= (1 << logs(i)) for i, x in enumerate(e))


def int_slots_bound_list(w: int, length: int, logs_list: List[int], X: int) -> bool:
    """`intSlotsBound` with the per-slot log-bounds given as a list (logs i = logs_list[i])."""
    e = balanced_digits(w, length, X)
    if e is None:
        return False
    return all(abs(x) <= (1 << lg) for x, lg in zip(e, logs_list))


# ------------------------------------------------------------------------------------------ SO-POLY-B (proposed)
@dataclass(frozen=True)
class PackLayout:
    lo: Key
    dims: Tuple[int, ...]
    stride: Tuple[int, ...]
    width: int
    blockRows: int


@dataclass
class PackedAdvice:
    la: PackLayout
    lb: PackLayout
    target: PackLayout
    scale: int
    rounded: List[List[int]] = field(repr=False)
    outLog: int


def _ndiv(a: int, b: int) -> int:
    """Lean `Nat` division (`a / 0 = 0`)."""
    return a // b if b else 0


def _nmod(a: int, b: int) -> int:
    """Lean `Nat` modulus (`a % 0 = a`)."""
    return a % b if b else a


def _nsub(a: int, b: int) -> int:
    """Lean truncated `Nat` subtraction."""
    return a - b if a > b else 0


def layout_slot(L: PackLayout, k: Key) -> Optional[int]:
    """`PackLayout.slot`. PROPOSED BODY: `some (Σ_j (k_j - lo_j) stride_j)` when `k` has `dims.length` coordinates
    and `lo_j ≤ k_j < lo_j + dims_j` for every j (the lengths of `lo`, `dims`, `stride` agree), else `none`."""
    n = len(L.dims)
    if len(k) != n or len(L.lo) != n or len(L.stride) != n:
        return None
    s = 0
    for j in range(n):
        d = k[j] - L.lo[j]
        if d < 0 or d >= L.dims[j]:
            return None
        s += d * L.stride[j]
    return s


def dense_len(L: PackLayout) -> int:
    """`PackLayout.denseLen` (Revision 7, F14): `1 + Σ_j (dims_j - 1) stride_j` when every extent is positive,
    `0` on an empty box."""
    if any(d == 0 for d in L.dims):
        return 0
    return 1 + sum((d - 1) * s for d, s in zip(L.dims, L.stride))


def layout_dense(L: PackLayout, cs, skip_zero: bool = False) -> Optional[List[int]]:
    """`PackLayout.dense`: the dense slot list of length `denseLen` (`none` on an out-of-box key; repeated keys
    add).  `skip_zero=True` is the VARIANT needed by the 'minimal' zero-part policy (zero entries are ignored, so
    an all-zero part fits a one-slot box); it is NOT the signature's docstring and is reported as a proposal."""
    out = [0] * dense_len(L)
    for k, v in cs:
        if skip_zero and v == 0:
            continue
        s = layout_slot(L, k)
        if s is None or s >= len(out):
            return None
        out[s] += v
    return out


def prod_key(La: PackLayout, Lb: PackLayout, i: int) -> Key:
    """`PackLayout.prodKey La Lb i`. PROPOSED BODY: mixed-radix digits of `i` by the (shared) strides of `La`,
    greatest stride first (`d_0 = i / stride_0`, `d_1 = (i % stride_0) / stride_1`, ...), plus `La.lo + Lb.lo`."""
    rem = i
    key = []
    for j in range(len(La.stride)):
        s = La.stride[j]
        key.append(La.lo[j] + (Lb.lo[j] if j < len(Lb.lo) else 0) + _ndiv(rem, s))
        rem = _nmod(rem, s)
    return tuple(key)


def compat(n: int, La: PackLayout, Lb: PackLayout) -> bool:
    """`PackLayout.compat n La Lb`. PROPOSED BODY (the docstring's 'n axes, equal widths and strides, NO WRAP',
    made precise for any n): all of `lo`, `dims`, `stride` of both layouts have length n; the strides and the widths
    are equal; every extent is positive; the last stride is 1; and for every j < n - 1,
        stride_j > Σ_{j' > j} (dimsA_{j'} + dimsB_{j'} - 2) stride_{j'}
    (for n = 2: stride_0 ≥ dimsA_1 + dimsB_1 - 1, stride_1 = 1).  This makes the greedy digit decoding of
    `prodKey` invert the product slot map, so `intEval_mul` holds."""
    for L in (La, Lb):
        if len(L.lo) != n or len(L.dims) != n or len(L.stride) != n:
            return False
        if any(d < 1 for d in L.dims):
            return False
    if La.stride != Lb.stride or La.width != Lb.width:
        return False
    if n == 0:
        return True
    st = La.stride
    if st[n - 1] != 1:
        return False
    for j in range(n - 1):
        tail = sum((La.dims[q] + Lb.dims[q] - 2) * st[q] for q in range(j + 1, n))
        if not st[j] > tail:
            return False
    return True


def block_len(adv: PackedAdvice) -> int:
    """`PackedAdvice.blockLen`. PROPOSED BODY: `la.blockRows * la.stride.headD 1` (blockRows rows of the leading
    axis; for n = 2 rows = first key coordinate, so `stride_0` divides `blockLen`)."""
    head = adv.la.stride[0] if adv.la.stride else 1
    return adv.la.blockRows * head


def cut(adv: PackedAdvice, d: List[int]) -> List[List[int]]:
    """`PackedAdvice.cut`: `d` cut into blocks of `blockLen` slots, the last one zero-padded (`[]` for `d = []`
    or `blockLen = 0`)."""
    L = block_len(adv)
    if L == 0:
        return []
    out = []
    for s in range(0, len(d), L):
        blk = d[s:s + L]
        out.append(blk + [0] * (L - len(blk)))
    return out


def shard_conv(L: int, A: List[List[int]], B: List[List[int]], s: int) -> List[int]:
    """`shardConv L A B s`: `Σ_{i ≤ s} listConv (A.getD i []) (B.getD (s - i) [])`, zero-padded to `2L - 1`
    (literal; small inputs only)."""
    out = [0] * _nsub(2 * L, 1)
    for i in range(s + 1):
        a = A[i] if i < len(A) else []
        b = B[s - i] if s - i < len(B) else []
        for q, x in enumerate(list_conv(a, b)):
            if q < len(out):
                out[q] += x
    return out


def _flatten_max_abs(A: List[List[int]]) -> int:
    return max((max_abs(x) for x in A), default=0)


def shard_fits(w: int, L: int, A: List[List[int]], B: List[List[int]], s: int, mA=None, mB=None) -> bool:
    """`shardFits w L A B s`, the docstring's test `2 · (s + 1) · L · max|A| · max|B| < 2^w` (max over all
    entries of all blocks; `mA`, `mB` may be passed precomputed)."""
    mA = _flatten_max_abs(A) if mA is None else mA
    mB = _flatten_max_abs(B) if mB is None else mB
    return 2 * (s + 1) * L * mA * mB < (1 << w)


def shard_fits_min_width(L: int, mA: int, mB: int, s: int) -> int:
    """the least w with `shardFits w L A B s`."""
    return (2 * (s + 1) * L * mA * mB).bit_length()


def recon_fits(w: int, scale: int, logs_list: List[int], r: List[int]) -> bool:
    """`reconFits w scale logs r` (concrete in the signatures): `2 (2^scale |r_i| + 2^(logs i)) < 2^w` for all i."""
    lim = 1 << w
    return all(2 * ((abs(x) << scale) + (1 << lg)) < lim for x, lg in zip(r, logs_list))


def prod_len(adv: PackedAdvice) -> int:
    """`PackedAdvice.prodLen := la.denseLen + lb.denseLen - 1` (ℕ subtraction)."""
    return _nsub(dense_len(adv.la) + dense_len(adv.lb), 1)


def target_contains(T: PackLayout, k: Key) -> bool:
    n = len(T.dims)
    if len(k) != n or len(T.lo) != n:
        return False
    return all(T.lo[j] <= k[j] < T.lo[j] + T.dims[j] for j in range(n))


def in_box(adv: PackedAdvice, i: int) -> bool:
    """`PackedAdvice.inBox`. PROPOSED BODY: `i < prodLen` and `prodKey la lb i` lies in the target box."""
    return i < prod_len(adv) and target_contains(adv.target, prod_key(adv.la, adv.lb, i))


class InBoxTable:
    """`inBox` for every product slot, computed once (a cache; same values as `in_box`)."""

    def __init__(self, adv: PackedAdvice):
        self.n = prod_len(adv)
        la, lb, T = adv.la, adv.lb, adv.target
        nd = len(la.dims)
        if nd == 2 and len(T.dims) == 2 and la.stride[1] == 1 and la.stride[0] > 0:
            st = la.stride[0]
            r0, c0 = la.lo[0] + lb.lo[0], la.lo[1] + lb.lo[1]
            tab = bytearray(self.n)
            for row in range(T.lo[0] - r0, T.lo[0] + T.dims[0] - r0):
                for col in range(T.lo[1] - c0, T.lo[1] + T.dims[1] - c0):
                    if 0 <= col < st and row >= 0:
                        q = row * st + col
                        if q < self.n:
                            tab[q] = 1
            self.tab = tab
        else:
            self.tab = bytearray(1 if in_box(adv, i) else 0 for i in range(self.n))

    def __call__(self, i: int) -> bool:
        return 0 <= i < self.n and self.tab[i] == 1


def shard_logs_list(adv: PackedAdvice, s: int, box=None) -> List[int]:
    """`PackedAdvice.shardLogs adv s` on the window slots `0 ≤ i < 2·blockLen - 1`. PROPOSED BODY:
    `fun i => if inBox (s · blockLen + i) then scale - 1 else outLog`."""
    L = block_len(adv)
    box = box or (lambda q: in_box(adv, q))
    hi = _nsub(adv.scale, 1)
    return [hi if box(s * L + i) else adv.outLog for i in range(_nsub(2 * L, 1))]


def combined(adv: PackedAdvice) -> List[int]:
    """`PackedAdvice.combined` (Revision 7, F14): window s added at offset `s · blockLen`, zero-extended, then
    `take prodLen`."""
    L = block_len(adv)
    n = prod_len(adv)
    out = [0] * n
    for s, r in enumerate(adv.rounded):
        base = s * L
        for i, x in enumerate(r):
            if x and base + i < n:
                out[base + i] += x
    return out


def shape_ok(adv: PackedAdvice, box=None, why=None) -> bool:
    """`PackedAdvice.shapeOK`. PROPOSED BODY (the docstring's guards): `1 ≤ scale`; `0 < la.width`,
    `0 < la.blockRows`, `lb.blockRows = la.blockRows`; `compat n la lb` with `n = la.dims.length`; equal widths
    of la, lb, target; `target` has n axes and is a sub-box of the product window
    (`la.lo_j + lb.lo_j ≤ t.lo_j`, `t.lo_j + t.dims_j ≤ la.lo_j + lb.lo_j + la.dims_j + lb.dims_j - 1`);
    `0 < blockLen`; every window has length `2·blockLen - 1`; and the advice is zero on every window slot that is
    not `inBox` (outside the target box or beyond the product window).  `why` (a list) collects the failed
    guard."""
    def fail(msg):
        if why is not None:
            why.append(msg)
        return False
    la, lb, T = adv.la, adv.lb, adv.target
    n = len(la.dims)
    if adv.scale < 1:
        return fail("scale < 1")
    if la.width <= 0 or la.blockRows <= 0 or lb.blockRows != la.blockRows:
        return fail("width/blockRows")
    if not compat(n, la, lb):
        return fail("compat")
    if not (la.width == lb.width == T.width):
        return fail("widths")
    if len(T.lo) != n or len(T.dims) != n:
        return fail("target axes")
    for j in range(n):
        lo = la.lo[j] + lb.lo[j]
        if T.lo[j] < lo or T.lo[j] + T.dims[j] > lo + la.dims[j] + lb.dims[j] - 1:
            return fail("target not a sub-box of the product window")
    L = block_len(adv)
    if L <= 0:
        return fail("blockLen")
    box = box or (lambda q: in_box(adv, q))
    for s, r in enumerate(adv.rounded):
        if len(r) != 2 * L - 1:
            return fail("window %d length" % s)
        base = s * L
        for i, x in enumerate(r):
            if x and not box(base + i):
                return fail("nonzero advice outside the box (window %d slot %d)" % (s, i))
    return True


def check_shard(adv: PackedAdvice, A, B, s: int, box=None, packs=None, mAB=None, why=None) -> bool:
    """`checkShard adv A B s`: blocks of length `blockLen`, advice window of length `2·blockLen - 1`,
    `shardFits`, `reconFits` with `shardLogs s`, and `intSlotsBound w (2L - 1) (shardLogs s)` of
    `Σ_{i ≤ s} packShift(A_i) packShift(B_{s-i}) - 2^scale packShift(r_s)` (`w = la.width`).
    `packs = (PA, PB)` may pass the block packings precomputed (a cache: same values)."""
    def fail(msg):
        if why is not None:
            why.append(msg)
        return False
    L = block_len(adv)
    w = adv.la.width
    if any(len(x) != L for x in A) or any(len(x) != L for x in B):
        return fail("block length")
    r = adv.rounded[s] if s < len(adv.rounded) else []
    if len(r) != _nsub(2 * L, 1):
        return fail("advice window length")
    mA, mB = mAB if mAB is not None else (_flatten_max_abs(A), _flatten_max_abs(B))
    if not shard_fits(w, L, A, B, s, mA, mB):
        return fail("shardFits")
    logs = shard_logs_list(adv, s, box)
    if not recon_fits(w, adv.scale, logs, r):
        return fail("reconFits")
    if packs is None:
        PA = [pack_shift(w, x) for x in A]
        PB = [pack_shift(w, x) for x in B]
    else:
        PA, PB = packs
    X = 0
    for i in range(s + 1):
        if i < len(PA) and s - i < len(PB):
            X += PA[i] * PB[s - i]
    X -= pack_shift(w, r) << adv.scale
    if not int_slots_bound_list(w, _nsub(2 * L, 1), logs, X):
        return fail("intSlotsBound (window %d)" % s)
    return True


def check_packed_product(adv: PackedAdvice, da: List[int], db: List[int], why=None, box=None) -> bool:
    """`checkPackedProduct adv da db`: `shapeOK`; raw shapes (F14) `da.length = la.denseLen`,
    `db.length = lb.denseLen`, both positive; `rounded.length = (cut da).length + (cut db).length - 1`; and
    `checkShard` on every shard."""
    def fail(msg):
        if why is not None:
            why.append(msg)
        return False
    box = box or InBoxTable(adv)
    if not shape_ok(adv, box, why):
        return False
    if len(da) != dense_len(adv.la) or len(db) != dense_len(adv.lb) or not da or not db:
        return fail("raw factor length")
    A, B = cut(adv, da), cut(adv, db)
    ns = _nsub(len(A) + len(B), 1)
    if len(adv.rounded) != ns:
        return fail("shard count")
    w = adv.la.width
    packs = ([pack_shift(w, x) for x in A], [pack_shift(w, x) for x in B])
    mAB = (_flatten_max_abs(A), _flatten_max_abs(B))
    for s in range(ns):
        if not check_shard(adv, A, B, s, box, packs, mAB, why):
            return False
    return True


# ------------------------------------------------------------------------------------------ the conclusion
def conv_kronecker(a: List[int], b: List[int]) -> List[int]:
    """`listConv a b` exactly, by ONE Kronecker product at a width that provably fits (fast; tested against
    `list_conv`)."""
    if not a or not b:
        return []
    bound = 2 * min(len(a), len(b)) * max_abs(a) * max_abs(b)
    w = bound.bit_length() + 1
    n = len(a) + len(b) - 1
    e = balanced_digits(w, n, pack_sum(w, a) * pack_sum(w, b))
    assert e is not None
    return e


def check_sound_conclusion(adv: PackedAdvice, da: List[int], db: List[int], box=None) -> bool:
    """The conclusion of `checkPackedProduct_sound`, tested directly on the exact convolution:
    `combined.length = (listConv da db).length` and, slot by slot, `|conv_i - 2^scale combined_i| ≤ 2^scale`
    in the box, `|conv_i| ≤ 2^(outLog + 1)` outside."""
    conv = conv_kronecker(da, db)
    comb = combined(adv)
    if len(comb) != len(conv):
        return False
    box = box or InBoxTable(adv)
    sc, ol = adv.scale, adv.outLog
    for i, c in enumerate(conv):
        if box(i):
            if abs(c - (comb[i] << sc)) > (1 << sc):
                return False
        elif abs(c) > (1 << (ol + 1)):
            return False
    return True
