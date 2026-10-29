#!/usr/bin/env python3
"""SO-DATA-PY unit tests of the checker mirror and the advice builder (deterministic seeds; no data files).

usage: sodata_test.py            (prints one line per test group, exits nonzero on failure)

1. The fast slot decoder equals the LITERAL landed loop `intSlotsBoundAux` on random inputs, including
   out-of-range and leftover cases; `pack_sum` equals the definition; `conv_kronecker` equals `list_conv`;
   `shard_conv` summed over shards (overlap-add) equals `list_conv` (the shard decomposition).
2. The design's §8 negative tests: audit 5's carry-cancelling advice (`packSum 4 [16, -1, 0] = 0`,
   `reconFits 4 1 (fun _ => 0) [16, -1, 0] = false`), scale 0 rejected, the raw-length alias [0] vs [0, 0]
   rejected (F14).
3. Random end-to-end products (2-D sparse factors, random parity): the builder's advice passes
   `checkPackedProduct` and the `checkPackedProduct_sound` conclusion; the product slots map to the right keys
   (`prodKey` against a direct sparse product); and every corruption in `corruptions` FAILS.
"""
import random
import sys
from fractions import Fraction as F

import sodata_packed as SP
import sodata_advice as SA
from sodata_packed import PackedAdvice, PackLayout


def corruptions(adv, da, db, box=None):
    """(name, adv', da', db') variants that the checker must reject."""
    out = []
    L = SP.block_len(adv)
    box = box or SP.InBoxTable(adv)

    def clone(**kw):
        d = dict(la=adv.la, lb=adv.lb, target=adv.target, scale=adv.scale, rounded=[list(r) for r in adv.rounded],
                 outLog=adv.outLog)
        d.update(kw)
        return PackedAdvice(**d)
    # an in-box advice slot +2 (a +1 can survive a rounding tie)
    for s, r in enumerate(adv.rounded):
        hit = [i for i in range(len(r)) if box(s * L + i)]
        if hit:
            a = clone()
            a.rounded[s][hit[len(hit) // 2]] += 2
            out.append(("in-box slot +2 (window %d)" % s, a, da, db))
            break
    # nonzero advice outside the target box
    for s, r in enumerate(adv.rounded):
        miss = [i for i in range(len(r)) if not box(s * L + i)]
        if miss:
            a = clone()
            a.rounded[s][miss[0]] = 1
            out.append(("nonzero advice off the box (window %d)" % s, a, da, db))
            break
    out.append(("scale 0", clone(scale=0), da, db))
    # outLog - 1: must fail when some out-of-box window value needs the full outLog (tight by construction)
    if adv.outLog > 0:
        out.append(("outLog - 1", clone(outLog=adv.outLog - 1), da, db))
    a = clone()
    a.rounded[0] = a.rounded[0][:-1]
    out.append(("short advice window", a, da, db))
    a = clone()
    a.rounded = a.rounded[:-1]
    out.append(("missing advice window", a, da, db))
    if len(adv.rounded) > 1 and adv.rounded[0] != adv.rounded[1]:
        a = clone()
        a.rounded[0], a.rounded[1] = a.rounded[1], a.rounded[0]
        out.append(("swapped windows 0 and 1", a, da, db))
    w = adv.la.width
    nl = lambda L_, w_: PackLayout(L_.lo, L_.dims, L_.stride, w_, L_.blockRows)
    out.append(("width - 1", clone(la=nl(adv.la, w - 1), lb=nl(adv.lb, w - 1), target=nl(adv.target, w - 1)),
                da, db))
    out.append(("raw factor alias (da ++ [0])", clone(), da + [0], db))
    out.append(("raw factor truncated", clone(), da[:-1], db))
    return out


def probes(adv, da, db):
    """variants the checker MAY accept; acceptance must imply the `checkPackedProduct_sound` conclusion."""
    t = adv.target
    out = []
    # a factor entry changed at its largest coefficient (rejected unless the product stays within the bounds)
    j = max(range(len(da)), key=lambda i: abs(da[i]))
    d2 = list(da)
    d2[j] += max(abs(da[j]), 1 << (adv.scale + 2))
    out.append(("factor tamper", adv, d2, db))
    if adv.scale > 1:
        out.append(("scale - 1 (advice unchanged)",
                    PackedAdvice(adv.la, adv.lb, t, adv.scale - 1, adv.rounded, adv.outLog), da, db))
    for d in ((1, 0), (-1, 0), (0, 1), (0, -1)):
        tl = PackLayout((t.lo[0] + d[0], t.lo[1] + d[1]), t.dims, t.stride, t.width, t.blockRows)
        out.append(("target box shifted by %s" % (d,),
                    PackedAdvice(adv.la, adv.lb, tl, adv.scale, adv.rounded, adv.outLog), da, db))
    return out


def must_fail(name, adv, da, db):
    why = []
    ok = SP.check_packed_product(adv, da, db, why=why)
    assert not ok, "corruption accepted: " + name
    return why[0] if why else "?"


def test_decoder(rng):
    n = 0
    for _ in range(3000):
        w = rng.randint(1, 12)
        ln = rng.randint(0, 7)
        logs_l = [rng.randint(0, w) for _ in range(ln)]
        logs = lambda i: logs_l[i] if i < len(logs_l) else 0
        mode = rng.random()
        if mode < 0.5:
            e = [rng.randint(-(1 << (w - 1)), (1 << (w - 1)) - 1) for _ in range(ln)]
            X = SP.pack_sum(w, e) + (rng.choice([0, 0, 0, 1, -1]) << (w * ln))
        else:
            X = rng.randint(-(1 << (w * ln + 2)), 1 << (w * ln + 2))
        assert SP.int_slots_bound_literal(w, ln, logs, X) == SP.int_slots_bound(w, ln, logs, X), (w, ln, X)
        n += 1
    for _ in range(300):
        w = rng.randint(0, 40)
        cs = [rng.randint(-1000, 1000) for _ in range(rng.randint(0, 100))]
        assert SP.pack_sum(w, cs) == sum(c * (1 << (w * i)) for i, c in enumerate(cs))
        a = [rng.randint(-10**6, 10**6) for _ in range(rng.randint(1, 60))]
        b = [rng.randint(-10**6, 10**6) for _ in range(rng.randint(1, 60))]
        assert SP.conv_kronecker(a, b) == SP.list_conv(a, b)
        # shard decomposition: overlap-add of shardConv windows == listConv of the flattened padded blocks
        Lb = rng.randint(1, 9)
        adv = PackedAdvice(PackLayout((0,), (1,), (1,), 1, Lb), PackLayout((0,), (1,), (1,), 1, Lb),
                           PackLayout((0,), (1,), (1,), 1, Lb), 1, [], 0)
        A, B = SP.cut(adv, a), SP.cut(adv, b)
        tot = [0] * (len(A) * Lb + len(B) * Lb)
        for s in range(len(A) + len(B) - 1):
            for i, x in enumerate(SP.shard_conv(Lb, A, B, s)):
                tot[s * Lb + i] += x
        ref = SP.list_conv(sum(A, []), sum(B, []))
        assert tot[:len(ref)] == ref and not any(tot[len(ref):])
    return "decoder == literal loop on %d cases; packSum, Kronecker, shard decomposition OK" % n


def test_negative_contracts():
    assert SP.pack_sum(4, [16, -1, 0]) == 0                          # packSum_audit5_cancel
    assert SP.recon_fits(4, 1, [0, 0, 0], [16, -1, 0]) is False       # reconFits_audit5_rejects
    # audit 5's scenario as a whole product: zero factors, advice [16, -1, 0] at w = 4, scale = 1
    la = PackLayout((0,), (1,), (1,), 4, 2)
    adv = PackedAdvice(la, la, la, 1, [[16, -1, 0]], 0)
    assert not SP.check_packed_product(adv, [0], [0])
    # scale 0 is rejected whatever the data (checkPackedProduct_scale_zero)
    adv0 = PackedAdvice(la, la, la, 0, [[0, 0, 0]], 0)
    assert not SP.check_packed_product(adv0, [0], [0])
    # F14 alias: [0] versus [0, 0] cut to the same blocks; the raw length check rejects the short call
    la2 = PackLayout((0,), (2,), (1,), 8, 1)
    adv2 = PackedAdvice(la2, la2, PackLayout((0,), (3,), (1,), 8, 1), 1, [[0], [0], [0]], 0)
    assert SP.cut(adv2, [0]) == SP.cut(adv2, [0, 0])[:1] and SP.check_packed_product(adv2, [0, 0], [0, 0])
    assert not SP.check_packed_product(adv2, [0], [0, 0])
    return "audit-5 carry cancel rejected, scale 0 rejected, raw-length alias rejected"


def rand_factor(rng, S):
    k0, l0 = rng.randint(-6, 2), rng.randint(-4, 1)
    rows, cols = rng.randint(1, 70), rng.randint(1, 9)
    keys = set()
    for _ in range(rng.randint(1, rows * cols)):
        keys.add((k0 + rng.randint(0, rows - 1), l0 + rng.randint(0, cols - 1)))
    keys = sorted(keys)
    vals = []
    for k, l in keys:
        mag = rng.randint(0, S)
        v = rng.randint(1, 1 << mag) * rng.choice([1, -1])
        vals.append(v)
    return keys, vals


def test_products(rng, Wt):
    nprod = ncorr = nprobe = nacc = 0
    reasons = {}
    for t in range(60):
        S = rng.choice([20, 40, 72])
        ka, va = rand_factor(rng, S)
        kb, vb = rand_factor(rng, S)
        pa, pb = rng.randint(0, 1), rng.randint(0, 1)
        policy = "support" if t % 3 else "minimal"
        P, parts = SA.build_complex((ka, va, S, pa), (kb, vb, S, pb), Wt, 1e-6, policy=policy)
        nprod += 1
        # direct sparse product of the nonzero part: every product slot carries the right key
        direct = {}
        for (a1, b1), x in zip(ka, va):
            for (a2, b2), y in zip(kb, vb):
                direct[(a1 + a2, b1 + b2)] = direct.get((a1 + a2, b1 + b2), 0) + (x * y << (2 * (P - S)))
        for nm, adv, da, db, info in parts:
            conv = SP.conv_kronecker(da, db)
            got = {}
            for i, c in enumerate(conv):
                if c:
                    got[SP.prod_key(adv.la, adv.lb, i)] = c
            if not info["zero"]:
                assert got == {k: v for k, v in direct.items() if v}, (t, nm)
            else:
                assert not got
            for cname, a, xa, xb in corruptions(adv, da, db):
                reasons[cname.split(" (")[0]] = must_fail(cname, a, xa, xb)
                ncorr += 1
            for cname, a, xa, xb in probes(adv, da, db):
                if SP.check_packed_product(a, xa, xb):
                    assert SP.check_sound_conclusion(a, xa, xb), "unsound acceptance: " + cname
                    nacc += 1
                nprobe += 1
    return "%d random complex products (4 parts each) pass; prodKey matches the sparse product; %d corruptions " \
           "rejected (%s); %d box-shift probes, %d accepted, all with the sound conclusion" % (
               nprod, ncorr, ", ".join(sorted(reasons)), nprobe, nacc)


def main():
    from rotlib import Weights
    rng = random.Random(20261029)
    Wt = Weights(F(1, 70), nmax=200)
    for f in (lambda: test_decoder(rng), test_negative_contracts, lambda: test_products(rng, Wt)):
        print("PASS", f())
    print("ALL PASS")


if __name__ == "__main__":
    main()
