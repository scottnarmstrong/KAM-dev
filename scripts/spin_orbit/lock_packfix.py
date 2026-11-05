#!/usr/bin/env python3
"""LOCK-DATA: regenerate the cfgLow exp-residual advice `[1, i, j]` of the lock certificate (untrusted tooling).

The generator `sofx_packed.PackedEngine.build_real` sizes the packing width with `2 len(A) L max|A| max|B|`, but the
landed `shardFits` bounds shard `s` (up to `#A + #B - 2`) by `2 (s+1) L max|A| max|B|`.  When the right operand has
more blocks (cfgLow: `∂_j g` 367 terms against the witness's 5898), the advice fails `shardFits` and the checker
falls back to `directItems` (about 1.1M term products per residual: kernel-infeasible).  The width conditions are
monotone, so `fix_packed` raises the width until the landed check (mirror) accepts the advice; nothing else in the
advice changes.

    SO_LOCK_DATA=... SO_LOCK_SIZE=... python3 lock_packfix.py GENDIR OUTDIR [BUDGET_EXP]

Writes OUTDIR/gen.pkl: GENDIR's gen.pkl with the cfgLow keys (1, i, j) replaced (generated at budget 10^-BUDGET_EXP,
default 24, the cfgFull budget).
"""
import os
import pickle
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lock_seg as LSG       # noqa: E402
import sofx_model as M       # noqa: E402
import sofx_packed as PK     # noqa: E402


def fix_packed(B, W, eng, adv, a, b):
    """the packed advice `adv` with each real part's width raised until `mulPacked` succeeds."""
    if adv[0] != "packed":
        return adv
    P, parts = adv[1], list(adv[2:])
    for _ in range(64):
        if eng.mulPacked(B, W, ("packed", P, *parts), a, b) is not None:
            return ("packed", P, *parts)
        why = eng.last_info.get("why", [])
        if "shardFits" not in why:
            raise SystemExit("advice fails for another reason: %r" % (why,))
        for p in parts:
            for Lx in {id(p.la): p.la, id(p.lb): p.lb, id(p.target): p.target}.values():
                Lx.width += 1
    raise SystemExit("width did not converge")


def main(gdir, odir, bexp=24):
    c, d = LSG.lock_cert(gdir)
    g = pickle.load(open(os.path.join(gdir, "gen.pkl"), "rb"))
    B, n, W, pe = c.B, c.n, c.weight, c.piEnc
    cfg = c.cfgLow
    eng = PK.PackedEngine({"cfgFull": F(1, 10 ** 24), "cfgLow": F(1, 10 ** bexp)})
    new = {}
    st = M.ComposeState()
    for i, op in enumerate(c.jetOps):
        if op[0] == "exp":
            k = st.nExp
            gm = M.toDeg(B, W, pe, 0, st.slot(B, W, op[1])[0])
            E = c.wit.expWit[k][0]
            for j in range(n):
                dg = M.itemsPoly(M.derivItems(B, j, gm.poly))
                nE = M.negP(B, E)
                adv = eng.generate(B, W, cfg.root(), (1, k, j), dg, nE)
                adv = fix_packed(B, W, eng, adv, dg, nE)
                out = eng.mulPacked(B, W, adv, dg, nE)
                assert out is not None
                new[(1, k, j)] = adv
                # patch the live book now: the later slots (and later exp operands) depend on this product
                book = cfg.root().book
                hits = [idx for idx, (key, _) in enumerate(book) if tuple(key) == (1, k, j)]
                assert len(hits) == 1, hits
                book[hits[0]] = (book[hits[0]][0], adv)
                print("slot", i, "key", (1, k, j), "terms", len(dg), len(nE), "->", len(out[0]),
                      "rem", float(eng.last_info.get("rem", 0)), "w", adv[2].la.width, flush=True)
        assert M.composeStep(B, n, c.emb, c.wit, W, cfg, pe, st, op) is not None, i
    book = g["books"]["cfgLow"]
    hit = 0
    for idx, (key, adv) in enumerate(book):
        if tuple(key) in new:
            book[idx] = (key, new[tuple(key)])
            hit += 1
    assert hit == len(new), (hit, len(new))
    assert [tuple(k) for k, _ in book] == [tuple(k) for k, _ in cfg.root().book]
    os.makedirs(odir, exist_ok=True)
    pickle.dump(g, open(os.path.join(odir, "gen.pkl"), "wb"))
    print("replaced", hit, "cfgLow advice entries ->", odir, flush=True)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 24)
