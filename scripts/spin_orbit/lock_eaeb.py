#!/usr/bin/env python3
"""LOCK-DATA: the operand slot terms of every packed product of the lock (untrusted tooling).

For each packed product of both composition chains and each nonempty part (rr, ii, ri, ir), the lists
`adv.la.slotTerms x` and `adv.lb.slotTerms y` that the landed checker computes from the operands' mantissas
(`checkPackedSp adv ea eb`).  The emitter states each product's shard checks against these as literals (one
module proves `ea = literal`), so a shard module no longer recomputes the operands (4.2 GB, measured on M1).

Records are streamed (one pickle per product) to OUT, keyed by (chain, full key):

    SO_LOCK_DATA=... SO_LOCK_SIZE=... python3 lock_eaeb.py GENDIR OUT.pkls
"""
import os
import pickle
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lock_seg as LSG       # noqa: E402
import sofx_model as M       # noqa: E402
import sofx_packed as SP     # noqa: E402

CUR = [None]
OUT = [None]
_orig_poly = M.polyProduct
_orig_mul = SP.PackedEngine.mulPacked


def slot_terms(L, x):
    """`PackLayout.slotTerms`: the slot of each key (0 when it has none) with its value."""
    out = []
    for k, v in x:
        s = SP.packSlotAux(k, L.lo, L.dims, L.stride)
        out.append((0 if s is None else s, v))
    return out


def _poly(B, W, cfg, key, a, b):
    CUR[0] = (cfg.root().name, tuple(cfg.full_key(key)))
    return _orig_poly(B, W, cfg, key, a, b)


def _mul(self, B, W, padv, a, b):
    _, P, rr, ii, ri, ir = padv
    ma, mb = SP.toMants(B, P, a), SP.toMants(B, P, b)
    if ma is not None and mb is not None:
        rec = {}
        for part, adv, x, y in (("rr", rr, ma[0], mb[0]), ("ii", ii, ma[1], mb[1]), ("ri", ri, ma[0], mb[1]),
                                ("ir", ir, ma[1], mb[0])):
            if x and y:
                rec[part] = (slot_terms(adv.la, x), slot_terms(adv.lb, y))
        pickle.dump((CUR[0], rec), OUT[0])
    return _orig_mul(self, B, W, padv, a, b)


def main(gdir, out):
    c, d = LSG.lock_cert(gdir)
    M.polyProduct = _poly
    SP.PackedEngine.mulPacked = _mul
    OUT[0] = open(out, "wb")
    B, n, W, pe = c.B, c.n, c.weight, c.piEnc
    for tag, cfg in (("cfgFull", c.cfgFull), ("cfgLow", c.cfgLow)):
        st = M.ComposeState()
        for i, op in enumerate(c.jetOps):
            assert M.composeStep(B, n, c.emb, c.wit, W, cfg, pe, st, op) is not None, (tag, i)
        print(tag, "done", flush=True)
    OUT[0].close()


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
