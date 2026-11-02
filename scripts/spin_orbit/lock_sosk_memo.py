#!/usr/bin/env python3
"""LOCK-DATA, SOS option (a): the two packed SOS squares as ledger-style memos (untrusted tooling).

    SO_LOCK_DATA=... SO_LOCK_SIZE=... python3 lock_sosk_memo.py GENDIR(=gen_D100d) OUT.pkl

For the keys [7, 1] (pLo) and [7, 2] (pHi): the memo of `g g*` exactly as the ledger records a packed product
(ctx, cfg, fullKey, key, P, a, b, out = the mirror's mulPacked output, parts with the operand part sizes) and the
operand slot terms per part (as lock_eaeb.py), so that lock_cseg.py emits the product machinery for them
(operand literals, shard groups, decode, remainder, side checks, product theorem).
"""
import os
import pickle
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.set_int_max_str_digits(0)
import lock_seg as LSG       # noqa: E402
import sofx_check as C       # noqa: E402
import sofx_packed as PK     # noqa: E402
import lock_eaeb as LE       # noqa: E402


def main(gdir, out):
    c, _d = LSG.lock_cert(gdir)
    g = pickle.load(open(os.path.join(gdir, "gen.pkl"), "rb"))
    B, W = c.B, c.weight
    book = {tuple(k): a for k, a in g["books"]["cfgLow"]}
    eng = PK.PackedEngine({"cfgFull": F(1, 10 ** 24), "cfgLow": F(1, 10 ** 8)})
    memos, eaeb = [], {}
    for side, key, sos in (("pLo", (7, 1), c.graph["sosLo"]), ("pHi", (7, 2), c.graph["sosHi"])):
        gp = [((int(k[0]), int(k[1])), (int(v[0]), int(v[1]))) for k, v in sos]
        conj = C.conjSorted(B, gp)
        adv = book[key]
        res = eng.mulPacked(B, W, adv, gp, conj)
        assert res is not None, (side, eng.last_info)
        ma, mb = PK.toMants(B, 112, gp), PK.toMants(B, 112, conj)
        parts, rec = [], {}
        for part, ad, x, y in (("rr", adv[2], ma[0], mb[0]), ("ii", adv[3], ma[1], mb[1]),
                               ("ri", adv[4], ma[0], mb[1]), ("ir", adv[5], ma[1], mb[0])):
            parts.append(dict(part=part, empty=not (x and y), x=len(x), y=len(y)))
            if x and y:
                rec[part] = (LE.slot_terms(ad.la, x), LE.slot_terms(ad.lb, y))
        memos.append(dict(ctx="graph/%s" % side, cfg="cfgLow", fullKey=key, key=key, P=112, a=gp, b=conj,
                          out=res, parts=parts))
        eaeb[("cfgLow", key)] = rec
        print(side, "memo: out terms", len(res[0]), "parts", [(p["part"], p["empty"], p["x"], p["y"]) for p in parts],
              flush=True)
    pickle.dump(dict(memos=memos, eaeb=eaeb), open(out, "wb"))
    print("written", out, flush=True)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
