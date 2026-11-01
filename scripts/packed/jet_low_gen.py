#!/usr/bin/env python3
"""V2-PACKED-JET-LOW: LG00's whole cfgLow jet chain as packed blocks (untrusted tooling; the kernel re-checks).

Reads `jet_extract_low.py`'s JSON (the program, the live slots, the leaves computed by lg00-cert's bit-exact mirror)
and runs the whole chain in Python with the bit-exact mirror of `KAM/CertificateSharp/Packed/Jet*.lean`
(`jet_gate_gen.py`), then cuts it into the blocks of `JetWit.lean` (`JBlockW`), in this order:
  - the action block (`jActionsOk`: the action slots packed from the embedding);
  - the exponential blocks (`jExpNode`: exp(+-i 2pi angleAt_j), Taylor with remainder), the power blocks
    (`jPowsAux`) and the character blocks (`jCharsOk`), `JetChar.lean`;
  - the segments (`jSegOk`): the constants, sums and products in slot order, at most `--heavy` heavy steps each
    (box-by-box products and reduces in place), cut at the `inv`/`sqrt` slots, whose blocks (`jInvOk`,
    `jSqrtOk`: the landed output as an untrusted candidate, its residual as the radius) sit between them. A box
    node above scale 2^P is reduced in place only when a product or a witness reads it or it is wanted.
Every import of a block is an export of an earlier block (by construction). Writes one probe per block into
$V2P_GATE_DIR (default .lake/v2-packed-jet/low), and LowPlan.json (FullPlan.json).
V2-PACKED-JET-FULL: `--stage=Full` (with `jet_extract_low.py --stage=Full`) generates the cfgFull chain on the box of
half-width 48, the blocks named `Full…`, into .lake/v2-packed-jet/full; there the exponentials are staged
(`JetStage.lean`, `--taylor=K` Taylor steps per block: `tstart`, `tstep`, `texp`), the powers split (`--pows=K` per
block), the action slots split (`--act=K` per block). `--cache=PATH` saves the mirror run (pickle; this script's own
output) and reuses it when present, so re-planning skips the run.
Usage: python3 -I scripts/packed/jet_low_gen.py LOW.json [--stage=Low|Full] [--heavy=34] [--char-keys=8] [--char-io=48]
       [--act=K] [--taylor=K] [--pows=K] [--cache=PATH] [--only=K]
"""
import json
import os
import pickle
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import jet_gate_gen as JG     # noqa: E402
G, GG = JG.G, JG.GG
STAGE = next((x.split("=")[1] for x in sys.argv if x.startswith("--stage=")), "Low")
assert STAGE in ("Low", "Full")
if STAGE == "Full":
    JG.H = 48                                           # the box of the cfgFull chain (V2-PACKED.md 12.8)
P, Q, H, n = JG.P, JG.Q, JG.H, JG.n
PRE = STAGE                                             # block names: LowSeg_0, FullSeg_0, ...
OUT = os.environ.get("V2P_GATE_DIR", os.path.join(JG.ROOT, ".lake", "v2-packed-jet", STAGE.lower()))


def opt(name, default):
    return next((x.split("=", 1)[1] for x in sys.argv if x.startswith("--%s=" % name)), default)
CERT = os.environ.get("LG00_CERT", "/home/scott/KAM-dev-worktrees/lg00-cert/KAM/LG00Cert")
LEAVES = ("action", "char", "inv", "sqrt", "exp")


def leaf_node(C, lv, aC, lb):
    if lv["kind"] == "const":
        L = C.LU0
        d = {}
        x = (sum(v << (L.w * L.slot(tuple(k))) for k, v in lv["re"]),
             sum(v << (L.w * L.slot(tuple(k))) for k, v in lv["im"]))
        return JG.Node(True, aC, P, x, lv["rad"], C.pnorm(L, P, x))
    L = C.Lb
    x = (sum(v << (L.w * L.slot(tuple(k))) for k, v in lv["re"]),
         sum(v << (L.w * L.slot(tuple(k))) for k, v in lv["im"]))
    return JG.Node(False, 2 ** lb, P, x, lv["rad"], C.pnorm(L, P, x))


def digits_bits(C, x):
    return max([abs(c) for z in x for c in JG.unpack(C.Lb, z).values()] + [1]).bit_length()


def plan_steps(D, consumers, wanted):
    """`(i, eT, red)` for the non-leaf live slots, from the layout flags (pass 1 decides them)."""
    return None


class Ops:
    """The node operations of pass 1 (loads and digits) or pass 2 (exact), as `JetNode.lean`."""

    def __init__(self, C, bk, st, lb):
        self.C, self.bk, self.st, self.lb = C, bk, st, lb

    def mul(self, a, b, eT):
        if self.bk is not None:
            return JG.j_mul(self.C, self.bk, a, b, eT, self.st)
        self.st["lbfix"] = self.lb
        return JG.j_mul_pass1(self.C, a, b, eT, self.st)

    def red(self, nd, eT):
        if self.bk is not None:
            return JG.j_red(self.C, self.bk, nd, eT, self.st)
        self.st["lbfix"] = self.lb
        return JG.j_red_pass1(self.C, nd, eT, self.st)

    def add(self, a, b):
        return JG.j_add(self.C, a, b) if self.bk is not None else JG.j_add_pass1(self.C, a, b)

    def norm(self, nd):                                # JetChar.jNorm
        return self.red(nd, P) if nd.e > P else nd


def const_node(C, D, key, aC, lb):
    return leaf_node(C, D["consts"][key], aC, lb)


def up_pow(B, M, k):                                    # JetChar.upPow
    r = B.ofInt(1)
    for _ in range(k):
        r = B.upMul(r, M)
    return r


def taylor_order(C, D, j):
    """The Taylor degree N of exp(+-i 2pi angleAt_j): remainder 2 M^(N+1)/(N+1)! below 2^-130 with M a generous
    estimate of |w| (the angle's packed norm times 2pi times 1.25); the check holds for any N."""
    lv = D["angles"][str(j)]
    L = C.Lb
    x = (sum(v << (L.w * L.slot(tuple(k))) for k, v in lv["re"]),
         sum(v << (L.w * L.slot(tuple(k))) for k, v in lv["im"]))
    M = float(F(C.pnorm(L, P, x), 2 ** P)) * 6.2832 * 1.25 + 1e-6
    import math
    N = 4
    while 2 * M ** (N + 1) / math.factorial(N + 1) > 2.0 ** -130:
        N += 1
    return N


def chars(C, bk, D, aC, lb, st):
    """The packed characters (`JetChar.lean`): the exponential nodes, their powers and every character slot's
    node; returns (E, pows, nodes, N) with E[(j, neg)], pows[(j, neg)] = [base^2, ...], nodes[slot]."""
    ops_, ops = D["ops"], Ops(C, bk, st, lb)
    keys = sorted({tuple(ops_[j][1]) for j in D["live"] if ops_[j][0] == "char"})
    need = {}
    for k in keys:
        for i, ki in enumerate(k):
            if ki:
                need[(i, ki < 0)] = max(need.get((i, ki < 0), 0), abs(ki))
    E, pows, Ns, TS = {}, {}, {}, {}
    one = const_node(C, D, "1/0/0", aC, lb)
    for (j, neg), M in sorted(need.items()):
        Ns[(j, neg)] = N = taylor_order(C, D, j)
        A = leaf_node(C, dict(D["angles"][str(j)], kind="angle"), aC, lb)
        c = const_node(C, D, "0/%d/1" % (-1 if neg else 1), aC, lb)
        w = ops.norm(ops.mul(c, A, P))
        t = s_ = one
        ts = [(t, s_)]
        for m in range(N):
            t2 = ops.norm(ops.mul(t, w, P))
            cq = const_node(C, D, "%s/0/0" % F(1, m + 1), aC, lb)
            t = ops.norm(ops.mul(t2, cq, P))
            s_ = ops.add(s_, t)
            ts.append((t, s_))
        TS[(j, neg)] = dict(w=w, ts=ts)
        if bk is not None:
            B = C.B
            Mw = B.upAdd(w.nb, w.r)
            assert B.ble(B.upMul(Mw, B.ofRatUp(F(1, N + 2))), B.ofRatDown(F(1, 2)))
            import math
            rem = B.upMul(B.ofRatUp(F(2, math.factorial(N + 1))), up_pow(B, Mw, N + 1))
            e = JG.Node(s_.u, s_.A, s_.e, s_.x, B.upAdd(s_.r, rem), s_.nb)
        else:
            e = s_
        E[(j, neg)] = e
        cur, outs = e, []
        for _ in range(2, M + 1):
            cur = ops.norm(ops.mul(cur, e, P))
            outs.append(cur)
        pows[(j, neg)] = outs
    fac = lambda i, ki: one if ki == 0 else (E[(i, ki < 0)] if abs(ki) == 1 else pows[(i, ki < 0)][abs(ki) - 2])
    nodes, by_key = {}, {}
    L = C.Lb
    for k in keys:
        x = ((1 << P) << (L.w * L.slot(k)), 0)
        acc = JG.Node(False, 2 ** lb, P, x, 0, C.pnorm(L, P, x) if bk is not None else None)
        for i, ki in enumerate(k):
            acc = ops.norm(ops.mul(acc, fac(i, ki), P))
        by_key[k] = acc
    for j in D["live"]:
        if ops_[j][0] == "char":
            nodes[j] = by_key[tuple(ops_[j][1])]
    return E, pows, nodes, Ns, by_key, one, TS


def wit_node(C, bk, D, kind, na, lv, aC, lb, ops):
    """The exported node of an `inv` or `sqrt` slot (`JetWit.lean`): the candidate (the landed output, packed) with
    the radius from its residual; constants c_A = c_S = 1, s0 = 1/2 for `sqrt`."""
    L, B = C.Lb, C.B
    x = (sum(v << (L.w * L.slot(tuple(k))) for k, v in lv["re"]),
         sum(v << (L.w * L.slot(tuple(k))) for k, v in lv["im"]))
    cand = JG.Node(False, 2 ** lb, P, x, 0, C.pnorm(L, P, x) if bk is not None else None)
    neg = lambda nd: JG.Node(nd.u, nd.A, nd.e, (-nd.x[0], -nd.x[1]), nd.r, nd.nb)
    one = const_node(C, D, "1/0/0", aC, lb)

    def renorm(nd):                                     # JetWit.jRenorm
        ops.st["aB"] = max(ops.st["aB"], nd.A)
        if bk is None:
            return nd
        return JG.Node(nd.u, nd.A, nd.e, nd.x, nd.r, C.pnorm(C.lay(nd.u), nd.e, nd.x))
    if kind == "inv":
        d = renorm(ops.add(one, neg(ops.mul(na, cand, P))))
        if bk is None:
            return JG.Node(False, 2 ** lb, P, x, None, None), cand
        dl = B.upAdd(d.r, d.nb)
        assert B.ble(dl, B.ofRatDown(F(1, 2))), "inv residual"
        return JG.Node(False, 2 ** lb, P, x, B.upMul(B.upMul(cand.nb, dl), B.ofRatUp(F(2))), cand.nb), cand
    sq = ops.mul(cand, cand, P)
    dA, dS, e = (renorm(ops.add(na, neg(one))), renorm(ops.add(cand, neg(one))),
                 renorm(ops.add(sq, neg(na))))
    if bk is None:
        return JG.Node(False, 2 ** lb, P, x, None, None), cand
    assert B.ble(B.upAdd(dA.r, dA.nb), B.ofRatDown(F(1, 2))), "sqrt operand"
    assert B.ble(B.upAdd(B.upAdd(dS.r, dS.nb), B.ofRatUp(F(1, 2))), B.ofRatDown(F(1))), "sqrt candidate"
    return JG.Node(False, 2 ** lb, P, x, B.upMul(B.upAdd(e.r, e.nb), B.ofRatUp(F(2))), cand.nb), cand


def run(C, bk, D, lb, aC, decide):
    """The whole chain. `decide` (pass 1) fixes the steps; then the same steps are replayed exactly."""
    ops, leaves = D["ops"], D["leaves"]
    S, steps, st = {}, [], {"aW": 0, "aB": 0, "smax": 0, "lb": 0}
    CH = chars(C, bk, D, aC, lb, st)
    ops_obj, wits = Ops(C, bk, st, lb), {}
    for i in D["live"]:
        op = ops[i]
        lv = leaves.get(str(i))
        if op[0] == "char":
            S[i] = CH[2][i]
            continue
        if op[0] in ("inv", "sqrt"):
            S[i], cand = wit_node(C, bk, D, op[0], S[op[1]], lv, aC, lb, ops_obj)
            wits[i] = cand
            continue
        if lv is not None and lv["kind"] in LEAVES:
            S[i] = leaf_node(C, lv, aC, lb)
            st["lb"] = max(st["lb"], digits_bits(C, S[i].x))
            continue
        if op[0] == "const":
            S[i] = leaf_node(C, lv, aC, lb)
            steps.append((i, 0, 0))
            continue
        a, b = S[op[1]], S[op[2]]
        if op[0] == "add":
            nd = JG.j_add(C, a, b) if bk is not None else JG.j_add_pass1(C, a, b)
            eT = 0
        else:
            genuine = not (a.u or b.u)
            eT = P if genuine else 0
            if bk is not None:
                nd = JG.j_mul(C, bk, a, b, eT, st)
            else:
                st["lbfix"] = lb
                nd = JG.j_mul_pass1(C, a, b, eT, st)
        red = 0
        if nd.e > P and decide(i):
            red = P
            if bk is not None:
                nd = JG.j_red(C, bk, nd, red, st)
            else:
                st["lbfix"] = lb
                nd = JG.j_red_pass1(C, nd, red, st)
        S[i] = nd
        steps.append((i, eT, red))
    st["chars"] = CH
    st["wits"] = wits
    return S, steps, st


def book_of(C, st, aC):
    bk = JG.book_of(C, st)
    lc = aC.bit_length() + 1
    lrc = (bk.aB + JG.mul_load(C.LU0, C.LU0, 2 ** bk.lb, 2 ** bk.smax)).bit_length()
    lnc = bk.lb + 1
    r, c = G.maxes(C.W, Q, C.LU0.lo, C.LU0.dims, C.LU0.S)
    need = [bk.w] + [x for l in (lc, lrc, lnc) for x in (l + 2, (C.LU0.dims[0] * C.LU0.S * 2 ** l * r * c).bit_length())]
    w = max(need)
    w += (-w) % 8
    bk.w, bk.P, bk.aC, bk.lc, bk.lrc, bk.lnc = w, P, aC, lc, lrc, lnc
    return bk


def main():
    D = json.load(open(sys.argv[1]))
    W = F(D["weight"]["w"][0], D["weight"]["w"][1])
    heavy_max = int(next((x.split("=")[1] for x in sys.argv if x.startswith("--heavy=")), "34"))
    ops, live = D["ops"], D["live"]
    wanted = set(D["wanted"])
    consumers = {}
    for i in live:
        op = ops[i]
        if op[0] in ("add", "mul"):
            for x in op[1:3]:
                consumers.setdefault(x, []).append(i)
        elif op[0] in ("inv", "sqrt", "exp"):
            consumers.setdefault(op[1], []).append(i)
    decide = lambda i: i in wanted or any(ops[c][0] in ("mul", "inv", "sqrt", "exp") for c in consumers.get(i, []))
    aC = max(abs(v) for lv in list(D["leaves"].values()) + list(D["consts"].values()) if lv["kind"] == "const"
             for _, v in lv["re"] + lv["im"])
    # pass 1: wide slots, `lb` to a fixed point
    cache = opt("cache", None)
    if cache is not None and os.path.exists(cache):
        with open(cache, "rb") as f:
            ck = pickle.load(f)
        assert ck["stage"] == STAGE and ck["H"] == H and ck["source"] == os.path.abspath(sys.argv[1])
        bk, S, steps, CH, wits = ck["bk"], ck["S"], ck["steps"], ck["chars"], ck["wits"]
        C = JG.Ctx(W, bk.w)
        print("mirror run from the cache", cache)
        plan_and_emit(C, bk, D, S, steps, heavy_max, wanted, CH, wits)
        return
    C1 = JG.Ctx(W, 1024)
    lb = 140
    for _ in range(6):
        S, steps, st = run(C1, None, D, lb, aC, decide)
        if st["lb"] <= lb:
            break
        lb = st["lb"]
    st["lb"] = lb
    bk = book_of(C1, st, aC)
    print("book", {k: (v if k in ("lb", "lr", "lrb", "ln", "smax", "ls", "lsb", "off", "w", "P", "lc", "lrc", "lnc") else
                       v.bit_length()) for k, v in bk.__dict__.items()}, "steps", len(steps))
    if "--stats" in sys.argv:
        return
    C = JG.Ctx(W, bk.w)
    S, steps2, st2 = run(C, bk, D, lb, aC, decide)
    assert steps2 == steps
    if cache is not None:
        with open(cache, "wb") as f:
            pickle.dump(dict(stage=STAGE, H=H, source=os.path.abspath(sys.argv[1]), bk=bk, S=S, steps=steps,
                             chars=st2["chars"], wits=st2["wits"]), f, protocol=pickle.HIGHEST_PROTOCOL)
    if "--mirror-only" in sys.argv:  # V2-PACKED-PROD: the mirror and its cache only (no probe emission)
        return
    plan_and_emit(C, bk, D, S, steps, heavy_max, wanted, st2["chars"], st2["wits"])


def plan_and_emit(C, bk, D, S, steps, heavy_max, wanted, CH, wits):
    ops, leaves = D["ops"], D["leaves"]
    actions = sorted(int(j) for j, v in leaves.items() if v["kind"] == "action")
    given = sorted(int(j) for j, v in leaves.items() if v["kind"] == "exp")
    assert not given, "an exp slot (no packed block yet)"
    # segments in slot order, cut at the witness slots (each witness block between its operand's segment and
    # the segments reading its result); `seq` interleaves ("seg", chunk index) and ("wit", slot)
    step_of = {t[0]: t for t in steps}
    chunks, seq, cur, hv = [], [], [], 0
    # `--seg-io=K`: at most K imports + exports per segment (V2-PACKED-JET-FULL: at cfgFull each node held by a
    # process costs about 0.12 GB; a segment of 8 heavy steps and 24 nodes exceeded 4 GiB)
    seg_io = int(opt("seg-io", "0"))
    last_use = {}
    for i in D["live"]:
        op = ops[i]
        rd = op[1:3] if op[0] in ("add", "mul") else op[1:2] if op[0] in ("inv", "sqrt", "exp") else []
        for x in rd:
            last_use[x] = max(last_use.get(x, -1), i)

    def io_with(ch, t):
        dfn = {u[0] for u in ch} | {t[0]}
        rd = lambda u: ops[u[0]][1:3] if ops[u[0]][0] in ("add", "mul") else []
        imps = {x for u in ch + [t] for x in rd(u)} - dfn
        exps = [x for x in dfn if x in wanted or last_use.get(x, -1) > t[0]]
        return len(imps) + len(exps)

    def flush():
        nonlocal cur, hv
        if cur:
            seq.append(("seg", len(chunks)))
            chunks.append(cur)
            cur, hv = [], 0
    for j in D["live"]:
        if j in step_of:
            t = step_of[j]
            h = (1 if t[1] else 0) + (1 if t[2] else 0)
            if cur and (hv + h > heavy_max or (seg_io and io_with(cur, t) > seg_io)):
                flush()
            cur.append(t)
            hv += h
        elif ops[j][0] in ("inv", "sqrt"):
            flush()
            seq.append(("wit", j))
    flush()
    reads = lambda t: [x for x in ops[t[0]][1:3]] if ops[t[0]][0] in ("add", "mul") else []
    # a slot is exported by its segment when a later block reads it or it is wanted
    pos = {}
    for q, (kind, v) in enumerate(seq):
        for j in ([t[0] for t in chunks[v]] if kind == "seg" else [v]):
            pos[j] = q
    seg_of = {t[0]: c for c, ch in enumerate(chunks) for t in ch}
    later = {}
    for q, (kind, v) in enumerate(seq):
        rd = [x for t in chunks[v] for x in reads(t)] if kind == "seg" else [ops[v][1]]
        for x in rd:
            if x in seg_of and pos[x] != q:
                later.setdefault(x, set()).add(q)
    data_head = _data_head(C, bk, D)
    os.makedirs(OUT, exist_ok=True)
    plan = []
    E = JG.Emit(C)
    # the action blocks (`--act=K` slots each; one block by default)
    act_k = int(opt("act", "0")) or len(actions)
    emb = _emb_text()
    for g in range(0, len(actions), act_k):
        acts = actions[g:g + act_k]
        E.defs = list(data_head) + [emb]
        for j in acts:
            E.node("act_%d" % j, S[j])
        E.defs.append("def actions : List (ℕ × JNode LGF) :=\n  [%s]\n" % ",\n   ".join(
            "(%d, act_%d)" % (j, j) for j in acts))
        nm = PRE + "Act" if act_k >= len(actions) else "%sAct_%d" % (PRE, g // act_k)
        _write(nm, "The action block (`jActionsOk`): %d action slots packed from the embedding." % len(acts),
               D, "".join(d + "\n" for d in E.defs), "jActionsOk 2 gW lgPe gCfg jbk lg00Emb lgProg actions = true")
        plan.append(dict(name=nm, kind="actions", exports=len(acts)))
    E_, pows_, _, Ns, by_key, _, TS = CH
    kname = lambda j, neg, m: "fac_%d_%s_%d" % (j, "n" if neg else "p", m)
    klit = lambda j, neg, m: "Sum.inr (%d, %s, %d)" % (j, "true" if neg else "false", m)
    sg = lambda neg: "n" if neg else "p"
    tf = lambda neg: "true" if neg else "false"
    tay_k = int(opt("taylor", "0"))
    pow_k = int(opt("pows", "0"))
    for (j, neg), e in sorted(E_.items()):
        N = Ns[(j, neg)]
        if tay_k:
            # the staged exponential (`JetStage.lean`): tstart, tstep (tay_k steps each), texp
            T = TS[(j, neg)]
            one = T["ts"][0][0]
            E.defs = list(data_head) + [emb]
            E.node("tw", T["w"])
            E.node("tone", one)
            nm = "%sTw_%d_%s" % (PRE, j, sg(neg))
            _write(nm, "The start of the staged exponential exp(%si 2pi angleAt_%d) (`JBlockT.tstart`): w and 1."
                   % ("-" if neg else "", j), D, "".join(d + "\n" for d in E.defs),
                   "(JBlockT.tstart %d %s tw tone).ok 2 gW lgPe gCfg jbk lg00Emb lgProg = true" % (j, tf(neg)))
            plan.append(dict(name=nm, kind="tstart", heavy=1, exports=3))
            for m0 in range(0, N, tay_k):
                k = min(tay_k, N - m0)
                E.defs = list(data_head) + [emb]
                E.node("tw", T["w"])
                E.node("tt", T["ts"][m0][0])
                E.node("ts", T["ts"][m0][1])
                E.node("tt1", T["ts"][m0 + k][0])
                E.node("ts1", T["ts"][m0 + k][1])
                nm = "%sTay_%d_%s_%d" % (PRE, j, sg(neg), m0)
                _write(nm, "Taylor steps %d..%d of exp(%si 2pi angleAt_%d) (`JBlockT.tstep`)."
                       % (m0, m0 + k, "-" if neg else "", j), D, "".join(d + "\n" for d in E.defs),
                       "(JBlockT.tstep %d %s %d %d tw tt ts tt1 ts1).ok 2 gW lgPe gCfg jbk lg00Emb lgProg = true"
                       % (j, tf(neg), m0, k))
                plan.append(dict(name=nm, kind="tstep", heavy=2 * k, imports=3, exports=2))
            E.defs = list(data_head) + [emb]
            E.node("tw", T["w"])
            E.node("ts", T["ts"][N][1])
            E.node(kname(j, neg, 1), e)
            nm = "%sTexp_%d_%s" % (PRE, j, sg(neg))
            _write(nm, "The exponential exp(%si 2pi angleAt_%d) from its partial sum of degree %d (`JBlockT.texp`)."
                   % ("-" if neg else "", j, N), D, "".join(d + "\n" for d in E.defs),
                   "(JBlockT.texp %d %s %d tw ts %s).ok 2 gW lgPe gCfg jbk lg00Emb lgProg = true"
                   % (j, tf(neg), N, kname(j, neg, 1)))
            plan.append(dict(name=nm, kind="texp", heavy=0, imports=2, exports=1))
        else:
            E.defs = list(data_head) + [emb]
            E.node(kname(j, neg, 1), e)
            nm = "%sExp_%d_%s" % (PRE, j, sg(neg))
            _write(nm, "The exponential block (`jExpNode`): exp(%si 2pi angleAt_%d), Taylor degree %d."
                   % ("-" if neg else "", j, N), D, "".join(d + "\n" for d in E.defs),
                   "(JBlockX.expo %d %s %d %s).ok 2 gW lgPe gCfg jbk lg00Emb lgProg = true"
                   % (j, tf(neg), N, kname(j, neg, 1)))
            plan.append(dict(name=nm, kind="expo", heavy=2 * N + 1, exports=1))
        outs = pows_[(j, neg)]
        if outs and not pow_k:
            E.defs = list(data_head) + [emb]
            E.node(kname(j, neg, 1), e)
            for m, o in enumerate(outs, 2):
                E.node(kname(j, neg, m), o)
            nm = "%sPow_%d_%s" % (PRE, j, sg(neg))
            _write(nm, "The power block (`jPowsAux`): exp(%si 2pi angleAt_%d)^m, m = 2..%d."
                   % ("-" if neg else "", j, len(outs) + 1), D, "".join(d + "\n" for d in E.defs),
                   "(JBlockX.pows %d %s %s [%s]).ok 2 gW lgPe gCfg jbk lg00Emb lgProg = true"
                   % (j, tf(neg), kname(j, neg, 1),
                      ", ".join(kname(j, neg, m) for m in range(2, len(outs) + 2))))
            plan.append(dict(name=nm, kind="pows", heavy=len(outs), imports=1, exports=len(outs)))
        elif outs:
            # powers from any power (`JBlockT.pows`), pow_k each: from m0 = 1 (cur = base), then m0 = 1 + pow_k, ...
            for g in range(0, len(outs), pow_k):
                m0 = 1 + g
                E.defs = list(data_head) + [emb]
                E.node(kname(j, neg, 1), e)
                if m0 > 1:
                    E.node(kname(j, neg, m0), outs[m0 - 2])
                chunk = list(range(m0 + 1, min(m0 + pow_k, len(outs) + 1) + 1))
                for m in chunk:
                    E.node(kname(j, neg, m), outs[m - 2])
                nm = "%sPow_%d_%s_%d" % (PRE, j, sg(neg), m0)
                _write(nm, "Powers exp(%si 2pi angleAt_%d)^m, m = %d..%d, from the power %d (`JBlockT.pows`)."
                       % ("-" if neg else "", j, chunk[0], chunk[-1], m0), D, "".join(d + "\n" for d in E.defs),
                       "(JBlockT.pows %d %s %d %s %s [%s]).ok 2 gW lgPe gCfg jbk lg00Emb lgProg = true"
                       % (j, tf(neg), m0, kname(j, neg, 1), kname(j, neg, m0),
                          ", ".join(kname(j, neg, m) for m in chunk)))
                plan.append(dict(name=nm, kind="pows", heavy=len(chunk), imports=2, exports=len(chunk)))
    char_slots = {}
    for j in D["live"]:
        if ops[j][0] == "char":
            char_slots.setdefault(tuple(ops[j][1]), []).append(j)
    keys = sorted(char_slots)
    fac_node = lambda i, neg, m: E_[(i, neg)] if m == 1 else pows_[(i, neg)][m - 2]
    # character groups: at most `--char-keys` keys (2 heavy steps each) and `--char-io` imports + exports
    # (V2-PACKED-JET-LOW: 17 keys with 57 exports exceeded 4 GiB)
    ck = int(next((x.split("=")[1] for x in sys.argv if x.startswith("--char-keys=")), "8"))
    cio = int(next((x.split("=")[1] for x in sys.argv if x.startswith("--char-io=")), "48"))
    kfacs = lambda ks: {(i, ki < 0, abs(ki)) for k in ks for i, ki in enumerate(k) if ki}
    groups, cur = [], []
    for k in keys:
        nxt = cur + [k]
        if cur and (len(nxt) > ck or len(kfacs(nxt)) + sum(len(char_slots[x]) for x in nxt) > cio):
            groups.append(cur)
            nxt = [k]
        cur = nxt
    if cur:
        groups.append(cur)
    for g, ks in enumerate(groups):
        facs = sorted(kfacs(ks))
        E.defs = list(data_head) + [emb]
        for (i, neg, m) in facs:
            E.node(kname(i, neg, m), fac_node(i, neg, m))
        ents = sorted(j for k in ks for j in char_slots[k])
        for j in ents:
            E.node("chr_%d" % j, S[j])
        E.defs.append("def facs : List (JKey × JNode LGF) :=\n  [%s]\n" % ",\n   ".join(
            "(%s, %s)" % (klit(*f), kname(*f)) for f in facs))
        E.defs.append("def entries : List (ℕ × JNode LGF) :=\n  [%s]\n" % ",\n   ".join(
            "(%d, chr_%d)" % (j, j) for j in ents))
        nm = "%sChr_%d" % (PRE, g)
        _write(nm, "A character block (`jCharsOk`): %d keys, %d character slots." % (len(ks), len(ents)), D,
               "".join(d + "\n" for d in E.defs),
               "(JBlockX.chars facs entries).ok 2 gW lgPe gCfg jbk lg00Emb lgProg = true")
        plan.append(dict(name=nm, kind="chars", heavy=2 * len(ks), imports=len(facs), exports=len(ents)))
    only = next((int(x.split("=")[1]) for x in sys.argv if x.startswith("--only=")), None)
    for q, (kind, v) in enumerate(seq):
        if kind == "wit":
            j = v
            a = ops[j][1]
            E.defs = list(data_head) + [emb]
            E.node("wna", S[a])
            cand = wits[j]
            E.node("wcand", JG.Node(False, cand.A, cand.e, cand.x, 0, cand.nb))
            E.node("wout", S[j])
            if ops[j][0] == "inv":
                st_ = "(JBlockW.inv %d %d wna wcand.x wout).ok 2 gW lgPe gCfg jbk lg00Emb lgProg = true" % (a, j)
            else:
                st_ = ("(JBlockW.sqrt %d %d wna wcand.x 1 1 (1 / 2 : ℚ) wout).ok 2 gW lgPe gCfg jbk lg00Emb lgProg"
                       " = true" % (a, j))
            nm = "%s%s_%d" % (PRE, "Inv" if ops[j][0] == "inv" else "Sqrt", j)
            _write(nm, "The %s block of slot %d (operand %d): the candidate's residual (`JetWit.lean`)."
                   % (ops[j][0], j, a), D, "".join(d + "\n" for d in E.defs), st_)
            plan.append(dict(name=nm, kind=ops[j][0], heavy=2, imports=1, exports=1))
            continue
        c, ch = v, chunks[v]
        defined = {t[0] for t in ch}
        imp = sorted({x for t in ch for x in reads(t)} - defined)
        exp = sorted(j for j in defined if any(qq > q for qq in later.get(j, ())) or j in wanted)
        hv_c = sum((1 if t[1] else 0) + (1 if t[2] else 0) for t in ch)
        plan.append(dict(name="%sSeg_%d" % (PRE, c), kind="seg", first=ch[0][0], last=ch[-1][0], steps=len(ch),
                         heavy=hv_c, imports=len(imp), exports=len(exp)))
        if only is not None and c != only:
            continue
        E.defs = list(data_head)
        for j in imp:
            E.node("imp_%d" % j, S[j])
        E.defs.append("def imports : List (ℕ × JNode LGF) :=\n  [%s]\n" % ",\n   ".join(
            "(%d, imp_%d)" % (j, j) for j in imp))
        E.defs.append("def steps : List JStep :=\n  [%s]\n" % ",\n   ".join("(%d, %d, %d)" % t for t in ch))
        for j in exp:
            E.node("exp_%d" % j, S[j])
        E.defs.append("def exports : List (ℕ × JNode LGF) :=\n  [%s]\n" % ",\n   ".join(
            "(%d, exp_%d)" % (j, j) for j in exp))
        _write("%sSeg_%d" % (PRE, c), "Segment %d of %d (`jSegOk`): slots %d..%d, %d steps (%d heavy), %d imports, %d "
               "exports." % (c, len(chunks), ch[0][0], ch[-1][0], len(ch), hv_c, len(imp), len(exp)), D,
               "".join(d + "\n" for d in E.defs),
               "jSegOk 2 gW lgPe gCfg jbk lgProg %d imports steps exports = true" % ch[0][0])
    # the wanted slots: each exported by its segment
    for j in wanted:
        assert j in seg_of, ("wanted slot outside the segments", j)
    meta = dict(lg00_cert_commit=D["lg00_cert_commit"], live=len(D["live"]), steps=len(steps),
                heavy=sum((1 if t[1] else 0) + (1 if t[2] else 0) for t in steps),
                products=sum(1 for t in steps if t[1]), in_place=sum(1 for t in steps if t[2]),
                constants=sum(1 for t in steps if ops[t[0]][0] == "const"), heavy_max=heavy_max,
                book={k: (v if k in ("lb", "lr", "lrb", "ln", "smax", "ls", "lsb", "off", "w", "P", "lc", "lrc", "lnc") else
                          "2^%d" % v.bit_length()) for k, v in bk.__dict__.items()},
                blocks=plan, wanted={str(j): [float(F(S[j].r, 2 ** P)), float(F(S[j].nb, 2 ** P))]
                                     for j in sorted(wanted)})
    with open(os.path.join(OUT, PRE + "Plan.json"), "w") as f:
        json.dump(meta, f, indent=1)
    print(json.dumps({k: v for k, v in meta.items() if k not in ("blocks", "wanted")}, indent=1))
    print("segments", len(chunks), "max imports+exports", max(b["imports"] + b["exports"] for b in plan
                                                                if b["kind"] == "seg"))


def _data_head(C, bk, D):
    dco = os.path.join(CERT, "Data", "DCoeffs.lean")
    cert = os.path.join(CERT, "Data", "Cert.lean")
    out = [G.grab(dco, "lgD4"), G.grab(cert, "lg00Pi").replace("def lg00Pi ", "def lgPe "),
           "def gW : CertWeight := ⟨(29 / 5000 : ℚ), lgD4⟩\n",
           "def gCfg : ModelConfig LGF := ⟨%d, 30, 12, CertFixed.toMant lgP, []⟩\n" % (24 if STAGE == "Low" else 48),
           ("def jbk : JBook where\n  Lb := %s\n  LU0 := %s\n  Lw := %s\n  q := %d\n  lb := %d\n  lr := %d\n"
            "  lrb := %d\n  ln := %d\n  aW := %d\n  aB := %d\n  smax := %d\n  ls := %d\n  lsb := %d\n  off := %d\n"
            "  P := %d\n  aC := %d\n  lc := %d\n  lrc := %d\n  lnc := %d\n"
            % (JG.lay_lit(C.Lb), JG.lay_lit(C.LU0), JG.lay_lit(C.Lw), Q, bk.lb, bk.lr, bk.lrb, bk.ln, bk.aW, bk.aB,
               bk.smax, bk.ls, bk.lsb, bk.off, bk.P, bk.aC, bk.lc, bk.lrc, bk.lnc))]
    ops = D["ops"]
    names = []
    for c0 in range(0, len(ops), 200):
        nm = "ops_%d" % (c0 // 200)
        names.append(nm)
        out.append("def %s : List SlpOp :=\n  [%s]\n" % (nm, ",\n   ".join(JG.op_lit(op) for op in ops[c0:c0 + 200])))
    out.append("def lgProg : Slp := ⟨%s%s⟩\n" % (" ++\n    (".join(names), ")" * (len(names) - 1)))
    return out


def _emb_text():
    data = os.path.join(CERT, "Data")
    comps = ["lg00Angle0_0", "lg00Angle1_0", "lg00Action0_0", "lg00Action1_0"]
    txt = "".join(G.grab(os.path.join(data, "E0.lean"), nm) + "\n" for nm in comps)
    return TERM_ABBREVS + txt + G.grab(os.path.join(data, "Cert.lean"), "lg00Emb")


# the term abbreviations of lg00-cert's data literals (as the B3 probes)
TERM_ABBREVS = ("def dz (n : ℕ) : ℤ := if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)\n\n"
                "abbrev tm (k₀ k₁ re im : ℕ) : CertKey × CC LGF := ([dz k₀, dz k₁], ⟨⟨dz re⟩, ⟨dz im⟩⟩)\n\n"
                "abbrev tr (k₀ k₁ re : ℕ) : CertKey × CC LGF := ([dz k₀, dz k₁], ⟨⟨dz re⟩, ⟨0⟩⟩)\n\n"
                "abbrev tz (k₀ k₁ v : ℕ) : CertKey × ℤ := ([dz k₀, dz k₁], dz v)\n\n")


HEAD = JG.HEAD.replace("abbrev LGF : Type := CertFixed 128\n",
                       "abbrev lgP : ℕ := 128\n\nabbrev LGF : Type := CertFixed lgP\n")
if STAGE == "Full":
    HEAD = HEAD.replace("public import KAM.CertificateSharp.Packed.JetIngest",
                        "public import KAM.CertificateSharp.Packed.JetStage").replace(
        "LG00's cfgLow jet chain", "LG00's cfgFull jet chain").replace(
        "generated by `scripts/packed/jet_gate_gen.py`", "generated by `scripts/packed/jet_low_gen.py --stage=Full`")


def _write(name, doc, D, body, stmt):
    if len(stmt) + 4 > 100:  # the statement within 100 columns: the block's arguments on their own line
        stmt = stmt.replace(").ok ", ").ok\n      ", 1)
    txt = HEAD % (name, doc, 0, len(D["ops"]), D["lg00_cert_commit"][:8], name) + body
    txt += "\nset_option profiler true\nset_option profiler.threshold 1\n\ntheorem probe :\n    %s := by\n" \
           "  decide +kernel\n\nend KAM.CertificateSharp.Packed.JGate.%s\n" % (stmt, name)
    with open(os.path.join(OUT, name + ".lean"), "w") as f:
        f.write(txt)


if __name__ == "__main__":
    main()
