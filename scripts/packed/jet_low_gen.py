#!/usr/bin/env python3
"""V2-PACKED-JET-LOW: LG00's whole cfgLow jet chain as packed blocks (untrusted tooling; the kernel re-checks).

Reads `jet_extract_low.py`'s JSON (the program, the live slots, the leaves computed by lg00-cert's bit-exact mirror)
and runs the whole chain in Python with the bit-exact mirror of `KAM/CertificateSharp/Packed/Jet*.lean`
(`jet_gate_gen.py`), then cuts it into the blocks of `JetChain.lean`:
  - block 0: the action block (`jActionsOk`: the 20 action slots packed from the embedding);
  - block 1: the given block (V2-PACKED-JET-LOW M1: the characters, `inv` and `sqrt`, as hypotheses);
  - segments (`jSegOk`): the constants, sums and products in slot order, at most `--heavy` heavy steps each
    (box-by-box products and reduces in place). A box node above scale 2^P is reduced in place only when a product
    reads it or it is wanted; sums keep the larger scale.
Every import of a block is an export of an earlier block (by construction). Writes one probe per checked block
(segments and actions) into $V2P_GATE_DIR (default .lake/v2-packed-jet/low), and LowPlan.json.
Usage: python3 -I scripts/packed/jet_low_gen.py LOW.json [--heavy=34] [--only=K]
"""
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import jet_gate_gen as JG     # noqa: E402
G, GG = JG.G, JG.GG
P, Q, H, n = JG.P, JG.Q, JG.H, JG.n
OUT = os.environ.get("V2P_GATE_DIR", os.path.join(JG.ROOT, ".lake", "v2-packed-jet", "low"))
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


def run(C, bk, D, lb, aC, decide):
    """The whole chain. `decide` (pass 1) fixes the steps; then the same steps are replayed exactly."""
    ops, leaves = D["ops"], D["leaves"]
    S, steps, st = {}, [], {"aW": 0, "aB": 0, "smax": 0, "lb": 0}
    for i in D["live"]:
        op = ops[i]
        lv = leaves.get(str(i))
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
    aC = max(abs(v) for lv in D["leaves"].values() if lv["kind"] == "const" for _, v in lv["re"] + lv["im"])
    # pass 1: wide slots, `lb` to a fixed point
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
    S, steps2, _ = run(C, bk, D, lb, aC, decide)
    assert steps2 == steps
    plan_and_emit(C, bk, D, S, steps, heavy_max, wanted)


def plan_and_emit(C, bk, D, S, steps, heavy_max, wanted):
    ops, leaves = D["ops"], D["leaves"]
    actions = sorted(int(j) for j, v in leaves.items() if v["kind"] == "action")
    given = sorted(int(j) for j, v in leaves.items() if v["kind"] in ("char", "inv", "sqrt", "exp"))
    chunks, cur, hv = [], [], 0
    for t in steps:
        h = (1 if t[1] else 0) + (1 if t[2] else 0)
        if cur and hv + h > heavy_max:
            chunks.append(cur)
            cur, hv = [], 0
        cur.append(t)
        hv += h
    chunks.append(cur)
    reads = lambda t: [x for x in ops[t[0]][1:3]] if ops[t[0]][0] in ("add", "mul") else []
    # a slot is exported by its segment when a later segment reads it or it is wanted
    seg_of = {t[0]: c for c, ch in enumerate(chunks) for t in ch}
    later = {}
    for c, ch in enumerate(chunks):
        for t in ch:
            for x in reads(t):
                if x in seg_of and seg_of[x] != c:
                    later.setdefault(x, set()).add(c)
    data_head = _data_head(C, bk, D)
    os.makedirs(OUT, exist_ok=True)
    plan = []
    E = JG.Emit(C)
    # the action block
    E.defs = list(data_head)
    E.defs.append(_emb_text())
    for j in actions:
        E.node("act_%d" % j, S[j])
    E.defs.append("def actions : List (ℕ × JNode LGF) :=\n  [%s]\n" % ",\n   ".join(
        "(%d, act_%d)" % (j, j) for j in actions))
    _write("LowAct", "The action block (`jActionsOk`): %d action slots packed from the embedding." % len(actions),
           D, "".join(d + "\n" for d in E.defs), "jActionsOk 2 gW lgPe gCfg jbk lg00Emb lgProg actions = true")
    plan.append(dict(name="LowAct", kind="actions", exports=len(actions)))
    plan.append(dict(name="(given)", kind="given", exports=len(given)))
    only = next((int(x.split("=")[1]) for x in sys.argv if x.startswith("--only=")), None)
    for c, ch in enumerate(chunks):
        defined = {t[0] for t in ch}
        imp = sorted({x for t in ch for x in reads(t)} - defined)
        exp = sorted(j for j in defined if c in () or any(cc > c for cc in later.get(j, ())) or j in wanted)
        hv_c = sum((1 if t[1] else 0) + (1 if t[2] else 0) for t in ch)
        plan.append(dict(name="LowSeg_%d" % c, kind="seg", first=ch[0][0], last=ch[-1][0], steps=len(ch),
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
        _write("LowSeg_%d" % c, "Segment %d of %d (`jSegOk`): slots %d..%d, %d steps (%d heavy), %d imports, %d "
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
    with open(os.path.join(OUT, "LowPlan.json"), "w") as f:
        json.dump(meta, f, indent=1)
    print(json.dumps({k: v for k, v in meta.items() if k not in ("blocks", "wanted")}, indent=1))
    print("segments", len(chunks), "max imports+exports", max(b["imports"] + b["exports"] for b in plan
                                                                if b["kind"] == "seg"))


def _data_head(C, bk, D):
    dco = os.path.join(CERT, "Data", "DCoeffs.lean")
    cert = os.path.join(CERT, "Data", "Cert.lean")
    out = [G.grab(dco, "lgD4"), G.grab(cert, "lg00Pi").replace("def lg00Pi ", "def lgPe "),
           "def gW : CertWeight := ⟨(29 / 5000 : ℚ), lgD4⟩\n",
           "def gCfg : ModelConfig LGF := ⟨24, 30, 12, CertFixed.toMant lgP, []⟩\n",
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


def _write(name, doc, D, body, stmt):
    txt = HEAD % (name, doc, 0, len(D["ops"]), D["lg00_cert_commit"][:8], name) + body
    txt += "\nset_option profiler true\nset_option profiler.threshold 1\n\ntheorem probe :\n    %s := by\n" \
           "  decide +kernel\n\nend KAM.CertificateSharp.Packed.JGate.%s\n" % (stmt, name)
    with open(os.path.join(OUT, name + ".lean"), "w") as f:
        f.write(txt)


if __name__ == "__main__":
    main()
