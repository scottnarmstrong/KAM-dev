#!/usr/bin/env python3
"""LOCK-GEN part 3: regenerate the SO-LOCK-COST gate's G2 segment boundaries for the landed program (untrusted).

    python3 lock_gate.py [GATE_DIR]

The gate's generator `G0_emit.lean` placed the tail segments at s = 3158 − L, LOCK-GEN-2's count for the κ-scaled
`ham`; the gate compiles the bare `lockHamExpr` (3116 ops), so `take L` truncated those tails to 758 and 358 ops.
This script, with no Lean run:
 1. reprints op literals in G0's `opLit` / `chunked` format and checks them byte for byte against the gate's own
    `G1lit.lean` (whole program) and every existing `G2_*` segment;
 2. rewrites `G0_emit.lean` (original kept as `G0_emit.lean.orig-3158`): G1lit length n, tail segments at
    `lockJ.prog.ops.length − L`, guarded by the expected n;
 3. writes `G2_segments.json`: per (P, s, L) the op range, op census, and the sha256 of the `segLit` text the
    regenerated G0 will print (accIn / accOut need the exact Lean ball pass, so the probe files themselves are
    produced by `run_gate.sh emit`);
 4. moves the stale tail probes `G2_P*_s{2358,2758}_*` to `stale-3158/`.
"""
import os, sys, json, hashlib, shutil
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lock_ham as LH                 # noqa: E402
import lock_jet as LJ                 # noqa: E402
from lock_emit import OMEGA_R, CENTRE  # noqa: E402

GATE = "/mnt/HC_Volume_106379410/kam-data/so-lock/gate"
PS, LS, OLD_N = (128, 320), (400, 800), 3158


def q_lit(q):
    return "((%d : ℚ) / %d)" % (q.numerator, q.denominator)


def op_lit(o):
    t = o[0]
    if t == "const":
        return "SlpOp.const %s %s (%d)" % (q_lit(o[1]), q_lit(o[2]), o[3])
    if t == "char":
        return "SlpOp.char [" + ", ".join("(%d : ℤ)" % i for i in o[1]) + "]"
    return "SlpOp.%s %s" % (t, " ".join(str(x) for x in o[1:]))


def chunked(nm, ty, lits):
    """G0's `chunked`: `def nm_i` blocks of 200 joined by `++`."""
    cs = [lits[i:i + 200] for i in range(0, len(lits), 200)]
    s = "".join("def %s_%d : List %s := [\n  " % (nm, i, ty) + ",\n  ".join(c) + "]\n" for i, c in enumerate(cs))
    return s + "def %s : List %s := " % (nm, ty) + (" ++ ".join("%s_%d" % (nm, i) for i in range(len(cs))) or "[]") + "\n"


def block(text, nm):
    """The `chunked` text of `nm` inside a probe file."""
    i = text.index("def %s_0 " % nm)
    j = text.index("\n", text.index("def %s : " % nm)) + 1
    return text[i:j]


def main():
    g = sys.argv[1] if len(sys.argv) > 1 else GATE
    ops = [LJ.norm_op(o) for o in LJ.jet(2, LH.lock_ham_expr(OMEGA_R, CENTRE))["prog"]]
    n, lits = len(ops), [op_lit(o) for o in ops]
    seg_text = lambda s, L: chunked("segLit", "SlpOp", lits[s:s + L])
    # 1. printer check against the gate's own files
    checks = {"G1lit.lean": block(open(os.path.join(g, "G1lit.lean")).read(), "lockOpsLit")
              == chunked("lockOpsLit", "SlpOp", lits)}
    for P in PS:
        for L in LS:
            for s in (0, OLD_N - L):
                f = "G2_P%d_s%d_L%d.lean" % (P, s, L)
                if os.path.exists(os.path.join(g, f)):
                    checks[f] = block(open(os.path.join(g, f)).read(), "segLit") == seg_text(s, L)
    print("printer checks", checks)
    assert all(checks.values()), checks
    # 2. regenerated generator
    src = os.path.join(g, "G0_emit.lean")
    orig = src + ".orig-3158"
    if not os.path.exists(orig):
        shutil.copy2(src, orig)
    t = open(orig).read()
    old_lit = "theorem g1lit : (lockOpsLit.length == %d) = true" % OLD_N
    old_loop = "      emitG2 P 0 L\n      emitG2 P (%d - L) L\n" % OLD_N
    assert old_lit in t and old_loop in t
    t = t.replace(old_lit, "theorem g1lit : (lockOpsLit.length == %d) = true" % n)
    t = t.replace("#eval do\n", "-- LOCK-GEN-2 Part 3 (lock_gate.py): landed program length %d; tails at n - L.\n"
                  "def lockN : ℕ := %d\n\n#eval do\n" % (n, n))
    t = t.replace(old_loop, "      emitG2 P 0 L\n"
                  "      if lockJ.prog.ops.length == lockN then emitG2 P (lockJ.prog.ops.length - L) L\n"
                  "      else IO.println s!\"G2: program length {lockJ.prog.ops.length} ≠ {lockN}, no tail file\"\n")
    open(src, "w").write(t)
    # 3. segment manifest
    segs = []
    for P in PS:
        for L in LS:
            for s in (0, n - L):
                txt = seg_text(s, L)
                segs.append(dict(file="G2_P%d_s%d_L%d.lean" % (P, s, L), P=P, s=s, L=L, ops=[s, min(s + L, n)],
                                 census=dict(Counter(o[0] for o in ops[s:s + L])),
                                 segLit_sha256=hashlib.sha256(txt.encode()).hexdigest()))
    stale = []
    for P in PS:
        for L in LS:
            f = "G2_P%d_s%d_L%d.lean" % (P, OLD_N - L, L)
            if os.path.exists(os.path.join(g, f)):
                os.makedirs(os.path.join(g, "stale-3158"), exist_ok=True)
                shutil.move(os.path.join(g, f), os.path.join(g, "stale-3158", f))
                stale.append(dict(file="stale-3158/" + f, covered=[OLD_N - L, n], ops=n - (OLD_N - L)))
    json.dump(dict(program_length=n, generator="scripts/spin_orbit/lock_gate.py", printer_checks=checks,
                   segments=segs, stale=stale), open(os.path.join(g, "G2_segments.json"), "w"), indent=1)
    print("n", n, "segments", [(d["s"], d["L"]) for d in segs], "stale", stale)


if __name__ == "__main__":
    main()
