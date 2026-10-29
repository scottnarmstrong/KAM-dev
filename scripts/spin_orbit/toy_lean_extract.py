#!/usr/bin/env python3
"""Extract the landed jet programs (and, optionally, the landed `Slp.balls`) of the SO toy Hamiltonians.

Untrusted tooling (SO-TOYGEN).  The jet compiler `HamExpr.jet` (KAM/Certificate/Expr/Diff*.lean) and the ball
pass `Slp.balls` (KAM/Certificate/Expr/Ball.lean) are LANDED Lean code.  Instead of re-implementing the jet
compiler in Python, this script writes a scratch Lean file (in a temporary directory, never in the repository),
runs it with `nice -n 5 lake env lean` inside an existing build of the project, and parses the printed JSON.
The Python mirror (toy_arith.py) consumes the extracted programs; the extracted balls are a cross-check of the
Python ball mirror.

    python3 toy_lean_extract.py BUILD_DIR OUT.json [BALLS.json]

BUILD_DIR is a checkout with a built `KAM.Certificate.Expr.Ball` (the shared `inp` build); BALLS.json (optional)
lists ball requests {"toy": name, "rhoH": q, "wH": q, "centre": [q], "radius": [q], "taylorN": N}.
"""
import json, os, subprocess, sys, tempfile

# The toy Hamiltonians (design §8; A-E §J gives `toyHam3` verbatim; `toyHam2`, `toyHam2d` are this package's
# literal choices with p = I_0, J = I_1, q = theta_0).
TOYS = {
    "T2": (2, ".add (.action 1) (.mul (.const (1 / 2)) (.pow (.action 0) 2))"),
    "T2d": (2, ".add (.action 1) (.mul (.mul (.const (1 / 2)) (.pow (.action 0) 2))\n"
               "    (.div (.add (.const 3) (.cosMode [1, 0])) (.add (.const 3) (.cosMode [1, 0]))))"),
    "T3": (3, ".add (.action 2) (.add (.mul (.const (1 / 2)) (.pow (.action 0) 2))\n"
              "    (.mul (.const (1 / 2)) (.pow (.action 1) 2)))"),
}
# The negative toy TR uses the T2 Hamiltonian.

HEADER = r'''import KAM.Certificate.Expr.Ball
open KAM.Certificate

def jq (x : ℚ) : String := "\"" ++ toString x ++ "\""

def opJ : SlpOp → String
  | .const re im deg => s!"[\"C\", {jq re}, {jq im}, {deg}]"
  | .action j => s!"[\"A\", {j}]"
  | .char k => s!"[\"X\", {k}]"
  | .add a b => s!"[\"+\", {a}, {b}]"
  | .mul a b => s!"[\"*\", {a}, {b}]"
  | .exp a => s!"[\"E\", {a}]"
  | .inv a => s!"[\"I\", {a}]"

def jetJ {n : ℕ} (name : String) (e : HamExpr n) : String :=
  let j := e.jet
  "{\"toy\": \"" ++ name ++ "\", \"n\": " ++ toString n ++ ", \"ops\": [" ++
    ", ".intercalate (j.prog.ops.map opJ) ++ "], \"v0\": " ++ toString j.v0 ++ ", \"d1\": " ++
    toString j.d1 ++ ", \"d2\": " ++ toString j.d2 ++ ", \"d3\": " ++ toString j.d3 ++ "}"

def ballJ (b : CC ℚ × ℚ) : String := "[" ++ jq b.1.re ++ ", " ++ jq b.1.im ++ ", " ++ jq b.2 ++ "]"

def ballsJ {n : ℕ} (name : String) (e : HamExpr n) (W : CertWeight) (c r : List ℚ) (N : ℕ) :
    String :=
  match e.jet.prog.balls n W c r N with
  | none => "{\"toy\": \"" ++ name ++ "\", \"balls\": null}"
  | some bs => "{\"toy\": \"" ++ name ++ "\", \"balls\": [" ++ ", ".intercalate (bs.map ballJ) ++ "]}"
'''


def lean_rat(q):
    from fractions import Fraction as F
    q = F(q)
    s = "(%d : ℚ)" % q.numerator if q.denominator == 1 else "((%d : ℚ) / %d)" % (q.numerator, q.denominator)
    return s


def build_source(balls):
    src = [HEADER]
    for name, (n, body) in TOYS.items():
        src.append("def toy%s : HamExpr %d :=\n  %s\n" % (name, n, body))
    for name in TOYS:
        src.append('#eval IO.println (jetJ "%s" toy%s)' % (name, name))
    for req in balls:
        w = "⟨%s, %s⟩" % (lean_rat(req["rhoH"]), lean_rat(req["wH"]))
        c = "[" + ", ".join(lean_rat(x) for x in req["centre"]) + "]"
        r = "[" + ", ".join(lean_rat(x) for x in req["radius"]) + "]"
        src.append('#eval IO.println (ballsJ "%s" toy%s %s %s %s %d)' % (req["toy"], req["toy"], w, c, r,
                                                                        int(req["taylorN"])))
    return "\n".join(src) + "\n"


def run(build_dir, balls=()):
    with tempfile.TemporaryDirectory() as td:
        path = os.path.join(td, "ToyJets.lean")
        with open(path, "w") as f:
            f.write(build_source(balls))
        out = subprocess.run(["nice", "-n", "5", "lake", "env", "lean", path], cwd=build_dir,
                             capture_output=True, text=True)
    if out.returncode != 0:
        raise SystemExit("lean failed:\n" + out.stdout + out.stderr)
    lines = [json.loads(l) for l in out.stdout.splitlines() if l.startswith("{")]
    jets = {d["toy"]: d for d in lines if "ops" in d}
    bls = [d for d in lines if "balls" in d]
    return jets, bls


def main():
    build_dir, out = sys.argv[1], sys.argv[2]
    balls = json.load(open(sys.argv[3])) if len(sys.argv) > 3 else []
    jets, bls = run(build_dir, balls)
    res = {"source": {k: {"n": v[0], "lean": v[1]} for k, v in TOYS.items()}, "jets": jets}
    if balls:
        res["balls"] = [dict(req, result=b["balls"]) for req, b in zip(balls, bls)]
    with open(out, "w") as f:
        json.dump(res, f, indent=1, sort_keys=True)
        f.write("\n")
    print("jets:", {k: len(v["ops"]) for k, v in jets.items()}, " ball requests:", len(bls))


if __name__ == "__main__":
    main()
