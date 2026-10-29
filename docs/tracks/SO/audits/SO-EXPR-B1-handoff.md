# SO-EXPR-B1 prover handoff (branch inp-soexprb, b67f81c3; track SO package run by the main orchestrator)


## Files (all new, all Lean modules)
- `KAM/Certificate/Expr/Slp.lean` (125 lines): `SlpOp`, `Slp`, `HamJet`, `phaseNat` verbatim from SOSignatures §D;
  `Slp.val` defined (not sorry) as the `getD` of a left fold `Slp.vals` (helpers `slpConstVal`, `SlpOp.step`);
  prefix/append lemmas (`Slp.val_append`: appending ops never changes an existing slot).
- `KAM/Certificate/Expr/DiffCalculus.lean` (163): `jetDeriv u f z = fderiv ℂ f z u`, `JetSmoothOn`, rules on an open
  set (add, mul, exp, inv, congr), `dirVec`, `phaseBasis_eq_dirVec`, `iteratedFDeriv_two_eq_jetDeriv`.
- `KAM/Certificate/Expr/DiffBuild.lean` (316): program builder with zero folding (`Option ℕ` slots, `none` = identically 0),
  `Realizes`, computation combinators (`SlpComp`, `SlpEnt`), tables `slpTab1/2`.
- `KAM/Certificate/Expr/DiffNode.lean` (~560): `SlpNode` (value slot + d1/d2 tables), `SlpNode.Sound`, `slpFinish`, nodes
  for const/action/char/add/mul/exp/inv, each with a soundness theorem.
- `KAM/Certificate/Expr/Diff.lean` (~400): `slpCompile`, `HamExpr.jet`, `HamExpr.jet_v0/jet_d1/jet_d2` exactly as signed.
  (Extra modules DiffCalculus/DiffBuild/DiffNode are internal splits of the design's `Expr/Diff`; `Diff` is the facade.)

## Approach
`HamExpr` compiles bottom-up, each sub-expression once (sharing), into a node: value slot plus tables of first and second
directional derivatives (directions `dirVec n i`, `i < 2n`, = `phaseNat` order). Product/`exp`/`inv` rules are
slot formulas (`(x⁻¹)' = -x⁻¹x⁻¹x'`, `(x⁻¹)'' = 2x⁻³x'x' - x⁻²x''`); zero/constant folding by `none` slots; sin/cos
go through `exp` (constants `±i/2`, `1/2`) and sin/cos modes through characters `e^{±2πik·θ}` (`negKey`); `div` = product with `inv`;
`pow a m` = m-fold product (m=0: constant 1). Soundness is proved per primitive on an open set with smooth
operands, with `SlpEnt` combinators making each entry proof a one-liner. `jet_v0` uses `S = ∅` (value claim is global).
`iteratedFDeriv 2` is identified with `jetDeriv u (jetDeriv v f)` for `C²` functions.
Slot 0 of the jet program is `const 0 0 0` (folded entries read slot 0, the signature's `getD … 0` default).
No operation is ever dropped from the program: only identically-zero derivative slots are folded, so every `inv`
operand stays in the program (audit-2 obligation for SO-BALL's `nonvanishingOn_of_balls`).

## Extension point for B2 (d3)
`SlpNode` gets a field `d3`, `SlpNode.Sound` a clause, `slpFinish` a `slpTab3` (same `slpMapSt` pattern), and each node
a third-order formula + `jetDeriv3_*` rule; `HamExpr.jet.d3` is `[]` here (B2 replaces it). jet_d1/d2 proofs only use `.d1/.d2`.

## Checks (exact)
- Gate builds: `inp_lake_build.sh /root/code/KAM-inp-soexprb KAM.Certificate.Expr.Diff` -> `Built KAM.Certificate.Expr.Diff`, no
  warnings from my files (only Basic.lean:85 unused `hS`, SO-EXPR-A's).
- `sh scripts/lint_sources.sh`: `check_lean_modules: PASS`, frozen anchors OK, ABI hashes OK; only message:
  `KAM.lean is out of date; run scripts/gen_root_imports.py` (expected: new modules; I do not edit KAM.lean).
- No line over 100 columns; no sorry/axiom/maxHeartbeats/native_decide/EuclideanSpace; all files < 600 lines.
- `decide +kernel` sanity (scratch file, not committed): for `ex : HamExpr 1 := div (add cosMode[1] (exp action0)) (add (const 1)
  (pow (action 0) 2))`, `ex.jet.d1.length = 2`, `d2.length = 2`, and `ex2 : HamExpr 2 := sin (cos (cosMode[1,2] + sinMode[0,1]))`
  `d2.length = 4` hold by `decide +kernel` (so `HamExpr.jet` is kernel-reducible). Program sizes: ex 72 ops, ex2 228 ops.
- `#print axioms HamExpr.jet_v0 / jet_d1 / jet_d2`: `[propext, Classical.choice, Quot.sound]` each.

## Uncertainties / notes
- Signatures matched verbatim (`Slp.val` signed with sorry body; mine is the fold definition). No signed statement was false.
- `jet_d1/d2` direction convention: `d2[a][b]` = `∂_a ∂_b H` (= `iteratedFDeriv ![pb a, pb b]`, matching the signature).
- No dependency pruning of unused slots (folding only); programs are larger than a pruned jet; add pruning later only if
  SO-REPLAY needs it, preserving denominator-validation slots.
- Short names added: `SlpNode`, `SlpComp`, `SlpEnt`, `Realizes`, `SlotOk`, `JetSmoothOn`, `jetDeriv`, `dirVec`, `negKey`, `slp*`;
  all grep-checked absent from KAM before use (`Realizes` only matched as part of Real.* text).
- Suspected errata: none. Deviations: none beyond the extra internal modules and `d3 := []`.

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md; design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md, Revision 4, passed its design audit); draft signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean. Signature file section D, the SO-EXPR part B1 slice (SlpOp, Slp, Slp.val, HamJet, phaseNat, HamExpr.jet, jet_v0, jet_d1, jet_d2; NOT jet_d3). Stacked on inp-soexpr (SO-EXPR-A, passed, landing). Check that jet_d1 and jet_d2 identify the compiled program's values with fderiv and iteratedFDeriv of HamExpr.eval EXACTLY (all directions, on the open set where every divisor is nonvanishing), with no hypothesis beyond the signed ones, and that Slp.val is kernel-evaluable as the design requires.

AUDIT FOCUS: the package's signed declarations match the draft signatures verbatim; every proof is sound with no added premise; the slice the design assigns to these modules is complete. Audit ONLY KAM/Certificate/Expr/{Slp,Diff,DiffBuild,DiffCalculus,DiffNode}.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib, no harmful root shadow, lines <= 100, no native_decide or axiom.
