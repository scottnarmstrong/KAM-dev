# SO-HAMX prover handoff (branch inp-sohamx, dcdd492d; track SO package run by the main orchestrator)

Files: KAM/SpinOrbit/HamExpr.lean (new, ~85 lines).
Declarations: `KAM.SpinOrbit.soHamExpr` (verbatim body), `soHamExpr_eval` (= `soHC`), `soHamExpr_clock`.
Helpers (new, unique short names): `soHamExpr_eval_foldr`, `soHamExpr_list_sum_range`.
Approach: eval of the foldr by list induction; list sum -> Finset.range sum; soModes = image (·+1) (range 7);
clock via `soHamExpr.eval = soHC`, `fderiv_soHC_apply`, `phaseBasis_inr`.
Checks: gate build `KAM.SpinOrbit.HamExpr` succeeded (no warnings in my file); `scripts/lint_sources.sh`:
check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK; only "KAM.lean is out of date" (generated; not edited).
`#print axioms soHamExpr_eval` and `soHamExpr_clock`: [propext, Classical.choice, Quot.sound].
Uncertainties: none; signatures as signed. No errata, no deviations. No heartbeat issues.

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md; design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md, Revision 4, passed its design audit); draft signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean. Signature file section I 'KAM/SpinOrbit/HamExpr.lean' (soHamExpr, soHamExpr_eval = the landed complexified lunar Hamiltonian soHC of KAM/SpinOrbit/Hamiltonian.lean, soHamExpr_clock). Stacked on inp-soexpr. Note: owner ruling O5 (14:20) moves the lunar client to a rotated frame in design Revision 5; this package is still audited against the CURRENT signed (original-frame) declarations, which remain valid.

AUDIT FOCUS: the package's signed declarations match the draft signatures verbatim; every proof is sound with no added premise; the slice the design assigns to these modules is complete. Audit ONLY KAM/SpinOrbit/HamExpr.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib, no harmful root shadow, lines <= 100, no native_decide or axiom.
