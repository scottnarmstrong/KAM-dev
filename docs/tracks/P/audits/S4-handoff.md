# S4 prover handoff (branch inp-p14-s4, 0d8cd7a7; off inp; offloaded P14 package run by the main orchestrator)


**Files:** new `KAM/Planetary/SecularBox/ParametricIntegral.lean` (157 lines). KAM.lean not edited (lint reports "KAM.lean is out of date; run scripts/gen_root_imports.py" — orchestrator to regenerate).

**Declarations:** `KAM.Planetary.secular_parametric_integral` (signature verbatim; the only S4 row declaration). Helpers (unique names, grepped): `sb_param_integral_continuousOn`, `sb_param_integral_hasFDerivAt`, `sb_param_integral_contDiffOn` (general E×P→H, any finite measure-on-compacts μ).
Graph steps: only `p14:sb-sm-3; p8:e-diff` (audit table maps just this theorem to S4); nothing assigned to another package found.

**Approach:** induction on k (generalised over the codomain H, all types in one universe `u` since `E →L H` appears). k=0: `continuousAt_of_dominated` with a constant bound from compactness of closedBall×Q. Step: `hasFDerivAt_integral_of_dominated_of_fderiv_le` with F' = (fderiv G).comp inl bounded on closedBall×Q; fderiv of the integral equals the integral of F' on U, which is C^k by IH; conclude via `contDiffOn_succ_iff_fderiv_of_isOpen`. Imports only Mathlib + frozen `Phase` def.

**Checks:** gate build `KAM.Planetary.SecularBox.ParametricIntegral`: success, no warnings. `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only note is KAM.lean out of date (generated). `#print axioms KAM.Planetary.secular_parametric_integral`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations:** none. No heartbeat issues (default budget). One file-level `set_option linter.unusedSectionVars false` (a linter option, not a resource override).

AUDIT FOCUS (design docs/tracks/P/design/P14-LEAN-DESIGN.md row S4 and its node rows (p14:sb-sm-3, p8:e-diff); P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean): (1) secular_parametric_integral = signature file EXACTLY: compare the universe/type parameters too (the proof generalises over one universe u; the signed statement must be byte-identical, not specialised); and the S4 slice COMPLETE; (2) proof soundness: induction on k, continuousAt_of_dominated with the compactness bound, hasFDerivAt_integral_of_dominated_of_fderiv_le in the step, the domination hypotheses; no added premises; (3) the file-level set_option linter.unusedSectionVars false: a linter option, not a heartbeat override (allowed), but check it hides no meaningful unused section variable in a public statement; (4) hygiene (no EuclideanSpace; no public short name used elsewhere in KAM; no root shadow). Audit ONLY KAM/Planetary/SecularBox/ParametricIntegral.lean.
