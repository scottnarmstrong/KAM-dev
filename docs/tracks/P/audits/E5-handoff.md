# E5 prover handoff (P14; branch inp-p14-e5, 8248376b; off inp; offloaded package run by the main orchestrator; prover on claude-10)


**Files:** new `KAM/Planetary/Exponential/LocalComplexification.lean`. KAM.lean not touched (lint reports it out of date; orchestrator regenerates).

**Declarations proved (signatures verbatim from P14Signatures.lean):** `KAM.Planetary.complex_division`,
`KAM.Planetary.local_complex_restriction`, `KAM.Planetary.local_analytic_complexification`.
These are all declarations the signature file/design assign to E5 (row E5). Others in the signature file belong to other packages:
`real_trace_identity` (E6 row), `secular_parametric_integral` (S4), `angle_quadrature` (S9), `interval_constancy` (A5); not done here by design.

**Approach:**
- complex_division: `div_eq_mul_inv`, `DifferentiableOn.mul`, `DifferentiableOn.inv`.
- local_complex_restriction: `complexifyPhase = realInclusion₂` (existing, KAM.Strip.RealRestriction) CLM; chain rule with `HasFDerivAt.restrictScalars` and `Complex.reCLM`.
- local_analytic_complexification: reuse P5-CL `local_real_complexification` on `Fin (d+d) → ℝ` for `f ∘ unpack`; transport via ℂ-linear isometric packing `Fin.append` (helpers `e5Pack`, `e5Unpack`, `e5Unpack_pack`, `norm_e5Pack`, `e5Pack_complexify`; names grepped, new).

**Checks:** gate build of KAM.Planetary.Exponential.LocalComplexification: success (no warnings printed, no sorry). `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK; only message is "KAM.lean is out of date" (expected). Default heartbeats, no overrides.
`#print axioms` for all three: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations:** none. No signature changes. Imports: Mathlib, frozen ComplexifyPhase Def, KAM.Strip.Analytic/RealRestriction, KAM.Planetary.PGAssembly.ComplexLocal (no providers/theorem anchors). Feasibility gate N1 for E5: passed at default resources.

AUDIT FOCUS (design docs/tracks/P/design/P14-LEAN-DESIGN.md row E5, Appendix A and node rows; audits DESIGN-P14-design-audit-{1,2}.md; signatures .drafts/design/P14Signatures.lean): (1) complex_division, local_complex_restriction, local_analytic_complexification = signature file exactly, and COMPLETE for E5 (the prover assigns real_trace_identity to E6, secular_parametric_integral to S4, angle_quadrature to S9, interval_constancy to A5: confirm against the design rows); (2) proofs sound (real analytic power series, restrictScalars; the existing P5-CL local_real_complexification reused if applicable, not duplicated); no added premises; (3) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/Exponential/LocalComplexification.lean.
