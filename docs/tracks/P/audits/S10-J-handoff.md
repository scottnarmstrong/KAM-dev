# S10-J prover handoff (branch inp-s10j, cdea3ad; base inp-s9n; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/Nondegeneracy/DiagonalTensor.lean` (≈172 lines). KAM.lean not edited (lint reports it out of
date: needs `scripts/gen_root_imports.py` by the orchestrator).

**Declarations (signatures verbatim, namespace `KAM.Planetary.Nondegeneracy`):** `jetNorm`, `scalarJet`, `jetMax` (defs);
`f_pol` (bpP:p10:f-pol); `f_leib` (bpP:p10:f-leib). Helpers: `hasDerivAt_diag`, `sum_update_eq_zero`, `sum_update_eq`,
`pol_aux`, `iteratedFDeriv_diag_eq`.

**Approach:** `f_pol`: induction on the order. Differentiating s ↦ T(x+s w)^ν at 0 (`ContinuousMultilinearMap.hasFDerivAt`)
gives ν·T(w,x,…,x)=0 by symmetry; `curryLeft` in the first slot is a symmetric (ν-1)-form with zero diagonal.
`f_leib`: diagonal derivative = 1D `iteratedDeriv` along y+t•v (via `iteratedFDerivWithin_comp_right` on an open set),
then Mathlib `iteratedDeriv_fun_mul`. Uses only `ContDiffOn ⊤` from `AnalyticOnNhd.contDiffOn`.

**Checks:** gate build `KAM.Planetary.Nondegeneracy.DiagonalTensor`: success, no warnings in my file.
`scripts/lint_sources.sh`: only "KAM.lean is out of date" (expected; generated). Lean-line-length check clean.
`#print axioms f_pol` / `f_leib`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations:** none. No heartbeat issues; no statement changes. Quarantine respected (imports
Mathlib and SecularSpectrum.Norms only).

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S10-J and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) statements/definitions = design signatures (jetNorm, scalarJet, jetMax, f_pol, f_leib); (2) proofs sound (iteratedFDeriv); no added premises; (3) hygiene. Audit ONLY Nondegeneracy/DiagonalTensor*.lean (compare with branch inp-s9n).
