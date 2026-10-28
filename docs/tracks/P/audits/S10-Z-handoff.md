# S10-Z prover handoff (branch inp-s10z, 8835bc2; contains inp-s8b (S8-B, audited); offloaded package run by the main orchestrator; prover on claude-12)


Branch inp-s10z, commits 19dbc14 and 8835bc2 (HEAD).

## Files
- new: `KAM/Planetary/Nondegeneracy/AnalyticZeros.lean` (≈260 lines; no other file touched; KAM.lean not edited).

## Declarations (namespace `KAM.Planetary.Nondegeneracy`)
- `rnd_def` (verbatim from the signature file), `analytic_zero_null`, `generic`: statements verbatim, fully proved.
- Helpers: `countable_of_isolated`, `null_zero_of_deriv`, `lineAt`, `insertNth_eq_add`, `volume_null_iff_lines`,
  `measurableSet_zero_inter`, `null_zero_of_dir`, `exists_coord_deriv_ne`, `local_null`.
- "identity/products" in the package-table row has no declaration in P810Signatures.lean, so nothing was written for it
  (the identity theorem is used directly from Mathlib inside `analytic_zero_null`). Orchestrator: confirm that is intended.

## Approach
Local, no induction on dimension. Near x where f is not identically zero, Taylor series (HasFPowerSeriesOnBall.factorial_smul
+ hasSum) gives a coordinate derivative chain with nonzero value at x (multilinear `map_sum` expansion on the standard basis).
Induction on chain length `k` (`local_null`): `∂_j g` has null zero set on V ⇒ `g` does, via `null_zero_of_dir`:
Fubini along coordinate lines (`MeasurableEquiv.piFinSuccAbove`, `Measure.prod_apply_symm`) and the 1-D fact that zeros with
nonzero derivative are isolated hence countable. Connectedness + `eqOn_zero_of_preconnected_of_eventuallyEq_zero` excludes
local flatness; `countable_cover_nhdsWithin` gives the countable cover. `generic`: finite union of null sets; openness via
ContinuousOn.isOpen_inter_preimage; density from `IsOpen.measure_pos`.

## Checks
- Gate build `inp_lake_build.sh /root/code/KAM-inp-s10z KAM.Planetary.Nondegeneracy.AnalyticZeros`: rc=0, no warnings in my file.
- `#print axioms` of analytic_zero_null, generic, rnd_def: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: line-length warnings fixed; remaining output: "KAM.lean is out of date; run
  scripts/gen_root_imports.py" (orchestrator regenerates, I must not edit it), check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK.
- No sorry/axiom/maxHeartbeats; imports only Mathlib and `KAM.Planetary.SecularForm.Basic` (for `Vec`); no provider or frozen theorem.

## Uncertainties / errata / deviations
None. No signature changed; no design signals (all elaborates at default heartbeats, whole file builds in seconds).
Note: the signature file's `generic` sits under `variable {n d m}`; here `n` is dropped (unused), so the elaborated statement is identical.

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S10-Z and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) statements/definitions = design signatures (rnd_def, analytic_zero_null, generic, identity/products), faithful on their whole carrier (rnd_def: every nonzero REAL relation vector); (2) proofs sound (analytic uniqueness, Fubini); no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/Nondegeneracy/AnalyticZeros*.lean.
