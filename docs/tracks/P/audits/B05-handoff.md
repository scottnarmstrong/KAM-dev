# B05 prover handoff (branch inp-p11b-b05, 91363ada; contains inp-p11b-b04 BEFORE its round-2 fix (B04b adds c-prime positivity only; no existing B04 statement changes); offloaded P11B package run by the main orchestrator)


## Files (all new, none edited elsewhere)
- `KAM/Planetary/WeakKAM/ExtensionNorm.lean` (91 lines): Euclidean/max norm conversion (`selectionLength_le_sqrt_mul_norm`,
  `abs_le_selectionLength`, `norm_le_selectionLength`, `norm_le_one_of_selectionLength_eq_one`), `selectionOpNorm_le_of_unit`
  (multilinear operator norm from unit ball), real inclusion as a linear isometry `selectionRealLI`.
- `KAM/Planetary/WeakKAM/ExtensionStage.lean` (222): `selectionIncrement`, `selectionRealCollar`, smoothness of the real trace,
  `selectionIncrement_norm_iteratedFDeriv_le` (fe-cauchy via P11A `param_cauchy`, t'=3t/4), `selectionStage_contDiff` (fe-supp/fe-reg),
  `selectionStage_norm_iteratedFDeriv_le` (fe-leib, operator norms, Mathlib bilinear Leibniz bound).
- `KAM/Planetary/WeakKAM/ExtensionFrequency.lean` (68): `selectionFrequencyMap_apply` (frequencyMap = Re of complex gradient at real points),
  `selectionFrequencyMap_contDiffOn`.
- `KAM/Planetary/WeakKAM/Extension.lean` (236): `finite_extension` (signature copied verbatim from P11BSignatures.lean) plus helpers
  (`selectionCutoffC_nonneg`, `le_selectionExtensionC`, `selectionStage_extension_bound`, `selectiont_pos`, `selectiont_le_one`, ...).
Only `finite_extension` is a signature declaration of B05; all other names are new helpers (grepped for clashes first).

## Approach
Cutoffs χ_j from `smooth_cutoff` (E = K_j, t = t_j ≤ 1) chosen by `choose`; each χ_j·Re Δω_j is globally C^μ (supported inside the real collar,
zero elsewhere). Derivative bound: Leibniz (operator norm) + parameter Cauchy (u^u ℓ/(t/4)^u) + t_j ≤ 1; Euclidean seminorm via
`selectionLength ≤ √n ‖·‖`; sum over stages and `le_csSup` against the sup in `selectionExtensionC`. No EuclideanSpace anywhere.

## Checks
- `lake build KAM.Planetary.WeakKAM.Extension` via the gate: success, no warnings in my files (warnings shown are in earlier files).
- `#print axioms KAM.Planetary.finite_extension`: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: only failure is "KAM.lean is out of date; run scripts/gen_root_imports.py" (generated file, not edited by me;
  the 4 new modules need regenerating). Module check, frozen-anchor guard, ABI hashes all PASS.
- No `sorry`, `maxHeartbeats`, `EuclideanSpace`; all files < 250 lines.

## Uncertainties / deviations
- Hypotheses `hμ : a.μ = d.μ` and `htθ : a.t₀ ≤ ϑ/√n` of `finite_extension` are unused by the proof (cutoffs are globally smooth on ℝⁿ, so the
  source's "support inside V" argument is not needed; `hμ` is not needed since the bound is stated with d.μ). They are kept (verbatim signature) and
  referenced via `have _ := And.intro hμ htθ` to avoid unused-variable warnings. Not a defect, just slack in the statement.
- Imports P11A `KAM.Planetary.MaximalStep.Parameter` (param_cauchy), `PGAssembly.JetsPolar` (iteratedFDeriv_comp_clm_of_isOpen) and
  `KAM.Strip.AnalyticTaylor`; B03 bridges not used.
- Suspected source errata: none. (Source (fe-leib) "Reindexing ... ≤ c' ℓ t^{-k} ≤ c' ℓ t^{-μ}" matches the formula for `selectionExtensionC`.)

AUDIT FOCUS (design docs/tracks/P/design/P11B-LEAN-DESIGN.md row B05 and its proof plan; P11B design audits; signatures /root/code/KAM-inp/.drafts/design/P11BSignatures.lean): (1) finite_extension and every B05 definition (selectionIncrement, selectionRealCollar, selectionExtensionC, ...) = signature file EXACTLY, and the B05 slice COMPLETE: read the design row and proof plan line by line (sibling B04 failed for an omitted proof-plan obligation); (2) the handoff says the signature premises h-mu and h-t-theta are unused because the cutoffs are globally smooth on R^n: decide whether that bypass is sound and whether the proof still establishes what the design's consumers (B07/B08, the selection theorem) need, e.g. support inside V if a consumer relies on it; (3) proof soundness: fe-cauchy via param_cauchy with t'=3t/4, fe-supp/fe-reg, fe-leib Leibniz bound and the constant selectionExtensionC; the frequency map as Re of the complex gradient; no added premises; (4) hygiene (no EuclideanSpace; no public short name already used elsewhere in KAM; no root shadow). Audit ONLY KAM/Planetary/WeakKAM/Extension{,Norm,Stage,Frequency}.lean (the Cutoff* files are B04's, audited separately).
