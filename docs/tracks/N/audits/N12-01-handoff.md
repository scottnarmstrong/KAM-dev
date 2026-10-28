# N12-01 prover handoff (branch inp-n1201, 6457d89; off inp; offloaded package run by the main orchestrator; prover on claude-12)


## Files (new)
- KAM/Nekhoroshev/Averaging/Setting.lean (112 lines)
- KAM/Nekhoroshev/Averaging/Field.lean (219 lines)

## Nodes → declarations
- bpN:p12:s-setting#data: `AvgPhase`, `AvgComplexPhase`, `AveragingData`, `avgDomain`, `avgG`, `avgH`, `avgA`, `avgB`, `avgM`
  (signature text verbatim; `avgA`/`avgB` placed in Setting so Field and later modules share them).
  Compact bounds Ω₀, M₂: `avg_compact_bounds` (∃ Ω₀ M₂ ≥ 0, ‖frequencyMap h I‖ ≤ Ω₀ and ∀ i, ∑ j |avgM h I i j| ≤ M₂ on closedBall 0 R).
  NOTE: this theorem is NOT in N12Signatures.lean; it is the "Ω₀,M₂ compact bounds" deliverable of the package row, statement matching
  the hypotheses of `envelopes_from_slab` (`hΩ`, `hM` on `closedBall 0 R`). Small extras: `AveragingData.toData` (Data n R s 1 h f), `avgDomain_subset_Wdom`.
- bpN:p12:fbounds (fb-poly, fb-cauchy, fb-real): `fbounds`, exact signature.
- bpN:p12:averaged: `averaged`, exact signature.

## Approach
- fbounds: Cauchy on closedBall (ι₂ z) (s/2) ⊆ complexDomain via `KAM.norm_fderiv_le_of_closedBall` (‖fderiv ℂ f‖ ≤ 2/s); real partials = Re of complex derivative along ι₂
  (chain rule); `avgH h f ε = realPart h ∘ snd + ε * Re(f∘ι₂)` pointwise; HasFDerivAt sum gives the field.
- averaged: slice θ ↦ Re f(ι(θ,I)) is C¹ on all ℝⁿ, ℤ-periodic in each coordinate; `KAM.torusAverage_coordinate_eq_zero` (Strip/Averages); coordinatewise via proj.
- compact bounds: frequencyMap is C² on the open realActionDomain (realPart h is C³), continuity of fderiv, compactness of closedBall 0 R ⊆ ball (R+s).

## Checks
- `inp_lake_build.sh … KAM.Nekhoroshev.Averaging.Setting KAM.Nekhoroshev.Averaging.Field`: Build completed successfully, no warnings in my files.
- `#print axioms` fbounds, averaged, avg_compact_bounds: [propext, Classical.choice, Quot.sound].
- `scripts/lint_sources.sh`: all checks pass except "KAM.lean is out of date" (generated root; I did not edit it — orchestrator must run gen_root_imports.py to add the two modules).

## Uncertainties / errata / deviations
- No heartbeat issues; no set_option used. No suspected source errata. No statement changed.
- Only deviation: added `avg_compact_bounds` (name chosen by me) and the two small helper lemmas above.

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-01 and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements = design signatures (standing data, domains, field bounds and zero average; the finite compact bounds Ω₀, M₂); definitions faithful on their whole carrier; (2) proofs sound; no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY the N12-01 modules (Setting, Field).
