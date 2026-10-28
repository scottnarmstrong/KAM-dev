# P23-10 prover handoff (branch inp-p2310, 4b34dce; contains inp-p2305 (P23-05, audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/Averaging/Splitting.lean` (imports `Averaging.Direct`, `Canonical.TransformSeries`, `Canonical.Adjoint`). No other file touched.

**Declarations (signatures verbatim, only line-wrapped for the 100-col lint):** `firstGen`, `directMap`, `split` (`bpP:p2:split`).
Extra public helpers (distinct names, no new premises): `firstGen_class_bound` (sp-coef: `InClass` + `WBound` of `firstGen` with `qδ/(2πα₁)`), `split_coeff` (conclusion (b) of `split`), `dtheta_firstGen_eq` (`∂θᵢ homGen = ∂θᵢ firstGen`, first block). Private: `genC`, `homGen_eq_series`, `coeff_homGen`, `norm_div_divisor_le`, `dtheta_eq_zero_of_modes`, `component_mvt` (copy of the private one in `Canonical/CanonicalMap`), `finite_zBall'`.

**Approach.**
- sp-coef: `homGen K {0} h f = fourierSeries genC` (finite support in `zBall`), so `coeff homGen I k = genC k I` via `torusCoeff_fourierSum`; `‖genC‖ ≤ q/(2πα₁)‖f̂ₖ‖` for `k₁ ≠ 0` from `TwoDiv` (branch `α₁`); `projections` gives coefficients of `firstGen`; weighted bound by comparison. (b): `coeff_add` / `coeff_const_mul` with `projections`.
- sp-field: `CanonData` for `homGen` (`Φ = qδ/(2πα₂)` from `direct`, smallness from `hsmall`); `∂θᵢ(φ-φ⁽¹⁾)=0` (first block) because `φ-φ⁽¹⁾` has only `k₁=0` modes (Fourier representation `coefficients_repr`, line-invariance of the characters, derivative of an eventually constant function); then `vf_bound` for `firstGen`.
- sp-int: first-block action displacement by mean-value along `flow_a` trajectory with the ℝ-CLM `w ↦ firstBlock w.2`; last block and angle displacement from `canonical_map_a` (last conjunct), `lastBlock` norm ≤ full norm.

**Checks.** `LEAN_NUM_THREADS=1 inp_lake_build.sh /root/code/KAM-inp-p2310 KAM.Planetary.Averaging.Splitting` → `Built ... Build completed successfully`, no warnings. `sh scripts/lint_sources.sh`: only "KAM.lean is out of date" (generated file, not edited per rules); line-length, module check, frozen-anchor guard, ABI hashes OK.
`#print axioms KAM.Planetary.split` (also `firstGen_class_bound`, `dtheta_firstGen_eq`): `[propext, Classical.choice, Quot.sound]`.

**Uncertainties / design signals.** None: no heartbeat issues, file 343 lines, no `sorry`, no premise added. Quarantine respected (imports only proved N/Canonical modules and `Averaging.Direct`).
**Suspected errata / deviations.** None. Note the source writes `ᾱ₂ρσ`-smallness for `u`; the signature's `hsmall` is exactly it. Signature line breaks differ cosmetically.

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md revision 2 row P23-10 and proof plan; audits DESIGN-P23-design-audit-{1,2}.md; signatures .drafts/design/P23Signatures.lean): (1) statements = design signatures (firstGen, split, directMap: coefficient split, field, integration); (2) proofs sound, consuming P23-05 as designed; no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/Averaging/Splitting*.lean (compare with branch inp-p2305).
