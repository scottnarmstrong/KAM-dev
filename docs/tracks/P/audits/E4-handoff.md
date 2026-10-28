# E4 prover handoff (branch inp-p14-e4, 9c2811cf; off inp (E2, E5 on inp); offloaded P14 package run by the main orchestrator)


**Files:** new `KAM/Planetary/Exponential/KeplerData.lean` (≈373 lines). Nothing else touched (KAM.lean is stale: orchestrator must regenerate it).

**Proved:** `KAM.Planetary.h_data` (bpP:p14:h-data; steps hd-i, hd-ii, hd-iv, hd-v), statement verbatim from the signature file. `planetaryKeplerC` and `fastBox`/`EnlargedData` already exist in E0 Setting, so they are imported, not redefined. The brief's summary list ("both signs, sum Hessian bound") is all conjuncts of `h_data`; no other declaration is assigned to this module.

**Approach:** generic calculus over `𝕜 ∈ {ℝ,ℂ}` for `keplerSumGen 𝕜 m z = -∑ m_i³/(2 z_i²)` (`planetaryKeplerC = keplerSumGen ℂ` by rfl; `realPart` of it = `keplerSumGen ℝ`): ContDiffOn on the nowhere-zero set, `HasFDerivAt`, second derivative as the diagonal form `-3m_i³/z_i⁴`, curried operator-norm bound `∑ 3|m_i|³/‖z_i‖⁴`. `keplerData_margin` gives `0<5l/8 ≤ l-3κ ≤ Re z_i` and `‖z_i‖ ≤ u+3κ`. g, v are attained minima (`Finset.exists_min_image`, n≥2 gives nonemptiness). `HasDefiniteFastPart` is proved for h (σ=-1), and `hasDefiniteFastPart_neg` (general lemma) gives -h (σ=+1) by negation. M is the exact sum.

**New public names** (grepped first, no collisions): `keplerSumGen`, `keplerSumGenD`, `keplerSumGen_contDiffOn`, `keplerSumGen_hasFDerivAt`, `keplerSumGen_fderiv_eq`, `keplerSumGenD_hasFDerivAt`, `keplerSumGen_fderiv2_apply`, `keplerSumGen_hess_norm_le`, `keplerData_margin`, `hasDefiniteFastPart_neg`, `planetaryKeplerC_ofReal`, `realPart_planetaryKeplerC`, `planetaryKeplerC_eq`, `keplerSumGen_real_freq`, `keplerSumGen_real_hess`.

**Checks:**
- `inp_lake_build.sh … KAM.Planetary.Exponential.KeplerData`: "Built … Build completed successfully" (only an unrelated pre-existing warning in KAM/Kepler/Mass.lean).
- `scripts/lint_sources.sh`: all checks PASS except "KAM.lean is out of date" (expected; not edited per rules). Over-100-char lines fixed.
- `#print axioms KAM.Planetary.h_data`: `[propext, Classical.choice, Quot.sound]`.
- No sorry/axiom/opaque, no heartbeat overrides, no EuclideanSpace; no frozen theorem or provider imports (only frozen Defs).

**Uncertainties / errata / deviations:** none. No statement defect found; no extra hypotheses. No heartbeat design signals. Imports of Enlargement/LocalComplexification are listed (per brief) though not strictly used.

AUDIT FOCUS (design docs/tracks/P/design/P14-LEAN-DESIGN.md row E4, node rows 144-148 and its proof plan; line 298 on the curried bilinear operator norm; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean): (1) h_data = signature file EXACTLY, and the E4 slice COMPLETE (steps hd-i, hd-ii, hd-iv, hd-v; the design row also names 'both signs' and the 'sum Hessian bound': check they are covered); (2) the Hessian bound uses the curried bilinear operator norm as line 298 requires, not a matrix norm; (3) proof soundness: the generic keplerSumGen calculus over R and C, planetaryKeplerC = keplerSumGen C by rfl, the real-part identification, ContDiffOn on the nowhere-zero set; no added premises; (4) hygiene (no EuclideanSpace; no public short name already used elsewhere in KAM; no root shadow). Audit ONLY KAM/Planetary/Exponential/KeplerData.lean.
