# S8-M prover handoff (branch inp-s8m, 7499b26; contains inp-s7r and inp-s8p (audited); offloaded package run by the main orchestrator; prover on claude-12)


**File (new):** `KAM/Planetary/SecularForm/Momentum.lean` (~625 lines). Not imported by KAM.lean (root not edited).

**Declarations (signatures verbatim from P810Signatures.lean):** `momentum`, `position`, `modelDelta`,
`lemma64` (bpP:p8:lemma64 a-e), `lemma64_coordinates`, `identification` (bpP:p8:identification).
Helpers (public, new names): `blk`, `blk_mem`, `assemble_mem`, `position_eq_block`, `momentum_eq_block`,
`pmom`, `ppos`, `momSlot`, `unitAngle`, `hasDerivAt_keplerPart_momentum`, `fderiv_keplerPart_momentum`,
`hasDerivAt_position`, `hasDerivAt_ppos`, `ppos_periodic`, `integral_pmom`, `mean_planeSq_pmom`,
`avg_prod/avg_one/avg_two/avg_sum/avg_const_mul/avg_add/avg_apply`, `perturbation_diff`, `nu_pos`.

**Approach.**
- (a): the line `r ↦ Ψ(assemble Λ (update t k r) η ξ)` has derivative `fderiv Ψ w (unitAngle k)`; by `pc_dec` and
  `product_chart` (X_h = Σ ν_k unitAngle k) the position part of body i equals the Kepler field `p_i/m_i`
  (computed by `fderiv_keplerPart_momentum`); other angles do not move body i (so those derivatives vanish).
- (b): `q^(i)` is C¹ and 2π-periodic (`poincare_periodic`), so `periodic_derivative_integral` gives zero mean.
- (c),(d),(e): `avg_prod` (cell integral of a product of one-variable functions, via `Measure.restrict_pi_pi` and
  `integral_fin_nat_prod_eq_prod`) gives avg_one/avg_two; virial value from `poincare_means`; (e) by expanding
  `planeSq (Σ v) = Σ_i Σ_j planeDot`.
- identification: `f_mov - f_fix = |ΣP|²/(2 m0)` literally (`perturbation_diff`), continuity, (e), and an
  integrable-add lemma for the conditional last clause.
No pair-collision guard anywhere; only `x ∈ slowDom D`.

**Checks.**
- Gate: `inp_lake_build.sh /root/code/KAM-inp-s8m KAM.Planetary.SecularForm.Momentum` -> "Build completed successfully (9125 jobs)" (built the
  pre-wrap version; the last commit only wraps one >100-char line; the final file re-elaborated with `lake env lean`, no errors/warnings in Momentum).
- `sh scripts/lint_sources.sh`: only remaining message is the pre-existing "KAM.lean is out of date" (root is generated, not edited); check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK.
- `#print axioms` of lemma64, lemma64_coordinates, identification: `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, no heartbeat options.

**Uncertainties / design signals.** None; all proofs elaborate at default heartbeats (each `lake env lean` run ~20 s).
`modelDelta` is defined here (signature file places it just before `identification`).
**Suspected errata / deviations.** None. Statements are as in the signature file (the blueprint's (a)
"∂_{λ_k} q^(i)=0" is the `lemma64_coordinates` first clause).

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S8-M and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) statements = design signatures exactly (momentum, position, modelDelta, lemma64 parts a-e, lemma64_coordinates, identification); (2) proofs sound; no added premises; (3) hygiene. Audit ONLY KAM/Planetary/SecularForm/Momentum.lean (compare with branch inp-s7r).
