# P23-17 prover handoff (branch inp-p2317, 7ddf518; contains inp-p2316 (audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files
- `KAM/Planetary/TwoScale/LimitActionsChain.lean` (136 lines): `ActionSteps` (Prop bundle of the `iterative` outputs about `ĩ_j`), `actionChain` (real `ǐ_j`), `chain_mem` (la-wp), `incl_chain_succ`, `chain_step` (blockwise step bounds), `chain_freq` ((iv) frequency identity for the same `ǐ_j`).
- `KAM/Planetary/TwoScale/LimitActions.lean` (~440 lines): scalar facts via the proved `sums`, partial/tail sums, telescoping block bounds (la-tele), Lipschitz recursion and product bound (la-lip), `chain_limit`, and
  `limit_actions_of_steps`; applicability check `iterative_actionSteps`.

## Statements (no signature existed in P23Signatures.lean; designed from the blueprint P3b L20-39, the design's `limit_actions` bullet, and the release gate)
`limit_actions_of_steps (S : ActionSteps sbar p h Ds hs fs is) : ∃ i, ` uniform convergence of `actionChain is` to `i` on `Ds 0`; chain membership `ǐ_j I ∈ Ds j`; (i) block bounds `20(Mbar_i/Mbar)Ê₀ρ̂₀` and sup bound `20 Ê₀ρ̂₀`; tail `‖i I - ǐ_j I‖ ≤ 20 ρ̂_j Ê_j`; (ii) `i I ∈ realTube (Ds j) (ρ_j/2)`; (iii) `‖(iI-I)-(iJ-J)‖ ≤ 2560 n Ê₀ ‖I-J‖`, `2560 n Ê₀ < 1/3`, two-sided bi-Lipschitz, `InjOn i`; (iv) `realFreq (hs j) (ǐ_j I) = realFreq h I`.
`iterative_actionSteps (H : KamHyp D sbar p h f) : ∃ Ds hs fs Ψ Φ is, Ds 0 = dioBase D h p ∧ ActionSteps ...` — obtained by projecting the output of `iterative` (P23-16), so the hypotheses are derived dependencies on the same witnesses, never source premises. P23-22 should `obtain` the `iterative` witnesses once, build `ActionSteps` from the same projections (as in this proof), and apply `limit_actions_of_steps`.

## Inventory (design gate)
la-wp → `chain_mem`/`incl_chain_succ` (uses `maps`, `Ds_succ`); la-tele → `chain_step`, `chain_sup_step`, `chain_block_le`, `chain_limit` (uses `step`, `sums`, `rho_hi`, `eHat_sq`); la-loc → location conjunct (`R_le_ρ`, `eHat_lt_small`); la-lip → `chain_lip`, `prod_le`, `lip`; (iv) → `chain_freq` (uses `step`, `hs_zero`).

## Checks
- `inp_lake_build.sh … KAM.Planetary.TwoScale.LimitActions` (builds Chain too): success, no errors, no sorry; only unused-variable warnings (Ψ Φ in the check theorem).
- `#print axioms limit_actions_of_steps` and `iterative_actionSteps`: [propext, Classical.choice, Quot.sound].
- `scripts/lint_sources.sh`: only message besides PASS lines is "KAM.lean is out of date" (generated root; not edited per rules; orchestrator regenerates).

## Notes / uncertainties
- No heartbeat overrides; no design signal. The first build took ~2 min in the gate for LimitActions (many nlinarith) but under default heartbeats.
- Location is stated with `ρ_j = (seq p j).ρ` (`realTube` is strict; strictness holds since `20 Ê < 1/8`). For `j=0` the sup bound `‖i I − I‖ ≤ 20 Ê₀ ρ̂₀` is given non-strictly (the blueprint's "Re(D₀)_{20Ê₀ρ̂₀}").
- The `2560 n` uses `(a+b : ℕ)` cast as in `iterative`'s `640 * (a+b)` convention (`↑a + ↑b`); the final statement uses `(a + b : ℝ)`.
- Suspected errata: none. Deviations: the helper's signature is mine (none supplied); blueprint's `Ê_j<1/40` replaced by proved `Ê_j<1/160`.

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md: row P23-17, the 'limit_actions' bullet, finding N2 and the 'Private-interface release gate'; design audits; blueprint P3b bpP:p3:limit-actions L20-L39). P23-17 has NO signed declaration: it supplies private conditional helpers. Refute-first on the release gate: (1) ActionSteps is a Prop bundle: verify that EVERY field is exactly a proved output of iterative (P23-16) on the same witnesses, discharged in full by iterative_actionSteps, with no field that smuggles a limit_actions conclusion or any hard proof step (no conclusion-shaped hypothesis); (2) limit_actions_of_steps proves every obligation of the design's limit_actions bullet (uniform convergence, tail 20 rhohat_j Ehat_j, block displacement 20(Mbar_i/Mbar) Ehat_0 rhohat_0, Dstar in every real half-radius stage, defect Lipschitz 2560n Ehat_0, frequency identity for the SAME check-i_j); check the stated deviations (Ehat_j<1/160 vs 1/40; non-strict j=0 sup bound; (a+b) casts) are sound and not weakenings; (3) the inventory maps each local obligation (la-wp, la-tele, la-loc, la-lip) to a helper; (4) proofs sound, no sorry/axioms; (5) hygiene. Audit ONLY KAM/Planetary/TwoScale/LimitActions*.lean (compare with branch inp-p2316).
