# P23-21 prover handoff (branch inp-p2321, 03cf7aea; contains inp-p2318 (round-2 passed) and P23-17; offloaded package run by the main orchestrator; prover on claude-10)


## Files (new)
- `KAM/Planetary/TwoScale/MeasureActions.lean` (109 lines): `mem_realTube_of`, `ActionsMeas`, `meas_actions_of_limit`.
- `MeasureScaled.lean` (111): `scaled_cover` (cover transported through `sc`/`unsc`), `scaleEquiv`, `norm_scaleEquiv`, `lip_image_scaled`.
- `MeasureTorus.lean` (216): `volume_box`, `TorusMeas`, `TorusMeas.volume_tube_diff`, `shell_subset`, `preimage_mem`, `TorusMeas.meas_torus_of_limit`.
- `MeasureJoint.lean` (221): `KamHyp.kam_small_n`, `KamHyp.mbar_div_le`, `actionsMeas_of_limit`, `torusMeas_of_limit`, `ko_eq`, `exists_omega`, `meas_torus_final`, `meas_of_iterative`.
- `Measure.lean` (20): facade (module doc, imports MeasureJoint). Total about 680 lines, no file over 221.

## Note on signatures
`P23Signatures.lean` contains no signed declaration for `meas_actions`/`meas_torus` (they are local obligations
inside `two_scale_kam`; the only statement of them is the draft `PPart23Signatures-partial-from-inp.lean`, not
used). The private interfaces below are new, with distinct names; no public signature changed.

## Private interfaces (finding N2) and inventory
Prop bundles of proved outputs only, discharged by `meas_of_iterative` on the witnesses of one `iterative_steps`:
- `ActionsMeas D D₀ i Ê ρ̂` = {D₀ ⊆ D, 0 ≤ Ê, 0 < Êρ̂, ‖i I − I‖ ≤ 20Êρ̂, defect Lipschitz 2560nÊ, 2560nÊ < 1/3}
  ← `limit_actions_of_steps` (blocks → sup via `norm_le_of_blocks`, Mbar_i ≤ Mbar), KamHyp (`eHat_pos`, `eHat_nonneg`, `R_pos`).
- `TorusMeas D D₀ i Φ Ê ρ̂ s` = ActionsMeas + {0<ρ̂, 0<s ≤ 1/4 (from `widths`), Ê ≤ 1/8 (`eHat_lt_small`), rescaled
  defect Lipschitz 768nÊ on ℝⁿ×D_*, 768nÊ < 1/10, rescaled displacement ≤ 3/2 Ê} ← `limit_phi_real_of_steps`.
- Obligation map: `ma-ext`, `ma-meas` → `meas_actions_of_limit`; `mt-split`, `mt-shell` → `volume_tube_diff`/`shell_subset`;
  `mt-ext` → `scaled_cover`; `mt-pre` → `preimage_mem`; `mt-meas` → `lip_image_scaled`; `mt-sum` → `meas_torus_of_limit`.
- Application in the joint construction (for P23-22): `meas_torus_final` takes the exact clause shapes of `two_scale_kam`
  (`hblk`, `hlipI` = block bounds and 2560 defect clause on `i`; `hlipΦ` = the 768 limitmap clause on `Φ`; `hI₀` = the
  first clause (I₀, Ω→D₀ with unique inverse); `hK` = `K ω θ = Φ (θ, i (I₀ ω))`) plus ONE retained derived fact `hsup`
  (rescaled displacement of Φ, the 3/2 block bounds: output of `limit_phi_real_of_steps`, NOT a clause of `two_scale_kam`;
  it must be carried from the joint construction) and concludes the last clause of `two_scale_kam` (KO as
  ⋃ ω∈Ω, range (K ω); D₀ = dioBase, Ω = omegaSet) with constant `complementConstant (a+b)`.
  `meas_of_iterative` checks on `iterative_steps` witnesses (same `Ds,hs,fs,Ψ,Φ,is`, same `i`, `Φinf`) that all bundles hold.
  No fresh witnesses; no derived invariant is turned into a premise of `two_scale_kam`.

## Approach
Source steps as in P3b L160-189, with these precisions: closed shell = existential distance `∃ J ∈ X, ‖x−J‖ ≤ ρ`,
contained in the OPEN tube `realTube D (32Êρ̂)` since `ρ₁ ≤ 30Êρ̂ < 32Êρ̂` and `ρ₂+η ≤ 22Êρ̂ < 32Êρ̂` (uses `0 < Êρ̂`).
Torus part is simplified: with W = realTube ∖ D_*, the complement in the cell is ⊆ (cell × W) ∪ Φ_e((enlarged cell) × (N_{ρ₂}(D_*)∖D_*)),
and N∖D_* ⊆ W, so total ≤ (1+2ⁿ)·meas(W) ≤ (1+2ⁿ)(1+(4/3)ⁿ)(a+b) ≤ `complementConstant n`·(a+b) (slack of exactly (a+b)).
Periodicity of Φ is not needed (the cell is a subset of ℝⁿ, `Φ_e⁻¹(y)` lies in the enlarged cell). The scaling determinant is
cancelled in `lip_image_scaled` (`addHaar_image_linearMap`).

## Checks
- Gate builds (LEAN_NUM_THREADS=1), each module green; final `inp_lake_build.sh … KAM.Planetary.TwoScale.Measure`: "Build completed successfully (9185 jobs)", no sorry, no errors.
- `scripts/lint_sources.sh`: check_lean_modules PASS (722 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only the expected
  "KAM.lean is out of date" (not edited per rules). No lines > 100 chars. grep: no EuclideanSpace, maxHeartbeats, sorry, axiom.
- `#print axioms` (in MeasureJoint.lean) for `meas_actions_of_limit`, `TorusMeas.meas_torus_of_limit`, `meas_torus_final`,
  `meas_of_iterative`: only `propext, Classical.choice, Quot.sound`.
- Public names checked unique across KAM by grep.

## Uncertainties / deviations / errata
- No heartbeat problems. No deviation from the source constants. Source gaps (p3a L91/L184/L202, p2 L177) were not needed here.
- Source remark: (D×T^n)∖K_Ω in the statement is over the open tube `realTube D r` (as in `two_scale_kam`), handled by the extra shell piece, within `complementConstant`.
- Possible erratum (minor): P3b `mt-ext` says N_ρ closed neighbourhoods "⊂ Re(X_r)" while `actionNbhd` is OPEN (`<r`); true only because the radii are strictly less than r, which needs Êρ̂>0 (holds under KamHyp). Recorded for the ledger.
- Pre-existing unrelated warnings (Cover `hη` unused) untouched. Audit of the applicability of the bundles is left to the independent audit.

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md: row P23-21, the meas_actions / meas_torus bullets ('closed shells as existential distances, cell and rescaling'), finding N2 and the 'Private-interface release gate'; blueprint P3b; P23-17 and P23-18 audits for the parallel bundle rulings). P23-21 is a PRIVATE conditional package. Refute-first: (1) every Prop bundle (ActionsMeas, TorusMeas, any new one) contains ONLY proved outputs of iterative / limit_actions_of_steps / the P23-18 helpers on the SAME witnesses, discharged by applicability theorems (actionsMeas_of_limit, torusMeas_of_limit, meas_of_iterative); no field smuggles a measure conclusion or a hard step; (2) meas_actions_of_limit, meas_torus_of_limit and meas_torus_final prove every obligation of the design bullets (closed shells as existential distances, cell, rescaling; constants proved, not assumed); KamHyp.kam_small_n, KamHyp.mbar_div_le are consequences of KamHyp, not new hypotheses; (3) the inventory maps each local obligation to a helper; (4) proofs sound, no sorry/axioms; (5) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM: check volume_box, shell_subset, preimage_mem, scaled_cover, scaleEquiv, ko_eq, exists_omega). Audit ONLY KAM/Planetary/TwoScale/Measure*.lean.
