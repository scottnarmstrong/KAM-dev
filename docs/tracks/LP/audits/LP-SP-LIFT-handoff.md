# LP-SP-LIFT handoff (wave 4: spatial chart lift on a stopped interval; MAIN L14 + L18 alignment, d = 3)

Track LP, non-frozen. The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
Branch `inp-lp-splift`. No `sorry`/axiom/`set_option` of any kind; every file a Lean module; largest file 302 lines.
Hard rules (repeated): never `set_option maxHeartbeats`; no Lean file over 1500 lines.

## Files (all new, namespace `KAM.Planetary.Spatial`; 1063 lines total)
`KAM/Planetary/Spatial/ChartLift.lean` (facade), `ChartLift/{Stopped (159), Uniform (158), Setting (302), Lift (257), Premises (158)}.lean`.
Only existing file touched: generated `KAM/Root/Planetary.lean` (`scripts/gen_root_imports.py`, needed for lint).
Stale prerequisites (SP-CHART, SP-PROD, Rotation46, SP-ADAPT) were rebuilt first through `lp_build.sh`, unchanged.

## Declarations
- `Stopped`: `SpatialLiftData ν U z₀ δ r` (Prop structure: `pos_mass, two_le, compact, subset_chamber, delta_pos, r_pos,
  budget : n*r + strongThresholdModulus ν U r ≤ δ/4, physical : SpatialNegativeEnergy ν z₀, ball, amd : C(z₀) ≤ B(Λ z₀) - δ,
  aligned : angularMomentum3 z₀ = spaceLength (angularMomentum3 z₀) • e₃`); `SpatialStoppedOn` (literally the antecedent of
  SP-CONF's `hstop`); `spLiftSecularBall ν δ I0 : Set (Phase (n+n)) = {y | Σ_k (y.1 k² + y.2 k²)/2 ≤ B(I0) - δ/4}` (ball (47));
  `SpatialLiftData.{spLift_n_mul_r_pos, spLift_abs_threshold_sub_le, spLift_threshold_ball_le, spLift_strongAMD_le_of_stopped}`;
  **item 1/2 (states)** `SpatialLiftData.spLift_prograde_of_stopped`: on `uIcc 0 t`, `SpatialBarrierState ν U (δ/2) (z u) ∧
  L(z u) = |L(z u)| • e₃ ∧ (∀ i, δ/2 ≤ L_i(z u) ⬝ᵥ e₃) ∧ z u ∈ spatialRegionProd ν` (conservation `angularMomentum3_const` +
  `proj_margin` with `m = δ/2`).
- `Uniform`: `uniformDataNM` = track P's `uniform_data` retyped to `Phase (a + b)` (N12), plus `udZero*`, `udAngleNM`, `udCellNM_isCompact`.
- `Setting`: `spatialChartAMD`, `spLiftChartSafe ν` (= `spatialPoincareProdDom n ∩ Ψ⁻¹' spatialCollisionFreeDomain n`),
  `spatialPulledHam ν μ = H_μ ∘ Ψ`, `spLiftChartHam ν μ w = spatialHProd ν w + μ * fSpatial ν (Ψ w)`, `spatialChartHam_eq_pulled`,
  `spLiftChartHam_field_eq` (fields agree on the open `spLiftChartSafe`), `differentiableAt_spLiftChartHam`,
  `spatialPoincareProdCast_isChart` (via `phaseCast`, `n*3 = n+(n+n)`), `spatialLiftPhysicalDeriv` (chart solution ⇒ physical solution),
  lattice periodicity (`spLiftChartSafe_shift_iff`, `spatialLiftField_periodic`), compact `spatialLiftQ I0 r c` (closed, bounded ⇒ compact).
- `Lift`: `mem_spatialChartSafe_of_liftQ`, and **item 3**
  `SpatialLiftData.spatialChartLift_of_stopped`: `(hd) (hJ : J.OrdConnected) (h0 : 0 ∈ J) (hz : IsSpatialMovingSolutionOn ν μ J z)
  (hz0 : z 0 = z₀) (ht : t ∈ J) (hs : SpatialStoppedOn ν z₀ δ r z t) : ∃ w I, IsOpen I ∧ I.OrdConnected ∧ uIcc 0 t ⊆ I ∧
  (∀ u ∈ I, w u ∈ spLiftChartSafe ν ∧ HasDerivAt w (hamiltonianVectorField (spLiftChartHam ν μ) (w u)) u) ∧
  (∀ u ∈ uIcc 0 t, spatialPoincareProd ν (w u) = z u) ∧ fast (w 0).2 = spatialActionVector ν z₀`.
- `Premises`: `spatialStoppedBlock ν δ I0 r wS : PartialBlock n (n+n) = ⟨I0, spLiftSecularBall ν δ I0, r, wS⟩`;
  `lpRescaleNM_mem_realDom` (generic `n m`); **item 4** `SpatialLiftData.spatialChartLift_premises`: `∃ w, (∀ u ∈ uIcc 0 t, w u ∈
  spLiftChartSafe ν ∧ Ψ (w u) = z u ∧ HasDerivAt w (X_{spLiftChartHam ν μ} (w u)) u) ∧ (∀ u ∈ uIcc 0 t, lpRescaleNM b.lam (w u) ∈
  b.realDom b.rB) ∧ fastAction (lpRescaleNM b.lam (w 0)) = b.Ic ∧ (∀ u ∈ uIcc 0 t, (slow (w u).1, slow (w u).2) ∈ b.S)`
  for `b = spatialStoppedBlock ν δ (spatialActionVector ν z₀) r wS` (any `wS`), the shape `nonresonant_drift_of_chartDataNM` consumes.
  Shape check (conditional, NOT `hstop`): `spatialStopped_drift_of_chartData` composes with `nonresonant_drift_of_chartDataNM`
  (premises `ExtNFHyp`, `hsmall`, trace identity `htr` with `lpRescaleHamNM b.lam (spLiftChartHam ν μ)`, `htime`, stopped conditions)
  and concludes `‖Λ(z u) - Λ z₀‖ ≤ r/2` on `uIcc 0 t`.

## Checks (all run)
- `lp_build.sh /root/code/KAM-inp-lp-splift KAM.Planetary.Spatial.ChartLift.{Stopped,Uniform,Setting,Lift,Premises} KAM.Planetary.Spatial.ChartLift`:
  each "Build completed successfully" (last: 9274 jobs); no warning from a ChartLift file.
- `lp_lint.sh`: exit 0 (`check_lean_modules: PASS (3749 Lean files)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`).
- `main_shortname_check.py /root/code/KAM-inp-lp-splift <6 modules>`: `short-name check OK (no reused public short name)`, exit 0
  (first run flagged 11 reused short names, incl. against unmerged `inp-lp-spdom`/`inp-lp-spnrr`; renamed with an `spLift` prefix).
- `#print axioms` (`.drafts/ax_splift.lean`, via `lp_lean.sh`): `spLift_prograde_of_stopped`, `spLift_strongAMD_le_of_stopped`,
  `spatialChartLift_of_stopped`, `spatialChartLift_premises`, `spatialStopped_drift_of_chartData`, `mem_spatialChartSafe_of_liftQ`,
  `uniformDataNM`, `spatialLiftPhysicalDeriv`, `spatialLiftQ_isCompact`, `lpRescaleNM_mem_realDom`: exactly `[propext, Classical.choice, Quot.sound]`.

## AUDIT FOCUS
1. `SpatialLiftData.aligned` is the only orientation datum (typing/alignment premise per MAIN L18, not a conclusion); `amd` forces `L ≠ 0`
   via `proj_margin`. No drift/confinement premise anywhere; `spatialStopped_drift_of_chartData` is explicitly conditional.
2. `SpatialStoppedOn` copied literally from SP-CONF's `hstop` antecedent (strict `< r`, strict `< B - δ/2`, `SpatialNegativeEnergy`).
3. Chart deficit = strong AMD only through alignment (`spatialChartAMD_eq_of_aligned`); the chart-domain membership (`mem_spatialChartSafe_of_liftQ`)
   uses only `C ≤ fixed-plane deficit` (`spatialStrongAMD_le_spatialFixedPlaneDeficit`), hence the barrier compact of SP-GEO.
4. `uniformDataNM` is a verbatim retyping (`a = n`, `b = n + n`) of `uniform_data`; `spatialLiftQ` bounds (`|c|+1`, `Σ(|I0-r|+|I0+r|)`).
5. `spLiftChartHam` (split form) vs `spatialPulledHam` (`H∘Ψ`): equal on the domain, fields equal on the open `spLiftChartSafe`.
6. `lpRescaleNM_mem_realDom`: index arithmetic of `Fin.castAdd (m+m)` / `natAdd` vs SP-ADAPT's `lpRescaleNMFun`.
7. Ball (47) is `spLiftSecularBall` (physical slow coordinates, `Phase (n+n)`); LP-SP-DOM's name to be joined at landing.

## Errata / deviations / design signals
- No MAIN defect found in L14, L18, T19 for d = 3.
- Deviations: `KAM/Root/Planetary.lean` regenerated; names carry the `spLift` prefix (short-name check; the orchestrator joins them with
  LP-SP-DOM / LP-SP-NRR at landing: `spLiftChartSafe` ↔ spdom `spatialChartSafe`, `spLiftChartHam` ↔ spnrr `spatialChartHam`,
  `spLiftSecularBall` ↔ spdom `spatialSecularBall`).
- No interface mismatch with SP-ADAPT or SP-PROD. No heartbeat/OOM signals; each module builds in ≈ 5–30 s under the 4 GB cap.
