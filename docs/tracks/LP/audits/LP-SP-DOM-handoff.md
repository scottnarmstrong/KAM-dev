# LP-SP-DOM handoff (track LP, non-frozen; MAIN Lemma 18, lines 580–597, with L8 244–271, (47), N2, N3, N12)

## Files (all new; namespace `KAM.Planetary.Spatial`; no heartbeat/recursion option; largest 239 lines)
`KAM/Planetary/Spatial/AnalyticDomain.lean` (facade) and `AnalyticDomain/{Core,Safety,Extension,Containment,Alignment}.lean`
(239 / 107 / 131 / 140 / 114 lines). Only existing file touched: generated `KAM/Root/Planetary.lean`
(`scripts/gen_root_imports.py`, needed for lint). Stale prerequisite modules were rebuilt by `lp_build.sh` itself.
Reused unchanged from planar LP-DOM (action-only, dimension-free): `strongLevelSet`, `IsSharedTube`, `exists_isSharedTube`,
`sharedTube`, `isCompact_strongLevelSet`, `strongThreshold` and its modulus lemmas, `strongThreshold_le_action`.

## Layout
`w : Phase (n + (n + n))` as in SP-PROD (`fast w.1 = λ`, `slow w.1 = (ξ|v)`, `fast w.2 = I`, `slow w.2 = (η|u)`), so
`slow w` carries all `2n` slow pairs. The complex tube is `complexTubeNM` / `tubeNM` (SP-TUBE), never track P's `n+n` tube.

## Declarations (D = brief item)
- `spatialSlowDeficit w := ((Σ_k slow w.1 k²) + Σ_k slow w.2 k²)/2` (= `Σ(Γ_i+Z_i)` by SP-PROD `sum_gamma_add_z_eq_half_slow_sq`).
- **D2** `spatialStrongCore ν L δ r := {w | (∀ i, 0 ≤ fast w.1 i ∧ fast w.1 i ≤ 2π) ∧ ∃ I0 ∈ strongLevelSet ν L δ, ‖fast w.2 - I0‖ ≤ 4r ∧ spatialSlowDeficit w ≤ strongThreshold ν I0 - δ/4}`;
  `isCompact_spatialStrongCore (hν) (hn : 2 ≤ n) (hL : IsCompact L) (hLch : L ⊆ chamber ν) (hδ : 0 < δ) : IsCompact (spatialStrongCore ν L δ r)`;
  `spatialStrongCore_margin (hg : IsSharedTube ν L δ r) : w ∈ core → fast w.2 ∈ sharedTube ν L δ r ∧ spatialSlowDeficit w ≤ B(fast w.2) - 3δ/16`;
  `spatialStrongCore_subset_dom : core ⊆ spatialPoincareProdDom n` (`Γ_i+Z_i < I_i`, MAIN 587).
- **D3** `spatialChartSafe ν := spatialPoincareProdDom n ∩ spatialPoincareProd ν ⁻¹' spatialCollisionFreeDomain n`;
  `spatialNegativeEnergy_spatialPoincareProd`, `spatialActionVector_spatialPoincareProd`,
  `spatialStrongAMD_le_spatialSlowDeficit` (every chart point, no alignment; via SP-PROD `spatialStrongAMD_le_spatialFixedPlaneDeficit`),
  `spatialStrongCore_barrierState : w ∈ core → SpatialBarrierState ν (sharedTube ν L δ r) (3δ/16) (spatialPoincareProd ν w)`,
  `spatialStrongCore_subset_chartSafe` (via `exists_spatialBarrierCompact`).
- **D4** `spatialChartSafe_shift_iff`, `fSpatial_spatialPoincareProd_shift`,
  `exists_spatialStrongTube : ∃ R > 0, ∃ M, ∃ fc, DifferentiableOn ℂ fc (complexTubeNM core R) ∧ (∀ w, complexifyPhase w ∈ complexTubeNM core R → w ∈ spatialChartSafe ν ∧ fc (complexifyPhase w) = (fSpatial ν (spatialPoincareProd ν w) : ℂ)) ∧ (fast-shift periodicity: ∀ k z ∈ tube, z + complexifyPhase (fastShift k) ∈ tube ∧ fc (…) = fc z) ∧ ∀ z ∈ complexTubeNM core (R/2), ‖fc z‖ ≤ M`
  (`R, M, fc` depend only on `(ν, L, δ, r)`, chosen before `I⁰`, `μ`; proof: `tubeNM` + compactness of a thickening of the core).
- **D5** `spatialSecularBall ν δ I0 : Set (Phase (n + n)) := {y | ((Σ y.1²) + Σ y.2²)/2 ≤ B(I0) - δ/4}` and
  `spatialStrongCore_containment (hrs : 0 < rs) (hrg : rs ≤ 4r) (hmax : max rs (max (4s) (4b)) < R/2) (hI0 : I0 ∈ strongLevelSet ν L δ)`
  with complex actions within `rs` of `I0`, `‖Im λ‖ < 4s`, and `∃ y ∈ spatialSecularBall, (all 2n complex slow coordinates of z.1, z.2) within 4b of (y.1, y.2)`
  `⇒ z ∈ complexTubeNM core (R/2)`.
- **D6** `spatialHamiltonian_split_chartSafe : w ∈ spatialChartSafe ν → H_μ (Ψ w) = -Σ ν_i³/(2 (fast w.2 i)²) + μ * fSpatial ν (Ψ w)` (restates SP-PROD).
- **Alignment (MAIN 595–597)** `spatialStrongAMD_eq_spatialFixedPlaneDeficit_of_aligned`, `eq_smul_e₃_of_spatialUnit_eq`,
  `spatialStrongAMD_eq_spatialSlowDeficit_of_aligned` (chart aligned identity `C = (Σ slow²)/2`),
  `aligned_rotated_solution_stays_aligned` (conservation `angularMomentum3_const` on an order-connected `J`),
  `exists_aligned_rotated_solution` (one fixed `R` from `exists_rotation_align_angularMomentum3`; the rotated solution is a solution, `L = |L| e₃` along it, `C = C_{e₃}`, and `C` unchanged by `R`).

## Not done
Nothing in the brief omitted. As in planar LP-DOM, D5 is stated as containment in `complexTubeNM core (R/2)` (the object the bound `M` lives on); the
"every Newtonian denominator has a single branch, bounded below" clause of L8 is carried by `tubeNM` (holomorphic extension of the analytic `fSpatial ∘ Ψ`
on a neighbourhood of the compact core) exactly as in the planar package, not by a separate explicit denominator estimate.

## Checks
- `lp_build.sh` (one module per call, after the last edit): `AnalyticDomain.{Safety,Extension,Containment,Alignment}` and the facade `AnalyticDomain`: all `Build completed successfully` (Core: `Built … (13s)`); no `sorry`, no warning in my files.
- `lp_lint.sh`: exit 0 (`check_lean_modules: PASS (3737 Lean files…)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`). (First run flagged three lines over 100 characters; fixed.)
- `main_shortname_check.py` on the 6 modules: `short-name check OK`, exit 0.
- `#print axioms` (`.drafts/ax_spdom.lean`, via `lp_lean.sh`): all 13 main declarations (listed in that file) depend on exactly `[propext, Classical.choice, Quot.sound]`.
- Every module docstring contains the SPEC §4 sentence.

## AUDIT FOCUS
- `spatialSlowDeficit` vs MAIN (47): `|z|₂²/2` over all `4n` real slow coordinates (`slow w.1` and `slow w.2`, each of length `n+n`); the core uses the closed `≤ B(I⁰) − δ/4`.
- D3 uses only `spatialStrongAMD ≤ spatialFixedPlaneDeficit` (no `L ∥ e₃`), matching MAIN 593 ("including points whose total angular momentum is not parallel").
- D5: the slow hypotheses range over `Fin (n+n)` (both `ξ|v` and `η|u`); fast block index `Fin.castAdd (n+n)`, slow block `Fin.natAdd n`; the angle cell is recovered with `⌊Re λ/2π⌋` and the tube centre is `x + fastShift k`.
- `exists_spatialStrongTube` hypotheses: `2 ≤ n`, `IsCompact L`, `L ⊆ chamber ν`, `IsSharedTube`, `0 < δ`; the fast shift invariance of `spatialChartSafe` (`spatialChartSafe_shift_iff`) is the hypothesis `hWp` of `tubeNM`.
- Alignment lemmas assume `L = |L| e₃` / `L ≠ 0` as typing premises (MAIN 597), not conclusions; `J` order-connected (as `angularMomentum3_const`).

## Source defects, deviations, design signals
No MAIN defect found. Deviations: `Phase (n + (n + n))` rather than `n + 2n` (as SP-PROD); D3's compact set uses `exists_spatialBarrierCompact` (SP-GEO) rather than a planar barrier compact. Design signals: none; each module builds in 6–15 s under the 4 GB cap.
