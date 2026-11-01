# LP-SP-OSC handoff (MAIN Lemma 16 with N10, d = 3; track LP, non-frozen)

Branch `inp-lp-sposc`. All four brief items proved. No `sorry`/axiom/`set_option`; every file a module; namespace
`KAM.Planetary.Spatial`. Only existing file touched: the generated `KAM/Root/Planetary.lean` (+4 imports from
`scripts/gen_root_imports.py`, needed for `lp_lint.sh`).

## Files (1,005 lines; largest 321)
- `KAM/Planetary/Spatial/Osculating/Estimates.lean` (303): `spatialSpecEnergy/Axis/EccVector k q V` on `Fin 3`; Lagrange identities,
  `spatialSpecAxis_tangency`, perturbation estimates (Fin 3 twins of planar `Osculating/Estimates.lean`).
- `.../Osculating/Core.lean` (117): `spatial_osc_core` (pointwise (43)). The dimension-free scalar parts are REUSED from the planar
  package: `abs_specAxis_sub_le`, `abs_peri_apo_sub_le`, `orbital_scalar`, `exists_pos_bounds_mass`, constants `oscAE, oscAF, oscB, oscAa, oscAe, oscAmax, oscAperi`.
- `.../Osculating/Basic.lean` (264): MAIN (42) definitions, velocity identification, dictionary, tangency, OD-11 (b) carrier.
- `KAM/Planetary/Spatial/Osculating.lean` (321): `SpatialOscEstimate`, `exists_spatial_osc_estimates`, `spatialBarrier_osc_data`,
  `spatial_osculating_barrier`, `spatialOscPhase_of_estimates`.

## Items
1. Definitions: `spatialOscVelocity := (1/ν i) • p_i + μ • ∑ j, p_j`, `spatialOscParam := 1 + μ * ν i`, `spatialOscEnergy`, `spatialOscAxis`,
   `spatialOscEccVector`, `spatialOscEcc`, `spatialOscPeri`, `spatialOscApo`, `spatialKeplerPeri/Apo` (literal MAIN (42); Euclidean `spaceLength`).
   OD-11 (b): `SpatialOscPhase n ν μ` (subtype: `0<ν`, `0<μ`, `0<|q_i|`, `E^osc<0`, `e^osc<1`), `spatialSourceOsc{Velocity,Param,Energy,Axis,EccVector,Ecc,Peri,Apo}`,
   `spatialSourceKeplerPeri/Apo` (on `SpatialElliptic`), defining equations `spatialSource*_eq` (all `rfl`), `spatialOscPhase_ellipse`
   (`0<a`, `0<a(1-e)`, `a(1-e) ≤ |q| ≤ a(1+e)`), `spatialOscPhase_of_estimates`.
   Dictionary: `spatialOsc*_eq_spec` (rfl), `spatialKeplerEnergy_eq_spec : spatialKeplerEnergy ν z i = ν i * spatialSpecEnergy 1 q ((1/ν i) • p)`, `…Axis…`, `…EccVector…`.
2. Velocity: `spatialOscVelocity_eq_hamiltonianVectorField (hz : SpatialNoCollision z.1) :
   bodyVector3 (hamiltonianVectorField (spatialHamiltonian ν μ) z).1 i = spatialOscVelocity ν μ z i` (and the `spatialMovingField` form inside item 4's conclusion; defeq).
   Tangency: `spatialOsc_tangency (hμ : 0 ≤ μ) (hν : 0 < ν i) (hq : 0 < |q_i|) (hE : E^osc < 0) : 0 < a ∧ oscPeri ≤ |q_i| ∧ |q_i| ≤ oscApo`.
3. (43) uniform: `exists_spatial_osc_estimates (hν) {K} {dS R P c eStar} (hdS hR hP hc) (he : eStar < 1) (hK : ∀ z ∈ K, SpatialNegativeEnergy ν z ∧ (∀ i, dS ≤ |q_i| ∧ |q_i| ≤ R) ∧
   (∀ i, |p_i| ≤ P) ∧ (∀ i, spatialKeplerEnergy ν z i ≤ -c) ∧ (∀ i, |spatialKeplerEccVector ν z i| ≤ eStar)) : ∃ μ0 A Aosc, 0<μ0 ∧ 0<A ∧ 0<Aosc ∧ ∀ μ, 0<μ → μ ≤ μ0 → ∀ z ∈ K, ∀ i, SpatialOscEstimate ν c μ A Aosc z i`.
   `SpatialOscEstimate ν c μ A Aosc z i :=` `oscEnergy ≤ -(c/ν i)/2 ∧ 0 < oscAxis ∧ oscPeri ≤ |q_i| ∧ |q_i| ≤ oscApo ∧ oscEcc < 1 ∧
   |oscAxis - keplerAxis| + |oscEccVector - keplerEccVector| ≤ A μ ∧ |oscPeri - keplerPeri| ≤ Aosc μ ∧ |oscApo - keplerApo| ≤ Aosc μ`.
   (F2: summed element estimate and ellipse validity exported explicitly.) Constants as planar: `A = M (Aa+Ae)`, `Aosc = M (2Aa + amax Ae)`, `M = 1+∑ν`, `D = nP`, `Pv = P/min ν`, `c1 = c/M`.
4. Bridge + half-gaps (N10): `spatialBarrier_osc_data hν hn hUc hUch hm : ∃ dS dP R P c eStar, positivity ∧ eStar<1 ∧ ∀ z, SpatialBarrierState ν U m z →
   SpatialNegativeEnergy ∧ SpatialNoCollision z.1 ∧ bounds of item 3 ∧ (∀ i, dS ≤ spatialKeplerPeri) ∧ (∀ a : AdjIdx n, dP ≤ keplerPeri upper - keplerApo lower)`, `eStar = 1 - 2 c dS/M`.
   `spatial_osculating_barrier hν hn hUc hUch hm : ∃ dS dP c, 0<dS ∧ 0<dP ∧ 0<c ∧ ∃ μ0 A Aosc, 0<μ0 ∧ 0<A ∧ 0<Aosc ∧ Aosc*μ0 ≤ dS/2 ∧ 2*(Aosc*μ0) ≤ dP/2 ∧
   ∀ μ, 0<μ → μ ≤ μ0 → ∀ z, SpatialBarrierState ν U m z → (∀ i, bodyVector3 (spatialMovingField ν μ z).1 i = spatialOscVelocity ν μ z i) ∧ (∀ i, SpatialOscEstimate ν c μ A Aosc z i) ∧
   (∀ i, dS/2 ≤ spatialOscPeri ν μ z i) ∧ (∀ a : AdjIdx n, dP/2 ≤ spatialOscPeri ν μ z a.upperIdx - spatialOscApo ν μ z a.1)`.

## Items not done
None. Not in scope: trajectory-level tangent-ellipse / `IsSpatialMovingSolutionOn` corollary (as planar).

## Checks
- `lp_build.sh /root/code/KAM-inp-lp-sposc` of `KAM.Planetary.Spatial.Osculating.{Estimates,Core,Basic}` then `KAM.Planetary.Spatial.Osculating`: each `Build completed successfully` (after prebuilding stale `Spatial.Geometry`, `Spatial.Field`, `StrongAMD.Osculating`). No warnings in my files.
- `lp_lint.sh`: exit 0 (check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK) — after wrapping lines to ≤ 100 chars.
- `main_shortname_check.py` on the four modules: `short-name check OK`, exit 0.
- `grep sorry|maxHeartbeats|axiom|admit|unsafe|opaque` in the four files: empty.
- `#print axioms` (scratch `.drafts/ax_sposc.lean`, via `lp_lean.sh`) of `spatialOscVelocity_eq_hamiltonianVectorField`, `spatialOsc_tangency`, `spatialSpecAxis_tangency`, `spatial_osc_core`, `exists_spatial_osc_estimates`, `spatialBarrier_osc_data`, `spatial_osculating_barrier`, `spatialOscPhase_of_estimates`, `spatialOscPhase_ellipse`, `spatialKeplerAxis_eq_spec`: all exactly `[propext, Classical.choice, Quot.sound]`.

## AUDIT FOCUS
- **Mass scale.** Energy clause is the specific `-(c/ν i)/2` (as planar audit note); `spatialKeplerEnergy` is the total `ν_i E_i`. `M = 1+∑ν`, no normalization assumed.
- **Tangency with `Fin 3`.** `spatialSpecAxis_tangency` feeds `orbital_scalar` with `C = √k · |q × V|` (length, not signed), `s = k|V|²`; check `hC2`, `hecc2`, `hdot2` (Lagrange identity `spaceSq_spatialSpecEccVector`, radial identity with `spaceSq (spaceCross q V)`).
- **Reuse of planar scalar algebra** (`abs_specAxis_sub_le`, `abs_peri_apo_sub_le`, constants): dimension free; `spatial_osc_core` states `hax'` by definitional unfolding of `spatialSpecAxis`.
- `spatialOscEccVector` uses `(1/k) •`; all lengths Euclidean `spaceLength`. Circular case: reverse triangle inequality only.
- Bridge `spatialBarrier_osc_data`: `SpatialNoCollision` from `dS ≤ |q_i|` and `dP ≤ |q_i - q_j|` (G2); `eStar` from `a ≤ M/(2c)`.
- `μ0 = min μ1 (min (dS/(2Aosc)) (dP/(4Aosc)))`; both N10 inequalities are in the conclusion.
- Carrier `SpatialOscPhase` requires `0<μ` and `0<ν`, includes `E^osc<0`, `e^osc<1` as carrier conditions; they are outputs of the theorem, never hypotheses.

## Source defects, deviations, design signals
- No errata in MAIN L16 for d = 3. Remark (as planar): `|k_i - 1| ≤ μ` in the proof sketch needs `ν_i ≤ 1`; here `≤ M μ`.
- Deviations: energy clause specific scale; added `0<a`, `e<1`, tangency to `SpatialOscEstimate`; `KAM/Root/Planetary.lean` regenerated; the four modules wrapped to ≤ 100 chars for lint.
- Design signals: none (each file builds in ≈ 10 s under the 4 GB cap).
