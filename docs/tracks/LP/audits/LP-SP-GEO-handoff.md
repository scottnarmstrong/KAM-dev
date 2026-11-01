# LP-SP-GEO handoff (MAIN Lemmas 5–6 for d = 3; track LP, non-frozen)

Branch `inp-lp-spgeo`. All five items proved; no `sorry`/axiom/`set_option`; every file a module.
Namespace `KAM.Planetary.Spatial`. Existing file touched: only the generated `KAM/Root/Planetary.lean`.

## Files
- `KAM/Planetary/Spatial/Geometry.lean` (321 lines): G0, G2, G3, N11.
- `KAM/Planetary/Spatial/Continuation.lean` (157 lines): `spatial_moving_ode`, M3, M4, MAIN-shaped corollary.

Standing premises: `hν : ∀ i, 0 < ν i`, `hn : 2 ≤ n`, `hUc : IsCompact U`, `hUch : U ⊆ chamber ν`, `hm : 0 < m`.
Reused unchanged from the planar packages: `strongThreshold`, `DeficitBarrier`, `exists_deficitBarrier`,
`exists_axis_bound`, `chain_gap`, `perihelionFloor`, `strongThresholdModulus` and its lemmas.

## Definitions
- `spatialActionVector ν z := fun i => spatialKeplerAction ν z i`
- `SpatialBarrierState ν U m z := SpatialNegativeEnergy ν z ∧ spatialActionVector ν z ∈ U ∧ spatialStrongAMD ν z ≤ strongThreshold ν (spatialActionVector ν z) - m`
- `spatialBarrierCompact n dS dP R P`, `spatialMovingField ν μ := KAM.hamiltonianVectorField (spatialHamiltonian ν μ)`

## Declarations
1. G0 `actionAxis_spatialActionVector (hz : SpatialNegativeEnergy ν z) i : actionAxis ν (spatialActionVector ν z) i = spatialKeplerAxis ν z i`
2. G2 `spatialStrongBarrier_physical : ∃ dS dP R P c, 0<dS ∧ 0<dP ∧ 0<R ∧ 0<P ∧ 0<c ∧ DeficitBarrier ν U m dS dP ∧ ∀ z, SpatialBarrierState ν U m z → (perihelia ≥ dS) ∧ (adjacent gaps ≥ dP) ∧ (∀ i, dS ≤ |q_i|) ∧ (∀ i≠j, dP ≤ |q_i - q_j|) ∧ (|q_i| ≤ R) ∧ (|p_i| ≤ P) ∧ (E_i ≤ -c) ∧ (angularMomentum3 z ≠ 0 ∧ ∀ i, m ≤ spaceDot (planetAngularMomentum3 z i) (spatialUnit (angularMomentum3 z)))` (R = 2M, P = ν_max √(2/dS), c = ν_min/(2M), as planar).
3. G3 `exists_spatialBarrierCompact : ∃ K, IsCompact K ∧ K ⊆ {z | SpatialNoCollision z.1} ∧ ∀ z, SpatialBarrierState ν U m z → z ∈ K`
4. N11 `spatialPerihelionFloor_le` (explicit `aMin`, `Imax`, floor `perihelionFloor`).
5. `spatial_moving_ode ν μ`: open domain ∧ `ContDiffOn ℝ 1 (spatialMovingField ν μ)` ∧ `IsSpatialMovingSolutionOn ↔ IsSolutionIn` (via `analyticOnNhd_spatialHamiltonian`).
6. M3 `spatialStrongAMD_le_of_tube`: `C(z t) ≤ B(Λ(z t)) - δ + n*r + strongThresholdModulus ν U r` (uses `spatialStrongAMD_sub_eq_sum`; hypotheses as planar `strongAMD_le_of_tube`).
7. M4 `spatial_maximal_global_of_barrier` (`IsMaximalSolution (spatialMovingField ν μ) (spatialCollisionFreeDomain n) x₀ Tm Tp z`; barrier states near an end force `Tp = ⊤`, `Tm = ⊥`; via `gen_continuation_compact`), and `spatial_maximal_global_of_tube` (`n r + Ω ≤ δ/2`, so `m = δ/2`; assumes `SpatialNegativeEnergy` along the tail, as MAIN's ellipticity condition).

## Checks
- `lp_build.sh` of `KAM.Planetary.Spatial.Momentum` (prerequisite rebuild), then `.Geometry`, `.Continuation`: all `Build completed successfully`; no warnings in my files (only upstream `KAM/Kepler/Energy.lean`).
- `lp_lint.sh`: exit 0 (check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK), after `gen_root_imports.py` regenerated `KAM/Root/Planetary.lean`.
- `main_shortname_check.py` on both modules: `short-name check OK`, exit 0.
- `#print axioms` (scratch `.drafts/ax_spgeo.lean`, via `lp_lean.sh`) of G0, G2, G3, N11, `spatial_moving_ode`, M3, M4, corollary: all exactly `[propext, Classical.choice, Quot.sound]`.

## AUDIT FOCUS
- G2 projection margin is stated as `L ≠ 0 ∧ ∀ i, m ≤ L_i · L̂` (vector `L̂ = spatialUnit L`); `L ≠ 0` derived at index 0 (needs `n ≥ 1`, from `2 ≤ n`).
- `spaceLength` is Euclidean throughout; the `|p_i| ≤ P` step goes through `Real.sqrt_le_iff` on `spaceLength = √(spaceSq)` and `spatial_orbital_identities`'s `spaceSq p = ν²(2/|q| − 1/a)`.
- `DeficitBarrier` constants are literally the planar ones (dimension-free), joined to spatial eccentricity by definitional unfolding of `eccDeficit`.
- `SpatialBarrierState` uses `SpatialNegativeEnergy` (includes `0 < ν i`, `0 < |q_i|`, `E_i < 0`).
- M3 does not assume physical states along `J` (identity (13) needs only the solution), same harmless strengthening as planar.

## Source defects, deviations, design signals
- No errata in MAIN L5/L6 for d = 3. Deviations: (a) `KAM/Root/Planetary.lean` regenerated; (b) G2 margin in vector form instead of planar sign condition.
- Design signals: none (files build in 6–20 s under the 4 GB cap; largest file 321 lines).
