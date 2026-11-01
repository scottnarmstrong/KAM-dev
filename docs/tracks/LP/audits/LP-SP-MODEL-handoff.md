# LP-SP-MODEL handoff (wave 4: spatial exact model, MAIN L1–L3 for d = 3, rotation invariance)

Branch `inp-lp-spmodel`. Track LP, non-frozen. No `sorry`, `axiom`, `admit`, `unsafe`, `opaque`; no `set_option`
of any kind; every file is a Lean module; largest file 353 lines. Existing files touched: only the generated
`KAM/Root/Planetary.lean` (output of `scripts/gen_root_imports.py`, needed for `lp_lint.sh` to exit 0).

## Files (all new, namespace `KAM.Planetary.Spatial`, facade `KAM/Planetary/Spatial.lean`)
| File | Content |
|---|---|
| `Vector.lean` | `spaceDot`, `spaceSq`, `spaceLength`, `spaceCross` (explicit components), `bodyVector3`, `ofBodies3`, `posCLM3/momCLM3`; algebra (Lagrange, Cauchy–Schwarz, Binet–Cauchy), calculus of `1/|v|`; bridges `spaceDot_eq_dotProduct`, `spaceSq_eq_dotProduct`, `spaceCross_eq_crossProduct` (Mathlib `dotProduct`, `crossProduct`, per the LP-SP-ROT coordination note) |
| `Model.lean` | `spatialHamiltonian`, `SpatialNoCollision`, `IsSpatialMovingSolutionOn`, `SpatialMovingUniqueOn`, `spatialGKernel/FKernel`; openness of the collision-free domain, analyticity/differentiability of `H_μ`, action–reaction |
| `Field.lean` | `hamiltonianVectorField_spatial`: the Hamilton field in body blocks |
| `Elements.lean` | `spatialKeplerEnergy/Axis/Action/EccVector`, `planetAngularMomentum3`, `angularMomentum3`, `spatialStrongAMD`; carrier `SpatialNegativeEnergy`, subtype `SpatialElliptic`, `spatialStrongAMDOn` (OD-11 (b)) |
| `Orbital.lean` | L2 |
| `Momentum.lean` | L3 |
| `Newton.lean` | `spatialBarycentricPositions/Velocities`, `spatialMasses`, `IsSpatialNewtonSolutionOn`, L1 |
| `RotationAlgebra.lean`, `Rotation.lean`, `RotationSolution.lean`, `Alignment.lean` | rotation invariance |

## Items proved (declaration names; statements as elaborated, abbreviated binders)
Definitions (literal, no `if`):
- `spatialHamiltonian ν μ z = (∑ i, (spaceSq (bodyVector3 z.2 i) / (2 * ν i) - ν i / spaceLength (bodyVector3 z.1 i))) + μ * (spaceSq (∑ i, bodyVector3 z.2 i) / 2 - ∑ i, ∑ j ∈ univ.filter (i < ·), ν i * ν j / spaceLength (bodyVector3 z.1 i - bodyVector3 z.1 j))` on `Phase (n * 3)` (MAIN (1)).
- `SpatialNoCollision q := (∀ i, 0 < spaceLength (bodyVector3 q i)) ∧ ∀ i j, i ≠ j → 0 < spaceLength (bodyVector3 q i - bodyVector3 q j)`.
- `IsSpatialMovingSolutionOn ν μ J z := KAM.Iso.IsHamiltonianSolutionOn (spatialHamiltonian ν μ) Set.univ J z ∧ ∀ t ∈ J, SpatialNoCollision (z t).1`; `SpatialMovingUniqueOn`: the frozen planar `MovingUniqueOn` pattern.
- `spatialKeplerEnergy ν z i = spaceSq p / (2 ν i) - ν i / |q|` (= ν_i E_i, planar convention), `spatialKeplerAxis = -ν i / (2 * energy)`, `spatialKeplerAction = ν i * √axis`, `spatialKeplerEccVector = (|p|²/ν² - 1/|q|) • q - (q·p/ν²) • p`, `angularMomentum3 z = ∑ i, spaceCross (bodyVector3 z.1 i) (bodyVector3 z.2 i)`, `spatialStrongAMD ν z = ∑ i, spatialKeplerAction ν z i - spaceLength (angularMomentum3 z)`.

Theorems:
1. **L1** `isSpatialNewtonSolutionOn_of_isSpatialMovingSolutionOn (hm : ∀ i, 0 < ν i) (hμ : 0 ≤ μ) (hz : IsSpatialMovingSolutionOn ν μ J z) : IsSpatialNewtonSolutionOn (spatialMasses ν μ) J (fun t => spatialBarycentricPositions ν μ (z t).1) (fun t => spatialBarycentricVelocities ν μ (z t).2)`; masses `(1, μν_1, …, μν_n)`, `G = 1`, Euclidean lengths, any time set `J`. Supporting: `hamiltonianVectorField_spatial` (blocks `p/ν + μ Σp` and `-ν g + μ ν f`).
2. **L2** `spatial_orbital_identities (i) (hz : 0 < ν i ∧ 0 < spaceLength (bodyVector3 z.1 i) ∧ spatialKeplerEnergy ν z i < 0)`: `0 < a ∧ 0 < Λ ∧ Λ² = ν² a ∧ e² = 1 - |L_i|²/Λ² ∧ e ≤ 1 ∧ |L_i| = Λ √(1-e²) ∧ |L_i| ≤ Λ ∧ a(1-e) ≤ |q| ∧ |q| ≤ a(1+e) ∧ |p|² = ν²(2/|q| - 1/a)`, `e = spaceLength (spatialKeplerEccVector ν z i)`, `|L_i| = spaceLength (planetAngularMomentum3 z i)`. No prograde premise; radial case included. Reduces to the planar dimension-free `StrongAMD.orbital_scalar`.
3. **L3 (vector)**, carrier hypothesis `hz : SpatialNegativeEnergy ν z` (all `i`: `0 < ν i`, `0 < |q_i|`, `E_i < 0`):
   - `angularMomentum3_const (hJ : J.OrdConnected) (hz : IsSpatialMovingSolutionOn ν μ J z) : ∀ s ∈ J, ∀ t ∈ J, angularMomentum3 (z t) = angularMomentum3 (z s)` (vector; torque cancellation via `sum_cross_rate_eq_zero`).
   - `spatialStrongAMD_nonneg`; `angularMomentum3_ne_zero_of_strongAMD_lt (hk : spatialStrongAMD ν z < spatialKeplerAction ν z k) : angularMomentum3 z ≠ 0`.
   - `action_sub_strongAMD_le_proj (hL : angularMomentum3 z ≠ 0) i : Λ_i - C ≤ spaceDot (L_i) (spatialUnit L)`; `proj_margin (hm : 0 < m) (hC : ∀ i, C ≤ Λ_i - m) i : L ≠ 0 ∧ m ≤ L_i · L̂`; `spatialUnit L = (spaceLength L)⁻¹ • L`.
   - (13): `spatialStrongAMD_sub_eq_sum` (`C(t) - C(s) = Σ (Λ_i(t) - Λ_i(s))`), `spatialStrongAMD_eq_sum_sub_proj` (`C = Σ (Λ_i - L_i·L̂)` for `L ≠ 0`), `sum_action_mul_eccDeficit_le_spatialStrongAMD` (`Σ Λ_i (1 - √(1-e_i²)) ≤ C`).
4. **Rotation** (`R : Matrix (Fin 3) (Fin 3) ℝ`, `hR : Rᵀ * R = 1`, `hdet : R.det = 1`; `spatialRotatePhase R z` applies `R` to every `q_i`, `p_i`): `mulVec_spaceCross` (`R(a×b) = Ra × Rb`), `spatialHamiltonian_rotate`, `spatialNoCollision_rotate_iff`, `spatialKeplerEnergy/Axis/Action_rotate`, `spatialKeplerEccVector_rotate` (`𝐞 ↦ R𝐞`), `spaceLength_spatialKeplerEccVector_rotate`, `spatialNegativeEnergy_rotate_iff`, `planetAngularMomentum3_rotate`, `angularMomentum3_rotate` (`L ↦ R L`), `spatialStrongAMD_rotate`, `hamiltonianVectorField_spatial_rotate`, `isSpatialMovingSolutionOn_rotate_iff : IsSpatialMovingSolutionOn ν μ J z ↔ IsSpatialMovingSolutionOn ν μ J (fun t => spatialRotatePhase R (z t))` (only `hR` is needed), `exists_rotation_align (hL : L ≠ 0) : ∃ R, Rᵀ * R = 1 ∧ R.det = 1 ∧ R *ᵥ spatialUnit L = ![0,0,1]`, `exists_rotation_align_angularMomentum3`.

## Not done
- Rotation invariance of `SpatialMovingUniqueOn` (not requested in the brief; follows from the iff).
- MAIN's "if `C < B_⋆(I)` then all `H_i` are positive" is stated in margin form (`proj_margin`, and the strict corollary `0 < Λ_i - C ≤ H_i` is immediate from `action_sub_strongAMD_le_proj`); `B_⋆` itself is not referenced here (threshold package).

## Checks
- `lp_build.sh /root/code/KAM-inp-lp-spmodel KAM.Planetary.Spatial` (after each module individually): `Build completed successfully (9113 jobs).`
- `lp_lint.sh`: exit 0 (`check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`) after regenerating `KAM/Root/Planetary.lean`.
- `main_shortname_check.py`: `short-name check OK`.
- `#print axioms` (scratch `.drafts/axioms_spmodel.lean`, via `lp_lean.sh`) of every main declaration above: `[propext, Classical.choice, Quot.sound]` only.

## AUDIT FOCUS
1. `spatialHamiltonian`: literal MAIN (1) (kinetic `|p|²/(2ν)`, recoil `μ|Σp|²/2`, pair potentials `i<j`), compared with the frozen planar `movingHamiltonian 1 1 ν μ` (`(1/ν + μ)|p|²/2 + μ Σ_{i<j} p_i·p_j` form; equal by `|Σp|² = Σ|p|² + 2Σ_{i<j}`, proved as `spaceSq_sum`).
2. `IsSpatialMovingSolutionOn` mirrors the frozen planar predicate (including the guard `DifferentiableAt` and domain `univ`).
3. `spatialBarycentric*` use `m₀ = 1` literally (`-μ/(1+μΣν)`, velocity `-μ Σ p`); `IsSpatialNewtonSolutionOn` has `G = 1` and mass at index 0 equal to `1`.
4. `spatialKeplerEnergy` is the total `ν_i E_i` (planar convention), so `spatialKeplerAxis = -ν/(2·energy)`; all elements are total definitions, meaningful on `SpatialNegativeEnergy` (OD-11 (b): carrier + `SpatialElliptic` + `spatialStrongAMDOn`).
5. `spatialStrongAMD` uses `spaceLength` of the vector `L` (Euclidean), not the Pi sup norm; `spaceCross` orientation is the standard one (`spaceCross_eq_crossProduct`).
6. The rotation orientation (`det R = 1`) matters only for `L ↦ R L`; solutions/Hamiltonian/lengths are invariant under all orthogonal `R`.

## Source defects, deviations, design signals
- No suspected errata in MAIN L1–L3 for d = 3.
- Deviations: (a) L2/L3 per-planet statements use `spaceLength (L_i)` for `|L_i|` (vector), not an absolute value of a scalar; (b) `L̂` is the explicit `spatialUnit` and statements carry `L ≠ 0`; (c) `KAM/Root/Planetary.lean` regenerated by the script (existing generated file).
- Design signals: none (no heartbeat problems, no OOM; each file builds in ≈ 5–15 s under the 4 GB cap).
