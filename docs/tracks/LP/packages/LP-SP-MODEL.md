# Package LP-SP-MODEL: the spatial exact model, orbital identities and vector angular momentum (MAIN L1–L3, d = 3)

Wave 4, first spatial package. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped
wrappers, handoff). Base: `inp-lp`.

## Design (spatial; roadmap §1–§2, §3 rows 1–3)

- The frozen planar definitions are `Fin 2`-specific (`bodyVector`, `planeLength`, `planeCross`,
  `movingHamiltonian`, `IsMovingSolutionOn`, `IsNewtonSolutionOn`), so the spatial track needs its own
  dimension-three definitions under `KAM/Planetary/Spatial/`, namespace `KAM.Planetary.Spatial`.
- Roadmap §2: "Fixing `d = 2` and `d = 3` in two public declarations is preferable to making dimension-generic
  cross-product machinery part of the public surface." Use explicit `Fin 3` vectors and an explicit cross
  product. Generic internal helpers are fine, but never on the public statement surface.
- Ambient types: `Phase (n * 3) = (Fin (n*3) → ℝ) × (Fin (n*3) → ℝ)` (the frozen `Phase` is dimension-free), with
  a block map `bodyVector3` (via `finProdFinEquiv`, as the frozen `bodyVector` does). Physical lengths are
  Euclidean, never the Pi sup norm. Never `EuclideanSpace`.
- These definitions will enter the LP2 freeze proposal. Write them literally from MAIN (1)–(2), with no `if`
  totalization. Per OD-11 recommendation (b), add source-carrier versions with characterizations wherever a
  quantity is meaning-carrying only on a carrier (e.g. the Kepler elements on negative energy).

## Source

`docs/tracks/LP/source/MAIN.md` §1 (lines 9–93: (1), (2), `d = 3`), Lemma 1 (97–108), Lemma 2 (110–128), Lemma 3
(130–139), with `source/AMENDMENTS.md`. The planar packages are templates: LP-MOM
(`KAM/Planetary/StrongAMD/{Orbital,Momentum,Reflection}.lean`) and track P's planar `Newtonian/*`,
`AMD/AngularMomentum.lean`.

## Owned files

`KAM/Planetary/Spatial/*.lean` (suggested: `Vector.lean`, `Model.lean`, `Orbital.lean`, `Momentum.lean`,
`Rotation.lean`, `Newton.lean`) and the facade `KAM/Planetary/Spatial.lean`. Nothing else.

## Definitions (literal)

- **Vectors.** `spaceDot`, `spaceSq`, `spaceLength = √spaceSq`, `spaceCross` (the standard cross product on
  `Fin 3 → ℝ`).
- **Blocks.** `bodyVector3 : (Fin (n*3) → ℝ) → Fin n → Fin 3 → ℝ`.
- **Model.**
  - `spatialHamiltonian ν μ z := Σ_i (|p_i|²/(2ν_i) − ν_i/|q_i|) + μ (|Σ_i p_i|²/2 − Σ_{i<j} ν_iν_j/|q_i − q_j|)`
    (MAIN (1)).
  - `SpatialNoCollision`.
  - `IsSpatialMovingSolutionOn ν μ J z := KAM.Iso.IsHamiltonianSolutionOn (spatialHamiltonian ν μ) univ J z ∧
    ∀ t ∈ J, SpatialNoCollision (z t).1`, matching the frozen planar `IsMovingSolutionOn` pattern.
  - `SpatialMovingUniqueOn`, the frozen planar `MovingUniqueOn` pattern.
- **Elements.** `spatialKeplerEnergy` (total, `ν_i E_i`, as the planar convention), `spatialKeplerAxis`,
  `spatialKeplerAction`, `spatialKeplerEccVector`, `angularMomentum3 z := Σ_i q_i × p_i`, and
  `spatialStrongAMD ν z := Σ_i Λ_i − |L|` (MAIN (2), Euclidean `|L|`).
- **Newton (MAIN L1).** `spatialBarycentricPositions`, `spatialBarycentricVelocities` (the planar frozen
  formulas, with `Fin 3`), `IsSpatialNewtonSolutionOn`, the planar frozen pattern with Euclidean lengths.

## Theorems

1. **L1.** A spatial moving solution with positive masses and `μ ≥ 0` reconstructs a Newtonian solution with masses
   `(1, μν_1, …, μν_n)` (track P's planar `Newtonian/Reconstruction.lean` is the template).
2. **L2 (d = 3, no prograde premise; radial case included).** For `0 < ν_i`, `q_i ≠ 0` and negative energy:
   - `0 < a`, `Λ² = ν² a`;
   - `e² = 1 − |L_i|²/Λ²`, `e ≤ 1`, `|L_i| = Λ √(1 − e²)`, `|L_i| ≤ Λ`;
   - `a(1 − e) ≤ |q| ≤ a(1 + e)`, and `|p|² = ν²(2/|q| − 1/a)`.
3. **L3 (vector).**
   - `angularMomentum3` is constant along spatial moving solutions (torque cancellation, MAIN line 136).
   - `spatialStrongAMD ≥ 0`.
   - If `spatialStrongAMD < Λ_k` for some `k`, then `L ≠ 0`.
   - With `L̂ = L/|L|`, the projections satisfy `Λ_i − C ≤ L_i · L̂`, so `C ≤ min Λ − m` gives `L_i · L̂ ≥ m`.
   - (13): `C(t) − C(s) = Σ(Λ_i(t) − Λ_i(s))`, and `Σ Λ_i (1 − √(1 − e_i²)) ≤ C`.
4. **Rotation invariance (for the alignment in MAIN L18).** For a rotation `R` (`Rᵀ R = 1`, `det R = 1`) applied to
   every `q_i` and `p_i`:
   - invariant: `spatialHamiltonian`, `SpatialNoCollision`, energies, axes, actions, `|𝐞_i|`, all lengths and
     `spatialStrongAMD`;
   - `L ↦ R L`;
   - `IsSpatialMovingSolutionOn ν μ J z ↔ IsSpatialMovingSolutionOn ν μ J (R ∘ z)`;
   - for every nonzero `L` there is a rotation with `R (L/|L|) = e₃`.

## Checks and stop condition

- `lp_build.sh` on each module.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of items 1–4.

Stop when done or blocked; report, and never add a hypothesis silently. This is a large package (expected
1,500–3,000 lines). Split it into focused modules and commit after each item.

## Handoff

`docs/tracks/LP/audits/LP-SP-MODEL-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-SP-MODEL.md`,
then `touch .drafts/READY-LP-SP-MODEL`.
