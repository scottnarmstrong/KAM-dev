# LP-W4A: combined audit handoff for LP-SP-MODEL + LP-SP-ROT (track LP, wave 4, spatial)

Branch `inp-lp-w4a` (worktree `/root/code/KAM-inp-lp-thr`) = `inp-lp-spmodel` (f0faca48) + `inp-lp` + `inp-lp-sprot`
(bfb15083, plus a pre-audit docstring sentence). The package diff is `git diff inp-lp...HEAD -- KAM`: the
`KAM/Planetary/Spatial/*` modules of SP-MODEL (Vector, Model, Field, Elements, Orbital, Momentum, Newton,
RotationAlgebra, Rotation, RotationSolution, Alignment; facade `Spatial.lean`) and SP-ROT (`Rotation46.lean`), plus the
regenerated root, about 2,360 lines. Nothing in track LP is frozen. These are the first spatial (d = 3) packages:
NEW definitions (the spatial Hamiltonian, solution and uniqueness predicates, Kepler elements, vector angular
momentum, spatial strong AMD, Newtonian reconstruction) that will enter the LP2 freeze proposal.

Prover handoffs: `docs/tracks/LP/audits/LP-SP-MODEL-handoff.md`, `LP-SP-ROT-handoff.md`. Briefs:
`/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-SP-MODEL.md`, `LP-SP-ROT.md`.

Source: `docs/tracks/LP/source/MAIN.md` §1 (1)–(2) with `d = 3`, Lemmas 1–3 (97–139), Lemma 17 (533–578: (46), the
`R e₃` identity, inverse), with `source/AMENDMENTS.md`. Design: roadmap §1–§2 (explicit `d = 3` public definitions,
Euclidean lengths, no `EuclideanSpace`); OWNER-DECISIONS OD-11 option (b) (source carriers for meaning-carrying
definitions; SP-MODEL adds `SpatialNegativeEnergy`, `SpatialElliptic`, `spatialStrongAMDOn`).

## Orchestrator checks (kam-lp)
- `lp_build.sh` of all 13 spatial modules in import order: built. `lp_lint.sh`: exit 0. Short-name check: OK.
  `git diff --check`: clean. Every module docstring carries the SPEC §4 sentence.

## REPORT FORMAT
One section per package (LP-SP-MODEL first, then LP-SP-ROT), each with a verdict, then a combined verdict.

## AUDIT FOCUS
LP-SP-MODEL:
- `spatialHamiltonian` is literally MAIN (1) in `d = 3` (kinetic `|p|²/(2ν)`, recoil `μ|Σp|²/2`, pair potentials
  `i<j`); `IsSpatialMovingSolutionOn` / `SpatialMovingUniqueOn` mirror the frozen planar predicates exactly.
- `IsSpatialNewtonSolutionOn` and the barycentric formulas (mass 1 at index 0, `G = 1`) and L1's reconstruction.
- L2 without a prograde premise (radial case), via the dimension-free `orbital_scalar`.
- L3 vector conservation (torque cancellation), the projection margin with `L̂ = L/|L|`, (13).
- Rotation invariance (`isSpatialMovingSolutionOn_rotate_iff`) and `exists_rotation_align` (det 1).
- OD-11 (b) carrier versions and their adequacy.
LP-SP-ROT:
- (46) literal; `incTilt` sign `(u, −v, 0)`; `skewMatrix` orientation; `Rᵀ R = 1`, `det R = 1`; `R e₃` (MAIN 559);
  cross-product invariance; the inverse (MAIN 571–576); analyticity on the carrier.
