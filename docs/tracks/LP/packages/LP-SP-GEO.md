# Package LP-SP-GEO: the spatial uniform barrier and continuation (MAIN Lemmas 5–6 for d = 3)

Wave 4. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff).
Base: `inp-lp-spgeo` = `inp-lp` (all planar packages) + LP-SP-MODEL (`KAM/Planetary/Spatial/*`; handoff
`docs/tracks/LP/audits/LP-SP-MODEL-handoff.md`).

## Why

MAIN Lemmas 5–6 are stated for `d = 2, 3`. The planar versions are LP-GEOMOD (`Geometry.lean`, `Modulus.lean`,
`Continuation.lean`). The threshold side is dimension-free and reused unchanged: THR (`strongThreshold`,
`orderedStrongThreshold`, `pairThreshold_le_of_feasible`, `DeficitBarrier`) and Modulus (`strongThresholdModulus`
and its lemmas, `exists_cthickening_compact`). Only the physical side changes: spatial elements, vector `L`,
Euclidean lengths in `ℝ³`, and the spatial moving field.

## Source

`docs/tracks/LP/source/MAIN.md` Lemma 5 (162–175), Lemma 6 (177–189), with `source/AMENDMENTS.md` N2 and N11.
LP-GEOMOD's statements and proofs are the template: `docs/tracks/LP/audits/LP-GEOMOD-handoff.md`.

## Owned files

`KAM/Planetary/Spatial/Geometry.lean`, `KAM/Planetary/Spatial/Continuation.lean` (split with facades if needed).
Do not edit LP-SP-MODEL or planar files.

## Statements (spatial analogues of LP-GEOMOD, same quantifier order)

Standing premises: `hν`, `2 ≤ n`, compact `U ⊆ chamber ν`, `0 < m`. Write:
- `Λ z := fun i => spatialKeplerAction ν z i`;
- `C := spatialStrongAMD ν z`;
- `B := strongThreshold ν`;
- `SpatialBarrierState ν U m z :=` negative energy on every planet (`SpatialNegativeEnergy`) `∧ Λ z ∈ U ∧
  C ≤ B (Λ z) − m`.

1. **G0.** `actionAxis ν (Λ z) i = spatialKeplerAxis ν z i` on negative-energy states.
2. **G2 (physical form).** `∃ dS dP R P c > 0` (from LP-GEOMOD's `DeficitBarrier` constants, reused) such that
   every `SpatialBarrierState` satisfies:
   - perihelia `≥ dS`, adjacent annulus gaps `≥ dP`;
   - `|q_i| ≥ dS`, all-pairs `|q_i − q_j| ≥ dP`, `|q_i| ≤ R`, `|p_i| ≤ P`, energies `≤ −c`;
   - the projection margin: `L ≠ 0` and `m ≤ L_i · L̂` for every `i` (SP-MODEL's `proj_margin`).

   Use SP-MODEL's `spatial_orbital_identities` and `sum_action_mul_eccDeficit_le_spatialStrongAMD`.
3. **G3 (compactness).** `∃ K, IsCompact K ∧ K ⊆ {z | SpatialNoCollision z.1} ∧` every `SpatialBarrierState` lies
   in `K`.
4. **M3 (17), spatial.** For a spatial moving solution on `OrdConnected J ∋ 0` with
   `‖Λ(z t) − Λ(z 0)‖ ≤ r` and both actions in `U`:
   `C(z t) ≤ B(Λ(z t)) − δ + n r + strongThresholdModulus ν U r` when `C(z 0) ≤ B(Λ(z 0)) − δ`. Use SP-MODEL's
   `spatialStrongAMD_sub_eq_sum`.
5. **M4 (continuation).** For the maximal solution of the spatial moving field on the open collision-free domain
   (C¹ via SP-MODEL's analyticity; use `KAM.ODE.gen_continuation_compact` as in LP-GEOMOD): barrier states near
   the ends force `Tp = ⊤` and `Tm = ⊥`.

## Checks and stop condition

- `lp_build.sh` on each module.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of items 1–5.

Expected size 800–1,600 lines. Stop when done or blocked; report.

## Handoff

`docs/tracks/LP/audits/LP-SP-GEO-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-SP-GEO.md`, then
`touch .drafts/READY-LP-SP-GEO`.
