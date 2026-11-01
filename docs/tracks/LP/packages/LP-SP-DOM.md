# Package LP-SP-DOM: the spatial whole-sublevel complex domain (MAIN Lemma 18)

Wave 4. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff;
module docstrings carry the SPEC §4 sentence). Base: `inp-lp-spdom` = `inp-lp` + LP-SP-MODEL, SP-GEO, SP-ROT,
SP-CHART, SP-PROD, SP-TUBE (handoffs in `docs/tracks/LP/audits/`).

## Template

The planar LP-DOM (landed: `KAM/Planetary/StrongAMD/AnalyticDomain/{Core,Safety,Extension,Containment}.lean`,
D0–D6; audit LP-W2A-1) and LP-DOMX (`AnalyticDomain/Bounds*`, `lemma8_complete`). MAIN L18: "Lemma 8 holds spatially
with `m = 2n`". Mirror D0–D6, using:
- the spatial product chart `spatialPoincareProd` on `Phase (n + (n + n))` (SP-PROD);
- `tubeNM` / `complexTubeNM` (SP-TUBE; never track P's `n+n` tube);
- the spatial barrier (SP-GEO: `SpatialBarrierState`, `exists_spatialBarrierCompact`);
- the dimension-free threshold, `𝓛_δ` and shared tube (`strongLevelSet`, `exists_isSharedTube`; reuse them, they
  are action-only).

## Source

`docs/tracks/LP/source/MAIN.md` Lemma 18 (580–597), (47), with `source/AMENDMENTS.md` N2, N3, N12. Lemma 8 (244–271) is
the planar original.

## Owned files

`KAM/Planetary/Spatial/AnalyticDomain.lean` (and parts). Do not edit other files.

## Statements (spatial D1–D6)

1. **D2 core.** `spatialStrongCore ν L δ r`: chart points `w : Phase (n + (n + n))` such that:
   - the fast angles lie in `[0, 2π]`;
   - `∃ I⁰ ∈ 𝓛_δ` with `‖I − I⁰‖ ≤ 4r`;
   - `(Σ slow²)/2 = Σ(Γ_i + Z_i) ≤ B(I⁰) − δ/4` (MAIN (47)).

   Prove it is compact, and that core points lie in `spatialPoincareProdDom n`: `Γ_i + Z_i < I_i` (MAIN line
   587: `Γ_i + Z_i ≤ B(I⁰) − δ/4 ≤ B(I) − 3δ/16 ≤ I_i − 3δ/16`).
2. **D3 safety, for the whole ball (MAIN line 589).** Core points map to `SpatialBarrierState ν U (3δ/16)`, even when
   `L` is not parallel to `e₃`. Use `spatialStrongAMD ≤ spatialFixedPlaneDeficit = Σ(Γ + Z)` (SP-PROD). Hence the
   core lies in the collision-free part of the chart domain.
3. **D4 extension.** `tubeNM` gives the holomorphic, fast-periodic extension `fc` of `fSpatial ν ∘ spatialPoincareProd ν`
   with real trace and a uniform sup bound `M` on the half tube. Constants come before `I⁰` and `μ`.
4. **D5 containment (MAIN (22) with (47), N3).** Complex chart points with:
   - actions within `r_*` (`r_* ≤ 4 r_g`) of `I⁰`;
   - `|Im λ| < 4s`;
   - complex slow coordinates (all `2n` pairs) within `4b` of a real point of ball (47);
   lie in the half tube.
5. **D6 split.** `spatialHamiltonian_spatialPoincareProd` restated on the collision-free part (cite SP-PROD).
6. **Alignment remark (MAIN 595–597).** For a spatial moving solution with `L ≠ 0`, after the rotation
   `exists_rotation_align_angularMomentum3` (SP-MODEL), `spatialStrongAMD = spatialFixedPlaneDeficit` along the
   solution (`L` is conserved and aligned with `e₃`). State the identity for aligned states (SP-PROD
   `…_of_aligned`), plus a lemma that the aligned rotated solution stays aligned (conservation).

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of items 1–6.

Expected size 800–1,800 lines. Stop when done or blocked.

## Handoff

`docs/tracks/LP/audits/LP-SP-DOM-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-SP-DOM.md`, then
`touch .drafts/READY-LP-SP-DOM`.
