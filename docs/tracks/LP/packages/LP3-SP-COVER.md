# Package LP3-SP-COVER: the spatial finite cover and normalized perturbation for LP3 (`k = n + n`)

LP3, spatial. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff;
module docstrings carry the SPEC §4 sentence). Base: `inp-lp-lp3spcov` = `inp-lp-spsrcb2` (every spatial LP package,
including SP-SAFE; proved, under audit) + `inp-lp-lp3cp` (planar LP3-COVERPERT, the template) + `inp-lp-lp3kep`.

The plan put the spatial packages "after LP-SP-SAFE lands". The spatial ingredients are proved and their statements
are reviewed, so this package starts on the unlanded branch. If an audit later changes an interface it uses, the
orchestrator re-merges and you (or a successor) adapt.

## Import ruling (D58 in docs/DECISIONS.md, main 56e4a2c4)

LP modules MAY import the **sealed** frozen anchor `KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev` and the
frozen definitions. Never import any `KAM/Provider/*` module.

## Template and source

- **Template (follow it closely):** the planar `KAM/Planetary/StrongAMD/Nek/Cover.lean` and `Nek/Perturbation.lean`,
  with their handoff `docs/tracks/LP/audits/LP3-COVERPERT-handoff.md`.
- **Plan:** `docs/tracks/LP/lp3/LP3-PLAN.md` §2.3, §2.5 (the spatial version: `k = 2n` slow pairs,
  `Phase (n + (n + n))`), §3, and the §5 row LP3-SP-COVER.
- **Spatial ingredients:**
  - `KAM/Planetary/Spatial/AnalyticDomain/{Extension,Containment}.lean` (`exists_spatialStrongTube`,
    `spatialStrongCore`, `spatialSecularBall`, containment D5);
  - `AnalyticDomain/Bounds.lean` (`SpatialTubeData`, `lemma18_complete`);
  - `ChartLift/Setting.lean` (`spLiftChartSafe`, `spLiftChartHam`, `spatialPulledHam`);
  - `ChartLift/Stopped.lean` (`spLiftSecularBall`).

## Statements (the spatial twins of COVERPERT; reuse its generic pieces, never duplicate them)

1. **Cells.** The fast cells are the planar ones verbatim: `nekCellInner`, `nekCellOuter`, `nekWidth/Eta/Rho`, the
   cover `IsNekCover`/`exists_isNekCover`, `nekCell_collar` and `IsNekCover.mem_innerCore`. Reuse them; if a planar
   lemma is stated with planar-only data, generalize it in your own file rather than editing it. The slow cell is
   `D_j = slowBall (n + n) (B(c_j) − 5δ/16)`, an open set in `Phase (n + n)`, with the slow gap `exists_nekSlowGap`
   for `2n` slow pairs (constant `√(2·2n)` or the exact one your erosion lemma needs; state it).
2. **Containment.** `partialComplexDomain G'_j D_j ρ ⊆ complexTubeNM (spatialStrongCore ν L δ r) (R/2)`, or the
   tube that SP-DOM/DOMX's extension `fc` lives on. Use exactly the tube where the spatial `fc` is holomorphic and
   bounded.
3. **Perturbation.** `P = fc/B₀` (cut off to `0` off the tube, as in the planar version);
   `IsPartialPerturbation G'_j D_j ρ (±P)` for every centre in `𝓛_δ`. Also give the `V_j` region, the identity
   `degenerateHamiltonian (realPart (planetaryKeplerC ν)) (Re P ∘ complexifyPhase) (B₀ μ) = spLiftChartHam ν μ` on
   `V_j` (or the spatial chart Hamiltonian that SP-LIFT's lift solves; state which one), and the field equality.
4. **Bundled** `exists_spatialNekPerturbation`, with the quantifier order of the planar `exists_nekPerturbation`.

## Owned files

`KAM/Planetary/Spatial/Nek/Cover.lean` and `KAM/Planetary/Spatial/Nek/Perturbation.lean` (new). Do not edit other
files (the generated `KAM/Root/Planetary.lean` excepted).

## Checks and stop condition

- `lp_build.sh` (the real check; `lp_lean.sh` may not catch missing binders).
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of the main declarations.

If an interface of the spatial packages does not fit, STOP and report the exact mismatch. Expected size 400–650 lines.

## Handoff

`docs/tracks/LP/audits/LP3-SP-COVER-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP3-SP-COVER.md`,
then `touch .drafts/READY-LP3-SP-COVER`.
