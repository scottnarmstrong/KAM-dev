# Track LP freeze and seal (decision D62)

Branch `inp-lp-freeze` (off `inp` 6798a3c5), one pass and one landing (orchestrator plan change, root-b8; precedent:
track R "froze and sealed", `docs/MANIFEST-CHANGES.md`). Freezes and seals exactly the 128 files of FREEZE-PROPOSAL
draft 7 revision 1, the approval object `inp-lp-freeze7` at `de343000` (`docs/tracks/LP/freeze/draft7/**.txt`, D62):
89 definitions, 34 characterization theorems and 5 anchors (LP0, LP1, LP1-H, LP2, LP2-H). Draft 8 (LP3) is not
included (it awaits its own approval).

## Commits

- S0: merge `inp-lp` (ad2c28fe) and the approved `de343000` (8e6f75d0); roots unchanged.
- A (172f4234): the 89 frozen definitions; implementation rebased (FREEZE-PROPOSAL §7).
- B (9a23d75c): the 39 theorem anchors installed sealed; the 39 providers; the 34 characterization lemmas moved out
  of the implementation into their providers; 128 manifest entries SEALED (ABI placeholders); roots.
- C: ABI hashes; this record; the MANIFEST-CHANGES rows; check outputs.

## Method (scripts in `docs/tracks/LP/freeze/`, all reusing the guard's own code)

1. `mk_rebase_plan.py` → `rebase-plan.json`: the machine form of the approved §7 rebase table and §5
   characterization table (read from `de343000`).
2. `lp_rebase.py --phase defs`: deletes exactly the 89 listed `def`/`abbrev` blocks (with docstrings) from 11
   implementation modules and adds the `public import`s of their frozen files; asserted that no other line changes.
3. `lp_freeze_install.py --kind definition` and `--kind theorem --sealed`: each file is the approved draft with only
   `<APPROVAL-DATE>` → `2026-11-01` and `<DECISION>` → `D62` filled (each exactly once), and, for a theorem, the
   body between the `FROZEN_ANCHOR_PROOF` markers set to `by exact <provider export> <explicit binders>`, with the
   binders from `Guard.explicit_binders`, wrapped at 100 columns with a 6-space continuation, and asserted equal to
   the sealing string of the file's own docstring.
4. `lp_rebase.py --phase characterizations`: deletes the 34 characterization lemmas from `Threshold/Pair.lean` (2),
   `StrongAMD/SourceCarrier.lean` (10), `Spatial/SourceCarrier.lean` (20) and `PlanarSafety/SourceThreshold.lean`
   (2; the module is then empty and deleted), recording their proofs. A sealed frozen theorem carries the lemma's
   fully qualified name, so the two cannot coexist.
5. `lp_providers.py`: the 5 anchor providers are copied byte for byte from `inp-lp-providers` (f2fa9f88). The 34
   characterization providers are f2fa9f88's files (same header, imports, namespace, opens, and the anchor's exact
   statement text), with the one-line proof replaced by the implementation proof moved verbatim (§7 point 3).
   `sourceOscPeri_pos` and `orderedStrongThreshold_isLeast` get their sibling (`sourceOscAxis_pos`,
   `orderedCrossThreshold_isLeast`) verbatim as a `private theorem`. No provider imports a provider or a frozen theorem.
6. `lp_manifest_add.py`: 128 entries from the approved `manifest-entries.json`; `author_approval` and
   `split_policy.ruling_ref` from `approval-D62.json`; state SEALED; `full_file_sha256`, `prefix_sha256`,
   `suffix_sha256` and closure hashes with `Guard.digest` and `Guard.check_theorem_region`; each drafted
   `definition_closure` cross-checked against the import closure. The 179 earlier entries are JSON-equal.
   `abi_sha256` comes from `scripts/abi_hashes.py` on the 128 new entries (two runs, identical).
7. `scripts/gen_root_imports.py`; `lp_manifest_changes_rows.py` (128 rows, citing D62).

## Files

| # | Declaration | Frozen file | Manifest id | Kind | Provider |
|---|---|---|---|---|---|
| 1 | `KAM.Planetary.StrongAMD.actionAxis` | `KAM/Frozen/Planetary/StrongAMD/Defs/ActionAxis.lean` | `planetary.d59.actionAxis.v1` | definition | — |
| 2 | `KAM.Planetary.StrongAMD.chamber` | `KAM/Frozen/Planetary/StrongAMD/Defs/Chamber.lean` | `planetary.d59.chamber.v1` | definition | — |
| 3 | `KAM.Planetary.StrongAMD.eccDeficit` | `KAM/Frozen/Planetary/StrongAMD/Defs/EccDeficit.lean` | `planetary.d59.eccDeficit.v1` | definition | — |
| 4 | `KAM.Planetary.StrongAMD.pairFeasible` | `KAM/Frozen/Planetary/StrongAMD/Defs/PairFeasible.lean` | `planetary.d59.pairFeasible.v1` | definition | — |
| 5 | `KAM.Planetary.StrongAMD.pairObjective` | `KAM/Frozen/Planetary/StrongAMD/Defs/PairObjective.lean` | `planetary.d59.pairObjective.v1` | definition | — |
| 6 | `KAM.Planetary.StrongAMD.pairThreshold` | `KAM/Frozen/Planetary/StrongAMD/Defs/PairThreshold.lean` | `planetary.d59.pairThreshold.v1` | definition | — |
| 7 | `KAM.Planetary.StrongAMD.AdjIdx` | `KAM/Frozen/Planetary/StrongAMD/Defs/AdjIdx.lean` | `planetary.d59.AdjIdx.v1` | definition | — |
| 8 | `KAM.Planetary.StrongAMD.AdjIdx.upperIdx` | `KAM/Frozen/Planetary/StrongAMD/Defs/AdjIdxUpperIdx.lean` | `planetary.d59.AdjIdx.upperIdx.v1` | definition | — |
| 9 | `KAM.Planetary.StrongAMD.OrderedActions` | `KAM/Frozen/Planetary/StrongAMD/Defs/OrderedActions.lean` | `planetary.d59.OrderedActions.v1` | definition | — |
| 10 | `KAM.Planetary.StrongAMD.orderedPairThreshold` | `KAM/Frozen/Planetary/StrongAMD/Defs/OrderedPairThreshold.lean` | `planetary.d59.orderedPairThreshold.v1` | definition | — |
| 11 | `KAM.Planetary.StrongAMD.orderedCrossThreshold` | `KAM/Frozen/Planetary/StrongAMD/Defs/OrderedCrossThreshold.lean` | `planetary.d59.orderedCrossThreshold.v1` | definition | — |
| 12 | `KAM.Planetary.StrongAMD.orderedStrongThreshold` | `KAM/Frozen/Planetary/StrongAMD/Defs/OrderedStrongThreshold.lean` | `planetary.d59.orderedStrongThreshold.v1` | definition | — |
| 13 | `KAM.Planetary.StrongAMD.strongAMD` | `KAM/Frozen/Planetary/StrongAMD/Defs/StrongAMD.lean` | `planetary.d59.strongAMD.v1` | definition | — |
| 14 | `KAM.Planetary.StrongAMD.keplerPeri` | `KAM/Frozen/Planetary/StrongAMD/Defs/KeplerPeri.lean` | `planetary.d59.keplerPeri.v1` | definition | — |
| 15 | `KAM.Planetary.StrongAMD.keplerApo` | `KAM/Frozen/Planetary/StrongAMD/Defs/KeplerApo.lean` | `planetary.d59.keplerApo.v1` | definition | — |
| 16 | `KAM.Planetary.StrongAMD.oscVelocity` | `KAM/Frozen/Planetary/StrongAMD/Defs/OscVelocity.lean` | `planetary.d59.oscVelocity.v1` | definition | — |
| 17 | `KAM.Planetary.StrongAMD.oscParam` | `KAM/Frozen/Planetary/StrongAMD/Defs/OscParam.lean` | `planetary.d59.oscParam.v1` | definition | — |
| 18 | `KAM.Planetary.StrongAMD.oscEnergy` | `KAM/Frozen/Planetary/StrongAMD/Defs/OscEnergy.lean` | `planetary.d59.oscEnergy.v1` | definition | — |
| 19 | `KAM.Planetary.StrongAMD.oscAxis` | `KAM/Frozen/Planetary/StrongAMD/Defs/OscAxis.lean` | `planetary.d59.oscAxis.v1` | definition | — |
| 20 | `KAM.Planetary.StrongAMD.oscEccVector` | `KAM/Frozen/Planetary/StrongAMD/Defs/OscEccVector.lean` | `planetary.d59.oscEccVector.v1` | definition | — |
| 21 | `KAM.Planetary.StrongAMD.oscEcc` | `KAM/Frozen/Planetary/StrongAMD/Defs/OscEcc.lean` | `planetary.d59.oscEcc.v1` | definition | — |
| 22 | `KAM.Planetary.StrongAMD.oscPeri` | `KAM/Frozen/Planetary/StrongAMD/Defs/OscPeri.lean` | `planetary.d59.oscPeri.v1` | definition | — |
| 23 | `KAM.Planetary.StrongAMD.oscApo` | `KAM/Frozen/Planetary/StrongAMD/Defs/OscApo.lean` | `planetary.d59.oscApo.v1` | definition | — |
| 24 | `KAM.Planetary.StrongAMD.SourceCanonicalPhase` | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceCanonicalPhase.lean` | `planetary.d59.SourceCanonicalPhase.v1` | definition | — |
| 25 | `KAM.Planetary.StrongAMD.SourceOsculatingPhase` | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOsculatingPhase.lean` | `planetary.d59.SourceOsculatingPhase.v1` | definition | — |
| 26 | `KAM.Planetary.StrongAMD.sourceStrongAMD` | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceStrongAMD.lean` | `planetary.d59.sourceStrongAMD.v1` | definition | — |
| 27 | `KAM.Planetary.StrongAMD.sourceKeplerPeri` | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceKeplerPeri.lean` | `planetary.d59.sourceKeplerPeri.v1` | definition | — |
| 28 | `KAM.Planetary.StrongAMD.sourceKeplerApo` | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceKeplerApo.lean` | `planetary.d59.sourceKeplerApo.v1` | definition | — |
| 29 | `KAM.Planetary.StrongAMD.sourceOscVelocity` | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscVelocity.lean` | `planetary.d59.sourceOscVelocity.v1` | definition | — |
| 30 | `KAM.Planetary.StrongAMD.sourceOscParam` | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscParam.lean` | `planetary.d59.sourceOscParam.v1` | definition | — |
| 31 | `KAM.Planetary.StrongAMD.sourceOscEnergy` | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscEnergy.lean` | `planetary.d59.sourceOscEnergy.v1` | definition | — |
| 32 | `KAM.Planetary.StrongAMD.sourceOscAxis` | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscAxis.lean` | `planetary.d59.sourceOscAxis.v1` | definition | — |
| 33 | `KAM.Planetary.StrongAMD.sourceOscEccVector` | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscEccVector.lean` | `planetary.d59.sourceOscEccVector.v1` | definition | — |
| 34 | `KAM.Planetary.StrongAMD.sourceOscEcc` | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscEcc.lean` | `planetary.d59.sourceOscEcc.v1` | definition | — |
| 35 | `KAM.Planetary.StrongAMD.sourceOscPeri` | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscPeri.lean` | `planetary.d59.sourceOscPeri.v1` | definition | — |
| 36 | `KAM.Planetary.StrongAMD.sourceOscApo` | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscApo.lean` | `planetary.d59.sourceOscApo.v1` | definition | — |
| 37 | `KAM.Planetary.Spatial.spaceDot` | `KAM/Frozen/Planetary/Spatial/Defs/SpaceDot.lean` | `planetary.d59.spaceDot.v1` | definition | — |
| 38 | `KAM.Planetary.Spatial.spaceSq` | `KAM/Frozen/Planetary/Spatial/Defs/SpaceSq.lean` | `planetary.d59.spaceSq.v1` | definition | — |
| 39 | `KAM.Planetary.Spatial.spaceLength` | `KAM/Frozen/Planetary/Spatial/Defs/SpaceLength.lean` | `planetary.d59.spaceLength.v1` | definition | — |
| 40 | `KAM.Planetary.Spatial.spaceCross` | `KAM/Frozen/Planetary/Spatial/Defs/SpaceCross.lean` | `planetary.d59.spaceCross.v1` | definition | — |
| 41 | `KAM.Planetary.Spatial.bodyVector3` | `KAM/Frozen/Planetary/Spatial/Defs/BodyVector3.lean` | `planetary.d59.bodyVector3.v1` | definition | — |
| 42 | `KAM.Planetary.Spatial.planetAngularMomentum3` | `KAM/Frozen/Planetary/Spatial/Defs/PlanetAngularMomentum3.lean` | `planetary.d59.planetAngularMomentum3.v1` | definition | — |
| 43 | `KAM.Planetary.Spatial.angularMomentum3` | `KAM/Frozen/Planetary/Spatial/Defs/AngularMomentum3.lean` | `planetary.d59.angularMomentum3.v1` | definition | — |
| 44 | `KAM.Planetary.Spatial.spatialHamiltonian` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialHamiltonian.lean` | `planetary.d59.spatialHamiltonian.v1` | definition | — |
| 45 | `KAM.Planetary.Spatial.SpatialNoCollision` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialNoCollision.lean` | `planetary.d59.SpatialNoCollision.v1` | definition | — |
| 46 | `KAM.Planetary.Spatial.IsSpatialMovingSolutionOn` | `KAM/Frozen/Planetary/Spatial/Defs/IsSpatialMovingSolutionOn.lean` | `planetary.d59.IsSpatialMovingSolutionOn.v1` | definition | — |
| 47 | `KAM.Planetary.Spatial.SpatialMovingUniqueOn` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialMovingUniqueOn.lean` | `planetary.d59.SpatialMovingUniqueOn.v1` | definition | — |
| 48 | `KAM.Planetary.Spatial.spatialBarycentricPositions` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialBarycentricPositions.lean` | `planetary.d59.spatialBarycentricPositions.v1` | definition | — |
| 49 | `KAM.Planetary.Spatial.spatialBarycentricVelocities` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialBarycentricVelocities.lean` | `planetary.d59.spatialBarycentricVelocities.v1` | definition | — |
| 50 | `KAM.Planetary.Spatial.spatialMasses` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialMasses.lean` | `planetary.d59.spatialMasses.v1` | definition | — |
| 51 | `KAM.Planetary.Spatial.IsSpatialNewtonSolutionOn` | `KAM/Frozen/Planetary/Spatial/Defs/IsSpatialNewtonSolutionOn.lean` | `planetary.d59.IsSpatialNewtonSolutionOn.v1` | definition | — |
| 52 | `KAM.Planetary.Spatial.spatialKeplerEnergy` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerEnergy.lean` | `planetary.d59.spatialKeplerEnergy.v1` | definition | — |
| 53 | `KAM.Planetary.Spatial.spatialKeplerAxis` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerAxis.lean` | `planetary.d59.spatialKeplerAxis.v1` | definition | — |
| 54 | `KAM.Planetary.Spatial.spatialKeplerAction` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerAction.lean` | `planetary.d59.spatialKeplerAction.v1` | definition | — |
| 55 | `KAM.Planetary.Spatial.spatialKeplerEccVector` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerEccVector.lean` | `planetary.d59.spatialKeplerEccVector.v1` | definition | — |
| 56 | `KAM.Planetary.Spatial.SpatialNegativeEnergy` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialNegativeEnergy.lean` | `planetary.d59.SpatialNegativeEnergy.v1` | definition | — |
| 57 | `KAM.Planetary.Spatial.SpatialElliptic` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialElliptic.lean` | `planetary.d59.SpatialElliptic.v1` | definition | — |
| 58 | `KAM.Planetary.Spatial.spatialKeplerPeri` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerPeri.lean` | `planetary.d59.spatialKeplerPeri.v1` | definition | — |
| 59 | `KAM.Planetary.Spatial.spatialKeplerApo` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerApo.lean` | `planetary.d59.spatialKeplerApo.v1` | definition | — |
| 60 | `KAM.Planetary.Spatial.spatialOscVelocity` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscVelocity.lean` | `planetary.d59.spatialOscVelocity.v1` | definition | — |
| 61 | `KAM.Planetary.Spatial.spatialOscParam` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscParam.lean` | `planetary.d59.spatialOscParam.v1` | definition | — |
| 62 | `KAM.Planetary.Spatial.spatialOscEnergy` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEnergy.lean` | `planetary.d59.spatialOscEnergy.v1` | definition | — |
| 63 | `KAM.Planetary.Spatial.spatialOscAxis` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscAxis.lean` | `planetary.d59.spatialOscAxis.v1` | definition | — |
| 64 | `KAM.Planetary.Spatial.spatialOscEccVector` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEccVector.lean` | `planetary.d59.spatialOscEccVector.v1` | definition | — |
| 65 | `KAM.Planetary.Spatial.spatialOscEcc` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEcc.lean` | `planetary.d59.spatialOscEcc.v1` | definition | — |
| 66 | `KAM.Planetary.Spatial.spatialOscPeri` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscPeri.lean` | `planetary.d59.spatialOscPeri.v1` | definition | — |
| 67 | `KAM.Planetary.Spatial.spatialOscApo` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscApo.lean` | `planetary.d59.spatialOscApo.v1` | definition | — |
| 68 | `KAM.Planetary.Spatial.SpatialOscPhase` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscPhase.lean` | `planetary.d59.SpatialOscPhase.v1` | definition | — |
| 69 | `KAM.Planetary.Spatial.SpatialSourceCanonicalPhase` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceCanonicalPhase.lean` | `planetary.d59.SpatialSourceCanonicalPhase.v1` | definition | — |
| 70 | `KAM.Planetary.Spatial.SpatialSourceOsculatingPhase` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOsculatingPhase.lean` | `planetary.d59.SpatialSourceOsculatingPhase.v1` | definition | — |
| 71 | `KAM.Planetary.Spatial.spatialSourceKeplerAxis` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerAxis.lean` | `planetary.d59.spatialSourceKeplerAxis.v1` | definition | — |
| 72 | `KAM.Planetary.Spatial.spatialSourceKeplerAction` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerAction.lean` | `planetary.d59.spatialSourceKeplerAction.v1` | definition | — |
| 73 | `KAM.Planetary.Spatial.spatialSourceKeplerEccVector` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerEccVector.lean` | `planetary.d59.spatialSourceKeplerEccVector.v1` | definition | — |
| 74 | `KAM.Planetary.Spatial.spatialSourceKeplerEcc` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerEcc.lean` | `planetary.d59.spatialSourceKeplerEcc.v1` | definition | — |
| 75 | `KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourcePlanetAngularMomentum.lean` | `planetary.d59.spatialSourcePlanetAngularMomentum.v1` | definition | — |
| 76 | `KAM.Planetary.Spatial.spatialSourceAngularMomentum` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceAngularMomentum.lean` | `planetary.d59.spatialSourceAngularMomentum.v1` | definition | — |
| 77 | `KAM.Planetary.Spatial.spatialSourceStrongAMD` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceStrongAMD.lean` | `planetary.d59.spatialSourceStrongAMD.v1` | definition | — |
| 78 | `KAM.Planetary.Spatial.spatialSourceKeplerPeri` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerPeri.lean` | `planetary.d59.spatialSourceKeplerPeri.v1` | definition | — |
| 79 | `KAM.Planetary.Spatial.spatialSourceKeplerApo` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerApo.lean` | `planetary.d59.spatialSourceKeplerApo.v1` | definition | — |
| 80 | `KAM.Planetary.Spatial.spatialSourceOscVelocity` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscVelocity.lean` | `planetary.d59.spatialSourceOscVelocity.v1` | definition | — |
| 81 | `KAM.Planetary.Spatial.spatialSourceOscParam` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscParam.lean` | `planetary.d59.spatialSourceOscParam.v1` | definition | — |
| 82 | `KAM.Planetary.Spatial.spatialSourceOscEnergy` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEnergy.lean` | `planetary.d59.spatialSourceOscEnergy.v1` | definition | — |
| 83 | `KAM.Planetary.Spatial.spatialSourceOscAxis` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscAxis.lean` | `planetary.d59.spatialSourceOscAxis.v1` | definition | — |
| 84 | `KAM.Planetary.Spatial.spatialSourceOscEccVector` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEccVector.lean` | `planetary.d59.spatialSourceOscEccVector.v1` | definition | — |
| 85 | `KAM.Planetary.Spatial.spatialSourceOscEcc` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEcc.lean` | `planetary.d59.spatialSourceOscEcc.v1` | definition | — |
| 86 | `KAM.Planetary.Spatial.spatialSourceOscPeri` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscPeri.lean` | `planetary.d59.spatialSourceOscPeri.v1` | definition | — |
| 87 | `KAM.Planetary.Spatial.spatialSourceOscApo` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscApo.lean` | `planetary.d59.spatialSourceOscApo.v1` | definition | — |
| 88 | `KAM.Planetary.Spatial.spatialSourceBarycentricPositions` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceBarycentricPositions.lean` | `planetary.d59.spatialSourceBarycentricPositions.v1` | definition | — |
| 89 | `KAM.Planetary.Spatial.spatialSourceBarycentricVelocities` | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceBarycentricVelocities.lean` | `planetary.d59.spatialSourceBarycentricVelocities.v1` | definition | — |
| 90 | `KAM.Planetary.StrongAMD.orderedPairThreshold_isLeast` | `KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedPairThresholdIsLeast.lean` | `planetary.d59.orderedPairThreshold_isLeast.v1` | theorem | `KAM.Provider.Planetary.StrongAMD.OrderedPairThresholdIsLeast` (moved proof) |
| 91 | `KAM.Planetary.StrongAMD.orderedPairThreshold_existsUnique_value` | `KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedPairThresholdExistsUniqueValue.lean` | `planetary.d59.orderedPairThreshold_existsUnique_value.v1` | theorem | `KAM.Provider.Planetary.StrongAMD.OrderedPairThresholdExistsUniqueValue` (moved proof) |
| 92 | `KAM.Planetary.StrongAMD.orderedCrossThreshold_isLeast` | `KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedCrossThresholdIsLeast.lean` | `planetary.d59.orderedCrossThreshold_isLeast.v1` | theorem | `KAM.Provider.Planetary.StrongAMD.OrderedCrossThresholdIsLeast` (moved proof) |
| 93 | `KAM.Planetary.StrongAMD.orderedStrongThreshold_isLeast` | `KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedStrongThresholdIsLeast.lean` | `planetary.d59.orderedStrongThreshold_isLeast.v1` | theorem | `KAM.Provider.Planetary.StrongAMD.OrderedStrongThresholdIsLeast` (moved proof) |
| 94 | `KAM.Planetary.StrongAMD.sourceStrongAMD_nonneg` | `KAM/Frozen/Planetary/StrongAMD/Theorems/SourceStrongAMDNonneg.lean` | `planetary.d59.sourceStrongAMD_nonneg.v1` | theorem | `KAM.Provider.Planetary.StrongAMD.SourceStrongAMDNonneg` (moved proof) |
| 95 | `KAM.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD` | `KAM/Frozen/Planetary/StrongAMD/Theorems/SumActionMulEccDeficitLeSourceStrongAMD.lean` | `planetary.d59.sum_action_mul_eccDeficit_le_sourceStrongAMD.v1` | theorem | `KAM.Provider.Planetary.StrongAMD.SumActionMulEccDeficitLeSourceStrongAMD` (moved proof) |
| 96 | `KAM.Planetary.StrongAMD.sourceKepler_axis_pos` | `KAM/Frozen/Planetary/StrongAMD/Theorems/SourceKeplerAxisPos.lean` | `planetary.d59.sourceKepler_axis_pos.v1` | theorem | `KAM.Provider.Planetary.StrongAMD.SourceKeplerAxisPos` (moved proof) |
| 97 | `KAM.Planetary.StrongAMD.sourceKepler_ecc_le_one` | `KAM/Frozen/Planetary/StrongAMD/Theorems/SourceKeplerEccLeOne.lean` | `planetary.d59.sourceKepler_ecc_le_one.v1` | theorem | `KAM.Provider.Planetary.StrongAMD.SourceKeplerEccLeOne` (moved proof) |
| 98 | `KAM.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength` | `KAM/Frozen/Planetary/StrongAMD/Theorems/SourceKeplerPeriLePlaneLength.lean` | `planetary.d59.sourceKeplerPeri_le_planeLength.v1` | theorem | `KAM.Provider.Planetary.StrongAMD.SourceKeplerPeriLePlaneLength` (moved proof) |
| 99 | `KAM.Planetary.StrongAMD.planeLength_le_sourceKeplerApo` | `KAM/Frozen/Planetary/StrongAMD/Theorems/PlaneLengthLeSourceKeplerApo.lean` | `planetary.d59.planeLength_le_sourceKeplerApo.v1` | theorem | `KAM.Provider.Planetary.StrongAMD.PlaneLengthLeSourceKeplerApo` (moved proof) |
| 100 | `KAM.Planetary.StrongAMD.sourceOscAxis_pos` | `KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscAxisPos.lean` | `planetary.d59.sourceOscAxis_pos.v1` | theorem | `KAM.Provider.Planetary.StrongAMD.SourceOscAxisPos` (moved proof) |
| 101 | `KAM.Planetary.StrongAMD.sourceOscPeri_pos` | `KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscPeriPos.lean` | `planetary.d59.sourceOscPeri_pos.v1` | theorem | `KAM.Provider.Planetary.StrongAMD.SourceOscPeriPos` (moved proof) |
| 102 | `KAM.Planetary.StrongAMD.sourceOscPeri_le_planeLength` | `KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscPeriLePlaneLength.lean` | `planetary.d59.sourceOscPeri_le_planeLength.v1` | theorem | `KAM.Provider.Planetary.StrongAMD.SourceOscPeriLePlaneLength` (moved proof) |
| 103 | `KAM.Planetary.StrongAMD.planeLength_le_sourceOscApo` | `KAM/Frozen/Planetary/StrongAMD/Theorems/PlaneLengthLeSourceOscApo.lean` | `planetary.d59.planeLength_le_sourceOscApo.v1` | theorem | `KAM.Provider.Planetary.StrongAMD.PlaneLengthLeSourceOscApo` (moved proof) |
| 104 | `KAM.Planetary.Spatial.spatialSourceKeplerAxis_pos` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerAxisPos.lean` | `planetary.d59.spatialSourceKeplerAxis_pos.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceKeplerAxisPos` (moved proof) |
| 105 | `KAM.Planetary.Spatial.spatialSourceKeplerAction_pos` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerActionPos.lean` | `planetary.d59.spatialSourceKeplerAction_pos.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceKeplerActionPos` (moved proof) |
| 106 | `KAM.Planetary.Spatial.spatialSourceKeplerAction_sq` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerActionSq.lean` | `planetary.d59.spatialSourceKeplerAction_sq.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceKeplerActionSq` (moved proof) |
| 107 | `KAM.Planetary.Spatial.spatialSourceKeplerEcc_sq` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccSq.lean` | `planetary.d59.spatialSourceKeplerEcc_sq.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceKeplerEccSq` (moved proof) |
| 108 | `KAM.Planetary.Spatial.spatialSourceKeplerEcc_nonneg` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccNonneg.lean` | `planetary.d59.spatialSourceKeplerEcc_nonneg.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceKeplerEccNonneg` (moved proof) |
| 109 | `KAM.Planetary.Spatial.spatialSourceKeplerEcc_le_one` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccLeOne.lean` | `planetary.d59.spatialSourceKeplerEcc_le_one.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceKeplerEccLeOne` (moved proof) |
| 110 | `KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLength.lean` | `planetary.d59.spatialSourcePlanetAngularMomentum_length.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourcePlanetAngularMomentumLength` (moved proof) |
| 111 | `KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLengthLe.lean` | `planetary.d59.spatialSourcePlanetAngularMomentum_length_le.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourcePlanetAngularMomentumLengthLe` (moved proof) |
| 112 | `KAM.Planetary.Spatial.spatialSourceKeplerPeri_le_length` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerPeriLeLength.lean` | `planetary.d59.spatialSourceKeplerPeri_le_length.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceKeplerPeriLeLength` (moved proof) |
| 113 | `KAM.Planetary.Spatial.spatialSourceKeplerApo_ge_length` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerApoGeLength.lean` | `planetary.d59.spatialSourceKeplerApo_ge_length.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceKeplerApoGeLength` (moved proof) |
| 114 | `KAM.Planetary.Spatial.spatialSourceStrongAMD_nonneg` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceStrongAMDNonneg.lean` | `planetary.d59.spatialSourceStrongAMD_nonneg.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceStrongAMDNonneg` (moved proof) |
| 115 | `KAM.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceActionMulEccDeficitLe.lean` | `planetary.d59.spatialSourceAction_mul_eccDeficit_le.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceActionMulEccDeficitLe` (moved proof) |
| 116 | `KAM.Planetary.Spatial.spatialSourceOscParam_pos` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscParamPos.lean` | `planetary.d59.spatialSourceOscParam_pos.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceOscParamPos` (moved proof) |
| 117 | `KAM.Planetary.Spatial.spatialSourceOscEnergy_neg` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEnergyNeg.lean` | `planetary.d59.spatialSourceOscEnergy_neg.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceOscEnergyNeg` (moved proof) |
| 118 | `KAM.Planetary.Spatial.spatialSourceOscEcc_lt_one` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEccLtOne.lean` | `planetary.d59.spatialSourceOscEcc_lt_one.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceOscEccLtOne` (moved proof) |
| 119 | `KAM.Planetary.Spatial.spatialSourceOscEcc_nonneg` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEccNonneg.lean` | `planetary.d59.spatialSourceOscEcc_nonneg.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceOscEccNonneg` (moved proof) |
| 120 | `KAM.Planetary.Spatial.spatialSourceOscAxis_pos` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscAxisPos.lean` | `planetary.d59.spatialSourceOscAxis_pos.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceOscAxisPos` (moved proof) |
| 121 | `KAM.Planetary.Spatial.spatialSourceOscPeri_pos` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscPeriPos.lean` | `planetary.d59.spatialSourceOscPeri_pos.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceOscPeriPos` (moved proof) |
| 122 | `KAM.Planetary.Spatial.spatialSourceOscPeri_le_length` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscPeriLeLength.lean` | `planetary.d59.spatialSourceOscPeri_le_length.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceOscPeriLeLength` (moved proof) |
| 123 | `KAM.Planetary.Spatial.spatialSourceOscApo_ge_length` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscApoGeLength.lean` | `planetary.d59.spatialSourceOscApo_ge_length.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialSourceOscApoGeLength` (moved proof) |
| 124 | `KAM.Planetary.StrongAMD.planar_strongAMD_barrier` | `KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDBarrier.lean` | `planetary.d59.planar_strongAMD_barrier.v1` | theorem | `KAM.Provider.Planetary.StrongAMD.PlanarStrongAMDBarrier` (staged one-liner) |
| 125 | `KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety` | `KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafety.lean` | `planetary.d59.planar_strongAMD_exponentialSafety.v1` | theorem | `KAM.Provider.Planetary.StrongAMD.PlanarStrongAMDExponentialSafety` (staged one-liner) |
| 126 | `KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger` | `KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyHalfInteger.lean` | `planetary.d59.planar_strongAMD_exponentialSafety_halfInteger.v1` | theorem | `KAM.Provider.Planetary.StrongAMD.PlanarStrongAMDExponentialSafetyHalfInteger` (staged one-liner) |
| 127 | `KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafety.lean` | `planetary.d59.spatial_strongAMD_exponentialSafety.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialStrongAMDExponentialSafety` (staged one-liner) |
| 128 | `KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyHalfInteger.lean` | `planetary.d59.spatial_strongAMD_exponentialSafety_halfInteger.v1` | theorem | `KAM.Provider.Planetary.Spatial.SpatialStrongAMDExponentialSafetyHalfInteger` (staged one-liner) |

## Checks

- Identity (`lp_identity_check.py --approved de343000:docs/tracks/LP/freeze/draft7 --date 2026-11-01 --decision D62`;
  full output in `docs/tracks/LP/freeze/identity-check.txt`): 128 files checked / ALL IDENTICAL. Only the two placeholders and
  the proof body differ from the approved texts.
- `scripts/check_frozen_anchors.py --root . --manifest manifest/frozen-anchors.json`: FROZEN-ANCHOR GUARD OK.
- Build: `/root/code/KAM-inp/.drafts/LP/lp_build_fast.sh /root/code/KAM-inp-lp-freeze KAM.Root.Planetary
  KAM.Root.Provider KAM.Root.Frozen`: "Build completed successfully (11090 jobs)", rc 0; 287 modules rebuilt (the
  284 of `replay-modules.txt` and 3 roots); no warning and no `sorry` in any new or changed file.
- ABI: `abi_hashes.py` on the 128 new entries, twice: identical. `abi_hashes.py . manifest/frozen-anchors.json
  --check`: ABI HASHES OK (305 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
- `lp_lint.sh`: exit 0 (check_lean_modules: PASS (4225 Lean files, 0 comparator configurations); FROZEN-ANCHOR GUARD OK; ABI HASHES OK (305 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))).
- Provider type probe and axioms (`lp_axioms.py --probe`, run with `lp_lean.sh`, then `--verify`): 39 anchors, 39 providers, 89 definitions / ALL OK.
  For each of the 39 anchors, `example : type_of% @X := @Pv` elaborates and the types of X and its provider are
  `Expr.eqv`. All 39 anchors and 39 providers depend on exactly `[propext, Classical.choice, Quot.sound]`, and all
  89 definitions on a subset of these.
- Kernel replay: per module, `systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env
  LEAN_NUM_THREADS=1 lake env leanchecker <Module>` behind the MemAvailable ≥ 8 GB gate, for the 284 modules of
  `docs/tracks/LP/freeze/replay-modules.txt` (128 frozen, 39 providers, 117 rebuilt LP modules). The result is in
  the handoff.

## Deviations

- **The 34 characterization providers are not f2fa9f88's one-liners.** Those apply the implementation lemmas,
  which the freeze must delete (same fully qualified names; §7 point 3). They carry the moved proofs instead,
  with the same statement text, and are Expr-equal to their anchors (probe). The 5 anchor providers are f2fa9f88's,
  byte for byte.
- No frozen text was changed beyond the two placeholders and the proof body.
