# PP1-3 prover handoff (branch inp-pp13, cdf9b35; off inp with inp-design-p1; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/Hamiltonian/TorusUnion.lean` (281 lines). KAM.lean not touched.

**Nodes proved** (signatures verbatim from PPart1Signatures.lean section G, `bpP:p1:torus-union`):
`unitCube` (def), `torus_union`, `torus_union_measurableSet_of_sigmaCompact` (B1),
`torus_union_measurableSet_of_injOn` (B2), `torus_union_lower`, `torus_union_saturation`,
`nullMeasurableSet_torus_union_saturation`.

**Extra helpers** (new names): `measurableSet_unitCube`, `volume_unitCube`, `volume_prod_unitCube`,
`nullMeasurableSet_prod_unitCube`, `isSigmaCompact_unitCube`, `isSigmaCompact_prod_unitCube`,
`measurableSet_of_isSigmaCompact`, `lipschitzOnWith_of_bound`, `exists_isSigmaCompact_subset_null`,
`nullMeasurableSet_image_of_lipschitzOn`.

**Approach:** upper bound is `KAM.lip_image_prod` directly on `E ×ˢ unitCube d` (valid for any sign of
`Λ`, so B3 needs no case split and McShane is NOT needed; `KAM.Measure.McShane` is not imported, a
deviation from the design's import list only). Null measurability: `S = E × cube` null measurable ⇒
measurable `t ⊆ S` a.e. equal; `t` = σ-compact `B` + null (inner regularity, `exists_isCompact_sdiff_lt`
on `t ∩ closedBall n`); `F '' B` σ-compact hence Borel, `F '' (S \ B)` null by `lip_image_prod`. B1: σ-compact
product image. B2: `MeasurableSet.image_of_continuousOn_injOn` (Lipschitz ⇒ continuous on S).
Lower: `lip_image_prod` applied to `Function.invFunOn F S` (Lipschitz `lam⁻¹` on the image); iff's follow.
Saturation: `ϑ = fract ϑ + ⌊ϑ⌋`; measurability: countable union of translates (preimage under translation).
Haar instance of `volume` on `Phase d` is supplied locally by `Measure.prod.instIsAddHaarMeasure _ _`
(Decision 10); `isAddHaarMeasure_volume_phase` (Liouville package) is not imported.

**Checks:** gate build `KAM.Planetary.Hamiltonian.TorusUnion`: success, no warnings, no sorry.
`#print axioms` of all six theorems: [propext, Classical.choice, Quot.sound].
`scripts/lint_sources.sh`: check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK; only complaint is KAM.lean out of date (generated, not mine to edit).

**Uncertainties / design signals:** none; no heartbeat issues. **Errata:** none. **Deviations:** McShane import dropped (unneeded).

AUDIT FOCUS (design docs/tracks/P/design/PART1-LEAN-DESIGN.md row P1-3 (TorusUnion) and proof plan; its audit DESIGN-P1-design-audit-1.md; blueprint-P p1 torus-union): (1) statements = design signatures and blueprint (measure of a union of tori / lattice-torus union, with the sign issue B3 handled as the design states); (2) proofs sound (measurability, Fubini); (3) hygiene (lint incl. 100-char lines). Audit ONLY the PP1-3 module(s) (KAM/Planetary/Hamiltonian/TorusUnion*).
