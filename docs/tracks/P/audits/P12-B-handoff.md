# P12-B prover handoff (branch inp-p12b, 696f22e; contains inp-p12a (audited); offloaded package run by the main orchestrator; prover on claude-10)


## Files
- New: `KAM/Planetary/PlanarAssembly/Boxes.lean` (381 lines). No other file changed (KAM.lean untouched).

## Declarations (all in `KAM.Planetary.PlanarAssembly`, signatures verbatim from P1213Signatures.lean)
- `secular_radius`, `coupling_threshold` (defs), `radius_choices` (bpP:p12:data D8-D9, p12:quantifiers): explicit min arithmetic.
- `birkhoff_mono_radius` (stepP:p12:pg-h4): shrink delta to `min delta r`.
- `collar` (bpP:p12:collar, co-inc, co-meas): frontier of the box = pi Icc \ pi Ioo; collar ⊆ pi Ioo(l-t,u+t) \ Icc(l+t,u-t); volume by `measure_sdiff` and `Real.volume_pi_Ioo`/`volume_Icc_pi`; exact difference 4t(L0+L1).
- `product_chart` (bpP:p7:product-chart (b), joint signature): `kepler_h = -Σ κ²m³/(2 I²)`; analytic; gradient via `HasFDerivAt` sum; Hessian via local equality with the cube formula + `hasFDerivAt_pi`; decoupling via `keplerPart_poincareProd`.
- `fast_diffeo` (bpP:p12:fast-diffeo, fd-an/open/inv): image = product of open intervals `(c/u³, c/l³)`; inverse `(c/w)^(3⁻¹)` with `ContDiffAt.rpow_const_of_ne` (C¹ suffices for frozen predicate).
- `kepler_h` is NOT redeclared: it is imported from P12-A's `Geometry.lean` (identical to the signature).

## Checks
- `scripts/lint_sources.sh`: only failure is pre-existing "KAM.lean is out of date" / DRAFT-import guard in generated KAM.lean (not touched, per rule 10); `check_lean_modules: PASS`, `ABI HASHES OK`. Nothing from Boxes.lean flagged.
- Gate build `inp_lake_build.sh /root/code/KAM-inp-p12b KAM.Planetary.PlanarAssembly.Boxes`: `Build completed successfully (9116 jobs)`, no warnings from Boxes.lean, no sorry.
- `#print axioms` of collar, product_chart, fast_diffeo, radius_choices, birkhoff_mono_radius: `[propext, Classical.choice, Quot.sound]`.

## Uncertainties / errata / deviations
- None. No signature changed; `hn` in `product_chart` and `hc` in `radius_choices` are unused (kept verbatim; discharged by `have _ := ...`). No maxHeartbeats, no EuclideanSpace.
- Private helpers (`kepEnergy`, `fast_assemble`, `kepler_h_eq`, `hProd_eq`, cube-root lemmas) are file-local. KAM.lean needs regeneration (orchestrator) to include the new module.

AUDIT FOCUS (design docs/tracks/P/design/P1213-LEAN-DESIGN.md row P12-B, node table and design note 8 on product_chart; audits DESIGN-P1213-design-audit-{1,2}.md; signatures .drafts/design/P1213Signatures.lean): (1) statements and definitions = signature file exactly (secular_radius, coupling_threshold, radius_choices, birkhoff_mono_radius, collar, product_chart, fast_diffeo); product_chart is the joint exact signature for the P7 product-chart analyticity/derivative claims (note 8): check it is complete and not weakened; (2) proofs sound; the unused hypotheses hn (product_chart) and hc (radius_choices) are kept verbatim from the signature: confirm the signature intends them and that nothing is vacuous; no added premises; (3) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/PlanarAssembly/Boxes.lean.
