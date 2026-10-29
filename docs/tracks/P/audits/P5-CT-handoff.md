# P5-CT prover handoff (branch inp-p5ct, ab155243; offloaded package run by the main orchestrator)


## Files
- `KAM/Planetary/PGAssembly/CellTransfer.lean` (293 lines): signed `outputRepresentative`, `cell_transfer` (verbatim),
  helpers `ct_*`, `ctCellMap`.
- `KAM/Planetary/PGAssembly/CellTransferTile.lean` (104 lines): `ctFastCell`, `measurableSet_ctFastCell`,
  `exists_fastShift_mem_ctFastCell`, `fastShift_unique`, `volume_fastTranslates_inter_fastCell`.
- Not edited: KAM.lean (it is flagged out of date by lint, as expected; orchestrator regenerates).

## Nodes
- `bpP:p5:cell-transfer` -> `outputRepresentative`, `cell_transfer`.
- `ct-cell` (sigma-compactness) -> `ct_rawUnion_eq`, `ct_rawUnion_sigmaCompact`, `ct_sigmaCompact_inter_cell`
  (Lipschitz cell image + `torus_union_saturation` + F-sigma cell).
- `ct-dec` -> `ct_kset_eq`, `ct_phi_shift`, `ct_kset_cover` (kset = union of fast translates of phi(S(outputRep))).
- `ct-disj` -> `ct_cell_shift_unique`, `ct_translate_inj` (phi injective mod fast lattice via `phi_chart` Q2).
- `ct-count` -> `volume_fastTranslates_inter_fastCell` (tiling by the fast cell).
- `ct-liou` -> final step of `cell_transfer`: P1 `chart_measure_image` (c = 1, injective) and `volume_angleScale_image`.
- Borel/location parts: `ct_kset_measurable` (P1 `measurableSet_chart_image`), `ct_kset_subset_cylinder` (`location`).

## Approach
R = rawUnion B is shift-invariant (periodicity) and sigma-compact; A = S_{2pi} R lies in phiDomain (location).
kset = phi(A) is Borel by P1 Liouville. With E = phi(S(R ∩ unit cell)), kset = ⋃_k (E + fastShift k) with pairwise
disjoint translates and phi injective on S(R0); cutting by the fast cell gives vol E = (2pi)^(a+b) vol R0.
No hypothesis beyond the signed ones (hB, hsub).

## Checks
- `inp_lake_build.sh ... CellTransferTile CellTransfer`: built, no warnings/sorry in my files.
- `sh scripts/lint_sources.sh`: only "KAM.lean is out of date" (expected); modules PASS, FROZEN-ANCHOR GUARD OK, ABI OK.
- Lines <= 100 cols; no maxHeartbeats/EuclideanSpace/sorry.
- `#print axioms KAM.Planetary.cell_transfer`: [propext, Classical.choice, Quot.sound].

## Uncertainties / errata / deviations
None. No suspected source defects; signatures unchanged. Public helper short names are `ct`-prefixed;
a private `measurableSet_fastCell` exists in PlanarAssembly, so mine is named `ctFastCell`-based.
No design signals (everything elaborates at default heartbeats, each file < 5 s of warm elaboration).

AUDIT FOCUS: design docs/tracks/P/design/P45-LEAN-DESIGN.md row P5-CT (cell_transfer, outputRepresentative; P1 chart_measure_image, volume_angleScale_image, torus_union*) and its node table; P45 design audits; signatures /root/code/KAM-inp/.drafts/design/P45Signatures.lean. Audit ONLY KAM/Planetary/PGAssembly/CellTransfer*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
