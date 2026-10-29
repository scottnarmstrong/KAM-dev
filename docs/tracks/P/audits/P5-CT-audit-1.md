# P5-CT independent package audit 1

Overall verdict: **FAIL for complete mapped-slice coverage (F1)**. The signed
`outputRepresentative` definition and `cell_transfer` theorem **PASS** their exact
contracts and proof checks. F1 is a missing intermediate graph conclusion, not an
incorrect measure theorem or an additional assumption. No frozen anchor is sealed
by this infrastructure package; in particular this is not a seal-readiness receipt
for frozen P-G.

Audited HEAD `ab1552432a9473cb683329c648d0477eda4d7100`, worktree
`/root/code/KAM-inp-p5ct`. The requested `git diff inp...HEAD` reports multiple merge
bases and chooses `0f347d6926a79e37d59d1e5fd044af61862721ae`; the other merge base is
`1005e6394f3da22fb5263f98658969aa2071587c`. The comparison adds six files (1,065
lines): the two audited CellTransfer modules and four Family dependency modules.
The full comparison was inspected, but only `CellTransfer.lean` and
`CellTransferTile.lean` receive implementation verdicts here. The handoff was
already untracked. No production file was edited.

Read: AGENTS.md, PLAN, DECISIONS, the supplied package-audit brief and handoff;
P45 design (especially node table 196–201, package row 506, proof plan 305–307,
consumer table 563), all four P45 design-audit histories for the relevant contracts;
shared `P45Signatures.lean:1186–1195`; track-P statement; P5 blueprint 266–275 and
its graph packet 1917–2105; frozen P-G and its phase/cylinder/cell/shift/torus-union
interfaces; Family, Chart, and the consumed P1 Liouville/angle-scaling/torus-union
interfaces. The revision-3 design audit approves these signed contracts; revision 4
changes the upstream extension agreement, not this cell-transfer signature.

## F1 — Missing sigma-compact chart-image conclusion in `ct-dec`

The assigned graph node `stepP:p5:ct-dec` explicitly concludes **“T is
sigma-compact”** (`docs/graph/P/packets/P-p5.nodes.md:1991`; blueprint
`blueprint-P/parts/p5-pg-assembly.tex:271`). Here

```lean
T = phi d r mu h ''
  (angleScale (2*Real.pi) '' outputRepresentative d r mu h B)
```

`CellTransfer.lean:231–252` proves the translate decomposition.
`CellTransfer.lean:267–271` proves sigma-compactness of the scaled representative
only as an argument to `measurableSet_of_isSigmaCompact`, then proves
`MeasurableSet T` using `measurableSet_chart_image`. Neither module establishes
`IsSigmaCompact T` locally or as an export. Borelness does not imply
sigma-compactness in general. The complete mapped-slice requirement therefore
fails, although the signed theorem intentionally needs only Borelness here.

Repair: add a distinctly named helper with the original `d r mu h hB hsub`
premises and conclusion `IsSigmaCompact T`, or prove it locally. A diagnostic
scratch proof of precisely that conclusion elaborated at default heartbeats:

```lean
  have hR := ct_sigmaCompact_inter_cell
    (ct_rawUnion_sigmaCompact d r mu h hB hsub)
  have hA := hR.image (ct_continuous_angleScale (2*Real.pi))
  obtain ⟨_, hchart, _, _⟩ := phi_chart d r mu h
  exact hA.image_of_continuousOn (hchart.1.continuousOn.mono
    ((image_mono inter_subset_left).trans (ct_scaled_subset d r mu h hsub)))
```

This diagnostic establishes that no extra premise or signature change is needed;
it does not supply the missing production declaration. No consumer failure of the
signed `cell_transfer` has been found. The coverage verdict would change after
this clause is supplied or an explicit graph-route ruling removes it.

## Node coverage

All names below are in `KAM.Planetary`.

| Node | Declarations / proof location | Verdict | Reason |
|---|---|---|---|
| `bpP:p5:cell-transfer` signed contract | `outputRepresentative`, `cell_transfer` | PASS | Exact signature and definition body; exact `(2*pi)^(a+b)` ENNReal equality, same B and admissibility premises. |
| Blueprint whole-torus clause | `kset` definition; audit probe | PASS | Membership supplies J in B and theta; the entire range for that same J is included by definition. No new source premise needed. |
| `stepP:p5:ct-cell` | `ct_spec`, `ctCellMap`, `ct_rawUnion_period`, `ct_rawUnion_eq`, `ct_rawUnion_sigmaCompact`, `ct_sigmaCompact_inter_cell`; final hR0 | PASS | Lipschitz parameter-cell image is sigma-compact, countable saturation gives raw union, and compact intersections give output-cell representative. |
| `stepP:p5:ct-dec` | `ct_scaled_subset`, `ct_kset_eq`, `ct_phi_shift`, `ct_kset_cover`, `ct_kset_measurable`, `ct_kset_subset_cylinder` | FAIL, F1 | Correct cover, location and Borelness; missing `IsSigmaCompact T` clause. |
| `stepP:p5:ct-disj` | `ct_cell_shift_unique`, `ct_translate_inj`; final hinj and disjointness argument | PASS | Q2, nonzero angle scaling, half-open unit-cell uniqueness; yields both image injectivity and distinct fast translates. |
| `stepP:p5:ct-count` | Tile helpers and `volume_fastTranslates_inter_fastCell`; final hcell | PASS | Countable additivity on disjoint measurable translates and translated half-open slabs; no finite-volume premise or physical-cell preservation. |
| `stepP:p5:ct-liou` | `cell_transfer:283–285`, P1 `chart_measure_image`, `volume_angleScale_image` | PASS | Chart constant 1, established injectivity, positive 2*pi; exactly one angle scaling and exponent a+b. |

The signed conclusion omits an explicit whole-torus conjunct, as approved in the
design. The definition of `kset` retains it, and the scratch probe verifies the
literal conclusion. Thus the later lower/strictness measure uses have the exact
cell identity, and the `main`/frozen `IsCylinderKolmogorovSet` assembly can recover
the whole-range inclusion with the same J witness. Later consumer modules are not
implemented in this checkout; no assertion of their proof closure is made.

## Every public declaration

| Declaration | Verdict | Statement / classification |
|---|---|---|
| `outputRepresentative` | PASS | Signed definition: raw output union intersected with its output-angle cell. |
| `ct_spec` | PASS | Projects the proved family witness specification, not an assumed conclusion. |
| `ctCellMap` | PASS | Total `(J,theta) ↦ raw J theta`, with canonical phase output. |
| `ct_rawUnion_period` | PASS | Equality under every integer angle shift for B subset D0. |
| `ct_rawUnion_eq` | PASS | Exact lattice saturation of parameter-cell image. |
| `ct_rawUnion_sigmaCompact` | PASS | Sigma-compact raw union from sigma-compact B. |
| `ct_sigmaCompact_inter_cell` | PASS | Generic sigma-compact R intersected with the half-open output cell. |
| `ct_continuous_angleScale` | PASS | Global continuity, all real c; stronger than the positive-c use. |
| `ct_scaled_subset` | PASS | Scaled raw union lies in chart domain. |
| `ct_kset_eq` | PASS | Exact physical-image identity, all B without extra source restrictions. |
| `ct_kset_subset_cylinder` | PASS | Location for B subset D0. |
| `ct_kset_measurable` | PASS | Borel physical union; does not claim sigma-compact T. |
| `ct_angleShift_add` | PASS | Additive lattice arithmetic. |
| `ct_cell_shift_unique` | PASS | Equal translates of unit-cell points imply equality of points and shifts. |
| `ct_fastShift_zero` | PASS | Zero fast lattice shift. |
| `ct_blockFast_append` | PASS | Fast projection of appended zero slow block. |
| `ct_phi_shift` | PASS | Chart equivariance on raw union, arbitrary full integer shift. |
| `ct_translate_inj` | PASS | Equality of translated chart images implies equal representative and fast shift. |
| `ct_kset_cover` | PASS | Exact cover; its name states only the cover, not the full ct-dec node. |
| `cell_transfer` | PASS | Signed conjunction, no extra premises or weakened factors. |
| `ctFastCell` | PASS | Total set definition: fast positions in [0,2*pi), other coordinates unrestricted. |
| `measurableSet_ctFastCell` | PASS | Borel finite intersection of coordinate half-open slabs. |
| `exists_fastShift_mem_fastCell` | PASS | Floor construction, arbitrary phase point. Handoff spells the name differently; actual export checked. |
| `fastShift_unique` | PASS | Unique shift putting a fixed point in the fast cell. |
| `volume_fastTranslates_inter_fastCell` | PASS | Generic measurable E with disjoint translates; arbitrary volume including infinity. Its disjointness premise is proved in the application. |

There are exactly three new definitions, classified above; no new abbrev,
structure, fallback branch, or altered metric/measure instance. `ctCellMap` is
used on actions × parameter angles; it does not identify that parameter-cell
image with the output representative. All declarations remain in
`KAM.Planetary`, with no root declaration or harmful shadow. A repository-wide
short-name declaration scan found no duplicates for any of these 25 exports.

## Validation receipts

All Lean/Lake invocations were sequential within this audit, with
`LEAN_NUM_THREADS=1` and inherited/explicit `nice -n 5`. No budget overrides,
cache reset, library clean, package update, generated-root edit or frozen edit.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5ct KAM.Planetary.PGAssembly.CellTransferTile KAM.Planetary.PGAssembly.CellTransfer
```

Exit **0**. Gate: `[inp-gate] slot 2 acquired 21:11:25`.
Final output: `Build completed successfully (9377 jobs).`
This is the target dependency-graph job count, not a clean rebuild. Replayed
upstream linter warnings were emitted; no warning was attributed to either
audited CellTransfer file.

2. Fresh scratch probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5CTAudit.lean
```

Exit **0**. The probe copies the literal signed definition and theorem telescope
under fresh names; checks definition equality by `rfl`, elaborates
`by exact KAM.Planetary.cell_transfer d r mu h hB hsub`, and checks
`example : type_of% @signedTransfer := @KAM.Planetary.cell_transfer`.
It also proves the blueprint whole-range inclusion and the diagnostic F1 clause.
Independent textual comparison reports both signed declarations `EXACT TEXT MATCH: True`
(the theorem comparison excludes its proof body). No frozen/provider type or
seal-body probe applies: this package exports helpers, not a frozen provider.

All 22 theorem axiom outputs follow; only `ct_blockFast_append` omits
`Classical.choice` from the usual three axioms:

```text
'KAM.Planetary.ct_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ct_rawUnion_period' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ct_rawUnion_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ct_rawUnion_sigmaCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ct_sigmaCompact_inter_cell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ct_continuous_angleScale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ct_scaled_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ct_kset_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ct_kset_subset_cylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ct_kset_measurable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ct_angleShift_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ct_cell_shift_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ct_fastShift_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ct_blockFast_append' depends on axioms: [propext, Quot.sound]
'KAM.Planetary.ct_phi_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ct_translate_inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ct_kset_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.cell_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.measurableSet_ctFastCell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exists_fastShift_mem_fastCell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fastShift_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.volume_fastTranslates_inter_fastCell' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.CellTransfer KAM.Planetary.PGAssembly.CellTransferTile
```

Exit **0**. Exact output:

```text
replaying KAM.Planetary.PGAssembly.CellTransferTile
replaying KAM.Planetary.PGAssembly.CellTransfer
```

4. Source lint and guard:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely for the explicitly permitted stale generated-root exception.
Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (943 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The module-system check, frozen-anchor guard and all 144 frozen ABI hashes pass.
The generated root was not regenerated.

5. Static and protected-path checks: `CellTransfer.lean` has **293** lines;
`CellTransferTile.lean` has **105**, not 104 as in the handoff. Both have maximum
Unicode line width **100**, module/header/import/docstring/public-section form,
and exposed definitions. No forbidden proof escape, resource override or
`EuclideanSpace` in the audited code. The 331-module local KAM import closure has
**no provider and no frozen theorem module**, hence no DRAFT_SORRY theorem import.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty;
`git diff --check inp...HEAD` exits **0**. The multiple-merge-base warning is
recorded above, not hidden by selecting a different diff.

## Errata, deviations and limits

No new suspected defect in a pinned paper or frozen declaration was found. F1 is
an implementation-coverage omission relative to the assigned graph/blueprint,
not source errata. Existing corrected output-cell reasoning (blueprint review
P5-04, closed in p5-review-2) is respected by the code.

Documentation correction: `CellTransfer.lean:18` says **“raw union with input
angles in the unit cell”**. These are output angles of the raw family, as the
actual definition at 36–38 and signed design require. This wording should be
corrected without changing the definition. The handoff also uses
`exists_fastShift_mem_ctFastCell`; the actual export is
`exists_fastShift_mem_fastCell` at Tile:41. Both are nonblocking documentation
notes.

No source change or graph-status change is authorized by this report. Validation
of the signed result does not establish complete campaign, frozen P-G, later
consumer or graph closure. Temporary Lean probe files were deleted after checks.
