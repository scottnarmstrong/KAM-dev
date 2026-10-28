# P5-CT independent package audit 2 (delta)

Overall verdict: **PASS WITH NOTES** for P5-CT; round-1 **F1 CLOSED**.
The signed exports PASS and the mapped slice is complete relative to the
round-1 coverage audit plus this verified delta. This infrastructure package
seals no frozen anchor and is not a seal-readiness verdict for frozen P-G.

Audited HEAD `409e318648eddfcd301ae728eaa0c7976662d45c`, baseline
`c76fa593`, worktree `/root/code/KAM-inp-p5ct`. Scope: only
`KAM/Planetary/PGAssembly/CellTransfer*.lean`; round-1 report is the baseline
for unchanged declarations. The user's explicit report destination overrides
the generic brief's MAIN-worktree destination. No production edits.

Read: AGENTS, PLAN, DECISIONS, package brief, handoff/AUDIT FOCUS, audit 1,
P45 design node table 196–201, P5 blueprint 266–275, graph packet 1982–2002,
signed declarations in shared P45Signatures 1186–1195, track-P statement,
P-G anchor, PGData/admissible/pgD0 and chart interfaces. Applied the
lean-statement-audit method to the added helper; no provider/frozen seal
is part of this package.

## Delta and F1

`git diff c76fa593..HEAD` contains exactly **13 insertions, 0 deletions**, in
CellTransfer only. Removing the new docstring/theorem block reproduces the
baseline file **byte-for-byte**. The block is inserted at 254–266 before the
unchanged signed theorem; “appends” means adds one lemma, not appends after
all preexisting declarations. Tile is unchanged.

The new export `KAM.Planetary.ct_chartImage_sigmaCompact` (257–265) states:

```lean
IsSigmaCompact
  (phi d r mu h '' (angleScale (2*Real.pi) '' outputRepresentative d r mu h B))
```

This is literally the chart image T from blueprint-P/parts/p5-pg-assembly.tex:271
and docs/graph/P/packets/P-p5.nodes.md:1991: **“T is sigma-compact”**.
It is neither merely Borelness nor sigma-compactness of the pre-chart image.
The original `d r mu h hB hsub` premises are preserved, including implicit B.
The proof obtains sigma-compactness of the output-cell intersection, takes its
continuous angle-scaling image, extracts analytic (hence continuous) chart
regularity from `phi_chart`, and restricts it using the proved
`ct_scaled_subset`. No continuity, domain containment, chart-image regularity,
or other hard step becomes an input premise. F1 is resolved at source level.

| Binder/input | Class | Source / justification |
|---|---|---|
| implicit a | TYPING | Fin a fast carrier, unchanged signed telescope |
| implicit b | TYPING | Fin b slow carrier, unchanged signed telescope |
| d : PGData a b | STANDING | Same standing data as signed cell_transfer; PG/Setting:46–80 |
| r : ℝ | TYPING | Source radius parameter |
| mu : ℝ | TYPING | Source perturbation parameter |
| h : admissible d (pgRstar d) r mu | STANDING | Parameters:71–72: positive r, r below pgRstar, positive mu, mu below mu0 and literal smallness bound |
| implicit B : Set (Fin (a+b) → ℝ) | TYPING | Source action subset carrier |
| hB : IsSigmaCompact B | SOURCE | Blueprint p5:267,271; graph quantifier at 1990 |
| hsub : B ⊆ pgD0 d r mu | SOURCE | Blueprint p5:267, B subset D0 |

Top-level counts: TYPING 5, STANDING 2, SOURCE 2, RULED 0, EXCESS 0.
The two standing bundles are unchanged from audit 1. Reinspection of PGData
finds only the frozen geometry, positivity, analyticity, periodicity, fast
frequency diffeomorphism, secular Birkhoff, torsion and symmetry premises.
Admissible expands to the five scalar inequalities listed above; neither bundle
contains a sigma-compactness/chart-image conclusion. No delta in nested inputs.

## Coverage and signed contracts

| Node / declaration | Verdict | Evidence |
|---|---|---|
| bpP:p5:cell-transfer / outputRepresentative, cell_transfer | PASS | Exact text comparison against shared signatures; fresh definition rfl and signed theorem type/application probes |
| stepP:p5:ct-cell | PASS, unchanged | ct_rawUnion_sigmaCompact, ct_sigmaCompact_inter_cell; baseline bytes retained |
| stepP:p5:ct-dec / ct_chartImage_sigmaCompact | PASS, F1 closed | Literal IsSigmaCompact T; fresh exact-premise application probe |
| stepP:p5:ct-dec / ct_kset_cover, ct_kset_measurable, ct_kset_subset_cylinder | PASS, unchanged | Cover, Borelness and location from round 1 retained |
| stepP:p5:ct-disj | PASS, unchanged | ct_cell_shift_unique, ct_translate_inj; final injectivity/disjointness proof retained |
| stepP:p5:ct-count | PASS, unchanged | Tile helpers and volume_fastTranslates_inter_fastCell retained |
| stepP:p5:ct-liou | PASS, unchanged | Exact chart constant 1 and single (2*pi)^(a+b) factor retained |

Every old public declaration and its proof/body is unchanged; their individual
statement classifications and consumer analysis in audit 1 remain applicable.
Fresh comparisons report `Signed definition exact: True` and
`Signed theorem exact: True`. The unsigned new name describes its literal
conclusion and is unique across project declarations. All exports remain in
KAM.Planetary; no root shadow is introduced.

Definition classification: **no new definitions/abbrevs/structures** in this
delta. The existing three definitions remain literal: outputRepresentative is
rawUnion intersected with the output-angle cell; ctCellMap is the total raw-family
phase map; ctFastCell is the physical fast-angle slab. No fallback, metric,
normalization, choice or definition-body change.

## Validation receipts

All invocations below are sequential within this audit, with LEAN_NUM_THREADS=1
and nice -n 5. No heartbeat/recursion/synthesis overrides, clean rebuild,
package update, cache reset, generated-root edit or frozen edit.

1. Targeted build (exit **0**):

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5ct KAM.Planetary.PGAssembly.CellTransferTile KAM.Planetary.PGAssembly.CellTransfer
```

```text
[inp-gate] slot 2 acquired 21:47:35 for KAM.Planetary.PGAssembly.CellTransferTile KAM.Planetary.PGAssembly.CellTransfer
Build completed successfully (9377 jobs).
```

Upstream replayed linter warnings were emitted. The job count describes the
existing target dependency graph; no clean rebuild was requested.

2. Fresh scratch probe (exit **0**):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5CTAudit2.lean
```

It copies the signed definition and proves its defining equality by rfl; copies
the signed theorem under a fresh name and applies the production export with
exactly `d r mu h hB hsub`; checks
`example : type_of% @signedTransfer := @KAM.Planetary.cell_transfer`;
and applies the new export to the literal IsSigmaCompact T conclusion above.
Provider/frozen type and seal-body probes are inapplicable: no anchor is sealed.
The complete fresh axiom output for all 23 public theorems is:

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
'KAM.Planetary.ct_chartImage_sigmaCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.cell_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.measurableSet_ctFastCell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exists_fastShift_mem_fastCell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fastShift_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.volume_fastTranslates_inter_fastCell' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay (exit **0**):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.CellTransfer KAM.Planetary.PGAssembly.CellTransferTile
```

```text
replaying KAM.Planetary.PGAssembly.CellTransferTile
replaying KAM.Planetary.PGAssembly.CellTransfer
```

4. Lint (exit **1**, solely the brief's permitted stale generated-root exception):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (943 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Module-system, forbidden-token, resource-override, 100-column, size, frozen-anchor
and all 144 ABI checks pass. The generated root was not regenerated.

5. Static checks:

- CellTransfer: **306 lines**, maximum Unicode width **100**.
- CellTransferTile: **105 lines**, maximum Unicode width **100**.
- Copyright/module/public imports/docstring/exposed public section retained.
- Repository-wide declaration scan: no duplicate short name among any of the
  26 public exports, including the new ct_chartImage_sigmaCompact.
- Local KAM import closure: **331 modules**, no Provider or frozen theorem module;
  hence no DRAFT_SORRY theorem import.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty.
- `git diff --check inp...HEAD`: exit **0**.
- `git diff c76fa593..HEAD --numstat`: `13  0  KAM/Planetary/PGAssembly/CellTransfer.lean`.

The required `git diff inp...HEAD` was inspected. It reports multiple merge bases,
using `0f347d6926a79e37d59d1e5fd044af61862721ae` (other base:
`1005e6394f3da22fb5263f98658969aa2071587c`). It adds the two audited modules,
four Family dependency modules, and the round-1 report/handoff. Those dependencies
receive no new implementation verdict in this delta audit. Compared with audit 1,
all production changes consist solely of the one added lemma.

## Notes, errata and limits

No new suspected source/blueprint/frozen defect or implementation deviation.
F1 was an implementation-coverage omission, now repaired without changing source
premises or signed contracts. Round-1 documentation notes remain nonblocking:

- CellTransfer:18 says **“raw union with input angles in the unit cell”**;
  its definition at 36–38 correctly uses output angles. The prose should say
  output angles.
- Handoff names exists_fastShift_mem_ctFastCell, while the actual Tile export
  at line 41 is exists_fastShift_mem_fastCell; handoff Tile count 104 is really 105.

No Lean source, frozen file, generated file, graph status or git state was edited.
Only this report was written outside the authorized scratch directory. Temporary
probe and receipt files were removed after their results were recorded here.
This package verdict does not assert later consumer proof closure, frozen P-G
closure, or complete campaign closure.
