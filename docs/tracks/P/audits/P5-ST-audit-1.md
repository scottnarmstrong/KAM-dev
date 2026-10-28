# Independent package audit 1: P5-ST

Overall verdict: **PASS WITH NOTES** for the scoped infrastructure package
`KAM/Planetary/PGAssembly/Strictness.lean`.
The signed strictness contract and all assigned proof steps are implemented without added
source premises. This is not a seal-readiness verdict for the frozen P-G anchor:
`KAM.Planetary.properlyDegenerateKAM` remains `DRAFT_SORRY`. There is no provider in
this package and no provider/frozen-type or frozen seal-body test applies here.

## Scope and snapshot

- Worktree: `/root/code/KAM-inp-p5st`; report destination follows the user's explicit
  worktree-local path, overriding the generic brief's main-worktree destination.
- HEAD: `5b966a75c4f6e6dac741312f603a3e5e425fd243`.
- `inp` observed: `980388b435b56c1a548f7c9771a8f4c62033aba7`.
- `git diff inp...HEAD` warns of multiple merge bases and selects
  `8f19267d4a71f86284c9979293b8f991fb2c0b96`. The full comparison was inspected:
  CellTransfer (293 lines), CellTransferTile (105), Lower (251), Strictness (426).
  The first three are inherited dependencies, outside the handoff's ONLY-Strictness scope.
  The two package commits `89e79b68` and `5b966a75` touch only Strictness.
- Audited module SHA256:
  `3fea3bbee6601b503088865521af69e9caf6771a2b47b806654e401d5898acf0`.
- Shared `/root/code/KAM-inp/.drafts/design/P45Signatures.lean` SHA256:
  `586ed2e3188b154d5cc6d44d3f85b420ef85ddd7faaa2bcbb6d6ca6db7d0f304`.
- Local `docs/tracks/P/design/P45-LEAN-DESIGN.md` SHA256:
  `a1d2cd226b6b2f6b668f2712e66d6191a9fd6ab4c03ddc5183539f92c72d5dbf`.

Read AGENTS.md, PLAN.md, DECISIONS.md, the shared audit brief, local handoff/AUDIT FOCUS,
P45 design package/node rows and proof/consumer plan, relevant findings of design audits
1–4, the shared signatures, blueprint Part 5 lines 302–325 and graph packet strictness
records, track-P statement, actual frozen P-G telescope and its relevant frozen definitions.
The frozen definitions retain canonical angle/action order, disc cylinder, physical fast
period 2*pi, and the actual degenerate Hamiltonian. D20 supersedes historical statement
prose saying approval is pending. No I/N theorem is implemented or certified by this package.

## Declaration and node decisions

Names are in `KAM.Planetary` except the already imported root-level
`finite_measure_coordinate_cut`. Line numbers refer to Strictness.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| st-add / inverse | `stParam` (42) | PASS | Unique raw-family parameter on the union; explicit zero extension outside. |
| st-add / inverse specification | `stParam_eq` (47) | PASS | Raw equality implies physical equality, then family injectivity identifies J. |
| st-add / set transport | `stParam_preimage` (58) | PASS | Exact preimage intersected with the full raw union. |
| st-ivt / sigma compactness | `stSigma_inter_closed` (72) | PASS | Closed intersection of a sigma-compact set. |
| st-add / inverse measurability | `stParam_measurable` (78) | PASS | Closed preimages from sigma-compact restricted raw unions and the explicit outside branch. |
| st-add / parameter measure | `stMeasure` (103) | PASS | Push-forward of volume restricted to the output representative. |
| st-add / finiteness | `stCell_ne_top` (107) | PASS | Exact disc-cell volume, bounded V, positive r. |
| st-add / finiteness | `stRep_ne_top` (112) | PASS | Cell transfer and a positive finite (2*pi)^n factor. |
| st-add / instance | `stMeasure_finite` (121) | PASS | Finiteness is proved from restricted volume, not assumed. |
| st-add / measure evaluation | `stMeasure_apply` (127) | PASS | All measurable A; restricts parameters to D0 explicitly. |
| st-add / source mass | `st_mass` (135) | PASS | Literal physical-cell mass = (2*pi)^n times parameter measure on sigma-compact subsets of D0. |
| st-add / support | `stMeasure_compl_D0` (141) | PASS | Measure is supported on D0. |
| st-add / support | `stMeasure_inter_D0` (147) | PASS | Intersecting a measurable set with D0 preserves mass. |
| st-add / real bridge | `st_mass_real` (152) | PASS | Exact toReal factor, with positive (2*pi)^n. |
| `stepP:p5:st-add` | `st_add` (159) | PASS | Literal countable additivity for pairwise disjoint sigma-compact B_i subsets of D0. |
| st-null / raw representative | `st_slice_rep_null` (169) | PASS | Hyperplane nullity, product-cell Lipschitz null image, countable lattice saturation, then representative inclusion. |
| `stepP:p5:st-null` | `st_null` (189) | PASS | Literal physical-cell slice mass zero, all coordinates j (stronger than first-coordinate version). |
| st-null / cut input | `stMeasure_slice_null` (200) | PASS | Parameter measure gives zero to every coordinate slice. |
| st-ivt / generic IVT | `st_cut_value` (213) | PASS | Any finite coordinate-slice-null measure; every strictly intermediate real mass is attained. |
| st-ivt / positivity | `stCell_toReal_pos` (258) | PASS | Positive cell volume from nonempty open V, positive r and exact disc volume. |
| `stepP:p5:st-ivt` / cut mass | `st_ivt` (265) | PASS | Literal target min(total/2, sqrt(r)*cell/2), no free constant or extra assumption. |
| st-ivt / cut and complement | `strictness_aux` (328) | PASS | Cut subset D0, both sigma-compact, exact deleted mass. This supports st-ivt despite its st-conc docstring label. |
| `bpP:p5:strictness`; `stepP:p5:st-conc` | `strictness` (360) | PASS | Exact signed type; positive retained mass, requested lower coefficient and strict upper bound. |
| st-ivt / P5-CUT input | `finite_measure_coordinate_cut` (imported) | PASS, reused | Supplies continuity for arbitrary finite measures with null slices; not redefined here. |

All four step nodes mapped by design lines 211–214 are established. Their content need not
be duplicated in a single theorem: `st_ivt` supplies the cut value, `strictness_aux` supplies
the two sigma-compact sets, and the proof of `strictness` supplies the mass split and bounds.
There is no export named `st_conc` claiming a weaker substitute. `st_add`, `st_null` and
`st_ivt` state their literal mass conclusions. Intermediate null-image and saturation
assertions of st-null are proved inside `st_slice_rep_null`.

## Signature, premises and consumer fidelity

The sole newly signed declaration, `strictness`, equals shared signatures lines 1237–1243
after whitespace normalization. A scratch theorem copied that complete telescope and
conclusion under a fresh name, proved it by `exact strictness d r mu h hr`, and checked
`example : type_of% @audit_strictness := @strictness`. Both elaborated at default limits.
No draft signature module or frozen DRAFT theorem was imported by the probe.

The dimensions and data retain `PGData`'s exact frozen source assumptions. Admissibility is
`0<r`, `r<pgRstar d`, `0<mu`, `mu<d.mu0`, and the explicit logarithmic smallness bound.
The extra signed `r<finalRadius d` is the design-approved data-only radius shrink, not a
conclusion premise. Coordinates, sigma-compactness, measurability and disjointness in the
helpers are their source/typing conditions. The generic cut lemma explicitly requires a
finite measure and null slices, and the package proves both when applying it. No KAM
existence, hard measure step or strictness conclusion is supplied as an input or instance.

Writing C=pgLoss d, K=volume(cell).toReal and T=volume(full union intersect cell).toReal:
the proof derives C>0, K>0, T>0, T<=K and sqrt(r)*2*(C+1)<1. It deletes
q=min(T/2,sqrt(r)*K/2)>0, proves W=T-q using the parameter measure, and derives
W>0, W>=(1-(C+1/2)*sqrt(r))*K and W<K. All toReal comparisons have finite-measure
justifications; no top-to-zero fallback is used in the inequalities.

Deletion is in the original parameter carrier. Since `kset B` is the union of entire
physicalTorus ranges, keeping D0 minus B keeps whole tori; it does not cut points out of
individual tori. Sigma-compactness enables the existing cell-transfer measurability and
location conclusions. For the planned P5-MAIN consumer (design lines 562–566), the signed
lower bound leaves the required strict slack when the final C is at least pgLoss+1;
the separately proved positivity handles truncation by ENNReal.ofReal. No production
consumer of Strictness is present in this checkout, so this is a verified interface
compatibility result, not a downstream main/provider build receipt.

## Definition classification

Exactly two definitions, no new abbreviation/structure:

- `stParam`: intended total extension of the unique parameter inverse. On the raw union,
  `stParam_eq` proves independence of the existential choice by physical-family
  injectivity. Off that union it is literally zero. That fallback is intentional and
  measurable, and restricted volume in stMeasure never draws mass from outside the
  raw union. The inverse claim is made only on its correct carrier; no bogus global
  inverse identity or outside value enters a theorem.
- `stMeasure`: literal map of volume restricted to `outputRepresentative D0` along
  stParam. It is a genuine Borel measure on the whole parameter space. It is not the
  physical mass itself: the physical mass is exactly (2*pi)^n times this measure.
  `stMeasure_apply`, support lemmas and `st_mass` verify its intended characterization.

Both: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS OK; CHARACTERIZATION OK;
CHOICE_INDEPENDENCE OK where applicable. Definition verdict PASS. The one new instance
`stMeasure_finite` proves a property of this constructed measure and adds no source field.

## Independent verification

All audit-owned Lean/Lake invocations were sequential with `LEAN_NUM_THREADS=1` and
`nice -n 5`; lint's ABI subprocess inherited those settings. No clean/update/cache-get,
resource override, production edit or state-changing git command was used.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5st KAM.Planetary.PGAssembly.Strictness
   ```

   Exit 0. Relevant exact output:

   ```text
   [inp-gate] slot 1 acquired 22:28:14 for KAM.Planetary.PGAssembly.Strictness
   Build completed successfully (9398 jobs).
   ```

   Lake also replayed dependency warnings and axiom-print information; no Strictness
   warning or build error was reported. The job count is Lake's dependency total,
   not a clean library rebuild.

2. Independent exact-signature probe and all-public-declaration axiom inspection:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5STAudit1.lean
   ```

   Exit 0. No probe warnings/errors; the complete exact output is:

   ```text
'KAM.Planetary.stParam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stParam_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stParam_preimage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stSigma_inter_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stParam_measurable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stMeasure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stCell_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stRep_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stMeasure_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stMeasure_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.st_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stMeasure_compl_D0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stMeasure_inter_D0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.st_mass_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.st_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.st_slice_rep_null' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.st_null' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stMeasure_slice_null' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.st_cut_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stCell_toReal_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.st_ivt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.strictness_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.strictness' depends on axioms: [propext, Classical.choice, Quot.sound]
'finite_measure_coordinate_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   This covers all 20 new public theorems, both definitions, the finite-measure
   instance, and the imported cut lemma. No sorryAx or additional axiom occurs.

3. Kernel replay, one invocation:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.Strictness KAM.Planetary.PGAssembly.CutMeasure
   ```

   Exit 0. Exact output:

   ```text
replaying KAM.Planetary.PGAssembly.CutMeasure
replaying KAM.Planetary.PGAssembly.Strictness
   ```

4. Source lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1, solely the generated-root discrepancy explicitly permitted by the brief.
   Exact output:

   ```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1030 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
   ```

   Module checks, frozen-anchor guard and all 144 frozen ABI hashes passed. The generated
   root was not regenerated. No other lint finding occurred.

## Hygiene and integrity

Strictness is 426 lines, maximum 99 Unicode characters per line; all lines satisfy the
100-character focus. Copyright, module command, public imports, module docstring and
exposed public noncomputable section are present. No forbidden token, heartbeat/recursion
option or EuclideanSpace occurs. A full project declaration-name scan found zero reused
short names among all 23 new named declarations. No root declaration or global ambient
norm instance was introduced.

Recursive project-import inspection found 352 project modules, no providers, no frozen
theorems, and 55 frozen definition modules, all manifest SEALED. Thus neither draft P-G
nor another provider is hidden upstream. `git diff inp...HEAD -- KAM/Frozen manifest
KAM.lean README.md` is empty (apart from Git's merge-base warning). `git diff --check`
passes. Generated files and protected anchors were untouched.

## Notes, uncertainties, source gaps and closeout

No mathematical defect, added premise, weakened signed conclusion, harmful fallback,
new suspected pinned-paper erratum or implementation deviation was found in scope.
The module follows the blueprint's corrected output-representative argument rather than
identifying a parameter-cell image with an output cell; the old P5-04 problem is not
reintroduced. The known CP10/CP11 omission of a strictness proof is explicitly replaced
by this argument. This audit does not newly adjudicate those papers against their PDFs.

Two locator/receipt qualifications should be retained. The handoff calls strictness_aux
part of st-conc, but its actual conclusion is the cut-mass/sigma-compactness portion of
st-ivt; the final strictness proof establishes st-conc. The design node table still lists
finite_measure_coordinate_cut under Strictness, while the package table and actual
implementation correctly reuse P5-CUT. Neither affects node coverage or consumers.

The graph packet `docs/graph/P/packets/P-p5.nodes.md:2411,2441,2472,2504,2535` still
marks the five strictness proposition/step records NOT_STARTED. Its st-ivt note at
2506–2507 retains the earlier continuity/IVT source gap. This package now proves the
missing IVT and sigma-compactness content, with explicit Mathlib inputs, but this report
does not modify graph statuses or certify graph bookkeeping closure. No frozen theorem
is sealed by the package audit. These scope/bookkeeping notes and the lint qualification
above are preserved in the overall PASS WITH NOTES verdict.

The scratch probe `.lake/abi-scratch/P5STAudit1.lean` was deleted after successful
elaboration and axiom inspection. Only this requested report was persistently written
inside the repository. The pre-existing untracked P5-ST-handoff.md was preserved.
Final checks found exactly those two untracked report/handoff files and no tracked
worktree changes; report whitespace/fences and declaration coverage passed, and the
protected-path diff and `git diff --check` remained clean.
