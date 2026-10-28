# P6-5 independent audit 1

**Verdict: PASS WITH NOTES for the scoped P6-5 package.** All four new public
theorems match the design signatures, elaborate at those independently extracted
types, have standard axiom closure, and pass kernel replay. The Part 1 declaration
for measure-positive (b) is delivered and has the required type. No mathematical
or statement defect was found in `Assembly.lean`. Repository-wide lint exits 1:
the generated root is stale and an inherited Part 1 line exceeds 100 characters.
Neither is introduced by P6-5. The explicit numerical box-volume estimate in the
blueprint is not an exported conclusion of the approved design interface.

Audit date: 2026-10-28. This is a focused, refute-first, tier-2 audit, not a
closure audit of P-PLANAR or P-FIXED. No frozen theorem is sealed by this package.
Those two headline anchors remain `DRAFT_SORRY` / `FROZEN_UNPROVED`; neither
receives a seal-ready verdict here. No provider/type/seal-body test applies to
P6-5: it introduces ordinary infrastructure theorems, not a provider export.

## Scope, authority and frozen inputs

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the P6-5 handoff and its
AUDIT FOCUS, the relevant design and three design audits, Track P's statement
document, the Part 6 blueprint statements, the frozen predicates and relevant
headline statements. The live manifest, rather than the historical draft status
in `docs/tracks/P/statement.md`, determines the frozen declaration states.

The user's exact worktree/report-path instruction overrides the brief's generic
instruction to put the report in the main worktree. Only this report is added;
temporary probes/logs used `.lake/abi-scratch/` and were removed. No source,
frozen file, manifest, generated file, history or dependency was edited.

Snapshot:

- HEAD: `1548226f2c35a45a33cbf91535f21a7dcca026b3`.
- `inp`: `1699a58fc52973a29e47f1636a414db9a7ffda8d`.
- Requested `git diff inp...HEAD` reports multiple merge bases and selects
  `376727b7235b56169255872ccc65151144c6df16`.
  The other merge base is `00cf49c93cbcea2fd371edf0865258fadd64a43d`.
- The complete comparison contains 46 changed files, including inherited work.
  Audit scope is only `KAM/Planetary/Newtonian/Assembly.lean`, with supporting
  interfaces inspected to establish its meaning. `git show --stat HEAD` confirms
  P6-5 itself adds only that 156-line file.
- The handoff was already untracked at audit start and was preserved.

SHA-256 snapshot identifiers:

| Input | SHA-256 |
|---|---|
| `KAM/Planetary/Newtonian/Assembly.lean` | `616fcfd05fe16642d0976a0afad77332bbceb235effda6b360229c81bc85d6e2` |
| `docs/tracks/P/design/KEPLER-LEAN-DESIGN.md` | `b23265f9c90c8fdf3bebd66fb7eac1cf965e3b1b22080d85ff9c2becf2fe4a15` |
| `blueprint-P/parts/p6-newtonian-models.tex` | `b6885887ba6dfd181e79925cb4584b4b5590d0debc3bc205a2c49aa86b634899` |
| `KAM/Planetary/Hamiltonian/Liouville.lean` | `0f9ad36a119c0196661fabe20252df0de0acca65233cb9633fbd09aa09286213` |
| `docs/tracks/P/audits/P6-5-handoff.md` | `67d13747509c31286d415010b613ace7a218eac4d4a476ae96d9be1f16c16a50` |
| `KAM/Frozen/Planetary/Defs/MovingKolmogorovSet.lean` | `a62a269c68b80408afdaae03a3058bb1d1196b267caabedcbc895d0a72c1c3aa` |
| `KAM/Frozen/Planetary/Defs/FixedKolmogorovSet.lean` | `a5d7108e10d7dbd95aa980ffdc45c73950905179398a2057101f2b5b2159e8f9` |

## Declaration ledger

All declaration names below have namespace `KAM.Planetary`.

| Node | Declaration and implementation locator | Verdict | Reason |
|---|---|---|---|
| measure-positive (a), coordinate bounds | `circularTube_norm_lt`, Assembly:41 | PASS | Exact design type, including strict inequalities and absolute values of masses. Pi max norm and period-one circular-point formula agree with the source. |
| measure-positive (a), finiteness | `volume_lt_top_of_subset_circularTube`, Assembly:101 | PASS WITH NOTES | Exact design type; proves finite outer volume for every subset, without a measurability premise. The blueprint's additional numerical box estimate is not exported. |
| measure-positive (b) | `measure_chart_image`, Liouville:216 | PASS, dependency interface | Existing Part 1 export, not redeclared in Assembly. Exact D17 consumer signature, Borel image measurability, full-position-lattice assumptions, factor `ENNReal.ofReal (c ^ d)`, unit cell and positivity equivalence retained. |
| movkol-assembly | `movingKolmogorovSet_of_tube`, Assembly:113 | PASS | Exact design type; constructs the literal frozen moving predicate with all-time Newton reconstruction and barycentric pair bounds. |
| fixkol-assembly | `fixedKolmogorovSet_of_tube`, Assembly:133 | PASS | Exact design type; constructs the literal frozen fixed predicate with all-time fixed-center equations and the Sun at the origin. Arbitrary real epsilon retained. |

For all five signatures, extraction from the design's embedded Lean block and
comparison with the actual declaration, ignoring whitespace only, returned
`signature tokens identical: True`. Design locators are lines 2025–2060; package
row P6-5 is line 438; proof-plan guidance is section 7.1; Part 1 ownership and the
consumer caveat are lines 594–598. The design audits already distinguish the
full-position-lattice lemma from the Cartesian-cylinder measure argument; this
audit checked the actual delivered interface rather than relying on their PASS.

## Premises, definitions and mathematical proof checks

There are **no new definitions, abbreviations, structures, instances or choice
constructions** in Assembly. Definition classification: N/A for new objects.
Existing objects were unfolded/inspected: `Phase`, `circularPoint`, `circularTube`,
`IsPhysicalTorus`, `NoCollision`, `PairBounds`, the two solution predicates and the
two Kolmogorov predicates; `AxisData` and the three tube constants were inspected
at the dependency boundary. Their bodies are used literally, without a substitute
predicate, off-domain fallback or changed norm.

Premise classification (SOURCE = statement premise; STANDING = Part 6
convention; TYPING = carrier data). No RULED or EXCESS premise was found.

| Declarations | Binders / expanded logical input | Classification and source |
|---|---|---|
| All four new theorems | `n`; `G`, `m0`, `m`, `a`, `eta`; `z` or `S` where present | TYPING; Part 6 conventions and the exact design carriers. No ambient typeclass premise is introduced. |
| Coordinate bound and finiteness | `hG`, `hm0`, `ha` | SOURCE; blueprint:250, “G,m0 > 0 ... a_i > 0”. |
| Coordinate bound | `hz` | SOURCE; blueprint:252, “every z in U_eta”. |
| Finiteness | `hS` | SOURCE; blueprint:252, “every S subset U_eta”. |
| Both assemblies | `gamma`, `A` | TYPING; explicit design representation of the axis-dependent constants. |
| Both assemblies | `h.gap_pos`: positive gamma | SOURCE; tube-constants:210–215. |
| Both assemblies | `h.le_axis`: gamma <= every axis | SOURCE; same definition of the minimum. |
| Both assemblies | `h.le_diff`: gamma <= each nonzero axis gap | SOURCE; same definition of the minimum; distinctness retained. |
| Both assemblies | `h.axis_le`: every axis <= A | SOURCE; same definition of the maximum. |
| Both assemblies | `hη`, `hG`, `hm0`, `hm` | SOURCE; blueprint:267, inherited by:282. |
| Both assemblies | `hn` | STANDING; blueprint:23, “Throughout n >= 1”. |
| Moving assembly | `mu`, `hμ` | TYPING and SOURCE respectively; blueprint:267, “mu >= 0”. |
| Fixed assembly | `epsilon` | TYPING; blueprint:282 explicitly permits epsilon in R. |
| Both assemblies | `hS` | SOURCE; blueprint:269 (S1), Borel `MeasurableSet S`. |
| Both assemblies | `hSt` | SOURCE; blueprint:269 (S1), containment in the smaller tube. |
| Both assemblies | `hS2`, expanded as witnesses `w,K,theta`, `K theta=z`, `range K subset S`, physical torus | SOURCE; blueprint:270 (S2) verbatim, with fixed Hamiltonian at:282. |

The last input is legitimate for these assembly propositions: it supplies the
source's torus data, not the collision, Newton/fixed equations or pair bounds
that the assembly must prove. It is not an existence proof of those tori or of
a positive-measure set. `IsPhysicalTorus` retains analyticity, Hamiltonian
differentiability, lattice periodicity/injectivity, derivative injectivity,
Lagrangian property, Diophantine frequency and the complete orbit derivative
identity. No hidden premise asserts the missing physical reconstruction.

Line-by-line proof check:

1. Assembly:46–99 picks the actual circular-point witness from tube membership.
   Component projections are norm contractions; the sine/cosine coordinates are
   bounded by one. Finite-range boundedness justifies `le_ciSup`. Nonnegativity of
   the two suprema justifies `pi_norm_le_iff_of_nonneg`. Triangle inequalities give
   the strict bounds. The factor `abs (m i)` permits arbitrary signed masses,
   strengthening the positive-mass source statement. The omitted assumptions
   `eta > 0`, `n > 0`, `m_i > 0` do not invalidate this stronger assertion: for
   nonpositive eta the tube is empty, and the empty index case is handled by the
   Pi norm/nonnegative supremum lemmas. `hG`, `hm0` are retained but unused.
2. Assembly:104–109 bounds the product norm by the maximum of the two coordinate
   bounds, then invokes finite measure of bounded subsets. No measurability or
   positive-volume claim is smuggled into this step.
3. Assembly:123–131 uses positivity and the two upper bounds for
   `min eta (gamma/6)`. Tube monotonicity supplies the frozen eta-containment.
   Every point of each complete torus lies in the smaller tube by `hKS` then
   `hSt`. `circularTube_pair_bounds` supplies collision exclusion at every phase.
   `orbit_transfer_moving` receives all its sign hypotheses, the original torus
   and that exclusion; the barycentric pair-bound lemma supplies the last frozen
   conjunct. There is no restricted time interval or shifted initial-phase gap.
4. Assembly:143–152 repeats this construction with `orbit_transfer_fixed`, whose
   actual hypotheses require `hm0`, `hm` but not positivity of epsilon or G.
   The final pair configuration is exactly `Fin.cons 0 ...`, as frozen.

Adversarial second pass checked empty dimensions, empty/nonpositive-radius tubes,
signed masses, zero moving coupling, arbitrary fixed coupling, Borel versus
completed measurability, range containment versus one initial point, every
initial phase/time, max norm versus Euclidean force distance, and hidden bundled
conclusions. No counterexample or extra hypothesis survived. Unused `hn` (and
fixed `hG`) match the source/design and are harmless.

## Part 1 dependency and coverage notes

Assembly's comment says measure-positive (b) “is Part 1's
`KAM.Planetary.measure_chart_image` ... not re-declared here.” This is accurate:
there is **no application or import of Liouville in Assembly itself**. Reuse is
package-level delivery of the already existing declaration, not a new proof step
inside Assembly. Liouville:227–229 constructs `IsChart` from the analytic and
symplectic premises and applies the actual Part 1 lattice results. Its exact
consumer signature was independently elaborated and kernel-replayed here; the
rest of the Part 1 mathematical implementation is outside this audit's scope.

The required domain invariance, periodic map, injectivity modulo the full lattice
and periodic set hypotheses all remain visible. This does not establish that a
particular P12 Cartesian cylinder satisfies them. Design:598 explicitly says it
“is NOT the interface for P12's Cartesian cylinder torus”; that consumer limit
must remain attached to this result.

Blueprint:252 additionally states the numerical product-box bound, whereas
design:2030–2031 and Assembly:101–109 conclude only `volume S < top`. This is a
pre-existing design coverage restriction, not an implementation/type mismatch
or a false mathematical assertion. The norm bounds and finiteness needed by
the frozen headlines are delivered; do not mark the explicit box-volume formula
itself formalized from these declarations. Blueprint (b)'s final positive-finite
claim is obtained by combining its positivity equivalence with (a) and actual
consumer inputs; P6-5 does not prove the required positive-volume torus union.

## Independent verification

All Lean-related commands were sequential, with `LEAN_NUM_THREADS=1`; direct
Lean/kernel checks and the lint ABI subprocess ran under `nice -n 5`. Builds used
the required gate. No cleanup, dependency update, cache fetch or full-library
rebuild was requested. Existing dependency warnings were replayed; the only
reported newly built target was Liouville (6.8s).

### Targeted build

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p65 KAM.Planetary.Newtonian.Assembly KAM.Planetary.Hamiltonian.Liouville
[inp-gate] slot 1 acquired 06:45:27 for KAM.Planetary.Newtonian.Assembly KAM.Planetary.Hamiltonian.Liouville
Build completed successfully (9107 jobs).
exit 0
```

Replayed unused-variable warnings were in Energy:106 (`hm`, `hκ`), Algebra:146
(`hc`) and Chart:193 (`hc`); none was in Assembly.

### Signature probes and axiom closure

Generated `.lake/abi-scratch/P65Audit.lean` by extracting each design signature
through `:= sorry`, replacing the declaration header by `example`, and replacing
the body with an application of the corresponding actual theorem. Imports were
Assembly and Liouville; namespace opens were `MeasureTheory Set Real` and
`KAM KAM.Kepler KAM.Planetary`; the common variable was `{n : Nat}`.
The explicit argument lists used were:

```text
circularTube_norm_lt: hG hm0 ha hz
volume_lt_top_of_subset_circularTube: hG hm0 ha hS
movingKolmogorovSet_of_tube: h hη hn hG hm0 hm hμ hS hSt hS2
fixedKolmogorovSet_of_tube: h hη hn hG hm0 hm hS hSt hS2
measure_chart_image: hc hO hΨ hs hQ1 hQ2 hA hAO hAper
```

Command: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P65Audit.lean`;
exit 0. Exact axiom output:

```text
'KAM.Planetary.circularTube_norm_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.volume_lt_top_of_subset_circularTube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.movingKolmogorovSet_of_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fixedKolmogorovSet_of_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.measure_chart_image' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Newtonian.Assembly KAM.Planetary.Hamiltonian.Liouville
replaying KAM.Planetary.Hamiltonian.Liouville
replaying KAM.Planetary.Newtonian.Assembly
LEAN_CHECKER_EXIT=0
```

### Source hygiene and protected paths

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
Lean lines over 100 characters:
/root/code/KAM-inp-p65/KAM/Planetary/Hamiltonian/Liouville.lean:35:108
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (428 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
LINT_EXIT=1
```

This is a failed global lint invocation, not a claimed PASS. The 108-character
line is inherited from PP1-7 commit `b1e76a2`, verified in `HEAD^`; it is outside
P6-5's authorized module scope. Root regeneration is explicitly delegated to the
orchestrator. Assembly has 156 lines, zero lines over 100 characters, the required
copyright/module/public imports/docstring/public section, and no forbidden proof
escape or resource override. A transitive KAM-import walk from Assembly and
Liouville visits 61 modules and finds **no provider or frozen theorem imports**.
Frozen definitions are permitted; no DRAFT_SORRY anchor enters this closure.

`git diff --check inp...HEAD -- KAM/Planetary/Newtonian/Assembly.lean` exits 0
(only Git's multiple-merge-base warning). The protected-path comparison is not
literally empty: `git diff --numstat inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`
returns `9 0 KAM.lean`. Frozen files, manifest and README have no diff. The nine
root imports are inherited: `git diff --quiet 00cf49c93cbcea2fd371edf0865258fadd64a43d HEAD -- KAM.lean`
exits 0, and P6-5's own commit touches Assembly alone. This is recorded rather
than silently treating the complete branch comparison as clean.

## Closeout, limitations and errata

All four new declarations and the required Part 1 interface are classified;
all five exact-type checks, five axiom checks and the single kernel replay pass.
P6-5's source hygiene passes locally; the two inherited repository lint notes
remain for integration. No repair was performed. The report's whitespace check
passes; scratch probes and audit logs were removed after recording their output.

No new suspected pinned-source erratum, false blueprint statement or frozen
definition defect was established. No mathematical deviation was introduced by
the auditor. The inherited box-volume coverage restriction and full-lattice
consumer restriction are explicitly retained above. This audit does not re-audit
the pinned external PDFs, all dependency proofs, unrelated branch additions,
P12/P13 applicability, or closure of the physical headline theorems.
