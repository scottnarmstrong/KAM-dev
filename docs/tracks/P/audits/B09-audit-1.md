# B09 independent package audit 1

Verdict: **PASS WITH NOTES** for the B09 infrastructure slice, including signed
`KAM.Planetary.finite_measure`. No frozen anchor is supplied or sealed by B09;
“seal-ready” does not apply to a new provider here. There is no mathematical or
proof-soundness failure found in the four audited modules. The notes concern the
inherited comparison baseline, generated-root lint, and the later consumer's
obligation to maintain a common cutoff witness across prefix lengths.

Audited HEAD: `b4f089ee44eaae0358ceaded96ff665c0e899ec0`.
Comparison `inp`: `4a5b757e944936d0ae6e9269a1170dc7098e4240`.
Scope is exactly `KAM/Planetary/WeakKAM/FiniteMeasure*.lean`, as requested.
Read AGENTS.md, PLAN, DECISIONS, the common audit brief, B09 handoff, P11B design
(row B09 and its node table), both P11B design audits, canonical signatures,
track-P statement, the relevant blueprint proof and frozen carrier definitions.
Also checked the four literal SOURCE_CONCLUSION records in
`docs/graph/P/packets/P-p11a3.nodes.md:1160–1283` and the live main-worktree
`docs/graph/P/DEPGRAPH.md:25464–25587`; these preserve the same obligations.
The user's exact worktree report destination overrides the common brief's
main-worktree output instruction. No production files were edited.

## Comparison baseline and protected paths

Ran `git diff inp...HEAD`, including the full four-file B09 addition, and
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`.
Git reports multiple merge bases and chooses
`27aee278bfaca9f8a57042f8101d68bf8996c340`. The full comparison has 165 files,
21146 insertions and 750 deletions; it is not solely B09.

The literal protected-path empty-diff check **does not pass on this baseline**:
83 root-import additions, the earlier `AmdConfinement.lean` seal body, and the
manifest's AMD `DRAFT_SORRY` → `SEALED` transition are present. These are inherited
from earlier history (notably `91350549`, `a81e8d42` and root-regeneration commits),
not B09 edits. `git diff ef956822555492af5143f71f2412132f70a3f007..HEAD --
KAM/Frozen manifest KAM.lean README.md` is empty. That commit is the parent of
B09's first commit `b8b468bf`; its complete delta to HEAD consists of the four
in-scope files only. This narrower check supplements, and does not replace, the
requested three-dot comparison. The inherited seal itself is outside this audit.

`git diff --check inp...HEAD` exits 2 for existing blank EOF lines in
`docs/tracks/P/audits/B07-audit-1.md:175` and `P5-CH-audit-1.md:272`.
The same check restricted to the four B09 files exits 0.

## Signature, nodes and consumer applicability

Canonical `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean:650–665`
and production `FiniteMeasure.lean:223–238` match **byte for byte**, from
`theorem finite_measure` through the entire type, excluding the proof delimiter.
A fresh scratch copy under `b09AuditExact` replaces the canonical placeholder
with `by exact finite_measure d ε he hsmall c ν hc`. It also checks
`example : type_of% @b09AuditExact := @finite_measure`.
This validates the whole signed type and explicit argument order; frozen/provider
identity and a frozen seal-body probe are inapplicable because B09 adds neither.

The design node table (P11B-LEAN-DESIGN.md:80–83) maps all four nodes to the
signed theorem and its local proof. Completion is distributed as follows;
no conditional helper is accepted in place of a node.

| Node | Actual proof / export | Verdict | Reason |
|---|---|---|---|
| `bpP:p11a:finite-measure` | `finite_measure`, F:223–293 | PASS | Literal signed finite-prefix output, including the constructed H and nonemptiness. |
| `stepP:p11a:fm-close` | `selection_stage_close`; `selection_eta_le`; `selectionDioHyp` | PASS | Every shorter prefix uses the same χ; SC3/A5 give thetaMax closeness; stability proves D3 rather than assumes it. |
| `stepP:p11a:fm-family` | F:90–128 and F:246–278 | PASS | Actual all-mode family is the extension at min(modeStage(k),ν); D1–D3 are proved, power_law is applied at 2γ, and hGH gives good-set inclusion. |
| `stepP:p11a:fm-incl` | `selection_retained_of_tests`; F:278–293 | PASS | Shell identity, retained recursion, real-to-complex modulus inequality, and closed-test compactness. |

Here F means `FiniteMeasure.lean`. The full `fm-close` conclusion is not the
statement of `selection_stage_close` alone: D3 is assembled by the subsequent
`selectionDioHyp` call with the proved bounds. Likewise `selection_family_measure`
is a generic conditional helper, not a literal standalone replacement for
`fm-family`: its proof invokes `power_law` (F:120–121), whose first conjunct
is compactness of the exact all-mode good set, then retains its measure conjunct.
The main theorem constructs the required family and proves its inclusion via
`hGH`. Thus compactness is furnished by the actual upstream theorem application,
even though it is discarded as unused for the signed finite-test conclusion.
There is no unsigned declaration with a graph-node identifier being substituted
for that node's full conclusion.

The scalar dictionary is explicit: `selectionLength = p11euclid`, the vector and
scalar jet equalities are proved, `selectionCDio_eq` proves equality of the
original constants, and `2 * selectionGamma = min A B` accounts for the /2 in
selectionGamma. No unexplained constant or enlarged constant dependence occurs.
The original frequencyMap, Pi carriers and original volume are retained.

Blueprint p11a3:258–264 also asserts nesting across prefix lengths. The signed
contract deliberately packages a single finite prefix, as design departure D3
at P11B-LEAN-DESIGN.md:206 explains. This is not a new narrowing by B09.
For later `ps-H` (blueprint p11a3:332) and the joint iteration record, unrelated
existential χ choices from separate calls to finite_measure cannot justify
nesting. Consumers must use one global cutoff sequence; B09's fixed-χ
`selection_stage_of_cutoffs` and `selection_stage_close` support that use.
No downstream production consumer of finite_measure exists in this checkout.
B10's actual infinite construction and its retained derivative bounds remain
outside this scoped audit; this report does not certify them.

## Every new public declaration

All names below are in `KAM.Planetary`; E, H and B abbreviate
`FiniteMeasureExt.lean`, `FiniteMeasureHyp.lean` and `FiniteMeasureBridge.lean`.
Every theorem has been included in the independent axiom probe.

| Node / role | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| bridge / implementation helper | `selectionLength_eq_p11euclid` (B:33) | PASS | Literal Euclidean length equality; no ambient norm change. |
| bridge / implementation helper | `selectionLength_fun_eq` (B:37) | PASS | Function-level dictionary, by extensionality. |
| bridge / implementation helper | `continuous_selectionReal` (B:40) | PASS | Coordinatewise real inclusion is continuous. |
| bridge / implementation helper | `selectionV` (B:44) | PASS | Real preimage of the original complex action collar; exact whole-carrier definition. |
| bridge / implementation helper | `isOpen_selectionV` (B:47) | PASS | Preimage of the open collar. |
| bridge / implementation helper | `selectionThick_eq_p11thick` (B:50) | PASS | Exact thickening dictionary for every K and radius. |
| bridge / implementation helper | `selectionThick_subset_V` (B:55) | PASS | Euclidean distance bounds the Pi norm; strict 2ϑ margin. |
| bridge / implementation helper | `K_subset_selectionThick` (B:64) | PASS | Zero displacement, guarded by nonnegative radius. |
| bridge / implementation helper | `selectionPatch` (B:68) | PASS | Original K, real collar V and ϑ; all patch fields proved. |
| bridge / implementation helper | `isCompact_selectionThick` (B:82) | PASS | Minkowski sum with a closed bounded Euclidean ball; also valid for negative radius. |
| bridge / implementation helper | `p11dg_eq_selectionDGVector` (B:102) | PASS | Vector diagonal-jet formula equality. |
| bridge / implementation helper | `p11dg_scalar_eq_selectionDG` (B:107) | PASS | Scalar tensor equality under the stated differentiability guard. |
| bridge / implementation helper | `selectionFrequency_contDiffOn` (H:25) | PASS | Holomorphy gives each requested finite smoothness order on V. |
| bridge / implementation helper | `selectionDGVector_le_sqrt_mul_norm` (H:29) | PASS | Explicit sqrt(n) conversion from Pi norm; n≥1 prevents empty sphere. |
| bridge / implementation helper | `selectionM₀_bddAbove` (H:46) | PASS | Compact thickening, continuous finite family of iterated derivatives; no unbounded sSup fallback. |
| bridge / implementation helper | `selection_jet_le_M₀` (H:72) | PASS | Uses the proved boundedness before applying le_csSup. |
| bridge / implementation helper | `selection_eta_le` (H:77) | PASS | Literal thetaMax formula gives β/2 for both ρ=1 and ρ=2. |
| bridge / implementation helper | `selectionDioHyp` (H:99) | PASS | Distinct conditional helper; D1/D2 from source data, D3 from stability_jet and proved closeness. Not a substitute for a graph node. |
| bridge / implementation helper | `SelectionExtensionChain.mono` (E:29) | PASS | Restricts analytic prefix fields; no retention or output assumed. |
| bridge / implementation helper | `selection_coherent_cutoffs` (E:41) | PASS | Chooses one sequence of actual smooth cutoffs with all derivative bounds. |
| bridge / implementation helper | `selection_stage_of_cutoffs` (E:65) | PASS | Reproves B05 output for supplied legitimate cutoffs; no existential rechoice between prefixes. |
| bridge / implementation helper | `selectionT_mono` (F:33) | PASS | Schedule cutoff monotonicity for positive initial cutoff. |
| bridge / implementation helper | `selectionModeStage_eq_of_mem_shell` (F:39) | PASS | Actual shell has its declared modeStage; handles first shell. |
| bridge / implementation helper | `isCompact_selection_tests` (F:50) | PASS | Closed intersections inside compact K; arbitrary index family, stronger than finite tests. |
| bridge / implementation helper | `abs_sum_re_le` (F:72) | PASS | Real part bounded by complex modulus; no real-frequency equality needed for inclusion. |
| bridge / implementation helper | `selectionCDio_eq` (F:79) | PASS | Exact numerical constant dictionary, using β>0 for real powers. |
| bridge / implementation helper | `selection_family_measure` (F:90) | PASS | Conditional measure helper; instantiated on the constructed clamped family. Full fm-family also uses the power_law conjunction and hGH. |
| bridge / implementation helper | `selection_adm_facts` (F:131) | PASS | Derived adapted-schedule scalars, including ε=0 and positive ε₀. |
| bridge / implementation helper | `selection_stage_close` (F:150) | PASS | Prefix extension bound plus SC3 and A5; full fm-close additionally uses selection_eta_le and selectionDioHyp. |
| bridge / implementation helper | `selection_retained_of_tests` (F:191) | PASS | Shell-stage identity plus induction; reaches the next retained set without assuming it nonempty. |
| finite-measure | `finite_measure` (F:223) | PASS | SIGNED: exact canonical declaration; cutoff witnesses, compactness, inclusion, measure and nonemptiness proved. |

## Definition classification and hypotheses

Only two new global definitions occur: `selectionV` (B:44) and
`selectionPatch` (B:68). Both are **intended objects on their whole carrier**.
selectionV is the literal real preimage of actionNbhd K (2ϑ); selectionPatch
uses the original K, V, ϑ and proved patch properties. There are no new
abbreviations or structures, instances, substitute norm spaces or measures.
Local `wt`, Hs, A and B are literal formulas used in the proof.

The coherent-cutoff construction sets the witness to zero outside its finite
prefix. That is harmless unused data: every consumed cutoff index is <ν,
including when shorter prefixes are used. Smoothness/extension bounds are
proved from actual cutoffs and holomorphic increments, not from a junk value.
The M₀ sSup receives a genuine bounded-above proof before it is used as an
upper bound; unit spheres are nonempty under n≥1. fderiv/iteratedFDeriv uses
that require smoothness have the analytic/open-neighbourhood guards proved.

SelectionFiniteChain is an allowed already-built retained-prefix premise, not
a hypothesis asserting the next stage's measure/nonemptiness. B09 proves that
next-stage conclusion. selectionDioHyp's hreg/hclose are conditional premises
under a distinct helper name; F:249–250 discharges them using hstage. The signed
result adds no hypothesis and asks for no supplied good set or output family.
The weaker analytic prefix is supplied through hc.toSelectionExtensionChain.

The recursive KAM import closure has 82 modules, no providers and no frozen
theorem modules. Its 12 frozen imports are definition anchors, all currently
SEALED: ActionNbhd, ComplexStrip, FrequencyMap, HamiltonianVectorField,
HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals,
OmegaZero, RealHamiltonian, SymplecticForm, and Planetary/Phase. No
DRAFT_SORRY theorem is imported directly or transitively by these modules.

## Independent verification receipts

All Lean/Lake operations are sequential, with `LEAN_NUM_THREADS=1` and
`nice -n 5`; no clean, update, cache fetch, heartbeat override or full-library
rebuild was performed. Waiting at the existing compile gate was allowed.

Targeted build:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b09 KAM.Planetary.WeakKAM.FiniteMeasure
[inp-gate] slot 2 acquired 21:49:53 for KAM.Planetary.WeakKAM.FiniteMeasure
Build completed successfully (9128 jobs).
exit 0
```

Replayed warnings concern pre-existing dependencies: unused variables,
deprecated names, unused simp arguments and one style suggestion. No B09
module warning or default-heartbeat failure was reported.

Exact-type/body and all-public-theorem axiom probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B09Audit.lean
exit 0
```

There were exactly 29 output lines and no elaboration errors or warnings:

```text
'KAM.Planetary.selectionT_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionModeStage_eq_of_mem_shell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isCompact_selection_tests' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.abs_sum_re_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionCDio_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_family_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_adm_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_stage_close' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_retained_of_tests' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.finite_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLength_eq_p11euclid' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLength_fun_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuous_selectionReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_selectionV' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionThick_eq_p11thick' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionThick_subset_V' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.K_subset_selectionThick' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isCompact_selectionThick' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11dg_eq_selectionDGVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11dg_scalar_eq_selectionDG' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SelectionExtensionChain.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_coherent_cutoffs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_stage_of_cutoffs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionFrequency_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionDGVector_le_sqrt_mul_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionM₀_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_jet_le_M₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_eta_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionDioHyp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay (one invocation, all four modules):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.FiniteMeasure KAM.Planetary.WeakKAM.FiniteMeasureBridge KAM.Planetary.WeakKAM.FiniteMeasureHyp KAM.Planetary.WeakKAM.FiniteMeasureExt
replaying KAM.Planetary.WeakKAM.FiniteMeasureExt
replaying KAM.Planetary.WeakKAM.FiniteMeasureHyp
replaying KAM.Planetary.WeakKAM.FiniteMeasureBridge
replaying KAM.Planetary.WeakKAM.FiniteMeasure
exit 0
```

B09 static hygiene: no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`,
`EuclideanSpace` or `set_option` appears in these four files. Each has the
copyright, module command, public imports, module docstring and public section.
The two definitions are under `@[expose] public noncomputable section`.
No declaration is introduced at the root namespace; a whole-KAM declaration-name
scan found no reused public B09 helper short name outside these files.

| Module suffix | Lines | Maximum line length |
|---|---:|---:|
| FiniteMeasure | 295 | 100 |
| FiniteMeasureBridge | 118 | 99 |
| FiniteMeasureExt | 167 | 99 |
| FiniteMeasureHyp | 155 | 98 |

Repository lint (including its serialized Lean ABI subprocess):

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (908 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The only reported lint failure is the brief's explicitly allowed stale generated
root. Frozen-anchor guard and all 144 ABI hashes pass. KAM.lean was not regenerated.

## Suspected defects, deviations and limits

No new pinned-source erratum or frozen-definition defect was found. This audit
compares the pinned blueprint/source contracts and their implemented interfaces;
it does not claim an independent re-audit of every upstream PDF theorem.
The narrower single-prefix signed contract and the later coherent-witness
obligation are documented above with exact blueprint/design locators; they are
not silently identified with a proved infinite selection theorem.

B09 does not apply the existential `finite_extension` directly. Instead E:65–165
reconstructs its conclusions from the same cutoff hypotheses and existing
`selectionStage_contDiff` / `selectionStage_extension_bound` suppliers. This is
an implementation-route deviation that preserves the literal construction and
bounds, and allows all prefixes to share χ. No B05 file or signature changes.
The helper's extra cutoff premises are discharged by E:41–62 in the main proof;
they are not extra hypotheses on signed finite_measure.

The unsigned helpers are implementation components under distinct selection-*
names. Their docstring node attributions must be read with the composite proof
locators above: no claim is made that a generic closeness/measure helper alone
is the full literal graph statement. The design table itself assigns the nodes
to local parts of finite_measure. In particular, selectionDioHyp is not accepted
as an assumed all-mode family or an independent completed fm-* node.

No heartbeat/design signal or unresolved mathematical uncertainty arose in the
in-scope proof. The only release notes are the inherited protected-path
comparison differences, permitted generated-root lint failure, and downstream
common-witness requirement. The package PASS does not close P-G, any physical
headline, or any frozen anchor.

## Deliverable and cleanup

Only this report is created as a repository deliverable:
`/root/code/KAM-inp-p11b-b09/docs/tracks/P/audits/B09-audit-1.md`.
The pre-existing untracked B09-handoff.md is preserved. Temporary probe and
receipt files under this worktree's `.lake/abi-scratch/` are removed after their
contents are captured here. No state-changing git command was used.
