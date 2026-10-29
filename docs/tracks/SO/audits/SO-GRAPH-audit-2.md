# SO-GRAPH independent audit 2

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-sograph`.
Audited HEAD: `d819595b58024019f2faf542af1bfc1bf2827dcf`.
Comparison: `git diff inp...HEAD`, with `inp` at
`6cc8c0e509fe0f60c41c49ebe065a4a595cb4973` and merge base
`302963ff1dda8363f983a5e10f3b24c9f0ba38cb`.
Delta: `9791e24a..d68b8820` (F1 fix), plus the round-2 handoff in HEAD.

## Verdict

**PASS WITH NOTES. F1 is resolved.** All four signed declarations now have the
qualified names and contracts of `SOSignaturesLunar.lean` §I.5. The only remaining
validation note is the explicitly permitted stale generated `KAM.lean` lint
exception. No blocking finding remains in this delta audit.

| Signed endpoint / anchor | Verdict | Scope |
| --- | --- | --- |
| `KAM.SpinOrbit.SoGraphCert` | PASS | Signed namespace and complete structure text match. |
| `KAM.SpinOrbit.checkSoGraph` | PASS | Signed namespace and header match; algorithm unchanged. |
| `KAM.SpinOrbit.soBarrier_of_cert` | PASS | Exact signed header with the correctly qualified carrier/checker; explicit-binder probe passes. |
| `KAM.SpinOrbit.soRotBarrier_of_cert` | PASS | Same; rotated endpoint probe passes. |
| Frozen provider / seal | N/A | No provider or frozen anchor is added or sealed by this package. |

## Authority, scope and delta

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the round-1 report, and
both AUDIT FOCUS and Round 2 in `SO-GRAPH-handoff.md`. Compared against the signed
`/root/code/KAM-inp/.drafts/design/SOSignaturesLunar.lean` §I.5 (lines 390–468),
whose namespace opens at line 237 and closes at line 538. The local design's §6
provides the graph/Cauchy context. This is the requested delta audit; the prior
mathematical review is retained where the verified delta leaves it unchanged.
The user's exact absolute output path overrides the brief's generic main-worktree
destination. No implementation file was edited.

Inspected the full three-dot diff: the two new Lean files (252 and 92 lines),
round-1 report (353 lines), and handoff (78 lines). The fix commit changes only
namespace/open lines and the stale docstring locator in the two Lean files
(+11/-14); the subsequent request adds seven handoff lines. The structure,
checker, and two model helpers move from `KAM.Certificate` to `KAM.SpinOrbit`.
Tests and fixtures follow that move. Existing production theorem names remain
in `KAM.SpinOrbit`.

An independent Python comparison removed block comments and namespace/open/end
lines, then normalized whitespace: the remaining declaration text is identical
between `9791e24a` and HEAD in each Lean file. Inspection of the raw delta
confirms that this normalization hides no statement/body/proof change. In
particular the model defaults, SOS residual payment, strict Cauchy margin,
open-strip argument, frequency scaling, and both barrier calls are unchanged.
Imports are unchanged; the landed `SoGraph.torus_of_rot` and
`soBarrier_of_exact_rotTorus` are used, not restated.

Fresh literal comparisons with the signed draft returned:

```text
SoGraphCert signed text equality: True
checkSoGraph signed text equality: True
soBarrier_of_cert signed text equality: True
soRotBarrier_of_cert signed text equality: True
KAM/SpinOrbit/Graph/Cert.lean declaration tokens unchanged excluding namespace/open/comments: True
KAM/SpinOrbit/Tests/GraphCert.lean declaration tokens unchanged excluding namespace/open/comments: True
```

For the structure this includes all fields in order. For the checker and theorems
it compares the header before `:=`, since the signed draft deliberately contains
placeholder bodies. This time the enclosing namespace also agrees, and a fresh
Lean probe resolves the signed qualified names. Thus the exact issue in round-1
F1, including the endpoint certificate carrier, is closed.

## Declaration review

All names below are now in `KAM.SpinOrbit`. `Cert` means
`KAM/SpinOrbit/Graph/Cert.lean`; `Tests` means
`KAM/SpinOrbit/Tests/GraphCert.lean`. PASS for unchanged mathematics incorporates
the round-1 review plus the independently verified delta and fresh checks below.

| Node / location | Declaration | Verdict | Reason |
| --- | --- | --- | --- |
| §I.5, Cert:40 | `SoGraphCert` | PASS | Signed qualified carrier restored; fields unchanged. |
| Derivative model, Cert:55 | `soGraphMonoModel` | PASS | Namespace moved; same DK (0,0) enclosure. |
| Action model, Cert:60 | `soGraphActionModel` | PASS | Namespace moved; same degree-zero action enclosure/defaults. |
| §I.5, Cert:66 | `checkSoGraph` | PASS | Signed name restored; same three SOS checks and strict margin. |
| Norm, Cert:77 | `norm_fst_apply_sub_le` | PASS | Unchanged coordinate/product max norm projection. |
| Norm, Cert:81 | `norm_snd_apply_sub_le` | PASS | Unchanged action projection. |
| Direction, Cert:85 | `realPt_one_zero` | PASS | Unchanged unit-vector identity. |
| Cauchy, Cert:90 | `soGraph_deriv_transfer` | PASS | Unchanged open-strip estimate and limiting argument. |
| Soundness, Cert:133 | `checkSoGraph_sound` | PASS | Same exact derivative/action bounds and paid residuals. |
| Exact torus, Cert:162 | `soGraph_exactTorus` | PASS | Same positive monotonicity, widened band, scaled Diophantine margin. |
| §I.5, Cert:215 | `soBarrier_of_cert` | PASS | Signed carrier/checker now resolve correctly; original consumer unchanged. |
| §I.5, Cert:235 | `soRotBarrier_of_cert` | PASS | Signed carrier/checker now resolve correctly; scaled Hamiltonian consumer unchanged. |
| Fixture, Tests:28 | `graphToyW` | PASS | Same finite rational weight candidate. |
| Fixture, Tests:30 | `graphToyPi` | PASS | Same finite rational pi enclosure candidate. |
| Fixture, Tests:32 | `graphToyCfg` | PASS | Same empty-advice configuration. |
| Fixture, Tests:35 | `graphToyCos` | PASS | Same conjugate-half cosine coefficients. |
| Fixture, Tests:37 | `graphToyK` | PASS | Same degree -1 angle and degree 0 action. |
| Fixture, Tests:40 | `graphToyParams` | PASS | Same total parameter record. |
| Fixture, Tests:44 | `graphToyBase` | PASS | Same graph-only carrier with placeholder torus fields. |
| Fixture, Tests:62 | `graphToy` | PASS | Same finite graph data. |
| Positive test, Tests:74 | `graphTest_pass` | PASS | Kernel computation still passes. |
| Rejection, Tests:78 | `graphTest_mono_fail` | PASS | Tightened monotonicity still rejected. |
| Rejection, Tests:82 | `graphTest_range_fail` | PASS | Both tightened action bounds still rejected. |
| Rejection, Tests:88 | `graphTest_margin_fail` | PASS | Insufficient strict Cauchy margin still rejected. |

## Definitions and hypotheses

`SoGraphCert` remains untrusted finite data: one base certificate, six rational
bounds/centres and three polynomial witnesses. No proof-valued field assumes the
conclusion. The two model definitions are concrete enclosure computations;
`checkSoGraph` is a kernel-reducible Boolean algorithm. The eight fixture
definitions remain total finite test data, with no claim that their placeholder
base is a passing torus certificate. No abbrev, choice-defined object, or new
premise is introduced by the move.

The same action exponent/default and optional component are used by model and
denotation; missing action means zero and missing exponent means degree zero.
The DK matrix's (0,0) entry exists by its construction. Round-1's whole-carrier
classification remains applicable. The arithmetic law classes are representation
laws; neither hard analytic premises nor conclusion-shaped hypotheses were
introduced. The displacement still transfers on the exact open strip, with
monotonicity `mono - disp/rhoInf > 0` and band `[pLo-disp,pHi+disp]`.

## Fresh independent validation

All Lean/Lake commands were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No clean, update, cache download or package mutation was performed.

### Targeted build and tests

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sograph KAM.SpinOrbit.Graph.Cert KAM.SpinOrbit.Tests.GraphCert
```

Exit 0. Relevant output:

```text
[inp-gate] slot 2 acquired 22:07:10 for KAM.SpinOrbit.Graph.Cert KAM.SpinOrbit.Tests.GraphCert
Build completed successfully (3325 jobs).
```

Only inherited warnings were replayed, from `KAM.ODE.Exit`,
`KAM.Certificate.Expr.Basic`, `KAM.Certificate.Arith.PiHigh`,
`KAM.Certificate.Sound.Static`, and `KAM.Certificate.Sound.Ham`.
Neither audited module emitted a warning. All four `decide +kernel` tests are
included in the tested module and in the kernel replay.

### Fully qualified signature, binder and axiom probe

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SoGraphAuditR2.lean
```

Exit 0. The probe imported the test module, checked both restored signed names,
and copied the two signed draft endpoint headers under fresh names, explicitly
qualifying `KAM.SpinOrbit.SoGraphCert` and `KAM.SpinOrbit.checkSoGraph`. Bodies:

```lean
by exact KAM.SpinOrbit.soBarrier_of_cert g hham hc hg hω hdio
by exact KAM.SpinOrbit.soRotBarrier_of_cert g hc0 hham hc hg hω hdio
```

For each endpoint, `example : type_of% @KAM.SpinOrbit.<endpoint> := @AuditR2_<endpoint>`
also elaborated. These verify actual resolved types and explicit binder order,
in addition to the literal signed-header checks. Frozen/provider seal probes
are inapplicable to this unfrozen helper package.

Exact name and axiom output:

```text
KAM.SpinOrbit.SoGraphCert (α : Type) : Type
KAM.SpinOrbit.checkSoGraph {α : Type} [CertArith α] (g : SoGraphCert α) : Bool
'KAM.SpinOrbit.norm_fst_apply_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.norm_snd_apply_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.realPt_one_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soGraph_deriv_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.checkSoGraph_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soGraph_exactTorus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soBarrier_of_cert' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotBarrier_of_cert' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.graphTest_pass' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.graphTest_mono_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.graphTest_range_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.graphTest_margin_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` or additional axiom occurs.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.Graph.Cert KAM.SpinOrbit.Tests.GraphCert
```

Exit 0. Complete output:

```text
replaying KAM.SpinOrbit.Tests.GraphCert
replaying KAM.SpinOrbit.Graph.Cert
```

### Lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1 solely for the generated root, an exception explicitly allowed by the
brief. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1381 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No other lint failure occurred. The generated root was not regenerated.

### Static hygiene and protected paths

Fresh masked-code scans of both Lean files found no forbidden proof escape,
resource override or banned ambient carrier. Both retain copyright/author
headers, `module`, public imports, module docstrings and public sections;
the production definitions remain in an `@[expose]` section. Line counts are
252 and 92; maximum widths are 100 and 94. All are within the required limits.

A fresh recursive source-import walk found 167 KAM modules, including 20 frozen
modules; all imported frozen modules have manifest state `SEALED`. There is no
provider import or DRAFT_SORRY import in the closure. This agrees with the
unchanged imports and clean axiom results.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit 0 with empty output. Generated files and protected paths were left
untouched. Scratch probes were removed after validation. The only persistent
auditor change is this report at the exact requested absolute path.

## Errata, deviations and remaining scope

- Round-1 F1 is resolved by restoring the signed namespace, without a signature
  amendment or additional premise. The fully qualified positive probes now pass.
- The stale `soGraph_transfer` docstring locator is corrected to the actual split
  `soGraph_deriv_transfer`, then `soGraph_exactTorus` (Cert:22–23).
- No new suspected source/blueprint defect or implementation deviation was found
  in this delta. No frozen statement was changed or newly sealed.
- This is a delta audit of F1, with fresh signature and hygiene validation. The
  unchanged analytic reasoning is covered by the round-1 report and the verified
  statement/body/proof preservation, rather than claimed as a new source audit.
- The passing toy tests remain graph-only. Concrete lunar torus certificates,
  passing full checks, the O1 window and final 3.3% confinement are outside this
  package's established result. No numerical lunar closure is inferred here.
