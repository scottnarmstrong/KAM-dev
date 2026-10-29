# N11-E2 independent package audit 2 (delta)

Overall verdict: **PASS WITH NOTES** (generated-root lint exception and existing source-locator notes).
Round 1 F1 is **CLOSED**: the combined
second Taylor display is now proved by `KAM.Nekhoroshev.ext_taylor_second`.
The four SIGNED declarations and their proofs are unchanged. No frozen anchor is sealed by this package.

## Scope and evidence

Audit date: 2026-10-28. HEAD `af8d6eb04ebdc3eaa1e7c49d091da0dc73a22be3`;
Round 1 baseline `e34782d24c4cadaf852dcd41ec2c37ba512269bb`;
comparison `inp` observed at `4a5b757e944936d0ae6e9269a1170dc7098e4240`.
Read the repository rules, PLAN, DECISIONS, external package-audit brief, AUDIT FOCUS,
Round 1 report, Round 2 fix handoff, N11 design and both design audits, relevant p11b
source/graph contracts, track-N partial statement and frozen partial-convex anchor.
This is a delta audit: unchanged proof analysis and nonblocking notes from Round 1
are carried forward after byte comparison, with fresh validation as recorded below.
The user's exact absolute destination overrides the generic brief's main-worktree destination.

`git diff inp...HEAD` includes Lie, Adjoint, inherited Bracket/VectorField and the
Round 1 audit/handoff documents. Only Lie and Adjoint receive a package verdict.
Git warns of multiple merge bases, selecting `7c254d1ada904dce883560fd988ff208b2edcb35`;
the other is `3fd1914def12280f375f18e1f5746c989f50de90`. No refs were changed.

`git diff e34782d2..HEAD` changes only Lie.lean: **58 insertions, zero deletions**.
The new block is Lie:192–249, immediately before the namespace/section terminators.
Removing precisely that block reproduces the baseline file byte for byte; Adjoint
is byte-identical. Thus “only appends” holds for declaration/proof content (the new
block is inserted before closing commands), rather than a literal append after EOF.

| Input | SHA-256 |
|---|---|
| Lie.lean | `715fc98c331902e8d8cfb251b57dae11cd018191ab8c175a745de40c8585bea5` |
| Adjoint.lean | `cbc5242f1419685ddea99538c4564432f44ea30dfab85dfe30dadf4ec6a1f852` |
| N11-LEAN-DESIGN.md | `f0fd0d111b6abd5c335a5ea144135a07b28be326f3d699f3c2761c46ad097609` |
| p11b-partial-nf.tex | `4005a51b99ed21cba7c6cbca27b8e70392f9d8d6c67d6b59fec9e25cac51232d` |
| Live external N11Signatures.lean | `fe33b7d1689fdfb8ea66242b975d2b44002039fc4aa25378313afc4bd59a8aeb` |
| Round 1 signatures, preserved in design Appendix A | `23bd2cc2645243b3357acccda6e04ff69fad4d055963010025c582f3c886a0e4` |

The live external signatures have unrelated changes (`flow` renamed `ext_flow`,
and `canonical_map` now includes `hc : 0 < b.c`). All four E2 headers match both
the Round 1 Appendix A pin and the live signatures after whitespace normalization.
Those unrelated interfaces are outside this audit's verdict.

## Declaration and node ledger

All unqualified declarations are in `KAM.Nekhoroshev`. B denotes
`blueprint-N/parts/p11b-partial-nf.tex`.

| Node / declaration | Location | Verdict | Evidence |
|---|---|---|---|
| SIGNED `ext_taylor_regular` | Lie:110 | PASS | Exact signature retained; smoothness and every within derivative. |
| SIGNED `ext_taylor` | Lie:119 | PASS | Exact signature retained; orientation, finite sum, integral kernel. |
| SIGNED `ext_taylor_bound` | Lie:160 | PASS | Exact signature retained; uniform bound and factorial normalization. |
| SIGNED `adjoint` | Adjoint:211 | PASS WITH NOTES | Exact signature retained; Round 1 direct bracket estimate/provenance notes remain. |
| UNSIGNED `ext_taylor_second` | Lie:200 | PASS | Literal B:79–80 combined display; only the permitted hypotheses. |
| private `continuousOn_extAd_comp` | Lie:192 | PASS | Continuity derived from existing smoothness and holomorphic iterates. |
| `bpN:p11:ext-taylor` | Lie:39–247 | PASS | Prior regularity/formula/bound plus new second display complete the assigned clause. |
| `stepN:p11:et-one` | Lie:67,75 | PASS | Unchanged chain rule and continuity argument; Round 1 carried forward. |
| `stepN:p11:et-ind` | Lie:58,75,93 | PASS | Unchanged holomorphic/smoothness/within-derivative induction. |
| `stepN:p11:et-taylor` | Lie:119,160,200 | PASS | Both displays now proved; F1 CLOSED. |
| `bpN:p11:adjoint` | Adjoint:211 | PASS WITH NOTES | Unchanged full iterative estimate and normalized bound. |
| `stepN:p11:ad-setup` | Adjoint:126 | PASS | Unchanged divided losses and induction. |
| `stepN:p11:ad-step` | Adjoint:73,105 | PASS | Unchanged direct estimate at exact output radius. |
| `stepN:p11:ad-prod` | Adjoint:126,186,211 | PASS | Unchanged factorial quotient/product and exponential estimate. |

## F1 disposition and adversarial proof review

B:79–80 and graph `bpN:p11:ext-taylor` SOURCE_CONCLUSION require

```text
(h+f₀)(γ 1) = h z + {h,φ}_c z + f₀ z
  + ∫₀¹ {(1−t){h,φ}_c + f₀, φ}_c (γ t) dt.
```

`stepN:p11:et-taylor` explicitly requires “the two displays”
(DEPGRAPH.md:16074). Lie:200–207 states exactly this conclusion, including the
bracket of the time-dependent observable, original field, time interval, order of
summands and bracket orientation. Pointwise function addition makes `(h + f₀)`
literal; the scalar `(1-t)` is cast from real to complex without changing time.

The premises are open Ω, holomorphic φ and h, the existing solution-in-Ω on
Icc 0 1, plus holomorphic f₀ and `γ 0 = z`. There is no extra smallness,
nondegeneracy, norm, dimension, integrability or conclusion-shaped premise.
`z ∈ Ω` follows from the solution at 0 and hz; it need not be assumed separately.
The order parameter is specialized to 2 and 1, with its inequalities discharged internally.

The proof applies `ext_taylor` with N=2 to h and N=1 to f₀. Holomorphy of
`{h,φ}_c` is derived. At each curve point, membership in open Ω gives actual
complex differentiability, justifying `fderiv_fun_add` and `fderiv_const_mul`.
Thus linearity is not asserted for junk off-domain fderiv values. Continuity of
the bracket iterates along γ gives interval integrability of each weighted term;
`integral_add` is applied with these proofs. Pointwise bracket linearity identifies
the integrand, and ring arithmetic combines the Taylor identities. No hard step
is supplied as a hypothesis. The new private helper derives, rather than assumes,
continuity from existing `contDiffOn_comp` at order zero.

Definition classification: **none**. Neither file adds a def, abbrev or structure;
the delta adds two proof declarations only. Existing EC, extBracket, extAd and
IsSolutionIn retain their literal carriers/meaning. No norm or constant changes.
No repeated public helper short name, root declaration, harmful shadow or global
instance is introduced. A production-tree declaration scan finds each of the five
public short names exactly once; the new private helper name also occurs once.

## Independent validation

Every Lean/Lake command was sequential with `LEAN_NUM_THREADS=1` and niceness 5;
the build wrapper itself executes `nice -n 5 lake build`. No heartbeat override,
cache download, dependency update or clean was used.

1. Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-n11e2 KAM.Nekhoroshev.Partial.Lie KAM.Nekhoroshev.Partial.Adjoint
```

Exit 0, after waiting for the shared gate. Output includes:

```text
[inp-gate] slot 2 acquired 21:42:57 for KAM.Nekhoroshev.Partial.Lie KAM.Nekhoroshev.Partial.Adjoint
Build completed successfully (3247 jobs).
```

Targets were replayed from cache. Only unused-variable warnings were reported:
Lie:160–162 (`hΩ`, `hφ`, `hu`, `hγ`) and inherited Gradient:168 (`hgr`).
No elaboration failure or heartbeat design signal.

2. Exact signatures, explicit applications, and axioms:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11E2Audit2.lean
```

Exit 0, no warnings/errors. The probe extracted each signed header from the live
external signatures, renamed it, and proved it by application to all explicit
binders in order. For each, both `example : type_of% @expected := @actual` and its
reverse elaborated. An independently written example of the literal combined
Taylor display elaborated by `exact ext_taylor_second hΩ hφ hh hf hγ hz`.
The external placeholder proofs were not imported. Exact axiom output:

```text
'KAM.Nekhoroshev.ext_taylor_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.ext_taylor' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.ext_taylor_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.ext_taylor_second' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Nekhoroshev.Partial.Lie KAM.Nekhoroshev.Partial.Adjoint
```

Exit 0. Complete output:

```text
replaying KAM.Nekhoroshev.Partial.Adjoint
replaying KAM.Nekhoroshev.Partial.Lie
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely for the expressly permitted stale generated-root exception.
Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (922 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No generated file was regenerated. No other lint failure occurred.

5. Diff and cleanup checks:

```sh
git diff inp...HEAD
git diff e34782d2..HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
git diff --check
```

The full comparison, delta, protected-path result and whitespace checks are
recorded above. The scratch probe was removed after validation. Final working-tree status contains
only this untracked report. The report has no trailing whitespace and ends with a newline;
`git diff --check` exits 0. No remaining required package check is UNCHECKED.

Static checks: Lie 252 lines, maximum width 100; Adjoint 253 lines, maximum width 97.
Both satisfy the module conventions, with copyright, module, public import,
module docstring and exposed public noncomputable section. Forbidden token and
resource-override scans of both files return no matches. Import closure has 73
local modules, 21 frozen definition modules, no provider and no frozen theorem.
No DRAFT_SORRY theorem is imported. Protected-path three-dot diff is empty;
`git diff --check inp...HEAD` exits 0 (apart from the disclosed merge-base warning).

## Notes, uncertainties and limits

- The existing graph locator defect remains: DEPGRAPH.md:15715 quotes
  `adjoint@L69-L86`, although the proof ends at B:73; B:75–86 is Taylor.
  DEPGRAPH.md:15731 quotes the product edge as `L72-L85`, overreaching B:72.
  These stale locators do not invalidate the formulas; no graph/source was edited.
- The adjoint implementation still applies the bracket with the iterate first
  and generator second, using a direct constant estimate instead of source B:71's
  antisymmetry route. Round 1's justification is carried forward unchanged.
- No new suspected pinned-source mathematical defect or implementation deviation
  was found. This audit checks the local blueprint contracts, not external PDFs.
- No provider/frozen-type seal probe is applicable: E2 is an infrastructure
  package. The frozen `partialConvex_nekhoroshev` body remains `by sorry`.
  Package acceptance does not seal that theorem or close the N11 campaign.
- Only this report is a persistent audit edit. Temporary probes are confined to
  this worktree's `.lake/abi-scratch/` and removed after validation; no production,
  frozen, manifest, generated root or README edits are authorized or performed.

## Lane-pause handoff

The orchestrator requested wrap-up while source lint was running. That existing
verification was allowed to finish; its frozen-anchor and ABI checks both passed.
No further Lean checks or lane work were started. The report is complete at the
requested worktree path. External PDF re-audit and later consumer/campaign closure
are UNCHECKED and outside this delta audit; no claim about them is made.
