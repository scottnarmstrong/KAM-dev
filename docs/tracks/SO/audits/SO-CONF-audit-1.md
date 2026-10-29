# SO-CONF independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-soconf`.
Audited HEAD: `e4edfebe5bd1c02c740c627c4e018fec837d658c`.
Comparison ref `inp`: `8aa7e422c350037616af06004f80f76bc5087771`.

**Verdict: PASS WITH NOTES.** The SO-CONF slice is complete and its signed declarations
match the draft exactly. No mathematical or proof blocker was found. The generated root
is stale, the expressly permitted lint exception. This is unfrozen implementation code;
there is no frozen anchor or provider to seal in this package.

## Scope and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the local
`docs/tracks/SO/audits/SO-CONF-handoff.md`, including AUDIT FOCUS.
The user's exact report destination overrides the generic brief's main-worktree destination.
Audit scope is only `KAM/SpinOrbit/Barrier.lean`; inherited ODE/model definitions were read
to check applicability, rather than independently re-audited as packages.

SO-specific authority:

- `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md`, Revision 3,
  especially lines 336–339 (barrier argument), 379 (module boundary), 410 (package),
  and Appendix A §I.
- `/root/code/KAM-inp/.drafts/design/SOSignatures.lean`, lines 1265–1272 (`SoBarrier`)
  and 1302–1307 (`so_confinement`). SHA256:
  `4998870ab6e4f1d8dd8da16a7a01f71b733e7b842b80894e8beedf57d6304fb8`.
- `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md`, global existence,
  continuous barriers and owner ruling O1. There is no local SO `statement.md` or
  `blueprint-SO/`; the handoff's named design and signatures supply this package's contract.

`git diff inp...HEAD` contains exactly one addition: `KAM/SpinOrbit/Barrier.lean`, 232 lines.
The pre-existing untracked handoff was left untouched. No frozen anchor is used or changed.

## Declaration review

All names below are in `KAM.SpinOrbit`; line references are in `Barrier.lean`.
There are ten explicit public declarations and four private proof helpers.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| SO-CONF signed graph data | `SoBarrier` (36) | PASS | Structure block is text-identical to the draft, including field order, carriers and actual-field invariance. Generated projections/constructor introduce no extra assumptions. |
| Field regularity | `soVq_contDiff` (47) | PASS | Proves C¹ regularity of the finite sine sum on the actual real product carrier. |
| Field regularity | `soField_contDiff` (51) | PASS | Uses `soField_eq`, preserving the derivative-defined physical field. |
| Force constant | `soForceBound` (58) | PASS | Exact finite sum `4π ε Σ |A_m|`; no extra parameter dependence. |
| Force constant sign | `soForceBound_nonneg` (60) | PASS | Proved from the model's positive epsilon. |
| Force estimate | `soVq_abs_le` (65) | PASS | Uniform for every real q and φ; absolute-sum and sine bounds, no domain premise. |
| A priori radius | `soRadius` (100) | PASS | Explicit polynomial bound in N and T, with the fixed force constant. |
| A priori estimate | `soSolution_norm_le` (102) | PASS | Any actual solution on an order-connected interval containing 0, for either sign of t. `|t| ≤ T` implies the needed nonnegative T. |
| Global existence / uniqueness | `so_global_exists_unique` (157) | PASS | Every real initial point has a solution on all real times, unique among all global solutions with those data; no barrier or lunar-band premise. |
| SO-CONF signed theorem | `so_confinement` (194) | PASS | Exact signed binders and conclusion; strict inequalities for every real t, plus global existence and uniqueness. |
| Private integration helper | `abs_sub_le_of_hasDerivAt` (76) | PASS | Mean value bound on the unoriented interval `uIcc 0 t`. |
| Private interval helper | `abs_le_of_mem_uIcc` (84) | PASS | Controls intermediate times for positive and negative t. |
| Private derivative projection | `hasDerivAt_fst'` (90) | PASS | Standard product projection by chain rule; private name. |
| Private derivative projection | `hasDerivAt_snd'` (95) | PASS | Standard product projection by chain rule; private name. |

The unsigned public helpers implement the proof route rather than replacing signed results.
They have no extra unproved analytic premises or conclusion-shaped instances.
No independently signed global-Lipschitz lemma is required by the signature file.

## Definitions and proof soundness

`SoBarrier` is a genuine data structure of continuous, doubly 1-periodic real graphs,
with range bounds and invariance for `soField` on the entire physical state space.
At `KAM/ODE/Exit.lean:107`, `IsInvariantSet F W S` quantifies over actual solutions on
order-connected time sets: membership in S at any time implies membership at every time
of that solution. At `KAM/ODE/Basic.lean:43`, those solutions satisfy
`HasDerivAt z (F (z t)) t`. Thus the input property concerns motion **on each graph**;
it does not assume confinement in the intervening slab or global existence.
Inconsistent range parameters merely make the structure uninhabited, as intended.

`soForceBound` is the intended nonnegative numerical force bound on its whole carrier
(a fixed real constant). `soRadius : ℝ → ℝ → ℝ` is the stated polynomial everywhere,
without branches, junk values or fallbacks. It is used as a radius only with
`N = ‖y 0‖ ≥ 0` and `T ≥ |t| ≥ 0`; no positivity claim is made for arbitrary negative inputs.
There are no other new explicit definitions, abbreviations or structures.

The component estimates prove
`|φ(t)| ≤ N + T`, `|p(t)| ≤ N + A*T`, and
`|q(t)| ≤ N + (N + A*T)*T`. Their sum bound controls the nested product max norm.
This supplies, rather than assumes, the universal a priori confinement premise of
`gen_confinement`. For every positive τ, compact-ball uniform data and maximal-solution
uniqueness identify endpoints beyond ±τ with those of the same maximal solution.
The endpoints are then proved to be bottom/top in `EReal`; global uniqueness follows
from `gen_uniqueness` on `univ`.

For confinement, continuity makes the strict slab open. Its closure has the two weak
inequalities, so every boundary point lies on one of the two graphs (lines 206–223).
Their union is invariant under the actual field, and the initial strict inequalities
exclude it. `gen_barrier` is used with both the time domain and state domain `univ`;
its implementation at `KAM/ODE/Exit.lean:140–161` covers both time directions.
There is no global ordering premise on the graphs. This is stronger than requiring
an ordered pair everywhere and remains valid: any boundary encounter would force
the solution back onto a graph at time zero, contradicting the strict initial data.

The complete SO-CONF slice is present: signed graph structure, global physical ODE
solution and uniqueness, and strict two-barrier confinement for all real times.
Graph construction from certificates and the concrete lunar momentum window belong
to downstream modules; O1 does not alter this general signed theorem.

## Independent checks

All Lean-bearing commands below were run sequentially with `LEAN_NUM_THREADS=1`
and `nice -n 5`. No concurrent Lean/Lake process was launched by this audit.

### Targeted compile gate

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-soconf KAM.SpinOrbit.Barrier
```

Exit 0. Output:

```text
[inp-gate] slot 1 acquired 12:10:13 for KAM.SpinOrbit.Barrier
⚠ [2884/2889] Replayed KAM.ODE.Exit
warning: KAM/ODE/Exit.lean:36:0: automatically included section variable(s) unused in theorem `KAM.ODE.gen_exit`:
  [NormedSpace ℝ E]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NormedSpace ℝ E] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Build completed successfully (2889 jobs).
```

The warning is inherited and outside the audited file. No warning suppression was added.

### Exact signed statement and axiom probe

Python extracted the structure block and the theorem statement through its pre-body
`:=` delimiter from both source and draft, with results:

```text
SoBarrier exact text: True
so_confinement exact signature text: True
```

The temporary `.lake/abi-scratch/SOConfAudit.lean` imported only
`KAM.SpinOrbit.Barrier`. It copied the draft theorem under the fresh name
`SOConfAudit.signed_so_confinement`, using this body:

```lean
by exact KAM.SpinOrbit.so_confinement B₁ B₂ x₀ h₁ h₂
```

It also checked both type directions:

```lean
example : type_of% @signed_so_confinement := @KAM.SpinOrbit.so_confinement
example : type_of% @KAM.SpinOrbit.so_confinement := @signed_so_confinement
```

Command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOConfAudit.lean
```

Exit 0. The probe issued `#print axioms` for every explicit new public theorem;
its complete Lean output was:

```text
'KAM.SpinOrbit.soVq_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soField_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soForceBound_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soVq_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soSolution_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.so_global_exists_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.so_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.Barrier
```

Exit 0. Complete output:

```text
replaying KAM.SpinOrbit.Barrier
```

### Source lint and protected paths

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the expressly permitted generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1291 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No other lint failure was reported. The generated root was not regenerated.

```sh
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Both exit 0 with empty output. The full three-dot diff adds only the audited module.
The module has the copyright header, `module`, four `public import` lines, module
docstring and `@[expose] public noncomputable section`. It has 232 total lines;
maximum Unicode line length is 98. No forbidden proof escape, `native_decide`,
resource override or `EuclideanSpace` occurs. All ten explicit public declaration
short names were searched across the other `KAM/**/*.lean` files: no duplicate
declaration was found. Every declaration is in `KAM.SpinOrbit`; no harmful root
shadow or reused public helper short name was found. The four generic helpers
are private.

The recursively inspected KAM import closure is:

```text
KAM.ODE.Basic
KAM.ODE.Continuation
KAM.ODE.Existence
KAM.ODE.Exit
KAM.ODE.Lipschitz
KAM.ODE.Maximal
KAM.ODE.UniformPeriodic
KAM.ODE.Uniqueness
KAM.SpinOrbit.Barrier
KAM.SpinOrbit.Model
```

There are no provider or frozen-module imports, hence no `DRAFT_SORRY` anchor
exposure and no imported frozen state to qualify.

## Notes, uncertainties and deviations

No suspected mathematical source defect, frozen-statement defect or signed-surface
deviation was found in scope. No external pinned-paper assertion is needed by
this elementary ODE/barrier slice.

One proof-route difference should be recorded: design lines 73–74, 336–338 and the
draft comment at 1299–1300 say global existence is obtained from the
“global Lipschitz bound of `soField`”. The implementation instead proves bounded
force and an explicit finite-time growth bound, then uses compact continuation
and C¹ local uniqueness. It exports no global Lipschitz constant. This is a valid
alternative proof of the exact signed conclusion, with no added premise and no
missing signed declaration; it is not a mathematical erratum.

`SoBarrier` is placed in `Barrier.lean`, matching the design's module DAG at line
379 and the handoff, although the draft groups its text under the Graph heading.
Downstream Graph modules must import this structure rather than redeclare it.

No repository file except this report was edited by the auditor. The temporary
audit probe was deleted after checking. Generated files, frozen files and the
manifest were left untouched; no state-changing git command was run.
