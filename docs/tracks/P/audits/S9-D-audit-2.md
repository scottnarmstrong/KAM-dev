# S9-D independent package audit 2 — delta audit

Overall verdict: **PASS WITH NOTES**. Round-1 finding **F1 is CLOSED**. The package's mathematical PASS is retained: exactly one qualified identifier in one proof changed; all statements, signatures, definitions, imports and other proofs are byte-identical to the round-1 baseline. Fresh build, kernel replay and axiom checks pass. The only lint diagnostic is the brief's permitted stale generated-root exception. The inherited triple-dot protected-path difference is recorded below. This is infrastructure: **no frozen anchor to seal**.

Audited HEAD `11308d4a8a074eb72aed419d6b0a4b0a238134e7`; baseline `b1125719ab31063ede93e405032d37fade8ee12c`; live comparison ref `inp` = `81bb576d2ebe1ee5c4cb309059b68d4b24148218`.
Report destination is `/root/code/KAM-inp-s9d/docs/tracks/P/audits/S9-D-audit-2.md`, as explicitly directed by the user, overriding the generic brief's main-worktree destination.

## Scope and evidence

Read the repository rules, PLAN and DECISIONS, the assigned package-audit brief, S9-D handoff and audit 1, relevant track-P conventions, P810 design row S9-D and associated design-audit findings, the current reference signatures, and blueprint P9 lines 69–103. Reviewed the three package modules. This round is a delta audit, not a repetition of the complete round-1 mathematical/source audit. Its unchanged proof and definition findings are carried forward on the basis of exact byte comparison; current signatures and validation were checked independently.

Scope is exactly:

- `KAM/Planetary/SecularSpectrum/Definiteness.lean` (247 lines).
- `KAM/Planetary/SecularSpectrum/Definiteness/Hadamard.lean` (107 lines).
- `KAM/Planetary/SecularSpectrum/Definiteness/Laplace.lean` (135 lines).

The reference `/root/code/KAM-inp/.drafts/design/P810Signatures.lean` has SHA-256 `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`, unchanged from round 1/design audit 2. A fresh whitespace-normalized comparison of the complete signatures of `l74`, `l75`, `l75_bound` and `definite` passes, including the entire let-bound `cHat` conclusion. No provider/frozen theorem signature or seal-body probe applies.

## Exact delta and F1 closure

Commands:

```sh
git diff b112571 HEAD
git diff --word-diff=porcelain b112571 HEAD
```

The entire repository delta contains only this hunk, in `Definiteness.lean:104`:

```diff
-    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
+    rw [PiLp.norm_eq_of_L2, Real.sqrt_eq_one] at h
```

An independent Python assertion checked the complete changed-path list equals just this module and checked its entire current text equals the baseline text with exactly one occurrence of `EuclideanSpace.norm_eq` replaced by `PiLp.norm_eq_of_L2`. Output:

```text
DELTA EXACT: one identifier replacement in Definiteness.lean:104; all other tracked bytes unchanged.
```

Thus no statement, signature, hypothesis, definition, import, other proof, frozen file, manifest, generated file or documentation changed in the fix commit. It is exactly one qualified-identifier replacement (the requested one-token change).

The local Mathlib theorem `PiLp.norm_eq_of_L2`, in `Mathlib/Analysis/Normed/Lp/PiLp.lean:780`, states `‖x‖ = √(∑ i, ‖x i‖ ^ 2)` for `x : PiLp 2 β`. Applied to the existing real unit eigenvector it proves the same sum-of-squares normalization. The ambient Pi carriers, explicit `length2`, sorted spectrum, Rayleigh quotient and quantitative coercivity conclusion are unchanged. No new mathematical premise is introduced.

```sh
rg -n 'EuclideanSpace' KAM/Planetary/SecularSpectrum/Definiteness.lean KAM/Planetary/SecularSpectrum/Definiteness
```

Exit 1, no output: no occurrence anywhere in the package modules, including comments. The full repository lint independently reports no forbidden-EuclideanSpace line. Historical audit/rule prose may still name the identifier; that prose is not package Lean code.

## Declaration inventory

All names have prefix `KAM.Planetary.SecularSpectrum`. Rows below retain the round-1 mathematics/statement findings for unchanged declarations; the repaired helper is independently built and kernel-replayed.

| Node / role | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| Hadamard row deficit | `dominance` (Hadamard:29) | PASS | Literal negative diagonal minus off-diagonal row sum; signed body unchanged. |
| l75 expansion helper | `erase_eq_union` (Hadamard:31) | PASS | Strict upper/lower partition of erased finite index set. |
| l75 expansion helper | `sum_erase_split` (Hadamard:40) | PASS | Each unordered pair counted once with both orientations. |
| l75 expansion helper | `sum_sum_split` (Hadamard:55) | PASS | Diagonal plus upper-triangle paired terms. |
| bpP:p9:l75 / stepP:p9:l75 | `l75` (Hadamard:64) | PASS | Exact signed identity; real Hermitian symmetry; no off-diagonal sign needed for equality. |
| bpP:p9:l75 consequence | `l75_bound` (Hadamard:92) | PASS | Nonnegative off-diagonal terms and literal row lower bound; arbitrary c is valid. |
| l74 positivity helper | `lap_base_pos` (Laplace:27) | PASS | Base bounded below by (1−α)² for 0<α<1. |
| l74 integrability helper | `lap_integrand_continuous` (Laplace:31) | PASS | All real s and integer modes; positive base justifies rpow continuity. |
| stepP:p9:l74-red | `laplace_def_eq_half` (Laplace:37) | PASS | Reflection about π; correct 1/π normalization from 1/(2π). |
| l74 difference helper | `laplace_def_sub_eq` (Laplace:60) | PASS | Difference of integrals with integrability supplied. |
| stepP:p9:l74-ibp | `ibp_formula` (Laplace:73) | PASS | H=sin(t)(1−cos(t)), H′=cos(t)−cos(2t); endpoints vanish; correct derivative sign and factor. Valid for all real s. |
| bpP:p9:l74 | `l74` (Laplace:109) | PASS | Exact signed formula and strict positive integral for s>0, 0<α<1. |
| coercivity constant | `coercivity` (facade:33) | PASS | Literal finite infimum of pair gaps divided by maximum action. |
| stepP:p9:p73-dom helper | `ratio_mem` (facade:37) | PASS | Positive strictly ordered axes imply pair ratio in (0,1). |
| stepP:p9:p73-dom helper | `pairA_sub_pairB_pos` (facade:41) | PASS | Exact common physical prefactor times l74 difference at s=3/2. |
| stepP:p9:p73-had helper | `pairB_nonneg` (facade:53) | PASS | S8-L positivity supplies the dropped square-term sign. |
| matrix symmetry | `qhat_hermitian` (facade:65) | PASS | Literal qhat, no axes restriction necessary. |
| off-diagonal identification | `qhat_off` (facade:72) | PASS | Unfolds the correct branch under i≠j. |
| stepP:p9:p73-dom | `dominance_qhat` (facade:76) | PASS | Identifies row deficit with the literal gap sum. |
| strict row gap | `gap_pos` (facade:84) | PASS | n≥2 supplies a nonempty erased set; every summand positive. |
| congruence denominator | `action_pos` (facade:90) | PASS | Only positive masses, G and axes used. |
| eigenvalue transfer | `quad_eigen_le` (facade:93) | PASS | Genuine sorted eigenvalue and unit eigenvector Rayleigh quotient; F1 closed by the permitted PiLp normalization at line 104. Its assumed quadratic estimate is appropriate for this distinct generic helper and is proved by its consumer. |
| continuity helper | `continuousAt_pair` (facade:121) | PASS | Positive denominator and S8-L analytic Laplace function on (0,1). |
| continuity helper | `continuousAt_gap` (facade:137) | PASS | Finite sum of pair differences, diagonal excluded. |
| continuity helper | `continuousAt_coercivity` (facade:144) | PASS | Finite nonempty infimum/supremum and positive action denominator. |
| bpP:p9:definite; p73-dom/had/cong | `definite` (facade:169) | PASS | Returns positive cHat, both qhat inequalities, positive coercivity, scaled bound, all sorted eigenvalue bounds, and continuity. Uses the repaired helper; statement and remaining proof unchanged. |


## Definitions, premises and dependencies

`dominance` is the literal algebraic row deficit on all real square matrices; no branch or fallback is used. `coercivity` is the intended total real finite-infimum/finite-supremum quotient. Outside positive ordered axes or for empty dimension its totalized operations do not assert positivity. On the theorem's `n ≥ 2`, `a ∈ axes n` domain, nonempty extrema and positive denominators are proved. Both definitions are byte-identical to round 1; there are no new structures or abbreviations.

There are no new premises, instances or bundled fields. The main theorem uses positive physical data, `2 ≤ n` and positive ordered axes. The generic `quad_eigen_le` quadratic-bound premise remains an intermediate helper premise discharged by `definite`, as in round 1. The sign-free Hadamard identity remains the design's permitted stronger identity; its inequality retains the off-diagonal sign premise. S8-C, S9-N and S8-L are consumed through unchanged imports and proof applications.

A fresh recursive KAM import scan found 72 modules, including 47 frozen definition modules, **no provider imports, no frozen theorem imports and no DRAFT_SORRY marker** in those frozen dependencies. There is no frozen theorem SEALED-state exception to invoke.

## Fresh independent validation

All auditor-controlled Lean/Lake jobs ran sequentially, with `LEAN_NUM_THREADS=1` and `nice -n 5` (the gate wrapper applies `nice` internally). Lint ran only after the preceding kernel job finished, because its ABI checker may invoke Lean. No resource override was used.

Targeted gated build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s9d KAM.Planetary.SecularSpectrum.Definiteness
```

Exit 0. Key exact output:

```text
[inp-gate] slot 1 acquired 13:10:19 for KAM.Planetary.SecularSpectrum.Definiteness
Build completed successfully (9118 jobs).
```

Lake replayed the current artifacts. Existing warnings were unused variables in Kepler/Energy, Poincare/Chart and Kepler/Mass, deprecated `ite_cond_eq_false` in Coefficients, and package warnings at Definiteness:70 (deprecated `if_neg`) and :86 (`haveI` style). No new warning is associated with line 104.

Axiom probe (24 `#print axioms` commands, one for each public lemma/theorem in the three modules):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S9DAudit2.lean
```

Exit 0. Exact output:

```text
'KAM.Planetary.SecularSpectrum.ratio_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.pairA_sub_pairB_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.pairB_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.qhat_hermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.qhat_off' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.dominance_qhat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.gap_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.action_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.quad_eigen_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.continuousAt_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.continuousAt_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.continuousAt_coercivity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.definite' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.erase_eq_union' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sum_erase_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sum_sum_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.l75' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.l75_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.lap_base_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.lap_integrand_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.laplace_def_eq_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.laplace_def_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.ibp_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.l74' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only standard axioms occur; no `sorryAx` or unapproved axiom appears.

Kernel replay (one invocation):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularSpectrum.Definiteness KAM.Planetary.SecularSpectrum.Definiteness.Hadamard KAM.Planetary.SecularSpectrum.Definiteness.Laplace
```

Exit 0. Exact output:

```text
replaying KAM.Planetary.SecularSpectrum.Definiteness.Laplace
replaying KAM.Planetary.SecularSpectrum.Definiteness.Hadamard
replaying KAM.Planetary.SecularSpectrum.Definiteness
```

Repository lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely for the permitted stale generated root. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (649 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The stale-root diagnostic is the audit brief's explicit exception; it is not a fresh package failure. No forbidden identifier/proof escape/resource override, overlong source line or oversized Lean module is reported. All three modules retain the copyright header, `module`, public imports, module docstring and exposed public noncomputable section. Frozen and ABI guards pass.

## Triple-dot comparison and protected paths

The requested `git diff inp...HEAD` was inspected with scope restricted to the three package modules. Git warns:

```text
warning: inp...HEAD: multiple merge bases, using 2c0f61b7b3c64df75621893f5f40bae338d7a580
```

`git merge-base --all inp HEAD` returns:

```text
2c0f61b7b3c64df75621893f5f40bae338d7a580
722ad4a37de68b025a0c690051afff665dcb1176
```

```sh
git diff --numstat inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Exit 0, with the same merge-base warning and exactly `94	0	KAM.lean`. Thus the brief's literal empty protected-path triple-dot condition remains unsatisfied by the inherited generated-root difference already recorded in round 1; no frozen, manifest or README difference occurs. This preexisting integration note is unchanged by the fix, not silently described as an empty comparison.

```sh
git diff --exit-code b112571 HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD -- KAM/Planetary/SecularSpectrum/Definiteness.lean KAM/Planetary/SecularSpectrum/Definiteness
git diff --check
```

All exit 0, with no output except the triple-dot merge-base warning on the scoped check. The exact-delta assertion additionally rules out every unrelated change since the baseline.

## Source defects, deviations and limits

No new suspected blueprint/pinned-source defect or implementation deviation was found. F1's forbidden identifier has been removed. Round-1 mathematical findings are retained on an exact-delta basis; this report does not claim a new pinned-PDF audit, frozen-anchor closure or completion of track P. The existing upstream Norms docstring sorting-direction note from round 1 is unchanged and outside scope.

Only this report was added to the repository. No production source, frozen file, manifest, README or generated root was edited; no commit, index or ref was changed. Temporary auditor probes/logs under `.lake/abi-scratch/` were removed after incorporation. The allowed stale-root lint exception and inherited generated-root triple-dot difference are the only remaining notes.
