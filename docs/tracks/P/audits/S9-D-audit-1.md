# S9-D independent package audit 1

Overall verdict: **FAIL (repository hygiene)**. The mathematical statements and reviewed proof arguments pass; the package violates the explicit `EuclideanSpace` prohibition at `KAM/Planetary/SecularSpectrum/Definiteness.lean:104`. This is infrastructure, with **no frozen anchor to seal**. No conclusion-shaped premise or mathematical counterexample was found.

Audited HEAD `c672945763ba0693704c802644c40ea5a3c4f8fc`, branch `inp-s9d`; comparison ref `inp` was `31f0bfbf70c07b1eefd006237f331c00e003a0e5`. Scope is exactly:

- `KAM/Planetary/SecularSpectrum/Definiteness.lean` (247 lines).
- `KAM/Planetary/SecularSpectrum/Definiteness/Hadamard.lean` (107 lines).
- `KAM/Planetary/SecularSpectrum/Definiteness/Laplace.lean` (135 lines).

Read AGENTS.md, PLAN.md, DECISIONS.md, the assigned package-audit brief and S9-D handoff, track-P statement conventions, P810 design row S9-D and signatures, design audits 1–2, and blueprint P9 lines 69–103. Inspected the actual S9-N/S8-C/S8-L definitions and exports consumed here and the relevant frozen definition interfaces. The signature file is absent from this worktree, so the reference was read from `/root/code/KAM-inp/.drafts/design/P810Signatures.lean`, SHA-256 `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`, matching design audit 2. The design audits are under `docs/tracks/P/design/`, rather than the handoff's `audits/` directory. Their main-worktree copies match the local files.

## Blocking finding

**F1 — explicit forbidden carrier API; lint failure.** `Definiteness.lean:104` says:

```lean
rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
```

AGENTS.md rule 7 says “Ambient types: `Fin n → ℝ`, `Fin n → ℂ`, Fourier indices `Fin n → ℤ`. Never `EuclideanSpace`.” `scripts/lint_sources.sh` explicitly rejects this identifier anywhere in code. The unit eigenvector used immediately above is Mathlib's Euclidean eigenvector; coercing it into the Pi carrier preserves the scalar calculation, so this is not evidence of a false eigenvalue bound. It nevertheless fails the literal repository rule and required lint gate. Refactor the unit-eigenvector normalization through a permitted coordinate/sum-of-squares interface, then rerun the package checks. No source edit was made by this auditor. The handoff's claim that the only lint message is stale `KAM.lean` is contradicted by the current code/check.

## Declaration and node inventory

All names below have prefix `KAM.Planetary.SecularSpectrum`. PASS assesses the declaration's mathematics and statement fidelity; the aggregate package remains FAIL for F1. Added technical helpers have their own names and prove intermediate facts rather than assuming the package conclusion.

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
| eigenvalue transfer | `quad_eigen_le` (facade:93) | FAIL hygiene / PASS mathematics | Genuine sorted eigenvalue and unit eigenvector Rayleigh quotient; F1 at line 104. Its assumed quadratic estimate is appropriate for this distinct generic helper and is proved by its consumer. |
| continuity helper | `continuousAt_pair` (facade:121) | PASS | Positive denominator and S8-L analytic Laplace function on (0,1). |
| continuity helper | `continuousAt_gap` (facade:137) | PASS | Finite sum of pair differences, diagonal excluded. |
| continuity helper | `continuousAt_coercivity` (facade:144) | PASS | Finite nonempty infimum/supremum and positive action denominator. |
| bpP:p9:definite; p73-dom/had/cong | `definite` (facade:169) | PASS statement/proof; FAIL package hygiene | Returns positive cHat, both qhat inequalities, positive coercivity, scaled bound, all sorted eigenvalue bounds, and continuity. Depends on F1 helper. |

## Statement fidelity and proof review

The declarations `l74`, `l75`, `l75_bound`, `definite` match the revised signature file after whitespace normalization, including the complete let-bound `cHat` conclusion of `definite`; the signed definitions `dominance` and `coercivity` also match. Fresh-name scratch declarations use the full reference theorem types and bodies `by exact l74 hs hα hα1`, `by exact l75 M hM x`, `by exact l75_bound M hM hOff hc x`, and `by exact definite D hn ha`. Two `rfl` probes check the definition bodies. No frozen provider-type or seal-body probe applies: there is no provider or frozen theorem implemented by S9-D.

The design-audit-1 F2 omission is repaired in this implementation: both unscaled bounds are actually conclusions. In `definite`, strict positivity is obtained by attainment of the finite minimum, never by a premise. The Hadamard square term has the required nonnegative coefficients. Congruence is literally `y i = x i / sqrt(action D a i)`, with positive action denominators and `length2 x² / maxAction ≤ length2 y²`; multiplying by negative cHat gives the correct inequality direction. The eigenvalue argument uses the reverse index required by S9-N's sorted spectrum. Finite extrema continuity uses genuine nonemptiness and a positive denominator. No matrix or norm surrogate is substituted.

S8-C supplies literal `pairA`, `pairB`, `qhat`, `coeffs` and `sigma`; S9-N supplies `length2` and `sorted`; S8-L supplies Laplace positivity and analyticity. The unguarded identity `l75` is stronger than the blueprint's sign-guarded identity, as the design explicitly permits; the inequality retains its sign guard. `l74` together with S8-L positivity also supplies the blueprint's b₂>0 corollary. Strict negative eigenvalues and 2*sigma<0 follow from the returned positive coercivity. No extra source premise, changed constant dependence, or lost quantifier was found.

## Definition classification and hypotheses

There are exactly two new definitions and no new structures/abbreviations:

- `dominance`: intended algebraic deficit on every real square matrix, including zero dimension; no branch or fallback.
- `coercivity`: intended total real expression. For nonempty finite indices its infimum/supremum are the minimum gap and maximum action. Outside positive ordered axes, or in dimension zero, totalized infimum/supremum/division may produce nonpositive/default values; no theorem claims positivity there or exploits those values. On the theorem's n≥2, a∈axes domain all extrema and denominators are justified explicitly.

`Data` contains positive physical/typing data only. The main theorem assumes exactly that data, n≥2 and membership in positive ordered axes. Helpers use genuine intermediate hypotheses; no hard source step is smuggled into a bundled field or typeclass. A recursive KAM import scan found **no provider and no DRAFT_SORRY anchor**; every transitive frozen import is a definition module. There is no imported frozen theorem needing a SEALED-state exception.

## Independent validation

All auditor-controlled Lean/Lake jobs were sequential and used `LEAN_NUM_THREADS=1`; Lean and kernel commands used `nice -n 5`, and the compile-gate wrapper invokes `nice -n 5 lake build` internally. No resource override was used.

Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s9d KAM.Planetary.SecularSpectrum.Definiteness
```

Exit 0. Output included `[inp-gate] slot 1 acquired 12:51:26 for KAM.Planetary.SecularSpectrum.Definiteness` and `Build completed successfully (9118 jobs).` It replayed preexisting unused-variable warnings in Kepler/Energy, Poincare/Chart and Kepler/Mass, deprecated `ite_cond_eq_false` in Coefficients, and package warnings at Definiteness:70 (deprecated `if_neg`) and :86 (`haveI` style). These warnings are separate from F1.

Signature/definition probes and axioms:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S9DAudit.lean
```

Exit 0 after correcting the auditor's initial extraction of the let-bound signature (the first scratch attempt had a parser error; no production defect). All four full reference-type applications and both definition-body probes elaborated at default settings. `#print axioms` was run for **all 24 new public lemmas/theorems**, with this exact output:

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
'KAM.Planetary.SecularSpectrum.lap_base_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.lap_integrand_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.laplace_def_eq_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.laplace_def_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.ibp_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.l74' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.erase_eq_union' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sum_erase_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sum_sum_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.l75' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.l75_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` or unapproved axiom occurs.

Kernel replay (one invocation):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularSpectrum.Definiteness KAM.Planetary.SecularSpectrum.Definiteness.Hadamard KAM.Planetary.SecularSpectrum.Definiteness.Laplace
```

Exit 0, exact output:

```text
replaying KAM.Planetary.SecularSpectrum.Definiteness.Laplace
replaying KAM.Planetary.SecularSpectrum.Definiteness.Hadamard
replaying KAM.Planetary.SecularSpectrum.Definiteness
```

Repository lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, exact output:

```text
forbidden EuclideanSpace in code (use `Fin n → ℝ`; see AGENTS.md):
/root/code/KAM-inp-s9d/KAM/Planetary/SecularSpectrum/Definiteness.lean:104
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (649 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The stale-root line is the brief's permitted exception; the forbidden EuclideanSpace line is **not**. No forbidden proof escape, resource override, over-100-character line or oversized file was reported. All three files have copyright headers, `module`, public imports, module docstrings and exposed public noncomputable sections. Frozen guard and ABI hashes pass. Lint therefore fails for the concrete new F1 in addition to the permitted generated-root exception.

Protected-path and diff checks:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff HEAD~3 HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD -- KAM/Planetary/SecularSpectrum/Definiteness.lean KAM/Planetary/SecularSpectrum/Definiteness
git diff --check
```

The required triple-dot comparison warns `inp...HEAD: multiple merge bases, using 2c0f61b7b3c64df75621893f5f40bae338d7a580`. `git merge-base --all inp HEAD` returns that hash and `722ad4a37de68b025a0c690051afff665dcb1176`. With Git's selected base, protected-path diff is **not empty**: only generated `KAM.lean`, 94 insertions (no frozen, manifest or README change). This is a branch-integration note, not silently waived as an empty diff. The three S9-D commits (`5470de7`, `a73989e`, `c672945`) change only the three audited modules; the supplemental `HEAD~3..HEAD` protected-path comparison is empty. Both diff whitespace checks exit 0, with no diagnostics apart from the triple-dot merge-base warning. The requested S9-D scope does not authorize auditing the other inherited packages.

## Source defects, deviations and limits

No newly suspected pinned-source erratum or false blueprint statement was found. P9 already declares its narrower independent j=1 Laplace proof, the stronger sign-free Hadamard identity, quantitative coercivity proof, and the halved Q_h convention. This implementation respects those choices. It does not reinstate the withdrawn claim that Fejoz's induction is unfinished, and no new primary-source quotation is relied on here. This is a local blueprint/design/proof audit, not a fresh pinned-PDF audit or a claim of full track-P completion.

The new implementation deviation is F1's forbidden EuclideanSpace API. The upstream Norms docstring calls the spectrum “decreasingly” sorted, whereas the body reverses Mathlib's descending spectrum to give increasing order; S9-D uses the body correctly. That existing wording is outside the audited files and is informational rather than a new source erratum.

No production edits, git state changes, frozen edits, generated-root regeneration or dependency-cache operations were performed. Only this report is an auditor-created repository artifact; the untracked S9-D handoff predated the audit. Temporary probes/logs under this worktree's `.lake/abi-scratch/` are removed after their outputs are incorporated here.
