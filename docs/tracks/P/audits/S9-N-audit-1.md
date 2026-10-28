# Independent package audit S9-N, audit 1

Date: 2026-10-28 (UTC).

Overall verdict: **PASS WITH NOTES** for the scoped S9-N package. Both main results pass exact-type, proof, axiom and kernel checks. N1 is a documentation error; N2 records inherited branch-diff hygiene. No frozen anchor is implemented or sealed by this package, so a per-anchor seal verdict and provider/frozen seal-body probes are **not applicable**.

## Scope and pinned evidence

- Worktree/report: `/root/code/KAM-inp-s9n`; this report is written only here, as expressly requested, overriding the generic brief's main-worktree output instruction.
- Audited HEAD: `6d648e40e5ea9d31c78d3ac00cccc80eb03536a5`; parent `121d5e40cce2535535389edd2fadc86c62a03617`.
- `inp` at audit: `5991245cabc06e69ec900cb6006b45f72cc85eb0`; `inp-s8b`: `326288529ed59457294068ad2b05b5b9295b3099`.
- Sole scoped implementation: `KAM/Planetary/SecularSpectrum/Norms.lean`, 158 lines, SHA-256 `94ddcb9b98178f723eae7b33d0ca33c26764592aa075f8f0df4e68a6f5409c1b`.
- Read AGENTS.md, PLAN.md, DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, S9-N-handoff.md, track P statement, the Revision 2 design (especially row S9-N, line 435), both design audits under `docs/tracks/P/design/`, and the actual draft `/root/code/KAM-inp/.drafts/design/P810Signatures.lean`.
- Signature draft SHA-256: `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`, matching design-audit-2. Relevant signature lines: 260–269, 854–856; design appendix: 817–826, 1411–1413.
- Direct source for this scope: `blueprint-P/parts/p9-secular-spectrum.tex:15–20`, especially `bpP:p9:conv#data`, `bpP:p9:norm-compare`, increasing spectrum, and the spectral convention. SHA-256 `19271673e246eed9d444a3f370c479aa13685528e306f9addcddc550cc56da54` matches the design. No external PDF assertion is used to bypass these exact contracts.

Ran both `git diff inp...HEAD` and the handoff-focused `git diff inp-s8b...HEAD -- KAM/Planetary/SecularSpectrum`. The latter adds only Norms (158 lines). The unrestricted comparison against inp-s8b also contains inherited unrelated packages; it is not a one-file whole-branch diff. `git show --stat HEAD` and `git diff HEAD^ HEAD` confirm that the S9-N commit changes only Norms.

`git diff inp...HEAD` warns of multiple merge bases, selecting `6f2cb1ec6284a98aaffeed74340762f20f4afc04`; `git merge-base --all inp HEAD` returns that commit and `408ea7a6f026a1ecf1d0cf0e988bdc54494497f9`. The inp-s8b merge base is `6f2cb1ec6284a98aaffeed74340762f20f4afc04`. These moving-branch comparisons were not silently substituted for the exact package commit.

## Findings

**N1 — nonblocking documentation error.** `Norms.lean:16` says “the decreasingly sorted spectrum”. The actual definition at lines 34–35 reverses Mathlib's antitone `eigenvalues₀` and therefore is increasing (nonstrictly, with multiplicity), exactly as blueprint p9:16 and design line 350 require. Mathlib `Analysis/Matrix/Spectrum.lean:60–64` supplies the antitone fact. A scratch proof of `Monotone (sorted M hM)` passed. Replace only the descriptive word “decreasingly” with “increasingly” in a subsequent authorized implementation edit. No production file was edited during this audit.

**N2 — inherited broad-diff hygiene.** The mandatory `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**: KAM.lean has 12 inherited generated imports, introduced before the S9-N commit (commit `408ea7a`). Frozen, manifest and README diffs are empty. The same root change appears against inp-s8b. `git diff HEAD^ HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. Thus the literal whole-branch protected-path check fails for the inherited root change; the scoped S9-N commit passes. The broad `git diff --check inp...HEAD` also exits 2 for pre-existing trailing whitespace in `docs/tracks/P/audits/P23-12-handoff.md:28`; `git diff --check HEAD^ HEAD` exits 0. These are recorded, not repaired or attributed to Norms.

No mathematical defect or added premise was found. No new suspected pinned-paper or blueprint erratum was found in this scope. N1 contradicts the implementation/source description, not the mathematical definition.

## Per-declaration review

All names below have prefix `KAM.Planetary.SecularSpectrum.`; node shorthand has prefix `bpP:p9:`. Support lemmas implement elementary steps of the two norm comparisons rather than claiming additional published nodes.

| Node / role | Declaration (Norms line) | Verdict | Reason |
|---|---|---|---|
| `conv#data` | `length2` (31) | PASS | Literal square root of sum of squares; exact design body. |
| `conv#data` | `op2` (32) | PASS | Literal supremum of Euclidean unit-vector images; boundedness proved below. |
| `conv#data` | `frobenius` (33) | PASS | Literal square root of squared entries; exact design body. |
| `conv#data / e-spec` | `sorted` (34) | PASS WITH NOTES | Reversed antitone eigenvalues give increasing order; docstring says decreasing (N1). |
| `local-analytic / lift` | `isSO` (36) | PASS | RᵀR=1 and det R=1; exact SO predicate. |
| `norm-compare` | `opMax` (37) | PASS | Literal supremum for the ambient Pi max norm; exact design body. |
| `norm-compare support` | `length2_nonneg` (39) | PASS | Square-root nonnegativity, no premise. |
| `norm-compare support` | `length2_eq_zero` (41) | PASS | Sum of nonnegative squares zero implies vector zero; only its explicit zero-length guard. |
| `norm-compare support` | `length2_smul` (49) | PASS | Absolute scalar homogeneity, including negative and zero scalars. |
| `norm-compare` | `norm_le_length2` (55) | PASS | Each squared coordinate is at most the sum of squares. |
| `norm-compare` | `length2_le_sqrt_mul_norm` (61) | PASS | Sum of n squared max-norm bounds; exact sqrt(n) factor. |
| `conv#data support` | `length2_mulVec_le` (70) | PASS | Rowwise Cauchy–Schwarz gives the Frobenius bound. |
| `conv#data support` | `op2_bddAbove` (81) | PASS | Frobenius bound on the complete Euclidean unit-image set. |
| `conv#data support` | `op2_nonneg` (87) | PASS | Real.sSup_nonneg handles the empty sphere as well. |
| `norm-compare support` | `length2_mulVec_le_op2` (90) | PASS | Zero case separated; normalize by positive Euclidean length and apply le_csSup. |
| `conv#data / norm-compare` | `norm_compare` (102) | PASS | All three exact design conclusions, no added hypothesis. |
| `norm-compare support` | `opMax_bddAbove` (109) | PASS | Frobenius times sqrt(n) bounds all max-unit images. |
| `norm-compare support` | `opMax_nonneg` (119) | PASS | Nonnegative image set, including n=0. |
| `norm-compare support` | `norm_mulVec_le_opMax` (122) | PASS | Zero case separated; normalize by positive Pi norm. |
| `norm-compare` | `norm_compare_operator` (134) | PASS | Both induced-norm comparisons with exactly sqrt(n), no extra premise. |

The six literal definition bodies and two main theorem headers match the design draft after whitespace normalization. Scratch copies of the six draft definitions were definitionally equal (`rfl`, comparing fully polymorphic exports) to production. Fresh declarations with the exact draft theorem statements were proved by `exact KAM.Planetary.SecularSpectrum.norm_compare x M` and `exact KAM.Planetary.SecularSpectrum.norm_compare_operator M`. This also checks the explicit binder order x,M and M without extra inputs.

The real carrier is `SecularForm.Vec n = Fin n → ℝ`, with `Mat n = Matrix (Fin n) (Fin n) ℝ`. The ambient Pi norm remains the max norm. The package matches the design's real specialization; it does not claim the blueprint's parallel complex norm comparisons or later spectral perturbation/local analytic results. The generalization from the physical n≥1 to all n is valid: empty-dimensional operator suprema evaluate to zero, checked independently in the probe. There is no new norm instance or EuclideanSpace carrier in the package.

## Definition classification

All six are literal definitions, not theorem-shaped assumption bundles or arbitrary witness choices. No new abbrev or structure occurs in Norms. Vec/Mat are unchanged upstream abbreviations inspected in SecularForm/Basic.

| Definition | Intended object and full-carrier review | BODY_MATCH | PUBLIC_CARRIER | WELL_DEFINEDNESS | CHARACTERIZATION | CHOICE_INDEPENDENCE | DEFINITION_VERDICT |
|---|---|---|---|---|---|---|---|
| `length2` | √(sum xᵢ²), every real Pi vector, including empty vector | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `op2` | Supremum of Euclidean-unit images; bounded above by proved Frobenius bound; empty n=0 sphere gives 0 | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `frobenius` | √(sum of squared real entries), all square matrices | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `sorted` | Literal reversed Mathlib ordered eigenvalue list on every real Hermitian matrix, including repeated eigenvalues | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A (library spectral construction) | PASS |
| `isSO` | RᵀR=1 ∧ det R=1, all real square matrices | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `opMax` | Supremum of Pi-max-unit images; proved finite bound, empty n=0 sphere gives 0 | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |

There is no invented off-domain branch or fallback relied on by the proofs. The real conditional-complete supremum convention for the empty set is the exact design formula and gives the correct zero-dimensional operator norm; no sphere nonemptiness assumption is smuggled in.

## Binder and hypothesis audit

The following table has one row per theorem binder after expanding Vec/Mat. `T` means TYPING and `S` means SOURCE (the elementary helper's explicitly stated zero-length condition). The norm-comparison source is p9:15; scaling/zero and Cauchy–Schwarz rows are the explicit elementary proof steps, not additional source-result premises. Every `{n}` is implicit; the vector of `length2_eq_zero` is implicit; other listed binders are explicit. There are no instance binders, hidden Data fields, standing/ruling assumptions, existential constants or wider constant dependencies.

| Declaration | Binder | Bin | Evidence |
|---|---|---|---|
| `length2_nonneg` | `n` | T | Natural dimension of Fin n (p9:15). |
| `length2_nonneg` | `x` | T | Real Pi vector (p9:15); no mathematical property assumed. |
| `length2_eq_zero` | `n` | T | Natural dimension of Fin n (p9:15). |
| `length2_eq_zero` | `x` | T | Real Pi vector (p9:15); no mathematical property assumed. |
| `length2_eq_zero` | `h` | S | Elementary helper zero criterion at Norms:41; discharged by a proof-local case split at :92. |
| `length2_smul` | `n` | T | Natural dimension of Fin n (p9:15). |
| `length2_smul` | `c` | T | Arbitrary real scalar for elementary homogeneity (Norms:49). |
| `length2_smul` | `x` | T | Real Pi vector (p9:15); no mathematical property assumed. |
| `norm_le_length2` | `n` | T | Natural dimension of Fin n (p9:15). |
| `norm_le_length2` | `x` | T | Real Pi vector (p9:15); no mathematical property assumed. |
| `length2_le_sqrt_mul_norm` | `n` | T | Natural dimension of Fin n (p9:15). |
| `length2_le_sqrt_mul_norm` | `x` | T | Real Pi vector (p9:15); no mathematical property assumed. |
| `length2_mulVec_le` | `n` | T | Natural dimension of Fin n (p9:15). |
| `length2_mulVec_le` | `M` | T | Real square matrix (p9:15). |
| `length2_mulVec_le` | `x` | T | Real Pi vector (p9:15); no mathematical property assumed. |
| `op2_bddAbove` | `n` | T | Natural dimension of Fin n (p9:15). |
| `op2_bddAbove` | `M` | T | Real square matrix (p9:15). |
| `op2_nonneg` | `n` | T | Natural dimension of Fin n (p9:15). |
| `op2_nonneg` | `M` | T | Real square matrix (p9:15). |
| `length2_mulVec_le_op2` | `n` | T | Natural dimension of Fin n (p9:15). |
| `length2_mulVec_le_op2` | `M` | T | Real square matrix (p9:15). |
| `length2_mulVec_le_op2` | `x` | T | Real Pi vector (p9:15); no mathematical property assumed. |
| `norm_compare` | `n` | T | Natural dimension of Fin n (p9:15). |
| `norm_compare` | `x` | T | Real Pi vector (p9:15); no mathematical property assumed. |
| `norm_compare` | `M` | T | Real square matrix (p9:15). |
| `opMax_bddAbove` | `n` | T | Natural dimension of Fin n (p9:15). |
| `opMax_bddAbove` | `M` | T | Real square matrix (p9:15). |
| `opMax_nonneg` | `n` | T | Natural dimension of Fin n (p9:15). |
| `opMax_nonneg` | `M` | T | Real square matrix (p9:15). |
| `norm_mulVec_le_opMax` | `n` | T | Natural dimension of Fin n (p9:15). |
| `norm_mulVec_le_opMax` | `M` | T | Real square matrix (p9:15). |
| `norm_mulVec_le_opMax` | `x` | T | Real Pi vector (p9:15); no mathematical property assumed. |
| `norm_compare_operator` | `n` | T | Natural dimension of Fin n (p9:15). |
| `norm_compare_operator` | `M` | T | Real square matrix (p9:15). |

Counts across 14 theorem signatures: **SOURCE 1, STANDING 0, TYPING 33, RULED 0, EXCESS 0**. Both main theorem signatures have SOURCE 0 / EXCESS 0: only their typing data. The single helper condition is used only to derive x=0; it does not assume either comparison or any hard proof obligation.

Proof reconstruction: coordinate domination and the n-term sum give the two vector bounds. Rowwise Cauchy–Schwarz gives the Frobenius action bound and hence supremum boundedness. Splitting x=0, otherwise scaling x by inverse length/norm, proves the two homogeneous action bounds using le_csSup with the proved boundedness witnesses. The final operator comparisons apply the vector bounds to unit vectors in each respective sphere. Real.sSup_le includes its nonnegative upper-bound argument, so neither direction assumes positive dimension or incorrectly applies a nonempty-set supremum rule at n=0.

## Imports, quarantine and hygiene

Direct imports are Mathlib and SecularForm.Basic. An independent recursive scan of all 64 reached KAM modules found no provider and no frozen theorem import: all 47 reached frozen files are manifested **SEALED definitions**. The directly imported Basic definitions SecularAverage, Assemble and PlaneLength were read; none appears in the new theorem signatures beyond the unchanged real Vec/Mat carriers. No DRAFT_SORRY theorem is imported, directly or transitively.

Norms has the copyright/authors header, module command, public imports, module docstring, and `@[expose] public noncomputable section`. It has 158 physical lines (therefore below the 1500 code-line cap), zero lines over 100 Unicode characters, zero forbidden proof escapes or resource overrides, and no new structure/instance. Broad Mathlib import is not an import-cycle or quarantine failure.

### Independent commands and results

All auditor-controlled Lean/Lake invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`. Lint (which launches an ABI Lean probe internally) ran only after the other Lean invocations finished. Existing build artifacts were retained; no clean, update, cache download or library-from-scratch rebuild was requested.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s9n KAM.Planetary.SecularSpectrum.Norms
```

Exit **0**. Output includes:

```text
[inp-gate] slot 2 acquired 09:29:16 for KAM.Planetary.SecularSpectrum.Norms
Build completed successfully (9110 jobs).
```

Replayed upstream unused-variable warnings only: Energy:106; Poincare/Chart:212,247; Mass:147,157,500,524. No warning from Norms; no default-heartbeat failure.

2. Exact draft-definition/theorem, ordering, n=0 and axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S9NAudit1.lean
```

Final exit **0**, no warnings/errors. Six definition equalities, two exact theorem application bodies, `op2 (M : Mat 0) = 0`, `opMax (M : Mat 0) = 0`, and `Monotone (sorted M hM)` all elaborate. Probe-local setup failures on earlier attempts were corrected: missing noncomputable section, an overly broad simp rewrite that recursed, and a nonexistent cast lemma. No production proof was changed and no resource override was used.

Exact axiom output:

```text
'KAM.Planetary.SecularSpectrum.length2_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.length2_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.length2_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.norm_le_length2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.length2_le_sqrt_mul_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.length2_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.op2_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.op2_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.length2_mulVec_le_op2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.norm_compare' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.opMax_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.opMax_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.norm_mulVec_le_opMax' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.norm_compare_operator' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay (one invocation, sole scoped module contains all lemma exports):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularSpectrum.Norms
```

Exit **0**. Exact output:

```text
replaying KAM.Planetary.SecularSpectrum.Norms
```

All scoped declarations replayed successfully.

4. Required source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely for the explicitly permitted stale generated root. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (521 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No forbidden-token, resource-override, 100-character-line, oversized-file, errata-render, module-system, frozen-byte or ABI failure was reported. This is **PASS under the brief’s stated stale-root exception**, not a claim of raw exit 0. KAM.lean was not regenerated.

5. Scope/protected paths and whitespace: commands and results are recorded in N2. S9-N commit-only checks pass; the mandatory broad-diff exceptions remain visible.

## Closeout

Files written: this report only, plus the temporary probe in the authorized `.lake/abi-scratch/` location (removed after validation). Pre-existing untracked S9-N-handoff.md is untouched. No state-changing git command, generated-file edit, frozen-file edit, source repair or errata-ledger edit was performed.

Uncertainties: no mathematical uncertainty remains for the scoped real norm package. N1 needs only a docstring correction by the implementation owner; the inherited broad-diff discrepancies in N2 remain outside this scoped audit. Provider sealing and any track headline/root closure are not claimed.
