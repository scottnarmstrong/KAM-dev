# SO-DIO independent audit 1

Date: 2026-10-29. Verdict: **PASS WITH NOTES** for the complete unfrozen SO-DIO helper slice. All four requested Diophantine results pass exact statement probes with no premises. No frozen theorem is supplied or sealed by this package; “seal-ready” is inapplicable. The generated-root lint exception is recorded below.

## Scope and authority

Audited only `KAM/Certificate/QuadraticDiophantine.lean`, at HEAD `f454a657ba33d680318a7241e2cd45cf166ec04b`, against local `inp` `184516586ae9060d87838ff1fb59d2547fe216e5`, using the full `git diff inp...HEAD`. The diff adds exactly this 263-line file (maximum 99 Unicode characters per line). SHA256: `511dafebbd09f98e74dcdf9f7cb95401186269e1c04efe2d5f55ab5aa14af632`.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the SO-DIO handoff and its AUDIT FOCUS, `/root/code/KAM-inp/.drafts/briefs/offload-main/SO-DIO.md`, the SO plan, proposal §2.4/§6.4, pilot §6, and `KAM/Frozen/Defs/IsDiophantine.lean`. The handoff explicitly substitutes the task brief and pilot for nonexistent SO signatures/blueprint nodes. Tracks I/N/P theorem anchors and statement files are not dependencies of this slice. The user's exact worktree report path overrides the generic audit brief's MAIN-worktree destination.

There are no SIGNED declarations, providers, frozen theorem bodies, or SO graph nodes here. Accordingly, provider/frozen-type equality and seal-copy probes are inapplicable. Instead, independently elaborated expected-type probes cover all ten public theorems, and `rfl` probes check all three definition bodies. No signed-file equality claim is made.

## Declaration inventory and fidelity

All names below are in `KAM.Certificate`; line references are to the audited module. The task brief and pilot §6 supply the node contract.

| Node / role | Declaration (line) | Verdict | Reason |
| --- | --- | --- | --- |
| Golden-ratio conjugate | `lunarG` (29) | PASS | Literally `(Real.sqrt 5 - 1) / 2`. |
| Lower frequency | `lunarNuMinus` (32) | PASS | Literally `1 - 1 / (40 + lunarG)`. |
| Upper frequency | `lunarNuPlus` (35) | PASS | Literally `1 + 1 / (40 + lunarG)`. |
| Lower closed form | `lunarNuMinus_eq` (58) | PASS | `(3039 + sqrt 5)/3118`, no binders/premises. |
| Upper closed form | `lunarNuPlus_eq` (61) | PASS | `(3197 - sqrt 5)/3118`, no binders/premises. |
| Lower polynomial | `lunarNuMinus_quadratic` (64) | PASS | Exact coefficients 1559, −3039, 1481. |
| Upper polynomial | `lunarNuPlus_quadratic` (67) | PASS | Exact coefficients 1559, −3197, 1639. |
| Lower infinite bound | `lunarNuMinus_lower` (173) | PASS | All integer a,b, only `(a,b) ≠ (0,0)`; literal coefficient 21 and ℓ¹ denominator. |
| Upper infinite bound | `lunarNuPlus_lower` (191) | PASS | Same quantifiers, hypotheses and constant. |
| Lower full vector | `lunarNuMinus_isDiophantine` (244) | PASS | Literal frozen predicate, γ=1/21, τ=1, `![lunarNuMinus,1]`, no premises. |
| Upper full vector | `lunarNuPlus_isDiophantine` (248) | PASS | Literal frozen predicate, γ=1/21, τ=1, `![lunarNuPlus,1]`, no premises. |
| Lower reference vector | `lunarNuMinus_half_isDiophantine` (252) | PASS | Literal frozen predicate, γ=1/42, τ=1, `![lunarNuMinus/2,1/2]`, no premises. |
| Upper reference vector | `lunarNuPlus_half_isDiophantine` (257) | PASS | Literal frozen predicate, γ=1/42, τ=1, `![lunarNuPlus/2,1/2]`, no premises. |
| Radical square | private `sqrt5_sq` (37) | PASS | Standard square-root square identity. |
| Radical bounds | private `sqrt5_bounds` (39) | PASS | `2 < sqrt 5 < 9/4` from positivity and the square. |
| Irrationality | private `sqrt5_irrational` (44) | PASS | Mathlib prime-square-root irrationality. |
| Denominator rewrite | private `forty_g` (48) | PASS | Exact ring identity. |
| Rationalization | private `inv_forty_g` (51) | PASS | Nonzero denominator proved from radical bounds. |
| Norm estimate | private `norm_bound` (72) | PASS | Explicit conjugate relations/irrationality and x≥1/2; all instantiated and proved in each public caller. |
| Affine irrationality | private `irr_comb` (161) | PASS | Only e=±1; derives sqrt 5 rational if the combination were rational. |
| Predicate conversion | private `isDiophantine_of_lower` (208) | PASS | Distinct conditional helper, proved by expanding the frozen predicate and scaling by 1/2; never substitutes an assumed lower bound for a source theorem. |

Slice complete: both defining frequencies, closed forms, exact quadratic equations, both infinite integer bounds, and all four required Diophantine statements are present. Discriminants equal 5; independent scratch Lean examples prove both integer identities with `norm_num`. Separate named public discriminant theorems are not required by the “done when” contract. The optional preferred general lemma is realized only for leading coefficient 1559, sufficient for both instances; it is private and makes no claim of general-denominator applicability.

## Definition classification and imports

The three public definitions above are exact closed real constants, expose their bodies through `@[expose] public section`, and contain no junk cases or fallback values. The denominator `40 + lunarG = (79 + sqrt 5)/2` is positive. There are no new abbrevs, structures, instances, or other global definitions. Local `set` terms s,d,N abbreviate the actual ℓ¹ size, absolute value and integral norm numerator, respectively.

The only direct KAM import is `KAM.Frozen.Defs.IsDiophantine`, whose manifest entry `kam.IsDiophantine.v1` is a SEALED definition (manifest lines 281–307). Other imports are Mathlib's irrationality and square-root modules. No provider or DRAFT_SORRY theorem is imported. All thirteen public short names have zero occurrences elsewhere under KAM; searching Mathlib for `lunar(G|Nu)` also returns no matches. All declarations are namespaced, with no root shadow or global instance change.

## Proof audit

1. Rationalization: `2/(79+sqrt 5) = (79-sqrt 5)/3118` because `79²−5=6236`. Subtracting/adding gives precisely the two advertised closed forms. Both discriminants are 5.
2. For either conjugate pair x,y, the proof establishes `N = 1559(ax+b)(ay+b)` for the integer `N=a²C+abB+1559b²`. If N=0 then one factor vanishes. For a=0 this forces b=0; otherwise it makes x or y rational. Thus N≠0 for every nonzero integer pair, giving `|ax+b||ay+b| ≥ 1/1559`.
3. With L=|a|+|b|, `|ay+b| ≤ d + L·9/(4·1559)`, where d=|ax+b|. In the L≥2 branch, assuming d<1/(21L) gives
   `1559 d(d+L·9/(4·1559)) < 1559/(441L²)+9/84 ≤ 1559/1764+9/84 = 437/441 < 1`.
   The exact slack is 4/441; the Lean proof's polynomial `nlinarith` deductions at lines 151–159 implement this contradiction without an analytic approximation.
4. In the L<2 branch, integrality and nonzeroness imply L≥1. If a=0, |b|≥1; if a≠0, then |a|≥1 and b=0 (otherwise L≥2). The bound x≥1/2 yields |ax|≥1/2≥1/21. This covers all signs, including the coordinate axes. The handoff's reference to x>1/2 is stronger than necessary: the private lemma uses x≥1/2 and proves the required estimate.
5. The conversion handles arbitrary `k : Fin 2 → ℤ`, proving `(k 0,k 1)≠(0,0)` from k≠0 by extensionality. Expanding the frozen definition yields exactly `γ/(Σ|kᵢ|)^τ ≤ |Σ kᵢωᵢ|`; `Real.rpow_one` handles τ=1. Halving both vector entries halves the dot product and γ. There is no restriction on signs, primitivity, frequency cutoffs, denominators, or nonzero individual components.

No hard step is introduced as an unproved hypothesis. Private conditional helpers name their input relations explicitly; both public applications discharge them. All public results match the required source premises and carriers; none changes a constant's dependence or weakens a conclusion.

## Independent checks

All Lean/Lake invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`; lint's ABI subprocess inherited both. No clean/update/cache operation, source repair, root regeneration, git mutation, or frozen/manifest edit was performed.

### Diff and static checks

Commands (cwd `/root/code/KAM-inp-sodio`):

```sh
git diff --stat inp...HEAD
git diff inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Output: one added source file, 263 insertions; protected-path diff empty; whitespace check exit 0. Python source/declaration scans report 263 lines, maximum width 99, no forbidden tokens/overrides, and no public short-name reuse. The module includes copyright/authors, `module`, public imports, module docstring and public section. No `native_decide`, `Lean.ofReduceBool`, `EuclideanSpace`, proof escape or resource override is present.

### Targeted compile gate

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sodio KAM.Certificate.QuadraticDiophantine
```

Exit 0, output:

```text
[inp-gate] slot 1 acquired 10:53:47 for KAM.Certificate.QuadraticDiophantine
Build completed successfully (2193 jobs).
```

This independent invocation accepted the existing build artifacts; it does not claim a forced source rebuild or repeat the prover's reported 46-second compilation. Kernel replay is checked separately below.

### Exact statements and axioms

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SODIOAudit.lean
```

Exit 0. The temporary probe imported the target module, checked the three definitions with `rfl`, assigned all ten public theorems to independently written expected types (using `@` for the parameterized lower-bound results and final Diophantine exports), explicitly applied each full-vector theorem to an arbitrary nonzero `Fin 2 → ℤ` vector in the expanded frozen predicate, and proved both discriminants equal 5. No probe added a premise to a package theorem. Exact axiom output:

```text
'KAM.Certificate.lunarNuMinus_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlus_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuMinus_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlus_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuMinus_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlus_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuMinus_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlus_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuMinus_half_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlus_half_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.QuadraticDiophantine
```

Exit 0, exact output:

```text
replaying KAM.Certificate.QuadraticDiophantine
```

This single module contains every new lemma and export; no separate provider or lemma modules exist.

### Source lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, exact output (successive chunks combined in order):

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1282 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The stale generated root is the sole lint failure, explicitly permitted by the audit brief and predicted in the handoff. It is left untouched. No other lint defect was emitted. This exception accounts for the overall PASS WITH NOTES; all four individual Diophantine results pass.

## Findings, uncertainties and deviations

No mathematical or statement-fidelity defect found in the audited slice. No suspected pinned-source erratum, false blueprint assertion, or implementation deviation requiring an errata entry. The pilot §6 line 248 says “it has not yet been formalized in Lean”; that historical pilot status predates this module and is now superseded for this Diophantine subtask.

The package does not certify a torus, residual, averaged torsion, or the final lunar confinement theorem. It discharges the stated infinite Diophantine inputs only. No SO signature file, graph or frozen anchor exists for this slice, as the handoff expressly states. Generated-root integration remains the orchestrator's task under the audit brief's permitted exception.

Final integrity checks: `git diff --exit-code` exits 0 (no tracked source modifications), the protected-path three-dot diff is empty, and the independent `.lake/abi-scratch/SODIOAudit.lean` probe has been removed. The pre-existing untracked handoff was preserved. The only lasting auditor-created repository file is this report; no work was written in `/root/code/KAM-inp`.
