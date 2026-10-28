# E4 independent package audit 2 — delta audit

**Overall verdict: PASS WITH NOTES. F1 CLOSED.** The four analytic negation bridges complete the assigned E4 both-sign slice; `h_data` and prior proofs are byte-unchanged. The only permitted hygiene note is the stale generated root, recorded below. This infrastructure package seals no frozen anchor.

Audit date: 2026-10-28. Scope: only `KAM/Planetary/Exponential/KeplerData.lean`.

## Scope and immutable baseline

Read AGENTS, PLAN, DECISIONS, the package audit brief, E4 handoff/focus and round-1 report, P14 design and its two design audits, the h-data and st-thr blueprint contracts, the track statement, and relevant frozen theorem/definition interfaces. The user's exact worktree destination overrides the brief's generic main-worktree destination. No production, frozen, manifest or generated file was edited; probes reside only in `.lake/abi-scratch/` and are removed after validation. No state-changing git command was used.

Audited HEAD: `fe57167c8d3eb73043c1f3dccddd5b874c4562ef`.
Observed `inp`: `a341f3aebaad7052378f3fd4846d8619bf8da9d9`.
Merge base: `0c4b228c40c18845100d2ce1ebc27d8727a509ad`.
Round-1 baseline: `b7a3a2f3`.

`git diff inp...HEAD --stat` reports the 422-line new module plus the committed round-1 audit (148 lines) and handoff (20 lines), three files / 590 insertions. `git diff --numstat b7a3a2f3 HEAD` reports exactly `48 0 KAM/Planetary/Exponential/KeplerData.lean`; no other file changed. The sole hunk inserts the four bridges immediately before the existing namespace/section terminators. Thus “only appends” holds in the requested sense: no previous byte is altered, although the insertion precedes the final `end` lines rather than occurring after them. A byte comparison removing precisely this inserted block recovers the entire baseline file, including closing suffix: **True**. In particular, `h_data`, all earlier declarations and every earlier proof are byte-unchanged.

The current `h_data` statement was independently compared byte-for-byte against `/root/code/KAM-inp/.drafts/design/P14Signatures.lean`: **True**. Current module SHA-256: `4e9e4083fe16c8b3e5fccddeba483220ee80496744568f88c81acb667971180f`.

## F1 repair and consumer fidelity

The controlling requirement is design `P14-LEAN-DESIGN.md:307`: “E4 derives holomorphy, C2, reality and the same Hessian bound for -h by negation.” The E4 row at line 377 includes “both signs”; design audit 2:30 explicitly retains the four bridges. Blueprint `p14a-amd-expsafe.tex:199` requires “(iv) and (ii), (iii) hold for $-h$ as well.” The second N application at `stepP:p14:st-thr` (line 278) needs exactly these additional complex clauses alongside the already delivered negative definite-fast-part predicate.

All four added lemmas have exactly the positive `h_data` hypothesis telescope: implicit n; `hn : 2 ≤ n`, B, admissibility, implicit kappa/e/A/rho, `EnlargedData B kappa e A`, `0 < rho`, and `rho ≤ kappa`. They add no analytic premise, instance obligation, alternate Hamiltonian, source parameter, or conclusion-shaped hypothesis. Their function is literally `-planetaryKeplerC B.mass`, their domain literally `KAM.actionNbhd (fastBox B (2*kappa)) rho`, their scalar field ℂ, and their real-point carrier `Fin n → ℝ`.

The first two proofs extract the corresponding positive conjunct and apply `.neg`. The real-trace proof extracts the positive real trace and simplifies the imaginary part of negation. The Hessian proof extracts M, its exact equality, positivity and the positive Hessian bound from `h_data`; it proves the function equality `fderiv ℂ (-h) = -fderiv ℂ h`, then applies `fderiv_neg` again and `ContinuousLinearMap.opNorm_neg`. This uses the standard total Fréchet derivative API and preserves the norm exactly; no differentiability assumption is smuggled into the proof.

The Hessian export states `∃ M, M = ∑ i, 3 * B.mass i^3 / (5 * B.lower i / 8)^4 ∧ 0 < M ∧ ...`. The quantifier does not permit a larger or differently dependent constant: its equality forces the original exact sum. In particular an independent consumer-shape probe assembles all four negative clauses and `HasDefiniteFastPart` with the **same g, v, M witnesses obtained from positive `h_data`**, identifying the separately returned M by its exact equality. The resulting clauses match the literal `hhol`, `hC2`, `hreal`, `hHess` slots of frozen `PartialConvexNekhoroshev.lean:56–60`. This tests supplying the E4 inputs, not the proof or full application of N-PARTIAL-CONVEX.

The nested derivative has type `(Fin n → ℂ) →L[ℂ] ((Fin n → ℂ) →L[ℂ] ℂ)`. Its norm is the **curried bilinear operator norm** required at design line 298, with max norms on both argument spaces. No matrix norm or entrywise bound replaces it.

## Declaration ledger and definitions

Names below lie in `KAM.Planetary`. Inherited PASS entries retain round 1's source review on the byte-identical baseline; build, theorem axioms and kernel replay are refreshed for the whole module in this round.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| Generic Kepler object | `keplerSumGen` (41) | PASS | Unchanged total rational sum over RCLike scalars. |
| hd-ii | `keplerSumGen_contDiffOn` (48) | PASS | Unchanged regularity on nowhere-zero locus. |
| Derivative object | `keplerSumGenD` (73) | PASS | Unchanged explicit continuous linear map. |
| hd-ii | `keplerSumGen_hasFDerivAt` (76) | PASS | Unchanged guarded first derivative. |
| Derivative identity | `keplerSumGen_fderiv_eq` (95) | PASS | Unchanged identification with actual fderiv. |
| hd-iv | `keplerSumGenD_hasFDerivAt` (99) | PASS | Unchanged curried second derivative. |
| hd-iv | `keplerSumGen_fderiv2_apply` (116) | PASS | Unchanged diagonal formula. |
| hd-iv | `keplerSumGen_hess_norm_le` (134) | PASS | Unchanged sum bound in operator norm. |
| hd-ii margin | `keplerData_margin` (156) | PASS | Unchanged nonzero-coordinate margin. |
| hd-v | `hasDefiniteFastPart_neg` (181) | PASS | Unchanged real definite-fast-part transport. |
| Real embedding | `planetaryKeplerC_ofReal` (212) | PASS | Unchanged literal real rational sum. |
| Real restriction | `realPart_planetaryKeplerC` (216) | PASS | Unchanged real-part identification. |
| Complex identity | `planetaryKeplerC_eq` (221) | PASS | Unchanged rfl identity. |
| hd-v frequency | `keplerSumGen_real_freq` (224) | PASS | Unchanged coordinate derivative. |
| hd-v Hessian | `keplerSumGen_real_hess` (229) | PASS | Unchanged signed quadratic form. |
| h-data; hd-i, ii, iv, v | `h_data` (238) | PASS | Exact approved signature and byte-unchanged proof. |
| F1 / negative holomorphy | `keplerDataNeg_differentiableOn` (376) | PASS | Exact negative differentiability clause and original hypotheses. |
| F1 / negative complex C2 | `keplerDataNeg_contDiffOn` (386) | PASS | Exact negative complex C2 clause and original hypotheses. |
| F1 / negative reality | `keplerDataNeg_im_eq_zero` (396) | PASS | Exact negative real-point trace clause and original hypotheses. |
| F1 / negative Hessian | `keplerDataNeg_hess_norm_le` (407) | PASS | Same exact positive M, same domain, curried operator norm. |

There are **no new definitions, abbreviations, structures or instances in the delta**. The full package's only new definitions remain `keplerSumGen` and `keplerSumGenD`: intended total algebraic objects on their whole carriers. Total division at zero does not enter the analytic claims, which retain the nonzero-coordinate guards and the proved collar margin. The derivative map is identified with fderiv only on that guarded locus. No fallback value or bundled unproved analytic obligation was introduced.

## Static hygiene

- The file has 422 lines and retains copyright, `module`, public imports, module docstring, exposed public section and existing namespace. No forbidden proof escape, heartbeat/recursion/synthesis override or `EuclideanSpace` appears.
- Recursive source-import traversal finds 85 KAM modules including the target, zero frozen theorem modules and zero provider modules. No imported DRAFT_SORRY theorem. No provider equality or seal-body probe applies to this ordinary infrastructure package.
- Full and short names of the four delta exports occur as declarations only at lines 376, 386, 396 and 407 respectively; repository-wide declaration scans find no other short-name declaration. Runtime environment checks additionally test root-level absence for all 18 public theorem names.
- `git diff --check inp...HEAD`: exit 0, no output.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, no output.
- The round-1 note about a separately named uniqueness lemma for g,v remains unchanged: the approved attained-minimum characterization already forces uniqueness. The delta introduces no new obligation there.

## Validation receipts

All Lean-related checks below run sequentially with `LEAN_NUM_THREADS=1` and niceness 5. The targeted build uses the prescribed compile gate. No clean, update, cache fetch or generated-root regeneration is performed.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-e4 KAM.Planetary.Exponential.KeplerData
```

Exit 0. Gate: `[inp-gate] slot 1 acquired 17:53:51 for KAM.Planetary.Exponential.KeplerData`.
Final output: `Build completed successfully (9131 jobs).`
Only replayed pre-existing unused-variable warnings appeared in `KAM/Kepler/Energy.lean:106`, `KAM/Planetary/Poincare/Chart.lean:212,247`, and `KAM/Kepler/Mass.lean:147,157,500,524`. No E4 error or heartbeat design signal.

### Exact signature, shared-M consumer inputs, axioms and root shadow

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/E4Audit2.lean
```

Exit 0. The copied exact h_data signature elaborated with `exact h_data hn B hB hd hrho hrk`. The negative consumer-input example elaborated using all four new exports with no additional premises and the original witnesses. Root names were checked via `Lean.getEnv` / `env.contains (Lean.Name.mkSimple name)`. Complete output:

```text
'KAM.Planetary.keplerSumGen_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerSumGen_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerSumGen_fderiv_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerSumGenD_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerSumGen_fderiv2_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerSumGen_hess_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerData_margin' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hasDefiniteFastPart_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.planetaryKeplerC_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.realPart_planetaryKeplerC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.planetaryKeplerC_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerSumGen_real_freq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerSumGen_real_hess' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.h_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerDataNeg_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerDataNeg_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerDataNeg_im_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerDataNeg_hess_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
Root shadow check: PASS
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Exponential.KeplerData
```

Exit 0. Complete output:

```text
replaying KAM.Planetary.Exponential.KeplerData
```

This replays the entire module, including all four appended proofs and all unchanged private/public proofs.

### Source lint and protected invariants

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the explicitly permitted stale generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (793 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The module checks, frozen-anchor guard and elaborated ABI check passed independently of the generated-root exception. `KAM.lean` was not regenerated. Lint's internal ABI Lean invocation ran only after the preceding build/probe/kernel checks had completed, inheriting `LEAN_NUM_THREADS=1` and niceness 5.

## Final disposition, uncertainties and errata

**Overall verdict: PASS WITH NOTES; round-1 F1 CLOSED.** `h_data`: PASS. Each of the four analytic negation bridges: PASS. The complete E4 both-sign slice passes; the only hygiene exception is the stale generated root expressly allowed by the brief. No blocking finding remains in this delta.

No new suspected blueprint/source/frozen-statement defect or introduced deviation was found. The design, blueprint and consumer agree on the four obligations, and the fix supplies them without changing any prior statement or proof. The round-1 handoff's inaccurate completeness claim is superseded by the actual repair; its historical text was not edited. The existing note about no separately exported minimum-uniqueness theorem remains nonblocking, as in round 1.

This is an infrastructure-package audit, not a claim that P-EXP-SAFE or N-PARTIAL-CONVEX has been proved or that a frozen anchor is seal-ready. No provider or frozen theorem was added, sealed or imported by E4. The consumer probe checks the exact negative analytic input forms and shared constants; it does not certify the entire stopped-action assembly or remaining packages. No other uncertainty affects this delta verdict.

The scratch probe `.lake/abi-scratch/E4Audit2.lean` was removed. Final `git diff --check inp...HEAD` and `git diff --check` exit 0 without output; protected-path diff is empty. The production source retains the SHA-256 recorded above. Final repository status contains only the requested untracked `docs/tracks/P/audits/E4-audit-2.md`; no tracked file changed.
