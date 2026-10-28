# E4 independent package audit 1

**Overall verdict: FAIL — incomplete E4 slice (F1).** The delivered `KAM.Planetary.h_data` has exactly the approved signature and its positive-sign analytic data and both definite-fast-part predicates pass source review. The package omits the separately assigned analytic negation bridges. This finding does not allege an unsound proof or a false frozen statement.

Audit date: 2026-10-28. Audited only `KAM/Planetary/Exponential/KeplerData.lean`, with dependencies inspected for meanings/import hygiene. HEAD: `9c2811cf3764ca895235008aa2c51999bf747e18`; observed `inp`: `d9183adae208ecf2e726620694b69c8168e33006`; merge base: `0c4b228c40c18845100d2ce1ebc27d8727a509ad`. `git diff inp...HEAD --stat` contains exactly this new 374-line module. The supplied handoff was already untracked at audit start.

Read the user instructions, AGENTS, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, E4 handoff/focus, P14 design and both design audits, blueprint a195–206 and its packet contracts, the relevant track statement/frozen exponential-safety theorem, and definitions of admissibility, action neighbourhood, frequency and definite fast part. The user's exact worktree report path overrides the generic brief's main-worktree destination. No production, frozen, manifest or generated file was edited. Temporary probes were restricted to this worktree's `.lake/abi-scratch/`.

## F1 — Missing analytic negation bridges (blocking package completeness)

**Required:** `docs/tracks/P/design/P14-LEAN-DESIGN.md:307` says “E4 derives holomorphy, C2, reality and the same Hessian bound for -h by negation.” The E4 assignment at line 377 includes “both signs”; design audit 2's F1 refutation paragraph expressly retains these four bridges in E4. The blueprint `blueprint-P/parts/p14a-amd-expsafe.tex:199` says “(iv) and (ii), (iii) hold for $-h$ as well.” These are the inputs needed by the negative-sign application at `stepP:p14:st-thr` (a278), beyond `HasDefiniteFastPart`.

**Delivered:** `KeplerData.lean:238–260` exports differentiability, complex C², reality and the nested-fderiv bound only for `planetaryKeplerC B.mass`. Its sole negated conclusion is `HasDefiniteFastPart ... (-planetaryKeplerC B.mass)` at line 256. `hasDefiniteFastPart_neg` (line 181) proves real regularity, real frequency and real definiteness; it supplies none of the four missing complex analytic clauses. The generic calculus helpers concern `keplerSumGen`, with no theorem about its negative. A search for all new names outside this file found no companion implementation.

**Refutation attempt:** Exact signature agreement is real, but the design intentionally leaves these bridges outside that signature. Generic Mathlib negation/fderiv lemmas make the obligations straightforward; availability of that API does not constitute the assigned production proof. Both definite-fast-part signs are proved, so this is not a complaint about their sign convention. The handoff's assertion that the summary list is entirely conjuncts of `h_data` misses this explicit design/source obligation.

**Required repair:** Keep `h_data` unchanged. Add distinctly named ordinary helpers deriving, on the same action neighbourhood and for the same M, `DifferentiableOn ℂ (-h)`, `ContDiffOn ℂ 2 (-h)`, zero imaginary part at real points, and `‖fderiv ℂ (fderiv ℂ (-h)) z‖ ≤ M`. A bundled companion theorem is acceptable. Re-audit the added public exports and their axioms/kernel replay. No extra source premise or new frozen statement is needed.

## Declaration and node ledger

Names below are in `KAM.Planetary`. PASS refers to the listed declaration/obligation, not to completion of P-EXP-SAFE.

| Node / role | Lean declaration | Verdict | Reason |
|---|---|---|---|
| Generic Kepler formula | `keplerSumGen` (41) | PASS | Literal total rational sum over either scalar field. |
| hd-ii calculus | `keplerSumGen_contDiffOn` (48) | PASS | Every requested order, over ℝ/ℂ, on nowhere-zero coordinates; no extra analytic premise. |
| Derivative object | `keplerSumGenD` (73) | PASS | Correct sum of weighted coordinate projections. |
| hd-ii derivative | `keplerSumGen_hasFDerivAt` (76) | PASS | Correct first derivative m³/z³, guarded by coordinate nonvanishing. |
| Derivative identification | `keplerSumGen_fderiv_eq` (95) | PASS | Literal Fréchet derivative equals the explicit CLM. |
| hd-iv derivative | `keplerSumGenD_hasFDerivAt` (99) | PASS | Correct second derivative coefficient −3m³/z⁴ and curried CLM. |
| hd-iv diagonal formula | `keplerSumGen_fderiv2_apply` (116) | PASS | Uses equality on a genuine open neighbourhood to differentiate fderiv. |
| hd-iv norm | `keplerSumGen_hess_norm_le` (134) | PASS | Two successive `ContinuousLinearMap.opNorm_le_bound` applications and sum triangle inequality; max norm on each argument, sum of diagonal magnitudes. |
| hd-ii collar | `keplerData_margin` (156) | PASS | Required lower margin plus stronger upper coordinate-norm bound. hrho positivity is unnecessary for this helper. |
| hd-v sign bridge | `hasDefiniteFastPart_neg` (181) | PASS | Negates the global sign, frequency and Hessian, preserving g,v and real C³. Conditional transport helper is distinctly named and does not stand in for h_data. |
| Real embedding | `planetaryKeplerC_ofReal` (212) | PASS | Exact real-to-complex formula, valid even at zero coordinates under total division. |
| Real restriction | `realPart_planetaryKeplerC` (216) | PASS | Frozen realPart equals the actual real rational sum. |
| Complex identification | `planetaryKeplerC_eq` (221) | PASS | Equality by `rfl`; no replacement Hamiltonian. |
| hd-v frequency | `keplerSumGen_real_freq` (224) | PASS | Correct coordinate derivative on Pi.single. |
| hd-v Hessian | `keplerSumGen_real_hess` (229) | PASS | Correct negative sum of weighted squares. |
| bpP:p14:h-data, approved signature | `h_data` (238) | PASS | Statement byte-identical to signature 276–298; no added premises, altered carrier, weakened conjunct or widened constant. |
| stepP:p14:hd-i | `h_data` (266–273) | PASS | Closed ball about an interior point of open G lies inside open G′ using rho≤kappa. |
| stepP:p14:hd-ii (including iii), h | `h_data` (298–307, 353–357) | PASS | Coordinate margin excludes all poles, C² and differentiability follow, real trace is genuinely real. |
| stepP:p14:hd-iv, h | `h_data` (358–370) | PASS | The exact sum M bounds the nested complex derivative; no matrix-norm substitution. |
| stepP:p14:hd-v | `h_data` (308–354) | PASS | h uses σ=−1; negation uses σ=+1. Both frozen predicates hold with identical positive constants. |
| Complete both-sign analytic E4 slice | No companion exports | FAIL | F1: absent holomorphy/C²/reality/Hessian bound for −h. |

The two private scalar derivative helpers (`hasDerivAt_inv_sq`, `hasDerivAt_inv_cube`) were also read: quotient-rule proofs with nonzero denominator premises, giving −c/z³ and −3c/z⁴ respectively.

## Constants, definitions and soundness

The only new definitions are `keplerSumGen` and `keplerSumGenD`. Both are intended total algebraic objects over all `Fin n → 𝕜`, including n=0 and zero coordinates. Lean's total division agrees with the blueprint's explicitly total Hamiltonian (a196). Differentiation and analytic claims are guarded by nowhere-zero coordinates; `h_data` proves this from the collar margin, so no proof relies on a junk value at a pole. `keplerSumGenD` is asserted to be the derivative only on that nonzero locus. There are no new abbreviations, structures, instances or bundled assumed proof obligations.

The existing `planetaryKeplerC`, `fastBox`, `EnlargedData` and frozen predicates retain their actual definitions. `EnlargedData` contains geometric source inequalities; it does not assume any h-data conclusion. `n≥2` produces a nonempty index set; `Finset.exists_min_image` supplies attaining indices for g,v. Positivity follows from positive masses/axes and kappa. The exact equality fixes M. Applying each lower-bound clause at the other's attaining index proves uniqueness of g,v mathematically, and hence their independence of rho,e,A. The design (304–306) also calls for a Lean uniqueness proof; no separately named uniqueness lemma is delivered. This is a documentation/implementation note: the exact signed-off characterization already entails that dependence, so it is not a separate statement-fidelity blocker.

The curried Hessian lives in `(Fin n → ℂ) →L[ℂ] ((Fin n → ℂ) →L[ℂ] ℂ)`. Lines 138–139 bound each operator norm in succession, and lines 358–370 use `Re z_i ≤ ‖z_i‖` and the positive 5 lower_i/8 margin to obtain the exact prescribed sum. The old maximum-vs-sum error from blueprint review F14A-01 does not recur.

## Hygiene and independent validation

Static checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
- `git diff --check inp...HEAD`: empty, exit 0.
- 374 lines, valid copyright/module/public imports/docstring/exposed public section; no forbidden proof escapes, resource overrides or `EuclideanSpace`.
- All 16 public declaration names searched against other KAM Lean files: no duplicate short declaration name or existing root export found.
- Recursive source-import traversal: 85 KAM modules including the target, **zero frozen theorem modules, zero provider modules**. No imported DRAFT_SORRY theorem; manifest-state exceptions are unnecessary.
- Source SHA-256: `9ce84cf08045591836b15d83088f3936e0cc3da065e0ac0cb5a477199d88cce7`.
- Signature SHA-256: `24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88` (live file, not the older hash in design audit 2).
- The signature substring from `theorem h_data` through its conclusion was compared byte-for-byte with production: `True`.

E4 contains no provider export and seals no anchor. Provider/frozen-type equality and seal-body probes therefore do not apply. Instead the audit probe copies the exact h_data statement under `example` and proves it with `exact h_data hn B hB hd hrho hrk`, testing the full explicit telescope against the delivered declaration. It also queries axioms of all 14 new public theorems.

Validation receipts follow below. All Lean-related commands are sequential, use `LEAN_NUM_THREADS=1` and run at niceness 5. The targeted build uses the prescribed compile gate; no clean/update/cache fetch/root regeneration was performed.

## Errata, deviations and limits

No new suspected defect in a pinned mathematical source or frozen statement was found. The local blueprint and design agree on the missing negation obligations; F1 is an implementation omission and the handoff's completeness claim is inaccurate. The previous blueprint norm defect is repaired in the current source and implementation. No deviations were introduced by the auditor. This audit does not certify pending N/P root theorems, source-PDF content beyond the supplied contracts, or consumer closure of the full exponential-safety theorem.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-e4 KAM.Planetary.Exponential.KeplerData
```

Exit 0. Gate output: `[inp-gate] slot 2 acquired 17:01:48 for KAM.Planetary.Exponential.KeplerData`.
Final output: `Build completed successfully (9131 jobs).`
Replayed pre-existing unused-variable warnings occurred in `KAM/Kepler/Energy.lean:106`, `KAM/Planetary/Poincare/Chart.lean:212,247` and `KAM/Kepler/Mass.lean:147,157,500,524`. No E4 elaboration error or heartbeat design signal occurred.

### Exact-signature probe and all public theorem axioms

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/E4Audit.lean
```

Exit 0. The exact signature example elaborated without error. Complete axiom output:

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
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Exponential.KeplerData
```

Exit 0. Complete output:

```text
replaying KAM.Planetary.Exponential.KeplerData
```

All E4 public and private lemma bodies are in that single module; no provider or separate E4 lemma module exists to add to the invocation.

### Source lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the permitted generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (793 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Hygiene verdict: **PASS WITH NOTES**, under the audit brief's explicit stale-root allowance. `KAM.lean` was not regenerated. This allowed exception is independent of the package-completeness FAIL above.

### Final audit state

The exact-signature probe, targeted build, all public theorem axiom checks and kernel replay passed. Lint has only the permitted stale generated-root exception. The temporary `E4Audit.lean` probe was deleted. Final repository status contains only the new audit report and the pre-existing untracked E4 handoff; tracked production files remain unchanged. `git diff --check inp...HEAD` and the protected-path diff remain empty.

**Disposition:** `h_data` as signed off: **PASS**. E4 as the complete design-assigned both-sign package: **FAIL (F1)**. No frozen anchor is sealed or claimed seal-ready by this infrastructure audit. Return E4 for the four analytic negation bridges, retaining the exact `h_data` telescope and curried Hessian norm.
