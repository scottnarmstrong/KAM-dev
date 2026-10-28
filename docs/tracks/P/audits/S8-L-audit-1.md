# S8-L independent package audit 1

Overall verdict: **PASS WITH NOTES** for S8-L, at HEAD `8462506eafec1cd2e99711f11787c647cdc60a5a` (2026-10-28). The five design-facing declarations pass statement/body fidelity; all 38 public theorem exports pass the axiom check. This is a helper-package audit, **not a frozen-anchor seal or track/root closure**. There is no S8-L provider or frozen theorem to seal; provider=frozen-type and copied frozen-seal-body probes are inapplicable. Exact design-type applications were checked instead.

## Authority, scope and comparisons

Read the supplied AGENTS.md, PLAN.md, DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, S8-L handoff and its AUDIT FOCUS; the revision-2 P810 design, Appendix A, both design audits, current original signatures, track P statement, and Part 8 source statements/proofs. Applied the statement-audit skill to the design-facing types and literal definition bodies. The user explicitly overrides the generic brief's report destination: this report is inside `/root/code/KAM-inp-s8l`.

The design audits and original signatures are absent at the handoff's relative worktree locations. Read their authoritative copies under `/root/code/KAM-inp/docs/tracks/P/design/DESIGN-P810-design-audit-{1,2}.md` and `/root/code/KAM-inp/.drafts/design/P810Signatures.lean`. Signature SHA-256: `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`, matching design audit 2. No draft signatures were imported into production or used as proof dependencies.

Audited only these four modules (all new):

| File under `KAM/Planetary/SecularForm/` | Lines | Role |
|---|---:|---|
| `LaplacePoch.lean` | 102 | Finite product, binomial series, Gamma growth |
| `LaplaceSeries.lean` | 152 | Complex binomial product and absolutely summable double series |
| `LaplaceCoeff.lean` | 193 | Literal integral/series, orthogonality, coefficient extraction |
| `Laplace.lean` | 146 | Public facade, positivity, holomorphy and Fourier expansion |

Requested comparisons were run: `git diff inp...HEAD` and `git diff inp-s8b...HEAD`. Current `inp` is `5991245cabc06e69ec900cb6006b45f72cc85eb0`; current `inp-s8b` is `326288529ed59457294068ad2b05b5b9295b3099`. Git warns that `inp...HEAD` has multiple merge bases and selects `6f2cb1ec6284a98aaffeed74340762f20f4afc04` (the other is `408ea7a6f026a1ecf1d0cf0e988bdc54494497f9`). The broad comparisons include inherited packages outside this audit. The S8-L-only commit interval `c5d87a6..HEAD` adds exactly these four files, 593 lines, and no other file.

**Protected-path note:** `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**: inherited `KAM.lean` changes add 12 imports for Finite*, RealSlice, Collar and OneScale. Frozen files, manifest and README have no differences. `git diff c5d87a6..HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. Thus the generic brief's broad protected-path-empty condition does not literally hold; the focused S8-L implementation has no protected-path edit. This is recorded, not silently repaired or charged to S8-L.

## Main contracts and expanded binders

All names below have prefix `KAM.Planetary.SecularForm`. Design locators: P810 design :690–706 (`laplace_def`, `poch`, `laplaceTerm`, `laplaceC`, `laplace`), :1175–1178 (`e_poch`), :1446–1448 (`laplace_fourier`); package row :423. Blueprint locators: `blueprint-P/parts/p8-secular-form.tex`:30,110–124.

| Export / node | Verdict | Evidence |
|---|---|---|
| `poch` / `bpP:p8:e-poch` | PASS | Exact finite product, empty product 1; same definition body as signatures. |
| `e_poch` / `bpP:p8:e-poch` | PASS | Exact recurrence, binomial `HasSum` and atTop growth; Big-O constant is scoped after fixed s. |
| `laplace_def` / `bpP:p8:laplace-def` | PASS | Exact `(2π)⁻¹` cosine integral over `[0,2π]`, integer mode. |
| `laplace` / `bpP:p8:laplace` | PASS | All eight conjuncts, endpoint values, nonnegative/strict-positive distinction and unit-disc complex function preserved. |
| `laplace_fourier` / `bpP:p8:laplace-def` | PASS | Exact complex `HasSum` indexed by all integers, positive exponential sign and unscaled radian angle. |
| `hasSum_kernel_complex` / `stepP:p8:la-exp` | PASS | Proves absolute double-series expansion; no assumed convergence or branch equality. |
| `hasSum_laplaceTerm`, `differentiableOn_laplaceC` / `stepP:p8:la-conv` | PASS | Series convergence and local uniform majorants prove the requested disc holomorphy directly. |

Binder bins: SOURCE = source domain/premise; TYPING = scalar or index data. STANDING, RULED and EXCESS counts are all zero. No hidden project structures or typeclass assumptions occur in these three theorem types. Implicitness and outer-to-inner order match the signatures. The source positivity guard `s>0` is inherited by the Laplace lemma from the immediately preceding definition.

| Theorem | Binder | Bin | Source |
|---|---|---|---|
| `e_poch` | `{s : ℝ}` | TYPING | design :1175; blueprint :30 |
| `e_poch` | `(hs : 0 < s)` | SOURCE | design :1175 |
| `laplace` | `{s : ℝ}` | TYPING | design :698 |
| `laplace` | `(hs : 0 < s)` | SOURCE | design :698; blueprint :110–116 |
| `laplace` | `(k : ℕ)` | TYPING | design :698; blueprint :117 |
| `laplace` | `{α : ℝ}` | TYPING | design :698 |
| `laplace` | `(hα : 0 ≤ α)` | SOURCE | design :698; blueprint :117 |
| `laplace` | `(hα1 : α < 1)` | SOURCE | design :698; blueprint :117 |
| `laplace_fourier` | `{s : ℝ}` | TYPING | design :1446 |
| `laplace_fourier` | `{α : ℝ}` | TYPING | design :1446 |
| `laplace_fourier` | `(hs : 0 < s)` | SOURCE | design :1446; blueprint :110 |
| `laplace_fourier` | `(hα : 0 ≤ α)` | SOURCE | design :1446; blueprint :110 |
| `laplace_fourier` | `(hα1 : α < 1)` | SOURCE | design :1446; blueprint :110 |
| `laplace_fourier` | `(t : ℝ)` | TYPING | design :1446; blueprint :111 |

Counts `(SOURCE, STANDING, TYPING, RULED, EXCESS)`: `e_poch=(1,0,1,0,0)`, `laplace=(3,0,3,0,0)`, `laplace_fourier=(3,0,3,0,0)`. Inner `q,z`, summation indices and the positive-α implication remain universally quantified/conclusion-local, not extra assumptions.

## Public declaration inventory

Every theorem listed here was read and independently axiom-checked. Helpers implement proof cuts, not extra premises of the main exports. Scalar/index binders are typing data; their only propositional inputs are the positivity/unit-interval/unit-ball guards explicitly shown in their source types. In particular no helper accepts a series identity, integral equality, analyticity, growth estimate or other unpaid proof step as an input.

| Node / role | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| `e-poch` | `poch_eq_ascPochhammer` (LaplacePoch:28) | PASS | Literal finite product equals Mathlib polynomial evaluation, all real s. |
| `e-poch` | `poch_nonneg` (LaplacePoch:34) | PASS | s>0 implies product nonnegative; no extra input. |
| `e-poch` | `poch_pos` (LaplacePoch:37) | PASS | s>0 implies every factor strictly positive. |
| `e-poch` | `choose_eq_poch_div` (LaplacePoch:40) | PASS | Generalized binomial coefficient identity for every real s and natural q. |
| `e-poch` | `poch_binomial` (LaplacePoch:47) | PASS | Stronger helper: arbitrary real s; only |z|<1. |
| `e-poch` | `poch_succ` (LaplacePoch:61) | PASS | Stronger helper: recurrence for every real s. |
| `e-poch` | `poch_div_factorial_isBigO` (LaplacePoch:64) | PASS | Gamma limit proves growth for s>0, not assumed. |
| `e-poch` | `e_poch` (LaplacePoch:95) | PASS | Exact design conjunction. |
| `la-exp` | `pcoef_nonneg` (LaplaceSeries:33) | PASS | Nonnegativity under source s>0. |
| `la-exp` | `pcoef_pos` (LaplaceSeries:36) | PASS | Strict positivity under source s>0; factorial nonzero. |
| `la-exp` | `summable_pcoef_mul_pow` (LaplaceSeries:39) | PASS | Source guards; unused _hs is redundant, not a hard obligation. |
| `la-exp` | `kernelWeight_nonneg` (LaplaceSeries:43) | PASS | Source guards s>0 and α≥0. |
| `la-exp` | `summable_kernelWeight` (LaplaceSeries:49) | PASS | Product of proved summable nonnegative sequences. |
| `la-exp` | `kernelWeight_swap` (LaplaceSeries:57) | PASS | Unconditional symmetry on all scalar arguments. |
| `la-exp` | `hasSum_cpow_series` (LaplaceSeries:62) | PASS | Stronger helper: every real s; only complex norm<1. |
| `la-exp` | `kernelBase_norm_sq` (LaplaceSeries:79) | PASS | Unconditional algebra/trigonometry identity. |
| `la-exp` | `kernelBase_re_pos` (LaplaceSeries:85) | PASS | α∈[0,1) gives right half-plane, all real t. |
| `la-exp` | `hasSum_kernel_complex` (LaplaceSeries:91) | PASS | Source guards only; branch and absolute convergence proved. |
| `la-conv` | `integral_cos_int_mul` (LaplaceCoeff:42) | PASS | All integer modes, including zero and negative modes. |
| `la-conv` | `integral_cos_mul_cos` (LaplaceCoeff:53) | PASS | Exact two Kronecker terms /2; handles zero-mode overlap. |
| `la-conv` | `hasSum_kernel_real` (LaplaceCoeff:87) | PASS | Real part of proved complex HasSum. |
| `la-conv` | `hasSum_freqWeight_pair` (LaplaceCoeff:98) | PASS | Dominated termwise integration with proved summable majorant. |
| `la-conv` | `summable_freqWeight` (LaplaceCoeff:130) | PASS | Restriction bounded by proved summable full weight. |
| `la-conv` | `freqWeight_neg_swap` (LaplaceCoeff:140) | PASS | Unconditional frequency sign/swap identity. |
| `la-conv` | `tsum_freqWeight_neg` (LaplaceCoeff:147) | PASS | Unconditional reindexing by product swap equivalence. |
| `la-conv` | `laplace_def_eq_tsum` (LaplaceCoeff:152) | PASS | Source guards only; ±k equality removes cosine half-factor. |
| `la-conv` | `laplaceTerm_eq_kernelWeight` (LaplaceCoeff:166) | PASS | Unconditional exact coefficient formula. |
| `la-conv` | `hasSum_laplaceTerm` (LaplaceCoeff:172) | PASS | Injective parametrization q↦(q+k,q); complement weight zero. |
| `laplace / laplace-def` | `laplaceTerm_nonneg` (Laplace:30) | PASS | Source guards s>0, α≥0. |
| `laplace / laplace-def` | `laplaceTerm_pos` (Laplace:34) | PASS | Source guards s>0, α>0. |
| `laplace / laplace-def` | `laplaceTerm_eq_coef_mul` (Laplace:41) | PASS | Literal defining equation, no premise. |
| `laplace / laplace-def` | `laplace_def_neg` (Laplace:45) | PASS | Stronger helper: evenness for all real s, α and integer k. |
| `laplace / laplace-def` | `laplace_def_zero` (Laplace:51) | PASS | Stronger helper: endpoint formula for every real s. |
| `laplace / laplace-def` | `differentiableOn_laplaceC` (Laplace:63) | PASS | Only s>0; local summable majorant on every smaller ball. |
| `laplace / laplace-def` | `laplaceC_ofReal` (Laplace:86) | PASS | Exact real/complex identification on source interval. |
| `laplace / laplace-def` | `analyticOnNhd_laplace_def` (Laplace:93) | PASS | Only s>0; complex restriction and real-part composition. |
| `laplace / laplace-def` | `laplace` (Laplace:107) | PASS | Exact eight-conjunct design export. |
| `laplace / laplace-def` | `laplace_fourier` (Laplace:123) | PASS | Exact Fourier design export; fiberwise regrouping of absolute series. |

## Definition classification

All eight new definitions are literal formulas, not characterized/choice-defined objects. There is no new abbrev, structure, instance or bundled hypothesis. The four design definitions are definitionally equal to fresh copies of the original signature bodies on their **entire declared carriers**, checked by `rfl`.

| Definition | Classification and whole-carrier assessment | BODY_MATCH | PUBLIC_CARRIER | WELL_DEFINEDNESS | CHARACTERIZATION | CHOICE_INDEPENDENCE | Verdict |
|---|---|---|---|---|---|---|---|
| `poch` (LaplacePoch:26) | Finite rising-factorial product for every real s and natural q, including q=0 | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `pcoef` (LaplaceSeries:28) | Literal `poch / q!`; denominator always positive | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `kernelWeight` (LaplaceSeries:31) | Literal product coefficient for every real s, α and pair | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `laplace_def` (LaplaceCoeff:28) | Literal total interval-integral expression, exact signature | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `laplaceTerm` (LaplaceCoeff:31) | Literal coefficient times integer power, exact signature | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `laplaceC` (LaplaceCoeff:33) | Literal total `tsum`, exact signature; actual convergence/holomorphy proved on unit disc | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `freq` (LaplaceCoeff:37) | Integer difference of natural indices, no natural-subtraction truncation | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `freqWeight` (LaplaceCoeff:40) | Exact restriction/indicator of a frequency fiber | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |

The zero branch of `freqWeight` is the mathematical indicator of the fiber, not a fallback for an unproved result. The total-integral/total-tsum conventions outside the analytic domain are exactly the chosen design formulas; no theorem relies on nonintegrability or nonsummability defaults. At every identification/convergence use the proof establishes summability or invokes the dominated-integral theorem. No claim of analytic meaning outside the source domain or unit disc is made.

## Proof refutation checks

1. **Binomial and growth:** LaplacePoch:47–59 uses the real binomial power series on `|z|<1`, so `1-z>0` justifies negative real powers. :64–93 uses Euler's Gamma sequence and `Gamma(s)>0` to bound the inverse sequence, then the explicit product formula and an eventual positive-q identity. Neither the growth rate nor a nonzero Gamma value is assumed. `poch_binomial` and `poch_succ` are valid strengthenings to arbitrary real s.
2. **Complex branches:** LaplaceSeries:95–149 takes `x=1-α exp(it)` with strictly positive real part. This proves `x≠0` and excludes argument π before applying conjugation of `cpow`. The product with its conjugate is reduced through the squared norm to the positive real kernel. This avoids any unsupported global multiplicativity rule for principal complex powers. The norm majorant is the independently proved summable `kernelWeight`, uniform in t.
3. **Integral normalization and extraction:** LaplaceCoeff:42–85 handles the zero-mode overlap in the two cosine Kronecker terms. :98–129 supplies measurability, the bound by the weight, its summability, and integrability of the constant dominator before interchanging integration and the series. :140–164 uses product-swap symmetry to identify the +k and −k fiber sums, so the cosine factor 1/2 is removed correctly. The `1/(2π)` normalization is preserved, including k=0.
4. **Convergence:** LaplaceCoeff:172–190 reindexes the nonnegative k fiber by `(q+k,q)` and proves all terms outside its range vanish. Laplace:63–84 chooses `‖z‖<r<1`, uses the proven real-r series as a summable majorant, and applies complex differentiability of a dominated series. No derivative convergence or analyticity hypothesis is inserted.
5. **Real restriction and positivity:** Laplace:86–105 identifies the complex series on the actual real interval and restricts complex analyticity through ofReal and real part. :107–121 proves nonnegative values and strict positivity only for α>0, with the exact special value at zero. It does not repeat the old false endpoint positivity claim.
6. **Fourier reconstruction:** Laplace:123–143 uses `HasSum.tsum_fiberwise` on the proved absolutely summable complex double series, identifies the exact frequency `a-b`, and substitutes the already proved integral coefficient. This proves the literal all-integer Fourier statement with no additional premise.

## Imports and hygiene

Static KAM import-closure traversal from the facade found **67 KAM modules**, including **47 frozen imports, all manifest state SEALED**, and **zero provider imports**. The directly inherited frozen imports from Basic are SecularAverage, Assemble and PlaneLength (their literal definitions were read); the closure contains only frozen definitions and no DRAFT_SORRY theorem. The new proofs use no physical-data fields, norm replacements or hidden assumption structures.

All four files have copyright/license/authors, `module`, public imports, module docstring and an exposed public noncomputable section. Every new definition is covered by `@[expose]`. All file sizes are below 1500. Static inspection and source lint find no sorry/admit/axiom/unsafe/opaque, heartbeat/recursion/synthesis overrides, or EuclideanSpace in these modules. `git diff --check inp...HEAD -- KAM/Planetary/SecularForm/Laplace*.lean` passed (exit 0; same multiple-merge-base warning only).

### Independent commands and receipts

Targeted build (one facade target through the prescribed gate):

```text
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-s8l KAM.Planetary.SecularForm.Laplace
[inp-gate] slot 1 acquired 09:57:04 for KAM.Planetary.SecularForm.Laplace
Build completed successfully (9113 jobs).
exit 0
```

The gate runs `nice -n 5 lake build`. Replayed warnings are pre-existing unused binders in Kepler.Energy, Poincare.Chart and Kepler.Mass; no S8-L error or warning was emitted. This is the targeted incremental build, not a library clean/rebuild.

Exact-type, definition-body and axiom probe:

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S8LAuditProbe.lean
exit 0
3 independently copied original-signature theorem applications: PASS
4 independently copied original-signature definition equations, by rfl: PASS
38 #print axioms commands: all [propext, Classical.choice, Quot.sound]
```

The three applications were exactly `e_poch hs`, `laplace hs k hα hα1` and `laplace_fourier hs hα hα1 t`, each against the copied **complete** original signature. No imported draft body or provider stands in for a frozen export.

Kernel replay, one invocation with all four module names:

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Planetary.SecularForm.Laplace \
  KAM.Planetary.SecularForm.LaplacePoch \
  KAM.Planetary.SecularForm.LaplaceSeries \
  KAM.Planetary.SecularForm.LaplaceCoeff
replaying KAM.Planetary.SecularForm.LaplaceCoeff
replaying KAM.Planetary.SecularForm.LaplaceSeries
replaying KAM.Planetary.SecularForm.LaplacePoch
replaying KAM.Planetary.SecularForm.Laplace
exit 0
```

Full axiom output (same order as the transient probe):

```text
'KAM.Planetary.SecularForm.laplaceTerm_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.laplaceTerm_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.laplaceTerm_eq_coef_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.laplace_def_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.laplace_def_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.differentiableOn_laplaceC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.laplaceC_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.analyticOnNhd_laplace_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.laplace' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.laplace_fourier' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.integral_cos_int_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.integral_cos_mul_cos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.hasSum_kernel_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.hasSum_freqWeight_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.summable_freqWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.freqWeight_neg_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.tsum_freqWeight_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.laplace_def_eq_tsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.laplaceTerm_eq_kernelWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.hasSum_laplaceTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.poch_eq_ascPochhammer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.poch_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.poch_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.choose_eq_poch_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.poch_binomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.poch_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.poch_div_factorial_isBigO' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.e_poch' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pcoef_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pcoef_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.summable_pcoef_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.kernelWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.summable_kernelWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.kernelWeight_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.hasSum_cpow_series' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.kernelBase_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.kernelBase_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.hasSum_kernel_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Helper binder audit

One row per binder below; rows for the three main contracts are above. All other explicit/implicit term arguments are enumerated here. SOURCE guards refer to p8:110–123 (and p8:30 for Pochhammer); TYPING entries are scalar/index data for those proof cuts. No STANDING, RULED or EXCESS binder occurs. There are no instance binders in these project theorem headers.

| Helper | Binder | Bin |
|---|---|---|
| `laplaceTerm_nonneg` | `{s : ℝ}` | TYPING |
| `laplaceTerm_nonneg` | `(hs : 0 < s)` | SOURCE |
| `laplaceTerm_nonneg` | `{α : ℝ}` | TYPING |
| `laplaceTerm_nonneg` | `(hα : 0 ≤ α)` | SOURCE |
| `laplaceTerm_nonneg` | `(k : ℕ)` | TYPING |
| `laplaceTerm_nonneg` | `(q : ℕ)` | TYPING |
| `laplaceTerm_pos` | `{s : ℝ}` | TYPING |
| `laplaceTerm_pos` | `(hs : 0 < s)` | SOURCE |
| `laplaceTerm_pos` | `{α : ℝ}` | TYPING |
| `laplaceTerm_pos` | `(hα : 0 < α)` | SOURCE |
| `laplaceTerm_pos` | `(k : ℕ)` | TYPING |
| `laplaceTerm_pos` | `(q : ℕ)` | TYPING |
| `laplaceTerm_eq_coef_mul` | `(s : ℝ)` | TYPING |
| `laplaceTerm_eq_coef_mul` | `(k : ℕ)` | TYPING |
| `laplaceTerm_eq_coef_mul` | `(q : ℕ)` | TYPING |
| `laplaceTerm_eq_coef_mul` | `(r : ℝ)` | TYPING |
| `laplace_def_neg` | `(s : ℝ)` | TYPING |
| `laplace_def_neg` | `(k : ℤ)` | TYPING |
| `laplace_def_neg` | `(α : ℝ)` | TYPING |
| `laplace_def_zero` | `(s : ℝ)` | TYPING |
| `laplace_def_zero` | `(k : ℕ)` | TYPING |
| `differentiableOn_laplaceC` | `{s : ℝ}` | TYPING |
| `differentiableOn_laplaceC` | `(hs : 0 < s)` | SOURCE |
| `differentiableOn_laplaceC` | `(k : ℕ)` | TYPING |
| `laplaceC_ofReal` | `{s : ℝ}` | TYPING |
| `laplaceC_ofReal` | `(hs : 0 < s)` | SOURCE |
| `laplaceC_ofReal` | `(k : ℕ)` | TYPING |
| `laplaceC_ofReal` | `{α : ℝ}` | TYPING |
| `laplaceC_ofReal` | `(hα : 0 ≤ α)` | SOURCE |
| `laplaceC_ofReal` | `(hα1 : α < 1)` | SOURCE |
| `analyticOnNhd_laplace_def` | `{s : ℝ}` | TYPING |
| `analyticOnNhd_laplace_def` | `(hs : 0 < s)` | SOURCE |
| `analyticOnNhd_laplace_def` | `(k : ℕ)` | TYPING |
| `integral_cos_int_mul` | `(n : ℤ)` | TYPING |
| `integral_cos_mul_cos` | `(k : ℤ)` | TYPING |
| `integral_cos_mul_cos` | `(m : ℤ)` | TYPING |
| `hasSum_kernel_real` | `{s : ℝ}` | TYPING |
| `hasSum_kernel_real` | `{α : ℝ}` | TYPING |
| `hasSum_kernel_real` | `(hs : 0 < s)` | SOURCE |
| `hasSum_kernel_real` | `(hα : 0 ≤ α)` | SOURCE |
| `hasSum_kernel_real` | `(hα1 : α < 1)` | SOURCE |
| `hasSum_kernel_real` | `(t : ℝ)` | TYPING |
| `hasSum_freqWeight_pair` | `{s : ℝ}` | TYPING |
| `hasSum_freqWeight_pair` | `{α : ℝ}` | TYPING |
| `hasSum_freqWeight_pair` | `(hs : 0 < s)` | SOURCE |
| `hasSum_freqWeight_pair` | `(hα : 0 ≤ α)` | SOURCE |
| `hasSum_freqWeight_pair` | `(hα1 : α < 1)` | SOURCE |
| `hasSum_freqWeight_pair` | `(k : ℤ)` | TYPING |
| `summable_freqWeight` | `{s : ℝ}` | TYPING |
| `summable_freqWeight` | `{α : ℝ}` | TYPING |
| `summable_freqWeight` | `(hs : 0 < s)` | SOURCE |
| `summable_freqWeight` | `(hα : 0 ≤ α)` | SOURCE |
| `summable_freqWeight` | `(hα1 : α < 1)` | SOURCE |
| `summable_freqWeight` | `(k : ℤ)` | TYPING |
| `freqWeight_neg_swap` | `(s : ℝ)` | TYPING |
| `freqWeight_neg_swap` | `(α : ℝ)` | TYPING |
| `freqWeight_neg_swap` | `(k : ℤ)` | TYPING |
| `freqWeight_neg_swap` | `(p : ℕ × ℕ)` | TYPING |
| `tsum_freqWeight_neg` | `(s : ℝ)` | TYPING |
| `tsum_freqWeight_neg` | `(α : ℝ)` | TYPING |
| `tsum_freqWeight_neg` | `(k : ℤ)` | TYPING |
| `laplace_def_eq_tsum` | `{s : ℝ}` | TYPING |
| `laplace_def_eq_tsum` | `{α : ℝ}` | TYPING |
| `laplace_def_eq_tsum` | `(hs : 0 < s)` | SOURCE |
| `laplace_def_eq_tsum` | `(hα : 0 ≤ α)` | SOURCE |
| `laplace_def_eq_tsum` | `(hα1 : α < 1)` | SOURCE |
| `laplace_def_eq_tsum` | `(k : ℤ)` | TYPING |
| `laplaceTerm_eq_kernelWeight` | `(s : ℝ)` | TYPING |
| `laplaceTerm_eq_kernelWeight` | `(α : ℝ)` | TYPING |
| `laplaceTerm_eq_kernelWeight` | `(k : ℕ)` | TYPING |
| `laplaceTerm_eq_kernelWeight` | `(q : ℕ)` | TYPING |
| `hasSum_laplaceTerm` | `{s : ℝ}` | TYPING |
| `hasSum_laplaceTerm` | `{α : ℝ}` | TYPING |
| `hasSum_laplaceTerm` | `(hs : 0 < s)` | SOURCE |
| `hasSum_laplaceTerm` | `(hα : 0 ≤ α)` | SOURCE |
| `hasSum_laplaceTerm` | `(hα1 : α < 1)` | SOURCE |
| `hasSum_laplaceTerm` | `(k : ℕ)` | TYPING |
| `poch_eq_ascPochhammer` | `(s : ℝ)` | TYPING |
| `poch_eq_ascPochhammer` | `(q : ℕ)` | TYPING |
| `poch_nonneg` | `{s : ℝ}` | TYPING |
| `poch_nonneg` | `(hs : 0 < s)` | SOURCE |
| `poch_nonneg` | `(q : ℕ)` | TYPING |
| `poch_pos` | `{s : ℝ}` | TYPING |
| `poch_pos` | `(hs : 0 < s)` | SOURCE |
| `poch_pos` | `(q : ℕ)` | TYPING |
| `choose_eq_poch_div` | `(s : ℝ)` | TYPING |
| `choose_eq_poch_div` | `(q : ℕ)` | TYPING |
| `poch_binomial` | `{s : ℝ}` | TYPING |
| `poch_binomial` | `(z : ℝ)` | TYPING |
| `poch_binomial` | `(hz : |z| < 1)` | SOURCE |
| `poch_succ` | `(s : ℝ)` | TYPING |
| `poch_succ` | `(q : ℕ)` | TYPING |
| `poch_div_factorial_isBigO` | `{s : ℝ}` | TYPING |
| `poch_div_factorial_isBigO` | `(hs : 0 < s)` | SOURCE |
| `pcoef_nonneg` | `{s : ℝ}` | TYPING |
| `pcoef_nonneg` | `(hs : 0 < s)` | SOURCE |
| `pcoef_nonneg` | `(q : ℕ)` | TYPING |
| `pcoef_pos` | `{s : ℝ}` | TYPING |
| `pcoef_pos` | `(hs : 0 < s)` | SOURCE |
| `pcoef_pos` | `(q : ℕ)` | TYPING |
| `summable_pcoef_mul_pow` | `{s : ℝ}` | TYPING |
| `summable_pcoef_mul_pow` | `{α : ℝ}` | TYPING |
| `summable_pcoef_mul_pow` | `(_hs : 0 < s)` | SOURCE |
| `summable_pcoef_mul_pow` | `(hα : 0 ≤ α)` | SOURCE |
| `summable_pcoef_mul_pow` | `(hα1 : α < 1)` | SOURCE |
| `kernelWeight_nonneg` | `{s : ℝ}` | TYPING |
| `kernelWeight_nonneg` | `{α : ℝ}` | TYPING |
| `kernelWeight_nonneg` | `(hs : 0 < s)` | SOURCE |
| `kernelWeight_nonneg` | `(hα : 0 ≤ α)` | SOURCE |
| `kernelWeight_nonneg` | `(p : ℕ × ℕ)` | TYPING |
| `summable_kernelWeight` | `{s : ℝ}` | TYPING |
| `summable_kernelWeight` | `{α : ℝ}` | TYPING |
| `summable_kernelWeight` | `(hs : 0 < s)` | SOURCE |
| `summable_kernelWeight` | `(hα : 0 ≤ α)` | SOURCE |
| `summable_kernelWeight` | `(hα1 : α < 1)` | SOURCE |
| `kernelWeight_swap` | `(s : ℝ)` | TYPING |
| `kernelWeight_swap` | `(α : ℝ)` | TYPING |
| `kernelWeight_swap` | `(p : ℕ × ℕ)` | TYPING |
| `hasSum_cpow_series` | `{s : ℝ}` | TYPING |
| `hasSum_cpow_series` | `(z : ℂ)` | TYPING |
| `hasSum_cpow_series` | `(hz : ‖z‖ < 1)` | SOURCE |
| `kernelBase_norm_sq` | `(α : ℝ)` | TYPING |
| `kernelBase_norm_sq` | `(t : ℝ)` | TYPING |
| `kernelBase_re_pos` | `{α : ℝ}` | TYPING |
| `kernelBase_re_pos` | `(hα : 0 ≤ α)` | SOURCE |
| `kernelBase_re_pos` | `(hα1 : α < 1)` | SOURCE |
| `kernelBase_re_pos` | `(t : ℝ)` | TYPING |
| `hasSum_kernel_complex` | `{s : ℝ}` | TYPING |
| `hasSum_kernel_complex` | `{α : ℝ}` | TYPING |
| `hasSum_kernel_complex` | `(hs : 0 < s)` | SOURCE |
| `hasSum_kernel_complex` | `(hα : 0 ≤ α)` | SOURCE |
| `hasSum_kernel_complex` | `(hα1 : α < 1)` | SOURCE |
| `hasSum_kernel_complex` | `(t : ℝ)` | TYPING |

Helper totals `(SOURCE, STANDING, TYPING, RULED, EXCESS) = (44,0,89,0,0)`. Positivity guards on intermediate summability helpers retain the source s>0 restriction; the unused `_hs` may be removed as optional cleanup, but is not an assumed hard proof step.

## Final lint, notes and closeout

Final source lint was run after the probe and kernel replay had finished:

```text
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (524 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The exit 1 is exclusively the explicitly permitted stale generated-root condition. The root was not regenerated. Audit execution note: the first lint launcher omitted explicit thread/nice settings; the final serialized run above corrects that invocation and is the reported compliant receipt. Builds, the independent probe and kernel replay used `LEAN_NUM_THREADS=1`; no additional auditor-controlled Lean job was launched during the final lint's ABI probe.

**Notes:** (1) The inherited broad-diff root edit is recorded above; no S8-L protected-path edits exist. (2) Generated root imports omit the four new modules, explaining the permitted lint exception. (3) `summable_pcoef_mul_pow` retains an unused source positivity hypothesis, optional cleanup only. None changes the design-facing result types or supplies an unpaid proof.

**Suspected errata/deviations:** no new mathematical source or blueprint defect found. The blueprint's existing warning at p8:125–126 quotes Fej04r Lemma 76's global-meromorphy assertion and rejects it because the half-order zero mode has a logarithmic singularity. S8-L uses only local unit-disc holomorphy and does not rely on that assertion. This audit compared the pinned repository blueprint and exact design; it did not independently re-audit the underlying source PDFs or certify new source-paper errata. No implementation deviation from the designated signatures was introduced. The initial lint invocation note is an audit-procedure deviation, corrected by the final run.

**Limits and handoff:** S8-L exports are proved helper infrastructure. No frozen theorem, provider, consumer theorem, global meromorphic continuation, planetary torsion result or track headline is certified closed by this report. No remaining mathematical blocker was identified within the assigned four-file scope. All transient audit probes, logs and the report-generation helper were removed from `.lake/abi-scratch/` after recording their evidence. Only this report was added by the auditor; the pre-existing untracked S8-L handoff was preserved. No source, generated file, frozen file, manifest, package cache or git state was edited. Final report validation checked the 38-theorem inventory, eight-definition classification, complete axiom receipts and whitespace; `git diff --check` exits 0.
