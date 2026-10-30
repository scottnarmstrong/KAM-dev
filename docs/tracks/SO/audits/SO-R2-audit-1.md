# SO-R2 independent package audit 1

Verdict: **PASS WITH NOTES** for the parameter package and generic/R2 assembly. No mathematical or proof-hygiene blocker found. The only failing required check is the expressly allowed stale generated `KAM.lean` check. No frozen anchor is proposed or proved by this package, so “seal-ready per anchor” is not applicable. This audit does not close the numerical certificate or the lunar headline.

Audited worktree: `/root/code/KAM-inp-sor2`. HEAD `19bf1a6344eb52e7e5d0b260942c580c56278797`; comparison branch `inp` at `1c6d2312e7d77f1a480555297c35789ce0edb2f1`; merge base `b0efa1c0595448bcf4b6aecac3c60eff3abdf80f`. Reviewed the complete `git diff inp...HEAD`: exactly two added Lean modules and the handoff, 424 added lines. No landed declaration changed. The user-specified report location overrides the generic brief's main-worktree output location.

Read AGENTS.md, PLAN.md, DECISIONS.md, the package-audit brief and SO-R2 handoff. SO has no `statement.md` or assigned I/N/P blueprint node for these additions. The controlling comparisons are SO-GEN3's **Full study**, SO-DION's landed `RotFreqN`, landed `LunarAssemblySharp`, the certificate definitions and sharp soundness interface; the SO design/freeze proposal and sharp isoenergetic blueprint supply context. The two SO-GEN3 source files are absent in this older package checkout but present on `inp`; inspected them with `git show inp:<path>`, without copying changes into the worktree. The transitive frozen imports are 24 SEALED definitions, with no frozen theorem or provider import. Relevant frozen Diophantine/strip and isoenergetic definitions were inspected; no anchor signature or seal-body obligation is silently substituted.

## Findings and scope notes

1. **Generated root only.** Lint exits 1 for `KAM.lean is out of date; run scripts/gen_root_imports.py`; module checks, anchor guard and ABI hashes pass. Left the generated root untouched as required.
2. **Actual data remain unpaid.** `lunar_barriers_of_R2` is a conditional assembly theorem. Concrete `gL`, `gU`, Hamiltonian/parameter identities, both full sharp checks, both graph checks, actual emitted-box enclosures and the five band inequalities must still be supplied. The helper boxes do not prove enclosure or static margins for an arbitrary emitted box. No final numerical data were replayed in this audit.
3. **C1 threshold versus the full sharp test.** The two threshold theorems test only C1 (their placeholder disp is zero). Their names and statements accurately say so. Budget theorems test both inequalities. A fresh audit probe also tests the full Bool at err = 1.48e-32 (true) and 1.49e-32 (false), using disp = 1 so the second inequality is harmless.
4. **Study rounding, informational.** SO-GEN3's upper disp = 3.13e-19 at err = 8.17e-35 really passes: minimum 3.129502401352492e-19, relative headroom about 1.59e-4. The generator computes a 1.001-inflated value internally but prints the uninflated minimum (`g3_r2.py:46-49`); that display policy does not invalidate either rounded study budget or the Lean package. Preserve sufficient upward slack when emitting final data.

## Field-by-field fidelity and definitions

`lunarR2` matches `inp:scripts/spin_orbit/g3_r2.py:28-34`, and the full-study table in `inp:docs/tracks/SO/studies/SO-GEN3.md:118-133`. All values are exact rationals; no approximate decimal was substituted.

| Lean field/object | SO-GEN3 R2(65) | Verdict |
|---|---|---|
| `lunarR2TimeScale` | c = 2 | PASS |
| `lunarR2Scalar`, `s` | 1 + 1/10^6 | PASS |
| `lunarR2Kappa` | c/s = 2000000/1000001 | PASS |
| `tau` | 1 | PASS |
| `rho` | 1/140 | PASS |
| `rhoInf` | rho/1000 = 1/140000 | PASS |
| `M` | 54/25 | PASS |
| `σK` (sK) | 1873/1000 | PASS |
| `σB` (sB) | 2689/500 | PASS |
| `σT` (sT) | 13/25 | PASS |
| `μ` (mu) | 1/160 | PASS |
| `γbar` (gbar) | kappa/(65+2) | PASS |
| `σω` (som) | 2 | PASS |
| `nuRay` (nu) | 1/10^6 | PASS |
| `γ` (gamma) | kappa/(65+2) | PASS |
| `err` | supplied residual budget | PASS |
| `E0` | 0 | PASS |
| `disp` | supplied displacement | PASS |

Classification of all 12 public definitions/abbreviations: the three scale constants and two sqrt endpoints are exact fixed rationals; `lunarR2` is the intended record on every rational err/disp input (validity is separately checked); `lunarR2SharpCore` is an exact parameter computation on every record; both coefficient lists are literal algebraic frequency data; `lunarR2Box` is ordinary finite polynomial interval evaluation on every list, including empty rows/lists, with nonnegative radii because the fixed endpoints are positive and ordered; `soPrecisionR2` is the literal natural 160; `SoBackendR2` is a transparent alias of the landed lawful arithmetic type. No choose/default object, junk branch, extra structure, instance or assumed result was introduced. Expose/public module sections cover these definitions.

## Declaration-by-declaration review

All public names below are in `KAM.SpinOrbit`; one private identity helper is included for completeness. SO rows are package/source correspondences rather than invented I/N/P blueprint labels.

| Node/source | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| SO-GEN3 / SO-DION | `lunarR2TimeScale` (LunarParamsR2:33) | PASS | Exact time scale c = 2. |
| SO-GEN3 / SO-DION | `lunarR2Scalar` (LunarParamsR2:35) | PASS | Exact ray scalar 1 + 10^-6. |
| SO-GEN3 / SO-DION | `lunarR2Kappa` (LunarParamsR2:38) | PASS | Exact c/s, nonzero fixed denominator. |
| SO-GEN3 / SO-DION | `lunarR2` (LunarParamsR2:41) | PASS | All 16 CertParams fields match R2(65); err and disp remain explicit data. |
| SO-GEN3 / SO-DION | `lunarR2Kappa_eq` (LunarParamsR2:60) | PASS | Exact rational normalization 2000000/1000001. |
| SO-GEN3 / SO-DION | `lunarR2Kappa_pos` (LunarParamsR2:63) | PASS | Strict positivity, kernel arithmetic. |
| SO-GEN3 / SO-DION | `lunarR2TimeScale_pos` (LunarParamsR2:66) | PASS | Strict positivity, kernel arithmetic. |
| SO-GEN3 / SO-DION | `lunarR2_gamma_le` (LunarParamsR2:70) | PASS | Equality in the SO-DION bound, for arbitrary err/disp. |
| SO-GEN3 / SO-DION | `lunarR2_staticCore_zero` (LunarParamsR2:75) | PASS | True parameter-only core at zero placeholders. |
| SO-GEN3 / SO-DION | `lunarR2_staticCore` (LunarParamsR2:80) | PASS | Same core for every err/disp; core does not inspect either field. |
| SO-GEN3 / SO-DION | `lunarR2_err_nonneg` (LunarParamsR2:83) | PASS | Ordinary source sign premise; discharges the separate err conjunct. |
| SO-GEN3 / SO-DION | `lunarR2SharpCore` (LunarParamsR2:88) | PASS | Definitionally the landed sharpTest at n = 2, on all CertParams. |
| SO-GEN3 / SO-DION | `sharpTest_eq_lunarR2SharpCore` (LunarParamsR2:96) | PASS | rfl, no approximation or substituted constants. |
| SO-GEN3 / SO-DION | `sharpTest_of_lunarR2SharpCore` (LunarParamsR2:101) | PASS | Explicit conditional rewrite helper; does not assert a certificate passes. |
| SO-GEN3 / SO-DION | `lunarR2_sharpCore_budgets` (LunarParamsR2:111) | PASS | Both inequalities pass at (6.9e-35,2.7e-19) and (8.2e-35,3.2e-19). |
| SO-GEN3 / SO-DION | `lunarR2_sharp_C1` (LunarParamsR2:118) | PASS | Strict first inequality passes at 1.48e-32; no full-test claim with disp = 0. |
| SO-GEN3 / SO-DION | `lunarR2_sharp_C1_fails` (LunarParamsR2:126) | PASS | First inequality fails at 1.49e-32. |
| SO-GEN3 / SO-DION | `lunarR2SqrtFiveLo` (LunarParamsR2:135) | PASS | Rational lower endpoint 2236067/10^6. |
| SO-GEN3 / SO-DION | `lunarR2SqrtFiveHi` (LunarParamsR2:137) | PASS | Rational upper endpoint 2236069/10^6. |
| SO-GEN3 / SO-DION | `lunarR2_sqrtFive_mem` (LunarParamsR2:139) | PASS | Proved real sqrt enclosure by squared rational comparisons. |
| SO-GEN3 / SO-DION | `lunarR2MinusCoeffs` (LunarParamsR2:149) | PASS | Exact SO-DION lower vector coefficients, m = 129, D = 8318. |
| SO-GEN3 / SO-DION | `lunarR2PlusCoeffs` (LunarParamsR2:155) | PASS | Exact SO-DION upper vector coefficients with reversed signs. |
| SO-GEN3 / SO-DION | `lunarR2Box` (LunarParamsR2:160) | PASS | Interval midpoint/radius for each polynomial row; arbitrary finite row lists. |
| SO-GEN3 / SO-DION | `lunarR2_checkAlgBox` (LunarParamsR2:167) | PASS | Both concrete two-coordinate boxes pass the landed checker. |
| SO-GEN3 / SO-DION | `lunarR2Box_minus_encloses` (LunarParamsR2:174) | PASS | Real enclosure of the exact lower frequency, via algFreq_encloses. |
| SO-GEN3 / SO-DION | `lunarR2Box_plus_encloses` (LunarParamsR2:180) | PASS | Real enclosure of the exact upper frequency, via algFreq_encloses. |
| SO-GEN3 / SO-DION | `lunarR2_rayMargins` (LunarParamsR2:189) | PASS | Exactly the three checkStatic ray conjuncts for each helper box. |
| SO-GEN3 / SO-DION | `lunarR2Box_normLo` (LunarParamsR2:199) | PASS | Exact L = kappa in both helper boxes. |
| SO sharp assembly | `lunar_barriers_of_sharpGen` (LunarAssemblySharpGen:34) | PASS | Same binders/conclusion as landed assembly; lawful backend generalized. |
| SO sharp assembly | `lunar_barriers_of_sharp_viaGen` (LunarAssemblySharpGen:62) | PASS | Literal landed signature; fresh type equality and application probes pass. |
| SO sharp assembly | `soPrecisionR2` (LunarAssemblySharpGen:85) | PASS | Exact precision 160; agrees with full-study checker precision. |
| SO sharp assembly | `SoBackendR2` (LunarAssemblySharpGen:88) | PASS | Transparent alias CertFixed 160; lawful arithmetic instance supplied. |
| SO sharp assembly | `lunarR2_dio_form` (LunarAssemblySharpGen:90) | PASS | Private cast/division identity only; no new Diophantine assumption. |
| SO sharp assembly | `lunar_barriers_of_R2` (LunarAssemblySharpGen:100) | PASS | Faithful N = 65 specialization; SO-DION discharges both frequency premises. |

The generic proof obtains each barrier from the landed `soRotBarrier_of_certSharp`, transfers the parameter equalities, then uses `soBarriers_of_band_rat`. No torus/barrier existence is assumed in a new field. `LawfulCertArith` is the existing arithmetic soundness interface, not an analytic conclusion. The explicit conditional `sharpTest_of_lunarR2SharpCore` is only a rewrite of the same computation. The R2 instance sets tau = 1 definitionally, uses equality gamma = kappa/67, and calls both landed `lunarRotFreq{Minus,Plus}N_isDiophantine_65` lemmas using proved kappa positivity. Binder order, constants, carriers, strictness and all three separated-barrier conclusions are preserved. Generalization to arbitrary lawful backends is strictly stronger than the existing fixed-backend theorem.

The sqrt endpoints enclose sqrt(5) by real square comparisons. At N = 65 the coefficient denominator is 2(65^2-65-1) = 8318 and numerator m = 129. The enclosure proofs rewrite the exact SO-DION formulas and apply `algFreq_encloses`; both boxes have second coordinate kappa with zero radius. The computed `freqNormLo` is exactly kappa. Their positive norm and two ray inequalities match `checkStatic` at `KAM/Certificate/Defs.lean:220-235`. Parameter core deliberately omits data shapes, weights, pi enclosure, err sign and actual-box conditions, all retained by the full checker.

## Independent checks and output

All Lean/Lake invocations were sequential and run with `LEAN_NUM_THREADS=1` and `nice -n 5`; lint's ABI subprocess inherited both. No heartbeat/depth overrides, cache reset, full-library rebuild, frozen edits, generated-file edits or state-changing git commands were used.

### Targeted gated build — exit 0

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sor2 KAM.SpinOrbit.LunarParamsR2 KAM.SpinOrbit.LunarAssemblySharpGen
```

The gate invokes `nice -n 5 lake build`. Exact build output:

```text
[inp-gate] slot 1 acquired 14:13:18 for KAM.SpinOrbit.LunarParamsR2 KAM.SpinOrbit.LunarAssemblySharpGen
⚠ [2839/2846] Replayed KAM.Certificate.Arith.PiHigh
warning: KAM/Certificate/Arith/PiHigh.lean:218:8: This simp argument is unused:
  Nat.succ_eq_add_one

Hint: Omit it from the simp argument list.
  [apply] simp [div_eq_mul_inv]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [2950/2988] Replayed KAM.Certificate.Expr.Basic
warning: KAM/Certificate/Expr/Basic.lean:85:5: Variable name `hS` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hS

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [3266/3308] Replayed KAM.Strip.CohomologicalRussmannLattice
warning: KAM/Strip/CohomologicalRussmannLattice.lean:45:48: `if_pos` has been deprecated: Use `ite_eq_left` instead

Hint: Replace the deprecated name:
  i̵f̵_̵p̵o̵s̵i̲t̲e̲_̲e̲q̲_̲l̲e̲f̲t̲
⚠ [3267/3308] Replayed KAM.Strip.CohomologicalRussmannBound
warning: KAM/Strip/CohomologicalRussmannBound.lean:72:33: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
⚠ [3272/3308] Replayed KAM.Certificate.Sound.Static
warning: KAM/Certificate/Sound/Static.lean:99:0: automatically included section variable(s) unused in theorem `KAM.Certificate.checkStatic_sound`:
  [LawfulCertArith α]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [LawfulCertArith α] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: KAM/Certificate/Sound/Static.lean:152:0: automatically included section variable(s) unused in theorem `KAM.Certificate.TorusCertificate.emb_structural`:
  [LawfulCertArith α]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [LawfulCertArith α] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
⚠ [3274/3308] Replayed KAM.Certificate.Sound.Ham
warning: KAM/Certificate/Sound/Ham.lean:68:0: automatically included section variable(s) unused in theorem `KAM.Certificate.TorusCertificate.ham_structural`:
  [CertArith α]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [CertArith α] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
⚠ [3345/3352] Replayed KAM.CertificateSharp.Sharp
warning: KAM/CertificateSharp/Sharp.lean:72:23: Variable name `D` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _D

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: KAM/CertificateSharp/Sharp.lean:89:23: Variable name `D` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _D

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [3359/3402] Replayed KAM.ODE.Exit
warning: KAM/ODE/Exit.lean:36:0: automatically included section variable(s) unused in theorem `KAM.ODE.gen_exit`:
  [NormedSpace ℝ E]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NormedSpace ℝ E] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Build completed successfully (3402 jobs).
```

All warnings are replayed unchanged dependencies; none names either new module.

### Fresh type/application/threshold/axiom probe — exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOR2Audit.lean
```

A Python literal-header comparison passed for the full generic signature after just its backend generalization, and for the verbatim `viaGen` signature. The fresh Lean probe included:

```lean
example : type_of% @lunar_barriers_of_sharp := @lunar_barriers_of_sharp_viaGen
example : type_of% @lunar_barriers_of_sharp := @lunar_barriers_of_sharpGen SoBackend _ _
```

It also copied the complete landed theorem declaration under `audit_sharp_copy`, with a body applying the generic theorem to exactly every explicit binder in order. That elaborated. There is no provider/frozen anchor in this delta to test as a seal.

With `p := lunarR2 0 0` and C1 evaluated from the landed `sharpIsoC1Q 2 ... (cRRQ 2 p.tau) ...`, the probe proved by `decide +kernel`:

```text
1.48830e-32 < (p.gamma^4 * p.rho^4) / C1 < 1.48832e-32
lunarR2SharpCore (lunarR2 (148 / 10^34) 1) = true
lunarR2SharpCore (lunarR2 (149 / 10^34) 1) = false
```

Every one of the 21 public theorem exports was printed. Exact output:

```text
'KAM.SpinOrbit.lunarR2Kappa_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR2Kappa_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR2TimeScale_pos' depends on axioms: [propext, Quot.sound]
'KAM.SpinOrbit.lunarR2_gamma_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR2_staticCore_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR2_staticCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR2_err_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.sharpTest_eq_lunarR2SharpCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.sharpTest_of_lunarR2SharpCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR2_sharpCore_budgets' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR2_sharp_C1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR2_sharp_C1_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR2_sqrtFive_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR2_checkAlgBox' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR2Box_minus_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR2Box_plus_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR2_rayMargins' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR2Box_normLo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunar_barriers_of_sharpGen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunar_barriers_of_sharp_viaGen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunar_barriers_of_R2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Exact rational study cross-check

Executed the `inp` versions of `sharp_q.py` and `g3_r2.py` in in-memory Python modules, using `git show` and Fraction arithmetic; no source/data files generated. The command used `g.R2()`, `g.threshold(p)` and `sq.sharpTest(g.R2(err=Fraction(e), disp=Fraction(disp)))` for the four pairs below; exit 0.

```text
threshold 1.488313218515e-32 log10 -31.827305661; displacement 3.830480295413e+15; branch E
6.8e-35 2.61e-19 minimum_disp=2.6047266008808987e-19 pass=True
8.17e-35 3.13e-19 minimum_disp=3.129502401352492e-19 pass=True
6.9e-35 2.7e-19 minimum_disp=2.6430314038350297e-19 pass=True
8.2e-35 3.2e-19 minimum_disp=3.140993842238731e-19 pass=True
```

These decimals are presentations of an untrusted exact-rational mirror; the separate Lean threshold inequalities above provide the independent kernel check.

### Kernel replay — exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.LunarParamsR2 KAM.SpinOrbit.LunarAssemblySharpGen
```

Exact output:

```text
replaying KAM.SpinOrbit.LunarAssemblySharpGen
replaying KAM.SpinOrbit.LunarParamsR2
```

### Names, source integrity and lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-sor2 KAM.SpinOrbit.LunarParamsR2 KAM.SpinOrbit.LunarAssemblySharpGen
```

Exit 0, exact output: `short-name check OK (no reused public short name)`. No git lookup diagnostic in this rerun.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
`git diff --check inp...HEAD`: empty, exit 0.
Both files have required copyright/module/public imports/docstring/public section; sizes 204 and 123 lines, maximum widths 99 and 97. No forbidden proof escapes, ambient types or resource overrides found. Recursive local import scan: 235 KAM modules, zero providers, 24 manifest entries, all SEALED definitions, zero DRAFT_SORRY imports.

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1; exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1464 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (146 frozen declarations)
```

The 1464-file module count is the current independent rerun; the handoff recorded 1462. This count difference does not affect the two reviewed modules or the passing guard/hash results.

## Errata, deviations, remaining uncertainty

No suspected defect in a pinned mathematical source, blueprint contradiction, weakened public conclusion or extra analytic hypothesis found. The older SO design and freeze proposal contain superseded R1/interim literals; this package neither changes those signed statements nor claims a final frozen R2 band. Comparison used the full-study R2 values specifically requested by the handoff. The only implementation variation is the disclosed slightly inflated err/disp budget pairs, plus helper frequency boxes which need not equal final emitted boxes. The source-display rounding note above is tooling/documentation, not a pinned-source erratum. No audit deviation was introduced.

Only this report was written outside `.lake/abi-scratch/`. All audit-created probe/log/import scratch files were removed after copying the receipts here; unrelated scratch was preserved. No commit or repository source modification was made.
