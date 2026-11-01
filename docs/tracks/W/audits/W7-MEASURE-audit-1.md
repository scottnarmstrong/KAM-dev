# W7-MEASURE independent package audit 1

Verdict: **FAIL for full blueprint completion**. The excluded-measure theorem and the density/Diophantine/limit implications pass statement review, but `shellInner` is not the blueprint object and strengthens the shell-estimate premise (F1). Some conclusions of the claimed completed coordinate and counting nodes are not exported (F2). These findings do not refute `exclSet_measure_le`.

Audited branch `inp-wpl`, HEAD `bbe8365ffa04e233a71582a21bc7784e44b59156`, compared using `git diff inp...HEAD` with `inp = 96ef6d94df72007fd2031a93d873c620d03561c5`. Scope: all 26 new files under `KAM/Wave/Measure/` (5454 lines, 189 named public theorems, 52 definitions and 3 structures), the 26 generated imports in `KAM/Root/Wave.lean`, and the handoff. No existing proof file is modified by this package. The requested report is written in the package worktree, overriding the generic brief's main-worktree destination.

Read: AGENTS, PLAN, DECISIONS; the supplied package-audit brief; `blueprint-W/parts/w7-measure.tex`; `docs/tracks/W/W-STATEMENTS.md` (the available track statement document); frozen `Nlw2`, `IsDiophantine`, `Lam`, `SineMode`; and the handoff. The handoff contains **no section labelled AUDIT FOCUS**; its declaration table, interface, and deviations were used as the audit focus. D53 is applied as supplied by the user even though this branch's DECISIONS ends at D51. No agents were delegated.

## Anchor scope

| Anchor / result | Verdict | Scope |
|---|---|---|
| `KAM.Wave.nlw2` | Not submitted for sealing | Manifest remains `DRAFT_SORRY`; W7 supplies implications for clauses (1)–(2), not a provider of the existential headline. Provider/frozen-type and seal-body probes are inapplicable. |
| `KAM.Wave.exclSet_measure_le` | PASS | Arbitrary admissible families, Borel excluded set, constant depending only on mass, literal `32/47` exponent. |
| W7 package completion claim | FAIL | F1 definition/carrier mismatch; F2 unexported portions of claimed completed nodes. |

## F1 — inner shell differs from the blueprint; shell-estimate premise is stronger

Location: `KAM/Wave/Measure/Shells.lean:40-41`, consumed at `ShellEst.lean:34` and `Shells.lean:152`.

Blueprint `bpW:w7:shells`, `w7-measure.tex:608-612`, defines

> `dist_∞(I, R² \ R_k) > a`.

Lean defines

```lean
{I | I ∈ shellSet q t0 k ∧ ∀ J, J ∉ shellSet q t0 k → a < dist I J}
```

Strict inequality against every point does not imply a strict inequality against their infimum. The complement contains the **open** removed square, so the infimum can be unattained.

Concrete counterexample, within the standing shell assumptions: take `q = t0 = 1/2`, `k = 0`, `a = 1/16`, and `I = (5/16, 5/16)`. The shell is `(0,1/2)² \ (0,1/4)²`. Every point in the removed open square has distance strictly greater than `1/16` from `I`; every point outside the outer square has distance at least `3/16`. Hence `I ∈ shellInner`. But points `(1/4-r,1/4-r)` in the removed square, for positive `r → 0`, have distance `1/16+r`, so the distance to the complement is `1/16`. Thus the blueprint excludes `I` from its inner shell.

This persists for arbitrarily small `a`: use `I = (1/4+a,1/4+a)` and `0 < a < 1/8`. It is not resolved by restricting `a ≤ α₀`. Consequently `shellInner ⊆ Pk` requires inclusion of a larger set than the source premise `U_{-a} R_k ⊆ Pk`. The boundary-layer theorem bounds the defect of the larger inner set. Even if the difference has measure zero, that does not give the exact set inclusion required by W8.

Repair needed: define the inner shell using `Metric.infDist` to the complement, or an equivalent **uniform** margin `∃ b > a, ∀ J ∉ R_k, b ≤ dist I J`, and reprove the boundary-layer and shell estimates for that definition. Do not silently enlarge `Pk` or weaken the source convention. The counterexample is to the transcription, not to the blueprint or the proved theorem on Lean's substituted set.

## F2 — the “every blueprint label … done” claim exceeds the public exports

1. `bpW:w7:freqcoords` (blueprint lines 135–148) includes the displayed matrix identity for `A⁻¹`, `A⁻¹ b = (8π/21) λ_J`, the equalities `‖A‖∞ = N_A` and `‖A⁻¹‖∞ = L_A`, and an affine bijection with its displayed inverse. `Coords.lean` exports determinant/scalar identities and the required upper and inverse-Lipschitz bounds; `ZoneBound.lean:32` exports injectivity. The two inverse-coordinate identities at `Coords.lean:259-264` are local `have`s inside a norm-bound proof. There is no public inverse formula, surjectivity/bijection theorem, or sharp operator-norm equality in this package or its `Normal` imports. Scalar definitions named `measNA`/`measLA` and upper bounds are not those equality statements. The existing measure proof validly uses injectivity and `Function.invFun` only on the image; it does not need a global inverse. Preserve that proof's PASS, but export the missing results or explicitly mark those source conclusions unformalized/bypassed under the project's graph policy.
2. `bpW:w7:count` (iii), blueprint line 451, states `∑_{k≠0}|k|⁻³ = Z₃ < 7`; `ext-zeta` additionally states the exact sphere cardinality `4N`. `ZetaSum.lean:40` proves only `encard ≤ 4N`; `ZetaSum.lean:92` proves only the weighted ENNReal **upper bound** `∑ … ≤ ofReal(c * 2π²/3)`. No equality or `measZ3 < 7` theorem is exported. The bound is sufficient for the checked measure consumers, but it is a weaker conclusion than the claimed completed counting node. Add the missing results or record the narrower coverage explicitly.

These are completion/export findings, not evidence of a false inequality in the main measure proof. No replacement theorem was added by the auditor.

## Node and declaration review

Names in this table are in `KAM.Wave` unless stated otherwise. All supporting public theorems are inventoried below and included in the axiom check.

| Blueprint node | Lean declarations / modules | Verdict | Reason / exact boundary |
|---|---|---|---|
| `omega0` | Existing `omegaTan`, `omegaNor`; `Coords.omegaTan_eq`, `omegaNor_eq` | PASS | Uses corrected W0 A/B and normal label `ν+3`. |
| `freqcoords` | `measDA_eq_abs_det`, `measLA_eq`, `measNA_lt`, `measure_omegaTan_image`, `norm_omegaTan_sub_le`, `norm_sub_le_measLA_mul`, `measS_eq`, `abs_measS_sub_le` | FAIL completion | Consumer bounds and determinant scaling pass, even for arbitrary sets in the image-measure theorem; F2 missing inverse/bijection and norm equalities. |
| `indexdef` | `normLab`, `japL`, `absWt`, `IsLam`, `IsLamMinus`, `hatW`, `kAbs`, `kAk`, `lam_cases`, pair/weight identities | PASS | Finite sums; sign cases exhaustive; smaller label selected only in the valid minus case. `hatW 0 = 1`. |
| `unpert-bounds` | `abs_measS_le`, `norm_omegaTan_le`, `three_betaStar_japL_le`, `omegaNor_sub_approx`, `abs_linF_omegaNor_sub_le` | PASS | Literal constants `β_*`, `m/2+1`, decay `j⁻²`, and frequency-coordinate Lipschitz estimate. |
| `constdef` | `Consts`, `alpha_facts`, `theta_mul_LA_le`, `theta_mul_LA_X` | PASS | Mass-only constants, finite exceptional minima with specified empty default; no family/domain dependence. |
| `zones`, `family` | `MeasSetup`, `IsFreqPair`, `AdmissibleFamily`, `Kprev`, `InZ`, `zoneSet`, `prepZone`, `prepSet`, `iterSet`, `exclSet`, `isFreqPair_unpert` | PASS | H1–H2 literally source assumptions. Common ε/θ; Borel domains; `Kν ≥ 2^ν`, `K₋₁=0`; correct cutoff and weights. |
| `slab`, `ext-borel` | `volume_le_of_slices_prod`, `volume_le_of_coord_slices`, `measSlab_measure_le`, `measurableSet_abs_lt_of_continuousOn` | PASS | Tonelli in coordinates, projection length bound, arbitrary Borel domain. Raw slab helper legitimately accepts a measurable small-value set; callers prove measurability. |
| `zone` | `IsFreqPair.zone_diff_bounds`, `zone_measure_le`, `linF_lip`, `drift_le`; `measure_abs_lt_le_of_growth` | PASS | Slope `|k|/4`, factor 8, affine Jacobian `D_A`; no convexity/open-domain premise. |
| `sep`, `largek` | `IsFreqPair.normal_sep`, `zoneSet_zero_empty`, `IsFreqPair.largek`, `prepZone_subset` | PASS | Normal separation pays drift by `4α`; zero modes empty; positive-level use established at consumers. |
| `Xdef`, `dichotomy` | `measXSet`, `measXSet_finite`, `IsFreqPair.zone_dichotomy` | PASS | Bounds both indices in minus pairs; no accidental finite truncation of the unbounded normal index set. |
| `Xzones` | `measPX`, `measCval`, `measSigmaX_pos/le`, `measCX_pos/le`, `IsFreqPair.Xzone_empty`, `Xzone_measure_le`, `X_bound` | PASS | Nonzero affine functions from proved W0 A3; constant/sloped cases separate; small θ compared with the actual finite gradients. Sloped bound is stronger: no `a ≤ α̂` or setup needed. |
| `count` (i) | `lamPlusFin`, `card_lamPlusFin_le`, `mem_lamPlusFin` | PASS WITH NOTES | Candidate superset suffices; cardinal helper assumes integer `N≥2`, while blueprint says `N≥1` for the actual admissible subset. Consumers prove `N≥18`; the small-N source endpoint is not exported explicitly. |
| `count` (ii) | `kAbs_eq_nat`, `tsum_Kprev_le` | PASS | Indicator sum yields multiplicity at most `|k|`; no monotonicity of `Kν` assumed. |
| `count` (iii), `ext-zeta` | `waveL1Sphere`, `encard_l1Sphere_le`, `tsum_lattice_le` | FAIL completion | Adequate upper bounds, missing equality/strict numerical conclusion; F2. |
| `prep` | `plus_bound`, `minus_n_bound`, `minus_assembly`, `prep_minus_n_bound`, `prep_perk_real`, `prepSet_measure_le`, `RealBounds` | PASS | Conditional summation helpers have separate names and their slice/containment premises are proved by callers. Cutoff uses Dirichlet `J₀-3`; threshold sum includes tail threshold. Exponent `8/11`, both signs, exceptional set, and `C_P` agree. Borel conclusion supplied in `Measure`. |
| `iter` | `IsFreqPair.minus_drift`, `iter_minus_n_bound`, `iter_perk_real`, `iterSet_measure_le` | PASS | `j⁻¹/²` drift and `A_k⁻¹/⁶`; multiplicity paid before lattice summation; exceptional term has `K_*²`; literal `C_I` contribution. Borel conclusion supplied in `Measure`. |
| `measurable` | `measurableSet_zoneSet`, `measurableSet_prepZone`, `exclSet_measurableSet`, `continuousOn_zoneFun` | PASS | Finite normal pairings, countable unions, Borel domain differences. Auxiliary constant-divisor Q zones also covered by the generic continuousOn lemma and zone estimate. |
| `measure` | `exclSet_measure_le` | PASS | `α̂^(8/11) = α̌^(2/3) = α^(32/47)`; drift ≤`2α`; `ρζ/D_A = L_A diam Π` used with the valid upper bound on frequency diameter. |
| `melnikov` | `melnikov_prep`, `melnikov_prep_zero`, `melnikov_iter`, `melnikov_sep` | PASS | Negations of strict zones; zero-normal vector weight 1; `melnikov_iter` is a per-zone helper, with source union-complement/cutoff premises implying its premise. |
| `shells` | `shellT`, `boxIoo`, `shellSet`, `shellInner` | FAIL | Shells themselves agree; inner-shell definition fails F1. Generalizing positive `t₀` beyond `≤1/2` is harmless for geometric lemmas. |
| `shell-geom` | `volume_shellSet`, `shellSet_disjoint`, `boxIoo_subset_iUnion_shell`, `shellSet_norm_ge`, `shellSet_dist_le`, `volume_shell_diff_inner_le` | FAIL as full source node | Volume/partition/size results pass; the boundary-layer theorem is on the substituted inner shell (F1). |
| `shell-est` | `shell_defect_le` | FAIL fidelity | Correct inequality on the Lean-defined object, but stronger `hinner` premise (F1). Bundling setup and retaining `Π_k⊆box` otherwise agrees; intermediate two-term bound is in its proof. |
| `density` | `density_one_of_shells`, `volume_box_diff_le`, `exists_shell_index`, `posQuadrant_inter_ball` | PASS | Exact frozen ratio in ENNReal and one-sided filter; measurable positive-quadrant Γ; finite nonzero shell/ball denominators; geometric tail accounts for `q⁻²`. Does not use `shellInner`. |
| `dioph` | `isDiophantine_of_lower_bound` | PASS | Frozen integer ℓ¹ norm, τ=24, and period-one conversion gives `c/(4π)`. |
| `limit` | `tendsto_frequency_limit` | PASS | Exact frozen target λ at modes `i+1` divided by `2π`; shell membership and uniform errors imply shell index tends to infinity. |

## Definition classification (all 55 new definitions/structures)

| Definitions / structures | Classification and whole-carrier assessment |
|---|---|
| `measDA`, `measNA`, `measLA`, `measS`, `measAlin` | Explicit mass-dependent scalars, the signed scalar pairing s, and actual A-linear map. Correct bodies; equality-export limits are F2. `measS`'s docstring calls it a “sup-norm”; that is wrong documentation, since s is signed, but its body and proofs use the correct pairing. |
| `normLab`, `japL`, `absWt`, `IsLam`, `IsLamMinus`, `hatW`, `kAbs`, `kAk` | Exact integer data/finite weights, total on all finitely supported vectors; no divergent-sum default. `sInf` selecting a support index is reached only for a nonzero minus pair; `sInf_minus` identifies the minimum. |
| `measBetaStar`, `measAKappa`, `measW`, `measTheta`, `measCLam`, `measKstar`, `measJstar` | Explicit blueprint constants. Positivity used only with standing `m>0`; no off-domain fallback relied upon. |
| `measXSet`, `measPX`, `measCval`, `measNX`, `measSigmaSet`, `measCSet`, `measSigmaX`, `measCX` | Actual finite exceptional set, affine slopes/constant magnitudes, cardinality, and finite image sets. The default 1 for empty minima is prescribed by the blueprint; finite nonempty sets attain their positive minima. |
| `measTheta0`, `measAlpha0`, `measZ3`, `measCP`, `measCI`, `measC7`, `alphaHat`, `alphaCheck` | Exact formulas, mass-only constants and real powers. Real powers are Mathlib's total operations, and analytical consumers establish positive α; no junk branch. |
| `MeasSetup`, `IsFreqPair`, `AdmissibleFamily` | Bundles of source/typing data, not theorem conclusions. Total maps restricted by hypotheses on D are legitimate representations of maps on D. |
| `AdmissibleFamily.Kprev`, `zoneSet`, `prepZone`, `InZ`, `prepSet`, `iterSet`, `exclSet`, `genZone` | Literal cutoff and set predicates/unions. Arbitrary off-domain map values never enter a zone. |
| `lamPlusFin`, `waveL1Sphere`, `lamMinusPlus`, `minusUnion` | Explicit finite candidate superset, exact lattice sphere, signed pair including the valid zero value when n=0, and exact indexed union. The candidate set is intentionally larger than the admissible subset, not a redefinition of Λ⁺. |
| `shellT`, `boxIoo`, `shellSet` | Literal powers, open boxes, and their differences, defined without exceptional values. |
| `shellInner` | **FAIL**, F1. Quantifier/inﬁmum mismatch changes the object on its intended positive-radius carrier. |

## Validation evidence

All Lean-related work below was serialized. D53 replaced the generic brief's priority setting. The lint wrapper and all children inherited one scope with `MemoryMax=4G`, `MemorySwapMax=0`, `nice -n 10`, `LEAN_NUM_THREADS=1`; each targeted build is scoped by the specified W driver. No budget override was used.

1. Independent lint (exit **0**):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpl
```

Exact output:

```text
check_lean_modules: PASS (3687 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

The opt-in application exception is the lint script's stated file-hash-only scope, not an application rebuild. The regenerated Wave root matches the generator check; its diff consists exactly of 26 Measure imports. The auditor did not edit it.

2. Targeted builds (driver exit **0**):

```sh
/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpl KAM.Wave.Measure.ShellEst KAM.Wave.Measure.Dioph KAM.Wave.Measure.Limit
```

Exact output:

```text
[w_build] slot 3: KAM.Wave.Measure.ShellEst (01:40:10)
Build completed successfully (3199 jobs).
[w_build] slot 3: KAM.Wave.Measure.Dioph (01:40:15)
Build completed successfully (2844 jobs).
[w_build] slot 3: KAM.Wave.Measure.Limit (01:40:19)
Build completed successfully (2845 jobs).
```

These three leaves cover all 26 package modules through imports; the driver holds a compile slot and wraps **each** `lake build` in:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake build <Module>
```

No warning, elaboration failure, OOM, or design signal occurred.

3. Every new public theorem: scratch probe imported all 26 modules and issued `#print axioms KAM.Wave.<name>` for every one of the 189 theorem declarations found in the reviewed sources. This is independent of the handoff's 13-result sample. Exit **0**, exactly 189 output rows, each of the exact form:

```text
'KAM.Wave.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The complete name set is preserved in the inventory below. For the main results the literal output was:

```text
'KAM.Wave.exclSet_measure_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.exclSet_measurableSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.prepSet_measure_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.iterSet_measure_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.density_one_of_shells' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.shell_defect_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.isDiophantine_of_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tendsto_frequency_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exact command (stdout/stderr captured to the same-basename scratch `.log`):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env sh -c 'LEAN_PATH="$PWD/.lake/build/lib/lean:/root/code/KAM-inp/.lake/build/lib/lean:$LEAN_PATH" exec lean .lake/abi-scratch/W7MeasureAudit1.lean'
```

4. F1 counterexample: same capped command, replacing `W7MeasureAudit1.lean` by `W7ShellCounterexample.lean`. Exit **0**, no output. The probe proved **both**

```lean
example : (fun _ : Fin 2 => (5 / 16 : ℝ)) ∈
    shellInner (1/2) (1/2) 0 (1/16) := by ...
example : Metric.infDist (fun _ : Fin 2 => (5/16 : ℝ))
    (shellSet (1/2) (1/2) 0)ᶜ ≤ 1/16 := by ...
```

The ellipses here abbreviate successful ordinary proof terms, not admits in the probe. Membership was proved by showing `dist I J ≤ 1/16` forces `J` back into the shell. The infimum bound used complement points `J_i = 1/4 - min(δ/2,1/8)` and `Metric.infDist_le_dist_of_mem`, for every δ>0. Thus this is an elaborated counterexample, not merely a numerical sketch. Probes/logs were removed after recording results.

5. Kernel replay and name checks: the user explicitly says the launcher already ran these and authorizes not rerunning replay. No `leanchecker` was invoked by this auditor; the launcher's exact command/output/exit code is unavailable in this pane. They are **launcher-reported checks**, not independently witnessed exit-0 claims in this report. The independent builds, 189 axiom queries, and counterexample above were actually run here.

6. Static hygiene and protected surface: `git diff --check inp...HEAD` exited **0**, no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exited **0**, no output. All 26 files have the required module headers/public interfaces/sections; largest file is `UnpertBounds.lean`, 413 lines. Lint found no forbidden proof escape, budget override, oversized file, or prohibited root/provider import. A transitive local-import walk reaches only frozen `KAM.IsDiophantine`, `KAM.Wave.lam`, and `KAM.Wave.sineMode`, all manifest **SEALED** definitions, and no provider. The DRAFT `Nlw2` was read as text only, not imported in either probe.


## Source defects, deviations, and remaining scope

No new defect in a pinned published source is established by this audit. This is a Lean-versus-local-blueprint package audit; published PDF page images were not independently re-read. The blueprint's existing source observations remain attributed to `bpW:w7:errata` (near the end of `w7-measure.tex`): the P96-K Lemma 5 slicing constant, reuse of κ in §6, and Lemma 10's asserted order-α Lipschitz closeness. They are not newly verified findings here. The package correctly uses the blueprint's repaired coordinate slicing and explicit θ smallness.

F1 is an introduced, unreported definition deviation. F2 concerns missing source conclusions, not a suspected false blueprint statement. Additional documentation issues: `Coords.lean:43` calls signed `measS` a “sup-norm”; `Coords.lean:126` calls the subtraction identity an injectivity theorem. The actual injectivity proof is `ZoneBound.lean:32`. Neither documentation error changes a theorem type.

The handoff's recorded strengthenings (sloped exceptional-zone bound without `a≤α̂`, weakened nonnegativity condition in `largek`, and setup bundling) are acceptable within their actual consumer uses. Its “every blueprint label … done” assertion needs the qualifications in F1/F2. W6 must still supply actual admissible families/exclusion/final-frequency estimates, and W8 must choose shells/master α and prove the limiting error estimates and assembly. W7 alone does not close either existential clause of `nlw2`.

The auditor changes only this report; scratch probes are removed after use. No source repair, generated-root regeneration, commit, or other state-changing git operation was performed.

## Complete public declaration inventory

All names have prefix `KAM.Wave.`. Line numbers refer to audited HEAD. The 189 `theorem` rows below all produced exactly the standard axiom set recorded above. Verdicts concern fidelity to the associated source node; F2 missing statements have no declaration to list. Additional helpers are valid conditional algebra/measure lemmas with their premises discharged in the reviewed consumers. Definitions are classified above.

| File (under `KAM/Wave/Measure/`) | Declaration and line | Kind | Verdict / note |
|---|---|---|---|
| `Consts.lean` | `measW`:32 | def | PASS |
| `Consts.lean` | `measTheta`:35 | def | PASS |
| `Consts.lean` | `measCLam`:38 | def | PASS |
| `Consts.lean` | `measKstar`:41 | def | PASS |
| `Consts.lean` | `measJstar`:44 | def | PASS |
| `Consts.lean` | `measXSet`:47 | def | PASS |
| `Consts.lean` | `measPX`:53 | def | PASS |
| `Consts.lean` | `measCval`:57 | def | PASS |
| `Consts.lean` | `measW_pos`:60 | theorem | PASS |
| `Consts.lean` | `measTheta_pos`:63 | theorem | PASS |
| `Consts.lean` | `measTheta_le`:67 | theorem | PASS |
| `Consts.lean` | `measCLam_pos`:75 | theorem | PASS |
| `Consts.lean` | `measKstar_pos`:81 | theorem | PASS |
| `Consts.lean` | `measJstar_pos`:84 | theorem | PASS |
| `Consts.lean` | `measXSet_finite`:88 | theorem | PASS |
| `Consts.lean` | `measNX`:185 | def | PASS |
| `Consts.lean` | `measSigmaSet`:188 | def | PASS |
| `Consts.lean` | `measCSet`:193 | def | PASS |
| `Consts.lean` | `measSigmaX`:198 | def | PASS |
| `Consts.lean` | `measCX`:203 | def | PASS |
| `Consts.lean` | `measSigmaSet_finite`:207 | theorem | PASS |
| `Consts.lean` | `measCSet_finite`:210 | theorem | PASS |
| `Consts.lean` | `affineForm_eq`:214 | theorem | PASS |
| `Consts.lean` | `measCval_eq`:233 | theorem | PASS |
| `Consts.lean` | `measSigmaX_pos`:246 | theorem | PASS |
| `Consts.lean` | `measSigmaX_le`:256 | theorem | PASS |
| `Consts.lean` | `measCval_pos`:265 | theorem | PASS |
| `Consts.lean` | `measCX_pos`:276 | theorem | PASS |
| `Consts.lean` | `measCX_le`:286 | theorem | PASS |
| `Consts.lean` | `measTheta0`:296 | def | PASS |
| `Consts.lean` | `measAlpha0`:301 | def | PASS |
| `Consts.lean` | `measZ3`:306 | def | PASS |
| `Consts.lean` | `measCP`:309 | def | PASS |
| `Consts.lean` | `measCI`:314 | def | PASS |
| `Consts.lean` | `measC7`:320 | def | PASS |
| `Consts.lean` | `alphaHat`:325 | def | PASS |
| `Consts.lean` | `alphaCheck`:328 | def | PASS |
| `Coords.lean` | `measDA`:32 | def | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `measNA`:36 | def | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `measLA`:40 | def | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `measS`:44 | def | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `measLam_facts`:51 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `measDA_pos`:60 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `measDA_eq_abs_det`:66 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `measNA_pos`:73 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `measLA_pos`:79 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `measLA_eq`:86 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `measNA_lt`:94 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `measAlin`:112 | def | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `measAlin_apply`:114 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `omegaTan_eq`:118 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `det_measAlin`:123 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `omegaTan_sub`:127 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `omegaTan_sub_apply`:131 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `measure_omegaTan_image`:138 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `measS_eq`:154 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `omegaNor_eq`:165 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `abs_measS_sub_le`:177 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `norm_omegaTan_sub_le`:200 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `norm_sub_le_measLA_mul`:240 | theorem | PASS as stated; F2 additional exports absent |
| `Coords.lean` | `measNA_dist_le`:314 | theorem | PASS as stated; F2 additional exports absent |
| `Count.lean` | `lamPlusFin`:30 | def | PASS |
| `Count.lean` | `card_lamPlusFin_le`:36 | theorem | PASS WITH NOTES, small-N coverage |
| `Count.lean` | `mem_lamPlusFin`:53 | theorem | PASS WITH NOTES, small-N coverage |
| `Count.lean` | `kAbs_eq_nat`:82 | theorem | PASS |
| `Count.lean` | `tsum_Kprev_le`:90 | theorem | PASS |
| `Count.lean` | `sum_rpow_neg_quarter_le`:124 | theorem | PASS |
| `Density.lean` | `posQuadrant_inter_ball`:29 | theorem | PASS |
| `Density.lean` | `exists_shell_index`:45 | theorem | PASS |
| `Density.lean` | `volume_box_diff_le`:67 | theorem | PASS |
| `Density.lean` | `density_one_of_shells`:99 | theorem | PASS |
| `Dioph.lean` | `isDiophantine_of_lower_bound`:28 | theorem | PASS |
| `Family.lean` | `MeasSetup`:35 | structure | PASS |
| `Family.lean` | `IsFreqPair`:43 | structure | PASS |
| `Family.lean` | `AdmissibleFamily`:65 | structure | PASS |
| `Family.lean` | `AdmissibleFamily.Kprev`:78 | def | PASS |
| `Family.lean` | `zoneSet`:85 | def | PASS |
| `Family.lean` | `prepZone`:90 | def | PASS |
| `Family.lean` | `InZ`:94 | def | PASS |
| `Family.lean` | `prepSet`:97 | def | PASS |
| `Family.lean` | `iterSet`:101 | def | PASS |
| `Family.lean` | `exclSet`:106 | def | PASS |
| `Family.lean` | `isFreqPair_unpert`:110 | theorem | PASS |
| `Iter.lean` | `zoneSet_neg`:27 | theorem | PASS |
| `Iter.lean` | `iter_perk_real`:41 | theorem | PASS |
| `Iter.lean` | `iterSet_measure_le`:128 | theorem | PASS |
| `IterMinus.lean` | `japL_lamMinusPlus`:33 | theorem | PASS |
| `IterMinus.lean` | `isLam_lamMinusPlus`:38 | theorem | PASS |
| `IterMinus.lean` | `IsFreqPair.minus_drift`:42 | theorem | PASS |
| `IterMinus.lean` | `iter_minus_n_bound`:80 | theorem | PASS |
| `Lambda.lean` | `normLab`:30 | def | PASS |
| `Lambda.lean` | `normLab_ge`:32 | theorem | PASS |
| `Lambda.lean` | `normLab_pos`:35 | theorem | PASS |
| `Lambda.lean` | `japL`:38 | def | PASS |
| `Lambda.lean` | `absWt`:41 | def | PASS |
| `Lambda.lean` | `IsLam`:44 | def | PASS |
| `Lambda.lean` | `IsLamMinus`:47 | def | PASS |
| `Lambda.lean` | `hatW`:52 | def | PASS |
| `Lambda.lean` | `kAbs`:57 | def | PASS |
| `Lambda.lean` | `kAk`:60 | def | PASS |
| `Lambda.lean` | `kAbs_nonneg`:62 | theorem | PASS |
| `Lambda.lean` | `kAbs_neg`:64 | theorem | PASS |
| `Lambda.lean` | `one_le_kAbs`:66 | theorem | PASS |
| `Lambda.lean` | `kAk_pos`:76 | theorem | PASS |
| `Lambda.lean` | `kAk_neg`:80 | theorem | PASS |
| `Lambda.lean` | `kAbs_pow_le_kAk`:82 | theorem | PASS |
| `Lambda.lean` | `kAk_le`:84 | theorem | PASS |
| `Lambda.lean` | `sum_single_pair`:91 | theorem | PASS |
| `Lambda.lean` | `linF_pair`:104 | theorem | PASS |
| `Lambda.lean` | `absWt_single`:109 | theorem | PASS |
| `Lambda.lean` | `absWt_pair`:114 | theorem | PASS |
| `Lambda.lean` | `lam_cases`:122 | theorem | PASS |
| `Lambda.lean` | `IsLam_of_minus`:151 | theorem | PASS |
| `Lambda.lean` | `linF_minus`:172 | theorem | PASS |
| `Lambda.lean` | `japL_minus`:176 | theorem | PASS |
| `Lambda.lean` | `japL_single`:192 | theorem | PASS |
| `Lambda.lean` | `japL_pair`:203 | theorem | PASS |
| `Lambda.lean` | `japL_ge_one`:215 | theorem | PASS |
| `Lambda.lean` | `japL_neg`:217 | theorem | PASS |
| `Lambda.lean` | `isLamMinus_neg`:223 | theorem | PASS |
| `Lambda.lean` | `isLamMinus_neg_iff`:229 | theorem | PASS |
| `Lambda.lean` | `sInf_minus`:232 | theorem | PASS |
| `Lambda.lean` | `hatW_minus`:246 | theorem | PASS |
| `Lambda.lean` | `hatW_neg`:253 | theorem | PASS |
| `Lambda.lean` | `hatW_le_japL`:264 | theorem | PASS |
| `Lambda.lean` | `hatW_pos`:274 | theorem | PASS |
| `Lambda.lean` | `normLab_rpow_le_one`:282 | theorem | PASS |
| `Lambda.lean` | `absWt_nonneg`:285 | theorem | PASS |
| `Lambda.lean` | `absWt_le_two`:288 | theorem | PASS |
| `Lambda.lean` | `absWt_mono`:311 | theorem | PASS |
| `Lambda.lean` | `absWt_minus`:317 | theorem | PASS |
| `Limit.lean` | `tendsto_frequency_limit`:29 | theorem | PASS |
| `Measure.lean` | `measurableSet_zoneSet`:33 | theorem | PASS |
| `Measure.lean` | `measurableSet_prepZone`:39 | theorem | PASS |
| `Measure.lean` | `exclSet_measurableSet`:48 | theorem | PASS |
| `Measure.lean` | `exclSet_measure_le`:64 | theorem | PASS |
| `Measure.lean` | `melnikov_prep`:161 | theorem | PASS |
| `Measure.lean` | `melnikov_prep_zero`:172 | theorem | PASS |
| `Measure.lean` | `melnikov_iter`:189 | theorem | PASS |
| `Measure.lean` | `melnikov_sep`:199 | theorem | PASS |
| `MinusSum.lean` | `lamMinusPlus`:29 | def | PASS |
| `MinusSum.lean` | `l1Norm_neg`:31 | theorem | PASS |
| `MinusSum.lean` | `isLam_neg`:35 | theorem | PASS |
| `MinusSum.lean` | `measXSet_neg`:38 | theorem | PASS |
| `MinusSum.lean` | `measXSet_neg_iff`:51 | theorem | PASS |
| `MinusSum.lean` | `isLamMinus_cases`:56 | theorem | PASS |
| `MinusSum.lean` | `minusUnion`:70 | def | PASS |
| `MinusSum.lean` | `minus_assembly`:74 | theorem | PASS |
| `MinusZones.lean` | `genZone`:29 | def | PASS |
| `MinusZones.lean` | `zoneSet_eq_genZone`:33 | theorem | PASS |
| `MinusZones.lean` | `genZone_mono`:37 | theorem | PASS |
| `MinusZones.lean` | `IsFreqPair.zone_bound_gen`:48 | theorem | PASS |
| `MinusZones.lean` | `IsFreqPair.zone_bound_const`:60 | theorem | PASS |
| `MinusZones.lean` | `IsFreqPair.X_bound`:71 | theorem | PASS |
| `MinusZones.lean` | `IsFreqPair.minus_n_bound`:103 | theorem | PASS |
| `Pair.lean` | `measAlphaM_pos`:32 | theorem | PASS |
| `Pair.lean` | `alpha_facts`:41 | theorem | PASS |
| `Pair.lean` | `theta_mul_LA_le`:75 | theorem | PASS |
| `Pair.lean` | `linF_sub`:95 | theorem | PASS |
| `Pair.lean` | `linF_sub'`:101 | theorem | PASS |
| `Pair.lean` | `abs_linF_le_absWt`:106 | theorem | PASS |
| `Pair.lean` | `normLab_inv_eq`:114 | theorem | PASS |
| `Pair.lean` | `IsFreqPair.drift_le`:118 | theorem | PASS |
| `Pair.lean` | `IsFreqPair.drift_le_two`:133 | theorem | PASS |
| `Pair.lean` | `IsFreqPair.norm_omega_le`:144 | theorem | PASS |
| `Pair.lean` | `abs_sum_k_mul_le`:156 | theorem | PASS |
| `Pair.lean` | `IsFreqPair.linF_lip`:167 | theorem | PASS |
| `Prep.lean` | `prep_perk_real`:31 | theorem | PASS |
| `Prep.lean` | `prepSet_measure_le`:88 | theorem | PASS |
| `PrepMinus.lean` | `linF_neg`:27 | theorem | PASS |
| `PrepMinus.lean` | `rpow_neg_two_eq`:32 | theorem | PASS |
| `PrepMinus.lean` | `prepZone_neg`:40 | theorem | PASS |
| `PrepMinus.lean` | `prepZone_minus`:52 | theorem | PASS |
| `PrepMinus.lean` | `prep_minus_n_bound`:64 | theorem | PASS |
| `RealBounds.lean` | `pow_le_kAk_rpow`:27 | theorem | PASS |
| `RealBounds.lean` | `rpow_two_three_quarter_le`:39 | theorem | PASS |
| `RealBounds.lean` | `three_le_rpow_neg`:49 | theorem | PASS |
| `RealBounds.lean` | `prep_real_bound`:62 | theorem | PASS |
| `RealBounds.lean` | `iter_real_bound`:132 | theorem | PASS |
| `SepLarge.lean` | `IsFreqPair.normal_sep`:31 | theorem | PASS |
| `SepLarge.lean` | `zoneSet_zero_empty`:46 | theorem | PASS |
| `SepLarge.lean` | `IsFreqPair.largek`:60 | theorem | PASS |
| `SepLarge.lean` | `prepZone_subset`:91 | theorem | PASS |
| `SepLarge.lean` | `IsFreqPair.zone_dichotomy`:99 | theorem | PASS |
| `ShellEst.lean` | `shell_defect_le`:30 | theorem | FAIL source fidelity, F1; proved for Lean object |
| `Shells.lean` | `shellT`:30 | def | PASS |
| `Shells.lean` | `boxIoo`:33 | def | PASS |
| `Shells.lean` | `shellSet`:36 | def | PASS |
| `Shells.lean` | `shellInner`:40 | def | FAIL F1 |
| `Shells.lean` | `measurableSet_boxIoo`:43 | theorem | PASS |
| `Shells.lean` | `volume_boxIoo`:46 | theorem | PASS |
| `Shells.lean` | `volume_boxIoo_of_nonneg`:51 | theorem | PASS |
| `Shells.lean` | `boxIoo_subset`:55 | theorem | PASS |
| `Shells.lean` | `shellT_pos`:59 | theorem | PASS |
| `Shells.lean` | `shellT_succ`:62 | theorem | PASS |
| `Shells.lean` | `shellT_antitone`:65 | theorem | PASS |
| `Shells.lean` | `shellT_tendsto`:71 | theorem | PASS |
| `Shells.lean` | `measurableSet_shellSet`:77 | theorem | PASS |
| `Shells.lean` | `volume_shellSet`:81 | theorem | PASS |
| `Shells.lean` | `shellSet_disjoint`:96 | theorem | PASS |
| `Shells.lean` | `boxIoo_subset_iUnion_shell`:105 | theorem | PASS |
| `Shells.lean` | `shellSet_norm_ge`:130 | theorem | PASS |
| `Shells.lean` | `shellSet_dist_le`:142 | theorem | PASS |
| `Shells.lean` | `volume_shell_diff_inner_le`:152 | theorem | FAIL source fidelity, F1; proved for Lean object |
| `Slab.lean` | `volume_le_of_slices_prod`:32 | theorem | PASS |
| `Slab.lean` | `volume_le_of_coord_slices`:86 | theorem | PASS |
| `Slab.lean` | `measSlab_measure_le`:146 | theorem | PASS |
| `Slab.lean` | `measurableSet_abs_lt_of_continuousOn`:164 | theorem | PASS |
| `UnpertBounds.lean` | `measBetaStar`:29 | def | PASS |
| `UnpertBounds.lean` | `measAKappa`:32 | def | PASS |
| `UnpertBounds.lean` | `measBetaStar_pos`:34 | theorem | PASS |
| `UnpertBounds.lean` | `measBetaStar_le`:39 | theorem | PASS |
| `UnpertBounds.lean` | `measAKappa_pos`:48 | theorem | PASS |
| `UnpertBounds.lean` | `abs_measS_le`:56 | theorem | PASS |
| `UnpertBounds.lean` | `norm_omegaTan_le`:77 | theorem | PASS |
| `UnpertBounds.lean` | `lamN_le_mul`:107 | theorem | PASS |
| `UnpertBounds.lean` | `lt_lamN`:119 | theorem | PASS |
| `UnpertBounds.lean` | `lamN_sq'`:126 | theorem | PASS |
| `UnpertBounds.lean` | `lamN_sub_eq`:129 | theorem | PASS |
| `UnpertBounds.lean` | `lamN_sub_le`:141 | theorem | PASS |
| `UnpertBounds.lean` | `lamN_sub_ge`:153 | theorem | PASS |
| `UnpertBounds.lean` | `omegaNor_ge`:179 | theorem | PASS |
| `UnpertBounds.lean` | `omegaNor_sub_ge`:195 | theorem | PASS |
| `UnpertBounds.lean` | `omegaNor_sub_approx`:242 | theorem | PASS |
| `UnpertBounds.lean` | `abs_linF_omegaNor_sub_le`:333 | theorem | PASS |
| `UnpertBounds.lean` | `three_betaStar_japL_le`:371 | theorem | PASS |
| `Xzones.lean` | `theta_mul_LA_X`:33 | theorem | PASS |
| `Xzones.lean` | `IsFreqPair.drift_lip`:51 | theorem | PASS |
| `Xzones.lean` | `IsFreqPair.continuousOn_zoneFun`:69 | theorem | PASS |
| `Xzones.lean` | `IsFreqPair.Xzone_empty`:100 | theorem | PASS |
| `Xzones.lean` | `IsFreqPair.Xzone_measure_le`:175 | theorem | PASS |
| `ZetaSum.lean` | `waveL1Sphere`:28 | def | PASS |
| `ZetaSum.lean` | `kAbs_eq_of_mem_l1Sphere`:30 | theorem | PASS |
| `ZetaSum.lean` | `encard_l1Sphere_le`:40 | theorem | PASS as upper bound; F2 source equality absent |
| `ZetaSum.lean` | `tsum_lattice_le`:92 | theorem | PASS as upper bound; F2 source equality absent |
| `ZoneBound.lean` | `omegaTan_injective`:32 | theorem | PASS |
| `ZoneBound.lean` | `continuous_omegaTan`:38 | theorem | PASS |
| `ZoneBound.lean` | `IsFreqPair.zone_diff_bounds`:43 | theorem | PASS |
| `ZoneBound.lean` | `measure_abs_lt_le_of_growth`:120 | theorem | PASS |
| `ZoneBound.lean` | `IsFreqPair.zone_measure_le`:165 | theorem | PASS |
| `ZoneSums.lean` | `japL_zero`:34 | theorem | PASS |
| `ZoneSums.lean` | `IsFreqPair.zone_bound_lam`:40 | theorem | PASS |
| `ZoneSums.lean` | `IsFreqPair.zone_bound_zero`:54 | theorem | PASS |
| `ZoneSums.lean` | `IsFreqPair.plus_bound`:72 | theorem | PASS |
