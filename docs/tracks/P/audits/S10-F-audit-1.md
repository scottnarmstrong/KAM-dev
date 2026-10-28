# Independent package audit S10-F, audit 1

Overall verdict: **PASS WITH NOTES**. The S10-F slice is complete and its exported contracts pass; no blocking finding. Notes concern namespace shadowing, one unused simp argument, and the expressly permitted stale generated root.

Audit target: HEAD `6b90a48b0edbee411825b4d0c630cd6133b05d70`, compared with `inp` at `ff90b30b9af90253cabe2e841aee0747709fbe1b` using `git diff inp...HEAD`. Git reports multiple merge bases and selects `fd08c5316be0424de54de3634c0482f2b17e2549`. The diff contains twelve new Lean files: six S10-H files plus the six S10-F files. Per AUDIT FOCUS, only `KAM/Planetary/Nondegeneracy/SymmetricRelation.lean` and `SymmetricRelation/*.lean` are audited here; S10-H is inspected as an upstream interface, not independently re-audited.

Read AGENTS.md, PLAN.md, DECISIONS.md, the common audit brief, S10-F handoff, P810 design and both design audits, the pinned original `/root/code/KAM-inp/.drafts/design/P810Signatures.lean`, Part 10 blueprint, track P statement, relevant frozen statement and definitions. The prompt overrides the common brief's report destination: this report is written in `/root/code/KAM-inp-s10f`.

No frozen anchor or provider belongs to S10-F. Provider/frozen-type equality and trial seal bodies are therefore not applicable. The actual contracts are `relation`, `fc_def`, `fc_analytic`, and `f_nonzero`; their declaration headers are byte-identical to the pinned signature file, and the two definition bodies are literal copies. This package does not seal P-G, P-PLANAR, P-FIXED, torsion, or any campaign headline.

## Statement and proof review

The S10-F slice is complete: `bpP:p10:Fc-def`, `bpP:p10:Fc-analytic`, `stepP:p10:Fc-poly`, `bpP:p10:F-nonzero`, and its F-A/F-B/F-C proof cuts. The analytic blueprint's identity relation factor is present directly in the product definition; there is no need for a simple-spectrum premise to prove analyticity of the product. No extra premise, changed physical carrier, widened constant dependence, assumed analytic root selection, or conclusion-shaped field was found.

The analytic argument uses `MvPolynomial.esymmAlgEquiv` over `Polynomial ℝ`, retaining the fast-sum parameter in the coefficient ring. The elementary symmetric values are signed characteristic coefficients of the literal secular matrix; finite polynomial evaluation proves analyticity even at repeated eigenvalues.

The induction retains every physical datum and every real relation coefficient. S10-P's `peel` and `weyl` yield the sorted limit (outer spectrum, 0), including the one-planet zero matrix. F-A uses divergence of the first fast frequency. F-B separates a nonzero remaining fast coefficient, a single slow coefficient, and two nonzero slow coefficients with an arbitrarily small spectral ratio from `n2`. F-C1 consumes S10-Z's `generic` to choose one outer axis tuple for all peeled relations. F-C2 does not apply induction to a zero relation: it derives a single nonzero slow coefficient and uses strict negativity. S10-H's block-spectrum and axes interfaces support the limit argument. Each conditional helper's hypotheses are explicitly discharged by the parent proof.

The proof establishes factorwise nonvanishing instead of the blueprint's full bijection and product-limit identity. That route proves the entire exported nonvanishing conclusion; the unused full product-limit identity is not separately claimed as a Lean export.

All declarations below have namespace prefix `KAM.Planetary.Nondegeneracy`. File locators are relative to `KAM/Planetary/Nondegeneracy/`.

| Declaration / node implementation | Locator | Verdict | Reason |
|---|---|---|---|
| `fc_analytic` | `SymmetricRelation.lean:38` | PASS | Fc-analytic: analytic on all axes, with no simple-spectrum premise. |
| `f_nonzero_two` | `SymmetricRelation.lean:42` | PASS | F-B base: all fast and slow coefficient subcases handled, including one-planet limit. |
| `f_nonzero_aux` | `SymmetricRelation.lean:84` | PASS | F-C induction quantifies over all data; generic common outer point for all nonzero peeled relations; zero peeled relation uses negativity. |
| `f_nonzero` | `SymmetricRelation.lean:128` | PASS | F-nonzero: every real nonzero relation, all positive physical data, n ≥ 2. |
| `relationPoly` | `SymmetricRelation/Analytic.lean:31` | PASS | Fc-poly: universal symmetric product over ℝ[X]. |
| `eval₂_relationPoly` | `SymmetricRelation/Analytic.lean:35` | PASS | Polynomial evaluation gives the literal relation product. |
| `relationPoly_isSymmetric` | `SymmetricRelation/Analytic.lean:40` | PASS | Renaming permutes factors by left multiplication. |
| `esymm_sorted` | `SymmetricRelation/Analytic.lean:47` | PASS | Correct coefficient index n−1−i and sign (−1)^(i+1). |
| `exists_relation_poly` | `SymmetricRelation/Analytic.lean:71` | PASS | Fundamental theorem of symmetric polynomials over ℝ[X], no assumed supplier. |
| `analyticAt_nu_action` | `SymmetricRelation/Analytic.lean:98` | PASS | Positive axes ensure nonzero square root/action denominator. |
| `fc_analytic_aux` | `SymmetricRelation/Analytic.lean:111` | PASS | Polynomial evaluation of analytic fast sum and characteristic coefficients. |
| `tendsto_nu_zero` | `SymmetricRelation/Cases.lean:29` | PASS | Positive inverse cubic action diverges as t tends to zero from above. |
| `eventually_ne_of_cons` | `SymmetricRelation/Cases.lean:51` | PASS | Finite intersection of eventual nonvanishing and axes membership. |
| `case_A` | `SymmetricRelation/Cases.lean:60` | PASS | F-A: normalized form tends to nonzero first fast coefficient. |
| `case_lim` | `SymmetricRelation/Cases.lean:78` | PASS | Distinct conditional limit helper; final induction discharges every limit premise. |
| `peelPerm` | `SymmetricRelation/Cases.lean:87` | PASS | Bijective deletion of preimage of last slot, no fallback. |
| `castSucc_peelPerm` | `SymmetricRelation/Cases.lean:97` | PASS | Exact embedding identity for the deleted permutation. |
| `peelRel` | `SymmetricRelation/Cases.lean:102` | PASS | Delete first fast coefficient and designated slow coefficient. |
| `relLim_eq` | `SymmetricRelation/Cases.lean:105` | PASS | F-C: identifies each limit factor with the smaller-system relation. |
| `relation` | `SymmetricRelation/Defs.lean:28` | PASS | Fc-def: literal fast sum plus permuted slow sum; exact signed draft body. |
| `fc_def` | `SymmetricRelation/Defs.lean:30` | PASS | Fc-def: product over every permutation, including the identity factor. |
| `snocZero` | `SymmetricRelation/Limits.lean:31` | PASS | Literal append-zero spectrum on Fin (n+1). |
| `coeffs_one` | `SymmetricRelation/Limits.lean:34` | PASS | Literal single-planet matrix is zero; name-shadowing note N1. |
| `sigma_one` | `SymmetricRelation/Limits.lean:41` | PASS | Single eigenvalue zero, derived from the characteristic polynomial. |
| `sigma_outer_nonpos` | `SymmetricRelation/Limits.lean:52` | PASS | Separate one-planet zero case; otherwise strict negativity. |
| `sigma_cons_close` | `SymmetricRelation/Limits.lean:60` | PASS | peel plus Weyl and sorted block spectrum; O(t^(3/2)). |
| `tendsto_sigma_cons` | `SymmetricRelation/Limits.lean:85` | PASS | Squeeze with positive-axis half bounds and positive exponent. |
| `eventually_cons_mem` | `SymmetricRelation/Limits.lean:107` | PASS | Positive increasing axes retained for sufficiently small t > 0. |
| `relLim` | `SymmetricRelation/Limits.lean:117` | PASS | Literal outer fast sum plus permuted append-zero spectrum. |
| `relation_cons` | `SymmetricRelation/Limits.lean:122` | PASS | Exact split of first fast term; outer masses/actions preserved. |
| `tendsto_relation` | `SymmetricRelation/Limits.lean:131` | PASS | Limit after subtracting the diverging first fast term. |
| `relation_of_fast_zero` | `SymmetricRelation/Small.lean:30` | PASS | Literal fast-zero specialization. |
| `fc_ne_zero_single` | `SymmetricRelation/Small.lean:36` | PASS | F-C2: strict negativity supplies each factor; existential conclusion suffices for parent. |
| `two_forms_ne` | `SymmetricRelation/Small.lean:46` | PASS | Elementary quantitative bound prevents cancellation in both two-slot forms. |
| `exists_small_ratio` | `SymmetricRelation/Small.lean:62` | PASS | F-B: explicit axes chosen using n2 and the action ratio, for arbitrary positive masses. |
| `fc_ne_zero_two` | `SymmetricRelation/Small.lean:105` | PASS | F-B: exhaustive identity/swap split and small-ratio estimate. |

## Definition classification

All seven new definitions/abbreviations are intended literal objects on their whole stated carriers: `relation` and `fc_def` are the sums/product in Fc-def; `relationPoly` is the universal polynomial product; `snocZero` appends zero; `relLim` is the actual outer limiting expression; `peelRel` deletes the stated coefficients; `peelPerm` deletes the preimage of the last output slot and constructs an equivalence by injectivity and finiteness. No junk branch, arbitrary chosen value, theorem bundle, or fallback is used. The usual off-axes values of the original physical definitions are not used to discharge any guarded physical conclusion.

## Notes and source boundaries

N1 (minor, naming): no duplicate fully qualified declaration was found in the source scan. Inside `Nondegeneracy`, the new `coeffs_one` takes precedence over the opened `Polynomial.coeffs_one` (Mathlib/Algebra/Polynomial/Basic.lean:1043); `MvPolynomial.coeffs_one` also exists in its own namespace. Qualify these names in future polynomial calculations when needed. `ArithmeticFunction.sigma_one` and `CoxeterMatrix.relation` are namespace-distinct names; no present ambiguous use was found. Generic names such as `case_A`, `case_lim`, `relLim`, and `peelPerm` are local to the intended namespace.

No new suspected blueprint or pinned-source defect was found. The inherited Fej04r issues are already explicitly recorded at blueprint p10:158–159 (general-n argument omitted) and p10:130 (complex topology/simple-connectedness issue); this real-domain proof supplies the induction and avoids that topology. No independent re-verification of the pinned PDF allegations is claimed. The only implementation departure is the factorwise route explained above. No audit-induced mathematical deviation or production edit occurred.

## Independent validation

Every Lean/Lake check below ran serially with `LEAN_NUM_THREADS=1` and `nice -n 5`; the build used the prescribed shared compile gate. No clean, dependency update, cache download, heartbeat override, or from-scratch library rebuild was performed.

1. Targeted build:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s10f KAM.Planetary.Nondegeneracy.SymmetricRelation
exit 0
[inp-gate] slot 1 acquired 16:03:34 for KAM.Planetary.Nondegeneracy.SymmetricRelation
Build completed successfully (9143 jobs).
```

The gate waited for a shared slot. S10-F's sole warning is `SymmetricRelation/Analytic.lean:129:37`: unused simp argument `Finset.prod_congr rfl`. Replayed upstream warnings are not findings in the scoped files. No default-heartbeat failure occurred.

2. Fresh signature/definition/axiom probe in `.lake/abi-scratch/S10FAudit.lean`:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S10FAudit.lean
exit 0
```

The successful probe checks the two exact theorem types and literal definition formulas:

```lean
example {n : ℕ} : (D : Data n) → (c : Vec n × Vec n) →
    AnalyticOnNhd ℝ (fc_def D c) (axes n) := @fc_analytic n
example {n : ℕ} : (D : Data n) → 2 ≤ n → ∀ {c : Vec n × Vec n},
    c ≠ 0 → ∃ a ∈ axes n, fc_def D c a ≠ 0 := @f_nonzero n
example {n : ℕ} (D : Data n) (c : Vec n × Vec n)
    (p : Equiv.Perm (Fin n)) (a : Vec n) :
    relation D c p a = (∑ i, c.1 i * nu D (action D a) i) +
      ∑ j, c.2 j * sigma D a (p j) := rfl
example {n : ℕ} (D : Data n) (c : Vec n × Vec n) (a : Vec n) :
    fc_def D c a = ∏ p : Equiv.Perm (Fin n), relation D c p a := rfl
```

An initial version of the auditor's scratch probe exited 1 because its two right-hand sides omitted the explicit dimension after `@`. The corrected version above exits 0; this was a probe construction error, not a package defect. All 29 public theorems were independently queried with `#print axioms`, with exact output:

```text
'KAM.Planetary.Nondegeneracy.fc_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.f_nonzero_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.f_nonzero_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.f_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.eval₂_relationPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.relationPoly_isSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.esymm_sorted' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.exists_relation_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.analyticAt_nu_action' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.fc_analytic_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.tendsto_nu_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.eventually_ne_of_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.case_A' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.case_lim' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.castSucc_peelPerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.relLim_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.coeffs_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.sigma_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.sigma_outer_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.sigma_cons_close' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.tendsto_sigma_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.eventually_cons_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.relation_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.tendsto_relation' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.relation_of_fast_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.fc_ne_zero_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.two_forms_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.exists_small_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.fc_ne_zero_two' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay, one invocation:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Nondegeneracy.SymmetricRelation KAM.Planetary.Nondegeneracy.SymmetricRelation.Defs KAM.Planetary.Nondegeneracy.SymmetricRelation.Analytic KAM.Planetary.Nondegeneracy.SymmetricRelation.Limits KAM.Planetary.Nondegeneracy.SymmetricRelation.Cases KAM.Planetary.Nondegeneracy.SymmetricRelation.Small
exit 0
replaying KAM.Planetary.Nondegeneracy.SymmetricRelation
replaying KAM.Planetary.Nondegeneracy.SymmetricRelation.Defs
replaying KAM.Planetary.Nondegeneracy.SymmetricRelation.Cases
replaying KAM.Planetary.Nondegeneracy.SymmetricRelation.Limits
replaying KAM.Planetary.Nondegeneracy.SymmetricRelation.Small
replaying KAM.Planetary.Nondegeneracy.SymmetricRelation.Analytic
```

4. Whole-library co-import:

```text
LEAN_NUM_THREADS=1 nice -n 5 bash /mnt/HC_Volume_106379410/orchestrator-tools/main_name_clash_check.sh /root/code/KAM-inp-s10f KAM.Planetary.Nondegeneracy.SymmetricRelation KAM.Planetary.Nondegeneracy.SymmetricRelation.Defs KAM.Planetary.Nondegeneracy.SymmetricRelation.Analytic KAM.Planetary.Nondegeneracy.SymmetricRelation.Limits KAM.Planetary.Nondegeneracy.SymmetricRelation.Cases KAM.Planetary.Nondegeneracy.SymmetricRelation.Small
exit 0
name-clash check OK (6 package modules + every built KAM module; 0 base clash(es) skipped)
```

This imports all 782 already-built KAM source modules together with all six package modules; no module was excluded to suppress a base collision. Three of the 785 KAM source modules have no local `.olean`: `KAM/Planetary/Quantitative/Thresholds.lean`, `KAM/Planetary/Exponential/Setting.lean`, and `KAM/Planetary/AMD/Setting.lean`. These were source-inspected for names: they declare in `KAM.Planetary` and its `QuantitativeData` namespace, and introduce none of the S10-F fully qualified names. Thus runtime co-import covers every available built module; the three unbuilt modules receive a source-level collision check, not a claimed runtime import. No unrelated build was launched to extend this scope. The separate source scan found only namespace-distinct Mathlib names discussed in N1. The scratch probe confirms resolution of `coeffs_one`, `Polynomial.coeffs_one`, `sigma_one`, and `ArithmeticFunction.sigma_one`.

5. Required source lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
exit 1
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (787 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The only failure is the explicitly permitted stale generated root. It was not regenerated. The 47 frozen modules in the 97-module KAM source import closure are all manifest-state `SEALED` definitions; no frozen theorem and no provider is imported. All six files have copyright, `module`, public imports, module docstring, and exposed public section. Their complete line counts are 133 (facade), 35 (Defs), 144 (Analytic), 146 (Limits), 122 (Cases), and 141 (Small), totalling 721. Static scoped scan found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, or `set_option`.

6. Repository integrity:

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
exit 0; empty diff

git diff --check inp...HEAD
exit 0; no whitespace errors

git diff --check -- docs/tracks/P/audits/S10-F-audit-1.md
exit 0 (report is untracked; also checked directly for trailing whitespace and 36 declaration rows)
```

Both triple-dot diff commands emit Git's multiple-merge-base warning documented above. Temporary probes were removed after validation. The audit changed only this report; the pre-existing untracked S10-F handoff was retained. No production source, frozen file, manifest, generated file, or git state was changed. Remaining uncertainty is limited to the three unbuilt modules’ runtime co-import, upstream results not re-audited within this package-only assignment, and the inherited source allegations; no unpaid obligation remains inside the specified S10-F slice.

