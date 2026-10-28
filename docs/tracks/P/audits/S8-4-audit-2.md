# Independent S8-4 package audit 2 — delta audit

Overall package verdict: **FAIL**. Round 1 F1 is resolved. F2 remains open: the new square-root conversion is a correct conditional expansion formula, but does not export the literal blueprint conclusion under just its hypotheses. In particular it requires a zero constant term. The three signed theorem statements pass unchanged. No frozen anchor is sealed by this infrastructure package.

Worktree: `/root/code/KAM-inp-s84`. Audited HEAD: `7fe32f2c38cb0bf0e64b39154c88f80623bf419a`; Round 1 baseline: `d2f7c975`. The explicit user destination overrides the generic brief's main-worktree destination. Only this report is retained; probes are temporary worktree `.lake/abi-scratch/` files. No production edits or state-changing git commands.

Authority: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, supplied package-audit brief, both handoffs (including the untracked/ignored `.drafts/handoff-S8-4.md` Round 2 notes), Round 1 report, P810 design inventory/row/proof-cut policy, exact signatures, track P statement, blueprint p8:216–234. This is a delta audit; the unchanged declaration-by-declaration classifications and proof review in audit 1 remain its baseline, not a claim that all proofs were rederived in this turn.

## Delta and signed statements

`git diff d2f7c975 HEAD --stat` contains exactly:

```text
 KAM/Planetary/SecularForm/Quartic.lean            |   1 +
 KAM/Planetary/SecularForm/Quartic/Conversion.lean | 439 ++++++++++++++++++++++
 KAM/Planetary/SecularForm/Quartic/PairJet.lean    |  14 +-
 3 files changed, 441 insertions(+), 13 deletions(-)
```

The facade adds only the public Conversion import. PairJet adds the JetsPolar import and removes the 13-line duplicate helper; all call sites remain unchanged. Conversion is entirely new. The tracked Round 2 commit does not change a handoff, signed definition, signed theorem header, or any other proof file. The handoff's “432 lines” is inaccurate: Conversion has **439** lines, safely below 1500.

All five signed definitions are byte-unchanged because the whole Defs file is identical to the baseline. All three signed theorem headers were freshly compared with `/root/code/KAM-inp/.drafts/design/P810Signatures.lean`: exact text equality, including binder order. Fresh copies under `audit2_` names elaborate with direct applications `quartic D hn`, `quartic_pair_scaling D hij hI hJ u v hu hv hSep`, and `quartic_scaling`. No draft proof body is imported. The unused signed premises remain original premises.

Signature SHA-256: `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`.
Blueprint SHA-256: `413806b9fcc86156e0b241da85668677b44bf142897c7039940504a50ae1febc`.
Design SHA-256: `f555e21a468123ce906f6818359cb8faaffc5d0435ea0f70c65967cec38722c4`.
These all match the Round 1 recorded values.

`git diff inp...HEAD` was also inspected as requested. Current inp was `55012a5372231318012c4f9e6249a5f3e0c5b302`. Git reports multiple merge bases and selects `9400863e51e5f140a497a3774d3dff7b479e0d04`. The full comparison includes inherited DiagonalJet files and audit documents; only the Quartic package and its delta are in the audit scope.

## Findings

**F1 — RESOLVED.** PairJet no longer declares `KAM.Planetary.SecularForm.iteratedFDeriv_comp_clm_of_isOpen`. Its unqualified uses (including downstream Jet/Coefficients/Diagonal) now resolve to the general `KAM.Planetary.iteratedFDeriv_comp_clm_of_isOpen`, `PGAssembly/JetsPolar.lean:34`. That result is generic in the scalar field and finite differentiability order; ℝ/order four is a valid specialization. JetsPolar imports only Mathlib. It adds no provider or frozen theorem dependency. Fresh code-masked name comparison finds 119 public package declarations and **zero external public leaf-name collisions**. Private `qcv_*` helpers do not create public aliases. No `_root_` declaration or root shadow was found.

**F2 — NOT RESOLVED: stronger hypothesis and missing literal attachment.** `Quartic/Conversion.lean:351–367` exports `quartic_sqrt_chart_conversion`. Its corrections have exactly the required signs, denominators, A/4, A′/4 and B/8 coefficients. The square-root map is the exact map, the scalar product is the real coordinate dot product, and positivity of the two actions is legitimate. However, at lines 353–355 its premise is

```text
W(v) − W₂(v) − Σ c_m quarticMonomials(v)_m = O(‖v‖⁵).
```

This is not simply “W₂ and W₄ are the quadratic and quartic parts” of W. It also requires **W(0)=0** and excludes lower odd terms. Evaluating the neighbourhood bound at zero proves W(0)=0, since both displayed polynomials vanish there. The blueprint at `p8-secular-form.tex:221` says “if W₂ ... is the quadratic part and W₄ the quartic part in v”; it does not require the constant part to vanish. Its W is the literal normalized inverse-distance pair average. At circular eccentricities, fixed 0<α<1, its integrand is continuous and strictly positive (distance between the two concentric circular orbits is bounded below by 1−α), so its average is nonzero. The local domain contains these circular points. Thus the literal W cannot satisfy the new hW.

A minimal counterexample to the claimed equivalence of hypothesis forms is the analytic, even, O(2)-invariant function W≡1: its quadratic and quartic parts are both zero, yet hW with A=A′=B=0 and c=0 is false. The fresh Lean probe verifies that the constant function 1 is not O(‖v‖⁵) at zero. This does not refute the proved conditional theorem; it refutes its identification with the literal source statement.

The six-monomial restriction agrees with the invariant quartic structure assigned to q4-str. In the analytic even setting, **after subtracting W(0)** and identifying the Taylor components, an O(‖v‖⁵) remainder is legitimate (indeed the next even order is six). Without these facts it is a stronger premise, not a definition of “quadratic part / quartic part.” Conversion imports only Mathlib and Defs and neither discharges this expansion premise for dimensionlessPair nor identifies its output with the literal fourth jet. No caller of the new theorem exists elsewhere in KAM. The generic helper may assume known expansion data under its own distinct name, but that does not pay the source application.

**Prefactor assessment.** Blueprint p8:221 explicitly concludes the formula “times the appropriate prefactor −G m_i m_j a_j⁻¹.” Omitting this constant is mathematically harmless for a clearly normalized W-only helper; it is not the literal physical Q₄^(ij) conclusion. The new conclusion is an O(‖u‖⁵) expansion of W∘φ, not an equality identifying Q₄^(ij) with the scaled expression. `quartic_pair_scaling` separately supplies the full-function prefactor, but no exported bridge combines it with a centered Taylor expansion and fourth-jet identification. This normalization omission alone can be repaired by a constant-multiplication corollary; the zero-constant premise is the decisive applicability failure. Neither should be silently inferred as already discharged.

To close F2, export the conversion of actual quadratic/quartic Taylor parts allowing an arbitrary constant (or explicitly center the function), discharge the analytic/even/invariant expansion for the intended W, identify the fourth jet, and retain the physical pair prefactor in the literal application. No production repair was attempted by this auditor.

## Delta declaration and graph verdicts

| Node / declaration | Verdict | Reason |
|---|---|---|
| `quartic` / bpP:p8:quartic | PASS WITH NOTES | Exact signed type and proof body unchanged; package q4-a remains incomplete. No frozen seal. |
| `quartic_pair_scaling` | PASS | Signed statement/body unchanged; exact full-function prefactor retained. |
| `quartic_scaling` | PASS | Signed statement/body unchanged; analytic separated-domain result. |
| q4-str / removed duplicate helper | PASS | F1 resolved by shared general chain rule; no renamed duplicate. |
| q4-str / `pair_matW_invariant`, `pair_contDiffOn`, `pair_quartic_structure` | PASS | Statements unchanged; imports now resolve to existing general helper. |
| q4-str / downstream `quartic_jet`, `analyticAt_pairQuartic`, `pairQuartic_of_ray` | PASS | Shared-helper resolution validated by import/build/probe chain; no changed hypotheses. |
| q4-a / `quartic_sqrt_chart_conversion` | PASS as conditional helper; FAIL as literal cut | Correct normalized expansion with A/4, A′/4, B/8; hW excludes nonzero constant term; no physical Taylor-jet application exported. |
| q4-a / overall proof cut p8:232 | FAIL | Scaling/analyticity pass; the literal conversion under only source premises remains unpaid, F2. |
| q4-b | PASS (unchanged baseline) | S8-D exact diagonal expansion, Taylor uniqueness and planet exchange unaffected. |
| q4-c | PASS WITH NOTES (unchanged baseline) | Exact radial derivative definitions/diagonal formulas; repaired printed polynomial and mixed coefficients remain outside the proved interface. |

No new def/abbrev/structure is introduced by the delta. Conversion's 18 `qcv_*` theorem helpers are private elementary identities/bounds; they do not supply assumed physical coefficients. All 34 existing definitions retain audit 1's classification: explicit mathematical objects, finite coordinate maps/carriers, coefficient extraction or domain predicates. Total square roots/inverses/integrals are used analytically only with local positivity/separation guards. The new proof proves its square-root guards on an eventual neighbourhood and does not exploit an invalid-domain fallback. Its product/Pi norm is the max norm; local finite-dimensional norm choice does not change the homogeneous Taylor terms.

Proof inspection of Conversion: exact square-root-square identities, quadratic correction cancellation, six quartic monomial differences, O(‖u‖⁶) tail bounds, weakening to O(‖u‖⁵), and composition of hW via a linear norm bound. No derivative of a bare O-term is taken. These establish the stated conditional expansion, not the missing application to an uncentered pair average.

## Validation

Commands that invoke Lean/Lake use `LEAN_NUM_THREADS=1` and `nice -n 5`. Checks are serialized. The gate waiter was suspended while the fresh probe/kernel/lint checks ran, then resumed; it held no acquired slot during those checks. An initial lint attempt was terminated during its Python frozen-source guard before any ABI Lean process, and rerun serially with the required environment/priority. No clean/update/cache/full-library build was run.

Fresh signature/axiom/refutation probe (exit **0**):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-s84-2-probe.lean
```

The probe copies the three literal signed theorem headers and proves them by the direct applications listed above. It also proves `(f =O[𝓝 0] (fun v => ‖v‖^5)) → f 0 = 0` and the negation of the analogous bound for the constant function 1. There are no errors. Complete axiom output for all 85 current public theorems:

```text
'KAM.Planetary.SecularForm.quartic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairQuartic_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.analyticAt_pairQuartic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.analyticAt_quarticCoeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quartic_sqrt_chart_conversion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planeSq_smul_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planeLength_smul_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairQuartic_of_ray' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quarticCoeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quarticCoeff_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.exists_poly_of_multilinear' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quartic_form_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairProj_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.action_axes_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quartic_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.exists_angle' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.orth_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairEmb_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.vec2_eta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairSlowSecular_pairData' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.action_axis' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.axis_mem_axes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pair_secular_nbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.analyticAt_pairSlowSecular' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.avg_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuous_ppos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planeSq_ppos_sub_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_false_pairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.avg_finset_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.secular_eq_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuous_pairKernel_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.integrableOn_pairKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairKernel_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.secular_false_eq_pairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pair_matW_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pair_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pair_quartic_structure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.poincare_fst_eq_unitPosition' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quartic_pair_scaling' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.matW_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuous_rotW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuous_reflW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairEmb_rotW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairEmb_reflW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.eventually_pair_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pair_rot_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pair_refl_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quartic_scaling' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_diffAt_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_diffAt_KC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_contAt_sepK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_contAt_intK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_contAt_kC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_contAt_KC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_contAt_sep' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_planeSq_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_kC_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_qscU_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_qscU_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_sep_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_good_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_intC_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qscEmbCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_isOpen_separatedDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_unitPosition' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_planeSq_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_planeDot_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_continuous_planeLength' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_continuous_qscU' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_periodic_qscU' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_planeLength_qscU' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_sep_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_sep_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_continuous_sep' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_continuous_G' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_dimensionlessPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_avgC_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.double_integral_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairSlowSecular_eq_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairKernel_eq_quarticPairKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairSlowSecular_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.iteratedDeriv_eq_zero_of_isBigO' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.iteratedDeriv_four_of_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Static hygiene: 21 Quartic files, maximum 439 lines. Code-masked scan found no forbidden proof escape, resource override, EuclideanSpace, or root override. New file has copyright, `module`, public imports, module docstring and exposed public section. Public-name comparison: 119 names, zero external public leaf-name collisions. Import closure: 131 local KAM modules, zero providers, zero frozen theorem modules; all 56 frozen definition modules have manifest state SEALED.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check
```

Both exit 0; no diff/check output apart from git's multiple-merge-base warning on the first command. No protected or generated file is edited. Provider/frozen seal probes are inapplicable: this package has no provider or frozen theorem export.

Kernel replay (exit **0**, one invocation, 21 package modules replayed):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.Quartic KAM.Planetary.SecularForm.Quartic.Conversion KAM.Planetary.SecularForm.Quartic.PairJet
```

Complete output:

```text
replaying KAM.Planetary.SecularForm.Quartic.Conversion
replaying KAM.Planetary.SecularForm.Quartic.Defs
replaying KAM.Planetary.SecularForm.Quartic.PairScaling
replaying KAM.Planetary.SecularForm.Quartic.ScalingTube
replaying KAM.Planetary.SecularForm.Quartic.Orthogonal
replaying KAM.Planetary.SecularForm.Quartic.Coefficients
replaying KAM.Planetary.SecularForm.Quartic.PairAverage
replaying KAM.Planetary.SecularForm.Quartic.Jet
replaying KAM.Planetary.SecularForm.Quartic.PairDecomp
replaying KAM.Planetary.SecularForm.Quartic.ScalingEmb
replaying KAM.Planetary.SecularForm.Quartic.ScalingComplex
replaying KAM.Planetary.SecularForm.Quartic.Diagonal
replaying KAM.Planetary.SecularForm.Quartic.Invariant
replaying KAM.Planetary.SecularForm.Quartic.ScalingReal
replaying KAM.Planetary.SecularForm.Quartic.PairAnalytic
replaying KAM.Planetary.SecularForm.Quartic.PairJet
replaying KAM.Planetary.SecularForm.Quartic.Scaling
replaying KAM.Planetary.SecularForm.Quartic.Taylor
replaying KAM.Planetary.SecularForm.Quartic.Swap
replaying KAM.Planetary.SecularForm.Quartic.PairSymmetry
replaying KAM.Planetary.SecularForm.Quartic
```

## Carried scope notes, errata and deviations

Audit 1 N1 is retained: the exact historical “13:08 OVERNIGHT” log entry was not recovered there. Current design dependencies assign S8-D to S8-4 and S8-X to S8-Q. S8-4 consumes S8-D through the literal `pairSlowSecular_diag_jet` in Diagonal; this delta does not change that. No historical ruling is invented here. Audit 1 N2 also stands: `secular D false` selects the fixed model; the handoff phrase does not assert a false proposition. PairDecomp proves equality to the pair sum on the analytic polydisc.

No new suspected defect in the pinned source or blueprint was found. Blueprint p8:221 explicitly retains the constant pair prefactor and speaks of Taylor parts; the mismatch is in the proposed Lean coverage, not a source erratum. Existing E-P-CP11-2 and the unpaid repaired polynomial/mixed-coefficient obligations remain as in audit 1. The handoff's new file-length discrepancy is documentary only. Its default-heartbeat timeout/splitting note is prover-reported history, not independently reproduced; current code has no budget override. No mathematical or production-code deviation was introduced by the auditor. Prior memory was consulted only for serial package-audit workflow and the permitted generated-root exception; package-specific conclusions were checked in the current worktree.

Full lint (exit **1**, solely the brief-permitted generated-root exception):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (743 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The root was not regenerated. Module checks, the frozen-anchor guard and all 144 frozen declaration ABI hashes pass.

Targeted compile-gate build (exit **0**):

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s84 KAM.Planetary.SecularForm.Quartic
```

Exact gate/result lines:

```text
[inp-gate] slot 1 acquired 18:50:15 for KAM.Planetary.SecularForm.Quartic
Build completed successfully (9177 jobs).
```

The replayed build log contains 27 warnings (unused variables and tactic-linter suggestions); no errors. A warning suggesting a linter-disable option is not a code-level override.

Temporary auditor probe removed after the checks. Final `git status --short` contains only `?? docs/tracks/P/audits/S8-4-audit-2.md`; final `git diff --check` exits 0.
