# P11B revision-2 delta design audit

**Overall verdict: PASS.** Revision 2 resolves both blocking findings, F1 and F2. The changed and added signatures preserve the source conclusions and consumer requirements. No new blocking design finding was found. N1 remains an explicit implementation release gate; this verdict approves the revised design surface, not theorem proofs or package release.

Date: 2026-10-28. Independent, refute-first delta audit under `/root/code/KAM-inp/.drafts/briefs/inp-audit-design.md`. Re-read repository `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the audit brief, the first report, revision-2 handoff and full revision diff. Used the manuscript-audit method already applied in audit 1: immutable inputs, separate discovery/refutation passes, and proposed repairs kept separate from sources. No repairs were made.

## Snapshot and exact delta

| Input | Revision / SHA256 |
|---|---|
| Revision-2 HEAD | `f369f9a04e6c590878207d6ea159406a6fdb9781` |
| Revision-1 comparison | `323c9214987b70b32939191a489fc417c9ebf5f3` |
| Design `docs/tracks/P/design/P11B-LEAN-DESIGN.md` | `8b3fd811a8c13414699fb79dc55e7b1b74e90cebf697f89e76a053ecb52c0bdd` |
| S2 = `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean` | `6800132b3e98b3badc215d5cb1cccc6b016e2f14ec976b661519e436cbf39596` |
| `DESIGN-P11B-design-audit-1.md` | `50d14b68c31f4fa382346e60382e6790bb31cc3c1568df513df5b1b5b0627464` |
| p11a3 blueprint | `90251ed2045353dd2c9574b5f2c53588eb5762ea9dbc86ed9075c00bf8d9ad1c` |
| p11a4 blueprint | `c88030106491131ffde29078d1f0919ae092592bf37e1bbc68a87ab087369b2b` |
| Adjacent P11A signatures, initial delta interface snapshot | `c1ef941ba62268340fdd602324da17a3962d8755f171e1d540a9ca67d4752960` |

S2 has **958 lines, 136 explicit declarations, 30 theorem signatures**. Appendix A is byte-identical. Relative to the revision-1 appendix, the exact non-comment declaration changes are:

- Added `SelectionExtensionChain`, `selection_iteration_parameter_blocks`, and `selection_iteration_parameter_first`.
- Changed `SelectionFiniteChain`, `finite_extension`, `selectionFixedKey`, `schedule_props`, and `free_radius`.
- `adm_budget_beta` and `displacement_power` have unchanged textual types but changed meaning through the key. Every descendant output record also inherits the revised prefix representation. `SelectionIteration.real_angle_derivative` has a new explanatory comment, with unchanged quantifiers and bound.

No declaration was deleted; no imports or ambient carriers changed. The five changed declarations, three added declarations, dependent uniform exports, prefix consumers, release-gate prose and package adjustments were independently checked below. The remaining declaration classifications are carried forward from audit 1 after verifying exact code equality, not represented as a new full audit of their proofs. Both the revision-2 commit and `git diff inp...HEAD` touch only the design document. The audit-1 report was already untracked when this delta audit started and is preserved.

## Re-check of every earlier finding

| Earlier ID | Severity | Delta verdict | Evidence and remaining action |
|---|---|---|---|
| F1 | Major | **RESOLVED** | S2:362–397 splits arbitrary analytic nested prefixes from resonance-retained prefixes. No further signature fix required. |
| F2 | Major | **RESOLVED** | S2:889–910 replaces h by actual M0 in the fixed-data key. Both uniform exports quantify over all same-key data after choosing coefficients. |
| N1 | Note | **RETAINED AS AN EXPLICIT RELEASE GATE** | Revision-2 section specifies the real-collar supplier, exact P11A bridges and PP1-4 landing/build prerequisite. These are still unproved obligations, not signature assumptions. |
| N2 | Note | **RESOLVED AT DESIGN LEVEL** | S2:209–210 and 359 expose the scalar clauses; S2:523–542 expose O4/E4 helpers; B08 now lists the intermediate finite-divisor proof goals. |

### F1: arbitrary nested analytic prefixes are restored

The source `bpP:p11a:finite-extension`, p11a3:156–165, assumes nonempty compact nested sets and bounded holomorphic real increments. Its graph packet record (`P-p11a3.nodes.md`, node `bpP:p11a:finite-extension`) contains no resonance-retention equation. S2:362–373 now contains exactly the corresponding initial/nesting, compactness, nonemptiness, holomorphy, reality and bound fields. The shell equation occurs only in `SelectionFiniteChain` at S2:377–379. `finite_extension` now assumes the weaker `SelectionExtensionChain`, while `finite_divisor` and `finite_measure` still assume the source's retained prefix.

The revised stronger predicate extends the weaker one, so B09 supplies `hc.toSelectionExtensionChain` to B05. The conclusion, derivative order, Euclidean/max-norm factors, fixed real neighbourhood and extension constants of `finite_extension` are unchanged. Thus this is a valid removal of the added premise, with no compensating loss in the conclusion.

Refutation replay: in the audit-1 example h(I)=I²/2, K=[-1,1], zero frequency increments and K0=K1=K, the source extension remains available even though b=0 fails the first resonance test. The new extension predicate admits this example; it no longer demands that K1 equal the smaller retained set. Checking the converse consumer did not uncover a loss: every retained prefix projects to the analytic prefix, and its retained equation remains available for shell testing. **F1 is closed.**

### F2: fixed-data uniformity now permits varying h

S2:889–890 now reads:

```lean
def selectionFixedKey (d : SelectionData n) :=
  (d.μ, d.ρ, d.τ, d.ϑ, d.strip, d.C₁, d.M, d.loss, d.K, selectionM₀ d)
```

This is the fixed numerical/geometric list in p11a3:402–410 (`adm-budget-beta`) and p11a4:180–186 (`displacement-power`). There is no fixed-function equality in the key. `adm_budget_beta` chooses c before universally quantifying over every d with that key. `displacement_power` likewise chooses cD and cstar before d, epsilon and f, and returns one complete family witness with the displacement bound.

Refutation replay: replacing h by h+1 preserves the frozen frequency map, all frequency jets and actual M0, hence the new key. It is no longer excluded by equality of h. More generally the universal d binder covers distinct Hamiltonians with the same listed numerical/geometric data. Choosing the existential constants after a representative d0 does not reintroduce a fixed-h premise: the same chosen constants must work for **all** d in its key class.

The design's proposed constant proof is compatible with the formulas: `selectionCDelta` uses only n, mu, tau, strip and C1 through T0; `selectionCGamma` uses only the fixed key's geometry, exponents, M and loss through `selectionChat`. Their product is invariant under key equality. The actual M0 used by the admissible threshold is now explicitly fixed. `adm_budget` supplies the same beta exponent for the lower-budget specialization. No new dependence on beta, epsilon, f or iteration index is permitted. **F2 is closed.**

The external-upper-bound M0 interface of Part 11 still requires P11a5's monotone minorant. This is the same separate downstream task as before; the source p11a3/4 statements fix actual M0, so replacing it by an inequality inside this key is not required here.

### N2: added scalar conclusions and derivative helpers

`schedule_props` adds the final derivative-sum bound <=C1 of source SC3 (p11a3:120). It follows from the already-returned bound <=8 lambda0/t0 and the existing h2 with t0>0. No new input premise or constant appears.

`free_radius` adds adapted epsilon0/s0<=lambdaMax, as p11a4:37–42 states. The balancing identity gives sqrt(2 n C1 epsilon); epsilon<=lambdaMax²/(2 n C1), positivity and the earlier admissibility result give the new conclusion. The adapted radius, epsilon0=2 epsilon and threshold are unchanged.

The two new helpers are explicitly conditional implementation lemmas with distinct names, not source theorem replacements. Their `SelectionIteration` input supplies previously constructed maps. The source exports still construct output records from raw source data, so this does not violate the prohibition on conclusion-shaped standing premises.

For `selection_iteration_parameter_blocks`, fix z in its stated phase domain. Joint map holomorphy restricts to the full parameter collar. Each projected defect has its **own** whole-collar bound, A or alpha, from `map_angle_bound` or `map_action_bound`; parameter Cauchy therefore yields the exact separate O4 estimates (p11a3:290). The inner radius is strictly positive and strictly smaller than the outer one. Although the helper permits an arbitrary schedule a, these radius hypotheses and its given domain point supply the needed local positivity; no omitted schedule-wide smallness is needed. At j=0 use the block sup bounds and `norm_iteratedFDeriv_zero`, with 0^0=1. The upstream `param_cauchy` requires j>=1, so its direct application is reserved for those orders. This edge case needs a proof branch, not another premise.

For `selection_iteration_parameter_first`, substitute t'=t/2 and j=1 in the returned joint parameter bound. Its hypothesis t>0 supplies 0<t/2<t, and `norm_iteratedFDeriv_one` identifies the norm with the Frechet derivative norm. The result is 2 max(A,alpha)/t, which implies source E4's 2(A+alpha)/t. Nonnegativity of A and alpha follows from their returned block bounds at the supplied domain point; hb in the smaller collar lies in the full collar. There is no illicit conversion of the max estimate into separate smaller constants.

The finite-divisor local goals remain compatible with its unchanged signature: the retained-prefix tail gives one gamma loss, the shell test supplies 2 gamma, and subtraction gives the final gamma divisor. The endpoint T_m and the empty tail for m=nu are explicitly retained. **N2 is closed at the signature/design level.**

### N1: reconciled scope, not a discharged proof

The revision explicitly keeps B10 unreleased until a local `selection_real_angle_derivative_on_collar` supplier is proved or P11A exports the stronger collar clause. That is the right distinction: the current P11A `canonical_step_real` still returns its derivative bound only for b in S.E, whereas P11B's unchanged output field covers every real b in the complex collar. Current adjacent P11A signatures were re-read rather than assumed unchanged: their initial delta hash differs from audit 1, but `canonical_step_real` (now lines 530–544), `real_lipschitz` (420–431), and `param_cauchy` (274–280) retain the relevant interface shapes.

During closeout the concurrently edited P11A draft changed again to SHA256 `1a4b339d7d9008ff8d1aa5f2a85addc1b0f3476c40ab8fbf7e922cf3f9be8493`. The four relevant signatures (`param_cauchy`, `real_lipschitz`, `canonical_step_real`, `canonical_step_param`, lines 274, 420, 530 and 545) were re-read at that snapshot and retain the same contracts used here. Other changes in that neighboring draft are outside this delta audit.

The proposed supplier route is coherent: prove the real C² periodic angle field and uniform size/derivative bounds on the whole real collar, apply `real_lipschitz` at time 1, and identify the chosen real flow with the canonical map's angle component by ODE uniqueness. Equality of derivatives must follow from equality as functions, not merely from equality at one initial point. No such equality or final derivative estimate is added as an input assumption of a source export. Exact scalar/singleton tensor, finite-type, thickening, cutoff/domain and frozen-frequency bridges remain prerequisite proofs.

The revision also correctly states that factor-one `chart_field` must land/build through PP1-4 before B16. Its module and olean are still absent from shared `/root/code/KAM-inp` at this delta check. The signature file does not import it and its successful elaboration cannot certify this gate. **N1 is retained as a note and a package-release condition; it is not a surviving F1/F2-type signature defect.**

## Declaration ledger

Each explicit declaration has a row below. The changed/added/dependent rows were audited against their source and consumers in this delta; UNCHANGED rows retain audit-1's classification following an exact code-diff check. All names have namespace `KAM.Planetary`; S2 line locators refer to the hashed revised signatures. Source labels expand to `bpP:p11a:*` (`step:*` to `stepP:p11a:*`). PASS classifies a design statement, not a proof body.

| Lean name (KAM.Planetary.) | Source label (bpP:p11a: unless noted) | Verdict | Delta disposition |
|---|---|---|---|
| `SelectionR` (S2:38) | `sel-data; domain-def` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `SelectionC` (S2:39) | `sel-data; domain-def` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `SelectionPhaseC` (S2:40) | `sel-data; domain-def` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `SelectionPoint` (S2:41) | `sel-data; domain-def` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionReal` (S2:43) | `sel-data; domain-def` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionRe` (S2:44) | `sel-data; domain-def` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionLength` (S2:45) | `sel-data; index-def` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionThick` (S2:46) | `sel-data; index-def` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionDomain` (S2:48) | `domain-def` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionScalar` (S2:50) | `sel-data; index-def` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionDG` (S2:53) | `sel-data; index-def` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionDGVector` (S2:56) | `sel-data; index-def` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `SelectionData` (S2:62) | `sel-data` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `SelectionPerturbation` (S2:103) | `sel-data(c)` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `sel_data` (S2:112) | `sel-data` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionCN` (S2:114) | `fourier-cutoff` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionCutoffError` (S2:116) | `fourier-cutoff` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionExponent` (S2:118) | `schedule-consts` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionVarpi` (S2:119) | `schedule-consts` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionQ` (S2:120) | `schedule-consts` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionVarrho` (S2:121) | `schedule-consts` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionCQ` (S2:122) | `schedule-consts` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionG` (S2:123) | `schedule-consts` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `schedule_consts` (S2:127) | `schedule-consts` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `schedule_ratios` (S2:130) | `schedule-ratios` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `geom_recursion` (S2:136) | `geom-recursion` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `SelectionSchedule` (S2:145) | `schedule` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionT` (S2:155) | `schedule` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionD` (S2:156) | `schedule` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectiont` (S2:157) | `schedule` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionε` (S2:159) | `schedule` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selections` (S2:161) | `schedule` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionσ` (S2:162) | `schedule` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectiond` (S2:163) | `schedule` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionr` (S2:166) | `schedule` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionell` (S2:168) | `schedule` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionTail` (S2:170) | `schedule` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionQsharp` (S2:171) | `schedule` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionQ₀` (S2:174) | `schedule` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `schedule` (S2:177) | `schedule` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `strip_budget` (S2:179) | `strip-budget` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `schedule_props` (S2:192) | `schedule-props:SC3` | PASS | CHANGED: explicit derivative-sum <= C1, same source premises. |
| `selectionBumpRaw` (S2:217) | `smooth-cutoff` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionBump` (S2:218) | `smooth-cutoff` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionBumpL1` (S2:220) | `smooth-cutoff` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionCutoffC` (S2:221) | `smooth-cutoff` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionExtensionC` (S2:223) | `smooth-cutoff` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `smooth_cutoff` (S2:228) | `smooth-cutoff` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `SelectionChain` (S2:237) | `retained-def; inductive-lemma` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionFrequency` (S2:244) | `retained-def; inductive-lemma` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionEnergy` (S2:247) | `retained-def; inductive-lemma` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionCompose` (S2:249) | `sec-comp#data` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionModeLength` (S2:254) | `schedule` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionShell` (S2:255) | `schedule` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionModeStage` (S2:259) | `schedule` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionExtendedFrequency` (S2:261) | `finite-extension` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionRetained` (S2:266) | `retained-def` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionInitial` (S2:271) | `initial` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `initial` (S2:275) | `initial` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionM₀` (S2:291) | `sel-data(d)` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionChat` (S2:294) | `sublevel; power-law; sel-data` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionCDio` (S2:300) | `sublevel; power-law; sel-data` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionGamma` (S2:302) | `sublevel; power-law; sel-data` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionT₀` (S2:306) | `adm-params` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectiont₀` (S2:309) | `adm-params` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionXi` (S2:311) | `adm-params` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionThetaMax` (S2:314) | `adm-params` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionLambdaMax` (S2:317) | `adm-params` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionAdmissible` (S2:322) | `adm-params` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `adm_params` (S2:323) | `adm-params` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionAdapted` (S2:327) | `free-radius` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `SelectionAdmissibility` (S2:332) | `adm-choice` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `adm_choice` (S2:347) | `adm-choice` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `free_radius` (S2:352) | `free-radius` | PASS | CHANGED: explicit adapted lambda <= lambdaMax, no extra smallness. |
| `SelectionExtensionChain` (S2:362) | `finite-extension` | PASS | NEW: analytic nested-prefix premises only; no resonance restriction. |
| `SelectionFiniteChain` (S2:377) | `retained-def; finite-divisor; finite-measure` | PASS | CHANGED: retains shell recursion and projects to the weaker analytic prefix. |
| `sec_retained_data` (S2:381) | `retained-def` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `finite_extension` (S2:383) | `finite-extension` | PASS | CHANGED: F1 closed; accepts the full source nested-prefix class. |
| `finite_divisor` (S2:399) | `finite-divisor` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `continuous_series_on_compact` (S2:412) | `step:ps-lim (local supplier)` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionΛ` (S2:422) | `homological; exported-sums` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionA` (S2:425) | `inductive-lemma:O3; exported-sums` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionAlpha` (S2:429) | `inductive-lemma:O3; exported-sums` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionKappa` (S2:431) | `inductive-lemma:O3; exported-sums` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionMapBudget` (S2:433) | `inductive-lemma:O3; exported-sums` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionRealBudget` (S2:435) | `inductive-lemma:O3; exported-sums` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `SelectionIteration` (S2:442) | `inductive-lemma; step:ps-iter` | PASS | COMMENT/DEPENDENT: real-collar output unchanged; local supplier now explicit (N1). |
| `selection_iteration_parameter_blocks` (S2:523) | `inductive-lemma:O4` | PASS | NEW helper: separate block Cauchy bounds; j=0 checked separately. |
| `selection_iteration_parameter_first` (S2:535) | `exported-sums:E4` | PASS | NEW helper: joint j=1 estimate at t/2; max bound is stronger than source sum. |
| `inductive_lemma` (S2:545) | `inductive-lemma; step:ps-iter` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `inductive_lemma_adapted` (S2:549) | `inductive-lemma; step:ps-iter` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `SelectionOutput` (S2:555) | `parameter-selection` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `parameter_selection` (S2:614) | `parameter-selection` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionQactual` (S2:619) | `exported-sums` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `exported_sums` (S2:623) | `exported-sums` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `param_lip_sum` (S2:642) | `param-lip-sum` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `finite_measure` (S2:650) | `finite-measure` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `SelectionComposition` (S2:667) | `composition` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `composition` (S2:712) | `composition` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `sec_comp_data` (S2:717) | `sec-comp#data` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionEvaluation` (S2:719) | `sec-limit#data` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `sec_limit_data` (S2:722) | `sec-limit#data` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `SelectionLimit` (S2:725) | `limit-map` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `limit_map` (S2:753) | `limit-map` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionHamiltonian` (S2:757) | `limit-torus; p0:hamsymp` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `SelectionTori` (S2:760) | `limit-torus` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `limit_torus` (S2:779) | `limit-torus` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `collar_increment_lipschitz` (S2:784) | `step:lf-stage (local supplier)` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionDelta` (S2:791) | `displacement; gamma-inverse` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionCDelta` (S2:794) | `displacement; gamma-inverse` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionCGamma` (S2:797) | `displacement; gamma-inverse` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `gamma_inverse` (S2:801) | `displacement; gamma-inverse` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `SelectionDisplacement` (S2:804) | `displacement` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `displacement` (S2:815) | `displacement` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `SelectionLipschitz` (S2:819) | `lipschitz-family` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `lipschitz_family` (S2:827) | `lipschitz-family` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionHalfCell` (S2:831) | `evaluation-bilipschitz` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionClosedCell` (S2:833) | `evaluation-bilipschitz` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionQuotient` (S2:835) | `evaluation-bilipschitz` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `SelectionEvaluationOutput` (S2:839) | `evaluation-bilipschitz; situation` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `evaluation_bilipschitz` (S2:880) | `evaluation-bilipschitz; situation` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `situation` (S2:885) | `evaluation-bilipschitz; situation` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionFixedKey` (S2:889) | `adm-budget-beta; displacement-power` | PASS | CHANGED: F2 closed; actual M0 replaces h in numerical/geometric key. |
| `selectionBetaExponent` (S2:891) | `adm-budget-beta` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `adm_budget_beta` (S2:896) | `adm-budget-beta` | PASS | DEPENDENT: universal same-key family now includes varying h and beta. |
| `displacement_power` (S2:902) | `displacement-power` | PASS | DEPENDENT: cD,cstar precede varying h,beta,epsilon,f; one final witness. |
| `SelectionRates` (S2:913) | `adm-budget` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionBudgetD` (S2:925) | `adm-budget` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionBudgetG` (S2:927) | `adm-budget` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionBudgetL` (S2:929) | `adm-budget` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionBudgetJ` (S2:930) | `adm-budget` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionBudgetX` (S2:932) | `adm-budget` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionBudgetH` (S2:934) | `adm-budget` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionBudgetExponent` (S2:938) | `adm-budget` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `selectionFamilyBounds` (S2:942) | `adm-budget` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |
| `adm_budget` (S2:949) | `adm-budget` | PASS | UNCHANGED; audit-1 classification retained after code-diff check. |

## Consumer, frozen-object, definition and package verdicts

**Consumers: PASS for the revised design, with N1 gates retained.** B09's retained chain supplies the weaker extension premise by its generated parent projection. B08/B09 still possess the retention equation. B10 can use the new separate-block helper for O4 and its first-derivative helper for E4 without importing any later package. The new scalar conjunctions change projection positions, but this is a design-only surface with no production proof consumers to break; future proofs must destructure the revised signatures. The final output records and their shared witnesses have unchanged content. P11a5 and Part 11 now have Hamiltonian-independent fixed-data uniform exports, subject to P11a5's existing bounded-M0/minorant and zero-case obligations. The new helpers neither replace these exports nor ask a downstream consumer to supply a constructed iteration as an extra source premise.

The brief's general ODE-consumer search in I/P and N Parts 7/11/12 is unaffected: no changed declaration concerns general flow uniqueness, continuation or a solution predicate. The source/frozen orbit, field and solution-predicate boundaries from audit 1 therefore remain applicable.

**Frozen objects and definitions: PASS.** No frozen file, manifest, ambient type, norm instance, dynamics definition or public input structure changed. `selectionFixedKey` now expresses the intended numerical/geometric data, including actual M0. `SelectionExtensionChain` has exactly analytic prefix premises; the subclass adds only source retention. No junk value is relied on by either new derivative helper: their supplied domain points and strict radius bounds guard the actual use sites. The original frozen `Phase`, strip/collar, frequency, field and form definitions remain the referenced objects. No frozen-source defect was found.

**Packages: PASS as a design; release conditions remain open.** Recomputed all 20 package waves from the revised direct-input table: no cycle, all declared waves match, maximum wave 14. Listed estimates remain 200–800 lines, below the 1500-line cap. B02 owns both prefix predicates; B05 accepts the weaker one; B09 projects its retained prefix; B10 owns the two local derivative helpers and the real-collar supplier obligation. B10 still has an 800-line estimate and must split before the hard cap if its expanded implementation exceeds that estimate. No type-level edge to a later module was added. There is no production Lean module changed or targeted production build to run.

## Verification receipts

- **Signature elaboration: exit 0, exactly 30 sorry warnings, no errors or other Lean diagnostics.** Exact canonical S2 copied to `.drafts/scratch/P11BSignatures-audit2.lean`, with byte equality checked. Required command:

  ```text
  /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh \
    /root/code/KAM-inp-design-p11b .drafts/scratch/P11BSignatures-audit2.lean
  ```

  The command is additionally serialized with the build-slot locks and the other two signature-slot locks, leaving one slot for the required wrapper. It uses `LEAN_NUM_THREADS=1`, `nice -n 5` and the existing shared build. No heartbeat override, clean, cache fetch, update or library rebuild is used. The signature file is run once.

- **New-helper API probe: exit 0; all nine #check commands succeeded, no errors or warnings.** Temporary `.lake/abi-scratch/P11BDeltaAPIs.lean`, run through the same wrapper and serialization. It checks `norm_iteratedFDeriv_zero`, `norm_iteratedFDeriv_one` and the seven Mathlib names from audit 1: `Real.log_le_sub_one_of_pos`, `HasCompactSupport.hasFDerivAt_convolution_right`, `MeasureTheory.tendsto_measure_iInter_atTop`, `hasSum_geometric_of_norm_lt_one`, `tendstoUniformlyOn_tsum_nat`, `continuousOn_tsum`, `HasFDerivAt.comp`. No additional external theorem is introduced by the changed signatures.

- **`scripts/lint_sources.sh`: exit 0.** Exact output: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (144 frozen declarations)`. Its ABI subprocess is routed through the existing `.drafts/gated-bin/lake` shim and required signature gate, with `P11B_ORIGINAL_PATH` restored inside the shim. The outer locks serialize this check with the auditor's other Lean calls. No generated file is rewritten.

- **Mechanical checks: PASS.** Exact Appendix A/canonical/scratch equality; 136 explicit declarations, 30 theorem bodies, all `sorry`, no definition body `sorry`; 958-line signature module; unchanged 119/119 unique relevant graph nodes, no missing or extra row; 20-package DAG and all 14 computed waves; `git diff --check HEAD^ HEAD` exit 0. Final hashes of the design, signatures, source blueprints and audit-1 report agree with the snapshot above; no trailing whitespace or pending check markers; git status shows only the pre-existing audit-1 report and the new audit-2 report.

- **Axioms/proof status.** All 30 bodies remain `sorry`. The current designer receipt reports `[propext, sorryAx, Classical.choice, Quot.sound]` for `finite_extension`, `adm_budget_beta`, `parameter_selection`, `limit_torus`, `evaluation_bilipschitz` and `displacement_power`. This receipt is distinguished from the independent signature/API/lint reruns above; no separate axiom rerun or proof/kernel validation was undertaken in this delta. No frozen theorem is closed.

## Closeout and remaining notes

No new F finding; F1 and F2 are resolved. The outstanding N1 implementation gates are explicitly preserved and must be enforced before the corresponding prover packages are released. The source compact-real-set continuity gap, inherited real-flow proofs and absence of a common positive-action-radius normal form are unchanged and are not closed by this audit.

Suspected new pinned-source errata: none. New deviations from the audited source statements: none found in this revision. The newly exposed scalar clauses and conditional helpers are faithful consequences with distinct implementation names.

Only `/root/code/KAM-inp-design-p11b/docs/tracks/P/design/DESIGN-P11B-design-audit-2.md` is written as a deliverable. The previous report, design, handoff, canonical signatures, frozen files and manifest are preserved; temporary audit probes and the scratch copy are removed after their checks. No state-changing git command is used. **PASS is a delta design verdict, not proof completion or authorization to bypass N1.**
