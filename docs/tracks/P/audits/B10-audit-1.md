# B10 independent package audit 1

**Overall verdict: PASS WITH NOTES.** Build, signature/axiom probes and all 13 kernel replays passed; source lint passed every substantive check and returned 1 only for the explicitly permitted stale generated root. No mathematical or signed-interface defect found in `KAM/Planetary/WeakKAM/Iteration*.lean`.

Audit date: 2026-10-28. HEAD `05e6b5aa24cb019eacc2508bc597cdb123e9b29c`; compared `inp` at `086928650ca9281e65a68123f75f45436881167a`. `git diff inp...HEAD` warns `multiple merge bases, using d69dedecde7104870d7281ffe9dba51228f5e523`; this is the requested literal comparison, not a substituted two-dot comparison. The diff contains 13 B10 modules and four inherited B09 `FiniteMeasure*` modules. The verdict covers only the 13 B10 modules; B09 and P11A interfaces were inspected as dependencies.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief, B10-handoff.md, P11B-LEAN-DESIGN.md (B10 and full node table), both P11B design audits, the live signature file, p11a3/p11a4 blueprint statements/proofs, track P statement, and the frozen definitions in the import closure. The explicit user report destination overrides the generic brief's main-worktree destination. No frozen theorem/provider is delivered by B10: provider=frozen-type and anchor seal-body tests are inapplicable. Signed theorem reconstruction is tested instead. This report certifies infrastructure, not any planetary headline or frozen seal.

## Signed interfaces and release gates

| Export | Verdict | Evidence |
|---|---|---|
| `SelectionIteration` | PASS | All fields, binders, carriers and bounds match the live signature record after comment/whitespace removal. |
| `inductive_lemma` | PASS | Header byte-identical to signature; exact-binder application probe; constructs one whole infinite iteration from raw data, including ε=0. |
| `inductive_lemma_adapted` | PASS | Header byte-identical; exact-binder probe; adapted radius and ε₀=2ε; assumes ε>0 as signed. |
| `selection_iteration_parameter_blocks` | PASS | Header byte-identical; exact-binder probe; separate A/α bounds; every order j, including zero. |
| `selection_iteration_parameter_first` | PASS | Header byte-identical; exact-binder probe; j=1 and t′=t/2 gives exact signed 2 max(A,α)/t. |
| `selection_real_angle_derivative_on_collar` / N1 | PASS | Local conditional supplier; every real b in the collar, every θ, exact exp(real-budget)−1 bound; the same clause is installed in every constructed iteration. |

The live signatures have SHA256 `e5ae0f3f6c134280acd184e6130e2c39bac49485097647cd36f52f7dbf87ef63`; design `b39ec4a5b9b976b355d6afe26047680ea2b1fbb1c86dd4073aa4428528961ea1`. These differ from the older design-audit snapshots, so the comparisons above were made afresh against the live file. Source p11a3 SHA256 `90251ed2045353dd2c9574b5f2c53588eb5762ea9dbc86ed9075c00bf8d9ad1c`, p11a4 `c88030106491131ffde29078d1f0919ae092592bf37e1bbc68a87ab087369b2b`.

## Refutation and completeness

**One coherent chain.** IterationAssemble:35–88 recursively defines `seq ν : {c // IterPrefix ... c ν}`; each successor chooses an extension of exactly its predecessor. `hag` and `hle` preserve all prefix data. The extracted F reads K/R at seq j and Δω/Δh/X at seq(j+1); `hF` proves agreement with every finite prefix. `IterPrefix.transfer` then supplies all pre/post fields of that same F. IterationPred:120–216 includes K/R through ν and increments/maps below ν, including every datum used by the cumulative energy, frequency, and composition. IterationStage:88–108 updates only the new slots and proves `stepChain_agree`. No independent existential witnesses are assembled by index. Conditional base/successor hypotheses in the abstract assembly helper are discharged by `iterPre_base` and `iterPrefix_step` in the raw-data exports.

**N1 on the full real collar.** IterationParam:59–85 takes realInclusion b in actionNbhd E t, without requiring b∈E. It applies delivered P11A `stepV_contDiff`, `stepV_bound`, `stepV_fderiv`, `stepV_periodic` and `real_lipschitz` at time 1. Its `funext` equality to `p11RealFlow` uses `step_flow_real` at every initial x, so rewriting transfers the derivative of the whole function. The inspected upstream proof of `step_flow_real` uses ODE uniqueness with the explicit remainder-reality guard; no derivative equality is inferred merely from equality at a single x. IterationStep:257–277 converts the exact budget and puts this into IterPost; assembly transfers it into SelectionIteration. Iteration:135–145 exports the requested named supplier. Its WeakBudgetCtx/StepFacts/IterPre arguments are implementation hypotheses, not extra inputs of either signed source theorem.

**Interface reconciliation.** `selectionDomain_eq_domain_def`, `selectionΛ_eq_p11Lambda`, `selectionCutoffError_eq_p11Error`, `phaseToC_eq_realInclusion₂`, `selectionReal_eq_realInclusion`, and the stage budget equalities use actual delivered P11A definitions. The retained-set proof consumes B09's literal scalar/singleton tensor, Euclidean-thickening, finite-type amount and frozen-frequency bridges (`FiniteMeasureBridge`, `FiniteMeasureHyp`, `ExtensionFrequency.selectionFrequencyMap_apply`); no replacement carrier, norm instance, or unproved amount comparison is introduced. These dependencies are checked at their B10 call sites, not re-audited as a new B09 package.

**O1–O5 and narrowed signed record.** O1 is recovered by applying `finite_divisor` to `o.chain ν` and using retained recursion; it is not a separate field of the signed record. O2 includes whole-old-collar increments, bounds and reality. Energy holomorphy/reality, frequency holomorphy/reality and recurrence follow from finite sums and chain data; the additional internal `energy_real` field is proved at base and successor. O3 includes joint holomorphy, actual map range, periodicity, reality, symplecticity, affine action dependence, injectivity and unscaled derivative bounds. O4's separate bounds come from applying Cauchy to each projected holomorphic defect with its own sup bound. `param_cauchy_gen` handles j=0 directly before the positive-order estimate. O5 is the canonical-step identity used in `iterPre_step` to establish the cumulative normal form. The signed cumulative field does not explicitly name each local conjugacy, but its constructor proves it from the delivered canonical step. The pointwise/sup and max-norm conventions remain those of the design. No exported constant acquires extra dependence.

| Graph node / clause | Lean witness (relative files in WeakKAM) | Verdict | Reason |
|---|---|---|---|
| `bpP:p11a:inductive-lemma` | Iteration:71 `inductive_lemma`; IterationAssemble:35 | PASS | Raw premises; coherent infinite chain is stronger than finite existence. |
| `stepP:p11a:il-p0` | IterationBase:45 `iterPre_base` | PASS | Initial R, empty composition, true zero energy, real gradient. |
| `stepP:p11a:il-ret` | IterationRetained:76,153,162; Iteration:35 | PASS | Explicit finite-test measure witness gives nonemptiness; closed subset gives compactness. |
| `stepP:p11a:il-c2` / O1 | IterationStage:144 `stage_hyp`; IterationFacts:209 | PASS | Finite divisor on Kν₊₁ before applying canonical step; tT(2C₁)≤D/2. |
| `stepP:p11a:il-c1` | IterationFacts:38,209; IterationStep:101 | PASS | Positive strip and exact stage domain identity. |
| `stepP:p11a:il-c3` | IterationFacts:81,91 | PASS | Qactual≤varpi/2 gives actual P11Step flow inequality. |
| `stepP:p11a:il-rem` | IterationFacts:126; IterationStep:310 | PASS | Exact canonical remainder bound is ≤ε at next stage; scalar proof pays 1/8+1/4+1/2. |
| `stepP:p11a:il-inc` / O2 | IterationIncrement:31,69; IterationStep:70 | PASS | Divisor-free cutoff on Bν, not merely retained collar. |
| `stepP:p11a:il-dom` | IterationAux:104 `selection_frequency_derivative_le` | PASS | Old increments differentiated at half collar; finite derivative sum ≤C₁. |
| `stepP:p11a:il-map` / O3 | IterationStep:130 `iterPost_step` | PASS | Canonical map clauses transferred with actual domains and budgets. |
| O4 / E4 | Iteration:90,117; IterationParam:26 | PASS | Signed separate block and first-derivative helpers, including zero order. |
| O5 | IterationStep:310 `iterPre_step` normal-form block | PASS | Canonical conjugation and preserved composition prefix. |
| `free-radius` / `fr-other`, B10 share | Iteration:77 `inductive_lemma_adapted` | PASS (B10 share) | Adapted iteration proved; does not assert completion of B12/B13 or the entire graph node. |
| N1 collar supplier | IterationParam:59; Iteration:135 | PASS | Whole-collar derivative clause, not restricted to retained real set. |

All nodes assigned to B10 by the design table are established locally or exported as specified. B11/B12 and later composition/limit-family nodes remain outside this audit.

## Definition classification

All new non-theorem declarations are listed; no hidden approximation/fallback replaces the intended object.

| Definition / structure | Classification | Whole-carrier assessment |
|---|---|---|
| `SelectionIteration` | Signed output data record | Literal chain plus all signed analytic/map outputs, never a source export premise. |
| `selectionSchedGen` | Exact schedule constructor | Fixed data constants with free s₀,ε₀; positivity/admissibility supplied separately. |
| `IterCtx` | Unused implementation proposition | Budget context plus γ equality; no theorem assumes it; harmless unused scaffolding. |
| `StepFacts` | Derived scalar premise bundle | P11Step scalar hypotheses only; proved by stepFacts_of_ctx, no analytic hard step hidden. |
| `stageStep` | Exact P11Step constructor | E=retained set; stage t,r,s,T,d,δ,σ,q,D,L,eps assigned literally. |
| `IterPre` | Internal prefix proposition | Current chain/remainder/normal form and energy reality; every field constructed. |
| `IterPost` | Internal step proposition | All step outputs, including N1, assembled into final record. |
| `IterPrefix` | Exact bounded-index conjunction | Pre for j≤ν, post for j<ν. |
| `ChainAgree` | Exact prefix equality proposition | K/R for j≤ν and Δω/Δh/X for j<ν; sufficient and used in transfer. |
| `selectionBaseChain` | Total base witness | Genuine K, zero increments, identity maps and initial remainder. Values at later indices are initialization, used only at prefix zero before successor updates. |
| `stageS` | Abbreviation | Direct stageStep at selectionRetained; no altered domain. |
| `stepChain` | Total functional update | Updates new slots and retains every other old value, including arbitrary future tail. No result relies on arbitrary tail values. |

## Every explicit declaration

Names below are relative to `KAM.Planetary`; file links include exact declaration locations. Structure-generated projections inherit their audited fields. “Implementation” means a distinctly named conditional helper, not a replacement for a source theorem.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| inductive-lemma / O4 / N1 | [`iterPrefix_step`](../../../../KAM/Planetary/WeakKAM/Iteration.lean:35) | PASS | Exact signed export or proved raw-data construction; supplier uses full collar. |
| inductive-lemma / O4 / N1 | [`selectionIteration_gen`](../../../../KAM/Planetary/WeakKAM/Iteration.lean:57) | PASS | Exact signed export or proved raw-data construction; supplier uses full collar. |
| inductive-lemma / O4 / N1 | [`inductive_lemma`](../../../../KAM/Planetary/WeakKAM/Iteration.lean:71) | PASS | Exact signed export or proved raw-data construction; supplier uses full collar. |
| inductive-lemma / O4 / N1 | [`inductive_lemma_adapted`](../../../../KAM/Planetary/WeakKAM/Iteration.lean:77) | PASS | Exact signed export or proved raw-data construction; supplier uses full collar. |
| inductive-lemma / O4 / N1 | [`selection_iteration_parameter_blocks`](../../../../KAM/Planetary/WeakKAM/Iteration.lean:90) | PASS | Exact signed export or proved raw-data construction; supplier uses full collar. |
| inductive-lemma / O4 / N1 | [`selection_iteration_parameter_first`](../../../../KAM/Planetary/WeakKAM/Iteration.lean:117) | PASS | Exact signed export or proved raw-data construction; supplier uses full collar. |
| inductive-lemma / O4 / N1 | [`selection_real_angle_derivative_on_collar`](../../../../KAM/Planetary/WeakKAM/Iteration.lean:135) | PASS | Exact signed export or proved raw-data construction; supplier uses full collar. |
| coherent assembly | [`ChainAgree.refl`](../../../../KAM/Planetary/WeakKAM/IterationAssemble.lean:26) | PASS | Equality-preserving recursion/assembly on one predecessor sequence. |
| coherent assembly | [`ChainAgree.trans`](../../../../KAM/Planetary/WeakKAM/IterationAssemble.lean:29) | PASS | Equality-preserving recursion/assembly on one predecessor sequence. |
| coherent assembly | [`selectionIteration_of_step`](../../../../KAM/Planetary/WeakKAM/IterationAssemble.lean:35) | PASS | Equality-preserving recursion/assembly on one predecessor sequence. |
| il-dom / frequency reality | [`selectionReal_eq_realInclusion`](../../../../KAM/Planetary/WeakKAM/IterationAux.lean:25) | PASS | Differentiation/reality on actual collars; finite Cauchy sum. |
| il-dom / frequency reality | [`selection_gradient_real`](../../../../KAM/Planetary/WeakKAM/IterationAux.lean:31) | PASS | Differentiation/reality on actual collars; finite Cauchy sum. |
| il-dom / frequency reality | [`selection_collar_sub_V`](../../../../KAM/Planetary/WeakKAM/IterationAux.lean:63) | PASS | Differentiation/reality on actual collars; finite Cauchy sum. |
| il-dom / frequency reality | [`selection_collar_mono_stage`](../../../../KAM/Planetary/WeakKAM/IterationAux.lean:78) | PASS | Differentiation/reality on actual collars; finite Cauchy sum. |
| il-dom / frequency reality | [`selection_frequency_differentiableOn`](../../../../KAM/Planetary/WeakKAM/IterationAux.lean:82) | PASS | Differentiation/reality on actual collars; finite Cauchy sum. |
| il-dom / frequency reality | [`selection_frequency_real`](../../../../KAM/Planetary/WeakKAM/IterationAux.lean:91) | PASS | Differentiation/reality on actual collars; finite Cauchy sum. |
| il-dom / frequency reality | [`selection_frequency_derivative_le`](../../../../KAM/Planetary/WeakKAM/IterationAux.lean:104) | PASS | Differentiation/reality on actual collars; finite Cauchy sum. |
| il-p0 | [`selectionBaseChain`](../../../../KAM/Planetary/WeakKAM/IterationBase.lean:26) | PASS | Definition classified above; Literal base data and initial analytic estimates. |
| il-p0 | [`selectionr_zero`](../../../../KAM/Planetary/WeakKAM/IterationBase.lean:33) | PASS | Literal base data and initial analytic estimates. |
| il-p0 | [`selections_zero`](../../../../KAM/Planetary/WeakKAM/IterationBase.lean:36) | PASS | Literal base data and initial analytic estimates. |
| il-p0 | [`selectiont_zero`](../../../../KAM/Planetary/WeakKAM/IterationBase.lean:39) | PASS | Literal base data and initial analytic estimates. |
| il-p0 | [`selectionε_zero`](../../../../KAM/Planetary/WeakKAM/IterationBase.lean:42) | PASS | Literal base data and initial analytic estimates. |
| il-p0 | [`iterPre_base`](../../../../KAM/Planetary/WeakKAM/IterationBase.lean:45) | PASS | Literal base data and initial analytic estimates. |
| literal P11A bridge | [`selectionDomain_eq_domain_def`](../../../../KAM/Planetary/WeakKAM/IterationBridge.lean:25) | PASS | Exact equality on stated full carrier, including x=0 for coth identity. |
| literal P11A bridge | [`coth_eq_exp`](../../../../KAM/Planetary/WeakKAM/IterationBridge.lean:31) | PASS | Exact equality on stated full carrier, including x=0 for coth identity. |
| literal P11A bridge | [`selectionΛ_eq_p11Lambda`](../../../../KAM/Planetary/WeakKAM/IterationBridge.lean:52) | PASS | Exact equality on stated full carrier, including x=0 for coth identity. |
| il-c1/c2/c3/rem scalar facts | [`selectionSchedGen`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:26) | PASS | Definition classified above; Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`IterCtx`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:30) | PASS | Definition classified above; Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`iter_strip`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:38) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`iter_r_pos`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:47) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`iter_s_succ`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:53) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`iter_eps_succ`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:59) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`iter_t_anti`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:64) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`iter_E_nonneg`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:71) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`iter_varpi_pos`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:74) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`iter_q_le`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:77) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`iter_Qactual_le`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:81) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`iter_flow_small`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:91) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`iter_rem_le`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:126) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`StepFacts`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:153) | PASS | Definition classified above; Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`stageStep`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:174) | PASS | Definition classified above; Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`stepFacts_of_ctx`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:209) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`iter_tail`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:230) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`iter_t_half`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:238) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`iter_sum_le`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:243) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`iter_rr`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:250) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`iter_E_le_one`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:256) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-c1/c2/c3/rem scalar facts | [`iter_E_nonneg'`](../../../../KAM/Planetary/WeakKAM/IterationFacts.lean:261) | PASS | Derived from admissibility and B03/B13 estimates; no new source premise. |
| il-inc / whole-collar coefficients | [`p11Error_nonneg`](../../../../KAM/Planetary/WeakKAM/IterationIncrement.lean:26) | PASS | Actual zero coefficients of cutoff; no divisor premise. |
| il-inc / whole-collar coefficients | [`cutoff_delta`](../../../../KAM/Planetary/WeakKAM/IterationIncrement.lean:31) | PASS | Actual zero coefficients of cutoff; no divisor premise. |
| il-inc / whole-collar coefficients | [`cutoff_R1_eq`](../../../../KAM/Planetary/WeakKAM/IterationIncrement.lean:55) | PASS | Actual zero coefficients of cutoff; no divisor premise. |
| il-inc / whole-collar coefficients | [`cutoff_delta_real`](../../../../KAM/Planetary/WeakKAM/IterationIncrement.lean:69) | PASS | Actual zero coefficients of cutoff; no divisor premise. |
| O4 / N1 | [`param_cauchy_gen`](../../../../KAM/Planetary/WeakKAM/IterationParam.lean:26) | PASS | Positive-order Cauchy plus j=0 branch, or full-collar real-flow proof. |
| O4 / N1 | [`step_real_lipschitz_collar`](../../../../KAM/Planetary/WeakKAM/IterationParam.lean:59) | PASS | Positive-order Cauchy plus j=0 branch, or full-collar real-flow proof. |
| coherent-prefix implementation | [`IterPre`](../../../../KAM/Planetary/WeakKAM/IterationPred.lean:27) | PASS | Definition classified above; Conditional equality/transfer fact; proves preservation of every read slot. |
| coherent-prefix implementation | [`IterPost`](../../../../KAM/Planetary/WeakKAM/IterationPred.lean:53) | PASS | Definition classified above; Conditional equality/transfer fact; proves preservation of every read slot. |
| coherent-prefix implementation | [`IterPrefix`](../../../../KAM/Planetary/WeakKAM/IterationPred.lean:110) | PASS | Definition classified above; Conditional equality/transfer fact; proves preservation of every read slot. |
| coherent-prefix implementation | [`selectionCollar_mono`](../../../../KAM/Planetary/WeakKAM/IterationPred.lean:114) | PASS | Conditional equality/transfer fact; proves preservation of every read slot. |
| coherent-prefix implementation | [`ChainAgree`](../../../../KAM/Planetary/WeakKAM/IterationPred.lean:120) | PASS | Definition classified above; Conditional equality/transfer fact; proves preservation of every read slot. |
| coherent-prefix implementation | [`ChainAgree.mono`](../../../../KAM/Planetary/WeakKAM/IterationPred.lean:127) | PASS | Conditional equality/transfer fact; proves preservation of every read slot. |
| coherent-prefix implementation | [`selectionFrequency_congr`](../../../../KAM/Planetary/WeakKAM/IterationPred.lean:133) | PASS | Conditional equality/transfer fact; proves preservation of every read slot. |
| coherent-prefix implementation | [`selectionEnergy_congr`](../../../../KAM/Planetary/WeakKAM/IterationPred.lean:139) | PASS | Conditional equality/transfer fact; proves preservation of every read slot. |
| coherent-prefix implementation | [`selectionCompose_congr`](../../../../KAM/Planetary/WeakKAM/IterationPred.lean:145) | PASS | Conditional equality/transfer fact; proves preservation of every read slot. |
| coherent-prefix implementation | [`selectionRetained_congr`](../../../../KAM/Planetary/WeakKAM/IterationPred.lean:153) | PASS | Conditional equality/transfer fact; proves preservation of every read slot. |
| coherent-prefix implementation | [`IterPre.transfer`](../../../../KAM/Planetary/WeakKAM/IterationPred.lean:161) | PASS | Conditional equality/transfer fact; proves preservation of every read slot. |
| coherent-prefix implementation | [`IterPost.transfer`](../../../../KAM/Planetary/WeakKAM/IterationPred.lean:199) | PASS | Conditional equality/transfer fact; proves preservation of every read slot. |
| coherent-prefix implementation | [`IterPrefix.transfer`](../../../../KAM/Planetary/WeakKAM/IterationPred.lean:209) | PASS | Conditional equality/transfer fact; proves preservation of every read slot. |
| signed output record | [`SelectionIteration`](../../../../KAM/Planetary/WeakKAM/IterationRecord.lean:25) | PASS | Definition classified above; Exact signed output fields. |
| il-ret / admissible-radius generalization | [`selection_stage_close_gen`](../../../../KAM/Planetary/WeakKAM/IterationRetained.lean:30) | PASS | Explicit extensions/tests; measure positivity and compactness. |
| il-ret / admissible-radius generalization | [`finite_measure_gen`](../../../../KAM/Planetary/WeakKAM/IterationRetained.lean:76) | PASS | Explicit extensions/tests; measure positivity and compactness. |
| il-ret / admissible-radius generalization | [`selectionRetained_nonempty`](../../../../KAM/Planetary/WeakKAM/IterationRetained.lean:153) | PASS | Explicit extensions/tests; measure positivity and compactness. |
| il-ret / admissible-radius generalization | [`selectionRetained_isCompact`](../../../../KAM/Planetary/WeakKAM/IterationRetained.lean:162) | PASS | Explicit extensions/tests; measure positivity and compactness. |
| il-c2 / exact stage | [`phaseToC_eq_realInclusion₂`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:28) | PASS | Literal delivered domains and finite-stage divisor, no limit argument. |
| il-c2 / exact stage | [`domain_def_mono_B`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:31) | PASS | Literal delivered domains and finite-stage divisor, no limit argument. |
| il-c2 / exact stage | [`p11Admissible_mono`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:34) | PASS | Literal delivered domains and finite-stage divisor, no limit argument. |
| il-c2 / exact stage | [`p11Bound_mono`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:38) | PASS | Literal delivered domains and finite-stage divisor, no limit argument. |
| il-c2 / exact stage | [`p11Real_mono`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:42) | PASS | Literal delivered domains and finite-stage divisor, no limit argument. |
| il-c2 / exact stage | [`selection_cast_single`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:46) | PASS | Literal delivered domains and finite-stage divisor, no limit argument. |
| il-c2 / exact stage | [`iterPre_admissible`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:56) | PASS | Literal delivered domains and finite-stage divisor, no limit argument. |
| il-c2 / exact stage | [`stageS`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:83) | PASS | Definition classified above; Literal delivered domains and finite-stage divisor, no limit argument. |
| il-c2 / exact stage | [`stepChain`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:88) | PASS | Definition classified above; Literal delivered domains and finite-stage divisor, no limit argument. |
| il-c2 / exact stage | [`stepChain_agree`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:104) | PASS | Literal delivered domains and finite-stage divisor, no limit argument. |
| il-c2 / exact stage | [`stepChain_K_succ`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:111) | PASS | Literal delivered domains and finite-stage divisor, no limit argument. |
| il-c2 / exact stage | [`stepChain_K_self`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:114) | PASS | Literal delivered domains and finite-stage divisor, no limit argument. |
| il-c2 / exact stage | [`stepChain_Δω_self`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:116) | PASS | Literal delivered domains and finite-stage divisor, no limit argument. |
| il-c2 / exact stage | [`stepChain_Δh_self`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:119) | PASS | Literal delivered domains and finite-stage divisor, no limit argument. |
| il-c2 / exact stage | [`stepChain_X_self`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:122) | PASS | Literal delivered domains and finite-stage divisor, no limit argument. |
| il-c2 / exact stage | [`stepChain_R_succ`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:127) | PASS | Literal delivered domains and finite-stage divisor, no limit argument. |
| il-c2 / exact stage | [`retained_collar_sub`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:138) | PASS | Literal delivered domains and finite-stage divisor, no limit argument. |
| il-c2 / exact stage | [`stage_hyp`](../../../../KAM/Planetary/WeakKAM/IterationStage.lean:144) | PASS | Literal delivered domains and finite-stage divisor, no limit argument. |
| O2–O5 / successor | [`selectionA_eq_stage`](../../../../KAM/Planetary/WeakKAM/IterationStep.lean:30) | PASS | Canonical-step clauses with exact budget/domain equalities and prefix preservation. |
| O2–O5 / successor | [`selectionKappa_eq_stage`](../../../../KAM/Planetary/WeakKAM/IterationStep.lean:35) | PASS | Canonical-step clauses with exact budget/domain equalities and prefix preservation. |
| O2–O5 / successor | [`selectionAlpha_eq_stage`](../../../../KAM/Planetary/WeakKAM/IterationStep.lean:40) | PASS | Canonical-step clauses with exact budget/domain equalities and prefix preservation. |
| O2–O5 / successor | [`selectionMapBudget_eq_stage`](../../../../KAM/Planetary/WeakKAM/IterationStep.lean:47) | PASS | Canonical-step clauses with exact budget/domain equalities and prefix preservation. |
| O2–O5 / successor | [`selectionRealBudget_eq_stage`](../../../../KAM/Planetary/WeakKAM/IterationStep.lean:54) | PASS | Canonical-step clauses with exact budget/domain equalities and prefix preservation. |
| O2–O5 / successor | [`stage_delta`](../../../../KAM/Planetary/WeakKAM/IterationStep.lean:70) | PASS | Canonical-step clauses with exact budget/domain equalities and prefix preservation. |
| O2–O5 / successor | [`stage_domain_eq`](../../../../KAM/Planetary/WeakKAM/IterationStep.lean:100) | PASS | Canonical-step clauses with exact budget/domain equalities and prefix preservation. |
| O2–O5 / successor | [`stage_domain_eq'`](../../../../KAM/Planetary/WeakKAM/IterationStep.lean:112) | PASS | Canonical-step clauses with exact budget/domain equalities and prefix preservation. |
| O2–O5 / successor | [`iterPost_step`](../../../../KAM/Planetary/WeakKAM/IterationStep.lean:124) | PASS | Canonical-step clauses with exact budget/domain equalities and prefix preservation. |
| O2–O5 / successor | [`stepChain_energy_succ`](../../../../KAM/Planetary/WeakKAM/IterationStep.lean:277) | PASS | Canonical-step clauses with exact budget/domain equalities and prefix preservation. |
| O2–O5 / successor | [`stepChain_frequency_succ`](../../../../KAM/Planetary/WeakKAM/IterationStep.lean:286) | PASS | Canonical-step clauses with exact budget/domain equalities and prefix preservation. |
| O2–O5 / successor | [`iterPre_step`](../../../../KAM/Planetary/WeakKAM/IterationStep.lean:297) | PASS | Canonical-step clauses with exact budget/domain equalities and prefix preservation. |

## Checks and exact receipts

All audit Lean invocations were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5` (the compile-gate script supplies nice for the build). No heartbeat/recursion override or clean/update/cache command was used.

1. Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b10 KAM.Planetary.WeakKAM.Iteration
```

Exit 0. Output included `[inp-gate] slot 2 acquired 22:43:27 for KAM.Planetary.WeakKAM.Iteration` and `Build completed successfully (9197 jobs).` Existing upstream warnings were replayed. B10's IterationParam:28 reports unused `htp`; no elaboration error.

2. Fresh signature applications and axioms:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B10Audit.lean
```

Exit 0. Four probe theorem headers were copied from the live signature file and their bodies were exactly the corresponding export applied to all explicit binders in order. Textual header comparisons returned True for all four; SelectionIteration comparison returned True after comments/whitespace removal. No draft signature proof or sorry was imported. The same probe printed axioms of **all 90 new explicit public theorems**, not only main exports. Exact output:

```text
'KAM.Planetary.iterPrefix_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionIteration_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.inductive_lemma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.inductive_lemma_adapted' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_iteration_parameter_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_iteration_parameter_first' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_real_angle_derivative_on_collar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ChainAgree.refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ChainAgree.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionIteration_of_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionReal_eq_realInclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_gradient_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_collar_sub_V' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_collar_mono_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_frequency_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_frequency_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_frequency_derivative_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionr_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selections_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectiont_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionε_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iterPre_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionDomain_eq_domain_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.coth_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionΛ_eq_p11Lambda' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iter_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iter_r_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iter_s_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iter_eps_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iter_t_anti' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iter_E_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iter_varpi_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iter_q_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iter_Qactual_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iter_flow_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iter_rem_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stepFacts_of_ctx' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iter_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iter_t_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iter_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iter_rr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iter_E_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iter_E_nonneg'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Error_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.cutoff_delta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.cutoff_R1_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.cutoff_delta_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.param_cauchy_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.step_real_lipschitz_collar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionCollar_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ChainAgree.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionFrequency_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionEnergy_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionCompose_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionRetained_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.IterPre.transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.IterPost.transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.IterPrefix.transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_stage_close_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.finite_measure_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionRetained_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionRetained_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.phaseToC_eq_realInclusion₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.domain_def_mono_B' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Admissible_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Bound_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Real_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_cast_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iterPre_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stepChain_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stepChain_K_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stepChain_K_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stepChain_Δω_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stepChain_Δh_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stepChain_X_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stepChain_R_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.retained_collar_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stage_hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionA_eq_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionKappa_eq_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionAlpha_eq_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionMapBudget_eq_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionRealBudget_eq_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stage_delta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stage_domain_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stage_domain_eq'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iterPost_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stepChain_energy_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stepChain_frequency_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iterPre_step' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.Iteration KAM.Planetary.WeakKAM.IterationAssemble KAM.Planetary.WeakKAM.IterationAux KAM.Planetary.WeakKAM.IterationBase KAM.Planetary.WeakKAM.IterationBridge KAM.Planetary.WeakKAM.IterationFacts KAM.Planetary.WeakKAM.IterationIncrement KAM.Planetary.WeakKAM.IterationParam KAM.Planetary.WeakKAM.IterationPred KAM.Planetary.WeakKAM.IterationRecord KAM.Planetary.WeakKAM.IterationRetained KAM.Planetary.WeakKAM.IterationStage KAM.Planetary.WeakKAM.IterationStep
```

Exit 0. All 13 modules replayed in this single invocation (imports supplied as the starting environment; no `--fresh` claim). Exact output:

```text
replaying KAM.Planetary.WeakKAM.IterationStep
replaying KAM.Planetary.WeakKAM.IterationStage
replaying KAM.Planetary.WeakKAM.IterationRetained
replaying KAM.Planetary.WeakKAM.IterationRecord
replaying KAM.Planetary.WeakKAM.IterationPred
replaying KAM.Planetary.WeakKAM.IterationParam
replaying KAM.Planetary.WeakKAM.IterationIncrement
replaying KAM.Planetary.WeakKAM.IterationFacts
replaying KAM.Planetary.WeakKAM.IterationBridge
replaying KAM.Planetary.WeakKAM.IterationBase
replaying KAM.Planetary.WeakKAM.IterationAux
replaying KAM.Planetary.WeakKAM.IterationAssemble
replaying KAM.Planetary.WeakKAM.Iteration
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the explicitly allowed stale-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (995 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No forbidden-token, line-length, file-size, errata-render, module-system, frozen-integrity or ABI failure. `KAM.lean` was left untouched as required. This expected exception and the disclosed admissible-radius proof duplication account for PASS WITH NOTES; there is no blocking B10 finding.

5. Static integrity:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit 0 with no diff/check output, aside from the stated multiple-merge-base warning. Direct inventory: 13 modules, 2154 physical lines total, maximum 419 in IterationStep; all lines ≤100 characters. No forbidden token, resource option or EuclideanSpace in the audit slice. All 13 have copyright, module command, public imports, module docstring and exposed public section. The handoff's 2153 total/418 maximum is off by one physical line, with no substantive effect.

Recursive KAM import inspection finds 14 frozen **definitions**, all manifest state SEALED; zero frozen theorem imports and zero provider imports. Hence no DRAFT_SORRY dependency. Exact frozen definitions: actionNbhd, complexStrip, frequencyMap, hamiltonianVectorField, hamiltonianVectorFieldℂ, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, omegaZero, realHamiltonian, symplecticForm, Planetary.Phase, circularPoint and circularTube.

Namespace inventory found no duplicate unqualified public helper declaration introduced by B10 and no root namespace declaration/shadow. Conventional qualified methods `ChainAgree.refl`, `ChainAgree.mono`, and `IterPre/IterPost/IterPrefix.transfer` share terminal method words with unrelated namespaces; these are method names under distinct owning structures, not competing unqualified helpers. This is a minor clarification to the handoff's collision description.

## Notes, uncertainties, errata and deviations

- No suspected new defect in the pinned-source statements used by B10, nor contradiction of its blueprint, was found. This audit used the pinned blueprint transcription and delivered dependencies; it does not independently re-audit all of Rus01 or P11A/B09 proof packages.
- Existing blueprint reality-guard issue GAP-2 (design:213, upstream p11a2 L248/L287) is explicitly handled by the delivered canonical_step_real reality premise; B10 supplies it and proves propagation. No claim is made that historical source wording was repaired here.
- The admissible-radius repetition of B09's finite measure argument is a disclosed implementation deviation: `finite_measure_gen` accepts explicit s₀,ε₀ and SelectionAdmissibility and produces the full finite test witness. It is used at both signed schedules, without editing or weakening B09. Its name distinguishes it from the graph export `finite_measure`.
- Internal prefix records and the abstract extension hypothesis are conditional implementation devices, all discharged before the raw-data signed exports. No conclusion-shaped hypothesis is added to those exports.
- O1 recovery, cumulative energy reality/holomorphy, and local O5 construction were checked despite being implicit rather than separately named fields in the signed record. No inspected B10 consumer need is lost by the signed packaging. Later source/graph/headline closure remains separate.
- No source, frozen, manifest, generated root or README edits; no git mutation. Only this report and temporary `.lake/abi-scratch/` probes/logs were written. All audit-created scratch files were removed after transferring their receipts into this report.
