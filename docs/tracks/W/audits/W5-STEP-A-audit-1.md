# W5-STEP-A independent audit 1

Date: 2026-11-01. **Overall: FAIL for complete closure of the stated AUDIT FOCUS; the existing infrastructure declarations pass their stated, narrower contracts.** The two closure findings below are missing exports, not counterexamples to the mathematical claims or evidence of an unsound Lean proof. No frozen theorem is sealed by this package, so no anchor is certified seal-ready.

## Revision and scope

Audited `git diff inp...HEAD` with HEAD `2a3fc7d7ffc90bf7163b383ef74d9ff3243bc4fe` and inp `d2802dae2400f4fe1ba9c03263ad59d9ada87cf9`. The run-A handoff refers to producer code `ada9a34f`; HEAD adds the run-A scope document. The 52 modules enumerated in that document are the complete code-review scope. The file inventory below pins their SHA-256 hashes. The worktree was clean before the audit.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief, both W5-STEP handoffs, the relevant frozen definitions and the controlling `blueprint-W/parts/w5-kamstep.tex`. Applied the run-A focus in place of the generic anchor/provider focus. No provider/frozen-type or seal-body test applies: there is no run-A provider or proposed seal.

Run-B source files were inspected only to trace consumption of run-A exports and to establish whether a missing run-A conclusion was supplied at that boundary. This report does not audit NewHam*, StepCore/StepHyp/StepHypMod/StepTheorem*, StepPlus*, StepConj, Step*Clauses, Homological/Modified*, or ModifiedStepSolve. In particular it gives no verdict on the run-B step theorem, modified solve, or reality package.

## Findings

### F1 — joint continuity in flow-calc (i) is not exported (FAIL for this clause)

Blueprint `bpW:w5:flow-calc` (i), `blueprint-W/parts/w5-kamstep.tex:431`, requires “$(t,w)\mapsto\phi^t(w)$ and $(t,w)\mapsto D\phi^t(w)$ are continuous on $[-1,1]\times U$”. The corresponding continuity step is `stepW:w5:c-cont`.

`KAM/Wave/KamStep/FlowVariational.lean:112` exports only

```lean
continuousOn_fderiv_holoFlow_time ... {w : F} (hw : w ∈ U) :
  ContinuousOn (fun t => fderiv ℂ (holoFlow X t) w) (Icc (-1 : ℝ) 1)
```

The initial point is fixed outside the continuity conclusion. `fderiv_holoFlow_eq` at line 85 gives the correct variational equation, but not the joint continuity conclusion. The inherited W1 flow APIs and these modules supply time continuity and holomorphy in the initial point; the reviewed export surface does not state the joint result for the flow or its derivative. Separate continuity is not the literal product-domain conclusion. The time-only theorem is correctly named and valid as a helper; it cannot be booked as all of flow-calc (i).

Consumers `FlowSmoothDeriv` and `FlowSymplectic` use the time-only theorem for time integrals, which is appropriate. They do not close the omitted product-domain statement. Required repair: export joint continuity on `Icc (-1) 1 ×ˢ U`, for both maps, from the available local uniform estimates, without a new continuity premise. No proof repair was made by this auditor.

### F2 — smoothing-space onto clause of flow-calc (iii) is not exported (FAIL for this clause)

Blueprint `bpW:w5:flow-calc` (iii), `blueprint-W/parts/w5-kamstep.tex:434`, requires that `Dφᵗ(w)` is invertible on `𝒫ᵖ` **and maps `𝒫^{p₊}` onto `𝒫^{p₊}`**. `KAM/Wave/KamStep/FlowInverse.lean:44` proves `IsUnit (fderiv ℂ (holoFlow X t) w)` in the ambient operator algebra only. Its statement has no smoothing target, embedding, or range equality. Ambient invertibility alone does not establish invertibility on the stronger weighted space.

`FlowSmoothDeriv.lean:105` correctly gives `Dφ = I + ι ∘ DΨ`. This supplies invariance in one direction when composed with `ι`; the onto statement additionally needs invertibility of `I + DΨ ∘ ι` on the target and the identification with the ambient inverse. The run-B consumer `NewHamTransport` uses the target equation `y + transNop … y = u` and `transSolve_spec` when the target operator norm is below one; that use is compatible with the run-A estimates. It is not an exported onto theorem in the audited modules. The consumer's `StepTheorem.lean:32-34` explicitly records `DΦ(w)(𝒫^{p₊}) = 𝒫^{p₊}` as not included. This is boundary evidence only, not a run-B audit finding.

Required repair: a source-facing theorem on the small domain showing that the derivative's image of `Set.range ι` equals `Set.range ι` (or an equivalent target inverse theorem with both inverse identities), instantiated with `stepEmbedCLM`. Retain the actual target representative; do not identify the two weighted spaces merely because their representative types coincide.

## Node verdicts and source comparison

PASS below means the specified supplier statement passes; it does not turn an abstract pointwise identity into an entire blueprint node. N/A marks assembly or reality conclusions deliberately assigned outside this run.

| Node / clause | Lean exports | Verdict | Reason / precise boundary |
|---|---|---|---|
| notation, setting | `StepPhase`, `stepDomain`, `stepToHom`, `stepZ`, `stepZb`, `kamHomEmbed`, `stepEmbedCLM` | PASS WITH NOTES | Weighted representatives in `HomL2`; label `j+2`; explicit weight-changing embedding. `StepPhase r` has the sum norm, not the default product max norm. |
| omega, ombd/omnd | `norm_stepSymp_le`, `stepSymp_antisymm`, `stepSymp_nondeg`, `stepSympCLM`, `stepSymp_embed` | PASS | `(4π+1)r²` is stronger than blueprint `(4π+2)r²`; tests against coordinate vectors establish nondegeneracy. Cross-weight pairing and embedding identities preserve the physical form. |
| omega, omnorm | `kamNorm_le_ratio_sq`, `stepNu_mono`, `kamNorm_kamHomEmbed_le` | PASS | Radius loss and weight monotonicity are expressed through representative maps; no unweighted identity substitution. |
| class, lambda-product | `IsSmoothing`, `isSmoothing_unique_apply`, `FamBound`, `FamBound.famMono`, `lamProd_bound` | PASS WITH NOTES | Source class data, field uniqueness, and existential nonnegative sup/Lipschitz majorants. Open domains and λ≥0 are supplied at analytic consumers; the raw predicates themselves do not enforce these guards. |
| data | `stepC1`, `stepExpT`, `stepCF`, `stepC0`, `stepC2`, `stepMF`, `stepMF_le_of_small`, `stepMF_margins`, `stepSolve_bound`, `stepEstimate_arith` | PASS | Correct constants and dependence: no dependence on m added; `M≤ση²/16` gives the sharper `M≤σ/1024`. Arithmetic lemmas are arithmetic, not analytic step closure. |
| B♮, m-const | `waveBN`, `waveBNconst`, `waveBN_summable`, `waveBW_le_waveBN`, `waveBN_le` | PASS | Squared `(1+modeSize)` factor, exponent `2τ+4`, four terms counted with multiplicity, including τ=0. Modified solver itself excluded. |
| freq | `stepFreqHyp`, `rpow_half_le_add_two_rpow`, `stepDivisors` | PASS | Retains `j^(1/2)` tails, `(j+2)^(pb-p)` correction weight and exact correction constants. `λ>0` is the proper guard for the `ε/λ` helper. Finite cutoff divisor conclusion is not global Melnikov. |
| taylor (i), t-poly/t-comp | `stepTaylorOf`, `tA0`…`tQt`, `stepFun_taylorOf_eq`, `taylorRv_eq` | PASS | Constructs the Taylor element from source smoothing/periodicity/bound data. Symmetry/transposition is derived from the Hessian, not assumed of the constructed blocks. Function identity identifies the weighted polynomial. |
| taylor (ii), t-scale/t-field | `stepSymp_scale`, `hasDerivAt_taylorSum_param`, `hasDerivAt_taylorRv`, `sum_taylorCoeff_symp`, `stepField_taylorOf_eq` | PASS | Correct `S_t=(θ,t²y,tu,tv)`, `T_t=(t²Θ,Y,tU,tV)`; coefficient/parameter interchange is proved on a finite-dimensional slice, then field equality by nondegeneracy. |
| Taylor estimates supporting identification | `norm_taylorCoeff_le`, `norm_taylor_remainder_le`, `taylorXR_bound`, `taylorXR_remainder_128`, `stepTaylor_fieldBound`, `stepTaylor_subFieldBound`, `taylorXR_sub` | PASS | Constants 3 and 128, open-disc limits, no θ strip loss. Differences retain linearity and the W4 field-bound interface. |
| taylor / normal-form reality infrastructure | `StepReal`, `fderiv_im_of_real`, `stepSymp_dfield_im`, `tB_real`, `tQ_entry_real`, `homCoeff_b_real`, `homCoeff_Q_real` | PASS, limited | Proves exactly reality of indicated derivatives, diagonal coefficients and averages. Full reality package and concrete flow reality are assigned to run B; no such closure is claimed here. |
| solve, s-in/s-out/s-class (non-modified) | `stepFun_field`, `stepField_differentiableAt`, `stepFun_isSmoothing`, `stepSolve_fam`, `stepSolve_equation`, `stepNhat_fam`, `stepNfun_lie` | PASS WITH NOTES | Solution is W4's actual solve, specified by equality `hF`; this is not an arbitrary solution assumed to satisfy the desired equation. Field/λ bounds and equation are proved. `HomGuard` and `1≤p+pb` hold at a=p=1. Frequency-output assembly and full reality are outside this run. |
| flow (i),(ii), f-margin/f-flow/f-par/f-der | `stepFlowHyp`, `stepFlowHyp_concrete'`, `holoFlow_smooth_eq`, `differentiableOn_smoothDisp`, `flowII_disp`, `flowII_disp_sub`, `flowII_deriv`, `flowII_deriv_sub` | PASS, supplier scope | Explicit source margin, target-valued displacement Ψ, parameter estimates `M,2N` and derivative estimates `M/ρ,2N/ρ`; concrete ρ=σ/8 is instantiated by consumers. `stepFlowHyp_concrete'` accepts the solved strip `s-σ`; avoids a second unwanted strip loss. |
| flow (iii), f-image | `stepImage_mem` | PASS | `σ≤1` follows from step data; correct radius and strip image. |
| flow (iv), f-real | `holoFlow_translate` | PASS, abstract equivariance | Translation invariance is an explicit hypothesis of this correctly named abstract helper. Concrete integer equivariance is assembled downstream. Concrete reality is outside this run. |
| flow-calc (i), c-var | `fderiv_holoFlow_eq`, `continuousOn_fderiv_holoFlow_time` | FAIL for full clause | Variational equation passes; joint continuity export missing (F1). |
| flow-calc (ii), c-skew/c-symp | `skew_of_hamiltonian`, `stepSymp_const`, `holoFlow_preserves_form` | PASS, abstract calculus | Skewness follows from symmetry of the second derivative; concrete supplier uses `stepSymp_embed`. Skewness in the abstract flow theorem is an honest analytic input, not an assumed symplectic conclusion. |
| flow-calc (iii), c-inv | `norm_fderiv_holoFlow_sub_id_le`, `isUnit_fderiv_holoFlow` | FAIL for full clause | Ambient Neumann inverse passes; stronger-space onto export missing (F2). |
| flow-calc (iv), c-trans | `hasFDerivAt_comp_hamiltonian` | PASS, pointwise supplier | Assumes `A Y = XG(φ w)` and proves the chain-rule pairing. It does not claim to construct Y or prove its target holomorphy. Run-B transport consumers construct Y via a target inverse rather than assuming the desired Hamiltonian conclusion. |
| flow-calc (v), c-time | `hasDerivWithinAt_comp_holoFlow`, `stepNfun_hasFDerivAt`, `stepNfun_lie` | PASS | Time derivative, actual normal form, Lie sign `DN·ιX_F = -L_NF`; no assumption that unbounded X_N is a p-weight vector. |
| pullback, p-inv/p-ass | `seminorm_solve_le`, `seminorm_solve_sub_le`, `stepNu_transNop_le`, `stepNu_transNop_sub_le`, `stepPullback_sup`, `stepPullback_sub`, `stepInv_sub`, `stepPullback_diff`, `stepPullback_const` | PASS, supplier scope | Correct inverse-free estimates on target representatives. Equations for the transported y are premises of explicitly conditional algebraic helpers; consumers discharge them using `transSolve_spec`. Constant arithmetic gives 7; full field assembly is run B. |
| commutator, k-bd | `hasFDerivAt_bracket`, `stepCommutator_arith` | PASS, supplier scope | Correct sign `DX_G X_F - DX_F X_G`; `24 ε M/(ση²)` arithmetic. Full Cauchy/parameter commutator assembly lives in excluded consumers, so no whole-node closure is certified by this arithmetic theorem. |
| analytic/integral infrastructure | `differentiableOn_fderiv_of_holomorphic`, `hasFDerivAt_fderiv_of_holomorphic`, `smoothing_integral`, `stepTriangle_on` | PASS | Operator-valued holomorphy is proved from local bounds and a quadratic remainder; integrals use uniform Riemann-sum limits with explicit time-Lipschitz hypotheses, not an assumed derivative of the integral. Triangle identity includes the interval-only version. |

## Definition classification

All new named definitions/abbreviations/structures are listed below by name. The classes mean:

* **Object**: intended polynomial, coordinate, pairing, norm, constant, or algebraic map on the stated carrier.
* **Predicate**: source data packaged as a proposition; not a theorem about arbitrary input.
* **Guarded analytic operation**: total Lean derivative/integral/series operation, identified with the analytic object only under the hypotheses of its theorem.

There is no new axiom, arbitrary fallback used inside the admissible domain, or conclusion hidden as a typeclass. In particular: `stepWinv` uses strictly positive `homWt`; `waveBN` is a total tsum and its estimate requires σ>0 and summability (not its default zero for divergent series); `riemannSum` is zero at n=0, but the quantitative lemma requires n>0 and convergence is eventually positive. `taylorCoeff`, `holoD2`, derivative-defined blocks and `stepField` may have totalized derivative values off their analytic domains; all identification and bound consumers stay in the specified open strip/domain. No equality of Taylor structures outside their strips is inferred. `smoothDisp` and `stepNfun` use integrals/pairings with integrability or convergence proved at the points used. `integral_clm_eq_zero` explicitly handles an undefined integral by zero; that identity is harmless and is not used to claim an analytic representation without integrability.

`StepPhase r` carries a normed/complete instance only with `Fact (0<r)`. `stepDomain ρ s r'` keeps carrier scale ρ separate from the domain radius r'. `IsSmoothing` does not itself assert openness; it is used on open `kamDomain` or with a separately supplied `IsOpen`. `FamBound` is a λ-norm encoding only with λ≥0. These are documented domain guards, not widened source claims.

| Definition / source | Classification | Reason |
| `KAM.Wave.IsSmoothing` (KAM/Wave/KamStep/Class.lean:33) | Predicate | Holomorphy plus Hamiltonian derivative identity; field uniqueness proved. |
| `KAM.Wave.FamBound` (KAM/Wave/KamStep/Class.lean:51) | Predicate | Nonnegative sup/Lipschitz witnesses and their weighted sum. |
| `KAM.Wave.stepC1` (KAM/Wave/KamStep/Data.lean:33) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepExpT` (KAM/Wave/KamStep/Data.lean:36) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepCF` (KAM/Wave/KamStep/Data.lean:39) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepC0` (KAM/Wave/KamStep/Data.lean:42) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepC2` (KAM/Wave/KamStep/Data.lean:45) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepTn` (KAM/Wave/KamStep/Data.lean:48) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepCFn` (KAM/Wave/KamStep/Data.lean:51) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepC0n` (KAM/Wave/KamStep/Data.lean:54) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepC2n` (KAM/Wave/KamStep/Data.lean:57) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepMF` (KAM/Wave/KamStep/Data.lean:60) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.StepPhase.toKHom` (KAM/Wave/KamStep/Flow.lean:30) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepDomain` (KAM/Wave/KamStep/Flow.lean:42) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.smoothField` (KAM/Wave/KamStep/FlowSmooth.lean:38) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.smoothDisp` (KAM/Wave/KamStep/FlowSmooth.lean:41) | Guarded analytic operation | Total analytic operation; identification only on its proved analytic domain. |
| `KAM.Wave.flowVarG` (KAM/Wave/KamStep/FlowVariational.lean:38) | Guarded analytic operation | Total analytic operation; identification only on its proved analytic domain. |
| `KAM.Wave.slice2L` (KAM/Wave/KamStep/HoloFderiv.lean:44) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.holoD2` (KAM/Wave/KamStep/HoloFderiv.lean:142) | Guarded analytic operation | Total analytic operation; identification only on its proved analytic domain. |
| `KAM.Wave.waveBN` (KAM/Wave/KamStep/LatticeBN.lean:29) | Guarded analytic operation | Total analytic operation; identification only on its proved analytic domain. |
| `KAM.Wave.waveBNconst` (KAM/Wave/KamStep/LatticeBN.lean:34) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepWinv` (KAM/Wave/KamStep/Omega.lean:36) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepPairCLM` (KAM/Wave/KamStep/Omega.lean:48) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepSymp` (KAM/Wave/KamStep/Omega.lean:68) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.riemannSum` (KAM/Wave/KamStep/ParamIntegral.lean:132) | Guarded analytic operation | Total analytic operation; identification only on its proved analytic domain. |
| `KAM.Wave.StepPhase` (KAM/Wave/KamStep/Phase.lean:29) | Object | Representative carrier with separately proved equivalent Banach norm. |
| `KAM.Wave.StepPhase.toK` (KAM/Wave/KamStep/Phase.lean:39) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.StepPhase.ofK` (KAM/Wave/KamStep/Phase.lean:42) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.kamAddGroupNorm` (KAM/Wave/KamStep/Phase.lean:77) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepNu` (KAM/Wave/KamStep/PullbackNu.lean:34) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.StepReal` (KAM/Wave/KamStep/RealCalc.lean:35) | Predicate | Coordinatewise real points. |
| `KAM.Wave.stepSympLin` (KAM/Wave/KamStep/StepCLM.lean:69) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepSympCLM` (KAM/Wave/KamStep/StepCLM.lean:79) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.kamHomEmbed` (KAM/Wave/KamStep/StepCLM.lean:106) | Object | Ratio of Dirichlet weights on normals; identity on angles/actions. |
| `KAM.Wave.stepEmbedCLM` (KAM/Wave/KamStep/StepCLM.lean:126) | Object | Same inclusion in the step norm. |
| `KAM.Wave.stepToHom` (KAM/Wave/KamStep/StepNfun.lean:32) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepNfun` (KAM/Wave/KamStep/StepNfun.lean:45) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepTaylorOf` (KAM/Wave/KamStep/TaylorAssemble.lean:40) | Object | Constructed Taylor coefficients and proved component conditions. |
| `KAM.Wave.stepIotaZ` (KAM/Wave/KamStep/TaylorBlocks.lean:32) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepIotaZb` (KAM/Wave/KamStep/TaylorBlocks.lean:38) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.blockP` (KAM/Wave/KamStep/TaylorBlocks.lean:101) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.blockP'` (KAM/Wave/KamStep/TaylorBlocks.lean:105) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.blockQ` (KAM/Wave/KamStep/TaylorBlocks.lean:109) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.blockQt` (KAM/Wave/KamStep/TaylorBlocks.lean:113) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.taylorRealPt` (KAM/Wave/KamStep/TaylorBoundA0.lean:33) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.e0` (KAM/Wave/KamStep/TaylorCommute.lean:33) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.tcE1` (KAM/Wave/KamStep/TaylorCommute.lean:34) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepW0L` (KAM/Wave/KamStep/TaylorData.lean:34) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.tA0` (KAM/Wave/KamStep/TaylorData.lean:48) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.tB` (KAM/Wave/KamStep/TaylorData.lean:49) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.tCp` (KAM/Wave/KamStep/TaylorData.lean:51) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.tCm` (KAM/Wave/KamStep/TaylorData.lean:52) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.tP` (KAM/Wave/KamStep/TaylorData.lean:53) | Guarded analytic operation | Total analytic operation; identification only on its proved analytic domain. |
| `KAM.Wave.tP'` (KAM/Wave/KamStep/TaylorData.lean:54) | Guarded analytic operation | Total analytic operation; identification only on its proved analytic domain. |
| `KAM.Wave.tQ` (KAM/Wave/KamStep/TaylorData.lean:55) | Guarded analytic operation | Total analytic operation; identification only on its proved analytic domain. |
| `KAM.Wave.tQt` (KAM/Wave/KamStep/TaylorData.lean:56) | Guarded analytic operation | Total analytic operation; identification only on its proved analytic domain. |
| `KAM.Wave.taylorG` (KAM/Wave/KamStep/TaylorEst.lean:32) | Guarded analytic operation | Total analytic operation; identification only on its proved analytic domain. |
| `KAM.Wave.taylorField` (KAM/Wave/KamStep/TaylorEst.lean:36) | Guarded analytic operation | Total analytic operation; identification only on its proved analytic domain. |
| `KAM.Wave.taylorXR` (KAM/Wave/KamStep/TaylorEst.lean:40) | Guarded analytic operation | Total analytic operation; identification only on its proved analytic domain. |
| `KAM.Wave.kamToStep` (KAM/Wave/KamStep/TaylorEst.lean:44) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepField` (KAM/Wave/KamStep/TaylorField.lean:32) | Guarded analytic operation | Total analytic operation; identification only on its proved analytic domain. |
| `KAM.Wave.sympK` (KAM/Wave/KamStep/TaylorFieldRv.lean:35) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepPrY` (KAM/Wave/KamStep/TaylorFunDeriv.lean:40) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepZ` (KAM/Wave/KamStep/TaylorFun.lean:31) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepZb` (KAM/Wave/KamStep/TaylorFun.lean:40) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepPr` (KAM/Wave/KamStep/TaylorFun.lean:61) | Object | Symmetric weight product encodes the cross-weight physical pairing. |
| `KAM.Wave.waveStepFun` (KAM/Wave/KamStep/TaylorFun.lean:66) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepPrTheta` (KAM/Wave/KamStep/TaylorFun.lean:73) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.taylorCoeff` (KAM/Wave/KamStep/TaylorOneVar.lean:32) | Guarded analytic operation | Total analytic operation; identification only on its proved analytic domain. |
| `KAM.Wave.entryImCLM` (KAM/Wave/KamStep/TaylorReal.lean:59) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.coordImCLM` (KAM/Wave/KamStep/TaylorReal.lean:76) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.taylorRv` (KAM/Wave/KamStep/TaylorRv.lean:32) | Guarded analytic operation | Total analytic operation; identification only on its proved analytic domain. |
| `KAM.Wave.scaleS` (KAM/Wave/KamStep/TaylorScale.lean:27) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.scaleT` (KAM/Wave/KamStep/TaylorScale.lean:31) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.stepTau` (KAM/Wave/KamStep/TaylorSmoothing.lean:35) | Object | Formula and intended domain checked; guards as above. |
| `KAM.Wave.zeroTaylor` (KAM/Wave/KamStep/ZeroTaylor.lean:27) | Object | Actual zero polynomial; used outside Π only. |

## Declaration inventory

One row per new named public declaration in the 52 scoped modules. P = PASS for its actual statement; PN = PASS WITH NOTES with the restriction stated in the row. These rows do not override the node-level FAILs F1/F2. Every theorem row was separately included in the fresh `#print axioms` probe (298 results). Anonymous algebraic carrier instances in Phase.lean:31-32 are the inherited `AddCommGroup` and `Module ℂ`, both PASS. Named normed/complete instances are listed below.

| Node / module | Lean declaration (namespace KAM.Wave unless shown) | Verdict | Reason / note |
|---|---|---|---|
| Class:33 | `IsSmoothing` | P | Source class definition, not assumed theorem closure. |
| Class:40 | `isSmoothing_unique_apply` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Class:51 | `FamBound` | P | Source formula / typing data checked. |
| Class:57 | `FamBound.famMono` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Class:65 | `lamProd_bound` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Data:33 | `stepC1` | P | Source formula / typing data checked. |
| Data:36 | `stepExpT` | P | Source formula / typing data checked. |
| Data:39 | `stepCF` | P | Source formula / typing data checked. |
| Data:42 | `stepC0` | P | Source formula / typing data checked. |
| Data:45 | `stepC2` | P | Source formula / typing data checked. |
| Data:48 | `stepTn` | P | Source formula / typing data checked. |
| Data:51 | `stepCFn` | P | Source formula / typing data checked. |
| Data:54 | `stepC0n` | P | Source formula / typing data checked. |
| Data:57 | `stepC2n` | P | Source formula / typing data checked. |
| Data:60 | `stepMF` | P | Source formula / typing data checked. |
| Data:62 | `stepC1_pos` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Data:65 | `waveC_pos` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Data:73 | `waveBWconst_pos` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Data:81 | `waveBNconst_pos` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Data:89 | `stepCF_pos` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Data:92 | `stepCFn_pos` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Data:95 | `stepC0_pos` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Data:98 | `stepC0n_pos` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Data:102 | `stepMF_le_of_small` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Data:118 | `stepMF_margins` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Data:129 | `stepSolve_bound` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Data:144 | `stepSolve_bound_mod` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Data:160 | `stepEstimate_arith` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Divisors:26 | `homPairL_sub_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Divisors:36 | `waveA_le_of_modeSize_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Divisors:47 | `stepDivisors` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Divisors:101 | `rpow_half_le_add_two_rpow` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Divisors:115 | `stepFreqHyp` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowEquivariant:32 | `holoFlow_translate` | PN | Correct conditional/abstract or arithmetic supplier; scope in node table. |
| FlowInverse:34 | `norm_fderiv_holoFlow_sub_id_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowInverse:44 | `isUnit_fderiv_holoFlow` | PN | Ambient inverse only; full node FAIL F2. |
| Flow:30 | `StepPhase.toKHom` | P | Source formula / typing data checked. |
| Flow:35 | `stepPhase_toK_continuous` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Flow:42 | `stepDomain` | P | Source formula / typing data checked. |
| Flow:44 | `stepDomain_isOpen` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Flow:49 | `stepDomain_margin` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Flow:68 | `stepFlowHyp` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Flow:78 | `stepImage_mem` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowSkew:30 | `skew_of_hamiltonian` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowSkew:43 | `hasFDerivAt_bracket` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowSmoothDeriv:39 | `hasFDerivAt_smoothDisp` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowSmoothDeriv:90 | `differentiableOn_smoothDisp` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowSmoothDeriv:97 | `norm_fderiv_smoothDisp_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowSmoothDeriv:105 | `fderiv_holoFlow_smooth` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowSmoothDeriv:125 | `norm_fderiv_smoothDisp_sub_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowSmooth:38 | `smoothField` | P | Source formula / typing data checked. |
| FlowSmooth:41 | `smoothDisp` | P | Source formula / typing data checked. |
| FlowSmooth:48 | `flowHyp_smooth` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowSmooth:66 | `continuousOn_smooth_integrand` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowSmooth:72 | `holoFlow_smooth_eq` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowSmooth:84 | `norm_smoothDisp_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowSmooth:105 | `norm_smoothDisp_sub_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowStepBounds:29 | `one_add_mul_exp_le_two` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowStepBounds:40 | `flowII_disp` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowStepBounds:49 | `flowII_disp_sub` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowStepBounds:70 | `flowII_deriv` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowStepBounds:81 | `flowII_deriv_sub` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowSymplectic:33 | `continuousOn_flowVarG` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowSymplectic:40 | `hasDerivWithinAt_fderiv_holoFlow` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowSymplectic:79 | `holoFlow_preserves_form` | PN | Correct conditional/abstract or arithmetic supplier; scope in node table. |
| FlowTime:30 | `hasDerivWithinAt_comp_holoFlow` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowTransport:26 | `hasFDerivAt_comp_hamiltonian` | PN | Correct conditional/abstract or arithmetic supplier; scope in node table. |
| FlowVariational:38 | `flowVarG` | P | Source formula / typing data checked. |
| FlowVariational:41 | `tendsto_picardD` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowVariational:50 | `tendsto_picardG` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowVariational:62 | `aestronglyMeasurable_flowVarG` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowVariational:69 | `norm_flowVarG_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowVariational:78 | `intervalIntegrable_flowVarG` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowVariational:85 | `fderiv_holoFlow_eq` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| FlowVariational:112 | `continuousOn_fderiv_holoFlow_time` | PN | Fixed-w time continuity only; full node FAIL F1. |
| HoloFderiv:35 | `differentiableAt_slice2` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| HoloFderiv:44 | `slice2L` | P | Source formula / typing data checked. |
| HoloFderiv:48 | `slice2L_apply` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| HoloFderiv:52 | `differentiableAt_fderiv_line` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| HoloFderiv:91 | `exists_hasFDerivAt_fderiv_plane` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| HoloFderiv:142 | `holoD2` | P | Source formula / typing data checked. |
| HoloFderiv:150 | `hasDerivAt_holoD2` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| HoloFderiv:154 | `holoD2_add_right` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| HoloFderiv:163 | `holoD2_smul_right` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| HoloFderiv:171 | `holoD2_plane` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| HoloFderiv:186 | `holoD2_add_left` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| HoloFderiv:196 | `holoD2_smul_left` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| HoloFderiv:213 | `holo_local_bound` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| HoloFderiv:225 | `norm_fderiv_le_local` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| HoloFderiv:241 | `differentiableAt_fderiv_line_at` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| HoloFderiv:258 | `taylorCoeff_one` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| HoloFderiv:261 | `norm_holoD2_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| HoloFderiv:293 | `norm_fderiv_remainder_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| HoloFderiv:353 | `hasFDerivAt_fderiv_of_holomorphic` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| HoloFderiv:411 | `differentiableOn_fderiv_of_holomorphic` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| LatticeBN:29 | `waveBN` | P | Source formula / typing data checked. |
| LatticeBN:34 | `waveBNconst` | P | Source formula / typing data checked. |
| LatticeBN:37 | `waveS_le_waveBNconst` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| LatticeBN:43 | `waveBN_pointwise` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| LatticeBN:75 | `waveBN_summable` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| LatticeBN:86 | `waveBW_le_waveBN` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| LatticeBN:99 | `waveBN_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Omega:36 | `stepWinv` | P | Source formula / typing data checked. |
| Omega:38 | `norm_stepWinv_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Omega:48 | `stepPairCLM` | P | Source formula / typing data checked. |
| Omega:51 | `norm_stepPairCLM_apply_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Omega:60 | `stepPairCLM_comm` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Omega:68 | `stepSymp` | P | Source formula / typing data checked. |
| Omega:72 | `norm_sum_two_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Omega:83 | `stepSymp_arith` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Omega:108 | `norm_stepSymp_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Omega:161 | `stepSymp_antisymm` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Omega:172 | `stepPairCLM_basis` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Omega:178 | `stepWinv_ne_zero` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Omega:184 | `stepSymp_sub_left` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Omega:193 | `stepSymp_nondeg` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| ParamIntegral:33 | `norm_integral_sub_riemann_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| ParamIntegral:132 | `riemannSum` | P | Source formula / typing data checked. |
| ParamIntegral:135 | `tendstoUniformlyOn_riemann` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| ParamIntegral:153 | `riemannSum_add` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| ParamIntegral:158 | `smoothing_integral` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Phase:29 | `StepPhase` | P | Source formula / typing data checked. |
| Phase:39 | `StepPhase.toK` | P | Source formula / typing data checked. |
| Phase:42 | `StepPhase.ofK` | P | Source formula / typing data checked. |
| Phase:44 | `StepPhase.toK_add` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Phase:45 | `StepPhase.toK_smul` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Phase:46 | `StepPhase.toK_zero` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Phase:47 | `StepPhase.toK_neg` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Phase:51 | `kamNorm_add_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Phase:68 | `kamNorm_neg` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Phase:71 | `kamNorm_smul` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Phase:77 | `kamAddGroupNorm` | P | Source formula / typing data checked. |
| Phase:86 | `stepPhaseNormed` | P | Source formula / typing data checked. |
| Phase:89 | `stepPhase_norm_eq` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Phase:92 | `stepPhaseNormedSpace` | P | Source formula / typing data checked. |
| Phase:98 | `norm_kamPhase_le_kamNorm` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Phase:125 | `kamNorm_le_norm_kamPhase` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Phase:144 | `stepPhaseComplete` | P | Source formula / typing data checked. |
| PullbackAbstract:34 | `seminorm_solve_le` | PN | Correct conditional/abstract or arithmetic supplier; scope in node table. |
| PullbackAbstract:46 | `seminorm_solve_sub_le` | PN | Correct conditional/abstract or arithmetic supplier; scope in node table. |
| Pullback:32 | `stepInv_sub` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Pullback:41 | `stepPullback_diff` | PN | Correct conditional/abstract or arithmetic supplier; scope in node table. |
| Pullback:71 | `stepPullback_const` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Pullback:77 | `stepCommutator_arith` | PN | Correct conditional/abstract or arithmetic supplier; scope in node table. |
| PullbackNu:34 | `stepNu` | P | Source formula / typing data checked. |
| PullbackNu:36 | `stepNu_add` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| PullbackNu:39 | `stepNu_neg` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| PullbackNu:41 | `stepNu_nonneg` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| PullbackNu:47 | `stepNu_mono` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| PullbackNu:63 | `stepNu_transNop_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| PullbackNu:83 | `stepNu_transNop_sub_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| PullbackNu:107 | `stepPullback_sup` | PN | Correct conditional/abstract or arithmetic supplier; scope in node table. |
| PullbackNu:121 | `stepPullback_sub` | PN | Correct conditional/abstract or arithmetic supplier; scope in node table. |
| RealCalc:35 | `StepReal` | P | Source formula / typing data checked. |
| RealCalc:40 | `im_deriv_eq_zero_of_real` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| RealCalc:51 | `stepReal_line` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| RealCalc:69 | `fderiv_im_of_real` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| RealCalc:91 | `stepSymp_field_im` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| RealCalc:99 | `stepSymp_dfield_im` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| RealCalc:127 | `integral_clm_eq_zero` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepCLM:32 | `stepSymp_add_left` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepCLM:39 | `stepSymp_smul_left` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepCLM:50 | `stepSymp_add_right` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepCLM:57 | `stepSymp_smul_right` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepCLM:69 | `stepSympLin` | P | Source formula / typing data checked. |
| StepCLM:79 | `stepSympCLM` | P | Source formula / typing data checked. |
| StepCLM:89 | `stepSympCLM_apply` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepCLM:94 | `norm_stepSympCLM_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepCLM:99 | `stepSympCLM_antisymm` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepCLM:106 | `kamHomEmbed` | P | Source formula / typing data checked. |
| StepCLM:110 | `kamHomEmbed_apply` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepCLM:114 | `kamNorm_kamHomEmbed_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepCLM:126 | `stepEmbedCLM` | P | Source formula / typing data checked. |
| StepCLM:135 | `stepEmbedCLM_apply` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepCLM:138 | `norm_stepEmbedCLM_apply_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepFieldBound:31 | `kamNorm_stepField` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepFieldBound:54 | `homU_stepZ` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepFieldBound:67 | `homV_stepZ` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepFieldBound:80 | `homDomain_stepZ` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepFieldBound:86 | `stepFieldS_norm` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepFieldBound:96 | `stepFieldS_bound` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepFieldBound:108 | `stepFlowHyp_concrete` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepFieldBound:122 | `stepFlowHyp_concrete'` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepNfun:32 | `stepToHom` | P | Source formula / typing data checked. |
| StepNfun:36 | `stepToHom_apply` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepNfun:45 | `stepNfun` | P | Source formula / typing data checked. |
| StepNfun:47 | `stepNfun_hasFDerivAt` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepNfun:53 | `stepNfun_lie` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepSolve:32 | `stepField_sub` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepSolve:92 | `stepSolve_fam_explicit` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepSolve:139 | `stepSolve_fam` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepSolve:186 | `stepFun_eq_homRval` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepSolve:194 | `stepSolve_equation` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepSolve:214 | `stepNhat_fam` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepSolve:238 | `stepSymp_comm_weights` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepSolve:256 | `stepFun_isSmoothing` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepSympEmbed:30 | `stepPairCLM_embed` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| StepSympEmbed:45 | `stepSymp_embed` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| SymplecticFlow:33 | `stepSymp_hasDerivWithinAt` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| SymplecticFlow:46 | `stepSymp_const` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorAssemble:30 | `stepDX_symm_pp` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorAssemble:40 | `stepTaylorOf` | P | Source formula / typing data checked. |
| TaylorBlocks:32 | `stepIotaZ` | P | Source formula / typing data checked. |
| TaylorBlocks:38 | `stepIotaZb` | P | Source formula / typing data checked. |
| TaylorBlocks:43 | `stepIotaZ_apply` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBlocks:46 | `stepIotaZb_apply` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBlocks:49 | `homSqrt2_inv_sq` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBlocks:52 | `stepZ_iotaZ` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBlocks:59 | `stepZb_iotaZ` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBlocks:66 | `stepZ_iotaZb` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBlocks:73 | `stepZb_iotaZb` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBlocks:83 | `stepSymp_z` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBlocks:101 | `blockP` | P | Source formula / typing data checked. |
| TaylorBlocks:105 | `blockP'` | P | Source formula / typing data checked. |
| TaylorBlocks:109 | `blockQ` | P | Source formula / typing data checked. |
| TaylorBlocks:113 | `blockQt` | P | Source formula / typing data checked. |
| TaylorBlocks:116 | `stepSymp_iotaZ` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBlocks:122 | `stepSymp_iotaZb` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBlocks:128 | `stepPr_blockP` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBlocks:136 | `stepPr_blockP'` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBlocks:144 | `stepPr_blockQ` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBlocks:151 | `stepPr_blockQt` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBlocks:158 | `homNormalEntry_eq_pr` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBlocks:175 | `homNormalEntry_symm_of_pr` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBoundA0:33 | `taylorRealPt` | P | Source formula / typing data checked. |
| TaylorBoundA0:35 | `realPt_mem_strip` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBoundA0:39 | `tA0_real_bound` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBoundA0:79 | `taylorConvex_complexStrip` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBoundA0:96 | `norm_fderiv_tA0_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBoundA0:132 | `tA0_bounded` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBound:32 | `norm_stepZ_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBound:48 | `norm_stepZb_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBound:64 | `norm_normal_le_kamNorm` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBound:73 | `kamNorm_fderiv_normal_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBound:125 | `norm_homSqrt2_inv_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBound:132 | `kamNorm_fderiv_iota_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBound:171 | `norm_tP_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBound:179 | `norm_tP'_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBound:187 | `norm_tQ_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBound:195 | `norm_tQt_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBound:205 | `norm_tB_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBound:222 | `norm_tCp_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorBound:229 | `norm_tCm_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorCommute:33 | `e0` | P | Source formula / typing data checked. |
| TaylorCommute:34 | `tcE1` | P | Source formula / typing data checked. |
| TaylorCommute:39 | `taylorMixed_symm` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorCommute:55 | `taylorHasDerivAt_line` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorCommute:63 | `analyticOnNhd_partial` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorCommute:67 | `hasDerivAt_taylorCoeff_zero` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorCommute:75 | `line_eventually_mem` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorCommute:81 | `hasDerivAt_taylorCoeff_one` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorCommute:112 | `line0_eventually_mem` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorCommute:118 | `taylorCoeff_two` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorCommute:121 | `hasDerivAt_taylorCoeff_two` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorCommute:189 | `hasDerivAt_taylorSum_param` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorData:34 | `stepW0L` | P | Source formula / typing data checked. |
| TaylorData:36 | `stepW0L_apply` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorData:38 | `stepW0L_mem` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorData:43 | `stepW0L_add_single` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorData:48 | `tA0` | P | Source formula / typing data checked. |
| TaylorData:49 | `tB` | P | Source formula / typing data checked. |
| TaylorData:51 | `tCp` | P | Source formula / typing data checked. |
| TaylorData:52 | `tCm` | P | Source formula / typing data checked. |
| TaylorData:53 | `tP` | P | Source formula / typing data checked. |
| TaylorData:54 | `tP'` | P | Source formula / typing data checked. |
| TaylorData:55 | `tQ` | P | Source formula / typing data checked. |
| TaylorData:56 | `tQt` | P | Source formula / typing data checked. |
| TaylorData:66 | `tA0_differentiableOn` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorData:69 | `tXfun_differentiableOn` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorData:72 | `tB_differentiableOn` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorData:79 | `tCp_differentiableOn` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorData:84 | `tCm_differentiableOn` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorData:89 | `tDX_differentiableOn` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorData:94 | `tBlock_differentiableOn` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorData:104 | `tA0_periodic` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorData:110 | `tX_periodic` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorData:115 | `tDX_periodic` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorEst:32 | `taylorG` | P | Source formula / typing data checked. |
| TaylorEst:36 | `taylorField` | P | Source formula / typing data checked. |
| TaylorEst:40 | `taylorXR` | P | Source formula / typing data checked. |
| TaylorEst:44 | `kamToStep` | P | Source formula / typing data checked. |
| TaylorEst:50 | `norm_kamToStep` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorEst:53 | `differentiableAt_scaleS` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorEst:62 | `differentiableAt_scaleT` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorEst:81 | `differentiableOn_taylorG` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorEst:90 | `norm_taylorG_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorEst:99 | `taylorCoeff_kamToStep` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorEst:111 | `contDiffAt_taylorG` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorEst:122 | `norm_taylorField_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorEst:140 | `taylorXR_bound` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorEst:154 | `taylorXR_remainder` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorEst:174 | `kamNorm_le_ratio_sq` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorEst:192 | `taylorXR_remainder_128` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFieldBound:30 | `stepZ_of_hom` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFieldBound:41 | `stepZb_of_hom` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFieldBound:52 | `kamDomain_of_hom` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFieldBound:57 | `stepTaylor_fieldBound` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFieldBound:77 | `stepTaylor_subFieldBound` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFieldDiff:31 | `differentiableOn_homPartial` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFieldDiff:39 | `stepField_differentiableAt` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorField:32 | `stepField` | P | Source formula / typing data checked. |
| TaylorField:40 | `stepPr_uv` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorField:52 | `stepFun_field` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFieldRv:32 | `factRealZeroLtOne` | P | Source formula / typing data checked. |
| TaylorFieldRv:35 | `sympK` | P | Source formula / typing data checked. |
| TaylorFieldRv:38 | `sympK_apply` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFieldRv:42 | `stepSymp_scale` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFieldRv:52 | `taylorCoeff_clm` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFieldRv:65 | `sum_taylorCoeff_symp` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFunDeriv:27 | `stepFderiv_apply_eq_sum` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFunDeriv:40 | `stepPrY` | P | Source formula / typing data checked. |
| TaylorFunDeriv:43 | `homPartial_apply_comp` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFunDeriv:55 | `stepFun_hasFDerivAt` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFun:31 | `stepZ` | P | Source formula / typing data checked. |
| TaylorFun:40 | `stepZb` | P | Source formula / typing data checked. |
| TaylorFun:48 | `stepZ_apply` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFun:52 | `stepZb_apply` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFun:61 | `stepPr` | P | Source formula / typing data checked. |
| TaylorFun:66 | `waveStepFun` | P | Source formula / typing data checked. |
| TaylorFun:73 | `stepPrTheta` | P | Source formula / typing data checked. |
| TaylorFun:75 | `hasFDerivAt_pair_term` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFun:82 | `hasFDerivAt_theta_comp` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFun:87 | `hasFDerivAt_op_apply` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFunSym:29 | `homPairL2_swap_of_entries` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFunSym:53 | `stepPr_eq_homPairL2` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorFunSym:57 | `stepPr_swap` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorLinear:29 | `taylorG_sub` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorLinear:34 | `taylorXR_sub` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorOneVar:32 | `taylorCoeff` | P | Source formula / typing data checked. |
| TaylorOneVar:35 | `norm_taylorCoeff_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorOneVar:76 | `norm_taylor_remainder_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorReal:37 | `homCoeff_zero_eq` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorReal:46 | `homCoeff_zero_clm` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorReal:54 | `kamEntry_smul_real` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorReal:59 | `entryImCLM` | P | Source formula / typing data checked. |
| TaylorReal:71 | `entryImCLM_apply` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorReal:76 | `coordImCLM` | P | Source formula / typing data checked. |
| TaylorReal:79 | `coordImCLM_apply` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorReal:81 | `real_mem_complexStrip` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorReal:84 | `stepReal_w0` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorReal:90 | `stepReal_basis_u` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorReal:96 | `stepReal_basis_v` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorReal:110 | `tB_real` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorReal:125 | `stepSymp_dfield_im'` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorReal:132 | `tQ_entry_real` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorReal:186 | `homCoeff_b_real` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorReal:195 | `homCoeff_Q_real` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorRv:32 | `taylorRv` | P | Source formula / typing data checked. |
| TaylorRv:35 | `scaleS_add_smul` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorRv:40 | `taylorCoeff_congr_eventually` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorRv:46 | `hasDerivAt_taylorRv` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorScale:27 | `scaleS` | P | Source formula / typing data checked. |
| TaylorScale:31 | `scaleT` | P | Source formula / typing data checked. |
| TaylorScale:34 | `scaleS_one` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorScale:35 | `scaleT_one` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorScale:37 | `scaleS_mem` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorScale:55 | `kamNorm_scaleT_le` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorSmoothing:35 | `stepTau` | P | Source formula / typing data checked. |
| TaylorSmoothing:37 | `kamDomain_isOpen'` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorSmoothing:39 | `kamDomain_add_tau` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorSmoothing:49 | `fderiv_eq_sympK` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorSmoothing:56 | `stepSymp_dX_symm` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorSmoothing:75 | `stepField_periodic` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorSmoothing:93 | `fderiv_field_periodic` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorValue:31 | `taylorCoeff_zero` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorValue:34 | `scaleS_eq` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorValue:47 | `taylorRv_eq` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorValue:115 | `c1_decomp` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorValue:134 | `stepZ_c1` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorValue:138 | `stepZb_c1` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorValue:147 | `stepSymp_linear` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorValue:155 | `stepSymp_ypart` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorValue:165 | `stepSymp_quadratic` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorValue:186 | `stepFun_taylorOf_eq` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| TaylorValue:215 | `stepField_taylorOf_eq` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Triangle:28 | `stepTriangle` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| Triangle:55 | `stepTriangle_on` | P | Stated identity/bound and analytic domain checked; standard axiom set. |
| ZeroTaylor:27 | `zeroTaylor` | P | Source formula / typing data checked. |

## Files and pinned bytes

Only this report is a persistent auditor edit. Probe files were created under `.lake/abi-scratch/` and removed after checking. No git mutation, source repair, generated-root regeneration, frozen edit, or manifest edit was performed.

| Scoped module (KAM.Wave.KamStep) | Lines | SHA-256 |
|---|---|---|
| Class | 71 | `bb70a30b686f2e51c733244d20923c1cf68e9dca5aa99614ddd56539033eabdd` |
| Data | 177 | `394ed37eb6f2514fa2a1ad7da4953e13616ce50d4ccc09e9a20598f9ea27a1f5` |
| Divisors | 161 | `291489a01ff61de2fd5c6e7cffafc696d8efbce874e7d9fa43a1058f34463c29` |
| FlowEquivariant | 46 | `70367cb770df6c90b23528044a90cb6a19bc2eaa397a50dfdd35b5de6082d1dd` |
| FlowInverse | 63 | `5ca37e474cf5187e55b316806ec9af0f35f4f06c7813f49a65f9b5a006971b57` |
| Flow | 119 | `4a0804b77c0098edb67b5b9430b40ff014b0c22507ccf63e73d812039179dcdf` |
| FlowSkew | 64 | `9e326ffcd1d67ec7af4298c1e1b063d75ae3eebab3c8a7e5692852c888fdb4c9` |
| FlowSmoothDeriv | 140 | `58a8f9e75edfed5b47ec928f912bd117b6314bfd0383f1ee53e42cf22cc0a0cd` |
| FlowSmooth | 160 | `80eb81fc716942a4d84d3932c1344a9e1957b586fba1cb815ed1144e9a289211` |
| FlowStepBounds | 101 | `4c98f0d3f04fce1c2a9b19bb25fa4a20e9d2bcc2f824f484eaadd45210f63580` |
| FlowSymplectic | 92 | `3498f2cd24de8a95577569aa7fe377807c38218ac0f7002cf2bef653a60fd41b` |
| FlowTime | 38 | `8abed11feba5bcf53fecd0a225b8c66f9d8898f3f5ed0247f1a1757b06e05f28` |
| FlowTransport | 37 | `776e1cb55cb94e61f88deb5dd1ec064105a242ddc2125bd8062edb52ae1e6f31` |
| FlowVariational | 121 | `df900c392c790cd17b13ee54038b5e6da780648d5657807feddb856f7a84aec0` |
| HoloFderiv | 416 | `8a7f78fe4b1b758a944c8a96247b1008944744006f9f0df046c8c7ad8a709ceb` |
| LatticeBN | 126 | `4649728afd4b169bcdef525db47611fca6430581476ee87ccf27693822141198` |
| Omega | 221 | `dc7c98379b64c5c6584b787674b47ffaa7ab284ace35b5d3a9ee5a6c1a91276d` |
| ParamIntegral | 220 | `e5f1b00a8832c2be1456522ffd2f575762f385b8f9d88c9386dbec6bf7c6fb9f` |
| Phase | 178 | `ec6a3653ada1a5ee43ee69da00b4c9f3ad33437e3ec8f446f6c84c64b114db0e` |
| PullbackAbstract | 63 | `2b1aee0558edc12f0b8317ff9feaafa28afc7c874c9402c37a71abd827af5459` |
| Pullback | 81 | `a82fd49a442c2bd5dee2f9dbd18741b53095bdefe0cd3534fdfcd656279c6314` |
| PullbackNu | 157 | `63587866fe81a9f83e0abc22be7897c81ad82652bcca0506d1ff9a55b389fa15` |
| RealCalc | 138 | `6eea82dbad3789c138f35154e61275720961d3735eac7e68600fbd91ebf99a08` |
| StepCLM | 142 | `fc0a943acce07e6d3117cb1afe8862a22973b99ea6684d136763f5c7d8692c48` |
| StepFieldBound | 135 | `2b126b3120ed392a7e8a3b58d613dc31cca09e8d9ec3a130b25489e83c203c3f` |
| StepNfun | 92 | `ae0864506749aa1a66214de93a47b79929877d11efdffd311ab60584aebeb70c` |
| StepSolve | 270 | `632084f422ac4ae3f09a23005a50ca885ed8c99ab57b848675840d8c33c9364d` |
| StepSympEmbed | 54 | `3d3c5d6ec6fdc34075bb000a02f3bd4a3f922d6229bd2de8ec3aca07d34ea205` |
| SymplecticFlow | 68 | `bbeff76225e0956f5dee1b9743033a77c32ef0946720bb41042a4c3ad5d0abf9` |
| TaylorAssemble | 94 | `470ba4bd2e7fdc36c7f4d9f59b81c378613c493c78ff7ff1daa9030b4b2a8259` |
| TaylorBlocks | 183 | `e2bcc522b8bd38652f6c8f4235581e0cac24b82500cb4e549c5312ad1602e215` |
| TaylorBoundA0 | 170 | `52ea35c11f3f437f4c802fd9a5dc34d18d11f61e9486e2c58003ddd4c35e3839` |
| TaylorBound | 236 | `9900517889988d283a94c8aab32dfe3184649022a6cf8f41f54eb46632c69b60` |
| TaylorCommute | 198 | `d4f03345bf5bfa55952adeb2d83b1c3236869425b3d56e3da82121b6476a6335` |
| TaylorData | 122 | `601d567e6dfe49bd492299786aae89f1817fe7ebc84ed34e1127f033624d09eb` |
| TaylorEst | 224 | `c4711f6d048d9967ca1a1b9f33c7e98f47ed377dc71878f91058d6d77bc79f46` |
| TaylorFieldBound | 107 | `509b5e0db6c387db71d551580ecdeb59834bd1220b23a23959f90b52ef1e8fd5` |
| TaylorFieldDiff | 82 | `92ddbed202708ac0739f79d486730f2a186e66f4b732e1fbb882c55ce9bf9173` |
| TaylorField | 124 | `afd57eb71fdb411a9af1858839a73f8c33d8a7c6214441a735c5c4c8606da5e4` |
| TaylorFieldRv | 93 | `d8d83f1ed626698273311dcf2f9df8dfceb56c49baa7d04637376ddee4e95353` |
| TaylorFunDeriv | 110 | `8306d3aa41d7ff55c3898fdc6bc28578e4949b719ae3325cf2018243721ea02c` |
| TaylorFun | 96 | `d4f35d2662e608eb83f3411fed802d51a71d004e035fb32ed4fa4be39f12c3f5` |
| TaylorFunSym | 66 | `cff623a7e35717277448e39a5879c21f66dadbebce83ce7607ed4a2868d2e07b` |
| TaylorLinear | 47 | `9b5757070c583ed2491c165877ded35878f7f40b30076cff3ffa3a65da13c44d` |
| TaylorOneVar | 104 | `3104901b7cc933efe3df6fcba4770ca9ae7ecc6cd2d3c17ea650bb67bad07a2e` |
| TaylorReal | 216 | `719e46277d1a8e39598da03e992e26caa2bf3138a04f01f7d5ba97186b0395dc` |
| TaylorRv | 95 | `dcdefc9fa964ec66ad97e5a51f5d89fb030b836a91f34a9afebd89a2ab7d67b6` |
| TaylorScale | 81 | `f29fb891f29c6c2327c6220b64b3aee77302dc04b8232a2af9961eff4beda08b` |
| TaylorSmoothing | 104 | `9ad90e03c87726995a8db5c53b3aca1df7f41a8fd3b28b25efec459531d03bca` |
| TaylorValue | 252 | `f3bbf781ed6d1e394d79716ae34750b0803940499ea81139060f5bfab1681a51` |
| Triangle | 77 | `789cfee415be47851df94b69af8cd22d849ade0674ce6463fd1ec3bd328ae029` |
| ZeroTaylor | 48 | `702b5ea20bdd89e2084a1dd5a5da10946b4a58a0dfcf75957ebd2f8f6365ea97` |

## Hygiene and validation

All Lean/Lake checks below were serial and ran inside the owner's D53 scope. No budget or recursion override was set. The launcher replay/name checks were stated as already completed by the user; their logs are unavailable in this turn. **Kernel replay was not rerun; there is no independently observed leanchecker exit code in this report.** The checks below are fresh auditor evidence, not a reconstruction of the unseen launcher results.

### Source hygiene / quarantine

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no output (exit 0). The wider diff does contain producer-generated `KAM/Root/Wave.lean` (106 added imports); this is disclosed, not an auditor modification. No module in the scoped import closure imports a provider or a frozen theorem. The five imported frozen definitions are SEALED in the current manifest: ComplexStrip, OmegaZero, Wave/Coeff, Wave/EllWeight, Wave/WaveSpace. No DRAFT_SORRY import is in that closure.

A comment-stripped scan of all 52 scoped files found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, or heartbeat/recursion/synthesis override. Module headers, copyright, interface imports, module docstrings and public sections pass the source linter. Maximum scoped file length: HoloFderiv.lean, 416 lines, below 1500.

Lint command (only the owner-specified lint entry point):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpja5
```

Exit 0. Complete output:

```text
check_lean_modules: PASS (3859 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

### Targeted builds

For each MODULE in the following table, in table order and waiting for completion before the next:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpja5 MODULE
```

The compile-gate driver invokes `lake build MODULE`. All 16 invocations exited 0. These are targeted incremental checks against the existing build snapshot, not a clean/library rebuild. Their import closures cover 52/52 scoped modules; transitive run-B imports are build dependencies only and receive no source-audit verdict. The large job counts below are Lake's reported dependency counts, not newly rebuilt source modules. Output also replayed 362 warning lines across those overlapping closures (unused variables/simp arguments and other linter warnings); there were no build errors. No warning suppression was added. The success output for each command is recorded exactly below.

| MODULE | Exact success output | Exit |
|---|---|---|
| `KAM.Wave.KamStep.Data` | `Build completed successfully (3173 jobs).` | 0 |
| `KAM.Wave.KamStep.Divisors` | `Build completed successfully (2319 jobs).` | 0 |
| `KAM.Wave.KamStep.FlowEquivariant` | `Build completed successfully (2887 jobs).` | 0 |
| `KAM.Wave.KamStep.FlowInverse` | `Build completed successfully (2889 jobs).` | 0 |
| `KAM.Wave.KamStep.FlowSkew` | `Build completed successfully (2174 jobs).` | 0 |
| `KAM.Wave.KamStep.FlowSymplectic` | `Build completed successfully (2889 jobs).` | 0 |
| `KAM.Wave.KamStep.FlowTime` | `Build completed successfully (2887 jobs).` | 0 |
| `KAM.Wave.KamStep.FlowTransport` | `Build completed successfully (2059 jobs).` | 0 |
| `KAM.Wave.KamStep.ParamIntegral` | `Build completed successfully (2844 jobs).` | 0 |
| `KAM.Wave.KamStep.Pullback` | `Build completed successfully (2047 jobs).` | 0 |
| `KAM.Wave.KamStep.PullbackNu` | `Build completed successfully (3350 jobs).` | 0 |
| `KAM.Wave.KamStep.StepSympEmbed` | `Build completed successfully (3322 jobs).` | 0 |
| `KAM.Wave.KamStep.TaylorFieldBound` | `Build completed successfully (3345 jobs).` | 0 |
| `KAM.Wave.KamStep.TaylorReal` | `Build completed successfully (3344 jobs).` | 0 |
| `KAM.Wave.KamStep.Triangle` | `Build completed successfully (2752 jobs).` | 0 |
| `KAM.Wave.KamStep.ZeroTaylor` | `Build completed successfully (3275 jobs).` | 0 |

### Axioms

Created `.lake/abi-scratch/W5StepAAudit.lean` containing the 52 scoped module imports followed by one `#print axioms <fully-qualified-name>` command for every new named public theorem (298 commands; names in the declaration inventory). The import list is exactly the scoped file inventory above. Exact check command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env sh -c 'LEAN_PATH="/root/code/KAM-inp-wpja5/.lake/build/lib/lean:/root/code/KAM-inp/.lake/build/lib/lean:$LEAN_PATH" exec lean .lake/abi-scratch/W5StepAAudit.lean'
```

Exit 0, 298 result lines, no error lines and no `sorryAx`. Every result has exactly `[propext, Classical.choice, Quot.sound]`. Complete output:

```text
'KAM.Wave.isSmoothing_unique_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.FamBound.famMono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamProd_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepC1_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.waveC_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.waveBWconst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.waveBNconst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepCF_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepCFn_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepC0_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepC0n_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepMF_le_of_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepMF_margins' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSolve_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSolve_bound_mod' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepEstimate_arith' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homPairL_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.waveA_le_of_modeSize_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepDivisors' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.rpow_half_le_add_two_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFreqHyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.holoFlow_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_fderiv_holoFlow_sub_id_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.isUnit_fderiv_holoFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepPhase_toK_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepDomain_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepDomain_margin' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFlowHyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepImage_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.skew_of_hamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasFDerivAt_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasFDerivAt_smoothDisp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.differentiableOn_smoothDisp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_fderiv_smoothDisp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.fderiv_holoFlow_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_fderiv_smoothDisp_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.flowHyp_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.continuousOn_smooth_integrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.holoFlow_smooth_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_smoothDisp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_smoothDisp_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.one_add_mul_exp_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.flowII_disp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.flowII_disp_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.flowII_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.flowII_deriv_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.continuousOn_flowVarG' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivWithinAt_fderiv_holoFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.holoFlow_preserves_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivWithinAt_comp_holoFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasFDerivAt_comp_hamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tendsto_picardD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tendsto_picardG' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.aestronglyMeasurable_flowVarG' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_flowVarG_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.intervalIntegrable_flowVarG' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.fderiv_holoFlow_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.continuousOn_fderiv_holoFlow_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.differentiableAt_slice2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.slice2L_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.differentiableAt_fderiv_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.exists_hasFDerivAt_fderiv_plane' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_holoD2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.holoD2_add_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.holoD2_smul_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.holoD2_plane' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.holoD2_add_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.holoD2_smul_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.holo_local_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_fderiv_le_local' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.differentiableAt_fderiv_line_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.taylorCoeff_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_holoD2_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_fderiv_remainder_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasFDerivAt_fderiv_of_holomorphic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.differentiableOn_fderiv_of_holomorphic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.waveS_le_waveBNconst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.waveBN_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.waveBN_summable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.waveBW_le_waveBN' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.waveBN_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_stepWinv_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_stepPairCLM_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepPairCLM_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_sum_two_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_arith' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_stepSymp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_antisymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepPairCLM_basis' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepWinv_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_sub_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_nondeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_integral_sub_riemann_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tendstoUniformlyOn_riemann' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.riemannSum_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.smoothing_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepPhase.toK_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepPhase.toK_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepPhase.toK_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepPhase.toK_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamNorm_add_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamNorm_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamNorm_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepPhase_norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_kamPhase_le_kamNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamNorm_le_norm_kamPhase' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.seminorm_solve_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.seminorm_solve_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepInv_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepPullback_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepPullback_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepCommutator_arith' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepNu_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepNu_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepNu_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepNu_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepNu_transNop_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepNu_transNop_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepPullback_sup' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepPullback_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.im_deriv_eq_zero_of_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepReal_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.fderiv_im_of_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_field_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_dfield_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.integral_clm_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_add_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_smul_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_add_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_smul_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSympCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_stepSympCLM_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSympCLM_antisymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamHomEmbed_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamNorm_kamHomEmbed_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepEmbedCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_stepEmbedCLM_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamNorm_stepField' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homU_stepZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homV_stepZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homDomain_stepZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFieldS_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFieldS_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFlowHyp_concrete' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFlowHyp_concrete'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepToHom_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepNfun_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepNfun_lie' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepField_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSolve_fam_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSolve_fam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFun_eq_homRval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSolve_equation' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepNhat_fam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_comm_weights' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFun_isSmoothing' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepPairCLM_embed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_embed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_hasDerivWithinAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepDX_symm_pp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepIotaZ_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepIotaZb_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homSqrt2_inv_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepZ_iotaZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepZb_iotaZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepZ_iotaZb' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepZb_iotaZb' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_z' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_iotaZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_iotaZb' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepPr_blockP' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepPr_blockP'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepPr_blockQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepPr_blockQt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homNormalEntry_eq_pr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homNormalEntry_symm_of_pr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.realPt_mem_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tA0_real_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.taylorConvex_complexStrip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_fderiv_tA0_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tA0_bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_stepZ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_stepZb_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_normal_le_kamNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamNorm_fderiv_normal_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_homSqrt2_inv_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamNorm_fderiv_iota_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_tP_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_tP'_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_tQ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_tQt_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_tB_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_tCp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_tCm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.taylorMixed_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.taylorHasDerivAt_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.analyticOnNhd_partial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_taylorCoeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.line_eventually_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_taylorCoeff_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.line0_eventually_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.taylorCoeff_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_taylorCoeff_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_taylorSum_param' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepW0L_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepW0L_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepW0L_add_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tA0_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tXfun_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tB_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tCp_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tCm_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tDX_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tBlock_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tA0_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tX_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tDX_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_kamToStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.differentiableAt_scaleS' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.differentiableAt_scaleT' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.differentiableOn_taylorG' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_taylorG_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.taylorCoeff_kamToStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.contDiffAt_taylorG' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_taylorField_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.taylorXR_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.taylorXR_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamNorm_le_ratio_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.taylorXR_remainder_128' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepZ_of_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepZb_of_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamDomain_of_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepTaylor_fieldBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepTaylor_subFieldBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.differentiableOn_homPartial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepField_differentiableAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepPr_uv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFun_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sympK_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.taylorCoeff_clm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sum_taylorCoeff_symp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFderiv_apply_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homPartial_apply_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFun_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepZ_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepZb_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasFDerivAt_pair_term' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasFDerivAt_theta_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasFDerivAt_op_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homPairL2_swap_of_entries' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepPr_eq_homPairL2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepPr_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.taylorG_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.taylorXR_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_taylorCoeff_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_taylor_remainder_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homCoeff_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homCoeff_zero_clm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamEntry_smul_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.entryImCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.coordImCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.real_mem_complexStrip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepReal_w0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepReal_basis_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepReal_basis_v' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tB_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_dfield_im'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tQ_entry_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homCoeff_b_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homCoeff_Q_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.scaleS_add_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.taylorCoeff_congr_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_taylorRv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.scaleS_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.scaleT_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.scaleS_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamNorm_scaleT_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamDomain_isOpen'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamDomain_add_tau' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.fderiv_eq_sympK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_dX_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepField_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.fderiv_field_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.taylorCoeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.scaleS_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.taylorRv_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.c1_decomp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepZ_c1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepZb_c1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_ypart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSymp_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFun_taylorOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepField_taylorOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepTriangle' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepTriangle_on' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The scratch probe was deleted after checking. Final source hashes were compared with the file inventory: 52/52 unchanged. Final `git status --short` contains only the new audit report.


## Errata, deviations and remaining uncertainty

No new suspected defect of a pinned mathematical source or frozen definition was found. F1/F2 concern incomplete Lean export coverage, not false blueprint claims. Existing documented source issues (P96-K Lemma A.4 margins, p.130's asserted new field, modified-divisor Lipschitz guard) are not newly adjudicated here. The stronger symplectic constant `(4π+1)r²`, explicit σ≤1 image guard implied by step data, representative-coordinate embedding, and separate majorant encoding were preserved. No auditor-introduced mathematical deviation.

Full Taylor/solve/flow reality is deliberately not certified in this run, consistently with the user's run-B scope. Joint-continuity and target-onto gaps remain as literally identified above; the tested infrastructure can be reused, but the complete requested flow-calculus clauses cannot yet be marked closed.
