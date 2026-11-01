NODE: bpW:w5:new-ham
KIND: lemma
TITLE: New Hamiltonian; conjugacy
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L474-L489
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L490-L511
CONTRACT_ID: bpW:w5:new-ham
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F); Phi = phi^1, D_+ = D(s-5sigma,eta r), R(t) = (1-t) hat N + t R, H = N + P, N_+ = N + hat N = <omega_+,y> + sum Omega_{+,j} z_j zbar_j, P_+ = (P - R) o Phi + int_0^1 {R(t),F} o phi^t dt
SOURCE_QUANTIFIERS: for w in D_+, W in P^{p_+}
SOURCE_CONCLUSION: (i) H o Phi = N_+ + P_+ + hat a_0 on D_+; (ii) P_+ in S_{p_+}(D_+), real and periodic, X_{P_+} = Phi^*(X_P - X_R) + int_0^1 (phi^t)^* [X_{R(t)},X_F] dt; (iii) varpi(X_H(Phi w), D Phi(w) W) = varpi(X_{N_+}(w) + X_{P_+}(w), W) with X_N : P -> P^{p-1} of Lemma bpW:w4:lie(i) and varpi extended to P^{p-1} x P^{p_+}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:flow, bpW:w5:newham-sec#bracket, bpW:w5:solve, bpW:w4:lie, bpW:w4:index, bpW:w5:class, stepW:w5:n-exp, stepW:w5:n-br, stepW:w5:n-field, stepW:w5:n-conj
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L475-L475 | the flow and its setting
EDGE: bpW:w5:newham-sec#bracket | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L478-L478 | {R(t),F}
EDGE: bpW:w5:solve | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L476-L476 | hat N, hat omega, hat Omega
EDGE: bpW:w4:lie | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L486-L486 | (i) X_N
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L487-L487 | (bpW:w4:pairing)
EDGE: bpW:w5:class | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L481-L481 | S_{p_+}
EDGE: stepW:w5:n-exp | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L491-L491 | proof step
EDGE: stepW:w5:n-br | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L499-L499 | proof step
EDGE: stepW:w5:n-field | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L503-L503 | proof step
EDGE: stepW:w5:n-conj | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L506-L506 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: sol-delta6-W-W-w5b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.stepExpansion_H, KAM.Wave.stepNewHam_flow_H, KAM.Wave.stepNewHam_concrete, KAM.Wave.stepPplusS, KAM.Wave.stepXplusS, KAM.Wave.stepPlus_isSmoothing, KAM.Wave.stepPplusS_periodic, KAM.Wave.Pplus_real_of_FT_real, KAM.Wave.stepWeakConj, KAM.Wave.stepXN, KAM.Wave.stepDN_eq_symp_XN, KAM.Wave.stepNfun_add_Nhat (KAM/Wave/KamStep/NewHamExp.lean, KAM/Wave/KamStep/NewHamFlow.lean, KAM/Wave/KamStep/NewHamConcrete.lean, KAM/Wave/KamStep/StepPlusAssemble.lean, KAM/Wave/KamStep/StepPeriodicFlow.lean, KAM/Wave/KamStep/RealStep.lean, KAM/Wave/KamStep/NewHamConj.lean, KAM/Wave/KamStep/RealNField.lean, KAM/Wave/KamStep/StepNplus.lean)
LEAN_NOTE: W5-STEP-B audit 1 PASS (new-ham (i)-(iii): scalar expansion, smoothing field of P_+ with the transport/commutator formula, field-form weak conjugacy with the affine X_N in p-1 representatives); reality and periodicity of P_+ in the W5-REAL chain
NOTE: -

NODE: stepW:w5:n-exp
KIND: step
TITLE: Expansion
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L491-L498
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L491-L498
CONTRACT_ID: stepW:w5:n-exp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:new-ham: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F); Phi = phi^1, D_+ = D(s-5sigma,eta r), R(t) = (1-t) hat N + t R, H = N + P, N_+ = N + hat N = <omega_+,y> + sum Omega_{+,j} z_j zbar_j, P_+ = (P - R) o Phi + int_0^1 {R(t),F} o phi^t dt
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:new-ham (for w in D_+, W in P^{p_+}); within the step: w in D_+; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: H(Phi w) = N(w) + hat N(w) + hat a_0 + (P - R)(Phi w) + int_0^1 {(1-tau) hat N + tau R, F}(phi^tau w) dtau; this is (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:flow, bpW:w5:flow-calc, bpW:w5:ext-ftc, bpW:w5:ext-triangle
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L492-L492 | (iii)
EDGE: bpW:w5:flow-calc | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L492-L492 | (v)
EDGE: bpW:w5:ext-ftc | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L492-L492 | calculus along curves
EDGE: bpW:w5:ext-triangle | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L495-L495 | the triangular double integral applied to g(tau) = {hat N - R, F}(phi^tau w)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b+claude-suborch-W-gapfix
REVIEWER: sol-delta7-W-w5b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.stepExpansion_H, KAM.Wave.stepNewHam_flow_H, KAM.Wave.stepNewHam_concrete (KAM/Wave/KamStep/NewHamExp.lean, KAM/Wave/KamStep/NewHamFlow.lean, KAM/Wave/KamStep/NewHamConcrete.lean)
LEAN_NOTE: step of PROVED parent bpW:w5:new-ham; W5-STEP-B audit 1 PASS
NOTE: -

NODE: stepW:w5:n-br
KIND: step
TITLE: Bracket field
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-br@L499-L502
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-br@L499-L502
CONTRACT_ID: stepW:w5:n-br
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:new-ham: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F); Phi = phi^1, D_+ = D(s-5sigma,eta r), R(t) = (1-t) hat N + t R, H = N + P, N_+ = N + hat N = <omega_+,y> + sum Omega_{+,j} z_j zbar_j, P_+ = (P - R) o Phi + int_0^1 {R(t),F} o phi^t dt
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:new-ham (for w in D_+, W in P^{p_+}); within the step: G, F in T; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: {G,F} in S_{p_+} with field [X_G,X_F]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:c-skew
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:c-skew | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-br@L501-L501 | skewness of DX
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.hasFDerivAt_bracket, KAM.Wave.stepBrG, KAM.Wave.stepBrZ, KAM.Wave.stepBrG_hasFDerivAt (KAM/Wave/KamStep/FlowSkew.lean, KAM/Wave/KamStep/StepBracket.lean)
LEAN_NOTE: step of PROVED parent bpW:w5:new-ham; W5-STEP-B audit 1 PASS
NOTE: -

NODE: stepW:w5:n-field
KIND: step
TITLE: Field of $P_+$
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-field@L503-L505
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-field@L503-L505
CONTRACT_ID: stepW:w5:n-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:new-ham: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F); Phi = phi^1, D_+ = D(s-5sigma,eta r), R(t) = (1-t) hat N + t R, H = N + P, N_+ = N + hat N = <omega_+,y> + sum Omega_{+,j} z_j zbar_j, P_+ = (P - R) o Phi + int_0^1 {R(t),F} o phi^t dt
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:new-ham (for w in D_+, W in P^{p_+}); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii): the field of P_+; reality
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:flow-calc, stepW:w5:n-br, bpW:w3:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:flow-calc | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-field@L503-L503 | (iv) transport, (i) continuity
EDGE: stepW:w5:n-br | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-field@L504-L504 | the bracket field
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-field@L504-L504 | differentiation under the t-integral
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.stepPlus_isSmoothing, KAM.Wave.newHam_integral_smoothing, KAM.Wave.hasFDerivAt_comp_flow_smooth, KAM.Wave.Pplus_real_of_FT_real (KAM/Wave/KamStep/StepPlusAssemble.lean, KAM/Wave/KamStep/NewHamIntegral.lean, KAM/Wave/KamStep/NewHamTransport.lean, KAM/Wave/KamStep/RealStep.lean)
LEAN_NOTE: step of PROVED parent bpW:w5:new-ham; W5-STEP-B audit 1 PASS
NOTE: -

NODE: stepW:w5:n-conj
KIND: step
TITLE: Conjugacy
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-conj@L506-L510
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-conj@L506-L510
CONTRACT_ID: stepW:w5:n-conj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:new-ham: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F); Phi = phi^1, D_+ = D(s-5sigma,eta r), R(t) = (1-t) hat N + t R, H = N + P, N_+ = N + hat N = <omega_+,y> + sum Omega_{+,j} z_j zbar_j, P_+ = (P - R) o Phi + int_0^1 {R(t),F} o phi^t dt
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:new-ham (for w in D_+, W in P^{p_+}); within the step: w, W; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii) weak conjugacy
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:lie, stepW:w5:n-field, stepW:w5:n-exp
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:lie | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-conj@L509-L509 | (i) convergence of the pairings
EDGE: stepW:w5:n-field | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-conj@L510-L510 | (ii)
EDGE: stepW:w5:n-exp | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-conj@L506-L506 | (i) H o Phi = N_+ + P_+ + hat a_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.stepWeakConj, KAM.Wave.stepXN, KAM.Wave.stepDN_eq_symp_XN (KAM/Wave/KamStep/NewHamConj.lean, KAM/Wave/KamStep/RealNField.lean)
LEAN_NOTE: step of PROVED parent bpW:w5:new-ham; W5-STEP-B audit 1 PASS
NOTE: -

NODE: bpW:w5:pullback
KIND: lemma
TITLE: Pull-back; P96-K (12)
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L520-L524
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L525-L544
CONTRACT_ID: bpW:w5:pullback
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F); Y(.,xi) holomorphic fields D(s-3sigma,4 eta r) -> P^{p_+}
SOURCE_QUANTIFIERS: for ¦t¦ <= 1
SOURCE_CONCLUSION: ¦(phi^t)^* Y¦^lambda_{eta r,D_+} <= 7 ¦Y¦^lambda_{eta r,D(s-3sigma,4 eta r)} (norm ¦.¦_{p_+,eta r})
CONSTANT_SCOPE: 7 absolute
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:flow, stepW:w5:p-inv, stepW:w5:p-dy, stepW:w5:p-ass
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L521-L521 | the setting
EDGE: stepW:w5:p-inv | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L526-L526 | proof step
EDGE: stepW:w5:p-dy | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L534-L534 | proof step
EDGE: stepW:w5:p-ass | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L537-L537 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: sol-delta6-W-W-w5b
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.stepPullback_bounds, KAM.Wave.stepPullback_const, KAM.Wave.stepPullback_diff, KAM.Wave.stepPullback_sup, KAM.Wave.stepPullback_sub, KAM.Wave.stepNu_transNop_le, KAM.Wave.stepNu_transNop_sub_le (KAM/Wave/KamStep/StepPullbackBound.lean, KAM/Wave/KamStep/Pullback.lean, KAM/Wave/KamStep/PullbackNu.lean)
LEAN_NOTE: W5-STEP-A audit 1 PASS, supplier scope (conditional algebraic helpers whose transport equation is discharged by consumers via transSolve_spec), W5-STEP-B audit 1: assembly in StepPlus*/StepPullbackBound without defect; missing: no standalone statement |(phi^t)^* Y|^lambda <= 7 |Y|^lambda for a general Y; the factor 7 is combined only inside the X_(P_+) bound (stepXplus_pair_bound, stepPlus_famBound)
NOTE: -

NODE: stepW:w5:p-inv
KIND: step
TITLE: Inverse in the small scale
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L526-L533
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L526-L533
CONTRACT_ID: stepW:w5:p-inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:pullback: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F); Y(.,xi) holomorphic fields D(s-3sigma,4 eta r) -> P^{p_+}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:pullback (for ¦t¦ <= 1); within the step: W; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦D(phi^t)^{-1}¦_{p_+->p_+,eta r} <= 2 on D(s-3sigma,r/4); for xi != zeta, with N_1 = sup_V ¦X_{F(xi)} - X_{F(zeta)}¦_{p_+,r} and lambda N_1 <= M_F ¦xi - zeta¦: lambda ¦Delta D phi^t¦_{p_+->p_+,eta r} <= ¦xi - zeta¦ and lambda ¦Delta (D phi^t)^{-1}¦ <= 4 ¦xi - zeta¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:omega, bpW:w5:flow, stepW:w5:f-der, bpW:w3:ext-neumann, bpW:w5:data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:omega | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L527-L527 | norm comparisons
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L527-L527 | (ii)
EDGE: stepW:w5:f-der | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L529-L533 | the parameter bound
EDGE: bpW:w3:ext-neumann | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L529-L533 | inverse norm bound from the one-half operator perturbation
EDGE: bpW:w5:data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L532-L532 | (bpW:w5:small)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b+claude-suborch-W-gapfix
REVIEWER: sol-delta7-W-w5b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.stepNu_transNop_le, KAM.Wave.stepNu_transNop_sub_le, KAM.Wave.seminorm_solve_le (KAM/Wave/KamStep/PullbackNu.lean, KAM/Wave/KamStep/PullbackAbstract.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w5:pullback; W5-STEP-A audit 1 PASS (inverse-free estimates on target representatives)
NOTE: -

NODE: stepW:w5:p-dy
KIND: step
TITLE: Derivative of $Y$
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-dy@L534-L536
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-dy@L534-L536
CONTRACT_ID: stepW:w5:p-dy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:pullback: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F); Y(.,xi) holomorphic fields D(s-3sigma,4 eta r) -> P^{p_+}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:pullback (for ¦t¦ <= 1); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦DY¦_{p->p_+,eta r} <= 2¦Y¦/sigma on D(s-4sigma,2 eta r)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:kam-domain, bpW:w1:cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:kam-domain | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-dy@L534-L534 | margins
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-dy@L536-L536 | Cauchy estimate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.kamNorm_lipschitz_small (KAM/Wave/KamStep/StepLip.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w5:pullback; Cauchy estimate at scale eta r (W5-STEP-B audit 1 scoped module StepLip)
NOTE: -

NODE: stepW:w5:p-ass
KIND: step
TITLE: Assemble
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L537-L543
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L537-L543
CONTRACT_ID: stepW:w5:p-ass
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:pullback: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F); Y(.,xi) holomorphic fields D(s-3sigma,4 eta r) -> P^{p_+}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:pullback (for ¦t¦ <= 1); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦(phi^t)^*Y¦ <= 2¦Y¦; lambda ¦Delta[(phi^t)^*Y]¦ <= (4¦Y¦ + 2 lambda ¦Y¦^L + ¦Y¦/2) ¦xi - zeta¦; hence ¦(phi^t)^*Y¦^lambda <= (13/2)¦Y¦ + 2 lambda ¦Y¦^L <= 7 ¦Y¦^lambda
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:p-inv, stepW:w5:p-dy, bpW:w5:lambda-product, stepW:w5:f-par
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:p-inv | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L537-L537 | inverse bounds
EDGE: stepW:w5:p-dy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L539-L539 | derivative of Y
EDGE: bpW:w5:lambda-product | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L538-L538 | lambda-norm of products
EDGE: stepW:w5:f-par | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L540-L543 | the bound on the parameter difference of the flow is used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b+claude-suborch-W-gapfix
REVIEWER: sol-delta7-W-w5b
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.stepPullback_bounds, KAM.Wave.stepPullback_diff, KAM.Wave.stepPullback_const (KAM/Wave/KamStep/StepPullbackBound.lean, KAM/Wave/KamStep/Pullback.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w5:pullback; W5-STEP-A audit 1 PASS, supplier scope: conditional helpers plus the arithmetic 7; not exported as a standalone lambda-norm bound
NOTE: -

NODE: bpW:w5:commutator
KIND: lemma
TITLE: Commutators
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L548-L551
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L552-L560
CONTRACT_ID: bpW:w5:commutator
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F)
SOURCE_QUANTIFIERS: for 0 <= t <= 1
SOURCE_CONCLUSION: ¦[X_{R(t)},X_F]¦^lambda_{eta r,D(s-3sigma,4 eta r)} <= 24 eps M_F/(sigma eta^2)
CONSTANT_SCOPE: 24 absolute
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:flow, bpW:w5:newham-sec#bracket, stepW:w5:k-cauchy, stepW:w5:k-bd
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L549-L549 | the setting
EDGE: bpW:w5:newham-sec#bracket | blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L550-L550 | the commutator
EDGE: stepW:w5:k-cauchy | blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L553-L553 | proof step
EDGE: stepW:w5:k-bd | blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L556-L556 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.hasFDerivAt_bracket, KAM.Wave.stepBrZ, KAM.Wave.stepBrZ_norm_le, KAM.Wave.stepBrZ_sub_norm_le, KAM.Wave.stepFieldS_cauchy, KAM.Wave.stepCommutator_arith (KAM/Wave/KamStep/FlowSkew.lean, KAM/Wave/KamStep/StepBracket.lean, KAM/Wave/KamStep/Pullback.lean)
LEAN_NOTE: W5-STEP-A audit 1 PASS, supplier scope (bracket sign DX_G X_F - DX_F X_G, arithmetic 24 eps M_F/(sigma eta^2)), W5-STEP-B audit 1: assembly without defect; missing: the bound |[X_R(t),X_F]|^lambda_(eta r, D(s-3sigma,4 eta r)) <= 24 eps M_F/(sigma eta^2) is not a standalone export (combined only inside stepXplus_pair_bound)
NOTE: -

NODE: stepW:w5:k-cauchy
KIND: step
TITLE: Cauchy
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-cauchy@L553-L555
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-cauchy@L553-L555
CONTRACT_ID: stepW:w5:k-cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:commutator: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:commutator (for 0 <= t <= 1); within the step: G in {R(t),F}; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦DX_G¦_{p->p_+,r} <= (2/sigma)¦X_G¦ on D(s-2sigma,r/2) and for parameter differences
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:kam-domain, bpW:w1:cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:kam-domain | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-cauchy@L554-L554 | margins
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-cauchy@L555-L555 | Cauchy
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.stepFieldS_cauchy, KAM.Wave.stepBrZ_norm_le, KAM.Wave.stepBrZ_sub_norm_le (KAM/Wave/KamStep/StepBracket.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w5:commutator; Cauchy bounds for the concrete fields and parameter differences (W5-STEP-B audit 1 scoped module StepBracket)
NOTE: -

NODE: stepW:w5:k-bd
KIND: step
TITLE: Bound
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L556-L559
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L556-L559
CONTRACT_ID: stepW:w5:k-bd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:commutator: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:commutator (for 0 <= t <= 1); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the commutator bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:taylor, bpW:w5:solve, bpW:w5:lambda-product, stepW:w5:k-cauchy, bpW:w5:omega
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:taylor | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L557-L557 | ¦X_R¦ <= 3 eps
EDGE: bpW:w5:solve | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L557-L557 | ¦X_{hat N}¦ <= 6 eps, ¦X_F¦ <= M_F
EDGE: bpW:w5:lambda-product | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L557-L557 | submultiplicativity
EDGE: stepW:w5:k-cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L558-L558 | derivative bounds
EDGE: bpW:w5:omega | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L559-L559 | ¦.¦_{eta r} <= eta^{-2}¦.¦_r
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.stepCommutator_arith, KAM.Wave.stepBrZ_norm_le (KAM/Wave/KamStep/Pullback.lean, KAM/Wave/KamStep/StepBracket.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w5:commutator; arithmetic exported, the commutator lambda-bound itself only inside the X_(P_+) assembly
NOTE: -

NODE: bpW:w5:step
KIND: theorem
TITLE: One KAM step
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L565-L588
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L589-L602
CONTRACT_ID: bpW:w5:step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: step data (Definition bpW:w5:data) and the smallness condition (bpW:w5:small); in the modified case also 2 beta <= p+1-p_+ for the Lipschitz parts; C_2 = 896 + 168 c_F
SOURCE_QUANTIFIERS: there exist a real holomorphic family Phi(.,xi) : D_+ = D(s-5sigma,eta r) -> D(s-4sigma,2 eta r), N_+, P_+; then for all xi in Pi
SOURCE_CONCLUSION: (i) H o Phi = N_+ + P_+ + hat a_0(xi) on D_+ with the weak conjugacy; Phi symplectic, D Phi(w) maps P^{p_+} onto itself, real, Phi(w + tau_k) = Phi(w) + tau_k; (ii) P_+ in S_{p_+}(D_+) real periodic with (bpW:w5:newerror) ¦X_{P_+}¦^lambda_{eta r,D_+} <= C_2(eps^2/(alpha sigma^t eta^2) + eta eps); (iii) ¦omega_+ - omega¦ + lambda¦.¦^L <= 6 pi eps, sup (j+2)^{p_+-p}(¦Omega_{+,j} - Omega_j¦ + lambda¦.¦^L) <= 3 eps, so (omega_+,Omega_+) satisfies (bpW:w5:freq) with M_0 + 3 eps and M_+ <= M + (6pi+3) eps/lambda (lambda > 0); (iv) for K >= 1, 0 < alpha_+ <= alpha with 6 pi (1+K)(1+K^tau) eps <= alpha - alpha_+, the divisor bounds with alpha_+ for ¦k¦_1 <= K, conditional on the same unmodified divisor bounds with alpha for the old frequencies on these modes (also with <l>^w); (v) ¦Phi - id¦^lambda_{p_+,r,D_+} <= 2 M_F and ¦D Phi - I¦^lambda_{p->p_+,r,D_+} <= 16 M_F/sigma
CONSTANT_SCOPE: C_2 = 896 + 168 c_F depends only on tau
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:data, bpW:w5:new-ham, bpW:w5:flow, bpW:w4:wave, bpW:w4:melnikov, stepW:w5:st-con, stepW:w5:st-1, stepW:w5:st-2, stepW:w5:st-freq, stepW:w5:st-div
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:data | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L566-L566 | step data and (bpW:w5:small)
EDGE: bpW:w5:new-ham | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L570-L570 | (iii) weak conjugacy
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L572-L572 | (iv)
EDGE: bpW:w4:wave | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L584-L584 | (ii) <l>^w
EDGE: bpW:w4:melnikov | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L582-L582 | Z, A_k, <l>
EDGE: stepW:w5:st-con | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L590-L590 | proof step
EDGE: stepW:w5:st-1 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L593-L593 | proof step
EDGE: stepW:w5:st-2 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L595-L595 | proof step
EDGE: stepW:w5:st-freq | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L597-L597 | proof step
EDGE: stepW:w5:st-div | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L599-L599 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: sol-delta6-W-W-w5b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.stepTheorem, KAM.Wave.stepTheoremMod, KAM.Wave.StepHypSrc, KAM.Wave.StepHypModSrc, KAM.Wave.stepFlow_bounds_smooth, KAM.Wave.stepDivisorsW, KAM.Wave.stepFreqHyp, KAM.Wave.stepDivisors (KAM/Wave/KamStep/StepTheoremSrc.lean, KAM/Wave/KamStep/StepPsi.lean, KAM/Wave/KamStep/StepDivisorsW.lean, KAM/Wave/KamStep/Divisors.lean)
LEAN_NOTE: W5-STEP-B audit 1 FAIL (F1: clause (v) in ambient norms; F2: Dirichlet-weight version of (iv) missing), W5-R2A audit 2 PASS WITH NOTES (both closed: target-norm clause (v) via the smoothing displacement Psi, homJapW divisor clause, holomorphy of Phi and the full Z^2 law appended); all other clauses (reality, D Phi onto P^{p_+}, field-form weak conjugacy, frequency corrections, modified case) W5-STEP-B audit 1 PASS; (iv) conditional on the old Melnikov condition as in the source ('whenever the same holds'); clause (iii) uses (j+2)^(p_+-p)
NOTE: -

NODE: stepW:w5:st-con
KIND: step
TITLE: Construction
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L590-L592
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L590-L592
CONTRACT_ID: stepW:w5:st-con
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:step: step data (Definition bpW:w5:data) and the smallness condition (bpW:w5:small); in the modified case also 2 beta <= p+1-p_+ for the Lipschitz parts; C_2 = 896 + 168 c_F
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:step (there exist a real holomorphic family Phi(.,xi) : D_+ = D(s-5sigma,eta r) -> D(s-4sigma,2 eta r), N_+, P_+; then for all xi in Pi); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Phi = phi^1, (i), the formula for X_{P_+}, and (v)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:taylor, bpW:w5:solve, bpW:w5:flow, bpW:w5:flow-calc, bpW:w5:new-ham
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:taylor | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L590-L590 | R
EDGE: bpW:w5:solve | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L590-L590 | F
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L590-L590 | the flow; (i)-(ii)
EDGE: bpW:w5:flow-calc | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L591-L591 | calculus
EDGE: bpW:w5:new-ham | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L591-L591 | the new Hamiltonian
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: sol-delta6-W-W-w5b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.stepTheorem, KAM.Wave.stepTheoremMod, KAM.Wave.stepNewHam_concrete, KAM.Wave.stepFlow_symplectic (KAM/Wave/KamStep/StepTheoremSrc.lean, KAM/Wave/KamStep/NewHamConcrete.lean, KAM/Wave/KamStep/StepSymplectic.lean)
LEAN_NOTE: step of PROVED parent bpW:w5:step; W5-STEP-B audit 1 PASS
NOTE: -

NODE: stepW:w5:st-1
KIND: step
TITLE: First term
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-1@L593-L594
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-1@L593-L594
CONTRACT_ID: stepW:w5:st-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:step: step data (Definition bpW:w5:data) and the smallness condition (bpW:w5:small); in the modified case also 2 beta <= p+1-p_+ for the Lipschitz parts; C_2 = 896 + 168 c_F
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:step (there exist a real holomorphic family Phi(.,xi) : D_+ = D(s-5sigma,eta r) -> D(s-4sigma,2 eta r), N_+, P_+; then for all xi in Pi); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the first term is <= 896 eta eps
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:taylor, bpW:w5:pullback
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:taylor | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-1@L594-L594 | (iv)
EDGE: bpW:w5:pullback | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-1@L594-L594 | pull-back bound
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.stepXplus_pair_bound, KAM.Wave.stepXplus_arith, KAM.Wave.stepPlus_famBound (KAM/Wave/KamStep/StepPlusBound.lean, KAM/Wave/KamStep/StepPlusArith.lean, KAM/Wave/KamStep/StepPlusFam.lean)
LEAN_NOTE: step of PROVED parent bpW:w5:step; W5-STEP-B audit 1 PASS (896 eta eps)
NOTE: -

NODE: stepW:w5:st-2
KIND: step
TITLE: Second term
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-2@L595-L596
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-2@L595-L596
CONTRACT_ID: stepW:w5:st-2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:step: step data (Definition bpW:w5:data) and the smallness condition (bpW:w5:small); in the modified case also 2 beta <= p+1-p_+ for the Lipschitz parts; C_2 = 896 + 168 c_F
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:step (there exist a real holomorphic family Phi(.,xi) : D_+ = D(s-5sigma,eta r) -> D(s-4sigma,2 eta r), N_+, P_+; then for all xi in Pi); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the second term is <= 168 c_F eps^2/(alpha sigma^t eta^2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:commutator, bpW:w5:pullback
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:commutator | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-2@L595-L595 | commutator bound
EDGE: bpW:w5:pullback | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-2@L595-L595 | pull-back bound
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.stepXplus_pair_bound, KAM.Wave.stepXplus_arith, KAM.Wave.stepCommutator_arith, KAM.Wave.stepEstimate_arith (KAM/Wave/KamStep/StepPlusBound.lean, KAM/Wave/KamStep/StepPlusArith.lean, KAM/Wave/KamStep/Pullback.lean, KAM/Wave/KamStep/Data.lean)
LEAN_NOTE: step of PROVED parent bpW:w5:step; W5-STEP-B audit 1 PASS (168 c_F eps^2/(alpha sigma^t eta^2))
NOTE: -

NODE: stepW:w5:st-freq
KIND: step
TITLE: Frequencies
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-freq@L597-L598
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-freq@L597-L598
CONTRACT_ID: stepW:w5:st-freq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:step: step data (Definition bpW:w5:data) and the smallness condition (bpW:w5:small); in the modified case also 2 beta <= p+1-p_+ for the Lipschitz parts; C_2 = 896 + 168 c_F
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:step (there exist a real holomorphic family Phi(.,xi) : D_+ = D(s-5sigma,eta r) -> D(s-4sigma,2 eta r), N_+, P_+; then for all xi in Pi); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii) from Lemma bpW:w5:solve; Lipschitz constants
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:solve
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:solve | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-freq@L597-L597 | the frequency corrections
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.stepOmegaHat_bound, KAM.Wave.stepOmegaTail_bound, KAM.Wave.stepOmegaHat_sub, KAM.Wave.stepOmegaTail_sub, KAM.Wave.stepFreqHyp (KAM/Wave/KamStep/StepFreqBound.lean, KAM/Wave/KamStep/Divisors.lean)
LEAN_NOTE: step of PROVED parent bpW:w5:step; W5-STEP-A audit 1 PASS (freq), W5-STEP-B audit 1 PASS (iii)
NOTE: -

NODE: stepW:w5:st-div
KIND: step
TITLE: Divisors
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-div@L599-L601
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-div@L599-L601
CONTRACT_ID: stepW:w5:st-div
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:step: step data (Definition bpW:w5:data) and the smallness condition (bpW:w5:small); in the modified case also 2 beta <= p+1-p_+ for the Lipschitz parts; C_2 = 896 + 168 c_F; for the modes |k|_1 <= K under consideration, the old frequencies satisfy the same unmodified divisor lower bound with alpha (L583-L584)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:step (there exist a real holomorphic family Phi(.,xi) : D_+ = D(s-5sigma,eta r) -> D(s-4sigma,2 eta r), N_+, P_+; then for all xi in Pi); within the step: ¦k¦_1 <= K; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv): the corrections shift the divisors by at most (alpha - alpha_+)<l>/A_k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:st-freq
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:st-freq | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-div@L599-L599 | the frequency corrections
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: sol-delta6-W-W-w5b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.stepDivisors, KAM.Wave.stepDivisorsW (KAM/Wave/KamStep/Divisors.lean, KAM/Wave/KamStep/StepDivisorsW.lean)
LEAN_NOTE: step of PROVED parent bpW:w5:step; W5-STEP-A audit 1 PASS, W5-R2A audit 2 PASS (Dirichlet-weight version)
NOTE: -

NODE: bpW:w5:action-angle
KIND: lemma
TITLE: Action--angle substitution
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L622-L660
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L661-L690
CONTRACT_ID: bpW:w5:action-angle
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3's normal form H' = Lambda + bar G + G^nor + K on B_{rho_1} (Theorem bpW:w3:main), W = W_{a,p}; a = p = 1; xi in C^2, w = (theta,y,u,v) in P with Re(xi_i + y_i) > 0; A_xi(w) as displayed (principal square root); (ii) 0 < s <= 1/8, r > 0, t > 0, ¦xi¦_infty <= t, Re xi_i >= 2r^2, c_A = 2200
SOURCE_QUANTIFIERS: for all such xi, w; every q in R in (iii)
SOURCE_CONCLUSION: (i) (xi,w) -> A_xi(w) holomorphic, 1-periodic in theta_i, real points to W_R; Z^{-1} A_xi(theta,0,0,0) = K^0_xi(theta) for real theta, xi in (0,infinity)^2; (ii) A_xi(D(s,r)) subset B_rho with rho^2 = c_A(t + r^2), in B_{rho_1} when c_A(t + r^2) < rho_1(m)^2; (iii) D A_xi(w) is a linear bijection P^q -> W^q with the displayed inverse, and Omega(D A_xi W, D A_xi W') = varpi(W,W') for q + q' >= 0; (iv) H' o A_xi = e(xi) + N_xi + P_xi with e(xi) = <lambda_J,xi> + (1/2)<A xi,xi>, N_xi = <omega^0(xi),y> + sum Omega^0_{j+2}(xi) z_j zbar_j, P_xi = tilde Q + G^nor o A_xi + K o A_xi; (v) P_xi in S_{p+1}(D(s,r)), real for real xi, with the displayed field, and X_{H'}(A_xi w) = D A_xi(w)(X_{N_xi}(w) + X_{P_xi}(w)) in W^{p-1}; (vi) no weight conversion is needed; ¦¦hat w¦¦ <= ¦¦u¦¦ + ¦¦v¦¦ <= sqrt2 ¦¦hat w¦¦ and ¦¦x¦¦_E <= ¦¦Zx¦¦ <= sqrt2 ¦¦x¦¦_E
CONSTANT_SCOPE: c_A = 2200 absolute
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main, bpW:w3:space, bpW:w3:omega, bpW:w5:setting, bpW:w0:periodone#linearTorus, bpW:w3:coords, bpW:w7:omega0, bpW:w4:from-w3, bpW:w5:class, stepW:w5:a-hol, stepW:w5:a-dom, stepW:w5:a-der, stepW:w5:a-nf, stepW:w5:a-field, stepW:w5:a-conj, bpW:w0:basis#lam, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L619-L619 | H' and B_{rho_1}
EDGE: bpW:w3:space | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L618-L618 | W, W^q
EDGE: bpW:w3:omega | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L618-L618 | the form Omega
EDGE: bpW:w5:setting | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L623-L623 | P and varpi
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L630-L630 | the linear torus K^0_xi
EDGE: bpW:w3:coords | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L631-L631 | Z
EDGE: bpW:w7:omega0 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L645-L645 | omega^0, Omega^0
EDGE: bpW:w4:from-w3 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L654-L654 | the weight identification
EDGE: bpW:w5:class | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L649-L649 | S_{p+1}
EDGE: stepW:w5:a-hol | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L662-L664 | proof step
EDGE: stepW:w5:a-dom | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L667-L667 | proof step
EDGE: stepW:w5:a-der | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L670-L670 | proof step
EDGE: stepW:w5:a-nf | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L674-L674 | proof step
EDGE: stepW:w5:a-field | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L678-L678 | proof step
EDGE: stepW:w5:a-conj | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L684-L684 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L643-L643 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L658-L658 | the frozen WaveSpace occurs directly here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The pointer to Proposition bpW:w5:initial in (vi) is a forward pointer; not an edge.

NODE: stepW:w5:a-hol
KIND: step
TITLE: Holomorphy and reality
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-hol@L662-L666
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-hol@L662-L666
CONTRACT_ID: stepW:w5:a-hol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:action-angle: W3's normal form H' = Lambda + bar G + G^nor + K on B_{rho_1} (Theorem bpW:w3:main), W = W_{a,p}; a = p = 1; xi in C^2, w = (theta,y,u,v) in P with Re(xi_i + y_i) > 0; A_xi(w) as displayed (principal square root); (ii) 0 < s <= 1/8, r > 0, t > 0, ¦xi¦_infty <= t, Re xi_i >= 2r^2, c_A = 2200
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:action-angle (for all such xi, w; every q in R in (iii)); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i) holomorphy, reality and the linear torus
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:periodone#linearTorus, bpW:w3:coords, bpW:w5:ext-sqrt
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-hol@L665-L665 | the displayed recovered q_i,p_i are the frozen linear torus
EDGE: bpW:w3:coords | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-hol@L665-L665 | the inverse Z coordinate map is used to recover q_i,p_i
EDGE: bpW:w5:ext-sqrt | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-hol@L663-L663 | principal square root holomorphic on Re > 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b+claude-suborch-W-gapfix
REVIEWER: sol-delta7-W-w5b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:a-dom
KIND: step
TITLE: Domain
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-dom@L667-L669
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-dom@L667-L669
CONTRACT_ID: stepW:w5:a-dom
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:action-angle: W3's normal form H' = Lambda + bar G + G^nor + K on B_{rho_1} (Theorem bpW:w3:main), W = W_{a,p}; a = p = 1; xi in C^2, w = (theta,y,u,v) in P with Re(xi_i + y_i) > 0; A_xi(w) as displayed (principal square root); (ii) 0 < s <= 1/8, r > 0, t > 0, ¦xi¦_infty <= t, Re xi_i >= 2r^2, c_A = 2200
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:action-angle (for all such xi, w; every q in R in (iii)); within the step: w in D(s,r); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) the tangential part is <= 2173(t + r^2), the normal part < r^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:a-der
KIND: step
TITLE: Derivative
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-der@L670-L673
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-der@L670-L673
CONTRACT_ID: stepW:w5:a-der
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:action-angle: W3's normal form H' = Lambda + bar G + G^nor + K on B_{rho_1} (Theorem bpW:w3:main), W = W_{a,p}; a = p = 1; xi in C^2, w = (theta,y,u,v) in P with Re(xi_i + y_i) > 0; A_xi(w) as displayed (principal square root); (ii) 0 < s <= 1/8, r > 0, t > 0, ¦xi¦_infty <= t, Re xi_i >= 2r^2, c_A = 2200
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:action-angle (for all such xi, w; every q in R in (iii)); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii) the inverse of D A and the form identity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:index
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-der@L673-L673 | (bpW:w4:pairing)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:a-nf
KIND: step
TITLE: Normal form
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L674-L677
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L674-L677
CONTRACT_ID: stepW:w5:a-nf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:action-angle: W3's normal form H' = Lambda + bar G + G^nor + K on B_{rho_1} (Theorem bpW:w3:main), W = W_{a,p}; a = p = 1; xi in C^2, w = (theta,y,u,v) in P with Re(xi_i + y_i) > 0; A_xi(w) as displayed (principal square root); (ii) 0 < s <= 1/8, r > 0, t > 0, ¦xi¦_infty <= t, Re xi_i >= 2r^2, c_A = 2200
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:action-angle (for all such xi, w; every q in R in (iii)); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv) by substituting w_i w_{-i} = xi_i + y_i into Lambda and bar G
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main, bpW:w0n:AB, bpW:w3:Lambda, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L676-L676 | (iii) bar G
EDGE: bpW:w0n:AB | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L676-L676 | A, B
EDGE: bpW:w3:Lambda | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L675-L675 | Lambda
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L675-L675 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:a-field
KIND: step
TITLE: Fields
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L678-L683
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L678-L683
CONTRACT_ID: stepW:w5:a-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:action-angle: W3's normal form H' = Lambda + bar G + G^nor + K on B_{rho_1} (Theorem bpW:w3:main), W = W_{a,p}; a = p = 1; xi in C^2, w = (theta,y,u,v) in P with Re(xi_i + y_i) > 0; A_xi(w) as displayed (principal square root); (ii) 0 < s <= 1/8, r > 0, t > 0, ¦xi¦_infty <= t, Re xi_i >= 2r^2, c_A = 2200
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:action-angle (for all such xi, w; every q in R in (iii)); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (v) the field of P_xi lies in P^{p+1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main, stepW:w5:a-der, bpW:w0:basis#lam, bpW:w0:basis#lambda-facts
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L678-L678 | (ii)-(iii) fields into W+
EDGE: stepW:w5:a-der | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L679-L679 | (iii)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L681-L681 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L682-L682 | J/lambda_J <= 1 gives the one-weight smoothing multiplier bound
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: sol-delta6-W-W-w5b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:a-conj
KIND: step
TITLE: Conjugacy
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L684-L689
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L684-L689
CONTRACT_ID: stepW:w5:a-conj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:action-angle: W3's normal form H' = Lambda + bar G + G^nor + K on B_{rho_1} (Theorem bpW:w3:main), W = W_{a,p}; a = p = 1; xi in C^2, w = (theta,y,u,v) in P with Re(xi_i + y_i) > 0; A_xi(w) as displayed (principal square root); (ii) 0 < s <= 1/8, r > 0, t > 0, ¦xi¦_infty <= t, Re xi_i >= 2r^2, c_A = 2200
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:action-angle (for all such xi, w; every q in R in (iii)); within the step: w, W; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (v) the conjugacy identity in W^{p-1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:Lambda, stepW:w5:a-nf, bpW:w5:new-ham, stepW:w5:a-der, bpW:w3:omega
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:Lambda | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L686-L686 | D Lambda(w')W'' = Omega(X_Lambda(w'),W'')
EDGE: stepW:w5:a-nf | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L686-L686 | (iv)
EDGE: bpW:w5:new-ham | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L686-L686 | (iii)'s computation for N_xi
EDGE: stepW:w5:a-der | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L688-L688 | (iii)
EDGE: bpW:w3:omega | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L689-L689 | nondegeneracy
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:initial
KIND: proposition
TITLE: The initial perturbation; KP96 \S7, Step~3
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L696-L705
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L706-L726
CONTRACT_ID: bpW:w5:initial
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0, a = p = 1; rho_1, C_*, C'_K W3's constants; 0 < s <= 1/8, 0 < r <= 1, t > 0, rho_xi > 0, Pi subset R^2 such that every zeta in C^2 with ¦zeta - xi¦_infty < rho_xi for some xi in Pi satisfies Re zeta_i >= 2r^2 and ¦zeta¦_infty <= t, and c_A(t + r^2) < rho_1^2; eps_in as displayed
SOURCE_QUANTIFIERS: for every lambda >= 0
SOURCE_CONCLUSION: P_xi in S_{p+1}(D(s,r)) is a real periodic family on Pi and ¦X_P¦^lambda_{r,D(s,r)} <= eps_in(1 + 4 lambda/rho_xi); omega^0, Omega^0_{j+2} satisfy (bpW:w4:freq) (hence (bpW:w5:freq)) with the constants of Lemma bpW:w4:wave and ¦omega^0(xi) - omega^0(xi')¦ <= N_A ¦xi - xi'¦
CONSTANT_SCOPE: eps_in explicit in r, t, C_*, C'_K, c_A
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main, bpW:w3:majorant, bpW:w5:action-angle, bpW:w4:wave, stepW:w5:i-q, stepW:w5:i-g, stepW:w5:i-k, stepW:w5:i-par, stepW:w5:i-freq, bpW:w7:freqcoords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L697-L697 | rho_1, C'_K
EDGE: bpW:w3:majorant | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L697-L697 | C_*
EDGE: bpW:w5:action-angle | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L701-L701 | P_xi
EDGE: bpW:w4:wave | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L704-L704 | the frequency constants
EDGE: stepW:w5:i-q | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L707-L707 | proof step
EDGE: stepW:w5:i-g | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L712-L712 | proof step
EDGE: stepW:w5:i-k | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L715-L715 | proof step
EDGE: stepW:w5:i-par | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L720-L720 | proof step
EDGE: stepW:w5:i-freq | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L725-L725 | proof step
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L704-L704 | N_A in the stated Lipschitz conclusion is the norm of A defined by freqcoords(ii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: sol-delta6-W-W-w5b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:i-q
KIND: step
TITLE: The polynomial part
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-q@L707-L711
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-q@L707-L711
CONTRACT_ID: stepW:w5:i-q
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:initial: m > 0, a = p = 1; rho_1, C_*, C'_K W3's constants; 0 < s <= 1/8, 0 < r <= 1, t > 0, rho_xi > 0, Pi subset R^2 such that every zeta in C^2 with ¦zeta - xi¦_infty < rho_xi for some xi in Pi satisfies Re zeta_i >= 2r^2 and ¦zeta¦_infty <= t, and c_A(t + r^2) < rho_1^2; eps_in as displayed
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:initial (for every lambda >= 0); within the step: w in D(s,r); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the field of tilde Q is <= r^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:freqcoords, bpW:w4:index
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-q@L708-L708 | (ii) N_A <= 3/5
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-q@L709-L709 | (bpW:w4:zu)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:i-g
KIND: step
TITLE: $G^{\rm nor}$
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-g@L712-L714
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-g@L712-L714
CONTRACT_ID: stepW:w5:i-g
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:initial: m > 0, a = p = 1; rho_1, C_*, C'_K W3's constants; 0 < s <= 1/8, 0 < r <= 1, t > 0, rho_xi > 0, Pi subset R^2 such that every zeta in C^2 with ¦zeta - xi¦_infty < rho_xi for some xi in Pi satisfies Re zeta_i >= 2r^2 and ¦zeta¦_infty <= t, and c_A(t + r^2) < rho_1^2; eps_in as displayed
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:initial (for every lambda >= 0); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the G^nor contribution is <= 2 C_* r^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main, bpW:w5:action-angle
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-g@L713-L713 | (iii)
EDGE: bpW:w5:action-angle | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-g@L714-L714 | (iii) inverse formula
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:i-k
KIND: step
TITLE: $K$
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-k@L715-L719
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-k@L715-L719
CONTRACT_ID: stepW:w5:i-k
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:initial: m > 0, a = p = 1; rho_1, C_*, C'_K W3's constants; 0 < s <= 1/8, 0 < r <= 1, t > 0, rho_xi > 0, Pi subset R^2 such that every zeta in C^2 with ¦zeta - xi¦_infty < rho_xi for some xi in Pi satisfies Re zeta_i >= 2r^2 and ¦zeta¦_infty <= t, and c_A(t + r^2) < rho_1^2; eps_in as displayed
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:initial (for every lambda >= 0); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the K contribution
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main, bpW:w5:action-angle
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-k@L715-L715 | (ii) ¦¦X_K¦¦ <= C'_K ¦¦w¦¦^5
EDGE: bpW:w5:action-angle | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-k@L715-L715 | (ii), (iii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:i-par
KIND: step
TITLE: Parameters
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-par@L720-L724
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-par@L720-L724
CONTRACT_ID: stepW:w5:i-par
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:initial: m > 0, a = p = 1; rho_1, C_*, C'_K W3's constants; 0 < s <= 1/8, 0 < r <= 1, t > 0, rho_xi > 0, Pi subset R^2 such that every zeta in C^2 with ¦zeta - xi¦_infty < rho_xi for some xi in Pi satisfies Re zeta_i >= 2r^2 and ¦zeta¦_infty <= t, and c_A(t + r^2) < rho_1^2; eps_in as displayed
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:initial (for every lambda >= 0); within the step: xi, xi'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the Lipschitz constant 4 eps_in/rho_xi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-par@L723-L723 | Cauchy estimate in xi
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:i-freq
KIND: step
TITLE: Frequencies
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-freq@L725-L725
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-freq@L725-L725
CONTRACT_ID: stepW:w5:i-freq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:initial: m > 0, a = p = 1; rho_1, C_*, C'_K W3's constants; 0 < s <= 1/8, 0 < r <= 1, t > 0, rho_xi > 0, Pi subset R^2 such that every zeta in C^2 with ¦zeta - xi¦_infty < rho_xi for some xi in Pi satisfies Re zeta_i >= 2r^2 and ¦zeta¦_infty <= t, and c_A(t + r^2) < rho_1^2; eps_in as displayed
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:initial (for every lambda >= 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the frequency conditions
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:wave, bpW:w7:freqcoords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:wave | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-freq@L725-L725 | (i)
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-freq@L725-L725 | (ii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:newham-sec#bracket
KIND: definition
TITLE: Poisson bracket and field commutator
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:newham-sec@L471-L472
PROOF_SOURCE: -
CONTRACT_ID: bpW:w5:newham-sec#bracket
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G C^1, X_F a field; G, F in W4's class T
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines {G,F} = DG . X_F and [X_G,X_F] = DX_G . X_F - DX_F . X_G
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:taylor
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:taylor | blueprint-W/parts/w5-kamstep.tex#bpW:w5:newham-sec@L472-L472 | the class T
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.hasFDerivAt_bracket, KAM.Wave.stepBrG, KAM.Wave.stepBrZ (KAM/Wave/KamStep/FlowSkew.lean, KAM/Wave/KamStep/StepBracket.lean)
LEAN_NOTE: definition formalized by W5-STEP (bracket function stepBrG = DG.X_F and field stepBrZ with the sign DX_G X_F - DX_F X_G); W5-STEP-A audit 1 PASS (hasFDerivAt_bracket), W5-STEP-B audit 1 PASS; (mapping inferred)
NOTE: Unlabelled prose L471-L472 fixing notation used by Lemmas bpW:w5:new-ham and bpW:w5:commutator.
