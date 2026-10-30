NODE: bpW:w5:new-ham
KIND: lemma
TITLE: New Hamiltonian; conjugacy
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L457-L472
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L473-L493
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
DEPS: bpW:w5:flow, bpW:w5:newham-sec#bracket, bpW:w5:solve, bpW:w4:lie, bpW:w4:index, bpW:w5:class, stepW:w5:n-exp, stepW:w5:n-br, stepW:w5:n-field, stepW:w5:n-conj, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L458-L458 | the flow and its setting
EDGE: bpW:w5:newham-sec#bracket | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L461-L461 | {R(t),F}
EDGE: bpW:w5:solve | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L459-L459 | hat N, hat omega, hat Omega
EDGE: bpW:w4:lie | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L469-L469 | (i) X_N
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L470-L470 | (bpW:w4:pairing)
EDGE: bpW:w5:class | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L464-L464 | S_{p_+}
EDGE: stepW:w5:n-exp | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L474-L474 | proof step
EDGE: stepW:w5:n-br | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L481-L481 | proof step
EDGE: stepW:w5:n-field | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L485-L485 | proof step
EDGE: stepW:w5:n-conj | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L488-L488 | proof step
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L458-L458 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:n-exp
KIND: step
TITLE: Expansion
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L474-L480
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L474-L480
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
DEPS: bpW:w5:flow, bpW:w5:flow-calc, bpW:w5:ext-ftc, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L475-L475 | (iii)
EDGE: bpW:w5:flow-calc | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L475-L475 | (v)
EDGE: bpW:w5:ext-ftc | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L475-L475 | calculus along curves
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L474-L474 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:n-br
KIND: step
TITLE: Bracket field
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-br@L481-L484
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-br@L481-L484
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
EDGE: stepW:w5:c-skew | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-br@L483-L483 | skewness of DX
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:n-field
KIND: step
TITLE: Field of $P_+$
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-field@L485-L487
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-field@L485-L487
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
EDGE: bpW:w5:flow-calc | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-field@L485-L485 | (iv) transport, (i) continuity
EDGE: stepW:w5:n-br | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-field@L486-L486 | the bracket field
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-field@L486-L486 | differentiation under the t-integral
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:n-conj
KIND: step
TITLE: Conjugacy
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-conj@L488-L492
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-conj@L488-L492
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
EDGE: bpW:w4:lie | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-conj@L491-L491 | (i) convergence of the pairings
EDGE: stepW:w5:n-field | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-conj@L492-L492 | (ii)
EDGE: stepW:w5:n-exp | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-conj@L488-L488 | (i) H o Phi = N_+ + P_+ + hat a_0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:pullback
KIND: lemma
TITLE: Pull-back; P96-K (12)
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L502-L506
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L507-L522
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
DEPS: bpW:w5:flow, stepW:w5:p-inv, stepW:w5:p-dy, stepW:w5:p-ass, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L503-L503 | the setting
EDGE: stepW:w5:p-inv | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L508-L508 | proof step
EDGE: stepW:w5:p-dy | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L514-L514 | proof step
EDGE: stepW:w5:p-ass | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L517-L517 | proof step
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L505-L505 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:p-inv
KIND: step
TITLE: Inverse in the small scale
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L508-L513
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L508-L513
CONTRACT_ID: stepW:w5:p-inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:pullback: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F); Y(.,xi) holomorphic fields D(s-3sigma,4 eta r) -> P^{p_+}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:pullback (for ¦t¦ <= 1); within the step: W; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦D(phi^t)^{-1}¦_{p_+->p_+,eta r} <= 2 and lambda¦Delta(D phi^t)^{-1}¦ <= 4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:omega, bpW:w5:flow, stepW:w5:f-der, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:omega | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L509-L509 | norm comparisons
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L509-L509 | (ii)
EDGE: stepW:w5:f-der | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L512-L512 | the parameter bound
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L510-L510 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:p-dy
KIND: step
TITLE: Derivative of $Y$
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-dy@L514-L516
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-dy@L514-L516
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
EDGE: bpW:w1:kam-domain | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-dy@L514-L514 | margins
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-dy@L516-L516 | Cauchy estimate
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:p-ass
KIND: step
TITLE: Assemble
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L517-L521
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L517-L521
CONTRACT_ID: stepW:w5:p-ass
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:pullback: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F); Y(.,xi) holomorphic fields D(s-3sigma,4 eta r) -> P^{p_+}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:pullback (for ¦t¦ <= 1); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the total bound 7 ¦Y¦^lambda
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:p-inv, stepW:w5:p-dy, bpW:w5:lambda-product, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:p-inv | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L517-L517 | inverse bounds
EDGE: stepW:w5:p-dy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L519-L519 | derivative of Y
EDGE: bpW:w5:lambda-product | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L518-L518 | lambda-norm of products
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L517-L517 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:commutator
KIND: lemma
TITLE: Commutators
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L526-L529
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L530-L538
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
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L527-L527 | the setting
EDGE: bpW:w5:newham-sec#bracket | blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L528-L528 | the commutator
EDGE: stepW:w5:k-cauchy | blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L531-L531 | proof step
EDGE: stepW:w5:k-bd | blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L534-L534 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:k-cauchy
KIND: step
TITLE: Cauchy
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-cauchy@L531-L533
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-cauchy@L531-L533
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
EDGE: bpW:w1:kam-domain | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-cauchy@L532-L532 | margins
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-cauchy@L533-L533 | Cauchy
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:k-bd
KIND: step
TITLE: Bound
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L534-L537
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L534-L537
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
EDGE: bpW:w5:taylor | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L535-L535 | ¦X_R¦ <= 3 eps
EDGE: bpW:w5:solve | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L535-L535 | ¦X_{hat N}¦ <= 6 eps, ¦X_F¦ <= M_F
EDGE: bpW:w5:lambda-product | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L535-L535 | submultiplicativity
EDGE: stepW:w5:k-cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L536-L536 | derivative bounds
EDGE: bpW:w5:omega | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L537-L537 | ¦.¦_{eta r} <= eta^{-2}¦.¦_r
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:step
KIND: theorem
TITLE: One KAM step
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L543-L566
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L567-L580
CONTRACT_ID: bpW:w5:step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: step data (Definition bpW:w5:data) and the smallness condition (bpW:w5:small); in the modified case also 2 beta <= p+1-p_+ for the Lipschitz parts; C_2 = 896 + 168 c_F
SOURCE_QUANTIFIERS: there exist a real holomorphic family Phi(.,xi) : D_+ = D(s-5sigma,eta r) -> D(s-4sigma,2 eta r), N_+, P_+; then for all xi in Pi
SOURCE_CONCLUSION: (i) H o Phi = N_+ + P_+ + hat a_0(xi) on D_+ with the weak conjugacy; Phi symplectic, D Phi(w) maps P^{p_+} onto itself, real, Phi(w + tau_k) = Phi(w) + tau_k; (ii) P_+ in S_{p_+}(D_+) real periodic with (bpW:w5:newerror) ¦X_{P_+}¦^lambda_{eta r,D_+} <= C_2(eps^2/(alpha sigma^t eta^2) + eta eps); (iii) ¦omega_+ - omega¦ + lambda¦.¦^L <= 6 pi eps, sup (j+2)^{p_+-p}(¦Omega_{+,j} - Omega_j¦ + lambda¦.¦^L) <= 3 eps, so (omega_+,Omega_+) satisfies (bpW:w5:freq) with M_0 + 3 eps and M_+ <= M + (6pi+3) eps/lambda (lambda > 0); (iv) for K >= 1, 0 < alpha_+ <= alpha with 6 pi (1+K)(1+K^tau) eps <= alpha - alpha_+, the divisor bounds with alpha_+ for ¦k¦_1 <= K (also with <l>^w); (v) ¦Phi - id¦^lambda_{p_+,r,D_+} <= 2 M_F and ¦D Phi - I¦^lambda_{p->p_+,r,D_+} <= 16 M_F/sigma
CONSTANT_SCOPE: C_2 = 896 + 168 c_F depends only on tau
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:data, bpW:w5:new-ham, bpW:w5:flow, bpW:w4:wave, bpW:w4:melnikov, stepW:w5:st-con, stepW:w5:st-1, stepW:w5:st-2, stepW:w5:st-freq, stepW:w5:st-div, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:data | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L544-L544 | step data and (bpW:w5:small)
EDGE: bpW:w5:new-ham | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L548-L548 | (iii) weak conjugacy
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L550-L550 | (iv)
EDGE: bpW:w4:wave | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L562-L562 | (ii) <l>^w
EDGE: bpW:w4:melnikov | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L560-L560 | Z, A_k, <l>
EDGE: stepW:w5:st-con | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L568-L568 | proof step
EDGE: stepW:w5:st-1 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L571-L571 | proof step
EDGE: stepW:w5:st-2 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L573-L573 | proof step
EDGE: stepW:w5:st-freq | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L575-L575 | proof step
EDGE: stepW:w5:st-div | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L577-L577 | proof step
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L569-L569 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:st-con
KIND: step
TITLE: Construction
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L568-L570
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L568-L570
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
DEPS: bpW:w5:taylor, bpW:w5:solve, bpW:w5:flow, bpW:w5:flow-calc, bpW:w5:new-ham, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:taylor | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L568-L568 | R
EDGE: bpW:w5:solve | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L568-L568 | F
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L568-L568 | the flow; (i)-(ii)
EDGE: bpW:w5:flow-calc | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L569-L569 | calculus
EDGE: bpW:w5:new-ham | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L569-L569 | the new Hamiltonian
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L569-L569 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:st-1
KIND: step
TITLE: First term
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-1@L571-L572
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-1@L571-L572
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
EDGE: bpW:w5:taylor | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-1@L572-L572 | (iv)
EDGE: bpW:w5:pullback | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-1@L572-L572 | pull-back bound
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:st-2
KIND: step
TITLE: Second term
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-2@L573-L574
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-2@L573-L574
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
EDGE: bpW:w5:commutator | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-2@L573-L573 | commutator bound
EDGE: bpW:w5:pullback | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-2@L573-L573 | pull-back bound
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:st-freq
KIND: step
TITLE: Frequencies
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-freq@L575-L576
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-freq@L575-L576
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
EDGE: bpW:w5:solve | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-freq@L575-L575 | the frequency corrections
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:st-div
KIND: step
TITLE: Divisors
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-div@L577-L579
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-div@L577-L579
CONTRACT_ID: stepW:w5:st-div
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:step: step data (Definition bpW:w5:data) and the smallness condition (bpW:w5:small); in the modified case also 2 beta <= p+1-p_+ for the Lipschitz parts; C_2 = 896 + 168 c_F
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
EDGE: stepW:w5:st-freq | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-div@L577-L577 | the frequency corrections
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:action-angle
KIND: lemma
TITLE: Action--angle substitution
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L600-L638
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L639-L667
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
EDGE: bpW:w3:main | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L597-L597 | H' and B_{rho_1}
EDGE: bpW:w3:space | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L596-L596 | W, W^q
EDGE: bpW:w3:omega | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L596-L596 | the form Omega
EDGE: bpW:w5:setting | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L601-L601 | P and varpi
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L608-L608 | the linear torus K^0_xi
EDGE: bpW:w3:coords | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L609-L609 | Z
EDGE: bpW:w7:omega0 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L623-L623 | omega^0, Omega^0
EDGE: bpW:w4:from-w3 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L632-L632 | the weight identification
EDGE: bpW:w5:class | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L627-L627 | S_{p+1}
EDGE: stepW:w5:a-hol | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L640-L640 | proof step
EDGE: stepW:w5:a-dom | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L644-L644 | proof step
EDGE: stepW:w5:a-der | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L647-L647 | proof step
EDGE: stepW:w5:a-nf | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L651-L651 | proof step
EDGE: stepW:w5:a-field | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L655-L655 | proof step
EDGE: stepW:w5:a-conj | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L661-L661 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L621-L621 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L636-L636 | the frozen WaveSpace occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The pointer to Proposition bpW:w5:initial in (vi) is a forward pointer; not an edge.

NODE: stepW:w5:a-hol
KIND: step
TITLE: Holomorphy and reality
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-hol@L640-L643
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-hol@L640-L643
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
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:a-dom
KIND: step
TITLE: Domain
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-dom@L644-L646
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-dom@L644-L646
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:a-der
KIND: step
TITLE: Derivative
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-der@L647-L650
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-der@L647-L650
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
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-der@L650-L650 | (bpW:w4:pairing)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:a-nf
KIND: step
TITLE: Normal form
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L651-L654
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L651-L654
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
EDGE: bpW:w3:main | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L653-L653 | (iii) bar G
EDGE: bpW:w0n:AB | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L653-L653 | A, B
EDGE: bpW:w3:Lambda | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L652-L652 | Lambda
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L652-L652 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:a-field
KIND: step
TITLE: Fields
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L655-L660
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L655-L660
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
DEPS: bpW:w3:main, stepW:w5:a-der, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L655-L655 | (ii)-(iii) fields into W+
EDGE: stepW:w5:a-der | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L656-L656 | (iii)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L658-L658 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:a-conj
KIND: step
TITLE: Conjugacy
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L661-L666
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L661-L666
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
EDGE: bpW:w3:Lambda | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L663-L663 | D Lambda(w')W'' = Omega(X_Lambda(w'),W'')
EDGE: stepW:w5:a-nf | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L663-L663 | (iv)
EDGE: bpW:w5:new-ham | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L663-L663 | (iii)'s computation for N_xi
EDGE: stepW:w5:a-der | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L665-L665 | (iii)
EDGE: bpW:w3:omega | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L666-L666 | nondegeneracy
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:initial
KIND: proposition
TITLE: The initial perturbation; KP96 \S7, Step~3
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L673-L682
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L683-L703
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
DEPS: bpW:w3:main, bpW:w3:majorant, bpW:w5:action-angle, bpW:w4:wave, stepW:w5:i-q, stepW:w5:i-g, stepW:w5:i-k, stepW:w5:i-par, stepW:w5:i-freq
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L674-L674 | rho_1, C'_K
EDGE: bpW:w3:majorant | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L674-L674 | C_*
EDGE: bpW:w5:action-angle | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L678-L678 | P_xi
EDGE: bpW:w4:wave | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L681-L681 | the frequency constants
EDGE: stepW:w5:i-q | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L684-L684 | proof step
EDGE: stepW:w5:i-g | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L689-L689 | proof step
EDGE: stepW:w5:i-k | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L692-L692 | proof step
EDGE: stepW:w5:i-par | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L697-L697 | proof step
EDGE: stepW:w5:i-freq | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L702-L702 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:i-q
KIND: step
TITLE: The polynomial part
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-q@L684-L688
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-q@L684-L688
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
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-q@L685-L685 | (ii) N_A <= 3/5
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-q@L686-L686 | (bpW:w4:zu)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:i-g
KIND: step
TITLE: $G^{\rm nor}$
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-g@L689-L691
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-g@L689-L691
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
EDGE: bpW:w3:main | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-g@L690-L690 | (iii)
EDGE: bpW:w5:action-angle | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-g@L691-L691 | (iii) inverse formula
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:i-k
KIND: step
TITLE: $K$
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-k@L692-L696
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-k@L692-L696
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
EDGE: bpW:w3:main | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-k@L692-L692 | (ii) ¦¦X_K¦¦ <= C'_K ¦¦w¦¦^5
EDGE: bpW:w5:action-angle | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-k@L692-L692 | (ii), (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:i-par
KIND: step
TITLE: Parameters
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-par@L697-L701
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-par@L697-L701
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
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-par@L700-L700 | Cauchy estimate in xi
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:i-freq
KIND: step
TITLE: Frequencies
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-freq@L702-L702
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-freq@L702-L702
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
EDGE: bpW:w4:wave | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-freq@L702-L702 | (i)
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-freq@L702-L702 | (ii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:newham-sec#bracket
KIND: definition
TITLE: Poisson bracket and field commutator
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:newham-sec@L454-L455
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
EDGE: bpW:w4:taylor | blueprint-W/parts/w5-kamstep.tex#bpW:w5:newham-sec@L455-L455 | the class T
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled prose L454-L455 fixing notation used by Lemmas bpW:w5:new-ham and bpW:w5:commutator.
