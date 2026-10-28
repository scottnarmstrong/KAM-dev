NODE: bpP:p14:sb-x-alg
KIND: external
TITLE: bpP:p14:sb-x-alg
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-x-alg@L36-L36
PROOF_SOURCE: -
CONTRACT_ID: bpP:p14:sb-x-alg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: real numbers, vectors c(F)=(cos F,sin F), rotations R_theta of R^2
SOURCE_QUANTIFIERS: universally over the real numbers, finite-dimensional vectors, sets, functions and parameters in the displayed facts, subject to their stated differentiability, continuity, compactness, positivity or periodicity conditions
SOURCE_CONCLUSION: sqrt is increasing and sqrt(y)^2=y for y>=0; ¦c(F)¦=1, c(F+2pi)=c(F), R_theta c(F)=c(F+theta); rotations preserve the dot product and the norm and commute with J_0; norm_num and linear_combination for rational identities and polynomial identities modulo relations
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external item (X1)

NODE: bpP:p14:sb-x-top
KIND: external
TITLE: bpP:p14:sb-x-top
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-x-top@L37-L37
PROOF_SOURCE: -
CONTRACT_ID: bpP:p14:sb-x-top
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: subsets of R^N; continuous functions
SOURCE_QUANTIFIERS: universally over the real numbers, finite-dimensional vectors, sets, functions and parameters in the displayed facts, subject to their stated differentiability, continuity, compactness, positivity or periodicity conditions
SOURCE_CONCLUSION: open sets are closed under finite intersections and continuous preimages; closed bounded sets of R^N are compact; a continuous function on a compact set is bounded; a continuous function on an open set that is positive on a compact K is bounded below on K; intervals are connected and a nonempty open and closed subset of a connected set is all of it
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external item (X2)

NODE: bpP:p14:sb-x-int
KIND: external
TITLE: bpP:p14:sb-x-int
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-x-int@L38-L38
PROOF_SOURCE: -
CONTRACT_ID: bpP:p14:sb-x-int
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: continuous functions on compact boxes; periodic functions
SOURCE_QUANTIFIERS: universally over the real numbers, finite-dimensional vectors, sets, functions and parameters in the displayed facts, subject to their stated differentiability, continuity, compactness, positivity or periodicity conditions
SOURCE_CONCLUSION: continuous functions are integrable on compact boxes; Fubini on Delta; for continuous g of period 2pi the integral of g(s-theta) over [0,2pi] equals that of g; fundamental theorem of calculus: t -> integral_0^t f has derivative f(t) if f is continuous
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external item (X3)

NODE: bpP:p14:sb-x-calc
KIND: external
TITLE: bpP:p14:sb-x-calc
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-x-calc@L40-L40
PROOF_SOURCE: -
CONTRACT_ID: bpP:p14:sb-x-calc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: real-variable calculus
SOURCE_QUANTIFIERS: universally over the real numbers, finite-dimensional vectors, sets, functions and parameters in the displayed facts, subject to their stated differentiability, continuity, compactness, positivity or periodicity conditions
SOURCE_CONCLUSION: chain rule; a C^k function composed with an affine map is C^k; a continuous function on an interval with derivative 0 at every point is constant; HasDerivAt for pairs and R^N-valued functions holds iff it holds coordinatewise; if H(z+s b)=H(z) for all s and H is differentiable at z then DH(z)b=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external item (X5)

NODE: bpP:p14:sb-conv#secularGamma
KIND: definition
TITLE: prose transcription: KAM.Planetary.secularGamma
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L26-L26
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.secularGamma
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): w in Phase(2+2) with w=((lambda,xi),(Lambda,eta)); u_i=(xi_i,eta_i)
SOURCE_QUANTIFIERS: w in Phase(2+2); output indexed by i in Fin 2
SOURCE_CONCLUSION: defines secularGamma w : Fin 2 -> R, Gamma_i=oscillatorAction(slow w_2)(slow w_1)=(xi_i^2+eta_i^2)/2=¦u_i¦^2/2
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/SecularGamma.lean
FROZEN_DECL: KAM.Planetary.secularGamma
FROZEN_ANCHOR_ID: planetary.d25.secularGamma.v1
FROZEN_ABI_SHA256: f1a010bd9ac0553ef49ce150d86aa256931c177b728a74f1defe37a11d5c9636
DEPS: bpP:p0:oscaction#oscillatorAction, bpP:p0:blocks#slow, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:oscaction#oscillatorAction | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L26-L26 | Gamma_i is the frozen oscillator action
EDGE: bpP:p0:blocks#slow | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L25-L25 | xi=slow w_1, eta=slow w_2
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L25-L25 | w in Phase(2+2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.secularGamma (KAM/Frozen/Planetary/Defs/SecularGamma.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: frozen definition transcribed in the unlabelled prose of 14b 'Conventions' (texttt name, no frozen tag); anchor bound by the SPEC

NODE: bpP:p14:sb-conv#secularAMD
KIND: definition
TITLE: prose transcription: KAM.Planetary.secularAMD
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L26-L26
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.secularAMD
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): w in Phase(2+2)
SOURCE_QUANTIFIERS: w in Phase(2+2)
SOURCE_CONCLUSION: defines secularAMD w = Gamma_0+Gamma_1 (the AMD A)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/SecularAMD.lean
FROZEN_DECL: KAM.Planetary.secularAMD
FROZEN_ANCHOR_ID: planetary.d25.secularAMD.v1
FROZEN_ABI_SHA256: ce3fdef4d7d891d8e81df40781062345603aed1e160d857d0386c752b3f85027
DEPS: bpP:p14:sb-conv#secularGamma, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L26-L26 | Gamma_i
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L25-L25 | w in Phase(2+2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.secularAMD (KAM/Frozen/Planetary/Defs/SecularAMD.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: frozen definition transcribed in the unlabelled prose of 14b 'Conventions' (texttt name, no frozen tag); anchor bound by the SPEC

NODE: bpP:p14:sb-conv#secularRoot
KIND: definition
TITLE: prose transcription: KAM.Planetary.secularRoot
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L26-L26
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.secularRoot
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): w in Phase(2+2), i in {0,1}
SOURCE_QUANTIFIERS: w in Phase(2+2), then i in Fin 2
SOURCE_CONCLUSION: defines secularRoot w i = k_i = 1-Gamma_i/Lambda_i (total Lean function; used only where Lambda_i>0, Gamma_i<Lambda_i)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/SecularRoot.lean
FROZEN_DECL: KAM.Planetary.secularRoot
FROZEN_ANCHOR_ID: planetary.d25.secularRoot.v1
FROZEN_ABI_SHA256: eff81429f1e4d4fb40045583cee0826d2fb317460aa07fdcdebc1636e6365957
DEPS: bpP:p14:sb-conv#secularGamma, bpP:p0:blocks#fast, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L26-L26 | Gamma_i
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L25-L25 | Lambda_i=fast w_2 i
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L25-L25 | w in Phase(2+2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.secularRoot (KAM/Frozen/Planetary/Defs/SecularRoot.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: frozen definition transcribed in the unlabelled prose of 14b 'Conventions' (texttt name, no frozen tag); anchor bound by the SPEC

NODE: bpP:p14:sb-conv#secularEccVector
KIND: definition
TITLE: prose transcription: KAM.Planetary.secularEccVector
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L27-L27
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.secularEccVector
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): w in Phase(2+2), i in {0,1}
SOURCE_QUANTIFIERS: w in Phase(2+2), then i in Fin 2
SOURCE_CONCLUSION: defines secularEccVector w i = v_i=rho_i u_i with rho_i=sqrt((1-Gamma_i/(2Lambda_i))/Lambda_i), e_i=¦v_i¦
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/SecularEccVector.lean
FROZEN_DECL: KAM.Planetary.secularEccVector
FROZEN_ANCHOR_ID: planetary.d25.secularEccVector.v1
FROZEN_ABI_SHA256: 3039bf17fef4d9de415e97e53d69869a5a86a83384d78fd35a59467a684100c8
DEPS: bpP:p14:sb-conv#secularGamma, bpP:p0:blocks#fast, bpP:p0:blocks#slow, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L26-L26 | Gamma_i in rho_i
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L25-L25 | Lambda_i
EDGE: bpP:p0:blocks#slow | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L25-L25 | u_i=(xi_i,eta_i)
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L25-L25 | w in Phase(2+2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.secularEccVector (KAM/Frozen/Planetary/Defs/SecularEccVector.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: frozen definition transcribed in the unlabelled prose of 14b 'Conventions' (texttt name, no frozen tag); anchor bound by the SPEC

NODE: bpP:p14:sb-conv#secularAxis
KIND: definition
TITLE: prose transcription: KAM.Planetary.secularAxis
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L27-L27
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.secularAxis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): m: Fin 2 -> R, w in Phase(2+2), i in {0,1}
SOURCE_QUANTIFIERS: m: Fin 2 -> R, then w in Phase(2+2), then i in Fin 2
SOURCE_CONCLUSION: defines secularAxis m w i = a_i=(Lambda_i/m_i)^2 (total Lean function; used only where m_i>0)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/SecularAxis.lean
FROZEN_DECL: KAM.Planetary.secularAxis
FROZEN_ANCHOR_ID: planetary.d25.secularAxis.v1
FROZEN_ABI_SHA256: 47fda3a6a287d2fd958de5e3db80633bcebdce343b0f59728fc0fd376867b82c
DEPS: bpP:p0:blocks#fast, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L27-L27 | Lambda_i=fast w_2 i
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L27-L27 | w in Phase(2+2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.secularAxis (KAM/Frozen/Planetary/Defs/SecularAxis.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: frozen definition transcribed in the unlabelled prose of 14b 'Conventions' (texttt name, no frozen tag); anchor bound by the SPEC

NODE: bpP:p14:sb-conv#orbitalUnit
KIND: definition
TITLE: prose transcription: KAM.Planetary.orbitalUnit
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L27-L27
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.orbitalUnit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): F in R
SOURCE_QUANTIFIERS: F in R
SOURCE_CONCLUSION: defines orbitalUnit F = c(F)=(cos F, sin F)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/OrbitalUnit.lean
FROZEN_DECL: KAM.Planetary.orbitalUnit
FROZEN_ANCHOR_ID: planetary.d25.orbitalUnit.v1
FROZEN_ABI_SHA256: 9c15c40a5451e900d32d005a82e70278478d00949b4d98571f64069d21277983
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.orbitalUnit (KAM/Frozen/Planetary/Defs/OrbitalUnit.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: frozen definition transcribed in the unlabelled prose of 14b 'Conventions' (texttt name, no frozen tag); anchor bound by the SPEC

NODE: bpP:p14:sb-conv#quarterTurn
KIND: definition
TITLE: prose transcription: KAM.Planetary.quarterTurn
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-conv@L29-L29
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.quarterTurn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): v in R^2
SOURCE_QUANTIFIERS: v: Fin 2 -> R
SOURCE_CONCLUSION: defines quarterTurn v = J_0 v, J_0(a,b)=(-b,a)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/QuarterTurn.lean
FROZEN_DECL: KAM.Planetary.quarterTurn
FROZEN_ANCHOR_ID: planetary.d25.quarterTurn.v1
FROZEN_ABI_SHA256: eb99e04660c4d46e766102e734f89eae7e0c55b64767ff2bec12b83d3d817357
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.quarterTurn (KAM/Frozen/Planetary/Defs/QuarterTurn.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: frozen definition transcribed in the unlabelled prose of 14b 'Conventions' (texttt name, no frozen tag); anchor bound by the SPEC

NODE: bpP:p14:sb-defs#secularIntegrand
KIND: definition
TITLE: Explicit secular objects: KAM.Planetary.secularIntegrand
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L47-L56
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.secularIntegrand
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): m: Fin 2 -> R, mu in R, w in Phase(2+2)
SOURCE_QUANTIFIERS: m: Fin 2 -> R, then mu in R, then w in Phase(2+2); F is a display variable for evaluating the definition at assemble Lambda F eta xi, not an additional argument
SOURCE_CONCLUSION: defines secularIntegrand m mu w = I_mu(w;F)=H_mov^(mu,m)(z(w;F)) prod_{i<2} J_i(w;F_i) evaluated at F=fast w_1 (statement: I_mu(w;F) of secularIntegrand m mu (assemble Lambda F eta xi)), H_mov=movingHamiltonian 1 1 m mu
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/SecularIntegrand.lean
FROZEN_DECL: KAM.Planetary.secularIntegrand
FROZEN_ANCHOR_ID: planetary.d25.secularIntegrand.v1
FROZEN_ABI_SHA256: 16702d5c0f02b4a4d51c752449ec680f2eee27bddf08a74f2c3f20c515412cc9
DEPS: bpP:p0:movham#movingHamiltonian, bpP:p14:sb-defs#ellipsePhase, bpP:p14:sb-defs#longitudeJacobian, bpP:p0:blocks#fast, bpP:p0:blocks#assemble, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L50-L50 | H_mov^(mu,m)=movingHamiltonian 1 1 m mu
EDGE: bpP:p14:sb-defs#ellipsePhase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L50-L50 | z(w;F)=ellipsePhase m w F
EDGE: bpP:p14:sb-defs#longitudeJacobian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L50-L50 | J_i(w;F_i)
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L50-L50 | F=fast w_1
EDGE: bpP:p0:blocks#assemble | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L50-L50 | assemble Lambda F eta xi
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs#secularIntegrand@L48-L48 | the frozen declaration has an argument w in Phase(2+2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.secularIntegrand (KAM/Frozen/Planetary/Defs/SecularIntegrand.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p14:sb-defs#exactSecularHamiltonian
KIND: definition
TITLE: Explicit secular objects: KAM.Planetary.exactSecularHamiltonian
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L47-L56
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.exactSecularHamiltonian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): m: Fin 2 -> R, mu in R, w in Phase(2+2)
SOURCE_QUANTIFIERS: m: Fin 2 -> R, then mu in R, then w in Phase(2+2); F is the bound integration variable, not an additional argument
SOURCE_CONCLUSION: defines exactSecularHamiltonian m mu w = H_sec^(m,mu)(w)=(2pi)^-2 int_Delta I_mu((F,xi;Lambda,eta);F) dF (Delta=[0,2pi]^2), the frozen secularAverage of secularIntegrand
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/ExactSecularHamiltonian.lean
FROZEN_DECL: KAM.Planetary.exactSecularHamiltonian
FROZEN_ANCHOR_ID: planetary.d25.exactSecularHamiltonian.v1
FROZEN_ABI_SHA256: d90042793cf876faa1b65bb38437ad55fbebf57ff89a66314bbcf3261073f273
DEPS: bpP:p0:secavg#secularAverage, bpP:p14:sb-defs#secularIntegrand, bpP:p0:blocks#fast, bpP:p0:blocks#slow, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:secavg#secularAverage | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L51-L51 | the average (2pi)^-2 int_Delta is secularAverage
EDGE: bpP:p14:sb-defs#secularIntegrand | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L51-L51 | integrand I_mu
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L51-L51 | fast w_2=Lambda
EDGE: bpP:p0:blocks#slow | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L51-L51 | slow w_1=xi, slow w_2=eta
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs#exactSecularHamiltonian@L48-L48 | the frozen declaration has an argument w in Phase(2+2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.exactSecularHamiltonian (KAM/Frozen/Planetary/Defs/ExactSecularHamiltonian.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p14:sb-defs#ellipsePhase
KIND: definition
TITLE: Explicit secular objects: KAM.Planetary.ellipsePhase
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L47-L56
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.ellipsePhase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): m: Fin 2 -> R, w in Phase(2+2), F in R^2
SOURCE_QUANTIFIERS: m, w, F
SOURCE_CONCLUSION: defines ellipsePhase m w F = z(w;F)=((q_i(w;F_i))_i,(p_i(w;F_i))_i) in Phase(2*2) (coordinate k via finProdFinEquiv.symm k)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/EllipsePhase.lean
FROZEN_DECL: KAM.Planetary.ellipsePhase
FROZEN_ANCHOR_ID: planetary.d25.ellipsePhase.v1
FROZEN_ABI_SHA256: 2ba210a6c21128ce7aa0126ca4a9adb005c85a130597a29a42bf82304408959d
DEPS: bpP:p14:sb-defs#ellipsePosition, bpP:p14:sb-defs#ellipseMomentum, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-defs#ellipsePosition | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L48-L48 | q_i(w;F_i)
EDGE: bpP:p14:sb-defs#ellipseMomentum | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L48-L48 | p_i(w;F_i)
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L48-L48 | values in Phase(2*2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.ellipsePhase (KAM/Frozen/Planetary/Defs/EllipsePhase.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p14:sb-defs#ellipsePosition
KIND: definition
TITLE: Explicit secular objects: KAM.Planetary.ellipsePosition
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L47-L56
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.ellipsePosition
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): m: Fin 2 -> R, w in Phase(2+2), i in {0,1}, F in R
SOURCE_QUANTIFIERS: m, w, i, F
SOURCE_CONCLUSION: defines ellipsePosition m w i F = q_i(w;F)=a_i(k_i c(F)-v_i+(x_i/(1+k_i)) v_i)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/EllipsePosition.lean
FROZEN_DECL: KAM.Planetary.ellipsePosition
FROZEN_ANCHOR_ID: planetary.d25.ellipsePosition.v1
FROZEN_ABI_SHA256: 35defd876e40b0b716ecde1e692c6314f45e6bfb5d768dbcfc1ad5a7ab50275d
DEPS: bpP:p14:sb-conv#secularEccVector, bpP:p14:sb-conv#orbitalUnit, bpP:p14:sb-conv#secularAxis, bpP:p14:sb-conv#secularRoot, bpP:p0:plane#planeDot, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L29-L29 | v_i
EDGE: bpP:p14:sb-conv#orbitalUnit | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L29-L29 | c(F)
EDGE: bpP:p14:sb-conv#secularAxis | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L29-L29 | a_i
EDGE: bpP:p14:sb-conv#secularRoot | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L29-L29 | k_i
EDGE: bpP:p0:plane#planeDot | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L29-L29 | x_i=v_i.c(F)
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs#ellipsePosition@L25-L25 | the frozen declaration has an argument w in Phase(2+2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.ellipsePosition (KAM/Frozen/Planetary/Defs/EllipsePosition.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p14:sb-defs#ellipseMomentum
KIND: definition
TITLE: Explicit secular objects: KAM.Planetary.ellipseMomentum
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L47-L56
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.ellipseMomentum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): m: Fin 2 -> R, w in Phase(2+2), i in {0,1}, F in R
SOURCE_QUANTIFIERS: m, w, i, F
SOURCE_CONCLUSION: defines ellipseMomentum m w i F = p_i(w;F)=(m_i^2/(Lambda_i J_i)) (J_0 c(F)-(x_i/(1+k_i)) J_0 v_i)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/EllipseMomentum.lean
FROZEN_DECL: KAM.Planetary.ellipseMomentum
FROZEN_ANCHOR_ID: planetary.d25.ellipseMomentum.v1
FROZEN_ABI_SHA256: b0f3078a3aee1fad0a7f5d89ac79e902f546502754b1ceb4c209e0007709f316
DEPS: bpP:p14:sb-conv#secularEccVector, bpP:p14:sb-conv#orbitalUnit, bpP:p14:sb-conv#quarterTurn, bpP:p14:sb-conv#secularRoot, bpP:p14:sb-defs#longitudeJacobian, bpP:p0:plane#planeDot, bpP:p0:blocks#fast, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L29-L29 | v_i
EDGE: bpP:p14:sb-conv#orbitalUnit | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L29-L29 | c(F)
EDGE: bpP:p14:sb-conv#quarterTurn | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L29-L29 | J_0=quarterTurn
EDGE: bpP:p14:sb-conv#secularRoot | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L29-L29 | k_i
EDGE: bpP:p14:sb-defs#longitudeJacobian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L29-L29 | J_i in the prefactor
EDGE: bpP:p0:plane#planeDot | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L29-L29 | x_i
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L29-L29 | Lambda_i
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs#ellipseMomentum@L25-L25 | the frozen declaration has an argument w in Phase(2+2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.ellipseMomentum (KAM/Frozen/Planetary/Defs/EllipseMomentum.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p14:sb-defs#longitudeJacobian
KIND: definition
TITLE: Explicit secular objects: KAM.Planetary.longitudeJacobian
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L47-L56
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.longitudeJacobian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): w in Phase(2+2), i in {0,1}, F in R
SOURCE_QUANTIFIERS: w, i, F
SOURCE_CONCLUSION: defines longitudeJacobian w i F = J_i(w;F)=1-x_i(F), x_i(F)=v_i.c(F)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/LongitudeJacobian.lean
FROZEN_DECL: KAM.Planetary.longitudeJacobian
FROZEN_ANCHOR_ID: planetary.d25.longitudeJacobian.v1
FROZEN_ABI_SHA256: 5fe7154f50c970f0aa831b9048c56da368b50601418ad63dd689eeefea930cb1
DEPS: bpP:p14:sb-conv#secularEccVector, bpP:p14:sb-conv#orbitalUnit, bpP:p0:plane#planeDot, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L28-L28 | v_i
EDGE: bpP:p14:sb-conv#orbitalUnit | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L28-L28 | c(F)
EDGE: bpP:p0:plane#planeDot | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L28-L28 | x_i=v_i.c(F) is the plane dot product
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-defs@L28-L28 | w in Phase(2+2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.longitudeJacobian (KAM/Frozen/Planetary/Defs/LongitudeJacobian.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p14:sb-box#SecularInputBox
KIND: definition
TITLE: \texttt{SecularInputBox}: KAM.Planetary.SecularInputBox
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-box@L58-L64
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.SecularInputBox
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): sigma in R, w in Phase(2+2); weights m=(1,sigma)=jupiterSaturnWeights sigma
SOURCE_QUANTIFIERS: sigma, w
SOURCE_CONCLUSION: defines SecularInputBox sigma w =: Box_sigma(w): (i) for i=0,1: 0<Lambda_i, 0<=Gamma_i<Lambda_i; (ii) 103/20<=a_0<=21/4 and 189/20<=a_1<=193/20; (iii) ¦v_0¦<=3/50, ¦v_1¦<=7/100; all lambda and all perihelia allowed
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/SecularInputBox.lean
FROZEN_DECL: KAM.Planetary.SecularInputBox
FROZEN_ANCHOR_ID: planetary.d25.SecularInputBox.v1
FROZEN_ABI_SHA256: 5008002e4d848cf38bd14ecd936e1ab66fea71db1d074f9a19bd52e9677c95d7
DEPS: bpP:p14:sb-conv#secularGamma, bpP:p14:sb-conv#secularAxis, bpP:p14:sb-conv#secularEccVector, bpP:p0:plane#planeLength, bpP:p14:sb-box#jupiterSaturnWeights, bpP:p0:blocks#fast, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-box@L60-L60 | Gamma_i in (i)
EDGE: bpP:p14:sb-conv#secularAxis | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-box@L60-L60 | a_i in (ii)
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-box@L60-L60 | v_i in (iii)
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-box@L60-L60 | ¦v_i¦ is planeLength
EDGE: bpP:p14:sb-box#jupiterSaturnWeights | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-box@L59-L59 | weights m=(1,sigma)
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-box@L60-L60 | Lambda_i
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-box@L59-L59 | w in Phase(2+2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.SecularInputBox (KAM/Frozen/Planetary/Defs/SecularInputBox.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p14:sb-box#jupiterSaturnWeights
KIND: definition
TITLE: \texttt{SecularInputBox}: KAM.Planetary.jupiterSaturnWeights
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-box@L58-L64
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.jupiterSaturnWeights
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): sigma in R
SOURCE_QUANTIFIERS: sigma
SOURCE_CONCLUSION: defines jupiterSaturnWeights sigma = (1,sigma) : Fin 2 -> R
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/JupiterSaturnWeights.lean
FROZEN_DECL: KAM.Planetary.jupiterSaturnWeights
FROZEN_ANCHOR_ID: planetary.d25.jupiterSaturnWeights.v1
FROZEN_ABI_SHA256: edad403adb04728f271bd99cc355550997a77cf9830c4d6ed7eebad8b2b92388
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.jupiterSaturnWeights (KAM/Frozen/Planetary/Defs/JupiterSaturnWeights.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p14:sb-regular#SecularRegular
KIND: definition
TITLE: \texttt{SecularRegular}: KAM.Planetary.SecularRegular
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-regular@L66-L70
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.SecularRegular
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): m: Fin 2 -> R, mu in R, w in Phase(2+2)
SOURCE_QUANTIFIERS: m, mu, w
SOURCE_CONCLUSION: defines SecularRegular m mu w =: Reg_{sigma,mu}(w): (i) m_i>0, Lambda_i>0, 0<=Gamma_i<Lambda_i; (ii) for every F in R^2: J_i(w;F_i)>0 and NoColl(z(w;F)_1); (iii) F -> I_mu((F,xi;Lambda,eta);F) integrable on Delta; (iv) H_sec is Frechet differentiable at w
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/SecularRegular.lean
FROZEN_DECL: KAM.Planetary.SecularRegular
FROZEN_ANCHOR_ID: planetary.d25.SecularRegular.v1
FROZEN_ABI_SHA256: 952bbd10a1a3ca90f95f54b929eaa1d267fc20c17896ec445e9d4328e2c165de
DEPS: bpP:p14:sb-conv#secularGamma, bpP:p14:sb-defs#longitudeJacobian, bpP:p0:nocoll#NoCollision, bpP:p14:sb-defs#ellipsePhase, bpP:p14:sb-defs#secularIntegrand, bpP:p0:blocks#assemble, bpP:p14:sb-defs#exactSecularHamiltonian, bpP:p0:blocks#fast, bpP:p0:phase#Phase, bpP:p0:blocks#slow
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-regular@L67-L67 | Gamma_i in (i)
EDGE: bpP:p14:sb-defs#longitudeJacobian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-regular@L67-L67 | J_i>0 in (ii)
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-regular@L67-L67 | NoColl in (ii)
EDGE: bpP:p14:sb-defs#ellipsePhase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-regular@L67-L67 | z(w;F)_1 in (ii)
EDGE: bpP:p14:sb-defs#secularIntegrand | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-regular@L68-L68 | integrand I_mu in (iii)
EDGE: bpP:p0:blocks#assemble | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-regular@L68-L68 | argument (F,xi;Lambda,eta)
EDGE: bpP:p14:sb-defs#exactSecularHamiltonian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-regular@L68-L68 | differentiability of H_sec in (iv)
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-regular@L67-L67 | Lambda_i
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-regular#SecularRegular@L67-L67 | w has the Phase(2+2) carrier in the frozen predicate
EDGE: bpP:p0:blocks#slow | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-regular#SecularRegular@L68-L68 | the integral evaluates assemble using slow w_2 and slow w_1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.SecularRegular (KAM/Frozen/Planetary/Defs/SecularRegular.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p14:sb-safety
KIND: theorem
TITLE: P-SECULAR-BOX, \texttt{secularBoxSafety}
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L72-L86
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L280-L307
CONTRACT_ID: planetary.d25.secularBoxSafety
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: sigma in [29/100,31/100]; mu>0; w0 in Phase(2+2) with Box_sigma(w0); m=(1,sigma); H=H_sec^(m,mu)
SOURCE_QUANTIFIERS: sigma and mu in R; sigma in [29/100,31/100] and mu>0; w0 in Phase(2+2) with Box_sigma(w0); then exists w; then the universal U,v,t,F,i clauses in the stated order
SOURCE_CONCLUSION: exists w: R -> Phase(2+2) with (a) w(0)=w0 and IsHamiltonianSolutionOn H univ univ w; (b) for every open convex U in R with 0 in U and every v: R -> Phase(2+2) with v(0)=w0, IsHamiltonianSolutionOn H univ U v and Reg_{sigma,mu}(v(t)) for all t in U: v(t)=w(t) for all t in U; (c) for every t: Reg_{sigma,mu}(w(t)), fast((w(t))_2)=fast((w0)_2) (Lambda constant), AMD(w(t))=AMD(w0)<16373/2500000, ¦v_i(w(t))¦<3/20 for i=0,1, and for every F in R^2: 1751/400<=¦q_i(w(t);F_i)¦<=4439/400 (i=0,1); 399/200<=¦q_1(w(t);F_1)¦-¦q_0(w(t);F_0)¦; PairBounds(399/200,4439/200; barycentricPositions 1 m mu (z(w(t);F)_1))
CONSTANT_SCOPE: none: all numerical constants are literals; w depends on (sigma,mu,w0)
FROZEN_FILE: KAM/Frozen/Planetary/Theorems/SecularBoxSafety.lean
FROZEN_DECL: KAM.Planetary.secularBoxSafety
FROZEN_ANCHOR_ID: planetary.d25.secularBoxSafety.v1
FROZEN_ABI_SHA256: 960d1b58a1fd45c10d30e4632f8154000761c77ab20f9e86a576601bcb6d1f48
DEPS: stepP:p14:sb-th-1, stepP:p14:sb-th-2, stepP:p14:sb-th-3, stepP:p14:sb-th-4, stepP:p14:sb-th-5, stepP:p14:sb-th-6, stepP:p14:sb-th-7, stepP:p14:sb-th-8, stepP:p14:sb-th-9, stepP:p14:sb-th-10, stepP:p14:sb-th-11, bpP:p14:sb-box#SecularInputBox, bpP:p14:sb-box#jupiterSaturnWeights, bpP:p14:sb-defs#exactSecularHamiltonian, bpP:p0:d25-movsol#IsHamiltonianSolutionOn, bpP:p14:sb-regular#SecularRegular, bpP:p14:sb-conv#secularAMD, bpP:p14:sb-conv#secularEccVector, bpP:p14:sb-defs#ellipsePosition, bpP:p14:sb-defs#ellipsePhase, bpP:p0:plane#planeLength, bpP:p0:nocoll#PairBounds, bpP:p0:barycentric#barycentricPositions, bpP:p0:blocks#fast, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-th-1 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L283-L283 | proof step
EDGE: stepP:p14:sb-th-2 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L285-L285 | proof step
EDGE: stepP:p14:sb-th-3 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L288-L288 | proof step
EDGE: stepP:p14:sb-th-4 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L290-L290 | proof step
EDGE: stepP:p14:sb-th-5 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L292-L292 | proof step
EDGE: stepP:p14:sb-th-6 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L294-L294 | proof step
EDGE: stepP:p14:sb-th-7 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L296-L296 | proof step
EDGE: stepP:p14:sb-th-8 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L298-L298 | proof step
EDGE: stepP:p14:sb-th-9 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L300-L300 | proof step
EDGE: stepP:p14:sb-th-10 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L302-L302 | proof step
EDGE: stepP:p14:sb-th-11 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L304-L304 | proof step
EDGE: bpP:p14:sb-box#SecularInputBox | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L73-L73 | hypothesis Box_sigma(w0)
EDGE: bpP:p14:sb-box#jupiterSaturnWeights | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L73-L73 | m=(1,sigma)
EDGE: bpP:p14:sb-defs#exactSecularHamiltonian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L73-L73 | H=H_sec^(m,mu)=exactSecularHamiltonian m mu
EDGE: bpP:p0:d25-movsol#IsHamiltonianSolutionOn | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L75-L75 | IsHamiltonianSolutionOn in (a),(b)
EDGE: bpP:p14:sb-regular#SecularRegular | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L76-L76 | Reg_{sigma,mu} in (b),(c)
EDGE: bpP:p14:sb-conv#secularAMD | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L77-L77 | AMD in (c)
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L77-L77 | ¦v_i¦ in (c)
EDGE: bpP:p14:sb-defs#ellipsePosition | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L79-L79 | q_i in (c)
EDGE: bpP:p14:sb-defs#ellipsePhase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L81-L81 | z(w(t);F)_1
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L79-L79 | ¦.¦ is planeLength
EDGE: bpP:p0:nocoll#PairBounds | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L81-L81 | PairBounds in (c)
EDGE: bpP:p0:barycentric#barycentricPositions | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L81-L81 | barycentricPositions
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L77-L77 | Lambda(w(t))=Lambda(w0)
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L73-L73 | Phase(2+2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: frozen root KAM.Planetary.secularBoxSafety; no smallness condition on mu

NODE: bpP:p14:sb-cited
KIND: theorem
TITLE: \texttt{secularBoxAtCitedMasses}
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L88-L92
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L309-L312
CONTRACT_ID: planetary.d25.secularBoxAtCitedMasses
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: w0 in Phase(2+2) with Box_{476/1591}(w0)
SOURCE_QUANTIFIERS: forall w0 (hypothesis Box_{476/1591}(w0))
SOURCE_CONCLUSION: the conclusion of Theorem sb-safety with sigma=476/1591 and mu=4773/5000000 substituted everywhere: exists w ... (a),(b),(c) as in sb-safety for H=H_sec^((1,476/1591),4773/5000000)
CONSTANT_SCOPE: none: sigma and mu are the literals 476/1591 and 4773/5000000
FROZEN_FILE: KAM/Frozen/Planetary/Theorems/SecularBoxAtCitedMasses.lean
FROZEN_DECL: KAM.Planetary.secularBoxAtCitedMasses
FROZEN_ANCHOR_ID: planetary.d25.secularBoxAtCitedMasses.v1
FROZEN_ABI_SHA256: a26520919c3c64c781c509be044346ee7ee4d428b76b1862aaa97ef59672a014
DEPS: stepP:p14:sb-ci-1, bpP:p14:sb-safety, bpP:p14:sb-box#SecularInputBox, bpP:p14:sb-box#jupiterSaturnWeights, bpP:p14:sb-defs#exactSecularHamiltonian, bpP:p0:d25-movsol#IsHamiltonianSolutionOn, bpP:p14:sb-regular#SecularRegular, bpP:p14:sb-conv#secularAMD, bpP:p14:sb-conv#secularEccVector, bpP:p14:sb-defs#ellipsePosition, bpP:p14:sb-defs#ellipsePhase, bpP:p0:plane#planeLength, bpP:p0:nocoll#PairBounds, bpP:p0:barycentric#barycentricPositions, bpP:p0:blocks#fast, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-ci-1 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L310-L310 | proof step (instantiation)
EDGE: bpP:p14:sb-safety | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L89-L89 | its conclusion with the two literals substituted
EDGE: bpP:p14:sb-box#SecularInputBox | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L89-L89 | hypothesis Box_{476/1591}
EDGE: bpP:p14:sb-box#jupiterSaturnWeights | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L89-L89 | weights m=(1,476/1591)
EDGE: bpP:p14:sb-defs#exactSecularHamiltonian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L89-L89 | H_sec
EDGE: bpP:p0:d25-movsol#IsHamiltonianSolutionOn | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L89-L89 | IsHamiltonianSolutionOn in the conclusion
EDGE: bpP:p14:sb-regular#SecularRegular | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L89-L89 | Reg in the conclusion
EDGE: bpP:p14:sb-conv#secularAMD | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L89-L89 | AMD
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L89-L89 | ¦v_i¦
EDGE: bpP:p14:sb-defs#ellipsePosition | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L89-L89 | q_i
EDGE: bpP:p14:sb-defs#ellipsePhase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L89-L89 | z(w(t);F)_1
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L89-L89 | planeLength
EDGE: bpP:p0:nocoll#PairBounds | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L89-L89 | PairBounds
EDGE: bpP:p0:barycentric#barycentricPositions | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L89-L89 | barycentricPositions
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L89-L89 | Lambda
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L89-L89 | Phase(2+2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: frozen root KAM.Planetary.secularBoxAtCitedMasses; the cited decimal masses (stepP:p14:sb-ci-2) are not used in the proof

NODE: bpP:p14:sb-numerics
KIND: lemma
TITLE: Numerical certificate
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-numerics@L103-L133
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-numerics@L134-L136
CONTRACT_ID: bpP:p14:sb-numerics
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lambda_J=sqrt(a_0), Lambda_S=sigma sqrt(a_1) the actions of a box point (used only in the labels)
SOURCE_QUANTIFIERS: none (each row is a closed numerical statement)
SOURCE_CONCLUSION: N1: 29/100<=476/1591<=31/100, 3*1591=4773, (4773/5000000)(476/1591)=357/1250000; N2: (87/100)^2<103/20 and 21/4<(23/10)^2; N3: (87/100)^2<(29/100)^2(189/20) and (31/100)^2(193/20)<(97/100)^2; N4a: (99819/100000)^2<1-(3/50)^2; N4b: (49877/50000)^2<1-(7/100)^2; N4c: (23/10)(181/100000)+(97/100)(123/50000)=16373/2500000; N5a: (16373/2500000)/(87/100)<19/2500; N5b: 1-(2481/2500)^2=94639/6250000<(3/20)^2; N6a: 51/10<103/20,21/4<53/10,47/5<189/20,193/20<97/10; N6b: 50(16373/2500000)<87/100; N6c: 1-(49/50)^2=99/2500<(1/5)^2; N6d: (53/10)(6/5)<(47/5)(4/5); N7a: (103/20)(17/20)=1751/400 and (193/20)(23/20)=4439/400; N7b: (189/20)(17/20)-(21/4)(23/20)=399/200; N7c: (21/4)(23/20)=483/80<=4439/400, (189/20)(17/20)>=1751/400, 399/200<=1751/400; N7d: 4439/400+483/80<=4439/200; the checked but unused source chain: (989/1000)^2>1-(3/20)^2, (87/100)(11/1000)=957/100000>16373/2500000
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-x-alg
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-x-alg | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-numerics@L135-L135 | exact rational arithmetic, norm_num
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sb_numerics (KAM/Planetary/SecularBox/Numerics.lean)
LEAN_NOTE: audit S0 PASS WITH NOTES; 33 conjuncts N1-N7 and source chain, closed rational
NOTE: numerical certificate; checked in exact rational arithmetic by the scratch script (provenance), in Lean each row is a norm_num goal

NODE: bpP:p14:sb-chart
KIND: lemma
TITLE: Eccentricity, radius, Jacobian
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-chart@L144-L152
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-chart@L153-L162
CONTRACT_ID: bpP:p14:sb-chart
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m_i>0, Lambda_i>0, 0<=Gamma_i<Lambda_i (elliptic point), F in R, i in {0,1}
SOURCE_QUANTIFIERS: w elliptic, F, i
SOURCE_CONCLUSION: (a) k_i in (0,1], radicand of rho_i positive, ¦v_i¦^2=1-k_i^2, e_i<1, k_i=sqrt(1-e_i^2), Gamma_i=Lambda_i(1-k_i); (b) J_i(F)>=1-e_i>0; (c) ¦q_i(w;F)¦=a_i(1-x_i(F)), hence a_i(1-e_i)<=¦q_i¦<=a_i(1+e_i) and ¦q_i¦>0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-ch-a, stepP:p14:sb-ch-b, stepP:p14:sb-ch-c, stepP:p14:sb-ch-d, bpP:p14:sb-conv#secularRoot, bpP:p14:sb-conv#secularEccVector, bpP:p14:sb-conv#secularGamma, bpP:p14:sb-conv#secularAxis, bpP:p14:sb-defs#longitudeJacobian, bpP:p14:sb-defs#ellipsePosition, bpP:p0:plane#planeLength
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-ch-a | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-chart@L154-L154 | (a)
EDGE: stepP:p14:sb-ch-b | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-chart@L156-L156 | (b)
EDGE: stepP:p14:sb-ch-c | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-chart@L157-L157 | (c) identity
EDGE: stepP:p14:sb-ch-d | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-chart@L161-L161 | radial bounds
EDGE: bpP:p14:sb-conv#secularRoot | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-chart@L147-L147 | k_i
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-chart@L147-L147 | v_i, rho_i, e_i
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-chart@L147-L147 | Gamma_i
EDGE: bpP:p14:sb-conv#secularAxis | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-chart@L149-L149 | a_i
EDGE: bpP:p14:sb-defs#longitudeJacobian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-chart@L148-L148 | J_i
EDGE: bpP:p14:sb-defs#ellipsePosition | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-chart@L149-L149 | q_i
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-chart@L149-L149 | ¦.¦ is planeLength
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sb_chart, sb_chart_axis_mul_one_sub_pos, sb_chart_radius_pos (KAM/Planetary/SecularBox/Chart.lean)
LEAN_NOTE: audit S1 round 2 PASS WITH NOTES (F1 closed by sb_chart_axis_mul_one_sub_pos, sb_chart_radius_pos)
NOTE: -

NODE: stepP:p14:sb-ch-a
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-a@L154-L155
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-a@L154-L155
CONTRACT_ID: stepP:p14:sb-ch-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: elliptic point: m_i>0, Lambda_i>0, 0<=Gamma_i<Lambda_i
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-chart; for i in {0,1}
SOURCE_CONCLUSION: k_i in (0,1], rho_i^2>0, ¦v_i¦^2=1-k_i^2, e_i^2<1, k_i=sqrt(1-e_i^2), Gamma_i=Lambda_i(1-k_i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-conv#secularRoot, bpP:p14:sb-conv#secularEccVector, bpP:p14:sb-conv#secularGamma, bpP:p14:sb-x-alg
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-conv#secularRoot | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-a@L154-L154 | k_i=1-Gamma_i/Lambda_i
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-a@L154-L154 | v_i=rho_i u_i, rho_i^2
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-a@L154-L154 | ¦u_i¦^2=2Gamma_i
EDGE: bpP:p14:sb-x-alg | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-a@L155-L155 | sqrt(y)^2=y, sqrt increasing
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sb_chart (KAM/Planetary/SecularBox/Chart.lean)
LEAN_NOTE: audit S1 round 2 PASS WITH NOTES (F1 closed by sb_chart_axis_mul_one_sub_pos, sb_chart_radius_pos); stated by corresponding conjuncts of sb_chart
NOTE: the statement of Proposition bpP:p7:d25(a) is named as the same identity; per L43 it is a consistency check and is not a dependency

NODE: stepP:p14:sb-ch-b
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-b@L156-L156
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-b@L156-L156
CONTRACT_ID: stepP:p14:sb-ch-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-chart; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-chart; for F in R
SOURCE_CONCLUSION: x_i<=e_i by Cauchy-Schwarz, so J_i=1-x_i>=1-e_i>0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-ch-a, bpP:p14:sb-defs#longitudeJacobian, bpP:p14:sb-conv#orbitalUnit, bpP:p14:sb-x-alg
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-ch-a | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-b@L156-L156 | e_i<1
EDGE: bpP:p14:sb-defs#longitudeJacobian | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-b@L156-L156 | J_i=1-x_i
EDGE: bpP:p14:sb-conv#orbitalUnit | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-b@L156-L156 | ¦c(F)¦=1
EDGE: bpP:p14:sb-x-alg | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-b@L156-L156 | ¦c(F)¦=1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sb_chart (KAM/Planetary/SecularBox/Chart.lean)
LEAN_NOTE: audit S1 round 2 PASS WITH NOTES (F1 closed by sb_chart_axis_mul_one_sub_pos, sb_chart_radius_pos); stated by corresponding conjuncts of sb_chart
NOTE: -

NODE: stepP:p14:sb-ch-c
KIND: step
TITLE: (c) the identity
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-c@L157-L160
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-c@L157-L160
CONTRACT_ID: stepP:p14:sb-ch-c
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-chart; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-chart; for F in R
SOURCE_CONCLUSION: ¦q/a¦^2=(1-x)^2 via (1+k)¦q/a¦^2=A(1-x)^2 with A=1+k, hence ¦q_i¦=a_i(1-x_i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-ch-a, stepP:p14:sb-ch-b, bpP:p14:sb-defs#ellipsePosition, bpP:p14:sb-conv#secularEccVector, bpP:p14:sb-conv#secularRoot, bpP:p14:sb-conv#secularAxis, bpP:p14:sb-conv#orbitalUnit, bpP:p14:sb-x-alg
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-ch-a | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-c@L158-L158 | e^2=1-k^2=(1-k)(1+k) and k>0
EDGE: stepP:p14:sb-ch-b | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-c@L160-L160 | 1-x>0
EDGE: bpP:p14:sb-defs#ellipsePosition | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-c@L157-L157 | q=a(kc-kappa v)
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-c@L157-L157 | v
EDGE: bpP:p14:sb-conv#secularRoot | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-c@L157-L157 | k
EDGE: bpP:p14:sb-conv#secularAxis | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-c@L157-L157 | a
EDGE: bpP:p14:sb-conv#orbitalUnit | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-c@L158-L158 | ¦c¦=1
EDGE: bpP:p14:sb-x-alg | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-c@L158-L158 | polynomial identity by linear_combination, ¦c¦=1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sb_chart (KAM/Planetary/SecularBox/Chart.lean)
LEAN_NOTE: audit S1 round 2 PASS WITH NOTES (F1 closed by sb_chart_axis_mul_one_sub_pos, sb_chart_radius_pos); stated by corresponding conjuncts of sb_chart
NOTE: -

NODE: stepP:p14:sb-ch-d
KIND: step
TITLE: Radial bounds
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-d@L161-L161
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-d@L161-L161
CONTRACT_ID: stepP:p14:sb-ch-d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-chart; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-chart; for F in R
SOURCE_CONCLUSION: a(1-e)<=¦q¦<=a(1+e) and ¦q¦>=a(1-e)>0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-ch-c, stepP:p14:sb-ch-a, stepP:p14:sb-ch-b, bpP:p14:sb-conv#secularAxis, bpP:p14:sb-x-alg
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-ch-c | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-d@L161-L161 | ¦q¦=a(1-x)
EDGE: stepP:p14:sb-ch-a | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-d@L161-L161 | a>0 and e<1
EDGE: stepP:p14:sb-ch-b | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-d@L161-L161 | Cauchy-Schwarz bound for x
EDGE: bpP:p14:sb-conv#secularAxis | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-d@L161-L161 | a=(Lambda_i/m_i)^2 is positive under the elliptic source premises
EDGE: bpP:p14:sb-x-alg | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ch-d@L161-L161 | the lower Cauchy bound and positivity are elementary real planar algebra, not an additional hypothesis
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sb_chart, sb_chart_axis_mul_one_sub_pos, sb_chart_radius_pos (KAM/Planetary/SecularBox/Chart.lean)
LEAN_NOTE: audit S1 round 2 PASS WITH NOTES (F1 closed by sb_chart_axis_mul_one_sub_pos, sb_chart_radius_pos)
NOTE: -

NODE: bpP:p14:sb-cov
KIND: lemma
TITLE: Rotation covariance
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cov@L164-L168
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cov@L169-L173
CONTRACT_ID: bpP:p14:sb-cov
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: w elliptic (both planets); theta in R; w^theta has the same lambda and Lambda and (xi_i',eta_i')=R_theta(xi_i,eta_i)
SOURCE_QUANTIFIERS: w, theta, F in R
SOURCE_CONCLUSION: Gamma_i,k_i,a_i unchanged; v_i(w^theta)=R_theta v_i(w); x_i(w^theta;F)=x_i(w;F-theta), J_i(w^theta;F)=J_i(w;F-theta), q_i(w^theta;F)=R_theta q_i(w;F-theta), p_i(w^theta;F)=R_theta p_i(w;F-theta)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-cv-1, stepP:p14:sb-cv-2, stepP:p14:sb-cv-3, bpP:p14:sb-conv#secularGamma, bpP:p14:sb-conv#secularRoot, bpP:p14:sb-conv#secularAxis, bpP:p14:sb-conv#secularEccVector, bpP:p14:sb-defs#longitudeJacobian, bpP:p14:sb-defs#ellipsePosition, bpP:p14:sb-defs#ellipseMomentum
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-cv-1 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cov@L170-L170 | slow data
EDGE: stepP:p14:sb-cv-2 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cov@L171-L171 | scalars
EDGE: stepP:p14:sb-cv-3 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cov@L172-L172 | vectors
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cov@L165-L165 | Gamma_i
EDGE: bpP:p14:sb-conv#secularRoot | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cov@L165-L165 | k_i
EDGE: bpP:p14:sb-conv#secularAxis | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cov@L165-L165 | a_i
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cov@L165-L165 | v_i
EDGE: bpP:p14:sb-defs#longitudeJacobian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cov@L166-L166 | J_i
EDGE: bpP:p14:sb-defs#ellipsePosition | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cov@L166-L166 | q_i
EDGE: bpP:p14:sb-defs#ellipseMomentum | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cov@L166-L166 | p_i
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: audit P14-S2 PASS WITH NOTES: sb_cov states Gamma, ecc vector, J, q, p covariance; the k/a/x invariance clauses (and sb-cv-1/2) hold only by unfolding, not stated; not marked proved
NOTE: -

NODE: stepP:p14:sb-cv-1
KIND: step
TITLE: Slow data
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-1@L170-L170
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-1@L170-L170
CONTRACT_ID: stepP:p14:sb-cv-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-cov; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-cov; i in {0,1}
SOURCE_CONCLUSION: Gamma_i,k_i,rho_i,a_i unchanged and v_i(w^theta)=R_theta v_i
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-conv#secularGamma, bpP:p14:sb-conv#secularRoot, bpP:p14:sb-conv#secularEccVector, bpP:p14:sb-conv#secularAxis, bpP:p14:sb-x-alg
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-1@L170-L170 | Gamma_i depends on ¦u_i¦
EDGE: bpP:p14:sb-conv#secularRoot | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-1@L170-L170 | k_i
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-1@L170-L170 | rho_i, v_i
EDGE: bpP:p14:sb-conv#secularAxis | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-1@L170-L170 | a_i
EDGE: bpP:p14:sb-x-alg | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-1@L170-L170 | rotations preserve the norm
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: sb_cov states only Gamma/ecc vector (cv-1) resp. J,q,p (cv-2); k,rho,a,x equalities not literal conjuncts; left
NOTE: -

NODE: stepP:p14:sb-cv-2
KIND: step
TITLE: Scalars
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-2@L171-L171
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-2@L171-L171
CONTRACT_ID: stepP:p14:sb-cv-2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-cov; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-cov; for F in R
SOURCE_CONCLUSION: x_i(w^theta;F)=x_i(w;F-theta) and J_i(w^theta;F)=J_i(w;F-theta)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-cv-1, bpP:p14:sb-x-alg, bpP:p14:sb-conv#orbitalUnit, bpP:p14:sb-defs#longitudeJacobian
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-cv-1 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-2@L171-L171 | v_i(w^theta)=R_theta v_i
EDGE: bpP:p14:sb-x-alg | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-2@L171-L171 | R_theta c(F)=c(F+theta), rotations preserve the dot product
EDGE: bpP:p14:sb-conv#orbitalUnit | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-2@L171-L171 | c(F)
EDGE: bpP:p14:sb-defs#longitudeJacobian | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-2@L171-L171 | J_i
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: sb_cov states only Gamma/ecc vector (cv-1) resp. J,q,p (cv-2); k,rho,a,x equalities not literal conjuncts; left
NOTE: -

NODE: stepP:p14:sb-cv-3
KIND: step
TITLE: Vectors
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-3@L172-L172
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-3@L172-L172
CONTRACT_ID: stepP:p14:sb-cv-3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-cov; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-cov; for F in R
SOURCE_CONCLUSION: q'=R_theta q(w;F-theta) and p'=R_theta p(w;F-theta)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-cv-1, stepP:p14:sb-cv-2, bpP:p14:sb-defs#ellipsePosition, bpP:p14:sb-defs#ellipseMomentum, bpP:p14:sb-conv#quarterTurn, bpP:p14:sb-x-alg
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-cv-1 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-3@L172-L172 | v'=R_theta v and k,a unchanged
EDGE: stepP:p14:sb-cv-2 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-3@L172-L172 | x/(1+k) and J unchanged up to the shift
EDGE: bpP:p14:sb-defs#ellipsePosition | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-3@L172-L172 | formula for q
EDGE: bpP:p14:sb-defs#ellipseMomentum | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-3@L172-L172 | formula for p
EDGE: bpP:p14:sb-conv#quarterTurn | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-3@L172-L172 | J_0 commutes with R_theta
EDGE: bpP:p14:sb-x-alg | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-cv-3@L172-L172 | rotation algebra
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sb_cov (KAM/Planetary/SecularBox/Covariance.lean)
LEAN_NOTE: audit S2 PASS WITH NOTES; position and momentum covariance
NOTE: -

NODE: bpP:p14:sb-smooth#data
KIND: definition
TITLE: Section data of 14b smoothness and flow: sigma, m=(1,sigma), mu
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-smooth#data@L177-L177
PROOF_SOURCE: -
CONTRACT_ID: bpP:p14:sb-smooth#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): sigma in [29/100,31/100] so m=(1,sigma) with m_i>0; mu>0
SOURCE_QUANTIFIERS: sigma and mu fixed before the statements of the subsection
SOURCE_CONCLUSION: fixes sigma in [29/100,31/100], m=(1,sigma) with m_i>0 and mu>0 for the subsection (its proofs work for every real mu)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-box#jupiterSaturnWeights
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-box#jupiterSaturnWeights | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-smooth#data@L177-L177 | m=(1,sigma)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: section data for the subsection sb-smooth (the SPEC suggested the name bpP:p14:sb-flow#data; the paragraph is the opening of sb-smooth, L177, and governs sb-smooth and sb-flow)

NODE: bpP:p14:sb-Sdef
KIND: definition
TITLE: The region $\mathcal S$
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-Sdef@L179-L183
PROOF_SOURCE: -
CONTRACT_ID: bpP:p14:sb-Sdef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data of bpP:p14:sb-smooth#data: sigma in [29/100,31/100], m=(1,sigma), mu>0
SOURCE_QUANTIFIERS: sigma fixed; w in Phase(2+2)
SOURCE_CONCLUSION: defines S=S_sigma = set of w with, for i=0,1: Lambda_i>0 and 50 Gamma_i<Lambda_i; 51/10<a_0<53/10 and 47/5<a_1<97/10; S does not constrain lambda, is invariant under w -> w^theta, and is open
CONSTANT_SCOPE: none (depends on sigma only through a_i)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-smooth#data, bpP:p14:sb-conv#secularGamma, bpP:p14:sb-conv#secularAxis, bpP:p0:blocks#fast, bpP:p0:phase#Phase, bpP:p14:sb-x-top
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-smooth#data | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-Sdef@L177-L177 | sigma, m=(1,sigma), m_i nonzero
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-Sdef@L180-L180 | Gamma_i
EDGE: bpP:p14:sb-conv#secularAxis | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-Sdef@L180-L180 | a_i
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-Sdef@L180-L180 | Lambda_i
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-Sdef@L180-L180 | w in Phase(2+2)
EDGE: bpP:p14:sb-x-top | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-Sdef@L181-L181 | openness: finite intersection of strict inequalities of continuous functions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sb_sdef, sb_s (KAM/Planetary/SecularBox/Region.lean)
LEAN_NOTE: audit S3 round 2 PASS WITH NOTES; definition body OK, openness by sb_s; theta-invariance not a separate declaration (follows from the definition not involving lambda)
NOTE: -

NODE: bpP:p14:sb-S
KIND: lemma
TITLE: Geometry on $\mathcal S$
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-S@L185-L188
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-S@L189-L193
CONTRACT_ID: bpP:p14:sb-S
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: w in S; F in R^2
SOURCE_QUANTIFIERS: w in S, F in R^2
SOURCE_CONCLUSION: k_i>49/50, e_i<1/5, J_i(F_i)>4/5; ¦q_0(w;F_0)¦<(53/10)(6/5) and ¦q_1(w;F_1)¦>(47/5)(4/5), so ¦q_0¦<¦q_1¦ and ¦q_i¦,¦q_0-q_1¦>0; the radicand of rho_i exceeds 99/(100 Lambda_i); every w in S is elliptic, Reg (i),(ii) hold at w and z(w;F)_1 has NoColl
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-S-1, stepP:p14:sb-S-2, stepP:p14:sb-S-3, bpP:p14:sb-Sdef, bpP:p14:sb-regular#SecularRegular, bpP:p0:nocoll#NoCollision, bpP:p14:sb-defs#ellipsePhase, stepP:p14:sb-th-8, bpP:p14:sb-conv#secularEccVector, bpP:p14:sb-conv#secularRoot, bpP:p14:sb-defs#longitudeJacobian, bpP:p14:sb-defs#ellipsePosition, bpP:p14:sb-smooth#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-S-1 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-S@L190-L190 | elliptic
EDGE: stepP:p14:sb-S-2 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-S@L191-L191 | eccentricity
EDGE: stepP:p14:sb-S-3 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-S@L192-L192 | radii
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-S@L186-L186 | the set S
EDGE: bpP:p14:sb-regular#SecularRegular | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-S@L186-L186 | Reg (i),(ii)
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-S@L186-L186 | NoColl of z(w;F)_1
EDGE: bpP:p14:sb-defs#ellipsePhase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-S@L186-L186 | z(w;F)_1
EDGE: stepP:p14:sb-th-8 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-S@L186-L186 | bridge bodyVector(z(w;F)_1) i=q_i(w;F_i) is what turns the bounds on q_i into NoColl of z(w;F)_1
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-S@L186-L186 | rho_i, e_i
EDGE: bpP:p14:sb-conv#secularRoot | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-S@L186-L186 | k_i
EDGE: bpP:p14:sb-defs#longitudeJacobian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-S@L186-L186 | J_i
EDGE: bpP:p14:sb-defs#ellipsePosition | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-S@L186-L186 | q_i
EDGE: bpP:p14:sb-smooth#data | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-S@L186-L186 | Reg(i) includes positivity of the fixed weights m=(1,sigma), supplied by the section data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sb_s_geometry, sb_s (KAM/Planetary/SecularBox/Region.lean)
LEAN_NOTE: audit S3 round 2 PASS WITH NOTES; literal conclusion via companion sb_s_geometry (signed sb_s alone is narrower)
NOTE: the last claim (NoColl of z(w;F)_1) needs the bridge stepP:p14:sb-th-8, stated later at L298 and cited by stepP:p14:sb-th-7; the Lemma's proof (L189-193) does not prove it (see report)

NODE: stepP:p14:sb-S-1
KIND: step
TITLE: Elliptic
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-1@L190-L190
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-1@L190-L190
CONTRACT_ID: stepP:p14:sb-S-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: w in S
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-S; i in {0,1}
SOURCE_CONCLUSION: Gamma_i<Lambda_i, k_i>49/50 and 1-Gamma_i/(2Lambda_i)>99/100
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-Sdef, bpP:p14:sb-conv#secularRoot, bpP:p14:sb-conv#secularGamma
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-1@L190-L190 | 50 Gamma_i<Lambda_i and Gamma_i>=0
EDGE: bpP:p14:sb-conv#secularRoot | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-1@L190-L190 | k_i
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-1@L190-L190 | Gamma_i
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sb_s_radicand, sb_s_geometry (KAM/Planetary/SecularBox/Region.lean)
LEAN_NOTE: audit S3 round 2 PASS WITH NOTES; radicand margin sb_s_radicand, k and Gamma<Lambda in sb_s_geometry
NOTE: -

NODE: stepP:p14:sb-S-2
KIND: step
TITLE: Eccentricity
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-2@L191-L191
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-2@L191-L191
CONTRACT_ID: stepP:p14:sb-S-2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-S; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-S; i in {0,1}
SOURCE_CONCLUSION: e_i^2<99/2500<1/25 and J_i>=1-e_i>4/5
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-S-1, bpP:p14:sb-chart, bpP:p14:sb-numerics, bpP:p14:sb-Sdef
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-S-1 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-2@L191-L191 | k_i>49/50
EDGE: bpP:p14:sb-chart | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-2@L191-L191 | (a) e_i^2=1-k_i^2 and (b) J_i>=1-e_i
EDGE: bpP:p14:sb-numerics | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-2@L191-L191 | N6c: 1-(49/50)^2=99/2500<(1/5)^2
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-2@L191-L191 | the statement or conditional application uses the region S or its affine slice S-prime
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sb_s_geometry (KAM/Planetary/SecularBox/Region.lean)
LEAN_NOTE: audit S3 round 2 PASS WITH NOTES; eccentricity and Jacobian bounds exported by companion
NOTE: -

NODE: stepP:p14:sb-S-3
KIND: step
TITLE: Radii
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-3@L192-L192
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-3@L192-L192
CONTRACT_ID: stepP:p14:sb-S-3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-S; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-S; F in R^2
SOURCE_CONCLUSION: ¦q_0¦<(53/10)(6/5), ¦q_1¦>(47/5)(4/5) and ¦q_1-q_0¦>0, ¦q_0-q_1¦=¦q_1-q_0¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-chart, stepP:p14:sb-S-2, bpP:p14:sb-Sdef, bpP:p14:sb-numerics, bpP:p0:plane#planeLength, bpP:p6:ext-tri
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-chart | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-3@L192-L192 | (c) a_i(1-e_i)<=¦q_i¦<=a_i(1+e_i)
EDGE: stepP:p14:sb-S-2 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-3@L192-L192 | e_i<1/5
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-3@L192-L192 | axis ranges of S
EDGE: bpP:p14:sb-numerics | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-3@L192-L192 | N6d: 53/10*6/5<47/5*4/5
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-3@L192-L192 | reverse triangle inequality for planeLength
EDGE: bpP:p6:ext-tri | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-S-3@L192-L192 | the proof applies the reverse triangle inequality to the physical planar lengths
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sb_s_geometry (KAM/Planetary/SecularBox/Region.lean)
LEAN_NOTE: audit S3 round 2 PASS WITH NOTES; radii, ordering and separation exported by companion
NOTE: -

NODE: bpP:p14:sb-smooth-prop
KIND: proposition
TITLE: Smoothness of $H_{\rm sec}$
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-smooth-prop@L195-L199
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-smooth-prop@L200-L205
CONTRACT_ID: bpP:p14:sb-smooth-prop
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: sigma in [29/100,31/100] fixed, m=(1,sigma); mu is any real number (as explicitly stated here and at L177); S is S_sigma
SOURCE_QUANTIFIERS: sigma, mu, then (a)-(c)
SOURCE_CONCLUSION: (a) for w in S: H_sec(w)=(2pi)^-2 int_Delta Ihat(w;F) dF with Ihat(w;F)=H_mov^(mu,m)(z(w;F)) prod_i J_i(w;F_i), and H_sec does not depend on lambda on S; (b) Ihat is C^infty on S x R^2 and 2pi-periodic in each F_i; (c) H_sec is C^infty on S (so C^2 and differentiable at every point of S) and Reg_{sigma,mu}(w) (iii),(iv) hold for w in S
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-sm-1, stepP:p14:sb-sm-2, stepP:p14:sb-sm-3, stepP:p14:sb-sm-4, bpP:p14:sb-smooth#data, bpP:p14:sb-Sdef, bpP:p14:sb-defs#exactSecularHamiltonian, bpP:p0:movham#movingHamiltonian, bpP:p14:sb-defs#ellipsePhase, bpP:p14:sb-defs#longitudeJacobian, bpP:p14:sb-regular#SecularRegular
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-sm-1 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-smooth-prop@L201-L201 | (a)
EDGE: stepP:p14:sb-sm-2 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-smooth-prop@L202-L202 | (b)
EDGE: stepP:p14:sb-sm-3 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-smooth-prop@L203-L203 | C^infty
EDGE: stepP:p14:sb-sm-4 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-smooth-prop@L204-L204 | integrability and differentiability
EDGE: bpP:p14:sb-smooth#data | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-smooth-prop@L196-L196 | m=(1,sigma), mu
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-smooth-prop@L196-L196 | the region S
EDGE: bpP:p14:sb-defs#exactSecularHamiltonian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-smooth-prop@L196-L196 | H_sec
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-smooth-prop@L196-L196 | H_mov^(mu,m)
EDGE: bpP:p14:sb-defs#ellipsePhase | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-smooth-prop@L196-L196 | z(w;F)
EDGE: bpP:p14:sb-defs#longitudeJacobian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-smooth-prop@L196-L196 | J_i
EDGE: bpP:p14:sb-regular#SecularRegular | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-smooth-prop@L197-L197 | Reg (iii),(iv)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sb_smooth_prop, secular_integrand_smooth, secular_integrand_identity (KAM/Planetary/SecularBox/Smooth.lean)
LEAN_NOTE: audit S5 PASS WITH NOTES; composite: (a) integral identity and lambda-independence, (b) smooth/periodic integrand, (c) C-infinity and Reg (iii),(iv)
NOTE: -

NODE: stepP:p14:sb-sm-1
KIND: step
TITLE: $\lambda$-independence
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-1@L201-L201
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-1@L201-L201
CONTRACT_ID: stepP:p14:sb-sm-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-smooth-prop; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-smooth-prop; for every w with the same slow data
SOURCE_CONCLUSION: I_mu((F,xi;Lambda,eta);F)=Ihat(w;F) for every w with these slow data; hence H_sec(w)=(2pi)^-2 int Ihat dF and H_sec does not depend on lambda
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:blocks#assemble, bpP:p0:blocks#fast, bpP:p0:blocks#slow, bpP:p14:sb-defs#secularIntegrand, bpP:p14:sb-defs#exactSecularHamiltonian, bpP:p14:sb-defs#ellipsePhase, bpP:p14:sb-defs#ellipsePosition, bpP:p14:sb-defs#ellipseMomentum, bpP:p14:sb-conv#secularEccVector, bpP:p14:sb-conv#secularRoot, bpP:p14:sb-conv#secularAxis, bpP:p14:sb-defs#longitudeJacobian
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:blocks#assemble | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-1@L201-L201 | assemble Lambda F eta xi and its blocks
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-1@L201-L201 | fast of the blocks
EDGE: bpP:p0:blocks#slow | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-1@L201-L201 | slow of the blocks
EDGE: bpP:p14:sb-defs#secularIntegrand | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-1@L201-L201 | I_mu
EDGE: bpP:p14:sb-defs#exactSecularHamiltonian | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-1@L201-L201 | H_sec
EDGE: bpP:p14:sb-defs#ellipsePhase | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-1@L201-L201 | ellipsePhase uses only xi,eta,Lambda,F
EDGE: bpP:p14:sb-defs#ellipsePosition | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-1@L201-L201 | q_i
EDGE: bpP:p14:sb-defs#ellipseMomentum | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-1@L201-L201 | p_i
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-1@L201-L201 | v_i
EDGE: bpP:p14:sb-conv#secularRoot | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-1@L201-L201 | k_i
EDGE: bpP:p14:sb-conv#secularAxis | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-1@L201-L201 | a_i
EDGE: bpP:p14:sb-defs#longitudeJacobian | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-1@L201-L201 | J_i
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: secular_integrand_identity, explicitSecularIntegrand, sb_smooth_prop (KAM/Planetary/SecularBox/Smooth.lean)
LEAN_NOTE: audit S5 PASS WITH NOTES; identity plus lambda-independence
NOTE: -

NODE: stepP:p14:sb-sm-2
KIND: step
TITLE: Smoothness of the chart
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-2@L202-L202
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-2@L202-L202
CONTRACT_ID: stepP:p14:sb-sm-2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-smooth-prop; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-smooth-prop; on S x R^2
SOURCE_CONCLUSION: v_i,x_i,q_i,p_i,1/¦q_i¦,1/¦q_0-q_1¦ are C^infty, every term of H_mov is C^infty, hence Ihat is C^infty on S x R^2 and 2pi-periodic in each F_i
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-S, bpP:p14:sb-x-calc, bpP:p0:movham#movingHamiltonian, bpP:p14:sb-smooth#data, bpP:p14:sb-Sdef, bpP:p14:sb-defs#ellipsePosition, bpP:p14:sb-defs#ellipseMomentum, bpP:p14:sb-conv#secularEccVector, bpP:p14:sb-conv#secularRoot, bpP:p14:sb-defs#longitudeJacobian, bpP:p14:sb-conv#orbitalUnit, bpP:p6:ext-sqrt
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-S | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-2@L202-L202 | Lambda_i>0, radicand of rho_i>99/(100Lambda_i), J_i>4/5, ¦q_i¦>0, ¦q_0-q_1¦>0 on S
EDGE: bpP:p14:sb-x-calc | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-2@L202-L202 | C^k closure under quotients, products, compositions
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-2@L202-L202 | terms of H_mov
EDGE: bpP:p14:sb-smooth#data | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-2@L202-L202 | m_i>0 and the coupling mu
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-2@L202-L202 | the region S
EDGE: bpP:p14:sb-defs#ellipsePosition | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-2@L202-L202 | q_i
EDGE: bpP:p14:sb-defs#ellipseMomentum | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-2@L202-L202 | p_i
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-2@L202-L202 | v_i, rho_i
EDGE: bpP:p14:sb-conv#secularRoot | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-2@L202-L202 | k_i
EDGE: bpP:p14:sb-defs#longitudeJacobian | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-2@L202-L202 | J_i
EDGE: bpP:p14:sb-conv#orbitalUnit | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-2@L202-L202 | F_i enters only through c(F_i)
EDGE: bpP:p6:ext-sqrt | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-2@L202-L202 | smoothness of sqrt on positive arguments and reciprocal away from zero is used for rho_i and the reciprocal radii
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: secular_integrand_smooth (KAM/Planetary/SecularBox/Smooth.lean)
LEAN_NOTE: audit S5 PASS WITH NOTES; C-infinity on S x R^2 and 2pi-periodicity
NOTE: -

NODE: stepP:p14:sb-sm-3
KIND: step
TITLE: Parameter integral
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-3@L203-L203
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-3@L203-L203
CONTRACT_ID: stepP:p14:sb-sm-3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-smooth-prop; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-smooth-prop; local at w_*
SOURCE_CONCLUSION: w -> int_Delta Ihat dF is C^2 on the interior of N with derivatives under the integral, and so of every order: H_sec is C^infty on S
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:e-diff, bpP:p14:sb-x-top, stepP:p14:sb-sm-2, stepP:p14:sb-sm-1, bpP:p14:sb-Sdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:e-diff | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-3@L203-L203 | differentiation under the integral (k=2 and every order)
EDGE: bpP:p14:sb-x-top | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-3@L203-L203 | continuity on the compact N x Delta
EDGE: stepP:p14:sb-sm-2 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-3@L203-L203 | Ihat is C^infty
EDGE: stepP:p14:sb-sm-1 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-3@L203-L203 | H_sec=int Ihat dF on S
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-3@L203-L203 | S open
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sb_smooth_prop (KAM/Planetary/SecularBox/Smooth.lean)
LEAN_NOTE: audit S5 PASS WITH NOTES; first clause (C-infinity of exactSecularHamiltonian on S) via S4 parametric integral
NOTE: the draft external bpP:p14:sb-x-diff is an alias of bpP:p8:e-diff (EXCLUDED); the edge goes to bpP:p8:e-diff

NODE: stepP:p14:sb-sm-4
KIND: step
TITLE: Integrability
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-4@L204-L204
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-4@L204-L204
CONTRACT_ID: stepP:p14:sb-sm-4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-smooth-prop; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-smooth-prop; for w in S
SOURCE_CONCLUSION: F -> Ihat(w;F) is integrable (Reg (iii)) and H_sec is differentiable at w (Reg (iv))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-x-int, stepP:p14:sb-sm-2, stepP:p14:sb-sm-1, stepP:p14:sb-sm-3, bpP:p14:sb-regular#SecularRegular, bpP:p14:sb-Sdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-x-int | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-4@L204-L204 | continuous functions are integrable on compact boxes
EDGE: stepP:p14:sb-sm-2 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-4@L204-L204 | continuity of Ihat
EDGE: stepP:p14:sb-sm-1 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-4@L204-L204 | identification of the integrand of Reg (iii) with Ihat
EDGE: stepP:p14:sb-sm-3 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-4@L204-L204 | H_sec is C^infty on the open set S
EDGE: bpP:p14:sb-regular#SecularRegular | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-4@L204-L204 | clauses (iii),(iv)
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sm-4@L204-L204 | S open
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sb_smooth_prop (KAM/Planetary/SecularBox/Smooth.lean)
LEAN_NOTE: audit S5 PASS WITH NOTES; SecularRegular clauses (integrability, differentiability)
NOTE: -

NODE: bpP:p14:sb-rot
KIND: proposition
TITLE: Rotation invariance
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-rot@L207-L210
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-rot@L211-L216
CONTRACT_ID: bpP:p14:sb-rot
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: w in S, theta in R; w^theta of Lemma cov
SOURCE_QUANTIFIERS: for w in S and theta in R
SOURCE_CONCLUSION: w^theta in S and H_sec(w^theta)=H_sec(w)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-rot-1, stepP:p14:sb-rot-2, stepP:p14:sb-rot-3, stepP:p14:sb-rot-4, bpP:p14:sb-Sdef, bpP:p14:sb-defs#exactSecularHamiltonian, bpP:p14:sb-cov, bpP:p14:sb-smooth#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-rot-1 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-rot@L212-L212 | membership
EDGE: stepP:p14:sb-rot-2 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-rot@L213-L213 | Hamiltonian
EDGE: stepP:p14:sb-rot-3 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-rot@L214-L214 | integrand
EDGE: stepP:p14:sb-rot-4 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-rot@L215-L215 | integral
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-rot@L208-L208 | S
EDGE: bpP:p14:sb-defs#exactSecularHamiltonian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-rot@L208-L208 | H_sec
EDGE: bpP:p14:sb-cov | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-rot@L208-L208 | the point w^theta
EDGE: bpP:p14:sb-smooth#data | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-rot@L208-L208 | sigma, mu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sb_rot (KAM/Planetary/SecularBox/Rotation.lean)
LEAN_NOTE: audit P14-S6 PASS WITH NOTES
NOTE: -

NODE: stepP:p14:sb-rot-1
KIND: step
TITLE: Membership
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-1@L212-L212
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-1@L212-L212
CONTRACT_ID: stepP:p14:sb-rot-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-rot; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-rot; no new binders
SOURCE_CONCLUSION: w^theta in S
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-cov, bpP:p14:sb-Sdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-cov | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-1@L212-L212 | Gamma_i,Lambda_i,a_i unchanged under w -> w^theta
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-1@L212-L212 | membership conditions of S
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sbRot_mem (KAM/Planetary/SecularBox/Rotation.lean)
LEAN_NOTE: audit P14-S6 PASS; named sb-rot-1
NOTE: -

NODE: stepP:p14:sb-rot-2
KIND: step
TITLE: The Hamiltonian
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-2@L213-L213
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-2@L213-L213
CONTRACT_ID: stepP:p14:sb-rot-2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: R_theta acts on Phase(2*2) by R_theta on each body vector of q and p
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-rot; for z in Phase(2*2)
SOURCE_CONCLUSION: H_mov(R_theta z)=H_mov(z)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:body#bodyVector, bpP:p0:movham#movingHamiltonian, bpP:p0:plane#planeLength, bpP:p0:plane#planeDot, bpP:p14:sb-x-alg
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-2@L213-L213 | bodyVector(R_theta z)=R_theta bodyVector(z)
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-2@L213-L213 | H_mov term by term
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-2@L213-L213 | ¦R_theta a-R_theta b¦=¦a-b¦
EDGE: bpP:p0:plane#planeDot | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-2@L213-L213 | R_theta a.R_theta b=a.b
EDGE: bpP:p14:sb-x-alg | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-2@L213-L213 | rotations preserve dot product and norm
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sbRot_moving (KAM/Planetary/SecularBox/Rotation.lean)
LEAN_NOTE: audit P14-S6 PASS; named sb-rot-2
NOTE: -

NODE: stepP:p14:sb-rot-3
KIND: step
TITLE: The integrand
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-3@L214-L214
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-3@L214-L214
CONTRACT_ID: stepP:p14:sb-rot-3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-rot; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-rot; for w in S, F in R^2
SOURCE_CONCLUSION: Ihat(w^theta;F)=Ihat(w;F-theta 1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-cov, stepP:p14:sb-rot-2, bpP:p14:sb-smooth-prop, bpP:p14:sb-defs#ellipsePhase, bpP:p14:sb-defs#longitudeJacobian, bpP:p14:sb-Sdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-cov | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-3@L214-L214 | covariance of z and J_i
EDGE: stepP:p14:sb-rot-2 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-3@L214-L214 | H_mov invariant under R_theta
EDGE: bpP:p14:sb-smooth-prop | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-3@L214-L214 | the integrand Ihat
EDGE: bpP:p14:sb-defs#ellipsePhase | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-3@L214-L214 | z(w;F)
EDGE: bpP:p14:sb-defs#longitudeJacobian | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-3@L214-L214 | J_i
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-3@L214-L214 | the statement or conditional application uses the region S or its affine slice S-prime
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sbRot_explicit (KAM/Planetary/SecularBox/Rotation.lean)
LEAN_NOTE: audit P14-S6 PASS; named sb-rot-3
NOTE: -

NODE: stepP:p14:sb-rot-4
KIND: step
TITLE: The integral
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-4@L215-L215
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-4@L215-L215
CONTRACT_ID: stepP:p14:sb-rot-4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-rot; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-rot; for w in S
SOURCE_CONCLUSION: int_Delta Ihat(w;F-theta 1) dF = int_Delta Ihat(w;F) dF, hence H_sec(w^theta)=H_sec(w)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-smooth-prop, bpP:p14:sb-x-int, stepP:p14:sb-rot-3, stepP:p14:sb-rot-1, bpP:p14:sb-defs#exactSecularHamiltonian, bpP:p14:sb-Sdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-smooth-prop | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-4@L215-L215 | (a) H_sec=average of Ihat and (b) continuity and periodicity
EDGE: bpP:p14:sb-x-int | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-4@L215-L215 | Fubini and periodic translation invariance
EDGE: stepP:p14:sb-rot-3 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-4@L215-L215 | Ihat(w^theta;F)=Ihat(w;F-theta 1)
EDGE: stepP:p14:sb-rot-1 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-4@L215-L215 | w^theta in S so (a) applies
EDGE: bpP:p14:sb-defs#exactSecularHamiltonian | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-4@L215-L215 | H_sec
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-rot-4@L215-L215 | the statement or conditional application uses the region S or its affine slice S-prime
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: PROVED
LEAN_REF: sbRot_box_shift, sbRot_pi_shift, sb_rot (KAM/Planetary/SecularBox/Rotation.lean)
LEAN_NOTE: audit P14-S6 PASS; named sb-rot-4
NOTE: -

NODE: bpP:p14:sb-pred
KIND: lemma
TITLE: Predicate and field on $\mathcal S$
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-pred@L226-L230
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-pred@L231-L234
CONTRACT_ID: bpP:p14:sb-pred
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed sigma, m=(1,sigma), mu and H=H_sec of the section; J subset R, z: R -> Phase(2+2), with z(t) in S for every t in J
SOURCE_QUANTIFIERS: for all J, z
SOURCE_CONCLUSION: H is C^2 on S, X_H is C^1 on S, and IsHamiltonianSolutionOn H univ J z iff IsSolIn X_H S J z
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-pr-1, stepP:p14:sb-pr-2, N:bpN:p3:gen-sol, bpP:p0:d25-movsol#IsHamiltonianSolutionOn, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p14:sb-defs#exactSecularHamiltonian, bpP:p14:sb-Sdef, bpP:p14:sb-smooth#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-pr-1 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-pred@L232-L232 | regularity
EDGE: stepP:p14:sb-pr-2 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-pred@L233-L233 | equivalence
EDGE: N:bpN:p3:gen-sol | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-pred@L228-L228 | IsSolIn in the conclusion
EDGE: bpP:p0:d25-movsol#IsHamiltonianSolutionOn | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-pred@L228-L228 | IsHamiltonianSolutionOn
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-pred@L227-L227 | X_H
EDGE: bpP:p14:sb-defs#exactSecularHamiltonian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-pred@L227-L227 | H=H_sec
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-pred@L227-L227 | S
EDGE: bpP:p14:sb-smooth#data | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-pred@L227-L227 | sigma, mu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: the pattern citation of N:bpN:p3:ham-reduction (L233) is not an edge

NODE: stepP:p14:sb-pr-1
KIND: step
TITLE: Regularity
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-pr-1@L232-L232
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-pr-1@L232-L232
CONTRACT_ID: stepP:p14:sb-pr-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-pred; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-pred; on S
SOURCE_CONCLUSION: H is C^2 on S and X_H is C^1 on S
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p3:ham-smooth, bpP:p14:sb-smooth-prop, bpP:p14:sb-Sdef
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p3:ham-smooth | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-pr-1@L232-L232 | ham-smooth with n=4 and k=1
EDGE: bpP:p14:sb-smooth-prop | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-pr-1@L232-L232 | (c) H_sec is C^infty on S
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-pr-1@L232-L232 | S open
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-pr-2
KIND: step
TITLE: Equivalence
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-pr-2@L233-L233
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-pr-2@L233-L233
CONTRACT_ID: stepP:p14:sb-pr-2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-pred; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-pred; for t in J
SOURCE_CONCLUSION: IsHamiltonianSolutionOn H univ J z is equivalent to IsSolIn X_H S J z
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:d25-movsol#IsHamiltonianSolutionOn, N:bpN:p3:gen-sol, bpP:p14:sb-smooth-prop, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p14:sb-Sdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:d25-movsol#IsHamiltonianSolutionOn | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-pr-2@L233-L233 | unfolding of the predicate
EDGE: N:bpN:p3:gen-sol | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-pr-2@L233-L233 | unfolding of IsSolIn
EDGE: bpP:p14:sb-smooth-prop | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-pr-2@L233-L233 | differentiability of H at z(t) in S
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-pr-2@L233-L233 | the derivative clause is the same with X_H
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-pr-2@L233-L233 | the statement or conditional application uses the region S or its affine slice S-prime
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: the pattern of N:bpN:p3:ham-reduction is not used as a dependency (L42 pattern only)

NODE: bpP:p14:sb-field
KIND: lemma
TITLE: Structure of $X_H$
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-field@L236-L240
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-field@L241-L244
CONTRACT_ID: bpP:p14:sb-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: w in S, H=H_sec; block order ((lambda,xi),(Lambda,eta)); y=(xi,eta), Lambda fixed, h_Lambda(y)=H(0,xi;Lambda,eta); A(y)=Gamma_0+Gamma_1
SOURCE_QUANTIFIERS: for w in S
SOURCE_CONCLUSION: X_H(w)=((omega(w),dH/deta),(0,-dH/dxi)); dH/dxi and dH/deta are the partials of h_Lambda; sum_i (xi_i dH/deta_i - eta_i dH/dxi_i)(w)=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-fd-1, stepP:p14:sb-fd-2, bpP:p14:sb-smooth-prop, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p14:sb-defs#exactSecularHamiltonian, bpP:p14:sb-Sdef, bpP:p14:sb-conv#secularGamma, bpP:p14:sb-smooth#data, bpP:p14:sb-flow#omega
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-fd-1 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-field@L242-L242 | components
EDGE: stepP:p14:sb-fd-2 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-field@L243-L243 | rotation identity
EDGE: bpP:p14:sb-smooth-prop | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-field@L237-L237 | H_sec is C^infty on S
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-field@L237-L237 | X_H
EDGE: bpP:p14:sb-defs#exactSecularHamiltonian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-field@L237-L237 | H=H_sec
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-field@L237-L237 | S
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-field@L238-L238 | A(y)=Gamma_0+Gamma_1
EDGE: bpP:p14:sb-smooth#data | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-field@L237-L237 | sigma, mu
EDGE: bpP:p14:sb-flow#omega | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-field@L237-L237 | the displayed lambda component omega(w) is the partial gradient defined at L224
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: N:bpN:p3:ham-reduction in the \source note is not used in the proof (no edge)

NODE: stepP:p14:sb-fd-1
KIND: step
TITLE: Components
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-fd-1@L242-L242
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-fd-1@L242-L242
CONTRACT_ID: stepP:p14:sb-fd-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-field; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-field; for w in S
SOURCE_CONCLUSION: X_H components: lambda_i: dH/dLambda_i, xi_i: dH/deta_i, Lambda_i: -dH/dlambda_i=0, eta_i: -dH/dxi_i; partials of h_Lambda are those of H
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:hamsymp#hamiltonianVectorField, bpP:p14:sb-smooth-prop, bpP:p14:sb-x-calc, bpP:p14:sb-Sdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-fd-1@L242-L242 | components of hamiltonianVectorField
EDGE: bpP:p14:sb-smooth-prop | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-fd-1@L242-L242 | (a) lambda-independence and differentiability of H
EDGE: bpP:p14:sb-x-calc | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-fd-1@L242-L242 | constant along a line gives zero derivative; chain rule for the affine map
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-fd-1@L242-L242 | the statement or conditional application uses the region S or its affine slice S-prime
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-fd-2
KIND: step
TITLE: Rotation identity
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-fd-2@L243-L243
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-fd-2@L243-L243
CONTRACT_ID: stepP:p14:sb-fd-2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-field; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-field; for w in S
SOURCE_CONCLUSION: sum_i(-eta_i dH/dxi_i + xi_i dH/deta_i)(w)=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-rot, bpP:p14:sb-cov, bpP:p14:sb-smooth-prop, bpP:p14:sb-x-calc, bpP:p14:sb-Sdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-rot | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-fd-2@L243-L243 | g(theta)=H(w^theta) is constant
EDGE: bpP:p14:sb-cov | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-fd-2@L243-L243 | the curve theta -> w^theta
EDGE: bpP:p14:sb-smooth-prop | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-fd-2@L243-L243 | H differentiable at w
EDGE: bpP:p14:sb-x-calc | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-fd-2@L243-L243 | chain rule
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-fd-2@L243-L243 | the statement or conditional application uses the region S or its affine slice S-prime
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p14:sb-flow#omega
KIND: definition
TITLE: The slow-flow frequency omega(w)=dH_sec/dLambda
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-flow#omega@L224-L224
PROOF_SOURCE: -
CONTRACT_ID: bpP:p14:sb-flow#omega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: w in S
SOURCE_QUANTIFIERS: for w in S
SOURCE_CONCLUSION: defines omega(w)=dH_sec/dLambda(w) in R^2 (partial gradient in the Lambda variables); omega is continuous on S and depends only on (xi,Lambda,eta)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-smooth-prop, bpP:p14:sb-defs#exactSecularHamiltonian, bpP:p14:sb-Sdef, bpP:p14:sb-smooth#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-smooth-prop | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-flow#omega@L224-L224 | H_sec is C^infty on S and lambda-independent (Proposition smooth-prop)
EDGE: bpP:p14:sb-defs#exactSecularHamiltonian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-flow#omega@L224-L224 | H_sec
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-flow#omega@L224-L224 | S
EDGE: bpP:p14:sb-smooth#data | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-flow#omega@L224-L224 | H_sec uses the fixed weights m=(1,sigma) and parameter mu of the section
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: section data of 14b 'slow flow' (coverage prose-L224); consumed by stepP:p14:sb-gl-1 and stepP:p14:sb-gl-3

NODE: bpP:p14:sb-slow
KIND: lemma
TITLE: Global slow flow
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-slow@L246-L249
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-slow@L250-L256
CONTRACT_ID: bpP:p14:sb-slow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: w_0 in S with AMD(w_0)<16373/2500000 and Lambda_i(w_0)>87/100 (i=0,1); Lambda^0=fast(w_0)_2; S'={y=(xi,eta): (0,xi;Lambda^0,eta) in S} (open)
SOURCE_QUANTIFIERS: w_0, then y
SOURCE_CONCLUSION: there is a continuous y=(xi,eta): R -> S' with y(0)=(xi(w_0),eta(w_0)) having derivative (dh/deta(y(t)),-dh/dxi(y(t))) at every t (h=h_{Lambda^0}), with A(y(t))=A(y(0)) and y(t) in S' for all t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-sl-1, stepP:p14:sb-sl-2, stepP:p14:sb-sl-3, stepP:p14:sb-sl-4, stepP:p14:sb-sl-5, bpP:p14:sb-Sdef, bpP:p14:sb-conv#secularAMD, bpP:p14:sb-conv#secularGamma, bpP:p0:blocks#fast, bpP:p14:sb-smooth#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-sl-1 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-slow@L251-L251 | field
EDGE: stepP:p14:sb-sl-2 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-slow@L252-L252 | maximal solution
EDGE: stepP:p14:sb-sl-3 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-slow@L253-L253 | conservation of A
EDGE: stepP:p14:sb-sl-4 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-slow@L254-L254 | compact set
EDGE: stepP:p14:sb-sl-5 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-slow@L255-L255 | continuation
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-slow@L247-L247 | S and S'
EDGE: bpP:p14:sb-conv#secularAMD | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-slow@L247-L247 | AMD(w_0)
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-slow@L247-L247 | A(y)=Gamma_0+Gamma_1
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-slow@L247-L247 | Lambda_i, Lambda^0
EDGE: bpP:p14:sb-smooth#data | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-slow@L247-L247 | sigma, mu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: the application of N:bpN:p3:gen-continuation-compact named in the \source note is consumed in stepP:p14:sb-sl-5

NODE: stepP:p14:sb-sl-1
KIND: step
TITLE: The field
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-1@L251-L251
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-1@L251-L251
CONTRACT_ID: stepP:p14:sb-sl-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-slow; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-slow; no new binders
SOURCE_CONCLUSION: X_h=(dh/deta,-dh/dxi) is C^1 on S' and y(0) in S'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-smooth-prop, bpP:p14:sb-x-calc, N:bpN:p3:ham-smooth, bpP:p14:sb-Sdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-smooth-prop | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-1@L251-L251 | H_sec is C^infty on S
EDGE: bpP:p14:sb-x-calc | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-1@L251-L251 | a C^k function composed with an affine map is C^k
EDGE: N:bpN:p3:ham-smooth | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-1@L251-L251 | ham-smooth with phase space R^2 x R^2
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-1@L251-L251 | S' open and w_0 in S
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-sl-2
KIND: step
TITLE: Maximal solution
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-2@L252-L252
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-2@L252-L252
CONTRACT_ID: stepP:p14:sb-sl-2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-slow; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-slow; no new binders
SOURCE_CONCLUSION: a maximal interval (T_-,T_+) containing 0 and a solution y of X_h in S' through y(0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p3:gen-maximal, stepP:p14:sb-sl-1, bpP:p14:sb-Sdef
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p3:gen-maximal | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-2@L252-L252 | existence of the maximal solution
EDGE: stepP:p14:sb-sl-1 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-2@L252-L252 | C^1 field on the open set S'
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-2@L252-L252 | the statement or conditional application uses the region S or its affine slice S-prime
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-sl-3
KIND: step
TITLE: Conservation of $A$
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-3@L253-L253
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-3@L253-L253
CONTRACT_ID: stepP:p14:sb-sl-3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-slow; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-slow; on (T_-,T_+)
SOURCE_CONCLUSION: A(y(t))=A_0=A(y(0)) for all t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-field, bpP:p14:sb-x-calc, stepP:p14:sb-sl-2, bpP:p14:sb-Sdef, bpP:p14:sb-conv#secularGamma
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-field | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-3@L253-L253 | sum_i(xi_i dh/deta_i-eta_i dh/dxi_i)=0
EDGE: bpP:p14:sb-x-calc | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-3@L253-L253 | continuous function with derivative zero is constant
EDGE: stepP:p14:sb-sl-2 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-3@L253-L253 | the solution y
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-3@L253-L253 | (0,xi;Lambda^0,eta) in S
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-3@L253-L253 | A=Gamma_0+Gamma_1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-sl-4
KIND: step
TITLE: A compact set
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-4@L254-L254
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-4@L254-L254
CONTRACT_ID: stepP:p14:sb-sl-4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-slow; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-slow; for y in K
SOURCE_CONCLUSION: K={Gamma_0+Gamma_1=A_0} is compact and contained in S', and y(t) in K for all t in (T_-,T_+)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-x-top, bpP:p14:sb-numerics, bpP:p14:sb-Sdef, stepP:p14:sb-sl-3, stepP:p14:sb-sl-2, bpP:p14:sb-conv#secularGamma
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-x-top | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-4@L254-L254 | closed and bounded implies compact
EDGE: bpP:p14:sb-numerics | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-4@L254-L254 | N6b: 50*16373/2500000<87/100
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-4@L254-L254 | conditions of S: 50 Gamma_i<Lambda_i and axis ranges
EDGE: stepP:p14:sb-sl-3 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-4@L254-L254 | y(t) lies in K since A is conserved
EDGE: stepP:p14:sb-sl-2 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-4@L254-L254 | y(t) in S' on (T_-,T_+)
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-4@L254-L254 | Gamma_i
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-sl-5
KIND: step
TITLE: Continuation
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-5@L255-L255
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-5@L255-L255
CONTRACT_ID: stepP:p14:sb-sl-5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-slow; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-slow; right and left ends
SOURCE_CONCLUSION: T_+=+infinity and T_-=-infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p3:gen-continuation-compact, stepP:p14:sb-sl-2, stepP:p14:sb-sl-4, stepP:p14:sb-sl-1, bpP:p14:sb-Sdef
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p3:gen-continuation-compact | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-5@L255-L255 | continuation for compact tails on both ends
EDGE: stepP:p14:sb-sl-2 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-5@L255-L255 | maximal solution
EDGE: stepP:p14:sb-sl-4 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-5@L255-L255 | y(t) in the compact K inside S'
EDGE: stepP:p14:sb-sl-1 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-5@L255-L255 | X_h C^1 on the open set S'
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-sl-5@L255-L255 | the statement or conditional application uses the region S or its affine slice S-prime
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p14:sb-global
KIND: proposition
TITLE: Global solution of the full system
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-global@L258-L261
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-global@L262-L266
CONTRACT_ID: bpP:p14:sb-global
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: w_0 as in Lemma slow
SOURCE_QUANTIFIERS: w_0, then w
SOURCE_CONCLUSION: there is w: R -> Phase(2+2) with w(0)=w_0, w(t) in S, Lambda(w(t))=Lambda^0, AMD(w(t))=AMD(w_0) for all t, and IsHamiltonianSolutionOn H_sec univ univ w
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-gl-1, stepP:p14:sb-gl-2, stepP:p14:sb-gl-3, bpP:p14:sb-slow, bpP:p14:sb-defs#exactSecularHamiltonian, bpP:p0:d25-movsol#IsHamiltonianSolutionOn, bpP:p14:sb-conv#secularAMD, bpP:p14:sb-Sdef, bpP:p14:sb-smooth#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-gl-1 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-global@L263-L263 | quadrature
EDGE: stepP:p14:sb-gl-2 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-global@L264-L264 | the curve
EDGE: stepP:p14:sb-gl-3 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-global@L265-L265 | the equation
EDGE: bpP:p14:sb-slow | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-global@L259-L259 | hypotheses on w_0 and the slow flow y
EDGE: bpP:p14:sb-defs#exactSecularHamiltonian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-global@L259-L259 | H_sec
EDGE: bpP:p0:d25-movsol#IsHamiltonianSolutionOn | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-global@L259-L259 | IsHamiltonianSolutionOn
EDGE: bpP:p14:sb-conv#secularAMD | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-global@L259-L259 | AMD(w(t))
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-global@L259-L259 | w(t) in S
EDGE: bpP:p14:sb-smooth#data | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-global@L259-L259 | sigma, mu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: the applications of N:bpN:p3:gen-sol, gen-maximal and gen-continuation-compact named in the \source note are consumed in Lemmas slow and pred and carry no edge here

NODE: stepP:p14:sb-gl-1
KIND: step
TITLE: Quadrature
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-1@L263-L263
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-1@L263-L263
CONTRACT_ID: stepP:p14:sb-gl-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-global; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-global; t in R
SOURCE_CONCLUSION: lambda(t)=lambda(w_0)+int_0^t omega_*(s)ds with omega_*(t)=omega((0,xi(t);Lambda^0,eta(t))) continuous, so lambda'=omega_*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-flow#omega, bpP:p14:sb-slow, bpP:p14:sb-x-int, bpP:p14:sb-Sdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-flow#omega | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-1@L263-L263 | omega continuous on S and depends on (xi,Lambda,eta)
EDGE: bpP:p14:sb-slow | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-1@L263-L263 | y continuous with values in S'
EDGE: bpP:p14:sb-x-int | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-1@L263-L263 | fundamental theorem of calculus
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-1@L263-L263 | the statement or conditional application uses the region S or its affine slice S-prime
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-gl-2
KIND: step
TITLE: The curve
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-2@L264-L264
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-2@L264-L264
CONTRACT_ID: stepP:p14:sb-gl-2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-global; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-global; t in R
SOURCE_CONCLUSION: w(t)=((lambda(t),xi(t)),(Lambda^0,eta(t))) satisfies w(0)=w_0, w(t) in S, Lambda(w(t))=Lambda^0, AMD(w(t))=AMD(w_0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-gl-1, bpP:p14:sb-slow, bpP:p14:sb-Sdef, bpP:p14:sb-conv#secularAMD, bpP:p0:phase#Phase, bpP:p0:blocks#fast, bpP:p0:blocks#slow
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-gl-1 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-2@L264-L264 | lambda(t)
EDGE: bpP:p14:sb-slow | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-2@L264-L264 | y(t) in S' and A(y(t))=A(y(0))
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-2@L264-L264 | Gamma_i,Lambda_i,a_i depend on (y,Lambda^0) only
EDGE: bpP:p14:sb-conv#secularAMD | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-2@L264-L264 | AMD(w(t))=A(y(t))
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-2@L264-L264 | a point is determined by fast and slow of each block
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-2@L264-L264 | fast of the blocks
EDGE: bpP:p0:blocks#slow | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-2@L264-L264 | slow of the blocks
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-gl-3
KIND: step
TITLE: The equation
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-3@L265-L265
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-3@L265-L265
CONTRACT_ID: stepP:p14:sb-gl-3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-global; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-global; t in R
SOURCE_CONCLUSION: w has derivative X_H(w(t)) at every t and H is differentiable at w(t) in S, hence IsHamiltonianSolutionOn H univ univ w
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-field, bpP:p14:sb-flow#omega, bpP:p14:sb-slow, stepP:p14:sb-gl-1, stepP:p14:sb-gl-2, bpP:p14:sb-x-calc, bpP:p14:sb-pred, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p14:sb-Sdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-field | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-3@L265-L265 | X_H(w(t)) in the block order and partials equal those of h
EDGE: bpP:p14:sb-flow#omega | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-3@L265-L265 | omega_*(t)
EDGE: bpP:p14:sb-slow | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-3@L265-L265 | derivative of y
EDGE: stepP:p14:sb-gl-1 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-3@L265-L265 | lambda'=omega_*
EDGE: stepP:p14:sb-gl-2 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-3@L265-L265 | w(t) in S
EDGE: bpP:p14:sb-x-calc | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-3@L265-L265 | HasDerivAt componentwise
EDGE: bpP:p14:sb-pred | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-3@L265-L265 | H differentiable at w(t) and the predicate
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-3@L265-L265 | X_H
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-gl-3@L265-L265 | the statement or conditional application uses the region S or its affine slice S-prime
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p14:sb-unique
KIND: proposition
TITLE: Uniqueness
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-unique@L268-L271
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-unique@L272-L276
CONTRACT_ID: bpP:p14:sb-unique
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: w as in Proposition global; U subset R open convex, 0 in U; v: R -> Phase(2+2) with v(0)=w_0 and IsHamiltonianSolutionOn H_sec univ U v
SOURCE_QUANTIFIERS: for w, U, v
SOURCE_CONCLUSION: v=w on U (no regularity of v(t) is used beyond the predicate)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-un-1, stepP:p14:sb-un-2, stepP:p14:sb-un-3, bpP:p14:sb-global, bpP:p14:sb-defs#exactSecularHamiltonian, bpP:p0:d25-movsol#IsHamiltonianSolutionOn, bpP:p14:sb-smooth#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-un-1 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-unique@L273-L273 | agreement set
EDGE: stepP:p14:sb-un-2 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-unique@L274-L274 | open
EDGE: stepP:p14:sb-un-3 | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-unique@L275-L275 | conclusion
EDGE: bpP:p14:sb-global | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-unique@L269-L269 | the solution w
EDGE: bpP:p14:sb-defs#exactSecularHamiltonian | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-unique@L269-L269 | H_sec
EDGE: bpP:p0:d25-movsol#IsHamiltonianSolutionOn | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-unique@L269-L269 | IsHamiltonianSolutionOn
EDGE: bpP:p14:sb-smooth#data | blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-unique@L269-L269 | sigma, mu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: the field of Lemma field named in the \source note is not consumed: the C^1 field on S comes from Lemma pred

NODE: stepP:p14:sb-un-1
KIND: step
TITLE: The agreement set
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-un-1@L273-L273
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-un-1@L273-L273
CONTRACT_ID: stepP:p14:sb-un-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-unique; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-unique; no new binders
SOURCE_CONCLUSION: D={t in U: v(t)=w(t)} contains 0 and is closed in U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:d25-movsol#IsHamiltonianSolutionOn, bpP:p14:sb-global
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:d25-movsol#IsHamiltonianSolutionOn | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-un-1@L273-L273 | the predicate gives differentiability, hence continuity of v and w
EDGE: bpP:p14:sb-global | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-un-1@L273-L273 | w(0)=w_0 and w continuous
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-un-2
KIND: step
TITLE: Open
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-un-2@L274-L274
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-un-2@L274-L274
CONTRACT_ID: stepP:p14:sb-un-2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-unique; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-unique; t_0 in D
SOURCE_CONCLUSION: there is an open interval J_0 containing t_0 with J_0 subset U and J_0 subset D
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-pred, N:bpN:p3:gen-uniqueness, bpP:p14:sb-Sdef, bpP:p14:sb-global, stepP:p14:sb-un-1
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-pred | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-un-2@L274-L274 | v and w are IsSolIn X_H S J_0
EDGE: N:bpN:p3:gen-uniqueness | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-un-2@L274-L274 | uniqueness for C^1 fields on open sets
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-un-2@L274-L274 | S open
EDGE: bpP:p14:sb-global | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-un-2@L274-L274 | w(t_0) in S
EDGE: stepP:p14:sb-un-1 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-un-2@L274-L274 | t_0 in D and continuity of v
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-un-3
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-un-3@L275-L275
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-un-3@L275-L275
CONTRACT_ID: stepP:p14:sb-un-3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-unique; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-unique; no new binders
SOURCE_CONCLUSION: D=U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-x-top, stepP:p14:sb-un-1, stepP:p14:sb-un-2
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-x-top | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-un-3@L275-L275 | connectedness of an interval
EDGE: stepP:p14:sb-un-1 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-un-3@L275-L275 | D nonempty and closed in U
EDGE: stepP:p14:sb-un-2 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-un-3@L275-L275 | D open
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-th-1
KIND: step
TITLE: Actions and axes
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-1@L283-L283
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-1@L283-L283
CONTRACT_ID: stepP:p14:sb-th-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Box_sigma(w0) (i),(ii); sigma in [29/100,31/100]
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-safety; sigma, w0 fixed
SOURCE_CONCLUSION: 87/100<Lambda_0<23/10 and 87/100<Lambda_1<97/100
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-box#SecularInputBox, bpP:p14:sb-conv#secularAxis, bpP:p14:sb-box#jupiterSaturnWeights, bpP:p14:sb-numerics, bpP:p14:sb-x-alg
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-box#SecularInputBox | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-1@L283-L283 | a_0 in [103/20,21/4], a_1 in [189/20,193/20], Lambda_0>0
EDGE: bpP:p14:sb-conv#secularAxis | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-1@L283-L283 | a_i=(Lambda_i/m_i)^2
EDGE: bpP:p14:sb-box#jupiterSaturnWeights | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-1@L283-L283 | m=(1,sigma)
EDGE: bpP:p14:sb-numerics | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-1@L283-L283 | N2 and N3
EDGE: bpP:p14:sb-x-alg | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-1@L283-L283 | sqrt increasing
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-th-2
KIND: step
TITLE: Initial AMD
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-2@L285-L286
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-2@L285-L286
CONTRACT_ID: stepP:p14:sb-th-2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-safety; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-safety; sigma, w0
SOURCE_CONCLUSION: AMD(w0)<16373/2500000 via k_0>99819/100000, k_1>49877/50000, Gamma_0<(23/10)(181/100000), Gamma_1<(97/100)(123/50000)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-chart, bpP:p14:sb-numerics, bpP:p14:sb-box#SecularInputBox, stepP:p14:sb-th-1, bpP:p14:sb-conv#secularAMD, bpP:p14:sb-conv#secularGamma, bpP:p14:sb-conv#secularRoot, bpP:p14:sb-conv#secularEccVector
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-chart | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-2@L285-L285 | (a) k_i>0, k_i^2=1-e_i^2 and Gamma_i=Lambda_i(1-k_i)
EDGE: bpP:p14:sb-numerics | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-2@L285-L285 | N4a, N4b, N4c
EDGE: bpP:p14:sb-box#SecularInputBox | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-2@L285-L285 | ¦v_0¦<=3/50 and ¦v_1¦<=7/100
EDGE: stepP:p14:sb-th-1 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-2@L285-L285 | Lambda_0<23/10, Lambda_1<97/100
EDGE: bpP:p14:sb-conv#secularAMD | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-2@L286-L286 | AMD=Gamma_0+Gamma_1
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-2@L285-L285 | Gamma_i
EDGE: bpP:p14:sb-conv#secularRoot | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-2@L285-L285 | k_i
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-2@L285-L285 | e_i=¦v_i¦
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-th-3
KIND: step
TITLE: $w_0\in\mathcal S$
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-3@L288-L288
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-3@L288-L288
CONTRACT_ID: stepP:p14:sb-th-3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-safety; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-safety; no new binders
SOURCE_CONCLUSION: w0 in S and the hypotheses of Lemma slow hold (AMD(w0)<16373/2500000, Lambda_i(w0)>87/100)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-th-2, stepP:p14:sb-th-1, bpP:p14:sb-numerics, bpP:p14:sb-box#SecularInputBox, bpP:p14:sb-Sdef, bpP:p14:sb-conv#secularGamma, bpP:p14:sb-conv#secularAMD
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-th-2 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-3@L288-L288 | Gamma_i<=AMD(w0)<16373/2500000
EDGE: stepP:p14:sb-th-1 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-3@L288-L288 | Lambda_i>87/100
EDGE: bpP:p14:sb-numerics | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-3@L288-L288 | N6b and N6a
EDGE: bpP:p14:sb-box#SecularInputBox | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-3@L288-L288 | axis ranges and Lambda_i>0
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-3@L288-L288 | membership conditions of S
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-3@L288-L288 | Gamma_i
EDGE: bpP:p14:sb-conv#secularAMD | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-3@L288-L288 | AMD
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-th-4
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-4@L290-L290
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-4@L290-L290
CONTRACT_ID: stepP:p14:sb-th-4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-safety; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-safety; no new binders
SOURCE_CONCLUSION: w with w(0)=w_0, w(t) in S, Lambda constant, AMD(w(t))=AMD(w_0)<16373/2500000 for all t, solving IsHamiltonianSolutionOn H univ univ: clause (a) and the conserved clauses of (c)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-global, stepP:p14:sb-th-3, stepP:p14:sb-th-2, bpP:p14:sb-defs#exactSecularHamiltonian, bpP:p0:d25-movsol#IsHamiltonianSolutionOn, bpP:p14:sb-conv#secularAMD, bpP:p0:blocks#fast, bpP:p14:sb-Sdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-global | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-4@L290-L290 | the global solution
EDGE: stepP:p14:sb-th-3 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-4@L290-L290 | w0 in S and the hypotheses of Lemma slow, hence of Proposition global
EDGE: stepP:p14:sb-th-2 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-4@L290-L290 | AMD(w0)<16373/2500000
EDGE: bpP:p14:sb-defs#exactSecularHamiltonian | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-4@L290-L290 | H
EDGE: bpP:p0:d25-movsol#IsHamiltonianSolutionOn | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-4@L290-L290 | IsHamiltonianSolutionOn
EDGE: bpP:p14:sb-conv#secularAMD | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-4@L290-L290 | secularAMD
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-4@L290-L290 | fast(w(t))_2=fast(w_0)_2
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-4@L290-L290 | the statement or conditional application uses the region S or its affine slice S-prime
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-th-5
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-5@L292-L292
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-5@L292-L292
CONTRACT_ID: stepP:p14:sb-th-5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-safety; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-safety; no new binders
SOURCE_CONCLUSION: clause (b): v(t)=w(t) for all t in U; the hypothesis Reg(v(t)) is not needed
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-unique, stepP:p14:sb-th-4, bpP:p0:d25-movsol#IsHamiltonianSolutionOn
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-unique | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-5@L292-L292 | uniqueness among IsHamiltonianSolutionOn solutions on U
EDGE: stepP:p14:sb-th-4 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-5@L292-L292 | w is the solution of Proposition global
EDGE: bpP:p0:d25-movsol#IsHamiltonianSolutionOn | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-5@L292-L292 | IsHamiltonianSolutionOn
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-th-6
KIND: step
TITLE: Eccentricities
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-6@L294-L294
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-6@L294-L294
CONTRACT_ID: stepP:p14:sb-th-6
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-safety; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-safety; for every t
SOURCE_CONCLUSION: ¦v_i(w(t))¦<3/20 (i=0,1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-th-4, stepP:p14:sb-th-1, bpP:p14:sb-numerics, bpP:p14:sb-chart, bpP:p14:sb-conv#secularRoot, bpP:p14:sb-conv#secularGamma, bpP:p14:sb-conv#secularEccVector
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-th-4 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-6@L294-L294 | Lambda_i(w(t))=Lambda_i and AMD(w(t))<16373/2500000
EDGE: stepP:p14:sb-th-1 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-6@L294-L294 | Lambda_i>87/100
EDGE: bpP:p14:sb-numerics | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-6@L294-L294 | N5a, N5b
EDGE: bpP:p14:sb-chart | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-6@L294-L294 | (a) e_i^2=1-k_i^2
EDGE: bpP:p14:sb-conv#secularRoot | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-6@L294-L294 | k_i
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-6@L294-L294 | Gamma_i
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-6@L294-L294 | e_i=¦v_i¦
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-th-7
KIND: step
TITLE: Regularity
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-7@L296-L296
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-7@L296-L296
CONTRACT_ID: stepP:p14:sb-th-7
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-safety; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-safety; for every t
SOURCE_CONCLUSION: Reg_{sigma,mu}(w(t)): (i),(ii) and (iii),(iv)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-S, stepP:p14:sb-th-8, bpP:p14:sb-smooth-prop, stepP:p14:sb-th-4, bpP:p14:sb-regular#SecularRegular, bpP:p0:nocoll#NoCollision, bpP:p14:sb-Sdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-S | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-7@L296-L296 | Reg (i),(ii): J_i>0 and NoColl
EDGE: stepP:p14:sb-th-8 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-7@L296-L296 | bridge from z(w;F)_1 to q_i(w;F_i)
EDGE: bpP:p14:sb-smooth-prop | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-7@L296-L296 | (c) gives (iii),(iv)
EDGE: stepP:p14:sb-th-4 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-7@L296-L296 | w(t) in S
EDGE: bpP:p14:sb-regular#SecularRegular | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-7@L296-L296 | the predicate Reg
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-7@L296-L296 | NoColl
EDGE: bpP:p14:sb-Sdef | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-7@L296-L296 | the statement or conditional application uses the region S or its affine slice S-prime
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-th-8
KIND: step
TITLE: Bridge
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-8@L298-L298
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-8@L298-L298
CONTRACT_ID: stepP:p14:sb-th-8
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): m: Fin 2 -> R, w in Phase(2+2), F: Fin 2 -> R, i in Fin 2; the inverse identities of finProdFinEquiv are structural facts, not assumptions
SOURCE_QUANTIFIERS: for every m, w, F and i of the indicated types; no ellipticity, regularity, box or orbit premise
SOURCE_CONCLUSION: bodyVector(z(w;F)_1) i=q_i(w;F_i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:body#bodyVector, bpP:p14:sb-defs#ellipsePhase, bpP:p14:sb-defs#ellipsePosition
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-8@L298-L298 | bodyVector of the positions
EDGE: bpP:p14:sb-defs#ellipsePhase | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-8@L298-L298 | coordinates of z(w;F)_1 via finProdFinEquiv.symm
EDGE: bpP:p14:sb-defs#ellipsePosition | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-8@L298-L298 | q_i(w;F_i)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-th-9
KIND: step
TITLE: Radii
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-9@L300-L300
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-9@L300-L300
CONTRACT_ID: stepP:p14:sb-th-9
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-safety; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-safety; for every t, F
SOURCE_CONCLUSION: for i=0,1: a_i(1-3/20)<=¦q_i¦<=a_i(1+3/20); for i=0: 1751/400<=¦q_0¦<=483/80<=4439/400; for i=1: (189/20)(17/20)<=¦q_1¦<=4439/400 and (189/20)(17/20)>=1751/400; hence 1751/400<=¦q_i¦<=4439/400 for both planets
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-chart, stepP:p14:sb-th-6, bpP:p14:sb-numerics, bpP:p14:sb-box#SecularInputBox, stepP:p14:sb-th-4, bpP:p14:sb-conv#secularAxis, bpP:p0:plane#planeLength
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-chart | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-9@L300-L300 | (c) a_i(1-e_i)<=¦q_i¦<=a_i(1+e_i)
EDGE: stepP:p14:sb-th-6 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-9@L300-L300 | e_i<3/20
EDGE: bpP:p14:sb-numerics | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-9@L300-L300 | N7a, N7c
EDGE: bpP:p14:sb-box#SecularInputBox | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-9@L300-L300 | axis ranges 103/20..21/4 and 189/20..193/20
EDGE: stepP:p14:sb-th-4 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-9@L300-L300 | Lambda(w(t))=Lambda(w_0)
EDGE: bpP:p14:sb-conv#secularAxis | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-9@L300-L300 | a_i
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-9@L300-L300 | ¦q_i¦
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-th-10
KIND: step
TITLE: Gap
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-10@L302-L302
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-10@L302-L302
CONTRACT_ID: stepP:p14:sb-th-10
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-safety; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-safety; for every t, F
SOURCE_CONCLUSION: ¦q_1¦-¦q_0¦>=399/200
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-th-9, bpP:p14:sb-numerics
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-th-9 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-10@L302-L302 | the same radial bounds with the box axis ranges
EDGE: bpP:p14:sb-numerics | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-10@L302-L302 | N7b
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-delta-P-a
REVIEWER: sol-delta2-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-th-11
KIND: step
TITLE: Pair bounds
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-11@L304-L306
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-11@L304-L306
CONTRACT_ID: stepP:p14:sb-th-11
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-safety; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-safety; for every t, F
SOURCE_CONCLUSION: PairBounds(399/200,4439/200; barycentricPositions 1 m mu (z(w(t);F)_1)): all ¦Q_j-Q_i¦ in [399/200,4439/200]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p14:sb-th-8, stepP:p14:sb-th-9, stepP:p14:sb-th-10, bpP:p14:sb-numerics, bpP:p0:barycentric#barycentricPositions, bpP:p0:nocoll#PairBounds, bpP:p0:body#bodyVector, bpP:p0:plane#planeLength, bpP:p6:ext-tri, bpP:p6:plane
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p14:sb-th-8 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-11@L304-L304 | b_j=q_j(w(t);F_j)
EDGE: stepP:p14:sb-th-9 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-11@L304-L304 | Sun-planet bounds
EDGE: stepP:p14:sb-th-10 | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-11@L304-L304 | planet-planet lower bound
EDGE: bpP:p14:sb-numerics | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-11@L304-L304 | N7c, N7d
EDGE: bpP:p0:barycentric#barycentricPositions | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-11@L304-L304 | barycentricPositions formula
EDGE: bpP:p0:nocoll#PairBounds | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-11@L304-L304 | PairBounds
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-11@L304-L304 | bodyVector
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-11@L304-L304 | triangle inequality for planeLength
EDGE: bpP:p6:ext-tri | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-11@L304-L304 | the planet-pair lower bound uses the reverse triangle inequality
EDGE: bpP:p6:plane | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-th-11@L304-L304 | physical planar length satisfies the triangle inequality and is invariant under sign reversal
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p14:sb-ci-1
KIND: step
TITLE: Instantiation
STATEMENT_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ci-1@L310-L310
PROOF_SOURCE: blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ci-1@L310-L310
CONTRACT_ID: stepP:p14:sb-ci-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpP:p14:sb-cited; previous proof steps and cited results are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of bpP:p14:sb-cited; for the given w0
SOURCE_CONCLUSION: the conclusion of Theorem sb-safety for sigma=476/1591, mu=4773/5000000, which is literally the claim
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p14:sb-safety, bpP:p14:sb-numerics, bpP:p14:sb-box#SecularInputBox
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p14:sb-safety | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ci-1@L310-L310 | Theorem sb-safety instantiated
EDGE: bpP:p14:sb-numerics | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ci-1@L310-L310 | N1: 29/100<=476/1591<=31/100 and mu>0
EDGE: bpP:p14:sb-box#SecularInputBox | blueprint-P/parts/p14b-secular-box.tex#stepP:p14:sb-ci-1@L310-L310 | hypothesis Box_{476/1591}(w0)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p14b+sol-review-P-b
REVIEWER: sol-delta-P-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
