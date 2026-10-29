NODE: bpI:p6:det-formula
KIND: lemma
TITLE: Determinant of the Kepler bordered matrix
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:det-formula@L13-L19
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:det-formula@L20-L35
CONTRACT_ID: bpI:p6:det-formula
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa, Omega in R and L > 0 (no sign condition on kappa, Omega)
SOURCE_QUANTIFIERS: kappa, Omega, L
SOURCE_CONCLUSION: det K_{kappa,Omega}(L) = 3 kappa Omega^2 / L^4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p6:expand, stepI:p6:eval, bpI:p0:keplerborder#keplerBorder
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p6:expand | blueprint-I/parts/p6-kepler.tex#bpI:p6:det-formula@L21-L21 | proof step: Sarrus expansion
EDGE: stepI:p6:eval | blueprint-I/parts/p6-kepler.tex#bpI:p6:det-formula@L29-L29 | proof step: evaluation of the expansion
EDGE: bpI:p0:keplerborder#keplerBorder | blueprint-I/parts/p6-kepler.tex#bpI:p6:det-formula@L16-L16 | K_{kappa,Omega}(L) is the frozen Kepler bordered matrix
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.keplerBorder_det (KAM/Iso/Kepler.lean)
LEAN_NOTE: audit W1-seal-1 PASS: all real kappa, Omega, positive L, exact rational determinant
NOTE: -

NODE: stepI:p6:expand
KIND: step
TITLE: Expansion
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:expand@L21-L28
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:expand@L21-L28
CONTRACT_ID: stepI:p6:expand
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa, Omega in R, L > 0; entries of K_{kappa,Omega}(L) from Definition keplerborder
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: K = (k_ij) with k11=-3kappa/L^4, k13=k31=kappa/L^3, k23=k32=-Omega, other entries 0; det K = k11k22k33+k12k23k31+k13k21k32-k13k22k31-k12k21k33-k11k23k32
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:keplerborder#keplerBorder
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:keplerborder#keplerBorder | blueprint-I/parts/p6-kepler.tex#stepI:p6:expand@L23-L23 | entries of the frozen matrix keplerBorder (carrier L > 0)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row names or confirms this step
NOTE: -

NODE: stepI:p6:eval
KIND: step
TITLE: Evaluation
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:eval@L29-L34
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:eval@L29-L34
CONTRACT_ID: stepI:p6:eval
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Sarrus expansion of step expand; k12 = k21 = k22 = k33 = 0
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: det K_{kappa,Omega}(L) = -k11 k23 k32 = 3 kappa Omega^2 / L^4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p6:expand
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p6:expand | blueprint-I/parts/p6-kepler.tex#stepI:p6:eval@L30-L30 | uses the entries and the expansion of the previous step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row names or confirms this step
NOTE: -

NODE: bpI:p6:kepler
KIND: theorem
TITLE: I-KEPLER, proof
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:kepler@L37-L42
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:kepler@L43-L48
CONTRACT_ID: bpI:p6:kepler
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa, Omega > 0; L > 0
SOURCE_QUANTIFIERS: kappa, Omega first, then L in the subtype {L : R | 0 < L}
SOURCE_CONCLUSION: det K_{kappa,Omega}(L) = 3 kappa Omega^2 / L^4 and det K_{kappa,Omega}(L) > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p6:k-value, stepI:p6:k-pos, bpI:p0:keplerborder#keplerBorder
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p6:k-value | blueprint-I/parts/p6-kepler.tex#bpI:p6:kepler@L44-L44 | proof step Value
EDGE: stepI:p6:k-pos | blueprint-I/parts/p6-kepler.tex#bpI:p6:kepler@L46-L46 | proof step Positivity
EDGE: bpI:p0:keplerborder#keplerBorder | blueprint-I/parts/p6-kepler.tex#bpI:p6:kepler@L38-L38 | K_{kappa,Omega}(L) is the frozen matrix keplerBorder
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.kepler_bordered_det (KAM/Frozen/Iso/Theorems/KeplerBorderedDet.lean); KAM.Iso.keplerBorder_det_pos (KAM/Iso/Kepler.lean)
LEAN_NOTE: I-KEPLER anchor SEALED (manifest); audit W1-seal-1 PASS WITH NOTES
NOTE: Proof of the frozen anchor bpI:p0:kepler (see its EDGE there); statement reference to the anchor dropped by SPEC (proved-in)

NODE: stepI:p6:k-value
KIND: step
TITLE: Value
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:k-value@L44-L44
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:k-value@L44-L44
CONTRACT_ID: stepI:p6:k-value
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa, Omega > 0, L > 0
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: det K_{kappa,Omega}(L) = 3 kappa Omega^2 / L^4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:det-formula
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:det-formula | blueprint-I/parts/p6-kepler.tex#stepI:p6:k-value@L44-L44 | the determinant formula, valid for all real kappa, Omega
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row names or confirms this step
NOTE: -

NODE: stepI:p6:k-pos
KIND: step
TITLE: Positivity
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:k-pos@L46-L47
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:k-pos@L46-L47
CONTRACT_ID: stepI:p6:k-pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa > 0, Omega != 0, L > 0; value of step k-value
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: 3 kappa Omega^2 / L^4 > 0, hence det K > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p6:k-value
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p6:k-value | blueprint-I/parts/p6-kepler.tex#stepI:p6:k-pos@L46-L46 | the value whose numerator and denominator are shown positive
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row names or confirms this step
NOTE: -

NODE: bpI:p6:kep-ham
KIND: definition
TITLE: The Kepler--rotation Hamiltonian
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-ham@L58-L67
PROOF_SOURCE: -
CONTRACT_ID: bpI:p6:kep-ham
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: kappa, Omega in R
SOURCE_QUANTIFIERS: kappa, Omega, then I in C^2 with I_1 != 0
SOURCE_CONCLUSION: defines h_{kappa,Omega}(I) = -kappa/(2 I_1^2) - Omega I_2 on C^2 (Lean division; value at I_1 = 0 never used); holomorphic on the open set {I_1 != 0}; real at real I with I_1 != 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerRotH, differentiableOn_keplerRotH, keplerRotH_real (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-1 PASS WITH NOTES; definition + holomorphy off I_1=0 + reality
NOTE: standing definition package of Parts 6-8 (SPEC)

NODE: bpI:p6:kep-border
KIND: lemma
TITLE: Frequency map and bordered Hessian of $h_{\kappa,\Omega}$
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L69-L87
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L88-L108
CONTRACT_ID: bpI:p6:kep-border
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa, Omega in R; I in R^2 with I_1 > 0
SOURCE_QUANTIFIERS: kappa, Omega, then I
SOURCE_CONCLUSION: frequencyMap h_{kappa,Omega} I = (kappa/I_1^3, -Omega); D(frequencyMap h)(I) = [[-3kappa/I_1^4,0],[0,0]]; borderedHessian h_{kappa,Omega} I = reindex_eps K_{kappa,Omega}(I_1); det borderedHessian h I = 3 kappa Omega^2 / I_1^4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:kep-ham, bpI:p0:realham#frequencyMap, bpI:p0:bordered#borderedHessian, bpI:p0:keplerborder#keplerBorder, stepI:p6:kb-real, stepI:p6:kb-grad, stepI:p6:kb-hess, stepI:p6:kb-entries, stepI:p6:kb-det
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L72-L72 | the Hamiltonian h_{kappa,Omega}
EDGE: bpI:p0:realham#frequencyMap | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L72-L72 | frozen frequencyMap of h
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L79-L79 | frozen borderedHessian of h
EDGE: bpI:p0:keplerborder#keplerBorder | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L79-L79 | frozen keplerBorder K_{kappa,Omega}(I_1)
EDGE: stepI:p6:kb-real | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L89-L89 | proof step
EDGE: stepI:p6:kb-grad | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L94-L94 | proof step
EDGE: stepI:p6:kb-hess | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L98-L98 | proof step
EDGE: stepI:p6:kb-entries | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L101-L101 | proof step
EDGE: stepI:p6:kb-det | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L106-L106 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: frequencyMap_keplerRotH, fderiv_frequencyMap_keplerRotH, borderedHessian_keplerRotH, det_borderedHessian_keplerRotH, finThreeEquivSumUnit (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-1 PASS WITH NOTES; all four clauses of the lemma
NOTE: -

NODE: stepI:p6:kb-real
KIND: step
TITLE: Real part near a real point
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-real@L89-L92
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-real@L89-L92
CONTRACT_ID: stepI:p6:kb-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa, Omega in R; I in R^2 with I_1 > 0; V = {J in R^2 : J_1 > 0} open
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: for J in V, h_{kappa,Omega}(iota J) is real and equals phi(J) = -kappa/(2 J_1^2) - Omega J_2; Re h(iota J) = phi(J) on the neighbourhood V of I
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:kep-ham
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-real@L90-L90 | h_{kappa,Omega} evaluated at real points
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: re_keplerRotH_real, keplerRotH_real (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-1 PASS WITH NOTES; named step kb-real (private helper re_keplerRotH_real)
NOTE: -

NODE: stepI:p6:kb-grad
KIND: step
TITLE: Gradient
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-grad@L94-L96
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-grad@L94-L96
CONTRACT_ID: stepI:p6:kb-grad
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: step kb-real; germ locality of the Frechet derivative
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: frequencyMap h J0 = grad phi(J0) = (kappa/J_1^3, -Omega) for J0 in V; on V the map frequencyMap h coincides with g(J) = (kappa J_1^-3, -Omega)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p6:kb-real, bpI:p0:realham#frequencyMap, bpI:p6:kep-ham
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p6:kb-real | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-grad@L95-L95 | Re h o iota agrees with phi near J0
EDGE: bpI:p0:realham#frequencyMap | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-grad@L95-L95 | frequencyMap is the real gradient of Re h o iota
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-grad@L95-L95 | the Hamiltonian h
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: frequencyMap_keplerRotH, hasFDerivAt_keplerRotH_real (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-1 PASS WITH NOTES; named step kb-grad
NOTE: -

NODE: stepI:p6:kb-hess
KIND: step
TITLE: Derivative of the frequency map
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-hess@L98-L99
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-hess@L98-L99
CONTRACT_ID: stepI:p6:kb-hess
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa,Omega in R; I in R^2 with I_1>0; h=h_{kappa,Omega} of Definition kep-ham
SOURCE_QUANTIFIERS: For every kappa,Omega in R and every real I with I_1>0
SOURCE_CONCLUSION: D(frequencyMap h)(I) = Dg(I), first row (-3kappa I_1^-4, 0), second row 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p6:kb-grad, bpI:p0:realham#frequencyMap, bpI:p6:kep-ham
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p6:kb-grad | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-hess@L98-L98 | frequencyMap h = g on the open set V, so derivatives agree
EDGE: bpI:p0:realham#frequencyMap | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-hess@L98-L98 | frequencyMap h
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-hess@L98-L99 | h or h~ is the Hamiltonian fixed by the Kepler package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: fderiv_frequencyMap_keplerRotH, hasFDerivAt_frequencyMap_keplerRotH (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-1 PASS WITH NOTES; named step kb-hess
NOTE: -

NODE: stepI:p6:kb-entries
KIND: step
TITLE: Entries of the bordered matrix
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-entries@L101-L104
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-entries@L101-L104
CONTRACT_ID: stepI:p6:kb-entries
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa,Omega in R; I in R^2 with I_1>0; h=h_{kappa,Omega} of Definition kep-ham; epsilon is the fixed bijection Fin 3 equiv Fin 2 plus Unit used in the enclosing statement
SOURCE_QUANTIFIERS: For every kappa,Omega in R and every real I with I_1>0
SOURCE_CONCLUSION: entries of borderedHessian h I: Dg(I) block, border entries g(I)_a, corner 0; these coincide with the entries of K_{kappa,Omega}(I_1); so borderedHessian h I = reindex_eps K_{kappa,Omega}(I_1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:bordered#borderedHessian, stepI:p6:kb-hess, stepI:p6:kb-grad, bpI:p0:keplerborder#keplerBorder, bpI:p6:kep-ham
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-entries@L101-L101 | definition of the bordered Hessian: block, border and corner entries
EDGE: stepI:p6:kb-hess | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-entries@L102-L102 | the Hessian block Dg(I)
EDGE: stepI:p6:kb-grad | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-entries@L102-L102 | the border entries g(I)_a
EDGE: bpI:p0:keplerborder#keplerBorder | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-entries@L103-L103 | entrywise comparison with keplerBorder at L = I_1
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-entries@L101-L104 | h or h~ is the Hamiltonian fixed by the Kepler package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: borderedHessian_keplerRotH (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-1 PASS WITH NOTES; named step kb-entries
NOTE: -

NODE: stepI:p6:kb-det
KIND: step
TITLE: Determinant
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-det@L106-L107
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-det@L106-L107
CONTRACT_ID: stepI:p6:kb-det
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa,Omega in R; I in R^2 with I_1>0; h=h_{kappa,Omega} of Definition kep-ham; epsilon is that same index bijection
SOURCE_QUANTIFIERS: For every kappa,Omega in R and every real I with I_1>0
SOURCE_CONCLUSION: det borderedHessian h I = det K_{kappa,Omega}(I_1) = 3 kappa Omega^2 / I_1^4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p6:kb-entries, bpI:p6:det-formula, bpI:p0:bordered#borderedHessian, bpI:p6:kep-ham
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p6:kb-entries | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-det@L106-L106 | borderedHessian h I = reindex K
EDGE: bpI:p6:det-formula | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-det@L107-L107 | value of det K at L = I_1 > 0
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-det@L106-L106 | determinant of the frozen bordered Hessian
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-det@L106-L107 | h or h~ is the Hamiltonian fixed by the Kepler package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: det_borderedHessian_keplerRotH (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-1 PASS WITH NOTES; named step kb-det (uses I-0 keplerBorder_det)
NOTE: -

NODE: bpI:p6:conversion-map
KIND: definition
TITLE: Period-one conversion map
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion-map@L112-L117
PROOF_SOURCE: -
CONTRACT_ID: bpI:p6:conversion-map
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (a definition)
SOURCE_QUANTIFIERS: theta, I in R^2 (and in C^2)
SOURCE_CONCLUSION: defines S(theta, I) = (2 pi theta, I/(2 pi)) on R^2 x R^2 and on C^2 x C^2; linear isomorphism; maps Z^2-translations of theta to 2 pi Z^2-translations of (ell, g)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: periodOneMap, periodOneMapC, periodOneCLM, periodOneInvCLM (KAM/Iso/Conversion.lean)
LEAN_NOTE: audit I-2 PASS WITH NOTES; definition landed
NOTE: 2 pi conversion package of Parts 6-8 (SPEC); the K reference in its \source is provenance

NODE: bpI:p6:conversion
KIND: lemma
TITLE: Conversion
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L119-L141
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L142-L155
CONTRACT_ID: bpI:p6:conversion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa, Omega in R; kappa' = kappa (2 pi)^2, Omega' = Omega/(2 pi); (a) H differentiable; (b) I in C^2 with I_1 != 0; (c),(d) I in R^2 with I_1 > 0
SOURCE_QUANTIFIERS: kappa, Omega first (then kappa', Omega'), then H or I
SOURCE_CONCLUSION: (a) D S^T J D S = J = D S J D S^T, D S X_{H o S} = X_H o S, and w solves w' = X_{H o S}(w) iff S w solves y' = X_H(y); (b) h_{kappa,Omega}(I/(2 pi)) = h_{kappa',Omega'}(I), so h~ is the Kepler-rotation Hamiltonian of the converted constants, holomorphic on {I_1 != 0}, real at real I; (c) grad h~(I) = (kappa'/I_1^3, -Omega') = (1/(2 pi)) grad h_{kappa,Omega}(I/(2 pi)); (d) K_{kappa',Omega'}(I_1) = D K_{kappa,Omega}(I_1/(2 pi)) D with D = diag(1/(2 pi), 1/(2 pi), 1), borderedHessian h~ I = reindex K_{kappa',Omega'}(I_1), det = 3 kappa' Omega'^2 / I_1^4 = 3 kappa Omega^2 / I_1^4; for kappa = Omega = 1, kappa' = (2pi)^2 > 0, Omega' = 1/(2pi) > 0 and det borderedHessian h~ I = 3/I_1^4 > 0 for real I_1 > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:conversion-map, bpI:p6:kep-ham, bpI:p0:keplerborder#keplerBorder, bpI:p0:bordered#borderedHessian, stepI:p6:cv-sympl, stepI:p6:cv-ham, stepI:p6:cv-border
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L122-L122 | the conversion S
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L126-L126 | h_{kappa,Omega} and h_{kappa',Omega'}
EDGE: bpI:p0:keplerborder#keplerBorder | blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L132-L132 | K_{kappa,Omega} and K_{kappa',Omega'}
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L133-L133 | borderedHessian of h~
EDGE: stepI:p6:cv-sympl | blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L143-L143 | proof of (a)
EDGE: stepI:p6:cv-ham | blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L149-L149 | proof of (b)
EDGE: stepI:p6:cv-border | blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L151-L151 | proof of (c) and (d)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-review-I-p67
REVIEWER: sol-delta-I-c
LEAN_STATUS: PROVED
LEAN_REF: periodOneMap_symplectic, periodOneMap_hamiltonianVectorField, periodOneMap_hasDerivAt_iff, keplerRotH_comp_div, frequencyMap_comp_div, keplerBorder_conversion, borderedHessian_conversion (KAM/Iso/Conversion.lean)
LEAN_NOTE: audit I-2 PASS WITH NOTES; parts (a)-(d); (b) proved in stronger total-division form
NOTE: -

NODE: stepI:p6:cv-sympl
KIND: step
TITLE: Symplectic
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-sympl@L143-L147
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-sympl@L143-L147
CONTRACT_ID: stepI:p6:cv-sympl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: S as in Definition conversion-map; J = [[0,1],[-1,0]]; H differentiable
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: D S = diag(2pi,2pi,1/(2pi),1/(2pi)); D S^T J D S = J = D S J D S^T; D S X_{H o S} = X_H o S; d/dt (S w) = D S w'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:conversion-map
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-sympl@L143-L143 | D S of the conversion map
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: periodOneMap_symplectic, periodOneMap_hamiltonianVectorField, periodOneMap_hasDerivAt_iff (KAM/Iso/Conversion.lean)
LEAN_NOTE: audit I-2 PASS WITH NOTES; named step cv-sympl
NOTE: -

NODE: stepI:p6:cv-ham
KIND: step
TITLE: Hamiltonian
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-ham@L149-L149
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-ham@L149-L149
CONTRACT_ID: stepI:p6:cv-ham
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I in C^2 with I_1 != 0
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: h_{kappa,Omega}(I/(2 pi)) = h_{kappa',Omega'}(I) (field arithmetic)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:kep-ham, bpI:p6:conversion-map
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-ham@L149-L149 | h_{kappa,Omega} at I/(2 pi) and h_{kappa',Omega'} at I
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-ham@L149-L149 | the substitution I -> I/(2 pi) is the action part of S
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerRotH_comp_div (KAM/Iso/Conversion.lean)
LEAN_NOTE: audit I-2 PASS WITH NOTES; named step cv-ham
NOTE: -

NODE: stepI:p6:cv-border
KIND: step
TITLE: Frequencies and bordered Hessian
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-border@L151-L154
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-border@L151-L154
CONTRACT_ID: stepI:p6:cv-border
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lemma kep-border for (kappa', Omega'); part (b); I real with I_1 > 0
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: grad h~(I) = (kappa'/I_1^3, -Omega') = (1/(2 pi)) grad h_{kappa,Omega}(I/(2 pi)); K_{kappa',Omega'}(I_1) = D K_{kappa,Omega}(I_1/(2 pi)) D entrywise; borderedHessian h~ I = reindex K_{kappa',Omega'}(I_1); det = 3 kappa' Omega'^2/I_1^4 = 3 kappa Omega^2/I_1^4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:kep-border, stepI:p6:cv-ham, bpI:p6:kep-ham, bpI:p6:conversion-map, bpI:p0:keplerborder#keplerBorder, bpI:p6:det-formula
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:kep-border | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-border@L151-L151 | applied to (kappa', Omega')
EDGE: stepI:p6:cv-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-border@L151-L151 | part (b): h~ = h_{kappa',Omega'}
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-border@L151-L151 | h~ is a Kepler-rotation Hamiltonian
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-border@L151-L151 | chain rule for I -> I/(2 pi)
EDGE: bpI:p0:keplerborder#keplerBorder | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-border@L153-L153 | entries of K_{kappa',Omega'}(I_1)
EDGE: bpI:p6:det-formula | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-border@L154-L154 | det K_{kappa,Omega}(L) at L = I_1/(2 pi) gives the second value of the determinant
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: frequencyMap_comp_div, keplerBorder_conversion, borderedHessian_conversion (KAM/Iso/Conversion.lean)
LEAN_NOTE: audit I-2 PASS WITH NOTES; named step cv-border
NOTE: -

NODE: bpI:p6:nondeg
KIND: corollary
TITLE: Nondegeneracy in period-one variables
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L157-L159
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L160-L163
CONTRACT_ID: bpI:p6:nondeg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa = Omega = 1; B subset {I in R^2 : I_1 > 0}; 0 < r_0 <= (1/2) inf_B I_1
SOURCE_QUANTIFIERS: B and r_0 (B_{r_0} as in Part 0)
SOURCE_CONCLUSION: h~ = h_{(2pi)^2,1/(2pi)} holomorphic on {I in C^2 : I_1 != 0}, real at real I, det borderedHessian h~ I = 3/I_1^4 > 0 for real I with I_1 > 0; h~ holomorphic on B_{r_0}, every real I in B_{r_0} has I_1 > 0, and det borderedHessian h~ I != 0 for every real I in B_{r_0} (nondegeneracy hypothesis of the frozen I-HEAD)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:conversion, bpI:p6:kep-border, bpI:p6:kep-ham, bpI:p0:bordered#borderedHessian, bpI:p0:domains#actionNbhd, stepI:p6:nd-domain, stepI:p6:nd-concl
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:conversion | blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L158-L158 | (b),(d): h~ and its bordered Hessian determinant
EDGE: bpI:p6:kep-border | blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L158-L158 | determinant formula for real I with I_1 > 0
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L158-L158 | h~ = h_{(2pi)^2,1/(2pi)}
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L158-L158 | borderedHessian h~
EDGE: bpI:p0:domains#actionNbhd | blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L158-L158 | B_{r_0} is the frozen action neighbourhood
EDGE: stepI:p6:nd-domain | blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L161-L161 | proof step Domain
EDGE: stepI:p6:nd-concl | blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L162-L162 | proof step Conclusion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: nondeg_period_one (KAM/Iso/Conversion.lean); differentiableOn_keplerRotH, keplerRotH_real, det_borderedHessian_keplerRotH (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-2 PASS WITH NOTES; nondeg_period_one plus imported I-1 API cover all clauses (I-2 audit says so)
NOTE: -

NODE: stepI:p6:nd-domain
KIND: step
TITLE: Domain
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-domain@L161-L161
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-domain@L161-L161
CONTRACT_ID: stepI:p6:nd-domain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B subset {I_1 > 0}, 0 < r_0 <= (1/2) inf_B I_1; I in B_{r_0}
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: there is J in B with |Re I_1 - J_1| < r_0 <= J_1/2, so Re I_1 > J_1/2 > 0; hence I_1 != 0, and I_1 > 0 for real I
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:domains#actionNbhd
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:domains#actionNbhd | blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-domain@L161-L161 | definition of B_{r_0}: I within r_0 of some J in B
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: nondeg_period_one (KAM/Iso/Conversion.lean)
LEAN_NOTE: audit I-2 PASS WITH NOTES; named step nd-domain
NOTE: -

NODE: stepI:p6:nd-concl
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-concl@L162-L162
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-concl@L162-L162
CONTRACT_ID: stepI:p6:nd-concl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa=Omega=1, h_tilde=h_{(2 pi)^2,1/(2 pi)}; B subset {I in R^2:I_1>0}, 0<r_0<=inf_B I_1/2, as in the enclosing nondegeneracy corollary
SOURCE_QUANTIFIERS: With kappa=Omega=1 fixed, for every B,r_0 satisfying the enclosing corollary, and every real I in B_{r_0} for the determinant assertion
SOURCE_CONCLUSION: h~ holomorphic on B_{r_0}, real at real I, and det borderedHessian h~ I = 3/I_1^4 > 0 for real I in B_{r_0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:conversion, bpI:p6:kep-border, stepI:p6:nd-domain, bpI:p6:kep-ham
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:conversion | blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-concl@L162-L162 | (b),(d) with kappa = Omega = 1
EDGE: bpI:p6:kep-border | blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-concl@L162-L162 | bordered Hessian determinant
EDGE: stepI:p6:nd-domain | blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-concl@L162-L162 | I_1 != 0 (and > 0 for real I) on B_{r_0}
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-concl@L162-L162 | h or h~ is the Hamiltonian fixed by the Kepler package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: nondeg_period_one (KAM/Iso/Conversion.lean); det_borderedHessian_keplerRotH (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-2 PASS WITH NOTES; named step nd-concl
NOTE: -

NODE: bpI:p7:x-hol
KIND: external
TITLE: Holomorphic functions of several variables
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:x-hol@L32-L34
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:x-hol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: holomorphic functions on open subsets of C^m
SOURCE_CONCLUSION: sums, products, compositions and quotients (nonvanishing denominator) of holomorphic functions are holomorphic; exp, sin, cos entire; z^{-1/2} = exp(-(1/2) Log z) holomorphic on {Re z > 0} with |z^{-1/2}| = |z|^{-1/2} <= (Re z)^{-1/2} and z^{-1/2} = 1/sqrt z for z > 0; sqrt holomorphic on {Re z > 0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p7:x-weier
KIND: external
TITLE: Weierstrass
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:x-weier@L35-L35
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:x-weier
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a sequence of holomorphic functions on an open set of C^m converging uniformly
SOURCE_QUANTIFIERS: open set U in C^m, functions f_m
SOURCE_CONCLUSION: the uniform limit is holomorphic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p7:x-param
KIND: external
TITLE: Parameter integrals
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:x-param@L36-L36
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:x-param
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Phi holomorphic on an open U in C^m x C with (q, t mu) in U for all t in [0,1]
SOURCE_QUANTIFIERS: Phi, U
SOURCE_CONCLUSION: (q, mu) -> int_0^1 Phi(q, t mu) dt is holomorphic on that set
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p7:x-schwarz
KIND: external
TITLE: Schwarz lemma (maximum modulus)
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:x-schwarz@L37-L37
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:x-schwarz
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: g holomorphic on a neighbourhood of the closed disc D(0, varrho), g(0) = 0
SOURCE_QUANTIFIERS: g, varrho, then mu with |mu| <= varrho
SOURCE_CONCLUSION: |g(mu)| <= (|mu|/varrho) max_{|zeta| = varrho} |g(zeta)|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p7:x-ift
KIND: external
TITLE: Inverse function theorem (real-analytic)
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:x-ift@L38-L38
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:x-ift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: real-analytic map between open subsets of R^m with invertible differential at every point
SOURCE_QUANTIFIERS: the map
SOURCE_CONCLUSION: it is a local real-analytic diffeomorphism; if bijective, it is a real-analytic diffeomorphism
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p7:x-forms
KIND: external
TITLE: Exterior calculus on open subsets of $\R^m$
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:x-forms@L39-L40
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:x-forms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: forms on open subsets of R^m; F smooth with F^*(sum p_i dq_i) = sum P_i dQ_i + dS for a smooth S
SOURCE_QUANTIFIERS: F, S
SOURCE_CONCLUSION: d^2 = 0; d commutes with pull-back by smooth maps; a form is determined by its values on tangent vectors; and DF^T J DF = J (sum dP_i wedge dQ_i standing for -J in the order Q, P)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p7:ham-eq
KIND: lemma
TITLE: Hamilton's equations
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L51-L57
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L58-L70
CONTRACT_ID: bpI:p7:ham-eq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: mu in R; W_mu as in section data
SOURCE_QUANTIFIERS: mu in R, then z in W_mu / J subset R, z : J -> R^2 x R^2
SOURCE_CONCLUSION: H^R3_mu is C^infty (real-analytic) on W_mu and V_mu = X_{H^R3_mu} = (d_p H, -d_q H) at every point of W_mu; RSol_mu(J,z) holds iff for every t in J: z(t) in W_mu and z differentiable at t with z'(t) = X_H(z(t)); IsRestrictedSolutionOn iff IsSolIn for V_mu on W_mu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:sec-ham#data, bpI:p0:restricted#restrictedHamiltonian, bpI:p0:restricted#restrictedVectorField, bpI:p0:restricted#IsRestrictedSolutionOn, bpI:p0:primaries#CollisionFree, bpN:p3:newton-reduction, stepI:p7:he-smooth, stepI:p7:he-deriv, stepI:p7:he-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:sec-ham#data | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L52-L52 | W_mu and the formulas for H^R3_mu, V_mu
EDGE: bpI:p0:restricted#restrictedHamiltonian | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L52-L52 | frozen restrictedHamiltonian
EDGE: bpI:p0:restricted#restrictedVectorField | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L52-L52 | frozen restrictedVectorField
EDGE: bpI:p0:restricted#IsRestrictedSolutionOn | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L53-L53 | RSol_mu
EDGE: bpI:p0:primaries#CollisionFree | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L53-L53 | collision-freeness clause
EDGE: bpN:p3:newton-reduction | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L54-L54 | shared ODE layer: IsRestrictedSolutionOn iff IsSolIn
EDGE: stepI:p7:he-smooth | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L59-L59 | proof step
EDGE: stepI:p7:he-deriv | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L61-L61 | proof step
EDGE: stepI:p7:he-sol | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L69-L69 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: analyticOnNhd_restrictedHamTotal, restrictedVectorField_eq_hamiltonian, isRestrictedSolutionOn_iff, restrictedHamiltonian_eq (KAM/Iso/RestrictedHam.lean)
LEAN_NOTE: audit I-3 PASS WITH NOTES (p7:ham-eq rows); steps he-* not named in audit, left
NOTE: -

NODE: stepI:p7:he-smooth
KIND: step
TITLE: Smoothness
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-smooth@L59-L59
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-smooth@L59-L59
CONTRACT_ID: stepI:p7:he-smooth
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: mu in R; z = (q,p) in W_mu
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: r_j^2 = theta(q - a_j) is a polynomial positive on W_mu; r_j and 1/r_j are C^infty (real-analytic) on W_mu; the remaining terms of H^R3_mu are polynomial
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:sec-ham#data, bpI:p0:primaries#radiusSq, bpI:p0:primaries#radius, bpI:p0:restricted#restrictedHamiltonian
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:sec-ham#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-smooth@L59-L59 | W_mu, r_j
EDGE: bpI:p0:primaries#radiusSq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-smooth@L59-L59 | r_j^2 = radiusSq
EDGE: bpI:p0:primaries#radius | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-smooth@L59-L59 | r_j = rad
EDGE: bpI:p0:restricted#restrictedHamiltonian | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-smooth@L59-L59 | terms of H^R3_mu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row names or confirms this step
NOTE: -

NODE: stepI:p7:he-deriv
KIND: step
TITLE: Derivatives
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-deriv@L61-L67
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-deriv@L61-L67
CONTRACT_ID: stepI:p7:he-deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: mu in R; z=(q,p) in the collision-free set W_mu of L48-49; r_j=rad(q-primary_j(mu))
SOURCE_QUANTIFIERS: For every mu in R and every z in W_mu
SOURCE_CONCLUSION: (d_p H, -d_q H) = ((p_0+q_1, p_1-q_0), (p_1,-p_0) - (1-mu)(q-a_1)/r_1^3 - mu (q-a_2)/r_2^3) = V_mu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:he-smooth, bpI:p0:restricted#restrictedHamiltonian, bpI:p0:primaries#primary1, bpI:p0:primaries#primary2, bpI:p0:restricted#restrictedVectorField, bpI:p7:sec-ham#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:he-smooth | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-deriv@L61-L61 | differentiability of H^R3_mu on W_mu
EDGE: bpI:p0:restricted#restrictedHamiltonian | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-deriv@L61-L61 | the Hamiltonian differentiated
EDGE: bpI:p0:primaries#primary1 | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-deriv@L61-L61 | a_1(mu)
EDGE: bpI:p0:primaries#primary2 | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-deriv@L61-L61 | a_2(mu)
EDGE: bpI:p0:restricted#restrictedVectorField | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-deriv@L67-L67 | the display of V_mu in Definition restricted
EDGE: bpI:p7:sec-ham#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-deriv@L61-L67 | r_j and W_mu are fixed in the section data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row names or confirms this step
NOTE: -

NODE: stepI:p7:he-sol
KIND: step
TITLE: Solution predicates
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-sol@L69-L69
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-sol@L69-L69
CONTRACT_ID: stepI:p7:he-sol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: mu in R; J subset R; z:R->R^2 x R^2; W_mu and the restricted Hamiltonian/field are the section data of L48-49
SOURCE_QUANTIFIERS: For every mu in R, J subset R and z:R->R^2 x R^2; equivalence at every t in J
SOURCE_CONCLUSION: the clauses of RSol_mu are z(t) in W_mu and z'(t) = V_mu(z(t)) = X_H(z(t)); the reduction to IsSolIn is the cited N result
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:primaries#CollisionFree, bpI:p0:restricted#IsRestrictedSolutionOn, bpI:p0:restricted#restrictedVectorField, stepI:p7:he-deriv, bpN:p3:newton-reduction, bpI:p7:sec-ham#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:primaries#CollisionFree | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-sol@L69-L69 | first clause of RSol_mu is collision-freeness
EDGE: bpI:p0:restricted#IsRestrictedSolutionOn | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-sol@L69-L69 | RSol_mu
EDGE: bpI:p0:restricted#restrictedVectorField | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-sol@L69-L69 | V_mu
EDGE: stepI:p7:he-deriv | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-sol@L69-L69 | V_mu = X_H
EDGE: bpN:p3:newton-reduction | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-sol@L69-L69 | reduction to IsSolIn
EDGE: bpI:p7:sec-ham#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-sol@L69-L69 | r_j and W_mu are fixed in the section data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row names or confirms this step
NOTE: -

NODE: bpI:p7:kepler-eq
KIND: proposition
TITLE: Kepler's equation, analytic solution
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L91-L114
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L115-L135
CONTRACT_ID: bpI:p7:kepler-eq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < e_1 < 1; e_2 = (1+e_1)/2, vartheta_* = (1+e_2)/2, y_0 = arcosh(vartheta_*/e_2), delta_K = (1/2)(1-vartheta_*) y_0, delta_E = min{e_2-e_1, (1-vartheta_*) y_0/(2 cosh y_0)}; P(e_1) = {(ell,e) in C^2 : |Im ell| < delta_K, dist(e, [-e_1,e_1]) < delta_E}
SOURCE_QUANTIFIERS: e_1 in (0,1), then the constants e_2, vartheta_*, y_0, delta_K, delta_E, then (ell, e) in P(e_1)
SOURCE_CONCLUSION: P is open, contains {(ell,e) real : |e| <= e_1}, |e| < e_1 + delta_E <= e_2, |Im e| < delta_E; there is a unique holomorphic u : P -> C with |Im u| <= y_0 and u - e sin u = ell; (a) |sin u|,|cos u| <= cosh y_0 = vartheta_*/e_2, |e cos u| <= vartheta_* < 1, |1 - e cos u| >= 1 - vartheta_*; (b) d_ell u = 1/(1 - e cos u), d_e u = sin u/(1 - e cos u), u(ell,0) = ell, u(ell+2pi,e) = u(ell,e) + 2pi, sin u, cos u, (1-e cos u)^-1 holomorphic and 2pi-periodic in ell; (c) u real at real points, exactly one real solution u_R(ell,e) for real ell and e in (-1,1), u_R real-analytic on R x (-1,1), u_R(.,e) an increasing diffeomorphism of R with u_R(0,e) = 0, u_R(2pi,e) = 2pi, u = u_R on real points of every P(e_1)
CONSTANT_SCOPE: e_2, vartheta_*, y_0, delta_K, delta_E depend only on e_1
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:ke-const, stepI:p7:ke-trig, stepI:p7:ke-contr, stepI:p7:ke-hol, stepI:p7:ke-a, stepI:p7:ke-b, stepI:p7:ke-c
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:ke-const | blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L116-L116 | proof step Constants
EDGE: stepI:p7:ke-trig | blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L119-L119 | proof step Trigonometric bounds
EDGE: stepI:p7:ke-contr | blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L121-L121 | proof step Contraction
EDGE: stepI:p7:ke-hol | blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L125-L125 | proof step Holomorphy
EDGE: stepI:p7:ke-a | blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L129-L129 | proof of (a)
EDGE: stepI:p7:ke-b | blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L131-L131 | proof of (b)
EDGE: stepI:p7:ke-c | blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L133-L133 | proof of (c)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerEq_tube, keplerTube_real_points, eccAnomC_periodic, eccAnomC_zero_ecc, hasDerivAt_eccAnomC_ell, hasDerivAt_eccAnomC_ecc, isOpen_keplerTube (KAM/Kepler/KeplerTube.lean); eccAnom_eq, analyticOnNhd_eccAnom, strictMono_eccAnom (KAM/Kepler/Equation.lean)
LEAN_NOTE: audit KEP-4 PASS WITH NOTES (complex tube) + KEP-2 PASS (real part c); full real slice by KEP-4 N1 composition
NOTE: Part 7 L113 sourcegap: Chi05 gives no domain; the blueprint supplies the full argument in this node and its steps

NODE: stepI:p7:ke-const
KIND: step
TITLE: Constants
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-const@L116-L117
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-const@L116-L117
CONTRACT_ID: stepI:p7:ke-const
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < e_1 < 1 and the constants of Proposition kepler-eq
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: 0 < e_1 < e_2 < vartheta_* < 1, vartheta_*/e_2 > 1, y_0 > 0, e_2 cosh y_0 = vartheta_*, e_2 sinh y_0 <= vartheta_* y_0, delta_K + e_2 sinh y_0 + delta_E cosh y_0 <= y_0; for (ell,e) in P: |e| < e_2, |Re e| < e_2, |Im e| < delta_E
CONSTANT_SCOPE: constants depend only on e_1
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerConstants_pos, tube_bounds (KAM/Kepler/KeplerTube.lean)
LEAN_NOTE: audit KEP-4 PASS WITH NOTES; scalar constants/tube helpers (KAM.Kepler.Tube.*); parent keplerEq_tube covers
NOTE: -

NODE: stepI:p7:ke-trig
KIND: step
TITLE: Trigonometric bounds
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-trig@L119-L119
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-trig@L119-L119
CONTRACT_ID: stepI:p7:ke-trig
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u = x + iy in C; e in C
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: |sin u|^2 = sin^2 x + sinh^2 y, |cos u|^2 = cos^2 x + sinh^2 y, both <= cosh^2 y; |Re sin u| <= cosh y, |Im sin u| <= sinh|y|; |Im(e sin u)| <= |Re e| sinh|y| + |Im e| cosh y
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: norm_sin_le, abs_re_sin_le, abs_im_sin_le (KAM/Kepler/EquationComplex.lean)
LEAN_NOTE: audit KEP-3 PASS WITH NOTES; named I ke-trig (namespace KAM.Kepler.EqC)
NOTE: -

NODE: stepI:p7:ke-contr
KIND: step
TITLE: A contraction
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-contr@L121-L123
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-contr@L121-L123
CONTRACT_ID: stepI:p7:ke-contr
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: steps ke-const, ke-trig; S = {u : |Im u| <= y_0} closed convex complete; (ell,e) in P; Phi_{ell,e}(u) = ell + e sin u
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: Phi_{ell,e}(S) subset S and Phi is a vartheta_*-contraction of S; hence a unique fixed point u(ell,e) in S, i.e. a unique solution of Kepler's equation in S
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:ke-const, stepI:p7:ke-trig, K:bp:p1:ext-mvt, K:bp:p1:ext-banach
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:ke-const | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-contr@L122-L122 | delta_K + e_2 sinh y_0 + delta_E cosh y_0 <= y_0 and the bounds on e
EDGE: stepI:p7:ke-trig | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-contr@L122-L122 | bounds of Im(e sin u) and ¦cos u¦
EDGE: K:bp:p1:ext-mvt | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-contr@L123-L123 | mean value inequality on the convex S
EDGE: K:bp:p1:ext-banach | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-contr@L123-L123 | Banach fixed point theorem
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: existsUnique_keplerOp (KAM/Kepler/EquationComplex.lean); keplerData_tube (KAM/Kepler/KeplerTube.lean)
LEAN_NOTE: audit KEP-3/KEP-4 PASS WITH NOTES; named I ke-contr; instantiated on tube (Tube.keplerData_tube)
NOTE: -

NODE: stepI:p7:ke-hol
KIND: step
TITLE: Holomorphy
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-hol@L125-L127
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-hol@L125-L127
CONTRACT_ID: stepI:p7:ke-hol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: steps ke-const, ke-contr, ke-trig; u_0 = ell, u_{m+1} = Phi_{ell,e}(u_m)
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: each u_m is holomorphic on P with values in S; |u_m - u| <= vartheta_*^{m+1}/(1 - vartheta_*) uniformly on P; hence u is holomorphic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:ke-contr, stepI:p7:ke-const, stepI:p7:ke-trig, bpI:p7:x-hol, bpI:p7:x-weier
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:ke-contr | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-hol@L125-L125 | S is Phi-invariant and Phi is a contraction with fixed point u
EDGE: stepI:p7:ke-const | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-hol@L126-L126 | delta_K < y_0, e_2 cosh y_0 = vartheta_*
EDGE: stepI:p7:ke-trig | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-hol@L126-L126 | ¦sin ell¦ <= cosh y_0 for ¦Im ell¦ < y_0
EDGE: bpI:p7:x-hol | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-hol@L125-L125 | u_m holomorphic as compositions
EDGE: bpI:p7:x-weier | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-hol@L127-L127 | uniform limit of holomorphic functions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerSol_analyticOnNhd (KAM/Kepler/EquationComplex.lean); eccAnomC_analyticOnNhd (KAM/Kepler/KeplerTube.lean)
LEAN_NOTE: audit KEP-3/KEP-4 PASS WITH NOTES; named I ke-hol (analytic IFT route instead of uniform limit)
NOTE: -

NODE: stepI:p7:ke-a
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-a@L129-L129
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-a@L129-L129
CONTRACT_ID: stepI:p7:ke-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u in S; steps ke-trig, ke-const
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: |sin u|,|cos u| <= cosh y_0 = vartheta_*/e_2, |e cos u| <= vartheta_* < 1, |1 - e cos u| >= 1 - vartheta_* on P
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:ke-contr, stepI:p7:ke-trig, stepI:p7:ke-const
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:ke-contr | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-a@L129-L129 | u in S
EDGE: stepI:p7:ke-trig | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-a@L129-L129 | trigonometric bounds
EDGE: stepI:p7:ke-const | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-a@L129-L129 | e_2 cosh y_0 = vartheta_*
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerEq_tube, tube_bounds (KAM/Kepler/KeplerTube.lean)
LEAN_NOTE: audit KEP-4 PASS WITH NOTES; keplerEq_tube gives all four analytic bounds
NOTE: -

NODE: stepI:p7:ke-b
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-b@L131-L131
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-b@L131-L131
CONTRACT_ID: stepI:p7:ke-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: part (a); u holomorphic with u - e sin u = ell
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: (1 - e cos u) d_ell u = 1, (1 - e cos u) d_e u = sin u, hence the formulas; u(ell,0) = ell; u(ell + 2pi, e) = u(ell,e) + 2pi by uniqueness in S; sin u, cos u, (1-e cos u)^-1 holomorphic and 2pi-periodic in ell
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:ke-hol, stepI:p7:ke-a, stepI:p7:ke-contr
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:ke-hol | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-b@L131-L131 | u holomorphic, so the identity can be differentiated
EDGE: stepI:p7:ke-a | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-b@L131-L131 | 1 - e cos u != 0 to divide
EDGE: stepI:p7:ke-contr | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-b@L131-L131 | uniqueness of the solution in S
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerSol_fderiv, keplerSol_shift (KAM/Kepler/EquationComplex.lean); hasDerivAt_eccAnomC_ell, hasDerivAt_eccAnomC_ecc, eccAnomC_periodic, eccAnomC_zero_ecc (KAM/Kepler/KeplerTube.lean)
LEAN_NOTE: audit KEP-3/KEP-4 PASS WITH NOTES; named I ke-b
NOTE: -

NODE: stepI:p7:ke-c
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-c@L133-L134
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-c@L133-L134
CONTRACT_ID: stepI:p7:ke-c
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: For the real-line assertion ell in R and e in (-1,1); for comparison with the complex branch 0<e_1<1 and (ell,e) a real point of P(e_1), with constants defined in L94-100
SOURCE_QUANTIFIERS: For every ell in R and e in (-1,1) there exists exactly one real u_R(ell,e); for each e choose e_1 with |e|<e_1<1 to compare the analytic branch; assertions on u_R hold on R x (-1,1)
SOURCE_CONCLUSION: phi(u) = ell + e sin u is a |e|-contraction of R with a unique real fixed point u_R(ell,e); u = u_R at real points of P; u_R real-analytic on R x (-1,1), d_ell u_R > 0, u_R(.,e) an increasing diffeomorphism of R, u_R(0,e) = 0, u_R(2pi,e) = 2pi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:ke-contr, stepI:p7:ke-hol, K:bp:p1:holomorphic-analytic, stepI:p7:ke-b, K:bp:p1:ext-banach, K:bp:p1:ext-mvt
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:ke-contr | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-c@L133-L133 | uniqueness in S gives u = u_R at real points of P
EDGE: stepI:p7:ke-hol | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-c@L134-L134 | u_R is the restriction of a holomorphic function
EDGE: K:bp:p1:holomorphic-analytic | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-c@L134-L134 | holomorphic implies real-analytic
EDGE: stepI:p7:ke-b | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-c@L134-L134 | d_ell u_R = 1/(1 - e cos u_R)
EDGE: K:bp:p1:ext-banach | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-c@L133-L133 | the complete nonempty real line carries the contraction with constant abs(e) < 1
EDGE: K:bp:p1:ext-mvt | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-c@L133-L133 | abs(e cos u) <= abs(e) bounds the derivative on the convex real line
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: keplerSol_real (KAM/Kepler/EquationComplex.lean); keplerTube_real_points (KAM/Kepler/KeplerTube.lean); eccAnom_eq, strictMono_eccAnom, analyticOnNhd_eccAnom (KAM/Kepler/Equation.lean)
LEAN_NOTE: audit KEP-3/KEP-4/KEP-2 PASS (WITH NOTES); named I ke-c; real slice KEP-4 N1
NOTE: -

NODE: bpI:p7:elements
KIND: definition
TITLE: Kepler region and elements
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:elements@L144-L156
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:elements
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (definition; typing data (q,p) in R^2 x R^2, q != 0)
SOURCE_QUANTIFIERS: (q,p)
SOURCE_CONCLUSION: defines E(q,p) = (1/2)|p|_2^2 - 1/|q|_2, the open region C = {q != 0, E < 0, Gamma > 0, Gamma^2 < -1/(2E)} and on C the elements L = 1/sqrt(-2E), G = Gamma, a = L^2, e = sqrt(1 + 2E Gamma^2), with L > G > 0, e in (0,1), E = -1/(2a), Gamma^2 = a(1 - e^2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: kE, keplerRegion, elemL, elemA, elemEcc, isOpen_keplerRegion (KAM/Kepler/Energy.lean); eccOf_mem_Ioo, delaunay_elements (KAM/Kepler/Orbit.lean)
LEAN_NOTE: audit KEP-1 (addendum PASS) + KEP-5 (addendum PASS)
NOTE: notation of Part 7 L20-27 (Gamma, E, C_0, e(L,G)) is used here

NODE: bpI:p7:orbit-maps
KIND: definition
TITLE: Orbit maps
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-maps@L158-L168
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:orbit-maps
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: ell, g, L, e, k; u = u(ell,e) of Proposition kepler-eq
SOURCE_QUANTIFIERS: (ell, g, L, e, k), then (ell, g, L, G) in D_R
SOURCE_CONCLUSION: defines Q_el(ell,g,L,e,k) (X = L^2(c-e), Y = L^2 k s, P_X = -s/(L D), P_Y = k c/(L D), q = R(g)(X,Y), p = R(g)(P_X,P_Y), D = 1 - e c) and the Delaunay orbit map Q(ell,g,L,G) = Q_el(ell,g,L,e(L,G),G/L) with e(L,G) = sqrt(1 - G^2/L^2); on D_R = R^2 x C_0 all quantities are real and D >= 1 - e > 0 (u = u_R)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:kepler-eq
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-maps@L159-L159 | u = u(ell,e), and u = u_R on the real domain
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: eccOf, deDom (KAM/Kepler/Energy.lean); orbitFrame, orbitMapR, delaunay, orbitMapR_radius_bounds (KAM/Kepler/Orbit.lean)
LEAN_NOTE: audit KEP-1 (addendum PASS) + KEP-5 (addendum PASS); real definitions; holomorphic extension is bpI:p7:orbit-maps-e
NOTE: -

NODE: bpI:p7:orbit-maps-e
KIND: proposition
TITLE: Orbit maps near $e=0$
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-maps-e@L170-L174
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-maps-e@L175-L179
CONTRACT_ID: bpI:p7:orbit-maps-e
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < e_1 < 1; P = P(e_1) as in Proposition kepler-eq
SOURCE_QUANTIFIERS: e_1, then (ell,g,L,e,k)
SOURCE_CONCLUSION: Q_el is holomorphic on {(ell,g,L,e,k) : (ell,e) in P, g in C, L in C minus {0}, k in C}, 2pi-periodic in ell and g, real on real points with |e| <= e_1; holomorphic on a neighbourhood of e = 0 (P contains the disc |e| < delta_E), e.g. with k = sqrt(1 - e^2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:kepler-eq, bpI:p7:orbit-maps, stepI:p7:om-hol, stepI:p7:om-per
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-maps-e@L171-L171 | P(e_1) and the solution u
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-maps-e@L171-L171 | the map Q_el
EDGE: stepI:p7:om-hol | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-maps-e@L176-L176 | proof step Holomorphy
EDGE: stepI:p7:om-per | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-maps-e@L178-L178 | proof step Periodicity, reality
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: orbitMapC_differentiableOn, orbitMapC_periodic, orbitMapC_real, orbitMapC_ofReal, orbitDomC_mem_ofReal (KAM/Kepler/OrbitComplex.lean)
LEAN_NOTE: audit KEP-9 PASS WITH NOTES; steps om-hol/om-per not named, left
NOTE: -

NODE: stepI:p7:om-hol
KIND: step
TITLE: Holomorphy
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-hol@L176-L176
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-hol@L176-L176
CONTRACT_ID: stepI:p7:om-hol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Proposition kepler-eq (a); (ell,e) in P
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: u, c, s holomorphic, |D| >= 1 - vartheta_* > 0; Q_el holomorphic as polynomial in (c,s,e,k,L,1/L,1/D) and entire R(g); k = sqrt(1 - e^2) holomorphic since |e| < e_2 < 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:kepler-eq, bpI:p7:orbit-maps, bpI:p7:x-hol
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-hol@L176-L176 | holomorphy of u and the bound ¦1 - e cos u¦ >= 1 - vartheta_*
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-hol@L176-L176 | formulas for X, Y, P_X, P_Y
EDGE: bpI:p7:x-hol | blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-hol@L176-L176 | holomorphy of compositions, R(g) entire, principal square root
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row names or confirms this step
NOTE: -

NODE: stepI:p7:om-per
KIND: step
TITLE: Periodicity, reality
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-per@L178-L178
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-per@L178-L178
CONTRACT_ID: stepI:p7:om-per
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Proposition kepler-eq (b),(c)
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: Q_el is 2pi-periodic in ell and g and real at real points with |e| <= e_1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:kepler-eq, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-per@L178-L178 | (b) periodicity of u, (c) reality of u
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-per@L178-L178 | R is 2pi-periodic and the formulas are real at real arguments
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row names or confirms this step
NOTE: -

NODE: bpI:p7:orbit-identities
KIND: proposition
TITLE: Identities for the orbit maps
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-identities@L181-L190
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-identities@L191-L203
CONTRACT_ID: bpI:p7:orbit-identities
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (ell,g,L,G) in D_R, e = e(L,G), (q,p) = Q(ell,g,L,G), r = |q|_2, u, c, s, D as in Definition orbit-maps
SOURCE_QUANTIFIERS: (ell,g,L,G) in D_R
SOURCE_CONCLUSION: (a) r = L^2 D = L^2(1 - e cos u), L^2(1-e) <= r <= L^2(1+e), |p|_2^2 = (1 + e cos u)/(L^2 D); (b) Gamma(q,p) = G, q.p = L e sin u; (c) E(q,p) = -1/(2L^2), Q(D_R) subset C, elements of Q(ell,g,L,G) are L, G, a = L^2, e; (d) (L e sin u)^2 = -G^2 + 2r - r^2/L^2, L^2 e cos u = L^2 - r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-maps, bpI:p7:elements, stepI:p7:oi-r, stepI:p7:oi-gam, stepI:p7:oi-en, stepI:p7:oi-d
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-identities@L182-L182 | Q and u, c, s, D
EDGE: bpI:p7:elements | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-identities@L186-L186 | elements of Definition elements and the region C
EDGE: stepI:p7:oi-r | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-identities@L194-L194 | proof of (a)
EDGE: stepI:p7:oi-gam | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-identities@L197-L197 | proof of (b)
EDGE: stepI:p7:oi-en | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-identities@L200-L200 | proof of (c)
EDGE: stepI:p7:oi-d | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-identities@L202-L202 | proof of (d)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: orbitMapR_radius, orbitMapR_radius_bounds, orbitMapR_speed_sq, orbitMapR_cross, orbitMapR_dot, orbitMapR_energy, orbitMapR_radial, delaunay_mem_region, delaunay_elements (KAM/Kepler/Orbit.lean)
LEAN_NOTE: audit KEP-5 PASS (addendum closes H01); rows (a)-(d)
NOTE: -

NODE: stepI:p7:oi-r
KIND: step
TITLE: Radius
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-r@L194-L195
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-r@L194-L195
CONTRACT_ID: stepI:p7:oi-r
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G = L k, k^2 = 1 - e^2, c^2 + s^2 = 1 (real case); R(g) orthogonal
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: r^2 = L^4 D^2, r = L^2 D > 0, |p|_2^2 = (1 + e c)/(L^2 D)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-r@L194-L194 | X, Y, P_X, P_Y, D >= 1 - e > 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: orbitMapR_radius, orbitMapR_radius_bounds, orbitMapR_speed_sq (KAM/Kepler/Orbit.lean)
LEAN_NOTE: audit KEP-5 PASS; row (a)
NOTE: -

NODE: stepI:p7:oi-gam
KIND: step
TITLE: Angular momentum, radial momentum
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-gam@L197-L198
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-gam@L197-L198
CONTRACT_ID: stepI:p7:oi-gam
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (ell,g,L,G) in D_R=R^2 x C_0 with 0<G<L; e=e(L,G), k=G/L, (q,p)=Q(ell,g,L,G), u,c,s,D as in the orbit-map definitions
SOURCE_QUANTIFIERS: For every (ell,g,L,G) in D_R, with the orbit quantities fixed as in the enclosing proposition
SOURCE_CONCLUSION: Gamma = X P_Y - Y P_X = L k = G and q.p = X P_X + Y P_Y = L e s
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-gam@L197-L197 | X, Y, P_X, P_Y
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: orbitMapR_cross, orbitMapR_dot (KAM/Kepler/Orbit.lean)
LEAN_NOTE: audit KEP-5 PASS; row (b)
NOTE: -

NODE: stepI:p7:oi-en
KIND: step
TITLE: Energy
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-en@L200-L200
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-en@L200-L200
CONTRACT_ID: stepI:p7:oi-en
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (ell,g,L,G) in D_R=R^2 x C_0 with 0<G<L; e=e(L,G), k=G/L, (q,p)=Q(ell,g,L,G), u,c,s,D as in the orbit-map definitions
SOURCE_QUANTIFIERS: For every (ell,g,L,G) in D_R, with the orbit quantities fixed as in the enclosing proposition
SOURCE_CONCLUSION: E = (1/2)|p|^2 - 1/r = -1/(2L^2); Q(ell,g,L,G) lies in C with elements L, G, L^2, e
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:oi-r, bpI:p7:elements, bpI:p7:orbit-maps, stepI:p7:oi-gam
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:oi-r | blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-en@L200-L200 | r and ¦p¦^2
EDGE: bpI:p7:elements | blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-en@L200-L200 | membership in C (G > 0, G^2 < L^2 = -1/(2E)) and the elements
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-en@L200-L200 | p and q of the orbit map
EDGE: stepI:p7:oi-gam | blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-en@L200-L200 | Gamma(q,p) = G is needed for the strict angular-momentum inequality and recovery of the elements
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: orbitMapR_energy, delaunay_mem_region, delaunay_elements (KAM/Kepler/Orbit.lean)
LEAN_NOTE: audit KEP-5 PASS; row (c)
NOTE: -

NODE: stepI:p7:oi-d
KIND: step
TITLE: (d)
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-d@L202-L202
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-d@L202-L202
CONTRACT_ID: stepI:p7:oi-d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (ell,g,L,G) in D_R=R^2 x C_0 with 0<G<L; e=e(L,G), k=G/L, (q,p)=Q(ell,g,L,G), u,c,s,D as in the orbit-map definitions
SOURCE_QUANTIFIERS: For every (ell,g,L,G) in D_R, with the orbit quantities fixed as in the enclosing proposition
SOURCE_CONCLUSION: L^2 e c = L^2 - r and (L e s)^2 = -G^2 + 2r - r^2/L^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:oi-r, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:oi-r | blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-d@L202-L202 | r = L^2 (1 - e c)
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-d@L202-L202 | the calculation uses the Delaunay orbit map or its element formulas
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: orbitMapR_radial (KAM/Kepler/Orbit.lean)
LEAN_NOTE: audit KEP-5 PASS; row (d)
NOTE: -

NODE: bpI:p7:symplectic
KIND: proposition
TITLE: The Delaunay map is symplectic
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:symplectic@L205-L217
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:symplectic@L218-L240
CONTRACT_ID: bpI:p7:symplectic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (ell,g,L,G) in D_R (open in R^4); F = 2 L e sin u; for the consequence, U subset R^4 open (target, coordinates (q,p)), H: U -> R of class C^1, W := {w in D_R : Q(w) in U} (open in R^4 since Q is continuous on the open set D_R)
SOURCE_QUANTIFIERS: w in D_R; U open; H: U -> R, C^1; then w in W
SOURCE_CONCLUSION: Q^*(sum p_i dq_i) = L dell + G dg + dF; D Q^T J D Q = J = D Q J D Q^T; Q^*(sum dq_i wedge dp_i) = dell wedge dL + dg wedge dG; D Q(w) invertible; on W: D Q X_{H o Q} = X_H o Q, i.e. w' = X_{H o Q}(w) iff d/dt Q(w) = X_H(Q(w)) for C^1 curves w in W
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-maps, stepI:p7:sy-g, stepI:p7:sy-coord, stepI:p7:sy-compare, stepI:p7:sy-ext, stepI:p7:sy-field
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#bpI:p7:symplectic@L206-L206 | the map Q on D_R
EDGE: stepI:p7:sy-g | blueprint-I/parts/p7-delaunay.tex#bpI:p7:symplectic@L219-L219 | proof step
EDGE: stepI:p7:sy-coord | blueprint-I/parts/p7-delaunay.tex#bpI:p7:symplectic@L222-L222 | proof step
EDGE: stepI:p7:sy-compare | blueprint-I/parts/p7-delaunay.tex#bpI:p7:symplectic@L234-L234 | proof step
EDGE: stepI:p7:sy-ext | blueprint-I/parts/p7-delaunay.tex#bpI:p7:symplectic@L236-L236 | proof step
EDGE: stepI:p7:sy-field | blueprint-I/parts/p7-delaunay.tex#bpI:p7:symplectic@L239-L239 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sonnet-amend-I-p1
REVIEWER: sol-delta2-I-amend
LEAN_STATUS: PROVED
LEAN_REF: delaunay_symplectic, delaunay_liouville, delaunay_hasFDerivAt, delaunay_fderiv_equiv, delaunay_hamiltonianVectorField (KAM/Kepler/DelaunaySymplectic.lean)
LEAN_NOTE: audit KEP-6 PASS WITH NOTES; curve iff of Hamiltonian transport not a separate decl (follows from invertibility); steps sy-* left
NOTE: -

NODE: stepI:p7:sy-g
KIND: step
TITLE: Reduction of the angle $g$
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-g@L219-L220
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-g@L219-L220
CONTRACT_ID: stepI:p7:sy-g
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q = R(g) xi, xi = (X,Y), pi = (P_X,P_Y), p = R(g) pi
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: p.dq = pi.dxi + G dg
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-maps, bpI:p7:orbit-identities
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-g@L219-L219 | xi, pi and the rotation form of q, p
EDGE: bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-g@L220-L220 | (b): Gamma = X P_Y - Y P_X = G
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row names or confirms this step
NOTE: -

NODE: stepI:p7:sy-coord
KIND: step
TITLE: Coordinates $(u,L,e)$
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-coord@L222-L232
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-coord@L222-L232
CONTRACT_ID: stepI:p7:sy-coord
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: on D_R use (u, L, e) in place of (ell, L, G); X = L^2(c-e), Y = L^2 k s
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: pi.dxi = L(1 + e c) du + 2 e s dL + L s de
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-maps, bpI:p7:kepler-eq
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-coord@L222-L222 | X, Y, P_X, P_Y
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-coord@L222-L222 | d_ell u > 0 and u = u_R: (ell,L,G) -> (u,L,e) is a diffeomorphism
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row names or confirms this step
NOTE: -

NODE: stepI:p7:sy-compare
KIND: step
TITLE: Comparison with $L\,d\ell$
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-compare@L234-L234
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-compare@L234-L234
CONTRACT_ID: stepI:p7:sy-compare
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (ell,g,L,G) in D_R=R^2 x C_0 with 0<G<L; e=e(L,G), k=G/L, (q,p)=Q(ell,g,L,G), u,c,s,D as in the orbit-map definitions; the one-form calculation is on D_R, F=2Le sin u
SOURCE_QUANTIFIERS: For every (ell,g,L,G) in D_R, with the orbit quantities fixed as in the enclosing proposition
SOURCE_CONCLUSION: pi.dxi - L dell = dF with F = 2 L e s; Q^*(sum p_i dq_i) = L dell + G dg + dF
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:sy-g, stepI:p7:sy-coord, bpI:p7:kepler-eq, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:sy-g | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-compare@L234-L234 | p.dq = pi.dxi + G dg
EDGE: stepI:p7:sy-coord | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-compare@L234-L234 | pi.dxi
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-compare@L234-L234 | ell = u - e sin u relates dell to du, de
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-compare@L234-L234 | the calculation uses the Delaunay orbit map or its element formulas
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row names or confirms this step
NOTE: -

NODE: stepI:p7:sy-ext
KIND: step
TITLE: Exterior derivative
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-ext@L236-L237
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-ext@L236-L237
CONTRACT_ID: stepI:p7:sy-ext
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Q is the Delaunay map on D_R as fixed in the symplectic proposition; F=2Le sin u; no one-form identity or invertibility is assumed as a source premise
SOURCE_QUANTIFIERS: For every (ell,g,L,G) in D_R, with the orbit quantities fixed as in the enclosing proposition
SOURCE_CONCLUSION: Q^*(sum dp_i wedge dq_i) = dL wedge dell + dG wedge dg, i.e. D Q^T J D Q = J, det D Q != 0, D Q J D Q^T = J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:sy-compare, bpI:p7:x-forms, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:sy-compare | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-ext@L236-L236 | Q^*(sum p_i dq_i) = L dell + G dg + dF
EDGE: bpI:p7:x-forms | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-ext@L236-L236 | d^2 = 0, pull-back commutes with d, form determined by values on vectors
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-ext@L236-L237 | the calculation uses the Delaunay orbit map or its element formulas
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row names or confirms this step
NOTE: -

NODE: stepI:p7:sy-field
KIND: step
TITLE: Hamiltonian fields
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-field@L239-L239
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-field@L239-L239
CONTRACT_ID: stepI:p7:sy-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Q is the Delaunay map on D_R; U subset R^4 open, H: U -> R of class C^1; W = {w in D_R : Q(w) in U} open; Q(w) lies in the open domain U of H for every w in W, so the chain rule applies at every point of W
SOURCE_QUANTIFIERS: for every open U and C^1 H: U -> R, every w in W; then for every C^1 curve w in W
SOURCE_CONCLUSION: on W: D Q X_{H o Q} = X_H o Q; for C^1 curves w in W: w' = X_{H o Q}(w) iff d/dt Q(w) = X_H(Q(w))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:sy-ext, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:sy-ext | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-field@L239-L239 | D Q J D Q^T = J
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-field@L239-L239 | the calculation uses the Delaunay orbit map or its element formulas
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-amend
REVIEWER: sol-delta2-I-amend
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row names or confirms this step
NOTE: -

NODE: bpI:p7:chart
KIND: theorem
TITLE: Delaunay chart
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L242-L246
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L247-L261
CONTRACT_ID: bpI:p7:chart
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none beyond the definitions of Q, C_0, C, D_R
SOURCE_QUANTIFIERS: Q on D_R
SOURCE_CONCLUSION: Q is 2pi-periodic in ell and g and induces a bijection (R/2piZ)^2 x C_0 -> C; Q : D_R -> C is a surjective real-analytic local diffeomorphism; the induced map on the quotient is a real-analytic diffeomorphism onto the open set C, symplectic by Proposition symplectic; E o Q = -1/(2L^2), Gamma o Q = G; the loci e = 0 and e = 1 are excluded from C_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-maps, bpI:p7:elements, bpI:p7:symplectic, bpI:p7:orbit-identities, stepI:p7:ch-reg, stepI:p7:ch-inj, stepI:p7:ch-surj1, stepI:p7:ch-surj2, stepI:p7:ch-surj3, stepI:p7:ch-diffeo
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L243-L243 | the map Q and D_R
EDGE: bpI:p7:elements | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L243-L243 | the region C and the elements
EDGE: bpI:p7:symplectic | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L243-L243 | symplectic quotient map
EDGE: bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L244-L244 | E o Q and Gamma o Q
EDGE: stepI:p7:ch-reg | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L248-L248 | proof step
EDGE: stepI:p7:ch-inj | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L250-L250 | proof step
EDGE: stepI:p7:ch-surj1 | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L252-L252 | proof step
EDGE: stepI:p7:ch-surj2 | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L256-L256 | proof step
EDGE: stepI:p7:ch-surj3 | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L258-L258 | proof step
EDGE: stepI:p7:ch-diffeo | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L260-L260 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: orbitMapR_periodic, delaunay_mem_region, delaunay_elements (KAM/Kepler/Orbit.lean); delaunay_periodic, delaunay_eq_iff, keplerRegion_subset_image, delaunay_localDiffeo (KAM/Kepler/DelaunayChart.lean); delaunay_symplectic (KAM/Kepler/DelaunaySymplectic.lean)
LEAN_NOTE: audit KEP-5 PASS + KEP-7 PASS WITH NOTES + KEP-6 PASS WITH NOTES; periodic, bijection, surjective local diffeo, symplectic, E and Gamma along Q
NOTE: -

NODE: stepI:p7:ch-reg
KIND: step
TITLE: Regularity
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-reg@L248-L248
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-reg@L248-L248
CONTRACT_ID: stepI:p7:ch-reg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (ell,g,L,G) in D_R, so 0 < G < L and 1-G^2/L^2 > 0; e(L,G) = sqrt(1-G^2/L^2)
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: Q is real-analytic on D_R; D Q invertible; Q(D_R) subset C
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:kepler-eq, bpI:p7:orbit-maps, bpI:p7:symplectic, bpI:p7:orbit-identities, bpI:p7:x-hol, K:bp:p1:holomorphic-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-reg@L248-L248 | (c): u_R real-analytic
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-reg@L248-L248 | Q built from u_R, e(L,G), R(g)
EDGE: bpI:p7:symplectic | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-reg@L248-L248 | invertibility of D Q
EDGE: bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-reg@L248-L248 | (c): Q(D_R) subset C
EDGE: bpI:p7:x-hol | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-reg@L248-L248 | the positive square-root formula for e extends holomorphically locally on C_0
EDGE: K:bp:p1:holomorphic-analytic | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-reg@L248-L248 | restrict the local holomorphic square-root formula to real actions to justify real analyticity of e
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: delaunay_localDiffeo (KAM/Kepler/DelaunayChart.lean)
LEAN_NOTE: audit KEP-7 PASS WITH NOTES; named step (ch-reg)
NOTE: -

NODE: stepI:p7:ch-inj
KIND: step
TITLE: Injectivity modulo $2\pi$
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-inj@L250-L250
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-inj@L250-L250
CONTRACT_ID: stepI:p7:ch-inj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Q(ell,g,L,G) = (q,p)
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: L, G, e, r are determined by (q,p); cos u and sin u are determined, so u and ell modulo 2pi; (X,Y) is determined and nonzero so g modulo 2pi: injectivity modulo 2pi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-identities, bpI:p7:elements, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-inj@L250-L250 | L = 1/sqrt(-2E), G = Gamma, cos u = (1 - r/L^2)/e, sin u = q.p/(L e)
EDGE: bpI:p7:elements | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-inj@L250-L250 | elements of (q,p)
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-inj@L250-L250 | X, Y and q = R(g)(X,Y)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: delaunay_eq_iff (KAM/Kepler/DelaunayChart.lean)
LEAN_NOTE: audit KEP-7 PASS WITH NOTES; named step (ch-inj)
NOTE: -

NODE: stepI:p7:ch-surj1
KIND: step
TITLE: Surjectivity: the elements
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj1@L252-L255
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj1@L252-L255
CONTRACT_ID: stepI:p7:ch-surj1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (q,p) in C
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: elements L, G, e with (L,G) in C_0, e = e(L,G); (q.p)^2 = 2r - r^2/L^2 - G^2 (*)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:elements
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:elements | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj1@L252-L252 | definition of L, G, e on C
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerRegion_subset_image (KAM/Kepler/DelaunayChart.lean)
LEAN_NOTE: audit KEP-7 PASS WITH NOTES; named step (ch-surj1..3)
NOTE: -

NODE: stepI:p7:ch-surj2
KIND: step
TITLE: Surjectivity: the anomaly
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj2@L256-L256
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj2@L256-L256
CONTRACT_ID: stepI:p7:ch-surj2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: step ch-surj1
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: c = (1 - r/L^2)/e, s = q.p/(L e) satisfy c^2 + s^2 = 1; there are u, ell = u - e sin u, g with Q-coordinates (X,Y) and R(g)(X,Y) = q
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:ch-surj1, bpI:p7:kepler-eq, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:ch-surj1 | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj2@L256-L256 | relation (*)
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj2@L256-L256 | (c): u = u_R(ell,e) by uniqueness
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj2@L256-L256 | X, Y, D
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerRegion_subset_image (KAM/Kepler/DelaunayChart.lean)
LEAN_NOTE: audit KEP-7 PASS WITH NOTES; named step (ch-surj1..3)
NOTE: -

NODE: stepI:p7:ch-surj3
KIND: step
TITLE: Surjectivity: the momentum
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj3@L258-L258
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj3@L258-L258
CONTRACT_ID: stepI:p7:ch-surj3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: steps ch-surj2; (q,p') = Q(ell,g,L,G)
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: p' = p, so Q(ell,g,L,G) = (q,p): surjectivity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-identities, stepI:p7:ch-surj2, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj3@L258-L258 | (b),(c): E, Gamma and q.p of Q
EDGE: stepI:p7:ch-surj2 | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj3@L258-L258 | the chosen (ell,g,L,G)
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj3@L258-L258 | Q
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerRegion_subset_image (KAM/Kepler/DelaunayChart.lean)
LEAN_NOTE: audit KEP-7 PASS WITH NOTES; named step (ch-surj1..3)
NOTE: -

NODE: stepI:p7:ch-diffeo
KIND: step
TITLE: Quotient diffeomorphism
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-diffeo@L260-L260
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-diffeo@L260-L260
CONTRACT_ID: stepI:p7:ch-diffeo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Q is the Delaunay map D_R -> C defined from the orbit formulas; no regularity, injectivity, surjectivity or periodicity conclusion is an added premise
SOURCE_QUANTIFIERS: On D_R, for all ell,g,L,G and all integer translates in ell,g; the induced map from (R/(2 pi Z))^2 x C_0 to C is the same quotient map as in the chart theorem
SOURCE_CONCLUSION: Q is 2pi-periodic in ell, g; the quotient map is a bijective local diffeomorphism, hence a real-analytic diffeomorphism onto C
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:kepler-eq, stepI:p7:ch-reg, stepI:p7:ch-inj, stepI:p7:ch-surj3, bpI:p7:x-ift, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-diffeo@L260-L260 | (b): periodicity of u
EDGE: stepI:p7:ch-reg | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-diffeo@L260-L260 | local diffeomorphism
EDGE: stepI:p7:ch-inj | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-diffeo@L260-L260 | injectivity modulo 2pi
EDGE: stepI:p7:ch-surj3 | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-diffeo@L260-L260 | surjectivity
EDGE: bpI:p7:x-ift | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-diffeo@L260-L260 | bijective local real-analytic diffeomorphism is a diffeomorphism
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-diffeo@L260-L260 | the calculation uses the Delaunay orbit map or its element formulas
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: delaunay_localDiffeo, delaunay_periodic (KAM/Kepler/DelaunayChart.lean)
LEAN_NOTE: audit KEP-7 PASS WITH NOTES; named step (ch-reg, ch-diffeo)
NOTE: -

NODE: bpI:p7:sec-ham#data
KIND: definition
TITLE: Data of section Hamilton's equations: W_mu and r_j
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-ham@L48-L49
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:sec-ham#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: mu in R; Definitions primaries and restricted
SOURCE_QUANTIFIERS: mu in R
SOURCE_CONCLUSION: defines W_mu = {z = (q,p) : CollisionFree mu z} = {q != a_1(mu), q != a_2(mu)}, open, and r_j = rad(q - a_j(mu)); H^R3_mu and V_mu are given on W_mu by the formulas of Definition restricted
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:primaries#CollisionFree, bpI:p0:primaries#radius, bpI:p0:primaries#primary1, bpI:p0:primaries#primary2, bpI:p0:restricted#restrictedHamiltonian, bpI:p0:restricted#restrictedVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:primaries#CollisionFree | blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-ham#data@L48-L48 | W_mu is the collision-free set
EDGE: bpI:p0:primaries#radius | blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-ham#data@L48-L48 | r_j = rad(q - a_j(mu))
EDGE: bpI:p0:primaries#primary1 | blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-ham#data@L48-L48 | a_1(mu)
EDGE: bpI:p0:primaries#primary2 | blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-ham#data@L48-L48 | a_2(mu)
EDGE: bpI:p0:restricted#restrictedHamiltonian | blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-ham#data@L49-L49 | H^R3_mu on W_mu
EDGE: bpI:p0:restricted#restrictedVectorField | blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-ham#data@L49-L49 | V_mu on W_mu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: data definition not named in any audited table
NOTE: section data node (SPEC): openness of W_mu is consumed by the ODE layer
