NODE: bpI:p2:standing
KIND: definition
TITLE: Standing data of Part~\ref{bpI:p2}
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing@L36-L42
PROOF_SOURCE: -
CONTRACT_ID: bpI:p2:standing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data and standing hypotheses of Part 2; inner hypotheses (I1)-(I4) of the I-G1 statement)
SOURCE_QUANTIFIERS: n, tau, M, sigma_K, sigma_B, sigma_T, sigma_omega, nu, omega*, D, H, E_0, gamma fixed (outermost)
SOURCE_CONCLUSION: defines the standing data of Part 2: n>=2, tau>=n-1, M,sigma_K,sigma_B,sigma_T>0, sigma_omega>1, nu>0, omega* in R^n minus {0}; D subset C^n x C^n and H: C^n x C^n -> C satisfy (I1)-(I4) of I-G1 (D open, Z^n-invariant in theta; H holomorphic, 1-periodic in theta, real at real points of D; ¦DH¦,¦X_H¦,¦DX_H¦,¦D^2 X_H¦,¦D^2 H¦ <= M on D); E_0 in R, gamma>0, omega* in Dio_{gamma,tau}
CONSTANT_SCOPE: all constants (n,tau,M,sigma's,nu,gamma,E_0) are fixed by the package; no dependence
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:diophantine#IsDiophantine, bpI:p0:hamiltonian#hamiltonianVectorFieldC
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:diophantine#IsDiophantine | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing@L41-L41 | omega* in Dio_{gamma,tau}
EDGE: bpI:p0:hamiltonian#hamiltonianVectorFieldC | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing@L40-L40 | X_H and its derivative bounds on D
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2
REVIEWER: sol-review-I-p2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.IsoStanding (KAM/Iso/Apost/Defs.lean)
LEAN_NOTE: Definition formalized (structure); audit I-D0-2 PASS (I-D0-1 table), nothing to prove
NOTE: -

NODE: bpI:p2:standing#k-bridge
KIND: step
TITLE: Bridge: Part 2 standing data contains K's standing data (h := H, B(frak) := D)
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing#k-bridge@L44-L48
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing#k-bridge@L44-L48
CONTRACT_ID: bpI:p2:standing#k-bridge
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p2:standing; for the frequency specialization take s>1. The r,K and Gram premises of Part 1 are supplied locally when that setting is used. K standing and K objects are targets of the identification, not extra hypotheses.
SOURCE_QUANTIFIERS: Part 2 standing data fixed; h:=H, mathfrak B:=D; for each s>1 set omega:=s omega*. For any local r,K satisfying the Part 1 strip, image and (where needed) Gram premises, use the indicated common objects.
SOURCE_CONCLUSION: The H,D,n,tau,M data meet K:bp:p2:standing after the frequency is specialized to omega=s omega*, whose Diophantinity is supplied by bpI:p2:ray. Thus K:bp:p2:hamiltonian applies on D. The common data for bpI:p1:setting agree; its r,K,image and frame premises are still checked at consumers. L,G,B,N,P,A,T,E,Omega_K,E_sym,E_red,Q,eta are K:bp:p2:objects with h:=H; Y:=DH(K)N, script-T:=avg extendedTorsion, and E^omega(K):=energyAverage(H,K)-E_0. No unbordered A5 or other result-specific premise is asserted.
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, K:bp:p2:standing, K:bp:p2:hamiltonian, bpI:p1:setting, bpI:p2:ray, K:bp:p2:objects
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing#k-bridge@L44-L44 | the package of Part 2
EDGE: K:bp:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing#k-bridge@L44-L44 | K standing data with h := H, B(frak) := D
EDGE: K:bp:p2:hamiltonian | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing#k-bridge@L45-L45 | K:bp:p2:hamiltonian applies to H on D
EDGE: bpI:p1:setting | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing#k-bridge@L45-L45 | Assumption bpI:p1:setting holds for omega = s omega*, s>1
EDGE: bpI:p2:ray | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing#k-bridge@L46-L46 | omega = s omega* is (gamma,tau)-Diophantine for s>1 (premise of bpI:p1:setting)
EDGE: K:bp:p2:objects | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing#k-bridge@L46-L46 | objects are those of K:bp:p2:objects with h := H
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.IsoStanding.setting (KAM/Iso/Apost/Standing.lean)
LEAN_NOTE: audit I2-1 PASS WITH NOTES: Part-1 Setting and K-standing at s*omega
NOTE: No SOURCE_GAP for the common-data transfer: n>=2,tau>=n-1 and all K Hamiltonian bounds are present, and the ray lemma pays Diophantinity. The sentence about Part 1 is read in its local r,K context; B1,B2,B4 supply its remaining premises wherever the frame is used. This bridge does not imply A5 or every K theorem hypothesis.

NODE: bpI:p2:ray
KIND: lemma
TITLE: Frequencies on the ray
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:ray@L50-L59
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:ray@L60-L65
CONTRACT_ID: bpI:p2:ray
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p2:standing (gamma, tau, omega* in Dio_{gamma,tau}, sigma_omega); s, sbar in R; omega = s omega*, omegabar = sbar omega*
SOURCE_QUANTIFIERS: standing data fixed; s, sbar in R
SOURCE_CONCLUSION: (a) s>0 gives omega in Dio_{gamma s,tau}; s>=1 gives omega in Dio_{gamma,tau}; gamma <= ¦omega*_1¦ <= ¦omega*¦; ¦omegabar-omega¦ = ¦sbar-s¦¦omega*¦. (b) nu(s):=min{s-1,sigma_omega-s}¦omega*¦ satisfies nu(sbar) >= nu(s)-¦omegabar-omega¦; if nu(s)>=nu' and ¦omegabar-omega¦ <= d < nu' then 1<sbar<sigma_omega and nu(sbar) >= nu'-d > 0
CONSTANT_SCOPE: gamma, tau, sigma_omega, omega* as in the standing data; nu' and d free
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, bpI:p0:diophantine#IsDiophantine, stepI:p2:ray-dio, stepI:p2:ray-margin
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:ray@L50-L50 | omega*, gamma, tau, sigma_omega
EDGE: bpI:p0:diophantine#IsDiophantine | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:ray@L53-L53 | Dio_{gamma,tau} membership
EDGE: stepI:p2:ray-dio | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:ray@L61-L61 | proof step of this result
EDGE: stepI:p2:ray-margin | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:ray@L63-L63 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2
REVIEWER: sol-review-I-p2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.ray (KAM/Iso/Apost/Standing.lean); KAM.Iso.Apost.rayMargin (KAM/Iso/Apost/Defs.lean)
LEAN_NOTE: audit I2-1 PASS WITH NOTES: all six conjuncts
NOTE: -

NODE: stepI:p2:ray-dio
KIND: step
TITLE: Diophantine
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ray-dio@L61-L62
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ray-dio@L61-L62
CONTRACT_ID: stepI:p2:ray-dio
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: omega* in Dio_{gamma,tau}; s>0 (s>=1 for the same gamma)
SOURCE_QUANTIFIERS: omega* fixed; s; k in Z^n minus {0}
SOURCE_CONCLUSION: ¦k.s omega*¦ = ¦s¦¦k.omega*¦ >= ¦s¦gamma(sum ¦k_i¦)^{-tau}; k = e_1 gives gamma <= ¦omega*_1¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, bpI:p1:ray, bpI:p0:diophantine#IsDiophantine
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ray-dio@L62-L62 | omega* in Dio_{gamma,tau}
EDGE: bpI:p1:ray | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ray-dio@L62-L62 | s omega* Diophantine with the constant of omega* for s>=1
EDGE: bpI:p0:diophantine#IsDiophantine | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ray-dio@L62-L62 | Diophantine inequality
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2
REVIEWER: sol-review-I-p2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.ray (KAM/Iso/Apost/Standing.lean)
LEAN_NOTE: Rule 05:10: ray conjuncts (a),(c) resp. (d),(e); I2-1-audit-1.md:40 and proof narrative (Standing:76-102) confirm by line range; parent ray PROVED.
NOTE: -

NODE: stepI:p2:ray-margin
KIND: step
TITLE: Margins
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ray-margin@L63-L64
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ray-margin@L63-L64
CONTRACT_ID: stepI:p2:ray-margin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ¦sbar-s¦ definitions; sigma_omega
SOURCE_QUANTIFIERS: s, sbar in R; omega*
SOURCE_CONCLUSION: sbar-1 >= s-1-¦sbar-s¦ and sigma_omega-sbar >= sigma_omega-s-¦sbar-s¦; multiplying by ¦omega*¦: nu(sbar) >= nu(s)-¦omegabar-omega¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ray-margin@L64-L64 | sigma_omega and omega* from the standing data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2
REVIEWER: sol-review-I-p2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.ray (KAM/Iso/Apost/Standing.lean)
LEAN_NOTE: Rule 05:10: ray conjuncts (a),(c) resp. (d),(e); I2-1-audit-1.md:40 and proof narrative (Standing:76-102) confirm by line range; parent ray PROVED.
NOTE: -

NODE: bpI:p2:constants
KIND: definition
TITLE: Constants
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:constants@L67-L91
PROOF_SOURCE: -
CONTRACT_ID: bpI:p2:constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (definition; inputs mu,nu>0, 0<rho_infty<rho; the K constants of K:bp:p2:constants)
SOURCE_QUANTIFIERS: n, tau, M, sigma_K, sigma_B, sigma_T fixed; then the K constants; then the hat-constants in the stated order; then (mu,nu) and (rho,rho_infty)
SOURCE_CONCLUSION: Use K constants kappa=tau+n>=2n-1>=3, a=2kappa+2>=8, c_R,m,Theta,C_X,C_T,C_Omega,C_sym,C_red,C_xi0,C_G,C_B,C_DeltaN,C_DeltaX,C_DeltaT. In the following formulas all hat-C names carry hats; C_P,C_Y,C_DeltaScriptT do not: hatC_S=max{C_xi0,m Theta+2n c_R m^5}; hatC_xiN=hatC_S+2n c_R m; hatC_g=C_T hatC_xiN+Theta hatC_S+2n m^2 Theta; hatC_xi=max{c_R hatC_g,Theta hatC_xiN}; hatC_DeltaK=2m^2 hatC_xi; hatC_Delta=max{hatC_DeltaK,Theta^2 hatC_S}; C_P=m^2+n+m^3+C_X; hatC_partial=C_P hatC_xi+2m^2 Theta hatC_g; hatC_lin=C_red hatC_xi+C_sym hatC_g+Theta C_Omega hatC_S; hatC_E1=4m^2 Theta^2 hatC_lin+m hatC_DeltaK^2+Theta hatC_S hatC_partial; hatC_E2=n Theta^2(2n m+C_Omega)c_R hatC_g+m hatC_DeltaK^2; hatC_E=max{hatC_E1,hatC_E2}; C_Y=n m(2m^2+C_DeltaN); C_DeltaScriptT=C_DeltaT+8n^2 m^4+1+C_Y; hatc_step=2Theta^3 max{C_sym,m C_DeltaScriptT hatC_Delta}; hatc_sum=4Theta^2 hatC_Delta max{n,C_B,m^2 C_DeltaScriptT}. For mu,nu>0 and 0<rho_infty<rho: hatc_*=max{2^{2a}hatC_E,hatc_step max{1,2/mu},2hatc_sum/mu,4Theta^2 hatC_Delta/nu}; delta_0=min{1,(rho-rho_infty)/8}.
CONSTANT_SCOPE: the K constants and all hat constants except hat-c_* and delta_0 depend only on (n,tau,M,sigma_K,sigma_B,sigma_T); hat-c_* in addition on (mu,nu); delta_0 on (rho,rho_infty); all finite, >=1 unless stated
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p2:constants, bpI:p2:standing, bpI:p2:standing#k-bridge
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:constants@L69-L69 | the K constants kappa,a,c_R,m,Theta,C_* used as inputs
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:constants@L69-L69 | constants depend on n,tau,M,sigma_K,sigma_B,sigma_T, nu from the standing data
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:constants@L69-L69 | applies K:bp:p2:constants under the Part 2 standing data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.iso_constants_spec (KAM/Iso/Apost/Constants.lean); KAM.Iso.Apost.hatCS (KAM/Iso/Apost/Defs.lean)
LEAN_NOTE: audit I2-2 PASS WITH NOTES (defs by I-D0-2); iso_constants_spec = Appendix A conjunction
NOTE: -

NODE: bpI:p2:admissible
KIND: definition
TITLE: Isoenergetic admissible parameterization
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L93-L112
PROOF_SOURCE: -
CONTRACT_ID: bpI:p2:admissible
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p2:standing; r,beta>0, 0<=eps<=1, s>1, omega := s omega*; K: C^n -> C^n x C^n
SOURCE_QUANTIFIERS: standing data and constants fixed; r, beta, eps, s, K
SOURCE_CONCLUSION: defines (r,beta,eps,s)-admissible: (B1) K holomorphic, primary, real on reals on T_r; (B2) B_beta(K(theta)) in D on T_r; (B3) ¦DK¦<=sigma_K on T_r; (B4) det G_K != 0, ¦B¦<=sigma_B on T_r; (B5) det avg T_H != 0 and ¦avg T_H^{-1}¦<=sigma_T; (B6) ¦E_{H,K,omega}¦<=eps on T_r; (B7) ¦Ebar_H(K)-E_0¦<=eps; and records gamma <= ¦omega¦ <= Theta (bpI:p2:freq, via K:bp:p2:frequency with A3,A4,A6 = B3,B4,B6 and omega in Dio_{gamma,tau}) and gamma delta^j <= Theta for delta<=1, j>=0
CONSTANT_SCOPE: sigma_K, sigma_B, sigma_T, gamma, E_0 as in the standing data; Theta, m from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, bpI:p2:constants, bpI:p2:standing#k-bridge, bpI:p0:domains#complexStrip, bpI:p0:stripdata#IsPrimaryOnStrip, bpI:p0:stripdata#IsRealOnReals, bpI:p0:stripdata#gramMatrix, bpI:p0:extended#extendedTorsionAverage, bpI:p0:stripdata#invarianceError, bpI:p0:extended#energyAverage, bpI:p1:extended-basic, K:bp:p2:frequency, K:bp:p2:admissible, bpI:p2:ray
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L94-L94 | sigma_K,sigma_B,sigma_T,D,H,E_0,gamma
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L110-L110 | m, Theta in the frequency bound
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L105-L105 | K:bp:p2:frequency applied under the standing data
EDGE: bpI:p0:domains#complexStrip | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L97-L97 | strip T_r
EDGE: bpI:p0:stripdata#IsPrimaryOnStrip | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L97-L97 | K primary on T_r
EDGE: bpI:p0:stripdata#IsRealOnReals | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L97-L97 | K real on reals
EDGE: bpI:p0:stripdata#gramMatrix | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L100-L100 | det G_K
EDGE: bpI:p0:extended#extendedTorsionAverage | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L101-L101 | avg T_H
EDGE: bpI:p0:stripdata#invarianceError | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L102-L102 | E_{H,K,omega}
EDGE: bpI:p0:extended#energyAverage | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L103-L103 | Ebar_H(K)
EDGE: bpI:p1:extended-basic | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L101-L101 | T_H and its average are defined by this lemma
EDGE: K:bp:p2:frequency | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L105-L105 | frequency bound gamma<=¦omega¦<=Theta
EDGE: K:bp:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L105-L105 | premise form (A3,A4,A6) of the frequency bound
EDGE: bpI:p2:ray | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L106-L106 | omega = s omega* in Dio_{gamma,tau}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.IsoAdmissible (KAM/Iso/Apost/Defs.lean); KAM.Iso.Apost.IsoAdmissible.freq (KAM/Iso/Apost/Standing.lean)
LEAN_NOTE: Definition formalized (I-D0-2 PASS); freq display proved in audit I2-1 PASS WITH NOTES
NOTE: -

NODE: bpI:p2:correction
KIND: lemma
TITLE: Size of the isoenergetic correction
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L132-L150
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L151-L166
CONTRACT_ID: bpI:p2:correction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p2:standing; s>1, omega = s omega*, 0<delta<=1, 2delta<r, 0<=eps<=1; K (r,beta,eps,s)-admissible (bpI:p2:admissible)
SOURCE_QUANTIFIERS: standing data, constants fixed; r, beta, s, delta, eps, K; then the border-solve data eta^L, eta^N, eta^omega, T, Y, sigma, xi^L_0 are defined from K
SOURCE_CONCLUSION: Lemma bpI:p1:border-solve applies with eta^L = -N^T Omega_0 E, eta^N = L^T Omega_0 E, eta^omega = -E^omega(K), T = T_{H,K,omega}, Y = DH(K)N, sigma = sigma_T, xi^L_0 = 0; xi, DeltaK := P xi are holomorphic, 1-periodic, real on reals, xi^omega in R; Deltaomega := -omega xi^omega, omegabar = sbar omega*, sbar = s(1-xi^omega); estimates ¦xi_0¦,¦xi^omega¦ <= C_S eps/(gamma delta^{kappa+1}), ¦xi^N¦ <= C_xiN eps/(gamma delta^{kappa+1}), ¦g^L¦ <= C_g eps/(gamma delta^{kappa+2}) on T_{r-delta}; ¦xi¦ <= C_xi eps/(gamma^2 delta^a), ¦DeltaK¦ <= C_DeltaK eps/(gamma^2 delta^a), ¦d_omega xi¦ <= C_g eps/(gamma delta^{kappa+2}), ¦d_omega DeltaK¦ <= C_partial eps/(gamma^2 delta^{a+1}) on T_{r-2delta}; ¦Deltaomega¦ = ¦sbar-s¦¦omega*¦ <= Theta^2 C_S eps/(gamma^2 delta^a); with d := C_Delta eps/(gamma^2 delta^a): ¦DeltaK¦ <= d on T_{r-2delta} and ¦Deltaomega¦ <= d
CONSTANT_SCOPE: Constants of Definition bpI:p2:constants: all depend only on (n,tau,M,sigma_K,sigma_B,sigma_T); hat-c_* also on (mu,nu); delta_0 on (rho,rho_infty); no dependence on K, s, e, gamma, omega*, sigma_omega; Gamma_delta = c_R gamma^{-1} delta^{-kappa}
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible, bpI:p2:standing#k-bridge, bpI:p1:border-solve, stepI:p2:co-data, stepI:p2:co-xi0, stepI:p2:co-xi, stepI:p2:co-omega, stepI:p2:co-dk, stepI:p2:co-reg
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L133-L133 | gamma, omega*, M, sigma_T, E_0
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L141-L141 | hat constants C_S,...,C_partial,C_Delta, Theta, c_R, kappa, a
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L133-L133 | K is (r,beta,eps,s)-admissible; B1-B7 and the frequency bound
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L133-L133 | applies the Part 1 lemma and K objects under the standing data
EDGE: bpI:p1:border-solve | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L133-L133 | the bordered solve is applied with the stated data
EDGE: stepI:p2:co-data | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L152-L152 | proof step of this result
EDGE: stepI:p2:co-xi0 | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L154-L154 | proof step of this result
EDGE: stepI:p2:co-xi | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L156-L156 | proof step of this result
EDGE: stepI:p2:co-omega | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L160-L160 | proof step of this result
EDGE: stepI:p2:co-dk | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L162-L162 | proof step of this result
EDGE: stepI:p2:co-reg | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L164-L164 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.correction (KAM/Iso/Apost/Correction.lean)
LEAN_NOTE: audit I2-3 PASS WITH NOTES: complete correction bounds and regularity
NOTE: -

NODE: stepI:p2:co-data
KIND: step
TITLE: Hypotheses of the border solve
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L152-L153
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L152-L153
CONTRACT_ID: stepI:p2:co-data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K admissible; omega = s omega*, s>1; 0<delta<=1, 2delta<r; standing data
SOURCE_QUANTIFIERS: K, eps, delta, r fixed
SOURCE_CONCLUSION: the hypotheses of border-solve hold: omega in Dio_{gamma,tau}, gamma<=¦omega¦<=Theta; on T_{r-delta} H_L = 2n m^2 eps, H_N = 2n m eps, H_T = C_T/delta; eta^L,eta^N,T holomorphic, 1-periodic, real on reals; avg eta^N = 0; Y holomorphic, periodic, real on reals with ¦Y¦ <= M sigma_K sigma_B <= m^3 =: H_Y; avg T_H invertible with ¦script-T^{-1}¦ <= sigma_T <= m; eta^omega real, ¦eta^omega¦ <= eps
CONSTANT_SCOPE: m, C_T, Theta from the constants; no new constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:admissible, bpI:p2:standing, bpI:p2:constants, bpI:p2:standing#k-bridge, bpI:p1:geometry-noA5, bpI:p1:energy-approx, bpI:p1:extended-basic, K:bp:p2:periodicity, K:bp:p2:frame-basic
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | freq bound (bpI:p2:freq), B5, B7
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | M, E_0 real, D, H
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | m, Theta, C_T, H_Y
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | K periodicity and frame results applied under the standing data
EDGE: bpI:p1:geometry-noA5 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | H_L, H_N, H_T bounds
EDGE: bpI:p1:energy-approx | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | avg eta^N = 0 (d) and avg(H o K) real (a)
EDGE: bpI:p1:extended-basic | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | Y holomorphic, periodic, real; bound on Y; avg T_H = script-T
EDGE: K:bp:p2:periodicity | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | eta^L, eta^N, T holomorphic, periodic, real on reals
EDGE: K:bp:p2:frame-basic | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | eta^L, eta^N, T holomorphic, periodic, real on reals
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2
REVIEWER: sol-review-I-p2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.correction, KAM.Iso.Apost.CorrectionAux.correction_core, KAM.Iso.Apost.isoNewS_smul_sub, KAM.Iso.Apost.isoNewS_smul_eq, KAM.Iso.Apost.CorrectionAux.norm_fderiv_frameMat_le (KAM/Iso/Apost/Correction.lean)
LEAN_NOTE: Rule 05:10: I2-3-audit-1.md:47 (Correction.lean:385-438 matches blueprint p2 L132-166) with items 3-5; bodies are step-labelled locals in correction_core (205-335); parent correction PROVED. Lean proves H_L,H_N on T_r (stronger).
NOTE: -

NODE: stepI:p2:co-xi0
KIND: step
TITLE: The constants $\xi_0,\xi^\omega$
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi0@L154-L155
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi0@L154-L155
CONTRACT_ID: stepI:p2:co-xi0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:correction, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:correction, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: S_* <= C_S eps/(gamma delta^{kappa+1}) (first entry <= 2n m(m Theta + c_R C_T)eps/(gamma delta^{kappa+1}), second <= (Theta + 2n c_R m^4) eps/(gamma delta^kappa))
CONSTANT_SCOPE: C_S from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p2:co-data, bpI:p1:border-solve, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p2:co-data | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi0@L155-L155 | proof step of this result
EDGE: bpI:p1:border-solve | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi0@L155-L155 | the quantity S_* of the border solve
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi0@L155-L155 | C_xi0, C_S, c_R, Theta, m
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi0@L155-L155 | gamma, sigma_T
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi0@L155-L155 | gamma delta^j <= Theta absorption
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.correction, KAM.Iso.Apost.CorrectionAux.correction_core, KAM.Iso.Apost.isoNewS_smul_sub, KAM.Iso.Apost.isoNewS_smul_eq, KAM.Iso.Apost.CorrectionAux.norm_fderiv_frameMat_le (KAM/Iso/Apost/Correction.lean)
LEAN_NOTE: Rule 05:10: I2-3-audit-1.md:47 (Correction.lean:385-438 matches blueprint p2 L132-166) with items 3-5; bodies are step-labelled locals in correction_core (205-335); parent correction PROVED. Lean proves H_L,H_N on T_r (stronger).
NOTE: -

NODE: stepI:p2:co-xi
KIND: step
TITLE: $\xi^N,g^L,\xi^L$
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L156-L159
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L156-L159
CONTRACT_ID: stepI:p2:co-xi
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:correction, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:correction, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: ¦xi^N¦ <= S_*+Gamma_delta H_N <= C_xiN eps/(gamma delta^{kappa+1}); ¦g^L¦ <= C_g eps/(gamma delta^{kappa+2}); ¦xi^L¦ <= c_R C_g eps/(gamma^2 delta^{2kappa+2}); ¦xi¦ <= C_xi eps/(gamma^2 delta^a); ¦DeltaK¦ <= ¦P¦¦xi¦ <= C_DeltaK eps/(gamma^2 delta^a); d_omega xi = (g^L,-eta^N) with ¦eta^N¦ <= C_g eps/(gamma delta^{kappa+2})
CONSTANT_SCOPE: C_xiN, C_g, C_xi, C_DeltaK from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p2:co-data, stepI:p2:co-xi0, bpI:p1:border-solve, bpI:p2:constants, bpI:p2:standing, K:bp:p2:frame-basic, bpI:p2:standing#k-bridge, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p2:co-data | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L157-L157 | proof step of this result
EDGE: stepI:p2:co-xi0 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L157-L157 | proof step of this result
EDGE: bpI:p1:border-solve | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L157-L157 | (b),(c): bounds on xi^N, g^L, xi^L and d_omega xi
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L158-L158 | C_xiN, C_g, C_xi, C_DeltaK, c_R
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L158-L158 | gamma, Theta
EDGE: K:bp:p2:frame-basic | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L159-L159 | bound ¦P¦ <= 2 m^2 on T_{r-2delta} used in ¦DeltaK¦ <= ¦P¦¦xi¦
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L159-L159 | K frame bounds under the standing data
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L159-L159 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.correction, KAM.Iso.Apost.CorrectionAux.correction_core, KAM.Iso.Apost.isoNewS_smul_sub, KAM.Iso.Apost.isoNewS_smul_eq, KAM.Iso.Apost.CorrectionAux.norm_fderiv_frameMat_le (KAM/Iso/Apost/Correction.lean)
LEAN_NOTE: Rule 05:10: I2-3-audit-1.md:47 (Correction.lean:385-438 matches blueprint p2 L132-166) with items 3-5; bodies are step-labelled locals in correction_core (205-335); parent correction PROVED. Lean proves H_L,H_N on T_r (stronger).
NOTE: -

NODE: stepI:p2:co-omega
KIND: step
TITLE: The frequency correction
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-omega@L160-L161
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-omega@L160-L161
CONTRACT_ID: stepI:p2:co-omega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:correction, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:correction, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: ¦Deltaomega¦ = ¦omega¦¦xi^omega¦ <= Theta^2 C_S eps/(gamma^2 delta^a) and Deltaomega = -xi^omega s omega*, so ¦Deltaomega¦ = ¦sbar-s¦¦omega*¦
CONSTANT_SCOPE: C_S, Theta from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p2:co-xi0, bpI:p2:ray, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p2:co-xi0 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-omega@L161-L161 | bound on xi^omega
EDGE: bpI:p2:ray | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-omega@L161-L161 | ¦omegabar-omega¦ = ¦sbar-s¦¦omega*¦ (ray (a))
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-omega@L161-L161 | C_S, Theta
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-omega@L161-L161 | gamma, omega*
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-omega@L161-L161 | ¦omega¦ <= Theta (bpI:p2:freq)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.correction, KAM.Iso.Apost.CorrectionAux.correction_core, KAM.Iso.Apost.isoNewS_smul_sub, KAM.Iso.Apost.isoNewS_smul_eq, KAM.Iso.Apost.CorrectionAux.norm_fderiv_frameMat_le (KAM/Iso/Apost/Correction.lean)
LEAN_NOTE: Rule 05:10: I2-3-audit-1.md:47 (Correction.lean:385-438 matches blueprint p2 L132-166) with items 3-5; bodies are step-labelled locals in correction_core (205-335); parent correction PROVED. Lean proves H_L,H_N on T_r (stronger).
NOTE: -

NODE: stepI:p2:co-dk
KIND: step
TITLE: Derivative of the correction along $\omega$
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L162-L163
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L162-L163
CONTRACT_ID: stepI:p2:co-dk
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:correction, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:correction, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: ¦d_omega L¦ <= m^2+n eps/delta, ¦d_omega N¦ <= m^3+C_X/delta, ¦d_omega P¦ <= C_P/delta on T_{r-delta}; ¦d_omega DeltaK¦ <= C_P C_xi eps/(gamma^2 delta^{a+1}) + 2 m^2 C_g eps/(gamma delta^{kappa+2}) <= C_partial eps/(gamma^2 delta^{a+1})
CONSTANT_SCOPE: C_P, C_partial, C_X from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p2:frame-identities, bpI:p2:standing#k-bridge, stepI:p2:co-xi, stepI:p2:co-data, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible, bpI:p1:geometry-noA5
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p2:frame-identities | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L163-L163 | d_omega L = AL - DE, d_omega N = AN - X_N (c)
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L163-L163 | K frame identities under the standing data
EDGE: stepI:p2:co-xi | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L163-L163 | bounds on xi and d_omega xi
EDGE: stepI:p2:co-data | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L163-L163 | data of the border solve (eps bound B6)
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L163-L163 | C_P, C_X, C_partial, m
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L163-L163 | gamma
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L163-L163 | B6: ¦E¦ <= eps
EDGE: bpI:p1:geometry-noA5 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L163-L163 | Provides the DE and X_N bounds used in the two frame derivative estimates.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.correction, KAM.Iso.Apost.CorrectionAux.correction_core, KAM.Iso.Apost.isoNewS_smul_sub, KAM.Iso.Apost.isoNewS_smul_eq, KAM.Iso.Apost.CorrectionAux.norm_fderiv_frameMat_le (KAM/Iso/Apost/Correction.lean)
LEAN_NOTE: Rule 05:10: I2-3-audit-1.md:47 (Correction.lean:385-438 matches blueprint p2 L132-166) with items 3-5; bodies are step-labelled locals in correction_core (205-335); parent correction PROVED. Lean proves H_L,H_N on T_r (stronger).
NOTE: -

NODE: stepI:p2:co-reg
KIND: step
TITLE: Regularity
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L164-L165
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L164-L165
CONTRACT_ID: stepI:p2:co-reg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:correction, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:correction, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: xi and P are holomorphic, 1-periodic and real on reals, hence DeltaK=P xi is holomorphic, 1-periodic and real on reals on T_{r-2delta}; xi^omega is real by border-solve(e). Since hatC_DeltaK,Theta^2 hatC_S<=hatC_Delta, ¦DeltaK¦<=d there and ¦Deltaomega¦<=d.
CONSTANT_SCOPE: C_Delta from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:border-solve, K:bp:p2:periodicity, bpI:p2:standing#k-bridge, stepI:p2:co-data, stepI:p2:co-xi, stepI:p2:co-omega, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:border-solve | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | (a),(e): xi holomorphic, periodic, real on reals
EDGE: K:bp:p2:periodicity | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | P holomorphic, periodic, real on reals
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | K periodicity under the standing data
EDGE: stepI:p2:co-data | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | hypotheses (realness) of the border solve
EDGE: stepI:p2:co-xi | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | ¦DeltaK¦ bound
EDGE: stepI:p2:co-omega | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | ¦Deltaomega¦ bound
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | C_Delta >= C_DeltaK, Theta^2 C_S
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.correction, KAM.Iso.Apost.CorrectionAux.correction_core, KAM.Iso.Apost.isoNewS_smul_sub, KAM.Iso.Apost.isoNewS_smul_eq, KAM.Iso.Apost.CorrectionAux.norm_fderiv_frameMat_le (KAM/Iso/Apost/Correction.lean)
LEAN_NOTE: Rule 05:10: I2-3-audit-1.md:47 (Correction.lean:385-438 matches blueprint p2 L132-166) with items 3-5; bodies are step-labelled locals in correction_core (205-335); parent correction PROVED. Lean proves H_L,H_N on T_r (stronger).
NOTE: -

NODE: bpI:p2:newton-error
KIND: lemma
TITLE: The new errors
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L168-L181
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L182-L193
CONTRACT_ID: bpI:p2:newton-error
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting of bpI:p2:correction (standing data; s>1; 0<delta<=1; 2delta<r; K admissible); d < beta; C_sym eps/(gamma delta^{kappa+1}) <= 1/2; Kbar := K+DeltaK on T_{r-2delta}, Kbar := K elsewhere
SOURCE_QUANTIFIERS: standing data and constants fixed; r,beta,s,delta,eps,K as in bpI:p2:correction; use its constructed xi,DeltaK,Deltaomega,omegabar and d := hatC_Delta eps/(gamma^2 delta^a), subject to the additional two inequalities; define Kbar and the new errors as displayed; no new independent beta or d
SOURCE_CONCLUSION: Kbar(T_{r-2delta}) in D; S := I - Omega_0 E_sym invertible with ¦S^{-1}¦<=2 on T_{r-2delta}; Ebar := E_{H,Kbar,omegabar} = P S^{-1} E_lin + Delta^2 X + xi^omega d_omega DeltaK with E_lin := E_red xi + Omega_0 E_sym d_omega xi - (0,Omega_K omega) xi^omega, Delta^2 X := X_H(Kbar)-X_H(K)-A DeltaK; Ebar^omega := Ebar_H(Kbar)-E_0 = E^omega_lin + avg(Delta^2 H), E^omega_lin = avg(D(H o K) xi^L), Delta^2 H := H(Kbar)-H(K)-DH(K)DeltaK; ¦Ebar¦ <= C_E eps^2/(gamma^4 delta^{2a}) on T_{r-2delta} and ¦Ebar^omega¦ <= C_E eps^2/(gamma^4 delta^{2a})
CONSTANT_SCOPE: Constants of Definition bpI:p2:constants: all depend only on (n,tau,M,sigma_K,sigma_B,sigma_T); hat-c_* also on (mu,nu); delta_0 on (rho,rho_infty); no dependence on K, s, e, gamma, omega*, sigma_omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible, bpI:p2:standing#k-bridge, bpI:p2:correction, stepI:p2:ne-invert, stepI:p2:ne-expand, stepI:p2:ne-reduce, stepI:p2:ne-est, stepI:p2:ne-energy
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L169-L169 | gamma, M, D, H
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L169-L169 | C_sym, C_E, kappa, a
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L169-L169 | K is (r,beta,eps,s)-admissible; B1-B7 and the frequency bound
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L184-L184 | K frame identities applied under the Part 2 standing data
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L169-L169 | setting of the lemma; DeltaK, Deltaomega, d, xi
EDGE: stepI:p2:ne-invert | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L183-L183 | proof step of this result
EDGE: stepI:p2:ne-expand | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L185-L185 | proof step of this result
EDGE: stepI:p2:ne-reduce | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L187-L187 | proof step of this result
EDGE: stepI:p2:ne-est | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L189-L189 | proof step of this result
EDGE: stepI:p2:ne-energy | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L191-L191 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.newton_error (KAM/Iso/Apost/NewtonError.lean)
LEAN_NOTE: audit I2-4 PASS WITH NOTES: all six conclusions
NOTE: -

NODE: stepI:p2:ne-invert
KIND: step
TITLE: Invertibility and domain
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L183-L184
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L183-L184
CONTRACT_ID: stepI:p2:ne-invert
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:newton-error, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:newton-error, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: S invertible with ¦S^{-1}¦<=2; Q P = S so Q^{-1} = P S^{-1}; Kbar(theta) in B_beta(K(theta)) in D and the segment [K,Kbar] in D
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:geometry-noA5, K:bp:p1:neumann, K:bp:p2:frame-identities, bpI:p2:standing#k-bridge, bpI:p2:correction, bpI:p2:admissible, bpI:p2:standing, bpI:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:geometry-noA5 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L184-L184 | ¦Omega_0 E_sym¦ <= 1/2
EDGE: K:bp:p1:neumann | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L184-L184 | Neumann series: ¦S^{-1}¦ <= 2
EDGE: K:bp:p2:frame-identities | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L184-L184 | Q P = S (f)
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L184-L184 | K frame identities under the standing data
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L184-L184 | ¦DeltaK¦ <= d
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L184-L184 | B2: B_beta(K) in D
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L184-L184 | D open, convex ball in D
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L184-L184 | Uses constants or exponents fixed by this package.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.NewtonErrorAux.sMat_bounds, KAM.Iso.Apost.NewtonErrorAux.isoResidual_eq_frame, KAM.Iso.Apost.newton_error (KAM/Iso/Apost/NewtonError.lean)
LEAN_NOTE: Rule 05:10: I2-4-audit-1.md:61-66 (table by Lean line ranges 321-328, 331-361, 374-438, 451-570) and 'Expansion and reduction/Invariance bound/Energy' paragraphs; parent newton-error PROVED. Lean uses M for source m; D(H o K) bound sharper than source form.
NOTE: -

NODE: stepI:p2:ne-expand
KIND: step
TITLE: Expansion
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-expand@L185-L186
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-expand@L185-L186
CONTRACT_ID: stepI:p2:ne-expand
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:newton-error, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:newton-error, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: Ebar = X_H(K+DeltaK)-(L+D DeltaK)(omega+Deltaomega) = E + A DeltaK - d_omega DeltaK - L Deltaomega + Delta^2 X - D DeltaK Deltaomega, and D DeltaK Deltaomega = -xi^omega d_omega DeltaK
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:correction, stepI:p2:ne-invert, bpI:p2:standing#k-bridge, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-expand@L186-L186 | definitions of DeltaK, Deltaomega, xi^omega
EDGE: stepI:p2:ne-invert | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-expand@L186-L186 | Kbar in D so X_H(Kbar) is defined
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-expand@L186-L186 | K objects (L, A, E) under the standing data
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-expand@L186-L186 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-expand@L186-L186 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.NewtonErrorAux.sumVec_invarianceError_isoNewtonMap (KAM/Iso/Apost/NewtonError.lean)
LEAN_NOTE: Rule 05:10: I2-4-audit-1.md:61-66 (table by Lean line ranges 321-328, 331-361, 374-438, 451-570) and 'Expansion and reduction/Invariance bound/Energy' paragraphs; parent newton-error PROVED. Lean uses M for source m; D(H o K) bound sharper than source form.
NOTE: -

NODE: stepI:p2:ne-reduce
KIND: step
TITLE: Reduction by $Q$
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L187-L188
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L187-L188
CONTRACT_ID: stepI:p2:ne-reduce
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:newton-error, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:newton-error, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: Q(E + A DeltaK - d_omega DeltaK - L Deltaomega) = Lambda xi - d_omega xi + (omega,0) xi^omega - eta + E_lin = E_lin by the first two border equations; applying Q^{-1} = P S^{-1} gives (bpI:p2:newerr)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:reduced, bpI:p2:standing#k-bridge, bpI:p1:border-solve, bpI:p2:correction, stepI:p2:ne-expand, stepI:p2:ne-invert, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:reduced | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L188-L188 | (b): reduction of the equation by Q
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L188-L188 | Part 1 reduced lemma under the standing data
EDGE: bpI:p1:border-solve | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L188-L188 | first two equations of (b)
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L188-L188 | the data of the correction
EDGE: stepI:p2:ne-expand | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L188-L188 | expanded error
EDGE: stepI:p2:ne-invert | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L188-L188 | Q^{-1} = P S^{-1}
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L188-L188 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L188-L188 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.NewtonErrorAux.sumVec_error_eq (KAM/Iso/Apost/NewtonError.lean)
LEAN_NOTE: Rule 05:10: I2-4-audit-1.md:61-66 (table by Lean line ranges 321-328, 331-361, 374-438, 451-570) and 'Expansion and reduction/Invariance bound/Energy' paragraphs; parent newton-error PROVED. Lean uses M for source m; D(H o K) bound sharper than source form.
NOTE: -

NODE: stepI:p2:ne-est
KIND: step
TITLE: Estimates
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L189-L190
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L189-L190
CONTRACT_ID: stepI:p2:ne-est
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:newton-error, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:newton-error, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: ¦E_lin¦ <= C_lin eps^2/(gamma^2 delta^{a+1}); ¦Delta^2 X¦ <= M¦DeltaK¦^2 <= m C_DeltaK^2 eps^2/(gamma^4 delta^{2a}); ¦xi^omega d_omega DeltaK¦ <= C_S C_partial eps^2/(gamma^3 delta^{kappa+a+2}); with ¦P¦¦S^{-1}¦ <= 4 m^2: ¦Ebar¦ <= C_E1 eps^2/(gamma^4 delta^{2a})
CONSTANT_SCOPE: C_lin, C_E1 from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:geometry-noA5, bpI:p2:correction, K:bp:p2:hamiltonian, bpI:p2:standing#k-bridge, stepI:p2:ne-reduce, stepI:p2:ne-invert, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:geometry-noA5 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | bounds on E_red, E_sym, Omega_K
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | bounds on xi, d_omega xi, xi^omega, d_omega DeltaK
EDGE: K:bp:p2:hamiltonian | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | (e): ¦Delta^2 X¦ <= M¦DeltaK¦^2
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | K Hamiltonian lemma under the standing data
EDGE: stepI:p2:ne-reduce | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | E_lin and the representation of Ebar
EDGE: stepI:p2:ne-invert | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | ¦S^{-1}¦ <= 2
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | C_red, C_sym, C_Omega, C_lin, C_E1, Theta, m
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | gamma, M
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | gamma <= Theta
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.NewtonErrorAux.norm_error_le, KAM.Iso.Apost.NewtonErrorAux.norm_isoQuadX_le (KAM/Iso/Apost/NewtonError.lean)
LEAN_NOTE: Rule 05:10: I2-4-audit-1.md:61-66 (table by Lean line ranges 321-328, 331-361, 374-438, 451-570) and 'Expansion and reduction/Invariance bound/Energy' paragraphs; parent newton-error PROVED. Lean uses M for source m; D(H o K) bound sharper than source form.
NOTE: -

NODE: stepI:p2:ne-energy
KIND: step
TITLE: The energy error
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L191-L192
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L191-L192
CONTRACT_ID: stepI:p2:ne-energy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:newton-error, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:newton-error, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: Ebar^omega = E^omega + avg(DH(K)DeltaK) + avg(Delta^2 H); avg(DH(K)DeltaK) = -E^omega + E^omega_lin; ¦Delta^2 H¦ <= (M/2)¦DeltaK¦^2; ¦D(H o K)¦ <= n Theta(2n m + C_Omega) eps/(gamma delta^{kappa+1}) on R^n; the product with ¦xi^L¦ is <= C_E2 eps^2/(gamma^4 delta^{2a}); so ¦Ebar^omega¦ <= C_E eps^2/(gamma^4 delta^{2a})
CONSTANT_SCOPE: C_E2, C_E from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:energy-approx, bpI:p1:border-solve, K:bp:p1:taylor, bpI:p2:correction, stepI:p2:ne-invert, bpI:p2:standing#k-bridge, bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible, bpI:p1:geometry-noA5, K:bp:p1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:energy-approx | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | (f): avg(DH(K)DeltaK) and the bound on D(H o K)
EDGE: bpI:p1:border-solve | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | third equation avg(Y xi^N) = eta^omega
EDGE: K:bp:p1:taylor | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | Taylor remainder ¦Delta^2 H¦ <= (M/2)¦DeltaK¦^2
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | bounds on xi^L, eta^N, DeltaK
EDGE: stepI:p2:ne-invert | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | segment [K,Kbar] in D
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | Part 1 energy lemma under the standing data
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | M, omega, D^2 H bound
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | C_E2, C_E, C_Omega, Theta, m
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | gamma delta^{kappa+1} <= Theta
EDGE: bpI:p1:geometry-noA5 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | the bound on Omega_K and the eta bounds supply the displayed estimate for D(H o K)
EDGE: K:bp:p1:ext-integral | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | continuous integrands on the compact real cube; linearity of the energy average and norm bounded by the unit-cube supremum
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.NewtonErrorAux.energyAverage_sub_eq, KAM.Iso.Apost.NewtonErrorAux.norm_energyAverage_sub_le, KAM.Iso.Apost.NewtonErrorAux.norm_isoQuadH_le (KAM/Iso/Apost/NewtonError.lean)
LEAN_NOTE: Rule 05:10: I2-4-audit-1.md:61-66 (table by Lean line ranges 321-328, 331-361, 374-438, 451-570) and 'Expansion and reduction/Invariance bound/Energy' paragraphs; parent newton-error PROVED. Lean uses M for source m; D(H o K) bound sharper than source form.
NOTE: -

NODE: bpI:p2:torsion
KIND: lemma
TITLE: The new averaged extended torsion
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L205-L213
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L214-L225
CONTRACT_ID: bpI:p2:torsion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing data; K (r,beta,eps,s)-admissible; 0<delta<=1, 4delta<r; Kbar, omegabar as in bpI:p2:newton-error; d<beta; 2 m C_DeltaScriptT d/delta^2 <= 1
SOURCE_QUANTIFIERS: standing data and constants fixed; r,beta,eps,s,delta,K as stated, with 4delta<r; use the correction/new-error constructions Kbar,omegabar and d := hatC_Delta eps/(gamma^2 delta^a); impose the stated smallness conditions on this d, not a new independent parameter
SOURCE_CONCLUSION: omegabar in R^n; T_H for (Kbar,omegabar) defined on T_{r-3delta}; Kbar holomorphic on T_{r-2delta}, primary, real on reals; det Gbar != 0 on T_{r-3delta} with ¦DKbar¦ <= 2m, ¦Bbar¦ <= 2m; B_{beta-d}(Kbar) in D on T_{r-2delta}; ¦DKbar-DK¦ <= nd/delta and ¦Bbar-B¦ <= C_B d/delta on T_{r-3delta}; avg Tbar := avg T_H(Kbar,omegabar) defined, invertible, ¦avg Tbar - avg T¦ <= C_DeltaScriptT d/delta^2, ¦avg Tbar^{-1} - avg T^{-1}¦ <= 2 m^2 C_DeltaScriptT d/delta^2
CONSTANT_SCOPE: Constants of Definition bpI:p2:constants: all depend only on (n,tau,M,sigma_K,sigma_B,sigma_T); hat-c_* also on (mu,nu); delta_0 on (rho,rho_infty); no dependence on K, s, e, gamma, omega*, sigma_omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible, bpI:p2:standing#k-bridge, bpI:p2:newton-error, bpI:p2:correction, stepI:p2:to-frame, stepI:p2:to-omega, stepI:p2:to-row, stepI:p2:to-avg, stepI:p2:to-inv
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L206-L206 | standing data
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L206-L206 | C_DeltaScriptT, C_B, m
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L206-L206 | K is (r,beta,eps,s)-admissible; B1-B7 and the frequency bound
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L222-L222 | K averages/matrix lemmas applied to the displayed full-matrix difference
EDGE: bpI:p2:newton-error | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L206-L206 | Kbar, omegabar as in the new-error lemma
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L216-L216 | the correction supplies norm(Kbar-K) <= d for the frame perturbation application
EDGE: stepI:p2:to-frame | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L215-L215 | proof step of this result
EDGE: stepI:p2:to-omega | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L217-L217 | proof step of this result
EDGE: stepI:p2:to-row | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L219-L219 | proof step of this result
EDGE: stepI:p2:to-avg | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L221-L221 | proof step of this result
EDGE: stepI:p2:to-inv | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L223-L223 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.torsion_step (KAM/Iso/Apost/Torsion.lean)
LEAN_NOTE: audit I2-5 PASS WITH NOTES: exact design-v2 statement
NOTE: Preextract candidate edge to bpI:p2:iteration (parenthetical forward pointer to (iii),(iv)) dropped: forward pointer, would create a cycle.

NODE: stepI:p2:to-frame
KIND: step
TITLE: Frame
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L215-L216
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L215-L216
CONTRACT_ID: stepI:p2:to-frame
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:torsion, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:torsion, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: ball B_{beta-d}(Kbar) in D, derivative and Gram-inverse bounds, ¦Nbar-N¦ <= C_DeltaN d/delta, ¦Nbar¦ <= 2m^2 on T_{r-3delta}, ¦Tbar_omega - T_omega¦ <= C_DeltaT d/delta^2 on T_{r-4delta}; Nbar, Tbar_omega holomorphic on T_{r-3delta} so T_H(Kbar,omegabar) is continuous on R^n and its average is defined
CONSTANT_SCOPE: C_DeltaN and the old K torsion constant C_DeltaT from bpI:p2:constants; the inherited smallness uses C_DeltaScriptT >= C_DeltaT
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:perturbation-noA5, bpI:p2:correction, bpI:p2:newton-error, bpI:p1:extended-basic, bpI:p2:standing#k-bridge, bpI:p2:constants, bpI:p2:admissible, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:perturbation-noA5 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L216-L216 | perturbation lemma applied with Ktilde = Kbar
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L216-L216 | ¦Kbar-K¦ <= d on T_{r-2delta}
EDGE: bpI:p2:newton-error | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L216-L216 | Kbar := K+DeltaK
EDGE: bpI:p1:extended-basic | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L216-L216 | average of T_H defined for Kbar
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L216-L216 | Part 1 perturbation lemma under the standing data
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L216-L216 | C_DeltaT, C_DeltaN, m
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L216-L216 | B1-B4 hypotheses of the perturbation lemma
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L216-L216 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.torsion_step, KAM.Iso.Apost.TorsionAux.isoNewtonMap_differentiableOn (KAM/Iso/Apost/Torsion.lean)
LEAN_NOTE: audit I2-5 PASS WITH NOTES: to-frame mapped to torsion_step assembly and aux lemmas
NOTE: SOURCE_GAP: scoped to the final parenthetical application of bpI:p1:extended-basic at L216 with Kbar and omegabar. That lemma assumes bpI:p1:setting, including a positive Diophantine constant for this same frequency. The torsion lemma explicitly uses no Diophantine property of omegabar, and none is supplied here; the k-bridge concerns the old omega=s omega*. The frame perturbation application at the old omega is paid by the stated local data. The printed holomorphy/continuity discussion suggests a direct finite-frequency proof, but this record does not silently strengthen the cited Part 1 contract or add Diophantinity as a source hypothesis.

NODE: stepI:p2:to-omega
KIND: step
TITLE: Effect of the frequency on the torsion block
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L217-L218
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L217-L218
CONTRACT_ID: stepI:p2:to-omega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:torsion, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:torsion, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: T_{omegabar}(Kbar)-T_omega(Kbar) = -Nbar^T Omega_0 [D Nbar_j Deltaomega]_j; ¦d_{Deltaomega} Nbar¦ <= n¦Deltaomega¦ 2m^2/delta on T_{r-4delta}; ¦Nbar^T¦ <= 4 n m^2; hence the difference is <= 8 n^2 m^4 d/delta on T_{r-4delta}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:cauchy-corollaries, stepI:p2:to-frame, bpI:p2:correction, bpI:p0:stripdata#torsion, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:cauchy-corollaries | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L218-L218 | Cauchy estimate with loss delta
EDGE: stepI:p2:to-frame | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L218-L218 | bound on Nbar
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L218-L218 | ¦Deltaomega¦ <= d
EDGE: bpI:p0:stripdata#torsion | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L218-L218 | torsion entries N_i.Omega_0(A N_j - D N_j omega)
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L218-L218 | m
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L218-L218 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L218-L218 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.TorsionDiff.torsion_sub_freq, KAM.Iso.Apost.TorsionDiff.norm_torsion_sub_freq_le (KAM/Iso/Apost/TorsionDiff.lean)
LEAN_NOTE: audit I2-5 PASS WITH NOTES: to-omega affine identity and Cauchy bound
NOTE: -

NODE: stepI:p2:to-row
KIND: step
TITLE: Effect on the energy row
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L219-L220
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L219-L220
CONTRACT_ID: stepI:p2:to-row
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:torsion, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:torsion, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: Ybar-Y = (DH(Kbar)-DH(K))Nbar + DH(K)(Nbar-N); ¦DH(Kbar)-DH(K)¦ <= M d; ¦Ybar-Y¦ <= C_Y d/delta on T_{r-3delta}
CONSTANT_SCOPE: C_Y from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:increments-open, stepI:p2:to-frame, bpI:p2:correction, stepI:p2:ne-invert, bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:increments-open | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L220-L220 | F = DH: ¦DH(Kbar)-DH(K)¦ <= M d
EDGE: stepI:p2:to-frame | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L220-L220 | bounds on Nbar and Nbar-N
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L220-L220 | ¦Kbar-K¦ <= d
EDGE: stepI:p2:ne-invert | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L220-L220 | segment [K,Kbar] in D
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L220-L220 | M, ¦D^2 H¦ <= M on D
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L220-L220 | C_Y, C_DeltaN, m
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L220-L220 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.TorsionDiff.energyRow_sub, KAM.Iso.Apost.TorsionDiff.sum_norm_energyRow_sub_le (KAM/Iso/Apost/TorsionDiff.lean)
LEAN_NOTE: audit I2-5 PASS WITH NOTES: to-row exact splitting and row estimate
NOTE: -

NODE: stepI:p2:to-avg
KIND: step
TITLE: The average
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L221-L222
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L221-L222
CONTRACT_ID: stepI:p2:to-avg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:torsion, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:torsion, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: avg Tbar - avg T = avg of [[Tbar_{omegabar}-T_omega, Deltaomega],[Ybar-Y, 0]] on R^n in T_{r-4delta}; its norm <= max{C_DeltaT^K d/delta^2 + 8 n^2 m^4 d/delta + d, C_Y d/delta} <= C_DeltaScriptT d/delta^2
CONSTANT_SCOPE: C_DeltaScriptT from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p2:averages, K:bp:p2:matrix, bpI:p2:standing#k-bridge, stepI:p2:to-frame, stepI:p2:to-omega, stepI:p2:to-row, bpI:p2:correction, bpI:p1:extended-basic, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p2:averages | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | (a): average of the difference
EDGE: K:bp:p2:matrix | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | (c): norm of the block matrix
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | K averages/matrix lemmas under the standing data
EDGE: stepI:p2:to-frame | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | bound on Tbar_omega - T_omega
EDGE: stepI:p2:to-omega | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | effect of the frequency on the torsion block
EDGE: stepI:p2:to-row | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | bound on Ybar - Y
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | ¦Deltaomega¦ <= d
EDGE: bpI:p1:extended-basic | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | block structure of T_H and its average
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | C_DeltaScriptT
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.TorsionDiff.norm_extendedTorsionAverage_sub_le, KAM.Iso.Apost.TorsionDiff.torsion_diff_arith (KAM/Iso/Apost/TorsionDiff.lean)
LEAN_NOTE: audit I2-5 PASS WITH NOTES: to-avg block difference, integral norm, domination
NOTE: -

NODE: stepI:p2:to-inv
KIND: step
TITLE: Inverse (Lemma~A.1)
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-inv@L223-L224
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-inv@L223-L224
CONTRACT_ID: stepI:p2:to-inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:torsion, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:torsion, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: ¦avg T^{-1}¦ ¦avg Tbar-avg T¦<=1/2. Neumann gives invertibility and ¦avg Tbar^{-1}-avg T^{-1}¦<=2 sigma_T^2 ¦avg Tbar-avg T¦<=2m^2 C_DeltaScriptT d/delta^2, in the max-row-sum norm on C^{(n+1)x(n+1)}.
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:neumann, stepI:p2:to-avg, bpI:p2:admissible, bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:neumann | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-inv@L224-L224 | Neumann series (HL19 Lemma A.1)
EDGE: stepI:p2:to-avg | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-inv@L224-L224 | difference bound for the averages
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-inv@L224-L224 | B5: ¦avg T^{-1}¦ <= sigma_T
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-inv@L224-L224 | sigma_T <= m, C_DeltaScriptT
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-inv@L224-L224 | sigma_T
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.torsion_step (KAM/Iso/Apost/Torsion.lean)
LEAN_NOTE: audit I2-5 PASS WITH NOTES: to-inv assembly via neumann_fintype in torsion_step
NOTE: -

NODE: bpI:p2:step
KIND: proposition
TITLE: The isoenergetic step
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L227-L241
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L242-L250
CONTRACT_ID: bpI:p2:step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing data; r>0, 0<delta<=1, 4delta<r, beta>0, 0<=eps<=1, s>1; K (r,beta,eps,s)-admissible; c_step eps/(gamma^4 delta^{2a}) <= min{1,beta}; Kbar, omegabar as in correction and new-error; d := C_Delta eps/(gamma^2 delta^a)
SOURCE_QUANTIFIERS: standing data, constants fixed; r, delta, beta, eps, s, K
SOURCE_CONCLUSION: (a) Kbar holomorphic, primary on T_{r-2delta}, real on reals; (b) ¦Kbar-K¦ <= d <= beta/2 on T_{r-2delta}, B_{beta-d}(Kbar(theta)) in D, ¦sbar-s¦¦omega*¦ <= d; (c) ¦E_{H,Kbar,omegabar}¦ <= C_E eps^2/(gamma^4 delta^{2a}) on T_{r-2delta} and ¦Ebar_H(Kbar)-E_0¦ <= C_E eps^2/(gamma^4 delta^{2a}); (d) ¦DKbar-DK¦ <= nd/delta, det Gbar != 0, ¦Bbar-B¦ <= C_B d/delta on T_{r-3delta}; (e) avg T_H(Kbar,omegabar) invertible with ¦avg Tbar^{-1}-avg T^{-1}¦ <= 2 m^2 C_DeltaScriptT d/delta^2
CONSTANT_SCOPE: Constants of Definition bpI:p2:constants: all depend only on (n,tau,M,sigma_K,sigma_B,sigma_T); hat-c_* also on (mu,nu); delta_0 on (rho,rho_infty); no dependence on K, s, e, gamma, omega*, sigma_omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible, bpI:p2:correction, bpI:p2:newton-error, stepI:p2:st-small, stepI:p2:st-error, stepI:p2:st-frame
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L228-L228 | standing data
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L230-L230 | c_step, C_Delta, C_E, C_B, C_DeltaScriptT, a, m
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L228-L228 | K is (r,beta,eps,s)-admissible; B1-B7 and the frequency bound
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L232-L232 | Kbar, omegabar, d from the correction lemma
EDGE: bpI:p2:newton-error | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L232-L232 | errors of Kbar
EDGE: stepI:p2:st-small | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L243-L243 | proof step of this result
EDGE: stepI:p2:st-error | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L246-L246 | proof step of this result
EDGE: stepI:p2:st-frame | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L248-L248 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-global-I
REVIEWER: sol-delta-I-global
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.step (KAM/Iso/Apost/Step.lean)
LEAN_NOTE: audit I2-6 PASS WITH NOTES: all conclusions (a)-(e)
NOTE: -

NODE: stepI:p2:st-small
KIND: step
TITLE: Smallness
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-small@L243-L245
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-small@L243-L245
CONTRACT_ID: stepI:p2:st-small
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:step, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:step, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: C_sym eps/(gamma delta^{kappa+1}) <= Theta^3 C_sym X <= 1/2; d <= Theta^2 C_Delta X <= beta/2; 2 m C_DeltaScriptT d/delta^2 <= 2 m Theta^2 C_DeltaScriptT C_Delta X <= 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:admissible, bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-small@L244-L244 | gamma <= Theta (bpI:p2:freq) and gamma^2 delta^{a-2} <= Theta^2
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-small@L244-L244 | c_step, C_sym, C_Delta, C_DeltaScriptT, Theta, m
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-small@L244-L244 | gamma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.Arith.iso_step_small (KAM/Iso/Apost/ConstantsArith.lean)
LEAN_NOTE: audit I2-2 PASS WITH NOTES: exactly the three scalar conclusions of st-small
NOTE: -

NODE: stepI:p2:st-error
KIND: step
TITLE: Correction and errors
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-error@L246-L247
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-error@L246-L247
CONTRACT_ID: stepI:p2:st-error
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:step, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:step, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: (a) Kbar holomorphic, primary, real on reals (Kbar(theta+k) = K(theta)+(k,0)+DeltaK(theta)); (b) except the ball; (c) both errors <= C_E eps^2/(gamma^4 delta^{2a})
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:correction, bpI:p2:newton-error, stepI:p2:st-small, bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-error@L247-L247 | DeltaK holomorphic, periodic, real; ¦DeltaK¦ <= d; ¦Deltaomega¦ <= d
EDGE: bpI:p2:newton-error | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-error@L247-L247 | error bounds (c)
EDGE: stepI:p2:st-small | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-error@L247-L247 | hypotheses d<beta and C_sym eps/(gamma delta^{kappa+1}) <= 1/2 of new-error
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-error@L247-L247 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-error@L247-L247 | Uses constants or exponents fixed by this package.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-error@L247-L247 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.step (KAM/Iso/Apost/Step.lean); KAM.Iso.Apost.torsion_step (KAM/Iso/Apost/Torsion.lean)
LEAN_NOTE: Rule 05:10: I2-6-audit-1.md:32-36 maps blueprint L234-238 items (a)-(e) to Step.lean:54-80; parent step PROVED.
NOTE: -

NODE: stepI:p2:st-frame
KIND: step
TITLE: Ball, frame, torsion
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L248-L249
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L248-L249
CONTRACT_ID: stepI:p2:st-frame
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:step, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:step, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: B_{beta-d}(Kbar) in D from perturbation-noA5(a); (d) and (e) are bpI:p2:torsion
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:perturbation-noA5, bpI:p2:torsion, bpI:p2:correction, stepI:p2:st-small, bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:perturbation-noA5 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L249-L249 | (a): the ball
EDGE: bpI:p2:torsion | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L249-L249 | (d),(e)
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L249-L249 | ¦Kbar-K¦ <= d input of the perturbation lemma
EDGE: stepI:p2:st-small | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L249-L249 | d <= beta/2 and the smallness of torsion
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L249-L249 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L249-L249 | Uses constants or exponents fixed by this package.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L249-L249 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.step (KAM/Iso/Apost/Step.lean); KAM.Iso.Apost.torsion_step (KAM/Iso/Apost/Torsion.lean)
LEAN_NOTE: Rule 05:10: I2-6-audit-1.md:32-36 maps blueprint L234-238 items (a)-(e) to Step.lean:54-80; parent step PROVED.
NOTE: -

NODE: bpI:p2:schedule
KIND: definition
TITLE: Schedule
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:schedule@L255-L259
PROOF_SOURCE: -
CONTRACT_ID: bpI:p2:schedule
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<rho_infty<rho; gamma>0; e>=0
SOURCE_QUANTIFIERS: rho, rho_infty, gamma, e fixed; delta_s, r_s, eps_s, d_s defined for s>=0
SOURCE_CONCLUSION: defines delta_s := 2^{-s} delta_0, r_s := rho - 8 delta_0(1-2^{-s}), eps_0 := e, eps_{s+1} := C_E eps_s^2/(gamma^4 delta_s^{2a}), d_s := C_Delta eps_s/(gamma^2 delta_s^a); then r_0 = rho, r_{s+1} = r_s - 4 delta_s, rho_infty <= rho - 8 delta_0 < r_s, delta_s <= 1, 4 delta_s < r_s
CONSTANT_SCOPE: C_E, C_Delta, a, delta_0 from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:schedule@L256-L256 | delta_0, a, C_E, C_Delta
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:schedule@L256-L256 | gamma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2
REVIEWER: sol-review-I-p2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.schedule (KAM/Apost/Schedule.lean); KAM.Iso.Apost.isoEpsSeq, KAM.Iso.Apost.isoDSeq (KAM/Iso/Apost/Defs.lean)
LEAN_NOTE: audit I2-7 PASS WITH NOTES: schedule reused; sequences are definitions (I-D0-2)
NOTE: Candidate edge to K:bp:p2:schedule dropped: '(as K:bp:p2:schedule)' is a comparison; the facts r_{s+1}=r_s-4 delta_s, delta_s<=1, 4 delta_s < r_s are routine algebra of the stated formulas.

NODE: bpI:p2:error-decay
KIND: lemma
TITLE: Decay
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:error-decay@L261-L263
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:error-decay@L264-L266
CONTRACT_ID: bpI:p2:error-decay
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: schedule of bpI:p2:schedule; q := 2^{2a} C_E e/(gamma^4 delta_0^{2a}) <= 1
SOURCE_QUANTIFIERS: rho, rho_infty, gamma, e fixed
SOURCE_CONCLUSION: eps_s <= q^{2^s-1} 2^{-2as} e <= 2^{-2as} e; eps_s/delta_s^j <= e/delta_0^j for 0<=j<=2a; sum_s eps_s/delta_s^j <= 2e/delta_0^j for 0<=j<=2a-1
CONSTANT_SCOPE: C_E, a, delta_0 from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:schedule, bpI:p2:constants, bpI:p2:standing, K:bp:p1:iteration
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:error-decay@L262-L262 | eps_s, delta_s recursion
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:error-decay@L262-L262 | C_E, a, delta_0
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:error-decay@L262-L262 | gamma
EDGE: K:bp:p1:iteration | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:error-decay@L265-L265 | iteration lemma with p = 2a
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.iso_error_decay (KAM/Iso/Apost/Schedule.lean)
LEAN_NOTE: audit I2-7 PASS WITH NOTES: full decay contract, exact design type
NOTE: L265 explicitly supplies the scalar recurrence with Qprime=hatC_E/(gamma^4 delta_0^{2a}) and invokes K:bp:p1:iteration with p=2a; the remaining sums are geometric. The reference to K decay compares the proof and does not import its fixed C_E as an extra theorem hypothesis.

NODE: bpI:p2:iteration
KIND: proposition
TITLE: The induction
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L268-L283
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L284-L292
CONTRACT_ID: bpI:p2:iteration
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p2:standing; K and s=s_0>1 satisfy (I5)-(I12) of I-G1 on T_rho with margin mu: B1; B_mu(K) in D; ¦DK¦<=sigma_K-mu; det G != 0, ¦B¦<=sigma_B-mu; det avg T_H != 0, ¦avg T_H^{-1}¦<=sigma_T-mu; ¦E_{H,K,s omega*}¦<=e, ¦Ebar_H(K)-E_0¦<=e; nu(s_0)>=nu; e<=1; c_* e/(gamma^4 delta_0^{2a}) <= 1
SOURCE_QUANTIFIERS: standing data, constants, schedule fixed; then K, s_0, e; then there are K_j, s_j (K_0 = K) for all j
SOURCE_CONCLUSION: with D_j := sum_{i<j} d_i, for every j: (i) K_j is (r_j,mu-D_j,eps_j,s_j)-admissible, eps_j<=e<=1; (ii) D_j<=mu/4, D_j<=nu/2, ¦K_j-K¦<=D_j on T_{r_j}, ¦s_j-s_0¦¦omega*¦<=D_j, nu(s_j)>=nu-D_j>=nu/2, 1<s_j<sigma_omega; (iii) ¦DK_j¦ <= sigma_K-mu+sum nd_i/delta_i <= sigma_K-mu/2; (iv) ¦B_j¦ <= sigma_B-mu+sum C_B d_i/delta_i <= sigma_B-mu/2; (v) ¦avg T_j^{-1}¦ <= sigma_T-mu+sum 2 m^2 C_DeltaScriptT d_i/delta_i^2 <= sigma_T-mu/2; (vi) ¦K_{j+1}-K_j¦<=d_j, ¦DK_{j+1}-DK_j¦<=nd_j/delta_j on T_{r_{j+1}}, ¦s_{j+1}-s_j¦¦omega*¦<=d_j
CONSTANT_SCOPE: Constants of Definition bpI:p2:constants: all depend only on (n,tau,M,sigma_K,sigma_B,sigma_T); hat-c_* also on (mu,nu); delta_0 on (rho,rho_infty); no dependence on K, s, e, gamma, omega*, sigma_omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible, bpI:p2:schedule, bpI:p2:ray, stepI:p2:it-sums, stepI:p2:it-stepsmall, stepI:p2:it-step
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L269-L269 | standing data
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L271-L271 | c_*, delta_0, a
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L269-L269 | admissibility of K_j
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L275-L275 | r_j, delta_j, eps_j, d_j
EDGE: bpI:p2:ray | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L276-L276 | nu(s_j) and 1<s_j<sigma_omega
EDGE: stepI:p2:it-sums | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L285-L285 | proof step of this result
EDGE: stepI:p2:it-stepsmall | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L288-L288 | proof step of this result
EDGE: stepI:p2:it-step | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L290-L290 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.iteration (KAM/Iso/Apost/Iteration.lean)
LEAN_NOTE: audit I2-8 PASS: all six conclusions
NOTE: -

NODE: stepI:p2:it-sums
KIND: step
TITLE: Summed bounds
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-sums@L285-L287
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-sums@L285-L287
CONTRACT_ID: stepI:p2:it-sums
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:iteration, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:iteration, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: gamma <= Theta; sum_i d_i/delta_i^k <= 2 Theta^2 C_Delta X for k=0,1,2; hence sum d_i <= min{mu/4,nu/2}, sum n d_i/delta_i <= mu/4, sum C_B d_i/delta_i <= mu/4, sum 2 m^2 C_DeltaScriptT d_i/delta_i^2 <= mu/2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:admissible, bpI:p2:error-decay, bpI:p2:schedule, bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-sums@L286-L286 | gamma <= Theta from K admissible (bpI:p2:freq)
EDGE: bpI:p2:error-decay | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-sums@L286-L286 | eps_s/delta_s^j and sum bounds
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-sums@L286-L286 | d_i := C_Delta eps_i/(gamma^2 delta_i^a)
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-sums@L287-L287 | c_* >= 2^{2a}C_E, 2 c_sum/mu, 4 Theta^2 C_Delta/nu; C_B, C_DeltaScriptT
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-sums@L286-L286 | gamma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.iso_sums_le (KAM/Iso/Apost/Iteration.lean)
LEAN_NOTE: audit I2-8 PASS: it-sums sums and five bounds (scalar helper iso_iteration_sums in I2-2)
NOTE: -

NODE: stepI:p2:it-stepsmall
KIND: step
TITLE: Step smallness
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-stepsmall@L288-L289
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-stepsmall@L288-L289
CONTRACT_ID: stepI:p2:it-stepsmall
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:iteration, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:iteration, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: c_step eps_j/(gamma^4 delta_j^{2a}) <= c_step X <= min{1,mu/2} <= min{1,mu-D_j}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p2:it-sums, bpI:p2:error-decay, bpI:p2:schedule, bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p2:it-sums | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-stepsmall@L289-L289 | X <= 1/c_* and D_j <= mu/4
EDGE: bpI:p2:error-decay | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-stepsmall@L289-L289 | eps_j <= e and eps_j/delta_j^{2a} <= e/delta_0^{2a}
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-stepsmall@L289-L289 | eps_j, delta_j
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-stepsmall@L289-L289 | c_step <= c_*
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-stepsmall@L289-L289 | gamma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.iso_stepsmall_seq (KAM/Iso/Apost/Iteration.lean)
LEAN_NOTE: audit I2-8 PASS: every-stage step-smallness bound
NOTE: -

NODE: stepI:p2:it-step
KIND: step
TITLE: Base and induction
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L290-L291
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L290-L291
CONTRACT_ID: stepI:p2:it-step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:iteration, with its definitions and inherited packages. For the induction transition assume (i)-(v) at j, as explicitly stated at L291. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:iteration, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: (i)-(v) at j+1 and (vi) at j: Proposition step applies with (r_j,delta_j,mu-D_j,eps_j,s_j) and yields K_{j+1} := Kbar_j, s_{j+1} := sbar_j; 1<s_{j+1}<sigma_omega and nu(s_{j+1}) >= nu-D_{j+1}; B1-B7 for K_{j+1}; (iii)-(v) with the summed bounds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:step, stepI:p2:it-sums, stepI:p2:it-stepsmall, bpI:p2:ray, bpI:p2:admissible, bpI:p2:schedule, bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:step | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L291-L291 | Proposition step applied at each j
EDGE: stepI:p2:it-sums | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L291-L291 | summed bounds D_{j+1} <= nu/2, mu/4
EDGE: stepI:p2:it-stepsmall | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L291-L291 | smallness hypothesis of the step
EDGE: bpI:p2:ray | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L291-L291 | (b): 1<sbar_j<sigma_omega, nu(sbar_j) >= nu(s_j)-d_j
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L291-L291 | admissibility at j and j+1; B3-B5
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L291-L291 | r_{j+1} = r_j-4 delta_j, d_j
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L291-L291 | c_*, C_B, C_DeltaScriptT
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L291-L291 | standing data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-d
REVIEWER: sol-delta-I-f
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.iso_stage_succ, KAM.Iso.Apost.iso_ray_step (KAM/Iso/Apost/Iteration.lean)
LEAN_NOTE: audit I2-8 PASS: induction step and ray step
NOTE: -

NODE: bpI:p2:limit
KIND: proposition
TITLE: The limit
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L294-L304
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L305-L314
CONTRACT_ID: bpI:p2:limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting of bpI:p2:iteration; K_infty := lim K_j on T_{rho_infty}, K_infty := K elsewhere; s_infty := lim s_j
SOURCE_QUANTIFIERS: as in bpI:p2:iteration; then K_infty, s_infty
SOURCE_CONCLUSION: (a) limits exist; K_j -> K_infty and DK_j -> DK_infty uniformly on T_{rho_infty}; K_infty holomorphic, primary, real on reals; (b) ¦K_infty-K¦ <= 2 C_Delta e/(gamma^2 delta_0^a) <= mu/4 and ¦s_infty omega*-s_0 omega*¦ <= 2 C_Delta e/(gamma^2 delta_0^a) <= nu/2; (c) 1<s_infty<sigma_omega (nu(s_infty)>=nu/2); (d) B_{mu/2}(K_infty(theta)) in D and ¦DK_infty¦ <= sigma_K-mu/2 on T_{rho_infty}; (e) E_{H,K_infty,s_infty omega*} = 0 on T_{rho_infty}
CONSTANT_SCOPE: Constants of Definition bpI:p2:constants: all depend only on (n,tau,M,sigma_K,sigma_B,sigma_T); hat-c_* also on (mu,nu); delta_0 on (rho,rho_infty); no dependence on K, s, e, gamma, omega*, sigma_omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:iteration, bpI:p2:standing, bpI:p2:constants, stepI:p2:lim-conv, stepI:p2:lim-close, stepI:p2:lim-margins, stepI:p2:lim-inv, bpI:p2:admissible, bpI:p2:schedule
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:iteration | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L295-L295 | the sequence (K_j,s_j) and (i)-(vi)
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L295-L295 | standing data
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L298-L298 | C_Delta, delta_0, a
EDGE: stepI:p2:lim-conv | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L306-L306 | proof step of this result
EDGE: stepI:p2:lim-close | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L308-L308 | proof step of this result
EDGE: stepI:p2:lim-margins | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L310-L310 | proof step of this result
EDGE: stepI:p2:lim-inv | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L312-L312 | proof step of this result
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L295-L295 | The setting of iteration includes admissibility and its scheduled sequences.
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L295-L295 | The setting of iteration includes admissibility and its scheduled sequences.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: isoLimit, isoSLimit, limit, isoLimit_eq, isoLimit_of_not_mem, isoLimit_tendsto, isoSLimit_tendsto, isoLimit_eq_iff, isoSLimit_eq_iff (KAM/Iso/Apost/Limit.lean)
LEAN_NOTE: audit I2-9 PASS WITH NOTES (selectors with convergence and uniqueness; I-G1 itself separate)
NOTE: -

NODE: stepI:p2:lim-conv
KIND: step
TITLE: Convergence
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L306-L307
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L306-L307
CONTRACT_ID: stepI:p2:lim-conv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:limit, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:limit, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: sum d_j <= 2 C_Delta e/(gamma^2 delta_0^a) and sum n d_j/delta_j <= 2n C_Delta e/(gamma^2 delta_0^{a+1}) converge; K_j, DK_j uniformly Cauchy, (s_j) Cauchy (omega* != 0); uniform limits give holomorphy, primary, real on reals and DK_infty = lim DK_j: (a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:error-decay, K:bp:p1:uniform-limits, bpI:p2:iteration, bpI:p2:schedule, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:error-decay | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L307-L307 | convergence of the sums sum d_j and sum nd_j/delta_j
EDGE: K:bp:p1:uniform-limits | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L307-L307 | holomorphy, primary, real and DK_infty = lim DK_j
EDGE: bpI:p2:iteration | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L307-L307 | (vi) increments bounds
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L307-L307 | T_{rho_infty} in T_{r_j}: rho_infty < r_j
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L307-L307 | C_Delta, delta_0
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L307-L307 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L307-L307 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: isoLimit_eq_of_tendsto, isoSLimit_eq_of_tendsto, isoDSeq_summable_tsum_le, isoDSeq_div_summable, exists_tendsto_of_dist_ray, tendsto_isoSLimit, isoLimit_tendsto, isoSLimit_tendsto (KAM/Iso/Apost/Limit.lean)
LEAN_NOTE: audit I2-9 PASS WITH NOTES; rows lim-conv
NOTE: -

NODE: stepI:p2:lim-close
KIND: step
TITLE: Closeness and frequency
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L308-L309
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L308-L309
CONTRACT_ID: stepI:p2:lim-close
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:limit, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:limit, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: ¦K_infty-K¦ <= sup D_j and ¦s_infty-s_0¦¦omega*¦ <= sup D_j <= min{mu/4,nu/2}: (b); nu(s_infty) >= nu/2 > 0: (c)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p2:it-sums, bpI:p2:iteration, bpI:p2:ray, stepI:p2:lim-conv, bpI:p2:standing, bpI:p2:constants, bpI:p2:schedule
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p2:it-sums | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L309-L309 | sup_j D_j <= min{mu/4,nu/2}
EDGE: bpI:p2:iteration | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L309-L309 | (ii): ¦K_j-K¦ <= D_j, nu(s_j) >= nu-D_j
EDGE: bpI:p2:ray | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L309-L309 | nu(.) of ray (b): continuity of nu(s)
EDGE: stepI:p2:lim-conv | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L309-L309 | existence of the limits K_infty, s_infty
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L309-L309 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L309-L309 | Uses constants or exponents fixed by this package.
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L309-L309 | Uses the scheduled eps_j,delta_j,d_j or their partial sums.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.limit (KAM/Iso/Apost/Limit.lean)
LEAN_NOTE: Rule 05:10: I2-9-audit-1.md:61 and narrative on Limit.lean:408-428 (ray displacement, nu/2 margin, derivative and ball estimates); parent limit PROVED. (c) via ray Lipschitz at s_inf, same conclusion.
NOTE: -

NODE: stepI:p2:lim-margins
KIND: step
TITLE: Margins
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-margins@L310-L311
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-margins@L310-L311
CONTRACT_ID: stepI:p2:lim-margins
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:limit, with its definitions and inherited packages. For the ball inclusion take theta in T_{rho_infty} and ¦z-K_infty(theta)¦<mu/2. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:limit, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: z in D (¦z-K(theta)¦<3mu/4 and B_mu(K) in D); ¦DK_infty¦ = lim ¦DK_j¦ <= sigma_K-mu/2: (d)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:iteration, stepI:p2:lim-close, stepI:p2:lim-conv, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:iteration | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-margins@L311-L311 | B_mu(K) in D (I6) and (iii)
EDGE: stepI:p2:lim-close | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-margins@L311-L311 | ¦K_infty-K¦ <= mu/4
EDGE: stepI:p2:lim-conv | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-margins@L311-L311 | DK_infty = lim DK_j
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-margins@L311-L311 | D
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-margins@L311-L311 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.limit (KAM/Iso/Apost/Limit.lean)
LEAN_NOTE: Rule 05:10: I2-9-audit-1.md:61 and narrative on Limit.lean:408-428 (ray displacement, nu/2 margin, derivative and ball estimates); parent limit PROVED. (c) via ray Lipschitz at s_inf, same conclusion.
NOTE: -

NODE: stepI:p2:lim-inv
KIND: step
TITLE: Invariance
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L312-L313
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L312-L313
CONTRACT_ID: stepI:p2:lim-inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:limit, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:limit, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: E_j(theta) = X_H(K_j(theta)) - DK_j(theta) s_j omega* -> E_{H,K_infty,s_infty omega*}(theta) and ¦E_j¦ -> 0, so E_{H,K_infty,s_infty omega*} = 0 on T_{rho_infty}: (e)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:iteration, bpI:p2:error-decay, stepI:p2:lim-conv, stepI:p2:lim-margins, bpI:p2:standing, bpI:p0:stripdata#invarianceError, bpI:p2:admissible, bpI:p2:constants, bpI:p2:schedule
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:iteration | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | B6: ¦E_j¦ <= eps_j
EDGE: bpI:p2:error-decay | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | eps_j <= 2^{-2aj} e
EDGE: stepI:p2:lim-conv | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | K_j -> K_infty, DK_j -> DK_infty, s_j -> s_infty
EDGE: stepI:p2:lim-margins | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | K_infty(theta) in D
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | X_H continuous on D
EDGE: bpI:p0:stripdata#invarianceError | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | E_{H,K,omega} = X_H(K) - DK omega
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | Uses B-component premises or frequency bound in the inherited admissible context.
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | Uses constants or exponents fixed by this package.
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | Uses the scheduled eps_j,delta_j,d_j or their partial sums.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: isoEpsSeq_tendsto_zero, lim_invariance_moving (KAM/Iso/Apost/Limit.lean)
LEAN_NOTE: audit I2-9 PASS WITH NOTES; rows lim-inv
NOTE: -

NODE: bpI:p2:energy-limit
KIND: lemma
TITLE: Passage of the energy average to the limit
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:energy-limit@L316-L318
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:energy-limit@L319-L324
CONTRACT_ID: bpI:p2:energy-limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting of bpI:p2:limit
SOURCE_QUANTIFIERS: as in bpI:p2:limit
SOURCE_CONCLUSION: Ebar_H(K_infty) = E_0 and Ebar_H(K_j) -> Ebar_H(K_infty)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:limit, bpI:p2:standing, bpI:p0:extended#energyAverage, stepI:p2:el-unif, stepI:p2:el-int
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:limit | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:energy-limit@L317-L317 | the setting and K_j -> K_infty
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:energy-limit@L317-L317 | H, E_0
EDGE: bpI:p0:extended#energyAverage | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:energy-limit@L317-L317 | Ebar_H
EDGE: stepI:p2:el-unif | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:energy-limit@L320-L320 | proof step of this result
EDGE: stepI:p2:el-int | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:energy-limit@L322-L322 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2
REVIEWER: sol-review-I-p2
LEAN_STATUS: PROVED
LEAN_REF: energy_limit, tendsto_energyAverage_of_uniform (KAM/Iso/Apost/Limit.lean)
LEAN_NOTE: audit I2-9 PASS WITH NOTES
NOTE: -

NODE: stepI:p2:el-unif
KIND: step
TITLE: Uniform convergence of $H\circ K_j$ on $\R^n$
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-unif@L320-L321
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-unif@L320-L321
CONTRACT_ID: stepI:p2:el-unif
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:energy-limit, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:energy-limit, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: ¦H(K_j)-H(K_infty)¦ <= M¦K_j-K_infty¦ -> 0 uniformly on R^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:increments-open, bpI:p2:limit, bpI:p2:iteration, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:increments-open | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-unif@L321-L321 | F = H, ¦DH¦ <= M
EDGE: bpI:p2:limit | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-unif@L321-L321 | (b): ¦K_infty-K¦ <= mu/4 and uniform convergence
EDGE: bpI:p2:iteration | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-unif@L321-L321 | ¦K_j-K¦ <= D_j <= mu/4 and B_mu(K) in D
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-unif@L321-L321 | ¦DH¦ <= M on D
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-unif@L321-L321 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: tendsto_energyAverage_of_uniform (KAM/Iso/Apost/Limit.lean)
LEAN_NOTE: audit I2-9 PASS WITH NOTES; row el-unif / el-int
NOTE: -

NODE: stepI:p2:el-int
KIND: step
TITLE: Integrals
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L322-L323
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L322-L323
CONTRACT_ID: stepI:p2:el-int
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:energy-limit, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:energy-limit, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: H o K_infty integrable on [0,1]^n; ¦Ebar_H(K_j)-Ebar_H(K_infty)¦ <= sup ¦H(K_j)-H(K_infty)¦ -> 0; hence Ebar_H(K_infty) = E_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:ext-integral, stepI:p2:el-unif, bpI:p2:limit, bpI:p2:iteration, bpI:p2:error-decay, bpI:p2:standing, bpI:p0:extended#energyAverage, bpI:p2:admissible, bpI:p2:schedule
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:ext-integral | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | integrability of the continuous periodic H o K_infty
EDGE: stepI:p2:el-unif | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | uniform convergence of H o K_j
EDGE: bpI:p2:limit | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | K_infty continuous, primary
EDGE: bpI:p2:iteration | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | B7: ¦Ebar_H(K_j)-E_0¦ <= eps_j
EDGE: bpI:p2:error-decay | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | eps_j -> 0
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | H periodic in theta
EDGE: bpI:p0:extended#energyAverage | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | Ebar_H
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | Uses B-component premises or frequency bound in the inherited admissible context.
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | Uses the scheduled eps_j,delta_j,d_j or their partial sums.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: tendsto_energyAverage_of_uniform (KAM/Iso/Apost/Limit.lean)
LEAN_NOTE: audit I2-9 PASS WITH NOTES; row el-unif / el-int
NOTE: -

NODE: bpI:p2:g1
KIND: theorem
TITLE: I-G1 with explicit constants
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L329-L337
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L338-L355
CONTRACT_ID: bpI:p2:g1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=2, tau>=n-1, 0<rho_infty<rho; M,sigma_K,sigma_B,sigma_T,mu,gammabar>0; sigma_omega>1; nu>0; omega* in R^n minus {0} (the data of I-G1 fixed); Definition bpI:p2:constants; for the inner statement D,H,K,s,gamma,e,E_0 satisfying (I1)-(I13) of I-G1
SOURCE_QUANTIFIERS: n, tau, rho, rho_infty, M, sigma_K, sigma_B, sigma_T, mu, gammabar, sigma_omega, nu, omega* fixed; then C_1, C_2, C_3 > 0; then for all D, H, K, s, gamma, e, E_0 satisfying (I1)-(I13): (O1)-(O6)
SOURCE_CONCLUSION: with C_1 := rho^{4 tau} max{gammabar^4, c_* delta_0^{-2a}}, C_2 = C_3 := 2 C_Delta rho^{2 tau} delta_0^{-a}: C_1,C_2,C_3>0 and the conclusions (O1)-(O6) of I-G1 hold
CONSTANT_SCOPE: C_1,C_2,C_3 depend only on (n,tau,rho,rho_infty,M,sigma_K,sigma_B,sigma_T,mu,gammabar,nu); fixed before D,H,K,s,gamma,e,E_0; do not use omega*, sigma_omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:constants, bpI:p2:standing, stepI:p2:g1-constants, stepI:p2:g1-standing, stepI:p2:g1-e, stepI:p2:g1-dict, stepI:p2:g1-apply, stepI:p2:g1-o, stepI:p2:g1-o2, stepI:p2:g1-o3
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L330-L330 | C_1,C_2,C_3 defined from C_Delta, c_*, delta_0, a
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L334-L334 | (I1)-(I4), E_0, gamma, omega* in Dio
EDGE: stepI:p2:g1-constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L339-L339 | proof step of this result
EDGE: stepI:p2:g1-standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L341-L341 | proof step of this result
EDGE: stepI:p2:g1-e | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L343-L343 | proof step of this result
EDGE: stepI:p2:g1-dict | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L345-L345 | proof step of this result
EDGE: stepI:p2:g1-apply | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L347-L347 | proof step of this result
EDGE: stepI:p2:g1-o | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L349-L349 | proof step of this result
EDGE: stepI:p2:g1-o2 | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L351-L351 | proof step of this result
EDGE: stepI:p2:g1-o3 | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L353-L353 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2
REVIEWER: sol-review-I-p2
LEAN_STATUS: PROVED
LEAN_REF: g1_explicit (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES (explicit-constant I-G1 body; frozen anchor sealed separately)
NOTE: -

NODE: stepI:p2:g1-constants
KIND: step
TITLE: The constants
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-constants@L339-L340
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-constants@L339-L340
CONTRACT_ID: stepI:p2:g1-constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Only the fixed outer I-G1 data n,tau,rho,rho_infty,M,sigma_K,sigma_B,sigma_T,mu,gammabar,sigma_omega,nu,omega* with their stated guards. C_1,C_2,C_3 are the displayed choices; finiteness and positivity follow from their definitions.
SOURCE_QUANTIFIERS: Fix the outer data first; construct C_1,C_2,C_3 from the displayed formulas, independently of omega*,sigma_omega; only afterward quantify D,H,K,s,gamma,e,E_0 in the theorem. No inner datum is assumed here.
SOURCE_CONCLUSION: C_1 >= rho^{4tau} gammabar^4 > 0 and C_2 > 0; their dependence is read off the definitions (rho^{4tau}, rho^{2tau} real powers of a positive number)
CONSTANT_SCOPE: C_1,C_2,C_3 depend only on (n,tau,rho,rho_infty,M,sigma_K,sigma_B,sigma_T,mu,gammabar,nu)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-constants@L340-L340 | finiteness, positivity and dependence of all constants
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-constants@L340-L340 | n, tau, M, sigma's, nu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: isoC1_pos, isoC2_pos (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES
NOTE: -

NODE: stepI:p2:g1-standing
KIND: step
TITLE: Standing data
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-standing@L341-L342
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-standing@L341-L342
CONTRACT_ID: stepI:p2:g1-standing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (I1)-(I4), E_0 in R, gamma>0, omega* in Dio_{gamma,tau} (I10)
SOURCE_QUANTIFIERS: data and D,H,E_0,gamma fixed
SOURCE_CONCLUSION: (I1)-(I4), E_0 in R, gamma>0 and omega* in Dio_{gamma,tau} from (I10), together with the fixed outer data, are exactly bpI:p2:standing.
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-standing@L342-L342 | the stated hypotheses are exactly the standing data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: g1_explicit (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES; IsoStanding construction inside g1_explicit (G1:106-124)
NOTE: -

NODE: stepI:p2:g1-e
KIND: step
TITLE: Size of the errors
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-e@L343-L344
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-e@L343-L344
CONTRACT_ID: stepI:p2:g1-e
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:g1, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:g1, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: e < gamma^4/gammabar^4 <= 1, and c_* e/(gamma^4 delta_0^{2a}) < 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p2:g1-constants, bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p2:g1-constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-e@L344-L344 | C_1 >= rho^{4tau} gammabar^4 and C_1 >= rho^{4tau}c_* delta_0^{-2a}
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-e@L344-L344 | c_*, delta_0, a
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-e@L344-L344 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: iso_g1_error_small (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES
NOTE: -

NODE: stepI:p2:g1-dict
KIND: step
TITLE: Dictionary for the hypotheses
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-dict@L345-L346
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-dict@L345-L346
CONTRACT_ID: stepI:p2:g1-dict
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:g1, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:g1, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: (I5): B1; (I6): B_mu(K) in D, ¦DK¦<=sigma_K-mu; (I7): det G != 0, ¦B¦<=sigma_B-mu; (I8): det avg T_H != 0, ¦avg T_H^{-1}¦ <= sigma_T-mu (average defined by extended-basic); (I9): s>1 and nu(s)>=nu; (I11)=B6, (I12)=B7; s>1 gives s omega* in Dio_{gamma,tau}; so K is (rho,mu,e,s)-admissible with the sharper constants
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:admissible, bpI:p1:extended-basic, bpI:p2:ray, stepI:p2:g1-e, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-dict@L346-L346 | identification of (I5)-(I12) with B1-B7 (sharper constants)
EDGE: bpI:p1:extended-basic | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-dict@L346-L346 | the average avg T_H is defined
EDGE: bpI:p2:ray | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-dict@L346-L346 | s>1 gives s omega* in Dio_{gamma,tau}
EDGE: stepI:p2:g1-e | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-dict@L346-L346 | e<=1 so that eps = e is in the admissible range 0<=eps<=1 (prose L114-115)
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-dict@L346-L346 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: norm_le_of_rowSum_le_of_nonempty, margin_of_le, g1_explicit (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES; dictionary G1:128-146
NOTE: Preextract candidate edge to bpI:p0:totality dropped (administrative pointer, deleted in I-p0; the remark (T2) is a Lean-totality note, not a consumed fact).

NODE: stepI:p2:g1-apply
KIND: step
TITLE: Iteration and limit
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L347-L348
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L347-L348
CONTRACT_ID: stepI:p2:g1-apply
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:g1, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:g1, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: Propositions bpI:p2:iteration and bpI:p2:limit apply and give K_infty, s_infty
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:iteration, bpI:p2:limit, stepI:p2:g1-dict, stepI:p2:g1-e, stepI:p2:g1-standing, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:iteration | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L348-L348 | proposition applied
EDGE: bpI:p2:limit | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L348-L348 | proposition applied
EDGE: stepI:p2:g1-dict | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L348-L348 | supplies the admissibility hypotheses (I5)-(I12)
EDGE: stepI:p2:g1-e | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L348-L348 | e<=1 and c_* e/(gamma^4 delta_0^{2a}) <= 1
EDGE: stepI:p2:g1-standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L348-L348 | standing data holds
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L348-L348 | constants
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L348-L348 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L348-L348 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: g1_explicit (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES; applies Apost.limit, G1:147-149
NOTE: -

NODE: stepI:p2:g1-o
KIND: step
TITLE: (O1), (O4)--(O6)
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o@L349-L350
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o@L349-L350
CONTRACT_ID: stepI:p2:g1-o
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:g1, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:g1, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: (O1) is limit (a); (O4) is limit (d); (O5) ¦K_infty-K¦ <= 2 C_Delta e/(gamma^2 delta_0^a) = C_2 e/(gamma^2 rho^{2tau}) on T_{rho_infty}; (O6) ¦s_infty omega*-s omega*¦ <= C_3 e/(gamma^2 rho^{2tau}); 1<s_infty<sigma_omega by (c)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:limit, stepI:p2:g1-apply, stepI:p2:g1-constants, bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:limit | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o@L350-L350 | (a),(b),(c),(d)
EDGE: stepI:p2:g1-apply | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o@L350-L350 | limit applied
EDGE: stepI:p2:g1-constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o@L350-L350 | C_2,C_3 definitions/positivity
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o@L350-L350 | C_Delta, delta_0, a
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o@L350-L350 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: g1_explicit (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES; G1:156-164
NOTE: -

NODE: stepI:p2:g1-o2
KIND: step
TITLE: (O2)
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o2@L351-L352
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o2@L351-L352
CONTRACT_ID: stepI:p2:g1-o2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:g1, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:g1, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: (O2): E_{H,K_infty,s_infty omega*} = 0 on T_{rho_infty}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:limit, stepI:p2:g1-apply, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:limit | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o2@L352-L352 | (e)
EDGE: stepI:p2:g1-apply | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o2@L352-L352 | limit applied
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o2@L352-L352 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: g1_explicit (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES; G1:147-149,161
NOTE: -

NODE: stepI:p2:g1-o3
KIND: step
TITLE: (O3)
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L353-L354
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L353-L354
CONTRACT_ID: stepI:p2:g1-o3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:g1, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:g1, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: Assumption bpI:p1:setting holds with r = rho_infty, omega = s_infty omega*; by energy-conservation (b), H(K_infty(theta)) = E_0 for all theta in T_{rho_infty} (pointwise); no frame or Gram determinant of K_infty is used
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, bpI:p2:energy-limit, bpI:p1:energy-conservation, bpI:p2:limit, stepI:p2:g1-o2, stepI:p2:g1-apply, bpI:p2:ray, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L354-L354 | Assumption bpI:p1:setting holds with r = rho_infty, omega = s_infty omega*
EDGE: bpI:p2:energy-limit | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L354-L354 | Ebar_H(K_infty) = E_0
EDGE: bpI:p1:energy-conservation | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L354-L354 | (b): H(K_infty) = E_0 pointwise
EDGE: bpI:p2:limit | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L354-L354 | K_infty regularity, (d) and (e)
EDGE: stepI:p2:g1-o2 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L354-L354 | (O2): E = 0
EDGE: stepI:p2:g1-apply | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L354-L354 | limit applied
EDGE: bpI:p2:ray | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L354-L354 | s_infty omega* in Dio_{gamma,tau} since s_infty>1
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L354-L354 | E_0, D, H
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: g1_explicit (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES; G1:151-155,161
NOTE: Preextract candidate edge to bpI:p1:o3 dropped (deleted administrative remark; the used fact is carried by bpI:p1:energy-conservation).
