NODE: N:bpN:p11:nonresonant
KIND: external
TITLE: [N] Nonresonant stability in the extended phase space (KAM.Nekhoroshev.nonresonant)
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L65-L68
PROOF_SOURCE: -
CONTRACT_ID: N:bpN:p11:nonresonant
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r,s,K_a,alpha>0, L>=0, p>1, q=p/(p-1), kappa=2 pi K_a s>=6; r=r_B; h holomorphic on V_r(I_c), real on real points; ¦k.omega(I_c)¦>=alpha for 0<¦k¦_1<=K_a (cond-nr, Lambda={0}), cond-L with L, K_a L r<=alpha/p; (SL); f in O(r,s)^{e,R}, ¦f¦<=eps with eps>0, eps<=alpha r/(2^7 q K_a); H=h+f; T_nr=(s r/(5 eps))e^{kappa/6}
SOURCE_QUANTIFIERS: r,s,K_a,alpha,L,p; h; f; eps; F; J; y; t_1
SOURCE_CONCLUSION: for every F with F=X^c_{H^R} on W^e_r, J containing 0, y with y'=F(y) on J, y(0)=(theta_0,I_c,x-tilde_0), x-tilde_0 in S-tilde, and t_1 in J with ¦t_1¦<=T_nr and x-tilde(u) in S-tilde between 0 and t_1: ¦I(u)-I_c¦<=r/2 between 0 and t_1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-N graph, node bpN:p11:nonresonant (there KIND proposition, contract bpN:p11:nonresonant v1); Lean theorem KAM.Nekhoroshev.nonresonant cited by MAIN L433 (never read here)
