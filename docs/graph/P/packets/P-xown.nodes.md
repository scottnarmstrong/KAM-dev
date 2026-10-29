NODE: bpN:p6:iterative-special
KIND: lemma
TITLE: Special cases for track P
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative-special@L140-L144
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative-special@L140-L144
CONTRACT_ID: bpN:p6:iterative-special
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source hypotheses and data of N iterative, including its original nonresonance/Lipschitz hypotheses, p>1, 1/p+1/q=1 and smallness u=q delta/(alpha-bar rho sigma)<=1/4; (1) g=0; (2) Lambda={0}; the numbered cases are separate specializations
SOURCE_QUANTIFIERS: the data (n,r,s,rho,sigma,K,alpha,L,p), then f and the normal-form data as in N iterative
SOURCE_CONCLUSION: (1) for g=0, ¦g¦_*=0 and ¦f_+¦<=(1-2q delta/(alpha-bar rho sigma))^{-1}(2q delta/(e alpha-bar rho sigma)+exp(-2pi K sigma)) delta; (2) for Lambda={0}, P_Lambda T_K f=f^_0=avg f, cond-nr is ¦k.omega(I)¦>=alpha for 0<¦k¦_1<=K, and the transformed Hamiltonian is h+g+avg f+f_+; (3) no constant depends on f or H beyond delta and ¦g¦_*, with the data and smallness dependence stated at L144
CONSTANT_SCOPE: as stated in (3): data (n,r,s,rho,sigma,K,alpha,L,p); f and H enter only through delta and ¦g¦_*
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p6:iterative, N:bpN:p6:setting, N:bpN:p4:projections, N:bpN:p4:norm
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p6:iterative | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative-special@L140-L144 | specialize (d) and the transformed Hamiltonian
EDGE: N:bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative-special@L140-L144 | original N hypotheses, alpha-bar and ¦g¦_*
EDGE: N:bpN:p4:projections | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative-special@L140-L144 | P_Lambda T_K f=f^_0 for Lambda={0}
EDGE: N:bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative-special@L140-L144 | weighted remainder norm and Fourier coefficients
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-P-d
REVIEWER: sol-review-P-p
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: P-OWNED: N excludes this remark from its own root closure; P consumes its first-step and averaging facts through p2:direct. Source remains the N blueprint; do not label it an N import.

NODE: bpI:p7:scaling
KIND: proposition
TITLE: Scaling to a general Kepler strength
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:scaling@L311-L318
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:scaling@L319-L322
CONTRACT_ID: bpI:p7:scaling
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: k>0; E_k(q,p)=¦p¦^2/2-k/¦q¦ and S_k(Q,P)=(Q/k,kP); for the dynamical claims (Q,P)(tau) solves Hamilton equations of E_1; mean-anomaly averages as in Proposition means; mass dictionary: body of mass m>0 in the field of a centre of strength k=G m_0 with H(q,p)=¦p¦^2/(2m)-km/¦q¦
SOURCE_QUANTIFIERS: k>0 then (Q,P) a solution (or Kepler orbit with semi-major axis a); m>0 and k=G m_0 for the mass dictionary
SOURCE_CONCLUSION: S_k is linear and symplectic (DS_k^T J DS_k=J), E_k o S_k=k^2 E_1, (q,p)(t)=S_k(Q,P)(k^2 t) solves Hamilton equations of E_k, semi-major axis a_k=a/k, averages <1/¦q¦_2>=1/a_k, <¦p¦_2^2>=k/a_k, E_k=-k/(2a_k); mass dictionary: H=m E_k(q,p/m), v=p/m obeys qdot=v, vdot=-kq/¦q¦^3, orbit and elements a_k,e are those of E_k, Gamma_mass=m Gamma(q,v), L_mass=m sqrt(k a_k), <¦p¦^2>=m^2 k/a_k, <1/¦q¦>=1/a_k
CONSTANT_SCOPE: none (k and m are the data; no dependence on any other constant)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:means, stepI:p7:sc-alg, stepI:p7:sc-flow
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:means | blueprint-I/parts/p7-delaunay.tex#bpI:p7:scaling@L320-L321 | averages 1/¦Q¦ and ¦P¦^2 over the mean anomaly equal 1/a and 1/a, giving the scaled averages and E_k
EDGE: stepI:p7:sc-alg | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sc-alg@L320-L320 | local energy and symplectic block calculation
EDGE: stepI:p7:sc-flow | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sc-flow@L321-L321 | local field transport, time rescaling and averages
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: writer-xown-sonnet+sol-review-P-p
REVIEWER: sol-delta-P-p
LEAN_STATUS: PROVED
LEAN_REF: scaleMK_energy, scaleMK_symplectic, scaleMK_cross (KAM/Kepler/Energy.lean); energyMK_eq_mul_energy, scaleMK_hamiltonianVectorField, scaleMK_flow, delaunayMK_means (KAM/Kepler/Mass.lean)
LEAN_NOTE: audit KEP-1 PASS (addendum) + KEP-10 PASS WITH NOTES; steps sc-* not named, left
NOTE: P-OWNED: I excludes this proposition from its own root closure; P consumes it at bpP:p6:kepler-part, stepP:p7:rg-scale and (via bpI:p7:circular) Part 7. Source remains the I blueprint. Proof step sc-alg cites Lemma bpI:p6:conversion(a) and step sc-flow cites Step stepI:p7:sy-field (naturality of Hamiltonian fields) only as "as in" pointers to the same one-line algebra, so no edges are recorded; both are nodes of the published I graph, if the reviewer wants them as imports.

NODE: bpI:p7:means
KIND: proposition
TITLE: Mean values
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:means@L290-L296
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:means@L297-L301
CONTRACT_ID: bpI:p7:means
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (L,G) in C_0, g in R, e=e(L,G), a=L^2, (q,p)=Q(ell,g,L,G) (Delaunay map of Definition orbit-maps), r=¦q¦_2
SOURCE_QUANTIFIERS: (L,G) in C_0 and g in R, then the mean anomaly ell in [0,2pi]
SOURCE_CONCLUSION: (1/2pi) int_0^{2pi} dell/r = 1/a; (1/2pi) int_0^{2pi} ¦p¦_2^2 dell = 1/a (virial); (1/2pi) int_0^{2pi} r dell = a(1+e^2/2)
CONSTANT_SCOPE: none (a=L^2 and e=e(L,G) are determined by (L,G))
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: I:bpI:p7:kepler-eq, I:bpI:p7:orbit-identities, I:bpI:p7:orbit-maps, bpI:p7:x-change, stepI:p7:mv-cv, stepI:p7:mv-int
ROUTES: -
ROUTE_FOR: -
EDGE: I:bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#bpI:p7:means@L298-L298 | ell -> u=u_R(ell,e) increasing C^1 with u(0)=0, u(2pi)=2pi and dell=D du (parts (b),(c))
EDGE: I:bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#bpI:p7:means@L299-L300 | r=aD (part a) and E=-1/(2a) (part c) used for the three integrals and the virial identity
EDGE: I:bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#bpI:p7:means@L291-L291 | the statement and proof use the defined Delaunay orbit map and its quantities
EDGE: bpI:p7:x-change | blueprint-I/parts/p7-delaunay.tex#stepI:p7:mv-cv@L298-L298 | change of variables with the increasing C1 Kepler anomaly map; the proof uses continuous integrands
EDGE: stepI:p7:mv-cv | blueprint-I/parts/p7-delaunay.tex#stepI:p7:mv-cv@L298-L298 | the labelled change-of-variable proof step
EDGE: stepI:p7:mv-int | blueprint-I/parts/p7-delaunay.tex#stepI:p7:mv-int@L300-L300 | the labelled three-integral and virial computation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: writer-xown-sonnet+sol-review-P-p
REVIEWER: sol-delta-P-p
LEAN_STATUS: PROVED
LEAN_REF: orbitMapR_mean_inv_radius, orbitMapR_mean_speed_sq, orbitMapR_mean_radius, integral_comp_eccAnom (KAM/Kepler/Means.lean)
LEAN_NOTE: audit KEP-8 PASS WITH NOTES
NOTE: P-OWNED: I excludes this proposition from its own root closure; P consumes it via circular, stepP:p7:ke-c and scaling. Source remains the I blueprint; not an I import. The P-owned external x-change supplies mv-cv; the labelled proof steps and direct orbit-map definition are explicitly attached. The averages are over one 2pi mean-anomaly period.

NODE: bpI:p7:circular
KIND: corollary
TITLE: Circular endpoint
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:circular@L303-L306
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:circular@L307-L309
CONTRACT_ID: bpI:p7:circular
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: real arguments L>0, 0<=e<1, k=sqrt(1-e^2), G=Lk, u=u_R(ell,e); Delaunay data as in Definition orbit-maps
SOURCE_QUANTIFIERS: L>0 and 0<=e<1 (including e=0), ell and g real
SOURCE_CONCLUSION: the endpoint formulas (a),(b) of orbit-identities, the scalar identities E=-1/(2L^2) and Gamma=G of its part (c), the mean values of means (with the scaling and mass dictionary of scaling) hold for 0<=e<1, in particular for circular orbits e=0 (u=ell, r=L^2, ¦p¦=1/L, E=-1/(2L^2), Gamma=L); not claimed for e=0: membership in the strictly noncircular region C, the Delaunay-elements definition on C, and the chart statements of Theorem chart (these remain for 0<e<1 only)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: I:bpI:p7:orbit-identities, I:bpI:p7:kepler-eq, bpI:p7:means, bpI:p7:scaling, I:bpI:p7:orbit-maps, stepI:p7:ci-alg
ROUTES: -
ROUTE_FOR: -
EDGE: I:bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#bpI:p7:circular@L308-L308 | same algebra as steps oi-r..oi-en with e>=0: endpoint formulas (a),(b) and scalar energy and Gamma identities of (c)
EDGE: I:bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#bpI:p7:circular@L308-L308 | u=u_R(ell,e) defined for ¦e¦<1 (part (c))
EDGE: bpI:p7:means | blueprint-I/parts/p7-delaunay.tex#bpI:p7:circular@L308-L308 | steps mv-cv..mv-int use only c^2+s^2=1, k^2=1-e^2, D>=1-e>0, so the mean values hold for e>=0
EDGE: bpI:p7:scaling | blueprint-I/parts/p7-delaunay.tex#bpI:p7:circular@L304-L304 | the scaling and mass dictionary of the statement is stated as holding for 0<=e<1 (proof does not otherwise re-derive it)
EDGE: I:bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#bpI:p7:circular@L304-L304 | the endpoint uses Q_el with independent eccentricity and G=L sqrt(1-e^2)
EDGE: stepI:p7:ci-alg | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ci-alg@L308-L308 | the labelled algebraic extension to e=0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: writer-xown-sonnet+sol-review-P-p
REVIEWER: sol-delta-P-p
LEAN_STATUS: PROVED
LEAN_REF: orbitMapR_mean_inv_radius, orbitMapR_mean_speed_sq, orbitMapR_mean_radius (KAM/Kepler/Means.lean); orbitMapR_radius, orbitMapR_cross, orbitMapR_energy, orbitMapR_speed_sq (KAM/Kepler/Orbit.lean); delaunayMK_means (KAM/Kepler/Mass.lean)
LEAN_NOTE: composite of audits KEP-5 PASS (addendum; e=0 endpoint formulas) + KEP-8 PASS WITH NOTES (means at e=0) + KEP-10 PASS WITH NOTES (mass dictionary means); step ci-alg not named, left
NOTE: P-OWNED: I excludes this corollary from its own root closure; P consumes it at bpP:p7:kepler, stepP:p7:ke-c and stepP:p7:po-el. Source remains the I blueprint. The proof is the single labelled step ci-alg (same algebra, no e>0), explicitly linked below this corollary.

NODE: bpI:p7:x-change
KIND: external
TITLE: Change of variables in R
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:x-change@L41-L41
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:x-change
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u:[a,b] -> R is C1 and increasing; phi is the integrand of the source formula (no regularity class is explicitly specified there)
SOURCE_QUANTIFIERS: real a,b with a<=b; u:[a,b] -> R; phi on u([a,b])
SOURCE_CONCLUSION: int_a^b phi(u(ell)) u_prime(ell) dell = int_{u(a)}^{u(b)} phi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-P-p
REVIEWER: sol-delta-P-p
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: P-OWNED external: excluded by the published I graph because its only consumer means is outside the I root closure; owned by P under the writer ruling. The actual consumer mv-cv uses continuous phi, so the standard change-of-variable theorem applies. The source item leaves integrand regularity implicit; this record does not silently add a source premise.

NODE: stepI:p7:mv-cv
KIND: step
TITLE: Change of variable
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:mv-cv@L298-L298
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:mv-cv@L298-L298
CONTRACT_ID: stepI:p7:mv-cv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (L,G) in C_0, g in R, e=e(L,G), a=L^2, (q,p)=Q(ell,g,L,G), r=¦q¦_2, as in means; no previously derived integral identity is assumed
SOURCE_QUANTIFIERS: (L,G) in C_0; g in R; continuous phi on [0,2pi]
SOURCE_CONCLUSION: ell -> u_R(ell,e) is increasing C1 with endpoints 0,2pi and dell=D du; int_0^{2pi} phi(u(ell)) dell = int_0^{2pi} phi(u) D(u) du, D(u)=1-e cos u
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: I:bpI:p7:kepler-eq, I:bpI:p7:orbit-maps, bpI:p7:x-change
ROUTES: -
ROUTE_FOR: -
EDGE: I:bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:mv-cv@L298-L298 | parts (b),(c) supply the real anomaly diffeomorphism, derivative and endpoints
EDGE: I:bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:mv-cv@L298-L298 | defines u and D used by the orbit parametrization
EDGE: bpI:p7:x-change | blueprint-I/parts/p7-delaunay.tex#stepI:p7:mv-cv@L298-L298 | change of variables for the continuous integrand and increasing C1 inverse anomaly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-P-p
REVIEWER: sol-delta-P-p
LEAN_STATUS: PROVED
LEAN_REF: integral_comp_eccAnom (KAM/Kepler/Means.lean)
LEAN_NOTE: audit KEP-8 PASS WITH NOTES; named stepI:p7:mv-cv
NOTE: -

NODE: stepI:p7:mv-int
KIND: step
TITLE: Integrals
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:mv-int@L300-L300
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:mv-int@L300-L300
CONTRACT_ID: stepI:p7:mv-int
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (L,G) in C_0, g in R, e=e(L,G), a=L^2, (q,p)=Q(ell,g,L,G), r=¦q¦_2, as in means; no previously derived integral identity is assumed
SOURCE_QUANTIFIERS: (L,G) in C_0; g in R
SOURCE_CONCLUSION: the normalized means of 1/r, ¦p¦_2^2 and r are 1/a, 1/a and a(1+e^2/2), respectively
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:mv-cv, I:bpI:p7:orbit-identities, I:bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:mv-cv | blueprint-I/parts/p7-delaunay.tex#stepI:p7:mv-int@L300-L300 | replace dell by D du in the continuous integrals
EDGE: I:bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#stepI:p7:mv-int@L300-L300 | r=aD and E=-1/(2a) supply the radius and virial calculation
EDGE: I:bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:mv-int@L300-L300 | the orbit quantities q,p,r,a,e are the defined ones
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-P-p
REVIEWER: sol-delta-P-p
LEAN_STATUS: PROVED
LEAN_REF: orbitMapR_mean_inv_radius, orbitMapR_mean_speed_sq, orbitMapR_mean_radius (KAM/Kepler/Means.lean)
LEAN_NOTE: audit KEP-8 PASS WITH NOTES; integrals of the three means
NOTE: -

NODE: stepI:p7:ci-alg
KIND: step
TITLE: Same algebra
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ci-alg@L308-L308
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ci-alg@L308-L308
CONTRACT_ID: stepI:p7:ci-alg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: real L>0, 0<=e<1, k=sqrt(1-e^2), G=Lk; ell,g real; q,p are the explicit orbit formulas with u=u_R(ell,e)
SOURCE_QUANTIFIERS: L>0; 0<=e<1; ell,g in R
SOURCE_CONCLUSION: the radius, momentum, scalar energy and angular-momentum formulas and the three means extend to e=0; at e=0 u=ell, r=L^2, ¦p¦_2=1/L, E=-1/(2L^2), Gamma=L; no membership in C or chart bijectivity at e=0 is asserted
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: I:bpI:p7:orbit-maps, I:bpI:p7:orbit-identities, I:bpI:p7:kepler-eq, stepI:p7:mv-cv, stepI:p7:mv-int
ROUTES: -
ROUTE_FOR: -
EDGE: I:bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ci-alg@L308-L308 | the explicit Q_el formulas admit independent e=0
EDGE: I:bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ci-alg@L308-L308 | reuse the computations of oi-r through oi-en, which require D>0 but not e>0; do not apply the C-membership conclusion at e=0
EDGE: I:bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ci-alg@L308-L308 | real anomaly exists for ¦e¦<1 and u(ell,0)=ell
EDGE: stepI:p7:mv-cv | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ci-alg@L308-L308 | reuse the change-of-variable computation, whose derivative and endpoint conditions still hold at e=0
EDGE: stepI:p7:mv-int | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ci-alg@L308-L308 | reuse the integral and scalar virial computations with D=1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-P-p
REVIEWER: sol-delta-P-p
LEAN_STATUS: PROVED
LEAN_REF: ci_alg (KAM/Kepler/ScalingNodes.lean)
LEAN_NOTE: audit GAP-P7 round 2 PASS WITH NOTES; audit-1 F1 closed
NOTE: The dependencies on proof computations record the source-explicit reuse of algebra, not application of a strictly noncircular statement at e=0.

NODE: stepI:p7:sc-alg
KIND: step
TITLE: Algebra
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sc-alg@L320-L320
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sc-alg@L320-L320
CONTRACT_ID: stepI:p7:sc-alg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: k>0; E_k(q,p)=¦p¦_2^2/2-k/¦q¦_2 on q!=0; S_k(Q,P)=(Q/k,kP); J is the standard positions-first symplectic matrix
SOURCE_QUANTIFIERS: k>0; Q,P in R^2 with Q!=0
SOURCE_CONCLUSION: E_k(S_k(Q,P))=k^2 E_1(Q,P); DS_k=diag(k^-1,k^-1,k,k) and DS_k^T J DS_k=J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-P-p
REVIEWER: sol-delta-P-p
LEAN_STATUS: PROVED
LEAN_REF: sc_alg (KAM/Kepler/ScalingNodes.lean)
LEAN_NOTE: audit GAP-P7 round 2 PASS WITH NOTES
NOTE: The conversion(a) citation is an as-in pointer to the same block multiplication for a different matrix, not an application of that specialized result.

NODE: stepI:p7:sc-flow
KIND: step
TITLE: Flow and averages
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sc-flow@L321-L321
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sc-flow@L321-L321
CONTRACT_ID: stepI:p7:sc-flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: k>0; E_k and S_k as in scaling; for the flow assertion (Q,P)(tau) solves Hamilton equations of E_1 on the collision-free domain; for the averages a is the semi-major axis of the bound Kepler orbit, with mean-anomaly averages as in means
SOURCE_QUANTIFIERS: k>0; an E_1 solution on its time interval; for the averages a bound Kepler orbit
SOURCE_CONCLUSION: DS_k X_{E_k o S_k}=X_{E_k} o S_k and k^2 DS_k X_{E_1}=X_{E_k} o S_k; t -> S_k(Q,P)(k^2 t) solves E_k; a_k=a/k, <1/¦q¦_2>=1/a_k, <¦p¦_2^2>=k/a_k, E_k=-k/(2a_k)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:sc-alg, bpI:p7:means, I:bpI:p7:orbit-identities
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:sc-alg | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sc-flow@L321-L321 | energy rescaling and the symplectic matrix identity supply the local field calculation
EDGE: bpI:p7:means | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sc-flow@L321-L321 | unit-strength mean values give the scaled averages
EDGE: I:bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sc-flow@L321-L321 | part (c) supplies E_1=-1/(2a), a=L^2, used in the final scaled-energy identity
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-delta-P-p
REVIEWER: sol-delta-P-ah
LEAN_STATUS: PROVED
LEAN_REF: sc_flow (KAM/Kepler/ScalingNodes.lean)
LEAN_NOTE: audit GAP-P7 round 2 PASS WITH NOTES; pointwise flow / parametrized-orbit averages
NOTE: The sy-field citation is an as-in pointer: the source repeats naturality and the curve chain rule for the linear S_k. It does not apply the Q-specific Delaunay-field theorem.
