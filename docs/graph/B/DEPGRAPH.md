# Proof dependency database — track B (program B: effective stability, B1-T / B1-E)

GRAPH_VERSION: 4
ROOTS: b:2.2#B1-T, b:2.3#B1-E, b:4#HH
CORPUS: docs/explorations/program-b-plan.md (§2.1–2.3 L66–L206, §3.1 L300–L340, §3.2–3.3 L341–L424, §4 first instance L529–L566, Brief 2 L833–L870), docs/tracks/B/FREEZE-PROPOSAL.md (§2 L17–L99, §6 L161–L166) and docs/tracks/B/FREEZE-PROPOSAL-HH.md (L1–L41), pinned by SHA-256 in docs/graph/B/CORPUS.sha256 (main 95387f9b0, 2026-11-03)
CONVENTIONS: Phase n = (Fin n -> R) x (Fin n -> R); max norm; X_H = (partial_J H, -partial_phi H); symplecticForm(v,w) = sum_j (v.2 j w.1 j - v.1 j w.2 j); solutions on an open interval containing [-T,T], unique on interval intersections, bounds for every |t| <= T (plan §2.1); action margins are b_j - a_j in actions (squared radii) for B1-E; bracket {F,G} = sum_j (F_phi G_J - F_J G_phi) (plan L79-L82); B1-E coordinates w = (q,p) with I_j = oscillatorAction w.2 w.1; root statement fields follow the exact frozen text, plan premises are provenance (FREEZE-PROPOSAL §6)
STANDING_ASSUMPTIONS: -
EXTERNAL_POLICY: Mathlib-level inputs are KIND external nodes: ODE local existence/uniqueness and compact continuation (ext:ode#*), and the Cauchy estimate (ext:analysis#cauchy); cited GLS17/CL20 derivations are reproduced in the plan and are provenance, not external inputs
FROZEN_ANCHORS: b:defs#hamiltonianVectorField, b:defs#symplecticForm, b:defs#oscillatorAction, b:2.2#B1-T, b:2.3#B1-E, b:4#HH
FROZEN_MANIFEST: manifest/frozen-anchors.json | sha256:0c83c45ed823f7f76695aee111d6c48f8f051adc1642a12a736a814ca5e9a43f
WRITER: kam-b1
GLOBAL_REVIEWER: sonnet-global-B-hh
GLOBAL_REVIEW_REF: B1 roots: docs/graph/B/reviews/GLOBAL-review.md, GLOBAL-recheck.md (sonnet-global-B); HH root: GLOBAL-review-hh.md, GLOBAL-recheck-hh.md, GLOBAL-final-hh.md (sonnet-global-B-hh, final VERDICT ACCEPT); node reviews NODE-review.md, NODE-*-hh.md

The dependency direction is `NODE -> prerequisite`. `DEPS` is conjunctive. Node blocks are generated from the
writer's node table; correct structure after publication only by append-only `AMEND` records.

## Nodes

NODE: b:defs#hamiltonianVectorField
KIND: definition
TITLE: Hamiltonian vector field X_H = (dH/dJ, -dH/dphi)
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:2.1@L77-L80
PROOF_SOURCE: -
CONTRACT_ID: kam.hamiltonianVectorField
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H : Phase n -> R
SOURCE_QUANTIFIERS: n; H
SOURCE_CONCLUSION: defines X_H = (partial_J H, -partial_phi H) on Phase n
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/HamiltonianVectorField.lean
FROZEN_DECL: KAM.hamiltonianVectorField
FROZEN_ANCHOR_ID: kam.hamiltonianVectorField.v1
FROZEN_ABI_SHA256: 427a145572df4c3e14079cf88feb16d60e1cd92fcd1770faddd36ad706562ca6
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.hamiltonianVectorField (KAM/Frozen/Defs/HamiltonianVectorField.lean)
LEAN_NOTE: sealed frozen definition; nothing to prove
NOTE: -

NODE: b:defs#symplecticForm
KIND: definition
TITLE: Repository symplectic form
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:2.1@L85-L86
PROOF_SOURCE: -
CONTRACT_ID: kam.symplecticForm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v, w : Phase n
SOURCE_QUANTIFIERS: n; v, w
SOURCE_CONCLUSION: defines symplecticForm(v,w) = sum_j (v.2 j * w.1 j - v.1 j * w.2 j)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/SymplecticForm.lean
FROZEN_DECL: KAM.symplecticForm
FROZEN_ANCHOR_ID: kam.symplecticForm.v1
FROZEN_ABI_SHA256: 542b8d8eb08283f5c961a969dd96003cbb23fc447da8ea444498cb92a48f6d75
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.symplecticForm (KAM/Frozen/Defs/SymplecticForm.lean)
LEAN_NOTE: sealed frozen definition; nothing to prove
NOTE: -

NODE: b:defs#oscillatorAction
KIND: definition
TITLE: Oscillator actions I_j(q,p) = (q_j^2 + p_j^2)/2
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:2.3@L167-L173
PROOF_SOURCE: -
CONTRACT_ID: planetary.oscillatorAction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q, p : Vec n
SOURCE_QUANTIFIERS: n; q, p; j
SOURCE_CONCLUSION: defines I_j(q,p) = (q_j^2 + p_j^2)/2
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/OscillatorAction.lean
FROZEN_DECL: KAM.Planetary.oscillatorAction
FROZEN_ANCHOR_ID: planetary.oscillatorAction.v1
FROZEN_ABI_SHA256: b37f7928355c64fc3555d65704a95ecdb67fe55bdd7bb2471ac609553f2a962a
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.oscillatorAction (KAM/Frozen/Planetary/Defs/OscillatorAction.lean)
LEAN_NOTE: sealed frozen definition; nothing to prove
NOTE: -

NODE: b:defs#bracket
KIND: definition
TITLE: Poisson bracket convention {F,G} = sum_j (F_phi_j G_J_j - F_J_j G_phi_j); ad_chi F = {F,chi}
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:2.1@L79-L82
PROOF_SOURCE: -
CONTRACT_ID: b.def.bracket
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F, G differentiable on Phase n
SOURCE_QUANTIFIERS: F, G
SOURCE_CONCLUSION: defines {F,G}; along a solution of X_G, d/dt F = {F,G}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:defs#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: b:defs#hamiltonianVectorField | docs/explorations/program-b-plan.md#b:2.1@L79-L82 | the bracket is the derivative of F along X_G
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: PROVED
LEAN_REF: convention realized in KAM.EffectiveStability.bracket_action_eq_of_eventuallyEq and the frozen B1-E bracket text
LEAN_NOTE: convention; nothing further to prove
NOTE: convention only; in the frozen B1-E text the bracket {I_j,R} is written out as q_j R_{p_j} - p_j R_{q_j} (FREEZE-PROPOSAL L59-L60, L80-L83)

NODE: ext:ode#local
KIND: external
TITLE: Local existence and uniqueness for C^1 (locally Lipschitz) vector fields (Picard-Lindelof)
STATEMENT_SOURCE: external:repo-ode#local
PROOF_SOURCE: -
CONTRACT_ID: ext.ode.local
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: vector field C^1 on an open set U; initial point in U
SOURCE_QUANTIFIERS: field, U, initial point; then exists eps>0
SOURCE_CONCLUSION: a unique local solution on (-eps, eps) in U; two solutions agree near a common time
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: EXTERNAL
LEAN_REF: KAM.ODE.gen_uniqueness_inter (KAM/ODE/Uniqueness.lean)
LEAN_NOTE: discharged by the repository ODE library (Picard-Lindelof based)
NOTE: repository KAM.ODE local theory (built on Mathlib IsPicardLindelof); invoked by "Handle T=0 by local existence" (L854) and by the uniqueness step

NODE: ext:ode#compact-continuation
KIND: external
TITLE: Continuation: a solution confined to a compact subset of the open domain of a C^1 field extends past both ends of a bounded interval
STATEMENT_SOURCE: external:repo-ode#continuation
PROOF_SOURCE: -
CONTRACT_ID: ext.ode.continuation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: C^1 field on open U; solution on a bounded open interval staying in a compact K subset U
SOURCE_QUANTIFIERS: field, U, K; then the solution
SOURCE_CONCLUSION: the solution extends to a strictly larger open interval (both ends), still a solution in U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: EXTERNAL
LEAN_REF: KAM.ODE.gen_maximal (KAM/ODE/Continuation.lean)
LEAN_NOTE: discharged by the repository ODE library
NOTE: "the existing continuation theorem" (plan L850-L851); the repository KAM.ODE continuation library

NODE: b:brief2#chart-transport
KIND: step
TITLE: Symplectic field identity and chart transport: DPsi(w) X_{H o Psi}(w) = X_H(Psi w); chart solutions push forward to physical solutions
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L852-L853
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L852-L853
CONTRACT_ID: b.step.chart-transport
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: V open; H C^2 on V; Psi C^2 on the open chart domain D with Psi(D) subset V; DPsi preserves symplecticForm; symplecticForm nondegenerate; Psiinv o Psi = id on D
SOURCE_QUANTIFIERS: n; H, Psi; then w in D; then any chart solution w(t) in D
SOURCE_CONCLUSION: DPsi(w) is invertible and DPsi(w) X_{H o Psi}(w) = X_H(Psi w); H o Psi is C^2 on D (so X_{H o Psi} is C^1); if w solves w' = X_{H o Psi}(w) in D then z = Psi o w solves z' = X_H(z) in V and Psi(Psiinv(z t)) = z t with Psiinv(z t) = w t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:defs#hamiltonianVectorField, b:defs#symplecticForm
ROUTES: -
ROUTE_FOR: -
EDGE: b:defs#hamiltonianVectorField | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L852-L853 | both sides of the identity are Hamiltonian fields
EDGE: b:defs#symplecticForm | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L852-L853 | symplecticity of DPsi and nondegeneracy of symplecticForm give the identity and invertibility
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.hasDerivAt_comp_chart, fderiv_chart_apply_hamiltonianVectorField (KAM/EffectiveStability/Transfer.lean)
LEAN_NOTE: landed main (track B batch 2+)
NOTE: frozen premises: hH, hPsi, hPsiV, hPsisymp, hPsiinv (FREEZE-PROPOSAL L31-L37); no inverse regularity or open image is needed (OD-B3, left inverse)

NODE: b:brief2#stopped-drift
KIND: step
TITLE: Stopped drift: a scalar derivative bound |f'| <= eta on an interval containing 0 gives |f(t) - f(0)| <= eta |t| in both time directions
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L847-L848
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L847-L848
CONTRACT_ID: b.step.stopped-drift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f differentiable on an interval I containing 0 with |f'| <= eta there; eta >= 0
SOURCE_QUANTIFIERS: f, eta; then t in I
SOURCE_CONCLUSION: |f(t) - f(0)| <= eta |t| for t >= 0 and t <= 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.abs_sub_le_of_deriv_bound (KAM/EffectiveStability/StoppedDrift.lean)
LEAN_NOTE: landed main
NOTE: eta = 0 allowed, no division (L854-L855)

NODE: b:brief2#uniqueness
KIND: step
TITLE: Uniqueness on interval intersections
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:2.1@L94-L95
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L853-L853
CONTRACT_ID: b.step.uniqueness
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: V open; H C^2 on V (so X_H is C^1, hence locally Lipschitz); y, z solutions in V on order-connected intervals I, U containing 0 with y(0) = z(0)
SOURCE_QUANTIFIERS: solutions y, z; intervals I, U
SOURCE_CONCLUSION: y = z on I intersect U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:ode#local, b:defs#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: ext:ode#local | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L853-L853 | local uniqueness propagated along the interval intersection
EDGE: b:defs#hamiltonianVectorField | docs/explorations/program-b-plan.md#b:2.1@L90-L95 | the solution notion HasDerivAt z (X_H (z t)) and C^1 regularity of X_H from H C^2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_uniqueness_inter used in torus_confinement_proof / oscillator_confinement_proof
LEAN_NOTE: landed main
NOTE: -

NODE: b:2.2#action-derivative
KIND: step
TITLE: Cylinder action derivative J'_j = -d_{phi_j} R along a chart solution
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L848-L848
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:2.2-source-and-proof@L157-L159
CONTRACT_ID: b.step.torus-action-derivative
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H o Psi = N(J) + R(phi,J) on the open chart domain C_(b+eps); H o Psi C^2 there (chart-transport) and R differentiable there; w = (phi,J) solves w' = X_{H o Psi}(w) in C_(b+eps)
SOURCE_QUANTIFIERS: w on an interval I; t in I; j
SOURCE_CONCLUSION: J_j'(t) = -partial_{phi_j} R(w(t)) (the N part does not depend on phi, differentiated through H o Psi - R)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:brief2#chart-transport, b:defs#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: b:brief2#chart-transport | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L848-L848 | H o Psi is C^2 on C_(b+eps), from chart-transport conclusion, so fderiv(H o Psi) - fderiv R is the derivative of N(J)
EDGE: b:defs#hamiltonianVectorField | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L848-L848 | J-component of X_{N+R} is -partial_phi (N+R) = -partial_phi R
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.fderiv_angle_eq_of_eventuallyEq, hamiltonianVectorField_snd_apply (KAM/EffectiveStability/ActionDerivative.lean)
LEAN_NOTE: landed main
NOTE: frozen version differentiates H o Psi - R, so no regularity of N is assumed (FREEZE-PROPOSAL L25-L27)

NODE: b:2.2#first-exit
KIND: step
TITLE: B1-T first-exit bootstrap: while |t| <= T a chart solution started in |J| <= a stays in |J_j| <= a_j + eta_j |t| < b_j (inside the chart domain)
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:2.2-source-and-proof@L161-L161
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L849-L850
CONTRACT_ID: b.step.torus-first-exit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: eps > 0; |J_j(0)| <= a_j; eta_j >= 0; a_j + T eta_j < b_j; |d_{phi_j} R| <= eta_j on closed C_b; w a chart solution on an interval I containing 0 while it stays in C_(b+eps)
SOURCE_QUANTIFIERS: for any such w and I (existence NOT assumed); then t in I with |t| <= T; j
SOURCE_CONCLUSION: w(t) in closed C_b, |J_j(t) - J_j(0)| <= eta_j |t| and |J_j(t)| <= a_j + eta_j |t| < b_j, so w never reaches the boundary of C_(b+eps) for |t| <= T
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:2.2#action-derivative, b:brief2#stopped-drift
ROUTES: -
ROUTE_FOR: -
EDGE: b:2.2#action-derivative | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L849-L850 | the derivative identity bounds abs J_j'abs  by eta_j while in closed C_b
EDGE: b:brief2#stopped-drift | docs/explorations/program-b-plan.md#b:2.2-source-and-proof@L161-L161 | stopped drift applied on the sub-interval before the first exit from closed C_b, contradicted by the strict margin
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.firstExit_box_of_deriv (KAM/EffectiveStability/FirstExit.lean)
LEAN_NOTE: landed main
NOTE: a_j >= 0 follows from |J_j(0)| <= a_j; eta = 0 and both time directions allowed (L847-L848, L854-L855); the reviewer rule L863-L864 (no assumed existence interval) is respected

NODE: b:2.2#periodic-reduction
KIND: step
TITLE: Periodic continuation: an angle-periodic C^1 chart field with solutions confined to a closed action box inside the domain continues past [-T,T]
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:2.2-source-and-proof@L161-L163
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L850-L852
CONTRACT_ID: b.step.torus-periodic-reduction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H o Psi = N(J) + R with R angle-periodic (so X_{H o Psi} is 1-periodic in phi); field X_{H o Psi} C^1 on C_(b+eps) by chart-transport; confinement of every chart solution to closed C_b for |t| <= T (first exit)
SOURCE_QUANTIFIERS: w0 with |J0| <= a; T
SOURCE_CONCLUSION: the chart solution from w0 exists on an open interval Ioo(-T1, T1) with T < T1 and stays in C_(b+eps)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:2.2#first-exit, ext:ode#compact-continuation, ext:ode#local, b:brief2#chart-transport, b:defs#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: b:2.2#first-exit | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L850-L851 | confinement in the closed action box
EDGE: ext:ode#compact-continuation | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L851-L852 | continuation applied on the compact fundamental cell [0,1]^n x closed box, transported by angle periodicity
EDGE: ext:ode#local | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L854-L854 | T = 0 and the restart after integer angle shifts by local existence/uniqueness
EDGE: b:brief2#chart-transport | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L850-L852 | C^1 regularity of the chart field X_{H o Psi}; its angle periodicity from hRper and H o Psi = N(J) + R
EDGE: b:defs#hamiltonianVectorField | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L850-L852 | the continued field is the Hamiltonian field X_{H o Psi}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.exists_confined_solution_periodic (KAM/EffectiveStability/ChartFlow.lean)
LEAN_NOTE: landed main
NOTE: lifted angles are unbounded, so the cylinder is not compact (L162-L163); periodicity of R (hRper, FREEZE-PROPOSAL L40-L41) replaces the plan's V/H/Psi periodicity premises (OD-B2)

NODE: b:2.2#B1-T
KIND: theorem
TITLE: B1-T: finite confinement in a canonical cylinder (frozen torus_confinement)
STATEMENT_SOURCE: docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L24-L54
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:2.2-source-and-proof@L157-L163
CONTRACT_ID: effectiveStability.d72.torus_confinement
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b,eta : Vec n; eps > 0; T >= 0; eta_j >= 0; a_j + T eta_j < b_j; V open; H C^2 on V; Psi C^2 on C_(b+eps) := {abs J_j < b_j + eps}; Psi(C_(b+eps)) subset V; DPsi preserves symplecticForm; Psiinv o Psi = id on C_(b+eps); N : Vec n -> R; R differentiable on C_(b+eps), 1-periodic in phi; H(Psi w) = N(J) + R(w) on C_(b+eps); abs(fderiv R w (e_j,0)) <= eta_j on closed C_b; w0 with abs(J0_j) <= a_j
SOURCE_QUANTIFIERS: n, a, b, eta, eps, T, V, H, Psi, Psiinv, N, R and their premises fixed; for every w0; then exists T1 > T and z
SOURCE_CONCLUSION: z(0) = Psi(w0); for t in Ioo(-T1,T1): z(t) in V and z'(t) = X_H(z(t)); every solution y in V on an order-connected I containing 0 with y(0) = Psi(w0) equals z on I intersect Ioo(-T1,T1); for every abs t <= T: Psi(Psiinv(z t)) = z t, abs(J_j(t) - J0_j) <= eta_j abs t and abs J_j(t) <= a_j + eta_j T, where (phi,J)(t) = Psiinv(z t)
CONSTANT_SCOPE: no unquantified constant
FROZEN_FILE: KAM/Frozen/EffectiveStability/TorusConfinement.lean
FROZEN_DECL: KAM.EffectiveStability.torus_confinement
FROZEN_ANCHOR_ID: effectiveStability.d72.torus_confinement.v1
FROZEN_ABI_SHA256: bc5bc3eca192d370415c8cd4916c61345fda22452343ea83734171747c129a54
DEPS: b:2.2#periodic-reduction, b:2.2#first-exit, b:brief2#uniqueness, b:brief2#chart-transport, b:defs#hamiltonianVectorField, b:defs#symplecticForm
ROUTES: -
ROUTE_FOR: -
EDGE: b:2.2#periodic-reduction | docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L47-L48 | existence on Ioo(-T1,T1) with T < T1
EDGE: b:2.2#first-exit | docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L53-L54 | drift and confinement bounds
EDGE: b:brief2#uniqueness | docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L49-L52 | uniqueness clause
EDGE: b:brief2#chart-transport | docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L47-L53 | z = Psi o w solves X_H in V and Psi(Psiinv(z t)) = z t
EDGE: b:defs#hamiltonianVectorField | docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L48-L48 | HasDerivAt z (X_H (z t))
EDGE: b:defs#symplecticForm | docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L35-L36 | hPsisymp
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.torus_confinement (KAM/Frozen/EffectiveStability/TorusConfinement.lean); provider KAM.Provider.EffectiveStability.torus_confinement
LEAN_NOTE: SEALED (D72, manifest effectiveStability.d72.torus_confinement.v1, main cff2accd5); seal audit 1 PASS WITH NOTES; standard axioms
NOTE: statement source = the exact frozen text (FREEZE-PROPOSAL §2, owner D72); mathematical source plan §2.2 L100-L136; deviations (minimal premises OD-B2, left-inverse chart OD-B3, n >= 1 dropped OD-B6) listed in FREEZE-PROPOSAL §6 L161-L166

NODE: b:2.3#action-bracket
KIND: step
TITLE: Oscillator action derivative (I_j o w)' = {I_j, H o Psi} along a chart solution
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L849-L849
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L848-L849
CONTRACT_ID: b.step.osc-action-bracket
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: w solves w' = X_{H o Psi}(w) in E_(b+eps); H o Psi C^2 there (chart-transport)
SOURCE_QUANTIFIERS: w on an interval I; t in I; j
SOURCE_CONCLUSION: (I_j o w)'(t) = {I_j, H o Psi}(w(t))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:brief2#chart-transport, b:defs#oscillatorAction, b:defs#bracket, b:defs#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: b:brief2#chart-transport | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L848-L849 | H o Psi is C^2 on E_(b+eps), from chart-transport conclusion, so I_j o w has derivative DI_j . X_{H o Psi}
EDGE: b:defs#oscillatorAction | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L849-L849 | I_j is the frozen oscillator action
EDGE: b:defs#bracket | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L849-L849 | derivative along X_G is the bracket with G
EDGE: b:defs#hamiltonianVectorField | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L849-L849 | d/dt I(w) = DI . X_{H o Psi}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.hasDerivAt_oscillatorAction, bracket_action_eq_of_eventuallyEq (KAM/EffectiveStability/ActionDerivative.lean)
LEAN_NOTE: landed main
NOTE: -

NODE: b:2.3#normal-form-commutes
KIND: step
TITLE: Vanishing normal-form contribution: g = H o Psi - R = N o I gives {I_j, g} = 0
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:2.3-continuation@L196-L196
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L849-L849
CONTRACT_ID: b.step.osc-normal-form-commutes
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: g differentiable on E_(b+eps) and g = N o I there (N arbitrary)
SOURCE_QUANTIFIERS: g; j; w in E_(b+eps)
SOURCE_CONCLUSION: {I_j, g}(w) = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:defs#oscillatorAction, b:defs#bracket
ROUTES: -
ROUTE_FOR: -
EDGE: b:defs#oscillatorAction | docs/explorations/program-b-plan.md#b:2.3-continuation@L196-L196 | g is a function of the actions, invariant under the I_j rotations
EDGE: b:defs#bracket | docs/explorations/program-b-plan.md#b:2.3-continuation@L196-L196 | {I_j, .} is the derivative along the j-th rotation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.bracket_action_eq_of_eventuallyEq (KAM/EffectiveStability/ActionDerivative.lean)
LEAN_NOTE: landed main
NOTE: frozen version: rotation invariance of the differentiable H o Psi - R, no differentiability of N (FREEZE-PROPOSAL L60-L61); source states it as the algebraic lemma {I_j, N o I} = 0

NODE: b:2.3#first-exit
KIND: step
TITLE: B1-E first-exit bootstrap: while |t| <= T, 0 <= I_j(w(t)) <= a_j + eta_j |t| < b_j; no exit through I_j = 0
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:2.3-continuation@L195-L196
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L849-L850
CONTRACT_ID: b.step.osc-first-exit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: eps > 0; I_j(w0) <= a_j; eta_j >= 0; a_j + T eta_j < b_j; |{I_j,R}| <= eta_j on closed E_b; w a chart solution on an interval I containing 0 while it stays in E_(b+eps)
SOURCE_QUANTIFIERS: for any such w and I (existence NOT assumed); then t in I with |t| <= T; j
SOURCE_CONCLUSION: w(t) in closed E_b, |I_j(w(t)) - I_j(w0)| <= eta_j |t| and 0 <= I_j(w(t)) <= a_j + eta_j |t| < b_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:2.3#action-bracket, b:2.3#normal-form-commutes, b:brief2#stopped-drift, b:defs#oscillatorAction
ROUTES: -
ROUTE_FOR: -
EDGE: b:2.3#action-bracket | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L849-L849 | derivative of I_j along w
EDGE: b:2.3#normal-form-commutes | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L849-L849 | leaves {I_j,R}
EDGE: b:brief2#stopped-drift | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L849-L850 | stopped drift applied on the sub-interval before the first exit from closed E_b
EDGE: b:defs#oscillatorAction | docs/explorations/program-b-plan.md#b:2.3-continuation@L195-L195 | I_j >= 0 and I_j = 0 is an interior Cartesian point
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.firstExit_box_nonneg, firstExit_box_of_deriv (KAM/EffectiveStability/FirstExit.lean)
LEAN_NOTE: landed main
NOTE: zero actions and eta = 0 without division (L854-L855); no assumed existence interval (L863-L864)

NODE: b:2.3#compact-continuation
KIND: step
TITLE: B1-E continuation via the compact Cartesian set closed E_b inside E_(b+eps)
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:2.3-continuation@L196-L196
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L850-L852
CONTRACT_ID: b.step.osc-continuation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: closed E_b = {I_j <= b_j} compact (product of closed discs; b_j > 0 from a_j >= 0 and the margin) inside E_(b+eps); field X_{H o Psi} C^1 there by chart-transport; first-exit confinement for |t| <= T
SOURCE_QUANTIFIERS: w0 with I(w0) <= a; T
SOURCE_CONCLUSION: the chart solution from w0 exists on Ioo(-T1, T1) with T < T1 and stays in E_(b+eps)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:2.3#first-exit, ext:ode#compact-continuation, ext:ode#local, b:defs#oscillatorAction, b:brief2#chart-transport, b:defs#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: b:2.3#first-exit | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L850-L851 | confinement in closed E_b
EDGE: ext:ode#compact-continuation | docs/explorations/program-b-plan.md#b:2.3-continuation@L196-L196 | closed E_b provides continuation
EDGE: ext:ode#local | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L854-L854 | T = 0 by local existence
EDGE: b:defs#oscillatorAction | docs/explorations/program-b-plan.md#b:2.3-continuation@L196-L196 | compactness of closed E_b from I_j = (q_j^2+p_j^2)/2
EDGE: b:brief2#chart-transport | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L850-L852 | C^1 regularity of the chart field X_{H o Psi}
EDGE: b:defs#hamiltonianVectorField | docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L850-L852 | the continued field is the Hamiltonian field X_{H o Psi}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.exists_confined_solution_compact (KAM/EffectiveStability/ChartFlow.lean)
LEAN_NOTE: landed main
NOTE: -

NODE: b:2.3#B1-E
KIND: theorem
TITLE: B1-E: Cartesian oscillator confinement, including zero actions (frozen oscillator_confinement)
STATEMENT_SOURCE: docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L57-L95
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:2.3-continuation@L195-L205
CONTRACT_ID: effectiveStability.d72.oscillator_confinement
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b,eta : Vec n; eps > 0; T >= 0; eta_j >= 0; a_j + T eta_j < b_j; V open; H C^2 on V; Psi C^2 on E_(b+eps) := {I_j < b_j + eps}; Psi(E_(b+eps)) subset V; DPsi preserves symplecticForm; Psiinv o Psi = id on E_(b+eps); N : Vec n -> R; R differentiable on E_(b+eps); H(Psi w) = N(I(w)) + R(w) there; abs(q_j R_{p_j} - p_j R_{q_j}) <= eta_j on closed E_b; w0 with I_j(w0) <= a_j
SOURCE_QUANTIFIERS: n, a, b, eta, eps, T, V, H, Psi, Psiinv, N, R and their premises fixed; for every w0; then exists T1 > T and z
SOURCE_CONCLUSION: z(0) = Psi(w0); for t in Ioo(-T1,T1): z(t) in V and z'(t) = X_H(z(t)); uniqueness on I intersect Ioo(-T1,T1) as in B1-T; for every abs t <= T: Psi(Psiinv(z t)) = z t, abs(I_j(Psiinv(z t)) - I_j(w0)) <= eta_j abs t and I_j(Psiinv(z t)) <= a_j + eta_j T
CONSTANT_SCOPE: no unquantified constant
FROZEN_FILE: KAM/Frozen/EffectiveStability/OscillatorConfinement.lean
FROZEN_DECL: KAM.EffectiveStability.oscillator_confinement
FROZEN_ANCHOR_ID: effectiveStability.d72.oscillator_confinement.v1
FROZEN_ABI_SHA256: 6ea8db1e9947d08a0c3cd70be06e80dc6e5cb64ac5d4c82902023f04dfd3ef4c
DEPS: b:2.3#compact-continuation, b:2.3#first-exit, b:brief2#uniqueness, b:brief2#chart-transport, b:defs#hamiltonianVectorField, b:defs#symplecticForm, b:defs#oscillatorAction
ROUTES: -
ROUTE_FOR: -
EDGE: b:2.3#compact-continuation | docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L86-L87 | existence on Ioo(-T1,T1)
EDGE: b:2.3#first-exit | docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L92-L95 | drift and confinement bounds
EDGE: b:brief2#uniqueness | docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L88-L91 | uniqueness clause
EDGE: b:brief2#chart-transport | docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L87-L92 | z = Psi o w and Psi(Psiinv(z t)) = z t
EDGE: b:defs#hamiltonianVectorField | docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L87-L87 | HasDerivAt z (X_H (z t))
EDGE: b:defs#symplecticForm | docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L70-L72 | hPsisymp
EDGE: b:defs#oscillatorAction | docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L66-L69 | action domains and conclusion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.oscillator_confinement (KAM/Frozen/EffectiveStability/OscillatorConfinement.lean); provider KAM.Provider.EffectiveStability.oscillator_confinement
LEAN_NOTE: SEALED (D72, manifest effectiveStability.d72.oscillator_confinement.v1, main cff2accd5); seal audit 1 PASS WITH NOTES; standard axioms; consumers: oscillator step/chain checker stack generic over CertCoeff K and oscillatorChain_physical_disc (B3-CHAINK, track B batch 17)
NOTE: statement source = exact frozen text (FREEZE-PROPOSAL §2, owner D72); mathematical source plan §2.3 L165-L193; deviations in FREEZE-PROPOSAL §6 L161-L166

NODE: b:3.2#lie-identity
KIND: step
TITLE: Lie series with integral remainder for an exact time-one flow; remainder bound B/(m+1)!
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:3.2@L343-L354
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:3.2@L353-L356
CONTRACT_ID: b.step.lie-identity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: chi with flow Phi_chi^s defined for 0 <= s <= 1 on the stated (outer complex) domain; H analytic there; |ad_chi^{m+1} H| <= B along the flow
SOURCE_QUANTIFIERS: chi, H, m; then the domain points
SOURCE_CONCLUSION: H o Phi_chi^1 = sum_{k<=m} ad_chi^k H / k! + integral remainder, and the remainder is bounded by B/(m+1)!
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:defs#bracket
ROUTES: -
ROUTE_FOR: -
EDGE: b:defs#bracket | docs/explorations/program-b-plan.md#b:3.2@L347-L349 | ad_chi F = {F,chi}; d/ds F o Phi^s = {F,chi} o Phi^s
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability (RealFlow/Lie, Poly/Lie: cartEval_lieSum_complex, Lie-Taylor remainder; OscillatorStep/Remainder)
LEAN_NOTE: landed main (B2)
NOTE: plan: "the existing taylor_lie is the starting point" (L354)

NODE: b:3.2#chart-composition
KIND: step
TITLE: Chart from generators: a composition of exact time-one flows is canonical, has the explicit inverse given by the reversed flows, and composed forward/inverse displacement bounds
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:3.2@L355-L356
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:3.2@L398-L402
CONTRACT_ID: b.step.chart-composition
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: generators chi_1..chi_m with flows for |s| <= 1 on nested domains with strict margins (§3.1 L317-L318)
SOURCE_QUANTIFIERS: the generators and domains
SOURCE_CONCLUSION: Psi = Phi_{chi_1}^1 o ... o Phi_{chi_m}^1 is symplectic on its domain, Psiinv = reversed flows satisfies Psi(Psiinv z) = z and Psiinv(Psi w) = w where defined, discarded polynomial terms stay in R, and forward/inverse displacement bounds compose with the needed derivative factors
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:defs#symplecticForm, b:defs#hamiltonianVectorField, ext:ode#local, b:3.2#lie-identity
ROUTES: -
ROUTE_FOR: -
EDGE: b:3.2#lie-identity | docs/explorations/program-b-plan.md#b:3.2@L355-L356 | the discarded polynomial terms remain in R
EDGE: b:defs#symplecticForm | docs/explorations/program-b-plan.md#b:3.2@L355-L355 | composition of exact flows remains canonical (symplectic)
EDGE: b:defs#hamiltonianVectorField | docs/explorations/program-b-plan.md#b:3.2@L355-L355 | Hamiltonian flows of the generators
EDGE: ext:ode#local | docs/explorations/program-b-plan.md#b:3.1@L317-L318 | every flow for -1 <= s <= 1 and its inverse exist on the domain
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.oscChainMap / oscChainInv, oscChainInv_sub_le, oscChainMap_oscChainInv (OscillatorChain/*, OscillatorChainPhysical)
LEAN_NOTE: landed main (B2, B3-CHAINK)
NOTE: "a truncated coordinate substitution is not the map being certified" (L356); the explicit inverse and the displacement bounds come from L316-L318, L321, L398-L402; "reversed flows" is the group property of exact flows (uniqueness, ext:ode#local), an inference not stated in the source

NODE: ext:analysis#cauchy
KIND: external
TITLE: Cauchy estimate: a holomorphic function bounded by E on a polydisc with margins delta has first derivatives bounded by E/delta on the inner set
STATEMENT_SOURCE: external:analysis#cauchy-estimate
PROOF_SOURCE: -
CONTRACT_ID: ext.analysis.cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f holomorphic on complex discs of radius r + delta about the real points, |f| <= E there
SOURCE_QUANTIFIERS: f, E, r, delta
SOURCE_CONCLUSION: |partial f| <= E/delta on the discs of radius r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes
LEAN_STATUS: EXTERNAL
LEAN_REF: KAM.EffectiveStability Cauchy estimates (Cauchy.lean, CauchyThird.lean)
LEAN_NOTE: discharged by the repository's Cauchy estimates
NOTE: standard analytic input used by plan L368-L369 and L382-L384 without proof (repository Cauchy estimates)

NODE: b:3.2#oscillator-drift
KIND: step
TITLE: Oscillator drift bound: {I_j, R} <= eta_j from the retained residual polynomial plus Cauchy tails, propagated through the charts
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:3.2@L373-L385
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:3.2@L387-L402
CONTRACT_ID: b.step.oscillator-drift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: residual R = retained polynomial P + Lie tails (lie-identity) on Cartesian complex discs with margins; radii w_j with w_j^2 >= 2 b_j, w_j >= 0 fixed before the arithmetic run
SOURCE_QUANTIFIERS: j; w in closed E_b
SOURCE_CONCLUSION: |{I_j, R}(w)| <= eta_j = eta_finite + eta_Lie (+ eta_model + eta_rounding), each contribution propagated through later charts; finite part eta_poly = sum |alpha_j - beta_j| |c_ab| prod rho^(alpha+beta) (L378-L379); Cartesian tail contribution w_j E (1/dq_j + 1/dp_j) (L383-L384)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:3.2#lie-identity, b:defs#bracket, b:defs#oscillatorAction, b:3.2#chart-composition, ext:analysis#cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: b:3.2#lie-identity | docs/explorations/program-b-plan.md#b:3.2@L383-L384 | tail E bounded on the complex discs
EDGE: b:defs#bracket | docs/explorations/program-b-plan.md#b:3.2@L375-L375 | {I_j, z^a zeta^b} = i(a_j - b_j) z^a zeta^b
EDGE: b:defs#oscillatorAction | docs/explorations/program-b-plan.md#b:3.2@L375-L375 | I_j = z_j zeta_j
EDGE: b:3.2#chart-composition | docs/explorations/program-b-plan.md#b:3.2@L399-L402 | propagate each contribution through later charts with derivative factors
EDGE: ext:analysis#cauchy | docs/explorations/program-b-plan.md#b:3.2@L382-L384 | tail on Cartesian complex discs with margins gives w_j E (1/dq_j + 1/dp_j)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.abs_actionBracket_le_supBound, oscillatorChain_confinement (OscillatorChain/Drift)
LEAN_NOTE: landed main (B2, B3-CHAINK)
NOTE: the (Tail) series formula (L387-L397) applies to CL-style infinite majorants; the HH certificate uses finite Lie orders with the B/(m+1)! remainder

NODE: b:3.1#checker-soundness
KIND: claim
TITLE: Checker soundness: an accepted finite normal-form certificate yields the unique trajectory with the stated chart/original-coordinate bounds
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:3.1@L324-L333
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:3.1@L335-L340
CONTRACT_ID: b.claim.checker-soundness
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: supported Hamiltonian expression (exact polynomial first, L304-L306); finite certificate c with: H expression, parameter box and conventions; nested domains, radii and strict margins; generators chi_1..chi_m; normal form N and retained residual P; bounds on discarded terms; (divisor witnesses, producer-side only); forward/inverse displacement bounds and initial-set inclusions; drift bounds eta_j, observable bounds d_i, time T (L313-L322); checkNormalForm Hexpr c = true
SOURCE_QUANTIFIERS: for every expression and certificate; every parameter in c.parameterBox; every z0 in c.initialRegion
SOURCE_CONCLUSION: a unique Hexpr trajectory on an open interval containing [-c.T, c.T] (§2.1 convention), with the stated original-coordinate observable and domain bounds; chart, residual and continuation facts proved from the data
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:2.3#B1-E, b:3.2#chart-composition, b:3.2#lie-identity, b:3.2#oscillator-drift, b:2.3#transfer
ROUTES: -
ROUTE_FOR: -
EDGE: b:2.3#transfer | docs/explorations/program-b-plan.md#b:3.1@L322-L322 | original-coordinate observable bounds (L329-L331) are the transfer formula
EDGE: b:2.3#B1-E | docs/explorations/program-b-plan.md#b:2.3@L197-L198 | the dynamics conclusion (continuation, confinement) is the B1-E sufficient-condition theorem applied to the proved chart data
EDGE: b:3.2#chart-composition | docs/explorations/program-b-plan.md#b:3.1@L336-L336 | "prove the chart ... facts": symplectic chart with explicit inverse
EDGE: b:3.2#lie-identity | docs/explorations/program-b-plan.md#b:3.1@L336-L336 | "residual ... facts": H o Psi = N o I + R with exact Lie identities
EDGE: b:3.2#oscillator-drift | docs/explorations/program-b-plan.md#b:3.1@L319-L322 | drift bounds eta_j for the B1-E bracket premise
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.checkOscChain_sound (OscillatorChainCheck.lean), oscillatorChain_physical_disc (OscillatorChainPhysicalDisc.lean)
LEAN_NOTE: landed main (B2, B3-CHAINK); generic over CertCoeff K
NOTE: models the polynomial/oscillator (B1-E) case only; torus/Fourier-Taylor expressions (L358-L371) are out of this closure; B1-E use: "included once a finite normal form is certified" (L197-L198) with L335-L337; divisor witnesses are listed as inputs (L319) but soundness checks the identities directly: an arbitrary generator is allowed (L317) and a bad one fails the inequality (L337) (owner ruling OD-B12)

NODE: b:4#model-identification
KIND: step
TITLE: Model identification: the checker's exact Q(sqrt 2) polynomial is the HH Hamiltonian, smooth on all of phase space
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:4-first-instance@L531-L537
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:3.1@L304-L310
CONTRACT_ID: b.step.hh-model
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Hexpr = I_1 - (sqrt 2/2) I_2 + q_1^2 q_2 - q_2^3/3 with exact coefficients in Q(sqrt 2) (supported algebraic constant)
SOURCE_QUANTIFIERS: w in Phase 2
SOURCE_CONCLUSION: the evaluation of Hexpr at w equals the displayed H(w) (q = w.1, p = w.2); H is a polynomial, hence C^2 on V = all of Phase 2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:defs#oscillatorAction, b:defs#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: b:defs#oscillatorAction | docs/explorations/program-b-plan.md#b:4-first-instance@L535-L535 | I_j = (q_j^2 + p_j^2)/2
EDGE: b:defs#hamiltonianVectorField | docs/tracks/B/FREEZE-PROPOSAL-HH.md#b:freeze-hh@L23-L26 | the inlined H whose field X_H is the solution field
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.HenonHeiles.hhH_eval (HenonHeiles/Eval.lean)
LEAN_NOTE: via algebraMap_qsqrt2_real (B3-COEF)
NOTE: "a polynomial that approximates a different H is a different model" (L308-L310); exact arithmetic over Q(sqrt 2) is the supported-constant case of L305

NODE: b:4#certificate-accepted
KIND: step
TITLE: The accepted HH certificate: checkNormalForm(HH, c) = true with the literals a_j = (81/10^6)^2, b_j = 10^-8, eta_j <= 10^-19, T = 10^10, d_j <= 10^-10
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:4-first-instance@L545-L553
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:3.1@L338-L340
CONTRACT_ID: b.step.hh-certificate
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the identified HH model; a finite certificate c in the normalized chart (L546; no rescaling of coordinates or time, §3.3 L418-L424 does not apply)
SOURCE_QUANTIFIERS: j = 1, 2; the finite data
SOURCE_CONCLUSION: checkNormalForm(HH, c) = true with a_j, b_j, eta_j, T, d_j (per j) for forward oscillator-action displacement on closed E_b and inverse displacement on the physical disc, and the initial-set inclusion of the physical disc in the inverse chart domain (L321)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:4#model-identification
ROUTES: -
ROUTE_FOR: -
EDGE: b:4#model-identification | docs/explorations/program-b-plan.md#b:4-first-instance@L546-L546 | the certificate is for the identified model, in its normalized chart
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.HenonHeiles.hhCert_check : checkOscChain hhCert = true (HenonHeiles/Check.lean)
LEAN_NOTE: decide +kernel in 34 shards (KAMHenonHeiles); eta = 1e-19, 3 steps
NOTE: computational leaf: a finite exact computation replayed in the kernel; producer untrusted (L338-L340); CL20's reported computation (L560-L566) only motivates the literals

NODE: b:4#inverse-chart
KIND: step
TITLE: Inverse chart on the physical disc: every physical z0 with I_j(z0) <= (1/12500)^2 equals Psi(w0) for w0 = Psiinv(z0) in the chart domain, with inverse action displacement <= d_j
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:2.2@L153-L155
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:4-first-instance@L553-L553
CONTRACT_ID: b.step.hh-inverse-chart
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the certified chart Psi with explicit inverse (reversed flows) defined on the physical disc; inverse displacement bound from the certificate
SOURCE_QUANTIFIERS: z0 with I_j(z0) <= (1/12500)^2
SOURCE_CONCLUSION: w0 = Psiinv(z0) lies in the chart domain, Psi(w0) = z0 and |I_j(w0) - I_j(z0)| <= d_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:3.2#chart-composition, b:4#certificate-accepted, b:3.1#checker-soundness, b:defs#oscillatorAction
ROUTES: -
ROUTE_FOR: -
EDGE: b:3.2#chart-composition | docs/explorations/program-b-plan.md#b:2.2@L153-L155 | "prove Q in Psi({...}) using the inverse chart"
EDGE: b:4#certificate-accepted | docs/explorations/program-b-plan.md#b:4-first-instance@L553-L553 | inverse displacement bound on the physical disc
EDGE: b:3.1#checker-soundness | docs/explorations/program-b-plan.md#b:3.1@L321-L321 | acceptance becomes the inverse displacement bound and initial-set inclusion on the actual chart
EDGE: b:defs#oscillatorAction | docs/explorations/program-b-plan.md#b:4-first-instance@L553-L553 | oscillator-action displacement
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes
LEAN_STATUS: PROVED
LEAN_REF: oscillatorChain_physical_disc (OscillatorChainPhysicalDisc.lean) via oscChainInv_sub_le and discPlane_sq_le
LEAN_NOTE: Lean route: coordinate tail + disc (OD-B18)
NOTE: L153-L155 is the torus-section requirement, applied by analogy to the oscillator chart. DEVIATION (OD-B18, B3-READY): the Lean route bounds the inverse chart by a coordinate displacement tail and the disc estimate (sigma + tail)^2 <= a (oscillatorChain_physical_disc) instead of the action displacement d_j

NODE: b:4#initial-inclusion
KIND: step
TITLE: Initial-set inclusion: physical actions <= (1/12500)^2 give chart actions <= a_j
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:4-first-instance@L555-L555
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:4-first-instance@L554-L555
CONTRACT_ID: b.step.hh-initial-inclusion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I_j(z0) <= (1/12500)^2; w0 = Psiinv(z0) with |I_j(w0) - I_j(z0)| <= d_j <= 10^-10
SOURCE_QUANTIFIERS: z0; j
SOURCE_CONCLUSION: I_j(w0) <= (1/12500)^2 + 10^-10 = 6.5e-9 < a_j = 6.561e-9
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:4#inverse-chart, b:defs#oscillatorAction
ROUTES: -
ROUTE_FOR: -
EDGE: b:4#inverse-chart | docs/explorations/program-b-plan.md#b:4-first-instance@L555-L555 | the inverse displacement d_j
EDGE: b:defs#oscillatorAction | docs/explorations/program-b-plan.md#b:4-first-instance@L540-L540 | I_j in the initial set
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.HenonHeiles.henonHeiles_confinement_proof (norm_num on the disc premises)
LEAN_NOTE: via the disc variant (OD-B18): (1/12500 + tail)^2 <= (81/10^6)^2, tail = 147597/2e12
NOTE: source inequality as stated; Lean route per the inverse-chart NOTE

NODE: b:2.3#transfer
KIND: corollary
TITLE: Oscillator observable transfer: |A_i(z(t)) - A_i(z0)| <= 2 d_i + |t| sum_j |L_ij| eta_j with L I in place of L J
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:2.3@L201-L201
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:2.2@L143-L150
CONTRACT_ID: b.cor.osc-transfer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z0 = Psi(w0) with I_j(w0) <= a_j; B1-E conclusion along w(t) = Psiinv(z(t)); static bound |A_i(Psi w) - (L I(w))_i| <= d_i on closed E_b
SOURCE_QUANTIFIERS: observable A, matrix L, d; t with |t| <= T
SOURCE_CONCLUSION: |A_i(z(t)) - A_i(z0)| <= 2 d_i + |t| sum_j |L_ij| eta_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:2.3#B1-E, b:defs#oscillatorAction
ROUTES: -
ROUTE_FOR: -
EDGE: b:2.3#B1-E | docs/explorations/program-b-plan.md#b:2.3@L201-L201 | confinement and drift of the chart actions
EDGE: b:defs#oscillatorAction | docs/explorations/program-b-plan.md#b:2.3@L201-L201 | L I uses the oscillator actions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.observable_transfer_bound (Transfer.lean); oscillatorChain_physical_core (OscillatorChainPhysical.lean)
LEAN_NOTE: landed main
NOTE: for HH: A = I (physical actions), L = id, d_i the forward action displacement

NODE: b:4#physical-bounds
KIND: step
TITLE: Physical output: I_j(z(t)) < b_j + d_j <= 101/10^10 and |I_j(z(t)) - I_j(z0)| <= 2 d_j + eta_j T <= 12/10^10
STATEMENT_SOURCE: docs/explorations/program-b-plan.md#b:4-first-instance@L556-L557
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:4-first-instance@L556-L557
CONTRACT_ID: b.step.hh-physical-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: chart confinement I_j(w(t)) <= a_j + eta_j T <= 7.561e-9 < b_j and chart drift <= eta_j |t| (B1-E via soundness), w(0) = w0 from the initial inclusion; forward action displacement <= d_j on closed E_b
SOURCE_QUANTIFIERS: z0, z(t) = Psi(w(t)); t with |t| <= T = 10^10; j
SOURCE_CONCLUSION: I_j(z(t)) < b_j + d_j <= 1.01e-8 = 101/10^10 and |I_j(z(t)) - I_j(z0)| <= 2 d_j + eta_j T <= 1.2e-9 = 12/10^10
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: b:3.1#checker-soundness, b:2.3#transfer, b:4#initial-inclusion, b:4#certificate-accepted, b:defs#oscillatorAction
ROUTES: -
ROUTE_FOR: -
EDGE: b:3.1#checker-soundness | docs/explorations/program-b-plan.md#b:4-first-instance@L556-L556 | chart confinement a_j + eta_j T < b_j
EDGE: b:2.3#transfer | docs/explorations/program-b-plan.md#b:4-first-instance@L557-L557 | 2 d_j + eta_j T is the transfer formula with A = I, L = id
EDGE: b:4#initial-inclusion | docs/explorations/program-b-plan.md#b:4-first-instance@L555-L557 | the chart solution starts in I(w0) <= a_j
EDGE: b:4#certificate-accepted | docs/explorations/program-b-plan.md#b:4-first-instance@L556-L557 | literals a, b, eta, T, d
EDGE: b:defs#oscillatorAction | docs/explorations/program-b-plan.md#b:4-first-instance@L557-L557 | physical actions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.HenonHeiles.henonHeiles_confinement_proof (KAM/EffectiveStability/HenonHeiles/Confinement.lean)
LEAN_NOTE: a + eta T + d = 7.58e-9 < 1.01e-8; 2d + eta T = 1.04e-9 <= 1.2e-9
NOTE: forward displacement only (z(t) = Psi(w(t))); the Lean route bounds I(z(t)) by a_j + eta_j T + d_j, which also gives < 101/10^10

NODE: b:4#HH
KIND: theorem
TITLE: Hénon–Heiles confinement (frozen henonHeiles_confinement)
STATEMENT_SOURCE: docs/tracks/B/FREEZE-PROPOSAL-HH.md#b:freeze-hh@L20-L36
PROOF_SOURCE: docs/explorations/program-b-plan.md#b:4-first-instance@L545-L559
CONTRACT_ID: effectiveStability.d73.henonHeiles_confinement
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z0 : Phase 2 with I_j(z0) <= (1/12500)^2 for j = 1, 2; H = I_1 - (sqrt 2/2) I_2 + q_1^2 q_2 - q_2^3/3 with q = z.1, p = z.2 (inlined)
SOURCE_QUANTIFIERS: for every z0 with the premise; then exists T1 > 10^10 and z
SOURCE_CONCLUSION: z(0) = z0 and z' = X_H(z) on Ioo(-T1,T1); every y with y(0) = z0 solving y' = X_H(y) on an order-connected I containing 0 equals z on I intersect Ioo(-T1,T1); for every |t| <= 10^10 and j: I_j(z(t)) < 101/10^10 and |I_j(z(t)) - I_j(z0)| <= 12/10^10
CONSTANT_SCOPE: all literals explicit; no unquantified constant
FROZEN_FILE: KAM/Frozen/EffectiveStability/HenonHeilesConfinement.lean
FROZEN_DECL: KAM.EffectiveStability.henonHeiles_confinement
FROZEN_ANCHOR_ID: effectiveStability.d73.henonHeiles_confinement.v1
FROZEN_ABI_SHA256: ecd0cc37042f3fbd267c8c113583f4e1ba70c7e974edc0ba299ce10f626295ea
DEPS: b:3.1#checker-soundness, b:4#certificate-accepted, b:4#model-identification, b:4#inverse-chart, b:4#physical-bounds, b:defs#hamiltonianVectorField, b:defs#oscillatorAction
ROUTES: -
ROUTE_FOR: -
EDGE: b:3.1#checker-soundness | docs/tracks/B/FREEZE-PROPOSAL-HH.md#b:freeze-hh@L22-L32 | existence past 10^10 and uniqueness from the sound checker
EDGE: b:4#certificate-accepted | docs/tracks/B/FREEZE-PROPOSAL-HH.md#b:freeze-hh@L22-L36 | the accepted HH certificate instantiates soundness with T = 10^10
EDGE: b:4#model-identification | docs/tracks/B/FREEZE-PROPOSAL-HH.md#b:freeze-hh@L23-L31 | the inlined H is the certified model, V = all of Phase 2
EDGE: b:4#inverse-chart | docs/tracks/B/FREEZE-PROPOSAL-HH.md#b:freeze-hh@L21-L22 | the solution starts at z0 = Psi(w0)
EDGE: b:4#physical-bounds | docs/tracks/B/FREEZE-PROPOSAL-HH.md#b:freeze-hh@L33-L36 | the two physical bounds
EDGE: b:defs#hamiltonianVectorField | docs/tracks/B/FREEZE-PROPOSAL-HH.md#b:freeze-hh@L23-L26 | HasDerivAt z (X_H (z t))
EDGE: b:defs#oscillatorAction | docs/tracks/B/FREEZE-PROPOSAL-HH.md#b:freeze-hh@L21-L36 | oscillator actions in the premise (L21) and the conclusion (L33-L36)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes
LEAN_STATUS: PROVED
LEAN_REF: KAM.EffectiveStability.henonHeiles_confinement (KAM/Frozen/EffectiveStability/HenonHeilesConfinement.lean); provider KAM.Provider.EffectiveStability.henonHeiles_confinement
LEAN_NOTE: SEALED (D73, manifest effectiveStability.d73.henonHeiles_confinement.v1, main 95387f9b0); seal audit HH-1 PASS WITH NOTES; standard axioms; library KAMHenonHeiles; T2-CONF (D74-D76) packages KAM/EffectiveStability/Tube/* (core) and KAM/EffectiveStability/SJSU/* (library KAMSJSU) landed on main a9e07eb24 (18:17 UTC 06 Nov) and after, outside the B root closure; no node change (T2-CONF gets its own graph at its freeze)
NOTE: statement source = exact frozen text (FREEZE-PROPOSAL-HH, owner D73); mathematical target plan §4 L539-L543; plan-to-freeze: "unique solution through |t| <= 10^10" is stated in the §2.1 form (open Ioo(-T1,T1), T1 > 10^10, uniqueness on order-connected intervals through 0); library KAMHenonHeiles

## Append-only structural amendments

(none)

<!-- BEGIN PROOF DEPGRAPH GENERATED -->
Regenerated by `proof_depgraph.py`; do not hand-edit.

### Dashboard

* Total nodes: **30**
* Frozen anchors: **6**
* Versioned statement contracts: **30**
* Total edges: **81**
* Root-closure nodes: **30**
* Dependency leaves in root closure: **7**
* Assumption boundary leaves: **0**
* External boundary leaves: **3**
* Alternative routes: **0**
* Topology review queue: **0**
* Explicit source gaps: **0**
* Coverage items: **43**; excluded: **15**

### Roots

* `b:2.2#B1-T` [REVIEWED; frozen] — contract `effectiveStability.d72.torus_confinement@1`
* `b:2.3#B1-E` [REVIEWED; frozen] — contract `effectiveStability.d72.oscillator_confinement@1`
* `b:4#HH` [REVIEWED; frozen] — contract `effectiveStability.d73.henonHeiles_confinement@1`

### Topology review queue

* _(none)_

### Dependency leaves in root closure

* `b:brief2#stopped-drift` [REVIEWED] — Stopped drift: a scalar derivative bound |f'| <= eta on an interval containing 0 gives |f(t) - f(0)| <= eta |t| in both time directions
* `b:defs#hamiltonianVectorField` [REVIEWED] — Hamiltonian vector field X_H = (dH/dJ, -dH/dphi)
* `b:defs#oscillatorAction` [REVIEWED] — Oscillator actions I_j(q,p) = (q_j^2 + p_j^2)/2
* `b:defs#symplecticForm` [REVIEWED] — Repository symplectic form
* `ext:analysis#cauchy` [REVIEWED] — Cauchy estimate: a holomorphic function bounded by E on a polydisc with margins delta has first derivatives bounded by E/delta on the inner set
* `ext:ode#compact-continuation` [REVIEWED] — Continuation: a solution confined to a compact subset of the open domain of a C^1 field extends past both ends of a bounded interval
* `ext:ode#local` [REVIEWED] — Local existence and uniqueness for C^1 (locally Lipschitz) vector fields (Picard-Lindelof)

### Assumption boundary leaves

* _(none)_

### External boundary leaves

* `ext:analysis#cauchy` [REVIEWED] — Cauchy estimate: a holomorphic function bounded by E on a polydisc with margins delta has first derivatives bounded by E/delta on the inner set
* `ext:ode#compact-continuation` [REVIEWED] — Continuation: a solution confined to a compact subset of the open domain of a C^1 field extends past both ends of a bounded interval
* `ext:ode#local` [REVIEWED] — Local existence and uniqueness for C^1 (locally Lipschitz) vector fields (Picard-Lindelof)

### Uncovered graph nodes

* _(none)_

### Nodes outside every root closure

* _(none)_

### Explicit source gaps

* _(none)_
<!-- END PROOF DEPGRAPH GENERATED -->
