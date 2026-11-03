# Proof dependency database — track B (program B: effective stability, B1-T / B1-E)

GRAPH_VERSION: 4
ROOTS: b:2.2#B1-T, b:2.3#B1-E
CORPUS: docs/explorations/program-b-plan.md (§2.1–2.3 L66–L206, Brief 2 L833–L870) and docs/tracks/B/FREEZE-PROPOSAL.md (§2 exact frozen text L17–L99, §6 deviations L161–L166), pinned by SHA-256 in docs/graph/B/CORPUS.sha256 (main 6ecfdbddc, 2026-11-03)
CONVENTIONS: Phase n = (Fin n -> R) x (Fin n -> R); max norm; X_H = (partial_J H, -partial_phi H); symplecticForm(v,w) = sum_j (v.2 j w.1 j - v.1 j w.2 j); solutions on an open interval containing [-T,T], unique on interval intersections, bounds for every |t| <= T (plan §2.1); action margins are b_j - a_j in actions (squared radii) for B1-E; bracket {F,G} = sum_j (F_phi G_J - F_J G_phi) (plan L79-L82); B1-E coordinates w = (q,p) with I_j = oscillatorAction w.2 w.1; root statement fields follow the exact frozen text, plan premises are provenance (FREEZE-PROPOSAL §6)
STANDING_ASSUMPTIONS: -
EXTERNAL_POLICY: Mathlib-level ODE inputs (local existence/uniqueness, compact continuation) are KIND external nodes ext:ode#*; cited GLS17/CL20 derivations are reproduced in the plan and are provenance, not external inputs
FROZEN_ANCHORS: b:defs#hamiltonianVectorField, b:defs#symplecticForm, b:defs#oscillatorAction, b:2.2#B1-T, b:2.3#B1-E
FROZEN_MANIFEST: manifest/frozen-anchors.json | sha256:fd93ee6b8a686eb4fbd6ee6f8332c437ec230aa41bffebacb8cfb7be77aeb45a
WRITER: kam-b1
GLOBAL_REVIEWER: sonnet-global-B
GLOBAL_REVIEW_REF: docs/graph/B/reviews/GLOBAL-review.md and docs/graph/B/reviews/GLOBAL-recheck.md (fresh Sonnet, ACCEPT WITH FINDINGS; findings applied); node review docs/graph/B/reviews/NODE-review.md

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
LEAN_NOTE: SEALED (D72, manifest effectiveStability.d72.oscillator_confinement.v1, main cff2accd5); seal audit 1 PASS WITH NOTES; standard axioms; consumers: oscillator step/chain checker stack generic over CertCoeff K and oscillatorChain_physical_disc (B3-CHAINK, track B batch 17); literal application KAM.EffectiveStability.henonHeiles_confinement (D73, SEALED, library KAMHenonHeiles) uses the oscillator checker route, not this anchor (not yet a graph root)
NOTE: statement source = exact frozen text (FREEZE-PROPOSAL §2, owner D72); mathematical source plan §2.3 L165-L193; deviations in FREEZE-PROPOSAL §6 L161-L166

## Append-only structural amendments

(none)

<!-- BEGIN PROOF DEPGRAPH GENERATED -->
Regenerated by `proof_depgraph.py`; do not hand-edit.

### Dashboard

* Total nodes: **18**
* Frozen anchors: **5**
* Versioned statement contracts: **18**
* Total edges: **43**
* Root-closure nodes: **18**
* Dependency leaves in root closure: **6**
* Assumption boundary leaves: **0**
* External boundary leaves: **2**
* Alternative routes: **0**
* Topology review queue: **0**
* Explicit source gaps: **0**
* Coverage items: **22**; excluded: **8**

### Roots

* `b:2.2#B1-T` [REVIEWED; frozen] — contract `effectiveStability.d72.torus_confinement@1`
* `b:2.3#B1-E` [REVIEWED; frozen] — contract `effectiveStability.d72.oscillator_confinement@1`

### Topology review queue

* _(none)_

### Dependency leaves in root closure

* `b:brief2#stopped-drift` [REVIEWED] — Stopped drift: a scalar derivative bound |f'| <= eta on an interval containing 0 gives |f(t) - f(0)| <= eta |t| in both time directions
* `b:defs#hamiltonianVectorField` [REVIEWED] — Hamiltonian vector field X_H = (dH/dJ, -dH/dphi)
* `b:defs#oscillatorAction` [REVIEWED] — Oscillator actions I_j(q,p) = (q_j^2 + p_j^2)/2
* `b:defs#symplecticForm` [REVIEWED] — Repository symplectic form
* `ext:ode#compact-continuation` [REVIEWED] — Continuation: a solution confined to a compact subset of the open domain of a C^1 field extends past both ends of a bounded interval
* `ext:ode#local` [REVIEWED] — Local existence and uniqueness for C^1 (locally Lipschitz) vector fields (Picard-Lindelof)

### Assumption boundary leaves

* _(none)_

### External boundary leaves

* `ext:ode#compact-continuation` [REVIEWED] — Continuation: a solution confined to a compact subset of the open domain of a C^1 field extends past both ends of a bounded interval
* `ext:ode#local` [REVIEWED] — Local existence and uniqueness for C^1 (locally Lipschitz) vector fields (Picard-Lindelof)

### Uncovered graph nodes

* _(none)_

### Nodes outside every root closure

* _(none)_

### Explicit source gaps

* _(none)_
<!-- END PROOF DEPGRAPH GENERATED -->
