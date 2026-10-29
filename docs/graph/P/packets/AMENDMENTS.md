AMEND: P-A001-ext-closure-agreement
TARGET: bpP:p5:ext
AUTHOR: claude-inp-sub-orchestrator
REVIEWER: root-bb-ruling-OVERNIGHT-0120
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: -
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: there are delta_c in (0,1), M_P < infinity and P~: [0,mu_0] x X_{delta_c} -> C with P~(mu,.) holomorphic, P~ = P at real points of the closed cylinder cl C(V, r0), P~ periodic under 2 pi k e_f (fast angles), ¦P~¦ <= M_P, P~ jointly continuous in mu; and H~_0 holomorphic on {I: dist(I, closure V) < delta_c} with ¦H~_0¦, ¦dH~_0¦, ¦d^2 H~_0¦ <= M_0
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: ERRATUM (logged for owner review, ruling OVERNIGHT 01:20): the printed clause "P~ = P at real points" (all of X_{delta_c}) is false; P45 design revision 4 and the P5-EX audit give a counterexample. Agreement holds on cl C(V, r0), which is all any consumer uses.

AMEND: P-A002-prin-constant-scope
TARGET: stepP:p11:pr-in
AUTHOR: claude-inp-sub-orchestrator
REVIEWER: root-bb-ruling-OVERNIGHT-0145
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: -
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: the constant c in (i)-(iii) may depend on n, tau, the fixed data and the derivative multi-index orders |alpha|, |beta|, |gamma|, and is chosen before eps; consumers use finitely many orders bounded in terms of mu (blueprint p11-cp09-preparation.tex:209-211)
SET_ROUTE_FOR: -
NOTE: Constant-scope clarification (orchestrator ruling OVERNIGHT 01:45, logged for owner review; audit P11A-P8b-audit-2 finding F2). The Lean exports state forall beta, exists c, before eps, which meets this scope.

AMEND: P-A003-remain-clause-1
TARGET: bpP:p11b:remain
AUTHOR: claude-inp-sub-orchestrator
REVIEWER: root-bb-survey-GAP-PLAN-P2
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: -
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: B:=min over K_a of ¦det beta-hat¦>0 satisfies htorsion (det beta-hat is continuous and nonzero on the compact K_a)
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Cut to clause (1) (option chosen under root-bb's second gap survey, item 6; logged for owner review). The dropped clause (2) is a remark listing Part 12 tasks (joint analyticity near the cylinder closure, extension, hperiod, fast diffeomorphism, collar) and the n=2/P-FIXED reuse of P_0, Omega, beta-hat; those are discharged by the P12/P13 assembly nodes, not by this claim.
