NODE: bpN:p3:ext-pl
KIND: external
TITLE: Picard--Lindel\"of, quantitative form
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ext-pl@L32-L40
PROOF_SOURCE: -
CONTRACT_ID: bpN:p3:ext-pl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F : E → E; x ∈ E; a, M, L ≥ 0 with ¦F(y)¦ ≤ M and F L-Lipschitz on the closed ball B̄(x,a); T ≥ 0 with MT ≤ a (E finite-dimensional real normed space)
SOURCE_QUANTIFIERS: E; F; x; a, M, L; T; t₀ (t₀ is not introduced in the text, read as arbitrary in ℝ)
SOURCE_CONCLUSION: there is α : ℝ → E with α(t₀) = x and α has derivative F(α(t)) within [t₀−T, t₀+T] at each t of that interval
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a
REVIEWER: sol-review-N-c
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external fact E1 (Mathlib IsPicardLindelof with r = 0); the text writes '¦F(y)¦ ≤ M' without saying y ∈ B̄(x,a) and uses t₀ without introducing it (reported)

NODE: bpN:p3:ext-unique
KIND: external
TITLE: Uniqueness with a Lipschitz constant on a set
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ext-unique@L41-L45
PROOF_SOURCE: -
CONTRACT_ID: bpN:p3:ext-unique
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: S ⊂ E; F L-Lipschitz on S; f, g : [a,b] → E continuous with right derivatives F(f(t)), F(g(t)) on [a,b), values in S, f(a) = g(a)
SOURCE_QUANTIFIERS: E; S; F; L; a ≤ b; f, g
SOURCE_CONCLUSION: f = g on [a,b]; mirror statement with f(b) = g(b) and left derivatives
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a
REVIEWER: sol-review-N-c
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external fact E2 (Mathlib ODE_solution_unique_of_mem_Icc_right/left)

NODE: bpN:p3:ext-lip-local
KIND: external
TITLE: $C^1$ implies locally Lipschitz
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ext-lip-local@L46-L49
PROOF_SOURCE: -
CONTRACT_ID: bpN:p3:ext-lip-local
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F C¹ at p (first sentence); F locally Lipschitz on a compact set (second sentence)
SOURCE_QUANTIFIERS: F; p; then L and a neighbourhood depending on p; compact set
SOURCE_CONCLUSION: there are L and a neighbourhood of p on which F is L-Lipschitz; a function locally Lipschitz on a compact set is Lipschitz there
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a
REVIEWER: sol-review-N-c
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external fact E3; stays an external (SPEC decision): its \ref to Lemma gen-lip is a pointer to a related statement, not a restatement

NODE: bpN:p3:ext-compact
KIND: external
TITLE: Topology
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ext-compact@L53-L57
PROOF_SOURCE: -
CONTRACT_ID: bpN:p3:ext-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; A ⊂ E nonempty closed (for the distance statement)
SOURCE_QUANTIFIERS: E; compact sets and sequences; A
SOURCE_CONCLUSION: Heine-Borel in E; continuous images of compact sets are compact; sequential compactness; x ↦ dist(x,A) continuous and positive exactly on E∖A for nonempty closed A; thickenings K_δ = {y : ∃x∈K, ¦y−x¦ ≤ δ}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a
REVIEWER: sol-review-N-c
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external fact E5 (topology)

NODE: bpN:p3:ext-calc
KIND: external
TITLE: Calculus
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ext-calc@L58-L62
PROOF_SOURCE: -
CONTRACT_ID: bpN:p3:ext-calc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: chain rule data; f continuous on [s,t] with right derivative 0 on [s,t); one-sided derivatives at a point; H C^{k+1} on an open set
SOURCE_QUANTIFIERS: functions; s < t; k
SOURCE_CONCLUSION: chain rule HasFDerivAt.comp_hasDerivAt; f constant on [s,t]; two one-sided derivatives agreeing give a two-sided one; ContDiffOn.fderiv_of_isOpen: H C^{k+1} on an open set gives DH C^k there
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a
REVIEWER: sol-review-N-c
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external fact E6 (calculus)

NODE: bpN:p3:gen-sol
KIND: definition
TITLE: Solutions in $W$
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-sol@L88-L93
PROOF_SOURCE: -
CONTRACT_ID: bpN:p3:gen-sol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F : E → E; W ⊂ E; J ⊂ ℝ; z : ℝ → E (§s-conv conventions: E finite-dimensional real normed space; F : E → E total; W ⊂ E open; 'C¹ on W' = ContDiffOn ℝ 1 F W; intervals are order-connected; derivatives two-sided)
SOURCE_QUANTIFIERS: E; F; W; J; z
SOURCE_CONCLUSION: defines IsSolIn F W J z: for every t ∈ J, z(t) ∈ W and z has derivative F(z(t)) at t (two-sided HasDerivAt, including endpoints of J)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.IsSolutionIn (KAM/ODE/Basic.lean)
LEAN_NOTE: definition formalized; audit N3-1 PASS
NOTE: package for the general layer; the conventions paragraph prose-L15-L26 is recorded in the source fields (E, two-sided derivative); suggested Lean name KAM.ODE.IsSolutionIn (not a frozen declaration)

NODE: bpN:p3:gen-sol#consequences
KIND: claim
TITLE: Elementary consequences of IsSolIn
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-sol@L95-L99
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-sol@L95-L99
CONTRACT_ID: bpN:p3:gen-sol#consequences
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing F:E->E, W subset E, J,Jprime subset R, z,y:R->E; (i),(ii): IsSolIn F W J z; (i): Jprime subset J; (iii): Jprime open and z=y on Jprime
SOURCE_QUANTIFIERS: F,W,J,z; (i) every Jprime subset J; (ii) all t in J; independently (iii) every open Jprime and y,z agreeing there
SOURCE_CONCLUSION: (i) IsSolIn F W J' z (restriction); (ii) z is continuous on J; (iii) local nature: for open J' with z = y on J', IsSolIn F W J' y ⇔ IsSolIn F W J' z
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-sol, bpN:p3:ext-calc
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-sol#consequences@L95-L95 | elementary consequences of the predicate IsSolIn
EDGE: bpN:p3:ext-calc | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-sol#consequences@L95-L95 | each a one-line Lean lemma, from the calculus facts (differentiable implies continuous; derivative at a point depends only on a neighbourhood)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.IsSolutionIn.mono, KAM.ODE.IsSolutionIn.continuousOn, KAM.ODE.isSolutionIn_congr_of_isOpen (KAM/ODE/Basic.lean)
LEAN_NOTE: (i)-(iii); audit N3-1 PASS
NOTE: section-data claim for coverage item p3:prose-L95-L99; statement and proof are the same unlabelled paragraph; consumers: short-boot, short-ext, uq-compact, ext-right, max-glue, cont-glue, exit-closed, exit-bdry

NODE: bpN:p3:gen-symmetry
KIND: lemma
TITLE: Symmetries
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-symmetry@L101-L110
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-symmetry@L111-L114
CONTRACT_ID: bpN:p3:gen-symmetry
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: IsSolIn F W J z; (a) c ∈ ℝ; (b) F C¹ on W for the second clause; (c) v ∈ E with W + v = W and F(x+v) = F(x) for x ∈ W
SOURCE_QUANTIFIERS: E; F; W; J; z; then c, resp. v
SOURCE_CONCLUSION: (a) t ↦ z(t+c) is a solution on J−c; (b) t ↦ z(−t) is a solution of −F on −J, and −F is C¹ on W if F is; (c) t ↦ z(t)+v is a solution of F in W on J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-sol, stepN:p3:sym
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-symmetry@L102-L102 | hypothesis IsSolIn F W J z and conclusion about solutions
EDGE: stepN:p3:sym | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-symmetry@L112-L112 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_symmetry, KAM.ODE.gen_symmetry_shift, KAM.ODE.gen_symmetry_neg, KAM.ODE.gen_symmetry_neg_contDiffOn, KAM.ODE.gen_symmetry_translate (KAM/ODE/Basic.lean)
LEAN_NOTE: (a)(b)(c); audit N3-1 PASS
NOTE: -

NODE: stepN:p3:sym
KIND: step
TITLE: Chain rule
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:sym@L112-L113
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:sym@L112-L113
CONTRACT_ID: stepN:p3:sym
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: IsSolIn F W J z; c in R for (a); for (c) v in E, W+v=W and F(x+v)=F(x) for x in W; the C1 assertion in (b) is conditional on F being C1, not a premise for time reversal
SOURCE_QUANTIFIERS: as gen-symmetry
SOURCE_CONCLUSION: (a), (b) by the chain rule for t ↦ t+c, t ↦ −t; (c) z+v has derivative F(z(t)) = F(z(t)+v) and z(t)+v ∈ W+v = W
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:ext-calc, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:ext-calc | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:sym@L112-L112 | chain rule for t ↦ t+c and t ↦ −t
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:sym@L113-L113 | membership in W and derivative of the solution
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_symmetry (KAM/ODE/Basic.lean)
LEAN_NOTE: proved inside parent gen_symmetry (chain rule); audit N3-1 PASS
NOTE: -

NODE: bpN:p3:gen-lip
KIND: lemma
TITLE: Bounds and Lipschitz constants on compact sets
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-lip@L116-L120
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-lip@L121-L134
CONTRACT_ID: bpN:p3:gen-lip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F C¹ on the open set W ⊂ E; K ⊂ W compact
SOURCE_QUANTIFIERS: E; W; F; K; then M and L
SOURCE_CONCLUSION: F is bounded on K, and there is L ≥ 0 with ¦F(x)−F(y)¦ ≤ L¦x−y¦ for x, y ∈ K
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:lip-bdd
ROUTES: stepN:p3:lip-mathlib, stepN:p3:lip-explicit
ROUTE_FOR: -
EDGE: stepN:p3:lip-bdd | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-lip@L124-L124 | boundedness of F on K (common to both routes)
EDGE: stepN:p3:lip-mathlib | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-lip@L122-L122 | route (i): via Mathlib (locally Lipschitz on compact set)
EDGE: stepN:p3:lip-explicit | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-lip@L124-L124 | route (ii): explanatory proof by contradiction and compactness ('Alternatively')
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_lip (KAM/ODE/Lipschitz.lean)
LEAN_NOTE: audit N3-1 PASS
NOTE: 'Alternatively' at L122 makes the Mathlib route and the explanatory proof two alternative routes for the Lipschitz clause; the bound is shared

NODE: stepN:p3:lip-mathlib
KIND: route
TITLE: Via Mathlib
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-mathlib@L122-L122
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-mathlib@L122-L122
CONTRACT_ID: stepN:p3:lip-mathlib
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F C¹ on W open; K ⊂ W compact
SOURCE_QUANTIFIERS: as gen-lip
SOURCE_CONCLUSION: F is locally Lipschitz at every point of W, hence on K, and LocallyLipschitzOn.exists_lipschitzOnWith_of_compact gives L
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:ext-lip-local
ROUTES: -
ROUTE_FOR: bpN:p3:gen-lip
EDGE: bpN:p3:ext-lip-local | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-mathlib@L122-L122 | C¹ implies locally Lipschitz; locally Lipschitz on a compact set is Lipschitz
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_lip (KAM/ODE/Lipschitz.lean)
LEAN_NOTE: Route taken by gen_lip (Lipschitz.lean L35-45: LocallyLipschitzOn from ContDiffAt.exists_lipschitzOnWith, then LocallyLipschitzOn.exists_lipschitzOnWith_of_compact). Audit N3-1-audit-1.md L42 (PASS) and refute-first item 4 at L105.
NOTE: -

NODE: stepN:p3:lip-explicit
KIND: route
TITLE: Explanatory proof of the Lipschitz clause
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-explicit@L124-L133
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-explicit@L124-L133
CONTRACT_ID: stepN:p3:lip-explicit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F C¹ on W open; K ⊂ W compact
SOURCE_QUANTIFIERS: as gen-lip
SOURCE_CONCLUSION: there exists L>=0 such that abs(F(x)-F(y))<=L abs(x-y) for all x,y in K; proved by contradiction using the boundedness step and a compact subsequence
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:lip-contra, stepN:p3:lip-compact
ROUTES: -
ROUTE_FOR: bpN:p3:gen-lip
EDGE: stepN:p3:lip-contra | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-explicit@L126-L126 | if no L works, sequences x_k, y_k with the Lipschitz quotient > k
EDGE: stepN:p3:lip-compact | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-explicit@L130-L130 | convergent subsequence and local Lipschitz constant contradict
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: BYPASSED
LEAN_REF: KAM.ODE.gen_lip (KAM/ODE/Lipschitz.lean)
LEAN_NOTE: Explicit contradiction/subsequence route is not taken; gen_lip (KAM/ODE/Lipschitz.lean L35-45, audit N3-1-audit-1.md L42,L105) uses the Mathlib route stepN:p3:lip-mathlib.
NOTE: new route node: the remaining steps lip-bdd..lip-compact of Lemma gen-lip ('The remaining steps are the explanatory proof of that fact', L122); lip-bdd is shared with the other route; STATEMENT/PROOF_SOURCE are L124-L133

NODE: stepN:p3:lip-bdd
KIND: step
TITLE: Bounded
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-bdd@L124-L124
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-bdd@L124-L124
CONTRACT_ID: stepN:p3:lip-bdd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; K subset W compact
SOURCE_QUANTIFIERS: E,W,F,K fixed as in gen-lip; then there exists M>=0
SOURCE_CONCLUSION: ¦F¦ ≤ M on the compact set K
CONSTANT_SCOPE: M is chosen after F,W,K; no uniform numerical bound over later F is asserted
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:ext-compact
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:ext-compact | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-bdd@L124-L124 | continuous image of a compact set is bounded
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_lip (KAM/ODE/Lipschitz.lean)
LEAN_NOTE: Bound |F|<=M on compact K proved verbatim by IsCompact.exists_bound_of_continuousOn with max C 0 (Lipschitz.lean L40-42); audit N3-1-audit-1.md L42 and refute-first item 4 (L105).
NOTE: -

NODE: stepN:p3:lip-contra
KIND: step
TITLE: Contradiction hypothesis
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-contra@L126-L128
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-contra@L126-L128
CONTRACT_ID: stepN:p3:lip-contra
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; K subset W compact; contradiction branch: no L>=0 satisfies the Lipschitz inequality on K; M denotes the bound constructed by lip-bdd (not a newly assumed boundedness premise)
SOURCE_QUANTIFIERS: F,W,K fixed; choose M by lip-bdd; for every integer k>=1 choose x_k,y_k in K with x_k!=y_k
SOURCE_CONCLUSION: for every k there are x_k ≠ y_k ∈ K with ¦F(x_k)−F(y_k)¦ > k¦x_k−y_k¦, hence ¦x_k−y_k¦ < 2M/k → 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:lip-bdd
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p3:lip-bdd | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-contra@L128-L128 | the bound M gives ¦x_k−y_k¦ < 2M/k
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-delta-N-c
REVIEWER: sol-delta2-N-c
LEAN_STATUS: BYPASSED
LEAN_REF: KAM.ODE.gen_lip (KAM/ODE/Lipschitz.lean)
LEAN_NOTE: Step belongs only to the explicit contradiction route; the route actually taken is stepN:p3:lip-mathlib inside KAM.ODE.gen_lip (Lipschitz.lean L35-45; audit N3-1-audit-1.md L105).
NOTE: -

NODE: stepN:p3:lip-compact
KIND: step
TITLE: Compactness
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-compact@L130-L133
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-compact@L130-L133
CONTRACT_ID: stepN:p3:lip-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; K subset W compact; contradiction branch of lip-contra; x_k,y_k denote the sequences constructed there, not additional compactness or local-Lipschitz assumptions
SOURCE_QUANTIFIERS: data of gen-lip and the contradiction sequences; then a strictly increasing subsequence k_j, limit p in K, and L_p and a neighborhood N_p of p; finally sufficiently large j
SOURCE_CONCLUSION: a subsequence x_{k_j} → p ∈ K and y_{k_j} → p; for large j both lie in the L_p-Lipschitz neighbourhood N_p and k_j > L_p, contradicting lip-contra
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:ext-compact, bpN:p3:ext-lip-local, stepN:p3:lip-contra
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:ext-compact | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-compact@L131-L131 | sequential compactness produces a subsequence converging to p in K
EDGE: bpN:p3:ext-lip-local | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-compact@L131-L131 | C1 at the chosen limit p supplies L_p and its neighborhood
EDGE: stepN:p3:lip-contra | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:lip-compact@L132-L132 | contradiction with the choice of x_k, y_k
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: BYPASSED
LEAN_REF: KAM.ODE.gen_lip (KAM/ODE/Lipschitz.lean)
LEAN_NOTE: Step belongs only to the explicit contradiction route; the route actually taken is stepN:p3:lip-mathlib (compact local-to-global Lipschitz theorem of Mathlib) inside KAM.ODE.gen_lip (Lipschitz.lean L43-44).
NOTE: -

NODE: bpN:p3:gen-uniform
KIND: definition
TITLE: Uniform data
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniform@L136-L141
PROOF_SOURCE: -
CONTRACT_ID: bpN:p3:gen-uniform
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F C¹ on the open set W; Φ ⊂ E; δ > 0; M, L ≥ 0 (§s-conv conventions: E finite-dimensional real normed space; F : E → E total; W ⊂ E open; 'C¹ on W' = ContDiffOn ℝ 1 F W; intervals are order-connected; derivatives two-sided)
SOURCE_QUANTIFIERS: E; W; F; Φ; δ, M, L
SOURCE_CONCLUSION: defines 'Φ has uniform data (δ,M,L)': for every x ∈ Φ, B̄(x,δ) ⊂ W, ¦F¦ ≤ M on B̄(x,δ) and F is L-Lipschitz on B̄(x,δ)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.UniformData (KAM/ODE/Lipschitz.lean)
LEAN_NOTE: definition formalized; audit N3-1 PASS
NOTE: package for continuation results, Part 7 transfer and Part 11c; the parenthetical via ext-mvt (gradient bound gives Lipschitz clause) is an aside, not used

NODE: bpN:p3:gen-uniform-compact
KIND: lemma
TITLE: Compact sets have uniform data
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniform-compact@L143-L146
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniform-compact@L147-L154
CONTRACT_ID: bpN:p3:gen-uniform-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F C¹ on the open set W; K ⊂ W compact; uniform data of bpN:p3:gen-uniform
SOURCE_QUANTIFIERS: E; W; F; K; then δ > 0, M, L
SOURCE_CONCLUSION: K has uniform data (δ,M,L) for some δ > 0, and K_δ = {y : ∃x∈K, ¦y−x¦ ≤ δ} ⊂ W is compact
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-uniform, stepN:p3:uc-delta, stepN:p3:uc-data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniform-compact@L144-L144 | conclusion is uniform data
EDGE: stepN:p3:uc-delta | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniform-compact@L148-L148 | choice of δ and compactness of K_δ
EDGE: stepN:p3:uc-data | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniform-compact@L153-L153 | constants M, L on K_δ
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_uniform_compact, KAM.ODE.closedThickening (KAM/ODE/Lipschitz.lean)
LEAN_NOTE: audit N3-1 PASS
NOTE: -

NODE: stepN:p3:uc-delta
KIND: step
TITLE: Choice of $\delta$
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uc-delta@L148-L151
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uc-delta@L148-L151
CONTRACT_ID: stepN:p3:uc-delta
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K ⊂ W compact, W open
SOURCE_QUANTIFIERS: case split K = ∅, W = E, otherwise; δ
SOURCE_CONCLUSION: δ > 0 with K_δ ⊂ W (δ = 1 if K = ∅ or W = E; else 2δ = min of dist(·, E∖W) on K) and K_δ compact (image of K × B̄(0,δ) under addition)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:ext-compact
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:ext-compact | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uc-delta@L149-L149 | dist(·,A) continuous and positive on K, minimum on compact K, image of compact set
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_uniform_compact, KAM.ODE.closedThickening (KAM/ODE/Lipschitz.lean)
LEAN_NOTE: Lipschitz.lean L61-68: delta>0 from IsCompact.exists_cthickening_subset_open, closedThickening K delta = cthickening, hence inside W and compact (ProperSpace). Same conclusion by Mathlib instead of the explicit 2delta=min dist construction. Audit N3-1-audit-1.md L45 and refute-first item 5 (L106).
NOTE: -

NODE: stepN:p3:uc-data
KIND: step
TITLE: Data
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uc-data@L153-L153
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uc-data@L153-L153
CONTRACT_ID: stepN:p3:uc-data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; K subset W compact; delta and K_delta={y:exists x in K, abs(y-x)<=delta} are the objects chosen in uc-delta; their compactness and containment are proved there
SOURCE_QUANTIFIERS: F,W,K fixed as in gen-uniform-compact; delta,K_delta constructed by uc-delta; then choose M,L>=0 on K_delta by gen-lip; finally every x in K
SOURCE_CONCLUSION: ¦F¦ ≤ M and F L-Lipschitz on K_δ ⊃ B̄(x,δ) for x ∈ K
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-lip, stepN:p3:uc-delta, bpN:p3:gen-uniform
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-lip | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uc-data@L153-L153 | bound and Lipschitz constant on the compact set K_δ
EDGE: stepN:p3:uc-delta | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uc-data@L153-L153 | K_δ ⊂ W compact
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uc-data@L153-L153 | the resulting bounds on every closedBall(x,delta) supply the three uniform-data clauses
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_uniform_compact (KAM/ODE/Lipschitz.lean)
LEAN_NOTE: Lipschitz.lean L69-73: gen_lip applied to the compact thickening, every centre ball included in it. Audit N3-1-audit-1.md L45 and item 5 (L106).
NOTE: -

NODE: bpN:p3:gen-uniform-periodic
KIND: lemma
TITLE: Uniform data for angle-periodic fields
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniform-periodic@L156-L160
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniform-periodic@L161-L169
CONTRACT_ID: bpN:p3:gen-uniform-periodic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E = ℝⁿ × ℝⁿ with max norm; U ⊂ ℝⁿ open; W = ℝⁿ × U; F C¹ on W with F(θ+k,I) = F(θ,I) for (θ,I) ∈ W, k ∈ ℤⁿ; K ⊂ U compact
SOURCE_QUANTIFIERS: n; U; F; K; then δ ∈ (0,1], M, L
SOURCE_CONCLUSION: Φ = ℝⁿ × K has uniform data (δ,M,L) for some δ ∈ (0,1]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-uniform, stepN:p3:up-cell, stepN:p3:up-translate
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniform-periodic@L157-L157 | conclusion is uniform data
EDGE: stepN:p3:up-cell | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniform-periodic@L162-L162 | choice of δ and compact cell C
EDGE: stepN:p3:up-translate | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniform-periodic@L166-L166 | translation of balls into the cell
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_uniform_periodic (KAM/ODE/UniformPeriodic.lean)
LEAN_NOTE: audit N3-63 PASS WITH NOTES
NOTE: -

NODE: stepN:p3:up-cell
KIND: step
TITLE: A compact cell
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:up-cell@L162-L164
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:up-cell@L162-L164
CONTRACT_ID: stepN:p3:up-cell
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E=R^n x R^n with max norm; U subset R^n open; W=R^n x U; F C1 on W and integer-periodic in angles; K subset U compact
SOURCE_QUANTIFIERS: n,U,F,K fixed as in gen-uniform-periodic; split K empty or not; choose delta in (0,1]; define K_delta,C=[-1,2]^n x K_delta; then choose M,L_C>=0 on C
SOURCE_CONCLUSION: δ ∈ (0,1] with K_δ ⊂ U; C = [−1,2]ⁿ × K_δ compact ⊂ W; constants M, L_C of F on C
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:uc-delta, bpN:p3:ext-compact, bpN:p3:gen-lip, bpN:p3:gen-uniform
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p3:uc-delta | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:up-cell@L162-L163 | choose the action collar by the earlier compact-neighborhood construction, handling K empty and U=R^n
EDGE: bpN:p3:ext-compact | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:up-cell@L163-L163 | compactness of C
EDGE: bpN:p3:gen-lip | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:up-cell@L164-L164 | M and L_C on the compact C
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:up-cell@L162-L162 | empty-K branch: the uniform-data conditions are vacuous
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_uniform_periodic (KAM/ODE/UniformPeriodic.lean)
LEAN_NOTE: Compact cell [-1,2]^n x cthickening delta K with delta=min(delta0,1), constants M,L chosen before the centre. Audit N3-63-audit-1.md L42 (row, PASS WITH NOTES package) and proof review L121.
NOTE: -

NODE: stepN:p3:up-translate
KIND: step
TITLE: Translating a ball into the cell
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:up-translate@L166-L168
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:up-translate@L166-L168
CONTRACT_ID: stepN:p3:up-translate
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E=R^n x R^n with max norm; U subset R^n open; W=R^n x U; F C1 on W and integer-periodic in angles; K subset U compact; delta,C,M,L_C are the constructed objects from up-cell, with 0<delta<=1; their proved cell bounds are supplied by that dependency
SOURCE_QUANTIFIERS: the periodic-field source data first; delta,C,M,L_C constructed by up-cell; every x=(theta,I) in Phi, with k=(floor(theta_i))_i and xprime=x-(k,0)
SOURCE_CONCLUSION: B̄(x',δ) ⊂ C and B̄(x,δ) = B̄(x',δ) + (k,0) ⊂ W; by periodicity ¦F¦ ≤ M and F is L_C-Lipschitz on B̄(x,δ)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:up-cell, bpN:p3:gen-uniform
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p3:up-cell | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:up-translate@L166-L166 | cell C and constants M, L_C
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:up-translate@L167-L168 | translation verifies containment, uniform boundedness and Lipschitzness on each ball
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_uniform_periodic (KAM/ODE/UniformPeriodic.lean)
LEAN_NOTE: Integer shift floor(x.1) translates each ball into the cell; periodicity gives the bounds. Audit N3-63-audit-1.md L42 and proof review L121 (same shift for all ball points).
NOTE: -

NODE: bpN:p3:gen-short
KIND: lemma
TITLE: A priori short-time confinement
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-short@L173-L179
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-short@L180-L188
CONTRACT_ID: bpN:p3:gen-short
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: J interval; t₀ ∈ J; α : ℝ → E with α(t₀) = x and α'(t) = F(α(t)) for all t ∈ J (two-sided; F only a function); ¦F¦ ≤ M on B̄(x,δ), M > 0
SOURCE_QUANTIFIERS: E; F; J; t₀; α; x; δ; M
SOURCE_CONCLUSION: ¦α(t)−x¦ ≤ M¦t−t₀¦ for all t ∈ J with ¦t−t₀¦ < δ/M; in particular α(t) ∈ B̄(x,δ)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:short-boot, stepN:p3:short-ext
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p3:short-boot | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-short@L181-L181 | bootstrap set A and its supremum
EDGE: stepN:p3:short-ext | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-short@L185-L185 | extension past s*
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_short, KAM.ODE.gen_short_forward (KAM/ODE/Existence.lean)
LEAN_NOTE: audit N3-45 PASS WITH NOTES
NOTE: -

NODE: stepN:p3:short-boot
KIND: step
TITLE: Forward bootstrap
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:short-boot@L181-L183
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:short-boot@L181-L183
CONTRACT_ID: stepN:p3:short-boot
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; J an interval; t0 in J; alpha:R->E with alpha(t0)=x and two-sided derivative F(alpha(t)) for every t in J; M>0 and abs(F)<=M on closedBall(x,delta); forward branch: t in J and t0<t<t0+delta/M
SOURCE_QUANTIFIERS: the gen-short data fixed first; t in J in the forward branch; define A={v in [t0,t]:abs(alpha(u)-x)<=M(u-t0) for all u in [t0,v]} and sstar=sSup(A)
SOURCE_CONCLUSION: t₀ ∈ A, A closed, so s* ∈ A (t < t₀ by time reversal, t = t₀ trivial)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-symmetry, bpN:p3:gen-sol#consequences
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-symmetry | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:short-boot@L181-L181 | case t < t₀ by time reversal (gen-symmetry(b))
EDGE: bpN:p3:gen-sol#consequences | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:short-boot@L183-L183 | continuity of α on J gives A closed
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-delta-N-c
REVIEWER: sol-delta2-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_short_forward, KAM.ODE.gen_short (KAM/ODE/Existence.lean)
LEAN_NOTE: Existence.lean L59-111 (bootstrap: closed set S cap Icc, t0 in S, Icc_subset_of_forall_exists_gt) and L120-143 (t<t0 via gen_symmetry_neg). Audit N3-45-audit-1.md L18-19 (Part 3 L173-183) and proof bullet L253.
NOTE: -

NODE: stepN:p3:short-ext
KIND: step
TITLE: Extension
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:short-ext@L185-L187
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:short-ext@L185-L187
CONTRACT_ID: stepN:p3:short-ext
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; J an interval; t0 in J; alpha:R->E with alpha(t0)=x and two-sided derivative F(alpha(t)) for every t in J; M>0 and abs(F)<=M on closedBall(x,delta); t in J with t0<t<t0+delta/M; A and sstar=sSup(A) are the objects defined by short-boot; examine the contradiction branch sstar<t
SOURCE_QUANTIFIERS: the parent data, forward t, A,sstar; if sstar<t choose eta>0 with sstar+eta<=t, then every u in [sstar,sstar+eta]
SOURCE_CONCLUSION: s* = t: otherwise ¦α(s*)−x¦ < δ, continuity gives η with α([s*,s*+η]) ⊂ B̄(x,δ), the mean value inequality gives ¦α(u)−x¦ ≤ M(u−t₀) there, contradicting the definition of s*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:short-boot, bpN:p3:gen-sol#consequences, K:bp:p1:ext-mvt
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p3:short-boot | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:short-ext@L185-L185 | s* ∈ A and definition of A
EDGE: bpN:p3:gen-sol#consequences | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:short-ext@L185-L185 | continuity of α gives η
EDGE: K:bp:p1:ext-mvt | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:short-ext@L186-L186 | mean value inequality for a curve with derivative bounded by M
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_short_forward (KAM/ODE/Existence.lean)
LEAN_NOTE: Existence.lean L83-111: continuity gives epsilon-neighbourhood, mean value inequality (Convex.norm_image_sub_le_of_norm_hasDerivWithin_le) extends the bound past u. Audit N3-45-audit-1.md L18 and bullet L253.
NOTE: -

NODE: bpN:p3:gen-uniform-exist
KIND: proposition
TITLE: Local existence with uniform time
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniform-exist@L190-L196
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniform-exist@L197-L203
CONTRACT_ID: bpN:p3:gen-uniform-exist
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F C¹ on the open set W; Φ has uniform data (δ,M,L); M' = max(M,1); ε = δ/M'
SOURCE_QUANTIFIERS: E; W; F; Φ; δ, M, L; then for every x ∈ Φ and t₀ ∈ ℝ an α
SOURCE_CONCLUSION: for every x ∈ Φ and t₀ ∈ ℝ there is α : ℝ → E with α(t₀) = x, ¦α(t)−x¦ < δ on (t₀−ε, t₀+ε) and IsSolIn F W (t₀−ε, t₀+ε) α; ε depends only on (δ,M)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-uniform, bpN:p3:gen-sol, stepN:p3:ue-pl, stepN:p3:ue-stay
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniform-exist@L191-L191 | hypothesis: Φ has uniform data (δ,M,L)
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniform-exist@L194-L194 | the conclusion is IsSolIn on the open time interval; L196 is only end{proposition}
EDGE: stepN:p3:ue-pl | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniform-exist@L198-L198 | construction of α by Picard-Lindelöf
EDGE: stepN:p3:ue-stay | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniform-exist@L202-L202 | α stays in B̄(x,δ) ⊂ W
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_uniform_exist (KAM/ODE/Existence.lean)
LEAN_NOTE: audit N3-45 PASS WITH NOTES
NOTE: parent depends on the package gen-uniform (statement) and gen-sol (conclusion predicate)

NODE: stepN:p3:ue-pl
KIND: step
TITLE: Picard--Lindel\"of
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ue-pl@L198-L200
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ue-pl@L198-L200
CONTRACT_ID: stepN:p3:ue-pl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; Phi subset E has uniform data (delta,M,L), delta>0, M,L>=0; x in Phi; t0 in R; Mprime=max(M,1), eps=delta/Mprime
SOURCE_QUANTIFIERS: the uniform-data setting, Mprime=max(M,1), eps=delta/Mprime; every x in Phi and t0 in R; then choose alpha with the within-derivative property
SOURCE_CONCLUSION: ext-pl with a = δ, bound M', Lipschitz L, T = ε (M'T = δ ≤ a) gives α with α(t₀) = x and derivative F(α(t)) within [t₀−ε,t₀+ε]; two-sided on the open interval
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:ext-pl, bpN:p3:gen-uniform
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:ext-pl | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ue-pl@L198-L198 | quantitative Picard-Lindelöf with a = δ, T = ε
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ue-pl@L198-L198 | bound M and Lipschitz constant L on B̄(x,δ) come from the uniform data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_uniform_exist, KAM.ODE.picard_lindelof_ball (KAM/ODE/Existence.lean)
LEAN_NOTE: Existence.lean L155-160: picard_lindelof_ball with a=delta, bound max M 1, T=delta/max M 1. Audit N3-45-audit-1.md L17,L20 and bullet L252,L254.
NOTE: -

NODE: stepN:p3:ue-stay
KIND: step
TITLE: Staying in $W$
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ue-stay@L202-L202
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ue-stay@L202-L202
CONTRACT_ID: stepN:p3:ue-stay
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; Phi subset E has uniform data (delta,M,L), delta>0, M,L>=0; x in Phi; t0 in R; Mprime=max(M,1), eps=delta/Mprime; alpha is the curve constructed by ue-pl, with its within-derivative conclusion supplied by that edge
SOURCE_QUANTIFIERS: the gen-uniform-exist data and x,t0; alpha constructed by ue-pl; then every t in J=(t0-eps,t0+eps)
SOURCE_CONCLUSION: ¦α(t)−x¦ ≤ M'¦t−t₀¦ < δ, so α(t) ∈ B̄(x,δ) ⊂ W
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-short, stepN:p3:ue-pl, bpN:p3:gen-uniform, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-short | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ue-stay@L202-L202 | a priori short-time confinement on J
EDGE: stepN:p3:ue-pl | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ue-stay@L202-L202 | the solution α
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ue-stay@L202-L202 | B̄(x,δ) ⊂ W
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ue-stay@L202-L202 | the pointwise derivative and membership establish the general solution predicate on the open interval
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_uniform_exist (KAM/ODE/Existence.lean)
LEAN_NOTE: Existence.lean L161-176: gen_short gives strict ||alpha-x||<delta, closedBall_subset yields membership in W. Audit N3-45-audit-1.md L20 and bullet L254.
NOTE: -

NODE: bpN:p3:gen-local
KIND: theorem
TITLE: Local existence, both time directions
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-local@L205-L210
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-local@L211-L213
CONTRACT_ID: bpN:p3:gen-local
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F C¹ on the open set W; x₀ ∈ W; t₀ ∈ ℝ; (for the uniform clause) K ⊂ W compact
SOURCE_QUANTIFIERS: E; W; F; x₀; t₀; (K); then ε and α
SOURCE_CONCLUSION: there are ε > 0 and α : ℝ → E with α(t₀) = x₀ and IsSolIn F W (t₀−ε, t₀+ε) α; ε may be taken uniform on any compact K ⊂ W (all x₀ ∈ K)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-sol, stepN:p3:loc-red
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-local@L207-L207 | conclusion IsSolIn
EDGE: stepN:p3:loc-red | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-local@L212-L212 | reduction to uniform data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_local (KAM/ODE/Existence.lean)
LEAN_NOTE: audit N3-45 PASS WITH NOTES
NOTE: -

NODE: stepN:p3:loc-red
KIND: step
TITLE: Reduction
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:loc-red@L212-L212
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:loc-red@L212-L212
CONTRACT_ID: stepN:p3:loc-red
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; for the point case x0 in W and t0 in R; for uniformity K subset W compact
SOURCE_QUANTIFIERS: F C1 on open W fixed; the point case x0 in W, or the compact case K subset W; choose delta,M,L by gen-uniform-compact and eps=delta/max(M,1); then every initial point in that set and every initial time t0 admits a curve alpha
SOURCE_CONCLUSION: the singleton {x0}, respectively K, has uniform data (delta,M,L); hence for eps=delta/max(M,1)>0, every x in that set and every t0 in R admit alpha:R->E with alpha(t0)=x and IsSolIn F W (t0-eps,t0+eps) alpha
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-uniform-compact, bpN:p3:gen-uniform-exist, bpN:p3:gen-uniform, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-uniform-compact | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:loc-red@L212-L212 | uniform data on the compact set
EDGE: bpN:p3:gen-uniform-exist | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:loc-red@L212-L212 | local solution of uniform time
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:loc-red@L212-L212 | the compact-set lemma supplies the uniform-data package needed for the uniform-time proposition
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:loc-red@L212-L212 | the claim constructed by gen-uniform-exist is a solution in the sense of IsSolIn
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_local (KAM/ODE/Existence.lean)
LEAN_NOTE: Existence.lean L184-199: uniform data on compact K (singleton for x0) via gen_uniform_compact, epsilon=delta/max M 1 chosen before x0,t0. Audit N3-45-audit-1.md L21 and bullet L254.
NOTE: -

NODE: bpN:p3:gen-uniqueness
KIND: theorem
TITLE: Uniqueness on arbitrary intervals
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniqueness@L217-L224
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniqueness@L225-L234
CONTRACT_ID: bpN:p3:gen-uniqueness
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F C¹ on the open set W; J ⊂ ℝ an interval of any kind; t₀ ∈ J; y₁, y₂ : ℝ → E with IsSolIn F W J y_i and y₁(t₀) = y₂(t₀); no confinement, boundedness or smallness assumed
SOURCE_QUANTIFIERS: E; W; F; J; t₀; y₁, y₂
SOURCE_CONCLUSION: y₁ = y₂ on J; in particular solutions on intervals J₁, J₂ agreeing at one point of J₁∩J₂ agree on J₁∩J₂
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-sol, stepN:p3:uq-compact, stepN:p3:uq-lip, stepN:p3:uq-apply
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniqueness@L219-L219 | hypothesis IsSolIn F W J y_i
EDGE: stepN:p3:uq-compact | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniqueness@L226-L226 | compact piece
EDGE: stepN:p3:uq-lip | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniqueness@L230-L230 | Lipschitz constant on K
EDGE: stepN:p3:uq-apply | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniqueness@L232-L232 | apply the uniqueness external
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_uniqueness, KAM.ODE.gen_uniqueness_inter (KAM/ODE/Uniqueness.lean)
LEAN_NOTE: audit N3-45 PASS WITH NOTES
NOTE: -

NODE: stepN:p3:uq-compact
KIND: step
TITLE: A compact piece
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uq-compact@L226-L228
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uq-compact@L226-L228
CONTRACT_ID: stepN:p3:uq-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; J an interval; t0 in J; IsSolIn F W J y_i (i=1,2); y_1(t0)=y_2(t0); take t1 in J, t1>t0 in the forward case (mirror case uses the left-derivative external)
SOURCE_QUANTIFIERS: the gen-uniqueness data fixed first; every t1 in J, with forward branch t1>t0; define K=y_1([t0,t1]) union y_2([t0,t1])
SOURCE_CONCLUSION: K is compact and K ⊂ W
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:ext-compact, bpN:p3:gen-sol#consequences, bpN:p3:ext-unique, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:ext-compact | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uq-compact@L227-L227 | continuous images of compact sets are compact
EDGE: bpN:p3:gen-sol#consequences | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uq-compact@L227-L227 | y_i continuous on [t₀,t₁] and the values lie in W
EDGE: bpN:p3:ext-unique | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uq-compact@L226-L226 | left-derivative form for the mirror case t₁ < t₀
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uq-compact@L227-L228 | the two solution predicates give image containment in W
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_uniqueness (KAM/ODE/Uniqueness.lean)
LEAN_NOTE: Private lipschitz_on_images (Uniqueness.lean L33-47): union of images of [t0,t1] under the two solutions is compact and inside W. Audit N3-45-audit-1.md L30 and bullet L255.
NOTE: -

NODE: stepN:p3:uq-lip
KIND: step
TITLE: Lipschitz on $K$
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uq-lip@L230-L230
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uq-lip@L230-L230
CONTRACT_ID: stepN:p3:uq-lip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; J an interval; t0 in J; IsSolIn F W J y_i (i=1,2); y_1(t0)=y_2(t0); t1 in J with t1>t0; K denotes the union of the two compact curve images constructed by uq-compact
SOURCE_QUANTIFIERS: the gen-uniqueness data and forward t1; K constructed by uq-compact; then choose L>=0 by gen-lip
SOURCE_CONCLUSION: F is L-Lipschitz on K
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-lip, stepN:p3:uq-compact, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-lip | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uq-lip@L230-L230 | Lipschitz constant on the compact set K
EDGE: stepN:p3:uq-compact | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uq-lip@L230-L230 | the compact set K
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uq-lip@L230-L230 | the compact images used for the Lipschitz application come from the source solutions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_uniqueness (KAM/ODE/Uniqueness.lean)
LEAN_NOTE: lipschitz_on_images obtains L from gen_lip on that compact set (Uniqueness.lean L46). Audit N3-45-audit-1.md L30 (PASS: constructs K and L from the compact images and gen_lip).
NOTE: -

NODE: stepN:p3:uq-apply
KIND: step
TITLE: Apply \ref{bpN:p3:ext-unique}
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uq-apply@L232-L233
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uq-apply@L232-L233
CONTRACT_ID: stepN:p3:uq-apply
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; J an interval; t0 in J; IsSolIn F W J y_i (i=1,2); y_1(t0)=y_2(t0); t1 in J with t1>t0; K and L are the constructed compact-image set and its Lipschitz constant, supplied by the two preceding steps
SOURCE_QUANTIFIERS: the gen-uniqueness data first, every forward t1 in J; K and L constructed by uq-compact and uq-lip; apply the uniqueness external on [t0,t1]
SOURCE_CONCLUSION: y₁(t₁) = y₂(t₁)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:ext-unique, stepN:p3:uq-lip, stepN:p3:uq-compact, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:ext-unique | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uq-apply@L232-L232 | uniqueness with a Lipschitz constant on a set
EDGE: stepN:p3:uq-lip | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uq-apply@L232-L232 | F is Lipschitz on K
EDGE: stepN:p3:uq-compact | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uq-apply@L232-L232 | values in K, continuity
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uq-apply@L232-L233 | the source predicates supply genuine two-sided derivatives, hence the right derivatives used here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_uniqueness (KAM/ODE/Uniqueness.lean)
LEAN_NOTE: Uniqueness.lean L56-77: Mathlib ODE_solution_unique_of_mem_Icc_right/left on [t0,t] and [t,t0]. Audit N3-45-audit-1.md L22 and bullet L255.
NOTE: -

NODE: bpN:p3:gen-extend
KIND: lemma
TITLE: Extension to an open interval
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-extend@L238-L241
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-extend@L242-L249
CONTRACT_ID: bpN:p3:gen-extend
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F C¹ on the open set W; J ≠ ∅ an interval; IsSolIn F W J y
SOURCE_QUANTIFIERS: E; W; F; J; y; then J' and y'
SOURCE_CONCLUSION: there are an open interval J' ⊃ J and y' with y' = y on J and IsSolIn F W J' y'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-sol, stepN:p3:ext-right, stepN:p3:ext-left
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-extend@L240-L240 | hypothesis and conclusion IsSolIn
EDGE: stepN:p3:ext-right | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-extend@L243-L243 | right end
EDGE: stepN:p3:ext-left | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-extend@L248-L248 | left end
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_extend (KAM/ODE/Maximal.lean)
LEAN_NOTE: audit N3-63 PASS WITH NOTES
NOTE: -

NODE: stepN:p3:ext-right
KIND: step
TITLE: Right end
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ext-right@L243-L246
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ext-right@L243-L246
CONTRACT_ID: stepN:p3:ext-right
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; J a nonempty interval; IsSolIn F W J y; if J has a largest point call it b; otherwise use the unchanged interval and curve
SOURCE_QUANTIFIERS: F,W,J,y as in gen-extend; if J has largest point b choose eps>0 and alpha by gen-local, then define J1,y1 by the splice; if J has no largest point put J1=J and y1=y
SOURCE_CONCLUSION: y₁ = y on s ≤ b, = α on s > b is a solution on J₁ = J ∪ (b,b+ε): two-sided derivative at b from the two one-sided ones
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-local, bpN:p3:ext-calc, bpN:p3:gen-sol#consequences, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-local | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ext-right@L243-L243 | local solution α through y(b) at t₀ = b
EDGE: bpN:p3:ext-calc | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ext-right@L245-L245 | two one-sided derivatives give a two-sided one
EDGE: bpN:p3:gen-sol#consequences | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ext-right@L244-L244 | local nature: y₁ agrees with y, resp. α, near t
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ext-right@L243-L245 | the given solution supplies y(b) in W and its endpoint derivative for the splice
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-delta-N-c
REVIEWER: sol-delta2-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_extend (KAM/ODE/Maximal.lean)
LEAN_NOTE: Private extend_right (Maximal.lean L89-153): local existence at the greatest endpoint, gluing with two one-sided derivatives (L122-133). Audit N3-63-audit-1.md L32,L34 and review L115.
NOTE: -

NODE: stepN:p3:ext-left
KIND: step
TITLE: Left end
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ext-left@L248-L248
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ext-left@L248-L248
CONTRACT_ID: stepN:p3:ext-left
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; J a nonempty interval; IsSolIn F W J y; J1,y1 denote the extension constructed by ext-right; apply the same construction to its reversal
SOURCE_QUANTIFIERS: the gen-extend source data; J1,y1 constructed by ext-right; reverse, construct the right extension for -F, then reverse back
SOURCE_CONCLUSION: reverse y1 and J1, extend at its largest endpoint by ext-right for -F, then reverse back; the resulting interval has neither included endpoint and is open, and its curve extends the original solution y on J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:ext-right, bpN:p3:gen-symmetry, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p3:ext-right | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ext-left@L248-L248 | apply Step ext-right to the reversed solution
EDGE: bpN:p3:gen-symmetry | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ext-left@L248-L248 | time reversal (gen-symmetry(b))
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:ext-left@L248-L248 | the reversed and extended curves are solutions of the appropriate total fields on open W
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_extend (KAM/ODE/Maximal.lean)
LEAN_NOTE: Private extend_open (Maximal.lean L155-192): reverses time, extends the other end, proves no endpoints remain. Audit N3-63-audit-1.md L33-34.
NOTE: -

NODE: bpN:p3:gen-maximal
KIND: theorem
TITLE: Maximal solution
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-maximal@L251-L258
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-maximal@L259-L268
CONTRACT_ID: bpN:p3:gen-maximal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F C¹ on the open set W; x₀ ∈ W
SOURCE_QUANTIFIERS: E; W; F; x₀; then T₋, T₊, z
SOURCE_CONCLUSION: there exist Tminus in [-infinity,0), Tplus in (0,+infinity] and z:R->E with z(0)=x0 and IsSolIn F W (Tminus,Tplus) z; every solution y through x0 on an interval J containing 0 has J subset (Tminus,Tplus) and y=z on J; the maximal interval and the restricted solution z|(Tminus,Tplus) are unique, with arbitrary values outside it; initial time t0 is handled by gen-symmetry(a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-sol, bpN:p3:gen-symmetry, stepN:p3:max-union, stepN:p3:max-glue, stepN:p3:max-max
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-maximal@L253-L253 | conclusion IsSolIn
EDGE: bpN:p3:gen-symmetry | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-maximal@L256-L256 | the source explicitly refers to the time shift here; L257 is provenance
EDGE: stepN:p3:max-union | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-maximal@L260-L260 | union of open intervals
EDGE: stepN:p3:max-glue | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-maximal@L263-L263 | gluing
EDGE: stepN:p3:max-max | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-maximal@L266-L266 | maximality
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_maximal, KAM.ODE.IsMaximalSolution (KAM/ODE/Maximal.lean)
LEAN_NOTE: audit N3-63 PASS WITH NOTES
NOTE: -

NODE: stepN:p3:max-union
KIND: step
TITLE: The union
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:max-union@L260-L261
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:max-union@L260-L261
CONTRACT_ID: stepN:p3:max-union
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; x0 in W
SOURCE_QUANTIFIERS: E,W,F,x0 fixed; define mathcalJ={open intervals J containing 0 admitting IsSolIn F W J y_J with y_J(0)=x0}; then its union I and extended endpoints Tminus,Tplus
SOURCE_CONCLUSION: 𝒥 ≠ ∅ and I = ∪𝒥 is an open interval (T₋,T₊) ∋ 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-local, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-local | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:max-union@L260-L260 | 𝒥 nonempty by local existence
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:max-union@L260-L260 | the union family is defined using the general solution predicate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_maximal (KAM/ODE/Maximal.lean)
LEAN_NOTE: exists_maximal (Maximal.lean L244-277): GoodInterval family nonempty by gen_local, I = eIoo Tm Tp open interval through 0 (hIlt, hIeq). Audit N3-63-audit-1.md L36-37 and review L117.
NOTE: -

NODE: stepN:p3:max-glue
KIND: step
TITLE: Gluing
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:max-glue@L263-L264
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:max-glue@L263-L264
CONTRACT_ID: stepN:p3:max-glue
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; x0 in W; mathcalJ and I are defined as in max-union; solutions y_J are chosen witnesses for those intervals
SOURCE_QUANTIFIERS: F,W,x0 fixed; mathcalJ,I and witnesses y_J from max-union; define the total z pointwise, choosing J containing t when t in I
SOURCE_CONCLUSION: define z(t)=y_J(t) for t in I using any J in mathcalJ containing t, and z(t)=x0 outside I; uniqueness makes this independent of J; z(0)=x0 and IsSolIn F W I z by the open-neighborhood local property
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-uniqueness, bpN:p3:gen-sol#consequences, stepN:p3:max-union, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-uniqueness | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:max-glue@L263-L263 | y_J = y_{J'} on J∩J' ∋ 0
EDGE: bpN:p3:gen-sol#consequences | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:max-glue@L264-L264 | local nature (iii)
EDGE: stepN:p3:max-union | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:max-glue@L263-L263 | the family 𝒥 and its union I
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:max-glue@L263-L264 | the glued curve satisfies IsSolIn on the union of its open solution neighborhoods
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_maximal (KAM/ODE/Maximal.lean)
LEAN_NOTE: exists_maximal (Maximal.lean L278-292): z defined by choice on good intervals, independence via gen_uniqueness_inter (hz_key), solution on I by isSolutionIn_congr_of_isOpen, z 0 = x0. Audit N3-63-audit-1.md L37 and review L117.
NOTE: -

NODE: stepN:p3:max-max
KIND: step
TITLE: Maximality
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:max-max@L266-L267
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:max-max@L266-L267
CONTRACT_ID: stepN:p3:max-max
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; x0 in W; mathcalJ,I,z are the constructed family, union and curve from max-union/max-glue; take any IsSolIn F W J y with J an interval containing 0 and y(0)=x0
SOURCE_QUANTIFIERS: E,W,F,x0 and the earlier constructed objects; every test interval J and solution y through x0; then choose Jprime,yprime by gen-extend
SOURCE_CONCLUSION: J ⊂ J' ⊂ I and y = y' = z on J; uniqueness of the maximal interval and of z on it
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-extend, bpN:p3:gen-uniqueness, stepN:p3:max-union, stepN:p3:max-glue, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-extend | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:max-max@L266-L266 | open J' ⊃ J and solution y' extending y
EDGE: bpN:p3:gen-uniqueness | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:max-max@L266-L266 | the explicit uniqueness citation is at L266, not L267
EDGE: stepN:p3:max-union | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:max-max@L266-L266 | J' ∈ 𝒥 so J' ⊂ I
EDGE: stepN:p3:max-glue | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:max-max@L267-L267 | z is a solution on I
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:max-max@L266-L267 | the maximality comparison and restricted-solution uniqueness concern the solution predicate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_maximal (KAM/ODE/Maximal.lean)
LEAN_NOTE: Maximality via gen_extend (Maximal.lean L296-302) and uniqueness of interval/z via eIoo_subset_of_maximal, left/right_eq_of_eIoo_subset (L308-343). Audit N3-63-audit-1.md L34,L38-41 and review L119.
NOTE: -

NODE: bpN:p3:gen-continuation
KIND: theorem
TITLE: Continuation criterion, uniform form
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation@L270-L277
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation@L278-L287
CONTRACT_ID: bpN:p3:gen-continuation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F C¹ on the open set W; x₀ ∈ W; (T₋,T₊), z the maximal interval and solution of gen-maximal; Φ has uniform data (δ,M,L)
SOURCE_QUANTIFIERS: E; W; F; x₀; Φ; δ, M, L; t_*
SOURCE_CONCLUSION: if T₊ < ∞ there is no t_* ∈ [0,T₊) with z(t) ∈ Φ for all t ∈ [t_*,T₊); symmetrically on the left; equivalently, staying in Φ near an end of the maximal interval forces that end to be ±∞
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-maximal, bpN:p3:gen-uniform, stepN:p3:cont-setup, stepN:p3:cont-alpha, stepN:p3:cont-glue
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-maximal | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation@L271-L271 | maximal interval and solution
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation@L272-L273 | the hypothesis is Phi with uniform data (delta,M,L)
EDGE: stepN:p3:cont-setup | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation@L279-L279 | set-up
EDGE: stepN:p3:cont-alpha | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation@L281-L281 | solution through z(t₁)
EDGE: stepN:p3:cont-glue | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation@L284-L284 | gluing past T₊
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_continuation (KAM/ODE/Continuation.lean)
LEAN_NOTE: audit N3-7 PASS WITH NOTES
NOTE: -

NODE: stepN:p3:cont-setup
KIND: step
TITLE: Set-up
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-setup@L279-L279
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-setup@L279-L279
CONTRACT_ID: stepN:p3:cont-setup
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; x0 in W; (Tminus,Tplus) and z the maximal interval and solution through x0; Phi has uniform data (delta,M,L); contradiction branch Tplus finite and some tstar in [0,Tplus) has z(t) in Phi on [tstar,Tplus)
SOURCE_QUANTIFIERS: the gen-continuation data; in the finite-right-endpoint tail branch choose eps=delta/max(M,1)>0 and t1 in [tstar,Tplus) with t1>Tplus-eps
SOURCE_CONCLUSION: ε as in gen-uniform-exist and t₁ ∈ [t_*,T₊) with t₁ > T₊ − ε
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-uniform-exist, bpN:p3:gen-uniform, bpN:p3:gen-maximal
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-uniform-exist | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-setup@L279-L279 | uniform existence time ε = δ/max(M,1)
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-setup@L279-L279 | delta,M are the uniform data fixing the positive common existence time
EDGE: bpN:p3:gen-maximal | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-setup@L279-L279 | the finite maximal endpoint and its interval permit choosing t1 sufficiently near Tplus
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_continuation (KAM/ODE/Continuation.lean)
LEAN_NOTE: Private continuation_right (Continuation.lean L45-110): epsilon=delta/max(M,1), t1=max(t_star,T-epsilon/2). Audit N3-7-audit-1.md L29 and proof audit L35.
NOTE: -

NODE: stepN:p3:cont-alpha
KIND: step
TITLE: A solution through $z(t_1)$
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-alpha@L281-L282
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-alpha@L281-L282
CONTRACT_ID: stepN:p3:cont-alpha
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; x0 in W; (Tminus,Tplus) and z the maximal interval and solution through x0; Phi has uniform data (delta,M,L); the finite-endpoint tail branch of cont-setup; eps and t1 are the constructed positive time and tail point
SOURCE_QUANTIFIERS: the gen-continuation data and finite-tail branch; eps,t1 chosen in cont-setup; then choose alpha through z(t1) and compare it with z on the overlap
SOURCE_CONCLUSION: α with α(t₁) = z(t₁) on (t₁−ε,t₁+ε) and α = z on (t₁−ε,t₁+ε) ∩ (T₋,T₊)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-uniform-exist, bpN:p3:gen-uniqueness, stepN:p3:cont-setup, bpN:p3:gen-uniform, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-uniform-exist | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-alpha@L281-L281 | solution α through x = z(t₁) ∈ Φ at t₀ = t₁
EDGE: bpN:p3:gen-uniqueness | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-alpha@L282-L282 | α = z on the overlap
EDGE: stepN:p3:cont-setup | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-alpha@L281-L281 | ε and t₁
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-alpha@L281-L281 | uniform data on Phi at z(t1) discharge the local-existence premises
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-alpha@L281-L282 | the newly constructed alpha and maximal z are compared as general solutions on the overlap
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_continuation (KAM/ODE/Continuation.lean)
LEAN_NOTE: continuation_right: local existence at z(t1) from uniform data, agreement with z on the overlap by uniqueness (Continuation.lean L58-100). Audit N3-7-audit-1.md L29 and proof audit L35-36.
NOTE: -

NODE: stepN:p3:cont-glue
KIND: step
TITLE: Gluing past $T_+$
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-glue@L284-L286
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-glue@L284-L286
CONTRACT_ID: stepN:p3:cont-glue
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; x0 in W; (Tminus,Tplus) and z the maximal interval and solution through x0; Phi has uniform data (delta,M,L); finite-endpoint tail branch; eps,t1,alpha are the objects constructed in cont-setup/cont-alpha, with overlap agreement supplied by those dependencies
SOURCE_QUANTIFIERS: the gen-continuation data and finite-tail branch; the earlier eps,t1,alpha; define y by the displayed piecewise gluing and extend it arbitrarily outside its solution interval
SOURCE_CONCLUSION: y = z on (T₋,T₊), y = α on [T₊,t₁+ε) is a solution on (T₋,t₁+ε) ∋ 0 with y(0) = x₀, contradicting gen-maximal; the left end by time reversal
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:cont-alpha, bpN:p3:gen-sol#consequences, bpN:p3:gen-maximal, bpN:p3:gen-symmetry, bpN:p3:gen-sol, bpN:p3:gen-uniform
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p3:cont-alpha | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-glue@L284-L284 | α and its agreement with z
EDGE: bpN:p3:gen-sol#consequences | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-glue@L285-L285 | local nature on the two open sets covering (T₋,t₁+ε)
EDGE: bpN:p3:gen-maximal | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-glue@L285-L285 | the extension past the endpoint contradicts maximality at this line
EDGE: bpN:p3:gen-symmetry | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-glue@L286-L286 | left end by time reversal
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-glue@L284-L285 | the pasted curve solves the same equation on the covering open neighborhoods
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cont-glue@L284-L285 | the source continuation setting includes the uniform-data package used to construct the patch
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_continuation (KAM/ODE/Continuation.lean)
LEAN_NOTE: continuation_right gluing by IsSolutionIn.union_of_isOpen and contradiction with maximality at L104; left end via IsMaximalSolution.neg and UniformData.neg (L38-42). Audit N3-7-audit-1.md L29 and proof audit L36-37.
NOTE: -

NODE: bpN:p3:gen-continuation-compact
KIND: corollary
TITLE: Compact continuation
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation-compact@L289-L292
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation-compact@L293-L295
CONTRACT_ID: bpN:p3:gen-continuation-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; x0 in W; (Tminus,Tplus),z the maximal interval and solution; K subset W compact; some tstar in [0,Tplus) has z(t) in K on [tstar,Tplus); the analogous left-tail alternative for the left conclusion
SOURCE_QUANTIFIERS: E,W,F,x0 fixed; the maximal solution; compact K; then a tail time tstar as stated
SOURCE_CONCLUSION: T₊ = +∞; likewise on the left
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-continuation, bpN:p3:gen-uniform-compact, bpN:p3:gen-maximal, bpN:p3:gen-uniform
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-continuation | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation-compact@L290-L290 | setting and continuation criterion applied to Φ = K
EDGE: bpN:p3:gen-uniform-compact | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation-compact@L294-L294 | uniform data for the compact set K
EDGE: bpN:p3:gen-maximal | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation-compact@L290-L290 | the corollary is stated for the maximal solution in the setting of the preceding theorem
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation-compact@L294-L294 | construct uniform data for K and apply the uniform continuation criterion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_continuation_compact (KAM/ODE/Continuation.lean)
LEAN_NOTE: audit N3-7 PASS WITH NOTES
NOTE: -

NODE: bpN:p3:gen-continuation-periodic
KIND: corollary
TITLE: Closed sets, periodic fields
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation-periodic@L297-L299
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation-periodic@L300-L302
CONTRACT_ID: bpN:p3:gen-continuation-periodic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E = ℝⁿ×ℝⁿ; U ⊂ ℝⁿ open; W = ℝⁿ × U; F C¹ on W with F(θ+k,I) = F(θ,I), k ∈ ℤⁿ; z the maximal solution through x₀ ∈ W; z(t)₂ ∈ K for t ∈ [t_*,T₊), K ⊂ U compact
SOURCE_QUANTIFIERS: n; U; F; x₀; K; t_*
SOURCE_CONCLUSION: T₊ = +∞ (likewise on the left); the angle components z(t)₁ may be unbounded
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-maximal, bpN:p3:gen-continuation, bpN:p3:gen-uniform-periodic, bpN:p3:gen-uniform
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-maximal | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation-periodic@L298-L298 | maximal solution through x₀
EDGE: bpN:p3:gen-continuation | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation-periodic@L301-L301 | the proof applies the continuation theorem here; L300 is begin{proof}
EDGE: bpN:p3:gen-uniform-periodic | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation-periodic@L301-L301 | this lemma supplies uniform data for R^n x K here
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation-periodic@L301-L301 | the proof uses the uniform-data package for the periodic cylinder
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_continuation_periodic (KAM/ODE/Continuation.lean)
LEAN_NOTE: audit N3-7 PASS WITH NOTES
NOTE: -

NODE: bpN:p3:gen-confinement
KIND: theorem
TITLE: Confinement glue
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-confinement@L310-L318
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-confinement@L319-L324
CONTRACT_ID: bpN:p3:gen-confinement
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F C¹ on the open set W; x₀ ∈ W; τ > 0; Φ ⊂ E with uniform data; a priori confinement: every solution y on an open interval J ∋ 0 with y(0) = x₀ satisfies y(t) ∈ Φ for t ∈ J, ¦t¦ ≤ τ
SOURCE_QUANTIFIERS: E; W; F; x₀; τ; Φ; (δ,M,L); then z
SOURCE_CONCLUSION: the maximal interval contains [−τ,τ] in its interior, z is a solution on [−τ,τ] with z(t) ∈ Φ for ¦t¦ ≤ τ, and every solution on [−L,L] (0 ≤ L ≤ τ) with initial value x₀ equals z there
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-uniform, bpN:p3:gen-sol, bpN:p3:gen-maximal, stepN:p3:conf-noexit, stepN:p3:conf-concl
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-confinement@L311-L312 | Phi is assumed to have uniform data
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-confinement@L313-L313 | solutions y and conclusion IsSolIn
EDGE: bpN:p3:gen-maximal | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-confinement@L314-L314 | the conclusion refers to the maximal interval and solution here, not the isolated L316 “there”
EDGE: stepN:p3:conf-noexit | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-confinement@L320-L320 | no exit before τ
EDGE: stepN:p3:conf-concl | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-confinement@L323-L323 | conclusion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_confinement (KAM/ODE/Continuation.lean)
LEAN_NOTE: audit N3-7 PASS WITH NOTES
NOTE: -

NODE: stepN:p3:conf-noexit
KIND: step
TITLE: No exit before $\tau$
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:conf-noexit@L320-L321
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:conf-noexit@L320-L321
CONTRACT_ID: stepN:p3:conf-noexit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; x0 in W; tau>0; Phi has uniform data (delta,M,L); for every open interval J containing 0 and every IsSolIn F W J y through x0, y(t) in Phi whenever t in J and abs(t)<=tau; z and (Tminus,Tplus) denote the maximal solution and interval
SOURCE_QUANTIFIERS: the source data, maximal solution and interval; in the right-end contradiction argument suppose Tplus<=tau; use the analogous left-end argument
SOURCE_CONCLUSION: T₊ > τ and T₋ < −τ: otherwise z(t) ∈ Φ on [0,T₊) by confinement and gen-continuation gives T₊ = ∞
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-maximal, bpN:p3:gen-continuation, bpN:p3:gen-uniform, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-maximal | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:conf-noexit@L320-L320 | maximal solution z on (T₋,T₊)
EDGE: bpN:p3:gen-continuation | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:conf-noexit@L321-L321 | continuation criterion gives T₊ = ∞
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:conf-noexit@L320-L321 | uniform data of Phi are a premise of the applied continuation criterion
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:conf-noexit@L320-L320 | the a priori hypothesis is instantiated with the maximal solution on its open interval
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_confinement (KAM/ODE/Continuation.lean)
LEAN_NOTE: gen_confinement (Continuation.lean L145-182): gen_maximal supplies z; if Tp<=tau confinement plus continuation forces Tp=top; left end symmetric. Audit N3-7-audit-1.md L27 and proof audit L39-40.
NOTE: -

NODE: stepN:p3:conf-concl
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:conf-concl@L323-L323
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:conf-concl@L323-L323
CONTRACT_ID: stepN:p3:conf-concl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; F:E->E total; W subset E open; F C1 on W; x0 in W; tau>0; Phi has uniform data (delta,M,L); for every open interval J containing 0 and every IsSolIn F W J y through x0, y(t) in Phi whenever t in J and abs(t)<=tau; z and its maximal interval are the objects of gen-maximal; endpoint inequalities are the conclusion of conf-noexit, not added hypotheses
SOURCE_QUANTIFIERS: the gen-confinement data and constructed maximal solution z; every t with abs(t)<=tau; every Ltime in [0,tau] and every IsSolIn F W [-Ltime,Ltime] y through x0
SOURCE_CONCLUSION: [-tau,tau] subset (Tminus,Tplus); IsSolIn F W [-tau,tau] z and z(t) in Phi for abs(t)<=tau; every Ltime in [0,tau] and every solution y through x0 on [-Ltime,Ltime] has y=z on that interval
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:conf-noexit, bpN:p3:gen-uniqueness, bpN:p3:gen-sol, bpN:p3:gen-uniform
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p3:conf-noexit | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:conf-concl@L323-L323 | [−τ,τ] in the maximal interval
EDGE: bpN:p3:gen-uniqueness | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:conf-concl@L323-L323 | uniqueness of solutions on [−L,L]
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:conf-concl@L323-L323 | restriction of the genuine maximal solution gives IsSolIn on the closed interval
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:conf-concl@L323-L323 | the retained source confinement setting assumes this package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3a+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_confinement (KAM/ODE/Continuation.lean)
LEAN_NOTE: gen_confinement conclusion: closed-interval solution by restriction, confinement, agreement with every competing solution for 0<=r<=tau via uniqueness. Audit N3-7-audit-1.md L27 and proof audit L39-40.
NOTE: -
