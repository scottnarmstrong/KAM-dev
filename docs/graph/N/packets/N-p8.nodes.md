NODE: bpN:p8:ext-free
KIND: external
TITLE: Subgroups of $\Z^n$
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:ext-free@L17-L17
PROOF_SOURCE: -
CONTRACT_ID: bpN:p8:ext-free
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Λ a subgroup of ℤⁿ
SOURCE_QUANTIFIERS: n; Λ
SOURCE_CONCLUSION: Λ is a free ℤ-module of rank d ≤ n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: External (Mathlib Submodule.basisOfPid); stays an external.

NODE: bpN:p8:ext-gram
KIND: external
TITLE: Gram matrices
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:ext-gram@L18-L18
PROOF_SOURCE: -
CONTRACT_ID: bpN:p8:ext-gram
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A ∈ ℝ^{n×d} with x↦Ax injective
SOURCE_QUANTIFIERS: n, d; A
SOURCE_CONCLUSION: AᵀA positive definite, det(AᵀA) > 0; det(MN)=det M det N, det Mᵀ=det M
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: External (Mathlib PosDef).

NODE: bpN:p8:ext-schur
KIND: external
TITLE: Schur complement
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:ext-schur@L19-L19
PROOF_SOURCE: -
CONTRACT_ID: bpN:p8:ext-schur
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G ∈ ℝ^{d×d} invertible; b, c ∈ ℝ^d; γ ∈ ℝ
SOURCE_QUANTIFIERS: d; G, b, c, γ
SOURCE_CONCLUSION: det [[G,b],[cᵀ,γ]] = det G (γ − cᵀG⁻¹b)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: External (Mathlib Matrix.det_fromBlocks₁₁).

NODE: bpN:p8:ext-units
KIND: external
TITLE: Unimodular matrices
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:ext-units@L20-L20
PROOF_SOURCE: -
CONTRACT_ID: bpN:p8:ext-units
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U ∈ ℤ^{d×d}; two bases of a free module
SOURCE_QUANTIFIERS: d; U
SOURCE_CONCLUSION: U invertible over ℤ iff det U ∈ {±1}; change-of-basis matrix between two bases is invertible; a nonzero integer has modulus ≥ 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: External (Mathlib isUnit_iff_isUnit_det, Basis.invertibleToMatrix).

NODE: bpN:p8:ext-indep
KIND: external
TITLE: Independence over $\Q$ and $\R$
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:ext-indep@L21-L21
PROOF_SOURCE: -
CONTRACT_ID: bpN:p8:ext-indep
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: columns of an integer matrix that are ℤ-linearly independent; rational matrix with Q-independent columns
SOURCE_QUANTIFIERS: d, n; matrix
SOURCE_CONCLUSION: ℤ-independent columns are ℚ-independent; ℚ-independent columns of a rational matrix are ℝ-independent (nonvanishing of a d×d minor)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: External (Mathlib LinearIndependent.iff_fractionRing; second half stated as a short lemma over the field extension).

NODE: bpN:p8:ext-basic
KIND: external
TITLE: Elementary facts
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:ext-basic@L22-L22
PROOF_SOURCE: -
CONTRACT_ID: bpN:p8:ext-basic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: as listed
SOURCE_QUANTIFIERS: n; x, y; K
SOURCE_CONCLUSION: Cauchy–Schwarz ¦x·y¦ ≤ ‖x‖‖y‖; a finite nonempty poset has a maximal element; ℰ_K is a finite set; a finite spanning set of a vector space contains a basis
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: External.

NODE: bpN:p8:lattice
KIND: definition
TITLE: Lattices
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice@L28-L31
PROOF_SOURCE: -
CONTRACT_ID: bpN:p8:lattice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data: n ≥ 1, Λ ≤ ℤⁿ a subgroup)
SOURCE_QUANTIFIERS: n; Λ
SOURCE_CONCLUSION: defines lattice, span W_Λ = span_ℝ Λ, dimension d = dim_ℝ W_Λ, trivial lattice Θ = {0}, resonance space R_Λ = {ω: k·ω=0 ∀k∈Λ} = W_Λ^⊥ of dimension n − d
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: PROVED
LEAN_REF: Lattice, lattice, latticeDim, integerReal, eBall, resonance, lattice_resonance (KAM/Nekhoroshev/ResonanceGeometry/Lattice.lean)
LEAN_NOTE: audit N89-G1 PASS WITH NOTES
NOTE: Package bpN:p8:lattice (SPEC): consumed by symbol (Λ, W_Λ, dim, R_Λ, Θ) throughout Parts 8, 9, 11c.

NODE: bpN:p8:lattice-basis
KIND: lemma
TITLE: Bases and unimodular change
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-basis@L33-L41
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-basis@L42-L46
CONTRACT_ID: bpN:p8:lattice-basis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Λ ≤ ℤⁿ a lattice
SOURCE_QUANTIFIERS: n; Λ; (a) basis a_1..a_d, A; (b) Ã=AU; (c) Γ ≤ Λ
SOURCE_CONCLUSION: (a) Λ has a ℤ-basis of d ≤ n vectors, ℝ-independent, dim_ℝ W_Λ = d = rank_ℤ Λ; (b) change of basis matrix U ∈ ℤ^{d×d} with det U = ±1, and converse; (c) for Γ ≤ Λ of equal dimension Ã = AN with N ∈ ℤ^{d×d}, det N ≠ 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:lattice, stepN:p8:lb-basis, stepN:p8:lb-unimod, stepN:p8:lb-sub
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-basis@L34-L35 | Λ, W_Λ, dim
EDGE: stepN:p8:lb-basis | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-basis@L43-L43 | proof step (a)
EDGE: stepN:p8:lb-unimod | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-basis@L44-L44 | proof step (b)
EDGE: stepN:p8:lb-sub | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-basis@L45-L45 | proof step (c)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: PROVED
LEAN_REF: latticeBasis, basisMatrix, lattice_basis, lattice_basis_change, lattice_basis_sub (KAM/Nekhoroshev/ResonanceGeometry/Lattice.lean)
LEAN_NOTE: audit N89-G1 PASS WITH NOTES
NOTE: -

NODE: stepN:p8:lb-basis
KIND: step
TITLE: Basis
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-basis@L43-L43
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-basis@L43-L43
CONTRACT_ID: stepN:p8:lb-basis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Λ ≤ ℤⁿ
SOURCE_QUANTIFIERS: Λ
SOURCE_CONCLUSION: Λ has a ℤ-basis with d ≤ n elements, ℝ-independent
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:ext-free, bpN:p8:ext-indep, bpN:p8:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:ext-free | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-basis@L43-L43 | ℤ-basis with d ≤ n
EDGE: bpN:p8:ext-indep | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-basis@L43-L43 | ℝ-independence
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-basis@L43-L43 | lattice objects, their spans/dimensions or the trivial/full lattice are used at this consumer; SPEC requires the package directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:lb-unimod
KIND: step
TITLE: Unimodular
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-unimod@L44-L44
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-unimod@L44-L44
CONTRACT_ID: stepN:p8:lb-unimod
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: bases A, Ã of Λ
SOURCE_QUANTIFIERS: Λ; A, Ã
SOURCE_CONCLUSION: Ã = AU with U ∈ ℤ^{d×d}, det U = ±1; converse for U unimodular
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p8:lb-basis, bpN:p8:ext-units, bpN:p8:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p8:lb-basis | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-unimod@L44-L44 | injectivity (independence) of A
EDGE: bpN:p8:ext-units | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-unimod@L44-L44 | integer det with product 1 is ±1; U⁻¹ integral
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-unimod@L44-L44 | lattice objects, their spans/dimensions or the trivial/full lattice are used at this consumer; SPEC requires the package directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-delta-N-e
REVIEWER: sol-delta2-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:lb-sub
KIND: step
TITLE: Sublattice
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-sub@L45-L45
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-sub@L45-L45
CONTRACT_ID: stepN:p8:lb-sub
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Γ ≤ Λ with equal dimension; bases Ã, A
SOURCE_QUANTIFIERS: Γ, Λ
SOURCE_CONCLUSION: Ã = AN with N integer and det N ≠ 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p8:lb-basis, bpN:p8:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p8:lb-basis | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-sub@L45-L45 | Ã injective by (a)
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-sub@L45-L45 | lattice objects, their spans/dimensions or the trivial/full lattice are used at this consumer; SPEC requires the package directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-delta-N-e
REVIEWER: sol-delta2-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p8:volume-def
KIND: definition
TITLE: Volume of a lattice
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:volume-def@L48-L51
PROOF_SOURCE: -
CONTRACT_ID: bpN:p8:volume-def
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data: lattice Λ with basis matrix A; radicand positive by ext-gram and lattice-basis(a))
SOURCE_QUANTIFIERS: n; Λ; basis matrix A
SOURCE_CONCLUSION: defines ¦Λ¦ = sqrt(det(AᵀA)) for Λ ≠ Θ and ¦Θ¦ = 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:ext-gram, bpN:p8:lattice-basis, bpN:p8:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:ext-gram | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:volume-def@L49-L49 | radicand det(AᵀA) > 0
EDGE: bpN:p8:lattice-basis | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:volume-def@L49-L49 | basis matrix A and (a): independence of columns
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:volume-def@L49-L49 | Λ, basis matrix, Θ
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: PROVED
LEAN_REF: gram, volume_def (KAM/Nekhoroshev/ResonanceGeometry/Volume.lean)
LEAN_NOTE: audit N89-G3 PASS WITH NOTES
NOTE: Package (SPEC): ¦Λ¦ used by symbol in lattice-volume, maximal, blocks, covering, Parts 9 and 11c. Edge to lattice-basis is the well-definedness input for the radicand; the independence of the basis matrix is lattice-volume(a), which is not an input.

NODE: bpN:p8:projection
KIND: lemma
TITLE: Orthogonal projection onto a span
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:projection@L53-L63
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:projection@L64-L68
CONTRACT_ID: bpN:p8:projection
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A ∈ ℝ^{n×d}, d ≥ 1, independent columns; W their span; G = AᵀA; Π_W = AG⁻¹Aᵀ, Q_W = 1 − Π_W; (d) W ⊂ W′ two such spans
SOURCE_QUANTIFIERS: n, d; A; v, ω ∈ ℝⁿ
SOURCE_CONCLUSION: (a) Π_W symmetric idempotent, Π_W v ∈ W, = v on W, Q_W v ⊥ W, ‖v‖² = ‖Π_W v‖² + ‖Q_W v‖²; (b) Π_W v unique w∈W with v − w ⊥ W; (c) dist₂(ω,W^⊥) = ‖Π_W ω‖; (d) Π_{W′}Π_W = Π_WΠ_{W′} = Π_W; consequently R_Λ = W_Λ^⊥, dist₂(ω,R_Λ) = ‖Π_{W_Λ} ω‖; also in (a) ||Pi_W v||_2 <= ||v||_2 and ||Q_W v||_2 <= ||v||_2; for d=0 set Pi_{0}=0; write Pi_Lambda=Pi_{W_Lambda}, Q_Lambda=Q_{W_Lambda}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:ext-gram, bpN:p8:lattice, stepN:p8:pr-alg, stepN:p8:pr-dist, stepN:p8:pr-nest, bpN:p8:lattice-basis
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:ext-gram | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:projection@L54-L54 | G = AᵀA invertible
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:projection@L61-L61 | R_Lambda and W_Lambda occur in the consequence on L61, not in the provenance note L62
EDGE: stepN:p8:pr-alg | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:projection@L65-L65 | proof step (a)
EDGE: stepN:p8:pr-dist | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:projection@L66-L66 | proof step (b),(c)
EDGE: stepN:p8:pr-nest | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:projection@L67-L67 | proof step (d)
EDGE: bpN:p8:lattice-basis | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:projection@L61-L61 | the consequence for an arbitrary lattice uses existence of an independent basis for its span, including the zero-dimensional convention
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: PROVED
LEAN_REF: projection_exists_unique, proj, compProj, projection, projection_zero, resonanceDistance, projection_distance_subspace, projection_distance (KAM/Nekhoroshev/ResonanceGeometry/Projection.lean)
LEAN_NOTE: audit N89-G2 PASS WITH NOTES
NOTE: Euclidean norm ‖·‖ on ℝⁿ (Part 8 convention, L9). The consequence line uses the lattice definitions (edge to bpN:p8:lattice).

NODE: stepN:p8:pr-alg
KIND: step
TITLE: Algebra
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:pr-alg@L65-L65
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:pr-alg@L65-L65
CONTRACT_ID: stepN:p8:pr-alg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A with independent columns, G = AᵀA invertible
SOURCE_QUANTIFIERS: A
SOURCE_CONCLUSION: Π_W symmetric, idempotent, Π_W A = A, A^T Q_W = 0, Pythagoras
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:ext-gram
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:ext-gram | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:pr-alg@L65-L65 | G invertible and symmetric
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:pr-dist
KIND: step
TITLE: Uniqueness, distance
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:pr-dist@L66-L66
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:pr-dist@L66-L66
CONTRACT_ID: stepN:p8:pr-dist
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: part (a)
SOURCE_QUANTIFIERS: W, v, ω
SOURCE_CONCLUSION: (b) uniqueness; (c) ‖ω−u‖² = ‖Π_Wω‖² + ‖Q_Wω−u‖², minimum at u = Q_Wω
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p8:pr-alg
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p8:pr-alg | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:pr-dist@L66-L66 | Π_Wω ∈ W, Q_Wω ⊥ W, Pythagoras
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:pr-nest
KIND: step
TITLE: Nested spans
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:pr-nest@L67-L67
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:pr-nest@L67-L67
CONTRACT_ID: stepN:p8:pr-nest
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W ⊂ W′; part (a)
SOURCE_QUANTIFIERS: W, W′
SOURCE_CONCLUSION: Π_{W′}Π_W = Π_WΠ_{W′} = Π_W
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p8:pr-alg
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p8:pr-alg | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:pr-nest@L67-L67 | Π_W v ∈ W ⊂ W′, Π_{W′} = id on W′, symmetry
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p8:lattice-volume
KIND: lemma
TITLE: Volume
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-volume@L70-L81
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-volume@L82-L88
CONTRACT_ID: bpN:p8:lattice-volume
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 1; Λ, Γ ≤ ℤⁿ lattices
SOURCE_QUANTIFIERS: n; Λ, Γ; (c) N; (e) k; (f) v_1..v_d
SOURCE_CONCLUSION: (a) det(AᵀA) independent of basis matrix; (b) ¦Λ¦² positive integer, ¦Λ¦ ≥ 1; (c) Γ ≤ Λ, dim equal ⇒ ¦Γ¦ = ¦det N¦¦Λ¦ ≥ ¦Λ¦; (d) for g ∈ ℤⁿ∖{0}, ¦ℤg¦ = ‖g‖, ¦ℤⁿ¦ = 1; (e) k ∈ ℤⁿ∖W_Λ ⇒ dim(Λ+ℤk) = dim Λ + 1, ¦Λ+ℤk¦ = ¦Λ¦‖Q_Λ k‖, Q_Λ k ≠ 0; (f) if v_1,…,v_d ∈ ℤⁿ are ℝ-independent and generate Γ, then ¦Γ¦ ≤ ∏‖v_i‖
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:lattice, bpN:p8:volume-def, bpN:p8:lattice-basis, bpN:p8:projection, stepN:p8:lv-ab, stepN:p8:lv-c, stepN:p8:lv-d, stepN:p8:lv-e, stepN:p8:lv-f
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-volume@L71-L71 | lattices, W_Λ, dim
EDGE: bpN:p8:volume-def | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-volume@L71-L80 | ¦Λ¦
EDGE: bpN:p8:lattice-basis | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-volume@L75-L75 | N is explicitly the basis-change matrix of lattice-basis(c)
EDGE: bpN:p8:projection | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-volume@L77-L77 | Q_Lambda k occurs in the adding-a-vector conclusion
EDGE: stepN:p8:lv-ab | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-volume@L83-L83 | proof (a),(b)
EDGE: stepN:p8:lv-c | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-volume@L84-L84 | proof (c)
EDGE: stepN:p8:lv-d | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-volume@L85-L85 | proof (d)
EDGE: stepN:p8:lv-e | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-volume@L86-L86 | proof (e)
EDGE: stepN:p8:lv-f | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-volume@L87-L87 | proof (f)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-delta-N-e
REVIEWER: sol-delta2-N-e
LEAN_STATUS: PROVED
LEAN_REF: addVector, lattice_volume, lattice_volume_index, lattice_volume_cyclic, lattice_volume_hadamard (KAM/Nekhoroshev/ResonanceGeometry/Volume.lean)
LEAN_NOTE: audit N89-G3 PASS WITH NOTES
NOTE: -

NODE: stepN:p8:lv-ab
KIND: step
TITLE: (a),(b)
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-ab@L83-L83
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-ab@L83-L83
CONTRACT_ID: stepN:p8:lv-ab
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: lattice basis matrices A, Ã = AU
SOURCE_QUANTIFIERS: Λ; A, Ã
SOURCE_CONCLUSION: det(ÃᵀÃ) = det(AᵀA); AᵀA integer matrix with positive determinant, so ¦Λ¦ ≥ 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:lattice-basis, bpN:p8:ext-gram, bpN:p8:volume-def, bpN:p8:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:lattice-basis | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-ab@L83-L83 | Ã = AU with det U = ±1 (b)
EDGE: bpN:p8:ext-gram | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-ab@L83-L83 | det multiplicative, det Uᵀ = det U, det(AᵀA) > 0
EDGE: bpN:p8:volume-def | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-ab@L83-L83 | ¦Θ¦ = 1 and ¦Λ¦ = sqrt det(AᵀA)
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-ab@L83-L83 | lattice objects, their spans/dimensions or the trivial/full lattice are used at this consumer; SPEC requires the package directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:lv-c
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-c@L84-L84
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-c@L84-L84
CONTRACT_ID: stepN:p8:lv-c
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Γ ≤ Λ equal dimension; Ã = AN
SOURCE_QUANTIFIERS: Γ, Λ
SOURCE_CONCLUSION: ¦Γ¦² = (det N)²¦Λ¦², ¦det N¦ ≥ 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:lattice-basis, bpN:p8:volume-def, bpN:p8:ext-units, bpN:p8:lattice, bpN:p8:ext-gram
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:lattice-basis | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-c@L84-L84 | N ∈ ℤ^{d×d}, det N ≠ 0 by (c)
EDGE: bpN:p8:volume-def | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-c@L84-L84 | ¦Γ¦, ¦Λ¦ via basis matrices
EDGE: bpN:p8:ext-units | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-c@L84-L84 | nonzero integer has modulus ≥ 1
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-c@L84-L84 | lattice objects, their spans/dimensions or the trivial/full lattice are used at this consumer; SPEC requires the package directly
EDGE: bpN:p8:ext-gram | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-c@L84-L84 | the determinant of N-transpose (A-transpose A) N is expanded multiplicatively
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:lv-d
KIND: step
TITLE: (d)
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-d@L85-L85
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-d@L85-L85
CONTRACT_ID: stepN:p8:lv-d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: g ∈ ℤⁿ∖{0}
SOURCE_QUANTIFIERS: g
SOURCE_CONCLUSION: ¦ℤg¦ = ‖g‖, ¦ℤⁿ¦ = 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:volume-def, bpN:p8:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:volume-def | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-d@L85-L85 | A = g and A = 1 as basis matrices
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-d@L85-L85 | lattice objects, their spans/dimensions or the trivial/full lattice are used at this consumer; SPEC requires the package directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:lv-e
KIND: step
TITLE: (e)
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-e@L86-L86
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-e@L86-L86
CONTRACT_ID: stepN:p8:lv-e
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Λ lattice; k ∈ ℤⁿ∖W_Λ
SOURCE_QUANTIFIERS: Λ; k
SOURCE_CONCLUSION: Q_Λ k ≠ 0; (A|k) basis of Λ+ℤk, dimension d+1; ¦Λ+ℤk¦ = ¦Λ¦‖Q_Λ k‖
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:projection, bpN:p8:ext-schur, bpN:p8:volume-def, bpN:p8:lattice, stepN:p8:lv-d, bpN:p8:ext-gram
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:projection | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-e@L86-L86 | (a): Q_Λ k ≠ 0, k·Π_Λ k = ‖Π_Λ k‖², Pythagoras
EDGE: bpN:p8:ext-schur | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-e@L86-L86 | Schur determinant formula
EDGE: bpN:p8:volume-def | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-e@L86-L86 | ¦Λ+ℤk¦² = det(A′ᵀA′)
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-e@L86-L86 | W_Λ, dimension count
EDGE: stepN:p8:lv-d | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-e@L86-L86 | case Λ = Θ
EDGE: bpN:p8:ext-gram | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-e@L86-L86 | G = AᵀA invertible
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:lv-f
KIND: step
TITLE: (f)
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-f@L87-L87
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-f@L87-L87
CONTRACT_ID: stepN:p8:lv-f
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v_1..v_d ∈ ℤⁿ ℝ-independent generating Γ
SOURCE_QUANTIFIERS: Γ; v_j
SOURCE_CONCLUSION: ¦Γ¦ ≤ ∏‖v_i‖
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p8:lv-e, bpN:p8:projection, bpN:p8:volume-def, bpN:p8:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p8:lv-e | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-f@L87-L87 | induction ¦Γ_j¦ = ¦Γ_{j−1}¦‖Q v_j‖
EDGE: bpN:p8:projection | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-f@L87-L87 | ‖Q v‖ ≤ ‖v‖
EDGE: bpN:p8:volume-def | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-f@L87-L87 | start ¦Θ¦ = 1
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-f@L87-L87 | lattice objects, their spans/dimensions or the trivial/full lattice are used at this consumer; SPEC requires the package directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p8:klattice
KIND: definition
TITLE: $K$-lattices
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:klattice@L96-L99
PROOF_SOURCE: -
CONTRACT_ID: bpN:p8:klattice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data: K ≥ 0, ℰ_K = {k∈ℤⁿ: ‖k‖ ≤ K} from the L9 convention)
SOURCE_QUANTIFIERS: n; K ≥ 0; Λ
SOURCE_CONCLUSION: defines K-lattice (Λ generated by Λ∩ℰ_K), maximal K-lattice (every K-lattice Λ′ ⊃ Λ with dim Λ′ = dim Λ equals Λ), 𝕄_K, 𝕄_K^d
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:klattice@L97-L98 | lattice, dimension
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: PROVED
LEAN_REF: klattice, maximalK (KAM/Nekhoroshev/ResonanceGeometry/Maximal.lean)
LEAN_NOTE: audit N89-G4 PASS WITH NOTES
NOTE: Package (SPEC). Candidate edge to bpN:p8:maximal dropped (forward pointer in \source). The ball ℰ_K is notation fixed in the prose L9 (coverage p8:prose-L9-L9).

NODE: bpN:p8:maximal
KIND: lemma
TITLE: Maximal $K$-lattices
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:maximal@L101-L111
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:maximal@L112-L118
CONTRACT_ID: bpN:p8:maximal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K ≥ 0; Λ a K-lattice
SOURCE_QUANTIFIERS: K; Λ; Γ; k; d
SOURCE_CONCLUSION: (a) for a K-lattice Lambda, Lambda in M_K iff E_K intersect W_Lambda is contained in Lambda; Theta is maximal, and a saturated K-lattice is maximal; (b) every K-lattice Gamma is contained in a maximal K-lattice of equal dimension, including the rank-one assertion for nonzero k in E_K; (c) IF Lambda in M_K and k in E_K minus Lambda, then k not in W_Lambda, dim Lambda < n, and Lambda+Zk is a K-lattice of dimension dim Lambda+1; (d) IF Lambda in M_K and dim Lambda=n then E_K is contained in Lambda; if also K>=1 then Lambda=Z^n; Z^n in M_K for K>=1; if 0<=K<1 then M_K={Theta}; (e) IF Lambda in M_K has dimension d then 1<=|Lambda|<=K^d
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:klattice, bpN:p8:lattice, bpN:p8:volume-def, stepN:p8:mx-char, stepN:p8:mx-exist, stepN:p8:mx-c, stepN:p8:mx-d, stepN:p8:mx-e
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:klattice | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:maximal@L102-L102 | K-lattice, 𝕄_K
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:maximal@L102-L103 | W_Λ, dimension
EDGE: bpN:p8:volume-def | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:maximal@L108-L108 | the volume bound is stated here, not in the source note L110
EDGE: stepN:p8:mx-char | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:maximal@L113-L113 | proof (a)
EDGE: stepN:p8:mx-exist | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:maximal@L114-L114 | proof (b)
EDGE: stepN:p8:mx-c | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:maximal@L115-L115 | proof (c)
EDGE: stepN:p8:mx-d | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:maximal@L116-L116 | proof (d)
EDGE: stepN:p8:mx-e | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:maximal@L117-L117 | proof (e)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: PROVED
LEAN_REF: maximal (KAM/Nekhoroshev/ResonanceGeometry/Maximal.lean)
LEAN_NOTE: audit N89-G4 PASS WITH NOTES
NOTE: -

NODE: stepN:p8:mx-char
KIND: step
TITLE: Characterisation
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-char@L113-L113
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-char@L113-L113
CONTRACT_ID: stepN:p8:mx-char
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Λ a K-lattice
SOURCE_QUANTIFIERS: K; Λ
SOURCE_CONCLUSION: Λ ∈ 𝕄_K iff ℰ_K∩W_Λ ⊂ Λ; Θ and saturated K-lattices maximal
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:klattice, bpN:p8:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:klattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-char@L113-L113 | K-lattice and maximality definitions
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-char@L113-L113 | W_Λ, equal dimension from equal span
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:mx-exist
KIND: step
TITLE: Existence
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-exist@L114-L114
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-exist@L114-L114
CONTRACT_ID: stepN:p8:mx-exist
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Γ a K-lattice
SOURCE_QUANTIFIERS: K; Γ
SOURCE_CONCLUSION: Γ ⊂ Λ ∈ 𝕄_K with dim Λ = dim Γ; k ∈ ℰ_K∖{0} lies in some Λ ∈ 𝕄_K^1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:klattice, bpN:p8:ext-basic, bpN:p8:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:klattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-exist@L114-L114 | K-lattices, maximality
EDGE: bpN:p8:ext-basic | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-exist@L114-L114 | finite nonempty poset has a maximal element; ℰ_K finite
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-exist@L114-L114 | lattice objects, their spans/dimensions or the trivial/full lattice are used at this consumer; SPEC requires the package directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:mx-c
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-c@L115-L115
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-c@L115-L115
CONTRACT_ID: stepN:p8:mx-c
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Λ ∈ 𝕄_K; k ∈ ℰ_K∖Λ
SOURCE_QUANTIFIERS: K; Λ; k
SOURCE_CONCLUSION: k ∉ W_Λ, dim Λ < n, Λ+ℤk is a K-lattice of dimension dim Λ + 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p8:mx-char, bpN:p8:klattice, bpN:p8:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p8:mx-char | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-c@L115-L115 | (a) and the K-lattice argument of Step Characterisation
EDGE: bpN:p8:klattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-c@L115-L115 | K-lattice
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-c@L115-L115 | lattice objects, their spans/dimensions or the trivial/full lattice are used at this consumer; SPEC requires the package directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:mx-d
KIND: step
TITLE: (d)
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-d@L116-L116
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-d@L116-L116
CONTRACT_ID: stepN:p8:mx-d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Λ ∈ 𝕄_K, dim Λ = n
SOURCE_QUANTIFIERS: K; Λ
SOURCE_CONCLUSION: ℰ_K ⊂ Λ; Λ = ℤⁿ ∈ 𝕄_K if K ≥ 1; 𝕄_K = {Θ} if K < 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p8:mx-char, bpN:p8:klattice, bpN:p8:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p8:mx-char | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-d@L116-L116 | (a) for ℰ_K ⊂ Λ and ℤⁿ ∈ 𝕄_K
EDGE: bpN:p8:klattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-d@L116-L116 | K-lattice, 𝕄_K
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-d@L116-L116 | lattice objects, their spans/dimensions or the trivial/full lattice are used at this consumer; SPEC requires the package directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:mx-e
KIND: step
TITLE: (e)
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-e@L117-L117
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-e@L117-L117
CONTRACT_ID: stepN:p8:mx-e
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Λ ∈ 𝕄_K of dimension d
SOURCE_QUANTIFIERS: K; Λ; v_i
SOURCE_CONCLUSION: 1 ≤ ¦Λ¦ ≤ K^d
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:lattice-volume, bpN:p8:ext-basic, bpN:p8:klattice, bpN:p8:lattice, bpN:p8:volume-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:lattice-volume | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-e@L117-L117 | (b) lower bound, (c),(f) upper bound
EDGE: bpN:p8:ext-basic | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-e@L117-L117 | a spanning set contains d independent vectors
EDGE: bpN:p8:klattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-e@L117-L117 | Λ∩ℰ_K spans W_Λ (K-lattice)
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-e@L117-L117 | lattice objects, their spans/dimensions or the trivial/full lattice are used at this consumer; SPEC requires the package directly
EDGE: bpN:p8:volume-def | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-e@L117-L117 | the lattice volume is used directly in the displayed computation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p8:blocks
KIND: definition
TITLE: Zones, blocks
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:blocks@L120-L127
PROOF_SOURCE: -
CONTRACT_ID: bpN:p8:blocks
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K ≥ 0; λ_1,…,λ_n > 0; Λ ∈ 𝕄_K
SOURCE_QUANTIFIERS: n; K; λ; Λ of dimension d
SOURCE_CONCLUSION: For Lambda in M_K of dimension d>=1, define delta_Lambda=lambda_d/|Lambda| and Z_Lambda={omega: dist_2(omega,R_Lambda)<delta_Lambda}={omega: ||Pi_Lambda omega||_2<delta_Lambda}. Set Z_Theta=R^n, Z_d^*=union over M_K^d of Z_Lambda for 1<=d<=n and Z_(n+1)^*=empty; for d>=1 set B_Lambda=Z_Lambda minus Z_(d+1)^*, B_Theta=R^n minus Z_1^*, and B_d^*=union over M_K^d of B_Lambda. These depend on K and the positive lambda data; an empty stratum gives an empty union.
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:klattice, bpN:p8:volume-def, bpN:p8:projection, bpN:p8:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:klattice | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:blocks@L121-L122 | 𝕄_K, 𝕄_K^d
EDGE: bpN:p8:volume-def | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:blocks@L122-L123 | ¦Λ¦ in δ_Λ
EDGE: bpN:p8:projection | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:blocks@L123-L124 | dist₂(ω,R_Λ) = ‖Π_Λ ω‖ by projection(c)
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:blocks@L122-L123 | R_Λ, d, Θ
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: PROVED
LEAN_REF: zone, zoneStratum, blocks (KAM/Nekhoroshev/ResonanceGeometry/Blocks.lean)
LEAN_NOTE: audit N89-G5 PASS WITH NOTES
NOTE: Package (SPEC): D_Λ, δ_Λ, B_Λ, Z_Λ used by symbol in Parts 9 and 11c.

NODE: bpN:p8:blocks-cover
KIND: proposition
TITLE: Covering of frequency space
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:blocks-cover@L129-L132
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:blocks-cover@L133-L136
CONTRACT_ID: bpN:p8:blocks-cover
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K ≥ 0; λ_1..λ_n > 0
SOURCE_QUANTIFIERS: K; λ; ω ∈ ℝⁿ
SOURCE_CONCLUSION: ℝⁿ = B_Θ ∪ B_1^* ∪ … ∪ B_n^*: every ω lies in B_Λ for some Λ ∈ 𝕄_K, a finite family
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:blocks, bpN:p8:klattice, stepN:p8:bc-finite, stepN:p8:bc-top
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:blocks | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:blocks-cover@L130-L131 | B_Λ, B_Θ, B_d^*
EDGE: bpN:p8:klattice | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:blocks-cover@L130-L131 | 𝕄_K
EDGE: stepN:p8:bc-finite | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:blocks-cover@L134-L134 | proof step
EDGE: stepN:p8:bc-top | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:blocks-cover@L135-L135 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: PROVED
LEAN_REF: blocks_cover (KAM/Nekhoroshev/ResonanceGeometry/Blocks.lean)
LEAN_NOTE: audit N89-G5 PASS WITH NOTES
NOTE: -

NODE: stepN:p8:bc-finite
KIND: step
TITLE: Finite family
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:bc-finite@L134-L134
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:bc-finite@L134-L134
CONTRACT_ID: stepN:p8:bc-finite
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K ≥ 0
SOURCE_QUANTIFIERS: K
SOURCE_CONCLUSION: 𝕄_K finite
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:klattice, bpN:p8:ext-basic
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:klattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:bc-finite@L134-L134 | subgroups generated by subsets of ℰ_K
EDGE: bpN:p8:ext-basic | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:bc-finite@L134-L134 | ℰ_K finite
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: PROVED
LEAN_REF: blocks_cover (KAM/Nekhoroshev/ResonanceGeometry/Blocks.lean)
LEAN_NOTE: audit N89-G5 PASS WITH NOTES
NOTE: -

NODE: stepN:p8:bc-top
KIND: step
TITLE: Top dimension
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:bc-top@L135-L135
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:bc-top@L135-L135
CONTRACT_ID: stepN:p8:bc-top
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ω ∈ ℝⁿ
SOURCE_QUANTIFIERS: ω
SOURCE_CONCLUSION: ω ∈ B_Θ or ω ∈ B_Λ for Λ ∈ 𝕄_K^d with d = max{d: ω ∈ Z_d^*}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:blocks, bpN:p8:klattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:blocks | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:bc-top@L135-L135 | Z_d^*, B_Λ, B_Θ, Z_{n+1}^* = ∅
EDGE: bpN:p8:klattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:bc-top@L135-L135 | the maximal K-lattice family or its dimension stratum is used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: PROVED
LEAN_REF: blocks_cover (KAM/Nekhoroshev/ResonanceGeometry/Blocks.lean)
LEAN_NOTE: audit N89-G5 PASS WITH NOTES
NOTE: -

NODE: bpN:p8:sqrt
KIND: lemma
TITLE: A numerical inequality
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:sqrt@L140-L143
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:sqrt@L144-L146
CONTRACT_ID: bpN:p8:sqrt
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A ≥ √2
SOURCE_QUANTIFIERS: A
SOURCE_CONCLUSION: A² − 1 ≥ 1 > 0 and sqrt(A²−1) − 1 ≥ A − √2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: PROVED
LEAN_REF: sqrt (KAM/Nekhoroshev/ResonanceGeometry/GeomFormula.lean)
LEAN_NOTE: audit N89-G6 PASS WITH NOTES
NOTE: Pure real-number inequality; no dependencies.

NODE: bpN:p8:geometric
KIND: lemma
TITLE: Geometric Lemma
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geometric@L148-L158
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geometric@L169-L180
CONTRACT_ID: bpN:p8:geometric
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 1; K > 0; E > 0; A ≥ E + √2; λ_1..λ_n > 0 with λ_{d+1}/λ_d ≥ AK (1 ≤ d < n); 𝕄_K, δ_Λ, B_Λ as in Definition blocks
SOURCE_QUANTIFIERS: n; K; E; A; λ; (a) ω ∈ B_Θ, k; (b) Λ ∈ 𝕄_K with d ≥ 1, ω ∈ B_Λ, k
SOURCE_CONCLUSION: (a) ω ∈ B_Θ, k ∈ ℤⁿ, 0 < ‖k‖ ≤ K ⇒ ¦k·ω¦ ≥ λ_1; (b) Λ ∈ 𝕄_K, d ≥ 1, ω ∈ B_Λ, k ∈ ℤⁿ∖Λ, ‖k‖ ≤ K ⇒ ¦k·ω¦ ≥ E K δ_Λ and dist₂(ω,R_Λ) < δ_Λ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:blocks, bpN:p8:maximal, bpN:p8:lattice, stepN:p8:gl-theta, stepN:p8:gl-theta2, stepN:p8:gl-setup, stepN:p8:gl-vol, stepN:p8:gl-proj, stepN:p8:gl-div, bpN:p8:klattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:blocks | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geometric@L149-L152 | 𝕄_K, δ_Λ, B_Λ
EDGE: bpN:p8:maximal | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geometric@L154-L154 | (d): no such k when d = n
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geometric@L154-L154 | R_Λ, d
EDGE: stepN:p8:gl-theta | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geometric@L170-L170 | proof (a)
EDGE: stepN:p8:gl-theta2 | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geometric@L171-L171 | proof (a)
EDGE: stepN:p8:gl-setup | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geometric@L172-L172 | proof (b)
EDGE: stepN:p8:gl-vol | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geometric@L173-L173 | proof (b)
EDGE: stepN:p8:gl-proj | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geometric@L174-L174 | proof (b)
EDGE: stepN:p8:gl-div | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geometric@L177-L177 | proof (b)
EDGE: bpN:p8:klattice | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geometric@L151-L151 | the maximal K-lattice family or its dimension stratum is used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-delta-N-e
REVIEWER: sol-delta2-N-e
LEAN_STATUS: PROVED
LEAN_REF: geometric (KAM/Nekhoroshev/ResonanceGeometry/Geometric.lean)
LEAN_NOTE: audit N89-G6 PASS WITH NOTES
NOTE: Statement lines L148-L158; the separate proof environment is L169-L180. Candidate edge to geom-formula moved to the proof steps (gl-setup, gl-proj, gl-div), where it is used.

NODE: bpN:p8:geom-formula
KIND: lemma
TITLE: The projection formula
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geom-formula@L160-L164
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geom-formula@L165-L167
CONTRACT_ID: bpN:p8:geom-formula
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W the span of a basis matrix of a lattice (or W = {0}); k ∈ ℝⁿ∖W; W_+ = W + ℝk; Π = Π_W, Q = Q_W, Π_+ = Π_{W_+}
SOURCE_QUANTIFIERS: n; W; k; ω
SOURCE_CONCLUSION: Qk ≠ 0; Π_+ω − Πω = (Qk·ω/‖Qk‖²)Qk; k·ω = Πk·Πω + Qk·ω; ¦Qk·ω¦ = ‖Qk‖‖Π_+ω − Πω‖; ‖Π_+ω‖² = ‖Πω‖² + ‖Π_+ω − Πω‖²
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:lattice, bpN:p8:projection
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geom-formula@L161-L161 | W the span of a lattice basis matrix
EDGE: bpN:p8:projection | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geom-formula@L166-L166 | (a),(b): Π_+ is characterised by orthogonality; symmetry and idempotence of Π
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: PROVED
LEAN_REF: geom_formula (KAM/Nekhoroshev/ResonanceGeometry/GeomFormula.lean)
LEAN_NOTE: audit N89-G6 PASS WITH NOTES
NOTE: -

NODE: stepN:p8:gl-theta
KIND: step
TITLE: (a): reduction to dimension one
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta@L170-L170
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta@L170-L170
CONTRACT_ID: stepN:p8:gl-theta
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ω ∈ B_Θ; k ∈ ℤⁿ, 0 < ‖k‖ ≤ K
SOURCE_QUANTIFIERS: K; ω; k
SOURCE_CONCLUSION: exists Λ_k = ℤg ∈ 𝕄_K^1 with k = jg, ‖g‖ ≤ ‖k‖, ¦Λ_k¦ = ‖g‖, δ_{Λ_k} ≥ λ_1/‖k‖
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:maximal, bpN:p8:lattice-basis, bpN:p8:lattice-volume, bpN:p8:blocks, bpN:p8:lattice, bpN:p8:volume-def, bpN:p8:klattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:maximal | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta@L170-L170 | (b): Λ_k ∈ 𝕄_K^1 containing k
EDGE: bpN:p8:lattice-basis | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta@L170-L170 | (a): rank-one subgroup is ℤg
EDGE: bpN:p8:lattice-volume | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta@L170-L170 | (d): ¦ℤg¦ = ‖g‖
EDGE: bpN:p8:blocks | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta@L170-L170 | δ_Λ = λ_1/¦Λ¦
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta@L170-L170 | lattice objects, their spans/dimensions or the trivial/full lattice are used at this consumer; SPEC requires the package directly
EDGE: bpN:p8:volume-def | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta@L170-L170 | the lattice volume is used directly in the displayed computation
EDGE: bpN:p8:klattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta@L170-L170 | the maximal K-lattice family or its dimension stratum is used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:gl-theta2
KIND: step
TITLE: (a): conclusion
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta2@L171-L171
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta2@L171-L171
CONTRACT_ID: stepN:p8:gl-theta2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ω ∈ B_Θ; Λ_k from the previous step
SOURCE_QUANTIFIERS: ω; k
SOURCE_CONCLUSION: ¦k·ω¦ ≥ ‖k‖δ_{Λ_k} ≥ λ_1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p8:gl-theta, bpN:p8:blocks, bpN:p8:projection, bpN:p8:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p8:gl-theta | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta2@L171-L171 | Λ_k, δ_{Λ_k} ≥ λ_1/‖k‖
EDGE: bpN:p8:blocks | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta2@L171-L171 | ω ∉ Z_1^* ⊃ Z_{Λ_k}
EDGE: bpN:p8:projection | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta2@L171-L171 | (c): dist₂(ω,k^⊥) = ‖Π_{ℝk}ω‖
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta2@L171-L171 | R_{Λ_k} = g^⊥
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:gl-setup
KIND: step
TITLE: (b): setting
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-setup@L172-L172
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-setup@L172-L172
CONTRACT_ID: stepN:p8:gl-setup
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Λ ∈ 𝕄_K, d ≥ 1; ω ∈ B_Λ; k ∈ ℤⁿ∖Λ, ‖k‖ ≤ K
SOURCE_QUANTIFIERS: Λ; ω; k
SOURCE_CONCLUSION: k ∉ W_Λ, d < n; Λ_+ ∈ 𝕄_K^{d+1} with Λ_+ ⊃ Λ+ℤk, W_{Λ_+} = W_+, Π_{Λ_+} = Π_+; ω ∈ Z_Λ; fixes V=|Lambda|, lambda=lambda_d, delta=delta_Lambda=lambda/V, Pi=Pi_Lambda, Q=Q_Lambda, V_+=|Lambda_+| and lambda_+=lambda_(d+1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:maximal, bpN:p8:geom-formula, bpN:p8:blocks, bpN:p8:volume-def, bpN:p8:lattice, bpN:p8:klattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:maximal | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-setup@L172-L172 | (c) and (b): k ∉ W_Λ and existence of Λ_+
EDGE: bpN:p8:geom-formula | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-setup@L172-L172 | Π_{Λ_+} = Π_+ of the projection formula
EDGE: bpN:p8:blocks | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-setup@L172-L172 | B_Λ ⊂ Z_Λ, δ_Λ = λ_d/¦Λ¦
EDGE: bpN:p8:volume-def | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-setup@L172-L172 | V = ¦Λ¦, V_+ = ¦Λ_+¦
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-setup@L172-L172 | lattice objects, their spans/dimensions or the trivial/full lattice are used at this consumer; SPEC requires the package directly
EDGE: bpN:p8:klattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-setup@L172-L172 | the maximal K-lattice family or its dimension stratum is used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:gl-vol
KIND: step
TITLE: Volumes
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-vol@L173-L173
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-vol@L173-L173
CONTRACT_ID: stepN:p8:gl-vol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting of Step (b): setting
SOURCE_QUANTIFIERS: Λ, Λ_+, k
SOURCE_CONCLUSION: V_+ ≤ V‖Qk‖, ‖Qk‖ ≥ V_+/V, V_+ ≤ KV
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:lattice-volume, stepN:p8:gl-setup, bpN:p8:projection, bpN:p8:lattice, bpN:p8:volume-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:lattice-volume | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-vol@L173-L173 | (c),(e)
EDGE: stepN:p8:gl-setup | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-vol@L173-L173 | Λ_+ ⊃ Λ+ℤk
EDGE: bpN:p8:projection | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-vol@L173-L173 | ‖Qk‖ ≤ ‖k‖
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-vol@L173-L173 | lattice objects, their spans/dimensions or the trivial/full lattice are used at this consumer; SPEC requires the package directly
EDGE: bpN:p8:volume-def | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-vol@L173-L173 | the lattice volume is used directly in the displayed computation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:gl-proj
KIND: step
TITLE: The two projections
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-proj@L174-L176
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-proj@L174-L176
CONTRACT_ID: stepN:p8:gl-proj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; ω ∈ B_Λ, ω ∉ Z_{d+1}^*; λ_{d+1}/λ_d ≥ AK; A ≥ E+√2
SOURCE_QUANTIFIERS: Λ; ω
SOURCE_CONCLUSION: ‖Π ω‖ < Kλ/V_+, ‖Π_+ω‖ ≥ AKλ/V_+, ‖Π_+ω − Πω‖ ≥ (Kλ/V_+) sqrt(A²−1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p8:gl-vol, bpN:p8:sqrt, bpN:p8:geom-formula, bpN:p8:blocks, stepN:p8:gl-setup
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p8:gl-vol | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-proj@L174-L174 | V_+ ≤ KV
EDGE: bpN:p8:sqrt | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-proj@L175-L175 | A² − 1 > 0
EDGE: bpN:p8:geom-formula | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-proj@L176-L176 | ‖Π_+ω−Πω‖² = ‖Π_+ω‖² − ‖Πω‖²
EDGE: bpN:p8:blocks | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-proj@L174-L174 | ω ∈ Z_Λ, ω ∉ Z_{Λ_+} ⊂ Z_{d+1}^*
EDGE: stepN:p8:gl-setup | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-proj@L174-L174 | Λ_+, V_+
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:gl-div
KIND: step
TITLE: The divisor
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-div@L177-L179
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-div@L177-L179
CONTRACT_ID: stepN:p8:gl-div
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: steps above
SOURCE_QUANTIFIERS: Λ; ω; k
SOURCE_CONCLUSION: ¦k·ω¦ ≥ K δ (sqrt(A²−1) − 1) ≥ K δ (A−√2) ≥ E K δ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:geom-formula, bpN:p8:sqrt, stepN:p8:gl-proj, stepN:p8:gl-vol, bpN:p8:ext-basic, stepN:p8:gl-setup
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:geom-formula | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-div@L177-L177 | k·ω = Πk·Πω + Qk·ω, ¦Qk·ω¦ = ‖Qk‖‖Π_+ω−Πω‖
EDGE: bpN:p8:sqrt | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-div@L179-L179 | sqrt(A²−1) − 1 ≥ A − √2
EDGE: stepN:p8:gl-proj | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-div@L178-L178 | lower bound on ‖Π_+ω−Πω‖
EDGE: stepN:p8:gl-vol | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-div@L178-L178 | ‖Qk‖ ≥ V_+/V
EDGE: bpN:p8:ext-basic | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-div@L178-L178 | Cauchy–Schwarz ¦Πk·Πω¦ ≤ ‖k‖‖Πω‖
EDGE: stepN:p8:gl-setup | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-div@L178-L178 | δ = λ/V and ω ∈ Z_Λ
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p8:covering
KIND: lemma
TITLE: Covering Lemma
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:covering@L184-L195
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:covering@L196-L201
CONTRACT_ID: bpN:p8:covering
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 1; p, b, r_0, M, m > 0; K ≥ 1; A ≥ pM/(bm) + √2; P any set; ω: P → ℝⁿ any map
SOURCE_QUANTIFIERS: n; p, b, r_0, M, m; K; A; P; ω; Λ
SOURCE_CONCLUSION: with λ_d = (b m r_0/(AK)ⁿ)(AK)^d, r_Λ = (r_0/(AK)ⁿ)(AK)^d/¦Λ¦, α_Λ = pMK r_Λ, δ_Λ = b m r_Λ, D_Λ = {I∈P: ω(I)∈B_Λ}: (a) P = ∪_{Λ∈𝕄_K} D_Λ (finite); (b) δ_Λ = λ_d/¦Λ¦ for d ≥ 1; (c) nonresonance ¦k·ω(I)¦ ≥ λ_1 ≥ α_Θ on D_Θ, ≥ α_Λ on D_Λ for k ∉ Λ, ‖k‖ ≤ K, and dist₂(ω(I),R_Λ) < δ_Λ; (d) r_Θ = r_0/(AK)ⁿ ≤ r_Λ ≤ r_0/(AK) for 1 ≤ dim Λ < n, r_{ℤⁿ} = r_0
CONSTANT_SCOPE: A, λ_d, r_Λ, α_Λ, δ_Λ, D_Λ are defined from the data (n, p, b, r_0, M, m, K, A, P, ω); no further dependence
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:blocks, bpN:p8:klattice, bpN:p8:volume-def, bpN:p8:lattice, stepN:p8:cv-params, stepN:p8:cv-cover, stepN:p8:cv-nonres, stepN:p8:cv-radii
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:blocks | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:covering@L192-L193 | blocks B_Λ for these K, λ
EDGE: bpN:p8:klattice | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:covering@L192-L192 | 𝕄_K
EDGE: bpN:p8:volume-def | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:covering@L186-L187 | ¦Λ¦ in r_Λ
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:covering@L187-L187 | dim Λ, Θ, R_Λ
EDGE: stepN:p8:cv-params | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:covering@L197-L197 | proof step
EDGE: stepN:p8:cv-cover | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:covering@L198-L198 | proof step
EDGE: stepN:p8:cv-nonres | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:covering@L199-L199 | proof step
EDGE: stepN:p8:cv-radii | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:covering@L200-L200 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: PROVED
LEAN_REF: covering, CoverParams.lam, CoverParams.radius, CoverParams.alpha, CoverParams.delta, actionBlock (KAM/Nekhoroshev/ResonanceGeometry/Covering.lean)
LEAN_NOTE: audit N89-G7 PASS WITH NOTES
NOTE: Package-like (SPEC): r_Λ, α_Λ, δ_Λ, D_Λ are used by symbol in Parts 9 and 11c via this lemma.

NODE: stepN:p8:cv-params
KIND: step
TITLE: Parameters of the Geometric Lemma
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-params@L197-L197
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-params@L197-L197
CONTRACT_ID: stepN:p8:cv-params
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Covering Lemma data
SOURCE_QUANTIFIERS: data
SOURCE_CONCLUSION: lambda_(d+1)/lambda_d=AK for 1<=d<n, all lambda_d>0; E=pM/(bm)>0, A>=E+sqrt(2), K>0, so the Geometric Lemma hypotheses hold. FOR dim Lambda=d>=1, delta_Lambda=lambda_d/|Lambda| is the zone radius; for Theta only the positive auxiliary number delta_Theta=bm r_Theta is defined. EK delta_Lambda=alpha_Lambda.
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:geometric, bpN:p8:blocks, bpN:p8:volume-def, bpN:p8:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:geometric | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-params@L197-L197 | Geometric Lemma applies (hypotheses verified)
EDGE: bpN:p8:blocks | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-params@L197-L197 | δ_Λ = λ_d/¦Λ¦ is the radius of Z_Λ
EDGE: bpN:p8:volume-def | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-params@L197-L197 | ¦Λ¦ in r_Λ
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-params@L197-L197 | lattice objects, their spans/dimensions or the trivial/full lattice are used at this consumer; SPEC requires the package directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:cv-cover
KIND: step
TITLE: Covering
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-cover@L198-L198
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-cover@L198-L198
CONTRACT_ID: stepN:p8:cv-cover
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I ∈ P
SOURCE_QUANTIFIERS: I
SOURCE_CONCLUSION: ω(I) ∈ B_Λ for some Λ ∈ 𝕄_K, so I ∈ D_Λ; finiteness
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:blocks-cover, bpN:p8:blocks, bpN:p8:klattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:blocks-cover | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-cover@L198-L198 | covering and finiteness at the point ω(I)
EDGE: bpN:p8:blocks | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-cover@L198-L198 | D_Λ via B_Λ
EDGE: bpN:p8:klattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-cover@L198-L198 | the maximal K-lattice family or its dimension stratum is used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:cv-nonres
KIND: step
TITLE: Nonresonance
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-nonres@L199-L199
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-nonres@L199-L199
CONTRACT_ID: stepN:p8:cv-nonres
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I ∈ D_Λ
SOURCE_QUANTIFIERS: I; Λ; k
SOURCE_CONCLUSION: ¦k·ω(I)¦ ≥ α_Λ (and ≥ λ_1 ≥ α_Θ for Λ = Θ); dist₂(ω(I),R_Λ) < δ_Λ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:geometric, stepN:p8:cv-params, bpN:p8:blocks
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:geometric | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-nonres@L199-L199 | (b),(a) at the point ω(I)
EDGE: stepN:p8:cv-params | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-nonres@L199-L199 | EKδ_Λ = α_Λ and parameter verification
EDGE: bpN:p8:blocks | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-nonres@L199-L199 | ω(I) ∈ B_Λ
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8
REVIEWER: sol-review-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p8:cv-radii
KIND: step
TITLE: Radii
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-radii@L200-L200
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-radii@L200-L200
CONTRACT_ID: stepN:p8:cv-radii
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Λ ∈ 𝕄_K; K ≥ 1; A ≥ 1
SOURCE_QUANTIFIERS: Λ
SOURCE_CONCLUSION: r_Θ ≤ r_Λ ≤ r_0/(AK) for 1 ≤ d < n; r_{ℤⁿ} = r_0; r_Θ ≤ r_Λ ≤ r_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:maximal, bpN:p8:lattice-volume, bpN:p8:lattice, bpN:p8:volume-def, bpN:p8:klattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:maximal | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-radii@L200-L200 | (e): 1 ≤ ¦Λ¦ ≤ K^d; (d): Λ = ℤⁿ when d = n
EDGE: bpN:p8:lattice-volume | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-radii@L200-L200 | (b), ¦ℤⁿ¦ = 1 by (d)
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-radii@L200-L200 | lattice objects, their spans/dimensions or the trivial/full lattice are used at this consumer; SPEC requires the package directly
EDGE: bpN:p8:volume-def | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-radii@L200-L200 | the lattice volume is used directly in the displayed computation
EDGE: bpN:p8:klattice | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-radii@L200-L200 | the maximal K-lattice family or its dimension stratum is used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p8:cutoffs
KIND: corollary
TITLE: Euclidean versus $\ell^1$ cut-offs; interface for Parts~\ref{bpN:p6}, \ref{bpN:p7} and~9
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:cutoffs@L203-L211
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:cutoffs@L212-L214
CONTRACT_ID: bpN:p8:cutoffs
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting of Lemma covering with K = K_g; K_a ≥ 0 analytic cut-off; (b) K_a ≤ K_g; (c) K_g ≥ √n K_a > 0
SOURCE_QUANTIFIERS: n; K_g; K_a; Λ ∈ 𝕄_{K_g}; I ∈ D_Λ; k
SOURCE_CONCLUSION: (a) Z_{K_a} ⊂ ℰ_{K_a} ⊂ Z_{√n K_a}; (b) K_a ≤ K_g ⇒ I is (α_Λ,K_a)-nonresonant modulo Λ (¦k·ω(I)¦ ≥ α_Λ for k ∈ Z_{K_a}∖Λ) and dist₂(ω(I),R_Λ) < δ_Λ; (c) K_g ≥ √n K_a ⇒ r_Λ = α_Λ/(pMK_g) ≤ α_Λ/(p√n M K_a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:covering, bpN:p1:norm-compare, bpN:p6:setting, bpN:p7:resonance-data, bpN:p8:klattice, stepN:p8:co-incl, bpN:p8:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:covering | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:cutoffs@L204-L204 | setting, r_Λ, α_Λ, δ_Λ, D_Λ
EDGE: bpN:p1:norm-compare | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:cutoffs@L206-L206 | (a) via norm-compare(b)
EDGE: bpN:p6:setting | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:cutoffs@L207-L207 | nonresonance modulo Λ of cond-nr; Z_{K_a}
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:cutoffs@L207-L207 | closeness to exact Λ-resonances
EDGE: bpN:p8:klattice | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:cutoffs@L207-L207 | Λ ∈ 𝕄_{K_g}
EDGE: stepN:p8:co-incl | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:cutoffs@L213-L213 | proof step
EDGE: bpN:p8:lattice | blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:cutoffs@L207-L207 | lattice objects, their spans/dimensions or the trivial/full lattice are used at this consumer; SPEC requires the package directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-delta-N-e
REVIEWER: sol-delta2-N-e
LEAN_STATUS: PROVED
LEAN_REF: cutoffs (KAM/Nekhoroshev/ResonanceGeometry/Covering.lean)
LEAN_NOTE: audit N89-G7 PASS WITH NOTES
NOTE: Candidate edges to bpN:p7:resonant-prop2 (L209: the radius condition of Prop (c) is only matched, not used) and bpN:p8:direction (remark, excluded) dropped: breaks the SPEC candidate cycle through bpN:p8:cutoffs -> p7:resonant-prop2. Consumers (Part 9, 11c) apply (b) and (c).

NODE: stepN:p8:co-incl
KIND: step
TITLE: Inclusions
STATEMENT_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:co-incl@L213-L213
PROOF_SOURCE: blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:co-incl@L213-L213
CONTRACT_ID: stepN:p8:co-incl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Corollary setting
SOURCE_QUANTIFIERS: K_a; K_g
SOURCE_CONCLUSION: (a) is norm-compare(b); (b) for k ∈ Z_{K_a}∖Λ, ‖k‖ ≤ ¦k¦₁ ≤ K_a ≤ K_g so Lemma covering(c) applies; (c) 1/(pMK_g) ≤ 1/(p√n M K_a), α_Λ = pMK_g r_Λ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:norm-compare, bpN:p8:covering, bpN:p6:setting, bpN:p7:resonance-data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:norm-compare | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:co-incl@L213-L213 | (a) = norm-compare(b); ‖k‖ ≤ ¦k¦₁
EDGE: bpN:p8:covering | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:co-incl@L213-L213 | (c) and closeness of Lemma covering; α_Λ = pMKr_Λ
EDGE: bpN:p6:setting | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:co-incl@L213-L213 | clause (b) uses the analytic Z_K cut-off and nonresonance predicate (N1)
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:co-incl@L213-L213 | the closeness clause in (b) uses the exact-resonance predicate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p8+sol-review-N-e
REVIEWER: sol-delta-N-e
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
