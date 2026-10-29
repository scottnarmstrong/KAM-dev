NODE: bpP:p1:ext-comp
KIND: external
TITLE: bpP:p1:ext-comp
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:ext-comp@L21-L21
PROOF_SOURCE: -
CONTRACT_ID: bpP:p1:ext-comp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (external fact)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: chain rule for fderiv and HasDerivAt; compositions of real analytic maps are real analytic (AnalyticAt.comp, AnalyticOnNhd.comp; the latter needs the range of the inner map inside the set where the outer map is analytic); sums and products of analytic maps are analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p1:ext-ift
KIND: external
TITLE: bpP:p1:ext-ift
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:ext-ift@L22-L22
PROOF_SOURCE: -
CONTRACT_ID: bpP:p1:ext-ift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (external fact)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: inverse function theorem: a C^1 map Psi with D Psi(z0) invertible is a homeomorphism from a neighbourhood of z0 onto an open set with C^1 inverse (a C^1 map has a strict derivative; a bijective linear map of R^2d is a continuous linear equivalence)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p1:ext-area
KIND: external
TITLE: Borel
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:ext-area@L23-L23
PROOF_SOURCE: -
CONTRACT_ID: bpP:p1:ext-area
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (external fact)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: area formula: for Borel A, meas Psi(A) <= integral over A of ¦det D Psi¦ (no injectivity); equality if Psi is injective on A (also for NullMeasurableSet A, the subscript-0 version); differentiable images of null sets are null
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p1:ext-borel
KIND: external
TITLE: Null sets need not be Borel
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:ext-borel@L24-L24
PROOF_SOURCE: -
CONTRACT_ID: bpP:p1:ext-borel
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (external fact)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: a Lebesgue measurable subset of R^N is an F_sigma set union a null set; closed sets are sigma-compact; continuous images of compact sets are compact; null sets need not be Borel (measurable means NullMeasurableSet unless Borel is said); injective continuous images of Borel sets are Borel (MeasurableSet.image_of_continuousOn_injOn)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p1:ext-det
KIND: external
TITLE: bpP:p1:ext-det
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:ext-det@L25-L25
PROOF_SOURCE: -
CONTRACT_ID: bpP:p1:ext-det
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (external fact)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: det(AB)=det A det B, det A^T=det A, det M_0=1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p1:omega-algebra
KIND: lemma
TITLE: Algebra of $\Omega$ and $X_H$
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:omega-algebra@L30-L34
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:omega-algebra@L35-L38
CONTRACT_ID: bpP:p1:omega-algebra
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: M_0, J_0, Omega, X_ell, X_H of conv#data; (a) ell linear, H any function; (b) A a real 2d x 2d matrix with Omega(Au,Av)=c Omega(u,v) for all u,v and c != 0; (c) A, c as in (b)
SOURCE_QUANTIFIERS: d; then (a) all w, linear ell, z, H; (b) A, c != 0, then every linear ell; (c) A, c
SOURCE_CONCLUSION: (a) M_0^T=-M_0, M_0^2=-1, Omega nondegenerate, Omega(w,X_ell)=ell(w) for all w and linear ell, X_ell unique with this property, Omega(w,X_H(z))=DH(z)w for every z; (b) A invertible, ¦det A¦=¦c¦^d, X_{ell o A}=c A^{-1} X_ell for every linear ell; (c) Omega(Au,Av)=c Omega(u,v) iff A^T(-M_0)A=c(-M_0), independent of the sign convention of the symplectic form
CONSTANT_SCOPE: none (c arbitrary nonzero real, A arbitrary matrix)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p1:oa-mat, stepP:p1:oa-b, bpP:p1:conv#data, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p0:hamsymp#symplecticForm
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p1:oa-mat | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:omega-algebra@L36-L36 | proof step: matrix algebra, (a) and uniqueness
EDGE: stepP:p1:oa-b | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:omega-algebra@L37-L37 | proof step: (b) and (c)
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:omega-algebra@L31-L31 | M_0, Omega, X_ell, X_H notation
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:omega-algebra@L31-L31 | X_H(z) in the last clause of (a)
EDGE: bpP:p0:hamsymp#symplecticForm | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:omega-algebra@L31-L31 | Omega, the frozen form
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: symplecticForm_antisymm, eq_zero_of_symplecticForm_right, symplecticForm_linearField, eq_linearField_iff, symplecticForm_hamiltonianVectorField, bijective_of_symplectic, abs_det_of_symplectic, apply_linearField_comp_of_symplectic, symplectic_neg_iff (KAM/Planetary/Hamiltonian/Algebra.lean)
LEAN_NOTE: audit PP1-1 PASS WITH NOTES (audit 2 closes hygiene H1); matrix M_0 clauses replaced by coordinate-free bilinear statements per design
NOTE: -

NODE: stepP:p1:oa-mat
KIND: step
TITLE: Matrices
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:oa-mat@L36-L36
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:oa-mat@L36-L36
CONTRACT_ID: stepP:p1:oa-mat
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: block form of M_0, X_ell=J_0 grad ell (conv#data)
SOURCE_QUANTIFIERS: all w, linear ell
SOURCE_CONCLUSION: M_0^T=-M_0, M_0^2=-1, M_0 X_ell = grad ell so Omega(w,X_ell)=w^T M_0 X_ell=ell(w); uniqueness since M_0 is invertible
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:oa-mat@L36-L36 | M_0, J_0, X_ell and Omega=v^T M_0 w
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: symplecticForm_linearField, eq_linearField_iff, eq_zero_of_symplecticForm_right (KAM/Planetary/Hamiltonian/Algebra.lean)
LEAN_NOTE: audit PP1-1 PASS WITH NOTES (audit 2 closes hygiene H1); named by audit (apply_eq_sum helper)
NOTE: -

NODE: stepP:p1:oa-b
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:oa-b@L37-L37
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:oa-b@L37-L37
CONTRACT_ID: stepP:p1:oa-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A a real 2d x 2d matrix; c != 0; Omega(Au,Av)=c Omega(u,v) for all u,v; ell linear
SOURCE_QUANTIFIERS: A, c != 0, ell
SOURCE_CONCLUSION: (det A)^2=c^{2d}, so A invertible and ¦det A¦=¦c¦^d; Omega(w,c A^{-1}X_ell)=ell(A w) for all w, so c A^{-1}X_ell=X_{ell o A}; (c) is the displayed matrix identity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:ext-det, stepP:p1:oa-mat, bpP:p1:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:ext-det | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:oa-b@L37-L37 | (det A)^2=c^{2d} from det(AB)=det A det B, det A^T = det A, det M_0=1
EDGE: stepP:p1:oa-mat | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:oa-b@L37-L37 | Omega(w,X_ell)=ell(w) and the uniqueness of X_ell
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:oa-b@L37-L37 | M_0, Omega and X_ell
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: bijective_of_symplectic, abs_det_of_symplectic, apply_linearField_comp_of_symplectic (KAM/Planetary/Hamiltonian/Algebra.lean)
LEAN_NOTE: audit PP1-1 PASS WITH NOTES (audit 2 closes hygiene H1); named by audit
NOTE: -

NODE: bpP:p1:order
KIND: claim
TITLE: Reordering of coordinates
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:order@L40-L42
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:order@L40-L42
CONTRACT_ID: bpP:p1:order
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 writes points as (J,theta) (action, angle); the frozen order is (position, momentum)=(angle, action)
SOURCE_QUANTIFIERS: pi(J,theta)=(theta,J)
SOURCE_CONCLUSION: the relabelling pi turns theta-dot=d_J H, J-dot=-d_theta H into X_H of the frozen field and the form dJ^dtheta into Omega, with no sign changes; all statements of Part 3 are read in the frozen order after applying pi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:hamsymp#hamiltonianVectorField, bpP:p0:hamsymp#symplecticForm, bpP:p1:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:order@L41-L41 | X_H of Part 0 is the target of the relabelled equations
EDGE: bpP:p0:hamsymp#symplecticForm | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:order@L41-L41 | the form Omega of Part 0
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:order@L41-L41 | the coordinate order and the form Omega
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: remark: its justification is inline (confirm, or exclude if not a mathematical claim)

NODE: bpP:p1:chart
KIND: definition
TITLE: Chart
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:chart@L46-L48
PROOF_SOURCE: -
CONTRACT_ID: bpP:p1:chart
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: O subset Ph_d open, c>0
SOURCE_QUANTIFIERS: d; O, c; then Psi
SOURCE_CONCLUSION: defines a c-chart on O: a total map Psi:Ph_d->Ph_d that is real analytic at every point of O and satisfies Omega(DPsi(z)u,DPsi(z)v)=c Omega(u,v) for z in O and all u,v; a 1-chart is a symplectic chart; the pulled-back Hamiltonian H^Psi:=c^{-1}(H o Psi)
CONSTANT_SCOPE: none (O, c, Psi, H arbitrary)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:conv#data, bpP:p0:hamsymp#symplecticForm
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:chart@L47-L47 | Ph_d and the form Omega
EDGE: bpP:p0:hamsymp#symplecticForm | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:chart@L47-L47 | Omega in the chart condition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: IsChart, isChart_iff, IsChart.analyticOnNhd, IsChart.symplectic, IsChart.mono, chartPullback, IsChart.bijective_fderiv (KAM/Planetary/Hamiltonian/Chart.lean)
LEAN_NOTE: audit PP1-4 PASS WITH NOTES
NOTE: -

NODE: bpP:p1:chart-field
KIND: lemma
TITLE: Charts and Hamiltonian fields
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:chart-field@L51-L55
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:chart-field@L56-L59
CONTRACT_ID: bpP:p1:chart-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Psi a c-chart on O; H:Ph_d->R; z in O
SOURCE_QUANTIFIERS: d, c, O, Psi, H, z
SOURCE_CONCLUSION: H^Psi is differentiable at z iff H is differentiable at Psi(z), and then DPsi(z) X_{H^Psi}(z)=X_H(Psi(z)); if H is not differentiable at Psi(z) both fields are 0 and the identity still holds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p1:cf-diff, stepP:p1:cf-field, bpP:p1:chart, bpP:p0:hamsymp#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p1:cf-diff | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:chart-field@L57-L57 | proof step: differentiability
EDGE: stepP:p1:cf-field | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:chart-field@L58-L58 | proof step: the field identity
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:chart-field@L52-L52 | c-chart and H^Psi
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:chart-field@L53-L53 | X_{H^Psi} and X_H
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: chart_field_differentiableAt_iff, chart_field (KAM/Planetary/Hamiltonian/Chart.lean)
LEAN_NOTE: audit PP1-4 PASS WITH NOTES
NOTE: -

NODE: stepP:p1:cf-diff
KIND: step
TITLE: Differentiability
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:cf-diff@L57-L57
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:cf-diff@L57-L57
CONTRACT_ID: stepP:p1:cf-diff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Psi a c-chart on O, z in O
SOURCE_QUANTIFIERS: z in O
SOURCE_CONCLUSION: H^Psi differentiable at z iff H differentiable at Psi(z): (<=) by the chain rule; (=>) via a C^1 local inverse near Psi(z) with H=c H^Psi o Psi^{-1}_loc
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:ext-comp, bpP:p1:ext-ift, bpP:p1:omega-algebra, bpP:p1:chart
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:ext-comp | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:cf-diff@L57-L57 | chain rule for the direction <=
EDGE: bpP:p1:ext-ift | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:cf-diff@L57-L57 | C^1 local inverse of Psi near Psi(z)
EDGE: bpP:p1:omega-algebra | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:cf-diff@L57-L57 | DPsi(z) is invertible by (b), needed for the inverse function theorem
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:cf-diff@L57-L57 | Psi is real analytic hence C^1 at z in O
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: chart_field_differentiableAt_iff (KAM/Planetary/Hamiltonian/Chart.lean)
LEAN_NOTE: audit PP1-4 PASS WITH NOTES; named by audit
NOTE: -

NODE: stepP:p1:cf-field
KIND: step
TITLE: The field
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:cf-field@L58-L58
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:cf-field@L58-L58
CONTRACT_ID: stepP:p1:cf-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Psi a c-chart on O; H:Ph_d->R; z in O; locally put ell=DH(Psi z), A=DPsi(z); split according to differentiability
SOURCE_QUANTIFIERS: z in O
SOURCE_CONCLUSION: D(H^Psi)(z)=c^{-1} ell o A, X_{H^Psi}(z)=c^{-1}X_{ell o A}=A^{-1}X_ell, hence A X_{H^Psi}(z)=X_H(Psi z); in the non-differentiable case both derivatives are 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:omega-algebra, bpP:p1:chart, bpP:p0:hamsymp#hamiltonianVectorField, stepP:p1:cf-diff, bpP:p1:ext-comp, bpP:p1:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:omega-algebra | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:cf-field@L58-L58 | part (b): X_{ell o A}=c A^{-1} X_ell
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:cf-field@L58-L58 | the chart condition on A=DPsi(z) and H^Psi=c^{-1}H o Psi
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:cf-field@L58-L58 | X_H(z)=X_{DH(z)} and the zero convention
EDGE: stepP:p1:cf-diff | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:cf-field@L58-L58 | differentiability equivalence to split the two cases
EDGE: bpP:p1:ext-comp | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:cf-field@L58-L58 | differentiate c^{-1} H composed with Psi in the differentiable branch
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:cf-field@L58-L58 | X_ell and the matrix convention
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: chart_field (KAM/Planetary/Hamiltonian/Chart.lean)
LEAN_NOTE: audit PP1-4 PASS WITH NOTES; named by audit
NOTE: -

NODE: bpP:p1:chart-orbit
KIND: corollary
TITLE: Orbits transfer
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:chart-orbit@L61-L63
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:chart-orbit@L64-L66
CONTRACT_ID: bpP:p1:chart-orbit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Psi a c-chart on O (and H, c as in Definition chart); y:J->O, J an interval; H^Psi differentiable at y(t) and y has derivative X_{H^Psi}(y(t)) at t for all t in J
SOURCE_QUANTIFIERS: d, c, O, Psi, H; then J, y
SOURCE_CONCLUSION: x=Psi o y has derivative X_H(x(t)) at every t in J and H is differentiable at x(t)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:ext-comp, bpP:p1:chart-field, bpP:p1:chart, bpP:p0:hamsymp#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:ext-comp | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:chart-orbit@L65-L65 | chain rule for Psi o y
EDGE: bpP:p1:chart-field | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:chart-orbit@L65-L65 | D Psi X_{H^Psi}=X_H o Psi and differentiability transfer
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:chart-orbit@L62-L62 | Psi, H^Psi
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:chart-orbit@L62-L62 | X_{H^Psi}, X_H
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: chart_orbit (KAM/Planetary/Hamiltonian/Chart.lean)
LEAN_NOTE: audit PP1-4 PASS WITH NOTES
NOTE: -

NODE: bpP:p1:hol-chart
KIND: lemma
TITLE: Holomorphic charts, real restriction
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:hol-chart@L72-L74
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:hol-chart@L75-L77
CONTRACT_ID: bpP:p1:hol-chart
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c>0; V subset C^{2d} open; Psi:V->C^{2d} holomorphic, real at real points; D Psi(z)^T M_0 D Psi(z)=c M_0 (complex matrices) for z in V cap R^{2d}; O=V cap R^{2d}
SOURCE_QUANTIFIERS: d, c, V, Psi, then any total extension Psi~ off O
SOURCE_CONCLUSION: any total map Ph_d->Ph_d that agrees with Psi on O is a c-chart on O, with real derivative D Psi(z) restricted to R^{2d}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:chart, bpP:p1:omega-algebra, K:bp:p1:holomorphic-analytic, bpP:p1:conv#data, stepP:p1:hc-real-derivative
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:hol-chart@L76-L76 | the target notion of c-chart
EDGE: bpP:p1:omega-algebra | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:hol-chart@L76-L76 | (c): the matrix identity equals the chart condition
EDGE: K:bp:p1:holomorphic-analytic | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:hol-chart@L76-L76 | holomorphic maps are analytic
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:hol-chart@L73-L73 | M_0 and the identification of R^{2d} with Ph_d
EDGE: stepP:p1:hc-real-derivative | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:hol-chart@L76-L76 | identify the real derivative with the restriction of the complex derivative on arbitrary V
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: hol_chart (KAM/Planetary/Hamiltonian/HolChart.lean)
LEAN_NOTE: audit PP1-5 PASS WITH NOTES; unused hc harmless
NOTE: -

NODE: bpP:p1:lattice-torus
KIND: definition
TITLE: Lattice torus in a chart
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:lattice-torus@L81-L92
PROOF_SOURCE: -
CONTRACT_ID: bpP:p1:lattice-torus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: O subset Ph_d open; G:Ph_d->R; w in R^d; K:R^d->Ph_d
SOURCE_QUANTIFIERS: d; O, G, w, K
SOURCE_CONCLUSION: defines LT(G,O,w,K): (L1) K real analytic on R^d, K(theta) in O and G differentiable at K(theta); (L2) K(theta+k)=K(theta)+iota_k; (L3) K(theta)=K(theta1) implies theta1-theta in Z^d; (L4) DK(theta) injective; (L5) Omega(DK u,DK v)=0; (L6) s -> K(theta+s w) has derivative X_G(K(theta+t w)) at s=t for all theta, t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:conv#data, bpP:p0:hamsymp#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:lattice-torus@L82-L82 | iota_k, Omega and X_G
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:lattice-torus@L89-L89 | X_G in the flow clause (L6)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: IsLatticeTorus (KAM/Planetary/Hamiltonian/Transport.lean)
LEAN_NOTE: audit PP1-6 PASS WITH NOTES
NOTE: -

NODE: bpP:p1:torus-transport
KIND: theorem
TITLE: Torus transport
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-transport@L94-L108
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-transport@L109-L117
CONTRACT_ID: bpP:p1:torus-transport
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c>0; O open; Psi a c-chart on O; H:Ph_d->R; G=H^Psi=c^{-1}H o Psi; w in R^d; K with LT(G,O,w,K); (Q1) O+iota_k=O and Psi(z+iota_k)=Psi(z)+sigma_k for z in O, k in Z^d; (Q2) z,z1 in O, k in Z^d, Psi(z1)=Psi(z)+sigma_k implies z1=z+iota_m for some m; (a) d=a+b, sigma_k=shift((k_i)_{i<a}), U contains Psi(K(R^d)); (b) sigma_k=0 and w (gamma,tau)-Diophantine for some gamma>0, tau>d-1
SOURCE_QUANTIFIERS: d, c, O, Psi, H, w, K, (sigma_k)_k; (a) a, b, U; (b) gamma, tau
SOURCE_CONCLUSION: with calK:=Psi o K: (a) IsCylinderTorus(H,U,w,calK); (b) IsPhysicalTorus(H,w,calK); in both cases calK(theta+t w) is the transport of the chart orbit, calK(R^d)=Psi(K(R^d)) and D calK(theta)=DPsi(K theta)DK(theta)
CONSTANT_SCOPE: none (gamma, tau only in (b), chosen with the Diophantine hypothesis)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p1:tt-an, stepP:p1:tt-lat, stepP:p1:tt-inj, stepP:p1:tt-lag, stepP:p1:tt-flow, stepP:p1:tt-dio, bpP:p1:chart, bpP:p1:lattice-torus, bpP:p0:fastshift#fastShift, bpP:p0:cyltorus#IsCylinderTorus, bpP:p0:phystorus#IsPhysicalTorus, bpP:p0:diophantine#IsDiophantine, bpP:p1:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p1:tt-an | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-transport@L111-L111 | step (i)
EDGE: stepP:p1:tt-lat | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-transport@L112-L112 | step (ii)
EDGE: stepP:p1:tt-inj | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-transport@L113-L113 | step (iii)
EDGE: stepP:p1:tt-lag | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-transport@L114-L114 | step (iv)
EDGE: stepP:p1:tt-flow | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-transport@L115-L115 | step (v)
EDGE: stepP:p1:tt-dio | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-transport@L116-L116 | step (vi)
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-transport@L95-L95 | Psi a c-chart, G=H^Psi
EDGE: bpP:p1:lattice-torus | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-transport@L95-L95 | hypothesis LT(G,O,w,K)
EDGE: bpP:p0:fastshift#fastShift | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-transport@L102-L102 | sigma_k=shift of the cylinder case
EDGE: bpP:p0:cyltorus#IsCylinderTorus | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-transport@L102-L102 | conclusion of (a)
EDGE: bpP:p0:phystorus#IsPhysicalTorus | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-transport@L103-L103 | conclusion of (b)
EDGE: bpP:p0:diophantine#IsDiophantine | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-transport@L103-L103 | Diophantine hypothesis of (b)
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-transport@L97-L97 | iota_k in Q1 and Q2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: torus_transport_cyl, torus_transport_phys, fderiv_chart_comp_torus (KAM/Planetary/Hamiltonian/Transport.lean)
LEAN_NOTE: audit PP1-6 PASS WITH NOTES
NOTE: -

NODE: stepP:p1:tt-an
KIND: step
TITLE: (i) Analyticity, range, differentiability
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-an@L111-L111
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-an@L111-L111
CONTRACT_ID: stepP:p1:tt-an
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K(R^d) subset O, Psi analytic on O; (L1); U contains Psi(K(R^d)) in (a)
SOURCE_QUANTIFIERS: theta in R^d
SOURCE_CONCLUSION: calK analytic on R^d; H differentiable at calK(theta); calK(theta) in Psi(K(R^d)) subset U in (a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:ext-comp, bpP:p1:chart-field, bpP:p1:lattice-torus, bpP:p1:chart
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:ext-comp | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-an@L111-L111 | composition of analytic maps
EDGE: bpP:p1:chart-field | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-an@L111-L111 | H differentiable at calK(theta) since G=H^Psi is differentiable at K(theta)
EDGE: bpP:p1:lattice-torus | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-an@L111-L111 | (L1): K analytic, in O, G differentiable
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-an@L111-L111 | Psi analytic on O
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: tt_an, tt_an_range (KAM/Planetary/Hamiltonian/Part1Nodes.lean)
LEAN_NOTE: audit GAP-P13 round 2 PASS WITH NOTES (12/12 nodes PASS)
NOTE: -

NODE: stepP:p1:tt-lat
KIND: step
TITLE: (ii) Lattice behaviour
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-lat@L112-L112
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-lat@L112-L112
CONTRACT_ID: stepP:p1:tt-lat
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (L2), (Q1)
SOURCE_QUANTIFIERS: theta in R^d, k in Z^d
SOURCE_CONCLUSION: calK(theta+k)=Psi(K theta+iota_k)=calK(theta)+sigma_k; in (a) this is clause (iii) of IsCylinderTorus (shift by k_f=(k_i)_{i<a}); in (b) it is periodicity, clause (iii) of IsPhysicalTorus
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:lattice-torus, bpP:p0:cyltorus#IsCylinderTorus, bpP:p0:phystorus#IsPhysicalTorus, bpP:p0:fastshift#fastShift, bpP:p1:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:lattice-torus | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-lat@L112-L112 | (L2)
EDGE: bpP:p0:cyltorus#IsCylinderTorus | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-lat@L112-L112 | clause (iii) of IsCylinderTorus
EDGE: bpP:p0:phystorus#IsPhysicalTorus | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-lat@L112-L112 | clause (iii) of IsPhysicalTorus
EDGE: bpP:p0:fastshift#fastShift | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-lat@L112-L112 | shift of the fast coordinates
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-lat@L112-L112 | iota_k in the lattice calculation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: tt_lat_cyl, tt_lat_phys (KAM/Planetary/Hamiltonian/Part1Nodes.lean)
LEAN_NOTE: audit GAP-P13 round 2 PASS WITH NOTES (12/12 nodes PASS)
NOTE: -

NODE: stepP:p1:tt-inj
KIND: step
TITLE: (iii) Injectivity modulo the lattice
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-inj@L113-L113
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-inj@L113-L113
CONTRACT_ID: stepP:p1:tt-inj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (Q2), (L2), (L3); (a) k in Z^a with calK(theta1)=calK(theta)+shift(k)
SOURCE_QUANTIFIERS: theta, theta1, k
SOURCE_CONCLUSION: theta1-theta in Z^d: Psi(K theta1)=Psi(K theta)+sigma_{(k,0)} gives K theta1=K theta+iota_m=K(theta+m) by (Q2),(L2), then (L3); (b) is the case k=0 (sigma_0=0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:lattice-torus, bpP:p0:fastshift#fastShift, bpP:p1:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:lattice-torus | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-inj@L113-L113 | (L2) and (L3)
EDGE: bpP:p0:fastshift#fastShift | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-inj@L113-L113 | shift(k) of the cylinder case
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-inj@L113-L113 | iota_k in the lattice calculation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: tt_inj_cyl, tt_inj_phys (KAM/Planetary/Hamiltonian/Part1Nodes.lean)
LEAN_NOTE: audit GAP-P13 round 2 PASS WITH NOTES (12/12 nodes PASS)
NOTE: -

NODE: stepP:p1:tt-lag
KIND: step
TITLE: (iv) Derivative and Lagrangian property
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-lag@L114-L114
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-lag@L114-L114
CONTRACT_ID: stepP:p1:tt-lag
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c>0; O open; Psi a c-chart on O; H:Ph_d->R; G=H^Psi=c^{-1}H o Psi; w in R^d; K with LT(G,O,w,K); (Q1) O+iota_k=O and Psi(z+iota_k)=Psi(z)+sigma_k for z in O, k in Z^d; (Q2) z,z1 in O, k in Z^d, Psi(z1)=Psi(z)+sigma_k implies z1=z+iota_m for some m; (a) d=a+b, sigma_k=shift((k_i)_{i<a}), U contains Psi(K(R^d)); (b) sigma_k=0 and w (gamma,tau)-Diophantine for some gamma>0, tau>d-1; write calK=Psi composed with K
SOURCE_QUANTIFIERS: theta, u, v
SOURCE_CONCLUSION: D calK(theta)=DPsi(K theta)DK(theta) is injective and Omega(D calK u,D calK v)=c Omega(DK u,DK v)=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:omega-algebra, bpP:p1:chart, bpP:p1:lattice-torus, bpP:p1:ext-comp, bpP:p1:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:omega-algebra | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-lag@L114-L114 | (b): DPsi(K theta) is invertible
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-lag@L114-L114 | Omega(DPsi u,DPsi v)=c Omega(u,v)
EDGE: bpP:p1:lattice-torus | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-lag@L114-L114 | (L4) injectivity and (L5) Lagrangian property
EDGE: bpP:p1:ext-comp | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-lag@L114-L114 | D calK=DPsi composed with DK by the chain rule
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-lag@L114-L114 | Omega in the Lagrangian calculation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: tt_lag (KAM/Planetary/Hamiltonian/Part1Nodes.lean)
LEAN_NOTE: audit GAP-P13 round 2 PASS WITH NOTES (12/12 nodes PASS)
NOTE: -

NODE: stepP:p1:tt-flow
KIND: step
TITLE: (v) The flow clause
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-flow@L115-L115
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-flow@L115-L115
CONTRACT_ID: stepP:p1:tt-flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (L6); y(s)=K(theta+s w) in O; G differentiable at y(t)
SOURCE_QUANTIFIERS: theta, t
SOURCE_CONCLUSION: s -> calK(theta+s w)=Psi(y(s)) has derivative X_H(calK(theta+t w)) at t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:chart-orbit, bpP:p1:lattice-torus, bpP:p1:chart
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:chart-orbit | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-flow@L115-L115 | pointwise orbit transfer
EDGE: bpP:p1:lattice-torus | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-flow@L115-L115 | (L6)
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-flow@L115-L115 | G=H^Psi and the chart data used to apply chart-orbit
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: tt_flow (KAM/Planetary/Hamiltonian/Part1Nodes.lean)
LEAN_NOTE: audit GAP-P13 round 2 PASS WITH NOTES (12/12 nodes PASS)
NOTE: -

NODE: stepP:p1:tt-dio
KIND: step
TITLE: (vi) Diophantine clause
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-dio@L116-L116
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-dio@L116-L116
CONTRACT_ID: stepP:p1:tt-dio
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (b): w (gamma,tau)-Diophantine with gamma>0, tau>d-1 is a hypothesis
SOURCE_QUANTIFIERS: gamma, tau
SOURCE_CONCLUSION: the Diophantine clause (vii) of IsPhysicalTorus holds in (b); IsCylinderTorus has no Diophantine clause in (a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:phystorus#IsPhysicalTorus, bpP:p0:cyltorus#IsCylinderTorus, bpP:p0:diophantine#IsDiophantine
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phystorus#IsPhysicalTorus | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-dio@L116-L116 | Diophantine clause of IsPhysicalTorus
EDGE: bpP:p0:cyltorus#IsCylinderTorus | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-dio@L116-L116 | IsCylinderTorus has no Diophantine clause
EDGE: bpP:p0:diophantine#IsDiophantine | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tt-dio@L116-L116 | (gamma,tau)-Diophantine
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: tt_dio (KAM/Planetary/Hamiltonian/Part1Nodes.lean)
LEAN_NOTE: audit GAP-P13 round 2 PASS WITH NOTES (12/12 nodes PASS)
NOTE: -

NODE: bpP:p1:typical
KIND: claim
TITLE: Typical charts
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:typical@L119-L121
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:typical@L119-L121
CONTRACT_ID: bpP:p1:typical
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (1) one oscillator, polar chart on {R>0}; (2) c>0; (3) Psi_1 a c_1-chart on O_1, Psi_2 a c_2-chart on O_2 containing Psi_1(O_1)
SOURCE_QUANTIFIERS: (3): Psi_1, Psi_2, c_1, c_2, O_1, O_2, H
SOURCE_CONCLUSION: (1) (psi,R)->(q,p)=sqrt(2R)(sin psi, cos psi) is a 1-chart on {R>0} (dp^dq=dR^dpsi=Omega in the frozen order), invariant under psi->psi+2 pi; (2) S_c is a c-chart; (3) Psi_2 o Psi_1 is a c_1 c_2-chart on O_1 and (H o Psi_2)^{Psi_1} with factors c_1^{-1} then c_2^{-1} equals H^{Psi_2 o Psi_1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:chart, bpP:p1:period-convert, bpP:p1:ext-comp, bpP:p1:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:typical@L120-L120 | c-chart and pulled-back Hamiltonian
EDGE: bpP:p1:period-convert | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:typical@L120-L120 | (2): S_c is a c-chart (Lemma period-convert(a))
EDGE: bpP:p1:ext-comp | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:typical@L120-L120 | (3): chain rule and analytic composition
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:typical@L120-L120 | Omega and the frozen order of coordinates
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: typical (KAM/Planetary/Hamiltonian/Part1Nodes.lean)
LEAN_NOTE: audit GAP-P13 round 2 PASS WITH NOTES (12/12 nodes PASS)
NOTE: (1) is asserted with the one-line computation dp^dq=dR^dpsi and no separate proof; the polar-chart claim is used by Part 5 and Part 7 (consumers cite this remark)

NODE: bpP:p1:period-convert
KIND: lemma
TITLE: Period conversion
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:period-convert@L127-L135
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:period-convert@L136-L140
CONTRACT_ID: bpP:p1:period-convert
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c>0, S_c(z_1,z_2)=(c z_1,z_2); (b) H~:Ph_d->R; (c) kappa~:R^d->Ph_d (period 2 pi), omega~ in R^d, K(theta):=kappa~(2 pi theta), w:=omega~/2 pi; (d) the frozen fast shift
SOURCE_QUANTIFIERS: c>0; (b) H~ and z; (c) kappa~, omega~, theta, t, tau_k
SOURCE_CONCLUSION: (a) S_c is a c-chart on all of Ph_d, S_c(z+iota_k)=S_c(z)+(c k,0), ¦det DS_c¦=c^d; (b) H~^{S_c}(z_1,z_2)=c^{-1}H~(c z_1,z_2) and S_c X_{H~^{S_c}}(z)=X_{H~}(S_c z) for every z; with c=2 pi this is Lemma period-dictionary, orbits correspond with the same time, omega=omega~/2 pi, Lagrangian iff after S_c (factor c); (c) analyticity, injectivity of DK, Lagrangian property (factor 4 pi^2), period-2 pi lattice formula, injectivity modulo 2 pi Z^d and the flow clause for (K,w) are equivalent to those of (kappa~,omega~), frozen frequency w=omega~/2 pi; (d) shift(k_f)=((2 pi k_f,0_b),0) equals S_{2 pi} applied to ((k_f,0_b),0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p1:pc-a, stepP:p1:pc-b, stepP:p1:pc-c, bpP:p1:conv#data, bpP:p1:chart, bpP:p1:lattice-torus, bpP:p0:fastshift#fastShift, bpP:p0:hamsymp#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p1:pc-a | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:period-convert@L137-L137 | proof of (a) (and (d))
EDGE: stepP:p1:pc-b | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:period-convert@L138-L138 | proof of (b)
EDGE: stepP:p1:pc-c | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:period-convert@L139-L139 | proof of (c)
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:period-convert@L128-L128 | S_c and iota_k
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:period-convert@L130-L130 | S_c is a c-chart
EDGE: bpP:p1:lattice-torus | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:period-convert@L132-L132 | the clauses (L1)-(L6) converted in (c)
EDGE: bpP:p0:fastshift#fastShift | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:period-convert@L133-L133 | frozen fast shift in (d)
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:period-convert@L131-L131 | X_{H~} and X_{H~^{S_c}}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: isChart_angleScale, angleScale_add_angleShift, abs_det_fderiv_angleScale, volume_angleScale_image, chartPullback_angleScale, angleScale_hamiltonianVectorField, fastShift_eq_angleScale (KAM/Planetary/Hamiltonian/Chart.lean); periodOne, IsTwoPiLatticeTorus, analyticOnNhd_periodOne_iff, fderiv_periodOne, periodOne_lattice_iff, periodOne_injMod_iff, periodOne_hasDerivAt_iff, isLatticeTorus_periodOne_iff (KAM/Planetary/Hamiltonian/Transport.lean)
LEAN_NOTE: composite of audits PP1-4 PASS WITH NOTES ((a),(b),(d)) + PP1-6 PASS WITH NOTES ((c))
NOTE: -

NODE: stepP:p1:pc-a
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:pc-a@L137-L137
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:pc-a@L137-L137
CONTRACT_ID: stepP:p1:pc-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c>0; S_c(z_1,z_2)=(c z_1,z_2)
SOURCE_QUANTIFIERS: u, v, z, k
SOURCE_CONCLUSION: Omega(S_c u,S_c v)=c Omega(u,v); det DS_c=c^d; S_c(z+iota_k)=S_c(z)+(c k,0) by linearity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:chart, bpP:p1:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:pc-a@L137-L137 | Omega(DPsi u,DPsi v)=c Omega(u,v) is the chart condition; S_c is analytic
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:pc-a@L137-L137 | Omega and S_c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: pc_a (KAM/Planetary/Hamiltonian/Part1Nodes.lean)
LEAN_NOTE: audit GAP-P13 round 2 PASS WITH NOTES (12/12 nodes PASS)
NOTE: -

NODE: stepP:p1:pc-b
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:pc-b@L138-L138
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:pc-b@L138-L138
CONTRACT_ID: stepP:p1:pc-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c>0; S_c(z_1,z_2)=(c z_1,z_2); H~:Ph_d->R
SOURCE_QUANTIFIERS: z
SOURCE_CONCLUSION: D S_c X_{H~^{S_c}}=X_{H~} o S_c; explicitly d_{z_2}H~^{S_c}=c^{-1}d_2 H~ and d_{z_1}H~^{S_c}=d_1 H~, which are Part 3 equations theta-dot=d_I H, I-dot=-d_theta H
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:chart-field, stepP:p1:pc-a, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p1:chart, bpP:p1:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:chart-field | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:pc-b@L138-L138 | D Psi X_{H^Psi}=X_H o Psi for Psi=S_c
EDGE: stepP:p1:pc-a | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:pc-b@L138-L138 | S_c is a c-chart
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:pc-b@L138-L138 | X_{H~}
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:pc-b@L138-L138 | the pulled-back Hamiltonian H~^{S_c}
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:pc-b@L138-L138 | S_c and its derivative
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: pc_b (KAM/Planetary/Hamiltonian/Part1Nodes.lean)
LEAN_NOTE: audit GAP-P13 round 2 PASS WITH NOTES (12/12 nodes PASS)
NOTE: -

NODE: stepP:p1:pc-c
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:pc-c@L139-L139
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:pc-c@L139-L139
CONTRACT_ID: stepP:p1:pc-c
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K(theta)=kappa~(2 pi theta) with the linear bijection theta->2 pi theta of R^d
SOURCE_QUANTIFIERS: theta, t
SOURCE_CONCLUSION: all claims of (c) follow by composition with the bijection (K(theta+s w)=kappa~(2 pi theta+s omega~) exactly, so no chain rule is needed for the flow clause); (d) is step (a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p1:pc-a, bpP:p1:lattice-torus, bpP:p1:ext-comp
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p1:pc-a | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:pc-c@L139-L139 | (d) is the lattice formula of (a)
EDGE: bpP:p1:lattice-torus | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:pc-c@L139-L139 | the clauses (L1)-(L6) that are transported
EDGE: bpP:p1:ext-comp | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:pc-c@L139-L139 | analyticity and derivative of composition with theta mapped to 2 pi theta
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: period_convert_bundle (KAM/Planetary/Hamiltonian/PeriodOneNodes.lean)
LEAN_NOTE: audit GAP-LREF PASS WITH NOTES (bundle export)
NOTE: -

NODE: bpP:p1:cyl-pipeline
KIND: corollary
TITLE: Cylinder pipeline (consumed by Part~5)
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:cyl-pipeline@L142-L144
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:cyl-pipeline@L145-L147
CONTRACT_ID: bpP:p1:cyl-pipeline
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d=a+b; H:Ph_d->R; Phi a 1-chart on open O_0 with O_0+(2 pi k,0)=O_0, Phi(z+(2 pi k,0))=Phi(z)+shift(k_f), and Phi(z1)=Phi(z)+shift(k_f) implies z1=z+(2 pi m,0); O=S_{2 pi}^{-1}(O_0), Psi=Phi o S_{2 pi}, G_3=H^Psi; LT(G_3,O,w,K_3); U contains Psi(K_3(R^d))
SOURCE_QUANTIFIERS: d, a, b, H, Phi, O_0, then w, K_3, U
SOURCE_CONCLUSION: IsCylinderTorus(H,U,w,Psi o K_3) with the same w: the frozen frequency equals Part 3 frequency omega in D_{gamma_1,gamma_2,tau} and CP angular frequency is 2 pi w
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:torus-transport, bpP:p1:typical, bpP:p1:period-convert, bpP:p1:chart, bpP:p1:lattice-torus, bpP:p0:fastshift#fastShift, bpP:p0:cyltorus#IsCylinderTorus, bpP:p1:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:torus-transport | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:cyl-pipeline@L146-L146 | apply Theorem (a) to Psi
EDGE: bpP:p1:typical | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:cyl-pipeline@L146-L146 | Psi=Phi o S_{2 pi} is a 2 pi-chart (composition (3))
EDGE: bpP:p1:period-convert | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:cyl-pipeline@L146-L146 | S_{2 pi} is a 2 pi-chart (a)
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:cyl-pipeline@L143-L143 | 1-chart Phi, G_3=H^Psi
EDGE: bpP:p1:lattice-torus | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:cyl-pipeline@L143-L143 | hypothesis LT(G_3,O,w,K_3)
EDGE: bpP:p0:fastshift#fastShift | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:cyl-pipeline@L143-L143 | shift(k_f) in the compatibility conditions
EDGE: bpP:p0:cyltorus#IsCylinderTorus | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:cyl-pipeline@L143-L143 | conclusion IsCylinderTorus
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:cyl-pipeline@L143-L143 | S_{2 pi} and iota_k
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: cyl_pipeline (KAM/Planetary/Hamiltonian/Transport.lean)
LEAN_NOTE: audit PP1-6 PASS WITH NOTES
NOTE: the pointers to Prop p3:two-scale-kam and Remark p1:order in the statement are illustrations of the hypothesis (for instance) and are not edges (an edge to p3:two-scale-kam would make a cycle with Part 3 which cites this corollary)

NODE: bpP:p1:phys-pipeline
KIND: corollary
TITLE: Physical pipeline (consumed by Parts~12, 13)
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:phys-pipeline@L149-L151
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:phys-pipeline@L152-L154
CONTRACT_ID: bpP:p1:phys-pipeline
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H:Ph_d->R; Phi a 1-chart on open O_0 with O_0+(2 pi k,0)=O_0, Phi(z+(2 pi k,0))=Phi(z), Phi(z1)=Phi(z) implies z1=z+(2 pi m,0); kappa~:R^d->O_0 with (L1)-(L5) for period 2 pi (tau_k=(2 pi k,0)) and the flow clause for G~=H o Phi; omega~ (gamma~,tau)-Diophantine with gamma~>0, tau>d-1
SOURCE_QUANTIFIERS: d, H, Phi, O_0, kappa~, omega~, gamma~, tau
SOURCE_CONCLUSION: IsPhysicalTorus(H,omega~/2 pi, theta->Phi(kappa~(2 pi theta))) and K(R^d)=Phi(kappa~(R^d))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:period-convert, bpP:p1:torus-transport, bpP:p1:dio-basic, bpP:p1:chart, bpP:p1:lattice-torus, bpP:p0:phystorus#IsPhysicalTorus, bpP:p0:diophantine#IsDiophantine, bpP:p1:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:period-convert | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:phys-pipeline@L153-L153 | (c): K_0(theta)=kappa~(2 pi theta) satisfies (L1)-(L6) with w=omega~/2 pi
EDGE: bpP:p1:torus-transport | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:phys-pipeline@L153-L153 | the argument of (b) applies verbatim with lattice tau_k in place of iota_k
EDGE: bpP:p1:dio-basic | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:phys-pipeline@L153-L153 | (c): w is (gamma~/2 pi,tau)-Diophantine
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:phys-pipeline@L150-L150 | 1-chart Phi
EDGE: bpP:p1:lattice-torus | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:phys-pipeline@L150-L150 | clauses (L1)-(L5) and the flow clause
EDGE: bpP:p0:phystorus#IsPhysicalTorus | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:phys-pipeline@L150-L150 | conclusion IsPhysicalTorus
EDGE: bpP:p0:diophantine#IsDiophantine | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:phys-pipeline@L150-L150 | Diophantine hypothesis on omega~
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:phys-pipeline@L150-L150 | S_{2 pi}, iota_k
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: phys_pipeline (KAM/Planetary/Hamiltonian/Transport.lean)
LEAN_NOTE: audit PP1-6 PASS WITH NOTES
NOTE: torus-transport is reused as an argument (not applicable verbatim because the lattice is tau_k, not iota_k), so the edge is kept; reviewer to confirm

NODE: bpP:p1:two-scale
KIND: definition
TITLE: Two-scale Diophantine set
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:two-scale@L158-L161
PROOF_SOURCE: -
CONTRACT_ID: bpP:p1:two-scale
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n=n_1+n_2; gamma_1,gamma_2,tau>0
SOURCE_QUANTIFIERS: n_1, n_2, gamma_1, gamma_2, tau
SOURCE_CONCLUSION: defines D_{gamma_1,gamma_2,tau}: the set of omega=(omega_1,omega_2) in R^{n_1} x R^{n_2} with ¦k.omega¦>=gamma_1 ¦k¦_1^{-tau} whenever k_1 != 0 and ¦k.omega¦>=gamma_2 ¦k¦_1^{-tau} whenever k_1=0, k != 0, k in Z^{n_1} x Z^{n_2}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: twoScaleDiophantine (KAM/Planetary/Hamiltonian/Diophantine.lean)
LEAN_NOTE: audit PP1-2 PASS WITH NOTES
NOTE: -

NODE: bpP:p1:dio-basic
KIND: lemma
TITLE: Elementary properties of \Lean{KAM.IsDiophantine}
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:dio-basic@L163-L171
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:dio-basic@L172-L174
CONTRACT_ID: bpP:p1:dio-basic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: omega in R^d, gamma,tau>0; the frozen definition gamma/¦k¦_1^tau <= ¦k.omega¦ for k != 0; (b) nu any function satisfying 0<nu(k)<=¦k¦_1 for every nonzero k; (d) the set D_{gamma_1,gamma_2,tau}
SOURCE_QUANTIFIERS: omega, gamma, tau; (a) gamma, tau, gamma1, tau1; (b) nu; (c) s>0; (d) gamma_1, gamma_2, tau
SOURCE_CONCLUSION: (a) (gamma,tau)-Diophantine implies (gamma1,tau1)-Diophantine for 0<gamma1<=gamma, tau1>=tau (so tau>d-1 and tau>a+b can be arranged); (b) if ¦k.omega¦>=gamma nu(k)^{-tau} for k != 0 with 0<nu(k)<=¦k¦_1 then (gamma,tau)-Diophantine; (c) omega is (gamma,tau)-Diophantine iff omega/s is (gamma/s,tau)-Diophantine; (d) D_{gamma_1,gamma_2,tau} is contained in the (min{gamma_1,gamma_2},tau)-Diophantine vectors
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:diophantine#IsDiophantine, bpP:p1:two-scale
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:diophantine#IsDiophantine | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:dio-basic@L164-L164 | the frozen definition of Diophantine
EDGE: bpP:p1:two-scale | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:dio-basic@L169-L169 | (d): the set D_{gamma_1,gamma_2,tau}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: IsDiophantine.mono, isDiophantine_of_le_l1, isDiophantine_smul_iff, isDiophantine_min_of_mem_twoScale (KAM/Planetary/Hamiltonian/Diophantine.lean)
LEAN_NOTE: audit PP1-2 PASS WITH NOTES; (a)-(d)
NOTE: -

NODE: bpP:p1:dio-sources
KIND: lemma
TITLE: CP10 and CP09 give the frozen Diophantine clauses
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:dio-sources@L176-L181
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:dio-sources@L182-L184
CONTRACT_ID: bpP:p1:dio-sources
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (a) omega in D_{gamma_1,gamma_2,tau}, gamma_1,gamma_2>0, tau>n=a+b; (b) omega~=omega*(b) with ¦<k,omega~>¦>=gamma ¦k¦_2^{-tau} for all k in Z^n minus 0, gamma>0, tau>n mu>=n, mu in Z_{>=1}
SOURCE_QUANTIFIERS: (a) omega, gamma_1, gamma_2, tau, a, b; (b) omega~, gamma, tau, mu, n
SOURCE_CONCLUSION: (a) omega is (min{gamma_1,gamma_2},tau)-Diophantine so the clause of IsCylinderKolmogorovSet holds for w=omega; w=omega~/2 pi with omega~ in D_{gamma~_1,gamma~_2,tau} gives w in D_{gamma~_1/2 pi,gamma~_2/2 pi,tau}; (b) omega~ is (gamma,tau)-Diophantine, w=omega~/2 pi is (gamma/2 pi,tau)-Diophantine and tau>n-1: clause (vii) of IsPhysicalTorus holds with d=n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:dio-basic, bpP:p1:two-scale, bpP:p0:cylkol#IsCylinderKolmogorovSet, bpP:p0:phystorus#IsPhysicalTorus, bpP:p0:diophantine#IsDiophantine
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:dio-basic | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:dio-sources@L183-L183 | (d), (c) for (a); (b), (c) for (b)
EDGE: bpP:p1:two-scale | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:dio-sources@L178-L178 | the set D_{gamma_1,gamma_2,tau}
EDGE: bpP:p0:cylkol#IsCylinderKolmogorovSet | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:dio-sources@L178-L178 | the Diophantine clause of IsCylinderKolmogorovSet
EDGE: bpP:p0:phystorus#IsPhysicalTorus | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:dio-sources@L179-L179 | clause (vii) of IsPhysicalTorus
EDGE: bpP:p0:diophantine#IsDiophantine | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:dio-sources@L179-L179 | (gamma,tau)-Diophantine
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: smul_mem_twoScale, cp10_isDiophantine, cp09_isDiophantine (KAM/Planetary/Hamiltonian/Diophantine.lean)
LEAN_NOTE: audit PP1-2 PASS WITH NOTES; (a),(b)
NOTE: -

NODE: bpP:p1:liouville
KIND: lemma
TITLE: Charts scale Lebesgue measure
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:liouville@L191-L193
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:liouville@L194-L199
CONTRACT_ID: bpP:p1:liouville
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Psi a c-chart on O; A subset O Lebesgue measurable
SOURCE_QUANTIFIERS: d, c, O, Psi, A
SOURCE_CONCLUSION: Psi(A) is Lebesgue measurable (NullMeasurableSet) and meas Psi(A)<=c^d meas A, with equality if Psi is injective on A; an injective symplectic chart preserves measure; if A is Borel then Psi(A) is Borel
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p1:li-det, stepP:p1:li-meas, stepP:p1:li-borel, stepP:p1:li-vol, bpP:p1:chart
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p1:li-det | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:liouville@L195-L195 | step: determinant
EDGE: stepP:p1:li-meas | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:liouville@L196-L196 | step: measurability
EDGE: stepP:p1:li-borel | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:liouville@L197-L197 | step: Borel sets
EDGE: stepP:p1:li-vol | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:liouville@L198-L198 | step: measure
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:liouville@L192-L192 | c-chart
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: chart_measure_image, measurableSet_chart_image, isAddHaarMeasure_volume_phase (KAM/Planetary/Hamiltonian/Liouville.lean)
LEAN_NOTE: audit PP1-7 PASS WITH NOTES
NOTE: -

NODE: stepP:p1:li-det
KIND: step
TITLE: Determinant
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-det@L195-L195
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-det@L195-L195
CONTRACT_ID: stepP:p1:li-det
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Psi a c-chart on O
SOURCE_QUANTIFIERS: z in O
SOURCE_CONCLUSION: ¦det D Psi(z)¦=c^d on O
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:omega-algebra, bpP:p1:chart
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:omega-algebra | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-det@L195-L195 | (b): ¦det A¦=¦c¦^d
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-det@L195-L195 | the c-chart condition and analytic regularity of Psi
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: IsChart.abs_det_fderiv (KAM/Planetary/Hamiltonian/Chart.lean)
LEAN_NOTE: audit PP1-4 PASS WITH NOTES; named by audit
NOTE: -

NODE: stepP:p1:li-meas
KIND: step
TITLE: Measurability
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-meas@L196-L196
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-meas@L196-L196
CONTRACT_ID: stepP:p1:li-meas
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Psi a c-chart on O; A subset O measurable
SOURCE_QUANTIFIERS: A, countable cover (O_j)
SOURCE_CONCLUSION: Psi(A) is Lebesgue measurable: cover O by countably many open O_j on which Psi is a homeomorphism onto an open set, split A cap O_j=B u N (F_sigma, null), Psi(B) sigma-compact, Psi(N) null since Psi is locally Lipschitz
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:ext-ift, bpP:p1:omega-algebra, bpP:p1:ext-borel, K:bp:p1:lip-image, bpP:p1:chart
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:ext-ift | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-meas@L196-L196 | local homeomorphisms with continuous inverse
EDGE: bpP:p1:omega-algebra | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-meas@L196-L196 | DPsi invertible on O (needed for the inverse function theorem)
EDGE: bpP:p1:ext-borel | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-meas@L196-L196 | A cap O_j = F_sigma u null; images of compact sets are compact
EDGE: K:bp:p1:lip-image | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-meas@L196-L196 | locally Lipschitz images of null sets are null
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-meas@L196-L196 | the c-chart condition and analytic regularity of Psi
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: chart_measure_image (KAM/Planetary/Hamiltonian/Liouville.lean)
LEAN_NOTE: audit PP1-7 PASS WITH NOTES; named by audit
NOTE: -

NODE: stepP:p1:li-borel
KIND: step
TITLE: Borel sets
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-borel@L197-L197
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-borel@L197-L197
CONTRACT_ID: stepP:p1:li-borel
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Psi a c-chart on O; A subset O Lebesgue measurable; for the Borel branch, A is Borel; obtain the local inverses from li-meas
SOURCE_QUANTIFIERS: A
SOURCE_CONCLUSION: Psi(A cap O_j)=(Psi_j^{-1})^{-1}(A cap O_j) is Borel, so Psi(A) is a countable union of Borel sets
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p1:li-meas
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p1:li-meas | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-borel@L197-L197 | the countable cover by local homeomorphisms and their continuous inverses
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: measurableSet_chart_image (KAM/Planetary/Hamiltonian/Liouville.lean)
LEAN_NOTE: audit PP1-7 PASS WITH NOTES; named by audit
NOTE: -

NODE: stepP:p1:li-vol
KIND: step
TITLE: Measure
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-vol@L198-L198
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-vol@L198-L198
CONTRACT_ID: stepP:p1:li-vol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Psi a c-chart on O; A subset O Lebesgue measurable; first the Borel case, then decompose a general measurable A using ext-borel
SOURCE_QUANTIFIERS: A
SOURCE_CONCLUSION: for Borel A: meas Psi(A)<=int_A ¦det D Psi¦=c^d meas A, equality if Psi is injective on A; for Lebesgue measurable A=B u N: meas Psi(A)<=meas Psi(B), equality under injectivity by the subscript-0 version
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:ext-area, stepP:p1:li-det, stepP:p1:li-meas, bpP:p1:ext-borel, bpP:p1:chart
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:ext-area | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-vol@L198-L198 | area formula and its subscript-0 version
EDGE: stepP:p1:li-det | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-vol@L198-L198 | ¦det D Psi¦=c^d
EDGE: stepP:p1:li-meas | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-vol@L198-L198 | Psi(A) measurable
EDGE: bpP:p1:ext-borel | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-vol@L198-L198 | A=B u N with B Borel, N null
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:li-vol@L198-L198 | the c-chart condition and analytic regularity of Psi
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: chart_measure_image (KAM/Planetary/Hamiltonian/Liouville.lean)
LEAN_NOTE: audit PP1-7 PASS WITH NOTES; named by audit
NOTE: -

NODE: bpP:p1:liouville-lattice
KIND: lemma
TITLE: Quotient version for whole tori
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:liouville-lattice@L201-L203
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:liouville-lattice@L204-L206
CONTRACT_ID: bpP:p1:liouville-lattice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the hypotheses of Theorem torus-transport with sigma_k=0 (c-chart Psi on O, (Q1), (Q2)); A subset O measurable with A+iota_k=A for all k; Q={z: z_{1,i} in [0,1) for all i}
SOURCE_QUANTIFIERS: d, c, O, Psi, then A
SOURCE_CONCLUSION: Psi(A) is Lebesgue measurable, Psi(A)=Psi(A cap Q), meas Psi(A)=c^d meas(A cap Q); hence 0<meas Psi(A) iff 0<meas A, and meas Psi(A)<infinity if A cap Q is bounded; Borel version: if A is Borel so is Psi(A)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:liouville, bpP:p1:ext-borel, bpP:p1:conv#data, bpP:p1:chart
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:liouville | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:liouville-lattice@L205-L205 | meas Psi(A cap Q)=c^d meas(A cap Q) for Psi injective on A cap Q
EDGE: bpP:p1:ext-borel | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:liouville-lattice@L205-L205 | injective continuous images of Borel sets are Borel
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:liouville-lattice@L202-L202 | iota_k
EDGE: bpP:p1:chart | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:liouville-lattice@L202-L202 | c-chart Psi on O
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: liouville_lattice, liouville_lattice_measurableSet (KAM/Planetary/Hamiltonian/Liouville.lean)
LEAN_NOTE: audit PP1-7 PASS WITH NOTES
NOTE: Q1 and Q2 are the explicitly stated lattice hypotheses at L202, not an application of the torus-transport theorem.

NODE: bpP:p1:torus-union
KIND: lemma
TITLE: Unions of whole tori as Lipschitz images
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-union@L212-L214
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-union@L215-L220
CONTRACT_ID: bpP:p1:torus-union
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E subset R^d Lebesgue measurable; A=E x [0,1)^d; calF:A->R^{2d} with ¦calF(x)-calF(y)¦<=Lambda ¦x-y¦ (max norms); optionally ¦calF(x)-calF(y)¦>=lambda ¦x-y¦, lambda>0; (B1) E sigma-compact; (B2) E Borel and calF continuous and injective on A; last clause calF(omega,theta)=phi_omega(theta) with phi_omega(theta+k)=phi_omega(theta)+iota_k
SOURCE_QUANTIFIERS: d, E, Lambda, calF, then lambda, then the family phi_omega
SOURCE_CONCLUSION: calF(A) is Lebesgue measurable (NullMeasurableSet, not asserted Borel) and meas calF(A)<=Lambda^{2d} meas E; (B1) calF(A) sigma-compact hence Borel; (B2) calF(A) Borel; then the saturated union of the translates calF(A)+iota_k is a countable union of Borel sets; with the lower bound meas calF(A)>=lambda^{2d} meas E, so 0<meas calF(A) iff 0<meas E and meas calF(A)<infinity iff meas E<infinity; union over omega in E of phi_omega(R^d)=union_k(calF(A)+iota_k) is measurable
CONSTANT_SCOPE: Lambda, lambda are the Lipschitz constants of calF
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p1:tu-ext, stepP:p1:tu-meas, stepP:p1:tu-borel, stepP:p1:tu-bounds, bpP:p1:ext-borel, bpP:p1:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p1:tu-ext | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-union@L216-L216 | step: extension
EDGE: stepP:p1:tu-meas | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-union@L217-L217 | step: measurability
EDGE: stepP:p1:tu-borel | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-union@L218-L218 | step: Borel cases
EDGE: stepP:p1:tu-bounds | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-union@L219-L219 | step: bounds
EDGE: bpP:p1:ext-borel | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-union@L213-L213 | (B2) injective continuous images of Borel sets are Borel
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:torus-union@L213-L213 | iota_k
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: unitCube, torus_union, torus_union_measurableSet_of_sigmaCompact, torus_union_measurableSet_of_injOn, torus_union_lower, torus_union_saturation, nullMeasurableSet_torus_union_saturation (KAM/Planetary/Hamiltonian/TorusUnion.lean)
LEAN_NOTE: audit PP1-3 PASS WITH NOTES
NOTE: -

NODE: stepP:p1:tu-ext
KIND: step
TITLE: Extension
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tu-ext@L216-L216
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tu-ext@L216-L216
CONTRACT_ID: stepP:p1:tu-ext
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: calF Lambda-Lipschitz on A in the max norm
SOURCE_QUANTIFIERS: coordinate components
SOURCE_CONCLUSION: a Lambda-Lipschitz extension calF^ of calF to R^{2d} (McShane componentwise)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:mcshane
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:mcshane | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tu-ext@L216-L216 | McShane extension
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: route substitution (D27, ruling OVERNIGHT 01:20): the Lean proof of the PROVED parent torus_union avoids this step
NOTE: -

NODE: stepP:p1:tu-meas
KIND: step
TITLE: Measurability
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tu-meas@L217-L217
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tu-meas@L217-L217
CONTRACT_ID: stepP:p1:tu-meas
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E subset R^d Lebesgue measurable; A=E x [0,1)^d; calF:A->R^{2d} with ¦calF(x)-calF(y)¦<=Lambda ¦x-y¦ (max norms); optionally ¦calF(x)-calF(y)¦>=lambda ¦x-y¦, lambda>0; (B1) E sigma-compact; (B2) E Borel and calF continuous and injective on A; last clause calF(omega,theta)=phi_omega(theta) with phi_omega(theta+k)=phi_omega(theta)+iota_k; use the extension constructed in tu-ext
SOURCE_QUANTIFIERS: A
SOURCE_CONCLUSION: A=B u N (F_sigma, null), calF^(B) sigma-compact, meas calF^(N)=0, so calF(A)=calF^(B) u calF^(N) is Lebesgue measurable (not Borel)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:ext-borel, K:bp:p1:lip-image, stepP:p1:tu-ext
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:ext-borel | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tu-meas@L217-L217 | F_sigma u null decomposition, sigma-compact images
EDGE: K:bp:p1:lip-image | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tu-meas@L217-L217 | Lipschitz images of null sets are null
EDGE: stepP:p1:tu-ext | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tu-meas@L217-L217 | the extension calF^
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: torus_union, nullMeasurableSet_image_of_lipschitzOn (KAM/Planetary/Hamiltonian/TorusUnion.lean)
LEAN_NOTE: audit PP1-3 PASS WITH NOTES; named by audit
NOTE: -

NODE: stepP:p1:tu-borel
KIND: step
TITLE: Borel cases
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tu-borel@L218-L218
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tu-borel@L218-L218
CONTRACT_ID: stepP:p1:tu-borel
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E subset R^d Lebesgue measurable; A=E x [0,1)^d; calF:A->R^{2d} with ¦calF(x)-calF(y)¦<=Lambda ¦x-y¦ (max norms); optionally ¦calF(x)-calF(y)¦>=lambda ¦x-y¦, lambda>0; (B1) E sigma-compact; (B2) E Borel and calF continuous and injective on A; last clause calF(omega,theta)=phi_omega(theta) with phi_omega(theta+k)=phi_omega(theta)+iota_k; treat B1 and B2 separately; the standing Lipschitz bound supplies continuity also in B1
SOURCE_QUANTIFIERS: cases B1, B2
SOURCE_CONCLUSION: (B1) E x [0,1)^d is a countable union of compact sets, images compact so calF(A) sigma-compact; (B2) calF(A) Borel by Lusin-Souslin
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:ext-borel
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:ext-borel | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tu-borel@L218-L218 | compact images and injective continuous images of Borel sets
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: torus_union_measurableSet_of_sigmaCompact, torus_union_measurableSet_of_injOn (KAM/Planetary/Hamiltonian/TorusUnion.lean)
LEAN_NOTE: audit PP1-3 PASS WITH NOTES; named by audit (B1,B2)
NOTE: -

NODE: stepP:p1:tu-bounds
KIND: step
TITLE: Bounds
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tu-bounds@L219-L219
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tu-bounds@L219-L219
CONTRACT_ID: stepP:p1:tu-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E subset R^d Lebesgue measurable; A=E x [0,1)^d; calF:A->R^{2d} with ¦calF(x)-calF(y)¦<=Lambda ¦x-y¦ (max norms); optionally ¦calF(x)-calF(y)¦>=lambda ¦x-y¦, lambda>0; (B1) E sigma-compact; (B2) E Borel and calF continuous and injective on A; last clause calF(omega,theta)=phi_omega(theta) with phi_omega(theta+k)=phi_omega(theta)+iota_k; the optional lower bound has lambda>0
SOURCE_QUANTIFIERS: calF, Lambda, lambda
SOURCE_CONCLUSION: meas calF(A)<=Lambda^{2d} meas A=Lambda^{2d} meas E; under the lower bound calF is injective with lambda^{-1}-Lipschitz inverse so meas E<=lambda^{-2d} meas calF(A); the last claim from periodicity and countability of Z^d
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:lip-image, bpP:p1:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:lip-image | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tu-bounds@L219-L219 | Lipschitz images scale measure by at most the Lipschitz constant to the power 2d
EDGE: bpP:p1:conv#data | blueprint-P/parts/p1-hamiltonian-tools.tex#stepP:p1:tu-bounds@L219-L219 | iota_k in the final translated union
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: torus_union, torus_union_lower (KAM/Planetary/Hamiltonian/TorusUnion.lean)
LEAN_NOTE: audit PP1-3 PASS WITH NOTES; named by audit
NOTE: -

NODE: bpP:p2:setting
KIND: definition
TITLE: Direct divisor setting
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:setting@L40-L43
PROOF_SOURCE: -
CONTRACT_ID: bpP:p2:setting
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D subset C^n, r>0, K>=0, alpha>0, q>=1, Lambda subset Z^n, h holomorphic on V_r D, omega=d_I h
SOURCE_QUANTIFIERS: n, D, r, K, alpha, q, Lambda, h
SOURCE_CONCLUSION: defines (Div_q): ¦k.omega(I)¦>=alpha/q for all I in V_r D and k in Z_K minus Lambda
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#bpP:p2:setting@L41-L41 | V_r D, Z_K
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: setting (KAM/Planetary/Averaging/Setting.lean)
LEAN_NOTE: audit P23-01 PASS WITH NOTES; DivisorBound dependency on N6-1 (now on tree)
NOTE: -

NODE: bpP:p2:direct
KIND: lemma
TITLE: Iterative Lemma, direct form
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:direct@L45-L50
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:direct@L51-L55
CONTRACT_ID: bpP:p2:direct
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of Definition setting with (Div_q), q>=1 arbitrary (q=1 allowed); the hypotheses of N homological and N iterative (with its Remark iterative-special) with N hypotheses cond-nr, cond-L, K L r<=alpha/p replaced by (Div_q)
SOURCE_QUANTIFIERS: D, r, K, alpha, q, Lambda, h as in setting; N constants as in the cited N statements
SOURCE_CONCLUSION: N homological and N iterative (with its Remark) hold verbatim, with the same phi=sum_{k in Z_K minus Lambda} f^_k/(2 pi i k.omega) chi_k, the same constants and estimates, under (Div_q) in place of cond-nr, cond-L and K L r<=alpha/p
CONSTANT_SCOPE: constants are those of the cited N statements (depend on nothing of the Part 2 hypotheses beyond what N states)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p2:dr-use, bpP:p2:setting, N:bpN:p6:homological, N:bpN:p6:iterative, bpN:p6:iterative-special, N:bpN:p6:setting, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p2:dr-use | blueprint-P/parts/p2-averaging.tex#bpP:p2:direct@L52-L52 | proof: where the hypotheses are used
EDGE: bpP:p2:setting | blueprint-P/parts/p2-averaging.tex#bpP:p2:direct@L47-L47 | (Div_q)
EDGE: N:bpN:p6:homological | blueprint-P/parts/p2-averaging.tex#bpP:p2:direct@L46-L46 | N homological solve
EDGE: N:bpN:p6:iterative | blueprint-P/parts/p2-averaging.tex#bpP:p2:direct@L46-L46 | N iterative lemma
EDGE: bpN:p6:iterative-special | blueprint-P/parts/p2-averaging.tex#bpP:p2:direct@L46-L46 | its Remark is extended to (Div_q)
EDGE: N:bpN:p6:setting | blueprint-P/parts/p2-averaging.tex#bpP:p2:direct@L47-L47 | the replaced hypotheses cond-nr, cond-L
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#bpP:p2:direct@L46-L46 | the Fourier convention and alpha-bar in the inherited estimates
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: direct, direct_step (KAM/Planetary/Averaging/Direct.lean)
LEAN_NOTE: audit P23-05 PASS WITH NOTES
NOTE: The special-case remark is consumed and owned by P in slice P-xown. The variant at source-gap L49 is supplied by dr-use; preserve the original N hypotheses except for the three explicitly replaced divisor assumptions.

NODE: stepP:p2:dr-use
KIND: step
TITLE: Where the hypotheses are used
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:dr-use@L52-L54
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:dr-use@L52-L54
CONTRACT_ID: stepP:p2:dr-use
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: N proofs of homological and iterative; (Div_q)
SOURCE_QUANTIFIERS: as in direct
SOURCE_CONCLUSION: the hypotheses enter N homological only through N divisor, whose conclusion is (Div_q), used only in the steps hom-def and hom-norm; the proof of N iterative uses them only through N homological; p^{-1}+q^{-1}=1 occurs only in N divisor; the rest (flow, composition, canonical-map, transform, bracket) never mentions omega
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p6:homological, N:bpN:p6:setting, N:bpN:p6:divisor, N:bpN:p6:iterative, bpP:p2:setting
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p6:homological | blueprint-P/parts/p2-averaging.tex#stepP:p2:dr-use@L52-L52 | N homological (steps hom-def and hom-norm, mapped to the result)
EDGE: N:bpN:p6:setting | blueprint-P/parts/p2-averaging.tex#stepP:p2:dr-use@L52-L52 | cond-nr, cond-L
EDGE: N:bpN:p6:divisor | blueprint-P/parts/p2-averaging.tex#stepP:p2:dr-use@L52-L52 | N divisor whose conclusion is (Div_q)
EDGE: N:bpN:p6:iterative | blueprint-P/parts/p2-averaging.tex#stepP:p2:dr-use@L54-L54 | N iterative uses the hypotheses only through homological
EDGE: bpP:p2:setting | blueprint-P/parts/p2-averaging.tex#stepP:p2:dr-use@L53-L53 | (Div_q) as the replaced hypothesis
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: direct_step (KAM/Planetary/Averaging/Direct.lean)
LEAN_NOTE: audit P23-05 PASS WITH NOTES; named by audit
NOTE: the steps hom-def, hom-norm of N are not imported as nodes; mapped to N:bpN:p6:homological

NODE: bpP:p2:split
KIND: lemma
TITLE: Two-scale step: splitting of $\phi$ and componentwise displacement
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:split@L57-L67
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:split@L68-L74
CONTRACT_ID: bpP:p2:split
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D subset C^n, r,s>0, 0<alpha_2<=alpha_1, q>=1, Lambda={0}, K>=0, (Div_q^{(2)}): ¦k.omega(I)¦>=alpha_1/q for k_1 != 0 and >=alpha_2/q for k_1=0, k != 0, I in V_r D, k in Z_K; f in O(r,s), delta=¦f¦_{r,s}; 0<rho<r/2, 0<sigma<s/2; u=q delta/(alpha-bar_2 rho sigma)<=1/4; phi and Phi=X^1_phi as in Lemma direct; phi^{(1)}=sum_{k_1 != 0} phi^_k chi_k, phi^{(2)}=phi-phi^{(1)}
SOURCE_QUANTIFIERS: n_1, n_2, D, r, s, alpha_1, alpha_2, q, K, then f, then rho, sigma
SOURCE_CONCLUSION: (a) phi^{(2)} independent of theta_1, ¦phi^{(1)}¦_{r,s}<=q delta/alpha-bar_1 and ¦phi¦_{r,s}<=q delta/alpha-bar_2; (b) on D_{r-3 rho/2,s-3 sigma/2}: ¦Phi_{I_1}-I_1¦<=q delta/(e alpha-bar_1 sigma), ¦Phi_{I_2}-I_2¦<=q delta/(e alpha-bar_2 sigma), ¦Phi_theta-theta¦<=q delta/(alpha-bar_2 rho)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p2:sp-coef, stepP:p2:sp-field, stepP:p2:sp-int, bpP:p2:direct, bpP:p2:conv#data, N:bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p2:sp-coef | blueprint-P/parts/p2-averaging.tex#bpP:p2:split@L69-L69 | step: coefficients
EDGE: stepP:p2:sp-field | blueprint-P/parts/p2-averaging.tex#bpP:p2:split@L71-L71 | step: field
EDGE: stepP:p2:sp-int | blueprint-P/parts/p2-averaging.tex#bpP:p2:split@L73-L73 | step: integrate
EDGE: bpP:p2:direct | blueprint-P/parts/p2-averaging.tex#bpP:p2:split@L60-L60 | phi, Phi=X^1_phi and the hypothesis u<=1/4 of Lemma direct
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#bpP:p2:split@L58-L58 | norm, D_{r,s}, alpha-bar_j, Z_K
EDGE: N:bpN:p5:setting | blueprint-P/parts/p2-averaging.tex#bpP:p2:split@L60-L60 | Phi=X_phi^1 and the Hamiltonian-field/flow notation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: firstGen, directMap, split (KAM/Planetary/Averaging/Splitting.lean)
LEAN_NOTE: audit P23-10 PASS WITH NOTES
NOTE: -

NODE: stepP:p2:sp-coef
KIND: step
TITLE: Coefficients
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-coef@L69-L70
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-coef@L69-L70
CONTRACT_ID: stepP:p2:sp-coef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D subset C^n, r,s>0, 0<alpha_2<=alpha_1, q>=1, Lambda={0}, K>=0, (Div_q^{(2)}): ¦k.omega(I)¦>=alpha_1/q for k_1 != 0 and >=alpha_2/q for k_1=0, k != 0, I in V_r D, k in Z_K; f in O(r,s), delta=¦f¦_{r,s}; 0<rho<r/2, 0<sigma<s/2; u=q delta/(alpha-bar_2 rho sigma)<=1/4; phi and Phi=X^1_phi as in Lemma direct; phi^{(1)}=sum_{k_1 != 0} phi^_k chi_k, phi^{(2)}=phi-phi^{(1)}
SOURCE_QUANTIFIERS: k in Z_K
SOURCE_CONCLUSION: ¦phi^_k¦<=q ¦f^_k¦/alpha-bar_1 for k_1 != 0 and <=q ¦f^_k¦/alpha-bar_2 for every k != 0; summing gives (a) (independence since phi^{(2)} has only modes with k_1=0); phi^{(i)} lie in O(r,s) with finite norm
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p6:homological, N:bpN:p4:coefficients, bpP:p2:direct, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p6:homological | blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-coef@L69-L69 | the formula for phi
EDGE: N:bpN:p4:coefficients | blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-coef@L70-L70 | finite family of holomorphic coefficients in O(r,s) with finite norm
EDGE: bpP:p2:direct | blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-coef@L69-L69 | the coefficient formula under Div_q, without the original Lipschitz/divisor premises of N
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-coef@L69-L69 | the split coordinates, alpha-bar and weighted norm conventions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: firstGen_class_bound, split_coeff (KAM/Planetary/Averaging/Splitting.lean)
LEAN_NOTE: audit P23-10 PASS WITH NOTES; named by audit
NOTE: -

NODE: stepP:p2:sp-field
KIND: step
TITLE: Field
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-field@L71-L72
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-field@L71-L72
CONTRACT_ID: stepP:p2:sp-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D subset C^n, r,s>0, 0<alpha_2<=alpha_1, q>=1, Lambda={0}, K>=0, (Div_q^{(2)}): ¦k.omega(I)¦>=alpha_1/q for k_1 != 0 and >=alpha_2/q for k_1=0, k != 0, I in V_r D, k in Z_K; f in O(r,s), delta=¦f¦_{r,s}; 0<rho<r/2, 0<sigma<s/2; u=q delta/(alpha-bar_2 rho sigma)<=1/4; phi and Phi=X^1_phi as in Lemma direct; phi^{(1)}=sum_{k_1 != 0} phi^_k chi_k, phi^{(2)}=phi-phi^{(1)}
SOURCE_QUANTIFIERS: z in D_{r-3 rho/2,s-3 sigma/2}
SOURCE_CONCLUSION: the trajectory X^t_phi(z), 0<=t<=1, stays in the closed ball B_nu(z,eps) inside Omega; first n_1 components of I-dot are -d_{theta_1}phi^{(1)} (since d_{theta_1}phi^{(2)}=0) bounded by q delta/(e alpha-bar_1 sigma); ¦d_{theta_2}phi¦<=q delta/(e alpha-bar_2 sigma), ¦d_I phi¦<=q delta/(alpha-bar_2 rho)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p5:setting, N:bpN:p5:flow, N:bpN:p5:canonical-map, N:bpN:p5:vf-bound, stepP:p2:sp-coef, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p5:setting | blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-field@L71-L71 | the scaled norm nu_{rho,sigma}
EDGE: N:bpN:p5:flow | blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-field@L71-L71 | the flow stays in the ball, N flow (a)
EDGE: N:bpN:p5:canonical-map | blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-field@L71-L71 | step cm-ab: trajectory stays in the domain
EDGE: N:bpN:p5:vf-bound | blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-field@L72-L72 | componentwise field bounds
EDGE: stepP:p2:sp-coef | blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-field@L72-L72 | norm bounds of phi^{(1)} and phi
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-field@L71-L71 | the split coordinates, alpha-bar and weighted norm conventions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: dtheta_firstGen_eq, split (KAM/Planetary/Averaging/Splitting.lean)
LEAN_NOTE: audit P23-10 PASS WITH NOTES; named by audit
NOTE: -

NODE: stepP:p2:sp-int
KIND: step
TITLE: Integrate
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-int@L73-L73
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-int@L73-L73
CONTRACT_ID: stepP:p2:sp-int
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D subset C^n, r,s>0, 0<alpha_2<=alpha_1, q>=1, Lambda={0}, K>=0, (Div_q^{(2)}): ¦k.omega(I)¦>=alpha_1/q for k_1 != 0 and >=alpha_2/q for k_1=0, k != 0, I in V_r D, k in Z_K; f in O(r,s), delta=¦f¦_{r,s}; 0<rho<r/2, 0<sigma<s/2; u=q delta/(alpha-bar_2 rho sigma)<=1/4; phi and Phi=X^1_phi as in Lemma direct; phi^{(1)}=sum_{k_1 != 0} phi^_k chi_k, phi^{(2)}=phi-phi^{(1)}
SOURCE_QUANTIFIERS: z
SOURCE_CONCLUSION: the mean value inequality along gamma, 0<=t<=1, gives (b) with t=1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:ext-mvt, stepP:p2:sp-field, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:ext-mvt | blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-int@L73-L73 | mean value inequality
EDGE: stepP:p2:sp-field | blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-int@L73-L73 | component bounds of the field along the trajectory
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:sp-int@L73-L73 | the split coordinates, alpha-bar and weighted norm conventions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: split (KAM/Planetary/Averaging/Splitting.lean)
LEAN_NOTE: audit P23-10 PASS WITH NOTES; named by audit
NOTE: -

NODE: bpP:p2:nfb
KIND: proposition
TITLE: Averaging with a loss budget and two scales
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:nfb@L78-L93
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:nfb@L94-L127
CONTRACT_ID: bpP:p2:nfb
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n=n_1+n_2; D subset R^n; r>0; s-bar>=0; s>0; K>0 with kappa=2 pi K s>=6; 0<alpha_2<=alpha_1; h holomorphic on V_r D, real on V_r D cap R^n, omega=d_I h; (A1) ¦k.omega(I)¦>=alpha_1 if k_1 != 0, >=alpha_2 if k_1=0, for all I in V_r D, k in Z_K minus {0}; (A2) f in O(r,s-bar+s) real on real points with E:=¦f¦_{r,s-bar+s}<=alpha_2 r/(128 K)
SOURCE_QUANTIFIERS: n_1, n_2, D, r, s-bar, s, K, alpha_1, alpha_2 (constants depending on nothing), then h, then f
SOURCE_CONCLUSION: there are Psi:D_{r/2,s-bar+s/6}->D_{r,s-bar+s}, Psi(theta1,I1)=(theta,I), and g, f_* with: (a) Psi holomorphic, injective, real, Psi(theta1+k,I1)=Psi(theta1,I1)+(k,0), (D Psi)^T J D Psi=J; (b) H o Psi=h+g+f_*, H=h+f, g=g(I1) real with sup_{V_{r/2}D}¦g-f^_0¦<=¦g-f^_0¦<=E/4 (indeed <=E/kappa); (c) f_* holomorphic, periodic, real, ¦f_*¦<=e^{-kappa/6}E; (d) alpha-bar_1 s ¦I_1-I_1'¦<=3E, alpha-bar_2 s ¦I_2-I_2'¦<=3E, alpha-bar_2 r ¦theta-theta'¦<=9E on D_{r/2,s-bar+s/6}; constants depend on nothing: no n, tau, q or L
CONSTANT_SCOPE: Psi, g, f_* depend on all the data; the constants 1/128, 1/4, 3, 9 are absolute
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p2:nfb-first, stepP:p2:nfb-N, stepP:p2:nfb-ind, stepP:p2:nfb-concl, stepP:p2:nfb-disp, bpP:p2:conv#data, bpP:p2:setting, bpP:p2:direct, N:bpN:p6:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p2:nfb-first | blueprint-P/parts/p2-averaging.tex#bpP:p2:nfb@L99-L99 | step 0
EDGE: stepP:p2:nfb-N | blueprint-P/parts/p2-averaging.tex#bpP:p2:nfb@L107-L107 | number of steps
EDGE: stepP:p2:nfb-ind | blueprint-P/parts/p2-averaging.tex#bpP:p2:nfb@L113-L113 | induction
EDGE: stepP:p2:nfb-concl | blueprint-P/parts/p2-averaging.tex#bpP:p2:nfb@L119-L119 | conclusion of the construction
EDGE: stepP:p2:nfb-disp | blueprint-P/parts/p2-averaging.tex#bpP:p2:nfb@L123-L123 | displacement (d)
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#bpP:p2:nfb@L79-L79 | the N norm, D_{r,s}, kappa, alpha-bar_j, Z_K
EDGE: bpP:p2:setting | blueprint-P/parts/p2-averaging.tex#bpP:p2:nfb@L95-L95 | by (A1), (Div_1^{(2)}) holds with q=1 on V_r D
EDGE: bpP:p2:direct | blueprint-P/parts/p2-averaging.tex#bpP:p2:nfb@L96-L96 | every step is Lemma direct on D_{r_i,S_i}
EDGE: N:bpN:p6:setting | blueprint-P/parts/p2-averaging.tex#bpP:p2:nfb@L97-L97 | weights ¦g¦_* contain the widths only through differences
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: nfb, nfb_core, NfbConcl (KAM/Planetary/Averaging/Finite.lean)
LEAN_NOTE: audit P23-12 PASS WITH NOTES
NOTE: -

NODE: stepP:p2:nfb-first
KIND: step
TITLE: Step 0
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-first@L99-L105
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-first@L99-L105
CONTRACT_ID: stepP:p2:nfb-first
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n=n_1+n_2; D subset R^n; r>0; s-bar>=0; s>0; K>0 with kappa=2 pi K s>=6; 0<alpha_2<=alpha_1; h holomorphic on V_r D, real on V_r D cap R^n, omega=d_I h; (A1) ¦k.omega(I)¦>=alpha_1 if k_1 != 0, >=alpha_2 if k_1=0, for all I in V_r D, k in Z_K minus {0}; (A2) f in O(r,s-bar+s) real on real points with E:=¦f¦_{r,s-bar+s}<=alpha_2 r/(128 K); put eps=E and use the Step 0 losses
SOURCE_QUANTIFIERS: cases A (e^{-kappa/6}<=y_0) and B (e^{-kappa/6}>y_0)
SOURCE_CONCLUSION: ¦f_1¦<=(1-2y_0)^{-1}(2y_0/e+e^{-kappa/6}) eps with (1-2y_0)^{-1}<=8/7; Case A: eps_1<=3 eps/(4 kappa)<=eps/8 (2.1); Case B (doubled losses): ¦f_1¦<=e^{-kappa/6} eps and the construction stops with Psi=Phi_0', g=f^_0, f_*=f_1, with displacements <3 eps/(alpha-bar_j s), <=4 eps/(alpha-bar r); from now on Case A
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p2:direct, bpP:p2:split, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p2:direct | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-first@L99-L99 | Lemma direct (d) with ¦g¦_*=0
EDGE: bpP:p2:split | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-first@L104-L104 | Lemma split(b) for the displacements in Case B
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-first@L101-L101 | the weighted norm, widths, kappa and alpha-bar
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: nfb (KAM/Planetary/Averaging/Finite.lean)
LEAN_NOTE: audit P23-12 PASS WITH NOTES; named by audit
NOTE: -

NODE: stepP:p2:nfb-N
KIND: step
TITLE: Number of steps
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-N@L107-L111
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-N@L107-L111
CONTRACT_ID: stepP:p2:nfb-N
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n=n_1+n_2; D subset R^n; r>0; s-bar>=0; s>0; K>0 with kappa=2 pi K s>=6; 0<alpha_2<=alpha_1; h holomorphic on V_r D, real on V_r D cap R^n, omega=d_I h; (A1) ¦k.omega(I)¦>=alpha_1 if k_1 != 0, >=alpha_2 if k_1=0, for all I in V_r D, k in Z_K minus {0}; (A2) f in O(r,s-bar+s) real on real points with E:=¦f¦_{r,s-bar+s}<=alpha_2 r/(128 K); Case A of nfb-first; N=floor(kappa/(12 ln 2)); split N=0 and N>=1
SOURCE_QUANTIFIERS: N=floor(kappa/(12 ln 2))
SOURCE_CONCLUSION: N<kappa/8; if N=0 then e^{-kappa/6}>1/4 so eps_1<=eps/8<=e^{-kappa/6} eps and Psi=Phi_0, g=f^_0, f_*=f_1 on D_{3r/4,s-bar+2s/3} with the displacement bounds; for N>=1 the schedule rho_i=r/(8N), sigma_i=s/(4N), r_i=3r/4-2(i-1)rho, s_i=2s/3-2(i-1)sigma, so r_{N+1}=r/2, s_{N+1}=s/6, e^{-2 pi K sigma}<=1/8, rho sigma=rs/(32N^2) and eps<=alpha-bar r s/(2^10 N), eps_1<alpha-bar rho sigma/2^8 (2.2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p6:ext-numerics, stepP:p2:nfb-first, bpP:p2:direct, bpP:p2:conv#data, bpP:p2:split
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p6:ext-numerics | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-N@L107-L107 | 12 ln 2>8
EDGE: stepP:p2:nfb-first | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-N@L107-L107 | (2.1) and Step 0 bounds
EDGE: bpP:p2:direct | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-N@L107-L107 | displacement bound of Lemma direct for N=0
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-N@L107-L107 | the weighted norm, widths, kappa and alpha-bar
EDGE: bpP:p2:split | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-N@L107-L107 | two-scale displacement bound (b) with sigma_0=s/6 for both action blocks in the N=0 Case-A branch, including alpha_1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-delta-P-d
REVIEWER: sol-delta2-P-b
LEAN_STATUS: PROVED
LEAN_REF: nfb (KAM/Planetary/Averaging/Finite.lean)
LEAN_NOTE: audit P23-12 PASS WITH NOTES; named by audit
NOTE: -

NODE: stepP:p2:nfb-ind
KIND: step
TITLE: Induction
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-ind@L113-L117
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-ind@L113-L117
CONTRACT_ID: stepP:p2:nfb-ind
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n=n_1+n_2; D subset R^n; r>0; s-bar>=0; s>0; K>0 with kappa=2 pi K s>=6; 0<alpha_2<=alpha_1; h holomorphic on V_r D, real on V_r D cap R^n, omega=d_I h; (A1) ¦k.omega(I)¦>=alpha_1 if k_1 != 0, >=alpha_2 if k_1=0, for all I in V_r D, k in Z_K minus {0}; (A2) f in O(r,s-bar+s) real on real points with E:=¦f¦_{r,s-bar+s}<=alpha_2 r/(128 K); Case A and N>=1; use the inductive construction of g_i and f_i
SOURCE_QUANTIFIERS: 1<=i<=N
SOURCE_CONCLUSION: step i (Lemma direct on D_{r_i,S_i}, losses (rho,sigma)) is admissible and eps_{i+1}<=eps_i/4, hence eps_i<=4^{1-i} eps_1 for 1<=i<=N+1: u_i<=2^{-8}, ¦g_{i-1}¦_*<=alpha-bar rho sigma/2^4 (weights <=1/2 for j>=1, <=1/N for g_0), eps_{i+1}<=(128/127)(2/e(1/16+1/2^8)+1/8) eps_i<eps_i/4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p2:direct, N:bpN:p4:projections, N:bpN:p6:setting, stepP:p2:nfb-N, stepP:p2:nfb-first, N:bpN:p6:ext-numerics, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p2:direct | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-ind@L113-L113 | Lemma direct (d) with delta=eps_i
EDGE: N:bpN:p4:projections | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-ind@L114-L114 | ¦g_i-g_{i-1}¦<=eps_i
EDGE: N:bpN:p6:setting | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-ind@L115-L115 | weights ¦g¦_* of N
EDGE: stepP:p2:nfb-N | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-ind@L115-L115 | schedule and (2.2)
EDGE: stepP:p2:nfb-first | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-ind@L116-L116 | eps_1 bound (2.1)
EDGE: N:bpN:p6:ext-numerics | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-ind@L116-L116 | sum 4^{1-i}=4/3
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-ind@L113-L113 | the weighted norm, widths, kappa and alpha-bar
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: nfb (KAM/Planetary/Averaging/Finite.lean)
LEAN_NOTE: audit P23-12 PASS WITH NOTES; named by audit
NOTE: -

NODE: stepP:p2:nfb-concl
KIND: step
TITLE: Conclusion of the construction
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-concl@L119-L121
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-concl@L119-L121
CONTRACT_ID: stepP:p2:nfb-concl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n=n_1+n_2; D subset R^n; r>0; s-bar>=0; s>0; K>0 with kappa=2 pi K s>=6; 0<alpha_2<=alpha_1; h holomorphic on V_r D, real on V_r D cap R^n, omega=d_I h; (A1) ¦k.omega(I)¦>=alpha_1 if k_1 != 0, >=alpha_2 if k_1=0, for all I in V_r D, k in Z_K minus {0}; (A2) f in O(r,s-bar+s) real on real points with E:=¦f¦_{r,s-bar+s}<=alpha_2 r/(128 K); Case A and N>=1; compose the constructed maps
SOURCE_QUANTIFIERS: Psi=Phi_0 o ... o Phi_N
SOURCE_CONCLUSION: H o Psi=h+g+f_* with g=g_N=g(I1) (finite sum of theta-independent functions), f_*=f_{N+1}; (a) by the telescoping lemma (holomorphic, canonical, injective; periodicity and reality inherited from each Phi_i); (c) eps_{N+1}<=4^{-N} eps_1<=4^{-N-1} eps<=e^{-kappa/6} eps; (b) ¦g-g_0¦<=(4/3) eps_1<=eps/kappa<=eps/6 and the sup bound from sup<=weighted norm
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p6:telescope, N:bpN:p6:iterative, N:bpN:p4:sup-weighted, stepP:p2:nfb-ind, stepP:p2:nfb-N, N:bpN:p6:ext-numerics, bpP:p2:conv#data, stepP:p2:nfb-first
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p6:telescope | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-concl@L119-L119 | composition of the Phi_i with domains U_i=D_{r_i,S_i}
EDGE: N:bpN:p6:iterative | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-concl@L119-L119 | reality and periodicity of each Phi_i
EDGE: N:bpN:p4:sup-weighted | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-concl@L121-L121 | sup bound from the weighted norm
EDGE: stepP:p2:nfb-ind | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-concl@L120-L120 | eps_i<=4^{1-i} eps_1
EDGE: stepP:p2:nfb-N | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-concl@L120-L120 | N+1>kappa/(12 ln 2)
EDGE: N:bpN:p6:ext-numerics | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-concl@L121-L121 | sum 4^{1-i}=4/3
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-concl@L119-L119 | the weighted norm, widths, kappa and alpha-bar
EDGE: stepP:p2:nfb-first | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-concl@L121-L121 | (2.1) gives eps_1<=3 eps/(4 kappa), hence (4/3) eps_1<=eps/kappa in the final average correction
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-delta-P-d
REVIEWER: sol-delta2-P-b
LEAN_STATUS: PROVED
LEAN_REF: nfb (KAM/Planetary/Averaging/Finite.lean)
LEAN_NOTE: audit P23-12 PASS WITH NOTES; named by audit
NOTE: -

NODE: stepP:p2:nfb-disp
KIND: step
TITLE: (d) Displacement
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-disp@L123-L126
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-disp@L123-L126
CONTRACT_ID: stepP:p2:nfb-disp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n=n_1+n_2; D subset R^n; r>0; s-bar>=0; s>0; K>0 with kappa=2 pi K s>=6; 0<alpha_2<=alpha_1; h holomorphic on V_r D, real on V_r D cap R^n, omega=d_I h; (A1) ¦k.omega(I)¦>=alpha_1 if k_1 != 0, >=alpha_2 if k_1=0, for all I in V_r D, k in Z_K minus {0}; (A2) f in O(r,s-bar+s) real on real points with E:=¦f¦_{r,s-bar+s}<=alpha_2 r/(128 K); Case A and N>=1; use the constructed maps and schedule
SOURCE_QUANTIFIERS: j=1,2
SOURCE_CONCLUSION: ¦Delta I_j¦<=(1/(e alpha-bar_j s))(6 eps+4N(4/3)eps_1)<=3 eps/(alpha-bar_j s) (6.5/e<2.4<=3) and ¦Delta theta¦<=(1/(alpha-bar r))(8 eps+8N(4/3)eps_1)<=9 eps/(alpha-bar r)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p6:telescope, N:bpN:p6:iterative, bpP:p2:split, stepP:p2:nfb-ind, stepP:p2:nfb-first, stepP:p2:nfb-N, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p6:telescope | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-disp@L123-L123 | seminorms of the composition
EDGE: N:bpN:p6:iterative | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-disp@L123-L123 | (a): each step lands in the shrunken domain
EDGE: bpP:p2:split | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-disp@L123-L123 | componentwise displacement (b) for each step
EDGE: stepP:p2:nfb-ind | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-disp@L124-L124 | eps_i<=4^{1-i} eps_1
EDGE: stepP:p2:nfb-first | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-disp@L124-L124 | step 0 displacement and (2.1)
EDGE: stepP:p2:nfb-N | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-disp@L126-L126 | N<kappa/8
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:nfb-disp@L123-L123 | the weighted norm, widths, kappa and alpha-bar
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: nfb (KAM/Planetary/Averaging/Finite.lean)
LEAN_NOTE: audit P23-12 PASS WITH NOTES; named by audit
NOTE: -

NODE: bpP:p2:avg
KIND: corollary
TITLE: Averaging with two scales, in Part~3's notation
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:avg@L136-L146
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:avg@L147-L150
CONTRACT_ID: bpP:p2:avg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<alpha_2<=alpha_1; D subset R^n; r>0; s-bar,s>0; K>0 with K s>=6; h real analytic on D_r (holomorphic on V_r D, real), omega=d h; f holomorphic on D_r x T_{s-bar+s}, real analytic, 1-periodic in theta, with N-norm E:=sup_{I in D_r} sum_k ¦f^_k(I)¦ e^{(s-bar+s)¦k¦_1}<infinity; (A1) i.e. (N1) of Lemma p3:avg; 64 e K E<alpha_2 r
SOURCE_QUANTIFIERS: n_1, n_2, D, r, s-bar, s, K, alpha_1, alpha_2, h, f
SOURCE_CONCLUSION: there is a holomorphic, injective, real, symplectic Psi:D_{r/2} x T_{s-bar+s/6}->D_r x T_{s-bar+s} with Psi-id Z^n-periodic in theta1, and g=g(I1), f_* with H o Psi=h+g+f_* and in the N-norm: sup_{D_{r/2}}¦g-f_0¦<=E/4, ¦f_*¦<=e^{-K s/6}E, alpha_1 s¦I_1-I_1'¦<=3E (<=9E), alpha_2 s¦I_2-I_2'¦<=3E (<=9E), 2 pi alpha_2 r ¦theta-theta'¦<=9E
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p2:av-dict, stepP:p2:av-hyp, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p2:av-dict | blueprint-P/parts/p2-averaging.tex#bpP:p2:avg@L148-L148 | step: dictionary
EDGE: stepP:p2:av-hyp | blueprint-P/parts/p2-averaging.tex#bpP:p2:avg@L149-L149 | step: hypotheses
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#bpP:p2:avg@L137-L137 | N-norm and the dictionary of widths
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: avg (KAM/Planetary/Averaging/Finite.lean)
LEAN_NOTE: audit P23-12 PASS WITH NOTES; also bpP:p3:avg
NOTE: the interface Lemma bpP:p3:avg is proved here: this corollary depends on nothing of Part 3 (the candidate edge to p3:avg is the interface it supplies)

NODE: stepP:p2:av-dict
KIND: step
TITLE: Dictionary
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:av-dict@L148-L148
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:av-dict@L148-L148
CONTRACT_ID: stepP:p2:av-dict
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: s-bar_N=s-bar/2 pi, s_N=s/2 pi (geometric); the Part 3 norm weight e^{(s-bar+s)¦k¦_1}
SOURCE_QUANTIFIERS: as in avg
SOURCE_CONCLUSION: T_{s-bar+s}=T_{s-bar_N+s_N}, E=¦f¦_{r,s-bar_N+s_N} in the notation of the proposition, kappa=2 pi K s_N=K s>=6, alpha-bar_j s_N=alpha_j s and alpha-bar_2 r=2 pi alpha_2 r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:av-dict@L148-L148 | dictionary of widths and kappa, alpha-bar
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: avg (KAM/Planetary/Averaging/Finite.lean)
LEAN_NOTE: audit P23-12 PASS WITH NOTES; named by audit
NOTE: -

NODE: stepP:p2:av-hyp
KIND: step
TITLE: Hypotheses
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:av-hyp@L149-L149
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:av-hyp@L149-L149
CONTRACT_ID: stepP:p2:av-hyp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<alpha_2<=alpha_1; D subset R^n; r>0; s-bar,s>0; K>0 with K s>=6; h real analytic on D_r (holomorphic on V_r D, real), omega=d h; f holomorphic on D_r x T_{s-bar+s}, real analytic, 1-periodic in theta, with N-norm E:=sup_{I in D_r} sum_k ¦f^_k(I)¦ e^{(s-bar+s)¦k¦_1}<infinity; (A1) i.e. (N1) of Lemma p3:avg; 64 e K E<alpha_2 r
SOURCE_QUANTIFIERS: as in avg
SOURCE_CONCLUSION: E<=alpha_2 r/(128 K), the other hypotheses of the proposition are identical, so (a)-(d) of the proposition are the claims, with e^{-kappa/6}=e^{-K s/6}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p2:nfb, stepP:p2:av-dict, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p2:nfb | blueprint-P/parts/p2-averaging.tex#stepP:p2:av-hyp@L149-L149 | hypotheses (A1), (A2) and conclusions (a)-(d)
EDGE: stepP:p2:av-dict | blueprint-P/parts/p2-averaging.tex#stepP:p2:av-hyp@L149-L149 | dictionary to the proposition
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:av-hyp@L149-L149 | alpha-bar and geometric widths in the translated smallness condition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: avg (KAM/Planetary/Averaging/Finite.lean)
LEAN_NOTE: audit P23-12 PASS WITH NOTES; named by audit
NOTE: -

NODE: bpP:p2:osc-bracket
KIND: lemma
TITLE: Extended bracket and field estimates
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-bracket@L171-L175
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-bracket@L176-L181
CONTRACT_ID: bpP:p2:osc-bracket
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u in O(v_0,S_0), w in O(v,S) with finite norms; 0<rho<r, 0<rho_p<r_p, 0<rho_q<r_q, 0<sigma<S; v-nu<v_0 componentwise; S-sigma<S_0; phi in O(v,S) for the field estimate
SOURCE_QUANTIFIERS: n, m, v_0, v, S_0, S, nu, u, w, phi
SOURCE_CONCLUSION: {u,w} in O(v-nu,S-sigma) and ¦{u,w}¦_{v-nu,S-sigma}<=(W/delta_nu)¦u¦_{v_0,S_0}¦w¦_{v,S} with W=(1/e)(rho/(r_0-r+rho)+sigma/(S_0-S+sigma))+m(rho_q/(r_{q0}-r_q+rho_q)+rho_p/(r_{p0}-r_p+rho_p))<=2 b R, R the largest of the four ratios; nu(X_phi)<=¦phi¦_{v,S}/delta_nu on D_{v-nu,S-sigma}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p2:ob-der, stepP:p2:ob-prod, stepP:p2:ob-field, bpP:p2:s-osc#data, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p2:ob-der | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-bracket@L177-L177 | step: derivative bounds
EDGE: stepP:p2:ob-prod | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-bracket@L178-L178 | step: products
EDGE: stepP:p2:ob-field | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-bracket@L180-L180 | step: field
EDGE: bpP:p2:s-osc#data | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-bracket@L172-L172 | D_{v,S}, bracket, delta_nu, nu-norm, b
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-bracket@L172-L172 | the Fourier norm and alpha-bar/width conventions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: osc_bracket, ob_der, ob_field (KAM/Planetary/Averaging/OscillatorBracket.lean)
LEAN_NOTE: audit P23-11 PASS WITH NOTES
NOTE: -

NODE: stepP:p2:ob-der
KIND: step
TITLE: Derivative bounds
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-der@L177-L177
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-der@L177-L177
CONTRACT_ID: stepP:p2:ob-der
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u in O(v_0,S_0), w in O(v,S) with finite norms; 0<rho<r, 0<rho_p<r_p, 0<rho_q<r_q, 0<sigma<S; v-nu<v_0 componentwise; S-sigma<S_0; phi in O(v,S) for the field estimate
SOURCE_QUANTIFIERS: each coordinate separately
SOURCE_CONCLUSION: at fixed x: sum_i ¦d_{theta_i}u¦_{x,S}<=¦u¦_{x,S_0}/(e(S_0-S)) and individually globally; ¦d_{I_i}u¦<=¦u¦/(r_0-r+rho), ¦d_{p_j}u¦<=¦u¦/(r_{p0}-r_p+rho_p), ¦d_{q_j}u¦<=¦u¦/(r_{q0}-r_q+rho_q) (global norms, each coordinate separately), likewise for w with losses rho,rho_p,rho_q
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p4:cauchy, bpP:p2:s-osc#data, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p4:cauchy | blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-der@L177-L177 | Cauchy estimates (a) angular, (b) in each parameter coordinate
EDGE: bpP:p2:s-osc#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-der@L177-L177 | x=(I,p,q) as parameter
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-der@L177-L177 | the Fourier norm and width conventions used in the derivative/product estimates
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: ob_der (KAM/Planetary/Averaging/OscillatorBracket.lean)
LEAN_NOTE: audit P23-11 PASS WITH NOTES
NOTE: SOURCE_GAP: L177 evaluates the angular Cauchy bound at width S with denominator e(S_0-S), but the hypotheses only give S-sigma<S_0, not S<S_0. L179 uses the shrunken-width denominator e(S_0-S+sigma). Keep the literal L177 claim exposed; do not add S<S_0 to the hypotheses.

NODE: stepP:p2:ob-prod
KIND: step
TITLE: Products
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-prod@L178-L179
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-prod@L178-L179
CONTRACT_ID: stepP:p2:ob-prod
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u in O(v_0,S_0), w in O(v,S) with finite norms; 0<rho<r, 0<rho_p<r_p, 0<rho_q<r_q, 0<sigma<S; v-nu<v_0 componentwise; S-sigma<S_0; phi in O(v,S) for the field estimate
SOURCE_QUANTIFIERS: fixed x then sup over x
SOURCE_CONCLUSION: ¦{u,w}¦_{x,S-sigma} is bounded by the sum of the (theta,I) and (q,p) products, the last sum at most m times the product of the maxima; the (theta,I) part is (1/e)(1/((r_0-r+rho)sigma)+1/((S_0-S+sigma)rho)), the (q,p) part m(1/((r_{q0}-r_q+rho_q)rho_p)+1/((r_{p0}-r_p+rho_p)rho_q)); hence W/delta_nu with W<=2 b R
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p4:algebra, stepP:p2:ob-der, bpP:p2:s-osc#data, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p4:algebra | blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-prod@L178-L178 | norm is an algebra at fixed x
EDGE: stepP:p2:ob-der | blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-prod@L179-L179 | inserted derivative bounds
EDGE: bpP:p2:s-osc#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-prod@L178-L178 | bracket, delta_nu, b
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-prod@L178-L178 | the Fourier norm and width conventions used in the derivative/product estimates
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: osc_bracket (KAM/Planetary/Averaging/OscillatorBracket.lean)
LEAN_NOTE: local to PROVED parent osc_bracket (ruling 01:20 (b)); audit P23-11 confirms (docs/tracks/P/audits/P23-11-audit-1.md:74)
NOTE: -

NODE: stepP:p2:ob-field
KIND: step
TITLE: Field
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-field@L180-L180
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-field@L180-L180
CONTRACT_ID: stepP:p2:ob-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u in O(v_0,S_0), w in O(v,S) with finite norms; 0<rho<r, 0<rho_p<r_p, 0<rho_q<r_q, 0<sigma<S; v-nu<v_0 componentwise; S-sigma<S_0; phi in O(v,S) for the field estimate
SOURCE_QUANTIFIERS: phi in O(v,S)
SOURCE_CONCLUSION: ¦d_I phi¦/sigma<=¦phi¦/(rho sigma), ¦d_theta phi¦/rho<=¦phi¦/(e sigma rho), ¦d_p phi¦/rho_q<=¦phi¦/(rho_p rho_q), ¦d_q phi¦/rho_p<=¦phi¦/(rho_q rho_p), i.e. nu(X_phi)<=¦phi¦/delta_nu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p2:s-osc#data, N:bpN:p4:cauchy, N:bpN:p4:sup-weighted, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p2:s-osc#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-field@L180-L180 | the scaled norm nu and the field X_phi
EDGE: N:bpN:p4:cauchy | blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-field@L180-L180 | coordinate Cauchy bounds with losses rho, sigma, rho_p and rho_q
EDGE: N:bpN:p4:sup-weighted | blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-field@L180-L180 | pointwise derivative sizes from the weighted norm
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-field@L180-L180 | the Fourier norm and width conventions used in the derivative/product estimates
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: ob_field (KAM/Planetary/Averaging/OscillatorBracket.lean)
LEAN_NOTE: audit P23-11 PASS WITH NOTES
NOTE: -

NODE: bpP:p2:osc-iter
KIND: lemma
TITLE: Iterative Lemma with an oscillator pair
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-iter@L183-L189
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-iter@L190-L195
CONTRACT_ID: bpP:p2:osc-iter
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the direct-divisor data of bpP:p2:setting with q=1, Lambda={0}, h independent of p,q; the remaining source hypotheses of N iterative, with the oscillator domains and all positive losses nu of s-osc#data, rho sigma replaced by delta_nu, and ¦g¦_R=sum_j R_j ¦g_j¦; ¦f¦_{v,S}=delta<=alpha-bar delta_nu/(16 b)
SOURCE_QUANTIFIERS: n, m, v, S, nu, K, alpha-bar, f, g_j, R_j
SOURCE_CONCLUSION: All conclusions of N iterative in direct form on the oscillator domains, including the holomorphic injective periodic map Phi=X_phi^1, reality under the inherited realness premises, symplectic for dtheta^dI+dq^dp, and the transformed normal form, with the replacements at L184; (a) ¦Phi_theta-theta¦<=delta/(alpha-bar rho), ¦Phi_I-I¦<=delta/(e alpha-bar sigma), ¦Phi_q-q¦<=delta/(alpha-bar rho_p), ¦Phi_p-p¦<=delta/(alpha-bar rho_q); (b) ¦f_+¦_{v-2nu,S-2 sigma}<=(1-2 e b delta/(alpha-bar delta_nu))^{-1}((2b/(alpha-bar delta_nu))(¦g¦_R+delta)+e^{-2 pi K sigma}) delta
CONSTANT_SCOPE: constants as in N iterative with 2/e replaced by 2b
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p2:oi-transfer, stepP:p2:oi-ratio, stepP:p2:oi-range, stepP:p2:oi-disp, bpP:p2:direct, N:bpN:p6:iterative, bpP:p2:s-osc#data, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p2:oi-transfer | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-iter@L191-L191 | step: transfer
EDGE: stepP:p2:oi-ratio | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-iter@L192-L192 | step: adjoint ratio
EDGE: stepP:p2:oi-range | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-iter@L193-L193 | step: smallness range
EDGE: stepP:p2:oi-disp | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-iter@L194-L194 | step: displacement
EDGE: bpP:p2:direct | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-iter@L184-L184 | direct form of the iterative lemma
EDGE: N:bpN:p6:iterative | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-iter@L184-L184 | the lemma extended
EDGE: bpP:p2:s-osc#data | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-iter@L184-L184 | delta_nu, b, R_j, the oscillator domains
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-iter@L184-L184 | the Fourier norm and alpha-bar/width conventions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: osc_iter (KAM/Planetary/Averaging/OscillatorStepComplete.lean)
LEAN_NOTE: audit P23-13j PASS; composed of P23-13h PASS WITH NOTES (osc_remainder_bound) and earlier P23-13 audits; signed statement exact
NOTE: source-gap L196 (the extension is stated by a short list of changes, not rewritten in N) is bridged by the four steps; the proof is a transfer argument and the reviewer should check it is complete

NODE: stepP:p2:oi-transfer
KIND: step
TITLE: Transfer
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-transfer@L191-L191
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-transfer@L191-L191
CONTRACT_ID: stepP:p2:oi-transfer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the direct-divisor data of bpP:p2:setting with q=1, Lambda={0}, h independent of p,q; the remaining source hypotheses of N iterative, with the oscillator domains and all positive losses nu of s-osc#data, rho sigma replaced by delta_nu, and ¦g¦_R=sum_j R_j ¦g_j¦; ¦f¦_{v,S}=delta<=alpha-bar delta_nu/(16 b); transfer the homological solution, bracket and field constructions to the enlarged phase space
SOURCE_QUANTIFIERS: each cited N statement
SOURCE_CONCLUSION: N homological is unchanged (¦phi¦<=delta/alpha-bar); N flow holds for an arbitrary norm and open set; N symplectic uses only D F=J S with S symmetric and J^T=-J, true for the enlarged J, and N canonical follows; N adjoint, composition, transform, canonical-map use the geometry only through the bracket and field bounds: replace N bracket and vf-bound by Lemma osc-bracket and rho sigma by delta_nu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p2:osc-bracket, N:bpN:p6:homological, N:bpN:p5:flow, N:bpN:p5:symplectic, N:bpN:p5:canonical, N:bpN:p5:adjoint, N:bpN:p5:composition, N:bpN:p5:transform, N:bpN:p5:canonical-map, bpP:p2:s-osc#data, bpP:p2:direct, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p2:osc-bracket | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-transfer@L191-L191 | replacement bracket and field bounds
EDGE: N:bpN:p6:homological | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-transfer@L191-L191 | unchanged
EDGE: N:bpN:p5:flow | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-transfer@L191-L191 | arbitrary norm and open set
EDGE: N:bpN:p5:symplectic | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-transfer@L191-L191 | D F=J S with S symmetric
EDGE: N:bpN:p5:canonical | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-transfer@L191-L191 | follows from symplectic
EDGE: N:bpN:p5:adjoint | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-transfer@L191-L191 | transfer
EDGE: N:bpN:p5:composition | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-transfer@L191-L191 | transfer
EDGE: N:bpN:p5:transform | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-transfer@L191-L191 | transfer
EDGE: N:bpN:p5:canonical-map | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-transfer@L191-L191 | transfer
EDGE: bpP:p2:s-osc#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-transfer@L191-L191 | delta_nu, the enlarged J
EDGE: bpP:p2:direct | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-transfer@L191-L191 | the homological equation under Div_1 rather than the original N hypotheses
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-transfer@L191-L191 | weighted norms, alpha-bar and Fourier widths
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: route substitution (D27, gap survey 2 item 4): osc_iter uses direct re-proofs; consumer aa-same is BYPASSED
NOTE: -

NODE: stepP:p2:oi-ratio
KIND: step
TITLE: The adjoint ratio
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-ratio@L192-L192
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-ratio@L192-L192
CONTRACT_ID: stepP:p2:oi-ratio
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the direct-divisor data of bpP:p2:setting with q=1, Lambda={0}, h independent of p,q; the remaining source hypotheses of N iterative, with the oscillator domains and all positive losses nu of s-osc#data, rho sigma replaced by delta_nu, and ¦g¦_R=sum_j R_j ¦g_j¦; ¦f¦_{v,S}=delta<=alpha-bar delta_nu/(16 b); use the generator constructed by oi-transfer
SOURCE_QUANTIFIERS: h>=0
SOURCE_CONCLUSION: each bracket costs a factor e b more, the ratio becomes e^2 b eta/4<=e b eta with eta:=2¦phi¦/delta_nu; theta_phi:=2 e b ¦phi¦/delta_nu; the Lie series converges with ¦ad^h_phi u¦/h!<=theta_phi^h ¦u¦ and ¦u o X^1_phi¦<=(1-theta_phi)^{-1}¦u¦, same for the integral remainders (the ratio b eta is not claimed since e^2/4>1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p5:transform, N:bpN:p5:composition-integral, bpP:p2:osc-bracket, stepP:p2:oi-transfer, N:bpN:p5:adjoint, bpP:p2:conv#data, bpP:p2:s-osc#data
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p5:transform | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-ratio@L192-L192 | Lie transform estimate
EDGE: N:bpN:p5:composition-integral | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-ratio@L192-L192 | integral remainder
EDGE: bpP:p2:osc-bracket | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-ratio@L192-L192 | bracket constant 2b/delta'
EDGE: stepP:p2:oi-transfer | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-ratio@L192-L192 | transferred iterated-bracket estimate
EDGE: N:bpN:p5:adjoint | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-ratio@L192-L192 | the iterated-bracket estimate with ratio e eta/4
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-ratio@L192-L192 | weighted norms, alpha-bar and Fourier widths
EDGE: bpP:p2:s-osc#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-ratio@L192-L192 | oscillator field, losses, delta_nu and b
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: p2_oi_ratio (KAM/Planetary/Averaging/OscillatorNodes.lean)
LEAN_NOTE: audit GAP-P2 round 4 PASS WITH NOTES
NOTE: -

NODE: stepP:p2:oi-range
KIND: step
TITLE: Smallness range
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-range@L193-L193
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-range@L193-L193
CONTRACT_ID: stepP:p2:oi-range
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the direct-divisor data of bpP:p2:setting with q=1, Lambda={0}, h independent of p,q; the remaining source hypotheses of N iterative, with the oscillator domains and all positive losses nu of s-osc#data, rho sigma replaced by delta_nu, and ¦g¦_R=sum_j R_j ¦g_j¦; ¦f¦_{v,S}=delta<=alpha-bar delta_nu/(16 b); use the source smallness delta<=alpha-bar delta_nu/(16 b)
SOURCE_QUANTIFIERS: as in osc-iter
SOURCE_CONCLUSION: theta_phi<=2 e b delta/(alpha-bar delta_nu)<=e/8<0.34 and (16/9) theta_phi<0.61<1, so the Lie series equals the composition at shrunken losses; (a) and (b) follow as in N iterative with 2/e->2b and 1-2 q delta/(alpha-bar rho sigma)->1-theta_phi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p5:composition, N:bpN:p6:iterative, stepP:p2:oi-ratio, stepP:p2:oi-transfer, bpP:p2:conv#data, bpP:p2:s-osc#data
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p5:composition | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-range@L193-L193 | equality of the Lie series with the composition, remainder factor 16/9
EDGE: N:bpN:p6:iterative | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-range@L193-L193 | (a) and (b) as in N iterative
EDGE: stepP:p2:oi-ratio | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-range@L193-L193 | theta_phi
EDGE: stepP:p2:oi-transfer | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-range@L193-L193 | the bound on phi needed to derive eps_phi<=1/4
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-range@L193-L193 | weighted norms, alpha-bar and Fourier widths
EDGE: bpP:p2:s-osc#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-range@L193-L193 | oscillator field, losses, delta_nu and b
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: p2_oi_range (KAM/Planetary/Averaging/OscillatorNodes.lean)
LEAN_NOTE: audit GAP-P2 round 4 PASS WITH NOTES (theta_phi from the actual generator norm)
NOTE: the forward mention that the assumption holds at every step of Prop osc-averaging is a consistency pointer and not an edge (osc-averaging uses osc-iter)

NODE: stepP:p2:oi-disp
KIND: step
TITLE: Displacement
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-disp@L194-L194
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-disp@L194-L194
CONTRACT_ID: stepP:p2:oi-disp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the direct-divisor data of bpP:p2:setting with q=1, Lambda={0}, h independent of p,q; the remaining source hypotheses of N iterative, with the oscillator domains and all positive losses nu of s-osc#data, rho sigma replaced by delta_nu, and ¦g¦_R=sum_j R_j ¦g_j¦; ¦f¦_{v,S}=delta<=alpha-bar delta_nu/(16 b); use the generator and flow constructed in oi-transfer and oi-range
SOURCE_QUANTIFIERS: as in osc-iter
SOURCE_CONCLUSION: ¦d_I phi¦<=¦phi¦/rho, ¦d_theta phi¦<=¦phi¦/(e sigma), ¦d_p phi¦<=¦phi¦/rho_p, ¦d_q phi¦<=¦phi¦/rho_q, giving the displacement bounds (a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p2:osc-bracket, stepP:p2:sp-field, stepP:p2:oi-transfer, stepP:p2:oi-range, bpP:p2:conv#data, bpP:p2:s-osc#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p2:osc-bracket | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-disp@L194-L194 | field estimate
EDGE: stepP:p2:sp-field | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-disp@L194-L194 | the componentwise trajectory argument explicitly reused here
EDGE: stepP:p2:oi-transfer | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-disp@L194-L194 | the generator norm bound delta/alpha-bar
EDGE: stepP:p2:oi-range | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-disp@L194-L194 | the established flow domain and smallness range
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-disp@L194-L194 | weighted norms, alpha-bar and Fourier widths
EDGE: bpP:p2:s-osc#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:oi-disp@L194-L194 | oscillator field, losses, delta_nu and b
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: osc_iter (KAM/Planetary/Averaging/OscillatorStepComplete.lean)
LEAN_NOTE: local to PROVED parent osc_iter (ruling 01:20 (b)); audit P23-13 confirms (docs/tracks/P/audits/P23-13-audit-1.md:97)
NOTE: -

NODE: bpP:p2:osc-averaging
KIND: proposition
TITLE: Averaging with oscillators, one scale
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-averaging@L198-L210
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-averaging@L211-L220
CONTRACT_ID: bpP:p2:osc-averaging
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of s-osc#data; h holomorphic on V_r D, real, omega=d h (h independent of p,q); alpha>0; K>0; kappa=2 pi K s>=6; (O1) ¦k.omega(I)¦>=alpha for I in V_r D, 0<¦k¦_1<=K; (O2) f in O(v,s-bar+s) real, E:=¦f¦_{v,s-bar+s} with 2^12 b K E s<=alpha d
SOURCE_QUANTIFIERS: n, m, D, v, s, s-bar, alpha, K, then h, then f; alpha-bar=2 pi alpha
SOURCE_CONCLUSION: there is a holomorphic, injective, real Psi:D_{v/2,s-bar+s/6}->D_{v,s-bar+s}, Psi-id periodic in theta, symplectic for d theta^dI+dq^dp, with H o Psi=h+g+f_* on D_{v/2,s-bar+s/6}, H=h+f, g=g(I,p,q) independent of theta, real, and ¦g-f^_0¦<=400 b E^2/(alpha-bar d), ¦f_*¦<=e^{-kappa/6}E, alpha-bar s¦I-I'¦<=3E, alpha-bar r¦theta-theta'¦<=9E, alpha-bar r_q¦p-p'¦<=9E, alpha-bar r_p¦q-q'¦<=9E
CONSTANT_SCOPE: constants 400, 2^12 absolute; no dependence on n
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p2:oa-first, stepP:p2:oa-iter, stepP:p2:oa-concl, bpP:p2:s-osc#data, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p2:oa-first | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-averaging@L213-L213 | step 0
EDGE: stepP:p2:oa-iter | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-averaging@L216-L216 | iteration (Case A)
EDGE: stepP:p2:oa-concl | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-averaging@L219-L219 | conclusion
EDGE: bpP:p2:s-osc#data | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-averaging@L198-L198 | the setting, d, b
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#bpP:p2:osc-averaging@L199-L199 | kappa, alpha-bar
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: OscHyp (KAM/Planetary/Averaging/OscillatorHyp.lean); osc_averaging, oscGood_of_hyp (KAM/Planetary/Averaging/OscillatorFinite.lean)
LEAN_NOTE: audit P23-15b PASS WITH NOTES; consumes the complete signed osc_iter (P23-13j)
NOTE: -

NODE: stepP:p2:oa-first
KIND: step
TITLE: Step 0
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-first@L213-L215
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-first@L213-L215
CONTRACT_ID: stepP:p2:oa-first
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of s-osc#data; h holomorphic on V_r D, real, omega=d h (h independent of p,q); alpha>0; K>0; kappa=2 pi K s>=6; (O1) ¦k.omega(I)¦>=alpha for I in V_r D, 0<¦k¦_1<=K; (O2) f in O(v,s-bar+s) real, E:=¦f¦_{v,s-bar+s} with 2^12 b K E s<=alpha d; eps=E; put rho_0=r/8, rho_p0=r_p/8, rho_q0=r_q/8, sigma_0=s/6
SOURCE_QUANTIFIERS: cases A (e^{-kappa/6}<=2 b y_0), B
SOURCE_CONCLUSION: eps_1<=(1-2 e b y_0)^{-1}(2 b y_0+e^{-kappa/6}) eps; Case A: eps_1<=0.08 eps/kappa and eps_1<=294 b eps^2/(alpha-bar d); Case B (doubled losses): ¦f_1¦<=e^{-kappa/6} eps, stop with g=f^_0, displacements <3 eps/(alpha-bar s), <=4 eps/(alpha-bar r), <=4 eps/(alpha-bar r_q), <=4 eps/(alpha-bar r_p)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p2:osc-iter, bpP:p2:s-osc#data, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p2:osc-iter | blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-first@L213-L213 | (b) with ¦g¦_R=0
EDGE: bpP:p2:s-osc#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-first@L213-L213 | delta_nu, b
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-first@L213-L213 | the norm, kappa and alpha-bar
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: osc_averaging (KAM/Planetary/Averaging/OscillatorFinite.lean)
LEAN_NOTE: local to PROVED parent osc_averaging (ruling 01:20 (b)); audit P23-15b confirms (docs/tracks/P/audits/P23-15b-audit-1.md:164)
NOTE: -

NODE: stepP:p2:oa-iter
KIND: step
TITLE: Iteration (Case A)
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-iter@L216-L218
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-iter@L216-L218
CONTRACT_ID: stepP:p2:oa-iter
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of s-osc#data; h holomorphic on V_r D, real, omega=d h (h independent of p,q); alpha>0; K>0; kappa=2 pi K s>=6; (O1) ¦k.omega(I)¦>=alpha for I in V_r D, 0<¦k¦_1<=K; (O2) f in O(v,s-bar+s) real, E:=¦f¦_{v,s-bar+s} with 2^12 b K E s<=alpha d; Case A of oa-first; N=floor(kappa/(12 ln 2)); split N=0 and N>=1
SOURCE_QUANTIFIERS: 1<=i<=N
SOURCE_CONCLUSION: N=0: stop; N>=1: losses rho=r/8N, rho_p=r_p/8N, rho_q=r_q/8N, sigma=s/4N, delta_nu>=d/(64N^2), eps/N<=alpha-bar d/(2^15 b N^2) (2.3), eps_1<=0.08 eps/(8N); ¦g_{i-1}¦_R+eps_i<=1.02 eps/N, x<=0.004, 2 e b u_i<1.1e-4 and eps_{i+1}<=(128/127)(0.004+1/8) eps_i<eps_i/4, so eps_i<=4^{1-i} eps_1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p2:nfb-N, bpP:p2:osc-iter, stepP:p2:oa-first, bpP:p2:conv#data, bpP:p2:s-osc#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p2:nfb-N | blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-iter@L216-L216 | the schedule of radii and budget
EDGE: bpP:p2:osc-iter | blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-iter@L218-L218 | (b) at each step
EDGE: stepP:p2:oa-first | blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-iter@L217-L217 | eps_1 bounds of Case A
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-iter@L216-L216 | the norm, kappa and alpha-bar
EDGE: bpP:p2:s-osc#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-iter@L216-L216 | oscillator radii, b, d and delta_nu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: osc_averaging (KAM/Planetary/Averaging/OscillatorFinite.lean)
LEAN_NOTE: local to PROVED parent osc_averaging (ruling 01:20 (b)); audit P23-15b confirms (docs/tracks/P/audits/P23-15b-audit-1.md:109)
NOTE: -

NODE: stepP:p2:oa-concl
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-concl@L219-L219
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-concl@L219-L219
CONTRACT_ID: stepP:p2:oa-concl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of s-osc#data; h holomorphic on V_r D, real, omega=d h (h independent of p,q); alpha>0; K>0; kappa=2 pi K s>=6; (O1) ¦k.omega(I)¦>=alpha for I in V_r D, 0<¦k¦_1<=K; (O2) f in O(v,s-bar+s) real, E:=¦f¦_{v,s-bar+s} with 2^12 b K E s<=alpha d; Case A and N>=1; use the constructed finite sequence of maps
SOURCE_QUANTIFIERS: as in osc-averaging
SOURCE_CONCLUSION: ¦f_*¦<=4^{-(N+1)} eps<=e^{-kappa/6} eps; ¦g-f^_0¦<=(4/3) eps_1<=400 b eps^2/(alpha-bar d); displacements I: (1/(e alpha-bar s))(6 eps+4N(4/3)eps_1)<=2.3 eps/(alpha-bar s), theta: <=8.2 eps/(alpha-bar r) (N eps_1<=0.01 eps), same for p, q with r_q, r_p
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p2:nfb-concl, bpP:p2:osc-iter, N:bpN:p6:telescope, stepP:p2:oa-iter, stepP:p2:oa-first, bpP:p2:conv#data, bpP:p2:s-osc#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p2:nfb-concl | blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-concl@L219-L219 | same conclusion argument as for the proposition
EDGE: bpP:p2:osc-iter | blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-concl@L219-L219 | (a) for the displacements
EDGE: N:bpN:p6:telescope | blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-concl@L219-L219 | telescoping displacements
EDGE: stepP:p2:oa-iter | blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-concl@L219-L219 | eps_i<=4^{1-i} eps_1
EDGE: stepP:p2:oa-first | blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-concl@L219-L219 | eps_1 bound
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-concl@L219-L219 | the norm, kappa and alpha-bar
EDGE: bpP:p2:s-osc#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:oa-concl@L219-L219 | oscillator radii, b, d and delta_nu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: osc_averaging (KAM/Planetary/Averaging/OscillatorFinite.lean)
LEAN_NOTE: local to PROVED parent osc_averaging (ruling 01:20 (b)); audit P23-15b confirms (docs/tracks/P/audits/P23-15b-audit-1.md:109)
NOTE: -

NODE: bpP:p2:averaged-remainder
KIND: proposition
TITLE: Averaged remainder for \Pref{bpP:p0:pg}: CP10 \S4, Step~1
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:averaged-remainder@L222-L234
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:averaged-remainder@L235-L238
CONTRACT_ID: bpP:p2:averaged-remainder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n=n_1>=1, m=n_2>=1; D-bar subset R^n; rho-bar, eps_0>0; s_0>0 (geometric); 0<epsilon<e^{-1/5}; mu>0; v_0=(rho-bar,eps_0,eps_0); H=H_0(I)+mu P(theta,I,p,q), H_0 holomorphic on V_{rho-bar}D-bar and real, P in O(v_0,s_0) real with ¦P¦_{v_0,s_0}<=1; <P>:=int_{T^n}P d theta=P^_0; K chosen by e^{-2 pi K s_0/6}=epsilon^5 (K=(15/(pi s_0)) log(1/epsilon), kappa=30 log(1/epsilon)>=6); alpha-bar=2 pi alpha, d=min{rho-bar s_0,eps_0^2}; (R1) ¦k.dH_0(I)¦>=alpha for I in V_{rho-bar}D-bar, 0<¦k¦_1<=K; (R2) 2^12(1+m) K s_0 mu<=alpha d
SOURCE_QUANTIFIERS: n, m, D-bar, rho-bar, eps_0, s_0, epsilon, mu, then H_0, P, then alpha (K, d determined)
SOURCE_CONCLUSION: there is a map phi-bar:D_{v_0/2,s_0/6}->D_{v_0,s_0} as in Proposition osc-averaging (s-bar=0, s=s_0) with H o phi-bar=H_0+mu<P>+P~ on D_{v_0/2,s_0/6}, ¦P~¦_{v_0/2,s_0/6}<=400(1+m)mu^2/(alpha-bar d)+mu epsilon^5, P~=(g-mu<P>)+f_*, g=g(I,p,q), ¦f_*¦<=mu epsilon^5 (f_*=mu epsilon^5 P-bar with ¦P-bar¦<=1), and alpha-bar s_0¦I-I-bar¦<=3 mu, alpha-bar rho-bar¦theta-theta-bar¦<=9 mu, alpha-bar eps_0¦p-p-bar¦,alpha-bar eps_0¦q-q-bar¦<=9 mu
CONSTANT_SCOPE: K depends on (epsilon, s_0) only; d on (rho-bar, s_0, eps_0); perturbation size E=mu before and mu epsilon^5 after averaging
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p2:ar-apply, stepP:p2:ar-collect, bpP:p2:osc-averaging, bpP:p2:s-osc#data, bpP:p2:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p2:ar-apply | blueprint-P/parts/p2-averaging.tex#bpP:p2:averaged-remainder@L236-L236 | step: apply
EDGE: stepP:p2:ar-collect | blueprint-P/parts/p2-averaging.tex#bpP:p2:averaged-remainder@L237-L237 | step: collect
EDGE: bpP:p2:osc-averaging | blueprint-P/parts/p2-averaging.tex#bpP:p2:averaged-remainder@L229-L229 | the map phi-bar is that of the proposition
EDGE: bpP:p2:s-osc#data | blueprint-P/parts/p2-averaging.tex#bpP:p2:averaged-remainder@L223-L223 | D_{v_0,s_0}, norm, d, b=1+m
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#bpP:p2:averaged-remainder@L224-L224 | kappa, alpha-bar
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: averaged_remainder, osc_zero_mode (KAM/Planetary/Averaging/OscillatorFinite.lean)
LEAN_NOTE: audit P23-15b PASS WITH NOTES
NOTE: [pre-extract: dropped reference to bpP:p0:pg, which part p2 proves or sets up]

NODE: stepP:p2:ar-apply
KIND: step
TITLE: Apply
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:ar-apply@L236-L236
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:ar-apply@L236-L236
CONTRACT_ID: stepP:p2:ar-apply
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n=n_1>=1, m=n_2>=1; D-bar subset R^n; rho-bar, eps_0>0; s_0>0 (geometric); 0<epsilon<e^{-1/5}; mu>0; v_0=(rho-bar,eps_0,eps_0); H=H_0(I)+mu P(theta,I,p,q), H_0 holomorphic on V_{rho-bar}D-bar and real, P in O(v_0,s_0) real with ¦P¦_{v_0,s_0}<=1; <P>:=int_{T^n}P d theta=P^_0; K chosen by e^{-2 pi K s_0/6}=epsilon^5 (K=(15/(pi s_0)) log(1/epsilon), kappa=30 log(1/epsilon)>=6); alpha-bar=2 pi alpha, d=min{rho-bar s_0,eps_0^2}; (R1) ¦k.dH_0(I)¦>=alpha for I in V_{rho-bar}D-bar, 0<¦k¦_1<=K; (R2) 2^12(1+m) K s_0 mu<=alpha d; specialize f=mu P, s-bar=0, s=s_0, r=rho-bar, r_p=r_q=eps_0, h=H_0; use mu as the upper bound for the actual E=¦mu P¦<=mu
SOURCE_QUANTIFIERS: as in the proposition
SOURCE_CONCLUSION: Proposition osc-averaging gives H o phi-bar=H_0+g+f_*, and f^_0=mu <P>
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p2:osc-averaging, bpP:p2:conv#data, bpP:p2:s-osc#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p2:osc-averaging | blueprint-P/parts/p2-averaging.tex#stepP:p2:ar-apply@L236-L236 | applied with (O1), (O2) given by (R1), (R2)
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:ar-apply@L236-L236 | the norm, kappa and alpha-bar
EDGE: bpP:p2:s-osc#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:ar-apply@L236-L236 | the oscillator radii, b and d
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: p2_ar_apply (KAM/Planetary/Averaging/OscillatorNodes.lean)
LEAN_NOTE: audit GAP-P2 round 4 PASS WITH NOTES
NOTE: -

NODE: stepP:p2:ar-collect
KIND: step
TITLE: Collect
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:ar-collect@L237-L237
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#stepP:p2:ar-collect@L237-L237
CONTRACT_ID: stepP:p2:ar-collect
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: P~:=(g-mu<P>)+f_*; choice e^{-kappa/6}=epsilon^5
SOURCE_QUANTIFIERS: as in the proposition
SOURCE_CONCLUSION: ¦P~¦ is at most the sum of the two bounds of the proposition and e^{-kappa/6} mu=mu epsilon^5
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p2:osc-averaging, stepP:p2:ar-apply, bpP:p2:conv#data, bpP:p2:s-osc#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p2:osc-averaging | blueprint-P/parts/p2-averaging.tex#stepP:p2:ar-collect@L237-L237 | bounds on ¦g-f^_0¦ and ¦f_*¦
EDGE: stepP:p2:ar-apply | blueprint-P/parts/p2-averaging.tex#stepP:p2:ar-collect@L237-L237 | H o phi-bar=H_0+g+f_* and f^_0=mu<P>
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:ar-collect@L237-L237 | the norm, kappa and alpha-bar
EDGE: bpP:p2:s-osc#data | blueprint-P/parts/p2-averaging.tex#stepP:p2:ar-collect@L237-L237 | the oscillator radii, b and d
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: p2_ar_apply_collect (KAM/Planetary/Averaging/OscillatorNodes.lean)
LEAN_NOTE: audit GAP-P2 round 4 PASS WITH NOTES (joint export with ar-apply)
NOTE: -

NODE: bpP:p2:use5
KIND: claim
TITLE: How Part~5 uses this
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:use5@L240-L246
PROOF_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:use5@L240-L246
CONTRACT_ID: bpP:p2:use5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the conversion of Proposition averaged-remainder from the CP angle-action variables (phi_CP,I_CP) with 2 pi-periodic angles and Cartesian oscillators remaining
SOURCE_QUANTIFIERS: (theta,I,p,q)=(phi_CP/2 pi, 2 pi I_CP, p_CP, q_CP)
SOURCE_CONCLUSION: the pure all-angle conversion of Lemma period-dictionary must not be applied to (phi,I,p,q); use instead the canonical chart (a c-chart of period-convert with c=1 acting on the angle-action block only): the Hamiltonian is the same function, omega=omega_CP/2 pi, alpha=alpha_CP/2 pi, rho-bar=2 pi rho-bar_CP, s_0=s_CP/2 pi, eps_0 unchanged; invariants alpha-bar=alpha_CP, d=min{rho-bar s_0,eps_0^2}, K s_0/alpha=K s_CP/alpha_CP, so (R2) is the same inequality in both conventions; displacement bounds alpha_CP s_CP¦Delta I_CP¦<=6 mu, alpha_CP rho-bar_CP¦Delta phi¦<=9 mu, alpha_CP eps_0¦Delta p¦,¦Delta q¦<=9 mu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p2:averaged-remainder, bpP:p2:conv#data, bpP:p1:chart
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p2:averaged-remainder | blueprint-P/parts/p2-averaging.tex#bpP:p2:use5@L243-L243 | (R2), d and the displacement bounds being converted
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#bpP:p2:use5@L243-L243 | norm and widths
EDGE: bpP:p1:chart | blueprint-P/parts/p2-averaging.tex#bpP:p2:use5@L243-L243 | the displayed chart has conformal factor 1; L244 computes preservation of the angle/action form
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: use5, use5_constants, oscPeriodChart (KAM/Planetary/TwoScale/Period.lean)
LEAN_NOTE: audit P23-08 PASS WITH NOTES
NOTE: Retain the mathematical dictionary (3): Part 5 steps av-dict and av-id consume it at L176 and L179. SPEC administrative exclusions have an explicit consumed-fact exception. The reference to period-convert with c=1 is a misleading pointer: the chart here rescales the angle and action reciprocally. Paragraph (1) delegates its estimate to Part 5 and creates no dependency on a Part 5 theorem.

NODE: bpP:p1:conv#data
KIND: definition
TITLE: Conventions of Part 1: phase space, form, X_ell, iota_k, S_c
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:conv#data@L17-L17
PROOF_SOURCE: -
CONTRACT_ID: bpP:p1:conv#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (conventions; typing data: d, the frozen phase space, form and field of Part 0)
SOURCE_QUANTIFIERS: d in N; z=(z_1,z_2) in Ph_d=R^d x R^d (positions, momenta), max norms, Lebesgue measure; k in Z^d; c>0
SOURCE_CONCLUSION: defines M_0=((0,-1),(1,0)), J_0=-M_0; the frozen form Omega(v,w)=sum_i(v_{2,i}w_{1,i}-v_{1,i}w_{2,i})=v^T M_0 w; X_ell:=((ell(0,e_i))_i,(-ell(e_i,0))_i) for a linear form ell, so X_H(z)=X_{DH(z)} and X_H(z)=0 where H is not differentiable (Lean totality); iota_k:=((k_i)_i,0); S_c(z_1,z_2):=(c z_1,z_2)
CONSTANT_SCOPE: M_0, J_0 absolute; X_ell depends on ell only; iota_k on k only; S_c on c>0 only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:phase#Phase, bpP:p0:hamsymp#symplecticForm, bpP:p0:hamsymp#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:conv#data@L17-L17 | the phase space Ph_d and its max-norm and Lebesgue conventions
EDGE: bpP:p0:hamsymp#symplecticForm | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:conv#data@L17-L17 | the frozen form Omega is restated as v^T M_0 w
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:conv#data@L17-L17 | X_H(z)=X_{DH(z)} and X_H=0 off differentiability points
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: linearField, hamiltonianVectorField_eq_linearField (KAM/Planetary/Hamiltonian/Algebra.lean); angleScale, angleScaleCLM, angleScaleCLM_apply, fullShift, fullShift_eq_angleScale (KAM/Planetary/Hamiltonian/Chart.lean)
LEAN_NOTE: composite of audits PP1-1 PASS WITH NOTES + PP1-4 PASS WITH NOTES; iota_k is existing angleShift (KAM/ODE/Basic.lean)
NOTE: section data of Part 1 (prose L17); bpP:p0:totality is the Lean-totality explanation and is not consumed beyond the definition of the frozen field

NODE: bpP:p2:conv#data
KIND: definition
TITLE: Conventions of Part 2: norm, widths, dictionary, index splitting
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:conv#data@L24-L36
PROOF_SOURCE: -
CONTRACT_ID: bpP:p2:conv#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (conventions; typing data: n, D subset C^n, geometric strip half-width s, radius r)
SOURCE_QUANTIFIERS: n=n_1+n_2; k=(k_1,k_2), theta=(theta_1,theta_2), I=(I_1,I_2); s>0 geometric; r>0; K>=0; alpha_j>0
SOURCE_CONCLUSION: defines the norm of track N: for u holomorphic on D_{r,s}=T_s x V_r D and 1-periodic in theta, ¦u¦_{r,s}=sup_{I in V_r D} sum_k ¦u^_k(I)¦ e^{2 pi ¦k¦_1 s}, with T_s={¦Im theta¦_inf<s}, V_r D={I in C^n: dist_inf(I,D)<r}, O(r,s) the class of such u; the dictionary to Part 3 (coefficient-radius widths sigma, T_sigma^{P3}=T_{sigma/2 pi}, (s-bar,s) of Part 3 correspond to (s-bar/2 pi,s/2 pi) here, same frequencies, divisors, Hamilton equations); kappa:=2 pi K s, alpha-bar_j:=2 pi alpha_j, Z_K={k in Z^n: ¦k¦_1<=K}; a function is independent of theta_1 iff all its modes have k_1=0; external facts 12 ln 2>8, sum_{i>=1}4^{1-i}=4/3, ¦k.v¦<=¦k¦_1 ¦v¦_inf
CONSTANT_SCOPE: none (notation; norm is N norm, not the sum_k sup_I norm of Part 3 as printed: only ¦.¦_{r,s}<=sum_k sup_I holds)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p4:norm, N:bpN:p4:domains, N:bpN:p6:ext-numerics
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p4:norm | blueprint-P/parts/p2-averaging.tex#bpP:p2:conv#data@L25-L25 | the norm ¦u¦_{r,s} is that of track N
EDGE: N:bpN:p4:domains | blueprint-P/parts/p2-averaging.tex#bpP:p2:conv#data@L26-L26 | the domains T_s and V_r D
EDGE: N:bpN:p6:ext-numerics | blueprint-P/parts/p2-averaging.tex#bpP:p2:conv#data@L36-L36 | the explicitly inherited numerical facts 12 ln 2>8 and sum 4^{1-i}=4/3
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: geometricWidth, realBase, coefficientDom, realTube, firstBlock, lastBlock, block_bridge, conv_data (KAM/Planetary/Averaging/Setting.lean)
LEAN_NOTE: audit P23-01 PASS WITH NOTES
NOTE: section data of Part 2 (prose L24-L36); the N-dictionary remark bpN:p4:dictionary is cited at L28 as a pointer and is not consumed (the dictionary is stated here); the N section-level external lists (s-ext of Parts 4 and 6) are not importable nodes (SPEC report: 2 skipped section labels)

NODE: bpP:p2:s-osc#data
KIND: definition
TITLE: Oscillator setting of Part 2: polydisc, norm, bracket, d and b
STATEMENT_SOURCE: blueprint-P/parts/p2-averaging.tex#bpP:p2:s-osc#data@L167-L169
PROOF_SOURCE: -
CONTRACT_ID: bpP:p2:s-osc#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n,m>=1; D subset R^n; v=(r,r_p,r_q); s>0; s-bar>=0; the N norm of conv#data with sup over (I,p,q)
SOURCE_QUANTIFIERS: n, m, D, v, s, s-bar; losses nu=(rho,rho_p,rho_q,sigma)
SOURCE_CONCLUSION: defines D_{v,S}=T_S x V_r D x B_{r_p} x B_{r_q} with B_a={x in C^m:¦x¦_inf<a}; O(v,S) and ¦.¦_{v,S} as in N with the sup over (I,p,q), only theta Fourier expanded; the field X_u=(d_I u,-d_theta u; d_p u,-d_q u) in the order (theta-dot,I-dot;q-dot,p-dot) and the bracket {u,w}=sum_i(d_{theta_i}u d_{I_i}w-d_{I_i}u d_{theta_i}w)+sum_j(d_{q_j}u d_{p_j}w-d_{p_j}u d_{q_j}w)=Du.X_w; d:=min{rs,r_p r_q}, b:=1+m; for losses nu: delta_nu:=min{rho sigma,rho_p rho_q} and the scaled norm nu(a,b_I,c_q,c_p)=max(¦a¦/sigma,¦b_I¦/rho,¦c_q¦/rho_q,¦c_p¦/rho_p)
CONSTANT_SCOPE: none (notation; the Euclidean ball of CP10 is replaced by the max-norm polydisc B_a)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p2:conv#data, N:bpN:p4:norm
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p2:conv#data | blueprint-P/parts/p2-averaging.tex#bpP:p2:s-osc#data@L167-L167 | the N norm, D_{r,s} and V_r D
EDGE: N:bpN:p4:norm | blueprint-P/parts/p2-averaging.tex#bpP:p2:s-osc#data@L167-L167 | norm of N with the sup over (I,p,q)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p1p2
REVIEWER: sol-review-P-d
LEAN_STATUS: PROVED
LEAN_REF: oscPack, oscUnpack, oscFunction, oscParams, oscDom, oscBound, oscClass, oscGauge, s_osc_data (KAM/Planetary/Averaging/OscillatorSetting.lean)
LEAN_NOTE: audit P23-06 PASS WITH NOTES; flat-coordinate implementation of the oscillator setting data (bracket/field not separate defs)
NOTE: section data of Part 2 (prose L167-L169)

NODE: stepP:p1:hc-real-derivative
KIND: step
TITLE: Real derivative on the real slice of an arbitrary complex open set
STATEMENT_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:hol-chart@L73-L76
PROOF_SOURCE: blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:hol-chart@L76-L76
CONTRACT_ID: stepP:p1:hc-real-derivative
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c>0; V subset C^{2d} open; Psi:V->C^{2d} holomorphic, real at real points; D Psi(z)^T M_0 D Psi(z)=c M_0 (complex matrices) for z in V cap R^{2d}; O=V cap R^{2d}
SOURCE_QUANTIFIERS: each real z in V
SOURCE_CONCLUSION: D_R(Psi restricted to V cap R^{2d})(z) equals the restriction of D_C Psi(z), so the complex matrix identity restricts to the real chart identity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:holomorphic-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:holomorphic-analytic | blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:hol-chart@L76-L76 | part (b) supplies real analyticity on the real slice, but not the explicitly needed derivative identification
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-P-d
REVIEWER: sol-delta-P-d
LEAN_STATUS: PROVED
LEAN_REF: fderiv_real_slice (KAM/Planetary/Hamiltonian/HolChart.lean)
LEAN_NOTE: audit PP1-5 PASS WITH NOTES
NOTE: SOURCE_GAP: The source invokes K real-restriction for arbitrary open V. Its statement at blueprint/parts/p1-analysis.tex L1047-L1051 only treats a whole strip T_rho. K holomorphic-analytic(b), L296-L312, supplies real analyticity on arbitrary open sets, but does not state the derivative identification used here. No general-domain derivative bridge is supplied by an allowed external or an applicable imported statement; retain this obligation without strengthening the hypotheses.
