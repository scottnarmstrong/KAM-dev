# GLOBAL review of root b:4#HH (sonnet-global-B-hh)

VERDICT: ACCEPT WITH FINDINGS

Scope read: program-b-plan L66-206, L296-345, L525-562; FREEZE-PROPOSAL-HH.md; DEPGRAPH.md; DEPGRAPH_COVERAGE.md;
the frozen statement. LEAN_* fields and all other Lean/status files ignored. Nothing edited except this report.

## What survived refutation (checked, no defect)
* Root identity: FROZEN_FILE `KAM/Frozen/EffectiveStability/HenonHeilesConfinement.lean`, FROZEN_DECL
  `KAM.EffectiveStability.henonHeiles_confinement` (namespace L25, theorem L32), anchor/contract
  `effectiveStability.d73.henonHeiles_confinement` v1 (`.v1` suffix consistent). The statement in the frozen file
  L32-48 is **byte-identical** to FREEZE-PROPOSAL-HH L20-36 (diffed, modulo the `:=` and the proof). The manifest
  entry and ABI hash were not opened (out of scope); only their internal consistency was checked.
* Model: frozen H (L36-38) = I0 - (sqrt2/2) I1 + q0^2 q1 - q1^3/3 with q=w.1, p=w.2, = plan (HH) L533-536 after
  index shift 1,2 -> 0,1. Precedence `sqrt 2/2 * (I1)` is (sqrt2/2)*I1. The inlined H appears twice (existence
  L35-38, uniqueness L40-43) and the two copies are textually identical.
* Box/time/bounds vs plan L539-542: `<= (1/12500)^2` L33; `10^10 < T1` and bounds for `|t| <= 10^10` L45; `< 101/10^10`
  and `<= 12/10^10` L46-48; all real-typed by unification. Existence on `Ioo(-T1,T1)` with T1>10^10 contains
  `Icc(-T,T)` as plan L91-96 requires; uniqueness (OrdConnected I, 0 in I, y 0 = z0, equal on I inter Ioo) matches
  plan L94-98 and avoids `exists!`; V = whole space so "stays in the regular domain" is vacuous.
* Quantifier order: z0, hz0, then exists T1, exists z (z may depend on z0, as B1-E); uniqueness quantifies
  over I, y after z. Correct.
* Coordinates: X_H = (d_p H, -d_q H) with q first slot is plan L80 with (phi,J)->(q,p); `oscillatorAction z.2 z.1 j`
  is consistent with the B1-E convention in CONVENTIONS (DEPGRAPH L6); the form is symmetric in (q,p) so order is harmless.
* Constant scope: every literal explicit (L652). Arithmetic of the source inequalities re-derived:
  (1/12500)^2 = 6.4e-9, +1e-10 = 6.5e-9 < a = (81e-6)^2 = 6.561e-9; a + eta T <= 7.561e-9 < b = 1e-8;
  a + eta T + d <= 7.661e-9 < 1.01e-8; 2d + eta T <= 1.2e-9 = 12/10^10. All hold with equality only in the last,
  which matches the non-strict frozen bound.
* Combination of d: physical drift = |I(Psi w(t)) - I(w(t))| + |I(w(t)) - I(w0)| + |I(w0) - I(Psi w0)| <= d + eta|t| + d
  (forward displacement twice, via z0 = Psi w0). Consistent with physical-bounds L622.
* Node/edge accounting: 23 nodes, 56 EDGE lines (grep-counted), 6 leaves, queue of 5 PROPOSED nodes agree with the
  dashboard. HH edges cite lines that contain what they claim (L22-32 existence+uniqueness, L23-26 HasDerivAt,
  L21 hz0, L33-36 bounds). DEPS are conjunctive, no ROUTES, so there is no OR structure to misread.
* b:4#initial-inclusion NOTE (OD-B18 Lean route: coordinate-tail disc estimate instead of an action displacement d):
  **accepted as a Lean-route deviation, not a source-topology change.** The source object (inverse-chart action
  displacement <= d on the physical box) is kept as the node's statement; no node or edge must change for it.
  (But see F1: the source node itself is under-specified.)

## Findings

### F1 (HIGH) No node produces the chart point w0 with Psi(w0) = z0 (right inverse / surjectivity onto the physical box)
Evidence: B1-E (DEPGRAPH L505-507) starts from `w0` with `I_j(w0) <= a_j` and concludes about `z(0) = Psi(w0)`;
its chart hypothesis is only the *left* inverse `Psiinv o Psi = id` (L505, chart-transport NOTE L203 "no inverse
regularity or open image is needed ... left inverse"). The frozen HH root starts from an arbitrary *physical* z0
(frozen L33) and asserts `z 0 = z0` (L34). The plan flags exactly this obligation at L153-155: "prove
Q ⊆ Psi({a}) using the inverse chart. Defining an image region alone does not prove that it contains the requested
physical initial data" and requires a diffeomorphism onto an open image (L117-118), which B1-E's frozen premises
drop. `b:4#initial-inclusion` (L585-611) has SOURCE_CONCLUSION "chart action I_j(w0) <= ... < a_j" (L594) and
SOURCE_HYPOTHESES only "inverse-chart action displacement <= d" (L592); it never states `w0 := Psiinv z0`
satisfies `Psi w0 = z0`, and nothing else in the closure does. Without it B1-E cannot be applied at z0
and `z 0 = z0` (frozen L34) and uniqueness through z0 are unsupported at the graph level.
Fix: add a node (e.g. `b:4#physical-to-chart`) "for physical z0 with I<=sigma^2, w0 := Psiinv z0 lies in E_(b+eps)
with I_j(w0) <= a_j and Psi w0 = z0 (two-sided inverse on the physical box; inverse flows defined there)", DEPS
b:3.1#checker-soundness, b:4#certificate; make initial-inclusion depend on it and HH use it for z 0 = z0. Plan
L153-155 is its source.

### F2 (HIGH) Checker-soundness is a one-edge black box; the premise discharge of B1-E is not exposed, and its proof source is outside the corpus
Evidence: b:3.1#checker-soundness DEPS = b:2.3#B1-E only (L546) with EDGE "dynamics conclusion is B1-E applied in
the certified chart" (L549). Its PROOF_SOURCE is L335-340 (L535), which states "must prove the chart, residual and
continuation facts from the accepted finite data" (plan L335-337) and "replayed through ... proved analytic lemmas"
(L339) but contains no proof. The proof content is plan §3.2 "Exact transformations and tails" (L341 ff.), §3.3
(L408 ff.) and §3.4: these are **not in CORPUS** (corpus stops at L340, DEPGRAPH L5; no coverage item mentions
L341+). Every premise of B1-E at this consumer (L505) lacks a discharging node: (a) H C^2 on open V with V⊇Psi(E_(b+eps));
(b) Psi C^2 on E_(b+eps) (composition of Lie flows, flow existence on the nested domains, plan L318);
(c) DPsi symplectic (time-one Hamiltonian flows, plan L318); (d) Psiinv o Psi = id on E_(b+eps) (inverse flow
domains, plan L317); (e) eps>0 margin and N, R definitions; (f) `H o Psi = N o I + R` on E_(b+eps) (Lie/Taylor
identities with discarded tails, plan L318-319); (g) R differentiable with the Cauchy/derivative-loss bound giving
`|{I_j,R}| <= eta_j` on closed E_b (plan L319, "derivative-loss margin"). Cauchy estimates and analytic-flow
well-definedness are external inputs of the argument and are not recorded as ext nodes; EXTERNAL_POLICY (L8)
lists only Picard-Lindelof and continuation. "Explicit source gaps: 0" (dashboard) is therefore wrong for this closure.
Fix: either (i) extend CORPUS to §3.2-3.3 and add step nodes for (a)-(g) with edges into B1-E at the matching
premises plus ext nodes for Cauchy estimates/analytic flow existence, or (ii) declare checker-soundness an explicit
SOURCE GAP / assumption-boundary leaf with PROOF_SOURCE `-`, so the closure does not claim a proved path.
The edge to B1-E should name each premise it feeds.

### F3 (MEDIUM) Missing node: identification of the checker polynomial with the displayed H (and exact sqrt 2 arithmetic)
Evidence: plan L307-309 "The model expression is interpreted exactly. A polynomial that approximates a different H is a
different model"; the certificate is an exact finite expression over the supported coefficient field (Q(sqrt2) for HH:
coefficient `-sqrt2/2` frozen L36-37). The frozen statement inlines a `fun w => ...` over `Real` (L35-38 twice) and
`Real.sqrt 2`. No node states: the evaluated polynomial of c.H equals that function pointwise; it is C^2 with V = univ
(B1-E premise (a)); the embedding Q(sqrt2) -> R sends sqrt2 to `Real.sqrt 2`, ordering/sign decisions on Q(sqrt2)
elements are sound, and the divisor non-vanishing for omega=(1,-sqrt2/2) (plan §3.3) holds. b:4#HH's only link is
`b:defs#hamiltonianVectorField` (L664), which says nothing about H.
Fix: add `b:4#model-identification` (HH expression <-> displayed function, C^2, V = univ, sqrt2 embedding), DEPS none
beyond the model text (plan L533-536), consumed by b:4#certificate, b:3.1#checker-soundness's instantiation and
b:4#HH (the frozen H appears in both existence and uniqueness clauses).

### F4 (MEDIUM) b:4#initial-inclusion does not depend on checker soundness; certificate -> soundness edge has the wrong direction
Evidence: initial-inclusion DEPS = certificate, oscillatorAction (L600). Its input "inverse-chart action displacement
<= d" is a property of the *actual* chart; b:4#certificate's SOURCE_CONCLUSION is only `checkNormalForm(HH,c) = true`
(L567), a Boolean. Turning acceptance into the inequality on the real chart is soundness; physical-bounds correctly lists
both (L628) but initial-inclusion does not. Conversely b:4#certificate DEPS soundness (L573, EDGE L576): a certificate
being accepted does not need the soundness theorem (soundness consumes it), so this edge hides that the certificate is a
finite computation leaf. Fix: initial-inclusion (and the new F1 node) depend on checker-soundness; drop the
certificate -> soundness edge (or retype it as a SOURCE note); make b:4#certificate a declared computation/leaf with the
model-identification dependency.

### F5 (MEDIUM) b:4#certificate has no source proof: the literals are the plan's *target*, and the computation's provenance is out of corpus
Evidence: certificate PROOF_SOURCE = plan L545-553 (L562 of DEPGRAPH) is the list of target values, introduced "A
sufficient finite certificate **would** establish" (plan L545) and "This is a proposed acceptance target, not a theorem
proved here" (plan L543). The plan's own account of the computation starts at L561 ("The source's short computation
uses explicit degree four ... stops at normalization step three") and is outside CORPUS (L559 cutoff, DEPGRAPH L5);
the actual certificate/E1 report is not in the corpus either. The truth of `eta <= 1e-19, d <= 1e-10` is therefore a
finite computation whose only source in the closure is a statement of what it should output.
Fix: record it as KIND computation/external leaf ("replayed finite certificate, producer untrusted", plan L338-340),
or add a source gap; extend CORPUS to L561 ff. for provenance (CL20 numbers) and say they are provenance only.

### F6 (LOW-MEDIUM) "Required domains" of forward/inverse displacement are unspecified, and are different at the two consumers
Evidence: certificate SOURCE_CONCLUSION (L567) and plan L553 say "on their required domains". Consumers need:
inverse displacement on the physical box {I_j <= sigma^2 (+ margin)} (initial-inclusion); forward displacement on all
chart points in closed E_b (I_j <= b_j) since w(t) only satisfies I_j <= a_j + eta T < b_j (physical-bounds).
If the forward bound were certified only on {I <= a} the 2d + eta T claim would fail. Fix: state the two domains in
the certificate node's SOURCE_CONCLUSION and the consumer hypotheses.

### F7 (LOW) Coverage manifest is stale for the new closure
Evidence: DEPGRAPH_COVERAGE L34-41 and L88-95 keep `b:2.2#transfer`/`b:2.3#transfer` as EXCLUDED with reason "internal corollary
... outside the root closure". The HH physical bound `|I(z t) - I(z0)| <= 2d + eta T` (physical-bounds L622) is exactly
the B1-transfer formula (plan L147-150, L201 "same transfer formula with L I") but physical-bounds' PROOF_SOURCE is
only plan L556-557 (inequalities), so the derivation has no source edge. Also plan L525-528 and L560 ff. are not
inventoried. Fix: update the EXCLUDED reasons (the transfer corollary is now used) and cite L147-150/L201 as
physical-bounds PROOF_SOURCE or add a transfer node.

### F8 (LOW) Edge source for oscillatorAction under-cites HH
HH EDGE `b:defs#oscillatorAction` cites only L21 "premise and conclusion" (DEPGRAPH L665); the conclusion uses are L34-36
of the proposal (frozen L46-48). Fix: cite L21 and L33-36.

## Cannot-refute list (for the record)
Uniqueness quantifier strength, time sign/units (plan L543 "HH model time units"), strictness of the <101/10^10 bound,
the T1 > T needed by B1-E (L507), and the AND-structure (no ROUTES) found no defect. Closure counts agree with the generated
dashboard.

## Recommendation
ACCEPT WITH FINDINGS: the root, statement and literal bookkeeping are sound. F1 and F2 must be repaired or explicitly
declared as gaps before b:4#HH can be called REVIEWED; F3-F5 should be repaired in the same amendment.
