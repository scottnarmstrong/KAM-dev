# P14 Lean design: AMD confinement, exponential safety, and the secular box

Design draft, 2026-10-28, branch `inp-design-p14`. No proof closure, statement approval, or freeze is claimed.
The design follows `DESIGN-P14.md` and the extended `DESIGN-COMMON.md`, including the global graph review.
Format model: the complete `PART145-LEAN-DESIGN.md` and its two audits; their proof-status distinctions apply here.

## Decisions

1. Use the frozen definitions literally. The four library assemblies have exactly the four frozen types;
   separate quarantined provider wrappers use the corresponding camelCase exports. No provider imports another provider.
2. Keep the deterministic helper independent of Nekhoroshev. `StoppedActionBound` is a premise only of `amd`;
   `expsafe` must derive it from the N theorem at both signs. It cannot assume the desired whole-horizon conclusion.
3. Build general-n chart identities componentwise from `poincare_elements`, `planetBlock`, and `poincareProd`.
   `keplerFunctions_poincareProd` in the delivered Kepler signatures has `Fin 2` binders and is not a general-n supplier.
4. Give the inherited source gaps explicit work: `chart_perturbation_analytic` for pc-share's analytic regularity,
   and `local_complex_restriction` for ho-hol's invalid use of a strip-only restriction lemma on a local domain.
   The real-analytic compact-tube route does not need the near-circular complex chart; it proves its own `tube`.
5. The secular flow is reduced at constant fast actions. Continue the slow solution on the compact AMD sphere,
   then recover fast angles by quadrature. Do not claim compactness of a set with unrestricted real angles.
6. `sb_unique` drops only the competitor's regularity premise: agreement is relatively closed by continuity,
   relatively open by local uniqueness inside S, hence global on the connected time interval. The frozen wrapper
   retains its exact regularity premise. This is a strictly stronger library helper.
7. The draft imports only definitions and existing ordinary modules. N-PARTIAL-CONVEX remains a dependency to be
   released as a sealed anchor or ordinary library theorem, never a new assumption on `expsafe`.

## Revision 2

Reconciles every finding of `DESIGN-P14-design-audit-1.md`; these are design repairs, not proof receipts.
No frozen telescope or definition changes. Appendix A and the untracked signatures are synchronized.

| Finding | Resolution and assigned proof work |
|---|---|
| F1 (major) | `h_data` now constrains g,v to attained finite minima and M to the exact source sum; these characterize constants independently of rho,e,A. It exports the real-coordinate lower margin. E4 proves existence/uniqueness of the minima and the negation bridges for -h. |
| F2 (medium) | `elements` and `eccentricity_deficit` require only the selected planet's four scalar hypotheses. A1 exports all elementary clauses (a)–(f); global consumers pass `hz i`. The old D1 premise strengthening is removed. |
| F3 (medium) | `real_domain` now exports distance/2 pair separation for every i≠j as well as radial separation and eccentricity. E3 proves both index orders using symmetry. `original_cylinder_subset` retains the last source inclusion. |
| F4 (low) | `uniform_data` returns delta≤pi jointly with UniformData. E8 chooses or shrinks delta before constructing the bounds; later consumers project the first conjunct. |
| F5 (medium) | Correct FTC supplier to `intervalIntegral.integral_hasDerivAt_right`. Add exact wrappers `angle_quadrature`, `interval_constancy`, `complex_division`; replace the unusable supplier-table entries and assign them to S9,A5,E5 respectively. |
| N1 (medium risk) | E5/E6 and S4 are feasibility gates: prove and check them at default resources before releasing dependent E7/E9–E12 or S5–S12 waves. Split focused modules before the cap; admitted signature elaboration does not pass these gates. |
| N2 (medium availability) | E11 is explicitly held until an ordinary N root proof export or independently audited sealed anchor with the exact frozen type is available. No provider or draft-anchor import may bypass this release gate. |

F5 executable routes: `angle_quadrature` uses continuous omega to supply interval integrability,
strong measurability at the endpoint filter, and endpoint continuity to the FTC supplier. Its output is
the two-sided derivative, including at t=0. `interval_constancy` converts OrdConnected to convexity and
uses `Convex.is_const_of_fderivWithin_eq_zero`; the HasDerivAt premises give differentiability on J and
zero fderivWithin at every point of J: where UniqueDiffWithinAt holds, restrict HasDerivAt and use
its derivative-within identity; otherwise use `fderivWithin_zero_of_not_uniqueDiffWithinAt`
(scalar-domain f). This handles singleton/empty J and endpoints without an added premise.
`complex_division` uses `DifferentiableOn.inv` on the multivariable complex domain, then
`DifferentiableOn.mul`, rewriting division as multiplication by the inverse. No scalar-domain
`DifferentiableOn.div` or whole-line constancy theorem is used.

The E4 exported margin and exact constants, E3 quantitative pair bound, E8 delta upper bound, and A1
local premises are part of the public contracts below, not prose-only promises. No new source erratum is
asserted; F1–F5 correct this design's transcription or library interfaces. Prior blueprint gaps remain.

## Carriers and standing structures

| Object | Exact carrier or definition | Guard |
|---|---|---|
| Physical phase | frozen `Phase (n * 2)` | positions first, momenta second |
| Chart phase | frozen `Phase (n + n)` | `((lambda,xi),(Lambda,eta))`, fast block first |
| Complex phase | `(Fin (n+n) → ℂ) × (Fin (n+n) → ℂ)` | frozen `KAM.Nekhoroshev.complexifyPhase` |
| Body indexing | frozen `bodyVector`, `finProdFinEquiv` | no separate vector representation |
| Euclidean physical length | frozen `planeLength` | Mathlib's Pi norm remains the max norm |
| Outer/inner/collar/compact regions | `amdOuter`, `amdInner`, `amdCollar`, `amdCompact` | wrappers around frozen LowAMD and explicit inequalities |
| Analytic enlargement | `EnlargedData B kappa e A` | only E1–E3 geometric source inequalities; no analytic/confinement conclusions as fields |
| Fast boxes/slow ball | `fastBox B kappa`, `slowBall n A` | open max-norm action box; quadratic slow ball |
| Secular region | `sb_sdef saturn` | exactly the strict S inequalities of p14b L179–183 |
| Rotation | `secularRotation` | existing `KAM.Kepler.rot`; preserves fast angles/actions |
| Reduced secular field | `reducedSecularH m mu I : Phase 2 → ℝ` | same frozen integral, affine insertion with lambda=0 |

All aliases unfold to frozen objects or explicit new sets. `chartAMD` is an auxiliary n-planet quadratic sum;
its bridge to `physicalAMD` is proved by `sec_domain_chart_facts`. It does not replace frozen `secularAMD` for n=2.
Every division/square root in element identities is under the selected planet's scalar ellipticity premises,
or under positive fast action and Gamma < Lambda. Every secular integral used analytically is proved integrable; total Bochner-integral values
outside the safe domain are never a substitute for integrability.

## Node to declaration table

The assigned checkout has packet sources but no assembled `docs/graph/P/DEPGRAPH.md`.
This inventory uses `/root/code/KAM-inp/docs/graph/P/DEPGRAPH.md`, selecting **every** record whose
`STATEMENT_SOURCE` is p14a or p14b: 182 records, including definitions, external facts and proof steps.
IDs are stable. `a` means `blueprint-P/parts/p14a-amd-expsafe.tex`; `b` means `blueprint-P/parts/p14b-secular-box.tex`.
Each locator below retains its exact graph label and line range. Statement and proof locations are separate columns.
All new declarations are in `KAM.Planetary`; module paths are prefixed by `KAM/Planetary/` and suffixed `.lean`.
A proof-step row denotes an internal obligation of the named parent declaration, not an extra theorem assuming
that parent's conclusion. Such rows deliberately have no separate Lean declaration.

| Graph node | Declaration / internal obligation | Module or existing supplier | Statement | Proof |
|---|---|---|---|---|
| `bpP:p14:x-planar` | `existing facts / x-planar` | KAM.Kepler.abs_planeDot_le, planeSq_mul_planeSq | `a#bpP:p14:x-planar@L28-L28` | `—` |
| `bpP:p14:x-top` | `existing facts / x-top` | IsCompact.exists_cthickening_subset_open; Metric.isCompact_iff_isClosed_bounded | `a#bpP:p14:x-top@L29-L29` | `—` |
| `bpP:p14:x-calc` | `existing facts / x-calc` | HasDerivAt.comp; interval_constancy (AMD/AngularMomentum) | `a#bpP:p14:x-calc@L30-L30` | `—` |
| `bpP:p14:x-cx` | `existing facts / x-cx` | local_analytic_complexification (new obligation) | `a#bpP:p14:x-cx@L31-L31` | `—` |
| `bpP:p14:x-id` | `existing facts / x-id` | real_trace_identity (new obligation) | `a#bpP:p14:x-id@L32-L32` | `—` |
| `bpP:p14:x-hol` | `existing facts / x-hol` | complex_division (Exponential/LocalComplexification); DifferentiableOn.mul | `a#bpP:p14:x-hol@L33-L33` | `—` |
| `bpP:p14:elements` | `elements` | AMD/Elements | `a#bpP:p14:elements@L42-L53` | `a#bpP:p14:elements@L54-L64` |
| `stepP:p14:el-a` | `internal elements / el-a` | AMD/Elements | `a#stepP:p14:el-a@L55-L55` | `a#stepP:p14:el-a@L55-L55` |
| `stepP:p14:el-b` | `internal elements / el-b` | AMD/Elements | `a#stepP:p14:el-b@L56-L59` | `a#stepP:p14:el-b@L56-L59` |
| `stepP:p14:el-c` | `internal elements / el-c` | AMD/Elements | `a#stepP:p14:el-c@L60-L60` | `a#stepP:p14:el-c@L60-L60` |
| `stepP:p14:el-d` | `internal elements / el-d` | AMD/Elements | `a#stepP:p14:el-d@L61-L61` | `a#stepP:p14:el-d@L61-L61` |
| `stepP:p14:el-e` | `internal elements / el-e` | AMD/Elements | `a#stepP:p14:el-e@L62-L62` | `a#stepP:p14:el-e@L62-L62` |
| `stepP:p14:el-f` | `internal elements / el-f` | AMD/Elements | `a#stepP:p14:el-f@L63-L63` | `a#stepP:p14:el-f@L63-L63` |
| `bpP:p14:ecc-bound` | `ecc_bound` | AMD/Elements | `a#bpP:p14:ecc-bound@L66-L69` | `a#bpP:p14:ecc-bound@L70-L73` |
| `stepP:p14:eb-sum` | `internal ecc_bound / eb-sum` | AMD/Elements | `a#stepP:p14:eb-sum@L71-L71` | `a#stepP:p14:eb-sum@L71-L71` |
| `stepP:p14:eb-ecc` | `internal ecc_bound / eb-ecc` | AMD/Elements | `a#stepP:p14:eb-ecc@L72-L72` | `a#stepP:p14:eb-ecc@L72-L72` |
| `bpP:p14:geometry` | `geometry` | AMD/Geometry | `a#bpP:p14:geometry@L75-L84` | `a#bpP:p14:geometry@L85-L91` |
| `stepP:p14:geo-a` | `internal geometry / geo-a` | AMD/Geometry | `a#stepP:p14:geo-a@L86-L86` | `a#stepP:p14:geo-a@L86-L86` |
| `stepP:p14:geo-b` | `internal geometry / geo-b` | AMD/Geometry | `a#stepP:p14:geo-b@L87-L87` | `a#stepP:p14:geo-b@L87-L87` |
| `stepP:p14:geo-c` | `internal geometry / geo-c` | AMD/Geometry | `a#stepP:p14:geo-c@L88-L88` | `a#stepP:p14:geo-c@L88-L88` |
| `stepP:p14:geo-d` | `internal geometry / geo-d` | AMD/Geometry | `a#stepP:p14:geo-d@L89-L89` | `a#stepP:p14:geo-d@L89-L89` |
| `stepP:p14:geo-k` | `internal geometry / geo-k` | AMD/Geometry | `a#stepP:p14:geo-k@L90-L90` | `a#stepP:p14:geo-k@L90-L90` |
| `bpP:p14:closure` | `closure` | AMD/Closure | `a#bpP:p14:closure@L93-L99` | `a#bpP:p14:closure@L100-L104` |
| `stepP:p14:cl-a` | `internal closure / cl-a` | AMD/Closure | `a#stepP:p14:cl-a@L101-L101` | `a#stepP:p14:cl-a@L101-L101` |
| `stepP:p14:cl-b` | `internal closure / cl-b` | AMD/Closure | `a#stepP:p14:cl-b@L102-L102` | `a#stepP:p14:cl-b@L102-L102` |
| `stepP:p14:cl-c` | `internal closure / cl-c` | AMD/Closure | `a#stepP:p14:cl-c@L103-L103` | `a#stepP:p14:cl-c@L103-L103` |
| `bpP:p14:moving-ode` | `moving_ode` | AMD/MovingODE | `a#bpP:p14:moving-ode@L108-L112` | `a#bpP:p14:moving-ode@L113-L116` |
| `stepP:p14:mo-reg` | `internal moving_ode / mo-reg` | AMD/MovingODE | `a#stepP:p14:mo-reg@L114-L114` | `a#stepP:p14:mo-reg@L114-L114` |
| `stepP:p14:mo-eq` | `internal moving_ode / mo-eq` | AMD/MovingODE | `a#stepP:p14:mo-eq@L115-L115` | `a#stepP:p14:mo-eq@L115-L115` |
| `bpP:p14:ang-mom` | `ang_mom` | AMD/AngularMomentum | `a#bpP:p14:ang-mom@L118-L120` | `a#bpP:p14:ang-mom@L121-L125` |
| `stepP:p14:am-eq` | `internal ang_mom / am-eq` | AMD/AngularMomentum | `a#stepP:p14:am-eq@L122-L122` | `a#stepP:p14:am-eq@L122-L122` |
| `stepP:p14:am-der` | `internal ang_mom / am-der` | AMD/AngularMomentum | `a#stepP:p14:am-der@L123-L123` | `a#stepP:p14:am-der@L123-L123` |
| `stepP:p14:am-const` | `internal ang_mom / am-const` | AMD/AngularMomentum | `a#stepP:p14:am-const@L124-L124` | `a#stepP:p14:am-const@L124-L124` |
| `bpP:p14:amd` | `amd` | AMD/Confinement | `a#bpP:p14:amd@L129-L133` | `a#bpP:p14:amd@L134-L151` |
| `stepP:p14:amd-max` | `internal amd / amd-max` | AMD/Confinement | `a#stepP:p14:amd-max@L136-L136` | `a#stepP:p14:amd-max@L136-L136` |
| `stepP:p14:amd-fwd` | `internal amd / amd-fwd` | AMD/Confinement | `a#stepP:p14:amd-fwd@L137-L138` | `a#stepP:p14:amd-fwd@L137-L138` |
| `stepP:p14:amd-margin` | `internal amd / amd-margin` | AMD/Confinement | `a#stepP:p14:amd-margin@L139-L143` | `a#stepP:p14:amd-margin@L139-L143` |
| `stepP:p14:amd-close` | `internal amd / amd-close` | AMD/Confinement | `a#stepP:p14:amd-close@L144-L144` | `a#stepP:p14:amd-close@L144-L144` |
| `stepP:p14:amd-bwd` | `internal amd / amd-bwd` | AMD/Confinement | `a#stepP:p14:amd-bwd@L145-L145` | `a#stepP:p14:amd-bwd@L145-L145` |
| `stepP:p14:amd-cont` | `internal amd / amd-cont` | AMD/Confinement | `a#stepP:p14:amd-cont@L146-L146` | `a#stepP:p14:amd-cont@L146-L146` |
| `stepP:p14:amd-a` | `internal amd / amd-a` | AMD/Confinement | `a#stepP:p14:amd-a@L147-L147` | `a#stepP:p14:amd-a@L147-L147` |
| `stepP:p14:amd-b` | `internal amd / amd-b` | AMD/Confinement | `a#stepP:p14:amd-b@L148-L148` | `a#stepP:p14:amd-b@L148-L148` |
| `stepP:p14:amd-c` | `internal amd / amd-c` | AMD/Confinement | `a#stepP:p14:amd-c@L149-L149` | `a#stepP:p14:amd-c@L149-L149` |
| `stepP:p14:amd-d` | `internal amd / amd-d` | AMD/Confinement | `a#stepP:p14:amd-d@L150-L150` | `a#stepP:p14:amd-d@L150-L150` |
| `bpP:p14:conv#data` | `amdOuter, amdInner, amdCollar, amdCompact` | AMD/Setting | `a#bpP:p14:conv#data@L5-L24` | `—` |
| `bpP:p14:enlarge` | `enlarge` | Exponential/Enlargement | `a#bpP:p14:enlarge@L170-L178` | `a#bpP:p14:enlarge@L179-L182` |
| `stepP:p14:en-lim` | `internal enlarge / en-lim` | Exponential/Enlargement | `a#stepP:p14:en-lim@L180-L180` | `a#stepP:p14:en-lim@L180-L180` |
| `stepP:p14:en-choice` | `internal enlarge / en-choice` | Exponential/Enlargement | `a#stepP:p14:en-choice@L181-L181` | `a#stepP:p14:en-choice@L181-L181` |
| `bpP:p14:real-domain` | `real_domain` | Exponential/RealDomain | `a#bpP:p14:real-domain@L184-L187` | `a#bpP:p14:real-domain@L188-L193` |
| `stepP:p14:rd-o` | `internal real_domain / rd-o` | Exponential/RealDomain | `a#stepP:p14:rd-o@L189-L189` | `a#stepP:p14:rd-o@L189-L189` |
| `stepP:p14:rd-ecc` | `internal real_domain / rd-ecc` | Exponential/RealDomain | `a#stepP:p14:rd-ecc@L190-L190` | `a#stepP:p14:rd-ecc@L190-L190` |
| `stepP:p14:rd-sep` | `internal real_domain / rd-sep` | Exponential/RealDomain | `a#stepP:p14:rd-sep@L191-L191` | `a#stepP:p14:rd-sep@L191-L191` |
| `stepP:p14:rd-last` | `internal real_domain / rd-last` | Exponential/RealDomain | `a#stepP:p14:rd-last@L192-L192` | `a#stepP:p14:rd-last@L192-L192` |
| `bpP:p14:h-data` | `h_data` | Exponential/KeplerData | `a#bpP:p14:h-data@L195-L200` | `a#bpP:p14:h-data@L201-L206` |
| `stepP:p14:hd-i` | `internal h_data / hd-i` | Exponential/KeplerData | `a#stepP:p14:hd-i@L202-L202` | `a#stepP:p14:hd-i@L202-L202` |
| `stepP:p14:hd-ii` | `internal h_data / hd-ii` | Exponential/KeplerData | `a#stepP:p14:hd-ii@L203-L203` | `a#stepP:p14:hd-ii@L203-L203` |
| `stepP:p14:hd-iv` | `internal h_data / hd-iv` | Exponential/KeplerData | `a#stepP:p14:hd-iv@L204-L204` | `a#stepP:p14:hd-iv@L204-L204` |
| `stepP:p14:hd-v` | `internal h_data / hd-v` | Exponential/KeplerData | `a#stepP:p14:hd-v@L205-L205` | `a#stepP:p14:hd-v@L205-L205` |
| `bpP:p14:tube` | `tube` | Exponential/ComplexTube | `a#bpP:p14:tube@L210-L212` | `a#bpP:p14:tube@L213-L218` |
| `stepP:p14:tb-local` | `internal tube / tb-local` | Exponential/ComplexTube | `a#stepP:p14:tb-local@L214-L214` | `a#stepP:p14:tb-local@L214-L214` |
| `stepP:p14:tb-leb` | `internal tube / tb-leb` | Exponential/ComplexTube | `a#stepP:p14:tb-leb@L215-L215` | `a#stepP:p14:tb-leb@L215-L215` |
| `stepP:p14:tb-glue` | `internal tube / tb-glue` | Exponential/ComplexTube | `a#stepP:p14:tb-glue@L216-L216` | `a#stepP:p14:tb-glue@L216-L216` |
| `stepP:p14:tb-per` | `internal tube / tb-per` | Exponential/ComplexTube | `a#stepP:p14:tb-per@L217-L217` | `a#stepP:p14:tb-per@L217-L217` |
| `bpP:p14:perturbation` | `perturbation` | Exponential/Perturbation | `a#bpP:p14:perturbation@L220-L226` | `a#bpP:p14:perturbation@L227-L235` |
| `stepP:p14:pt-input` | `internal perturbation / pt-input` | Exponential/Perturbation | `a#stepP:p14:pt-input@L228-L228` | `a#stepP:p14:pt-input@L228-L228` |
| `stepP:p14:pt-rho` | `internal perturbation / pt-rho` | Exponential/Perturbation | `a#stepP:p14:pt-rho@L229-L229` | `a#stepP:p14:pt-rho@L229-L229` |
| `stepP:p14:pt-def` | `internal perturbation / pt-def` | Exponential/Perturbation | `a#stepP:p14:pt-def@L230-L230` | `a#stepP:p14:pt-def@L230-L230` |
| `stepP:p14:pt-p12` | `internal perturbation / pt-p12` | Exponential/Perturbation | `a#stepP:p14:pt-p12@L231-L231` | `a#stepP:p14:pt-p12@L231-L231` |
| `stepP:p14:pt-p3` | `internal perturbation / pt-p3` | Exponential/Perturbation | `a#stepP:p14:pt-p3@L232-L232` | `a#stepP:p14:pt-p3@L232-L232` |
| `stepP:p14:pt-p4` | `internal perturbation / pt-p4` | Exponential/Perturbation | `a#stepP:p14:pt-p4@L233-L233` | `a#stepP:p14:pt-p4@L233-L233` |
| `stepP:p14:pt-neg` | `internal perturbation / pt-neg` | Exponential/Perturbation | `a#stepP:p14:pt-neg@L234-L234` | `a#stepP:p14:pt-neg@L234-L234` |
| `bpP:p14:uniform-data` | `uniform_data` | Exponential/UniformData | `a#bpP:p14:uniform-data@L239-L241` | `a#bpP:p14:uniform-data@L242-L245` |
| `stepP:p14:ud-cell` | `internal uniform_data / ud-cell` | Exponential/UniformData | `a#stepP:p14:ud-cell@L243-L243` | `a#stepP:p14:ud-cell@L243-L243` |
| `stepP:p14:ud-transl` | `internal uniform_data / ud-transl` | Exponential/UniformData | `a#stepP:p14:ud-transl@L244-L244` | `a#stepP:p14:ud-transl@L244-L244` |
| `bpP:p14:lift` | `lift` | Exponential/Lift | `a#bpP:p14:lift@L247-L249` | `a#bpP:p14:lift@L250-L256` |
| `stepP:p14:li-init` | `internal lift / li-init` | Exponential/Lift | `a#stepP:p14:li-init@L251-L251` | `a#stepP:p14:li-init@L251-L251` |
| `stepP:p14:li-max` | `internal lift / li-max` | Exponential/Lift | `a#stepP:p14:li-max@L252-L252` | `a#stepP:p14:li-max@L252-L252` |
| `stepP:p14:li-proj` | `internal lift / li-proj` | Exponential/Lift | `a#stepP:p14:li-proj@L253-L253` | `a#stepP:p14:li-proj@L253-L253` |
| `stepP:p14:li-cont` | `internal lift / li-cont` | Exponential/Lift | `a#stepP:p14:li-cont@L254-L254` | `a#stepP:p14:li-cont@L254-L254` |
| `stepP:p14:li-concl` | `internal lift / li-concl` | Exponential/Lift | `a#stepP:p14:li-concl@L255-L255` | `a#stepP:p14:li-concl@L255-L255` |
| `bpP:p14:hnu` | `hnu` | Exponential/Hamiltonian | `a#bpP:p14:hnu@L264-L266` | `a#bpP:p14:hnu@L267-L270` |
| `stepP:p14:hn-eq` | `internal hnu / hn-eq` | Exponential/Hamiltonian | `a#stepP:p14:hn-eq@L268-L268` | `a#stepP:p14:hn-eq@L268-L268` |
| `stepP:p14:hn-field` | `internal hnu / hn-field` | Exponential/Hamiltonian | `a#stepP:p14:hn-field@L269-L269` | `a#stepP:p14:hn-field@L269-L269` |
| `bpP:p14:stopped` | `stopped` | Exponential/Stopped | `a#bpP:p14:stopped@L272-L276` | `a#bpP:p14:stopped@L277-L287` |
| `stepP:p14:st-thr` | `internal stopped / st-thr` | Exponential/Stopped | `a#stepP:p14:st-thr@L278-L280` | `a#stepP:p14:st-thr@L278-L280` |
| `stepP:p14:st-seg` | `internal stopped / st-seg` | Exponential/Stopped | `a#stepP:p14:st-seg@L281-L281` | `a#stepP:p14:st-seg@L281-L281` |
| `stepP:p14:st-sol` | `internal stopped / st-sol` | Exponential/Stopped | `a#stepP:p14:st-sol@L282-L282` | `a#stepP:p14:st-sol@L282-L282` |
| `stepP:p14:st-core` | `internal stopped / st-core` | Exponential/Stopped | `a#stepP:p14:st-core@L283-L283` | `a#stepP:p14:st-core@L283-L283` |
| `stepP:p14:st-fwd` | `internal stopped / st-fwd` | Exponential/Stopped | `a#stepP:p14:st-fwd@L284-L284` | `a#stepP:p14:st-fwd@L284-L284` |
| `stepP:p14:st-bwd` | `internal stopped / st-bwd` | Exponential/Stopped | `a#stepP:p14:st-bwd@L285-L285` | `a#stepP:p14:st-bwd@L285-L285` |
| `stepP:p14:st-phys` | `internal stopped / st-phys` | Exponential/Stopped | `a#stepP:p14:st-phys@L286-L286` | `a#stepP:p14:st-phys@L286-L286` |
| `bpP:p14:expsafe` | `expsafe` | Exponential/Safety | `a#bpP:p14:expsafe@L295-L299` | `a#bpP:p14:expsafe@L300-L311` |
| `stepP:p14:es-const` | `internal expsafe / es-const` | Exponential/Safety | `a#stepP:p14:es-const@L301-L304` | `a#stepP:p14:es-const@L301-L304` |
| `stepP:p14:es-par` | `internal expsafe / es-par` | Exponential/Safety | `a#stepP:p14:es-par@L305-L305` | `a#stepP:p14:es-par@L305-L305` |
| `stepP:p14:es-stop` | `internal expsafe / es-stop` | Exponential/Safety | `a#stepP:p14:es-stop@L306-L306` | `a#stepP:p14:es-stop@L306-L306` |
| `stepP:p14:es-amd` | `internal expsafe / es-amd` | Exponential/Safety | `a#stepP:p14:es-amd@L307-L307` | `a#stepP:p14:es-amd@L307-L307` |
| `stepP:p14:es-axis` | `internal expsafe / es-axis` | Exponential/Safety | `a#stepP:p14:es-axis@L308-L309` | `a#stepP:p14:es-axis@L308-L309` |
| `stepP:p14:es-assemble` | `internal expsafe / es-assemble` | Exponential/Safety | `a#stepP:p14:es-assemble@L310-L310` | `a#stepP:p14:es-assemble@L310-L310` |
| `bpP:p14:sec-domain#data` | `chartSafe, chartAMD` | Exponential/Setting | `a#bpP:p14:sec-domain#data@L159-L162` | `—` |
| `bpP:p14:sec-domain#chart-facts` | `sec_domain_chart_facts` | Exponential/Dictionary | `a#bpP:p14:sec-domain#chart-facts@L162-L168` | `a#bpP:p14:sec-domain#chart-facts@L162-L168` |
| `bpP:p14:sec-stopped#data` | `planetaryKeplerC; degenerateHamiltonian` | Exponential/Hamiltonian | `a#bpP:p14:sec-stopped#data@L260-L262` | `—` |
| `bpP:p14:sb-x-alg` | `existing facts / sb-x-alg` | Real.sq_sqrt; KAM.Kepler.planeLength_rot, planeDot_rot, rot_quarterTurn | `b#bpP:p14:sb-x-alg@L36-L36` | `—` |
| `bpP:p14:sb-x-top` | `existing facts / sb-x-top` | Metric.isCompact_iff_isClosed_bounded; IsPreconnected | `b#bpP:p14:sb-x-top@L37-L37` | `—` |
| `bpP:p14:sb-x-int` | `existing facts / sb-x-int` | Function.Periodic.intervalIntegral_add_eq; intervalIntegral.integral_hasDerivAt | `b#bpP:p14:sb-x-int@L38-L38` | `—` |
| `bpP:p14:sb-x-calc` | `existing facts / sb-x-calc` | HasDerivAt.comp; hasDerivAt_pi | `b#bpP:p14:sb-x-calc@L40-L40` | `—` |
| `bpP:p14:sb-conv#secularGamma` | `secularGamma` | KAM/Frozen/Planetary/Defs/SecularGamma.lean (reuse) | `b#bpP:p14:sb-conv@L26-L26` | `—` |
| `bpP:p14:sb-conv#secularAMD` | `secularAMD` | KAM/Frozen/Planetary/Defs/SecularAMD.lean (reuse) | `b#bpP:p14:sb-conv@L26-L26` | `—` |
| `bpP:p14:sb-conv#secularRoot` | `secularRoot` | KAM/Frozen/Planetary/Defs/SecularRoot.lean (reuse) | `b#bpP:p14:sb-conv@L26-L26` | `—` |
| `bpP:p14:sb-conv#secularEccVector` | `secularEccVector` | KAM/Frozen/Planetary/Defs/SecularEccVector.lean (reuse) | `b#bpP:p14:sb-conv@L27-L27` | `—` |
| `bpP:p14:sb-conv#secularAxis` | `secularAxis` | KAM/Frozen/Planetary/Defs/SecularAxis.lean (reuse) | `b#bpP:p14:sb-conv@L27-L27` | `—` |
| `bpP:p14:sb-conv#orbitalUnit` | `orbitalUnit` | KAM/Frozen/Planetary/Defs/OrbitalUnit.lean (reuse) | `b#bpP:p14:sb-conv@L27-L27` | `—` |
| `bpP:p14:sb-conv#quarterTurn` | `quarterTurn` | KAM/Frozen/Planetary/Defs/QuarterTurn.lean (reuse) | `b#bpP:p14:sb-conv@L29-L29` | `—` |
| `bpP:p14:sb-defs#secularIntegrand` | `secularIntegrand` | KAM/Frozen/Planetary/Defs/SecularIntegrand.lean (reuse) | `b#bpP:p14:sb-defs@L47-L56` | `—` |
| `bpP:p14:sb-defs#exactSecularHamiltonian` | `exactSecularHamiltonian` | KAM/Frozen/Planetary/Defs/ExactSecularHamiltonian.lean (reuse) | `b#bpP:p14:sb-defs@L47-L56` | `—` |
| `bpP:p14:sb-defs#ellipsePhase` | `ellipsePhase` | KAM/Frozen/Planetary/Defs/EllipsePhase.lean (reuse) | `b#bpP:p14:sb-defs@L47-L56` | `—` |
| `bpP:p14:sb-defs#ellipsePosition` | `ellipsePosition` | KAM/Frozen/Planetary/Defs/EllipsePosition.lean (reuse) | `b#bpP:p14:sb-defs@L47-L56` | `—` |
| `bpP:p14:sb-defs#ellipseMomentum` | `ellipseMomentum` | KAM/Frozen/Planetary/Defs/EllipseMomentum.lean (reuse) | `b#bpP:p14:sb-defs@L47-L56` | `—` |
| `bpP:p14:sb-defs#longitudeJacobian` | `longitudeJacobian` | KAM/Frozen/Planetary/Defs/LongitudeJacobian.lean (reuse) | `b#bpP:p14:sb-defs@L47-L56` | `—` |
| `bpP:p14:sb-box#SecularInputBox` | `SecularInputBox` | KAM/Frozen/Planetary/Defs/SecularInputBox.lean (reuse) | `b#bpP:p14:sb-box@L58-L64` | `—` |
| `bpP:p14:sb-box#jupiterSaturnWeights` | `jupiterSaturnWeights` | KAM/Frozen/Planetary/Defs/JupiterSaturnWeights.lean (reuse) | `b#bpP:p14:sb-box@L58-L64` | `—` |
| `bpP:p14:sb-regular#SecularRegular` | `SecularRegular` | KAM/Frozen/Planetary/Defs/SecularRegular.lean (reuse) | `b#bpP:p14:sb-regular@L66-L70` | `—` |
| `bpP:p14:sb-safety` | `sb_safety` | SecularBox/Safety | `b#bpP:p14:sb-safety@L72-L86` | `b#bpP:p14:sb-safety@L280-L307` |
| `bpP:p14:sb-cited` | `sb_cited` | SecularBox/CitedMasses | `b#bpP:p14:sb-cited@L88-L92` | `b#bpP:p14:sb-cited@L309-L312` |
| `bpP:p14:sb-numerics` | `sb_numerics` | SecularBox/Numerics | `b#bpP:p14:sb-numerics@L103-L133` | `b#bpP:p14:sb-numerics@L134-L136` |
| `bpP:p14:sb-chart` | `sb_chart` | SecularBox/Chart | `b#bpP:p14:sb-chart@L144-L152` | `b#bpP:p14:sb-chart@L153-L162` |
| `stepP:p14:sb-ch-a` | `internal sb_chart / sb-ch-a` | SecularBox/Chart | `b#stepP:p14:sb-ch-a@L154-L155` | `b#stepP:p14:sb-ch-a@L154-L155` |
| `stepP:p14:sb-ch-b` | `internal sb_chart / sb-ch-b` | SecularBox/Chart | `b#stepP:p14:sb-ch-b@L156-L156` | `b#stepP:p14:sb-ch-b@L156-L156` |
| `stepP:p14:sb-ch-c` | `internal sb_chart / sb-ch-c` | SecularBox/Chart | `b#stepP:p14:sb-ch-c@L157-L160` | `b#stepP:p14:sb-ch-c@L157-L160` |
| `stepP:p14:sb-ch-d` | `internal sb_chart / sb-ch-d` | SecularBox/Chart | `b#stepP:p14:sb-ch-d@L161-L161` | `b#stepP:p14:sb-ch-d@L161-L161` |
| `bpP:p14:sb-cov` | `sb_cov` | SecularBox/Covariance | `b#bpP:p14:sb-cov@L164-L168` | `b#bpP:p14:sb-cov@L169-L173` |
| `stepP:p14:sb-cv-1` | `internal sb_cov / sb-cv-1` | SecularBox/Covariance | `b#stepP:p14:sb-cv-1@L170-L170` | `b#stepP:p14:sb-cv-1@L170-L170` |
| `stepP:p14:sb-cv-2` | `internal sb_cov / sb-cv-2` | SecularBox/Covariance | `b#stepP:p14:sb-cv-2@L171-L171` | `b#stepP:p14:sb-cv-2@L171-L171` |
| `stepP:p14:sb-cv-3` | `internal sb_cov / sb-cv-3` | SecularBox/Covariance | `b#stepP:p14:sb-cv-3@L172-L172` | `b#stepP:p14:sb-cv-3@L172-L172` |
| `bpP:p14:sb-smooth#data` | `sb_sdef parameters` | SecularBox/Region | `b#bpP:p14:sb-smooth#data@L177-L177` | `—` |
| `bpP:p14:sb-Sdef` | `sb_sdef` | SecularBox/Region | `b#bpP:p14:sb-Sdef@L179-L183` | `—` |
| `bpP:p14:sb-S` | `sb_s` | SecularBox/Region | `b#bpP:p14:sb-S@L185-L188` | `b#bpP:p14:sb-S@L189-L193` |
| `stepP:p14:sb-S-1` | `internal sb_s / sb-S-1` | SecularBox/Region | `b#stepP:p14:sb-S-1@L190-L190` | `b#stepP:p14:sb-S-1@L190-L190` |
| `stepP:p14:sb-S-2` | `internal sb_s / sb-S-2` | SecularBox/Region | `b#stepP:p14:sb-S-2@L191-L191` | `b#stepP:p14:sb-S-2@L191-L191` |
| `stepP:p14:sb-S-3` | `internal sb_s / sb-S-3` | SecularBox/Region | `b#stepP:p14:sb-S-3@L192-L192` | `b#stepP:p14:sb-S-3@L192-L192` |
| `bpP:p14:sb-smooth-prop` | `sb_smooth_prop` | SecularBox/Smooth | `b#bpP:p14:sb-smooth-prop@L195-L199` | `b#bpP:p14:sb-smooth-prop@L200-L205` |
| `stepP:p14:sb-sm-1` | `internal sb_smooth_prop / sb-sm-1` | SecularBox/Smooth | `b#stepP:p14:sb-sm-1@L201-L201` | `b#stepP:p14:sb-sm-1@L201-L201` |
| `stepP:p14:sb-sm-2` | `internal sb_smooth_prop / sb-sm-2` | SecularBox/Smooth | `b#stepP:p14:sb-sm-2@L202-L202` | `b#stepP:p14:sb-sm-2@L202-L202` |
| `stepP:p14:sb-sm-3` | `internal sb_smooth_prop / sb-sm-3` | SecularBox/Smooth | `b#stepP:p14:sb-sm-3@L203-L203` | `b#stepP:p14:sb-sm-3@L203-L203` |
| `stepP:p14:sb-sm-4` | `internal sb_smooth_prop / sb-sm-4` | SecularBox/Smooth | `b#stepP:p14:sb-sm-4@L204-L204` | `b#stepP:p14:sb-sm-4@L204-L204` |
| `bpP:p14:sb-rot` | `sb_rot` | SecularBox/Rotation | `b#bpP:p14:sb-rot@L207-L210` | `b#bpP:p14:sb-rot@L211-L216` |
| `stepP:p14:sb-rot-1` | `internal sb_rot / sb-rot-1` | SecularBox/Rotation | `b#stepP:p14:sb-rot-1@L212-L212` | `b#stepP:p14:sb-rot-1@L212-L212` |
| `stepP:p14:sb-rot-2` | `internal sb_rot / sb-rot-2` | SecularBox/Rotation | `b#stepP:p14:sb-rot-2@L213-L213` | `b#stepP:p14:sb-rot-2@L213-L213` |
| `stepP:p14:sb-rot-3` | `internal sb_rot / sb-rot-3` | SecularBox/Rotation | `b#stepP:p14:sb-rot-3@L214-L214` | `b#stepP:p14:sb-rot-3@L214-L214` |
| `stepP:p14:sb-rot-4` | `internal sb_rot / sb-rot-4` | SecularBox/Rotation | `b#stepP:p14:sb-rot-4@L215-L215` | `b#stepP:p14:sb-rot-4@L215-L215` |
| `bpP:p14:sb-pred` | `sb_pred` | SecularBox/Field | `b#bpP:p14:sb-pred@L226-L230` | `b#bpP:p14:sb-pred@L231-L234` |
| `stepP:p14:sb-pr-1` | `internal sb_pred / sb-pr-1` | SecularBox/Field | `b#stepP:p14:sb-pr-1@L232-L232` | `b#stepP:p14:sb-pr-1@L232-L232` |
| `stepP:p14:sb-pr-2` | `internal sb_pred / sb-pr-2` | SecularBox/Field | `b#stepP:p14:sb-pr-2@L233-L233` | `b#stepP:p14:sb-pr-2@L233-L233` |
| `bpP:p14:sb-field` | `sb_field` | SecularBox/Field | `b#bpP:p14:sb-field@L236-L240` | `b#bpP:p14:sb-field@L241-L244` |
| `stepP:p14:sb-fd-1` | `internal sb_field / sb-fd-1` | SecularBox/Field | `b#stepP:p14:sb-fd-1@L242-L242` | `b#stepP:p14:sb-fd-1@L242-L242` |
| `stepP:p14:sb-fd-2` | `internal sb_field / sb-fd-2` | SecularBox/Field | `b#stepP:p14:sb-fd-2@L243-L243` | `b#stepP:p14:sb-fd-2@L243-L243` |
| `bpP:p14:sb-flow#omega` | `sb_omega` | SecularBox/Field | `b#bpP:p14:sb-flow#omega@L224-L224` | `—` |
| `bpP:p14:sb-slow` | `sb_slow` | SecularBox/SlowFlow | `b#bpP:p14:sb-slow@L246-L249` | `b#bpP:p14:sb-slow@L250-L256` |
| `stepP:p14:sb-sl-1` | `internal sb_slow / sb-sl-1` | SecularBox/SlowFlow | `b#stepP:p14:sb-sl-1@L251-L251` | `b#stepP:p14:sb-sl-1@L251-L251` |
| `stepP:p14:sb-sl-2` | `internal sb_slow / sb-sl-2` | SecularBox/SlowFlow | `b#stepP:p14:sb-sl-2@L252-L252` | `b#stepP:p14:sb-sl-2@L252-L252` |
| `stepP:p14:sb-sl-3` | `internal sb_slow / sb-sl-3` | SecularBox/SlowFlow | `b#stepP:p14:sb-sl-3@L253-L253` | `b#stepP:p14:sb-sl-3@L253-L253` |
| `stepP:p14:sb-sl-4` | `internal sb_slow / sb-sl-4` | SecularBox/SlowFlow | `b#stepP:p14:sb-sl-4@L254-L254` | `b#stepP:p14:sb-sl-4@L254-L254` |
| `stepP:p14:sb-sl-5` | `internal sb_slow / sb-sl-5` | SecularBox/SlowFlow | `b#stepP:p14:sb-sl-5@L255-L255` | `b#stepP:p14:sb-sl-5@L255-L255` |
| `bpP:p14:sb-global` | `sb_global` | SecularBox/GlobalFlow | `b#bpP:p14:sb-global@L258-L261` | `b#bpP:p14:sb-global@L262-L266` |
| `stepP:p14:sb-gl-1` | `internal sb_global / sb-gl-1` | SecularBox/GlobalFlow | `b#stepP:p14:sb-gl-1@L263-L263` | `b#stepP:p14:sb-gl-1@L263-L263` |
| `stepP:p14:sb-gl-2` | `internal sb_global / sb-gl-2` | SecularBox/GlobalFlow | `b#stepP:p14:sb-gl-2@L264-L264` | `b#stepP:p14:sb-gl-2@L264-L264` |
| `stepP:p14:sb-gl-3` | `internal sb_global / sb-gl-3` | SecularBox/GlobalFlow | `b#stepP:p14:sb-gl-3@L265-L265` | `b#stepP:p14:sb-gl-3@L265-L265` |
| `bpP:p14:sb-unique` | `sb_unique` | SecularBox/Uniqueness | `b#bpP:p14:sb-unique@L268-L271` | `b#bpP:p14:sb-unique@L272-L276` |
| `stepP:p14:sb-un-1` | `internal sb_unique / sb-un-1` | SecularBox/Uniqueness | `b#stepP:p14:sb-un-1@L273-L273` | `b#stepP:p14:sb-un-1@L273-L273` |
| `stepP:p14:sb-un-2` | `internal sb_unique / sb-un-2` | SecularBox/Uniqueness | `b#stepP:p14:sb-un-2@L274-L274` | `b#stepP:p14:sb-un-2@L274-L274` |
| `stepP:p14:sb-un-3` | `internal sb_unique / sb-un-3` | SecularBox/Uniqueness | `b#stepP:p14:sb-un-3@L275-L275` | `b#stepP:p14:sb-un-3@L275-L275` |
| `stepP:p14:sb-th-1` | `internal sb_safety / sb-th-1` | SecularBox/Safety | `b#stepP:p14:sb-th-1@L283-L283` | `b#stepP:p14:sb-th-1@L283-L283` |
| `stepP:p14:sb-th-2` | `internal sb_safety / sb-th-2` | SecularBox/Safety | `b#stepP:p14:sb-th-2@L285-L286` | `b#stepP:p14:sb-th-2@L285-L286` |
| `stepP:p14:sb-th-3` | `internal sb_safety / sb-th-3` | SecularBox/Safety | `b#stepP:p14:sb-th-3@L288-L288` | `b#stepP:p14:sb-th-3@L288-L288` |
| `stepP:p14:sb-th-4` | `internal sb_safety / sb-th-4` | SecularBox/Safety | `b#stepP:p14:sb-th-4@L290-L290` | `b#stepP:p14:sb-th-4@L290-L290` |
| `stepP:p14:sb-th-5` | `internal sb_safety / sb-th-5` | SecularBox/Safety | `b#stepP:p14:sb-th-5@L292-L292` | `b#stepP:p14:sb-th-5@L292-L292` |
| `stepP:p14:sb-th-6` | `internal sb_safety / sb-th-6` | SecularBox/Safety | `b#stepP:p14:sb-th-6@L294-L294` | `b#stepP:p14:sb-th-6@L294-L294` |
| `stepP:p14:sb-th-7` | `internal sb_safety / sb-th-7` | SecularBox/Safety | `b#stepP:p14:sb-th-7@L296-L296` | `b#stepP:p14:sb-th-7@L296-L296` |
| `stepP:p14:sb-th-8` | `internal sb_safety / sb-th-8` | SecularBox/Safety | `b#stepP:p14:sb-th-8@L298-L298` | `b#stepP:p14:sb-th-8@L298-L298` |
| `stepP:p14:sb-th-9` | `internal sb_safety / sb-th-9` | SecularBox/Safety | `b#stepP:p14:sb-th-9@L300-L300` | `b#stepP:p14:sb-th-9@L300-L300` |
| `stepP:p14:sb-th-10` | `internal sb_safety / sb-th-10` | SecularBox/Safety | `b#stepP:p14:sb-th-10@L302-L302` | `b#stepP:p14:sb-th-10@L302-L302` |
| `stepP:p14:sb-th-11` | `internal sb_safety / sb-th-11` | SecularBox/Safety | `b#stepP:p14:sb-th-11@L304-L306` | `b#stepP:p14:sb-th-11@L304-L306` |
| `stepP:p14:sb-ci-1` | `internal sb_cited / sb-ci-1` | SecularBox/CitedMasses | `b#stepP:p14:sb-ci-1@L310-L310` | `b#stepP:p14:sb-ci-1@L310-L310` |

## Reuse and upstream interface (to reconcile)

Existing ordinary modules are authoritative when they have already implemented a delivered design.
The following names were inspected in source; signatures elaboration additionally checks the imported carriers.
No proposed upstream theorem is assigned a hypothetical full Lean type here.

| Supplier | Exact declaration(s) / graph interface | Supplied premises and consumed conclusion |
|---|---|---|
| `KAM/Kepler/Plane.lean` | `KAM.Kepler.planeLength_sq`, `planeSq_mul_planeSq`, `abs_planeDot_le`, `abs_planeLength_sub_le`, `norm_le_planeLength`, `planeLength_add_le` | all planar algebra; max-norm boundedness from physical radial bounds |
| `KAM/Planetary/Newtonian/Models.lean` | `isOpen_collisionFreeDomain`, `analyticOnNhd_movingHamiltonian`, `differentiableAt_movingHamiltonian`, `hamiltonianVectorField_moving`, `movingHamiltonian_split`, `analyticOnNhd_fMov` | collision-free membership supplied by geometry; exact literal moving Hamiltonian, including indirect term |
| `KAM/Planetary/Newtonian/Barycentric.lean` | `barycentricPositions_succ_sub_zero`, `barycentricPositions_succ_sub_succ` | all pair differences reduce to heliocentric vectors; no mass approximation |
| `KAM/Planetary/Newtonian/Reconstruction.lean` | `isNewtonSolutionOn_of_isMovingSolutionOn` | positive weights from admissibility, mu ≥ 0 from hmu, arbitrary interval J; frozen Newton predicate |
| `KAM/Planetary/Poincare/{Chart,Symplectic,Product}.lean` | `analyticOnNhd_poincare`, `poincare_elements`, `planetBlock`, `poincareProd`, `poincareProd_image`, `regionProd_one_iff`, `poincareProd_symplectic`, `movingHamiltonian_poincareProd`, `analyticOnNhd_fMov_poincareProd`, `poincareProd_lattice` | positive weights and strength 1; componentwise general-n dictionary, onto physical prograde region, analytic splitting |
| Delivered Kepler signatures, n=2 only | `secularGamma_eq`, `secularRoot_eq`, `secularEccVector_eq`, `secularAxis_eq`, `keplerFunctions_poincareProd` | use exact types only in the two-planet dictionary; p14b's direct algebra does not depend on these comparisons |
| Delivered P Part 1 | `KAM.Planetary.chart_field`, `chart_orbit`, `chart_field_differentiableAt_iff` | exact interface takes a self-map `Phase d → Phase d`; use `poincareProdCast` and `phaseCast (Nat.mul_two n)` at this boundary, with c=1, rather than pretending n+n and n*2 are definitionally equal |
| `KAM/ODE/Basic.lean` | `KAM.ODE.IsSolutionIn`, `.mono`, `.continuousOn`, `gen_symmetry_neg` | frozen predicate bridge, restriction, continuity and negative-time sign |
| `KAM/ODE/{Uniqueness,Maximal,Continuation,Exit,Lipschitz}.lean` | `gen_uniqueness`, `gen_uniqueness_inter`, `gen_maximal`, `gen_continuation_compact`, `gen_continuation`, `gen_exit`, `gen_uniform_compact`, `gen_lip`, `UniformData` | open W, C1 field, actual compact subset of W, two-sided derivatives; use exact EReal endpoint clauses of IsMaximalSolution |
| Existing periodic ODE helper | `KAM.ODE.gen_uniform_periodic` | period-one translation of an entire first block, domain univ × U; cannot apply directly to P's radian fast sub-block. `uniform_data` is the required generalization using the same compact-cell proof |
| N root, pending proof release | `KAM.Nekhoroshev.partialConvex_nekhoroshev` (`bpN:p0:partial`) | n fast actions, k=n slow pairs; G=`fastBox B kappa`, G'= `fastBox B (2*kappa)`, D=`slowBall n A`; h_data and perturbation supply every hypothesis. Consume queried-time fast drift ≤ nu^b/2 for an arbitrary supplied segment C and verified slow erosion |
| N Parts 11a–c, not yet delivered | owning root interface above; reconciliation only | require ordinary proof export with the exact frozen telescope, or wait for sealed anchor; no invented replacement theorem or conclusion-shaped hypothesis |
| P Part 8 `bpP:p8:e-diff` | interface to reconcile: real compact-box parameter differentiation | need Ck integral on open subsets of Phase 4, joint Ck integrand, compact F box. Local theorem `secular_parametric_integral` supplies this instance independently if the upstream interface differs |
| Local calculus wrappers (A5,E5,S9) | `interval_constancy`, `complex_division`, `angle_quadrature` | interval-local conservation, multivariable holomorphic quotients, two-sided angle quadrature; exact signatures in Appendix A |
| Mathlib | `hasFDerivAt_integral_of_dominated_of_fderiv_le`, `HasFDerivAt.restrictScalars`, `Function.Periodic.intervalIntegral_add_eq`, `intervalIntegral.integral_hasDerivAt_right` | parameter-integral induction, local real restriction, translation of each F variable, angle quadrature |

N's h-data has **curried bilinear operator norm**, not the max matrix-entry or matrix-operator norm.
Use M = sum_i 3 m_i^3/(5 lower_i/8)^4; g = min_i m_i^3/(upper_i+3 kappa)^3 and
v = min_i 3 m_i^3/(upper_i+3 kappa)^4. Positivity uses n≥2 and positive weights/axes.
The signs in `HasDefiniteFastPart` are -1 for h and +1 for -h; the real-frequency lower bound is unchanged.
The h_data signature characterizes g and v by lower bounds and attained minima, and fixes M by the
exact displayed sum. Thus the witnesses are uniquely determined by B.mass, B.lower, B.upper and kappa,
independent of e,A,rho; existential placement after rho does not permit them to vary. E4 proves the
finite-minimum existence using n≥2, and uniqueness by applying each minimum lower bound to the other's
attaining index. It also exports the coordinate margin 0 < 5*lower_i/8 ≤ lower_i-3*kappa ≤ Re z_i.
E4 derives holomorphy, C2, reality and the same Hessian bound for -h by negation.

## Conventions and departures

- Periods are radians in this layer: frozen `fastShift` adds 2*pi*k to lambda, with no time rescaling.
  N-PARTIAL-CONVEX already uses this convention; no period-one conversion is inserted in its application.
- N's number of fast actions is the **planet count n**, and its slow-pair count is k=n. Never replace the
  exponent by the expression at 2n. Prove the definitional equalities between `partialTimeExponent n` and
  `planetaryTimeExponent n`, and between their drift counterparts before rewriting the application.
- Use `ContDiffOn ℝ ∞`, local open-domain fderiv congruence, and `HasDerivAt`; no within-derivative at the
  horizon endpoints can replace the frozen two-sided derivative. Continue strictly beyond ±T.
- New files use copyright, `module`, `public import`, module docstring and `@[expose] public noncomputable section`.
  No bare Pi/matrix instances, no resource overrides. All theorem bodies in Appendix A are `sorry`, only in scratch.
- D1 corrected in Revision 2: `elements` and `eccentricity_deficit` take only the selected planet's four
  scalar conditions, exactly as the source. Global consumers pass `hz i` from frozen `ProgradeElliptic`.
  No new one-planet structure is introduced. `elements` exports clauses (a)–(f), including nonnegative
  eccentricity/deficit, C≤Lambda, and the second dot-product identity; the threshold deficit is separate.
- Departure D2: `stopped` existentially bundles B0 and nu0 after B. The proof fixes the same B0 produced by
  perturbation. This hides intermediate choices without changing uniformity in mu,T,delta,z0.
- Departure D3: `sb_cov` is strengthened to all w. Its equalities are algebraic and rotations preserve the
  squared slow radius even when total sqrt/division formulas are used; no positivity is needed for covariance.
- Departure D4: lambda-independence in `sb_smooth_prop` is global because the frozen integral never reads
  the input fast-angle block. The smoothness and regularity clauses remain restricted to S.
- Departure D5: `sb_unique` omits the competing curve's SecularRegular premise. The agreement-set argument
  above proves the stronger result; the public frozen type is preserved literally.
- Departure D6: root signatures use snake_case graph names (`amd`, `expsafe`, `sb_safety`, `sb_cited`);
  quarantined provider signatures retain the prescribed frozen camelCase names.

## Blueprint issues, inherited gaps, and errata

No new pinned-paper erratum is claimed. This is a blueprint/interface design, not a new PDF audit.
All source deviations already documented in p14a L339 and p14b L329 are retained: low-AMD specialization
rather than Nek77's original domain route; frozen max-norm/open-width N input; unscaled heliocentric chart;
rational-square secular estimates; direct conservation from the explicit F integral.

| Location and quoted text | Why it needs care | Design resolution |
|---|---|---|
| `p7-kepler-poincare.tex` L173, ho-hol: “the complex derivative restricts to the real one” with K:real-restriction | cited K theorem is on a full torus strip; the local chart domain is bounded in other variables | `local_complex_restriction`, via `HasFDerivAt.restrictScalars` and the real/imaginary projections; no strip hypothesis |
| p7 L207, pc-share: “whose proof gives analyticity as well as $C^\infty$” | that blueprint reference supplies smooth calculus, not analytic calculus | explicit `chart_perturbation_analytic`; use existing `analyticAt_inv_planeLength`, `analyticOnNhd_fMov`, `analyticOnNhd_poincareProd` and analytic composition |
| p14a L168: “Part 7 proves (Ch2) for n=2 ... componentwise” | cannot apply the Fin 2 theorem at arbitrary n | `sec_domain_chart_facts` from each `poincare_elements` and the product indexing; the extra general-n bridge is a local obligation |
| p14a L243: compact-cell uniform data | existing `gen_uniform_periodic` uses a period-one full angle block | own `uniform_data`; choose delta≤pi and compact lambda-cell [-pi,3pi]^n; remaining coordinates are compact |
| p14a L210–217, “Complexification of real analytic functions” and “Gluing” | substantial general analytic extension and real-trace uniqueness work, not already supplied by smoothness | own `local_analytic_complexification` and `tube`; prove equalities on intersections of real-centered polydiscs, including translated overlaps and the empty K case |
| p14b L203: “same holds for every order” | Mathlib inspected ParametricIntegral has a first-derivative theorem, no direct matching C∞ compact-box API | `secular_parametric_integral` by induction with continuous derivatives bounded on a compact parameter neighborhood times the F box; prove every finite order, then C∞ |
| p14b L138: “norm_num reaches directly” | norm_num proves closed rational goals, not inequalities involving variable k_i and e_i | split the closed certificate `sb_numerics` from variable inequalities; use ordered-ring reasoning and square comparison for the latter |

The assembled graph has no SOURCE_GAP record owned by p14a/b. Its expsafe closure inherits ho-hol;
this design names the repair obligation rather than interpreting source-model PASS as its proof.
Neither pc-share nor ho-hol is silently assumed proved because an existing design promises it.
The ordinary analytic modules inspected today provide usable suppliers, but kernel validation of the
new bridge and the eventual provider closure are still required. No frozen-file defect was found.

## Modules, packages, waves and import DAG

Every module below is `KAM/Planetary/<relative>.lean`; the table gives **exact paths** by this convention.
Sizes are estimated implementation lines, not signature lines. Each package is 150–800 lines; split before 1500.
Every package brief must reproduce the hard rules below, and name Appendix A plus its node rows as the contract.

| Package | Wave | Relative module path | Lines | Inputs; outputs |
|---|---:|---|---:|---|
| A0 | 1 | `AMD/Setting` | 150 | frozen defs; region definitions |
| A1 | 1 | `AMD/Elements` | 650 | Kepler/Plane, frozen elements; elements, eccentricity_deficit, ecc_bound |
| A2 | 2 | `AMD/Geometry` | 500 | A0,A1, Barycentric; geometry, amd_compact |
| A3 | 2 | `AMD/Closure` | 450 | A0,A1; closure and continuity on the negative-energy domain |
| A4 | 1 | `AMD/MovingODE` | 200 | Newtonian/Models, ODE/Hamiltonian; moving_ode |
| A5 | 2 | `AMD/AngularMomentum` | 350 | A4, hamiltonianVectorField_moving; interval_constancy, ang_mom, ordered-pair cancellation |
| A6 | 3 | `AMD/Confinement` | 750 | A2,A3,A4,A5, ODE/Exit,Maximal,Continuation, Reconstruction; amd |
| E0 | 1 | `Exponential/Setting` | 180 | frozen blocks; chartAMD, chartSafe, boxes, cylinders, EnlargedData, planetaryKeplerC |
| E1 | 2 | `Exponential/Dictionary` | 450 | E0, poincare_elements, Product; sec_domain_chart_facts, general-n prograde onto bridge |
| E2 | 2 | `Exponential/Enlargement` | 300 | E0, admissibility; enlarge, positivity of slow erosion |
| E3 | 3 | `Exponential/RealDomain` | 450 | E1,E2,A1; real_domain |
| E4 | 3 | `Exponential/KeplerData` | 600 | E2,E5, frozen HasDefiniteFastPart; h_data, both signs, sum Hessian bound |
| E5 | 1 | `Exponential/LocalComplexification` | 650 | real analytic power series, restrictScalars; complex_division, local_complex_restriction, local_analytic_complexification |
| E6 | 2 | `Exponential/ComplexTube` | 750 | E5, compactness, real_trace_identity; tube |
| E7 | 4 | `Exponential/Perturbation` | 550 | E3,E6, analyticOnNhd_fMov_poincareProd; chart_perturbation_analytic, perturbation |
| E8 | 2 | `Exponential/UniformData` | 400 | E0, gen_lip, compact-neighborhood API; uniform_data |
| E9 | 4 | `Exponential/Lift` | 600 | E1,E3,E8,A4, chart_orbit, ODE/Maximal,Continuation; lift |
| E10 | 5 | `Exponential/Hamiltonian` | 250 | E4,E7, movingHamiltonian_poincareProd; hnu, local fderiv equality, signs |
| E11 | 6 | `Exponential/Stopped` | 700 | E9,E10,E4,E7, exact released N root; stopped, both erosions, reversed segments |
| E12 | 7 | `Exponential/Safety` | 450 | E11,A6; expsafe, uniform constants and axis drift |
| S0 | 1 | `SecularBox/Numerics` | 180 | Mathlib norm_num; all N1–N7 and source-chain checks |
| S1 | 1 | `SecularBox/Chart` | 600 | frozen chart quantities, Kepler/Plane; sb_chart |
| S2 | 2 | `SecularBox/Covariance` | 350 | S1, Kepler rotations; secularRotation, sb_cov |
| S3 | 2 | `SecularBox/Region` | 400 | S0,S1; sb_sdef, sb_s |
| S4 | 1 | `SecularBox/ParametricIntegral` | 600 | Mathlib ParametricIntegral; secular_parametric_integral |
| S5 | 3 | `SecularBox/Smooth` | 650 | S3,S4, Newtonian/Models; sb_smooth_prop, integrability |
| S6 | 4 | `SecularBox/Rotation` | 450 | S2,S3,S5, periodic interval integral and Fubini; sb_rot |
| S7 | 5 | `SecularBox/Field` | 400 | S5,S6, ODE/Hamiltonian; sb_omega, reducedSecularH, sb_pred, sb_field |
| S8 | 6 | `SecularBox/SlowFlow` | 500 | S7,S0, ODE/Maximal,Continuation; sb_slow |
| S9 | 7 | `SecularBox/GlobalFlow` | 300 | S8,S7, FTC; angle_quadrature, sb_global |
| S10 | 8 | `SecularBox/Uniqueness` | 300 | S9,S7, gen_uniqueness, connectedness; sb_unique |
| S11 | 9 | `SecularBox/Safety` | 400 | S0,S1,S3,S5,S9,S10,Barycentric; sb_safety |
| S12 | 10 | `SecularBox/CitedMasses` | 150 | S11,S0; sb_cited and exact decimal mass identity |
| Q | after respective libraries | four provider modules listed below | 150 total | wrappers and integration receipts; no new mathematics |

Q may be grouped with S12 or E12 for a 150–800-line prover session; individual wrappers remain tiny.
All definitions belong to the earliest module named above; move a table-row reference to that module when
it lists a later consumer (e.g. sb_omega is defined in Field, and EnlargedData in Setting).

DAG: A0,A1 → A2,A3; A4 → A5; {A2,A3,A4,A5} → A6.
E0 → E1,E2,E8; {E1,E2} → E3; {E2,E5} → E4; E5 → E6; {E3,E6} → E7;
{E1,E3,E8,A4} → E9; {E4,E7} → E10; {E4,E7,E9,E10,N-root} → E11; {E11,A6} → E12.
S1 → S2; {S0,S1} → S3; {S3,S4} → S5; {S2,S3,S5} → S6;
{S5,S6} → S7 → S8 → S9 → S10; {S0,S1,S3,S5,S9,S10} → S11 → S12.
No arrow points from an implementation module to a provider or a DRAFT_SORRY theorem.

## Provider assembly to exact frozen types

Appendix A repeats all four frozen type telescopes twice: ordinary graph-named library results and
`KAM.Provider.Planetary.*`. The copied telescopes are the authority, including every conjunction and quantifier.
The provider files are:

- `KAM/Provider/Planetary/AmdConfinement.lean` imports `KAM.Planetary.AMD.Confinement`.
- `KAM/Provider/Planetary/PlanetaryExponentialSafety.lean` imports `KAM.Planetary.Exponential.Safety`.
- `KAM/Provider/Planetary/SecularBoxSafety.lean` imports `KAM.Planetary.SecularBox.Safety`.
- `KAM/Provider/Planetary/SecularBoxAtCitedMasses.lean` imports `KAM.Planetary.SecularBox.CitedMasses`.

Each wrapper applies the library theorem to exactly its explicit binders in order. Implementation bodies
are future work: `by exact KAM.Planetary.amd hn B hB mu T delta hmu hT hdelta hmargin hAMD z0 hz0 hstop`,
`by exact KAM.Planetary.expsafe hn B hB`,
`by exact KAM.Planetary.sb_safety saturn mu hsaturn hmu w0 hw0`, and
`by exact KAM.Planetary.sb_cited w0 hw0`, respectively. The signatures contain only sorry bodies.

| Frozen result | Binder-by-binder handling | Exact conclusion assembly |
|---|---|---|
| amdConfinement | `{n}`, hn: planet count≥2; B,hB: fixed geometric data; mu,T,delta and hmu,hT,hdelta: positive physical parameters; hmargin: each action collar; hAMD: AMD collar; z0,hz0: inner datum; hstop: stopped input | choose maximal z with z(0)=z0. First exit uses hstop only on [0,s] or [-s,0] already inside outer region. ang_mom gives AMD(t)-AMD(0)=sum action differences. closure gives no exit; amd_compact gives continuation strictly beyond ±T. Pack IsMovingSolutionOn, MovingUniqueOn, Newton reconstruction, and the pointwise region/momentum/eccentricity/radial/PairBounds group in frozen order; outside that group append physicalAMD≤initialAMD+n*delta and each action drift≤delta |
| planetaryExponentialSafety | `{n}`,hn,B,hB fixed **before** muStar,c,C; every positive mu<muStar; every z0 in the same inner region | choose stopped's B0,nu0, then theta=min{kappa,epsD,all inner action gaps,(A1-A0)/n}>0; muStar=B0^-1*min(nu0/2,(theta/2)^(1/b)), c=B0^(-a), C=B0^b*max_i upper_i/mass_i^2. Set nu=B0*mu, delta=nu^b/2 and T=exp(c*mu^(-a)); T≤nu^-1 exp(nu^-a), all amd margins hold. Apply amd; convert |t|≤T to Icc membership; factor axis difference=(Lambda(t)-Lambda(0))*(Lambda(t)+Lambda(0))/mass_i^2 and bound the sum by 2 upper_i. Reuse the first grouped clauses exactly; append the frozen axis drift for all real t with |t|≤T |
| secularBoxSafety | saturn,mu; hsaturn: closed rational mass-ratio range; hmu: positivity; w0,hw0: literal SecularInputBox | sb_numerics+sb_chart give actions>87/100, AMD<16373/2500000, and w0∈S. sb_global supplies w, initial equality, global Hamiltonian predicate, constant fast actions/AMD. sb_unique accepts the frozen U,v, openness, convexity, zero membership, initial equality, solution and regularity binders; its stronger helper ignores only the last premise. For each t, S and smoothness give SecularRegular; squares give eccentricity<3/20; conserved actions give initial axis ranges. Chart radii yield 1751/400 and 4439/400, difference 399/200; barycentric differences yield PairBounds(399/200,4439/200). Pack these in the exact frozen order, including every F∈(Fin 2→ℝ) |
| secularBoxAtCitedMasses | w0,hw0 at ratio 476/1591; no new smallness premise | apply ordinary sb_safety with saturn=476/1591, mu=4773/5000000 and rational certificates. All function arguments specialize literally. No provider or DRAFT_SORRY secularBoxSafety import. The equality mu*saturn=357/1250000 identifies the cited decimal model only |

N root application inside E11 is explicit: use G and G' as above, their open/convex proofs, open D,
rho>0, Mcomplex>0, closed-ball collar, holomorphic/C2/reality/bilinear-bound clauses of h_data, and its
HasDefiniteFastPart. Do this for both h and -h, before choosing the tested P, segment duration C or curve.
Set nu0=min(1,muPlus,muMinus,kappa^(1/b),epsD^(1/b)); epsD=(sqrt(2*A)-sqrt(2*outerAMD))/sqrt(2*n).
The finite physical segment lifts by E9; hnu and open-set fderiv congruence identify the Hamiltonian fields.
At initial time fast actions lie in innerCore G nu^b; through each queried time the slow point lies in
innerCore D nu^b because sqrt(sum slow squares)≤sqrt(2*outerAMD) and the max-norm error has Euclidean
length≤sqrt(2*n)*nu^b. Reverse negative times with (-h,-P). No whole-window slow confinement is assumed.

The identity-theorem obligation is restricted to intersections of real-centered complex balls, exactly
what gluing uses. `real_trace_identity` has that explicit signature; it does not assume equality on
an arbitrary complex domain as a substitute for proving the real-trace identity theorem.
Additional helper signatures `element_continuity`, `original_cylinder_subset`,
`secular_integrand_identity`, `secular_integrand_smooth`, and `secular_field_components` attach
respectively to A3, E3, S5, S5, and S7. The proof-step table points to the parent contracts;
these helpers provide the intermediate statements those packages consume.

## Risks and verification contract

The longest analytic obligations are real-analytic complexification/gluing and Ck parameter-integral induction;
the longest dynamic obligation is first-exit bookkeeping at two-sided endpoints. Split modules, never raise budgets.
The N root proof is an actual prerequisite of E11; the design does not certify its current proof status.
The general-n dictionary, radians/full-block periodicity distinction and curried Hessian sum are mandatory
integration checks. The secular result concerns the exact averaged model for every positive mu, not physical
Newtonian confinement at the cited masses.

Appendix A is a signature contract, not a proof: its sorry-bearing results have `sorryAx` until implemented.
Expected future proved-result axioms are only `propext`, `Classical.choice`, `Quot.sound`; obtain actual
`#print axioms` receipts when each provider is proved. The design validation prints axioms for its four
ordinary assemblies separately and reports the admitted status honestly.

## Hard rules (verbatim; reproduce in every prover brief)

1. **Never use `set_option maxHeartbeats`** (or any heartbeat-budget override). A default-heartbeat elaboration
   failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a
   proof will not elaborate at default heartbeats, report it as a design signal.
2. **No Lean file may exceed 1500 lines of code.** When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.
3. **Every `.lean` file is a Lean module**: copyright comment, `module`, imports (`public import` for the
   interface), module docstring, `public section`. Expose (`@[expose]`) definitions whose bodies must unfold.
4. **No `axiom`, `admit`, `unsafe`, `opaque`; `sorry` only** as the manifest-bound body of a frozen statement in
   `KAM/Frozen/`. No recursion-depth or synthesis-heartbeat overrides either.
5. **Frozen files are read-only.** Never edit anything under `KAM/Frozen/` or `manifest/`. If a frozen
   declaration looks wrong, stop and report; never add a premise or substitute a helper.
6. **No conclusion-shaped hypotheses.** A theorem may assume only source premises, standing assumptions, typing
   data and explicit owner rulings. Conditional helpers get distinct names and never stand in for a source result.
7. **Ambient types:** `Fin n → ℝ`, `Fin n → ℂ`, Fourier indices `Fin n → ℤ`. Never `EuclideanSpace`.
8. **Builds:** one targeted `nice -n 5 lake build <Module>` at a time; never `lake clean`; never rebuild the
   library from scratch in a worktree (worktrees use a copy-on-write overlay on `main`'s build snapshot). A wait
   on the compile gate is expected, not a hang.
9. **Providers are quarantined.** `KAM/Provider/<Name>.lean` proves its frozen theorem as `KAM.Provider.<name>`;
   no module except the frozen anchor may import a provider or a `DRAFT_SORRY` anchor (the root file skips them).
10. **Never edit `README.md`** (generated) or `KAM.lean` (generated by `scripts/gen_root_imports.py`).
11. **Errata:** report every suspected defect in a pinned source (location, quoted text, why it is wrong) in your
    handoff; the orchestrator records it in `docs/errata/ledger.json`. Deviations you introduce are reported too.


## Input snapshot

- `blueprint-P/parts/p14a-amd-expsafe.tex`: SHA-256 `a2735bd6fbc36dc765bafccac43af4e3742b101a7e0f2d97725e70ac37ff8452`.
- `blueprint-P/parts/p14b-secular-box.tex`: SHA-256 `f14536c948f27bc9ccb330b5df0b482846696aa7ea10283d42ee2569be2d0ae7`.
- `/root/code/KAM-inp/docs/graph/P/DEPGRAPH.md`: SHA-256 `7d58c7597a6e498eddaa56d6b062d015a466131dcd2e9abde2bc852f07b6e8ca`.
- `/root/code/KAM-inp/docs/graph/P/reviews/GLOBAL-review.md`: SHA-256 `39f5a84a7d261187fa474fa94ecc839a1fac463810fdd8ce674fe5766d539e65`.

## Validation receipts

- Required `inp_sig_check.sh /root/code/KAM-inp-design-p14 .drafts/scratch/P14Signatures.lean`: exit 0; 50 diagnostics, all `declaration uses sorry`; no other diagnostics. Default resources and one thread.
- Revision 2 signatures: 755 lines, SHA-256 `cd28718f0ef82c8da477ff5be2985046d08d795614be4d36fd0b7e267de98dd7`; log `.drafts/p14-r2-signatures.log`.
- Static comparison: 8/8 library/provider telescope strings byte-identical to the four frozen declarations; 182/182 scoped graph records represented; blueprint copies identical to inp.
- No production Lean modules were authored or changed; the required gated signature elaboration replaces a targeted module build for this design-only brief.

- `PATH="$PWD/.drafts/gated-bin:$PATH" scripts/lint_sources.sh`: exit 0. The local adapter restores the original PATH and routes only the ABI Lean invocation through the prescribed `inp_sig_check.sh` gate. Log `.drafts/p14-r2-lint.log`. Output:

```text
check_lean_modules: PASS (412 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

- Prescribed gate on `.drafts/scratch/P14R2Axioms.lean`: exit 0; the 50 theorem declarations have only sorry warnings; log `.drafts/p14-r2-axioms.log`. Actual `#print axioms` for `amd`, `expsafe`, `sb_safety`, `sb_cited` reports `[propext, sorryAx, Classical.choice, Quot.sound]` for each. This is an admitted-design receipt, not theorem proof closure.
- `git -C /root/code/KAM-inp-design-p14 diff --cached --check`: exit 0 after staging the sole owned design document.

## Appendix A: exact signatures

The scratch module below is reproduced byte for byte in the untracked deliverable
`/root/code/KAM-inp/.drafts/design/P14Signatures.lean`. Definitions are explicit; all theorem bodies are sorry.

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Iso.Defs.IsHamiltonianSolutionOn
public import KAM.Frozen.Nekhoroshev.Defs.HasDefiniteFastPart
public import KAM.Frozen.Nekhoroshev.Defs.InnerCore
public import KAM.Frozen.Nekhoroshev.Defs.IsPartialPerturbation
public import KAM.Frozen.Nekhoroshev.Defs.PartialDriftExponent
public import KAM.Frozen.Nekhoroshev.Defs.PartialTimeExponent
public import KAM.Frozen.Planetary.Defs.AMDBox
public import KAM.Frozen.Planetary.Defs.AMDBoxAdmissible
public import KAM.Frozen.Planetary.Defs.ActualMasses
public import KAM.Frozen.Planetary.Defs.BarycentricPositions
public import KAM.Frozen.Planetary.Defs.BarycentricVelocities
public import KAM.Frozen.Planetary.Defs.EllipsePhase
public import KAM.Frozen.Planetary.Defs.EllipsePosition
public import KAM.Frozen.Planetary.Defs.ExactSecularHamiltonian
public import KAM.Frozen.Planetary.Defs.Fast
public import KAM.Frozen.Planetary.Defs.IsMovingSolutionOn
public import KAM.Frozen.Planetary.Defs.IsNewtonSolutionOn
public import KAM.Frozen.Planetary.Defs.JupiterSaturnWeights
public import KAM.Frozen.Planetary.Defs.KeplerAction
public import KAM.Frozen.Planetary.Defs.KeplerAxis
public import KAM.Frozen.Planetary.Defs.KeplerEccVector
public import KAM.Frozen.Planetary.Defs.LowAMDRegion
public import KAM.Frozen.Planetary.Defs.MovingHamiltonian
public import KAM.Frozen.Planetary.Defs.MovingUniqueOn
public import KAM.Frozen.Planetary.Defs.NoCollision
public import KAM.Frozen.Planetary.Defs.OscillatorAction
public import KAM.Frozen.Planetary.Defs.PairBounds
public import KAM.Frozen.Planetary.Defs.PhysicalAMD
public import KAM.Frozen.Planetary.Defs.PlanetaryDriftExponent
public import KAM.Frozen.Planetary.Defs.PlanetaryTimeExponent
public import KAM.Frozen.Planetary.Defs.SecularAMD
public import KAM.Frozen.Planetary.Defs.SecularAverage
public import KAM.Frozen.Planetary.Defs.SecularEccVector
public import KAM.Frozen.Planetary.Defs.SecularInputBox
public import KAM.Frozen.Planetary.Defs.SecularRegular
public import KAM.Frozen.Planetary.Defs.Slow
public import KAM.Frozen.Planetary.Defs.StoppedActionBound
public import KAM.Frozen.Planetary.Defs.TotalMomentum
public import KAM.ODE.Basic
public import KAM.ODE.Lipschitz
public import KAM.Planetary.Poincare.Product
public import Mathlib

/-! # P14 design signatures. Planning evidence; every theorem body is sorry.
No frozen theorem or provider imports. Definitions are literal auxiliary objects.
-/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff NNReal
namespace KAM.Planetary
variable {n : ℕ}


/-- Local replacement for the strip-only restriction cited at p7:ho-hol. -/
theorem local_complex_restriction {d : ℕ}
    {f : ((Fin d → ℂ) × (Fin d → ℂ)) → ℂ} {z : Phase d}
    (hf : DifferentiableAt ℂ f (KAM.Nekhoroshev.complexifyPhase z)) (v : Phase d) :
    fderiv ℝ (fun w => (f (KAM.Nekhoroshev.complexifyPhase w)).re) z v =
      (fderiv ℂ f (KAM.Nekhoroshev.complexifyPhase z)
        (KAM.Nekhoroshev.complexifyPhase v)).re := sorry

theorem local_analytic_complexification {d : ℕ} {f : Phase d → ℝ} {x : Phase d}
    (hf : AnalyticAt ℝ f x) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ((Fin d → ℂ) × (Fin d → ℂ)) → ℂ,
      DifferentiableOn ℂ g (Metric.ball (KAM.Nekhoroshev.complexifyPhase x) r) ∧
      ∀ y : Phase d, ‖y-x‖ < r → g (KAM.Nekhoroshev.complexifyPhase y) = (f y : ℂ) := sorry

/-- Real-centered polydisc intersection instance needed by tube gluing. -/
theorem real_trace_identity {d : ℕ} (x y : Phase d) (r s : ℝ)
    {f g : ((Fin d → ℂ) × (Fin d → ℂ)) → ℂ}
    (hf : DifferentiableOn ℂ f
      (Metric.ball (KAM.Nekhoroshev.complexifyPhase x) r ∩
        Metric.ball (KAM.Nekhoroshev.complexifyPhase y) s))
    (hg : DifferentiableOn ℂ g
      (Metric.ball (KAM.Nekhoroshev.complexifyPhase x) r ∩
        Metric.ball (KAM.Nekhoroshev.complexifyPhase y) s))
    (heq : ∀ w : Phase d, KAM.Nekhoroshev.complexifyPhase w ∈
      Metric.ball (KAM.Nekhoroshev.complexifyPhase x) r ∩
        Metric.ball (KAM.Nekhoroshev.complexifyPhase y) s →
      f (KAM.Nekhoroshev.complexifyPhase w) = g (KAM.Nekhoroshev.complexifyPhase w)) :
    Set.EqOn f g (Metric.ball (KAM.Nekhoroshev.complexifyPhase x) r ∩
      Metric.ball (KAM.Nekhoroshev.complexifyPhase y) s) := sorry

/-- Real compact parameter integral; owns p8:e-diff's required instance here. -/
theorem secular_parametric_integral {d q : ℕ} {U : Set (Phase d)} (hU : IsOpen U)
    {Q : Set (Fin q → ℝ)} (hQ : IsCompact Q) {g : Phase d → (Fin q → ℝ) → ℝ}
    (k : ℕ) (hg : ContDiffOn ℝ k (fun p : Phase d × (Fin q → ℝ) => g p.1 p.2)
      (U ×ˢ univ)) :
    ContDiffOn ℝ k (fun w => ∫ F in Q, g w F) U := sorry

theorem angle_quadrature {omega : ℝ → (Fin 2 → ℝ)}
    (h : Continuous omega) (t : ℝ) :
    HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, omega s) (omega t) t := sorry

theorem interval_constancy {J : Set ℝ} (hJ : J.OrdConnected)
    {f : ℝ → ℝ} (hf : ∀ t ∈ J, HasDerivAt f 0 t) :
    ∀ s ∈ J, ∀ t ∈ J, f t = f s := sorry

theorem complex_division {d : ℕ}
    {U : Set ((Fin d → ℂ) × (Fin d → ℂ))}
    {f g : ((Fin d → ℂ) × (Fin d → ℂ)) → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hg0 : ∀ z ∈ U, g z ≠ 0) :
    DifferentiableOn ℂ (fun z => f z / g z) U := sorry

/-! ## AMD geometry -/
def amdOuter (B : AMDBox n) := LowAMDRegion B.mass B.lower B.upper B.outerAMD
def amdInner (B : AMDBox n) := LowAMDRegion B.mass B.innerLower B.innerUpper B.initialAMD
def amdCollar (B : AMDBox n) (delta : ℝ) : Set (Phase (n * 2)) :=
  {z ∈ amdOuter B | (∀ i, B.lower i + delta ≤ keplerAction B.mass z i ∧
    keplerAction B.mass z i ≤ B.upper i - delta) ∧
    physicalAMD B.mass z ≤ B.initialAMD + (n : ℝ) * delta}
def amdCompact (B : AMDBox n) : Set (Phase (n * 2)) :=
  {z | (∀ i, B.distance ≤ planeLength (bodyVector z.1 i) ∧
    planeLength (bodyVector z.1 i) ≤ B.radius ∧
    planeLength (bodyVector z.2 i) ≤ B.mass i * Real.sqrt (2 / B.distance)) ∧
    ∀ i j, i ≠ j → B.distance ≤ planeLength (bodyVector z.1 i - bodyVector z.1 j)}

theorem elements {m : Fin n → ℝ} {z : Phase (n * 2)} (i : Fin n)
    (hz : 0 < m i ∧ 0 < planeLength (bodyVector z.1 i) ∧
      keplerEnergy m z i < 0 ∧
      0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i)) :
    0 < keplerAxis m z i ∧ 0 < keplerAction m z i ∧
    keplerAction m z i ^ 2 = m i ^ 2 * keplerAxis m z i ∧
    keplerEnergy m z i = -(m i)^3 / (2 * keplerAction m z i ^ 2) ∧
    planeLength (keplerEccVector m z i)^2 = 1 -
      planeCross (bodyVector z.1 i) (bodyVector z.2 i)^2 / keplerAction m z i ^ 2 ∧
    planeLength (keplerEccVector m z i) < 1 ∧
    planeCross (bodyVector z.1 i) (bodyVector z.2 i) =
      keplerAction m z i * Real.sqrt (1 - planeLength (keplerEccVector m z i)^2) ∧
    planeDot (bodyVector z.1 i) (keplerEccVector m z i) =
      keplerAxis m z i * (1 - planeLength (keplerEccVector m z i)^2) -
        planeLength (bodyVector z.1 i) ∧
    keplerAxis m z i * (1 - planeLength (keplerEccVector m z i)) ≤
      planeLength (bodyVector z.1 i) ∧
    planeLength (bodyVector z.1 i) ≤
      keplerAxis m z i * (1 + planeLength (keplerEccVector m z i)) ∧
    planeSq (bodyVector z.2 i) < 2 * m i ^ 2 / planeLength (bodyVector z.1 i) ∧
    (0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i) ∧
      planeCross (bodyVector z.1 i) (bodyVector z.2 i) ≤ keplerAction m z i) ∧
    0 ≤ planeLength (keplerEccVector m z i) ∧
    planeDot (bodyVector z.1 i) (keplerEccVector m z i) =
      planeCross (bodyVector z.1 i) (bodyVector z.2 i)^2 / m i^2 -
        planeLength (bodyVector z.1 i) ∧
    keplerAction m z i - planeCross (bodyVector z.1 i) (bodyVector z.2 i) =
      keplerAction m z i * (1 - Real.sqrt (1 - planeLength (keplerEccVector m z i)^2)) ∧
    0 ≤ keplerAction m z i - planeCross (bodyVector z.1 i) (bodyVector z.2 i) := sorry

theorem eccentricity_deficit {m : Fin n → ℝ} {z : Phase (n * 2)}
    (i : Fin n)
    (hz : 0 < m i ∧ 0 < planeLength (bodyVector z.1 i) ∧
      keplerEnergy m z i < 0 ∧
      0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i)) {e : ℝ} (he : 0 ≤ e) (he1 : e < 1)
    (hle : e ≤ planeLength (keplerEccVector m z i)) :
    keplerAction m z i * (1 - Real.sqrt (1 - e ^ 2)) ≤
      keplerAction m z i - planeCross (bodyVector z.1 i) (bodyVector z.2 i) := sorry

theorem ecc_bound {m lo : Fin n → ℝ} {z : Phase (n * 2)} {A e : ℝ}
    (hz : ProgradeElliptic m z) (hlo : ∀ i, 0 < lo i)
    (hact : ∀ i, lo i < keplerAction m z i) (hA : physicalAMD m z < A)
    (he : 0 < e) (he1 : e < 1)
    (hbar : ∀ i, A ≤ lo i * (1 - Real.sqrt (1 - e ^ 2))) :
    ∀ i, planeLength (keplerEccVector m z i) < e ∧
      keplerAction m z i * Real.sqrt (1 - e ^ 2) <
        planeCross (bodyVector z.1 i) (bodyVector z.2 i) := sorry

theorem geometry (B : AMDBox n) (hB : B.Admissible) {z : Phase (n * 2)}
    (hz : z ∈ amdOuter B) :
    (∀ i, (B.lower i / B.mass i)^2 < keplerAxis B.mass z i ∧
      keplerAxis B.mass z i < (B.upper i / B.mass i)^2 ∧
      planeLength (bodyVector z.2 i) < B.mass i * Real.sqrt (2 / B.distance)) ∧
    (∀ i j, i < j → B.distance ≤
      planeLength (bodyVector z.1 j) - planeLength (bodyVector z.1 i)) ∧
    z ∈ amdCompact B ∧ NoCollision z.1 ∧
    (∀ i, planeLength (keplerEccVector B.mass z i) < B.ecc ∧
      B.distance ≤ planeLength (bodyVector z.1 i) ∧
      planeLength (bodyVector z.1 i) ≤ B.radius) ∧
    ∀ mu : ℝ, PairBounds B.distance (2 * B.radius)
      (barycentricPositions 1 B.mass mu z.1) := sorry

theorem amd_compact (B : AMDBox n) (hB : B.Admissible) :
    IsCompact (amdCompact B) ∧ amdCompact B ⊆ collisionFreeDomain n := sorry

theorem closure (B : AMDBox n) (hB : B.Admissible) {delta : ℝ} (hd : 0 < delta)
    (hmargin : ∀ i, B.lower i + 2 * delta < B.innerLower i ∧
      B.innerUpper i + 2 * delta < B.upper i)
    (hAMD : B.initialAMD + 2 * (n : ℝ) * delta < B.outerAMD) :
    IsOpen (amdOuter B) ∧
    ∀ (z : ℕ → Phase (n * 2)) (zs : Phase (n * 2)),
      (∀ k, z k ∈ amdCollar B delta) → Filter.Tendsto z Filter.atTop (nhds zs) →
      (∀ i, 0 < planeLength (bodyVector zs.1 i)) → zs ∈ amdCollar B delta := sorry

def negativeEnergyDomain (m : Fin n → ℝ) : Set (Phase (n*2)) :=
  {z | ∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy m z i < 0}
theorem element_continuity (m : Fin n → ℝ) :
    IsOpen (negativeEnergyDomain m) ∧
    (∀ i, ContinuousOn (fun z => keplerAction m z i) (negativeEnergyDomain m)) ∧
    ContinuousOn (physicalAMD m) (negativeEnergyDomain m) := sorry

theorem moving_ode (m : Fin n → ℝ) (mu : ℝ) :
    IsOpen (collisionFreeDomain n) ∧
    ContDiffOn ℝ 1 (KAM.hamiltonianVectorField (movingHamiltonian 1 1 m mu))
      (collisionFreeDomain n) ∧
    ∀ (J : Set ℝ) (z : ℝ → Phase (n * 2)), IsMovingSolutionOn m mu J z ↔
      KAM.ODE.IsSolutionIn (KAM.hamiltonianVectorField (movingHamiltonian 1 1 m mu))
        (collisionFreeDomain n) J z := sorry

theorem ang_mom {m : Fin n → ℝ} {mu : ℝ} {J : Set ℝ}
    (hJ : J.OrdConnected) {z : ℝ → Phase (n * 2)} (hz : IsMovingSolutionOn m mu J z) :
    ∀ s ∈ J, ∀ t ∈ J, totalMomentum (z t) = totalMomentum (z s) := sorry

/-! ## Enlarged analytic data: source geometry only, not conclusions as hypotheses. -/
def chartAMD (w : Phase (n + n)) : ℝ :=
  ∑ i, ((slow w.1 i)^2 + (slow w.2 i)^2) / 2
def chartSafe (m : Fin n → ℝ) : Set (Phase (n + n)) :=
  poincareProdDom n ∩ poincareProd m 1 ⁻¹' collisionFreeDomain n
def fastBox (B : AMDBox n) (kappa : ℝ) : Set (Fin n → ℝ) :=
  {I | ∀ i, B.lower i - kappa < I i ∧ I i < B.upper i + kappa}
def slowBall (n : ℕ) (A : ℝ) : Set (Phase n) :=
  {y | ∑ i, (y.1 i ^ 2 + y.2 i ^ 2) / 2 < A}
def enlargedCylinder (B : AMDBox n) (kappa A : ℝ) : Set (Phase (n + n)) :=
  {w | (∀ i, B.lower i - 2 * kappa ≤ fast w.2 i ∧
    fast w.2 i ≤ B.upper i + 2 * kappa) ∧ chartAMD w ≤ A}
def workingCylinder (B : AMDBox n) (kappa A : ℝ) : Set (Phase (n + n)) :=
  {w | fast w.2 ∈ fastBox B kappa ∧ (slow w.1, slow w.2) ∈ slowBall n A}
structure EnlargedData (B : AMDBox n) (kappa e A : ℝ) : Prop where
  kappa_pos : 0 < kappa
  ecc_lt : B.ecc < e
  ecc_one : e < 1
  amd_lt : B.outerAMD < A
  small : ∀ i, kappa ≤ B.lower i / 8
  deficit : ∀ i, A < (B.lower i - 2 * kappa) * (1 - Real.sqrt (1 - e^2))
  radii : ∀ i, B.distance / 2 ≤ ((B.lower i - 2 * kappa) / B.mass i)^2 * (1-e)
  gaps : ∀ i j, i < j → ((B.upper i + 2 * kappa) / B.mass i)^2 * (1+e) +
    B.distance / 2 ≤ ((B.lower j - 2 * kappa) / B.mass j)^2 * (1-e)

theorem enlarge (B : AMDBox n) (hB : B.Admissible) :
    ∃ kappa e A, EnlargedData B kappa e A := sorry

theorem sec_domain_chart_facts {m : Fin n → ℝ} (hm : ∀ i, 0 < m i)
    {w : Phase (n + n)} (hw : w ∈ poincareProdDom n) :
    ProgradeElliptic m (poincareProd m 1 w) ∧
    (∀ i, keplerAction m (poincareProd m 1 w) i = fast w.2 i ∧
      keplerAxis m (poincareProd m 1 w) i = fast w.2 i ^ 2 / m i ^ 2 ∧
      planeCross (bodyVector (poincareProd m 1 w).1 i)
        (bodyVector (poincareProd m 1 w).2 i) =
        fast w.2 i - ((slow w.1 i)^2 + (slow w.2 i)^2) / 2) ∧
    physicalAMD m (poincareProd m 1 w) = chartAMD w := sorry

theorem real_domain (B : AMDBox n) (hB : B.Admissible) {kappa e A : ℝ}
    (hd : EnlargedData B kappa e A) :
    enlargedCylinder B kappa A ⊆ chartSafe B.mass ∧
    ∀ w ∈ enlargedCylinder B kappa A,
      (∀ i,
        planeLength (keplerEccVector B.mass (poincareProd B.mass 1 w) i) < e ∧
        B.distance / 2 ≤ planeLength (bodyVector (poincareProd B.mass 1 w).1 i)) ∧
      ∀ i j, i ≠ j → B.distance / 2 ≤
        planeLength (bodyVector (poincareProd B.mass 1 w).1 i -
          bodyVector (poincareProd B.mass 1 w).1 j) := sorry

theorem original_cylinder_subset (B : AMDBox n) (hB : B.Admissible) {kappa e A : ℝ}
    (hd : EnlargedData B kappa e A) :
    {w : Phase (n+n) | (∀ i, B.lower i ≤ fast w.2 i ∧ fast w.2 i ≤ B.upper i) ∧
      chartAMD w ≤ B.outerAMD} ⊆ enlargedCylinder B kappa A := sorry

def planetaryKeplerC (m : Fin n → ℝ) (I : Fin n → ℂ) : ℂ :=
  -∑ i, (m i : ℂ)^3 / (2 * I i ^ 2)

theorem h_data (hn : 2 ≤ n) (B : AMDBox n) (hB : B.Admissible)
    {kappa e A rho : ℝ} (hd : EnlargedData B kappa e A)
    (hrho : 0 < rho) (hrk : rho ≤ kappa) :
    (∀ I ∈ fastBox B kappa, Metric.closedBall I rho ⊆ fastBox B (2*kappa)) ∧
    ∃ g v M : ℝ,
      (∀ i, g ≤ B.mass i^3 / (B.upper i + 3*kappa)^3) ∧
      (∃ i, g = B.mass i^3 / (B.upper i + 3*kappa)^3) ∧
      (∀ i, v ≤ 3 * B.mass i^3 / (B.upper i + 3*kappa)^4) ∧
      (∃ i, v = 3 * B.mass i^3 / (B.upper i + 3*kappa)^4) ∧
      M = ∑ i, 3 * B.mass i^3 / (5 * B.lower i / 8)^4 ∧
      0 < g ∧ 0 < v ∧ 0 < M ∧
      DifferentiableOn ℂ (planetaryKeplerC B.mass) (KAM.actionNbhd (fastBox B (2*kappa)) rho) ∧
      ContDiffOn ℂ 2 (planetaryKeplerC B.mass) (KAM.actionNbhd (fastBox B (2*kappa)) rho) ∧
      (∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ KAM.actionNbhd (fastBox B (2*kappa)) rho →
        (planetaryKeplerC B.mass (fun i => (I i : ℂ))).im = 0) ∧
      (∀ z ∈ KAM.actionNbhd (fastBox B (2*kappa)) rho,
        ‖fderiv ℂ (fderiv ℂ (planetaryKeplerC B.mass)) z‖ ≤ M) ∧
      KAM.Nekhoroshev.HasDefiniteFastPart (fastBox B (2*kappa)) rho g v (planetaryKeplerC B.mass) ∧
      KAM.Nekhoroshev.HasDefiniteFastPart (fastBox B (2*kappa)) rho g v (-planetaryKeplerC B.mass) ∧
      ∀ z ∈ KAM.actionNbhd (fastBox B (2*kappa)) rho, ∀ i,
        0 < 5 * B.lower i / 8 ∧
        5 * B.lower i / 8 ≤ B.lower i - 3*kappa ∧
        B.lower i - 3*kappa ≤ (z i).re := sorry

/-- Inherited pc-share/ho-hol gap: analytic regularity, not merely smoothness. -/
theorem chart_perturbation_analytic (m : Fin n → ℝ) (hm : ∀ i, 0 < m i) :
    AnalyticOnNhd ℝ (fun w => fMov 1 1 m (poincareProd m 1 w)) (chartSafe m) := sorry

def periodicOrbitSet (K : Set (Phase (n+n))) : Set (Phase (n+n)) :=
  {w | ∃ k : Fin n → ℤ, ∃ x ∈ K, w = x + fastShift k}
def complexTube (K : Set (Phase (n+n))) (r : ℝ) :
    Set ((Fin (n+n) → ℂ) × (Fin (n+n) → ℂ)) :=
  {z | ∃ x ∈ periodicOrbitSet K, ‖z - KAM.Nekhoroshev.complexifyPhase x‖ < r}

theorem tube {W K : Set (Phase (n+n))} (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hWp : ∀ k : Fin n → ℤ, ∀ w, w ∈ W ↔ w + fastShift k ∈ W)
    {f : Phase (n+n) → ℝ} (hf : AnalyticOnNhd ℝ f W)
    (hfp : ∀ k : Fin n → ℤ, ∀ w ∈ W, f (w + fastShift k) = f w) :
    ∃ r : ℝ, 0 < r ∧ ∃ fc : ((Fin (n+n) → ℂ) × (Fin (n+n) → ℂ)) → ℂ,
      DifferentiableOn ℂ fc (complexTube K r) ∧
      (∀ w : Phase (n+n), KAM.Nekhoroshev.complexifyPhase w ∈ complexTube K r →
        w ∈ W ∧ fc (KAM.Nekhoroshev.complexifyPhase w) = (f w : ℂ)) ∧
      ∀ k : Fin n → ℤ, ∀ z ∈ complexTube K r,
        z + KAM.Nekhoroshev.complexifyPhase (fastShift k) ∈ complexTube K r ∧
        fc (z + KAM.Nekhoroshev.complexifyPhase (fastShift k)) = fc z := sorry

theorem perturbation (B : AMDBox n) (hB : B.Admissible) {kappa e A : ℝ}
    (hd : EnlargedData B kappa e A) :
    ∃ rho B0 : ℝ, 0 < rho ∧ rho ≤ kappa ∧ 1 ≤ B0 ∧
      ∃ P : ((Fin (n+n) → ℂ) × (Fin (n+n) → ℂ)) → ℂ,
        KAM.Nekhoroshev.IsPartialPerturbation (fastBox B (2*kappa)) (slowBall n A) rho P ∧
        KAM.Nekhoroshev.IsPartialPerturbation (fastBox B (2*kappa)) (slowBall n A) rho (-P) ∧
        ∀ w ∈ workingCylinder B kappa A,
          P (KAM.Nekhoroshev.complexifyPhase w) =
            ((fMov 1 1 B.mass (poincareProd B.mass 1 w) / B0 : ℝ) : ℂ) := sorry

/-- General fast-block periodic compact-cylinder lemma; existing angleShift is period one. -/
theorem uniform_data {W Q : Set (Phase (n+n))} (hW : IsOpen W)
    {F : Phase (n+n) → Phase (n+n)} (hF : ContDiffOn ℝ 1 F W)
    (hWp : ∀ k : Fin n → ℤ, ∀ w, w ∈ W ↔ w + fastShift k ∈ W)
    (hFp : ∀ k : Fin n → ℤ, ∀ w ∈ W, F (w + fastShift k) = F w)
    (hQ : IsCompact Q) (hQ0 : ∀ w ∈ Q, fast w.1 = 0)
    (hQW : ∀ w : Phase (n+n),
      assemble (fast w.2) 0 (slow w.2) (slow w.1) ∈ Q → w ∈ W) :
    ∃ (delta M : ℝ) (L : ℝ≥0), KAM.ODE.UniformData F W
      {w | assemble (fast w.2) 0 (slow w.2) (slow w.1) ∈ Q} delta M L ∧ delta ≤ Real.pi := sorry

theorem lift (B : AMDBox n) (hB : B.Admissible) (mu l r : ℝ)
    (hl : l ≤ 0) (hr : 0 ≤ r) {z : ℝ → Phase (n*2)}
    (hz : IsMovingSolutionOn B.mass mu (Icc l r) z) (hout : ∀ t ∈ Icc l r, z t ∈ amdOuter B) :
    ∃ y : ℝ → Phase (n+n), ∀ t ∈ Icc l r,
      y t ∈ chartSafe B.mass ∧ poincareProd B.mass 1 (y t) = z t ∧
      HasDerivAt y (KAM.hamiltonianVectorField
        (fun w => movingHamiltonian 1 1 B.mass mu (poincareProd B.mass 1 w)) (y t)) t ∧
      (∀ i, fast (y t).2 i = keplerAction B.mass (z t) i) ∧
      chartAMD (y t) = physicalAMD B.mass (z t) := sorry

theorem hnu (B : AMDBox n) (hB : B.Admissible) {kappa e A : ℝ}
    (hd : EnlargedData B kappa e A) {B0 mu : ℝ} (hB0 : 0 < B0)
    {P : ((Fin (n+n) → ℂ) × (Fin (n+n) → ℂ)) → ℂ}
    (hP : ∀ w ∈ workingCylinder B kappa A, P (KAM.Nekhoroshev.complexifyPhase w) =
      ((fMov 1 1 B.mass (poincareProd B.mass 1 w) / B0 : ℝ) : ℂ)) :
    ∀ w ∈ workingCylinder B kappa A,
      degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC B.mass))
        (fun _ x => (P (KAM.Nekhoroshev.complexifyPhase x)).re) (B0*mu) w =
        movingHamiltonian 1 1 B.mass mu (poincareProd B.mass 1 w) := sorry

theorem stopped (hn : 2 ≤ n) (B : AMDBox n) (hB : B.Admissible) :
    ∃ B0 nu0 : ℝ, 1 ≤ B0 ∧ 0 < nu0 ∧ nu0 ≤ 1 ∧
      ∀ mu T delta : ℝ, 0 < mu → B0 * mu < nu0 → 0 < T → 0 < delta →
        T ≤ (B0*mu)⁻¹ * Real.exp ((B0*mu)^(-planetaryTimeExponent n)) →
        (B0*mu)^planetaryDriftExponent n / 2 ≤ delta →
        ∀ z0 : Phase (n*2), StoppedActionBound B mu T delta z0 := sorry

/-! ## Secular box: exact frozen objects, no appeal to a physical full-system theorem. -/
def sb_sdef (saturn : ℝ) : Set (Phase (2+2)) :=
  {w | (∀ i, 0 < fast w.2 i ∧ 50 * secularGamma w i < fast w.2 i) ∧
    51/10 < secularAxis (jupiterSaturnWeights saturn) w 0 ∧
    secularAxis (jupiterSaturnWeights saturn) w 0 < 53/10 ∧
    47/5 < secularAxis (jupiterSaturnWeights saturn) w 1 ∧
    secularAxis (jupiterSaturnWeights saturn) w 1 < 97/10}
def secularRotation (theta : ℝ) (w : Phase (2+2)) : Phase (2+2) :=
  assemble (fast w.2) (fast w.1)
    (fun i => (KAM.Kepler.rot theta ![slow w.1 i, slow w.2 i]) 1)
    (fun i => (KAM.Kepler.rot theta ![slow w.1 i, slow w.2 i]) 0)
def sb_omega (m : Fin 2 → ℝ) (mu : ℝ) (w : Phase (2+2)) : Fin 2 → ℝ :=
  fun i => fderiv ℝ (exactSecularHamiltonian m mu) w (0, Fin.append (Pi.single i 1) 0)
def reducedSecularH (m : Fin 2 → ℝ) (mu : ℝ) (I : Fin 2 → ℝ) (y : Phase 2) : ℝ :=
  exactSecularHamiltonian m mu (assemble I 0 y.2 y.1)

theorem sb_numerics :
    (29/100 : ℝ) ≤ 476/1591 ∧ (476/1591 : ℝ) ≤ 31/100 ∧
    (3 : ℝ)*1591 = 4773 ∧ (4773/5000000 : ℝ)*(476/1591) = 357/1250000 ∧
    (87/100 : ℝ)^2 < 103/20 ∧ (21/4 : ℝ) < (23/10)^2 ∧
    (87/100 : ℝ)^2 < (29/100)^2*(189/20) ∧
    (31/100 : ℝ)^2*(193/20) < (97/100)^2 ∧
    (99819/100000 : ℝ)^2 < 1-(3/50)^2 ∧
    (49877/50000 : ℝ)^2 < 1-(7/100)^2 ∧
    (23/10 : ℝ)*(181/100000)+(97/100)*(123/50000) = 16373/2500000 ∧
    (16373/2500000 : ℝ)/(87/100) < 19/2500 ∧
    (1 : ℝ)-(2481/2500)^2 = 94639/6250000 ∧
    (94639/6250000 : ℝ) < (3/20)^2 ∧
    (51/10 : ℝ) < 103/20 ∧ (21/4 : ℝ) < 53/10 ∧
    (47/5 : ℝ) < 189/20 ∧ (193/20 : ℝ) < 97/10 ∧
    (50 : ℝ)*(16373/2500000) < 87/100 ∧
    (1 : ℝ)-(49/50)^2 = 99/2500 ∧ (99/2500 : ℝ) < (1/5)^2 ∧
    (53/10 : ℝ)*(6/5) < (47/5)*(4/5) ∧
    (103/20 : ℝ)*(17/20) = 1751/400 ∧ (193/20 : ℝ)*(23/20) = 4439/400 ∧
    (189/20 : ℝ)*(17/20)-(21/4)*(23/20) = 399/200 ∧
    (21/4 : ℝ)*(23/20) = 483/80 ∧ (483/80 : ℝ) ≤ 4439/400 ∧
    (1751/400 : ℝ) ≤ (189/20)*(17/20) ∧ (399/200 : ℝ) ≤ 1751/400 ∧
    (4439/400 : ℝ)+(483/80) ≤ 4439/200 ∧
    (1 : ℝ)-(3/20)^2 < (989/1000)^2 ∧
    (87/100 : ℝ)*(11/1000) = 957/100000 ∧
    (16373/2500000 : ℝ) < 957/100000 := sorry

theorem sb_chart (m : Fin 2 → ℝ) (hm : ∀ i, 0 < m i) {w : Phase (2+2)}
    (hw : ∀ i, 0 < fast w.2 i ∧ 0 ≤ secularGamma w i ∧ secularGamma w i < fast w.2 i) :
    ∀ i, 0 < ((1 - secularGamma w i / (2 * fast w.2 i)) / fast w.2 i) ∧
      0 < secularRoot w i ∧ secularRoot w i ≤ 1 ∧
      secularRoot w i = Real.sqrt (1 - planeLength (secularEccVector w i)^2) ∧
      planeLength (secularEccVector w i)^2 = 1 - secularRoot w i ^ 2 ∧
      planeLength (secularEccVector w i) < 1 ∧
      secularGamma w i = fast w.2 i * (1 - secularRoot w i) ∧
      ∀ F : ℝ, 0 < longitudeJacobian w i F ∧
        1 - planeLength (secularEccVector w i) ≤ longitudeJacobian w i F ∧
        planeLength (ellipsePosition m w i F) = secularAxis m w i * longitudeJacobian w i F ∧
        secularAxis m w i * (1-planeLength (secularEccVector w i)) ≤ planeLength (ellipsePosition m w i F) ∧
        planeLength (ellipsePosition m w i F) ≤ secularAxis m w i * (1+planeLength (secularEccVector w i)) := sorry

theorem sb_cov (m : Fin 2 → ℝ) (w : Phase (2+2)) (theta : ℝ) :
    (∀ i, secularGamma (secularRotation theta w) i = secularGamma w i ∧
      secularEccVector (secularRotation theta w) i = KAM.Kepler.rot theta (secularEccVector w i)) ∧
    ∀ i F, longitudeJacobian (secularRotation theta w) i F = longitudeJacobian w i (F-theta) ∧
      ellipsePosition m (secularRotation theta w) i F =
        KAM.Kepler.rot theta (ellipsePosition m w i (F-theta)) ∧
      ellipseMomentum m (secularRotation theta w) i F =
        KAM.Kepler.rot theta (ellipseMomentum m w i (F-theta)) := sorry

theorem sb_s (saturn : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100)) :
    IsOpen (sb_sdef saturn) ∧ ∀ w ∈ sb_sdef saturn, ∀ F : Fin 2 → ℝ,
      (∀ i, (49/50 : ℝ) < secularRoot w i ∧
        planeLength (secularEccVector w i) < 1/5 ∧ (4/5 : ℝ) < longitudeJacobian w i (F i)) ∧
      NoCollision (ellipsePhase (jupiterSaturnWeights saturn) w F).1 := sorry

theorem sb_smooth_prop (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100)) :
    ContDiffOn ℝ ∞ (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) (sb_sdef saturn) ∧
    (∀ w ∈ sb_sdef saturn, SecularRegular (jupiterSaturnWeights saturn) mu w) ∧
    ∀ w : Phase (2+2), ∀ lam : Fin 2 → ℝ,
      exactSecularHamiltonian (jupiterSaturnWeights saturn) mu
        (assemble (fast w.2) lam (slow w.2) (slow w.1)) =
      exactSecularHamiltonian (jupiterSaturnWeights saturn) mu w := sorry

def explicitSecularIntegrand (m : Fin 2 → ℝ) (mu : ℝ)
    (w : Phase (2+2)) (F : Fin 2 → ℝ) : ℝ :=
  movingHamiltonian 1 1 m mu (ellipsePhase m w F) * ∏ i, longitudeJacobian w i (F i)
theorem secular_integrand_identity (m : Fin 2 → ℝ) (mu : ℝ)
    (w : Phase (2+2)) (F : Fin 2 → ℝ) :
    secularIntegrand m mu (assemble (fast w.2) F (slow w.2) (slow w.1)) =
      explicitSecularIntegrand m mu w F := sorry

theorem secular_integrand_smooth (saturn mu : ℝ)
    (hs : saturn ∈ Icc (29/100 : ℝ) (31/100)) :
    ContDiffOn ℝ ∞ (fun p : Phase (2+2) × (Fin 2 → ℝ) =>
      explicitSecularIntegrand (jupiterSaturnWeights saturn) mu p.1 p.2)
      (sb_sdef saturn ×ˢ univ) ∧
    ∀ w : Phase (2+2), ∀ F : Fin 2 → ℝ, ∀ i : Fin 2,
      explicitSecularIntegrand (jupiterSaturnWeights saturn) mu w (F + Pi.single i (2*Real.pi)) =
        explicitSecularIntegrand (jupiterSaturnWeights saturn) mu w F := sorry

theorem sb_rot (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    {w : Phase (2+2)} (hw : w ∈ sb_sdef saturn) (theta : ℝ) :
    secularRotation theta w ∈ sb_sdef saturn ∧
      exactSecularHamiltonian (jupiterSaturnWeights saturn) mu (secularRotation theta w) =
        exactSecularHamiltonian (jupiterSaturnWeights saturn) mu w := sorry

theorem sb_pred (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    (J : Set ℝ) (z : ℝ → Phase (2+2)) (hz : ∀ t ∈ J, z t ∈ sb_sdef saturn) :
    KAM.Iso.IsHamiltonianSolutionOn (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu)
      univ J z ↔ KAM.ODE.IsSolutionIn
        (KAM.hamiltonianVectorField (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu))
        (sb_sdef saturn) J z := sorry

theorem sb_field (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    {w : Phase (2+2)} (hw : w ∈ sb_sdef saturn) :
    fast (KAM.hamiltonianVectorField (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) w).2 = 0 ∧
    ∑ i, (slow w.1 i * slow
      (KAM.hamiltonianVectorField (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) w).1 i +
      slow w.2 i * slow
      (KAM.hamiltonianVectorField (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) w).2 i) = 0 := sorry

theorem secular_field_components (saturn mu : ℝ)
    (hs : saturn ∈ Icc (29/100 : ℝ) (31/100)) {w : Phase (2+2)} (hw : w ∈ sb_sdef saturn) :
    let H := exactSecularHamiltonian (jupiterSaturnWeights saturn) mu
    let h := reducedSecularH (jupiterSaturnWeights saturn) mu (fast w.2)
    fast (KAM.hamiltonianVectorField H w).1 = sb_omega (jupiterSaturnWeights saturn) mu w ∧
    (slow (KAM.hamiltonianVectorField H w).1, slow (KAM.hamiltonianVectorField H w).2) =
      KAM.hamiltonianVectorField h (slow w.1, slow w.2) := sorry

theorem sb_slow (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    {w0 : Phase (2+2)} (hw : w0 ∈ sb_sdef saturn)
    (hA : secularAMD w0 < (16373/2500000 : ℝ)) (hI : ∀ i, (87/100 : ℝ) < fast w0.2 i) :
    ∃ y : ℝ → Phase 2, y 0 = (slow w0.1, slow w0.2) ∧
      KAM.ODE.IsSolutionIn
        (KAM.hamiltonianVectorField (reducedSecularH (jupiterSaturnWeights saturn) mu (fast w0.2)))
        {y | assemble (fast w0.2) 0 y.2 y.1 ∈ sb_sdef saturn} univ y ∧
      ∀ t, secularAMD (assemble (fast w0.2) 0 (y t).2 (y t).1) = secularAMD w0 := sorry

theorem sb_global (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    {w0 : Phase (2+2)} (hw : w0 ∈ sb_sdef saturn)
    (hA : secularAMD w0 < (16373/2500000 : ℝ)) (hI : ∀ i, (87/100 : ℝ) < fast w0.2 i) :
    ∃ w : ℝ → Phase (2+2), w 0 = w0 ∧
      KAM.Iso.IsHamiltonianSolutionOn (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) univ univ w ∧
      ∀ t, w t ∈ sb_sdef saturn ∧ fast (w t).2 = fast w0.2 ∧ secularAMD (w t) = secularAMD w0 := sorry

/-- Stronger uniqueness: regularity of the competing curve is unnecessary. -/
theorem sb_unique (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    {w : ℝ → Phase (2+2)}
    (hw : KAM.Iso.IsHamiltonianSolutionOn (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) univ univ w)
    (hW : ∀ t, w t ∈ sb_sdef saturn)
    {U : Set ℝ} (hU : IsOpen U) (hUc : Convex ℝ U) (h0 : (0 : ℝ) ∈ U)
    {v : ℝ → Phase (2+2)} (hv0 : v 0 = w 0)
    (hv : KAM.Iso.IsHamiltonianSolutionOn (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) univ U v) :
    ∀ t ∈ U, v t = w t := sorry

/-- Exact frozen type, ordinary library assembly. -/
theorem amd {n : ℕ} (hn : 2 ≤ n) (B : AMDBox n) (hB : B.Admissible)
    (mu T delta : ℝ) (hmu : 0 < mu) (hT : 0 < T) (hdelta : 0 < delta)
    (hmargin : ∀ i, B.lower i + 2 * delta < B.innerLower i ∧
      B.innerUpper i + 2 * delta < B.upper i)
    (hAMD : B.initialAMD + 2 * (n : ℝ) * delta < B.outerAMD)
    (z0 : Phase (n * 2))
    (hz0 : z0 ∈ LowAMDRegion B.mass B.innerLower B.innerUpper B.initialAMD)
    (hstop : StoppedActionBound B mu T delta z0) :
    ∃ z : ℝ → Phase (n * 2), z 0 = z0 ∧ (IsMovingSolutionOn B.mass mu (Set.Icc (-T) T) z ∧
      MovingUniqueOn B.mass mu (Set.Icc (-T) T) z ∧
      IsNewtonSolutionOn (actualMasses 1 B.mass mu) (Set.Icc (-T) T)
        (fun t => barycentricPositions 1 B.mass mu (z t).1)
        (fun t => barycentricVelocities 1 B.mass mu (z t).2) ∧
      ∀ t ∈ (Set.Icc (-T) T),
        z t ∈ LowAMDRegion B.mass B.lower B.upper B.outerAMD ∧
        totalMomentum (z t) = totalMomentum (z 0) ∧
        (∀ i, planeLength (keplerEccVector B.mass (z t) i) < B.ecc ∧
          B.distance ≤ planeLength (bodyVector (z t).1 i) ∧
          planeLength (bodyVector (z t).1 i) ≤ B.radius) ∧
        PairBounds B.distance (2 * B.radius) (barycentricPositions 1 B.mass mu (z t).1)) ∧
      ∀ t ∈ Set.Icc (-T) T,
        physicalAMD B.mass (z t) ≤ B.initialAMD + (n : ℝ) * delta ∧
        ∀ i, |keplerAction B.mass (z t) i - keplerAction B.mass z0 i| ≤ delta := sorry

/-- Exact frozen type, ordinary library assembly. -/
theorem expsafe {n : ℕ} (hn : 2 ≤ n)
    (B : AMDBox n) (hB : B.Admissible) :
    ∃ muStar c C : ℝ, 0 < muStar ∧ 0 < c ∧ 0 < C ∧
      ∀ mu : ℝ, 0 < mu → mu < muStar →
      ∀ z0 ∈ LowAMDRegion B.mass B.innerLower B.innerUpper B.initialAMD,
      ∃ z : ℝ → Phase (n * 2), z 0 = z0 ∧
        (IsMovingSolutionOn B.mass mu (Set.Icc (-Real.exp (c * mu ^ (-planetaryTimeExponent n)))
                  (Real.exp (c * mu ^ (-planetaryTimeExponent n)))) z ∧ MovingUniqueOn B.mass mu
                    (Set.Icc (-Real.exp (c * mu ^ (-planetaryTimeExponent n)))
                  (Real.exp (c * mu ^ (-planetaryTimeExponent n)))) z ∧
        IsNewtonSolutionOn (actualMasses 1 B.mass mu) (Set.Icc (-Real.exp (c * mu ^
          (-planetaryTimeExponent n)))
                  (Real.exp (c * mu ^ (-planetaryTimeExponent n))))
          (fun t => barycentricPositions 1 B.mass mu (z t).1)
          (fun t => barycentricVelocities 1 B.mass mu (z t).2) ∧
        ∀ t ∈ (Set.Icc (-Real.exp (c * mu ^ (-planetaryTimeExponent n)))
                  (Real.exp (c * mu ^ (-planetaryTimeExponent n)))),
          z t ∈ LowAMDRegion B.mass B.lower B.upper B.outerAMD ∧
          totalMomentum (z t) = totalMomentum (z 0) ∧
          (∀ i, planeLength (keplerEccVector B.mass (z t) i) < B.ecc ∧
            B.distance ≤ planeLength (bodyVector (z t).1 i) ∧
            planeLength (bodyVector (z t).1 i) ≤ B.radius) ∧
          PairBounds B.distance (2 * B.radius) (barycentricPositions 1 B.mass mu (z t).1)) ∧
        ∀ t : ℝ, |t| ≤ Real.exp (c * mu ^ (-planetaryTimeExponent n)) →
          ∀ i, |keplerAxis B.mass (z t) i - keplerAxis B.mass z0 i| ≤
            C * mu ^ planetaryDriftExponent n := sorry

/-- Exact frozen type, ordinary library assembly. -/
theorem sb_safety (saturn mu : ℝ)
    (hsaturn : saturn ∈ Set.Icc (29 / 100 : ℝ) (31 / 100 : ℝ)) (hmu : 0 < mu)
    (w0 : Phase (2 + 2)) (hw0 : SecularInputBox saturn w0) :
    ∃ w : ℝ → Phase (2 + 2), w 0 = w0 ∧
      KAM.Iso.IsHamiltonianSolutionOn (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu)
        Set.univ Set.univ w ∧
      (∀ (U : Set ℝ) (v : ℝ → Phase (2 + 2)), IsOpen U → Convex ℝ U → 0 ∈ U →
        v 0 = w0 →
        KAM.Iso.IsHamiltonianSolutionOn
          (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) Set.univ U v →
        (∀ t ∈ U, SecularRegular (jupiterSaturnWeights saturn) mu (v t)) →
        ∀ t ∈ U, v t = w t) ∧
      ∀ t : ℝ,
        SecularRegular (jupiterSaturnWeights saturn) mu (w t) ∧
        fast (w t).2 = fast w0.2 ∧ secularAMD (w t) = secularAMD w0 ∧
        secularAMD (w t) < (16373 / 2500000 : ℝ) ∧
        (∀ i, planeLength (secularEccVector (w t) i) < (3 / 20 : ℝ)) ∧
        ∀ F : Fin 2 → ℝ,
          (∀ i, (1751 / 400 : ℝ) ≤
            planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) i (F i)) ∧
            planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) i (F i)) ≤
              (4439 / 400 : ℝ)) ∧
          (399 / 200 : ℝ) ≤
            planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) 1 (F 1)) -
            planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) 0 (F 0)) ∧
          PairBounds (399 / 200 : ℝ) (4439 / 200 : ℝ)
            (barycentricPositions 1 (jupiterSaturnWeights saturn) mu
              (ellipsePhase (jupiterSaturnWeights saturn) (w t) F).1) := sorry

/-- Exact frozen type, ordinary library assembly. -/
theorem sb_cited (w0 : Phase (2 + 2))
    (hw0 : SecularInputBox (476 / 1591 : ℝ) w0) :
    ∃ w : ℝ → Phase (2 + 2), w 0 = w0 ∧
      KAM.Iso.IsHamiltonianSolutionOn (exactSecularHamiltonian (jupiterSaturnWeights (476 / 1591 :
        ℝ)) (4773 / 5000000 : ℝ))
        Set.univ Set.univ w ∧
      (∀ (U : Set ℝ) (v : ℝ → Phase (2 + 2)), IsOpen U → Convex ℝ U → 0 ∈ U →
        v 0 = w0 →
        KAM.Iso.IsHamiltonianSolutionOn
          (exactSecularHamiltonian (jupiterSaturnWeights (476 / 1591 : ℝ)) (4773 / 5000000 : ℝ))
            Set.univ U v →
        (∀ t ∈ U, SecularRegular (jupiterSaturnWeights (476 / 1591 : ℝ)) (4773 / 5000000 : ℝ) (v t))
          →
        ∀ t ∈ U, v t = w t) ∧
      ∀ t : ℝ,
        SecularRegular (jupiterSaturnWeights (476 / 1591 : ℝ)) (4773 / 5000000 : ℝ) (w t) ∧
        fast (w t).2 = fast w0.2 ∧ secularAMD (w t) = secularAMD w0 ∧
        secularAMD (w t) < (16373 / 2500000 : ℝ) ∧
        (∀ i, planeLength (secularEccVector (w t) i) < (3 / 20 : ℝ)) ∧
        ∀ F : Fin 2 → ℝ,
          (∀ i, (1751 / 400 : ℝ) ≤
            planeLength (ellipsePosition (jupiterSaturnWeights (476 / 1591 : ℝ)) (w t) i (F i)) ∧
            planeLength (ellipsePosition (jupiterSaturnWeights (476 / 1591 : ℝ)) (w t) i (F i)) ≤
              (4439 / 400 : ℝ)) ∧
          (399 / 200 : ℝ) ≤
            planeLength (ellipsePosition (jupiterSaturnWeights (476 / 1591 : ℝ)) (w t) 1 (F 1)) -
            planeLength (ellipsePosition (jupiterSaturnWeights (476 / 1591 : ℝ)) (w t) 0 (F 0)) ∧
          PairBounds (399 / 200 : ℝ) (4439 / 200 : ℝ)
            (barycentricPositions 1 (jupiterSaturnWeights (476 / 1591 : ℝ)) (4773 / 5000000 : ℝ)
              (ellipsePhase (jupiterSaturnWeights (476 / 1591 : ℝ)) (w t) F).1) := sorry

end KAM.Planetary
namespace KAM.Provider.Planetary
open KAM.Planetary

/-- Quarantined provider signature; exact frozen telescope. -/
theorem amdConfinement {n : ℕ} (hn : 2 ≤ n) (B : AMDBox n) (hB : B.Admissible)
    (mu T delta : ℝ) (hmu : 0 < mu) (hT : 0 < T) (hdelta : 0 < delta)
    (hmargin : ∀ i, B.lower i + 2 * delta < B.innerLower i ∧
      B.innerUpper i + 2 * delta < B.upper i)
    (hAMD : B.initialAMD + 2 * (n : ℝ) * delta < B.outerAMD)
    (z0 : Phase (n * 2))
    (hz0 : z0 ∈ LowAMDRegion B.mass B.innerLower B.innerUpper B.initialAMD)
    (hstop : StoppedActionBound B mu T delta z0) :
    ∃ z : ℝ → Phase (n * 2), z 0 = z0 ∧ (IsMovingSolutionOn B.mass mu (Set.Icc (-T) T) z ∧
      MovingUniqueOn B.mass mu (Set.Icc (-T) T) z ∧
      IsNewtonSolutionOn (actualMasses 1 B.mass mu) (Set.Icc (-T) T)
        (fun t => barycentricPositions 1 B.mass mu (z t).1)
        (fun t => barycentricVelocities 1 B.mass mu (z t).2) ∧
      ∀ t ∈ (Set.Icc (-T) T),
        z t ∈ LowAMDRegion B.mass B.lower B.upper B.outerAMD ∧
        totalMomentum (z t) = totalMomentum (z 0) ∧
        (∀ i, planeLength (keplerEccVector B.mass (z t) i) < B.ecc ∧
          B.distance ≤ planeLength (bodyVector (z t).1 i) ∧
          planeLength (bodyVector (z t).1 i) ≤ B.radius) ∧
        PairBounds B.distance (2 * B.radius) (barycentricPositions 1 B.mass mu (z t).1)) ∧
      ∀ t ∈ Set.Icc (-T) T,
        physicalAMD B.mass (z t) ≤ B.initialAMD + (n : ℝ) * delta ∧
        ∀ i, |keplerAction B.mass (z t) i - keplerAction B.mass z0 i| ≤ delta := sorry

/-- Quarantined provider signature; exact frozen telescope. -/
theorem planetaryExponentialSafety {n : ℕ} (hn : 2 ≤ n)
    (B : AMDBox n) (hB : B.Admissible) :
    ∃ muStar c C : ℝ, 0 < muStar ∧ 0 < c ∧ 0 < C ∧
      ∀ mu : ℝ, 0 < mu → mu < muStar →
      ∀ z0 ∈ LowAMDRegion B.mass B.innerLower B.innerUpper B.initialAMD,
      ∃ z : ℝ → Phase (n * 2), z 0 = z0 ∧
        (IsMovingSolutionOn B.mass mu (Set.Icc (-Real.exp (c * mu ^ (-planetaryTimeExponent n)))
                  (Real.exp (c * mu ^ (-planetaryTimeExponent n)))) z ∧ MovingUniqueOn B.mass mu
                    (Set.Icc (-Real.exp (c * mu ^ (-planetaryTimeExponent n)))
                  (Real.exp (c * mu ^ (-planetaryTimeExponent n)))) z ∧
        IsNewtonSolutionOn (actualMasses 1 B.mass mu) (Set.Icc (-Real.exp (c * mu ^
          (-planetaryTimeExponent n)))
                  (Real.exp (c * mu ^ (-planetaryTimeExponent n))))
          (fun t => barycentricPositions 1 B.mass mu (z t).1)
          (fun t => barycentricVelocities 1 B.mass mu (z t).2) ∧
        ∀ t ∈ (Set.Icc (-Real.exp (c * mu ^ (-planetaryTimeExponent n)))
                  (Real.exp (c * mu ^ (-planetaryTimeExponent n)))),
          z t ∈ LowAMDRegion B.mass B.lower B.upper B.outerAMD ∧
          totalMomentum (z t) = totalMomentum (z 0) ∧
          (∀ i, planeLength (keplerEccVector B.mass (z t) i) < B.ecc ∧
            B.distance ≤ planeLength (bodyVector (z t).1 i) ∧
            planeLength (bodyVector (z t).1 i) ≤ B.radius) ∧
          PairBounds B.distance (2 * B.radius) (barycentricPositions 1 B.mass mu (z t).1)) ∧
        ∀ t : ℝ, |t| ≤ Real.exp (c * mu ^ (-planetaryTimeExponent n)) →
          ∀ i, |keplerAxis B.mass (z t) i - keplerAxis B.mass z0 i| ≤
            C * mu ^ planetaryDriftExponent n := sorry

/-- Quarantined provider signature; exact frozen telescope. -/
theorem secularBoxSafety (saturn mu : ℝ)
    (hsaturn : saturn ∈ Set.Icc (29 / 100 : ℝ) (31 / 100 : ℝ)) (hmu : 0 < mu)
    (w0 : Phase (2 + 2)) (hw0 : SecularInputBox saturn w0) :
    ∃ w : ℝ → Phase (2 + 2), w 0 = w0 ∧
      KAM.Iso.IsHamiltonianSolutionOn (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu)
        Set.univ Set.univ w ∧
      (∀ (U : Set ℝ) (v : ℝ → Phase (2 + 2)), IsOpen U → Convex ℝ U → 0 ∈ U →
        v 0 = w0 →
        KAM.Iso.IsHamiltonianSolutionOn
          (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) Set.univ U v →
        (∀ t ∈ U, SecularRegular (jupiterSaturnWeights saturn) mu (v t)) →
        ∀ t ∈ U, v t = w t) ∧
      ∀ t : ℝ,
        SecularRegular (jupiterSaturnWeights saturn) mu (w t) ∧
        fast (w t).2 = fast w0.2 ∧ secularAMD (w t) = secularAMD w0 ∧
        secularAMD (w t) < (16373 / 2500000 : ℝ) ∧
        (∀ i, planeLength (secularEccVector (w t) i) < (3 / 20 : ℝ)) ∧
        ∀ F : Fin 2 → ℝ,
          (∀ i, (1751 / 400 : ℝ) ≤
            planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) i (F i)) ∧
            planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) i (F i)) ≤
              (4439 / 400 : ℝ)) ∧
          (399 / 200 : ℝ) ≤
            planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) 1 (F 1)) -
            planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) 0 (F 0)) ∧
          PairBounds (399 / 200 : ℝ) (4439 / 200 : ℝ)
            (barycentricPositions 1 (jupiterSaturnWeights saturn) mu
              (ellipsePhase (jupiterSaturnWeights saturn) (w t) F).1) := sorry

/-- Quarantined provider signature; exact frozen telescope. -/
theorem secularBoxAtCitedMasses (w0 : Phase (2 + 2))
    (hw0 : SecularInputBox (476 / 1591 : ℝ) w0) :
    ∃ w : ℝ → Phase (2 + 2), w 0 = w0 ∧
      KAM.Iso.IsHamiltonianSolutionOn (exactSecularHamiltonian (jupiterSaturnWeights (476 / 1591 :
        ℝ)) (4773 / 5000000 : ℝ))
        Set.univ Set.univ w ∧
      (∀ (U : Set ℝ) (v : ℝ → Phase (2 + 2)), IsOpen U → Convex ℝ U → 0 ∈ U →
        v 0 = w0 →
        KAM.Iso.IsHamiltonianSolutionOn
          (exactSecularHamiltonian (jupiterSaturnWeights (476 / 1591 : ℝ)) (4773 / 5000000 : ℝ))
            Set.univ U v →
        (∀ t ∈ U, SecularRegular (jupiterSaturnWeights (476 / 1591 : ℝ)) (4773 / 5000000 : ℝ) (v t))
          →
        ∀ t ∈ U, v t = w t) ∧
      ∀ t : ℝ,
        SecularRegular (jupiterSaturnWeights (476 / 1591 : ℝ)) (4773 / 5000000 : ℝ) (w t) ∧
        fast (w t).2 = fast w0.2 ∧ secularAMD (w t) = secularAMD w0 ∧
        secularAMD (w t) < (16373 / 2500000 : ℝ) ∧
        (∀ i, planeLength (secularEccVector (w t) i) < (3 / 20 : ℝ)) ∧
        ∀ F : Fin 2 → ℝ,
          (∀ i, (1751 / 400 : ℝ) ≤
            planeLength (ellipsePosition (jupiterSaturnWeights (476 / 1591 : ℝ)) (w t) i (F i)) ∧
            planeLength (ellipsePosition (jupiterSaturnWeights (476 / 1591 : ℝ)) (w t) i (F i)) ≤
              (4439 / 400 : ℝ)) ∧
          (399 / 200 : ℝ) ≤
            planeLength (ellipsePosition (jupiterSaturnWeights (476 / 1591 : ℝ)) (w t) 1 (F 1)) -
            planeLength (ellipsePosition (jupiterSaturnWeights (476 / 1591 : ℝ)) (w t) 0 (F 0)) ∧
          PairBounds (399 / 200 : ℝ) (4439 / 200 : ℝ)
            (barycentricPositions 1 (jupiterSaturnWeights (476 / 1591 : ℝ)) (4773 / 5000000 : ℝ)
              (ellipsePhase (jupiterSaturnWeights (476 / 1591 : ℝ)) (w t) F).1) := sorry

end KAM.Provider.Planetary

```
