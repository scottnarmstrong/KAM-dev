# P11A Lean design audit 1

Overall verdict: **FAIL**.

The draft elaborates, and I found no counterexample to its weak-measure estimates or maximal-step estimates. It nevertheless fails the requested signature-fidelity gate: domain-local source premises become global premises (F1), preparation loses advertised derivative/size conclusions (F2), and several source-mapped exports omit clauses (F3–F5). These are design-contract findings, not claims that P-FIXED is false. Do not launch provers on the affected signatures unchanged.

## Scope, authority and immutable inputs

Independent tier-2, refute-first audit under `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-design.md`, the designer's handoff, and the common/P11A design briefs. Permission envelope: only this report persists as a new repository artifact; the explicitly requested signature copy and temporary ABI probes are the scratch exceptions. No commits, source repairs, frozen edits, manifest edits, or provider work.

Snapshot **v1**: HEAD `3dd384e6d23d2b32de6cbb7d4f6549dcd6c68e9a`; branch `inp-design-p11a`; comparison branch `inp` resolved to `29dbfb0f19abb6c634f7ce97adf459363f8ba243` during the audit. `git diff inp...HEAD` consists of the single 2142-line design addition. The source files retain the designer's pinned hashes.

| Input | SHA-256 |
|---|---|
| `docs/tracks/P/design/P11A-LEAN-DESIGN.md` | `4bd71abdefcffdd1b6aeaf428b3c16a112b939e40f0b575eb3f4cc4d3f68f968` |
| `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` | `40f6b495348ae7b10bf06bf8837bba7433b1bb648f98d17602eb780904690983` |
| `blueprint-P/parts/p11-cp09-preparation.tex` | `4c0e2dfefb50b1e06581e069a55846d25e0e4697a8826514ac699bbb83efb41f` |
| `blueprint-P/parts/p11a1-weak-measure.tex` | `66b5ce26db59b57dbf934938a7bae2fead6b6ff4c7c9d420d33b9582e272bab5` |
| `blueprint-P/parts/p11a2-cutoff-step.tex` | `990694a832aa02dca0138c5cbb3bab842984583f4ca92576479eff04786ed3ec` |
| `docs/graph/P/packets/P-p11.nodes.md` | `067fa835864b522d663c83ac1255f360a5a550e565662d651433d4b1786ad138` |
| `docs/graph/P/packets/P-p11a12.nodes.md` | `2c44ac33bbbf00f297fcbbd7e3270fa464d3da684aba89360e703958d45f86f7` |

The signatures have 1316 lines, **158 named declarations, including 58 theorem signatures**. Appendix A is byte-identical to the supplied signatures. The mapping table contains 164 scoped graph-node rows; that count includes local proof obligations and standing/external records, rather than 164 exported theorems. Graph records were checked against the actual packet files; the global review is at `/root/code/KAM-inp/docs/graph/P/reviews/GLOBAL-review.md`.

The checks compare premises, quantifier order, constant dependencies, both tensor gauges, period-one factors, frozen objects and actual consumers. Each finding below survived a separate adversarial reconsideration: I specifically looked for named companions, definitional consequences, valid restriction/extension arguments and the registry's local obligations before accepting it. Suggested repairs are proposals, not applied or certified implementations.

## Findings

### F1 — Major: total-function hypotheses constrain values outside the source domain

**Anchors (v1 signatures):** `homological_maximal` L370/L384; `homological_maximal_real` L1218; `homological_maximal_param` L1233; `aniso_bracket` L966–967; `aniso_avg` L980. Source: `bpP:p11a:homological-maximal`, p11a2 L173–185, and `bpP:p11:aniso-bracket` / `aniso-avg`, p11 L120–138.

The draft requires `hpoly : ∀ z, truncate T P z = P z` and requires rectangular inputs to satisfy `∀ z, ∀ i, f (...) = f z`. In the source these properties hold on the declared open parameter/action domain. The values of the total Lean function at parameters outside that domain, or at angles outside the strip, are unconstrained. The uniqueness clause likewise restricts competitors globally instead of only over B.

**Refutation check:** a good source function can be altered at a point outside B (for `hpoly`) or outside the strip (for periodicity), without changing any source hypothesis or conclusion. The draft's global premise can then fail. This is not repaired by openness, weighted summability, or local holomorphy. A proved domain-preserving periodic-extension adapter could repair applications, but no such adapter is in the package contracts, and the design brief expressly forbids extra source premises. The preparation specifications constrain periodicity on their stated domains; they do not constrain `f2` outside them, as the current `aniso_avg.hp` requires.

**Fix:** restrict each polynomial assertion to `Set.univ ×ˢ B` (or the corresponding parameter tube), restrict periodicity to the function's own strip/action domain, and restrict the polynomial condition on uniqueness competitors in the same way. Keep the explicit finite-sum generator. Full corrected theorem signatures appear in the repair appendix; no new premise is added.

### F2 — Major: prepared-system outputs do not deliver the advertised admissible datum

**Anchors:** `P11PreparedSpec` L1149–1157, `prepared` L1162–1168, `data_star` L1287–1291; design registry L386 and L412. Source: `bpP:p11:prepared` p11 L196–204 and `bpP:p11:data-star` L243–245. Actual consumer: `bpP:p11a:weak-kam-quantitative`, p11a5 L73–79, especially (A4).

The source's unscaled J estimate holds for **all** `‖J-J0‖ < s2/4` and normalized slow actions of size `< 5/4`. The signature replaces that with `‖J-J0‖ ≤ eps/2` and normalized slow actions `≤ 1/2`. These are smaller sets: `5*eps ≤ s2` gives `eps/2 < s2/4`. The retained estimate is useful for the amount argument, but is a weaker conclusion than the source statement, contrary to the audit brief. It is an unlisted departure.

Prepared(d) also promises a uniform vector-frequency diagonal-jet bound `M0*`, including order zero. The signature exports only the **scalar squared-family derivatives of positive order**. `data_star` exports compactness, volume, diameter and exponent arithmetic, but no frequency-size bound, admissibility of the prepared Hamiltonian, amount smallness or assembled datum. The registry explicitly says that `data_star` supplies (A1)–(A4) and the epsilon-independent fixed entries; its actual type does not.

**Refutation check:** the positive-order scalar derivative bound is invariant under adding a constant to a scalar family and cannot itself bound its zeroth jet. A max-norm bound on W plus the Hessian bound does not supply all derivatives through mu with the promised named `M0*`. Higher-order Cauchy estimates may prove the missing bound from the earlier analytic specifications, but that is additional work which the promised prepared/datum exports do not expose. The prose statement “the registry remains binding” does not make the missing facts accessible through the theorem's type.

**Fix:** restore the full unscaled domain and bind `checkW` there to the actual slow-stage derivatives; export a uniform `M0*` before nu and epsilon, a vector `p11JetBound` through mu, and an actual datum assembly theorem. Preserve the existing stronger domain of holomorphy of N/P, the amount `(beta_J/2)*eps^(mu+2)`, and the lower-budget direction. The repair appendix gives a strengthened output predicate and datum signature using the existing carriers. The still-pending KAM budget API must consume this datum through its exact reconciled type; do not invent an assumed admissibility field.

### F3 — Major: `polar_avg` does not export source clause (d)

**Anchors:** signature L935–947; design registry L368; source `bpP:p11:polar-avg`, p11 L155–163. Source consumer `stepP:p11:as-osc`, p11 L181, explicitly invokes “(b),(d)”.

The exported theorem gives a separate existential extension AG for each G, its bounds, its agreement with the raw polar integral, and the vanishing-order estimate. It contains no linearity statement and neither normalization `A(C)=C` nor `A((x_j^2+y_j^2)/2)=rho_j/(2*pi)`. No companion signature supplies them. These are substantive normalization clauses, including the period-one action factor.

**Refutation check:** agreement on the positive-real action region plus holomorphy implies uniqueness of the germ and allows these properties to be proved. Thus this is an incomplete exported contract, not a claim that the chosen extension is mathematically nonunique. A proof-local calculation in `polar_avg` does not export the clause its consumer cites.

**Fix:** retain the present extension lemma and add the exact linearity, normalization and extension-uniqueness companions in the repair appendix, or include equivalent conclusions in `polar_avg`. Their combination recovers linearity of the extension on its analytic domain without claiming that the raw, totalized integral is linear on arbitrary nonintegrable functions.

### F4 — Major: the rectangular field estimate is absent from its source-mapped signature

**Anchors:** `aniso_bracket` L959–970; registry L356–361. Source `bpP:p11:aniso-bracket`, p11 L120–128; consumer `stepP:p11:aa-same`, p11 L140, replacement (R2).

The source concludes both the weighted bracket bound and the anisotropic vector-field bound with different action weights rho1/rho2. The Lean theorem exports only the bracket bound. There is no companion field-estimate signature. The rectangular flow adapter requires exactly this field bound; the maximal-step affine flow does not substitute for a general rectangular generator.

**Refutation check:** the reuse table and package P3/P4 acknowledge the field estimate in prose, but no typed companion appears among the 158 declarations. This is not an objection to proving the original rectangular theorem: it is an omission in the signatures provers are instructed to prove exactly. Add the field companion below, using the frozen complex Hamiltonian field and the existing Pi norms. This repairs the missing clause independently of F1's premise repair.

### F5 — Moderate: `chart_scaling` covers only the amount clause of its advertised source lemma

**Anchors:** signature L1184–1189; source `bpP:p11a:chart-scaling`, p11a1 L201–212. Consumers are named in p11a1's final paragraph and p11a5's budget/chart discussion.

The signature exports only the amount inequality (a). It does not export tensor scaling, the transformed diameter/thickness/measure, the upper-size transfer (b), the required closeness recheck (c), or the good-set/measure transport (d). Calling it an “amount helper” accurately describes its type, but does not cover the full source lemma assigned to this layer.

**Refutation check:** these identities can be proved independently from the definitions, and the amount inequality itself is correctly oriented and true. The defect is completeness of the promised layer interface, not a counterexample to that inequality. The repair appendix supplies geometry, jet and good-set companions. Keep the amount helper under its current type or give it a distinct helper name; do not mark the complete source lemma delivered until the companions are available.

## Notes

- **N1 — Informational: reality correction is appropriate.** The source's unconditional real-flow clause lacks a reality premise. The separate `canonical_step_real` guard is explicit, matches the graph's recorded SOURCE_GAP, and can be supplied for the physical Hamiltonian. It does not change a frozen theorem. I do not count this declared source repair as an illicit extra premise.
- **N2 — Informational: upstream reconciliation remains a real gate.** Parts 2/8/9/10 and 11a3–5 are acknowledged ports. The literal secular Hessian, sorted spectrum, SO(n) lift, fixed-norm derivative estimate, finite retained-set divisors, lower monotone budget and displacement power remain proof/adapter obligations. Existence of their sorry-bodied output packages is not evidence that these obligations are discharged.
- **N3 — Informational: default totality is adequately guarded in the checked uses.** Empty-sphere/empty-set suprema and choice defaults exist on the full total carrier. The draft's positive dimensions, nonempty compact patches, analytic regularity and sufficiently small positive epsilon protect the intended uses. Keep the promised boundedness/attainment and choice-spec lemmas in the implementation; do not use fallback values to establish a theorem.

## Per-signature ledger

One row per named declaration (including abbreviations, definitions and structures). Names are in `KAM.Planetary`. “PASS” approves the displayed component as a design signature and its documented bridges; it is not a proof-status claim. A failed aggregate predicate is listed separately from its theorem. Other theorems are not automatically marked false because they depend on a package requiring repair.

| Lean name (signature line) | Blueprint label / responsibility | Verdict | Reason |
|---|---|---|---|
| `P11Vec` (L29) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `P11CVec` (L30) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `P11Phase` (L31) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `P11Family` (L32) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `p11euclid` (L35) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `p11dot` (L37) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `p11dotZ` (L39) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `p11dotC` (L42) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `p11thick` (L46) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `p11dg` (L50) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `p11op` (L54) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `p11scalar` (L58) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `p11maxJet` (L62) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `index_def` (L66) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `p11JetBound` (L71) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `p11eta` (L75) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `P11Patch` (L79) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `P11SublevelHyp` (L92) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `p11Csub` (L105) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `p11RNondegenerate` (L110) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `rank_compact` (L113) | `bpP:p11a:rank-compact` | PASS | Literal typed component; regularity/positivity guards retained |
| `stability` (L120) | `bpP:p11a:stability` | PASS | Literal typed component; regularity/positivity guards retained |
| `M_bound` (L131) | `bpP:p11a:M-bound` | PASS | Literal typed component; regularity/positivity guards retained |
| `divided_difference` (L139) | `bpP:p11a:divided-difference` | PASS | Literal typed component; regularity/positivity guards retained |
| `scalar_sublevel` (L146) | `bpP:p11a:scalar-sublevel` | PASS | Literal typed component; regularity/positivity guards retained |
| `ball_sublevel` (L153) | `bpP:p11a:ball-sublevel` | PASS | Literal typed component; regularity/positivity guards retained |
| `sublevel` (L163) | `bpP:p11a:sublevel` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11Good` (L171) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `P11DioHyp` (L175) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `diophantine_measure` (L192) | `bpP:p11a:diophantine-measure` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11CDio` (L204) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `p11GammaStar` (L209) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Explicit intended carrier, construction or source/output data |
| `power_law` (L213) | `bpP:p11a:power-law` | PASS | Literal typed component; regularity/positivity guards retained |
| `limit_bridge` (L225) | `bpP:p11a:limit-bridge` | PASS | Literal typed component; regularity/positivity guards retained |
| `limit_bridge_diophantine` (L231) | `bpP:p11a:limit-bridge` | PASS | Literal typed component; regularity/positivity guards retained |
| `domain_def` (L240) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11Admissible` (L243) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11Bound` (L248) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11Real` (L251) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11Cut` (L256) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11Taylor` (L260) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11Cutoff` (L263) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11C` (L265) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11Error` (L267) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11Loss` (L268) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11Lambda` (L270) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `fourier_cutoff` (L272) | `bpP:p11a:fourier-cutoff` | PASS | Literal typed component; regularity/positivity guards retained |
| `loss_choice` (L283) | `bpP:p11a:loss-choice` | PASS | Literal typed component; regularity/positivity guards retained |
| `loss_sum` (L290) | `bpP:p11a:loss-sum` | PASS | Literal typed component; regularity/positivity guards retained |
| `taylor_cutoff` (L301) | `bpP:p11a:taylor-cutoff` | PASS | Literal typed component; regularity/positivity guards retained |
| `cutoff` (L311) | `bpP:p11a:cutoff` | PASS | Literal typed component; regularity/positivity guards retained |
| `param_cauchy` (L322) | `bpP:p11a:param-cauchy` | PASS | Literal typed component; regularity/positivity guards retained |
| `divisor_wide` (L329) | `bpP:p11a:divisor-wide` | PASS | Literal typed component; regularity/positivity guards retained |
| `divisor_perturb` (L339) | `bpP:p11a:divisor-perturb` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11Solve` (L350) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11AngleClass` (L355) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11AngleAverage` (L360) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `homological_maximal` (L363) | `bpP:p11a:homological-maximal` | FAIL | F1: source-domain premise becomes global |
| `p11Affine` (L391) | `bpP:p11a:affine-flow / real-flow constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11Flow` (L394) | `bpP:p11a:affine-flow / real-flow constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11GaugeBound` (L398) | `bpP:p11a:affine-flow / real-flow constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `P11AffineHyp` (L401) | `bpP:p11a:affine-flow / real-flow constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `affine_flow` (L416) | `bpP:p11a:affine-flow` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11_complexification` (L446) | `stepP:p11:hc-rot / SG1` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11_real_slice_identity` (L453) | `stepP:p11:hc-rot / SG1` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11_radial_schwarz` (L459) | `stepP:p11:hc-mean / SG2` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11_bounded_global_flow` (L466) | `stepP:p11a:rl-global / SG3` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11RealFlow` (L472) | `bpP:p11a:affine-flow / real-flow constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11_global_variational` (L477) | `stepP:p11a:rl-deriv / SG4` | PASS | Literal typed component; regularity/positivity guards retained |
| `real_lipschitz` (L486) | `bpP:p11a:real-lipschitz` | PASS | Literal typed component; regularity/positivity guards retained |
| `P11Step` (L497) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11StepA` (L527) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11StepKappa` (L529) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11StepRem` (L530) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11R0` (L535) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11R1` (L537) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11DeltaH` (L539) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11DeltaW` (L540) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11StepPhi` (L543) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11StepMap` (L547) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11Normal` (L551) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11StepRemainder` (L554) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `P11StepHyp` (L559) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `canonical_step` (L574) | `bpP:p11a:canonical-step` | PASS | Literal typed component; regularity/positivity guards retained |
| `canonical_step_real` (L605) | `stepP:p11a:cs-lip (declared reality repair)` | PASS | Literal typed component; regularity/positivity guards retained |
| `canonical_step_param` (L621) | `stepP:p11a:cs-param` | PASS | Literal typed component; regularity/positivity guards retained |
| `P11Physical` (L641) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Explicit intended carrier, construction or source/output data |
| `p11Zeta` (L655) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Explicit intended carrier, construction or source/output data |
| `p11_zeta_pos` (L658) | `bpP:p6:tube-constants bridge` | PASS | Literal typed component; regularity/positivity guards retained |
| `forward_tube` (L661) | `bpP:p11:forward-tube` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11PhysicalDelta` (L671) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Explicit intended carrier, construction or source/output data |
| `p11SecularMatrix` (L675) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Explicit intended carrier, construction or source/output data |
| `P11PatchData` (L682) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Explicit intended carrier, construction or source/output data |
| `P11PatchSpec` (L690) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Explicit intended carrier, construction or source/output data |
| `p11_patch` (L705) | `bpP:p11:sec-A#data / P10 port` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11PatchData` (L707) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Explicit intended carrier, construction or source/output data |
| `norm_dict` (L710) | `bpP:p11:norm-dict` | PASS | Literal typed component; regularity/positivity guards retained |
| `select` (L722) | `bpP:p11:select` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11WorkingDom` (L730) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `P11SecularData` (L737) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11ChartInput` (L757) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11WorkingH` (L767) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11FastMean` (L770) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `P11SecularSpec` (L774) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `holo_chart` (L827) | `bpP:p11:holo-chart` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11SecularData` (L829) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11PolarC` (L832) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `p11PolarR` (L840) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Explicit intended carrier, construction or source/output data |
| `total_chart` (L844) | `bpP:p11:total-chart` | PASS | Literal typed component; regularity/positivity guards retained |
| `total_chart_transport` (L853) | `stepP:p11:tc-lat` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11K1` (L867) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11Alpha1` (L869) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11s1` (L870) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11d1` (L872) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11eta1` (L873) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `P11FastData` (L876) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `P11FastSpec` (L882) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `avg_fast` (L917) | `bpP:p11:avg-fast` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11FastData` (L924) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11PolarAverage` (L928) | `bpP:p11:polar-avg raw integral` | PASS | Explicit intended carrier, construction or source/output data |
| `polar_avg` (L935) | `bpP:p11:polar-avg` | FAIL | F3: linearity and normalization omitted |
| `p11Box` (L950) | `bpP:p11:aniso-bracket / aniso-avg domains` | PASS | Explicit intended carrier, construction or source/output data |
| `p11WBound` (L955) | `bpP:p11:aniso-bracket / aniso-avg domains` | PASS | Explicit intended carrier, construction or source/output data |
| `aniso_bracket` (L959) | `bpP:p11:aniso-bracket` | FAIL | F1/F4: global premises and missing field clause |
| `aniso_avg` (L973) | `bpP:p11:aniso-avg` | FAIL | F1: source-domain premise becomes global |
| `p11Rescale` (L1016) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11PreparedBox` (L1020) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11K2` (L1023) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11s2` (L1025) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `P11SlowData` (L1028) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11PartialVec` (L1038) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `P11SlowSpec` (L1042) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `avg_slow` (L1101) | `bpP:p11:avg-slow` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11SlowConstant` (L1106) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11SlowData` (L1110) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `P11PreparedData` (L1113) | `bpP:p11:prepared / amount outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11PreparedFreq` (L1120) | `bpP:p11:prepared / amount outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `p11PreparedFreqR` (L1122) | `bpP:p11:prepared / amount outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `P11PreparedSpec` (L1125) | `bpP:p11:prepared / amount outputs` | FAIL | F2: narrowed jets; missing vector size |
| `prepared` (L1162) | `bpP:p11:prepared` | FAIL | F2: weakened prepared output |
| `p11PreparedData` (L1171) | `bpP:p11:prepared / amount outputs` | PASS | Explicit intended carrier, construction or source/output data |
| `amount` (L1175) | `bpP:p11:amount` | PASS | Literal typed component; regularity/positivity guards retained |
| `chart_scaling` (L1184) | `bpP:p11a:chart-scaling` | FAIL | F5: only amount clause (a) |
| `wrapper` (L1192) | `bpP:p11:wrapper` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11Order` (L1201) | `stepP:p11:wr-nu` | PASS | Explicit intended carrier, construction or source/output data |
| `e4` (L1205) | `bpP:p11:e4` | PASS | Literal typed component; regularity/positivity guards retained |
| `e5` (L1208) | `bpP:p11:e5` | PASS | Literal typed component; regularity/positivity guards retained |
| `homological_maximal_real` (L1212) | `bpP:p11a:homological-maximal(d)` | FAIL | F1: source-domain premise becomes global |
| `homological_maximal_param` (L1225) | `bpP:p11a:homological-maximal(c)` | FAIL | F1: source-domain premise becomes global |
| `p11_normal_affine_bracket` (L1240) | `stepP:p11a:hm-bracket` | PASS | Literal typed component; regularity/positivity guards retained |
| `cutoff_coefficients` (L1247) | `stepP:p11a:cu-coeff / cutoff(a)` | PASS | Literal typed component; regularity/positivity guards retained |
| `canonical_step_simple_inverse` (L1256) | `canonical-step(ii), affine-flow(c),(e)` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11_lambda_spec` (L1271) | `bpP:p11a:sec-hom#lambda` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11Index` (L1280) | `bpP:p11a:index-def (least positive index)` | PASS | Explicit intended carrier, construction or source/output data |
| `p11Amount` (L1283) | `bpP:p11a:index-def (least positive index)` | PASS | Explicit intended carrier, construction or source/output data |
| `data_star` (L1287) | `bpP:p11:data-star` | FAIL | F2: geometry does not assemble admissibility |
| `affine_flow_param` (L1294) | `stepP:p11a:af-rest / affine-flow(f)` | PASS | Literal typed component; regularity/positivity guards retained |
| `p11_trig_derivative_bound` (L1305) | `stepP:p11a:rl-const` | PASS | Literal typed component; regularity/positivity guards retained |

## Consumer, frozen-object, definition and package verdicts

**Consumers: FAIL until F1–F5 are repaired.** The weak-measure layer otherwise preserves independent parameter/frequency dimensions, one map per mode, Euclidean target tensors, l1 Fourier cutoffs, ENNReal countable sums and the limiting-frequency bridge. The maximal step preserves the sign, zero perturbation, explicit cutoff/generator/remainder and fixed-norm derivative bound. Prepared/amount retain the correct epsilon exponent, but the promised full prepared/datum interface is incomplete. `wrapper` has the literal physical per-point torus conclusion; its realization still waits for the repaired preparation exports and reconciled K1–K6.

Read consumers in P11a3, P11a4, P11a5 and P13, plus the Part1 transport/measure signatures. In particular, `torus_transport_phys` needs an `IsChart`, actual lattice-torus data and both lattice properties; `measure_chart_image` needs analytic/symplectic chart data, saturation and the full position lattice. Casting `n+n` to `n*2` is necessary and is explicitly planned. Nothing in the draft assumes a Borel image merely from continuity. The brief's generic N:p3 consumer search in tracks I/P and N Parts 7/11/12 was also checked; those are ODE-layer consumers, not additional consumers of the P11A weak-measure/preparation exports.

**Frozen objects: PASS at design level.** Read the frozen `Phase`, `assemble`, `secularAverage`, `fixedHamiltonian`, `IsPhysicalTorus`, `IsDiophantine`, `hamiltonianVectorFieldℂ`, `complexStrip`, `actionNbhd`, `circularPoint` and `circularTube`. The signatures use these actual objects. In particular `p11SecularMatrix` differentiates the actual frozen secular average of the physical pullback, and `wrapper` concludes the actual frozen torus predicate. `p11PolarC` is a complex chart whose comparison to the existing real chart is an explicitly required bridge. `p11Zeta` unfolds the existing `axisGap`/`tubeRadius` formulas, whose equality was checked against the delivered source. No replacement solution predicate or global norm instance was found.

**Definitions and structures: PASS except the incomplete output specification F2.** `P11Physical`, `P11Step`, `P11StepHyp`, `P11AffineHyp`, sublevel and Diophantine hypotheses contain source premises. The stage structures contain construction data and their specifications occur as existential outputs; they are not extra assumptions of the physical existence theorems. The local and global flows use existing flow/ODE objects or explicit selected solutions. Intended uses must discharge existence/uniqueness rather than exploiting fallback branches. F1 concerns theorems' overstrong domain requirements, not a hidden axiom in a structure.

**Packages: PASS for dependency architecture, subject to contract repairs.** There are 29 packages in 12 waves; estimates are 150–800 lines per package and no proposed file exceeds 1500 lines. WeakMeasure does not import Preparation; MaximalStep does not import Preparation; the wrapper consumes the later weak-KAM outputs, with no backward dependency from the iteration to physical preparation. The rectangular branch correctly does not treat N's isotropic normal form as a ready-made substitute. External owner reconciliation is a stated launch gate. Add the repairs to W8/P3/P6/P8 rather than silently assigning untyped extra work to consumers.

## Verification

- Copied the original signatures byte-for-byte into `.drafts/scratch/P11ASignatures.lean`; the original hash is unchanged.
- Ran the signature file **once**, through `inp_sig_check.sh`, which executes `LEAN_NUM_THREADS=1 nice -n 5 lake env lean <copy>` against the shared `inp` build: **exit 0**, 58 warnings, all `declaration uses sorry`, no errors or other warnings.
- The three requested axiom prints (`sublevel`, `canonical_step`, `wrapper`) all report `[propext, sorryAx, Classical.choice, Quot.sound]`. This is expected for a signature draft and proves no theorem body.
- Ran one serial declaration-name probe in `.lake/abi-scratch/`: **exit 0**. Checked `Lagrange.interpolate`, `exists_deriv_eq_zero`, the Haar determinant image theorem, the orthonormal-extension theorem and the higher-order Schwarz theorem; also the delivered Cauchy, Fourier, lattice, flow, Lie and ODE declarations named in the reuse table. Their displayed types require the expected regularity, domain, derivative-continuity, gauge-interior and finite-dimensional hypotheses. The orthonormal-basis theorem requires an inner-product carrier; the design correctly chooses an explicit Householder matrix on the Pi carrier instead of installing a new instance. `Weighted.general_cauchy` is first order; the design correctly retains the arbitrary-order parameter estimate as new work.
- No proof module was edited, so no implementation module build was applicable. The narrow signature elaboration above is the required targeted Lean check; no library or dependency rebuild was launched by this audit.
- Lint and final whitespace/state receipts are recorded at closeout below. All audit-owned Lean calls were serialized, used `LEAN_NUM_THREADS=1` and `nice -n 5`, and used the campaign gate. Other independently running campaign processes are outside this audit's ownership; no such process was interrupted.

## Proposed corrected signatures

These are interface proposals in the same namespace and using the draft's existing notation. Existing successful components remain available. Code below intentionally uses `sorry` only as proposed design-body placeholders; it is not implementation code and was not added to the project. The source and signatures were not repaired during this audit.

### F1: source-domain replacements

```lean
theorem homological_maximal {n : ℕ} (hn : 1 ≤ n) {r delta T D M : ℝ}
    (hr : 0 < r) (hd : 0 < delta) (hdr : delta < r) (hT : 0 < T)
    (hD : 0 < D) (hM : 0 ≤ M) {B : Set (P11CVec n)} (hB : IsOpen B)
    (w : P11CVec n → P11CVec n) (hw : DifferentiableOn ℂ w B)
    (hdiv : ∀ b ∈ B, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T → D/2 ≤ ‖p11dotC k (w b)‖)
    (P : P11CVec n × P11CVec n → ℂ) (hP : p11AngleClass r B P)
    (hpoly : ∀ z ∈ Set.univ ×ˢ B, KAM.Weighted.truncate T P z=P z)
    (hb : p11Bound (KAM.complexStrip n r ×ˢ B) P M) :
    let phi := fun z : P11CVec n × P11CVec n => p11Solve T w P z.1 z.2
    p11AngleClass (r-delta) B phi ∧
    DifferentiableOn ℂ phi (Set.univ ×ˢ B) ∧
    (∀ z, KAM.Weighted.truncate T phi z=phi z) ∧
    DifferentiableOn ℂ (p11AngleAverage P) B ∧
    (∀ b ∈ B, p11AngleAverage phi b=0) ∧
    (∀ theta ∈ KAM.complexStrip n (r-delta), ∀ b ∈ B,
      fderiv ℂ (fun x => phi (x,b)) theta (w b)=P (theta,b)-p11AngleAverage P b) ∧
    p11Bound (KAM.complexStrip n (r-delta) ×ˢ B) phi (p11Lambda n delta*M/(Real.pi*D)) ∧
    (∀ b ∈ B, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      ‖KAM.Weighted.coeff phi b k‖ ≤ M*Real.exp (-2*Real.pi*KAM.Fourier.modeSize k*r)/(Real.pi*D)) ∧
    (∀ b ∈ B, ‖p11AngleAverage P b‖ ≤ M) ∧
    ∀ u, p11AngleClass (r-delta) B u →
      (∀ z ∈ Set.univ ×ˢ B, KAM.Weighted.truncate T u z=u z) →
      (∀ b ∈ B, p11AngleAverage u b=0) →
      (∀ theta ∈ KAM.complexStrip n (r-delta), ∀ b ∈ B,
        fderiv ℂ (fun x => u (x,b)) theta (w b)=P (theta,b)-p11AngleAverage P b) →
      EqOn u phi (KAM.complexStrip n (r-delta) ×ˢ B) := sorry
```

```lean
theorem homological_maximal_real {n : ℕ} {r T D : ℝ} (hr : 0 < r) (hT : 0 < T) (hD : 0 < D)
    {B : Set (P11CVec n)} (hB : IsOpen B) (w : P11CVec n → P11CVec n)
    (hw : DifferentiableOn ℂ w B)
    (hdiv : ∀ b ∈ B, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T → D/2 ≤ ‖p11dotC k (w b)‖)
    (P : P11CVec n × P11CVec n → ℂ) (hP : p11AngleClass r B P)
    (hpoly : ∀ z ∈ Set.univ ×ˢ B, KAM.Weighted.truncate T P z=P z)
    (hwr : ∀ b : P11Vec n, KAM.realInclusion n b ∈ B → ∀ i, (w (KAM.realInclusion n b) i).im=0)
    (hpr : ∀ x b : P11Vec n, KAM.realInclusion n b ∈ B →
      (P (KAM.realInclusion n x,KAM.realInclusion n b)).im=0) :
    ∀ x b : P11Vec n, KAM.realInclusion n b ∈ B →
      (p11Solve T w P (KAM.realInclusion n x) (KAM.realInclusion n b)).im=0 := sorry
```

```lean
theorem homological_maximal_param {n : ℕ} {r delta T D M t tp : ℝ}
    (hr : 0 < r) (hd : 0 < delta) (hdr : delta < r) (hT : 0 < T)
    (hD : 0 < D) (hM : 0 ≤ M) {E : Set (P11Vec n)} (htp : 0 < tp) (htt : tp < t)
    (w : P11CVec n → P11CVec n) (hw : DifferentiableOn ℂ w (KAM.actionNbhd E t))
    (hdiv : ∀ b ∈ KAM.actionNbhd E t, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T → D/2 ≤ ‖p11dotC k (w b)‖)
    (P : P11CVec n × P11CVec n → ℂ) (hP : p11AngleClass r (KAM.actionNbhd E t) P)
    (hpoly : ∀ z ∈ Set.univ ×ˢ KAM.actionNbhd E t,
      KAM.Weighted.truncate T P z=P z)
    (hb : p11Bound (KAM.complexStrip n r ×ˢ KAM.actionNbhd E t) P M)
    {j : ℕ} (hj : 1 ≤ j) :
    ∀ theta ∈ KAM.complexStrip n (r-delta), ∀ b ∈ KAM.actionNbhd E tp,
      ‖iteratedFDeriv ℂ j (p11Solve T w P theta) b‖ ≤
        (j : ℝ)^j*p11Lambda n delta*M/(Real.pi*D*(t-tp)^j) ∧
      ‖iteratedFDeriv ℂ j (p11AngleAverage P) b‖ ≤ (j : ℝ)^j*M/(t-tp)^j := sorry
```

```lean
theorem aniso_bracket {a b : ℕ} {c : P11CVec (a+b)} {r01 r02 r1 r2 rho1 rho2 s0 s sigma U W : ℝ}
    (h01 : r1 ≤ r01) (h02 : r2 ≤ r02) (h1 : 0 < rho1) (h2 : 0 < rho2)
    (hr1 : rho1 < r1) (hr2 : rho2 < r2) (hs : 0 < sigma) (hs' : sigma < s) (hs0 : s ≤ s0)
    {u w : P11Phase (a+b) → ℂ}
    (hu : DifferentiableOn ℂ u (KAM.complexStrip (a+b) s0 ×ˢ p11Box c r01 r02))
    (hw : DifferentiableOn ℂ w (KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2))
    (hup : ∀ z ∈ KAM.complexStrip (a+b) s0 ×ˢ p11Box c r01 r02,
      ∀ i : Fin (a+b), u (z.1+Pi.single i 1,z.2)=u z)
    (hwp : ∀ z ∈ KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2,
      ∀ i : Fin (a+b), w (z.1+Pi.single i 1,z.2)=w z)
    (hU : p11WBound (p11Box c r01 r02) s0 u U) (hW : p11WBound (p11Box c r1 r2) s w W) :
    p11WBound (p11Box c (r1-rho1) (r2-rho2)) (s-sigma) (KAM.Canonical.poissonBracket u w)
      ((sigma/(s0-s+sigma)+min rho1 rho2/min (r01-r1+rho1) (r02-r2+rho2)) /
        (Real.exp 1*min rho1 rho2*sigma)*U*W) := sorry
```

```lean
theorem aniso_avg {a b : ℕ} {c : P11CVec (a+b)} {r1 r2 s T alpha1 alpha2 E : ℝ}
    (hr1 : 0 < r1) (hr2 : 0 < r2) (hs : 0 < s) (hT : 0 < T)
    (hk : 6 ≤ 2*Real.pi*T*s) (ha : 0 < alpha2) (ha' : alpha2 ≤ alpha1)
    {h : P11CVec (a+b) → ℂ} {f : P11Phase (a+b) → ℂ}
    (hh : DifferentiableOn ℂ h (p11Box c r1 r2))
    (hf : DifferentiableOn ℂ f (KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2))
    (hp : ∀ z ∈ KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2,
      ∀ i : Fin (a+b), f (z.1+Pi.single i 1,z.2)=f z)
    (hrealh : ∀ x : P11Vec (a+b), KAM.realInclusion (a+b) x ∈ p11Box c r1 r2 →
      (h (KAM.realInclusion (a+b) x)).im=0)
    (hrealf : KAM.Canonical.RealOn (KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2) f)
    (hE : 0 ≤ E) (hb : p11WBound (p11Box c r1 r2) s f E)
    (hsmall : E ≤ alpha2*min r1 r2/(128*T))
    (hdiv : ∀ I ∈ p11Box c r1 r2, ∀ k : Fin (a+b) → ℤ, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      (if (fun i : Fin a => k (Fin.castAdd b i))=0 then alpha2 else alpha1) ≤
        ‖p11dotC k (fun i => fderiv ℂ h I (Pi.single i 1))‖) :
    ∃ Psi : P11Phase (a+b) → P11Phase (a+b), ∃ g : P11CVec (a+b) → ℂ,
      ∃ fs : P11Phase (a+b) → ℂ,
      let U := KAM.complexStrip (a+b) (s/6) ×ˢ p11Box c (r1/2) (r2/2)
      DifferentiableOn ℂ Psi U ∧ InjOn Psi U ∧
      DifferentiableOn ℂ g (p11Box c (r1/2) (r2/2)) ∧ DifferentiableOn ℂ fs U ∧
      KAM.Canonical.RealOn U fs ∧
      (∀ I : P11Vec (a+b), KAM.realInclusion (a+b) I ∈ p11Box c (r1/2) (r2/2) →
        (g (KAM.realInclusion (a+b) I)).im=0) ∧
      (∀ z ∈ U, ∀ k : Fin (a+b) → ℤ, Psi (z.1+(fun i => (k i : ℂ)),z.2)=Psi z+((fun i => (k i : ℂ)),0)) ∧
      (∀ z ∈ U, ∀ i : Fin (a+b), fs (z.1+Pi.single i 1,z.2)=fs z) ∧
      (∀ z : Phase (a+b), KAM.realInclusion₂ (a+b) z ∈ U → ∀ i,
        ((Psi (KAM.realInclusion₂ (a+b) z)).1 i).im=0 ∧
        ((Psi (KAM.realInclusion₂ (a+b) z)).2 i).im=0) ∧
      MapsTo Psi U (KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2) ∧
      (∀ z ∈ U, h (Psi z).2+f (Psi z)=h z.2+g z.2+fs z) ∧
      p11WBound (p11Box c (r1/2) (r2/2)) (s/6) fs (Real.exp (-2*Real.pi*T*s/6)*E) ∧
      p11WBound (p11Box c (r1/2) (r2/2)) (s/6)
        (fun z : P11Phase (a+b) => g z.2-KAM.Weighted.coeff f z.2 0) (130*E^2/(2*Real.pi*alpha2*min r1 r2*s)) ∧
      p11WBound (p11Box c (r1/2) (r2/2)) (s/6)
        (fun z : P11Phase (a+b) => g z.2-KAM.Weighted.coeff f z.2 0) (E/(2*Real.pi*T*s)) ∧
      (∀ z ∈ U,
        2*Real.pi*alpha1*s*‖(fun i : Fin a => (Psi z).2 (Fin.castAdd b i)-z.2 (Fin.castAdd b i))‖ ≤ 3*E ∧
        2*Real.pi*alpha2*s*‖(fun i : Fin b => (Psi z).2 (Fin.natAdd a i)-z.2 (Fin.natAdd a i))‖ ≤ 3*E) ∧
      (∀ z ∈ U, ‖(Psi z).1-z.1‖ ≤ 9*E/(2*Real.pi*alpha2*min r1 r2)) ∧
      (∀ z ∈ U, ∀ u v, KAM.Canonical.symplFormC (fderiv ℂ Psi z u) (fderiv ℂ Psi z v)=
        KAM.Canonical.symplFormC u v) := sorry
```

### F2: strengthen the prepared output and assemble its fixed data

The following retains `P11PreparedSpec` as a component, then restores its missing source clauses. `p11M0` is a permitted explicit choice of the source's unspecified dimension/order factor `c(n,mu)*(2L+1)`; its precise constant can be enlarged before nu is chosen. A proof must use the explicit Euclidean/max comparison. Do not infer this bound by identifying the two gauges.

To retain prepared(d) also at order zero, make the initial, freely chosen L dominate the Euclidean frequency size before it is selected. This is a stronger true output, not an identification of norms; its selector must replace the old selector. The positive-order scalar bound already present in `P11PreparedSpec` is retained.

```lean
def P11SecularFullSpec {n : ℕ} (D : P11Physical n)
    (C : P11SecularData n) : Prop :=
  P11SecularSpec D C ∧
  ∀ J ∈ Metric.ball (KAM.realInclusion n C.J0) (2*C.rC),
    KAM.Nekhoroshev.euclid
      (Fin.append (C.omega J) ((2*Real.pi : ℂ)⁻¹ • C.Omega J)) ≤ C.L

theorem holo_chart {n : ℕ} (D : P11Physical n) :
    ∃ C, P11SecularFullSpec D C := sorry

def p11SecularData {n : ℕ} (D : P11Physical n) : P11SecularData n :=
  (holo_chart D).choose

def p11M0 (n mu : ℕ) (L : ℝ) : ℝ :=
  (2*n+1 : ℝ)^(mu+1)*(2*L+1)

def p11SlowNormalizedFreq {n : ℕ} (D : P11Physical n)
    (nu eps : ℝ) (J rho : P11Vec n) : P11Vec (n+n) :=
  let A := p11SlowData D nu eps
  let I := Fin.append (KAM.realInclusion n J)
    (fun i : Fin n => (eps*(2*Real.pi+rho i) : ℂ))
  let W : P11CVec (n+n) :=
    fun i => fderiv ℂ (A.h0+A.g2) I (Pi.single i 1)
  Fin.append (fun i : Fin n => (W (Fin.castAdd n i)).re)
    (fun i : Fin n => (W (Fin.natAdd n i)).re/eps)

def P11PreparedFullSpec {n : ℕ} (D : P11Physical n)
    (nu eps c : ℝ) (Q : P11PreparedData n) : Prop :=
  let C := p11SecularData D
  let A := p11PatchData D
  let ell := Real.log (1/eps)
  let exponent := 5*C.tau+2+(C.tau+1)*(A.mu+1)
  P11PreparedSpec D nu eps c Q ∧
  (∀ rho : P11Vec n, ‖rho‖ < 5/4 →
    ∀ J : P11Vec n, ‖J-C.J0‖ < p11s2 C nu eps/4 →
      Q.checkW (Fin.append ((eps : ℝ)⁻¹ • (J-C.J0)) rho) =
        p11SlowNormalizedFreq D nu eps J rho) ∧
  (∀ rho : P11Vec n, ‖rho‖ < 5/4 →
    p11JetBound true A.mu {J | ‖J-C.J0‖ < p11s2 C nu eps/4}
      ((fun J => Q.checkW (Fin.append ((eps : ℝ)⁻¹ • (J-C.J0)) rho))-A.varpi)
      (c*eps*ell^exponent)) ∧
  p11JetBound true A.mu (p11thick (p11PreparedBox n) (1/4))
    (p11PreparedFreqR Q) (p11M0 n A.mu C.L) ∧
  (∀ direction, p11euclid direction=1 →
    ∀ y ∈ p11thick (p11PreparedBox n) (1/4),
      p11op (p11scalar 2 (p11PreparedFreqR Q) direction) 0 y ≤
        (2 : ℝ)^(A.mu+1)*(2*C.L+1)^2)

theorem prepared {n : ℕ} (D : P11Physical n) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ eps3 c3 : ℝ, 0 < eps3 ∧ eps3 < 1 ∧ 1 ≤ c3 ∧
    ∀ eps, 0 < eps → eps ≤ eps3 →
      5*eps ≤ p11s2 (p11SecularData D) nu eps ∧
      c3*eps*Real.log (1/eps)^(5*(p11SecularData D).tau+2+
        ((p11SecularData D).tau+1)*((p11PatchData D).mu+1)) ≤ 1 ∧
      ∃ Q, P11PreparedFullSpec D nu eps c3 Q := sorry

theorem data_star {n : ℕ} (D : P11Physical n) :
    IsCompact (p11PreparedBox n) ∧ volume (p11PreparedBox n)=1 ∧
    Metric.diam (p11PreparedBox n)=1 ∧
    0 < (1/4 : ℝ) ∧ 0 < (1/2 : ℝ) ∧
    max ((n : ℝ)*(p11PatchData D).mu) (2*n) >
      max (((n+n : ℕ) : ℝ)*(p11PatchData D).mu/2-1)
        (((n+n : ℕ) : ℝ)-1) ∧
    ∀ nu : ℝ, 1 ≤ nu →
      ∃ epsA c : ℝ, 0 < epsA ∧ epsA < 1 ∧ 1 ≤ c ∧
      ∀ eps, 0 < eps → eps ≤ epsA →
        let C := p11SecularData D
        let A := p11PatchData D
        let beta := (1/2 : ℝ)*eps^(A.mu+2)*A.beta
        let M := (2 : ℝ)^(A.mu+1)*(2*C.L+1)^2
        0 < beta ∧ beta ≤ min 1 M ∧
        1 ≤ p11M0 n A.mu C.L ∧
        ∃ Q, P11PreparedFullSpec D nu eps c Q ∧
          beta ≤ index_def 2 A.mu (p11PreparedFreqR Q) (p11PreparedBox n) := sorry
```

`p11PreparedData` and `amount` must select from the strengthened existence theorem, so all outputs refer to the **same** Q. Do not let different independent choices supply different conjuncts. The geometric portion of the old `data_star` remains above; the new portion assembles the analytic hypotheses, scalar bounds, vector bound, amount and amount smallness. After the exact 11a5 API is reconciled, its admissibility predicate and lower-budget consequences should be exported as a typed bridge from these outputs, rather than as another assumption.

### F3: linearity, normalization and uniqueness companions

These companions recover source (d) as an operator on the analytic germs. Uniqueness then transports the raw identities to the existential holomorphic extensions. They do not assert global linearity of a totalized integral on nonintegrable inputs.

```lean
theorem polar_average_linear {n : ℕ} {D : Set (P11CVec n)}
    (hD : IsOpen D) {r : ℝ} (hr : 0 < r)
    {G H : P11CVec n × P11Phase n → ℂ}
    (hG : DifferentiableOn ℂ G (D ×ˢ Metric.ball 0 r))
    (hH : DifferentiableOn ℂ H (D ×ˢ Metric.ball 0 r))
    (a b : ℂ) :
    ∀ z ∈ D ×ˢ Metric.ball 0 (Real.pi*r^2/4),
      (∀ i, 0 < (z.2 i).re) →
      p11PolarAverage (a • G+b • H) z =
        a*p11PolarAverage G z+b*p11PolarAverage H z := sorry

theorem polar_average_normalization {n : ℕ}
    (C : P11CVec n → ℂ) (z : P11CVec n × P11CVec n) :
    p11PolarAverage (fun y => C y.1) z = C z.1 ∧
    ∀ i : Fin n,
      p11PolarAverage (fun y => (y.2.1 i^2+y.2.2 i^2)/2) z =
        z.2 i/(2*Real.pi) := sorry

theorem polar_extension_unique {n : ℕ} {D : Set (P11CVec n)}
    (hD : IsOpen D) {R : ℝ} (hR : 0 < R)
    {A B : P11CVec n × P11CVec n → ℂ}
    (hA : DifferentiableOn ℂ A (D ×ˢ Metric.ball 0 R))
    (hB : DifferentiableOn ℂ B (D ×ˢ Metric.ball 0 R))
    (heq : ∀ z ∈ D ×ˢ Metric.ball 0 R, (∀ i, 0 < (z.2 i).re) → A z=B z) :
    EqOn A B (D ×ˢ Metric.ball 0 R) := sorry
```

In `polar_extension_unique`, `heq` is the ordinary equality-on-an-open-subset premise of an identity theorem, not an assumed physical output or a proof step in a physical existence theorem. No connectedness assumption on D is needed: fix J and apply the identity theorem in the connected action polydisc. The n=0 case reduces to the same value and is harmless.

### F4: rectangular vector-field companion

```lean
theorem aniso_field {a b : ℕ} {c : P11CVec (a+b)}
    {r1 r2 rho1 rho2 s sigma M : ℝ}
    (h1 : 0 < rho1) (h2 : 0 < rho2)
    (hr1 : rho1 < r1) (hr2 : rho2 < r2)
    (hs : 0 < sigma) (hs' : sigma < s)
    {phi : P11Phase (a+b) → ℂ}
    (hphi : DifferentiableOn ℂ phi
      (KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2))
    (hp : ∀ z ∈ KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2,
      ∀ i : Fin (a+b), phi (z.1+Pi.single i 1,z.2)=phi z)
    (hM : p11WBound (p11Box c r1 r2) s phi M) :
    ∀ z ∈ KAM.complexStrip (a+b) (s-sigma) ×ˢ
      p11Box c (r1-rho1) (r2-rho2),
      let X := KAM.hamiltonianVectorFieldℂ phi z
      max (‖X.1‖/sigma)
        (max (‖(fun i : Fin a => X.2 (Fin.castAdd b i))‖/rho1)
          (‖(fun i : Fin b => X.2 (Fin.natAdd a i))‖/rho2)) ≤
        M/(min rho1 rho2*sigma) := sorry
```

### F5: affine geometry, jet and good-set transport companions

These supplement the existing amount inequality instead of replacing it with a different gauge or amount. The complete D2/D3 transfer follows from the pointwise jet identities and the indicated powers, with the original smoothness hypotheses on the functions involved.

```lean
theorem chart_scaling_geometry {n : ℕ} (y0 : P11Vec n)
    {lambda : ℝ} (hl : 0 < lambda) (K : Set (P11Vec n))
    (hK : IsCompact K) (v : ℝ) :
    let A := fun y : P11Vec n => y0+lambda • y
    Metric.diam (A ⁻¹' K) = Metric.diam K/lambda ∧
    p11thick (A ⁻¹' K) (v/lambda) = A ⁻¹' p11thick K v ∧
    ∀ E : Set (P11Vec n),
      volume (A ⁻¹' E) = ENNReal.ofReal (lambda^n)⁻¹*volume E := sorry

theorem chart_scaling_jets {n m k : ℕ} (hn : 1 ≤ n)
    {V : Set (P11Vec n)} (hV : IsOpen V)
    {f : P11Vec n → P11Vec m} (hf : ContDiffOn ℝ k f V)
    (y0 : P11Vec n) {lambda : ℝ} (hl : 0 < lambda) :
    ∀ j ≤ k, ∀ y, y0+lambda • y ∈ V →
      p11dg (fun x => f (y0+lambda • x)) j y =
        lambda^j*p11dg f j (y0+lambda • y) ∧
      p11op (fun x => f (y0+lambda • x)) j y =
        lambda^j*p11op f j (y0+lambda • y) := sorry

theorem chart_scaling_good {n m : ℕ} (y0 : P11Vec n)
    {lambda : ℝ} (hl : 0 < lambda) (K : Set (P11Vec n))
    (wt : (Fin m → ℤ) → P11Vec n → P11Vec m)
    (psi : (Fin m → ℤ) → ℝ) :
    let A := fun y : P11Vec n => y0+lambda • y
    p11Good (A ⁻¹' K) (fun k y => wt k (A y)) psi =
      A ⁻¹' p11Good K wt psi ∧
    volume (K \ p11Good K wt psi) =
      ENNReal.ofReal (lambda^n)*
        volume ((A ⁻¹' K) \ p11Good (A ⁻¹' K) (fun k y => wt k (A y)) psi) := sorry
```

For source (b), apply `chart_scaling_jets` to orders `1..mu+1` and use `lambda^j ≤ max 1 (lambda^(mu+1))`. For (c), apply it to the scalar-family difference at orders `0..mu`, using the **rechecked** bound `max 1 (lambda^mu)*theta ≤ beta'/2`; do not assume scale invariance. These direct inequalities should also be packaged with the source lemma if the consumer API requires one-call D2/D3 transport.

## Closeout, limitations and errata

This report leaves five open numbered findings. The verdict is FAIL even though elaboration and syntax/name checks pass. This audit does not assess theorem proof bodies, authorize a repair, seal any frozen anchor, or change the graph's own review status. Proposed repair blocks have not been elaborated as a combined replacement module; the once-only source-signature elaboration is kept distinct from proposed changes.

No new pinned-paper erratum is asserted. The design's inherited CP09/Rus05 reports were treated as inherited provenance, not independently revalidated PDF findings. The source-level reality defect is precisely the already recorded p11a2 L248/L287 issue quoted in N1. F2's narrowing is an unreported design departure from p11 L201, and F3–F5 are omitted interface clauses; report these to the designer/orchestrator without editing the frozen material or errata ledger.

Final receipts: `scripts/lint_sources.sh` (unmodified, using the pre-existing gated PATH wrapper) exited **0**: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (144 frozen declarations)`. `git diff --check` exited **0**. An explicit scan of this untracked report found zero trailing-whitespace violations and balanced code fences. The actual scoped graph records and mapping-table IDs agree exactly: **164 records, 164 unique rows, no missing or extra IDs**. The signature ledger has **158 rows**. The audit-created declaration-name probe was deleted. Final `git status --short` contains only this report as a new untracked file; the explicitly authorized scratch signature copy remains byte-identical to its pre-existing contents and to the unchanged original.
