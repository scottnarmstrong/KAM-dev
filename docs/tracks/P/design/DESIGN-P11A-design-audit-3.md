# P11A design delta audit 3

Overall verdict: **PASS**.

Revision 3 resolves the remaining F5-R2 mismatch. The source-specific closeness companion now takes and returns diagonal jets, with exactly the source's numerical recheck. F1–F4 and the other F5 repairs remain unchanged and accepted at the design-signature level. No open design finding remains in this delta scope. This PASS does not establish proof closure, discharge the recorded upstream interfaces/source gaps, or seal any frozen theorem.

## Scope and immutable snapshot

Independent tier-2, refute-first delta audit under `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-design.md` and the manuscript-audit method. Read the R3 handoff, Revision 3 section, complete parent diff, both previous reports and the relevant source/packet contracts.

Audited revision `536a571e9dd8e034b73ebaa740587cf785727638` against R2 `3803613aad2c3a03784ade891edcaa2601e99e23`. The tracked delta is one design document, 54 inserted / 7 deleted lines. Only `chart_scaling_closeness` changes type: two `false` selectors become `true`. A comment changes and one axiom-print command is added. All other 170 named declarations are byte-identical in the signature file. The source blueprints, graph rows, package schedule and earlier reports are unchanged.

| Input at snapshot v3 | SHA-256 |
|---|---|
| `docs/tracks/P/design/P11A-LEAN-DESIGN.md` | `8619ea896c856347a9a5c5efac5080f0c830ea19245320b5f03a2b4267a300b9` |
| `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` | `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092` |
| `docs/tracks/P/design/DESIGN-P11A-design-audit-1.md` | `987cb366ade135712e1752d113c62ea8d3ca8010e5543460d5ac188fa82dd72b` |
| `docs/tracks/P/design/DESIGN-P11A-design-audit-2.md` | `86e4dce2f0f0ee8f2c36bd51d0e3ac6a43f5d03ba1d51957472fa768ade2f1ac` |
| `blueprint-P/parts/p11-cp09-preparation.tex` | `4c0e2dfefb50b1e06581e069a55846d25e0e4697a8826514ac699bbb83efb41f` |
| `blueprint-P/parts/p11a1-weak-measure.tex` | `66b5ce26db59b57dbf934938a7bae2fead6b6ff4c7c9d420d33b9582e272bab5` |
| `blueprint-P/parts/p11a2-cutoff-step.tex` | `990694a832aa02dca0138c5cbb3bab842984583f4ca92576479eff04786ed3ec` |
| `docs/graph/P/packets/P-p11.nodes.md` | `067fa835864b522d663c83ac1255f360a5a550e565662d651433d4b1786ad138` |
| `docs/graph/P/packets/P-p11a12.nodes.md` | `2c44ac33bbbf00f297fcbbd7e3270fa464d3da684aba89360e703958d45f86f7` |

Permission envelope: only this report is the new audit result. The requested unchanged signature copy is scratch. No source, signature original, frozen file, manifest, generated file, earlier report or git state was edited. No implementation module was built or rebuilt.

## Disposition of every earlier finding and note

| Item | R3 verdict | Recheck evidence |
|---|---|---|
| F1 — source-local premises | **RESOLVED** | All accepted restrictions on polynomial/uniqueness premises and rectangular periodicity remain exactly as audited in R2; no global extension premise returns. |
| F2 — complete preparation/datum | **RESOLVED at design-signature level** | Full unscaled J/rho domains, actual slow-stage derivative identification, vector/scalar zero jets, the larger initial L and fixed M0*, and the same chosen Q across prepared/amount/data_star are unchanged. The admissibility API remains a required reconciliation port rather than an input assumption. |
| F3 — polar clause (d) | **RESOLVED** | Analytic-domain linearity, both normalizations including `rho/(2*pi)`, and extension uniqueness are unchanged; the consumer uses their accepted fibrewise extension bridge. |
| F4 — rectangular field estimate | **RESOLVED** | The actual frozen Hamiltonian-field bound with separate action weights remains unchanged and supplies the rectangular R2 flow input. |
| F5 — full chart interface | **RESOLVED** | Amount, geometry, both jet identities, full-tensor D2 upper-size transfer, diagonal D3 closeness, good sets and excluded measure all have the required signatures. |
| F5-R2 — wrong closeness gauge | **RESOLVED** | Signatures L1187 and L1190 both use `p11JetBound true`. All other premises, quantifiers, domains and constants are unchanged. The prose now explicitly uses the diagonal jet identity and disclaims a full-tensor premise/polarization factor. |
| N1 — reality correction | **RETAINED, appropriate** | The explicit reality guard remains in `canonical_step_real`; the known p11a2 L248/L287 source issue stays recorded. Physical use must supply the guard. |
| N2 — exact upstream gates | **RETAINED** | Literal secular Hessian/spectrum/lift, finite-stage divisors, fixed-norm derivative control, exact admissibility, lower monotone budget and displacement power remain required interfaces/proofs. This audit does not certify their delivery or proof closure. |
| N3 — totality and choices | **RETAINED** | Boundedness/attainment and positive-small-epsilon choice specifications remain mandatory. No default selector branch is accepted as evidence. |

No new F-numbered finding or required repair is raised.

## F5-R2 closure: fidelity and actual application

The accepted signature is the same proposed correction from audit 2:

```lean
theorem chart_scaling_closeness {n m mu : ℕ} (hn : 1 ≤ n)
    {V : Set (P11Vec n)} (hV : IsOpen V) {f : P11Vec n → P11Vec m}
    (hf : ContDiffOn ℝ mu f V) {E : Set (P11Vec n)} (hEV : E ⊆ V)
    {theta beta' : ℝ} (ht : 0 ≤ theta) (hb : p11JetBound true mu E f theta)
    (y0 : P11Vec n) {lambda : ℝ} (hl : 0 < lambda)
    (hrecheck : max 1 (lambda^mu)*theta ≤ beta'/2) :
    p11JetBound true mu ((fun y => y0+lambda • y) ⁻¹' E)
      (fun y => f (y0+lambda • y)) (beta'/2) := sorry
```

The definition at signatures L57–59 maps `true` to `p11dg`. The source's `bpP:p11a:D3` (p11a1 L157), its packet SOURCE_HYPOTHESES, and `P11DioHyp.close` all use that diagonal gauge. Source `bpP:p11a:chart-scaling` (p11a1 L197–208), particularly clause (c) at L202, requires the same post-scaling recheck. The signature now matches both the supplied and needed predicates.

For each mode k and Euclidean unit frequency direction c, take
`f = p11scalar rho (wt k) c - p11scalar rho w c`, `E = p11thick K v`, and `A y = y0 + lambda • y`.
The source supplies n ≥ 1, E ⊆ V, C^mu regularity of this scalar-family difference, a nonnegative diagonal bound theta, positive lambda, and the explicit recheck when the transformed D3 bound is sought. Polynomial composition supplies regularity without an extra source premise. `chart_scaling_geometry` identifies the preimage thickening with the transformed thickening.

The diagonal half of `chart_scaling_jets` gives, for every j ≤ mu and A y ∈ E,

`p11dg (f ∘ A) j y = lambda^j * p11dg f j (A y) ≤ lambda^j * theta ≤ max 1 (lambda^mu) * theta ≤ beta'/2`.

This includes order zero. For 0 < lambda ≤ 1 the power bound is at most 1; for lambda ≥ 1 it is at most lambda^mu. Positivity/nonnegativity justify both multiplications. The result is exactly diagonal D3 on A⁻¹(E). No full-from-diagonal identification, polarization constant or enlarged theta is needed. The recheck is a genuine caller obligation, as in the source; it is not claimed to follow from arbitrary pre-scaling D3 automatically.

The full-tensor D2 helper `chart_scaling_upper` is deliberately unchanged. Its separate gauge and orders 1..mu+1 remain appropriate. This distinction prevents the previous mismatch from being moved into the size estimate.

**Refutation pass:** checked both Boolean positions rather than only the premise; tested the order-zero and both lambda regimes; inspected the entire prose diff for a leftover full-jet call; compared every unchanged declaration against the R2 signature snapshot. No unsupported replacement premise or new constant dependence survives these checks.

## Consumer, frozen-object, definition and package verdicts

**Consumers: PASS at this design scope.** The repaired companion can now be applied with the scalar-family difference and diagonal bound that D3 actually supplies. The geometric preimage and numerical recheck are explicit. F1–F4's previously accepted consumer bridges remain unchanged. Preparation's same-Q datum and the physical chart/measure/torus ports retain their earlier accepted types and stated reconciliation gates.

**Frozen objects: PASS.** No frozen object or manifest changed. The corrected helper concerns only the existing explicit Euclidean tensor gauges on Pi carriers. It does not redefine a frozen solution, Hamiltonian, torus, phase or neighbourhood. The existing field and action-neighbourhood definitions were rechecked; the physical/secular/torus uses are unchanged from audits 1–2. There is no new global norm or matrix instance.

**Definitions and structures: PASS.** None changed in R3. The accepted explicit constructions, output-only specifications, positive dimensions/parameters and guarded choice/default use remain intact. No conclusion-shaped physical input is introduced by the repair.

**Packages: PASS.** The schedule is unchanged: 30 packages in 12 waves, all estimated at 150–800 lines and no planned Lean file above 1500 lines. W8 owns the corrected companion; its diagonal jet supplier is already in the same chart-scaling package. P8D still follows P8 within wave 11 and the wrapper consumes P8D. No new import edge or cycle is introduced.

**Sources and limitations.** No new pinned-paper erratum, frozen defect or design deviation was found. The enlarged initial L and reality correction remain the explicitly recorded earlier choices. Complexification, radial Schwarz, nonlinear global-flow and variational suppliers, along with the neighbouring KAM interfaces, remain proof obligations. The global graph review and actual theorem bodies are outside this delta approval. R2's exit-143 optional probe remains an unsuccessful historical receipt; it is not relabelled as a successful probe. R3 introduces no Mathlib declaration name or dependency, so the earlier name/type review has no new name surface to check.

## Signature ledger

One row per current named declaration, including definitions and structures. Names are in `KAM.Planetary`; line numbers refer to the pinned R3 file. The unchanged rows inherit audit 2's PASS after exact declaration comparison; the one previously failed signature is rechecked above. PASS describes the design type, not its sorry body.

| Lean name (R3 line) | Blueprint label / responsibility | Verdict | Delta reason |
|---|---|---|---|
| `P11Vec` (L26) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `P11CVec` (L27) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `P11Phase` (L28) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `P11Family` (L29) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `p11euclid` (L31) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `p11dot` (L32) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `p11dotZ` (L33) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `p11dotC` (L35) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `p11thick` (L38) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `p11dg` (L41) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `p11op` (L44) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `p11scalar` (L47) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `p11maxJet` (L50) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `index_def` (L53) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `p11JetBound` (L57) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `p11eta` (L60) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `P11Patch` (L63) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `P11SublevelHyp` (L75) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `p11Csub` (L87) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `p11RNondegenerate` (L91) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `rank_compact` (L93) | `bpP:p11a:rank-compact` | PASS | Declaration unchanged; prior PASS retained |
| `stability` (L99) | `bpP:p11a:stability` | PASS | Declaration unchanged; prior PASS retained |
| `M_bound` (L109) | `bpP:p11a:M-bound` | PASS | Declaration unchanged; prior PASS retained |
| `divided_difference` (L116) | `bpP:p11a:divided-difference` | PASS | Declaration unchanged; prior PASS retained |
| `scalar_sublevel` (L122) | `bpP:p11a:scalar-sublevel` | PASS | Declaration unchanged; prior PASS retained |
| `ball_sublevel` (L128) | `bpP:p11a:ball-sublevel` | PASS | Declaration unchanged; prior PASS retained |
| `sublevel` (L137) | `bpP:p11a:sublevel` | PASS | Declaration unchanged; prior PASS retained |
| `p11Good` (L144) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `P11DioHyp` (L147) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `diophantine_measure` (L163) | `bpP:p11a:diophantine-measure` | PASS | Declaration unchanged; prior PASS retained |
| `p11CDio` (L174) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `p11GammaStar` (L178) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Declaration unchanged; prior PASS retained |
| `power_law` (L181) | `bpP:p11a:power-law` | PASS | Declaration unchanged; prior PASS retained |
| `limit_bridge` (L192) | `bpP:p11a:limit-bridge` | PASS | Declaration unchanged; prior PASS retained |
| `limit_bridge_diophantine` (L197) | `bpP:p11a:limit-bridge` | PASS | Declaration unchanged; prior PASS retained |
| `domain_def` (L205) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11Admissible` (L207) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11Bound` (L211) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11Real` (L213) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11Cut` (L217) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11Taylor` (L220) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11Cutoff` (L222) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11C` (L223) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11Error` (L225) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11Loss` (L226) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11Lambda` (L228) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Declaration unchanged; prior PASS retained |
| `fourier_cutoff` (L229) | `bpP:p11a:fourier-cutoff` | PASS | Declaration unchanged; prior PASS retained |
| `loss_choice` (L239) | `bpP:p11a:loss-choice` | PASS | Declaration unchanged; prior PASS retained |
| `loss_sum` (L245) | `bpP:p11a:loss-sum` | PASS | Declaration unchanged; prior PASS retained |
| `taylor_cutoff` (L255) | `bpP:p11a:taylor-cutoff` | PASS | Declaration unchanged; prior PASS retained |
| `cutoff` (L264) | `bpP:p11a:cutoff` | PASS | Declaration unchanged; prior PASS retained |
| `param_cauchy` (L274) | `bpP:p11a:param-cauchy` | PASS | Declaration unchanged; prior PASS retained |
| `divisor_wide` (L280) | `bpP:p11a:divisor-wide` | PASS | Declaration unchanged; prior PASS retained |
| `divisor_perturb` (L289) | `bpP:p11a:divisor-perturb` | PASS | Declaration unchanged; prior PASS retained |
| `p11Solve` (L299) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11AngleClass` (L303) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11AngleAverage` (L307) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Declaration unchanged; prior PASS retained |
| `homological_maximal` (L309) | `bpP:p11a:homological-maximal` | PASS | Declaration unchanged; prior PASS retained |
| `p11Affine` (L336) | `bpP:p11a:affine-flow / real-flow constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11Flow` (L338) | `bpP:p11a:affine-flow / real-flow constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11GaugeBound` (L341) | `bpP:p11a:affine-flow / real-flow constructions` | PASS | Declaration unchanged; prior PASS retained |
| `P11AffineHyp` (L343) | `bpP:p11a:affine-flow / real-flow constructions` | PASS | Declaration unchanged; prior PASS retained |
| `affine_flow` (L357) | `bpP:p11a:affine-flow` | PASS | Declaration unchanged; prior PASS retained |
| `p11_complexification` (L386) | `stepP:p11:hc-rot / SG1` | PASS | Declaration unchanged; prior PASS retained |
| `p11_real_slice_identity` (L392) | `stepP:p11:hc-rot / SG1` | PASS | Declaration unchanged; prior PASS retained |
| `p11_radial_schwarz` (L397) | `stepP:p11:hc-mean / SG2` | PASS | Declaration unchanged; prior PASS retained |
| `p11_bounded_global_flow` (L403) | `stepP:p11a:rl-global / SG3` | PASS | Declaration unchanged; prior PASS retained |
| `p11RealFlow` (L408) | `bpP:p11a:affine-flow / real-flow constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11_global_variational` (L412) | `stepP:p11a:rl-deriv / SG4` | PASS | Declaration unchanged; prior PASS retained |
| `real_lipschitz` (L420) | `bpP:p11a:real-lipschitz` | PASS | Declaration unchanged; prior PASS retained |
| `P11Step` (L430) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11StepA` (L459) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11StepKappa` (L461) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11StepRem` (L462) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11R0` (L466) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11R1` (L468) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11DeltaH` (L470) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11DeltaW` (L471) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11StepPhi` (L473) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11StepMap` (L477) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11Normal` (L480) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11StepRemainder` (L482) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Declaration unchanged; prior PASS retained |
| `P11StepHyp` (L486) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Declaration unchanged; prior PASS retained |
| `canonical_step` (L500) | `bpP:p11a:canonical-step` | PASS | Declaration unchanged; prior PASS retained |
| `canonical_step_real` (L530) | `stepP:p11a:cs-lip (declared reality repair)` | PASS | Declaration unchanged; prior PASS retained |
| `canonical_step_param` (L545) | `stepP:p11a:cs-param` | PASS | Declaration unchanged; prior PASS retained |
| `P11Physical` (L564) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Declaration unchanged; prior PASS retained |
| `p11Zeta` (L577) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Declaration unchanged; prior PASS retained |
| `p11_zeta_pos` (L579) | `bpP:p6:tube-constants bridge` | PASS | Declaration unchanged; prior PASS retained |
| `forward_tube` (L581) | `bpP:p11:forward-tube` | PASS | Declaration unchanged; prior PASS retained |
| `p11PhysicalDelta` (L590) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Declaration unchanged; prior PASS retained |
| `p11SecularMatrix` (L593) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Declaration unchanged; prior PASS retained |
| `P11PatchData` (L599) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Declaration unchanged; prior PASS retained |
| `P11PatchSpec` (L606) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Declaration unchanged; prior PASS retained |
| `p11_patch` (L620) | `bpP:p11:sec-A#data / P10 port` | PASS | Declaration unchanged; prior PASS retained |
| `p11PatchData` (L621) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Declaration unchanged; prior PASS retained |
| `norm_dict` (L623) | `bpP:p11:norm-dict` | PASS | Declaration unchanged; prior PASS retained |
| `select` (L634) | `bpP:p11:select` | PASS | Declaration unchanged; prior PASS retained |
| `p11WorkingDom` (L641) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Declaration unchanged; prior PASS retained |
| `P11SecularData` (L647) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11ChartInput` (L666) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11WorkingH` (L675) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11FastMean` (L677) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Declaration unchanged; prior PASS retained |
| `P11SecularSpec` (L680) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Declaration unchanged; prior PASS retained |
| `P11SecularFullSpec` (L732) | `bpP:p11:holo-chart / stronger initial L output` | PASS | Declaration unchanged; prior PASS retained |
| `holo_chart` (L738) | `bpP:p11:holo-chart` | PASS | Declaration unchanged; prior PASS retained |
| `p11SecularData` (L740) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11PolarC` (L742) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Declaration unchanged; prior PASS retained |
| `p11PolarR` (L749) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Declaration unchanged; prior PASS retained |
| `total_chart` (L752) | `bpP:p11:total-chart` | PASS | Declaration unchanged; prior PASS retained |
| `total_chart_transport` (L760) | `stepP:p11:tc-lat` | PASS | Declaration unchanged; prior PASS retained |
| `p11K1` (L773) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11Alpha1` (L775) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11s1` (L776) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11d1` (L778) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11eta1` (L779) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Declaration unchanged; prior PASS retained |
| `P11FastData` (L781) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Declaration unchanged; prior PASS retained |
| `P11FastSpec` (L786) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Declaration unchanged; prior PASS retained |
| `avg_fast` (L820) | `bpP:p11:avg-fast` | PASS | Declaration unchanged; prior PASS retained |
| `p11FastData` (L826) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11PolarAverage` (L829) | `bpP:p11:polar-avg raw integral` | PASS | Declaration unchanged; prior PASS retained |
| `polar_avg` (L835) | `bpP:p11:polar-avg` | PASS | Declaration unchanged; prior PASS retained |
| `p11Box` (L849) | `bpP:p11:aniso-bracket / aniso-avg domains` | PASS | Declaration unchanged; prior PASS retained |
| `p11WBound` (L853) | `bpP:p11:aniso-bracket / aniso-avg domains` | PASS | Declaration unchanged; prior PASS retained |
| `aniso_field` (L856) | `bpP:p11:aniso-bracket (field clause)` | PASS | Declaration unchanged; prior PASS retained |
| `polar_average_linear` (L874) | `bpP:p11:polar-avg(d)` | PASS | Declaration unchanged; prior PASS retained |
| `polar_average_normalization` (L884) | `bpP:p11:polar-avg(d)` | PASS | Declaration unchanged; prior PASS retained |
| `polar_extension_unique` (L890) | `bpP:p11:polar-avg / analytic extension bridge` | PASS | Declaration unchanged; prior PASS retained |
| `aniso_bracket` (L897) | `bpP:p11:aniso-bracket` | PASS | Declaration unchanged; prior PASS retained |
| `aniso_avg` (L912) | `bpP:p11:aniso-avg` | PASS | Declaration unchanged; prior PASS retained |
| `p11Rescale` (L955) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11PreparedBox` (L958) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11K2` (L960) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11s2` (L962) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Declaration unchanged; prior PASS retained |
| `P11SlowData` (L964) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11PartialVec` (L973) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Declaration unchanged; prior PASS retained |
| `P11SlowSpec` (L976) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Declaration unchanged; prior PASS retained |
| `avg_slow` (L1034) | `bpP:p11:avg-slow` | PASS | Declaration unchanged; prior PASS retained |
| `p11SlowConstant` (L1038) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11SlowData` (L1041) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Declaration unchanged; prior PASS retained |
| `P11PreparedData` (L1043) | `bpP:p11:prepared / amount outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11PreparedFreq` (L1049) | `bpP:p11:prepared / amount outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11PreparedFreqR` (L1051) | `bpP:p11:prepared / amount outputs` | PASS | Declaration unchanged; prior PASS retained |
| `P11PreparedSpec` (L1053) | `bpP:p11:prepared / amount outputs` | PASS | Declaration unchanged; prior PASS retained |
| `p11M0` (L1089) | `bpP:p11:prepared(d) / M0*` | PASS | Declaration unchanged; prior PASS retained |
| `p11SlowNormalizedFreq` (L1091) | `bpP:p11:prepared(c) / actual normalized frequency` | PASS | Declaration unchanged; prior PASS retained |
| `P11PreparedFullSpec` (L1100) | `bpP:p11:prepared(c),(d) / data-star` | PASS | Declaration unchanged; prior PASS retained |
| `prepared` (L1121) | `bpP:p11:prepared` | PASS | Declaration unchanged; prior PASS retained |
| `p11PreparedData` (L1129) | `bpP:p11:prepared / amount outputs` | PASS | Declaration unchanged; prior PASS retained |
| `amount` (L1132) | `bpP:p11:amount` | PASS | Declaration unchanged; prior PASS retained |
| `chart_scaling` (L1140) | `bpP:p11a:chart-scaling` | PASS | Declaration unchanged; prior PASS retained |
| `chart_scaling_geometry` (L1147) | `bpP:p11a:chart-scaling geometry` | PASS | Declaration unchanged; prior PASS retained |
| `chart_scaling_jets` (L1155) | `bpP:p11a:chart-scaling tensor identities` | PASS | Declaration unchanged; prior PASS retained |
| `chart_scaling_good` (L1164) | `bpP:p11a:chart-scaling(d)` | PASS | Declaration unchanged; prior PASS retained |
| `chart_scaling_upper` (L1175) | `bpP:p11a:chart-scaling(b)` | PASS | Declaration unchanged; prior PASS retained |
| `chart_scaling_closeness` (L1184) | `bpP:p11a:chart-scaling(c) / D3` | PASS | Both diagonal selectors corrected; F5-R2 closed |
| `wrapper` (L1193) | `bpP:p11:wrapper` | PASS | Declaration unchanged; prior PASS retained |
| `p11Order` (L1201) | `stepP:p11:wr-nu` | PASS | Declaration unchanged; prior PASS retained |
| `e4` (L1204) | `bpP:p11:e4` | PASS | Declaration unchanged; prior PASS retained |
| `e5` (L1206) | `bpP:p11:e5` | PASS | Declaration unchanged; prior PASS retained |
| `homological_maximal_real` (L1209) | `bpP:p11a:homological-maximal(d)` | PASS | Declaration unchanged; prior PASS retained |
| `homological_maximal_param` (L1221) | `bpP:p11a:homological-maximal(c)` | PASS | Declaration unchanged; prior PASS retained |
| `p11_normal_affine_bracket` (L1236) | `stepP:p11a:hm-bracket` | PASS | Declaration unchanged; prior PASS retained |
| `cutoff_coefficients` (L1242) | `stepP:p11a:cu-coeff / cutoff(a)` | PASS | Declaration unchanged; prior PASS retained |
| `canonical_step_simple_inverse` (L1250) | `canonical-step(ii), affine-flow(c),(e)` | PASS | Declaration unchanged; prior PASS retained |
| `p11_lambda_spec` (L1264) | `bpP:p11a:sec-hom#lambda` | PASS | Declaration unchanged; prior PASS retained |
| `p11Index` (L1272) | `bpP:p11a:index-def (least positive index)` | PASS | Declaration unchanged; prior PASS retained |
| `p11Amount` (L1274) | `bpP:p11a:index-def (least positive index)` | PASS | Declaration unchanged; prior PASS retained |
| `data_star` (L1277) | `bpP:p11:data-star` | PASS | Declaration unchanged; prior PASS retained |
| `affine_flow_param` (L1297) | `stepP:p11a:af-rest / affine-flow(f)` | PASS | Declaration unchanged; prior PASS retained |
| `p11_trig_derivative_bound` (L1307) | `stepP:p11a:rl-const` | PASS | Declaration unchanged; prior PASS retained |

## Independent verification and closeout

- Ran the supplied signature file **once**, unchanged, after copying it to `.drafts/scratch/P11ASignaturesAuditR3.lean`, with `/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-p11a .drafts/scratch/P11ASignaturesAuditR3.lean`: **exit 0**, **67 warnings**, all `declaration uses sorry`; no errors or other warnings. The gate runs `LEAN_NUM_THREADS=1 nice -n 5 lake env lean` against the shared inp build.
- The six axiom prints (`sublevel`, `canonical_step`, `wrapper`, `prepared`, `data_star`, `chart_scaling_closeness`) each returned `[propext, sorryAx, Classical.choice, Quot.sound]`. These are draft elaboration receipts, not proved theorems.
- Verified exact R2→R3 signature delta: only two Boolean selectors, their explanatory comment, and the added axiom print. Appendix A and the scratch/delivered files agree byte-for-byte; 1320 lines, 171 named declarations, 67 sorry-only theorem bodies; no forbidden declarations or resource overrides.
- Verified 164 unique unchanged graph mapping rows and the unchanged 30-package / 12-wave schedule (150–800 estimated lines each). The source/packet hashes match prior audits. The 171-row ledger preserves all earlier accepted components and closes its one previous FAIL.
- No new Mathlib declaration name is used by the repair. No extra optional probe was launched; the complete R3 signature check includes the corrected type directly. The successful original name review and R2's unsuccessful optional probe retain their distinct historical statuses.
- Audit-owned Lean calls were serial: lint started only after the full signature check exited. No library build, clean, update or cache fetch was run. The design-specific targeted elaboration is the applicable module check; no implementation module changed.

All earlier F-numbered findings are resolved at the design-signature level. The accepted informational notes and upstream/source proof obligations remain explicit; they are not additional design-fix requirements and do not certify mathematical or Lean proof closure.

Final required lint receipt: `LEAN_NUM_THREADS=1 PATH="$PWD/.drafts/scratch/sig-lint-bin:$PATH" nice -n 5 sh scripts/lint_sources.sh` exited **0**. Output: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (144 frozen declarations)`. The pre-existing PATH wrapper routed ABI elaboration through the supplied gate.

Final integrity receipt: `git diff --check` exited **0**; this untracked report also passed an explicit trailing-whitespace/fence scan and has 171 signature-ledger rows, all PASS. The pinned design, delivered signature, audit scratch copy and both earlier reports are unchanged after validation. Final git status contains only the three untracked audit reports; the first two pre-existed. No temporary ABI probe remains from this audit. No state-changing git command was run. **Closeout: PASS for R3's design-signature audit; zero open design findings.**
