# P11A design delta audit 2

Overall verdict: **FAIL**.

Revision 2 resolves F1–F4. F5 is substantially repaired, but its newly advertised source-closeness companion still uses the full tensor gauge where the source and consumer supply the diagonal gauge. One moderate interface finding remains below. This is not a counterexample to the chart-scaling mathematics: the revised jet identities already give a short route to the correct diagonal companion. Under the brief's explicit norm/premise-fidelity rule, the current source-mapped signature and its claimed application require correction before approval.

## Frozen delta and method

Independent tier-2 delta audit under the unchanged design-audit brief and repository rules, using the manuscript-audit method. Audited HEAD `3803613` against parent `3dd384e`; full commit identities are in the verification receipt below. Read the Revision 2 section, updated handoff, all semantic declaration changes, and the original findings. No design, signature, blueprint, frozen file, manifest or earlier report was edited. Only this report persists as the audit result, with the requested signature copy and disposable probe as scratch exceptions.

| Input at delta snapshot v2 | SHA-256 |
|---|---|
| `docs/tracks/P/design/P11A-LEAN-DESIGN.md` | `895bc1dd3cc1f53e359a9728e27b1a4e199772d95ba578a2bb4043485a84776b` |
| `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` | `1a4b339d7d9008ff8d1aa5f2a85addc1b0f3476c40ab8fbf7e922cf3f9be8493` |
| `docs/tracks/P/design/DESIGN-P11A-design-audit-1.md` | `987cb366ade135712e1752d113c62ea8d3ca8010e5543460d5ac188fa82dd72b` |
| `blueprint-P/parts/p11-cp09-preparation.tex` | `4c0e2dfefb50b1e06581e069a55846d25e0e4697a8826514ac699bbb83efb41f` |
| `blueprint-P/parts/p11a1-weak-measure.tex` | `66b5ce26db59b57dbf934938a7bae2fead6b6ff4c7c9d420d33b9582e272bab5` |
| `blueprint-P/parts/p11a2-cutoff-step.tex` | `990694a832aa02dca0138c5cbb3bab842984583f4ca92576479eff04786ed3ec` |
| `docs/graph/P/packets/P-p11.nodes.md` | `067fa835864b522d663c83ac1255f360a5a550e565662d651433d4b1786ad138` |
| `docs/graph/P/packets/P-p11a12.nodes.md` | `2c44ac33bbbf00f297fcbbd7e3270fa464d3da684aba89360e703958d45f86f7` |

The revision changes only the tracked design document: 246 inserted / 171 deleted lines. Removing blank-line and surrounding-comment changes from Appendix A yields **11 changed declarations, 13 additions, no removals and 147 unchanged declarations**. All 24 semantic changes were checked; the ledger below includes the whole current signature inventory (171 rows) so unchanged components are explicitly distinguished from delta findings. The file has 1319 lines and 67 sorry-bodied theorems. No proof closure follows from this inventory.

## Recheck of every earlier finding and note

| Earlier item | Delta verdict | Exact evidence and consumer check |
|---|---|---|
| F1 — source-local premises | **RESOLVED** | `homological_maximal` and its reality/parameter companions restrict polynomial premises to `univ ×ˢ B` or the parameter tube; uniqueness competitors are restricted too. `aniso_bracket` / `aniso_avg` now require periodicity only on their own strip/action domains. The source data supply these premises without controlling arbitrary extensions. The constructed finite sum may still have a stronger global polynomial conclusion. |
| F2 — full preparation/datum | **RESOLVED at design-signature level** | `P11PreparedSpec` restores `‖J-J0‖ < s2/4`, `‖rho‖ < 5/4`; `P11PreparedFullSpec` identifies the normalized map with the actual slow-stage derivatives and exports vector jets through mu and the scalar zeroth jet. `prepared`, the selector, `amount` and `data_star` share that full specification and selected Q. The datum exports the A1–A4 ingredients and amount smallness required by the quantitative KAM source. The exact future admissibility predicate remains an explicitly acknowledged reconciliation port, as permitted by the design brief. |
| F3 — polar averaging clause (d) | **RESOLVED** | `polar_average_linear`, `polar_average_normalization` and `polar_extension_unique` supply analytic-domain linearity, constants, the precise `rho/(2*pi)` normalization, and uniqueness of the holomorphic extension. In `as-osc`, apply the raw identities on the positive-real action region and uniqueness in the connected action polydisc at each fixed J. No connectedness of D or global integral-linearity assumption is required. |
| F4 — rectangular field estimate | **RESOLVED** | `aniso_field` bounds the actual frozen complex Hamiltonian field using angle weight sigma and separate action weights rho1/rho2. Its premises are supplied by the rectangular weighted input and local periodicity; this is the missing R2 input to `aa-same`. It does not substitute the isotropic normal form. |
| F5 — full chart interface | **PARTIALLY RESOLVED** | Geometry, both pointwise jet identities, upper-size transfer, good sets and excluded measure now have explicit signatures. The additional closeness companion has `p11JetBound false` on both sides; source (c)/D3 has `true`. See F5-R2. |
| N1 — reality correction | **RETAINED, appropriate** | The explicit reality guard in `canonical_step_real` remains unchanged. Physical data can supply it; the recorded p11a2 L248/L287 source defect remains declared. |
| N2 — upstream gates | **RETAINED** | Literal secular Hessian, spectrum/lift, finite retained-set divisors, fixed-norm estimate, lower monotone budget and displacement power remain exact-interface/proof obligations. The revised report does not reclassify these sorry packages as delivered proofs. |
| N3 — totality/choice gates | **RETAINED** | Positive dimensions, nonempty compact sets and positive-small-epsilon existence are still required before using infima/suprema and selected outputs. The revised selectors select the stronger specifications; no default value is used as evidence. |

## F5-R2 — Moderate: source closeness is diagonal, but the new companion requires full jets

**Status:** survives refutation as an exact interface/application mismatch; continuation of earlier F5. No mathematical falsity of the full-jet helper is asserted.

**Immutable anchors at v2:**

- Signatures L57–59 define `p11JetBound`: `true` selects `p11dg`; `false` selects `p11op`.
- `chart_scaling_closeness`, signatures L1184–1192, is introduced with the comment “Source chart-scaling (c)” and assumes `hb : p11JetBound false mu E f theta`; its conclusion also uses `false`.
- The design's Revision 2 text L860–864 instructs the consumer to apply this helper to the scalar-family difference from D3 and says that the numerical recheck suffices.
- `blueprint-P/parts/p11a1-weak-measure.tex`, `bpP:p11a:D3` at L157 and `bpP:p11a:chart-scaling` at L197–206, uses the **diagonal** derivative bound. The packet's `bpP:p11a:diophantine-measure` SOURCE_HYPOTHESES likewise explicitly says `dgn(...) <= beta/2`. The existing `P11DioHyp.close` also supplies `p11JetBound true`.

The advertised application therefore has a missing input: source D3 supplies a diagonal bound with theta, whereas the new helper asks for the full-tensor bound with the same theta. The design explicitly keeps these gauges separate. Polynomial composition supplies the scalar difference's `ContDiffOn` premise, not this change of jet-bound predicate. The listed generic polarization inequality is insufficient for the stated same-constant call, because it carries an order-dependent factor.

**Adversarial checks and limits of the finding.** I checked all new companions for an adapter. `chart_scaling_jets` correctly exports BOTH identities, and its diagonal identity directly proves the desired source conclusion by

`dg(f ∘ A, j, y) = lambda^j * dg(f, j, A y) ≤ max 1 (lambda^mu) * theta ≤ beta'/2`.

Thus the mathematical route and the collective ingredients are available. This observation rules out calling the whole chart lemma unprovable or claiming a counterexample to the helper. It does not make the specifically advertised `chart_scaling_closeness` call type-correct from D3, and no same-constant full-from-diagonal bridge is among the supplied signatures. This report does not assume the two gauges must differ for a particular symmetric derivative tensor; the defect is the source-specific premise/conclusion and the unsupported direct application asserted by the design. The audit brief explicitly requires the intended norm and the hypotheses the consumer actually supplies.

**Proposed fix:** replace both occurrences of `false` in this source-specific companion with `true`, using the existing diagonal identity in its proof. Alternatively parameterize the helper by the gauge Boolean and instantiate it with `true`; retain a full-jet helper under a distinct name if useful. Update the Revision 2 explanation accordingly. Do not insert a stronger D3 premise or a polarization loss into the blueprint. The direct corrected signature is:

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

The corrected signature is a proposal, not an applied repair; its scratch elaboration is reported separately from the once-only unchanged R2 signature check.

## Checks on the rest of the touched surface

**Fidelity and constants: PASS except F5-R2.** The extra Euclidean zeroth-order bound in `P11SecularFullSpec` is a declared stronger output obtained by enlarging the freely chosen initial L. No source premise is added. Its selection occurs before nu and epsilon; later strip/radius choices shrink as necessary. `p11M0 = (2*n+1)^(mu+1)*(2*L+1)` is fixed before nu/epsilon and is an allowed explicit choice of the source's dimension/order factor. Scalar `M*`, Hessian `C1`, the logarithmic exponent and the amount `(beta_J/2)*eps^(mu+2)` retain their prescribed dependence and normalization. Finite rescaled higher derivatives can be made uniformly small by lowering the epsilon threshold; the larger vector constant pays the Euclidean/max comparison rather than changing the ambient norm.

**Definitions: PASS.** `p11SlowNormalizedFreq` evaluates the actual complex derivatives of `h0+g2` at `(J, eps*(2*pi+rho))`, takes real parts and divides the slow block by eps. The full specification applies it only for sufficiently small positive eps in the stated slow-stage domain. The raw total definition outside that domain supplies no theorem claim. The duplicated full-domain J-jet conjunct is redundant with the base prepared specification but harmless. All added specification fields occur in existential outputs, never as extra physical input assumptions.

**Consumers/frozen objects: PASS for F1–F4; FAIL for the advertised F5-R2 call.** Prepared A1–A4 refer to the same selected Q: the actual N/P and physical chain, gradient, scalar derivatives, vector jets and amount are not assembled from independently chosen witnesses. The exact 11a5 admissibility/budget predicate remains a port, as already accepted in audit 1. The altered predicates introduce no replacement Hamiltonian, solution, torus, secular-average or neighbourhood object. Rechecked the frozen Hamiltonian field and neighbourhood definitions; existing secular/physical predicates are unchanged from audit 1. The new field bound uses `KAM.hamiltonianVectorFieldℂ`, and all carriers remain Pi types with their existing max norm. Frozen/manifest equality is also checked by lint.

**Packages: PASS.** The revised table has 30 packages and 12 waves. W8 gains ChartScaling (700 lines total), P3 gains the field estimate (450), P6 gains polar companions (650), and P8 splits into Prepared/Amount (750) followed by P8D Datum (300). P8D follows P8 within wave 11; the wrapper now depends on P8D. That explicit within-wave order avoids a cycle. The new geometry/jet helpers can depend on W0 alone, while the other W8 components retain the existing W7 dependencies. No planned implementation file exceeds 1500 lines, and all packages remain within 150–800 lines. These are planning checks, not verified estimates of eventual proof length.

**Source gaps and errata: unchanged.** No new pinned-paper or frozen-declaration defect was found. Complexification, radial Schwarz, nonlinear global-flow and variational suppliers remain new proof work. The known optional-reality defect stays explicitly repaired in its guarded companion. F5-R2 is a design adapter mismatch, not a suspected paper erratum.

## Signature ledger

One row per current named declaration. Unchanged rows inherit audit 1's bounded design verdict after normalized-signature comparison; changed/new rows were rechecked in this delta. Names are in `KAM.Planetary`; line numbers refer to the pinned R2 signature hash above. PASS approves the design type at this scope, not its sorry body.

| Lean name (R2 line) | Blueprint label / responsibility | Verdict | Delta reason |
|---|---|---|---|
| `P11Vec` (L26) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11CVec` (L27) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11Phase` (L28) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11Family` (L29) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11euclid` (L31) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11dot` (L32) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11dotZ` (L33) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11dotC` (L35) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11thick` (L38) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11dg` (L41) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11op` (L44) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11scalar` (L47) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11maxJet` (L50) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `index_def` (L53) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11JetBound` (L57) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11eta` (L60) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11Patch` (L63) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11SublevelHyp` (L75) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Csub` (L87) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11RNondegenerate` (L91) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `rank_compact` (L93) | `bpP:p11a:rank-compact` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `stability` (L99) | `bpP:p11a:stability` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `M_bound` (L109) | `bpP:p11a:M-bound` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `divided_difference` (L116) | `bpP:p11a:divided-difference` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `scalar_sublevel` (L122) | `bpP:p11a:scalar-sublevel` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `ball_sublevel` (L128) | `bpP:p11a:ball-sublevel` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `sublevel` (L137) | `bpP:p11a:sublevel` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Good` (L144) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11DioHyp` (L147) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `diophantine_measure` (L163) | `bpP:p11a:diophantine-measure` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11CDio` (L174) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11GammaStar` (L178) | `bpP:p11a:index-def / conv / S1–S3 / D1–D4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `power_law` (L181) | `bpP:p11a:power-law` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `limit_bridge` (L192) | `bpP:p11a:limit-bridge` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `limit_bridge_diophantine` (L197) | `bpP:p11a:limit-bridge` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `domain_def` (L205) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Admissible` (L207) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Bound` (L211) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Real` (L213) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Cut` (L217) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Taylor` (L220) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Cutoff` (L222) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11C` (L223) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Error` (L225) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Loss` (L226) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Lambda` (L228) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `fourier_cutoff` (L229) | `bpP:p11a:fourier-cutoff` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `loss_choice` (L239) | `bpP:p11a:loss-choice` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `loss_sum` (L245) | `bpP:p11a:loss-sum` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `taylor_cutoff` (L255) | `bpP:p11a:taylor-cutoff` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `cutoff` (L264) | `bpP:p11a:cutoff` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `param_cauchy` (L274) | `bpP:p11a:param-cauchy` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `divisor_wide` (L280) | `bpP:p11a:divisor-wide` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `divisor_perturb` (L289) | `bpP:p11a:divisor-perturb` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Solve` (L299) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11AngleClass` (L303) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11AngleAverage` (L307) | `bpP:p11a:domain-def / cutoff constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `homological_maximal` (L309) | `bpP:p11a:homological-maximal` | PASS | Rechecked local premises; F1 resolved |
| `p11Affine` (L336) | `bpP:p11a:affine-flow / real-flow constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Flow` (L338) | `bpP:p11a:affine-flow / real-flow constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11GaugeBound` (L341) | `bpP:p11a:affine-flow / real-flow constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11AffineHyp` (L343) | `bpP:p11a:affine-flow / real-flow constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `affine_flow` (L357) | `bpP:p11a:affine-flow` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11_complexification` (L386) | `stepP:p11:hc-rot / SG1` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11_real_slice_identity` (L392) | `stepP:p11:hc-rot / SG1` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11_radial_schwarz` (L397) | `stepP:p11:hc-mean / SG2` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11_bounded_global_flow` (L403) | `stepP:p11a:rl-global / SG3` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11RealFlow` (L408) | `bpP:p11a:affine-flow / real-flow constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11_global_variational` (L412) | `stepP:p11a:rl-deriv / SG4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `real_lipschitz` (L420) | `bpP:p11a:real-lipschitz` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11Step` (L430) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11StepA` (L459) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11StepKappa` (L461) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11StepRem` (L462) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11R0` (L466) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11R1` (L468) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11DeltaH` (L470) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11DeltaW` (L471) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11StepPhi` (L473) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11StepMap` (L477) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Normal` (L480) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11StepRemainder` (L482) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11StepHyp` (L486) | `bpP:p11a:canonical-step standing data / explicit outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `canonical_step` (L500) | `bpP:p11a:canonical-step` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `canonical_step_real` (L530) | `stepP:p11a:cs-lip (declared reality repair)` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `canonical_step_param` (L545) | `stepP:p11a:cs-param` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11Physical` (L564) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Zeta` (L577) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11_zeta_pos` (L579) | `bpP:p6:tube-constants bridge` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `forward_tube` (L581) | `bpP:p11:forward-tube` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11PhysicalDelta` (L590) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11SecularMatrix` (L593) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11PatchData` (L599) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11PatchSpec` (L606) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11_patch` (L620) | `bpP:p11:sec-A#data / P10 port` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11PatchData` (L621) | `bpP:p11:sec-A#data / literal frozen secular bridge` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `norm_dict` (L623) | `bpP:p11:norm-dict` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `select` (L634) | `bpP:p11:select` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11WorkingDom` (L641) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11SecularData` (L647) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11ChartInput` (L666) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11WorkingH` (L675) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11FastMean` (L677) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11SecularSpec` (L680) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11SecularFullSpec` (L732) | `bpP:p11:holo-chart / stronger initial L output` | PASS | Stronger true bound; enlarge freely chosen L before nu/eps |
| `holo_chart` (L738) | `bpP:p11:holo-chart` | PASS | Selects declared stronger initial-L output; F2 resolved |
| `p11SecularData` (L740) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Text unchanged; rechecked stronger holo_chart choice semantics |
| `p11PolarC` (L742) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11PolarR` (L749) | `bpP:p11:holo-chart / total-chart constructions` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `total_chart` (L752) | `bpP:p11:total-chart` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `total_chart_transport` (L760) | `stepP:p11:tc-lat` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11K1` (L773) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Alpha1` (L775) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11s1` (L776) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11d1` (L778) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11eta1` (L779) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11FastData` (L781) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11FastSpec` (L786) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `avg_fast` (L820) | `bpP:p11:avg-fast` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11FastData` (L826) | `bpP:p11:sec-C#data / avg-fast outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11PolarAverage` (L829) | `bpP:p11:polar-avg raw integral` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `polar_avg` (L835) | `bpP:p11:polar-avg` | PASS | Text unchanged; added companions close F3 |
| `p11Box` (L849) | `bpP:p11:aniso-bracket / aniso-avg domains` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11WBound` (L853) | `bpP:p11:aniso-bracket / aniso-avg domains` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `aniso_field` (L856) | `bpP:p11:aniso-bracket (field clause)` | PASS | Correct frozen field and anisotropic weights; F4 resolved |
| `polar_average_linear` (L874) | `bpP:p11:polar-avg(d)` | PASS | Analytic-domain integrability licenses linearity; F3 resolved |
| `polar_average_normalization` (L884) | `bpP:p11:polar-avg(d)` | PASS | Exact constant/quadratic values including 2*pi; F3 resolved |
| `polar_extension_unique` (L890) | `bpP:p11:polar-avg / analytic extension bridge` | PASS | Fibrewise connected-polydisc identity bridge; F3 resolved |
| `aniso_bracket` (L897) | `bpP:p11:aniso-bracket` | PASS | Rechecked local premises; F1 resolved |
| `aniso_avg` (L912) | `bpP:p11:aniso-avg` | PASS | Rechecked local premises; F1 resolved |
| `p11Rescale` (L955) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11PreparedBox` (L958) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11K2` (L960) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11s2` (L962) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11SlowData` (L964) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11PartialVec` (L973) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11SlowSpec` (L976) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `avg_slow` (L1034) | `bpP:p11:avg-slow` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11SlowConstant` (L1038) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11SlowData` (L1041) | `bpP:p11:sec-D#data / avg-slow outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11PreparedData` (L1043) | `bpP:p11:prepared / amount outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11PreparedFreq` (L1049) | `bpP:p11:prepared / amount outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11PreparedFreqR` (L1051) | `bpP:p11:prepared / amount outputs` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `P11PreparedSpec` (L1053) | `bpP:p11:prepared / amount outputs` | PASS | Full prepared outputs and consistent selection; F2 resolved |
| `p11M0` (L1089) | `bpP:p11:prepared(d) / M0*` | PASS | Explicit dimension/order constant fixed before nu/eps |
| `p11SlowNormalizedFreq` (L1091) | `bpP:p11:prepared(c) / actual normalized frequency` | PASS | Actual slow-stage derivatives; slow block divided by eps |
| `P11PreparedFullSpec` (L1100) | `bpP:p11:prepared(c),(d) / data-star` | PASS | Full unscaled domain, vector and scalar zero jets; F2 resolved |
| `prepared` (L1121) | `bpP:p11:prepared` | PASS | Full prepared outputs and consistent selection; F2 resolved |
| `p11PreparedData` (L1129) | `bpP:p11:prepared / amount outputs` | PASS | Full prepared outputs and consistent selection; F2 resolved |
| `amount` (L1132) | `bpP:p11:amount` | PASS | Full prepared outputs and consistent selection; F2 resolved |
| `chart_scaling` (L1140) | `bpP:p11a:chart-scaling` | PASS | Text unchanged; amount clause retained; see residual F5-R2 on companion |
| `chart_scaling_geometry` (L1147) | `bpP:p11a:chart-scaling geometry` | PASS | Correct inverse dilation for diameter/thickness/outer volume |
| `chart_scaling_jets` (L1155) | `bpP:p11a:chart-scaling tensor identities` | PASS | Correct lambda^j identity for both gauges |
| `chart_scaling_good` (L1164) | `bpP:p11a:chart-scaling(d)` | PASS | Correct preimage good set and lambda^n excluded measure |
| `chart_scaling_upper` (L1175) | `bpP:p11a:chart-scaling(b)` | PASS | Correct full-tensor upper-size transfer |
| `chart_scaling_closeness` (L1184) | `bpP:p11a:chart-scaling(c) / D3` | FAIL | F5-R2: full-jet predicate does not match source diagonal D3 |
| `wrapper` (L1193) | `bpP:p11:wrapper` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Order` (L1201) | `stepP:p11:wr-nu` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `e4` (L1204) | `bpP:p11:e4` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `e5` (L1206) | `bpP:p11:e5` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `homological_maximal_real` (L1209) | `bpP:p11a:homological-maximal(d)` | PASS | Rechecked local premises; F1 resolved |
| `homological_maximal_param` (L1221) | `bpP:p11a:homological-maximal(c)` | PASS | Rechecked local premises; F1 resolved |
| `p11_normal_affine_bracket` (L1236) | `stepP:p11a:hm-bracket` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `cutoff_coefficients` (L1242) | `stepP:p11a:cu-coeff / cutoff(a)` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `canonical_step_simple_inverse` (L1250) | `canonical-step(ii), affine-flow(c),(e)` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11_lambda_spec` (L1264) | `bpP:p11a:sec-hom#lambda` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Index` (L1272) | `bpP:p11a:index-def (least positive index)` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11Amount` (L1274) | `bpP:p11a:index-def (least positive index)` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `data_star` (L1277) | `bpP:p11:data-star` | PASS | Full prepared outputs and consistent selection; F2 resolved |
| `affine_flow_param` (L1297) | `stepP:p11a:af-rest / affine-flow(f)` | PASS | Unchanged normalized declaration; audit 1 PASS retained |
| `p11_trig_derivative_bound` (L1307) | `stepP:p11a:rl-const` | PASS | Unchanged normalized declaration; audit 1 PASS retained |

## Verification and closeout

- Exact commits: R2 `3803613aad2c3a03784ade891edcaa2601e99e23`; parent `3dd384e6d23d2b32de6cbb7d4f6549dcd6c68e9a`. The original three blueprint hashes and the two source-packet hashes match audit 1.
- Copied the supplied R2 signatures unchanged to `.drafts/scratch/P11ASignaturesAuditR2.lean`. Ran that copy **once** with `/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-p11a .drafts/scratch/P11ASignaturesAuditR2.lean`: **exit 0**, **67 warnings**, all `declaration uses sorry`; no errors or other warnings. The gate sets `LEAN_NUM_THREADS=1` and `nice -n 5` and uses the shared inp build.
- `#print axioms` for `sublevel`, `canonical_step`, `wrapper`, `prepared` and `data_star` each returned `[propext, sorryAx, Classical.choice, Quot.sound]`. This is an elaboration receipt for a design, not proof closure.
- The optional `.lake/abi-scratch/P11A-delta-probe.lean` contained a corrected diagonal companion and Mathlib name checks. It terminated with **exit 143 and no diagnostics**; it supplies no successful elaboration or name-check receipt. Its cause was not established. Memory pressure was observed while it ran; no external process was interrupted by this audit. The probe was deleted. No newly named Mathlib dependency was introduced by R2; the audit-1 name/type receipt remains historical, and the relevant Haar/Schwarz/integral declarations were also located in the current pinned library source. Fresh probe completion is an explicit validation limitation, not evidence that a declaration is missing.
- Static checks passed: **164 actual scoped records = 164 unique mapping rows**, no omissions or extras; **30 packages / 12 waves**, all estimated at 150–800 lines; **1319 signature lines**, **171 named declarations**, **67 sorry-only theorem bodies**, no forbidden declarations or resource overrides; Appendix A equals the supplied signature file.
- No implementation module was edited or rebuilt. The design brief's narrow signature elaboration is the applicable targeted Lean check. All audit-owned Lean calls were sequential; the optional probe had exited before lint was launched.

Open closeout item: F5-R2's source-specific gauge mismatch. F1–F4 are closed at the design-signature level; F5's other missing clauses are supplied. This report does not authorize changing any frozen theorem or source, and does not claim KAM proof completion.

Final required lint receipt: `LEAN_NUM_THREADS=1 PATH="$PWD/.drafts/scratch/sig-lint-bin:$PATH" nice -n 5 sh scripts/lint_sources.sh` exited **0**. Output: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (144 frozen declarations)`. The pre-existing wrapper routed ABI elaboration through the supplied gate.

Final report checks: `git diff --check` exited **0**; an explicit scan of this untracked report found no trailing whitespace and balanced code fences, with 171 signature rows. The supplied signatures, their audit scratch copy, the audited design and audit 1 retain the pinned hashes above. The disposable probe was removed. Final git status contains only the two untracked audit reports; audit 1 pre-existed and was not changed. No state-changing git command was run.
