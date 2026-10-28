# P11A-C8 independent package audit 1

Overall verdict: **FAIL on the requested naming-hygiene gate only (F1)**. The mathematical C8 slice is complete and passes the current amended signature, proof, axiom and kernel checks described below. Rename one public helper before accepting the package under the literal AUDIT FOCUS. No mathematical counterexample to the amended exports was found.

This is a report-only audit in `/root/code/KAM-inp-p11ac8`, at HEAD `e4164985defb6f3c43f492b1609b2b42da25bf32`, compared using `git diff inp...HEAD`; observed `inp` was `d9183adae208ecf2e726620694b69c8168e33006`. Git warns that there are multiple merge bases and uses `003b1db80283ab9f885b58a8e415ba28053b37df`. The 19-file comparison contains inherited C7 work and a HomologicalBracket change; this audit follows the explicit restriction to the ten `KAM/Planetary/MaximalStep/Step*.lean` files. C7 is consumed as an already audited dependency, not independently recertified here.

Read the supplied package brief, AGENTS.md, PLAN, DECISIONS, handoff/AUDIT FOCUS, the P statement, relevant frozen definitions and planetary anchors, blueprint `p11a2-cutoff-step.tex`, design row/companions/Appendix A, and the three P11A design-audit reports. The user's exact report destination overrides the generic brief's instruction to write in the main inp worktree. No source, frozen file, manifest, generated file or git state was edited.

No frozen anchor is proved or sealed by C8. Provider/frozen-export type equality and a frozen seal-body test are therefore **not applicable**: these are infrastructure declarations in `KAM.Planetary`, not provider exports. Instead, five signature-copy declarations were elaborated under fresh names with direct calls to their C8 implementations, followed by `example : type_of% @audit_sig_<name> := @<name>` for each. No draft-sorry signature file was imported.

| C8 export / anchor scope | Verdict | Evidence |
|---|---|---|
| `canonical_step` | PASS WITH NOTES | Exact current signature; all complex clauses; package F1 naming cleanup remains. |
| `canonical_step_param` | PASS WITH NOTES | Exact current signature, including arbitrary remainder bound Mr and all j ≥ 1; F1. |
| `canonical_step_real` | PASS WITH NOTES | Exact current signature with the approved explicit reality guard; F1. |
| `cutoff_coefficients` | PASS WITH NOTES | Exact **amended** signature; old off-B assertion is false; see D1 below. |
| `canonical_step_simple_inverse` | PASS WITH NOTES | Exact current signature; simple representation and both inverse identities; F1. |
| P-G / P-PLANAR / P-FIXED and other frozen physical headlines | Not audited for closure | C8 seals none and imports no frozen theorem or provider. |

## Findings and definition review

**F1 — minor but explicit acceptance failure: reused public short name.** `StepHom.lean:66` declares public `KAM.Planetary.step_small`; `KAM/Apost/Constants.lean:702` already declares public `KAM.Apost.step_small`. The AUDIT FOCUS requires “no public short name used elsewhere in KAM”. These are distinct fully qualified names, so this is not a kernel collision or a mathematical gap, but the literal requested hygiene condition fails. Rename the C8 helper (for example `p11_step_small`) and update uses at `StepHom.lean:141`, `StepRemainder.lean:58,66`. No edit was made by the auditor. The other textual match, `poissonBracket_congr` at `KAM/Nekhoroshev/NormalForm/IterativeRemainder.lean:95`, is **private** and does not violate this public-name condition. No public short-name match with a root declaration, root namespace declaration introduced by C8, or `_root_` shadow was found. All 104 named C8 declarations are in `KAM.Planetary`.

**Definition classification (all 23 named definitions/structures).**

- `P11Step`: source geometry, radii, cutoff/divisor/flow smallness and signs. `P11StepHyp`: holomorphy/reality/admissibility, input sup bound and derivative/divisor assumptions. Neither bundles a hard step conclusion.
- `p11StepA`, `p11StepKappa`, `p11StepRem`: literal explicit real formulas. Positive denominators and q ≤ 1/2 are supplied by the step structure; no division fallback is used in their estimates.
- `p11R0`, `p11R1`: restriction of the actual cutoff to eta=0 and its action derivative. `p11DeltaH`, `p11DeltaW`: actual zero Fourier coefficient averages. Totalized derivatives/integrals have their usual Lean values off regular domains; C8 proves regularity on every domain where it uses analytic identities. It does not claim the false global affine identity.
- `p11StepPhi`: explicit homological affine generator; `p11StepMap`: actual time-one selected Hamiltonian flow; `p11Normal`: literal h+omega·eta; `p11StepRemainder`: literal conjugation defect. The flow existence/uniqueness premises are derived in `step_affHyp`, not assumed as an output-shaped field.
- `stepF0`, `stepF1`, `stepFam0`, `stepFam1`: literal Taylor coefficient slices and eta-independent lifts. `stepP0`, `stepP1`: literal scalar/componentwise homological solutions.
- `stepAvg`, `stepW`, `stepU`: explicit average, negative cutoff oscillation, and `(1-t) stepW + R`. `stepV`: real part of the actual angle field. The real-flow identification is proved under the reality guard; taking the real part alone is not used as a substitute for reality.

All 13 signature data declarations match the current signature after comment/whitespace removal, including structure field order. All five requested theorem statement texts match after whitespace removal, including binder order, constants, norms and carriers. No new abbrev or hidden output specification occurs. Scratch parsing was corrected to distinguish type-level `let ... :=` from the final theorem proof delimiter before concluding textual equality; independent elaboration also passed.

## Counterexample and approved amendment

**D1 — confirmed design-signature defect, repaired by the explicit overnight ruling.** Local `docs/tracks/P/design/P11A-LEAN-DESIGN.md:2191` still says

`∀ z, p11Cutoff T R z = p11R0 T R (z.1.1,z.2) + ∑ i, p11R1 T R (z.1.1,z.2) i*z.1.2 i`.

The previous design audits accepted this clause, but it is false. This is a defect in the drafted companion, not a newly asserted erratum in a pinned published paper. The live main-inp design amendment and handoff record the orchestrator's D29 ruling; current signature line 1252 and `StepCoeff.lean:375` add only `z.2 ∈ B` to this clause. The package worktree's older design snapshot has not incorporated that amendment.

Independent mathematical check against `Basic.lean:52-61`, `Weighted/Norm.lean:48` and `Weighted/Projections.lean:37`: take n=1, r=2, s=1, d=1, epsilon=0, T=0, B empty (open; all regularity and boundedness premises are vacuous), and an off-B parameter b. Let f(theta)=1/(Re theta_0), with its finite totalized value 0 when Re theta_0=0. On the real unit interval f is non-integrable. Define R((theta,eta),b)=f(theta)+eta_0*(1-f(theta)), independently of b. R is affine and complex differentiable in eta everywhere, so p11Taylor R = R. At eta_0=1 the integrand is constantly 1, hence the T=0 cutoff is 1. At any eta_0≠1, `(1-eta_0) f + eta_0` is non-integrable: otherwise subtracting the integrable constant and dividing by the nonzero scalar would make f integrable. Thus the Bochner integral is 0. The cutoff as a function of eta is 0 on a neighborhood of eta=0 (for example |eta_0|<1/2); consequently p11R0=0 and p11R1=0. At eta_0=1 the old identity says 1=0. This also fills in the derivative-at-zero step implicit in the handoff's f,g argument. It is an analytic counterexample, not a separately formalized Lean counterexample.

The amendment is minimal as a domain correction: only the decomposition clause gains membership, with no change to its first two bounds or global assumptions. It does not restrict theta or eta unnecessarily. On B, admissibility gives continuous real-angle slices of the Taylor coefficients and their integrability on the compact unit cube; `coeff_add_sum` then supplies valid integral linearity. A weaker integrability-specific condition could alternatively suffice, but is unnecessary for the source. `cs-cutoff` concerns D(r-d,s;B), and all C8 uses of the decomposition (`step_avg_eq`, `step_bracket_N`, `step_R1_eq`) explicitly possess b∈B. No consumer needs an off-B assertion.

**Existing declared reality repair retained.** Blueprint `p11a2-cutoff-step.tex:248` allows R to be real “if reality is wanted” while the real-Lipschitz conclusion at line 264 is unguarded. The design's SG5 and design-audit-1 N1 already recognize this. `canonical_step_real` keeps the explicit `p11Real ... R` premise of the approved signature; no new premise was silently introduced by C8. Complex and parameter results remain independent of R reality. No new frozen defect or pinned-paper erratum was found.

## Proof and completeness review

`p11_cutoff_coeff` supplies all seven clauses: angle classes, polynomial identities on univ×B, scalar/vector bounds without a component-count loss, and the amended affine decomposition. `cutoff_coefficients` projects clauses 5–7. The derivative coefficient proof uses the affine decomposition only on B; finite truncation idempotence is proved even for arbitrary total input via its finite Fourier sum.

`step_hdiv` transfers the source real divisor bound to the whole action tube; `step_hm0/1` solve the homological equations with M0 and M0/s. `step_affHyp` derives every affine-flow premise from these bounds and the input smallness. `canonical_step` includes joint holomorphy, image domain, both displacements, gauge and ordinary derivative estimates, canonical form preservation, integer equivariance, remainder admissibility, both remainder bounds and the literal conjugation identity. Its epsilon=0 case never divides by epsilon or A.

The integral Lie work is present, not merely an assumption: `step_bracket_N` proves `{N,phi}=-(R_*-average)` with the frozen field's sign; `step_remainder_eq` invokes `Canonical.taylor_poschel` and proves the integral integrand replacement by local equality of differentiable functions. `step_U_le` gives U=(5+4E)epsilon on D(r-d,s). `flow_displacement_t` proves bounds for every t∈[-1,1]. At X^t z, `step_bracket_bound` uses closed coordinate discs of radii sigma and s/4 lying in the original open domain (the strict input action bound is retained even at q=1/2). Coordinate Cauchy bounds yield n*[A*U/sigma + ((n+1)sA/sigma)*4U/s] = n(4n+5)UA/sigma. `step_remainder_le` integrates and adds the cutoff error; `canonical_step` derives the coefficient 18 from E≤1 and q²/(1-q)≤2q². No integral identity or bracket estimate is assumed as a bundled premise.

`canonical_step_param` uses `param_cauchy_scalar` for scalar deltaH and remainder and `param_cauchy` for vector deltaW and displacements. Both have the identical j^j/(t-tp)^j estimate on the same tube; the scalar version even omits an unnecessary nonnegativity hypothesis. The arbitrary Mr premise is an output-bound refinement of the derivative clause, not an assumed canonical-step conclusion. A usable Mr=p11StepRem is proved by the complex step. No additional parameter-radius loss is introduced.

`StepReal` transfers reality through cutoff, homological coefficients, averages, actual flow and remainder. `StepRealFlow` obtains the real derivative bound from Fourier coefficient decay and the nonzero-mode lattice sum; it proves equality with the actual real angle flow by ODE uniqueness. The exponential bound has exactly 2T(1+E)epsilon Lambda(r-d)/(Ds), with no missing 2pi or dimension factor.

`canonical_step_simple_inverse` chooses Theta/M/v separately for each b∈B using affine_flow clause 4; the resulting parameterized functions use the same chosen slice at each b, so their theta derivatives are those of the original slice. No holomorphy in b of these auxiliary choices is asserted. The representation restricts from the larger flow domain using `step_z_mem`. For inverse identities, q≤1/2 gives membership in V=D(r1-2sigma,s/2), allowing clause 9. Both compositions are asserted and proved for z∈U, without assuming the inverse input remains in U.

## Declaration ledger

Every new named declaration is listed below (104 rows: 81 public theorems, 21 defs, 2 structures). `A` in a theorem note means its independent `#print axioms` output was exactly `[propext, Classical.choice, Quot.sound]`. Helper rows are supporting lemmas for the indicated blueprint node, not replacements for stronger source exports. Exact signed exports and data have the additional signature checks above.

| Node / file:line | Lean declaration (`KAM.Planetary.` prefix) | Verdict | Reason / note |
|---|---|---|---|
| `Step:28` | `step_normal_diff` | PASS | canonical-step(i)-(iii), cs-flow: joint flow, admissibility and assembly; A |
| `Step:36` | `step_U_mem` | PASS | canonical-step(i)-(iii), cs-flow: joint flow, admissibility and assembly; A |
| `Step:42` | `step_stepMap_diff` | PASS | canonical-step(i)-(iii), cs-flow: joint flow, admissibility and assembly; A |
| `Step:55` | `step_mapsU` | PASS | canonical-step(i)-(iii), cs-flow: joint flow, admissibility and assembly; A |
| `Step:66` | `domain_def_mono` | PASS | canonical-step(i)-(iii), cs-flow: joint flow, admissibility and assembly; A |
| `Step:72` | `step_Rp_admissible` | PASS | canonical-step(i)-(iii), cs-flow: joint flow, admissibility and assembly; A |
| `Step:109` | `canonical_step` | PASS | canonical-step(i)-(iii), cs-flow: joint flow, admissibility and assembly; A |
| `Step:200` | `canonical_step_simple_inverse` | PASS | canonical-step(i)-(iii), cs-flow: joint flow, admissibility and assembly; A |
| `StepBound:26` | `stepAvg` | PASS | cs-u / cs-hom: explicit average, negative oscillation, Lie integrand and bounds; definition classification above |
| `StepBound:30` | `stepW` | PASS | cs-u / cs-hom: explicit average, negative oscillation, Lie integrand and bounds; definition classification above |
| `StepBound:34` | `stepU` | PASS | cs-u / cs-hom: explicit average, negative oscillation, Lie integrand and bounds; definition classification above |
| `StepBound:37` | `coeff_congr_param` | PASS | cs-u / cs-hom: explicit average, negative oscillation, Lie integrand and bounds; A |
| `StepBound:44` | `step_avg_eq` | PASS | cs-u / cs-hom: explicit average, negative oscillation, Lie integrand and bounds; A |
| `StepBound:68` | `step_avg_le` | PASS | cs-u / cs-hom: explicit average, negative oscillation, Lie integrand and bounds; A |
| `StepBound:89` | `step_W_le` | PASS | cs-u / cs-hom: explicit average, negative oscillation, Lie integrand and bounds; A |
| `StepBound:103` | `step_U_diff` | PASS | cs-u / cs-hom: explicit average, negative oscillation, Lie integrand and bounds; A |
| `StepBound:125` | `step_U_le` | PASS | cs-u / cs-hom: explicit average, negative oscillation, Lie integrand and bounds; A |
| `StepBound:142` | `fderiv_pi_apply` | PASS | cs-u / cs-hom: explicit average, negative oscillation, Lie integrand and bounds; A |
| `StepBound:150` | `step_bracket_N` | PASS | cs-u / cs-hom: explicit average, negative oscillation, Lie integrand and bounds; A |
| `StepCoeff:30` | `stepF0` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; definition classification above |
| `StepCoeff:33` | `stepF1` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; definition classification above |
| `StepCoeff:36` | `coeff_add_sum` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:65` | `truncate_add_sum` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:91` | `taylor_eq` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:101` | `stepF1_eq` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:116` | `norm_half_single` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:124` | `stepF0_diff` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:131` | `stepF1_diff` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:143` | `stepF0_periodic` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:149` | `stepF1_periodic` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:160` | `norm_stepF0_le` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:165` | `norm_stepF1_le` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:181` | `truncate_congr_param` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:189` | `truncate_truncate` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:211` | `continuous_stepF0` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:218` | `continuous_stepF1` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:225` | `cutoff_decomp` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:237` | `cutoff_R0` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:244` | `cutoff_R1` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:260` | `stepFam0` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; definition classification above |
| `StepCoeff:262` | `stepFam1` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; definition classification above |
| `StepCoeff:264` | `cut_stepFam0` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:267` | `cut_stepFam1` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:272` | `p11_cutoff_coeff` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepCoeff:367` | `cutoff_coefficients` | PASS | cs-cutoff: Taylor coefficients, regular slices, finite Fourier truncation and bounds; A |
| `StepData:28` | `P11Step` | PASS | canonical-step data: literal current signature; explicit source data/object; definition classification above |
| `StepData:57` | `p11StepA` | PASS | canonical-step data: literal current signature; explicit source data/object; definition classification above |
| `StepData:59` | `p11StepKappa` | PASS | canonical-step data: literal current signature; explicit source data/object; definition classification above |
| `StepData:60` | `p11StepRem` | PASS | canonical-step data: literal current signature; explicit source data/object; definition classification above |
| `StepData:64` | `p11R0` | PASS | canonical-step data: literal current signature; explicit source data/object; definition classification above |
| `StepData:66` | `p11R1` | PASS | canonical-step data: literal current signature; explicit source data/object; definition classification above |
| `StepData:68` | `p11DeltaH` | PASS | canonical-step data: literal current signature; explicit source data/object; definition classification above |
| `StepData:69` | `p11DeltaW` | PASS | canonical-step data: literal current signature; explicit source data/object; definition classification above |
| `StepData:71` | `p11StepPhi` | PASS | canonical-step data: literal current signature; explicit source data/object; definition classification above |
| `StepData:75` | `p11StepMap` | PASS | canonical-step data: literal current signature; explicit source data/object; definition classification above |
| `StepData:78` | `p11Normal` | PASS | canonical-step data: literal current signature; explicit source data/object; definition classification above |
| `StepData:80` | `p11StepRemainder` | PASS | canonical-step data: literal current signature; explicit source data/object; definition classification above |
| `StepData:84` | `P11StepHyp` | PASS | canonical-step data: literal current signature; explicit source data/object; definition classification above |
| `StepHom:31` | `stepP0` | PASS | cs-hom: cutoff coefficients plus divisor_perturb and homological_maximal; definition classification above |
| `StepHom:35` | `stepP1` | PASS | cs-hom: cutoff coefficients plus divisor_perturb and homological_maximal; definition classification above |
| `StepHom:41` | `step_B_open` | PASS | cs-hom: cutoff coefficients plus divisor_perturb and homological_maximal; A |
| `StepHom:44` | `step_r_pos` | PASS | cs-hom: cutoff coefficients plus divisor_perturb and homological_maximal; A |
| `StepHom:47` | `step_dr` | PASS | cs-hom: cutoff coefficients plus divisor_perturb and homological_maximal; A |
| `StepHom:50` | `step_E_nonneg` | PASS | cs-hom: cutoff coefficients plus divisor_perturb and homological_maximal; A |
| `StepHom:56` | `step_lambda_nonneg` | PASS | cs-hom: cutoff coefficients plus divisor_perturb and homological_maximal; A |
| `StepHom:60` | `step_A_nonneg` | PASS | cs-hom: cutoff coefficients plus divisor_perturb and homological_maximal; A |
| `StepHom:66` | `step_small` | FAIL (hygiene) | Mathematical bound proved; A. Public short-name reuse F1. |
| `StepHom:74` | `step_hdiv` | PASS | cs-hom: cutoff coefficients plus divisor_perturb and homological_maximal; A |
| `StepHom:79` | `step_M_nonneg` | PASS | cs-hom: cutoff coefficients plus divisor_perturb and homological_maximal; A |
| `StepHom:82` | `step_hm0` | PASS | cs-hom: cutoff coefficients plus divisor_perturb and homological_maximal; A |
| `StepHom:102` | `step_hm1` | PASS | cs-hom: cutoff coefficients plus divisor_perturb and homological_maximal; A |
| `StepHom:129` | `step_affHyp` | PASS | cs-hom: cutoff coefficients plus divisor_perturb and homological_maximal; A |
| `StepLie:32` | `flow_displacement_t` | PASS | cs-bracket: flow displacement at every time and coordinate Cauchy estimates; A |
| `StepLie:80` | `norm_fderiv_dir_le` | PASS | cs-bracket: flow displacement at every time and coordinate Cauchy estimates; A |
| `StepLie:103` | `norm_fderiv_phase_le` | PASS | cs-bracket: flow displacement at every time and coordinate Cauchy estimates; A |
| `StepParameter:24` | `step_slice_diff` | PASS | cs-param: fixed-phase slices, full parameter tube, every derivative order; A |
| `StepParameter:31` | `canonical_step_param` | PASS | cs-param: fixed-phase slices, full parameter tube, every derivative order; A |
| `StepReal:26` | `step_R1_eq` | PASS | canonical-step reality: explicit R reality guard propagated to coefficients/flow/remainder; A |
| `StepReal:38` | `step_R_real` | PASS | canonical-step reality: explicit R reality guard propagated to coefficients/flow/remainder; A |
| `StepReal:73` | `step_hm_real` | PASS | canonical-step reality: explicit R reality guard propagated to coefficients/flow/remainder; A |
| `StepReal:89` | `coeff_zero_real` | PASS | canonical-step reality: explicit R reality guard propagated to coefficients/flow/remainder; A |
| `StepReal:101` | `step_avg_real` | PASS | canonical-step reality: explicit R reality guard propagated to coefficients/flow/remainder; A |
| `StepReal:110` | `step_real_flow` | PASS | canonical-step reality: explicit R reality guard propagated to coefficients/flow/remainder; A |
| `StepReal:131` | `step_Rp_real` | PASS | canonical-step reality: explicit R reality guard propagated to coefficients/flow/remainder; A |
| `StepRealFlow:29` | `stepV` | PASS | cs-lip: real angle flow identification and exp(L)-1 derivative bound; definition classification above |
| `StepRealFlow:33` | `stepP1_entire` | PASS | cs-lip: real angle flow identification and exp(L)-1 derivative bound; A |
| `StepRealFlow:41` | `stepV_contDiff` | PASS | cs-lip: real angle flow identification and exp(L)-1 derivative bound; A |
| `StepRealFlow:50` | `stepV_bound` | PASS | cs-lip: real angle flow identification and exp(L)-1 derivative bound; A |
| `StepRealFlow:63` | `stepV_periodic` | PASS | cs-lip: real angle flow identification and exp(L)-1 derivative bound; A |
| `StepRealFlow:76` | `step_fderiv_re` | PASS | cs-lip: real angle flow identification and exp(L)-1 derivative bound; A |
| `StepRealFlow:90` | `stepV_fderiv` | PASS | cs-lip: real angle flow identification and exp(L)-1 derivative bound; A |
| `StepRealFlow:165` | `step_flow_real` | PASS | cs-lip: real angle flow identification and exp(L)-1 derivative bound; A |
| `StepRealFlow:208` | `step_real_lipschitz` | PASS | cs-lip: real angle flow identification and exp(L)-1 derivative bound; A |
| `StepRealFlow:242` | `canonical_step_real` | PASS | cs-lip: real angle flow identification and exp(L)-1 derivative bound; A |
| `StepRemainder:26` | `step_norm_single_le_one` | PASS | cs-taylor / cs-bracket / cs-assemble: domains, Lie identity and explicit estimate; A |
| `StepRemainder:30` | `strip_of_close` | PASS | cs-taylor / cs-bracket / cs-assemble: domains, Lie identity and explicit estimate; A |
| `StepRemainder:39` | `strip_add_dir` | PASS | cs-taylor / cs-bracket / cs-assemble: domains, Lie identity and explicit estimate; A |
| `StepRemainder:49` | `poissonBracket_congr` | PASS | cs-taylor / cs-bracket / cs-assemble: domains, Lie identity and explicit estimate; A |
| `StepRemainder:57` | `step_A_le_quarter` | PASS | cs-taylor / cs-bracket / cs-assemble: domains, Lie identity and explicit estimate; A |
| `StepRemainder:62` | `step_Aeta_le` | PASS | cs-taylor / cs-bracket / cs-assemble: domains, Lie identity and explicit estimate; A |
| `StepRemainder:69` | `step_z_mem` | PASS | cs-taylor / cs-bracket / cs-assemble: domains, Lie identity and explicit estimate; A |
| `StepRemainder:77` | `step_bracket_bound` | PASS | cs-taylor / cs-bracket / cs-assemble: domains, Lie identity and explicit estimate; A |
| `StepRemainder:149` | `step_remainder_eq` | PASS | cs-taylor / cs-bracket / cs-assemble: domains, Lie identity and explicit estimate; A |
| `StepRemainder:212` | `step_remainder_le` | PASS | cs-taylor / cs-bracket / cs-assemble: domains, Lie identity and explicit estimate; A |

## Independent validation receipts

All audit-owned Lean/Lake/checker/ABI invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`. The compile-gate wrapper supplies nice itself. No clean, update, cache fetch, library-root build, heartbeat/recursion/synthesis-budget override or source rewrite was run.

1. Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ac8 KAM.Planetary.MaximalStep.StepRealFlow KAM.Planetary.MaximalStep.StepParameter
```

Exit **0**. Gate output: `[inp-gate] slot 2 acquired 17:18:19 for KAM.Planetary.MaximalStep.StepRealFlow KAM.Planetary.MaximalStep.StepParameter`. Final output: `Build completed successfully (9151 jobs).` All ten audited modules are in these targets' import closure. Warnings were unused-variable/simp hints and the existing `if_true` deprecation at `StepRealFlow.lean:130`; no elaboration errors or heartbeat failure.

2. Exact-signature and axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AC8Audit.lean > .lake/abi-scratch/P11AC8Audit.out 2>&1
```

Exit **0**, no errors. Probe imported only StepRealFlow and StepParameter. Five fresh signature-copy declarations used `canonical_step H`, `canonical_step_real H hreal`, `canonical_step_param H htp ht hj`, `cutoff_coefficients hn hr hs hT hd hdr he hB hR hb`, and `canonical_step_simple_inverse H`; the explicit-binder ordering and subsequent whole-type examples all elaborated. It then printed axioms for every one of the 81 public theorems in the ledger. There were exactly 81 axiom reports, every one with `[propext, Classical.choice, Quot.sound]`, and no `sorryAx`. In particular:

```text
'KAM.Planetary.canonical_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.canonical_step_simple_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_cutoff_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.cutoff_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.canonical_step_param' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.canonical_step_real' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay, one invocation for all ten modules:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.MaximalStep.StepData KAM.Planetary.MaximalStep.StepCoeff KAM.Planetary.MaximalStep.StepHom KAM.Planetary.MaximalStep.StepLie KAM.Planetary.MaximalStep.StepBound KAM.Planetary.MaximalStep.StepRemainder KAM.Planetary.MaximalStep.Step KAM.Planetary.MaximalStep.StepParameter KAM.Planetary.MaximalStep.StepReal KAM.Planetary.MaximalStep.StepRealFlow > .lake/abi-scratch/P11AC8Kernel.out 2>&1
```

Exit **0**. Exact output:

```text
replaying KAM.Planetary.MaximalStep.StepRealFlow
replaying KAM.Planetary.MaximalStep.StepReal
replaying KAM.Planetary.MaximalStep.StepParameter
replaying KAM.Planetary.MaximalStep.Step
replaying KAM.Planetary.MaximalStep.StepRemainder
replaying KAM.Planetary.MaximalStep.StepBound
replaying KAM.Planetary.MaximalStep.StepLie
replaying KAM.Planetary.MaximalStep.StepHom
replaying KAM.Planetary.MaximalStep.StepCoeff
replaying KAM.Planetary.MaximalStep.StepData
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the explicitly permitted generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (726 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Module checks, frozen-anchor guard and all 144 elaborated ABI hashes pass. No long-line, forbidden-token or oversize-file diagnostic was emitted. `KAM.lean` was not regenerated.

5. Static integrity and scope: `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no diff (only the multiple-merge-base warning). `git diff --check` exited 0. Source scan: no forbidden escape, override, EuclideanSpace or root declaration in any Step file. All ten files have copyright/module/public imports/module docstrings/exposed public sections. Line counts: Step 232; StepBound 181; StepCoeff 380; StepData 100; StepHom 153; StepLie 142; StepParameter 83; StepReal 173; StepRealFlow 261; StepRemainder 248. Maximum 380, below 1500.

An explicit recursive scan of all 105 KAM modules in the Step import closure found **zero frozen theorem imports and zero provider imports**. The imported frozen definitions are only definitions (including the literal field, strip, action tube, symplectic form and circular tube). Thus neither DRAFT_SORRY theorem imports nor illicit provider dependencies are hidden transitively. Public-name scan found only F1 after discarding the unrelated private `poissonBracket_congr`; no full-name/root shadow. A further Mathlib short-name scan found only `TruncatedWittVector.truncate_truncate` (`Mathlib/RingTheory/WittVector/Truncated.lean:353`), which is not a root declaration.

6. Audit-input hashes:

```text
627ab032a68be7aca3f547d898c1e82fe8146c18a363a5dd63163916b8d3beee  /root/code/KAM-inp/.drafts/design/P11ASignatures.lean
8619ea896c856347a9a5c5efac5080f0c830ea19245320b5f03a2b4267a300b9  docs/tracks/P/design/P11A-LEAN-DESIGN.md
990694a832aa02dca0138c5cbb3bab842984583f4ca92576479eff04786ed3ec  blueprint-P/parts/p11a2-cutoff-step.tex
```

Final closeout: the mathematical C8 implementation and all five amended signatures pass independent checks; the full requested package acceptance remains **FAIL solely for F1**, the public short-name reuse. D1 is an already authorized design correction, not an unpaid implementation gap. No other missing C8 companion or new premise was found. The only requested follow-up is to rename the helper and rerun its affected targeted checks; no source-law or frozen-type change is needed.

The scratch signature probe and its axiom/kernel/lint logs were removed after recording the receipts above. Initial git status had only the pre-existing untracked C8 handoff; final status adds only this audit report. No commit, checkout, reset, or other state-changing git command was run. The report has 104 unique declaration rows, balanced code fences, and no trailing whitespace; `git diff --check` exits 0.
