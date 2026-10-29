# GAP-P8c prover handoff (branch inp-gp8c, 5e9c2146; off inp; graph-gap programme package run by the main orchestrator)


## Files
- NEW `KAM/Planetary/SecularForm/EvenIdentNodes.lean` (~536 lines, append-only; no landed file edited; KAM.lean not touched,
  lint reports "KAM.lean is out of date" -> regenerate at landing).
- This handoff. No signature file entry exists for GAP-P8c in P11BSignatures.lean, so statements were designed from the DEPGRAPH
  SOURCE_CONCLUSION of each node.

## Node -> declaration (all in KAM.Planetary / KAM.Planetary.SecularForm)
| node | declaration | notes |
|---|---|---|
| stepP:p8:ev-tay | `SecularForm.p8_ev_tay` | for I in actionDomain, both models: odd jets vanish; fderiv = 0 (origin critical); every jet (hence the degree-2d part) invariant under rotations `slowRotCLE θ` and reflection η->-η (diagonal O(2)). Generic tool: `iteratedFDeriv_invariant_of_equiv` (export 1). |
| stepP:p8:ev-quad | `SecularForm.p8_ev_quad` | full-n Hessian of `slowSecular D b I` at 0: xi-eta block = 0, eta-eta block = xi-xi block (vector form; entries follow by specialising). Both models. |
| bpP:p8:evenness | `SecularForm.p8_evenness_full` | four invariances (landed `evenness`, on `slowDom`), p8_ev_tay items, degree-2 part = `quad A ξ + quad A η` with `A = coeffs D (axis D I)` (`slowSecular_second_jet`, both models via `same_jets`), `Aᵀ = A` (`coeffs_transpose`), jets analytic in Λ on `actionDomain` (`analyticOnNhd_slowSecular_jet`), `A(Λ)` analytic. |
| bpP:p8:identities | `SecularForm.p8_identities_full` (= `p8_identity_one`, `p8_identity_two`) | (I1) αβ''+2β' = b_{3/2}^(1) and (I2) α²b''+2αb'-2b = α b_{3/2}^(2) literally for every α in [0,1), INCLUDING α=0 (ruling): parity `laplace_def_neg_arg`, analyticity at 0 `analyticAt_laplace_def_zero`, and continuity from (0,1) where the landed `identities` holds. |
| stepP:p8:id-1 | `SecularForm.p8_id1` | coefficient identity (2q+2)(2q+3)((1/2)_{q+1}/(q+1)!)^2 = (3/2)_{q+1}(3/2)_q/((q+1)!q!), plus the series coefficient form of `laplaceTerm (3/2) 1 q`. |
| stepP:p8:id-2 | `SecularForm.p8_id2` | q=0: zero; q=r+1: 2q(2q+3)c_q = (3/2)_{r+2}(3/2)_r/((r+2)!r!), plus series coefficient form of `laplaceTerm (3/2) 2 r`. |

Supporting public declarations (all new, no short-name clash in KAM): `fderiv_fderiv_invariant_of_equiv`, `slowRotCLM`, `slowRotCLE`,
`slowReflCLE`, `slowEmbCLM`, `eventually_mem_slowDom_zero`, `slowSecular_eventually_rotate/_reflect`, `analyticAt_slowSecular_jet`,
`analyticOnNhd_slowSecular_jet`, `analyticAt_slowSecular_fix`, `slowSecular_fix_second_jet`, `slowSecular_second_jet`, `coeffs_transpose`,
`laplaceC_neg`, `laplace_def_eq_re`, `analyticAt_iteratedDeriv_two`, `eq_zero_of_continuousAt_of_zero_Ioo`.

## Approach
Reuse: `evenness`, `evenness_taylor`, `perturbation_analytic`, `quadratic_form`-machinery (`rayRemainder`, `iteratedDeriv_two_rayRemainder`,
`iteratedDeriv_two_ray`), `same_jets`, `coeffs_analytic`, `identities`, `coef1`, `coef2`, `laplaceC_ofReal`. Equivariance via
`ContinuousLinearEquiv.iteratedFDerivWithin_comp_right`; jet analyticity via `iteratedFDeriv_comp_clm_of_isOpen` + `compContinuousLinearMapL`.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-gp8c KAM.Planetary.SecularForm.EvenIdentNodes`: "Build completed successfully", no warnings in my file.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK (only note: KAM.lean out of date; not edited per brief).
- `#print axioms` of p8_ev_tay, p8_ev_quad, p8_evenness_full, p8_identities_full, p8_id1, p8_id2: [propext, Classical.choice, Quot.sound].
- No sorry / maxHeartbeats; lines <= 100 columns; no EuclideanSpace.

## Uncertainties / deviations
- The degree-2d part invariance is exported as invariance of the jet (`iteratedFDeriv ... (fun _ => slowRotCLE θ u) = ... (fun _ => u)` and as multilinear
  form in `iteratedFDeriv_invariant_of_equiv`); "polynomial in (u_1..u_n)" is read as homogeneity of the Taylor part (no invariant-theory content; `e_weyl` is a separate node).
- id-1/id-2 are exported as coefficient equalities in terms of the explicit series coefficients (`halfCoef`, `poch`, `laplaceTerm`), not as `HasSum` of the termwise-differentiated series (that termwise computation lives inside the landed `identities` proof).
- ev-quad is stated as bilinear-form block identities (equivalent to B=0, C=A for the Hessian matrices); no matrix `A,B,C` objects introduced.
- Evenness is stated on `slowDom D` (where the landed `evenness` holds), not on the box N_R(rho_*) as in the source.

## Suspected errata
- bpP:p8:evenness (DEPGRAPH NOTE already records it): S(R_θ(ξ,η),Λ)=S needs R_θ(ξ,η) in N_R(ρ_*); the box is not rotation-invariant for θ not in (π/2)ℤ. The Lean statement uses the chart domain `slowDom`, where it is true; local invariance suffices for ev-tay/ev-quad (as exported).
- None else.

ORCHESTRATOR RULING (OVERNIGHT 01:20, 01:30): graph-gap programme for the landed parts. This package appends UNSIGNED exports whose job is to state the LITERAL conclusion of each listed graph node, built from landed declarations. Package definition: section '**GAP-P8c:**' of /root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P.md. The Laplace identities are to hold on the source's literal interval, alpha = 0 included. KAM.lean regeneration is the sub-orchestrator's job at merge, not a finding.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/P/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint lines it cites, and give a per-node verdict: does the named declaration state that node's literal conclusion under only the source's hypotheses, with quantifiers in the source's order? An export that takes a proved dependency's OUTPUT as a premise is a FAIL (export from the source hypotheses and build the dependency inside). A node whose export is weaker, conditional on an unsourced premise, or a different statement is a FAIL for that node; list each such node precisely. Audit ONLY KAM/Planetary/SecularForm/EvenIdentNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
