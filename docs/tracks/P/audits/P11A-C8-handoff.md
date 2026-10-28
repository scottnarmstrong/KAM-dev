# P11A-C8 prover handoff (branch inp-p11ac8, e4164985; contains P11A-C7 (audited); offloaded package run by the main orchestrator; two rounds: C8 then C8b)


## Files (all new, under KAM/Planetary/MaximalStep/)
StepData (P11Step, p11StepA/Kappa/Rem, p11R0/R1, p11DeltaH/W, p11StepPhi/Map, p11Normal, p11StepRemainder,
P11StepHyp: verbatim from the signatures), StepCoeff, StepHom, StepLie, StepBound, StepRemainder, Step,
StepParameter, StepReal, StepRealFlow (all < 400 lines).

## Declarations proved (signatures verbatim)
- `canonical_step` (Step), `canonical_step_param` (StepParameter), `canonical_step_real` (StepRealFlow).
- Helper for the cutoff coefficients: `p11_cutoff_coeff` (StepCoeff), a corrected form of `cutoff_coefficients`.
`#print axioms` of canonical_step, canonical_step_real, canonical_step_param, p11_cutoff_coeff:
`[propext, Classical.choice, Quot.sound]`.

## Approach
cutoff = R0 + R1.eta via linearity of `truncate`/`coeff` (StepCoeff); `homological_maximal` for R0 and each
R1_i gives P11AffineHyp per b in B (StepHom); fibrewise `affine_flow` and joint `affine_flow_param` give the map
clauses. Remainder: `Canonical.taylor_poschel` with h = N_b, f0 = R(.,b); `{N_b,phi}` = -(R_* - <R_*>) through
`p11_normal_affine_bracket` and the homological equation; u_t = (1-t)w + R on D(r-d,s) bounded by eps(5+4E);
Cauchy estimates (radius sigma in theta, s/4 in eta) at X^t z with displacement for every t (`flow_displacement_t`)
give n(4n+5)UA/sigma (StepLie/StepRemainder). Parameter clause: param_cauchy(_scalar). Real clauses: reality of
coefficients/generators/flow/remainder (StepReal); real Lipschitz: the angle part at eta=0 is the real flow of
v = Re phi_1(., b) (ODE uniqueness, `fst_solution`), derivative bound from the coefficient decay
(`norm_hmCoef_le`, `sum_exp_le_lambda`), then `real_lipschitz` (StepRealFlow).

## Checks
Gate builds (StepRealFlow, StepParameter and everything below) succeed; `scripts/lint_sources.sh`: modules PASS,
frozen guard OK, ABI OK, no long lines; only "KAM.lean out of date" (generated). No sorry/maxHeartbeats/EuclideanSpace.
Name clashes: grepped; `norm_single_le_one` renamed `step_norm_single_le_one`.

## Suspected errata / deviations (REPORT)
1. **`cutoff_coefficients` (signature file L1242, design L2185) is false as stated**: its clause
   `∀ z, p11Cutoff T R z = p11R0 .. + ∑ ..` has no `z.2 ∈ B`. For `b ∉ B` R is unconstrained: take
   R((x,eta),b) = f(x) + eta_1 g(x) with f non-integrable, g = 1 - f; the cutoff at eta_1 = 1 has mean 1
   while coeff-0 of f and g are both junk 0. I did NOT prove it; `p11_cutoff_coeff` proves the b ∈ B form plus
   the angle-class, trigonometric-polynomial (`truncate T P = P`) and sup-norm facts consumed by the step.
   Under the audit this should replace `cutoff_coefficients`.
2. **Not proved: `canonical_step_simple_inverse`** (design companion); only canonical_step, _real, _param
   and the helper were done. The needed tools exist (`affine_flow` clauses 4, 9).
3. `canonical_step_param`'s remainder clause uses param_cauchy_scalar (identical statement, scalar).
No heartbeat problems.

## Round 2
`cutoff_coefficients` (amended) and `canonical_step_simple_inverse` proved; see handoff-P11A-C8b.md.

## C8b
Files: KAM/Planetary/MaximalStep/StepCoeff.lean (+`cutoff_coefficients`), Step.lean (+`canonical_step_simple_inverse`).
Approach: `cutoff_coefficients` (amended statement, verbatim up to a line break) is the projection of clauses 5-7 of
`p11_cutoff_coeff`. `canonical_step_simple_inverse`: per b in B choose Theta/M/v from `affine_flow` clause 4
(`choose!`), assemble parametrised functions; inverse clauses from `affine_flow` clause 9 (z.1 in V since q<=1/2).
Checks: `lake build KAM.Planetary.MaximalStep.Step` OK; lint_sources: modules PASS, frozen guard OK, ABI OK; only
"KAM.lean out of date" (generated). `#print axioms` of both: [propext, Classical.choice, Quot.sound].
Nothing already proved was changed. No errata/deviations new; erratum 1 of round 1 is resolved by the ruling.

ORCHESTRATOR RULING (OVERNIGHT 16:35, design note on inp 177d8b6b): the signed cutoff_coefficients was false as stated (its last clause lacked z.2 in B; counterexample in the C8 handoff errata); the signature file now has the amended clause '∀ z : P11Family n, z.2 ∈ B → p11Cutoff T R z = ...'.

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-C8 (line 719), the companion-results note at ~668 incl. the amendment bullet, Appendix ~2185-2200; P11A design audits; signatures /root/code/KAM-inp/.drafts/design/P11ASignatures.lean): (1) every C8 declaration (P11Step, p11StepA/Kappa/Rem, p11R0/R1, p11DeltaH/W, p11StepPhi/Map, p11Normal, p11StepRemainder, P11StepHyp, canonical_step, canonical_step_param, canonical_step_real, cutoff_coefficients (AMENDED form), canonical_step_simple_inverse) = signature file EXACTLY, and the C8 slice COMPLETE (integral Lie identity, explicit U/bracket estimate); (2) independently verify the cutoff_coefficients counterexample against the definitions and that the amendment is the minimal correction (consumers cs-cutoff use it only on B); (3) proof soundness: p11_cutoff_coeff (b in B form), the step construction, canonical_step_param using param_cauchy_scalar, the real versions, canonical_step_simple_inverse via affine_flow clauses 4 and 9 (choose! per b; q <= 1/2 for membership in V); no added premises; (4) hygiene (no EuclideanSpace; no public short name used elsewhere in KAM; no root shadow). Audit ONLY the KAM/Planetary/MaximalStep/Step*.lean files (Affine*, RealFlow, ParameterFlow, GlobalRealFlow are C7's, audited).
