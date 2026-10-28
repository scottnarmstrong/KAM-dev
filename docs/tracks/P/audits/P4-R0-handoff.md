# P4-R0 prover handoff (branch inp-p4r0, f7f0189; contains inp-p4s, inp-p4af, inp-p4lt (audited); offloaded package run by the main orchestrator; prover on claude-12; two sessions)

## Session 1

Files: KAM/Planetary/PGMeasure/ResonanceSlow.lean (new, ~90 lines). Committed on inp-p4r0.

Proved: `KAM.Planetary.beta_inverse` (signature verbatim), via helpers `abs_det_le_factorial_mul_pow`
(|det A| ≤ n! M^n) and `abs_adjugate_le` (adjugate entries ≤ (b-1)! M^(b-1), through
`Matrix.adjugate_fin_succ_eq_det_submatrix`); then adj(Tᵀ)·Tᵀv = det·v and a coordinatewise sum bound.

NOT done: "slow resonance sections and lattice sum". P45Signatures.lean contains no declaration for these
in this module (only beta_inverse is signed for P4-R0), and the design gives only prose ("Resonances", k_f=0
case via affine_slab with normal beta^T k_s, offset k_s·Omega, N3, then lattice_tail). I did not invent
unsigned statements; the orchestrator must supply signatures (or allow me to design helpers) for the
k_f = 0 slow-resonance measure bound before that part can be proved.

Checks: gate build of KAM.Planetary.PGMeasure.ResonanceSlow succeeded, no warnings; `#print axioms beta_inverse`
= [propext, Classical.choice, Quot.sound] (print line removed afterwards). scripts/lint_sources.sh: module check,
frozen guard, ABI hashes PASS; only message "KAM.lean is out of date" (generated; not edited per brief).
Uncertainties/errata/deviations: none. No heartbeat issues.

## Session 2 (internal resonance helpers)

File: KAM/Planetary/PGMeasure/ResonanceSlow.lean (now 463 lines; beta_inverse unchanged and still first).
No signed/frozen statement restated, no premise added to any signed declaration. All new declarations are
INTERNAL helpers with distinct names; the only hypotheses are the MeasureData fields (S4 source premises/N1/N3)
and the proposition's own parameters (lambda, mu, alpha2, Q measurable, Q ⊆ actionShell b (-lambda) lambda).

## Helpers and blueprint nodes (all `stepP:p4:dm-slow` of bpP:p4:two-scale-diophantine-measure unless stated)
- `slow_resonance_measure_le` — THE P4-M CONSUMER: measure of {J ∈ joinedActions core Q | ∃ k≠0, blockFast k = 0,
  |∑ k_i freq J i| < alpha2/(∑|k_i|)^tau} ≤ ofReal(b*LB*latticeS b (tau+1)*(alpha2/mu)/lambda) * volume core *
  ofReal((2*lambda)^b). RHS is exactly the `measure_c2*(alpha2/mu)/lambda` term of the signed bound
  (measure_c2 d = b*d.LB*latticeS b (d.tau+1) unfolds to it). P4-M: the `if blockFast k = 0 then alpha2` branch of
  resonanceBad puts every k_f=0 witness in this set, so resonanceBad ⊆ (this set) ∪ (k_f≠0 sets).
  Uses lattice_tail (`stepP:p4:lt-a`, with (n,tau):=(b,tau+1); N: b < tau+1 from htau).
- `slow_mode_measure_le` — one mode ks≠0 (k = Fin.append 0 ks): ≤ ofReal(2*(alpha2/mu)*(b*LB)*(2λ)^(b-1)*
  latticeWeight (tau+1) ks) * volume core. Tonelli over I ∈ core (`bpP:p4:ext-tonelli`-style, ℝᵇ sections).
- `slow_section_measure_le` — fixed I ∈ core: the ξ-section has measure ≤ ofReal(2 eps (2λ)^(b-1)(b LB)/|ks|₁),
  via `affine_slab` with normal beta^T ks (nonzero and ‖·‖ ≥ |ks|₁/(b LB) by N3), offset ks·Omega.
- `measurableSet_slow_mode`, `slow_dot_continuousOn`, `slowFrequency_continuousOn_core`, `slowFrequency_expand` —
  Borelness of the k_f=0 resonance set from N1 (slow Lipschitz in I on core) + affinity in ξ; no extra assumption
  (matches the design note "Borelness comes from N1/N2").
- `volume_prod_le_of_sections` — Tonelli on (Fin a → ℝ) × (Fin b → ℝ) with arbitrary ENNReal section bound (generic;
  P4-RA/RB may reuse it for ℝᵇ-valued sections).
- `appendEquivAB`, `appendEquivAB_apply`, `measurePreserving_appendEquivAB`, `volume_eq_volume_append_preimage` —
  (ℝᵃ×ℝᵇ ≃ᵐ ℝ^(a+b)) by Fin.append, measure preserving (a,b general version of KAM.Measure.appendMeasurableEquiv).
  Reusable by P4-RA/RB.
- `blockFast_append`, `blockSlow_append`, `eq_append_zero_of_blockFast_eq_zero`, `sum_append_zero_mul_freq`,
  `sum_abs_append_zero`, `dot_slowFrequency` — algebra: ∑ k_i freq_i = mu * k_s·slowFrequency when k_f=0;
  k_s·(Omega + beta xi) = (beta^T k_s)·xi + k_s·Omega.
- (earlier) `beta_inverse`, `abs_det_le_factorial_mul_pow`, `abs_adjugate_le`.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-p4r0 KAM.Planetary.PGMeasure.ResonanceSlow`: Built, no warnings.
- `#print axioms` of slow_resonance_measure_le, slow_mode_measure_le, beta_inverse: [propext, Classical.choice,
  Quot.sound] each (scratch file, not committed).
- scripts/lint_sources.sh: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only the generated
  "KAM.lean is out of date" message (not edited). No maxHeartbeats/sorry; file 463 lines.

## Notes for P4-M / uncertainties
- Hypothesis hl0 (lambda ≤ lambda0) is only needed in P4-M's other cases; slow helpers carry it in the signature
  but do not use it (N1 continuity is applied at ξ=0 and ξ=lambda0·e_j, using lambda0 itself).
- No suspected errata. Deviations: none (internal helpers only). No design signals (all default heartbeats).

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P4-R0 and the P4-M row/proof plan; audits DESIGN-P45-design-audit-{1,2,3}.md; signatures .drafts/design/P45Signatures.lean; blueprint-P p4 two-scale-diophantine-measure, step dm-slow): (1) beta_inverse = its design signature exactly; (2) the slow-resonance sections and lattice sum are INTERNAL helpers under the orchestrator ruling (distinct names, blueprint-node citations, shaped for P4-M's two_scale_diophantine_measure): check each helper is mathematically correct, faithful to its cited blueprint step, carries no conclusion-shaped or unjustified hypothesis, and does not restate or weaken any signed declaration; check they are usable by P4-M; (3) proofs sound; (4) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/PGMeasure/ResonanceSlow.lean.
