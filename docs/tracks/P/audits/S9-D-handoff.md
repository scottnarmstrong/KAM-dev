# S9-D prover handoff (branch inp-s9d, c672945; contains inp-s8c (audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files (new)
- KAM/Planetary/SecularSpectrum/Definiteness/Hadamard.lean (107 lines): `dominance`, `l75`, `l75_bound`
  (+ helper sum-splitting lemmas `erase_eq_union`, `sum_erase_split`, `sum_sum_split`).
- KAM/Planetary/SecularSpectrum/Definiteness/Laplace.lean (135): `l74` (+ `laplace_def_eq_half`
  [stepP:p9:l74-red], `ibp_formula` [l74-ibp]).
- KAM/Planetary/SecularSpectrum/Definiteness.lean (~246): `coercivity`, `definite` and helpers
  (`pairA_sub_pairB_pos`, `pairB_nonneg`, `qhat_hermitian`, `dominance_qhat`, `gap_pos`,
  `quad_eigen_le`, `continuousAt_*`).
All statements copied verbatim from P810Signatures.lean (`dominance` is in Hadamard, since `l75` needs it).

## Approach
- l75: split double sums over i<j / i=j via `sum_sum_split`, symmetry from Hermitian; l75_bound from l75.
- l74: reduce to [0,π] by symmetry t↦2π−t, integrate by parts (H = sin t(1−cos t)), positivity via
  `intervalIntegral_pos_of_pos_on`.
- definite: dominance of qhat equals the literal gap sum; l74 (s=3/2) gives each pair difference > 0;
  cHat attained (finite inf); inequalities via l75 / l75_bound; coercivity bound by congruence
  y_i = x_i/√Λ_i; eigenvalue bound via Hermitian eigenvector Rayleigh quotient (sorted = eigenvalues of
  an index); continuity via ContinuousAt of finite inf/sup and analyticity of laplace_def on (0,1).
- Only source premises (hn : 2 ≤ n, ha : a ∈ axes n); no conclusion-shaped hypotheses.

## Checks
- Gate builds: `KAM.Planetary.SecularSpectrum.Definiteness` -> "Build completed successfully", no sorry,
  no heartbeat options.
- `scripts/lint_sources.sh`: no over-100-char lines; check_lean_modules PASS; frozen guard OK; ABI OK.
  Only message: "KAM.lean is out of date" (not edited by me; orchestrator regenerates).
- `#print axioms` (l74, l75, l75_bound, definite, coercivity): [propext, Classical.choice, Quot.sound].

## Uncertainties / errata / deviations
- None found; signatures unchanged. `dominance` placed in Definiteness.Hadamard (imported by facade).
- Note: deprecation warnings (`ite_cond_eq_false`) in upstream Coefficients.lean are not mine.

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S9-D and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) statements = design signatures exactly (l74, l75, l75_bound, definite, coercivity; dominance if signed); (2) proofs sound (Hadamard identity, Laplace definiteness; S8-C, S9-N, S8-L consumed as designed); no added premises; (3) hygiene. Audit ONLY KAM/Planetary/SecularSpectrum/Definiteness.lean and Definiteness/*.lean.
