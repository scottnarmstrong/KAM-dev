# P5-FI prover handoff (branch inp-p5fi, 439541a; contains inp-p5fd (audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files (new)
KAM/Planetary/PGAssembly/: FrequencySchur (42 lines), FrequencyInvLinear (105), FrequencyInvDeriv (221),
FrequencyInvJac (126), FrequencyInvBounds (214), FrequencyInverse (169; imports all, facade for the two results).

## Declarations
- `schur_inverse_blocks` (FrequencySchur, re-exported by FrequencyInverse): `Matrix.invOf_fromBlocks₁₁_eq` + `Matrix.neg_mul`.
- `freq_inj` (FrequencyInverse), signature verbatim. Auxiliary: `freq_injOn` (injectivity), `jacobian_bounds`
  (FrequencyInvBounds), `hasFDerivAt_complexFrequency`, `complexFrequency_eq`, `fderiv_jp_embSlow`, `hessian_embSlow`
  (slow-slow Hessian block = `jetBeta`, uses `jetBeta_isSymm`), `lower_of_hasFDerivAt`, `inv_apriori`.

## Approach
- complexFrequency = (complexFast∘blockFast,0) + mu ∇jetPolynomial; derivative T0 = embFast∘∂complexFast∘bf + mu·partials∘D²jp.
- Injectivity: fast lower Lipschitz (c0) + the Lipschitz clauses of PGAnalyticSpec + slow affine formula Θ=Ω+βξ and LB; closes by
  mu·LN ≤ c0/2 and 2 mu LN² LB < c0 (strict).
- Inverse bounds: DIRECT vector a priori estimate (`inv_apriori`: pure real inequalities, uses mu·AN ≤ c0/2 and
  4 mu AN² LB ≤ c0) on T0 v = w giving ‖bf v‖ ≤ CU‖w‖ and ‖v‖ ≤ (CU/mu)‖w‖; invertibility by injective ⇒ surjective (finite dim).
  `schur_inverse_blocks` is therefore proved as stated but NOT consumed by `freq_inj` (the design's Neumann/Schur route is replaced by
  the equivalent a priori bounds; same constants pgCU).
- No signature changes; spec clauses used exactly as given.

## Checks
- Gate build of FrequencyInverse, FrequencySchur, FrequencyInvLinear: success, no sorry, no warnings from my files that matter.
- `scripts/lint_sources.sh`: all my checks PASS; only message left is "KAM.lean is out of date" (generated; not touched).
- `#print axioms freq_inj` / `schur_inverse_blocks`: [propext, Classical.choice, Quot.sound].
- No heartbeat overrides; max file 221 lines.
- Applied orchestrator rename: uses `blockFast_append_complex` / `blockSlow_append_complex`. Checked no new public name clashes
  with existing KAM declarations (grep).

## Uncertainties / errata / deviations
- None found in statements. Deviation: Schur lemma not used by freq_inj (see above). Note: PGAnalyticSpec's bound on D²jp
  is used as the operator norm of the Hessian on the radius-1 slow domain; fine as stated.

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P5-FI, proof plan and 'Revision 4'; audits DESIGN-P45-design-audit-{1,2,3,4}.md; signatures .drafts/design/P45Signatures.lean): (1) schur_inverse_blocks and freq_inj = signature file exactly; (2) proofs sound (Matrix.fromBlocks₁₁Invertible, Neumann series, P5-FD freq_data/pgAnalytic consumed as designed; block formulas of the frequency map and its derivative; Jacobian bounds); no added premises; (3) hygiene (no EuclideanSpace; the branch carries the 0d04590 rename port 6ac01b0, so the FrequencyLip lemmas are blockFast_append_complex / blockSlow_append_complex; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/PGAssembly/FrequencySchur.lean and FrequencyInv*.lean / FrequencyInverse.lean.
