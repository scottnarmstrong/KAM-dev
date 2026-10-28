# P11A-C7 prover handoff (branch inp-p11ac7, 24ba56d; contains inp-p11ac6 (in audit); offloaded package run by the main orchestrator; prover on claude-12)


## Files (new)
- `KAM/Planetary/MaximalStep/GlobalRealFlow.lean` (~150 lines): `p11_bounded_global_flow`, `p11RealFlow`,
  `p11_global_variational` (signatures verbatim) plus helpers `p11_norm_sub_le_of_sol`, `p11RealFlow_spec`,
  `p11RealFlow_eq` (public, p11_-prefixed, no clashes found by grep over KAM) and private maximal-solution lemmas.
- `KAM/Planetary/MaximalStep/RealFlow.lean` (~110 lines): `real_lipschitz` (verbatim) with private `p11_gronwall_lin`.

## Approach
- Global flow: maximal solution (`gen_maximal`, W = univ); bounded field keeps it in closedBall x (M T), so
  `gen_continuation_compact` forces both ends infinite (backward end by `IsMaximalSolution.neg`).
- Variational: `p11RealFlow v · x` is the maximal solution family (uniqueness `gen_uniqueness`); the existing generic
  `KAM.Nekhoroshev.FlowChain.reg_all` (local `ext_dep` chained) gives differentiability in x and the variational ODE
  for the actual `fderiv`; `fderiv` at time 0 is `fderiv_id`.
- `real_lipschitz`: displacement by mean-value bound; periodicity by ODE uniqueness for `u s = flow s x + k`;
  derivative bound by Mathlib `norm_le_gronwallBound_of_norm_deriv_right_le` on Y - 1 (δ=0, K=ε=L), negative times
  by time reversal of Y, A.
- New imports: GlobalRealFlow imports `KAM.ODE.Continuation` and `KAM.Nekhoroshev.Averaging.FlowChain` (no providers,
  no frozen theorem anchors).

## Checks
- `inp_lake_build.sh ... KAM.Planetary.MaximalStep.RealFlow`: Build completed successfully (no warnings in my files).
- `#print axioms` of `real_lipschitz`, `p11_global_variational`, `p11_bounded_global_flow`: all
  `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only message is
  "KAM.lean is out of date" (generated; I did not edit it, the orchestrator must run gen_root_imports.py).

## Uncertainties / errata / deviations
- None. No signature changed; `p11RealFlow` lacks a docstring as in the signature file (copied verbatim).
- No heartbeat or size issues. Statements were true as given (hb, hD, hv C² suffice).

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-C7 and proof plan; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): (1) statements and definitions = signature file exactly (p11RealFlow, real_lipschitz, the global real flow and variational bridge declarations); (2) proofs sound (nonlinear continuation, variational bridges, Gronwall; C6 consumed as designed); no added premises; (3) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/MaximalStep/GlobalRealFlow.lean and RealFlow.lean (the branch diff also shows many files from a newer inp base; ignore them).
