# P23-11 prover handoff (branch inp-p2311, 067d052; contains inp-p2306 (P23-06, audited); offloaded package run by the main orchestrator; prover on claude-12)


Branch inp-p2311 (contains P23-06). Final commit: see `git -C /root/code/KAM-inp-p2311 log -1`.

## Files
- NEW `KAM/Planetary/Averaging/OscillatorBracket.lean` (1094 lines; under the 1500 cap). Nothing else touched
  (KAM.lean not regenerated: `lint_sources.sh` reports "KAM.lean is out of date" only because of the new module).

## Declarations (signatures copied verbatim from P23Signatures.lean; binder order, hypotheses, conclusions unchanged)
- `KAM.Planetary.ob_der`  (`stepP:p2:ob-der`) — all four clauses, every angular derivative at the TARGET width `S-σ`,
  losses `S₀-S+σ`, `r₀-r+ρ`, `rp₀-rp+ρp`, `rq₀-rq+ρq`. Pays gap G1 with no new premise (no `S<S₀`).
- `KAM.Planetary.osc_bracket` (`bpP:p2:osc-bracket`, with `stepP:p2:ob-prod` inlined as `bracket_bound`).
  `hn`, `hm` are unused in the proof (`set_option linter.unusedVariables false in` for that statement only).
- `KAM.Planetary.ob_field` (`stepP:p2:ob-field`) — derived from `ob_der` with `r₀=r,…,S₀=S` plus a sup bound.

## Approach
- Transport: `oscUnpackL`/`oscPackL` continuous linear maps; `oscPack_theta/I/p/q` (coordinate directions),
  `fderiv_oscFunction` (chain rule), `osc_deriv_eqs`, `oscClass.flat` (FClass of the flat function),
  `oscBound_of_flat` (coefficients depend only on real slices).
- Flat layer: `FClass`, `wsum_dtheta_le` (reuses `cauchy_theta`, summed over angles inside the sup, at a fixed
  parameter), `wsum_dI_le` (NEW 1-D Cauchy disc `t ↦ x + t eᵢ` with its own loss `R`; needed because `oscParams`
  has four unequal radii and is not a `polyNbhd`, so `cauchy_action` does not apply directly; it mirrors
  `action_partial_sum_le`), `norm_le_of_wsum` (via `sup_le_wbound`), line lemmas `line_I/p/q`.
- Bracket: signed sum over `(Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin m)` (`brCoeff`, `brFun`, `bracket_flat_eq`), each product by
  `coeff_mul` (`prod_term`), sum by `wsum_sum_le'` (copy of the private `wsum_sum_le` of `Weighted.Bracket`), constants
  via `comp_aux`; the factor `m` comes from the `m` p/q pairs; angular sums are summed before the parameter sup.

## Checks
- `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2311 KAM.Planetary.Averaging.OscillatorBracket`
  → `✔ Built KAM.Planetary.Averaging.OscillatorBracket`, no warnings, no `sorry`.
- `sh scripts/lint_sources.sh`: `check_lean_modules: PASS (463 Lean files…)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`;
  only message: "KAM.lean is out of date; run scripts/gen_root_imports.py" (new module; KAM.lean is generated, not edited).
- `grep` for maxHeartbeats/sorry/axiom/admit/unsafe/opaque in the file: none.
- `#print axioms` of `ob_der`, `osc_bracket`, `ob_field`: `[propext, Classical.choice, Quot.sound]` each.

## Uncertainties / deviations
- None in signatures. Helper lemmas are public in `KAM.Planetary` (names above); a private `local macro pack_tac` is
  used for index bookkeeping. No design signal about heartbeats (all proofs elaborate at default budget; file builds in ~40 s).
- Only imports: OscillatorSetting, Weighted.{Algebra,Cauchy,Parametric,SupWeighted}; no provider, no DRAFT_SORRY anchor.

## Suspected errata
- None new beyond design gap G1 (P2 L177: `e(S₀-S)` should read `e(S₀-S+σ)` at target width `S-σ`), handled as the design states.

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md revision 2 row P23-11 and proof plan; audits DESIGN-P23-design-audit-{1,2}.md; signatures .drafts/design/P23Signatures.lean): (1) statements = design signatures (ob_der, osc_bracket, ob_field); this package pays design gap G1 WITHOUT any new premise; (2) proofs sound (Weighted Cauchy/algebra used correctly); (3) hygiene (lint incl. 100-char lines). Audit ONLY Averaging/OscillatorBracket*.lean (compare with branch inp-p2306).
