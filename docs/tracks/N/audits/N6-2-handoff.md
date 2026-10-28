# N6-2 prover handoff (branch inp-n62, 2da9ccb; contains inp-n61 (N6-1, delivered); offloaded package run by the main orchestrator; prover on claude-12)


## Files
- New: `KAM/Nekhoroshev/NormalForm/Homological.lean` (~515 lines; no other file touched; KAM.lean not regenerated).

## Declarations proved (all as in NPart67Signatures.lean; statements compared textually)
`homGen`, `homRes`, `homGenParam`, `homResParam`, `RealOnParam` (defs, verbatim); `realOnParam_iff_realOn` (Iff.rfl),
`homGen_eq_homGenParam`, `homRes_eq_homResParam` (rfl), `homological_param` (core), `homological_direct`, `homological`.
Only textual difference: `{m : ℕ}` of `homological_param` is a section variable (same binder order n, m, D, ...).

## Approach
- `Z_K` is finite (`zFin`, via `KAM.modeCutoff`), so the generator and `P_Λ T_K f` are finite sums
  (`tsum_eq_sum`); `homGenParam = fourierSeries (genCoeff ..)` with `genCoeff` the indicator-guarded quotient.
- Class/coefficients/bound `qδ/(2πα)` from `coefficients_series` (holomorphy of `aₖ` via `DifferentiableOn.mul`/`.inv`
  after `div_eq_mul_inv`, per audit N5; pointwise `|aₖ| ≤ q|f̂ₖ|/(2πα)`).
- Directional identity by differentiating the finite sum termwise (`HasFDerivAt.mul/comp/fun_sum`, `hasFDerivAt_character`),
  `∑ᵢ kᵢωᵢ = dotC`, then comparing with `truncate` finite sum; `homRes` via `projections` twice; `homRes = projMode (Λ∩Z_K) f`
  from the coefficient formula of `projections`. No coefficient-of-product lemma was needed.
- Reality: generic lemma "conjugate-symmetric summand over a symmetric set is real" (`tsum` with `Equiv.neg`), using
  `KAM.torusCoeff_conjugateSymmetric`, `KAM.conj_character_real`, `conj(k·ω)=k·ω` for real ω.
- `homological_direct`: core with `q = conjExp p`, `ω = freq h` (holomorphy via `differentiableAt_freq` from N6-1);
  `poissonBracket φ (h∘snd) = ∑ ∂θᵢφ · freq i` by `HasFDerivAt.comp` with `snd`. `homological` = `divisor` (.2) + direct.
- Audit notes applied: `DifferentiableOn.mul/.inv` (not `.div`); holomorphy of `freq h` via `holomorphic_regularity`
  (existing `differentiableAt_freq`), not the nonexistent `DifferentiableOn.fderiv`.

## Checks
- `scripts/lint_sources.sh`: PASS on my file (only message: "KAM.lean is out of date; run scripts/gen_root_imports.py" — generated
  file, orchestrator to regenerate; check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK).
- Gate: `inp_lake_build.sh /root/code/KAM-inp-n62 KAM.Nekhoroshev.NormalForm.Homological` → `Build completed successfully (3171 jobs)`,
  no sorry/warnings.
- `#print axioms` for homological_param, homological_direct, homological, both eq-bridges, realOnParam_iff_realOn:
  `[propext, Classical.choice, Quot.sound]`.
- No `set_option` of any kind; file < 1500 lines.

## Uncertainties / errata / deviations
None. No statement needed changes; no heartbeat design signals. Private helpers (`genCoeff`, `zFin`, ...) are file-local.

AUDIT FOCUS (design docs/tracks/N/design/PART67-LEAN-DESIGN.md v2 row N6-2 and proof plan; audits DESIGN-N67-design-audit-{1,2}.md, esp. F3 (Part 11 homological reuse carrier, homological_param); blueprint-N p6 homological): (1) statements = design v2 signatures and blueprint (parameter core, both forms, bridges; constants and losses); (2) proofs sound (W4-7 projections, small divisors); (3) hygiene (lint incl. 100-char lines). Audit ONLY the N6-2 module(s) (KAM/Nekhoroshev/NormalForm/Homological*).
