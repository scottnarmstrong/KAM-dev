# N6-3 prover handoff (branch inp-n63, bfb2572; contains inp-n61 (N6-1, delivered); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/NormalForm/BracketDecomp.lean` (~165 lines). Nothing else touched.
**Node:** `bpN:p6:bracket-g` → `KAM.NormalForm.bracket_g`, statement copied verbatim from NPart67Signatures.lean.
**Approach:** per term `KAM.Weighted.wbound_bracket` with (u,v;r₀,s₀) = (gⱼ, φ; rⱼ, sⱼ); `fderiv_fun_sum` gives
`{∑gⱼ, φ} = ∑{gⱼ, φ}` on `Dom r s` (private `poissonBracket_sum`); private `wsum_finset_sum_le` (a copy of
the private `wsum_sum_le` of Weighted/Bracket with coefficients 1, stated on real slices) sums the weighted
bounds; the per-term constants sum to `2/(eρσ)·starNorm·Φ` by `field_simp`. InClass of the bracket: holomorphy via
`differentiableOn_poissonBracket`, periodicity via `inClass_fderiv_apply`. Third bound (`2/(ρσ)`) from the second
using `1 ≤ e`, `Φ ≥ 0`, `Mⱼ ≥ 0` (derived at a point `I ∈ V_{r-ρ}D` from the hypotheses; vacuous if empty).
**Checks:**
- `inp_lake_build.sh KAM.Nekhoroshev.NormalForm.BracketDecomp`: "Build completed successfully (3167 jobs)", no warnings, no sorry.
- `#print axioms KAM.NormalForm.bracket_g`: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; no long-line complaints after fix. It prints "KAM.lean is out of date; run scripts/gen_root_imports.py" (generated root, not edited by me; orchestrator regenerates).
**Uncertainties / errata / deviations:** none. No heartbeat issues; no set_option used.

AUDIT FOCUS (design docs/tracks/N/design/PART67-LEAN-DESIGN.md v2 row N6-3 and proof plan; audits DESIGN-N67-design-audit-{1,2}.md; blueprint-N p6 bracket-g): (1) statements = design v2 signatures and blueprint (bracket decomposition into resonant/nonresonant parts with the stated bounds); (2) proofs sound; (3) hygiene (lint incl. 100-char lines). Audit ONLY the N6-3 module(s) (KAM/Nekhoroshev/NormalForm/BracketDecomp*).
