# S7-2 prover handoff (branch inp-s72, 4c2ce1a; contains inp-s71 (S7-1, delivered); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/Stability/Gradient.lean` (200 lines). No other file touched; KAM.lean not edited.

**Nodes proved (signatures verbatim from NPart67Signatures.lean B.3):**
- `bpN:p7:theta-derivative` -> `KAM.Stability.theta_derivative`
- `bpN:p7:resonant-gradient` -> `KAM.Stability.resSpan` (def), `KAM.Stability.resonant_gradient`

**Approach.**
- theta_derivative: for `0<s'<s`, `cauchy_theta` (s0 = s); pointwise bound `‖v z‖ ≤ wsum v s' z.2` (private `norm_le_wsum`, from
  `coefficients_repr` + `norm_character_le`, same argument as `sup_le_wbound`) at `z = ι₂(θ,I)` (in `Dom ϱ s'` by
  `realInclusion₂_mem_Dom_iff`); sum over j <= `wsum u s I/(e(s-s'))` <= `M/(e(s-s'))`; `s' ↓ 0` by `ge_of_tendsto`.
  Euclid bound from `euclid ≤ ∑‖·‖` (private). Value bound is `sup_le_wbound`.
- resonant_gradient: `thetaGradR (realH g) x i = Re (dtheta i g (ι₂ x))` (chain rule via `Complex.reCLM`); for `v ⊥ Λ`,
  `∑ vⱼ ∂θⱼ g (ι₂ x) = 0` since each term's Fourier series (`coefficients_repr` at width s/2, coefficients from
  `coefficients_deriv`) has summand `2πi (v·k) ĝ_k χ_k = 0` (k ∈ Λ: v·k=0; k ∉ Λ: ĝ_k=0), uniqueness of sums; membership in
  `resSpan Λ` by contradiction with `Submodule.exists_dual_map_eq_bot_of_notMem` (functional = dot with v).

**Checks.**
- `inp_lake_build.sh /root/code/KAM-inp-s72 KAM.Nekhoroshev.Stability.Gradient`: Build completed successfully, no sorry; only warning:
  unused variable `hgr` in `resonant_gradient`.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; prints
  "KAM.lean is out of date; run scripts/gen_root_imports.py" (expected: new module; I did not edit KAM.lean — orchestrator regenerates).
- `#print axioms theta_derivative` and `resonant_gradient`: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties / design notes.** `hgr : RealOn …` of `resonant_gradient` is unused by the proof (taking real parts suffices);
statement kept verbatim, so the linter warns. No heartbeat issues, no set_option. No suspected errata or deviations.

AUDIT FOCUS (design docs/tracks/N/design/PART67-LEAN-DESIGN.md v2 row S7-2 and proof plan; audits DESIGN-N67-design-audit-{1,2}.md; blueprint-N p7 theta-derivative, resonant-gradient): (1) statements = design v2 signatures and blueprint; (2) proofs sound; (3) hygiene (lint incl. 100-char lines). Audit ONLY the S7-2 module(s) (KAM/Nekhoroshev/Stability/Gradient*).
