# N6-6 prover handoff (branch inp-n66, ae47845; contains inp-n65 (N6-5, N6-2, N6-1, C5-10; audited) and inp (N6-3, C5-8, C5-9, W4-7); offloaded package run by the main orchestrator; prover on claude-12)


## Files
- New: `KAM/Nekhoroshev/NormalForm/IterativeRemainder.lean` (≈425 lines). Imports `IterativeMap` directly (not the facade),
  `BracketDecomp`, `Canonical.CompositionIntegral`, `Canonical.Transform`. No other file touched (KAM.lean not edited: lint reports
  it out of date, which is for the orchestrator's `gen_root_imports.py`).

## Nodes proved
- `bpN:p6:iterative-direct` (c): `KAM.NormalForm.iterative_direct_c` — signature copied verbatim from `NPart67Signatures.lean`.
- `bpN:p6:iterative-direct` (d): `KAM.NormalForm.iterative_direct_d` — signature copied verbatim.

## Approach
- `IterHyp.compose`: `ComposeData D (r-ρ) (s-σ) r s ρ σ Φ φ` for `φ = homGen`, `Φ = qδ/(2πα)`; `η = 2·iterU ≤ 1/2`
  (`iterMap` is `ComposeData.omega`'s flow by `rfl`).
- `transform` with `h ↦ h∘snd`, `f₀ = g + T_K f`, `w = {h∘snd, φ} = ξ - T_K f` (bound `2δ`; `IterHyp.bracket_eq` from
  `homological_direct` (a) + antisymmetry). `g`'s class/finite norm from `IsDecomp` (`decomp_wbound`, Finset induction).
- Integrand `remIntegrand t = {(1-t){h',φ} + f₀, φ}`; equals `{g + (1-t)ξ + t T_K f, φ}` on `Dom (r-ρ)(s-σ)`.
  `IterHyp.integrand` supplies the three hypotheses of `composition_integral`: class + bound `2/(eρσ)(|g|_*+δ)Φ` via `bracket_g` on the
  decomposition extended by the term `f_t` (`isDecomp_snoc`, `starNorm_snoc`), continuity of `(t,z) ↦ v_t z` and of `D v_t` from the
  pointwise affine-in-`t` form (`eq1`, `eq2`) and `ContDiffOn` of holomorphic `A,B,C` brackets.
- `IterHyp.iterF_class_bound`: `iterF = 𝓡 + (f - T_K f)∘Φ` pointwise on `Dom (r-2ρ)(s-2σ)` (linear combination of the transform identity and
  `bracket_eq`); tail by `truncation_tail` + `composition_series` (clauses 5, 6); sum by `wbound_add`; final constants by `field_simp`.
  (c) and (d) are then read off (c's identity is definitional from `iterF`).

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-n66 KAM.Nekhoroshev.NormalForm.IterativeRemainder`: `✔ Built ... Build completed successfully (3226 jobs)`, no warnings.
- `sh scripts/lint_sources.sh`: no complaint for my file (long-line list now has no IterativeRemainder entry); remaining output is
  `KAM.lean is out of date` and the pre-existing over-100-char line in `KAM/Planetary/Hamiltonian/Liouville.lean:35` (not mine);
  `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`.
- `#print axioms` (scratch copy): `iterative_direct_c`, `iterative_direct_d`: `[propext, Classical.choice, Quot.sound]`.
- Verbatim check of both statements against the signature file (diff of the theorem text: identical).
- No `sorry`, `axiom`, `set_option`, no heartbeat overrides; file ≪ 1500 lines.

## Uncertainties / errata / deviations
- None: no statement needed changing or an extra hypothesis; no suspected source errata.
- Extra public declarations (helpers, not blueprint nodes): `IterHyp.compose`, `IterHyp.iterMap_eq`, `IterHyp.bracket_eq`, `IterHyp.hClass`,
  `remIntegrand`, `IterHyp.integrand`, `IterHyp.iterF_class_bound`. Private: `inClass_mono'`, `wbound_zero`, `decomp_wbound`, `poissonBracket_lin`,
  `poissonBracket_congr`, `isDecomp_snoc`, `starNorm_snoc`.
- Design signals: none (default heartbeats everywhere; module builds in ~10 s).

AUDIT FOCUS (design docs/tracks/N/design/PART67-LEAN-DESIGN.md v2 row N6-6 and proof plan; audits DESIGN-N67-design-audit-{1,2}.md; blueprint-N p6 iterative (c),(d)): (1) statements = design v2 signatures and blueprint; IterativeRemainder imports IterativeMap directly, never the Iterative facade; (2) proofs sound, consuming N6-3 BracketDecomp, C5-8/C5-9 and W4-7 as designed; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Nekhoroshev/NormalForm/IterativeRemainder.lean; other files in the diff are inherited from inp merges.
