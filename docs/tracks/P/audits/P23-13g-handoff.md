# P23-13g prover handoff (branch inp-p2313g, cebb304; contains inp-p2313b (audited); offloaded package run by the main orchestrator; prover on claude-12)


Branch `inp-p2313g`, worktree /root/code/KAM-inp-p2313g.

## Files
- NEW `KAM/Planetary/Averaging/OscillatorRemainderData.lean` (~500 lines, under the 1500 cap). No other file touched.

## Declarations proved
- `oscRemIntegrand` (verbatim from `P23Signatures.lean`) and `osc_remainder_decomposition` (statement byte-identical to the signature
  file; I only added `set_option linter.unusedVariables false in` as `osc_bracket` does, and wrapped the binder line at 100 columns).
- Helpers (distinct names, no conclusion-shaped hypotheses): `osc_bound_mono`, `osc_bound_nonneg`, `osc_class_const_mul`,
  `osc_bound_add_sum`, `oscActionL`, `fderiv_oscH0`, `firstBlock_single_cast/nat`, `osc_hom_bracket`, `pb_lin3`, `pb_sum`,
  `pb_congr_eventually`, `osc_W_le`, `osc_bracket_bound_le`.

## Approach
1. `osc_hom_bracket`: at each point `z` of the original domain, re-run `homological_param` on a ball at the flat parameter
   (as `osc_hom_local` does, but keeping the equation conclusion and the `Λ={0}` residual); transport the flat directional
   derivative to `oscGen = G ∘ oscPackL`; compute `{H₀,φ}` coordinatewise (castAdd/natAdd split) to get `{H₀,φ} = ξ − T`.
2. Class/bound: `osc_bracket` for each `gj` (outer widths `rj..`, generator widths `r..`, loss `ρ..`), for the zero mode and for
   `T = oscTruncate K f` (both bound δ); the convex combination is handled by `osc_bound_const_mul` with `‖1−t‖+‖t‖=1`;
   finite sum by `osc_bound_add_sum`. `W ≤ 2(1+m)·max` via `osc_W_le`. The nonemptiness of the parameter set is case-split to
   get `0 ≤ Mj`. Equality of `v t` with the decomposition on `O` by `pb_lin3` + `pb_sum`, transport by `oscBound.congr`/`oscClass.congr`.
3. Continuity of `v` and `D v`: on `O` (open) `v t = P + (1−t) Q + t R` with `P,Q,R` brackets; they are holomorphic
   (`differentiableOn_poissonBracket`), so continuous, and so are their derivatives
   (`holomorphic_regularity_of_finiteDimensional`); `fderiv` of the combination by `fderiv_fun_add/const_mul`.
4. Identity: `taylor_poschel` with `W = OscFlowHyp.W`, `Ω=Ω₁=O`, `h=H₀`, `f₀=g+T`, trajectory in `O` from `flow_a`;
   integrand rewritten pointwise (eventual equality near each flow point, `pb_congr_eventually`) using `osc_hom_bracket`;
   closing step is a `linear_combination`.

## Checks
- `lake build KAM.Planetary.Averaging.OscillatorRemainderData` via the gate: see the end of this file.
- `sh scripts/lint_sources.sh`: no long-line or sorry complaints for this file; only the generic "KAM.lean is out of date" notice
  (I did not touch KAM.lean).
- No `sorry`, `axiom`, `maxHeartbeats`, or other option overrides in the file.

## Uncertainties / errata / deviations
- No statement looked false; no errata found in pinned sources.
- Deviation: none in signatures. The block-sum condition `0 ≤ Mj j` is not a hypothesis of the signature; it is derived inside the
  proof only when the parameter set at the smaller widths is nonempty (when empty, the weighted bound is vacuous).
- No heartbeat problems; all proofs elaborate at default heartbeats.
- `OscillatorRemainderData` is not in `KAM.lean` (generated; orchestrator to rerun `scripts/gen_root_imports.py`).

## Gate build / axioms (final)
- `inp_lake_build.sh /root/code/KAM-inp-p2313g KAM.Planetary.Averaging.OscillatorRemainderData`: `Build completed successfully (9121 jobs)`, no sorry warning.
- `#print axioms KAM.Planetary.osc_remainder_decomposition`: `[propext, Classical.choice, Quot.sound]`.

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md section 'Revision 3', row P23-13g and Appendix A.3; design audit docs/tracks/P/design/P23-design-audit-1.md; signatures .drafts/design/P23Signatures.lean): (1) statements = Appendix A.3 signatures exactly (oscRemIntegrand, osc_remainder_decomposition); the identity fp = integral of {g+(1-t)xi+t*T_K*f, phi} along the SAME flow + composed truncation tail; (2) proofs sound (homological_param, Canonical.Lie used correctly); no added premises; (3) hygiene. Audit ONLY KAM/Planetary/Averaging/OscillatorRemainderData*.lean (compare with branch inp-p2313b).
