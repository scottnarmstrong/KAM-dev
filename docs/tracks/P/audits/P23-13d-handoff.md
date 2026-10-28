# P23-13d prover handoff (branch inp-p2313d, febe620; contains inp-p2313c, inp-p2313b (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/Averaging/OscillatorCompositionSeries.lean` (~100 lines). No other file touched.

**Declarations (signatures verbatim from P23Signatures.lean):** `OscComposeData` (structure, Prop), `osc_lie_series`.

**Approach:** apply `osc_adjoint_bound` with r:=r-ρ, … (u on the one-loss domain, φ on the original domain as outer; margins r-ρ+ρ ≤ r etc.),
giving class and bound `q^j*A` of `(j!)⁻¹ ad^j_φ u` on the two-loss domain (`q=oscLieRatio`); `const_mul` for class.
`osc_ratio_range` (+ `small`) gives 0 ≤ q ≤ θ, (16/9)θ<1 so q<1. `osc_bound_tsum` with b j = q^j A (summable geometric) gives class, bound
`∑ q^j A = (1-q)⁻¹A` and weighted tails; HasSum from `oscBound.norm_le` + `Summable.of_norm_bounded`.

**Checks:** `inp_lake_build.sh … KAM.Planetary.Averaging.OscillatorCompositionSeries`: Built successfully, no warnings/sorry.
`#print axioms KAM.Planetary.osc_lie_series`: `[propext, Classical.choice, Quot.sound]`.
`scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; reports "KAM.lean is out of date; run
scripts/gen_root_imports.py" (generated file, not edited per rules — orchestrator to regenerate; it lists the new module).

**Uncertainties / design signals:** none; default heartbeats, no overrides.
**Suspected errata / deviations:** none. No premises added.

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md section 'Revision 3', row P23-13d and Appendix A.3; design audit docs/tracks/P/design/P23-design-audit-1.md; signatures .drafts/design/P23Signatures.lean): (1) statements = Appendix A.3 signatures exactly (OscComposeData, osc_lie_series); (2) proofs sound (q-geometric sums, holomorphic and periodic limit, HasSum and weighted tails); no added premises; (3) hygiene. Audit ONLY KAM/Planetary/Averaging/OscillatorCompositionSeries*.lean (compare with branch inp-p2313c).
