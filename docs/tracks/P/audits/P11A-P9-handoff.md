# P11A-P9 prover handoff (branch inp-p11ap9, c7d9bd3f; off inp; offloaded package run by the main orchestrator; prover on claude-12)

ORCHESTRATOR NOTES: (a) the prover created the file at KAM/Preparation/ForwardTube.lean; the orchestrator moved it to the design path KAM/Planetary/Preparation/ForwardTube.lean (c7d9bd3f) and rebuilt. (b) RULING on the deviation: the signed forward_tube / p11PhysicalDelta take D : P11Physical n, which the design assigns to Preparation/Working (P11A-P1, blocked on S10-R). forward_tube_core is accepted as an internal helper proving the same content from the raw data (G, m0, m, a); the signed one-line wrappers forward_tube and p11PhysicalDelta are deferred to P11A-P1, which must add them verbatim by applying forward_tube_core to D's fields. No premise is added to any signed declaration.


**Files:** new `KAM/Preparation/ForwardTube.lean` (224 lines). KAM.lean not edited (lint says "KAM.lean is out of date; run scripts/gen_root_imports.py" – orchestrator to regenerate).

**Proved:** `bpP:p11:forward-tube` as `KAM.Planetary.forward_tube_core` (raw data G m0 m a with 0<G, 0<m0, positivity of m, a; ζ>0): ∃ δ>0, δ ≤ m_i√(G m0 a_i)/4 ∀i, ∀ w with |Λ_i-Λ_i*| ≤ δ and Γ_i ≤ δ, w ∈ poincareProdDom n ∧ ‖poincareProd m (G m0) w - circularPoint G m0 m a (λ/2π)‖ < ζ. Conclusion is exactly that of the signature `forward_tube`.

**DEVIATION (needs orchestrator ruling):** the signature `forward_tube`/`p11PhysicalDelta` take `D : P11Physical n`, but `P11Physical` (and p11Zeta, p11_zeta_pos) is assigned by the design to `Preparation/Working` (P1), which depends on P9; it does not exist on this branch. I therefore did not duplicate it. `forward_tube` and `p11PhysicalDelta` are one-line wrappers
`obtain from forward_tube_core D.G_pos D.m0_pos D.m_pos D.a_pos hzeta` to be added in Working (or in a module after it). p11_zeta_pos and the statement are untouched.

**Approach:** compactness of the torus image K={assemble Λ* 2πφ 0 0, φ∈[0,1]^n}; U={w∈dom | ‖Ψ w - circ(λ/2π)‖<ζ} open (Ψ analytic on dom), contains K (circularPoint_eq_poincareProd); cthickening r K ⊆ U; δ=min(c, r, r²/2) (c lower bound of Λ*_i/4); angles reduced mod 2π via poincareProd_lattice and circularPoint fract-invariance; |ξ|,|η| ≤ √(2δ) ≤ r from Γ ≤ δ. Dom membership directly from Λ ≥ 3/4Λ*, Γ ≤ Λ*/4.

**Checks:** gate build `KAM.Preparation.ForwardTube`: success, no warnings in file. `#print axioms forward_tube_core`: [propext, Classical.choice, Quot.sound]. `scripts/lint_sources.sh`: module check PASS, FROZEN-ANCHOR OK, ABI OK; only note is KAM.lean out of date (generated).

**Uncertainties/errata:** none found; no heartbeat issues (no overrides).

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-P9 and node bpP:p11:forward-tube; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): refute-first: (1) forward_tube_core's statement, instantiated at the fields of any P11Physical D (G_pos, m0_pos, m_pos, a_pos, zeta), yields EXACTLY the signed forward_tube / p11PhysicalDelta conclusions, so the deferred wrappers will be one-line; check that no hypothesis of forward_tube_core goes beyond what P11Physical provides; (2) proof sound (compactness of the torus image, the open neighbourhood via analyticity of the Poincare chart, cthickening, angle reduction mod 2pi via poincareProd_lattice and circularPoint fract-invariance); (3) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/Preparation/ForwardTube.lean.
