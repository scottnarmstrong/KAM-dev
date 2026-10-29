# B17 prover handoff (branch inp-p11b-b17, ad0f5483; contains B16 (in audit) and B15; offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/WeakKAM/Displacement.lean` (~260 lines). Nothing else touched.

**Signed declarations (verbatim from P11BSignatures.lean):** `selectionDelta`, `selectionCDelta`,
`selectionCGamma`, `gamma_inverse`, `SelectionDisplacement`, `displacement`.
**Unsigned helpers:** `disp_rho_pos`, `disp_inv_A`, `disp_inv_B`, `disp_angle_le`, `disp_action_le`,
`disp_Xi_ge`, `disp_scalar` (steps dp-tel/dp-size), and `selectionDelta_le_power`
(literal conclusion of dpc-comb: Δ ≤ cΔ·cγ·√ε·β^(-(μ+1)/ρ); B20 consumes it).
Short names grepped: none pre-existing in KAM.

**Approach:** `displacement` takes `limit_torus`, reads the angle/action sums from the limit
record's complex bounds at `selectionReal θ` via `limit_real`, and bounds them by `wbud_exported`
(E2). Size: strip ≤ 1, s₀ ≤ t₀/(8n) ≤ 1/8, Q₀·Ξ ≤ 2⁻¹⁰ with Ξ ≥ 2. Power: Q₀/128 = cΔ√ε/γ with
ε₀/s₀ = √(2nC₁ε) (free_radius). `gamma_inverse`: case split on `min`, exact β-exponent identity
for the second branch.

**Checks:** gate build `KAM.Planetary.WeakKAM.Displacement` succeeded, no warnings/sorry;
`scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI OK; only message is
"KAM.lean is out of date" (generated; not edited per rules). Max line 99 cols.
`#print axioms` of `displacement`, `gamma_inverse`, `selectionDelta_le_power`: propext,
Classical.choice, Quot.sound.

**Uncertainties / errata / deviations:** none. No heartbeat issues. Not landed/pushed.

AUDIT FOCUS: design docs/tracks/P/design/P11B-LEAN-DESIGN.md row B17 (displacement, gamma-inverse, pointwise powers; B07, B13, B15, B16, P11A power_law explicit constants) and its node table incl. dp-* and dpc-* steps; P11B design audits; signatures /root/code/KAM-inp/.drafts/design/P11BSignatures.lean. Audit ONLY KAM/Planetary/WeakKAM/Displacement.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
