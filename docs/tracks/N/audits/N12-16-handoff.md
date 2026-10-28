# N12-16 prover handoff (branch inp-n1216, f4b6fc2; contains N12-01..N12-15 (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/Averaging/Mean.lean` (~165 lines). Nothing else changed (KAM.lean untouched; lint notes it is out of date, generated).

**Nodes:** `mean_family` (me-flow/me-cont), `averaging_mean_core` (me-good/bad/mean/markov, `s-mean#data`: A = 13*A₁). Signatures copied verbatim (whitespace-normalised textual comparison: identical).

**Approach:**
- `mean_family`: for x∈K, the supplied Φ x is a solution on [0,1/ε] in `avgDomain`; `IsMaximalSolution.maximal` (from `avgMaximal_spec`) gives [0,1/ε] ⊆ eIoo and Φ x = avgFlow there. So `averagingError ε Φ = sSup` of the flow displacement on K; continuity on K from `continuousOn_sSup_disp` (N12-15/02), integrable on compact K; bounds 0 ≤ m ≤ 3R/2 from the action ball.
- `averaging_mean_core`: A₁ from `bad`. Pointwise ofReal m ≤ 13·avgStopped on K: on `avgGood (R/8)` via the attained max and bad's third conjunct; off it via bad's nonstrict threshold and m ≤ 3R/2 = 12·(R/8). (Simpler than the design's Γρ/Markov split: no separate ρ·vol estimate.) Integral ≤ ofReal(13A₁√ε). E = {x∈K | λ < m x}, λ = A√ε/κ; measurable via continuity on K (domRestrict, subtype_image); Markov via setLIntegral.

**Checks:** gated build `KAM.Nekhoroshev.Averaging.Mean` succeeded (final rerun after docstring rewrap also succeeded, 3248 jobs, no Mean.lean warnings). `#print axioms` of both theorems: `[propext, Classical.choice, Quot.sound]`. `scripts/lint_sources.sh`: no long-line errors; check_lean_modules PASS, frozen guard OK, ABI hashes OK; only note "KAM.lean is out of date" (generated, not mine). No heartbeat options, no sorry.

**Uncertainties / errata / deviations:** none. No signature changes. Design signals: none.

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-16 and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements of mean_family and averaging_mean_core = signature file exactly; (2) proof sound (an arbitrary supplied family gains continuity ON K by uniqueness via IsMaximalSolution.maximal; good/bad split, Markov, A = 13*A1; N12-14 Stopped and N12-15 GoodSet consumed as designed); no added premises; this package feeds the N12-18 provider for the frozen averaging_mean, so check fidelity strictly; (3) hygiene. Audit ONLY KAM/Nekhoroshev/Averaging/Mean.lean (compare with branch inp-n1215).
