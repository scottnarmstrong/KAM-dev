# P11A-P7d prover handoff (branch inp-p11ap7d, 01c51946; contains P7c round 1 (fixing: P7cb), P7b, P7 round 1 (both passed), P5; offloaded package run by the main orchestrator)


## Files (new, KAM/Planetary/Preparation/)
- `SlowCoeff.lean` (~120 lines): `p11_torusAverage_natAdd` (2n-torus average of a function of the last n angles),
  `p11_slow_coeff_zero` (‖coeff f2 I 0‖ ≤ (eps MF)^3 on the avg box, from clauses 1-2 of the spec + P11FastSpec;
  the polar average of G∘Π cancels the eps·𝒜G term exactly).
- `SlowMW.lean`: `p11_C_norm_le`, `p11SlowMW`, `p11_slow_MW` (eps-independent sup bound of p11SlowW on the Z domain, needs η1 ≤ 1).
- `SlowAssembly.lean`: `p11_slow_eventually` (all eventual smallness conditions), `p11SlowAsmC`, `p11_slow_at`,
  **`avg_slow_of_spec`** (hC, 1 ≤ nu, 0 < eps1, Fast : ℝ → P11FastData n with P11FastSpec for eps ≤ eps1 ⊢
  ∃ eps2 c2, 0<eps2 ∧ eps2<1 ∧ 1≤c2 ∧ ∀ eps ≤ eps2, ∃ A, P11SlowSpecOf C (Fast eps) nu eps c2 A).
  `P11SecularHReal` is not needed (p11_slow_osc does not use it), so it is omitted.
- `SlowSigned.lean`: signed `P11SlowSpec`, `avg_slow`, `p11SlowConstant`, `p11SlowData` (long lines re-wrapped; no hypothesis added).
  `avg_slow` = `avg_slow_of_spec` at `(holo_chart D).choose_spec.1` and `p11FastData D` (hF from `avg_fast`); P11SlowSpec ≡ P11SlowSpecOf by defeq.
- `Slow.lean` facade now imports the P7/P7b/P7c/P7d modules. Merged inp-p11ap7c (append_eq_add rename).

## Approach
c₂ = max of c₀ (P7b) and the explicit constants hcg/hcd1/hcd3 of `p11_slow_conclude` (cf0 = M_F^3); ε₂ from the eventual lemmas
(base, π ε ≤ s₂, divisor cZ-smallness, Cauchy smallness with MW, b2) plus η1 ≤ 1, ε ≤ ε_osc, ε ≤ ε₁, ε<1/2.
Clauses 1-6 are restrictions of `p11_slow_osc` outputs (box V₂ ⊆ avg box), clause 6/jets monotone in c, divisor from `p11_slow_divisor`,
clauses 7-28 from `p11_slow_conclude`.

## Checks
- Gate build of `KAM.Planetary.Preparation.Slow` (all modules): `Build completed successfully (9418 jobs)`.
- `sh scripts/lint_sources.sh`: only the generated-KAM.lean notice; `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`.
- `#print axioms` of `avg_slow`, `avg_slow_of_spec`, `p11SlowData`: `[propext, Classical.choice, Quot.sound]`.
- No sorry/maxHeartbeats/axiom; all lines ≤ 100 columns; each file < 250 lines.

## Uncertainties / deviations / errata
- Only warning: deprecated `dif_pos` in SlowSigned (cosmetic). No errata found; no signed statement changed.
- `P11SecularHReal` hypothesis dropped from the core (unused).

ORCHESTRATOR RULINGS: 23:00/23:35 P7 parametric core split into P7b/P7c/P7d; 00:20 piece audits. P7c's fix round (P7cb) proves the literal mixed divisor bound delta0/2 for as-nr; if it strengthens p11_slow_divisor's statement, P7d will merge it before landing; the signed spec needs only delta0/4.

AUDIT FOCUS: the SIGNED P11SlowSpec, avg_slow, p11SlowConstant, p11SlowData (P11ASignatures.lean ~lines 979-1045) EXACTLY, with P11SlowSpec definitionally equal to P11SlowSpecOf (p11SecularData D) (p11FastData D eps); avg_slow_of_spec proved from P7b and P7c with no added premise (the handoff omits P11SecularHReal as unneeded: confirm); every clause of P11SlowSpec discharged; graph node bpP:p11:avg-slow and steps as-osc/as-nr/as-b2/as-concl now established (as-nr subject to P7cb); the eps-independence of MW and cf0. Audit ONLY: KAM/Planetary/Preparation/SlowAssembly.lean KAM/Planetary/Preparation/SlowCoeff.lean KAM/Planetary/Preparation/Slow.lean KAM/Planetary/Preparation/SlowMW.lean KAM/Planetary/Preparation/SlowSigned.lean  Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
