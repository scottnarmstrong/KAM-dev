# GAP-B prover handoff (branch inp-gapb, 280b5f15; offloaded package run by the main orchestrator)


Files: new `KAM/Planetary/WeakKAM/BudgetsTail.lean` (~190 lines). Nothing else touched (KAM.lean not regenerated:
`lint_sources.sh` reports "KAM.lean is out of date; run scripts/gen_root_imports.py" - orchestrator to regenerate).

Step -> declaration (unsigned):
- `stepP:p11a:es-3` -> `KAM.Planetary.exported_sums_es_3 (d) (ε) (he : 0 ≤ ε) (hsmall : ε ≤ selectionAdmissible d)`:
  for a := adm_params d ε and all ν:
  `(∑' j, (A a (j+ν) + α a (j+ν))) / t a (ν+1) ≤ 3 Q₀ Ξ / C_Q + Q₀ Ξ / 16 ∧ 3 Q₀ Ξ / C_Q + Q₀ Ξ / 16 ≤ 2⁻¹⁰ ∧
  ∑' j, selectionRealBudget a (j+ν) ≤ 2⁻¹²`. Same hypotheses as B13's `exported_sums`.
- Context form `exported_sums_es_3_ctx (c : WeakBudgetCtx d a) ν`; helper `wbudtail_quot` (tail quotient
  ≤ 32/31·(cA + cα), no short-name clashes in KAM).
Approach: reuses B13's `wbud_*` lemmas (lip_term geometric domination, tsum_shift_le, Xi lower bounds); bounds the
constants by `Q₀Ξ/C_Q`, `Q₀Ξ/32` (using s₀ ≤ t₀, Xi ≥ 2^(τ+1), Xi ≥ 2^(τ+1)σ/t₀), 32/31·2 ≤ 3, 32/31/32 ≤ 1/16;
middle inequality via C_Q ≥ 162, Q₀Ξ ≤ 2⁻¹⁰. Real tail: shift ≤ full sum ≤ 2⁻¹² (B13 constants).

Checks: gate build `KAM.Planetary.WeakKAM.BudgetsTail` succeeded (no warnings in the new file);
`lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK (only the KAM.lean staleness note);
`#print axioms exported_sums_es_3`: [propext, Classical.choice, Quot.sound]; no line > 100 cols.

Parent `bpP:p11a:exported-sums`: with this, every step is established: E1 `exported_sums` (∀ ν clause 9, B13),
E2 `exported_sums` (sum conjuncts, B13), E3 `exported_sums_es_3` (literal form; its final-2⁻¹⁰ scalar is also in
`exported_sums`), E4 B10 es-4 (Iteration modules). Caveat: blueprint SOURCE_CONCLUSION of the parent says Λ tail ≤ 2⁻¹⁰ while
es-3 says 2⁻¹²; proved the stronger 2⁻¹² (implies both).
Uncertainties/errata/deviations: none. Design signals: none.

AUDIT FOCUS: ORCHESTRATOR RULING (OVERNIGHT 23:10): append-only gap fill of graph step stepP:p11a:es-3 of bpP:p11a:exported-sums (left NOT_STARTED after B13 and B10). Read NODE: stepP:p11a:es-3 in docs/graph/P/DEPGRAPH.md (~line 26172) and the cited blueprint lines; verdict: does exported_sums_es_3 state that literal conclusion (both the A-sum quotient chain <= 3 Q_0 Xi/C_Q + Q_0 Xi/16 <= 2^-10 and the Lambda_R tail <= 2^-12) for the existing Lean objects, with only B13's exported_sums hypotheses? Also say whether bpP:p11a:exported-sums now has every step (E1-E4) established and by which declarations. Audit ONLY KAM/Planetary/WeakKAM/BudgetsTail.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
