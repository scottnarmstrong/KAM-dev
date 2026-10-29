# B20 prover handoff (branch inp-p11b-b20, c3296afb; contains B19 (passed), B18, B17, B16; offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/WeakKAM/PolynomialBudget.lean` (~320 lines). No other file touched.

**Declarations (signed ones verbatim):** `selectionFixedKey`, `selectionBetaExponent`, `SelectionRates`,
`selectionBudget{D,G,L,J,X,H,Exponent}`, `selectionFamilyBounds`, theorems `adm_budget`,
`adm_budget_beta`, `displacement_power`. Helpers (new, all prefixed `polyBudget_`):
`polyBudget_thetaMax_le`, `polyBudget_threshold_le`, `polyBudget_exponent_eq`, `polyBudget_key`,
`polyBudget_exponent_beta`, `polyBudget_CDelta`, `polyBudget_CGamma`.

**Approach.**
- `adm_budget`: reuse the delivered P11C `qb_poly` (KAM.Planetary.Quantitative.BudgetPower) through the
  existing correspondence `qbcOfSelection d (selectionM₀ d + 1)` (+1 makes M0 positive, since positivity of
  `selectionM₀` is not available). Rate bounds are used at c/2. `polyBudget_threshold_le` shows
  `thresholds Q ≤ selectionAdmissible d` (copy of `qb_comp` with `0 ≤ M₀` instead of `0 < M₀`; uses
  `qbc_oldThreshold_eq_selectionAdmissible`, so the three lambdaMax branches are compared with C₁≥1 in the
  first branch). `polyBudget_exponent_eq` identifies `BudgetRates.exponent` with `selectionBudgetExponent`
  (needs `max_assoc`, `if 0<s` vs `if s=0` for s≥0).
- `adm_budget_beta`: apply `adm_budget` with rates (0,0,1,0,0,0,0,0), strip rate 0, u := β, and
  c0 = min(ϑ, strip, loss, 1/(1+M+M₀+C₁+diam K)) taken from d₀; exponent computed to be `selectionBetaExponent`.
- `displacement_power`: cstar from `adm_budget_beta`; cD = selectionCDelta d₀ * selectionCGamma d₀
  (key-invariant, lemmas `polyBudget_CDelta/CGamma`); output from `evaluation_bilipschitz` (B19) and
  `selectionDelta_le_power` (B17, dpc-comb) via `o.displacement`.
  Its conclusion is the literal K5/K6 statement (bpP:p11a:displacement-power, stepP:p11a:qt-k6).

**Checks.** `inp_lake_build.sh … KAM.Planetary.WeakKAM.PolynomialBudget`: Build completed successfully,
no warnings in my file. `#print axioms` of adm_budget, adm_budget_beta, displacement_power: all
[propext, Classical.choice, Quot.sound]. `scripts/lint_sources.sh`: module check PASS, frozen guard OK,
ABI OK; only message is "KAM.lean is out of date; run scripts/gen_root_imports.py" (generated; I may not
edit it — orchestrator should regenerate). No lines >100 cols; no maxHeartbeats.

**Deviation / notes.**
- Imports `KAM.Planetary.Quantitative.BudgetPower` and `…BudgetAdmissible` (P11C Q2/Q3, already on main;
  BudgetAdmissible imports WeakKAM.Admissible only, so no cycle; no provider/DRAFT_SORRY imported).
  The design listed inputs B07,B17,B19 + explicit formulas; reusing Q3 avoids re-proving ~1000 lines.
  If P11C-Q6 / Q-files will import PolynomialBudget, make sure none of Q2/Q3's imports import it.
- No `KAM/Planetary/WeakKAM.lean` facade added (design: optional).
- No suspected errata; no design signals (default heartbeats everywhere).
- Uncertainty: none open; signature statements were provable as stated.

AUDIT FOCUS: design docs/tracks/P/design/P11B-LEAN-DESIGN.md row B20 (adm-budget, adm-budget-beta, uniform displacement-power; B07, B17, B19, explicit sublevel/power_law formulas) and its node table incl. the ab-* steps of bpP:p11a:adm-budget, displacement-power and qt-k6 (the sub-orchestrator holds bpP:p11a:displacement-power and stepP:p11a:qt-k6 open until B20's uniform displacement_power: check it states those nodes' literal conclusions); P11B design audits; signatures /root/code/KAM-inp/.drafts/design/P11BSignatures.lean. Check the M0+1 device (positivity of selectionM0 unavailable) adds no premise and the copied qb_comp variant is sound. Audit ONLY KAM/Planetary/WeakKAM/PolynomialBudget.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
