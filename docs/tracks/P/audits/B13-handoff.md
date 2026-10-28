# B13 prover handoff (branch inp-p11b-b13, 6f7490d1; contains B07 (round 2 in audit); offloaded P11B package run by the main orchestrator)


## Files (new)
- `KAM/Planetary/WeakKAM/BudgetsStage.lean` (~290 lines): verbatim signature defs `selectionΛ`, `selectionA`,
  `selectionAlpha`, `selectionKappa`, `selectionMapBudget`, `selectionRealBudget`, `selectionQactual`;
  helpers `selectionΛ_one_le/_nonneg/_anti/_le_pow`, `WeakBudgetHyp`, `weakBudgetHyp_of_adm`,
  `wbud_*` stagewise lemmas, `wbud_stage` (= E1: A ≤ 2σQ/C_Q, κ ≤ Q/16, α = κ s/2, Λ_R bound, Q ≤ Q₀ g₁^ν).
- `KAM/Planetary/WeakKAM/Budgets.lean` (~520 lines; imports BudgetsStage): `exported_sums` (E1–E3; node steps
  es-1..es-3), `param_lip_sum` (pl4-terms, pl4-sum), helpers `wbud_*`, `WeakBudgetCtx`, `weakBudgetCtx_of`.
  Budgets.lean is the facade-importing module named in the brief; BudgetsStage was split out for size/elaboration.
- Commits on branch inp-p11b-b13 (all edits committed). KAM.lean not edited (needs regeneration for the 2 new modules).

## Approach
One general estimate for every admissible schedule a built from d (`WeakBudgetCtx d a`): each budget is
dominated by c·(1/32)^j with explicit c, constants controlled by Q₀Ξ ≤ 2⁻¹⁰ (adm weighted) and C_Q ≥ 162, π ≤ 4.
E3 and param_lip_sum follow from the termwise bound (A_j+α_j)/t_{j+1} ≤ c·(1/32)^j (uses g₁w/2 = g₄ ≤ 1/32,
g₁ q w ≤ 1/32) and t_{j+ν+1} ≤ t_{ν+1}. exported_sums specialises to `adm_params d ε` via `adm_choice`;
param_lip_sum to `selectionAdapted d ε` via `free_radius`. Uses strip_budget (r_j - d_j ≥ σ_j, E_j ≤ 1/8),
schedule_props (Q^♯ = Q₀ g₁^j), schedule_ratios. E4 (parameter Cauchy) is not a statement of this module
(signature has none; it belongs to the iteration/canonical-step package, B10).

## Checks
- Gate: `inp_lake_build.sh /root/code/KAM-inp-p11b-b13 KAM.Planetary.WeakKAM.BudgetsStage KAM.Planetary.WeakKAM.Budgets`
  -> "Build completed successfully"; no warnings in my files (warnings shown are in pre-existing Admissible.lean).
- `sh scripts/lint_sources.sh`: only pre-existing failures: `KAM/Frozen/Planetary/Theorems/AmdConfinement.lean:77` (101 cols)
  and "KAM.lean is out of date" (new modules; I may not edit it). check_lean_modules, frozen guard, ABI hashes PASS.
- `#print axioms KAM.Planetary.exported_sums` and `param_lip_sum`: [propext, Classical.choice, Quot.sound].
- No new public name collides with existing KAM declarations (grep of all new names); lines ≤ 100.

## Deviation / suspected defect in the design signature file (needs orchestrator action)
`exported_sums` last conjunct in P11BSignatures.lean:
`∀ ν, (∑' j, selectionA a (j + ν) + selectionAlpha a (j + ν)) / selectiont a (ν + 1) ≤ …`
parses as `((∑' j, A(j+ν)) + α(j+ν)) / …` (tsum body is at precedence 67, `+` is not included), so `j` is unbound
in the second summand: it only elaborates when autoImplicit is on (it silently adds an implicit `{j : ℕ}`) and FAILS with
the project's `autoImplicit false`. I stated the literal source E3 conclusion instead, with the body parenthesised:
`(∑' j, (selectionA a (j + ν) + selectionAlpha a (j + ν))) / selectiont a (ν + 1) ≤ (2:ℝ)⁻¹ ^ 10`
(stronger than the auto-bound reading). Consumers (B14, B17, B18 etc.) must use this parenthesised form; the signature
file/design should be corrected. All other statements are verbatim.

## Notes
- No heartbeat overrides, no sorry/axiom. One whole-sum step (`sum_add_tsum_nat_add'` with implicit f) timed out at
  default heartbeats when f was inferred; fixed by extracting `wbud_tsum_shift_le` with explicit arguments (design signal
  only: avoid higher-order unification of tsum shifts).
- No errata in pinned sources found; blueprint (E2) numbers hold with slack (I used Ξ ≥ 2+t₀/σ₀ rather than the source's
  2Ξ, giving ΣMapBudget ≤ 2⁻¹⁴·32/31).

ORCHESTRATOR RULING (OVERNIGHT 19:00): the signature-file precedence defect in exported_sums is resolved in favour of the parenthesised source form; P11BSignatures.lean line 638 now reads (∑' j, (selectionA a (j + ν) + selectionAlpha a (j + ν))) / selectiont a (ν + 1).

AUDIT FOCUS: design docs/tracks/P/design/P11B-LEAN-DESIGN.md row B13 (exported-sums, param-lip-sum, adapted scalar budgets with explicit A/alpha/kappa formulas) and its node table; P11B design audits; signatures /root/code/KAM-inp/.drafts/design/P11BSignatures.lean (as amended). (a) every declaration = signature file EXACTLY (exported_sums against the amended line 638); (b) the slice COMPLETE: every graph node mapped to Budgets established; an UNSIGNED export named after a node states its literal conclusion; signed declarations follow the signature file; (c) proof soundness, no added premises: check the deviation 'Xi >= 2 + t0/sigma0 instead of the source's 2 Xi' still gives the source's bound; (d) hygiene: no EuclideanSpace, no reused public helper short name, no harmful root shadow, lines <= 100. Audit ONLY KAM/Planetary/WeakKAM/Budgets{,Stage}.lean.
