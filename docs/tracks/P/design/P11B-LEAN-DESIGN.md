# P11B Lean design: iteration, selection and the limit family

2026-10-28. Branch `inp-design-p11b`. Planning evidence; no proofs, frozen changes, or closure claims.

## Decisions

1. Follow the current split files `p11a3-iteration-selection.tex` and `p11a4-limit-family.tex`, not a generic invocation of Rus01 or track K’s quadratic iteration. All 119 graph nodes sourced from these files are accounted for below. Read graph source from `/root/code/KAM-inp/docs/graph/P/DEPGRAPH.md`; this worktree has no assembled graph. Graph IDs are preserved.
2. Use the frozen `Phase`, `complexStrip`, `actionNbhd`, `frequencyMap`, `IsDiophantine`, `hamiltonianVectorField`, `realHamiltonian`, and `symplecticForm` directly. Real and complex Pi/Prod norms are the max norms. Euclidean lengths occur only as explicit square-root-of-sum-of-squares functions for the measure-layer tensor bounds. No new norm instances.
3. Run the geometric schedule, with `T_j = T₀ 2^j`, `t_j = t₀ 2^{-((τ+1)j)}`, `ε_j = ε₀ varpi^j`, and `s_j = s₀ q^j`. Keep every branch of `lambdaMax` and the full eight-rate lower-budget theorem. Constants are computed before the perturbation; `selectionFixedKey` explicitly removes beta while fixing only the numerical/geometric data, including actual M₀; h may vary with that key.
4. Establish finite-stage divisors on `K_(ν+1)` before applying the canonical step; never infer them from a limit on `Kinf`. Smooth extensions are constructed from finite prefixes; their measure estimate makes the next retained set nonempty. Infinite iteration extends one existing chain coherently, rather than choosing unrelated finite witnesses.
5. Use the ε-adapted radius `sqrt (2 ε/(N C₁))` for all 11a-4 results and keep `ε₀ = 2 ε`. The fixed initial radius remains available for the 11a-3 selection theorem, including ε=0. No division by a vanishing adapted radius is used.
6. Return construction witnesses in output records. No source-facing theorem takes an iteration, good set, frequency limit, invariant torus, or Lipschitz estimate as a hypothesis. `SelectionExtensionChain` contains exactly the analytic nested-prefix premises of finite-extension. `SelectionFiniteChain` extends it with resonance retention for finite-divisor/finite-measure; its generated `toSelectionExtensionChain` projection supplies finite-extension. Conditional implementation helpers must have separate names.
7. `SelectionEvaluationOutput` extends the entire chain/selection/limit/torus/displacement construction, so all final clauses refer to the same witnesses. The public theorem `evaluation_bilipschitz` constructs that whole record from raw source data. Records are output packaging, never an additional assumption replacing a proof.
8. Design the graph’s `ps-lim` SOURCE_GAP as the new local theorem `continuous_series_on_compact`. Supply reality when consuming the upstream canonical-step real-flow clause. Do not claim an off-section normal form on a common positive action radius.

## Carriers and standing structures

| Object | Exact carrier or declaration | Meaning |
|---|---|---|
| Actions/parameters/frequencies | `SelectionR n := Fin n → ℝ`, `SelectionC n := Fin n → ℂ` | existing Pi norm |
| Real phase | frozen `KAM.Planetary.Phase n` | positions, then actions |
| Complex phase and joint point | `SelectionPhaseC n`; `SelectionPoint n := SelectionPhaseC n × SelectionC n` | ((theta, eta), b), parameter not a dynamical variable |
| Domain | `selectionDomain r s B` | frozen strip, open action ball about zero, parameter collar B |
| Real thickening | `selectionThick K ϑ` | explicit Euclidean closed thickening; NOT the max-norm collar |
| Standing data | `SelectionData n` | exactly sel-data (a)–(d), including C₁≥1 and finite type/top derivatives |
| Perturbation | `SelectionPerturbation d f ε` | holomorphic, periodic, real, pointwise bound only |
| Schedule | `SelectionSchedule n` | scalar data, no claimed inequalities |
| Finite chain | `SelectionChain n`, `SelectionExtensionChain d a c ν`, `SelectionFiniteChain d a c ν` | raw functions; nested analytic prefixes, then retained prefixes |
| Results, in dependency order | `SelectionIteration`, `SelectionOutput`, `SelectionComposition`, `SelectionLimit`, `SelectionTori`, `SelectionDisplacement`, `SelectionLipschitz`, `SelectionEvaluationOutput` | output records, progressively extending the same data |
| Quotient target | `(Fin n → AddCircle (1 : ℝ)) × SelectionR n` | period-one quotient, no manifold layer |

`SelectionData` has no perturbation field. Its `finite_type` expands the amount lower bound as the source’s pointwise existential derivative order; `top_bounds` expands Euclidean operator-tensor bounds by quantifying over Euclidean unit-ball arguments. `selectionM₀` is the supremum of the vector diagonal seminorms, not an independent hypothesis or a matrix maximum. `SelectionPerturbation` is supplied only after the admissible threshold. All definitions have literal bodies in Appendix A; no definition body is `sorry`.

## Every graph node → declaration

All unqualified new names are in `KAM.Planetary`. A step mapped to a parent theorem is a local proof obligation inside that declaration, with the exact source goal at its locator; it is not an additional exported theorem or an assumption. “Consumes” preserves every direct graph dependency (including definition inputs); the upstream-name table below resolves nodes outside this scope. Statement/proof locators are those in the authoritative graph, not inferred line numbers.

| Node | Declaration / local proof block | Statement locator | Proof locator | Consumes (direct graph IDs) |
|---|---|---|---|---|
| `bpP:p11a:sel-data` | `sel_data` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:sel-data@L32-L40` | `-` | bpP:p11a:power-law, bpP:p11a:diophantine-measure, bpP:p11a:index-def, bpP:p11a:domain-def |
| `bpP:p11a:y-log` | `Real.log_le_sub_one_of_pos` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:y-log@L45-L45` | `-` | - |
| `bpP:p11a:y-conv` | `HasCompactSupport.hasFDerivAt_convolution_right` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:y-conv@L46-L46` | `-` | - |
| `bpP:p11a:y-down` | `MeasureTheory.tendsto_measure_iInter_atTop` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:y-down@L47-L47` | `-` | - |
| `bpP:p11a:y-geom` | `hasSum_geometric_of_norm_lt_one` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:y-geom@L48-L48` | `-` | - |
| `bpP:p11a:schedule-consts` | `schedule_consts` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:schedule-consts@L68-L75` | `-` | bpP:p11a:fourier-cutoff, bpP:p11a:sel-data |
| `bpP:p11a:schedule-ratios` | `schedule_ratios` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:schedule-ratios@L77-L82` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:schedule-ratios@L83-L85` | stepP:p11a:sr-exp, bpP:p11a:schedule-consts |
| `stepP:p11a:sr-exp` | `schedule_ratios (local `sr_exp`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sr-exp@L84-L84` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sr-exp@L84-L84` | bpP:p11a:schedule-consts, bpP:p11a:sel-data |
| `bpP:p11a:schedule` | `schedule` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:schedule@L90-L97` | `-` | bpP:p11a:schedule-consts, bpP:p11a:sel-data, bpP:p11a:fourier-cutoff, bpP:p11a:loss-choice |
| `bpP:p11a:strip-budget` | `strip_budget` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:strip-budget@L99-L104` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:strip-budget@L105-L113` | stepP:p11a:sb-sum, stepP:p11a:sb-solve, stepP:p11a:sb-strip, stepP:p11a:sb-err, bpP:p11a:schedule, bpP:p11a:schedule-consts, bpP:p11a:sel-data |
| `stepP:p11a:sb-sum` | `strip_budget (local `sb_sum`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sb-sum@L106-L106` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sb-sum@L106-L106` | bpP:p11a:loss-sum, bpP:p11a:schedule, bpP:p11a:schedule-consts |
| `stepP:p11a:sb-solve` | `strip_budget (local `sb_solve`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sb-solve@L108-L108` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sb-solve@L108-L108` | bpP:p11a:y-log, stepP:p11a:sb-sum, bpP:p11a:sel-data, bpP:p11a:schedule-consts |
| `stepP:p11a:sb-strip` | `strip_budget (local `sb_strip`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sb-strip@L110-L110` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sb-strip@L110-L110` | bpP:p11a:schedule, stepP:p11a:sb-solve, bpP:p11a:y-geom |
| `stepP:p11a:sb-err` | `strip_budget (local `sb_err`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sb-err@L112-L112` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sb-err@L112-L112` | bpP:p11a:loss-choice, stepP:p11a:sb-solve, bpP:p11a:schedule, bpP:p11a:schedule-consts |
| `bpP:p11a:schedule-props` | `schedule_props` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:schedule-props@L115-L125` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:schedule-props@L126-L136` | stepP:p11a:sp-1, stepP:p11a:sp-2, stepP:p11a:sp-3, stepP:p11a:sp-4, stepP:p11a:sp-5, bpP:p11a:schedule, bpP:p11a:sel-data, bpP:p11a:schedule-consts |
| `stepP:p11a:sp-1` | `schedule_props (local `sp_1`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sp-1@L127-L127` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sp-1@L127-L127` | bpP:p11a:schedule, bpP:p11a:sel-data, bpP:p11a:schedule-consts |
| `stepP:p11a:sp-2` | `schedule_props (local `sp_2`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sp-2@L129-L129` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sp-2@L129-L129` | bpP:p11a:schedule-ratios, bpP:p11a:y-geom, bpP:p11a:schedule, stepP:p11a:sp-1 |
| `stepP:p11a:sp-3` | `schedule_props (local `sp_3`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sp-3@L131-L131` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sp-3@L131-L131` | bpP:p11a:schedule-ratios, bpP:p11a:schedule-consts, stepP:p11a:sp-1, bpP:p11a:y-geom, bpP:p11a:schedule |
| `stepP:p11a:sp-4` | `schedule_props (local `sp_4`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sp-4@L133-L133` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sp-4@L133-L133` | bpP:p11a:schedule, bpP:p11a:schedule-consts |
| `stepP:p11a:sp-5` | `schedule_props (local `sp_5`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sp-5@L135-L135` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sp-5@L135-L135` | stepP:p11a:sp-1, bpP:p11a:schedule |
| `bpP:p11a:smooth-cutoff` | `smooth_cutoff` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:smooth-cutoff@L143-L149` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:smooth-cutoff@L150-L154` | stepP:p11a:sc-constr, stepP:p11a:sc-deriv, bpP:p11a:sel-data |
| `stepP:p11a:sc-constr` | `smooth_cutoff (local `sc_constr`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sc-constr@L151-L151` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sc-constr@L151-L151` | - |
| `stepP:p11a:sc-deriv` | `smooth_cutoff (local `sc_deriv`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sc-deriv@L153-L153` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:sc-deriv@L153-L153` | bpP:p11a:y-conv, stepP:p11a:sc-constr |
| `bpP:p11a:finite-extension` | `finite_extension` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:finite-extension@L156-L165` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:finite-extension@L166-L174` | stepP:p11a:fe-supp, stepP:p11a:fe-reg, stepP:p11a:fe-cauchy, stepP:p11a:fe-leib, bpP:p11a:sel-data, bpP:p11a:schedule, bpP:p11a:smooth-cutoff |
| `stepP:p11a:fe-supp` | `finite_extension (local `fe_supp`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fe-supp@L167-L167` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fe-supp@L167-L167` | bpP:p11a:smooth-cutoff, bpP:p11a:sel-data, bpP:p11a:schedule |
| `stepP:p11a:fe-reg` | `finite_extension (local `fe_reg`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fe-reg@L169-L169` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fe-reg@L169-L169` | bpP:p11a:smooth-cutoff, stepP:p11a:fe-supp, bpP:p11a:sel-data |
| `stepP:p11a:fe-cauchy` | `finite_extension (local `fe_cauchy`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fe-cauchy@L171-L171` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fe-cauchy@L171-L171` | bpP:p11a:param-cauchy, bpP:p11a:schedule |
| `stepP:p11a:fe-leib` | `finite_extension (local `fe_leib`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fe-leib@L173-L173` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fe-leib@L173-L173` | bpP:p11a:smooth-cutoff, stepP:p11a:fe-cauchy, bpP:p11a:schedule |
| `bpP:p11a:initial` | `initial` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:initial@L183-L190` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:initial@L191-L195` | stepP:p11a:in-dom, stepP:p11a:in-taylor, bpP:p11a:sel-data, bpP:p11a:domain-def |
| `stepP:p11a:in-dom` | `initial (local `in_dom`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:in-dom@L192-L192` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:in-dom@L192-L192` | bpP:p11a:sel-data |
| `stepP:p11a:in-taylor` | `initial (local `in_taylor`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:in-taylor@L194-L194` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:in-taylor@L194-L194` | bpP:p11a:sel-data, stepP:p11a:in-dom |
| `bpP:p11a:adm-params` | `adm_params` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:adm-params@L197-L204` | `-` | bpP:p11a:sel-data, bpP:p11a:schedule-consts, bpP:p11a:smooth-cutoff, bpP:p11a:initial |
| `bpP:p11a:adm-choice` | `adm_choice` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:adm-choice@L206-L218` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:adm-choice@L219-L223` | stepP:p11a:ac-lam, stepP:p11a:ac-list, bpP:p11a:schedule, bpP:p11a:adm-params, bpP:p11a:sel-data, bpP:p11a:schedule-consts, bpP:p11a:smooth-cutoff |
| `stepP:p11a:ac-lam` | `adm_choice (local `ac_lam`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ac-lam@L220-L220` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ac-lam@L220-L220` | bpP:p11a:adm-params |
| `stepP:p11a:ac-list` | `adm_choice (local `ac_list`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ac-list@L222-L222` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ac-list@L222-L222` | stepP:p11a:ac-lam, bpP:p11a:adm-params, bpP:p11a:initial, bpP:p11a:sel-data |
| `bpP:p11a:sec-retained#data` | `sec_retained_data; SelectionFiniteChain; selectionRetained` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:sec-retained#data@L234-L238` | `-` | bpP:p11a:schedule, bpP:p11a:sel-data |
| `bpP:p11a:finite-divisor` | `finite_divisor` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:finite-divisor@L240-L245` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:finite-divisor@L246-L252` | stepP:p11a:fd-tel, stepP:p11a:fd-test, stepP:p11a:fd-concl, bpP:p11a:sec-retained#data, bpP:p11a:schedule |
| `stepP:p11a:fd-tel` | `finite_divisor (local `fd_tel`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fd-tel@L247-L247` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fd-tel@L247-L247` | bpP:p11a:sec-retained#data, bpP:p11a:schedule |
| `stepP:p11a:fd-test` | `finite_divisor (local `fd_test`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fd-test@L249-L249` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fd-test@L249-L249` | bpP:p11a:sec-retained#data |
| `stepP:p11a:fd-concl` | `finite_divisor (local `fd_concl`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fd-concl@L251-L251` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fd-concl@L251-L251` | stepP:p11a:fd-tel, stepP:p11a:fd-test, bpP:p11a:schedule |
| `bpP:p11a:finite-measure` | `finite_measure` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:finite-measure@L258-L265` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:finite-measure@L266-L272` | stepP:p11a:fm-close, stepP:p11a:fm-family, stepP:p11a:fm-incl, bpP:p11a:sel-data, bpP:p11a:sec-retained#data, bpP:p11a:finite-extension, bpP:p11a:schedule |
| `stepP:p11a:fm-close` | `finite_measure (local `fm_close`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fm-close@L267-L267` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fm-close@L267-L267` | bpP:p11a:finite-extension, bpP:p11a:schedule-props, bpP:p11a:adm-params, bpP:p11a:stability, bpP:p11a:diophantine-measure, bpP:p11a:sel-data |
| `stepP:p11a:fm-family` | `finite_measure (local `fm_family`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fm-family@L269-L269` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fm-family@L269-L269` | bpP:p11a:diophantine-measure, bpP:p11a:power-law, stepP:p11a:fm-close, bpP:p11a:stability, bpP:p11a:finite-extension, bpP:p11a:sel-data, bpP:p11a:schedule |
| `stepP:p11a:fm-incl` | `finite_measure (local `fm_incl`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fm-incl@L271-L271` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:fm-incl@L271-L271` | bpP:p11a:finite-extension, bpP:p11a:sec-retained#data, bpP:p11a:schedule |
| `bpP:p11a:inductive-lemma` | `inductive_lemma` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:inductive-lemma@L277-L294` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:inductive-lemma@L295-L312` | stepP:p11a:il-p0, stepP:p11a:il-ret, stepP:p11a:il-c2, stepP:p11a:il-c1, stepP:p11a:il-c3, stepP:p11a:il-rem, stepP:p11a:il-inc, stepP:p11a:il-dom, stepP:p11a:il-map, bpP:p11a:sel-data, bpP:p11a:schedule, bpP:p11a:adm-params, bpP:p11a:initial, bpP:p11a:sec-retained#data, bpP:p11a:canonical-step, bpP:p11a:domain-def |
| `stepP:p11a:il-p0` | `inductive_lemma (local `il_p0`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-p0@L296-L296` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-p0@L296-L296` | bpP:p11a:initial, bpP:p11a:adm-choice, bpP:p11a:sel-data, bpP:p11a:schedule |
| `stepP:p11a:il-ret` | `inductive_lemma (local `il_ret`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-ret@L298-L298` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-ret@L298-L298` | bpP:p11a:schedule-props, bpP:p11a:adm-choice, bpP:p11a:finite-measure, bpP:p11a:finite-divisor, bpP:p11a:sec-retained#data |
| `stepP:p11a:il-c2` | `inductive_lemma (local `il_c2`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-c2@L300-L300` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-c2@L300-L300` | bpP:p11a:canonical-step, bpP:p11a:cutoff, bpP:p11a:schedule-props, stepP:p11a:il-ret, bpP:p11a:schedule, bpP:p11a:sel-data, bpP:p11a:sec-retained#data |
| `stepP:p11a:il-c1` | `inductive_lemma (local `il_c1`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-c1@L302-L302` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-c1@L302-L302` | bpP:p11a:strip-budget, bpP:p11a:schedule-ratios, bpP:p11a:schedule, bpP:p11a:schedule-consts, bpP:p11a:sel-data |
| `stepP:p11a:il-c3` | `inductive_lemma (local `il_c3`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-c3@L304-L304` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-c3@L304-L304` | bpP:p11a:schedule-props, bpP:p11a:adm-choice, bpP:p11a:schedule-ratios, bpP:p11a:canonical-step, K:bp:p1:exp-sums, bpP:p11a:schedule, bpP:p11a:schedule-consts, stepP:p11a:il-c1 |
| `stepP:p11a:il-rem` | `inductive_lemma (local `il_rem`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-rem@L306-L306` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-rem@L306-L306` | bpP:p11a:canonical-step, bpP:p11a:schedule-ratios, stepP:p11a:il-c3, bpP:p11a:strip-budget, bpP:p11a:schedule |
| `stepP:p11a:il-inc` | `inductive_lemma (local `il_inc`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-inc@L308-L308` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-inc@L308-L308` | bpP:p11a:cutoff, stepP:p11a:cu-coeff, bpP:p11a:canonical-step, K:bp:p1:decay, bpP:p11a:strip-budget, bpP:p11a:schedule |
| `stepP:p11a:il-dom` | `inductive_lemma (local `il_dom`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-dom@L310-L310` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-dom@L310-L310` | bpP:p11a:param-cauchy, bpP:p11a:schedule-props, stepP:p11a:il-inc, bpP:p11a:sel-data, bpP:p11a:schedule, bpP:p11a:sec-retained#data |
| `stepP:p11a:il-map` | `inductive_lemma (local `il_map`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-map@L312-L312` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:il-map@L312-L312` | bpP:p11a:canonical-step, bpP:p11a:affine-flow, stepP:p11a:il-c3, bpP:p11a:schedule |
| `bpP:p11a:parameter-selection` | `parameter_selection` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:parameter-selection@L317-L326` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:parameter-selection@L327-L335` | stepP:p11a:ps-iter, stepP:p11a:ps-lim, stepP:p11a:ps-H, stepP:p11a:ps-dio, bpP:p11a:sel-data, bpP:p11a:adm-params, bpP:p11a:inductive-lemma, bpP:p11a:schedule, bpP:p11a:finite-measure, bpP:p0:diophantine#IsDiophantine |
| `stepP:p11a:ps-iter` | `parameter_selection (local `ps_iter`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ps-iter@L328-L328` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ps-iter@L328-L328` | bpP:p11a:inductive-lemma |
| `stepP:p11a:ps-lim` | `parameter_selection (local `ps_lim`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ps-lim@L330-L330` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ps-lim@L330-L330` | bpP:p11a:schedule-props, bpP:p11a:inductive-lemma, stepP:p11a:ps-iter, bpP:p11a:y-geom, bpP:p11a:schedule |
| `stepP:p11a:ps-H` | `parameter_selection (local `ps_H`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ps-H@L332-L332` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ps-H@L332-L332` | bpP:p11a:finite-measure, bpP:p11a:y-down, bpP:p11a:finite-extension |
| `stepP:p11a:ps-dio` | `parameter_selection (local `ps_dio`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ps-dio@L334-L334` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ps-dio@L334-L334` | bpP:p11a:limit-bridge, stepP:p11a:ps-lim, stepP:p11a:ps-H, bpP:p11a:finite-extension, bpP:p11a:schedule-props, bpP:p11a:schedule |
| `bpP:p11a:exported-sums` | `exported_sums` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:exported-sums@L340-L349` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:exported-sums@L350-L358` | stepP:p11a:es-1, stepP:p11a:es-2, stepP:p11a:es-3, stepP:p11a:es-4, bpP:p11a:parameter-selection, bpP:p11a:adm-choice, bpP:p11a:schedule-props, bpP:p11a:inductive-lemma, bpP:p11a:schedule, bpP:p11a:schedule-consts |
| `stepP:p11a:es-1` | `exported_sums (local `es_1`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:es-1@L351-L351` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:es-1@L351-L351` | bpP:p11a:inductive-lemma, bpP:p11a:strip-budget, stepP:p11a:il-c3, bpP:p11a:schedule-consts, bpP:p11a:schedule-ratios, bpP:p11a:schedule |
| `stepP:p11a:es-2` | `exported_sums (local `es_2`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:es-2@L353-L353` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:es-2@L353-L353` | stepP:p11a:es-1, bpP:p11a:adm-choice, bpP:p11a:adm-params, bpP:p11a:schedule-ratios, bpP:p11a:schedule-consts, bpP:p11a:schedule, bpP:p11a:y-geom |
| `stepP:p11a:es-3` | `exported_sums (local `es_3`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:es-3@L355-L355` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:es-3@L355-L355` | stepP:p11a:es-1, stepP:p11a:es-2, bpP:p11a:adm-choice, bpP:p11a:adm-params, bpP:p11a:schedule-props, bpP:p11a:schedule-ratios, bpP:p11a:schedule, bpP:p11a:y-geom |
| `stepP:p11a:es-4` | `exported_sums (local `es_4`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:es-4@L357-L357` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:es-4@L357-L357` | bpP:p11a:canonical-step, bpP:p11a:schedule, bpP:p11a:inductive-lemma |
| `bpP:p11a:adm-budget` | `adm_budget` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:adm-budget@L374-L383` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:adm-budget@L384-L396` | stepP:p11a:ab-gamma, stepP:p11a:ab-T0, stepP:p11a:ab-t0, stepP:p11a:ab-lam, stepP:p11a:ab-concl, bpP:p11a:power-law, bpP:p11a:sel-data, bpP:p11a:adm-params |
| `stepP:p11a:ab-gamma` | `adm_budget (local `ab_gamma`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ab-gamma@L387-L387` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ab-gamma@L387-L387` | bpP:p11a:power-law, bpP:p11a:sublevel, bpP:p11a:sel-data |
| `stepP:p11a:ab-T0` | `adm_budget (local `ab_T0`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ab-T0@L389-L389` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ab-T0@L389-L389` | bpP:p11a:adm-params, bpP:p11a:schedule-consts, stepP:p11a:ab-gamma |
| `stepP:p11a:ab-t0` | `adm_budget (local `ab_t0`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ab-t0@L391-L391` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ab-t0@L391-L391` | bpP:p11a:adm-params, stepP:p11a:ab-T0, bpP:p11a:sel-data |
| `stepP:p11a:ab-lam` | `adm_budget (local `ab_lam`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ab-lam@L393-L393` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ab-lam@L393-L393` | bpP:p11a:adm-params, stepP:p11a:ab-gamma, stepP:p11a:ab-T0, stepP:p11a:ab-t0, bpP:p11a:schedule-consts, bpP:p11a:smooth-cutoff, bpP:p11a:sel-data |
| `stepP:p11a:ab-concl` | `adm_budget (local `ab_concl`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ab-concl@L395-L395` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ab-concl@L395-L395` | bpP:p11a:adm-params, stepP:p11a:ab-lam |
| `bpP:p11a:adm-budget-beta` | `adm_budget_beta` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:adm-budget-beta@L402-L407` | `blueprint-P/parts/p11a3-iteration-selection.tex#bpP:p11a:adm-budget-beta@L408-L410` | stepP:p11a:abb-spec, bpP:p11a:sel-data, bpP:p11a:adm-params |
| `stepP:p11a:abb-spec` | `adm_budget_beta (local `abb_spec`)` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:abb-spec@L409-L409` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:abb-spec@L409-L409` | bpP:p11a:adm-budget, bpP:p11a:sel-data |
| `bpP:p11a:situation` | `situation` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:situation@L30-L32` | `-` | bpP:p11a:sel-data, bpP:p11a:schedule, bpP:p11a:adm-params, bpP:p11a:free-radius, bpP:p11a:inductive-lemma, bpP:p11a:parameter-selection, bpP:p11a:domain-def |
| `bpP:p11a:z-chain` | `HasFDerivAt.comp; Real.add_one_le_exp; local exponential estimate` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:z-chain@L54-L54` | `-` | - |
| `bpP:p11a:z-compact` | `IsCompact.image; IsSigmaCompact.image_of_continuousOn; MeasurableSet.iUnion; IsClosed.measurableSet` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:z-compact@L55-L55` | `-` | - |
| `bpP:p11a:z-uniform` | `Metric.uniformCauchySeqOn_iff; Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:z-uniform@L56-L56` | `-` | - |
| `bpP:p11a:free-radius` | `free_radius` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:free-radius@L35-L40` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:free-radius@L41-L47` | stepP:p11a:fr-small, stepP:p11a:fr-list, stepP:p11a:fr-other, bpP:p11a:sel-data, bpP:p11a:adm-params, bpP:p11a:adm-choice, bpP:p11a:schedule-props, bpP:p11a:inductive-lemma, bpP:p11a:parameter-selection, bpP:p11a:exported-sums |
| `stepP:p11a:fr-small` | `free_radius (local `fr_small`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:fr-small@L42-L42` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:fr-small@L42-L42` | bpP:p11a:adm-params, bpP:p11a:sel-data |
| `stepP:p11a:fr-list` | `free_radius (local `fr_list`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:fr-list@L44-L44` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:fr-list@L44-L44` | bpP:p11a:adm-choice, stepP:p11a:ac-lam, stepP:p11a:ac-list, bpP:p11a:initial, stepP:p11a:fr-small, bpP:p11a:sel-data, bpP:p11a:adm-params |
| `stepP:p11a:fr-other` | `free_radius (local `fr_other`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:fr-other@L46-L46` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:fr-other@L46-L46` | bpP:p11a:initial, stepP:p11a:fr-list, bpP:p11a:finite-divisor, bpP:p11a:finite-measure, bpP:p11a:adm-choice, bpP:p11a:schedule, bpP:p11a:exported-sums, bpP:p11a:finite-extension, bpP:p11a:sel-data, bpP:p11a:adm-params, bpP:p11a:schedule-props |
| `bpP:p11a:composition` | `composition` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:composition@L66-L75` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:composition@L76-L84` | stepP:p11a:co-dom, stepP:p11a:co-deriv, stepP:p11a:co-disp, stepP:p11a:co-inc, bpP:p11a:situation, bpP:p11a:sec-comp#data |
| `stepP:p11a:co-dom` | `composition (local `co_dom`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:co-dom@L77-L77` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:co-dom@L77-L77` | bpP:p11a:inductive-lemma, bpP:p11a:situation, bpP:p11a:sec-comp#data, bpP:p11a:z-chain, bpP:p11a:schedule |
| `stepP:p11a:co-deriv` | `composition (local `co_deriv`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:co-deriv@L79-L79` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:co-deriv@L79-L79` | bpP:p11a:inductive-lemma, bpP:p11a:canonical-step, bpP:p11a:exported-sums, bpP:p11a:z-chain, stepP:p11a:co-dom, bpP:p11a:situation, bpP:p11a:sec-comp#data |
| `stepP:p11a:co-disp` | `composition (local `co_disp`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:co-disp@L81-L81` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:co-disp@L81-L81` | bpP:p11a:inductive-lemma, stepP:p11a:co-dom, bpP:p11a:situation, bpP:p11a:sec-comp#data |
| `stepP:p11a:co-inc` | `composition (local `co_inc`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:co-inc@L83-L83` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:co-inc@L83-L83` | K:bp:p1:ext-mvt, stepP:p11a:co-deriv, stepP:p11a:co-dom, bpP:p11a:inductive-lemma, bpP:p11a:situation, bpP:p11a:sec-comp#data |
| `bpP:p11a:param-lip-sum` | `param_lip_sum` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:param-lip-sum@L86-L88` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:param-lip-sum@L89-L95` | stepP:p11a:pl4-terms, stepP:p11a:pl4-sum, bpP:p11a:situation |
| `stepP:p11a:pl4-terms` | `param_lip_sum (local `pl4_terms`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:pl4-terms@L90-L92` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:pl4-terms@L90-L92` | bpP:p11a:exported-sums, bpP:p11a:schedule-consts, bpP:p11a:schedule, bpP:p11a:situation |
| `stepP:p11a:pl4-sum` | `param_lip_sum (local `pl4_sum`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:pl4-sum@L94-L94` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:pl4-sum@L94-L94` | stepP:p11a:pl4-terms, bpP:p11a:schedule-ratios, bpP:p11a:adm-choice, bpP:p11a:adm-params, bpP:p11a:schedule-consts, bpP:p11a:situation |
| `bpP:p11a:limit-map` | `limit_map` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:limit-map@L100-L108` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:limit-map@L109-L117` | stepP:p11a:lm-inc, stepP:p11a:lm-der, stepP:p11a:lm-hol, stepP:p11a:lm-bounds, bpP:p11a:situation, bpP:p11a:composition, bpP:p11a:sec-comp#data |
| `stepP:p11a:lm-inc` | `limit_map (local `lm_inc`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lm-inc@L110-L110` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lm-inc@L110-L110` | bpP:p11a:strip-budget, bpP:p11a:composition, bpP:p11a:exported-sums, bpP:p11a:z-uniform, bpP:p11a:situation, bpP:p11a:sec-comp#data |
| `stepP:p11a:lm-der` | `limit_map (local `lm_der`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lm-der@L112-L112` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lm-der@L112-L112` | K:bp:p1:ext-cauchy, stepP:p11a:lm-inc, bpP:p11a:composition, bpP:p11a:strip-budget, bpP:p11a:exported-sums, bpP:p11a:situation, bpP:p11a:sec-comp#data |
| `stepP:p11a:lm-hol` | `limit_map (local `lm_hol`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lm-hol@L114-L114` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lm-hol@L114-L114` | K:bp:p1:uniform-limits, stepP:p11a:lm-inc, stepP:p11a:lm-der, bpP:p11a:situation, bpP:p11a:sec-comp#data |
| `stepP:p11a:lm-bounds` | `limit_map (local `lm_bounds`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lm-bounds@L116-L116` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lm-bounds@L116-L116` | bpP:p11a:composition, stepP:p11a:lm-hol, bpP:p11a:z-uniform, bpP:p11a:situation, bpP:p11a:sec-comp#data |
| `bpP:p11a:sec-limit#data` | `sec_limit_data; selectionEvaluation` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:sec-limit#data@L119-L121` | `-` | bpP:p11a:situation, bpP:p11a:limit-map, bpP:p11a:initial |
| `bpP:p11a:limit-torus` | `limit_torus` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:limit-torus@L123-L133` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:limit-torus@L134-L148` | stepP:p11a:lt-field, stepP:p11a:lt-cov, stepP:p11a:lt-lim, stepP:p11a:lt-lag, stepP:p11a:lt-emb, stepP:p11a:lt-dio, bpP:p11a:situation, bpP:p11a:sec-limit#data, bpP:p11a:parameter-selection, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p0:hamsymp#symplecticForm |
| `stepP:p11a:lt-field` | `limit_torus (local `lt_field`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lt-field@L135-L135` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lt-field@L135-L135` | bpP:p11a:inductive-lemma, K:bp:p1:ext-cauchy, bpP:p11a:strip-budget, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p11a:schedule, bpP:p11a:situation |
| `stepP:p11a:lt-cov` | `limit_torus (local `lt_cov`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lt-cov@L137-L139` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lt-cov@L137-L139` | bpP:p11a:composition, bpP:p11a:initial, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p11a:situation, bpP:p11a:sec-comp#data, bpP:p11a:z-chain |
| `stepP:p11a:lt-lim` | `limit_torus (local `lt_lim`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lt-lim@L141-L141` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lt-lim@L141-L141` | bpP:p11a:limit-map, stepP:p11a:lt-field, stepP:p11a:lt-cov, bpP:p11a:parameter-selection, bpP:p11a:exported-sums, bpP:p11a:adm-choice, bpP:p11a:composition, bpP:p11a:initial, bpP:p11a:situation, bpP:p11a:sec-comp#data, bpP:p11a:sec-limit#data |
| `stepP:p11a:lt-lag` | `limit_torus (local `lt_lag`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lt-lag@L143-L143` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lt-lag@L143-L143` | bpP:p11a:composition, bpP:p11a:limit-map, bpP:p0:hamsymp#symplecticForm, bpP:p11a:situation, bpP:p11a:sec-comp#data, bpP:p11a:sec-limit#data |
| `stepP:p11a:lt-emb` | `limit_torus (local `lt_emb`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lt-emb@L145-L145` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lt-emb@L145-L145` | bpP:p11a:limit-map, bpP:p11a:sec-limit#data, bpP:p11a:situation |
| `stepP:p11a:lt-dio` | `limit_torus (local `lt_dio`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lt-dio@L147-L147` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lt-dio@L147-L147` | bpP:p11a:parameter-selection, bpP:p11a:situation |
| `bpP:p11a:displacement` | `displacement` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:displacement@L157-L164` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:displacement@L165-L169` | stepP:p11a:dp-tel, stepP:p11a:dp-size, bpP:p11a:situation, bpP:p11a:sec-limit#data, bpP:p11a:adm-params, bpP:p11a:schedule-consts |
| `stepP:p11a:dp-tel` | `displacement (local `dp_tel`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:dp-tel@L166-L166` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:dp-tel@L166-L166` | bpP:p11a:limit-map, bpP:p11a:exported-sums, bpP:p11a:situation, bpP:p11a:sec-limit#data |
| `stepP:p11a:dp-size` | `displacement (local `dp_size`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:dp-size@L168-L168` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:dp-size@L168-L168` | bpP:p11a:adm-choice, bpP:p11a:free-radius, bpP:p11a:schedule-props, bpP:p11a:schedule-consts, bpP:p11a:adm-params, stepP:p11a:dp-tel, bpP:p11a:situation |
| `bpP:p11a:gamma-inverse` | `gamma_inverse` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:gamma-inverse@L171-L175` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:gamma-inverse@L176-L178` | stepP:p11a:gi-branches, bpP:p11a:sel-data, bpP:p11a:power-law |
| `stepP:p11a:gi-branches` | `gamma_inverse (local `gi_branches`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:gi-branches@L177-L177` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:gi-branches@L177-L177` | bpP:p11a:power-law, bpP:p11a:sublevel, bpP:p11a:sel-data |
| `bpP:p11a:displacement-power` | `displacement_power` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:displacement-power@L180-L184` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:displacement-power@L185-L187` | stepP:p11a:dpc-comb, bpP:p11a:sel-data, bpP:p11a:situation, bpP:p11a:displacement, bpP:p11a:gamma-inverse, bpP:p11a:sec-limit#data, bpP:p11a:adm-budget-beta |
| `stepP:p11a:dpc-comb` | `displacement_power (local `dpc_comb`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:dpc-comb@L186-L186` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:dpc-comb@L186-L186` | bpP:p11a:displacement, bpP:p11a:gamma-inverse, bpP:p11a:situation |
| `bpP:p11a:lipschitz-family` | `lipschitz_family` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:lipschitz-family@L192-L197` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:lipschitz-family@L198-L206` | stepP:p11a:lf-split, stepP:p11a:lf-tel, stepP:p11a:lf-stage, stepP:p11a:lf-sum, bpP:p11a:situation, bpP:p11a:sec-limit#data |
| `stepP:p11a:lf-split` | `lipschitz_family (local `lf_split`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lf-split@L199-L199` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lf-split@L199-L199` | bpP:p11a:limit-map, bpP:p11a:situation, bpP:p11a:sec-limit#data |
| `stepP:p11a:lf-tel` | `lipschitz_family (local `lf_tel`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lf-tel@L201-L201` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lf-tel@L201-L201` | bpP:p11a:limit-map, bpP:p11a:composition, bpP:p11a:situation, bpP:p11a:sec-comp#data, bpP:p11a:sec-limit#data |
| `stepP:p11a:lf-stage` | `lipschitz_family (local `lf_stage`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lf-stage@L203-L203` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lf-stage@L203-L203` | K:bp:p1:ext-cauchy, stepP:p11a:lf-tel, bpP:p11a:schedule, bpP:p11a:situation, K:bp:p1:ext-mvt |
| `stepP:p11a:lf-sum` | `lipschitz_family (local `lf_sum`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lf-sum@L205-L205` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:lf-sum@L205-L205` | bpP:p11a:param-lip-sum, stepP:p11a:lf-stage, stepP:p11a:lf-tel, stepP:p11a:lf-split, bpP:p11a:situation, bpP:p11a:sec-limit#data |
| `bpP:p11a:evaluation-bilipschitz` | `evaluation_bilipschitz` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:evaluation-bilipschitz@L212-L223` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:evaluation-bilipschitz@L224-L232` | stepP:p11a:eb-bounds, stepP:p11a:eb-ext, stepP:p11a:eb-meas, stepP:p11a:eb-cpt, bpP:p11a:situation, bpP:p11a:sec-limit#data |
| `stepP:p11a:eb-bounds` | `evaluation_bilipschitz (local `eb_bounds`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:eb-bounds@L225-L225` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:eb-bounds@L225-L225` | bpP:p11a:lipschitz-family, bpP:p11a:sec-limit#data, bpP:p11a:situation |
| `stepP:p11a:eb-ext` | `evaluation_bilipschitz (local `eb_ext`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:eb-ext@L227-L227` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:eb-ext@L227-L227` | bpP:p11a:limit-torus, K:bp:p1:mcshane, K:bp:p1:lipeo, stepP:p11a:eb-bounds, bpP:p11a:situation, bpP:p11a:sec-limit#data, bpP:p11a:lipschitz-family |
| `stepP:p11a:eb-meas` | `evaluation_bilipschitz (local `eb_meas`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:eb-meas@L229-L229` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:eb-meas@L229-L229` | K:bp:p1:ext-measure, K:bp:p1:lip-image, bpP:p11a:z-compact, stepP:p11a:eb-bounds, bpP:p11a:situation, bpP:p11a:sec-limit#data |
| `stepP:p11a:eb-cpt` | `evaluation_bilipschitz (local `eb_cpt`)` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:eb-cpt@L231-L231` | `blueprint-P/parts/p11a4-limit-family.tex#stepP:p11a:eb-cpt@L231-L231` | bpP:p11a:z-compact, stepP:p11a:eb-ext, stepP:p11a:eb-bounds, bpP:p11a:situation, bpP:p11a:sec-limit#data |
| `bpP:p11a:sec-comp#data` | `sec_comp_data; selectionCompose` | `blueprint-P/parts/p11a4-limit-family.tex#bpP:p11a:sec-comp#data@L64-L64` | `-` | bpP:p11a:situation |

`geom_recursion` is an extra source-labelled helper (11a-3 L58–65); it has no record in the current graph slice. It is included because the text explicitly states it. The induction actually needs only the prescribed Q_j bound plus the direct remainder inequality; no artificial dependency on geometric recursion is inserted.

## Conventions and exact assembly

- Angles have period 1; Fourier modes are `Fin n → ℤ`, with l1 length `selectionModeLength`. The divisor is `γ / |k|₁^τ`, exactly the frozen Diophantine predicate. Complex frequencies are restricted to real parts only after proving reality.
- `fderiv ℂ` differentiates jointly when its argument is a joint point; phase derivatives fix b, and parameter derivatives fix phase. Source real tensor bounds use `iteratedFDeriv ℝ`; no complex derivative is silently treated as a real derivative.
- Norm bounds are pointwise, avoiding a spurious `sSup` bound for an empty domain. The only suprema are the explicit source compact-sphere/multiindex constants. Positivity, finiteness and compactness proofs are required before using their order laws.
- All source powers are `Real.rpow` when the exponent is real and ordinary powers for natural indices. Negative powers have positive bases at every use. Integer stage cutoffs stay real: there is no rounded cutoff schedule.
- The defect is evaluated as `selectionEvaluation u b theta = (theta,b)+u b theta`. Measure uses the phase order `(theta,b)`. Do not apply a factor for the harmless block swap; it is an isometry and preserves product volume.
- `SelectionIteration.normal_form` is a finite-stage identity on a shrinking domain. Invariance uses only the first action jet at zero. The bound `ε_j/s_j² = (ε₀/s₀²)16^j` is not a convergent error estimate.
- `selectionQuotient` is only used for compactness of the quotient image; actual invariance and orbit equations are statements on the real covering space.

## Reuse map and upstream interface (to reconcile)

Existing delivered APIs are used by their exact names. The unimplemented neighbouring P11A graph nodes below are interface requirements, not assumed black-box statements. No provisional full theorem type for them is inserted into the signatures.

| Node / input | Exact upstream export or owner | Shape supplied here and conclusion consumed |
|---|---|---|
| p11a:index-def, diophantine-measure data | P11A: `index_def`, `diophantine_measure` | same real Pi carriers; source rho=1/2 scalar family, explicit Euclidean tensor bounds; D1/D2 supplied by `SelectionData`, D3 by the finite extension and stability |
| p11a:stability | P11A: `stability` | μ derivatives, original M₀, diagonal closeness ≤ thetaMax; consume error ≤ beta/2 |
| p11a:power-law | P11A: `power_law` | common finite-type source, family of C^μ perturbations indexed by all nonzero modes, margin 2γ; consume compact retained set and measure loss ≤ loss |
| p11a:sublevel | P11A: `sublevel` | consume the explicit C_Dio dependence for gamma-inverse and budget, not a generic unspecified constant |
| p11a:fourier-cutoff, loss-choice, loss-sum | P11A: `fourier_cutoff`, `loss_choice`, `loss_sum` | T≥1, alpha=varpi/8, d_T≤1; consume cutoff error and geometric strip-loss sum |
| p11a:domain-def | P11A: `domain_def` | three factors ((theta,eta),b); `selectionDomain` spells out the required carrier using frozen strip/collar, to become the same object when reconciled |
| p11a:cutoff / cu-coeff | P11A: `cutoff`, local `cu_coeff` | use the WHOLE B_ν collar to obtain holomorphic zero Fourier/Taylor coefficients; never restrict these increments first to B_(ν+1) |
| p11a:canonical-step | P11A: `canonical_step`, `canonical_step_real`, `real_lipschitz` | phase radius/strip/losses, finite retained E, collar t_(ν+1), L=2C₁, divisor D_ν, positive ε_ν, C1–C3 and reality supplied; consume O2–O5 and the unscaled map derivative |
| p11a:affine-flow | P11A: `affine_flow` | simple canonical affine-in-action map, not an arbitrary symplectomorphism; real-flow estimate receives real coefficients |
| p11a:param-cauchy | P11A: `param_cauchy` | whole complex collar, inner collar t/2 or 3t/4; consume j^j A/(t-t')^j |
| p11a:limit-bridge, divisor-wide | P11A: `limit_bridge`, `divisor_wide` | shell margin 2γ and single tail γ; direct finite-divisor does not depend on divisor-wide (avoid the graph cycle) |
| p1:ext-cauchy / ext-mvt | `KAM.increments_open`, `KAM.norm_fderiv_le_of_closedBall_bound`, `KAM.norm_iteratedDeriv_line_le_of_closedBall`; Pi row-sum bounds | convex fibre or a short segment inside a specified collar; no convexity of the retained set |
| p1:uniform-limits | `KAM.uniform_limits` (`KAM/Strip/Limits.lean`) | one fixed open complex strip and uniform derivative limit; used for lm-hol ONLY |
| p1:exp-sums / decay | `KAM.Fourier.exp_sums`, `KAM.decay`, `KAM.decay_boundary_radius`; P11A cutoff coefficients | period-one coefficient factors 2π; use at geometric widths, never treat a coefficient radius as a geometric width |
| p0 frozen dynamics | `KAM.hamiltonianVectorField`, `KAM.hamiltonianVectorFieldℂ`, `KAM.symplecticForm`, `KAM.IsDiophantine`, `KAM.realHamiltonian` | direct uses; complex form is existing `KAM.Canonical.symplFormC` |
| real symplectic covariance | delivered PP1-4 `KAM.Planetary.chart_field`, `chartPullback`, `IsChart` | land/build its own package in shared inp before B16; use factor 1 after real restriction; supplies lt-cov without assuming N small-flow hypotheses for a composed map |
| McShane / lipeomorphism | `KAM.mcshane_prod`, `KAM.lipeo_onto`, `KAM.lipeo_bounds` | max-norm Phase target, lambda=2^-10; consumes unrestricted extension and inverse inequality |
| image volume | `KAM.lip_image_prod` | exponent 2*n and product volume; apply to extension and inverse on the image |
| quotient and lattice | existing `AddCircle`, `KAM.Planetary.fullShift` is RADIAN in P1 | this part uses the literal period-one integer shift; do not reuse `fullShift` without conversion |

Ownership reconciliation is needed before any P11A consumer package is released. Helpers `selectionScalar`, `selectionDG`, `selectionCN`, `selectionCutoffError`, `selectionΛ` are literal scalar formulas for the interface, not a second analytic function representation. Once P11A delivers its definitions, make these aliases or prove formula bridges against those exact definitions; never assume their equality. No Poincare/Kepler reconstruction, ODE continuation, weighted coefficient algebra or quadratic track-K iteration is redeveloped here.

## Departures and blueprint issues

| Item | Design decision and reason |
|---|---|
| D1 coherent induction export | `inductive_lemma` returns a whole infinite coherent iteration, combining the source finite extension proposition with ps-iter. This is a stronger conclusion, not a new premise. Implement the source base/successor construction first; the final record is populated by recursion on those successors. |
| D2 witness packaging | Source theorems in 11a-4 return nested output records from raw data, rather than taking “situation S” as an additional hypothesis. They include the earlier constructed witnesses and their properties. The final evaluation record prevents accidentally combining unrelated choices. |
| D3 finite measure packaging | `finite_measure` constructs the finite cutoff extensions and the prescribed shell-tested H explicitly, rather than supplying a good set as an input. The joint infinite record retains the same cutoff sequence through `extended_formula` and its Hinf formula. Nesting follows by adding tests for that fixed modeStage/extended family. |
| D4 cutoff support | Use the closed support `tsupport` for the source support inclusion. This is at least the stated support control; the convolution vanishes on the complement of the t/2 closed thickening. |
| D5 expanded amount | Supply finite type by the literal pointwise derivative-order condition equivalent to beta_amount≥beta on the compact sphere×K, not by an unproved premise asserting equality of duplicate amount definitions. The upstream bridge belongs to interface reconciliation. |
| D6 quantitative bounds | Keep sum budgets and displacement in explicit pointwise/tsum form. The output records carry the derivative and convergence guarantees, rather than smuggling them into standing data. No source input premise is dropped. |

**GAP-1, graph `stepP:p11a:ps-lim`, p11a3 L330.** Quote: “uniform Weierstrass test” and the citation to “uniform-limits”. The cited `KAM.uniform_limits` requires a fixed open complex domain and uniform convergence of derivatives; continuous restrictions to Kinf do not meet these hypotheses. Add and prove `continuous_series_on_compact` (Appendix A), using summable scalar envelopes, uniform convergence and continuity on a subset. Apply twice, to Δomega and Δh. It does not require an open collar of Kinf, a positive limiting collar, or an interior point. This is local elementary infrastructure, not an added source premise or an imported unapproved black box.

**GAP-2, inherited upstream reality guard, p11a2 L248/L287 and graph cs-lip; current application p11a3 L300–312.** The global review reports that “reality of R is optional” although the real-flow Lipschitz clause needs it. Every remainder in this selection iteration is required to be real at real points (including the initial remainder). Require the upstream real clause to carry its explicit reality guard; supply `remainder_real` at every stage and propagate the real Fourier coefficients/generator. Do not pretend that an arbitrary complex canonical step has a real restriction. This design does not change the upstream statement or any frozen anchor. The inherited nodes `rl-global` (p11a2 L237: “solutions are global”) and `rl-deriv` (L239: “Y(t)=DTheta solves Ydot=Dphi(Theta)Y”) remain P11A obligations too: bounded Lipschitz periodic angle fields need an actual global flow construction and differentiability with respect to initial data. A linear-ODE existence theorem alone does not identify that solution with a nonlinear flow derivative. Supply the real trigonometric-polynomial hypotheses to the P11A real-flow result only after that result has its own independently reviewed proof; `SelectionIteration.real_angle_derivative` is an output obligation, not an axiom discharging those upstream gaps.

**LIMITATION-3, p11a4 L150–153, no-normal-form.** Quote: “ε_ν/s_ν² = (ε₀/s₀²)16^ν → ∞”. No fixed action-neighbourhood normal form or convergence of second action derivatives is exported. The invariant torus uses only ε_ν/s_ν and ε_ν/r_ν → 0 at the zero section, fixed-strip convergence of theta derivatives, and finite-stage symplectic covariance. The limitation is deliberate and matches the source, not a proof-completion claim.

**CORRECTION-4, p11a3 L254–255 and p11a4 L13/L42.** The source itself corrects the old tail endpoint T_(m-1) to T_m, and adapts s₀ for displacement. Preserve these corrections. The original fixed s₀ gives lambda₀≥lambdaMax/2, so it cannot yield a vanishing power-law defect as ε→0. No renamed fixed-radius retry is valid.

No new pinned-paper erratum is asserted. Rus01 provenance and the blueprint’s D-3, D-7, D-9, D-15–D-19 deviations remain as recorded in the split files. The exact formulas here are audited against those split files, not a claim that the original Rus01 theorem specializes directly.

## Modules, import DAG and prover packages

Each row is one prover package and one focused module. All paths have prefix `KAM/Planetary/WeakKAM/` and suffix `.lean`. Line estimates are proof-inclusive; each package is 150–800 lines. Output record definitions are split with their natural stage, not collected in a monolithic result file. Wave numbers include internal prerequisites; P11A and delivered P1 APIs are separately required inputs.

| Package | Exact module suffix | Nodes / contents | Inputs (package IDs or exact upstream APIs) | Wave | Estimated lines |
|---|---|---|---|---|---|
| B01 | `Data` | sel-data, carriers and input restrictions | frozen definitions, Mathlib | 1 | 350 |
| B02 | `Schedule` | schedule-consts, schedule-ratios, schedule, geom-recursion; raw SelectionChain/SelectionExtensionChain/SelectionFiniteChain and shell/retained definitions | B01; P11A fourier_cutoff formula | 2 | 600 |
| B03 | `StripBudget` | strip-budget, schedule-props | B02; loss_choice, loss_sum; Real.log_le_sub_one_of_pos | 3 | 550 |
| B04 | `Cutoff` | smooth-cutoff; exact bump integral constants | B01; HasCompactSupport.hasFDerivAt_convolution_right | 2 | 700 |
| B05 | `Extension` | finite-extension on arbitrary nested analytic prefixes; Leibniz and Euclidean/max norm conversion | B02,B04; param_cauchy | 3 | 650 |
| B06 | `Initial` | initial Taylor remainder, periodicity and reality | B01; one-variable integral Taylor formula | 2 | 300 |
| B07 | `Admissible` | adm-params, adm-choice, free-radius | B02,B04,B06; power_law explicit scalar constants | 3 | 650 |
| B08 | `FiniteDivisor` | finite-divisor and shell-index characterization; raw retained definitions are in B02 | B03,B05; source chain and shell tests | 4 | 350 |
| B09 | `FiniteMeasure` | finite-measure, coherent finite all-mode tests | B05,B07,B08; stability, power_law | 5 | 650 |
| B10 | `Iteration` | inductive-lemma, coherent prefix recursion, O1–O5; parameter_blocks/parameter_first helpers | B03,B06,B07,B08,B09,B13; cutoff, canonical_step, affine_flow | 6 | 800 |
| B11 | `ContinuousSeries` | continuous_series_on_compact (ps-lim gap) | B01; Mathlib uniform limits and summable envelopes | 2 | 200 |
| B12 | `Selection` | parameter-selection and finite-test specifications | B10,B11; limit_bridge, tendsto_measure_iInter_atTop | 7 | 600 |
| B13 | `Budgets` | exported-sums, param-lip-sum, adapted scalar budgets | B03,B07; explicit A/alpha/kappa formulas | 4 | 650 |
| B14 | `Composition` | composition, sec-comp data, derivative product recursion | B10,B12,B13; HasFDerivAt.comp, increments_open | 8 | 550 |
| B15 | `Limit` | limit-map, sec-limit data; fixed-strip derivative convergence | B14; KAM.uniform_limits, strip Cauchy | 9 | 600 |
| B16 | `Tori` | limit-torus: covariance, vanishing field remainder, Lagrangian, embedding | B15; delivered P1 chart_field and real restriction, frozen dynamics | 10 | 750 |
| B17 | `Displacement` | displacement, gamma-inverse, pointwise powers | B07,B13,B15,B16; P11A power_law explicit constants | 11 | 300 |
| B18 | `ParameterLipschitz` | collar_increment_lipschitz, lipschitz-family | B13,B15,B17; directional one-variable Cauchy and short/long split | 12 | 500 |
| B19 | `Evaluation` | evaluation-bilipschitz, half-cell, lattice/quotient compactness | B16,B17,B18; mcshane_prod, lipeo_onto, lip_image_prod | 13 | 650 |
| B20 | `PolynomialBudget` | adm-budget, adm-budget-beta, uniform displacement-power | B07,B17,B19; explicit sublevel/power_law formulas | 14 | 700 |

**Signature amendment B13 (2026-10-28, main-orchestrator ruling, OVERNIGHT 19:00).** In `exported_sums`
(Appendix), the last conjunct had a precedence defect: `(∑' j, selectionA a (j + ν) + selectionAlpha a (j + ν)) /
selectiont a (ν + 1)` parses with the second summand outside the tsum, leaving `j` unbound (it elaborated only with
autoImplicit, which the project disables). The intended source form E3 is `(∑' j, (selectionA a (j + ν) +
selectionAlpha a (j + ν))) / selectiont a (ν + 1)`. The Appendix and `.drafts/design/P11BSignatures.lean` carry the
parenthesised form; consumers B14, B17 and B18 use it.

**Coverage note B07 (2026-10-28, main-orchestrator ruling, OVERNIGHT 18:17).** The B07 audit found two coverage
gaps inherited from the signature. (i) A7 (p11a3:215, obtained from B06 `initial` at :222) was not attached; a
companion that consumes `initial` is added in round B07b. (ii) `fr-other` (p11a4:39,46: the later lemmas hold
verbatim with the adapted radius) refers to B10, B12 and B13 results. It is discharged where those packages
apply them at the adapted radius, so graph node `free-radius`/`fr-other` stays NOT_STARTED until B10/B12/B13 do.

The package DAG has **20 packages across 14 waves**. The nested output records create real type-level imports from Tori to Displacement to ParameterLipschitz; those edges are included even though their scalar estimates can be developed earlier. Raw chain/retained definitions live in Schedule, before Extension, avoiding a definitions cycle. Iteration imports Budgets for the exact map-bound formulas. The “Inputs” column is the import DAG: each Bxx module imports exactly the named earlier Bxx modules plus its listed external APIs and their interface definitions. External inputs do not import any Bxx module. There are no reverse imports from P11A. A small `KAM/Planetary/WeakKAM.lean` facade may publicly import `WeakKAM/Evaluation` and `WeakKAM/PolynomialBudget` after implementation; it is not a proof package. No module imports a provider or a DRAFT_SORRY anchor.

Before handing a package to a Sonnet prover, put the following hard rules verbatim in its brief. For B10, split before the 800-line estimate becomes unreliable; the hard cap remains 1500.

1. **Never use `set_option maxHeartbeats`** (or any heartbeat-budget override). A default-heartbeat elaboration
   failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a
   proof will not elaborate at default heartbeats, report it as a design signal.
2. **No Lean file may exceed 1500 lines of code.** When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.
3. **Every `.lean` file is a Lean module**: copyright comment, `module`, imports (`public import` for the
   interface), module docstring, `public section`. Expose (`@[expose]`) definitions whose bodies must unfold.
4. **No `axiom`, `admit`, `unsafe`, `opaque`; `sorry` only** as the manifest-bound body of a frozen statement in
   `KAM/Frozen/`. No recursion-depth or synthesis-heartbeat overrides either.
5. **Frozen files are read-only.** Never edit anything under `KAM/Frozen/` or `manifest/`. If a frozen
   declaration looks wrong, stop and report; never add a premise or substitute a helper.
6. **No conclusion-shaped hypotheses.** A theorem may assume only source premises, standing assumptions, typing
   data and explicit owner rulings. Conditional helpers get distinct names and never stand in for a source result.
7. **Ambient types:** `Fin n → ℝ`, `Fin n → ℂ`, Fourier indices `Fin n → ℤ`. Never `EuclideanSpace`.
8. **Builds:** one targeted `nice -n 5 lake build <Module>` at a time; never `lake clean`; never rebuild the
   library from scratch in a worktree (worktrees use a copy-on-write overlay on `main`'s build snapshot). A wait
   on the compile gate is expected, not a hang.
9. **Providers are quarantined.** `KAM/Provider/<Name>.lean` proves its frozen theorem as `KAM.Provider.<name>`;
   no module except the frozen anchor may import a provider or a `DRAFT_SORRY` anchor (the root file skips them).
10. **Never edit `README.md`** (generated) or `KAM.lean` (generated by `scripts/gen_root_imports.py`).
11. **Errata:** report every suspected defect in a pinned source (location, quoted text, why it is wrong) in your
    handoff; the orchestrator records it in `docs/errata/ledger.json`. Deviations you introduce are reported too.


## Proof plans and release gates

B04: normalize the compactly supported one-variable polynomial bump by its exact positive integral; tensor it in the coordinates. Differentiate convolution on the right. For the kth multilinear derivative sum over N^k coordinate choices, then maximize the finite multiindices. Prove the bump L1 constants finite and c-prime positive; approximate numerical integration is not a theorem input.

B05/B09: B05 assumes only `SelectionExtensionChain`; B09 projects its retained chain via `hc.toSelectionExtensionChain`. No resonance equation enters B05. Support at max-distance ≤t_j/2 lies strictly inside B_j. Multiply by the increment there and extend by zero outside that support. At any fixed finite prefix, the same cutoff choices must be used for every mode referencing a stage. The temporary family for modes beyond the current cutoff is extended by min{modeStage(k),ν}; apply the all-mode measure theorem to that family, then include its good set in the finite tests. No circular use of the final retained set.

B08: telescope from m=modeStage(k) to ν-1 directly, using S_m≤γ T_m^{-(τ+1)}. Multiply by |k|₁≤T_m. Subtract this ONE γ margin from the tested 2γ margin. For m=ν the increment sum is empty. The construction of the next map uses this finite result before any limit exists.

B10: derive C1 from the strip budget; C2 from finite-divisor and t_(ν+1) T_ν 2C₁≤D_ν/2; C3 from Q_ν≤Q₀g1^ν≤varpi/2. Obtain the whole-collar zero Fourier/Taylor coefficients before restricting the canonical map to B_(ν+1). The remainder estimate is ε_ν(2q²+2E_ν+Q_ν)≤(7/8)varpi ε_ν. Prove raw, unscaled phase derivative bounds; weighted symplectic estimates alone do not fill the output field. Export O4 via `selection_iteration_parameter_blocks`: compose joint holomorphy with each coordinate projection and apply `param_cauchy` to its own sup bound A or alpha. Projecting the max bound alone does not yield the smaller constants. Export E4 via `selection_iteration_parameter_first` at inner radius t/2 and j=1.

B12: first prove B11 using the exact Mathlib declarations `tendstoUniformlyOn_tsum_nat` and `continuousOn_tsum`, and use it twice on Kinf. Then continuity from above for the compact nested finite tests gives meas Hinf≥meas K-loss. Diophantine follows from the shell test and the same one-tail estimate. Distinguish Hinf from Kinf in every field: this source only claims the Diophantine conclusion on Hinf.

B14/B15: composition order is X0∘...∘X_(ν-1), with shared b. The fibre is convex, so the increment uses the phase derivative bound on that fibre. Prove estimates on T_(s/2), then Cauchy row-sum bounds on the strictly smaller T_(s/4); uniform convergence on the larger strip alone is insufficient to assert uniform derivative convergence on the same strip. KAM.uniform_limits then has precisely its stated hypotheses.

B16: transport the complex Hamiltonian field at every finite stage and restrict to real points. At eta=0, ∂eta R has bound ε_j/s_j and ∂theta R has bound 2ε_j/s. Pass these first-jet terms and theta derivatives to the limit. Real symplecticity is derived from `Canonical.symplFormC` via `phaseToC`, then use frozen `symplecticForm`. Lagrangianity is the limit of the zero-section pullback. The angle defect derivative ≤2^-11 proves immersion and injectivity on the covering space. Do not feed a composed real map to a small-holomorphic-flow theorem without its hypotheses.

B18: prove collar_increment_lipschitz by the short-distance/long-distance dichotomy for one stage. In the short case, move along a complex direction normalized in max norm and apply one-variable Cauchy, avoiding an extraneous factor N; the stage constant is ≤4e/t. Sum using param_lip_sum, not a convexity assumption on Kinf or a guessed positive limiting collar.

B19: extend the defect using KAM.mcshane_prod, then use KAM.lipeo_onto and KAM.lipeo_bounds. The half-open cube is a countable union of compact inner boxes; its evaluation image is sigma compact, hence F_sigma/Borel. Apply the inverse Lipschitz volume bound for the LOWER estimate: the factor is (1-lambda)^(2N), not its reciprocal and not (1+lambda)^(-2N). The full closed-cell image is compact; countable lattice saturation gives the real covering image and its quotient image is compact.

B20: bound each of the three lambdaMax branches before taking their minimum. Use C₁≥1 in the first branch. For strip rate 0, use L=0; for positive strip rate absorb log(1/u) by u^-1, so the constant may depend on that strip rate. Quantify the common coefficient before the other rates and every datum in the family. For beta variation, choose cstar and cD before the varying beta, ε and f, and return ONE evaluation output together with its power bound.

## Provider assembly and consumer boundary

No frozen theorem is closed directly by this scope. No provider is created, no frozen body is changed, and no `#print axioms` result is proof closure. P11a5 consumes the final witness, the explicit admissible formula and the uniform beta-budget/displacement constants. It must assemble its own quantitative theorem without adding a premise to P-FIXED. Part 13 later bridges to the frozen physical torus definitions; the current tori are in unreduced action-angle coordinates.

## Risks and uncertainties

- P11A interfaces are concurrent. Before proof work, reconcile its actual declarations for amount, collar, cutoff, increments and canonical map with the literal formulas in Appendix A; write bridge lemmas and run a combined signature check. This standalone check verifies Lean syntax/types, not the unavailable upstream consumer application.
- Output records contain many analytic fields; implement focused local lemmas and assemble records only at the end of a package. Do not attempt to solve a giant record goal with an unrestricted simp call.
- Source-faithful constants c-prime and C_Dio require exact integrals/suprema and all dimension factors. The budget proof cannot replace them with experimentally estimated constants.
- B10 must preserve finite prefixes, periodicity, reality and the affine map clause simultaneously. Independent existential chains of every length are insufficient.
- The new continuous-series bridge and inherited real-flow guard must be independently audited before the graph gap is marked resolved. The signatures do not close either gap.

## Revision 2

This revision addresses every finding in `DESIGN-P11B-design-audit-1.md` (F1, F2, N1, N2). It changes the design surface, with no production proofs or frozen changes.

| Finding | Resolution and package obligation |
|---|---|
| F1 (major), finite-extension domain | Added `SelectionExtensionChain` with initial, compact, nonempty, nested, holomorphic, real and bound fields only. `finite_extension` takes this weaker predicate. `SelectionFiniteChain` extends it with `retained`; its generated projection connects B09 to B05. B05 now covers arbitrary nested compact prefixes, including the audit's zero-increment example. |
| F2 (major), Hamiltonian-independent constants | `selectionFixedKey` replaces `d.h` by `selectionM₀ d`. Both `adm_budget_beta` and `displacement_power` choose coefficients before quantifying over every d with the same numerical/geometric key, hence before h, beta, epsilon and f vary. In B20, prove the explicit `selectionCDelta d * selectionCGamma d` constant invariant under key equality and use the uniform budget for cstar. The h→h+1 family is admitted because it preserves actual M₀. The later bounded-M₀ monotone minorant is a separate P11a5 obligation. |
| N1, upstream reconciliation | Standalone elaboration does not discharge any upstream bridge. B10 release requires checked bridges to the exact delivered P11A scalar/singleton tensor, thickening, finite-type amount, domain, cutoff and frozen frequency definitions. The collar supplier and B16 shared-build gate are specified below. |
| N2, explicit recoverable clauses | Added the final derivative-sum ≤C₁ clause to `schedule_props` and lambda≤lambdaMax to `free_radius`. Added conditional implementation helpers `selection_iteration_parameter_blocks` (separate O4 bounds from separate sup bounds) and `selection_iteration_parameter_first` (E4 at j=1, t'=t/2) in B10. These helpers assume an output record only under distinct names; source exports still construct their records from raw premises. Finite-divisor intermediate estimates remain named local proof blocks as specified below. |

**N1 collar supplier, B10 release gate.** Adjacent P11A `canonical_step_real` returns reality on the whole real collar but its angle-derivative estimate only for b∈S.E. The `SelectionIteration.real_angle_derivative` field requires every real b with `selectionReal b ∈ actionNbhd (K (ν+1)) (selectiont a (ν+1))`; membership in K alone cannot fill it. B10 must add a local supplier `selection_real_angle_derivative_on_collar`, after reconciling the P11A interfaces, with exactly that field's quantifiers and bound. For each such b, restrict the angle field of the real affine generator `p11StepPhi` to b, use whole-collar coefficient reality and divisor bounds to prove it is a real C² periodic field, with uniform sup bound and derivative bound `selectionRealBudget a ν`. Apply exact P11A `real_lipschitz` at time 1, and prove that its `p11RealFlow` equals the angle block of `p11StepMap` by ODE uniqueness, including equality of derivatives. This is a local proof obligation, not a new assumption or a provisional upstream theorem in the signatures. B10 remains unreleased until this supplier is proved or P11A exports the stronger collar clause. The output field is labelled accordingly in Appendix A.

**N1 covariance, B16 release gate.** `chart_field` was inspected in the delivered PP1-4 worktree, but its module was absent from inp/shared build at audit time. Land and build that package through its owner before B16; use its actual factor-one type after proving the real restriction bridge. The present signature check imports no chart_field module and certifies neither its landing nor its applicability.

**N2 finite-divisor local clauses, B08.** In `fd_tel`, for m=modeStage(k)≤ν prove the finite increment tail ≤`selectionTail a m` and ≤γ T_m^(-τ-1). In `fd_test`, use retained-prefix nesting to recover the stage-m shell test with margin 2γ. In `fd_concl`, multiply the tail by |k|₁≤T_m, bound the resulting error by γ|k|₁^(-τ), and subtract from the shell test; m=ν has empty tail. These are explicit internal source goals, not additional chain hypotheses. Only the final divisor inequality is public.

## Validation receipt

The exact command `/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-p11b .drafts/scratch/P11BSignatures-r2.lean` exited 0 with exactly **30** `declaration uses 'sorry'` warnings and no errors or other diagnostics (`.drafts/scratch/P11B-r2-signatures.log`). The delivered file and scratch copy are identical: **958 lines**, SHA256 `6800132b3e98b3badc215d5cb1cccc6b016e2f14ec976b661519e436cbf39596`. All 30 theorem bodies are `sorry`; no definition body is `sorry`.

The mechanical receipt `.drafts/scratch/P11B-r2-coverage.log` confirms 119/119 live graph nodes, no duplicate rows, exact Appendix A equality and the line cap. Recomputed dependency waves agree for all 20 packages (maximum 14); all estimates remain 150–800 lines. No production Lean module is changed and no production build target exists for this design-only revision. The required signature elaboration is the targeted check; upstream gates above remain open proof/package obligations.

`scripts/lint_sources.sh` exited 0: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (144 frozen declarations)` (`.drafts/scratch/P11B-r2-lint.log`). As in revision 1, the untracked `.drafts/gated-bin/lake` PATH shim routed its ABI subprocess through `inp_sig_check.sh` against the existing shared build. All Lean checks in this revision run sequentially through that gate, without a library rebuild.

The separate gated `.drafts/scratch/P11BAxioms-r2.lean` check exited 0, with only the same 30 sorry warnings and six requested axiom reports (`.drafts/scratch/P11B-r2-axioms.log`). `#print axioms` for `finite_extension`, `adm_budget_beta`, `parameter_selection`, `limit_torus`, `evaluation_bilipschitz` and `displacement_power` each reports `[propext, sorryAx, Classical.choice, Quot.sound]`. These are unproved draft signatures; elaboration and axiom inspection establish no proof closure. `git diff --check` passes.

Source snapshot: base worktree commit `081967912d5200ad4711d6d16abde6a8cfafea71`.

- `docs/graph/P/DEPGRAPH.md`: `7d58c7597a6e498eddaa56d6b062d015a466131dcd2e9abde2bc852f07b6e8ca`.
- `docs/graph/P/reviews/GLOBAL-review.md`: `39f5a84a7d261187fa474fa94ecc839a1fac463810fdd8ce674fe5766d539e65`.
- `blueprint-P/parts/p11a3-iteration-selection.tex`: `90251ed2045353dd2c9574b5f2c53588eb5762ea9dbc86ed9075c00bf8d9ad1c`.
- `blueprint-P/parts/p11a4-limit-family.tex`: `c88030106491131ffde29078d1f0919ae092592bf37e1bbc68a87ab087369b2b`.

## Appendix A. Exact signatures

Untracked canonical delivery: `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean`. The following block is byte-for-byte the delivered file. It is a single module below 1500 lines. No source theorem proof is supplied.

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Frozen.Defs.RealHamiltonian
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import KAM.Frozen.Defs.SymplecticForm
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Kepler.Basic
public import KAM.Canonical.Setting
public import KAM.Fourier.ExpSums
public import KAM.Strip.Limits
public import KAM.Measure.McShane
public import KAM.Measure.Lipeo
public import KAM.Measure.Lipschitz

/-! # P11B exact design signatures
Proofs are deliberately `sorry`. Output records are used only in conclusions of source exports.
No source theorem assumes an iteration, selected set, torus, or a quantitative conclusion.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

abbrev SelectionR (n : ℕ) := Fin n → ℝ
abbrev SelectionC (n : ℕ) := Fin n → ℂ
abbrev SelectionPhaseC (n : ℕ) := SelectionC n × SelectionC n
abbrev SelectionPoint (n : ℕ) := SelectionPhaseC n × SelectionC n

def selectionReal (x : SelectionR n) : SelectionC n := fun i => (x i : ℂ)
def selectionRe (x : SelectionC n) : SelectionR n := fun i => (x i).re
def selectionLength (x : SelectionR n) : ℝ := Real.sqrt (∑ i, x i ^ 2)
def selectionThick (K : Set (SelectionR n)) (v : ℝ) : Set (SelectionR n) :=
  {x | ∃ y ∈ K, selectionLength (x - y) ≤ v}
def selectionDomain (r s : ℝ) (B : Set (SelectionC n)) : Set (SelectionPoint n) :=
  {x | x.1.1 ∈ complexStrip n r ∧ ‖x.1.2‖ < s ∧ x.2 ∈ B}
def selectionScalar (ρ : ℕ) (ω : SelectionR n → SelectionR n)
    (c y : SelectionR n) : ℝ := (∑ i, c i * ω y i) ^ ρ
/-- Explicit Euclidean diagonal tensor seminorm; ambient Pi norm remains the max norm. -/
def selectionDG (j : ℕ) (g : SelectionR n → ℝ) (y : SelectionR n) : ℝ :=
  sSup {v | ∃ a : SelectionR n, selectionLength a = 1 ∧
    v = |iteratedFDeriv ℝ j g y (fun _ => a)|}
def selectionDGVector (j : ℕ) (g : SelectionR n → SelectionR n)
    (y : SelectionR n) : ℝ :=
  sSup {v | ∃ a : SelectionR n, selectionLength a = 1 ∧
    v = selectionLength (iteratedFDeriv ℝ j g y (fun _ => a))}

/-- Literal standing scalar/geometric inputs; no perturbation or construction outputs. -/
structure SelectionData (n : ℕ) where
  μ : ℕ
  ρ : ℕ
  τ : ℝ
  ϑ : ℝ
  strip : ℝ
  C₁ : ℝ
  β : ℝ
  M : ℝ
  loss : ℝ
  K : Set (SelectionR n)
  h : SelectionC n → ℂ
  n_pos : 1 ≤ n
  μ_pos : 1 ≤ μ
  rho_mem : ρ = 1 ∨ ρ = 2
  tau_nonneg : 0 ≤ τ
  tau_gap : (n : ℝ) * μ / ρ - 1 < τ
  compact : IsCompact K
  positive_measure : 0 < volume K
  theta_pos : 0 < ϑ
  theta_le : ϑ ≤ 1
  strip_pos : 0 < strip
  strip_le : strip ≤ 1
  hessian_normalized : 1 ≤ C₁
  beta_pos : 0 < β
  beta_le : β ≤ M
  loss_pos : 0 < loss
  loss_lt : ENNReal.ofReal loss < volume K
  holo : DifferentiableOn ℂ h (actionNbhd K (2 * ϑ))
  real : ∀ y : SelectionR n, selectionReal y ∈ actionNbhd K (2 * ϑ) →
    (h (selectionReal y)).im = 0
  hessian : ∀ b ∈ actionNbhd K (2 * ϑ),
    ‖fderiv ℂ (fun z i => fderiv ℂ h z (Pi.single i 1)) b‖ ≤ C₁
  finite_type : ∀ c : SelectionR n, selectionLength c = 1 → ∀ y ∈ K,
    ∃ j ≤ μ, β ≤ selectionDG j (selectionScalar ρ (frequencyMap h) c) y
  top_bounds : ∀ c : SelectionR n, selectionLength c = 1 → ∀ j : ℕ,
    1 ≤ j → j ≤ μ + 1 → ∀ y ∈ selectionThick K ϑ,
    ∀ a : Fin j → SelectionR n, (∀ i, selectionLength (a i) ≤ 1) →
    |iteratedFDeriv ℝ j (selectionScalar ρ (frequencyMap h) c) y a| ≤ M

/-- Perturbation premises, kept after the constants in every source theorem. -/
structure SelectionPerturbation (d : SelectionData n)
    (f : SelectionPhaseC n → ℂ) (ε : ℝ) : Prop where
  holo : DifferentiableOn ℂ f (complexStrip n d.strip ×ˢ actionNbhd d.K (2 * d.ϑ))
  periodic : ∀ z ∈ complexStrip n d.strip ×ˢ actionNbhd d.K (2 * d.ϑ),
    ∀ k : Fin n → ℤ, f (z.1 + (fun i => (k i : ℂ)), z.2) = f z
  real : ∀ z : Phase n, phaseToC z ∈
    complexStrip n d.strip ×ˢ actionNbhd d.K (2 * d.ϑ) → (f (phaseToC z)).im = 0
  bound : ∀ z ∈ complexStrip n d.strip ×ˢ actionNbhd d.K (2 * d.ϑ), ‖f z‖ ≤ ε

def sel_data (d : SelectionData n) := d
/-- Upstream p11a2 formula, not an invented Fourier representation. -/
def selectionCN (n : ℕ) : ℝ :=
  2 * (1 + 1 / π) * (3 * n / (Real.exp 1 * π)) ^ (n - 1)
def selectionCutoffError (n : ℕ) (T d : ℝ) : ℝ :=
  selectionCN n * (1 + d⁻¹ ^ n) * Real.exp (-π * T * d)
def selectionExponent (n μ : ℕ) (τ : ℝ) : ℝ := 2 * (τ + 1) * (μ + 1) + n + 4
def selectionVarpi (n μ : ℕ) (τ : ℝ) : ℝ := (2 : ℝ) ^ (-2 * selectionExponent n μ τ)
def selectionQ (n μ : ℕ) (τ : ℝ) : ℝ := Real.sqrt (selectionVarpi n μ τ) / 4
def selectionVarrho (n μ : ℕ) (τ : ℝ) : ℝ := selectionVarpi n μ τ / selectionQ n μ τ
def selectionCQ (n : ℕ) : ℝ := 18 * n * (4 * n + 5)
def selectionG (n μ : ℕ) (τ : ℝ) : Fin 4 → ℝ :=
  let v := selectionVarrho n μ τ
  ![v * (2 : ℝ) ^ τ * 2 ^ (n + 1), v * (2 : ℝ) ^ (τ + 1),
    v * (2 : ℝ) ^ ((τ + 1) * μ), v * (2 : ℝ) ^ (2 * τ) * 2 ^ (n + 1)]
def schedule_consts (n μ : ℕ) (τ : ℝ) : ℝ × ℝ × ℝ :=
  (selectionVarpi n μ τ, selectionQ n μ τ, selectionVarrho n μ τ)

theorem schedule_ratios (hn : 1 ≤ n) (hμ : 1 ≤ μ) (hτ : 0 ≤ τ) :
    0 < selectionQ n μ τ ∧ selectionQ n μ τ ≤ (2 : ℝ)⁻¹ ^ 5 ∧
    2 * selectionQ n μ τ ^ 2 = selectionVarpi n μ τ / 8 ∧
    (∀ i, selectionG n μ τ i ≤ (2 : ℝ)⁻¹ ^ 5) ∧
    selectionVarrho n μ τ ≤ (2 : ℝ) ^ (-(τ + 1)) / 32 := sorry

theorem geom_recursion {v c P p : ℝ} (hv : 0 < v) (hv1 : v < 1)
    (hc0 : 0 ≤ c) (hc : c ≤ 3 * v / 8) (hP : 0 < P) (hp : 0 < p)
    (hpv : p * v ≤ 1) (x : ℕ → ℝ) (hx : ∀ j, 0 ≤ x j)
    (hzero : P * x 0 ≤ v / 2)
    (hrec : ∀ j, x (j + 1) ≤ x j * (c + P * p ^ j * x j)) :
    ∀ j, x j ≤ x 0 * v ^ j ∧ P * p ^ j * x j ≤ v / 2 ∧
      x (j + 1) ≤ 7 * v * x j / 8 := sorry

/-- Formula inputs; no inequalities or iteration conclusions are hidden here. -/
structure SelectionSchedule (n : ℕ) where
  μ : ℕ
  τ : ℝ
  γ : ℝ
  strip : ℝ
  T₀ : ℝ
  t₀ : ℝ
  s₀ : ℝ
  ε₀ : ℝ

def selectionT (a : SelectionSchedule n) (j : ℕ) : ℝ := a.T₀ * 2 ^ j
def selectionD (a : SelectionSchedule n) (j : ℕ) : ℝ := a.γ * selectionT a j ^ (-a.τ)
def selectiont (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  a.t₀ * (2 : ℝ) ^ (-(a.τ + 1) * j)
def selectionε (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  a.ε₀ * selectionVarpi n a.μ a.τ ^ j
def selections (a : SelectionSchedule n) (j : ℕ) : ℝ := a.s₀ * selectionQ n a.μ a.τ ^ j
def selectionσ (a : SelectionSchedule n) (j : ℕ) : ℝ := a.strip / 24 * (2 : ℝ)⁻¹ ^ j
def selectiond (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  (Real.log (16 * selectionCN n / selectionVarpi n a.μ a.τ) +
    n * Real.log (π * selectionT a j)) / (π * selectionT a j)
def selectionr (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  a.strip - ∑ i ∈ Finset.range j, (selectiond a i + 3 * selectionσ a i)
def selectionell (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  2 * selectionε a j / selections a j
def selectionTail (a : SelectionSchedule n) (m : ℕ) : ℝ := ∑' j, selectionell a (j + m)
def selectionQsharp (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  selectionCQ n * (2 / selectionσ a j) ^ n * selectionε a j /
    (π * selectionD a j * selections a j * selectionσ a j)
def selectionQ₀ (a : SelectionSchedule n) : ℝ :=
  selectionCQ n * 2 ^ n * a.T₀ ^ a.τ * (a.ε₀ / a.s₀) /
    (π * a.γ * (a.strip / 24) ^ (n + 1))
def schedule (a : SelectionSchedule n) := a

theorem strip_budget (a : SelectionSchedule n) (hn : 1 ≤ n) (hμ : 1 ≤ a.μ)
    (hτ : 0 ≤ a.τ) (hs : 0 < a.strip) (hs1 : a.strip ≤ 1) (hT : 1 ≤ a.T₀)
    (hT' : 16 / (π * a.strip) *
      (Real.log (16 * selectionCN n / selectionVarpi n a.μ a.τ) +
        n * Real.log (32 * n / a.strip)) ≤ a.T₀) :
    Summable (selectiond a) ∧ (∑' j, selectiond a j) ≤ a.strip / 4 ∧
    (∑' j, 3 * selectionσ a j) = a.strip / 4 ∧
    ∀ j, a.strip / 2 ≤ selectionr a j ∧
      selectionr a (j + 1) = selectionr a j - selectiond a j - 3 * selectionσ a j ∧
      selectiond a j ≤ a.strip / 4 ∧ selectiond a j ≤ 1 / 4 ∧
      selectionCutoffError n (selectionT a j) (selectiond a j) ≤
        selectionVarpi n a.μ a.τ / 8 := sorry

theorem schedule_props (a : SelectionSchedule n) (hn : 1 ≤ n) (hμ : 1 ≤ a.μ)
    (hτ : 0 ≤ a.τ) (hγ : 0 < a.γ) (hT : 1 ≤ a.T₀)
    (ht : 0 < a.t₀) (hs : 0 < a.s₀) (he : 0 < a.ε₀) (hstrip : 0 < a.strip)
    (hC : 1 ≤ C₁) (h1 : 4 * (a.ε₀ / a.s₀) ≤ a.γ * a.T₀ ^ (-a.τ - 1))
    (h2 : 8 * (a.ε₀ / a.s₀) ≤ C₁ * a.t₀)
    (h3 : 4 * C₁ * a.t₀ ≤ a.γ * a.T₀ ^ (-a.τ - 1)) :
    ∀ j m, selectionT a (j + 1) = 2 * selectionT a j ∧
      selectiont a (j + 1) = (2 : ℝ) ^ (-(a.τ + 1)) * selectiont a j ∧
      selectiont a (j + 1) ≤ selectiont a j / 2 ∧
      selectiont a j ≤ a.γ * selectionT a j ^ (-a.τ - 1) / (4 * C₁) ∧
      selectionε a j / selections a j =
        (a.ε₀ / a.s₀) * selectionVarrho n a.μ a.τ ^ j ∧
      Summable (fun i => selectionell a (i + m)) ∧
      selectionTail a m ≤ 4 * (a.ε₀ / a.s₀) * selectionVarrho n a.μ a.τ ^ m ∧
      selectionTail a m ≤ a.γ * selectionT a m ^ (-a.τ - 1) ∧
      (∑ i ∈ Finset.range j, 4 * selectionε a i / (selections a i * selectiont a i))
        ≤ 8 * (a.ε₀ / a.s₀) / a.t₀ ∧
      (∑ i ∈ Finset.range j, 4 * selectionε a i / (selections a i * selectiont a i))
        ≤ C₁ ∧
      (∑ i ∈ Finset.range j, selectionell a i / selectiont a i ^ a.μ)
        ≤ 4 * (a.ε₀ / a.s₀) / a.t₀ ^ a.μ ∧
      selectionQsharp a j = selectionQ₀ a * selectionG n a.μ a.τ 0 ^ j ∧
      selectiont a (j + 1) * selectionT a j * (2 * C₁) ≤ selectionD a j / 2 := sorry

/-- Exact bump and integral constants of smooth-cutoff, not numerical quadrature. -/
def selectionBumpRaw (μ : ℕ) (x : ℝ) : ℝ := max (1 - x ^ 2) 0 ^ (μ + 1)
def selectionBump (μ : ℕ) (x : ℝ) : ℝ :=
  selectionBumpRaw μ x / ∫ y : ℝ, selectionBumpRaw μ y
def selectionBumpL1 (μ j : ℕ) : ℝ := ∫ y : ℝ, |iteratedDeriv j (selectionBump μ) y|
def selectionCutoffC (n μ k : ℕ) : ℝ := (n : ℝ) ^ k *
  sSup {v | ∃ a : Fin n → ℕ, (∑ i, a i) = k ∧ v = ∏ i, selectionBumpL1 μ (a i)}
def selectionExtensionC (n μ : ℕ) : ℝ := Real.sqrt n *
  sSup {v | ∃ k ≤ μ, v = (4 : ℝ) ^ k *
    ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
      selectionCutoffC n μ j * (k - j : ℕ) ^ (k - j)}

theorem smooth_cutoff (hn : 1 ≤ n) (hμ : 1 ≤ μ) (E : Set (SelectionR n))
    (hE : IsCompact E) (hne : E.Nonempty) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ χ : SelectionR n → ℝ, ContDiff ℝ μ χ ∧
      (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧ (∀ y ∈ E, χ y = 1) ∧
      tsupport χ ⊆ {y | Metric.infDist y E ≤ t / 2} ∧
      ∀ k ≤ μ, ∀ y, ∀ a : Fin k → SelectionR n, (∀ i, ‖a i‖ ≤ 1) →
        |iteratedFDeriv ℝ k χ y a| ≤ selectionCutoffC n μ k * (4 / t) ^ k := sorry

/-- Chain carrier is raw data; all chain properties are returned by the construction. -/
structure SelectionChain (n : ℕ) where
  K : ℕ → Set (SelectionR n)
  Δω : ℕ → SelectionC n → SelectionC n
  Δh : ℕ → SelectionC n → ℂ
  X : ℕ → SelectionC n → SelectionPhaseC n → SelectionPhaseC n
  R : ℕ → SelectionPoint n → ℂ

def selectionFrequency (d : SelectionData n) (c : SelectionChain n)
    (j : ℕ) (b : SelectionC n) : SelectionC n :=
  (fun i => fderiv ℂ d.h b (Pi.single i 1)) + ∑ i ∈ Finset.range j, c.Δω i b
def selectionEnergy (c : SelectionChain n) (j : ℕ) (b : SelectionC n) : ℂ :=
  ∑ i ∈ Finset.range j, c.Δh i b
def selectionCompose (c : SelectionChain n) (b : SelectionC n) : ℕ →
    SelectionPhaseC n → SelectionPhaseC n
  | 0 => id
  | j + 1 => selectionCompose c b j ∘ c.X j b

def selectionModeLength (k : Fin n → ℤ) : ℝ := ∑ i, |(k i : ℝ)|
def selectionShell (a : SelectionSchedule n) (j : ℕ) : Set (Fin n → ℤ) :=
  {k | 0 < selectionModeLength k ∧ selectionModeLength k ≤ selectionT a j ∧
    (j = 0 ∨ selectionT a (j - 1) < selectionModeLength k)}
/-- Explicit representative of the unique shell index for nonzero modes and T0≥1. -/
def selectionModeStage (a : SelectionSchedule n) (k : Fin n → ℤ) : ℕ :=
  ⌈Real.log (selectionModeLength k / a.T₀) / Real.log 2⌉₊
def selectionExtendedFrequency (d : SelectionData n) (c : SelectionChain n)
    (χ : ℕ → SelectionR n → ℝ) (ν : ℕ) (y : SelectionR n) : SelectionR n :=
  frequencyMap d.h y + ∑ j ∈ Finset.range ν,
    χ j y • selectionRe (c.Δω j (selectionReal y))

def selectionRetained (a : SelectionSchedule n) (d : SelectionData n)
    (c : SelectionChain n) (j : ℕ) : Set (SelectionR n) :=
  {b ∈ c.K j | ∀ k ∈ selectionShell a j,
    2 * a.γ / selectionModeLength k ^ a.τ ≤
      ‖∑ i, (k i : ℂ) * selectionFrequency d c j (selectionReal b) i‖}
def selectionInitial (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (x : SelectionPoint n) : ℂ :=
  d.h (x.2 + x.1.2) + f (x.1.1, x.2 + x.1.2) - d.h x.2

theorem initial (d : SelectionData n) (f : SelectionPhaseC n → ℂ) (ε t₀ s₀ : ℝ)
    (hf : SelectionPerturbation d f ε) (ht : 0 < t₀) (ht' : t₀ ≤ d.ϑ)
    (hs : 0 < s₀) (hs' : s₀ ≤ d.ϑ) :
    DifferentiableOn ℂ (fun x => selectionInitial d f x -
      ∑ i, fderiv ℂ d.h x.2 (Pi.single i 1) * x.1.2 i)
      (selectionDomain d.strip s₀ (actionNbhd d.K t₀)) ∧
    (∀ x ∈ selectionDomain d.strip s₀ (actionNbhd d.K t₀),
      ‖selectionInitial d f x - ∑ i, fderiv ℂ d.h x.2 (Pi.single i 1) * x.1.2 i‖
        ≤ ε + n / 2 * d.C₁ * s₀ ^ 2) ∧
    (∀ x ∈ selectionDomain d.strip s₀ (actionNbhd d.K t₀), ∀ k : Fin n → ℤ,
      selectionInitial d f ((x.1.1 + (fun i => (k i : ℂ)), x.1.2), x.2) = selectionInitial d f x) ∧
    ∀ z : Phase n, ∀ b : SelectionR n,
      (phaseToC z, selectionReal b) ∈ selectionDomain d.strip s₀ (actionNbhd d.K t₀) →
      (selectionInitial d f (phaseToC z, selectionReal b)).im = 0 := sorry

/-- Constant formulas consume no perturbation and introduce no new upstream theorem. -/
def selectionM₀ (d : SelectionData n) : ℝ :=
  sSup {v | ∃ j ≤ d.μ, ∃ y ∈ selectionThick d.K d.ϑ,
    v = selectionDGVector j (frequencyMap d.h) y}
def selectionChat (d : SelectionData n) : ℝ :=
  let diam := Metric.diam d.K
  let gap := (d.ρ : ℝ) * (d.τ + 1) / d.μ - n
  2 ^ (n + 2) * d.μ * (Real.sqrt n * diam) ^ (n - 1) *
    (1 + (4 + d.ϑ⁻¹) * Real.sqrt n * diam) * d.M *
    (n : ℝ) ^ ((d.ρ : ℝ) / (2 * d.μ)) * 2 * 3 ^ (n - 1) * (1 + gap⁻¹)
def selectionCDio (d : SelectionData n) : ℝ :=
  selectionChat d * d.β ^ (-1 - (d.μ : ℝ)⁻¹)
def selectionGamma (d : SelectionData n) : ℝ :=
  min ((1 / 2 : ℝ) * (Real.sqrt n)⁻¹ * (d.β / 4) ^ ((d.ρ : ℝ)⁻¹))
    ((d.loss / selectionCDio d) ^ ((d.μ : ℝ) / d.ρ)) / 2

def selectionT₀ (d : SelectionData n) : ℝ := max 1 (16 / (π * d.strip) *
  (Real.log (16 * selectionCN n / selectionVarpi n d.μ d.τ) +
    n * Real.log (32 * n / d.strip)))
def selectiont₀ (d : SelectionData n) : ℝ :=
  min (d.ϑ / Real.sqrt n) (selectionGamma d * selectionT₀ d ^ (-d.τ - 1) / (4 * d.C₁))
def selectionXi (d : SelectionData n) : ℝ :=
  (2 : ℝ) ^ (d.τ + 1) * (1 + selectiont₀ d / (d.strip / 24) +
    (d.strip / 24) / selectiont₀ d + selectionT₀ d * (d.strip / 24))
def selectionThetaMax (d : SelectionData n) : ℝ :=
  if d.ρ = 1 then d.β / 2 else
    min d.β (d.β / (2 ^ (d.μ + 1) * (2 * selectionM₀ d + d.β)))
def selectionLambdaMax (d : SelectionData n) : ℝ := min (d.C₁ * selectiont₀ d / 8)
  (min ((min (selectionVarpi n d.μ d.τ / 2) ((2 : ℝ)⁻¹ ^ 10 / selectionXi d)) *
    (π * selectionGamma d * (d.strip / 24) ^ (n + 1) /
      (selectionCQ n * 2 ^ n * selectionT₀ d ^ d.τ)))
    (selectionThetaMax d * selectiont₀ d ^ d.μ / (4 * selectionExtensionC n d.μ)))
def selectionAdmissible (d : SelectionData n) : ℝ := selectionLambdaMax d ^ 2 / (2 * n * d.C₁)
def adm_params (d : SelectionData n) (ε : ℝ) : SelectionSchedule n :=
  let s₀ := selectionLambdaMax d / (n * d.C₁)
  ⟨d.μ, d.τ, selectionGamma d, d.strip, selectionT₀ d, selectiont₀ d,
    s₀, ε + n / 2 * d.C₁ * s₀ ^ 2⟩
def selectionAdapted (d : SelectionData n) (ε : ℝ) : SelectionSchedule n :=
  ⟨d.μ, d.τ, selectionGamma d, d.strip, selectionT₀ d, selectiont₀ d,
    Real.sqrt (2 * ε / (n * d.C₁)), 2 * ε⟩

/-- Exact scalar A1--A6; A7 remains the separate `initial` theorem. -/
structure SelectionAdmissibility (d : SelectionData n) (a : SelectionSchedule n) : Prop where
  t_pos : 0 < a.t₀
  t_le : a.t₀ ≤ d.ϑ / Real.sqrt n
  collar : 4 * d.C₁ * a.t₀ ≤ a.γ * a.T₀ ^ (-a.τ - 1)
  increment : 8 * (a.ε₀ / a.s₀) ≤ d.C₁ * a.t₀
  radius : a.s₀ ≤ a.t₀ / (8 * n)
  quadratic : selectionQ₀ a ≤ selectionVarpi n a.μ a.τ / 2
  weighted : selectionQ₀ a * selectionXi d ≤ (2 : ℝ)⁻¹ ^ 10
  closeness : 4 * selectionExtensionC n a.μ * (a.ε₀ / a.s₀) / a.t₀ ^ a.μ
    ≤ selectionThetaMax d
  cutoff_ge : 1 ≤ a.T₀
  cutoff_loss : 16 / (π * d.strip) *
    (Real.log (16 * selectionCN n / selectionVarpi n d.μ d.τ) +
      n * Real.log (32 * n / d.strip)) ≤ a.T₀

theorem adm_choice (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) :
    0 < selectionAdmissible d ∧ SelectionAdmissibility d (adm_params d ε) ∧
    (adm_params d ε).ε₀ / (adm_params d ε).s₀ ≤ selectionLambdaMax d := sorry

theorem free_radius (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) :
    SelectionAdmissibility d (selectionAdapted d ε) ∧
    0 < (selectionAdapted d ε).s₀ ∧
    (selectionAdapted d ε).s₀ ≤ (adm_params d ε).s₀ ∧
    (selectionAdapted d ε).ε₀ = ε + n / 2 * d.C₁ * (selectionAdapted d ε).s₀ ^ 2 ∧
    (selectionAdapted d ε).ε₀ / (selectionAdapted d ε).s₀ = Real.sqrt (2 * n * d.C₁ * ε) ∧
    (selectionAdapted d ε).ε₀ / (selectionAdapted d ε).s₀ ≤ selectionLambdaMax d := sorry

/-- Analytic nested-prefix premises of finite-extension; no resonance tests are required. -/
structure SelectionExtensionChain (d : SelectionData n) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) : Prop where
  initial : c.K 0 = d.K
  compact : ∀ j ≤ ν, IsCompact (c.K j)
  nonempty : ∀ j ≤ ν, (c.K j).Nonempty
  nested : ∀ j < ν, c.K (j + 1) ⊆ c.K j
  holomorphic : ∀ j < ν, DifferentiableOn ℂ (c.Δω j) (actionNbhd (c.K j) (selectiont a j))
  real : ∀ j < ν, ∀ b : SelectionR n,
    selectionReal b ∈ actionNbhd (c.K j) (selectiont a j) →
    c.Δω j (selectionReal b) = selectionReal (selectionRe (c.Δω j (selectionReal b)))
  bound : ∀ j < ν, ∀ b ∈ actionNbhd (c.K j) (selectiont a j),
    ‖c.Δω j b‖ ≤ selectionell a j

/-- Retained prefixes additionally satisfy the shell tests used by divisor and measure estimates.
The generated `toSelectionExtensionChain` projection supplies finite-extension's weaker input. -/
structure SelectionFiniteChain (d : SelectionData n) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) : Prop extends SelectionExtensionChain d a c ν where
  retained : ∀ j < ν, c.K (j + 1) = selectionRetained a d c j

def sec_retained_data (c : SelectionChain n) := c

theorem finite_extension (d : SelectionData n) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) (hc : SelectionExtensionChain d a c ν)
    (hμ : a.μ = d.μ) (ht : 0 < a.t₀) (ht1 : a.t₀ ≤ 1)
    (htθ : a.t₀ ≤ d.ϑ / Real.sqrt n) (hτ : 0 ≤ a.τ) :
    ∃ χ : ℕ → SelectionR n → ℝ, ∃ w : SelectionR n → SelectionR n,
      (∀ j < ν, ContDiff ℝ d.μ (χ j) ∧
        (∀ y, 0 ≤ χ j y ∧ χ j y ≤ 1) ∧ (∀ y ∈ c.K j, χ j y = 1) ∧
        tsupport (χ j) ⊆ {y | Metric.infDist y (c.K j) ≤ selectiont a j / 2}) ∧
      w = selectionExtendedFrequency d c χ ν ∧
      ContDiffOn ℝ d.μ w {y | selectionReal y ∈ actionNbhd d.K (2 * d.ϑ)} ∧
      (∀ b ∈ c.K ν, w b = selectionRe (selectionFrequency d c ν (selectionReal b))) ∧
      (ν = 0 → w = frequencyMap d.h) ∧
      ∀ j ≤ d.μ, ∀ y ∈ selectionThick d.K d.ϑ,
        selectionDGVector j (w - frequencyMap d.h) y ≤ selectionExtensionC n d.μ *
          ∑ i ∈ Finset.range ν, selectionell a i / selectiont a i ^ d.μ := sorry

theorem finite_divisor (d : SelectionData n) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) (hc : SelectionFiniteChain d a c ν)
    (ht : 0 < a.t₀) (hT : 1 ≤ a.T₀) (hτ : 0 ≤ a.τ) (hγ : 0 < a.γ)
    (hs : 0 < a.s₀) (he : 0 < a.ε₀)
    (htail : ∀ m ≤ ν, Summable (fun j => selectionell a (j + m)) ∧
      selectionTail a m ≤ a.γ * selectionT a m ^ (-a.τ - 1)) :
    ∀ b ∈ selectionRetained a d c ν, ∀ k : Fin n → ℤ,
      0 < selectionModeLength k → selectionModeLength k ≤ selectionT a ν →
      a.γ / selectionModeLength k ^ a.τ ≤
        ‖∑ i, (k i : ℂ) * selectionFrequency d c ν (selectionReal b) i‖ ∧
      selectionD a ν ≤ a.γ / selectionModeLength k ^ a.τ := sorry

/-- Added local bridge for graph SOURCE_GAP ps-lim. Works on a real compact carrier. -/
theorem continuous_series_on_compact {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (K : Set (SelectionR n)) (v : ℕ → SelectionR n → E) (B : ℕ → ℝ)
    (hv : ∀ j, ContinuousOn (v j) K) (hB : Summable B)
    (hbound : ∀ j, ∀ b ∈ K, ‖v j b‖ ≤ B j) :
    TendstoUniformlyOn (fun m b => ∑ j ∈ Finset.range m, v j b)
      (fun b => ∑' j, v j b) atTop K ∧
    ContinuousOn (fun b => ∑' j, v j b) K ∧
    ∀ b ∈ K, Summable (fun j => v j b) := sorry

/-- a, alpha, kappa, Lambda_R, m, Q are exact scalar schedules, not map suprema. -/
def selectionΛ (n : ℕ) (r : ℝ) : ℝ :=
  ((Real.exp (2 * π * r) + 1) / (Real.exp (2 * π * r) - 1)) ^ n - 1

def selectionA (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  selectionΛ n (selectionσ a j) *
    (1 + selectionCutoffError n (selectionT a j) (selectiond a j)) * selectionε a j /
      (π * selectionD a j * selections a j)
def selectionAlpha (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  (n + 1) * selections a j * selectionA a j / selectionσ a j
def selectionKappa (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  2 * (n + 1) * selectionA a j / selectionσ a j
def selectionMapBudget (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  2 * selectionKappa a j + selectionKappa a j * selections a j / selectionσ a j
def selectionRealBudget (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  2 * selectionT a j *
    (1 + selectionCutoffError n (selectionT a j) (selectiond a j)) * selectionε a j *
      selectionΛ n (selectionr a j - selectiond a j) / (selectionD a j * selections a j)


/-- Exact normal-form and simple-map outputs; never an assumption of a source export. -/
structure SelectionIteration (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (a : SelectionSchedule n) extends SelectionChain n where
  chain : ∀ ν, SelectionFiniteChain d a toSelectionChain ν
  energy_holo : ∀ ν, DifferentiableOn ℂ (selectionEnergy toSelectionChain ν)
    (actionNbhd (K ν) (selectiont a ν))
  increment_holo : ∀ ν, DifferentiableOn ℂ (Δh ν) (actionNbhd (K ν) (selectiont a ν))
  increment_real : ∀ ν, ∀ b : SelectionR n,
    selectionReal b ∈ actionNbhd (K ν) (selectiont a ν) → (Δh ν (selectionReal b)).im = 0
  energy_bound : ∀ ν, ∀ b ∈ actionNbhd (K ν) (selectiont a ν), ‖Δh ν b‖ ≤ 2 * selectionε a ν
  frequency_derivative : ∀ ν, ∀ b ∈ actionNbhd (K ν) (selectiont a ν),
    ‖fderiv ℂ (selectionFrequency d toSelectionChain ν) b‖ ≤ 2 * d.C₁
  remainder_holo : ∀ ν, DifferentiableOn ℂ (R ν)
    (selectionDomain (selectionr a ν) (selections a ν) (actionNbhd (K ν) (selectiont a ν)))
  remainder_bound : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)), ‖R ν x‖ ≤ selectionε a ν
  remainder_periodic : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)), ∀ k : Fin n → ℤ,
    R ν ((x.1.1 + (fun i => (k i : ℂ)), x.1.2), x.2) = R ν x
  remainder_real : ∀ ν, ∀ z : Phase n, ∀ b : SelectionR n,
    (phaseToC z, selectionReal b) ∈ selectionDomain (selectionr a ν) (selections a ν)
      (actionNbhd (K ν) (selectiont a ν)) → (R ν (phaseToC z, selectionReal b)).im = 0
  normal_form : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)),
    selectionInitial d f (selectionCompose toSelectionChain x.2 ν x.1, x.2) =
      selectionEnergy toSelectionChain ν x.2 +
        (∑ i, selectionFrequency d toSelectionChain ν x.2 i * x.1.2 i) + R ν x
  map_holo : ∀ ν, DifferentiableOn ℂ (fun x : SelectionPoint n => X ν x.2 x.1)
    (selectionDomain (selectionr a (ν + 1)) (selections a (ν + 1))
      (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))))
  map_domain : ∀ ν, ∀ x ∈ selectionDomain (selectionr a (ν + 1)) (selections a (ν + 1))
    (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))),
    (X ν x.2 x.1, x.2) ∈ selectionDomain (selectionr a (ν + 1) + selectionσ a ν)
      (selections a ν) (actionNbhd (K (ν + 1)) (selectiont a (ν + 1)))
  map_periodic : ∀ ν, ∀ x ∈ selectionDomain (selectionr a (ν + 1)) (selections a (ν + 1))
    (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))), ∀ k : Fin n → ℤ,
    X ν x.2 (x.1 + ((fun i => (k i : ℂ)), 0)) = X ν x.2 x.1 + ((fun i => (k i : ℂ)), 0)
  map_real : ∀ ν, ∀ z : Phase n, ∀ b : SelectionR n,
    (phaseToC z, selectionReal b) ∈ selectionDomain (selectionr a (ν + 1))
      (selections a (ν + 1)) (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))) →
    ∃ w : Phase n, X ν (selectionReal b) (phaseToC z) = phaseToC w
  map_symplectic : ∀ ν, ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))),
    ∀ u v : SelectionPhaseC n,
    Canonical.symplFormC (fderiv ℂ (X ν x.2) x.1 u) (fderiv ℂ (X ν x.2) x.1 v) =
      Canonical.symplFormC u v

  map_angle_bound : ∀ ν, ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))),
    ‖(X ν x.2 x.1).1 - x.1.1‖ ≤ selectionA a ν
  map_action_bound : ∀ ν, ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))),
    ‖(X ν x.2 x.1).2 - x.1.2‖ ≤ selectionAlpha a ν
  map_derivative_bound : ∀ ν, ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))),
    ‖fderiv ℂ (X ν x.2) x.1 - ContinuousLinearMap.id ℂ (SelectionPhaseC n)‖
      ≤ selectionMapBudget a ν
  map_parameter_bound : ∀ ν, ∀ t' : ℝ, 0 < t' → t' < selectiont a (ν + 1) →
    ∀ z : SelectionPhaseC n, z.1 ∈ complexStrip n (selectionr a (ν + 1)) →
    ‖z.2‖ < selections a (ν + 1) → ∀ b ∈ actionNbhd (K (ν + 1)) t', ∀ j : ℕ,
    ‖iteratedFDeriv ℂ j (fun c => X ν c z - z) b‖ ≤
      (j : ℝ) ^ j * max (selectionA a ν) (selectionAlpha a ν) /
        (selectiont a (ν + 1) - t') ^ j

  map_affine : ∀ ν, ∀ b ∈ actionNbhd (K (ν + 1)) (selectiont a (ν + 1)),
    ∃ Θ : SelectionC n → SelectionC n,
    ∃ A : SelectionC n → (SelectionC n →L[ℂ] SelectionC n),
    ∃ v : SelectionC n → SelectionC n,
    ∀ z : SelectionPhaseC n, z.1 ∈ complexStrip n (selectionr a (ν + 1)) →
      ‖z.2‖ < selections a (ν + 1) → X ν b z = (Θ z.1, A z.1 z.2 + v z.1)
  map_injective : ∀ ν, ∀ b ∈ actionNbhd (K (ν + 1)) (selectiont a (ν + 1)),
    InjOn (X ν b) {z | z.1 ∈ complexStrip n (selectionr a (ν + 1)) ∧
      ‖z.2‖ < selections a (ν + 1)}
  /-- Requires the B10 real-collar supplier; canonical_step_real on S.E alone is insufficient. -/
  real_angle_derivative : ∀ ν, ∀ b : SelectionR n,
    selectionReal b ∈ actionNbhd (K (ν + 1)) (selectiont a (ν + 1)) → ∀ θ,
    ‖fderiv ℝ (fun v : SelectionR n =>
        selectionRe ((X ν (selectionReal b) (selectionReal v, 0)).1)) θ -
      ContinuousLinearMap.id ℝ (SelectionR n)‖ ≤ Real.exp (selectionRealBudget a ν) - 1

/-- Conditional implementation helper for source O4. Apply parameter Cauchy separately to
holomorphic angle/action defects with their separate sup bounds, not to the joint max estimate. -/
theorem selection_iteration_parameter_blocks (d : SelectionData n)
    (f : SelectionPhaseC n → ℂ) (a : SelectionSchedule n) (o : SelectionIteration d f a)
    (ν : ℕ) (t' : ℝ) (ht' : 0 < t') (htt : t' < selectiont a (ν + 1))
    (z : SelectionPhaseC n) (hz : z.1 ∈ complexStrip n (selectionr a (ν + 1)))
    (hη : ‖z.2‖ < selections a (ν + 1))
    (b : SelectionC n) (hb : b ∈ actionNbhd (o.K (ν + 1)) t') (j : ℕ) :
    ‖iteratedFDeriv ℂ j (fun c => (o.X ν c z).1 - z.1) b‖ ≤
      (j : ℝ) ^ j * selectionA a ν / (selectiont a (ν + 1) - t') ^ j ∧
    ‖iteratedFDeriv ℂ j (fun c => (o.X ν c z).2 - z.2) b‖ ≤
      (j : ℝ) ^ j * selectionAlpha a ν / (selectiont a (ν + 1) - t') ^ j := sorry

/-- Conditional implementation helper exporting E4 from the joint j=1 Cauchy bound. -/
theorem selection_iteration_parameter_first (d : SelectionData n)
    (f : SelectionPhaseC n → ℂ) (a : SelectionSchedule n) (o : SelectionIteration d f a)
    (ν : ℕ) (ht : 0 < selectiont a (ν + 1))
    (z : SelectionPhaseC n) (hz : z.1 ∈ complexStrip n (selectionr a (ν + 1)))
    (hη : ‖z.2‖ < selections a (ν + 1))
    (b : SelectionC n) (hb : b ∈ actionNbhd (o.K (ν + 1)) (selectiont a (ν + 1) / 2)) :
    ‖fderiv ℂ (fun c => o.X ν c z - z) b‖ ≤
      2 * max (selectionA a ν) (selectionAlpha a ν) / selectiont a (ν + 1) := sorry

/-- All finite chains are built coherently by extending the existing chain. -/
theorem inductive_lemma (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) : Nonempty (SelectionIteration d f (adm_params d ε)) := sorry

theorem inductive_lemma_adapted (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) :
    Nonempty (SelectionIteration d f (selectionAdapted d ε)) := sorry

/-- The finite all-mode tests are outputs, defined using the same first j cutoff extensions. -/
structure SelectionOutput (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (a : SelectionSchedule n) extends SelectionIteration d f a where
  cutoffs : ℕ → SelectionR n → ℝ
  cutoff_spec : ∀ j, ContDiff ℝ d.μ (cutoffs j) ∧
    (∀ y, 0 ≤ cutoffs j y ∧ cutoffs j y ≤ 1) ∧ (∀ y ∈ K j, cutoffs j y = 1) ∧
    tsupport (cutoffs j) ⊆ {y | Metric.infDist y (K j) ≤ selectiont a j / 2}
  extended : ℕ → SelectionR n → SelectionR n
  extended_formula : ∀ j, extended j = selectionExtendedFrequency d toSelectionChain cutoffs j
  extended_regular : ∀ j, ContDiffOn ℝ d.μ (extended j)
    {y | selectionReal y ∈ actionNbhd d.K (2 * d.ϑ)}
  extended_eq : ∀ j, ∀ b ∈ K j, extended j b =
    selectionRe (selectionFrequency d toSelectionChain j (selectionReal b))
  Kinf : Set (SelectionR n)
  Hinf : Set (SelectionR n)
  Kinf_eq : Kinf = ⋂ j, K j
  compact_K : IsCompact Kinf
  compact_H : IsCompact Hinf
  H_subset : Hinf ⊆ Kinf
  modeStage : (Fin n → ℤ) → ℕ
  modeStage_eq : modeStage = selectionModeStage a
  modeStage_spec : ∀ k ≠ 0, k ∈ selectionShell a (modeStage k)
  Hinf_eq : Hinf = {b ∈ d.K | ∀ k : Fin n → ℤ, k ≠ 0 →
    2 * a.γ / selectionModeLength k ^ a.τ ≤
      |∑ i, (k i : ℝ) * extended (modeStage k) b i|}
  finite_compact : ∀ ν, IsCompact {b ∈ d.K | ∀ k : Fin n → ℤ,
    0 < selectionModeLength k → selectionModeLength k ≤ selectionT a ν →
    2 * a.γ / selectionModeLength k ^ a.τ ≤
      |∑ i, (k i : ℝ) * extended (modeStage k) b i|}
  finite_inclusion : ∀ ν, {b ∈ d.K | ∀ k : Fin n → ℤ,
    0 < selectionModeLength k → selectionModeLength k ≤ selectionT a ν →
    2 * a.γ / selectionModeLength k ^ a.τ ≤
      |∑ i, (k i : ℝ) * extended (modeStage k) b i|} ⊆ K (ν + 1)
  finite_measure : ∀ ν, volume d.K - ENNReal.ofReal d.loss ≤
    volume {b ∈ d.K | ∀ k : Fin n → ℤ,
      0 < selectionModeLength k → selectionModeLength k ≤ selectionT a ν →
      2 * a.γ / selectionModeLength k ^ a.τ ≤
        |∑ i, (k i : ℝ) * extended (modeStage k) b i|}
  measure_H : volume d.K - ENNReal.ofReal d.loss ≤ volume Hinf
  ωstar : SelectionR n → SelectionR n
  hstar : SelectionR n → ℝ
  frequency_summable : ∀ b ∈ Kinf, Summable (fun j => selectionRe (Δω j (selectionReal b)))
  energy_summable : ∀ b ∈ Kinf, Summable (fun j => (Δh j (selectionReal b)).re)
  frequency_uniform : TendstoUniformlyOn
    (fun ν b => selectionRe (selectionFrequency d toSelectionChain ν (selectionReal b)))
    ωstar atTop Kinf
  energy_uniform : TendstoUniformlyOn
    (fun ν b => (selectionEnergy toSelectionChain ν (selectionReal b)).re) hstar atTop Kinf
  ωstar_sum : ∀ b ∈ Kinf, ωstar b = frequencyMap d.h b +
    ∑' j, selectionRe (Δω j (selectionReal b))
  hstar_sum : ∀ b ∈ Kinf, hstar b = ∑' j, (Δh j (selectionReal b)).re
  ωstar_cont : ContinuousOn ωstar Kinf
  hstar_cont : ContinuousOn hstar Kinf
  frequency_tail : ∀ m, ∀ b ∈ Kinf,
    ‖ωstar b - selectionRe (selectionFrequency d toSelectionChain m (selectionReal b))‖
      ≤ selectionTail a m
  energy_tail : ∀ m, ∀ b ∈ Kinf,
    |hstar b - (selectionEnergy toSelectionChain m (selectionReal b)).re| ≤ 4 * selectionε a m
  diophantine : ∀ b ∈ Hinf, IsDiophantine a.γ a.τ (ωstar b)

theorem parameter_selection (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) : Nonempty (SelectionOutput d f (adm_params d ε)) := sorry


def selectionQactual (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  selectionCQ n * selectionΛ n (selectionσ a j) * selectionε a j /
    (π * selectionD a j * selections a j * selectionσ a j)

theorem exported_sums (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) :
    let a := adm_params d ε
    Summable (selectionA a) ∧ Summable (selectionAlpha a) ∧
    Summable (selectionMapBudget a) ∧ Summable (selectionRealBudget a) ∧
    (∑' j, selectionMapBudget a j) ≤ (2 : ℝ)⁻¹ ^ 12 ∧
    (∑' j, selectionRealBudget a j) ≤ (2 : ℝ)⁻¹ ^ 12 ∧
    (∑' j, selectionA a j) ≤ 3 * (a.strip / 24) * selectionQ₀ a / selectionCQ n ∧
    (∑' j, selectionAlpha a j) ≤ a.s₀ * selectionQ₀ a / 16 ∧
    (∀ ν, selectionA a ν ≤ 2 * selectionσ a ν * selectionQactual a ν / selectionCQ n ∧
      selectionKappa a ν ≤ selectionQactual a ν / 16 ∧
      selectionAlpha a ν = selectionKappa a ν * selections a ν / 2 ∧
      selectionRealBudget a ν ≤ 4 * π / selectionCQ n * a.T₀ * (a.strip / 24) *
        selectionQactual a ν ∧
      selectionQactual a ν ≤ selectionQ₀ a * selectionG n a.μ a.τ 0 ^ ν) ∧
    -- Amended 2026-10-28 (OVERNIGHT 19:00): the tsum binds both summands (source E3); the unparenthesised
    -- form left `j` unbound and elaborated only with autoImplicit (disabled in this project).
    ∀ ν, (∑' j, (selectionA a (j + ν) + selectionAlpha a (j + ν))) /
      selectiont a (ν + 1) ≤ (2 : ℝ)⁻¹ ^ 10 := sorry

/-- Derived scalar budgets at the adapted radius; no iteration hypotheses. -/
theorem param_lip_sum (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) :
    let a := selectionAdapted d ε
    Summable (fun j => (selectionA a j + selectionAlpha a j) / selectiont a (j + 1)) ∧
    (∑' j, (selectionA a j + selectionAlpha a j) / selectiont a (j + 1)) ≤
      (2 : ℝ)⁻¹ ^ 10 / 16 := sorry

/-- Full finite-stage measure lemma; extensions are outputs, never a supplied good family. -/
theorem finite_measure (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) (c : SelectionChain n) (ν : ℕ)
    (hc : SelectionFiniteChain d (adm_params d ε) c ν) :
    ∃ χ : ℕ → SelectionR n → ℝ,
      (∀ j ≤ ν, ContDiffOn ℝ d.μ (selectionExtendedFrequency d c χ j)
        {y | selectionReal y ∈ actionNbhd d.K (2 * d.ϑ)} ∧
        ∀ b ∈ c.K j, selectionExtendedFrequency d c χ j b =
          selectionRe (selectionFrequency d c j (selectionReal b))) ∧
      let a := adm_params d ε
      let H := {b ∈ d.K | ∀ k : Fin n → ℤ,
        0 < selectionModeLength k → selectionModeLength k ≤ selectionT a ν →
        2 * a.γ / selectionModeLength k ^ a.τ ≤
          |∑ i, (k i : ℝ) * selectionExtendedFrequency d c χ (selectionModeStage a k) b i|}
      IsCompact H ∧ H ⊆ selectionRetained a d c ν ∧
        volume d.K - ENNReal.ofReal d.loss ≤ volume H ∧ H.Nonempty := sorry

/-- Finite compositions with one common chosen chain. -/
structure SelectionComposition (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (a : SelectionSchedule n) extends SelectionOutput d f a where
  composition_holo : ∀ ν, DifferentiableOn ℂ
    (fun x : SelectionPoint n => selectionCompose toSelectionChain x.2 ν x.1)
    (selectionDomain (selectionr a ν) (selections a ν) (actionNbhd (K ν) (selectiont a ν)))
  composition_domain : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)),
    (selectionCompose toSelectionChain x.2 ν x.1, x.2) ∈
      selectionDomain a.strip a.s₀ (actionNbhd d.K a.t₀)
  composition_derivative : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)),
    ‖fderiv ℂ (selectionCompose toSelectionChain x.2 ν) x.1 -
      ContinuousLinearMap.id ℂ (SelectionPhaseC n)‖ ≤
      Real.exp (∑ j ∈ Finset.range ν, selectionMapBudget a j) - 1
  composition_small : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)),
    ‖fderiv ℂ (selectionCompose toSelectionChain x.2 ν) x.1 -
      ContinuousLinearMap.id ℂ (SelectionPhaseC n)‖ ≤ (2 : ℝ)⁻¹ ^ 11
  composition_angle : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)),
    ‖(selectionCompose toSelectionChain x.2 ν x.1).1 - x.1.1‖ ≤
      ∑ j ∈ Finset.range ν, selectionA a j
  composition_action : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)),
    ‖(selectionCompose toSelectionChain x.2 ν x.1).2 - x.1.2‖ ≤
      ∑ j ∈ Finset.range ν, selectionAlpha a j
  composition_increment : ∀ ν, ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))),
    ‖selectionCompose toSelectionChain x.2 (ν + 1) x.1 -
      selectionCompose toSelectionChain x.2 ν x.1‖ ≤
      (1 + (2 : ℝ)⁻¹ ^ 11) * max (selectionA a ν) (selectionAlpha a ν)

  composition_periodic : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)), ∀ k : Fin n → ℤ,
    selectionCompose toSelectionChain x.2 ν (x.1 + ((fun i => (k i : ℂ)), 0)) =
      selectionCompose toSelectionChain x.2 ν x.1 + ((fun i => (k i : ℂ)), 0)
  composition_symplectic : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)), ∀ u v : SelectionPhaseC n,
    Canonical.symplFormC (fderiv ℂ (selectionCompose toSelectionChain x.2 ν) x.1 u)
      (fderiv ℂ (selectionCompose toSelectionChain x.2 ν) x.1 v) = Canonical.symplFormC u v
  composition_real : ∀ ν, ∀ z : Phase n, ∀ b : SelectionR n,
    (phaseToC z, selectionReal b) ∈ selectionDomain (selectionr a ν) (selections a ν)
      (actionNbhd (K ν) (selectiont a ν)) →
    ∃ w : Phase n, selectionCompose toSelectionChain (selectionReal b) ν (phaseToC z) = phaseToC w

theorem composition (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) :
    Nonempty (SelectionComposition d f (selectionAdapted d ε)) := sorry

def sec_comp_data (c : SelectionChain n) (b : SelectionC n) := selectionCompose c b
/-- Original coordinates, with the parameter in the action block. -/
def selectionEvaluation (u : SelectionR n → SelectionR n → Phase n)
    (b θ : SelectionR n) : Phase n := (θ, b) + u b θ

def sec_limit_data (u : SelectionR n → SelectionR n → Phase n) := selectionEvaluation u

/-- Fixed-strip zero-section limits; no common positive action radius is asserted. -/
structure SelectionLimit (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (a : SelectionSchedule n) extends SelectionComposition d f a where
  limitC : SelectionR n → SelectionC n → SelectionPhaseC n
  limit_holo : ∀ b ∈ Kinf, DifferentiableOn ℂ (limitC b) (complexStrip n (d.strip / 4))
  limit_equivariant : ∀ b ∈ Kinf, ∀ θ ∈ complexStrip n (d.strip / 4),
    ∀ k : Fin n → ℤ, limitC b (θ + (fun i => (k i : ℂ))) =
      limitC b θ + ((fun i => (k i : ℂ)), 0)
  limit_uniform : ∀ b ∈ Kinf, TendstoUniformlyOn
    (fun ν θ => selectionCompose toSelectionChain (selectionReal b) ν (θ, 0))
    (limitC b) atTop (complexStrip n (d.strip / 4))
  derivative_uniform : ∀ b ∈ Kinf, TendstoUniformlyOn
    (fun ν θ => fderiv ℂ
      (fun v => selectionCompose toSelectionChain (selectionReal b) ν (v, 0)) θ)
    (fderiv ℂ (limitC b)) atTop (complexStrip n (d.strip / 4))
  defect : SelectionR n → SelectionR n → Phase n
  limit_real : ∀ b ∈ Kinf, ∀ θ,
    limitC b (selectionReal θ) = phaseToC ((θ, 0) + defect b θ)
  periodic : ∀ b ∈ Kinf, ∀ θ, ∀ k : Fin n → ℤ,
    defect b (θ + (fun i => (k i : ℝ))) = defect b θ
  complex_angle_bound : ∀ b ∈ Kinf, ∀ θ ∈ complexStrip n (d.strip / 4),
    ‖(limitC b θ).1 - θ‖ ≤ ∑' j, selectionA a j
  complex_action_bound : ∀ b ∈ Kinf, ∀ θ ∈ complexStrip n (d.strip / 4),
    ‖(limitC b θ).2‖ ≤ ∑' j, selectionAlpha a j
  complex_derivative_bound : ∀ b ∈ Kinf, ∀ θ ∈ complexStrip n (d.strip / 4),
    ‖fderiv ℂ (fun v => limitC b v - (v, 0)) θ‖ ≤ (2 : ℝ)⁻¹ ^ 11
  angle_lipschitz : ∀ b ∈ Kinf, ∀ θ θ',
    ‖defect b θ - defect b θ'‖ ≤ (2 : ℝ)⁻¹ ^ 11 * ‖θ - θ'‖

theorem limit_map (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) : Nonempty (SelectionLimit d f (selectionAdapted d ε)) := sorry

def selectionHamiltonian (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (z : Phase n) : ℝ := realHamiltonian d.h f z

structure SelectionTori (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (a : SelectionSchedule n) extends SelectionLimit d f a where
  analytic : ∀ b ∈ Kinf, AnalyticOnNhd ℝ (selectionEvaluation defect b) univ
  invariance : ∀ b ∈ Kinf, ∀ θ,
    fderiv ℝ (selectionEvaluation defect b) θ (ωstar b) =
      hamiltonianVectorField (selectionHamiltonian d f) (selectionEvaluation defect b θ)
  orbit : ∀ b ∈ Kinf, ∀ θ, ∀ t : ℝ,
    HasDerivAt (fun t => selectionEvaluation defect b (θ + t • ωstar b))
      (hamiltonianVectorField (selectionHamiltonian d f)
        (selectionEvaluation defect b (θ + t • ωstar b))) t
  lagrangian : ∀ b ∈ Kinf, ∀ θ v w,
    symplecticForm (fderiv ℝ (selectionEvaluation defect b) θ v)
      (fderiv ℝ (selectionEvaluation defect b) θ w) = 0
  immersion_bound : ∀ b ∈ Kinf, ∀ θ v,
    (1 - (2 : ℝ)⁻¹ ^ 11) * ‖v‖ ≤ ‖fderiv ℝ (selectionEvaluation defect b) θ v‖
  embedding_bound : ∀ b ∈ Kinf, ∀ θ θ',
    (1 - (2 : ℝ)⁻¹ ^ 11) * ‖θ - θ'‖ ≤
      ‖selectionEvaluation defect b θ - selectionEvaluation defect b θ'‖

theorem limit_torus (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) : Nonempty (SelectionTori d f (selectionAdapted d ε)) := sorry

/-- Local analytic lemma used by lf-stage; no geometry of the closed set is needed. -/
theorem collar_increment_lipschitz (K : Set (SelectionR n)) (t e : ℝ)
    (ht : 0 < t) (he : 0 ≤ e) (g : SelectionC n → SelectionPhaseC n)
    (hg : DifferentiableOn ℂ g (actionNbhd K t))
    (hb : ∀ z ∈ actionNbhd K t, ‖g z‖ ≤ e) :
    ∀ b ∈ K, ∀ b' ∈ K,
      ‖g (selectionReal b) - g (selectionReal b')‖ ≤ 4 * e / t * ‖b - b'‖ := sorry

def selectionDelta (d : SelectionData n) (ε : ℝ) : ℝ :=
  let a := selectionAdapted d ε
  selectionQ₀ a * max (3 * (a.strip / 24) / selectionCQ n) (a.s₀ / 16)
def selectionCDelta (d : SelectionData n) : ℝ :=
  selectionCQ n * 2 ^ n * selectionT₀ d ^ d.τ * Real.sqrt (2 * n * d.C₁) /
    (128 * π * (d.strip / 24) ^ (n + 1))
def selectionCGamma (d : SelectionData n) : ℝ :=
  2 * max (2 * Real.sqrt n * (4 : ℝ) ^ ((d.ρ : ℝ)⁻¹))
    ((selectionChat d / d.loss) ^ ((d.μ : ℝ) / d.ρ))

theorem gamma_inverse (d : SelectionData n) (hβ : d.β ≤ 1) :
    (selectionGamma d)⁻¹ ≤ selectionCGamma d * d.β ^ (-((d.μ : ℝ) + 1) / d.ρ) := sorry

structure SelectionDisplacement (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (ε : ℝ) extends SelectionTori d f (selectionAdapted d ε) where
  displacement : ∀ b ∈ Kinf, ∀ θ, ‖defect b θ‖ ≤ selectionDelta d ε
  angle_displacement : ∀ b ∈ Kinf, ∀ θ, ‖(defect b θ).1‖ ≤
    3 * (d.strip / 24) * selectionQ₀ (selectionAdapted d ε) / selectionCQ n
  action_displacement : ∀ b ∈ Kinf, ∀ θ, ‖(defect b θ).2‖ ≤
    (selectionAdapted d ε).s₀ * selectionQ₀ (selectionAdapted d ε) / 16
  delta_small : selectionDelta d ε ≤ selectionQ₀ (selectionAdapted d ε) / 128
  delta_absolute : selectionDelta d ε ≤ (2 : ℝ)⁻¹ ^ 18
  delta_power : selectionDelta d ε ≤ selectionCDelta d * Real.sqrt ε / selectionGamma d

theorem displacement (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) : Nonempty (SelectionDisplacement d f ε) := sorry

structure SelectionLipschitz (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (ε : ℝ) extends SelectionDisplacement d f ε where
  lipschitz_separate : ∀ b ∈ Kinf, ∀ b' ∈ Kinf, ∀ θ θ',
    ‖defect b θ - defect b' θ'‖ ≤
      (2 : ℝ)⁻¹ ^ 11 * ‖θ - θ'‖ + (2 : ℝ)⁻¹ ^ 11 * ‖b - b'‖
  lipschitz_joint : ∀ b ∈ Kinf, ∀ b' ∈ Kinf, ∀ θ θ',
    ‖defect b θ - defect b' θ'‖ ≤ (2 : ℝ)⁻¹ ^ 10 * ‖((θ, b) : Phase n) - (θ', b')‖

theorem lipschitz_family (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) : Nonempty (SelectionLipschitz d f ε) := sorry

def selectionHalfCell (H : Set (SelectionR n)) : Set (Phase n) :=
  {z | z.2 ∈ H ∧ ∀ i, z.1 i ∈ Ico (0 : ℝ) 1}
def selectionClosedCell (H : Set (SelectionR n)) : Set (Phase n) :=
  {z | z.2 ∈ H ∧ ∀ i, z.1 i ∈ Icc (0 : ℝ) 1}
def selectionQuotient (z : Phase n) : (Fin n → AddCircle (1 : ℝ)) × SelectionR n :=
  (fun i => (z.1 i : AddCircle (1 : ℝ)), z.2)

/-- Joint final output: the same chain, frequencies and family satisfy all clauses. -/
structure SelectionEvaluationOutput (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (ε : ℝ) extends SelectionLipschitz d f ε where
  bilipschitz : ∀ b ∈ Kinf, ∀ b' ∈ Kinf, ∀ θ θ',
    (1 - (2 : ℝ)⁻¹ ^ 10) * ‖((θ, b) : Phase n) - (θ', b')‖ ≤
      ‖selectionEvaluation defect b θ - selectionEvaluation defect b' θ'‖ ∧
    ‖selectionEvaluation defect b θ - selectionEvaluation defect b' θ'‖ ≤
      (1 + (2 : ℝ)⁻¹ ^ 10) * ‖((θ, b) : Phase n) - (θ', b')‖
  inverse_bound : ∀ b ∈ Kinf, ∀ b' ∈ Kinf, ∀ θ θ',
    ‖((θ, b) : Phase n) - (θ', b')‖ ≤ (1 - (2 : ℝ)⁻¹ ^ 10)⁻¹ *
      ‖selectionEvaluation defect b θ - selectionEvaluation defect b' θ'‖
  extension : Phase n → Phase n
  extension_eq : ∀ z : Phase n, z.2 ∈ Kinf → extension z = selectionEvaluation defect z.2 z.1
  extension_bijective : Bijective extension
  extension_defect_lip : ∀ z z',
    ‖(extension z - z) - (extension z' - z')‖ ≤ (2 : ℝ)⁻¹ ^ 10 * ‖z - z'‖
  image_closed_union : ∀ H : Set (SelectionR n), IsCompact H → H ⊆ Kinf →
    ∃ C : ℕ → Set (Phase n), (∀ j, IsClosed (C j)) ∧
      (fun z : Phase n => selectionEvaluation defect z.2 z.1) '' selectionHalfCell H = ⋃ j, C j
  image_fsigma : ∀ H : Set (SelectionR n), IsCompact H → H ⊆ Kinf →
    IsSigmaCompact ((fun z : Phase n => selectionEvaluation defect z.2 z.1) '' selectionHalfCell H)
  image_measurable : ∀ H : Set (SelectionR n), IsCompact H → H ⊆ Kinf →
    MeasurableSet ((fun z : Phase n => selectionEvaluation defect z.2 z.1) '' selectionHalfCell H)
  measure_lower : ∀ H : Set (SelectionR n), IsCompact H → H ⊆ Kinf →
    ENNReal.ofReal ((1 - (2 : ℝ)⁻¹ ^ 10) ^ (2 * n)) * volume H ≤
      volume ((fun z : Phase n => selectionEvaluation defect z.2 z.1) '' selectionHalfCell H)
  measure_coarse : ∀ H : Set (SelectionR n), IsCompact H → H ⊆ Kinf →
    ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (2 * n)) * volume H ≤
      volume ((fun z : Phase n => selectionEvaluation defect z.2 z.1) '' selectionHalfCell H)
  measure_upper : ∀ H : Set (SelectionR n), IsCompact H → H ⊆ Kinf →
    volume ((fun z : Phase n => selectionEvaluation defect z.2 z.1) '' selectionHalfCell H) ≤
      ENNReal.ofReal ((1 + (2 : ℝ)⁻¹ ^ 10) ^ (2 * n)) * volume H
  closed_image_compact : ∀ H : Set (SelectionR n), IsCompact H → H ⊆ Kinf →
    IsCompact ((fun z : Phase n => selectionEvaluation defect z.2 z.1) '' selectionClosedCell H)
  lattice_union : ∀ H : Set (SelectionR n), H ⊆ Kinf →
    (fun z : Phase n => selectionEvaluation defect z.2 z.1) '' {z | z.2 ∈ H} =
      ⋃ k : Fin n → ℤ, (fun z : Phase n => z + ((fun i => (k i : ℝ)), 0)) ''
        ((fun z : Phase n => selectionEvaluation defect z.2 z.1) '' selectionClosedCell H)
  quotient_compact : ∀ H : Set (SelectionR n), IsCompact H → H ⊆ Kinf →
    IsCompact (selectionQuotient ''
      ((fun z : Phase n => selectionEvaluation defect z.2 z.1) '' {z | z.2 ∈ H}))

theorem evaluation_bilipschitz (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) : Nonempty (SelectionEvaluationOutput d f ε) := sorry

/-- Source situation is output packaging, not a new standing-assumption structure. -/
def situation (d : SelectionData n) (f : SelectionPhaseC n → ℂ) (ε : ℝ) :=
  SelectionEvaluationOutput d f ε

/-- Only geometric/numerical data, including actual M₀, are fixed; h and beta vary. -/
def selectionFixedKey (d : SelectionData n) :=
  (d.μ, d.ρ, d.τ, d.ϑ, d.strip, d.C₁, d.M, d.loss, d.K, selectionM₀ d)
def selectionBetaExponent (d : SelectionData n) : ℝ :=
  2 * max (2 * (((d.μ : ℝ) + 1) / d.ρ))
    (1 + d.μ * (((d.μ : ℝ) + 1) / d.ρ))

/-- c_* chosen BEFORE varying h, beta, epsilon and f with the same numerical/geometric key. -/
theorem adm_budget_beta (d₀ : SelectionData n) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : SelectionData n,
      selectionFixedKey d = selectionFixedKey d₀ → d.β ≤ 1 →
      c * d.β ^ selectionBetaExponent d ≤ selectionAdmissible d := sorry

/-- Both K5 and K6, with one family witness and constants uniform in h, beta, epsilon and f at fixed key. -/
theorem displacement_power (d₀ : SelectionData n) :
    ∃ cD cstar : ℝ, 0 < cD ∧ 0 < cstar ∧ ∀ d : SelectionData n,
      selectionFixedKey d = selectionFixedKey d₀ → d.β ≤ 1 →
      cstar * d.β ^ selectionBetaExponent d ≤ selectionAdmissible d ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ selectionAdmissible d →
      ∀ f : SelectionPhaseC n → ℂ, SelectionPerturbation d f ε →
      ∃ o : SelectionEvaluationOutput d f ε,
        ∀ b ∈ o.Kinf, ∀ θ, ‖o.defect b θ‖ ≤
          cD * Real.sqrt ε * d.β ^ (-((d.μ : ℝ) + 1) / d.ρ) := sorry

/-- Rates of the eight actual inputs, in the order of adm-budget. -/
structure SelectionRates where
  theta : ℝ
  strip : ℝ
  beta : ℝ
  loss : ℝ
  M : ℝ
  M₀ : ℝ
  C₁ : ℝ
  diam : ℝ
  nonneg : 0 ≤ theta ∧ 0 ≤ strip ∧ 0 ≤ beta ∧ 0 ≤ loss ∧
    0 ≤ M ∧ 0 ≤ M₀ ∧ 0 ≤ C₁ ∧ 0 ≤ diam

def selectionBudgetD (n μ : ℕ) (r : SelectionRates) : ℝ :=
  n * r.diam + r.M + r.theta + (1 + (μ : ℝ)⁻¹) * r.beta
def selectionBudgetG (n μ ρ : ℕ) (r : SelectionRates) : ℝ :=
  max (r.beta / ρ) ((μ : ℝ) / ρ * (r.loss + selectionBudgetD n μ r))
def selectionBudgetL (r : SelectionRates) : ℝ := if r.strip = 0 then 0 else r.strip + 1
def selectionBudgetJ (n μ ρ : ℕ) (τ : ℝ) (r : SelectionRates) : ℝ :=
  max r.theta (selectionBudgetG n μ ρ r + (τ + 1) * selectionBudgetL r + r.C₁)
def selectionBudgetX (n μ ρ : ℕ) (τ : ℝ) (r : SelectionRates) : ℝ :=
  max (selectionBudgetJ n μ ρ τ r) (selectionBudgetL r)
def selectionBudgetH (n μ ρ : ℕ) (τ : ℝ) (r : SelectionRates) : ℝ :=
  max (selectionBudgetJ n μ ρ τ r)
    (max (selectionBudgetG n μ ρ r + (n + 1) * r.strip + τ * selectionBudgetL r +
      selectionBudgetX n μ ρ τ r) (r.beta + r.M₀ + μ * selectionBudgetJ n μ ρ τ r))
def selectionBudgetExponent (n μ ρ : ℕ) (τ : ℝ) (r : SelectionRates) : ℝ :=
  2 * selectionBudgetH n μ ρ τ r + r.C₁

/-- Input bounds on a family of data, not a smallness conclusion. -/
def selectionFamilyBounds (c u : ℝ) (r : SelectionRates) (d : SelectionData n) : Prop :=
  c * u ^ r.theta ≤ d.ϑ ∧ c * u ^ r.strip ≤ d.strip ∧
  c * u ^ r.beta ≤ d.β ∧ c * u ^ r.loss ≤ d.loss ∧
  d.M ≤ c⁻¹ * u ^ (-r.M) ∧ selectionM₀ d ≤ c⁻¹ * u ^ (-r.M₀) ∧
  d.C₁ ≤ c⁻¹ * u ^ (-r.C₁) ∧ Metric.diam d.K ≤ c⁻¹ * u ^ (-r.diam)

/-- Uniform coefficient depends on the strip rate but not the other seven rates. -/
theorem adm_budget (n μ ρ : ℕ) (τ c as_ : ℝ) (hn : 1 ≤ n) (hμ : 1 ≤ μ)
    (hρ : ρ = 1 ∨ ρ = 2) (hτ : 0 ≤ τ) (hgap : (n : ℝ) * μ / ρ - 1 < τ)
    (hc : 0 < c) (hc1 : c ≤ 1) (has : 0 ≤ as_) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ r : SelectionRates, r.strip = as_ →
      ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ d : SelectionData n,
        d.μ = μ → d.ρ = ρ → d.τ = τ → selectionFamilyBounds c u r d →
        c' * u ^ selectionBudgetExponent n μ ρ τ r ≤ selectionAdmissible d := sorry

end KAM.Planetary
end
```
