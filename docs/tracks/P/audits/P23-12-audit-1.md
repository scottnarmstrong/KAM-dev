# P23-12 independent package audit 1

Overall verdict: **PASS WITH NOTES** for `KAM.Planetary.nfb` and `KAM.Planetary.avg` as infrastructure exports. No frozen anchor is claimed or sealed by this package. Provider/frozen-type and seal-body checks are therefore **not applicable**; independent design-type probes are used instead. This is not P-G or track closure.

Audited HEAD: `73df68628b999ea56e6874df4b859cb21cd6c63e`. Read AGENTS.md, PLAN, DECISIONS, the shared package-audit brief, P23-12 handoff/AUDIT FOCUS, revision-2 design and both design audits, relevant track statement conventions, P2 blueprint L78–158, and the imported frozen carrier/domain definitions. User-specified report location and Finite-only scope override the generic brief's main-worktree output instruction.

`git diff inp...HEAD` reports multiple merge bases and selects `ef8fc426c638557035e6101216aad4ef8b8a570e`; current `inp` is `6e36995edb8c5fb4ee4ec0ed914f4a0c55a9b7f1`. Its delta contains these nine modules plus inherited `Splitting.lean`. The focused `git diff inp-p2310...HEAD -- 'KAM/Planetary/Averaging/Finite*.lean'` against `d0388702ed5b35de29cb47b7963d614a0f6cd9ff` has the same nine added modules, 1869 lines total. Unrelated inherited changes in the unfiltered second diff are outside this audit. The handoff's 1856-line total is a minor stale count; each actual file remains at most 310 lines.

## Findings and fidelity

No blocking proof, definition, source-premise or consumer-contract defect was found in the scoped modules.

1. **Exact targets.** Whitespace-normalized statement comparison with `/root/code/KAM-inp/.drafts/design/P23Signatures.lean` returns `True` for both `nfb` and `avg`. The shared signature SHA256 is `7d7dae4308ea9ec0ca763a2a21ce4b83280bdbb4b91d2c4f5e7567b71085e834`. Fresh declarations with these literal target signatures are independently elaborated by applying the exports with all binders, together with reverse `type_of%` checks. `NfbConcl` unfolds to the full `nfb` conjunction. `nfb_core` is stronger by its pointwise `E/(2πKs)` bound, not weaker. Source `sbar>0` is relaxed to nonnegative in the existing AvgHyp; this strengthens applicability. Constants remain absolute and the norm is the existing fixed-action summable Fourier norm, not a sum of suprema.
2. **No unpaid induction premise.** `IterSetup.step` is the scalar direct-step expression, not a bound on an unknown map or remainder. `setup_of_avg` is explicitly conditional numerical plumbing. `goodSched_single` and `goodSched_multi` prove those scalar inequalities, and `goodSched_of_avg` proves the existential budget from `AvgHyp`. `Inv`, `StepConc`, `GoodSched` and the conditional chain lemmas are separate construction interfaces; none is an extra premise of `nfb` or `avg`. Induction derives class, summable bounds and reality starting with `(0,f)`.
3. **Same-flow inherited contract.** `FiniteStep.lean:164–191` calls `direct_step`, `split`, `iterHyp_two`, and `iterative_direct_a`. The latter uses `p=2`, `α_N=2α/q`, and the same `homGen`, `iterMap` and loss domain; `ha.2.2.2.1` supplies the full integer-vector translation law. `FiniteChain.lean:154–224` uses the actual N `telescope`, not an assumed equivalent. Maps-to/domain nesting pays every composition, symplectic derivative, injectivity and three block-seminorm displacement application. Reality and lattice laws are additionally composed on these same witnesses.
4. **Two numerical cases.** For `κ=2πKs≥6`, `y₀≤3/(8κ)≤1/16`. Case B uses losses `(r/4,s/3)`, final radii `(r/2,sbar+s/3)`, and one actual step with remainder at most `exp(-κ/6)E`; the normal-form correction is zero. This includes `E=0`. Case A uses first losses `(r/8,s/6)`, then `N=floor(κ/(12 log 2))` steps with `(r/(8N),s/(4N))`. `steps_pos` excludes N=0 here, so all used denominators are positive. Remainder bounds are explicit upper bounds, `ε₁=3E/(4κ)` and `εᵢ₊₁=εᵢ/4`, not asserted equal to actual norms. `multi_eps_Q`, `multi_star_Q` and `exp_step_le` pay `δ≤Q/256`, star≤Q/16, and exponential tail≤1/8. `step_big` proves the resulting quarter contraction. Floor estimates give the final exponential bound; geometric sums give correction≤E/κ and displacement≤3E,3E,9E.
5. **Domains and widths.** Case A finishes at `(r/2,sbar+s/6)`; Case B has a larger strip, restricted explicitly. The zero-mode identification is asserted on the actual domain. `avg` uses `geometricWidth s=s/(2π)`, so `2πK geometricWidth s=Ks`; all action factors, angle factor `2πα₂r`, exponential, and pointwise action-neighborhood bounds survive conversion. No dimension-dependent norm change, global inverse or Lipschitz premise is introduced.

Minor notes:

- `Finite.lean:160`: `hstrict` is unused. The exact design signature already includes `AvgHyp.small`, sufficient for the proof; the blueprint `av-hyp` explains why the strict source inequality supplies it. This is a redundant approved premise, not a silently added premise or proof gap.
- `FiniteNumerics.lean:175` says “No steps are possible in case A” immediately before the theorem proving `1 ≤ N`. Its intended meaning is that **zero** steps are impossible in Case A. The theorem and its use are correct; only the docstring is misleading.

## Node coverage

| Node | Lean proof locator | Verdict | Reason |
|---|---|---|---|
| `stepP:p2:nfb-first` | `step_first`, `step_single`, `goodSched_single`, `goodSched_multi` | PASS | Both tail/quadratic regimes; source losses and smallness. |
| `stepP:p2:nfb-N` | `steps_lt`, `steps_le`, `steps_succ_gt`, `steps_pos`, `multiSched` | PASS WITH NOTES | N=0 routed through Case B; unreachable source subcase noted below. |
| `stepP:p2:nfb-ind` | `step_big`, `multi_star`, `multi_eps_Q`, `multi_star_Q`, `step_conc`, `inv_all` | PASS | Every numerical and analytic invariant proved. |
| `stepP:p2:nfb-concl` | `finite_struct`, `finite_ident`, `gen_tail`, `nfb_core` | PASS | Joint witnesses, zero-mode normal form, exponential and correction bounds. |
| `stepP:p2:nfb-disp` | `finite_disp`, `multi_disp_σ`, `multi_disp_ρ` | PASS | N telescope on first/last action and angle seminorms. |
| `bpP:p2:nfb` | `nfb` | PASS | Exact designed joint contract. |
| `stepP:p2:av-dict`, `stepP:p2:av-hyp` | `avg` | PASS WITH NOTES | Literal width dictionary; strict smallness redundant in approved bundle. |
| `bpP:p2:avg`, `bpP:p3:avg` | `avg` | PASS | Same witnesses and absolute constants; stronger 3E action bounds. |

## Every new public declaration and definition classification

All names below have prefix `KAM.Planetary.`. File locators are relative to `KAM/Planetary/Averaging/`. Rows for `def`, `abbrev` and `structure` classify every new definition. Public generated structure projections/constructors have their parent record's classification. The two private helpers in `FiniteGen` are class restriction and the zero-function summable bound; they are also covered by kernel replay.

| Node / role | Declaration (kind; file:line) | Verdict | Reason or definition classification |
|---|---|---|---|
| bpP:p2:nfb / bpP:p2:avg / bpP:p3:avg | `NfbConcl` (def; `Finite.lean:34`) | PASS | Literal nfb output conjunction; never an input of a source theorem. |
| bpP:p2:nfb / bpP:p2:avg / bpP:p3:avg | `goodSched_of_avg` (theorem; `Finite.lean:60`) | PASS | Exhaustive scalar case split; no construction assumption remains. |
| bpP:p2:nfb / bpP:p2:avg / bpP:p3:avg | `nfb_core` (theorem; `Finite.lean:68`) | PASS | Same witnesses as nfb plus the stronger pointwise E/κ bound. |
| bpP:p2:nfb / bpP:p2:avg / bpP:p3:avg | `nfb` (theorem; `Finite.lean:128`) | PASS | Exact design statement; full source-only construction and all 3/3/9 constants. |
| bpP:p2:nfb / bpP:p2:avg / bpP:p3:avg | `avg` (theorem; `Finite.lean:157`) | PASS WITH NOTES | Exact design statement; s/(2π) conversion; unused hstrict noted below. |
| nfb-N / nfb-ind / nfb-concl | `goodSched_multi` (theorem; `FiniteCaseA.lean:29`) | PASS | Proves every IterSetup field and output budget from H and numeric case split. |
| nfb-concl / nfb-disp | `Sched.Ψ` (def; `FiniteChain.lean:35`) | PASS | Upstream chain in the order Φ₀ ∘ ⋯ ∘ Φₘ. |
| nfb-concl / nfb-disp | `Sched.gI` (def; `FiniteChain.lean:39`) | PASS | Finite sum of actual zero Fourier coefficients, globally defined. |
| nfb-concl / nfb-disp | `chain_trans'` (theorem; `FiniteChain.lean:48`) | PASS | Conditional composition lemma; its lattice inputs are proved for the actual flow. |
| nfb-concl / nfb-disp | `chain_real` (theorem; `FiniteChain.lean:62`) | PASS | Conditional composition lemma; realness inputs proved at every stage. |
| nfb-concl / nfb-disp | `chain_ident` (theorem; `FiniteChain.lean:80`) | PASS | Conditional composition lemma; identities discharged definitionally. |
| nfb-concl / nfb-disp | `Sched.U` (abbrev; `FiniteChain.lean:105`) | PASS | Abbreviation of the actual weighted stage domain. |
| nfb-concl / nfb-disp | `U_succ_subset` (theorem; `FiniteChain.lean:108`) | PASS | Domain/seminorm adapter in the explicit finite composition. |
| nfb-concl / nfb-disp | `stage_mapsTo` (theorem; `FiniteChain.lean:113`) | PASS | Domain/seminorm adapter in the explicit finite composition. |
| nfb-concl / nfb-disp | `stage_sub_big` (theorem; `FiniteChain.lean:124`) | PASS | Domain/seminorm adapter in the explicit finite composition. |
| nfb-concl / nfb-disp | `semiFirst` (def; `FiniteChain.lean:134`) | PASS | Norm composed with first action block projection, a seminorm. |
| nfb-concl / nfb-disp | `semiLast` (def; `FiniteChain.lean:139`) | PASS | Norm composed with last action block projection, a seminorm. |
| nfb-concl / nfb-disp | `semiAngle` (def; `FiniteChain.lean:144`) | PASS | Norm composed with angle projection, a seminorm. |
| nfb-concl / nfb-disp | `semiFirst_apply` (theorem; `FiniteChain.lean:147`) | PASS | Domain/seminorm adapter in the explicit finite composition. |
| nfb-concl / nfb-disp | `semiLast_apply` (theorem; `FiniteChain.lean:149`) | PASS | Domain/seminorm adapter in the explicit finite composition. |
| nfb-concl / nfb-disp | `semiAngle_apply` (theorem; `FiniteChain.lean:151`) | PASS | Domain/seminorm adapter in the explicit finite composition. |
| nfb-concl / nfb-disp | `finite_struct` (theorem; `FiniteChain.lean:154`) | PASS | Actual N telescope plus separately proved lattice/reality composition. |
| nfb-concl / nfb-disp | `finite_ident` (theorem; `FiniteChain.lean:183`) | PASS | Telescopes definitional Hamiltonian identities on maps-to domains. |
| nfb-concl / nfb-disp | `finite_disp` (theorem; `FiniteChain.lean:199`) | PASS | Actual N telescope applied to all three block seminorms. |
| nfb-concl (b) | `S_pos_succ` (theorem; `FiniteGen.lean:41`) | PASS | Positive widths, domain nesting, coefficient holomorphy or finite-sum bound. |
| nfb-concl (b) | `S_pos_le` (theorem; `FiniteGen.lean:45`) | PASS | Positive widths, domain nesting, coefficient holomorphy or finite-sum bound. |
| nfb-concl (b) | `R_final_le` (theorem; `FiniteGen.lean:51`) | PASS | Positive widths, domain nesting, coefficient holomorphy or finite-sum bound. |
| nfb-concl (b) | `S_final_le` (theorem; `FiniteGen.lean:55`) | PASS | Positive widths, domain nesting, coefficient holomorphy or finite-sum bound. |
| nfb-concl (b) | `G_eq_gI` (theorem; `FiniteGen.lean:59`) | PASS | Zero-mode equality on final domain; no unsupported global identification. |
| nfb-concl (b) | `gI_differentiable` (theorem; `FiniteGen.lean:72`) | PASS | Positive widths, domain nesting, coefficient holomorphy or finite-sum bound. |
| nfb-concl (b) | `gI_real` (theorem; `FiniteGen.lean:82`) | PASS | Positive widths, domain nesting, coefficient holomorphy or finite-sum bound. |
| nfb-concl (b) | `tail_sum` (theorem; `FiniteGen.lean:89`) | PASS | Positive widths, domain nesting, coefficient holomorphy or finite-sum bound. |
| nfb-concl (b) | `gen_tail` (theorem; `FiniteGen.lean:117`) | PASS | Finite later-mode sum, class and WBound including summability. |
| nfb-N / nfb-ind / nfb-disp | `multiSched` (def; `FiniteMulti.lean:29`) | PASS | Explicit first/subsequent losses; N>0 is proved before analytic use. |
| nfb-N / nfb-ind / nfb-disp | `multi_ρ_zero` (theorem; `FiniteMulti.lean:37`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multi_σ_zero` (theorem; `FiniteMulti.lean:39`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multi_ρ_succ` (theorem; `FiniteMulti.lean:41`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multi_σ_succ` (theorem; `FiniteMulti.lean:44`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multi_R_zero` (theorem; `FiniteMulti.lean:47`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multi_S_zero` (theorem; `FiniteMulti.lean:49`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multi_R_closed` (theorem; `FiniteMulti.lean:51`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multi_S_closed` (theorem; `FiniteMulti.lean:59`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multiEps` (def; `FiniteMulti.lean:68`) | PASS | Explicit scalar upper bounds; positive κ guards every estimate. |
| nfb-N / nfb-ind / nfb-disp | `multiEps_zero` (theorem; `FiniteMulti.lean:70`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multiEps_succ` (theorem; `FiniteMulti.lean:72`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multiEps_nonneg` (theorem; `FiniteMulti.lean:75`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multi_weight_tail` (theorem; `FiniteMulti.lean:80`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multi_weight_head` (theorem; `FiniteMulti.lean:90`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multi_star` (theorem; `FiniteMulti.lean:102`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multi_E_N` (theorem; `FiniteMulti.lean:180`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multi_eps_Q` (theorem; `FiniteMulti.lean:188`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multi_star_Q` (theorem; `FiniteMulti.lean:215`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multi_tail_sum` (theorem; `FiniteMulti.lean:244`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multi_n_eps` (theorem; `FiniteMulti.lean:255`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multi_disp_σ` (theorem; `FiniteMulti.lean:261`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-N / nfb-ind / nfb-disp | `multi_disp_ρ` (theorem; `FiniteMulti.lean:285`) | PASS | Explicit schedule formula, star weight, geometric sum or numeric budget estimate. |
| nfb-first / nfb-N / nfb-ind | `exp_one_gt_27` (theorem; `FiniteNumerics.lean:25`) | PASS | Pure real/natural arithmetic lemma; stated positivity and numeric inequalities suffice. |
| nfb-first / nfb-N / nfb-ind | `inv_one_sub_le` (theorem; `FiniteNumerics.lean:30`) | PASS | Pure real/natural arithmetic lemma; stated positivity and numeric inequalities suffice. |
| nfb-first / nfb-N / nfb-ind | `step_first` (theorem; `FiniteNumerics.lean:35`) | PASS | Pure real/natural arithmetic lemma; stated positivity and numeric inequalities suffice. |
| nfb-first / nfb-N / nfb-ind | `step_single` (theorem; `FiniteNumerics.lean:66`) | PASS | Pure real/natural arithmetic lemma; stated positivity and numeric inequalities suffice. |
| nfb-first / nfb-N / nfb-ind | `step_big` (theorem; `FiniteNumerics.lean:90`) | PASS | Pure real/natural arithmetic lemma; stated positivity and numeric inequalities suffice. |
| nfb-first / nfb-N / nfb-ind | `geom_quarter` (theorem; `FiniteNumerics.lean:113`) | PASS | Pure real/natural arithmetic lemma; stated positivity and numeric inequalities suffice. |
| nfb-first / nfb-N / nfb-ind | `steps_lt` (theorem; `FiniteNumerics.lean:123`) | PASS | Pure real/natural arithmetic lemma; stated positivity and numeric inequalities suffice. |
| nfb-first / nfb-N / nfb-ind | `steps_le` (theorem; `FiniteNumerics.lean:131`) | PASS | Pure real/natural arithmetic lemma; stated positivity and numeric inequalities suffice. |
| nfb-first / nfb-N / nfb-ind | `steps_succ_gt` (theorem; `FiniteNumerics.lean:137`) | PASS | Pure real/natural arithmetic lemma; stated positivity and numeric inequalities suffice. |
| nfb-first / nfb-N / nfb-ind | `exp_step_le` (theorem; `FiniteNumerics.lean:145`) | PASS | Pure real/natural arithmetic lemma; stated positivity and numeric inequalities suffice. |
| nfb-first / nfb-N / nfb-ind | `quarter_pow_lt` (theorem; `FiniteNumerics.lean:157`) | PASS | Pure real/natural arithmetic lemma; stated positivity and numeric inequalities suffice. |
| nfb-first / nfb-N / nfb-ind | `steps_pos` (theorem; `FiniteNumerics.lean:176`) | PASS WITH NOTES | Proves N≥1 from the Case A upper bound; docstring wording noted below. |
| nfb construction | `Sched` (structure; `FiniteSchedule.lean:29`) | PASS | Numeric schedule data only; admissibility supplied separately. |
| nfb construction | `Sched.R` (def; `FiniteSchedule.lean:38`) | PASS | Recursive subtraction of twice each action loss, on all natural stages. |
| nfb construction | `Sched.S` (def; `FiniteSchedule.lean:43`) | PASS | Recursive subtraction of twice each strip loss, on all natural stages. |
| nfb construction | `Sched.seq` (def; `FiniteSchedule.lean:50`) | PASS | Explicit upstream iterG/iterF recursion, initial (0,f); no selected/default stage. |
| nfb construction | `Sched.G` (def; `FiniteSchedule.lean:56`) | PASS | First projection of the explicit recursive pair. |
| nfb construction | `Sched.F` (def; `FiniteSchedule.lean:59`) | PASS | Second projection of the explicit recursive pair. |
| nfb construction | `Sched.Φ` (def; `FiniteSchedule.lean:63`) | PASS | Exact iterMap of current remainder on its stage domain. |
| nfb construction | `Sched.G_zero` (theorem; `FiniteSchedule.lean:69`) | PASS | Recursive equations or monotonicity with explicit loss-sign premises. |
| nfb construction | `Sched.F_zero` (theorem; `FiniteSchedule.lean:71`) | PASS | Recursive equations or monotonicity with explicit loss-sign premises. |
| nfb construction | `Sched.G_succ` (theorem; `FiniteSchedule.lean:73`) | PASS | Recursive equations or monotonicity with explicit loss-sign premises. |
| nfb construction | `Sched.F_succ` (theorem; `FiniteSchedule.lean:76`) | PASS | Recursive equations or monotonicity with explicit loss-sign premises. |
| nfb construction | `Sched.R_succ` (theorem; `FiniteSchedule.lean:80`) | PASS | Recursive equations or monotonicity with explicit loss-sign premises. |
| nfb construction | `Sched.S_succ` (theorem; `FiniteSchedule.lean:82`) | PASS | Recursive equations or monotonicity with explicit loss-sign premises. |
| nfb construction | `Sched.R_anti` (theorem; `FiniteSchedule.lean:84`) | PASS | Recursive equations or monotonicity with explicit loss-sign premises. |
| nfb construction | `Sched.S_anti` (theorem; `FiniteSchedule.lean:92`) | PASS | Recursive equations or monotonicity with explicit loss-sign premises. |
| nfb construction | `Sched.G_eq_sum` (theorem; `FiniteSchedule.lean:101`) | PASS | Recursive equations or monotonicity with explicit loss-sign premises. |
| nfb construction | `homRes_zero` (theorem; `FiniteSchedule.lean:119`) | PASS | Projection/truncation gives zero coefficient on actual domain; K≥0 includes mode zero. |
| nfb construction | `homRes_stage` (theorem; `FiniteSchedule.lean:135`) | PASS | Class, norm and conditional reality from full homological_direct. |
| nfb construction | `iterHyp_two` (theorem; `FiniteSchedule.lean:151`) | PASS | Exact N substitution p=2, α_N=2α/q; no Lipschitz premise. |
| nfb-first / nfb-N | `GoodSched` (def; `FiniteSetup.lean:33`) | PASS | Existential intermediate budget, proved from AvgHyp by goodSched_of_avg. |
| nfb-first / nfb-N | `E_le_kappa` (theorem; `FiniteSetup.lean:53`) | PASS | Scalar smallness/budget adapter; conditional interface, not a replacement source theorem. |
| nfb-first / nfb-N | `y_le` (theorem; `FiniteSetup.lean:64`) | PASS | Scalar smallness/budget adapter; conditional interface, not a replacement source theorem. |
| nfb-first / nfb-N | `setup_of_avg` (theorem; `FiniteSetup.lean:73`) | PASS | Scalar smallness/budget adapter; conditional interface, not a replacement source theorem. |
| nfb-first / nfb-N | `goodSched_single` (theorem; `FiniteSetup.lean:98`) | PASS | Doubled losses; zero later correction; E=0 and N=0 regime included. |
| nfb-ind | `IterSetup` (structure; `FiniteStep.lean:31`) | PASS | Conditional source/numerical interface; step field is scalar arithmetic proved in both cases. |
| nfb-ind | `Inv` (def; `FiniteStep.lean:56`) | PASS | Named induction invariant; proved by inv_all, not assumed by nfb/avg. |
| nfb-ind | `StepConc` (structure; `FiniteStep.lean:63`) | PASS | Output record, constructed by step_conc; conditional chain input only. |
| nfb-ind | `twoDiv_mono` (theorem; `FiniteStep.lean:98`) | PASS | Domain restriction/divisor adapter or stage invariant helper; all inputs discharged. |
| nfb-ind | `setting_of_twoDiv` (theorem; `FiniteStep.lean:102`) | PASS | Domain restriction/divisor adapter or stage invariant helper; all inputs discharged. |
| nfb-ind | `R_le_start` (theorem; `FiniteStep.lean:112`) | PASS | Domain restriction/divisor adapter or stage invariant helper; all inputs discharged. |
| nfb-ind | `S_le_start` (theorem; `FiniteStep.lean:116`) | PASS | Domain restriction/divisor adapter or stage invariant helper; all inputs discharged. |
| nfb-ind | `R_pos` (theorem; `FiniteStep.lean:120`) | PASS | Domain restriction/divisor adapter or stage invariant helper; all inputs discharged. |
| nfb-ind | `S_pos` (theorem; `FiniteStep.lean:125`) | PASS | Domain restriction/divisor adapter or stage invariant helper; all inputs discharged. |
| nfb-ind | `directHyp_stage` (theorem; `FiniteStep.lean:130`) | PASS | Domain restriction/divisor adapter or stage invariant helper; all inputs discharged. |
| nfb-ind | `inv_zero` (theorem; `FiniteStep.lean:144`) | PASS | Domain restriction/divisor adapter or stage invariant helper; all inputs discharged. |
| nfb-ind | `step_conc` (theorem; `FiniteStep.lean:147`) | PASS | direct_step, split and iterative_direct_a use the same iterMap; step bound discharged numerically. |
| nfb-ind | `inv_all` (theorem; `FiniteStep.lean:194`) | PASS | Induction proves every required remainder class/bound/reality assertion. |

These definitions represent the intended objects on their full carriers: arbitrary numeric schedules remain numeric data even outside admissible ranges, and analytic assertions are guarded by `IterSetup`/positive-case hypotheses. `multiSched` at N=0 has Lean's total division behavior, but the construction never invokes its analytic estimates there. There is no arbitrary selected stage or fallback map. `StepConc` is a conclusion record, explicitly proved before use; `GoodSched`/`NfbConcl` name intermediate/terminal propositions, not source assumptions. `WBound` retains `WSummable`, preventing reliance on junk-zero infinite sums. Definitions are exposed by `@[expose] public noncomputable section`.

## Independent validation

All Lean-related invocations were serialized in this audit and inherited `LEAN_NUM_THREADS=1`; all ran under `nice -n 5`. No resource-budget override, clean/cache/update, full rebuild or generated-root regeneration was used.

### Targeted build — exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2312 KAM.Planetary.Averaging.Finite
```

Output (warning hint omitted):

```text
[inp-gate] slot 2 acquired 08:46:20 for KAM.Planetary.Averaging.Finite
⚠ [9138/9138] Replayed KAM.Planetary.Averaging.Finite
warning: KAM/Planetary/Averaging/Finite.lean:160:5: Variable name `hstrict` is not explicitly referenced.
Build completed successfully (9138 jobs).
```

### Exact design-type checks and every public theorem's axioms — exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2312Audit.lean
```

The probe imported `KAM.Planetary.Averaging.Finite`. It copied the **entire** `nfb` and `avg` target signatures from the shared design under fresh names `audit_nfb`, `audit_avg`, with bodies:

```lean
-- Full target binders and conclusions are copied verbatim before these bodies.
by exact @KAM.Planetary.nfb a b D r sbar s K α₁ α₂ E h f H
by exact @KAM.Planetary.avg a b D r sbar s K α₁ α₂ E h f H hstrict
-- The probe also checks the reverse assignment.
example : type_of% @audit_nfb := @KAM.Planetary.nfb
example : type_of% @audit_avg := @KAM.Planetary.avg
```

Both fresh declarations and both examples elaborated without errors or warnings. Full statement extraction stops at the theorem proof delimiter (`:= by` / `:= sorry`), retaining the conclusion's `let V := ...`. Python whitespace-normalized equality returned:

```text
nfb FULL whitespace-normalised signature equal: True signature lines: 23
avg FULL whitespace-normalised signature equal: True signature lines: 20
```

The same probe ran `#print axioms` once for each of the 85 inventoried public theorem declarations. Exact output follows; all 85 use exactly the permitted three axioms, with no `sorryAx`:

```text
'KAM.Planetary.goodSched_of_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.nfb_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.nfb' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.goodSched_multi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chain_trans'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chain_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chain_ident' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.U_succ_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stage_mapsTo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stage_sub_big' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.semiFirst_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.semiLast_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.semiAngle_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.finite_struct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.finite_ident' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.finite_disp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.S_pos_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.S_pos_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.R_final_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.S_final_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.G_eq_gI' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.gI_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.gI_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tail_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.gen_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_ρ_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_σ_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_ρ_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_σ_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_R_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_S_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_R_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_S_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multiEps_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multiEps_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multiEps_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_weight_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_weight_head' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_star' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_E_N' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_eps_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_star_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_tail_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_n_eps' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_disp_σ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_disp_ρ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exp_one_gt_27' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.inv_one_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.step_first' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.step_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.step_big' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.geom_quarter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.steps_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.steps_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.steps_succ_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exp_step_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.quarter_pow_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.steps_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Sched.G_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Sched.F_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Sched.G_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Sched.F_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Sched.R_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Sched.S_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Sched.R_anti' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Sched.S_anti' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Sched.G_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.homRes_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.homRes_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iterHyp_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.E_le_kappa' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.y_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.setup_of_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.goodSched_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.twoDiv_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.setting_of_twoDiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.R_le_start' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.S_le_start' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.R_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.S_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.directHyp_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.inv_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.step_conc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.inv_all' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay — exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.Finite KAM.Planetary.Averaging.FiniteSchedule KAM.Planetary.Averaging.FiniteStep KAM.Planetary.Averaging.FiniteChain KAM.Planetary.Averaging.FiniteGen KAM.Planetary.Averaging.FiniteNumerics KAM.Planetary.Averaging.FiniteSetup KAM.Planetary.Averaging.FiniteMulti KAM.Planetary.Averaging.FiniteCaseA
```

Exact output:

```text
replaying KAM.Planetary.Averaging.FiniteCaseA
replaying KAM.Planetary.Averaging.FiniteMulti
replaying KAM.Planetary.Averaging.FiniteSetup
replaying KAM.Planetary.Averaging.FiniteNumerics
replaying KAM.Planetary.Averaging.FiniteGen
replaying KAM.Planetary.Averaging.FiniteChain
replaying KAM.Planetary.Averaging.FiniteStep
replaying KAM.Planetary.Averaging.FiniteSchedule
replaying KAM.Planetary.Averaging.Finite
```

### Source lint — exit 1, solely the permitted generated-root exception

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (476 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The handoff's claimed lint exit 0 is **not reproduced**: the current script propagates the stale-root check as exit 1. The generic audit brief explicitly permits this sole message. No other lint failure occurs; in particular the current lint includes the 100-character limit. The root is left untouched as required.

### Imports, file hygiene and repository integrity

- Recursive `KAM.*` import scan: 92 modules; 12 frozen definition modules; **zero provider imports and zero frozen theorem imports**, hence no imported DRAFT_SORRY theorem or theorem manifest-state exception. Imported carrier/domain definitions preserve `Fin n → ℂ`, frozen real phase order, first/last blocks and the literal action neighborhood. No new instance is declared.
- Scoped token scan: no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option`. Every scoped file has the copyright header, `module`, public imports, module docstring and exposed public noncomputable section.
- Independent Unicode-character line scan: **zero lines over 100 characters** in the nine modules. Actual line counts: Finite 226; FiniteCaseA 161; FiniteChain 227; FiniteGen 143; FiniteMulti 310; FiniteNumerics 196; FiniteSchedule 191; FiniteSetup 201; FiniteStep 214. No 1500-line violation.
- `git diff --exit-code inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty diff (only the already-disclosed merge-base warning).
- `git diff --check inp...HEAD`: exit 0, no whitespace errors (same merge-base warning). `git diff --check`: exit 0, no output.
- Report inventory validation: all **105** public declaration rows occur exactly once, including all 20 explicit definitions/structures/abbreviations; all **85** axiom result names match the theorem inventory. Final report whitespace/path and scratch-cleanup checks pass.

## Suspected blueprint/source defects and deviations

- `blueprint-P/parts/p2-averaging.tex:105–107`: after “From now on Case A”, the proof discusses “If N=0”. Case A entails `exp(-κ/6)≤y₀≤1/16`, hence `κ≥24 log 2` and N≥2. Thus this is an unreachable branch, not a counterexample to the theorem or an unpaid case. Lean proves N≥1, which suffices for all divisions, and handles the actual N=0 regime using Case B. This confirms the handoff's editorial observation, not a false source theorem.
- `blueprint-P/parts/p2-averaging.tex:115`: “weight ≤ ½(⅓+⅓) ≤ ½” is true (its intermediate value is ⅓). Lean retains the sharper ⅓. This is **not** an erratum or gap.
- No new suspected defect in a pinned original PDF is asserted. This audit checks the local blueprint/design and Lean package; inherited CP10 reports are not reverified against the PDF here.
- Disclosed implementation differences: recursive `Gᵢ` starts at zero (blueprint `g₀` names the first zero-mode increment); equality is proved on-domain by `G_eq_gI`. Numeric ε values are upper bounds. Single-step Case B also handles N=0. Source conclusions, laws, norms and constants are preserved. No production repair was made.

## Handoff boundary

Only this report is added by the auditor. The pre-existing untracked `P23-12-handoff.md` is preserved. Scratch probes are deleted after validation. No frozen/manifest/generated file was edited and no git state-changing command was run. Validation is independent of the prover's receipts. Upstream P23-10/P23-02 and N theorem bodies are reused; this is a focused package audit, not a new audit of all their source proofs or a seal of P-G.
