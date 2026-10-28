# GAP-B independent package audit 1

Verdict: **PASS WITH NOTES**. `stepP:p11a:es-3` is proved with its literal graph conclusion, under exactly the hypotheses of B13's `exported_sums`. Both the intermediate collar-tail chain and the real tail `≤ 2⁻¹²` are exported. All E1–E4 steps of `bpP:p11a:exported-sums` now have established declarations in this checkout, with E4 supplied by the constructed iteration and B10's Cauchy helper. This is infrastructure/graph-step coverage, not a frozen headline theorem seal.

## Scope and frozen inputs

Focused, tier-2, refute-first audit. Implementation audited: **only** `KAM/Planetary/WeakKAM/BudgetsTail.lean`; baseline modules inspected as dependencies and to check E1–E4 consumption. Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package brief, track-P statement conventions, P11B design/signatures, the handoff AUDIT FOCUS, graph contracts and blueprint source before the correspondence verdict.

Snapshot `frozen-v1`:

- HEAD: `280b5f15ed56e05074d580ff4e91db1c4c9266c7`.
- `inp`: `6671aafcf7763b616da28e69340b403fb2cc9121`.
- Full `git diff inp...HEAD`: one added file, 165 lines, `KAM/Planetary/WeakKAM/BudgetsTail.lean`.
- Implementation SHA256: `dd01a421a1f504c05f369b07e9d27950c99fcad48c698da8da5b0603d2b93990`.
- `docs/graph/P/DEPGRAPH.md`: `728136a5a4a0a6b3e16810a9b9863812bbf033fff74fc741937d377735088c34`.
- `blueprint-P/parts/p11a3-iteration-selection.tex`: `90251ed2045353dd2c9574b5f2c53588eb5762ea9dbc86ed9075c00bf8d9ad1c`.
- `docs/tracks/P/design/P11B-LEAN-DESIGN.md`: `b39ec4a5b9b976b355d6afe26047680ea2b1fbb1c86dd4073aa4428528961ea1`.
- `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean`: `e5ae0f3f6c134280acd184e6130e2c39bac49485097647cd36f52f7dbf87ef63`.

Closeout snapshot: HEAD and every hashed audited/source file remain unchanged. The shared `inp` ref advanced during the audit to `ec684b4ea4834e74ead53a406d997d653377ac3d`; the final `git merge-base inp HEAD` is `a2c95a9339a7bf00c88b45ff27058eaa6f5b3be9`. Repeating the full three-dot comparison still gives exactly the same single 165-line addition and an empty protected-path diff. This external ref movement changes no audited bytes or verdict.

Decision: the user's explicit absolute report path overrides the generic brief's main-worktree output instruction. Only this report and temporary `.lake/abi-scratch/` audit files were written. No production repairs, graph updates, commits, root regeneration, or frozen edits. No subagents. All audit Lean/Lake commands ran sequentially with `LEAN_NUM_THREADS=1` and `nice -n 5`.

## Declaration and coverage ledger

All names below have namespace `KAM.Planetary`.

| Node / role | Declaration and locator | Verdict | Evidence |
|---|---|---|---|
| E3 helper | `wbudtail_quot`, BudgetsTail:31 | PASS | Uniform collar-tail quotient ≤ `(32/31)(cA+cα)`; internal conditional context lemma, not substituted for the source export. |
| E3 context export | `exported_sums_es_3_ctx`, BudgetsTail:68 | PASS | Exact conjunction with intermediate `3 Q₀ Ξ/C_Q + Q₀ Ξ/16`, final `2⁻¹⁰`, and real tail `2⁻¹²`. |
| `stepP:p11a:es-3` | `exported_sums_es_3`, BudgetsTail:144 | PASS | Literal graph conclusion for `a := adm_params d ε`, all natural ν, same four explicit binders as B13; no iteration premise. |
| `stepP:p11a:es-1` | `exported_sums` clause 9; `wbud_stage` | PASS, baseline coverage | All five E1 clauses exported; geometric comparison to `2⁻⁵ν` follows from `wbud_ratios`. |
| `stepP:p11a:es-2` | `exported_sums` sum clauses; `wbud_nums`, `wbud_sums_Aα` | PASS, baseline coverage | Summability and four source unscaled budget conclusions supplied by B13. |
| `stepP:p11a:es-4` | `selection_iteration_parameter_first`, Iteration:117; `inductive_lemma`, Iteration:71 | PASS, baseline consumption | A fresh elaborated witness constructs the iteration and exports E4 on its half collar, weakening `max(A,α)` to `A+α` using proved nonnegativity. |
| `bpP:p11a:exported-sums` | Above E1–E4 exports together | PASS WITH NOTES | All four steps covered. B13's original `exported_sums` itself still omits E4 and E3's intermediate chain/real tail; coverage uses distinct exports, as the ruling requests. No monolithic replacement theorem or frozen seal is claimed. |

There are no new SIGNED declarations: all three new names are absent from the canonical signature file. Thus frozen/provider exact-type and seal-body probes are N/A, rather than presumed passed. The unsigned E3 export is checked against the literal graph/source conclusion, not a narrower signed interface. No other graph node is assigned to this append-only module by the GAP-B ruling. Other P11B packages and their earlier audit verdicts were not reopened.

## Statement fidelity and proof review

At DEPGRAPH:26172, the exact E3 contract is:

> `t_{nu+1}^-1 sum_{j>=nu}(A_{1,j}+A_{eta,j})<=3 Q_0 Xi/C_Q+Q_0 Xi/16<=2^-10 and sum_{j>=nu} Lambda_{R,j}<=2^-12`.

`exported_sums_es_3` has `{n : ℕ}`, `d : SelectionData n`, `ε : ℝ`, `he : 0 ≤ ε`, `hsmall : ε ≤ selectionAdmissible d`, followed by `let a := adm_params d ε; ∀ ν`. Constants are fixed before ν; none is existentially selected afterwards. `j+ν` enumerates every index in the tail once, including ν. Division by `selectiont a (ν+1)` is the inverse-times-sum convention; the fresh probe verifies this equivalent literal form. `(2 : ℝ)⁻¹ ^ k` is `2⁻ᵏ`. The sum binds both A and alpha. All quantities are the existing scalar schedules, not replacement maps or suprema. `varsigma₀ = a.strip/24`, `C_Q = 18 n (4 n+5)`, and the existing `selectionXi d` is used literally.

Proof checked line by line:

1. `wbudtail_quot` obtains actual summability of A, alpha and their weighted quotient before any tsum comparison. Positive collar widths and `t(j+ν+1) ≤ t(ν+1)` give the correct inequality direction for a nonnegative numerator. The shifted weighted tail is bounded by the full weighted sum; `wbud_lip_term` and the geometric summation theorem yield `(32/31)(cA+cα)`. This prevents the nonsummable-tsum default-zero loophole.
2. The context proof derives `s₀ ≤ t₀` from admissibility, `C_Q ≥ 162` from `n ≥ 1`, and uses the literal Xi lower bounds. It proves `cA ≤ 2 Q₀ Ξ/C_Q` and `cα ≤ Q₀ Ξ/32`. Nonnegativity justifies `64/31 ≤ 3` and `(32/31)/32 ≤ 1/16` in the displayed chain. `Q₀ Ξ ≤ 2⁻¹⁰` and `3/162+1/16 < 1` then prove the second conjunct.
3. For the real tail, the geometric domination proves summability and nonnegativity; the shifted tail is ≤ the full sum, which `wbud_nums` bounds by `2⁻¹²`. No claimed tail estimate is fed back as a hypothesis.
4. The public wrapper constructs its context from `adm_choice d ε he hsmall`; `s₀>0` and `ε₀>0` are proved internally. In particular ε=0 is allowed: `s₀` is fixed positive and `ε₀ = ε + n C₁ s₀²/2 > 0`. No ε>0 premise was silently added.

Adversarial checks targeted misplaced tsum scope, reversed collar comparison, hidden summability, ε=0, shifted endpoint, altered Xi, and a merely conditional E4. None refuted the package. The E4 probe obtains `o` directly from `inductive_lemma d ε he hsmall f hf`, proves the positive collar and A/alpha nonnegativity from the budget context, and applies `selection_iteration_parameter_first` to this exact `o`. Thus it does not assume the derivative estimate or a fabricated iteration. Its additional `f,hf` are precisely the source perturbation inputs needed for E4's maps, not extra premises of scalar E3.

## Binder classification

Five-bin test: SOURCE, STANDING, TYPING, RULED, EXCESS. Source locators are blueprint p11a3 `sel-data`, `parameter-selection`, `adm-params`, `adm-choice` (A1–A6), exported-sums:340–357; the GAP-B ruling permits exactly B13's export hypotheses. Structured inputs are expanded below. Data-valued fields are typing/standing-data parameters; proof-valued standing fields are STANDING. No instance parameters occur.

| Public export binder | Bin | Source / explanation |
|---|---|---|
| `{n : ℕ}` | TYPING | Source dimension; its positivity is in d. |
| `d : SelectionData n` | TYPING | Container expanded below, not a theorem conclusion. |
| `ε : ℝ` | TYPING | Source perturbation-size scalar. |
| `he : 0 ≤ ε` | SOURCE | Same as B13; source nonnegative size. |
| `hsmall : ε ≤ selectionAdmissible d` | SOURCE | Admissible selection threshold. |
| `ν : ℕ` (conclusion quantifier) | TYPING | Every nonnegative tail index. |

Counts before structure expansion: SOURCE 2, STANDING 0, TYPING 4 (including ν), RULED 0, EXCESS 0.

| Expanded `SelectionData` field | Bin | Source |
|---|---|---|
| `d.μ` | TYPING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.ρ` | TYPING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.τ` | TYPING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.ϑ` | TYPING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.strip` | TYPING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.C₁` | TYPING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.β` | TYPING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.M` | TYPING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.loss` | TYPING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.K` | TYPING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.h` | TYPING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.n_pos` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.μ_pos` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.rho_mem` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.tau_nonneg` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.tau_gap` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.compact` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.positive_measure` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.theta_pos` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.theta_le` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.strip_pos` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.strip_le` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.hessian_normalized` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.beta_pos` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.beta_le` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.loss_pos` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.loss_lt` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.holo` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.real` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.hessian` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.finite_type` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |
| `d.top_bounds` | STANDING | Literal fixed data / premise in `sel-data`; Data.lean:64–104. |

Expansion counts for d: TYPING 11, STANDING 21, SOURCE 0, RULED 0, EXCESS 0. No conclusion concerning exported sums, tail bounds, or iteration existence occurs in d.

For both context helpers the binders `{n}`, `{d}`, `{a : SelectionSchedule n}` and `ν` are typing data. `SelectionSchedule` has only the scalar fields μ, τ, γ, strip, T₀, t₀, s₀, ε₀; no logical field. `c : WeakBudgetCtx d a` is conditional bookkeeping, constructed in the source export's proof. Its fully expanded logical leaves are:

| Context leaf | Bin | Source / justification |
|---|---|---|
| `c.adm.t_pos` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.adm.t_le` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.adm.collar` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.adm.increment` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.adm.radius` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.adm.quadratic` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.adm.weighted` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.adm.closeness` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.adm.cutoff_ge` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.adm.cutoff_loss` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.hyp.hn` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.hyp.hμ` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.hyp.hτ` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.hyp.hγ` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.hyp.hT` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.hyp.ht` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.hyp.hs` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.hyp.he` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.hyp.hstrip` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.hyp.hstrip1` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.hyp.hloss` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.hyp.hC` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.hyp.inc` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.hyp.col` | STANDING | A1–A6 / schedule scalar conditions; produced by `adm_choice` and `weakBudgetHyp_of_adm`. |
| `c.hμ` | TYPING | Identifies schedule parameters with the fixed data formulas. |
| `c.hτ` | TYPING | Identifies schedule parameters with the fixed data formulas. |
| `c.hstrip` | TYPING | Identifies schedule parameters with the fixed data formulas. |
| `c.ht0` | TYPING | Identifies schedule parameters with the fixed data formulas. |
| `c.hT0` | TYPING | Identifies schedule parameters with the fixed data formulas. |

Context leaf counts: STANDING 24, TYPING 5, SOURCE 0, RULED 0, EXCESS 0 (in addition to the expanded fixed data). These are source scalar conditions and parameter identifications, not the E3 conclusion. The helper names remain distinct; the actual source-facing export has no context binder.

## Definitions and import hygiene

New `def`/`abbrev`/`structure`: **none**. Definition classification is N/A for GAP-B. Existing `selectionA`, `selectionAlpha`, `selectionRealBudget`, `selectiont`, `selectionQ₀`, `selectionXi`, `selectionCQ`, `selectionAdmissible`, and `adm_params` were inspected as literal source scalar formulas; no new fallback, choice or replacement carrier is introduced. They are baseline dependencies, not newly certified definition versions.

The direct import is `KAM.Planetary.WeakKAM.Budgets`. Recursive project import traversal found 66 KAM modules, zero provider imports and twelve frozen definitions, all manifest-state SEALED: ActionNbhd, ComplexStrip, FrequencyMap, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, RealHamiltonian, SymplecticForm, and Planetary/Phase. No frozen theorem or DRAFT_SORRY import is reachable. There is no provider or anchor in the GAP-B diff.

The new file has the copyright header, `module`, `public import`, module docstring, and exposed public noncomputable section. It has 165 lines, none longer than 100 characters. Forbidden-token/resource-override scan returned no matches. All three new declaration short names occur at exactly one declaration site in KAM; namespace `KAM.Planetary` introduces no root shadow. Ambient source types remain the existing Fin-function spaces.

## Verification evidence

The following commands were run sequentially from `/root/code/KAM-inp-gapb` (no audit build overlaps). The compile gate was used exactly as required:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gapb KAM.Planetary.WeakKAM.BudgetsTail
```

Exit **0**. Output: `[inp-gate] slot 2 acquired 23:20:57 for KAM.Planetary.WeakKAM.BudgetsTail`; `Build completed successfully (9112 jobs).` Replayed warnings were in baseline Schedule, CutoffTensor, CutoffScale, Cutoff, FourierCutoffTail, StripBudget and Admissible; no warning named BudgetsTail. No heartbeat override or compilation design failure occurred.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPBAudit1.lean
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPBE4Audit1.lean
```

Both exit **0**. First probe independently states the literal E3 inverse-times-sum type, proves it from the export, verifies weakening of the real tail to the parent lemma's `2⁻¹⁰`, prints the export and all new public theorem axioms. Second probe constructs the actual iteration and proves E4 with `A+alpha`. Exact probe sources appear below; both were deleted after verification.

Axiom output:

```text
'KAM.Planetary.wbudtail_quot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exported_sums_es_3_ctx' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exported_sums_es_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exported_sums' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_iteration_parameter_first' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.inductive_lemma' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.BudgetsTail
```

Exit **0**. Exact output: `replaying KAM.Planetary.WeakKAM.BudgetsTail`.

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the explicitly permitted generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1082 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No other lint finding. Generated files were left untouched.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check
```

Both exit **0**, no output. Protected paths unchanged. Starting untracked handoff was preserved; the only added repository artifact from this audit is this report.

## Source/documentation discrepancies and refutation disposition

1. **Nonblocking statement/proof strength discrepancy.** Blueprint p11a3:345 says the real tail is `≤2^{-10}`; p11a3:355 says `≤2^{-12} by (E2)`. DEPGRAPH:26172's E3 SOURCE_CONCLUSION requires `≤2^-12`, whereas the parent's SOURCE_CONCLUSION uses `≤2^-10`. Refutation check: E2 proves nonnegativity/summability and a full real sum ≤2⁻¹², hence the stronger tail; the fresh probe also derives the weaker parent conclusion. These statements are compatible, and GAP-B satisfies both. No false pinned-source claim is inferred.
2. **Stale graph status/note.** E3 remains `LEAN_STATUS: NOT_STARTED` and its note says `real tail ... <= 2^-10 is not a separate declaration`; the literal contract requires 2⁻¹² and the new export now provides it. The parent also remains NOT_STARTED. These statuses predate this append-only gap fill; no graph mutation was authorized. Orchestrator can update references following acceptance.
3. **Old design name mapping.** P11B design:102–103 names `exported_sums (local es_3)` and `(local es_4)`. Actual complete coverage uses `exported_sums_es_3` and `selection_iteration_parameter_first`, respectively, as the current GAP-B ruling and implementation direction specify. Refutation check: the declarations and consumption probes exist and elaborate; this is stale mapping prose, not missing proof content.

No new suspected analytic/source defect, added premise, deviation from the GAP-B ruling, or unresolved blocking finding. No independent re-audit of the whole B10/B13 implementation or physical headline theorem is claimed. Every GAP-B declaration is classified and verified; report-only scope was preserved.

## Reproducible scratch probes

### GAPBAudit1.lean

```lean
import KAM.Planetary.WeakKAM.BudgetsTail
import KAM.Planetary.WeakKAM.Iteration
open scoped BigOperators
open KAM KAM.Planetary
noncomputable section
variable {n : ℕ}
example (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) :
    let a := adm_params d ε
    ∀ ν : ℕ,
      (selectiont a (ν + 1))⁻¹ *
          (∑' j : ℕ, (selectionA a (j + ν) + selectionAlpha a (j + ν))) ≤
        3 * selectionQ₀ a * selectionXi d / selectionCQ n +
          selectionQ₀ a * selectionXi d / 16 ∧
      3 * selectionQ₀ a * selectionXi d / selectionCQ n +
          selectionQ₀ a * selectionXi d / 16 ≤ (2 : ℝ)⁻¹ ^ 10 ∧
      (∑' j : ℕ, selectionRealBudget a (j + ν)) ≤ (2 : ℝ)⁻¹ ^ 12 := by
  simpa only [div_eq_mul_inv, mul_comm] using exported_sums_es_3 d ε he hsmall
example (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) :
    let a := adm_params d ε
    ∀ ν : ℕ, (∑' j : ℕ, selectionRealBudget a (j + ν)) ≤ (2 : ℝ)⁻¹ ^ 10 := by
  intro a ν
  exact ((exported_sums_es_3 d ε he hsmall ν).2.2).trans (by norm_num)
#print KAM.Planetary.exported_sums_es_3
#print axioms KAM.Planetary.wbudtail_quot
#print axioms KAM.Planetary.exported_sums_es_3_ctx
#print axioms KAM.Planetary.exported_sums_es_3
#print axioms KAM.Planetary.exported_sums
#print axioms KAM.Planetary.selection_iteration_parameter_first
#check KAM.Planetary.inductive_lemma
```

### GAPBE4Audit1.lean

```lean
import KAM.Planetary.WeakKAM.Iteration
open KAM KAM.Planetary
noncomputable section
variable {n : ℕ}
example (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) :
    ∃ o : SelectionIteration d f (adm_params d ε), ∀ (ν : ℕ) (z : SelectionPhaseC n),
      z.1 ∈ complexStrip n (selectionr (adm_params d ε) (ν + 1)) →
      ‖z.2‖ < selections (adm_params d ε) (ν + 1) →
      ∀ b ∈ actionNbhd (o.K (ν + 1)) (selectiont (adm_params d ε) (ν + 1) / 2),
        ‖fderiv ℂ (fun c => o.X ν c z - z) b‖ ≤
          2 * (selectionA (adm_params d ε) ν + selectionAlpha (adm_params d ε) ν) /
            selectiont (adm_params d ε) (ν + 1) := by
  obtain ⟨o⟩ := inductive_lemma d ε he hsmall f hf
  obtain ⟨hA, -, hs, he0⟩ := selection_adm_facts d ε he hsmall
  let c := weakBudgetCtx_of d (adm_params d ε) hA rfl rfl rfl rfl rfl rfl hs he0
  refine ⟨o, ?_⟩
  intro ν z hz hη b hb
  have ht := wbud_t_pos c (ν + 1)
  obtain ⟨-, hA0, -, hκ0, -, hα, -⟩ := wbud_stage c.hyp ν
  have hs0 := wbud_s_pos c.hyp ν
  have hα0 : 0 ≤ selectionAlpha (adm_params d ε) ν := by rw [hα]; positivity
  refine (selection_iteration_parameter_first d f (adm_params d ε) o ν ht z hz hη b hb).trans ?_
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) (by norm_num)) ht.le
#print axioms KAM.Planetary.inductive_lemma
```

