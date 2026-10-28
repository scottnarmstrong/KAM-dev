# B03 independent package audit

Date: 2026-10-28. Worktree `/root/code/KAM-inp-p11b-b03`; HEAD `4e0f62fb`. Scope: **only** `KAM/Planetary/WeakKAM/StripBudget.lean` (382 lines).

## Verdict and scope

**Overall: PASS WITH NOTES (scoped B03 package).** `strip_budget` and `schedule_props`: **PASS**, complete and exactly signature-compatible. Both required P11A bridges and every public helper: **PASS**. Independent targeted build, signature/application probes, axiom checks and kernel replay succeed. Lint has only the expressly permitted stale generated-root failure. The additional whole-branch root difference is inherited rather than introduced by B03; see the comparison boundary below. No blocking B03 finding remains.

No frozen anchor is implemented or sealed by B03. Provider/frozen-type and frozen seal-body checks are therefore inapplicable. Instead, the two exact approved design signatures are checked using fresh declarations and full `@`-type assignments in an auditor-created scratch probe. This audit does not certify B04–B20, a constructed admissible schedule, an infinite iteration, or any physical theorem.

Read: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, `B03-handoff.md`, track-P statements, design row B03 and its node map/proof plans, both P11B design audits, B02 audit N1, the live signatures and blueprint `p11a3-iteration-selection.tex:45,69–136`. The user's exact report-path instruction overrides the generic brief's main-worktree destination. Only this report and temporary worktree-local ABI scratch files are written.

## Comparison boundary

The required `git diff inp...HEAD` warns:

```text
warning: inp...HEAD: multiple merge bases, using a74e96bc48beed5a651bb5312cf96f6e32f9794e
```

Its stat contains 34 files, including unrelated inherited additions and 14 added root imports. Thus the literal whole-branch protected-file emptiness condition is **not satisfied for `KAM.lean`**; this is recorded, not silently waived or repaired. `git diff inp...HEAD -- KAM/Frozen manifest README.md` is empty. Attribution checks `git show --stat c69b5f92`, `git show --stat 4e0f62fb`, and `git diff ddd66714..HEAD --name-only` show that both B03 commits change only `KAM/Planetary/WeakKAM/StripBudget.lean`; no B03 root/frozen/manifest/README edit exists. No state-changing git command was run. Initial untracked `B03-handoff.md` is preserved.

## Signature fidelity and completeness

Both theorem headers are byte-identical to `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean:179–220` and the corresponding design appendix. In particular, `strip_budget`'s `hμ : 1 ≤ a.μ` is signature-mandated, although unused in its proof. There is no added hypothesis or constant dependence. `schedule_props` retains every revised SC3 clause, including the derivative partial sum bounded by `C₁`.

The ownership row at design line 229 assigns exactly strip-budget and schedule-props. The node map at lines 49–59 gives all four sb steps and all five sp steps. The release-plan section at lines 276–296 contains no additional B03 construction obligation; downstream B10 consumes its strip/error and collar estimates. Both B02-N1 scalar bridges are exported here, before their use.

All names in the table are in `KAM.Planetary`. Lean line numbers refer to `StripBudget.lean`; source nodes have prefixes `bpP:p11a:` or `stepP:p11a:` as indicated.

| Node / obligation | Declaration / proof location | Verdict | Reason |
|---|---|---|---|
| B02 N1 constant bridge | `selectionCN_eq_p11C` L28 | PASS | Unconditional whole-carrier equality, proved by `rfl`. |
| B02 N1 cutoff bridge | `selectionCutoffError_eq_p11Error` L30 | PASS | Unconditional equality for every n,T,d; unfolds formulas and `inv_pow`. |
| schedule-consts positivity helper | `selectionVarpi_pos_le_one` L35 | PASS | τ≥0 implies exponent≥0 and 0<ϖ≤1; permits arbitrary natural n,μ. |
| schedule/loss bridge | `selectiond_eq_p11Loss` L45 | PASS | Exact equality at tolerance ϖ/8, with no schedule positivity premise. |
| bp y-log | private `n_log_le` L58 | PASS | `log_le_sub_one_of_pos` at sX/(32n), then logarithm product identity; drops the favorable −n. |
| bp strip-budget | `strip_budget` L74 | PASS | Exact signature; summability, total losses, widths, all radii and cutoff-error clauses. |
| step sb-sum | `strip_budget`, `hLS`, `hsumd`, L96–119 | PASS | `loss_sum` with θ=2, T0=a.T₀, a=A0, b=0, constant α=ϖ/8; verifies nonnegative A0 and 0<α≤1. |
| step sb-solve | `strip_budget`, `hsumle`, L121–133 | PASS | y-log at X=2πT₀ and hT' give total loss≤strip/4; no altered logarithm or factor. |
| step sb-strip | `strip_budget`, L134–158 | PASS | Nonnegative summable terms; total 3σ=strip/4 and partial combined loss≤strip/2; exact radius recurrence. |
| step sb-err | `strip_budget`, L159–165 | PASS | Each d≤strip/4≤1/4≤1, T_j≥1; bridge and `loss_choice` give error≤ϖ/8. |
| S1 power helper | `selectionT_rpow` L168 | PASS | Exact real-power identity for positive T₀ and every real x. |
| S1 t helper | `selectiont_eq` L177 | PASS | Exact geometric representation for every schedule and stage. |
| S1 ratio helper | `selection_eps_div_s` L183 | PASS | Exact ε_j/s_j=(ε₀/s₀)ϱ^j; q>0 and s₀>0 justify division. |
| bp y-geom helper | `geom_tsum_le_two` L193 | PASS | For 0≤g≤1/2, returns genuine summability and total≤2. |
| bp y-geom partial-sum helper | `geom_sum_le_two` L200 | PASS | Nonnegative finite partial sum bounded by the summable total. |
| bp schedule-props | `schedule_props` L205 | PASS | Exact revised signature, all 13 conjunction clauses. |
| step sp-1 / S1 | `schedule_props`, L229–267,293–304,324–329 | PASS | w=2^(τ+1)≥2; exact T,t recurrences, t bound and ε/s identity. s_j=s₀q^j is definitionally true; ell=2λ₀ϱ^j is explicitly proved as `hell`. |
| step sp-2 / S2 | `schedule_props`, L330–352 | PASS | Summability of shifted ell; tail≤4λ₀ϱ^m≤γT_m^(−τ−1), using h1 and ϱ≤w⁻¹. |
| step sp-3 / S3 | `schedule_props`, L268–292,305–323,353–356 | PASS | Geometric ratios ϱw and ϱw^μ≤1/2; both derivative sums and final ≤C₁ returned. The intermediate 8λ₀/t₀≤C₁ follows directly from h2 and ht. |
| step sp-4 / S4 | `schedule_props`, L357–367 | PASS | Exact Q♯=Q₀G(0)^j; G(0) is source g1 (zero-based Fin indexing). Positive denominators justify field simplification. |
| step sp-5 / S5 | `schedule_props`, L368–380 | PASS | t_(j+1)≤t_j/2 and 4C₁t_j≤γT_j^(−τ−1) imply the stated collar/divisor bound. |

The strip lower bound also holds at j+1 by universal instantiation, so no source endpoint is omitted. Using 3σ for δ+2σ is exact because δ=σ in the schedule. The helpers have ordinary scalar/source/typing premises, not conclusion-shaped hypotheses. Extra reusable helpers are distinct names, not replacements for weaker source claims. No fixed-parameter uniformity or norm carrier is changed.

## Definition classification and proof refutation

**No new `def`, `abbrev`, `structure`, instance or notation is introduced.** The entire new module consists of 11 public theorems and one private theorem. There is no junk-value construction or fallback. Imported `SelectionSchedule` is raw numeric data; B03's hypotheses explicitly impose the needed positivity and smallness conditions.

The crucial identity is `16 c/ϖ = 2 c/(ϖ/8)`; since ϖ>0 the field manipulation is valid. This equates the logarithm arguments, not merely asymptotic bounds. With X=2πT₀ the loss-sum numerator becomes 4(A0+n log X)/X. The tangent-line estimate and hT' bound its two contributions by strip/8 each. Nonnegativity is proved before comparing any term or finite partial sum to a `tsum`.

For schedule properties the proof uses ϱw≤1/32, ϱw^μ≤1/32, and hence convergent nonnegative geometric series; it never exploits Lean's default value of a nonsummable `tsum`. All divisions and real-power products used in S3–S5 have the required positive bases/denominators.

## Hygiene and independent validation

All Lean/Lake checks below run sequentially with `LEAN_NUM_THREADS=1` and `nice -n 5`; the build uses the prescribed shared compile gate. Default heartbeat/recursion budgets are retained.

1. Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b03 KAM.Planetary.WeakKAM.StripBudget
```

Exit **0**. Relevant output:

```text
[inp-gate] slot 2 acquired 16:36:14 for KAM.Planetary.WeakKAM.StripBudget
⚠ [9098/9098] Replayed KAM.Planetary.WeakKAM.StripBudget
warning: KAM/Planetary/WeakKAM/StripBudget.lean:74:61: Variable name `hμ` is not explicitly referenced.
Build completed successfully (9098 jobs).
```

Other replayed warnings are confined to imported Schedule (unused hv1/hc0) and FourierCutoffTail (deprecated if_pos/if_neg). No B03 design signal or heartbeat failure occurred.

2. Independent signature and axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B03Audit.lean
```

Exit **0**. The probe copies both theorem headers directly from the live signature file, renames them `audit_strip_budget` and `audit_schedule_props`, and supplies:

```lean
exact strip_budget a hn hμ hτ hs hs1 hT hT'
exact schedule_props a hn hμ hτ hγ hT ht hs he hstrip hC h1 h2 h3
```

It additionally checks both full types:

```lean
example : type_of% @audit_strip_budget := @strip_budget
example : type_of% @audit_schedule_props := @schedule_props
```

There is no `sorry` in this probe. Its complete axiom output is:

```text
'KAM.Planetary.selectionCN_eq_p11C' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionCutoffError_eq_p11Error' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionVarpi_pos_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectiond_eq_p11Loss' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.strip_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionT_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectiont_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selection_eps_div_s' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.geom_tsum_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.geom_sum_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.schedule_props' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Independent kernel replay (the scoped package has one lemma module and no provider):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.StripBudget
```

Exit **0**, output:

```text
replaying KAM.Planetary.WeakKAM.StripBudget
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (787 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The stale-root failure is explicitly permitted by the audit brief and B03 handoff. No generated file is regenerated. All other source checks pass.

5. `git diff --check`: exit **0**, no output. The untracked report is additionally checked for trailing whitespace. The auditor-created `.lake/abi-scratch/B03Audit.lean` is deleted after successful elaboration. Final `git status --short` contains only this new report and the pre-existing untracked B03 handoff. No tracked source or authority file is modified.

Static inspection: 382 lines, valid copyright/module/public-import/docstring/public-section form; no forbidden token (`sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, `set_option`) occurs. Exhaustive declaration-name search across `KAM/**/*.lean` found no other declaration with any of the 11 public short names, including `geom_tsum_le_two` and `geom_sum_le_two`. Namespace is `KAM.Planetary`; no root declaration shadows another name.

The recursively inspected project import closure has 52 KAM modules, no providers and no frozen theorem modules. Its 12 frozen modules are definition anchors, all manifest state `SEALED`: ActionNbhd, ComplexStrip, FrequencyMap, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, RealHamiltonian, SymplecticForm, Planetary/Phase. No `DRAFT_SORRY` anchor is imported.

## Source defects, deviations and limits

No new suspected blueprint or pinned-source defect was found in the audited slice. The blueprint labels these scalar arguments “Ours”; its existing D-15/D-16 schedule deviations are preserved. No pinned-paper claim is silently repaired. The only review notes are the inherited three-dot comparison/root difference and the permitted stale generated root. No Lean source was changed by this audit.

Snapshot SHA256:

```text
24519e40f9a176dedea7f0e0e85add84069e81d132e83f051218b77858e50c67  StripBudget.lean
6800132b3e98b3badc215d5cb1cccc6b016e2f14ec976b661519e436cbf39596  live P11BSignatures.lean
8b3fd811a8c13414699fb79dc55e7b1b74e90cebf697f89e76a053ecb52c0bdd  P11B-LEAN-DESIGN.md
90251ed2045353dd2c9574b5f2c53588eb5762ea9dbc86ed9075c00bf8d9ad1c  p11a3-iteration-selection.tex
```
