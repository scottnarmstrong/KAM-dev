# B2-MULTI independent package audit 1

Verdict: **PASS WITH NOTES** for `KAM.EffectiveStability.oscillatorChain_confinement`,
`oscillatorStep_of_chain`, and `chainSmoke_zeroDrift`. No blocking proof or statement defect found.
This is ordinary, unfrozen Track B infrastructure; no frozen anchor is certified seal-ready.

## Scope and controlling contract

Audited on 2026-11-03 in `/root/code/KAM-inp-b2multi` at
`cf22b3001d77fe742e81cbd7720d78097de05341`. The comparison was `git diff inp...HEAD`, with `inp`
at `597ea6fd20832ed0816072ffa5d4af9681d78546`. It contains exactly the six new Lean modules below
(918 lines) and `docs/tracks/B/audits/B2-MULTI-handoff.md` (115 lines). The six modules are unchanged
between producer commit `6821b4bb5` and audited HEAD; the intervening inp-b1 merge adds no further
code to this comparison. This verdict is tied to these bytes, not a future moving `inp`.

Read AGENTS.md, PLAN.md, DECISIONS.md, the named package-audit brief, the handoff and its AUDIT FOCUS,
brief-B2-MULTI.md and brief-B1-common.md, Track B SPEC/FREEZE-PROPOSAL/OWNER-DECISIONS,
program-b-plan §3.2 (external main-worktree copy, lines 341–420), the B2-STEP implementation,
ChartChain, the Cauchy API, and the relevant flow/symplectic/Taylor statements of
`blueprint-N/parts/p5-canonical-maps.tex` (44–138).

The specific Track B focus supersedes the generic I/N/P anchor/node checklist. There is no new
provider, frozen declaration, or I/N/P source theorem in this package, so provider/frozen type
identity and seal-body probes are **not applicable**. The frozen definitions of the Hamiltonian
field, symplectic form and oscillator action agree with SPEC. OD-B7 records the B2 extension;
local DECISIONS ends at D70, so D71 is packet status, not evidence of exact-text freeze approval.
The user's explicit worktree report path overrides the generic brief's main-worktree destination.
No production source, frozen file, manifest, generated root, or git state was changed by this audit.

## Findings and limits

1. **N1, documentation only:** `OscillatorChain/Domain.lean:17` says “onto the next box”; line 155
   says “onto `oscBox r (∑ ε δ)`”. `IsCanonicalChart` supplies `MapsTo` and a left inverse on the
   source, not surjectivity onto the majorant box. The stronger prose is false in general: a zero
   generator with positive allowed ε is the identity while the budget box strictly enlarges.
   Read both comments as **into**. The Lean declarations and consumers use the correct weaker
   property. No proof repair or new hypothesis is needed.
2. **N2, smoke-test coverage:** `Smoke.lean:87–126` genuinely applies the chain theorem to two steps
   and discharges its premises. But `I_j(w₀) ≤ 0` forces the initial point to the origin. It proves
   satisfiability, as requested, not a nonzero-action example, noncommuting-generator order test,
   or a numerical normal-form certificate. General list order is established by the inspected
   induction, not by this smoke test.
3. **N3, formulation:** step radii and ε are rational; `r`, `δc`, `a`, `b`, `η`, `εb`, `T`, and the
   initial point retain explicit real inequalities. `OscLieOK` admits literal polynomial equality
   as well as the exact Bool equality check. This is a finite structural check allowed by the
   brief and has proved evaluation semantics. No executable general-chain Bool checker or
   certificate-generation claim follows from this Prop-based soundness theorem.
4. **N4, whitespace:** `git diff --check inp...HEAD` exits 2 solely for trailing whitespace at
   `docs/tracks/B/audits/B2-MULTI-handoff.md:52`. This is outside Lean and has no proof impact.

## Mathematical review of the six focus items

All main-theorem premises reduce to finite polynomial data, CartFits typing, action-only/equality
Bool checks, structural polynomial equality, or displayed rational/real inequalities. `OscStep`
contains only data. `OscStepOK` has positivity/smallness/order/typing and derivative-majorant
fields; no field mentions a flow, remainder, or confinement. `OscChainOK` recursively records the
step checks and final normal-form check; `OscDomOK` records two finite radius budgets per step.
The supplied `hdrift` bounds the explicitly computed polynomial majorant after subtracting the
explicit rational sum `oscChainBound`, not an unknown derivative or confinement conclusion.

For `l = s :: t`, `Ψ_l = Φ_s ∘ Ψ_t`, `Ψinv_l = Ψinv_t ∘ Φ_s^{-1}`, and
`Rem_l(Q) = E_s(Q) ∘ Θ_t + Rem_t(s.out)`. The outer-step identity at `Ψ_t(w)` replaces its Lie
sum by `s.out`; the inductive identity then telescopes. The base case evaluates the final Bool
check and `cartActSubst` at `I(w)`. Real inclusion commutes with the inner chain on the proved
box, so the complex and real compositions are the same chart there. No unpropagated outer
remainder is added at the original point.

For a closed Cauchy polydisc about x with `|q_i|, |p_i| ≤ r_i`, the triangle inequality yields
`OscBound r δc`. Induction adds exactly `ε_s δ_s` displacement in the common Cartesian sup norm.
Before step s, the bound is `r_i + δc + oscTail(t)`; the second radius budget puts this strictly
inside `ρ_s − δ_s/2`. The first budget independently puts real inner images in the full gauge
interior needed for inverse identities. Thus every flow is used on its justified existence domain.
No derivative factors are missing: these are bounds for displacements in a single coordinate
system, not derivatives of coordinate transformations.

`oscChainDom` is recursively an intersection with the inner map's preimage of an open half
polydisc. Its openness uses continuity of the inner map **on that open inner domain**, not global
continuity of a totalized flow. The same induction proves holomorphy of Θ and of every composed
remainder. `norm_oscChainRem_le` applies each existing `norm_stepRem_le` at the mapped point,
uses CartFits for the current Q (and `fits_out` for recursion), and adds `B_s/L_s!` by the triangle
inequality. The empty sum is zero. The order convention is sum through `L−1`, remainder
`ad^L/L!`, matching blueprint-N `bpN:p5:taylor` and plan §3.2 with `m = L−1`.

At a stopped real point, εb > 0 and `2(b_i+εb) ≤ r_i²` give strict membership in `oscBox r 0`.
The telescoping equality therefore holds on a real neighbourhood, sufficient for equality of
Fréchet derivatives. The full closed δc-polydisc lies in the open `oscChainDom`; the entire
summed remainder is holomorphic there and bounded by `M = oscChainBound`. The abstract Cauchy
lemma yields `(|q_j|+|p_j|) M/δc ≤ 2 r_j M/δc`. Its nonnegativity step derives `M ≥ 0` by evaluating
the norm bound at the centre. No unjustified sign assumption or boundary differentiation is used.
`driftAbstract_le` is a distinctly named analytic helper with explicit analytic inputs; the main
finite-data theorem proves those inputs rather than assuming them.

The main proof restricts the composed canonical chart to the oscillator domain and applies
`oscillator_confinement` with V = univ and H = cartEval H. Its conclusion preserves physical
initial value, two-sided existence past T, uniqueness on every order-connected interval through
zero, chart-image membership, and endpoint-inclusive action bounds. It never replaces the exact
flow by a truncated coordinate map. The empty chain is also supported.

`oscillatorStep_of_chain` uses a singleton with output literally `cartLieSum χ H L`; its final
check is B2-STEP's hid, its tail is zero, and its sum reduces to `B/L!`. The compiled proof derives
this entire statement from the chain theorem. Independently, the audit proved that same full
signature from existing B2-STEP at rational ρ, δ, ε and `ρl = replicate n ρ`, converting casts and
using `replicate_getD_oscRad`. Thus the rational specialization has no additional analytic premise
or weaker conclusion. The two-step example's orders 1, radii 5, gauges 1, ε = 0, r = 2, δc = 1,
a = 0, b = 1, εb = T = 1, η = 0 discharge both strict budgets and the zero remainder/drift checks.

## Public theorem inventory

Names below are in `KAM.EffectiveStability`. Each row is a separate new public theorem. The
contract nodes are the B2-MULTI brief's finite-check, composition, telescoping, domain, tail,
Cauchy, confinement and reduction requirements; no unrelated blueprint closure is asserted.

| Node | Declaration | Verdict | Reason |
|---|---|---|---|
| Finite checks | `OscLieOK.cartEval_lieSum_eq` | PASS | Both finite identity branches imply evaluation equality over any ℚ-algebra. |
| Flow definition | `oscStepFlow_apply` | PASS | Definitional equality with exact complex time-one flow. |
| Radius typing | `replicate_getD_oscRad` | PASS | Fin n indices are within replicated list. |
| Small field | `OscStepOK.smallField` | PASS | Derivative majorants discharge the existing SmallField API. |
| Casts | `OscStepOK.delta_posℝ` | PASS | Rational positivity transferred to ℝ. |
| Budget | `oscTail_nonneg_of` | PASS | Finite sum of nonnegative εδ. |
| Complex domain | `cpolyOpen_sub_subset_gaugeInterior` | PASS | Strict half-radius box implies closed gauge-ball inclusion. |
| Sup norm | `norm_coord_le_prod` | PASS | Product/Pi max norms, no Euclidean carrier. |
| Displacement | `oscStepFlow_oscBound` | PASS | flow_a at t = 1 adds εδ coordinatewise. |
| Holomorphy | `oscChainDom_isOpen_and_differentiableOn` | PASS | Local preimage openness and chain rule on nested domains. |
| Finite checks | `OscChainOK.stepsOK` | PASS | Extracts per-step finite premises. |
| Complex budget | `oscChainTheta_oscBound` | PASS | Inner-tail displacement plus strict half-interior budget. |
| Holomorphy | `differentiableOn_oscChainRem` | PASS | Finite sum of holomorphic composed step remainders. |
| Tail bound | `norm_oscChainRem_le` | PASS | Mapped-point B/L! bounds summed; typed Q maintained. |
| Real domain | `isOpen_oscBox` | PASS | Finite intersection of strict coordinate inequalities. |
| Real domain | `oscBox_congr` | PASS | Rewrites equal offsets. |
| Composition | `chartChainMap_oscChartSteps` | PASS | Correct outermost-first map recursion. |
| Composition | `chartChainInv_oscChartSteps` | PASS | Reversed inverse recursion. |
| Composition | `chartChainTarget_oscChartSteps` | PASS | Majorant target box, not surjectivity. |
| Real slice | `norm_realInclusion₂_sub_coord` | PASS | Real coordinate differences have complex norm equal to absolute value. |
| Real domain | `oscBox_subset_realInterior` | PASS | Full gauge margin comes from first radius budget. |
| Canonical step | `oscStep_isCanonicalChart` | PASS | Smoothness, maps-to, symplecticity and left inverse proved. |
| Canonical chain | `oscChartSteps_ok` | PASS | Inner target matches next outer domain. |
| Canonical chain | `oscChain_isCanonical` | PASS WITH NOTES | Correct IsCanonicalChart; “onto” prose is N1. |
| Real slice | `oscChainMap_realInclusion` | PASS | Exact real/complex chain correspondence on box. |
| Telescoping | `oscChain_identity` | PASS | Outer remainder evaluated at inner chain, then recursive identity. |
| Cauchy | `driftAbstract_le` | PASS | Named analytic helper; neighbourhood identity and closed-disc holomorphy explicit. |
| Cauchy domain | `oscBound_of_cpolydisc` | PASS | Triangle inequality adds δc to coordinate radii. |
| Drift | `chainDrift_le` | PASS | Derives helper inputs from finite chain data. |
| Domain restriction | `osc_subset_oscBox` | PASS | Nonnegative radius and squared-radius inequality. |
| Confinement | `oscillatorChain_confinement` | PASS WITH NOTES | Full requested conclusion; unfrozen Prop-based infrastructure, N3. |
| Reduction | `oscillatorStep_of_chain` | PASS | Exact rational specialization, independently reverse-probed. |
| Satisfiability | `chainSmoke_zeroDrift` | PASS WITH NOTES | Two-step invocation valid; origin-only limitation N2. |

The two private helpers `oscStep_gen_real` and `smoke_supBound_nil` are respectively polynomial
reality and a zero-polynomial rewrite; neither assumes a substantive proof step.

## Definition classification

Every new definition/structure is listed. Structure projections are exactly the listed data or
finite-check fields. No new abbrev, class, instance, axiom, or hidden conclusion-bearing field occurs.

| Declaration | Classification and whole-carrier semantics | Verdict |
|---|---|---|
| `OscStep` | Finite data: gen/out polynomials, order, rational ρ/δ/ε. | PASS |
| `oscStepFlow` | Existing total complex flow at time 1. Genuine flow assertions guarded by SmallField and interior membership. | PASS |
| `oscChainTheta` | Composition of those total maps; empty chain id. | PASS |
| `oscChainRem` | Literal sum of composed step remainders; empty chain zero. Bound/identity claims restricted to justified domains. | PASS |
| `oscTail` | Exact finite rational sum of εδ. No fallback. | PASS |
| `oscChainBound` | Exact rational sum of polynomial B/L!; factorial never zero. Bounds asserted under stated typing/domain checks. | PASS |
| `OscStepOK` | Prop structure of rational/order/typing/majorant checks only. | PASS |
| `OscLieOK` | Literal equality or sound exact Bool polynomial equality. | PASS |
| `OscChainOK` | Finite recursive conjunction; base final normal-form Bool check. | PASS |
| `OscDomOK` | Finite recursive conjunction of explicit real budget inequalities. | PASS |
| `OscBound` | Coordinatewise complex-norm bound, meaningful for all r/c/z (possibly empty). | PASS |
| `oscChainDom` | Actual recursively defined open analytic locus, not a chosen/default surrogate. | PASS |
| `oscBox` | Literal strict real coordinate box (possibly empty). | PASS |
| `oscChainMap` | Exact time-one real-flow composition, empty id; physical claims guarded by box membership. | PASS |
| `oscChainInv` | Reversed exact time-minus-one real-flow composition; left inverse proved on source, not asserted globally. | PASS |
| `oscChartSteps` | Finite adapter into existing ChartStep, with boxes indexed by inner-tail budgets. | PASS |

The inherited `KAM.Canonical.flow` is choose-or-default off its existence locus (`Flow.lean:53`).
The new wrappers do not remove that totalization; the audited theorems establish existence and
uniqueness on every locus where physical flow or analytic estimates are claimed. No proof relies
on the default value being a solution. Negative/unusable radii simply make the relevant geometric
premises empty or unsatisfied; no whole-carrier physical meaning is invented there.

## Validation receipts

All Lean/Lake operations below were serial and inherited this exact cap/priority/thread prefix:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1
```

This applies also to the lint's ABI Lean subprocess. The compile gate adds its own prescribed
`nice -n 5 lake build`. No heartbeat, synthesis-heartbeat or recursion-depth override was used.

Build command (prefix above applied):

```sh
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-b2multi KAM.EffectiveStability.OscillatorChain.Smoke
```

Output, exit 0:

```text
[inp-gate] slot 1 acquired 01:48:33 for KAM.EffectiveStability.OscillatorChain.Smoke
Build completed successfully (2993 jobs).
```

Smoke transitively imports all six changed modules; this targeted build used the existing build
snapshot. No application library or generated root was built or regenerated deliberately.

Kernel command (one invocation; prefix above applied), exit 0:

```sh
lake env leanchecker --verbose \
  KAM.EffectiveStability.OscillatorChain.Basic \
  KAM.EffectiveStability.OscillatorChain.Remainder \
  KAM.EffectiveStability.OscillatorChain.Domain \
  KAM.EffectiveStability.OscillatorChain.Drift \
  KAM.EffectiveStability.OscillatorChain \
  KAM.EffectiveStability.OscillatorChain.Smoke
```

```text
replaying KAM.EffectiveStability.OscillatorChain
replaying KAM.EffectiveStability.OscillatorChain.Smoke
replaying KAM.EffectiveStability.OscillatorChain.Drift
replaying KAM.EffectiveStability.OscillatorChain.Domain
replaying KAM.EffectiveStability.OscillatorChain.Remainder
replaying KAM.EffectiveStability.OscillatorChain.Basic
```

The audit probe imported Smoke, printed axioms of all 33 public theorems, and copied the full
`oscillatorStep_of_chain` signature under `audit_oneStep_reverse`, proving it from B2-STEP with
replicated rational radii. Command (prefix above applied):

```sh
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  .lake/abi-scratch/B2MultiAudit.lean
```

Final exit 0, no warnings or errors. An initial scratch-only attempt omitted the ambient n binder
and needed an explicit rational-half cast; these probe mistakes were corrected before this run.
No package code was changed. Exact final axiom output:

```text
'KAM.EffectiveStability.OscLieOK.cartEval_lieSum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscStepFlow_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.replicate_getD_oscRad' depends on axioms: [propext, Quot.sound]
'KAM.EffectiveStability.OscStepOK.smallField' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.OscStepOK.delta_posℝ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscTail_nonneg_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.cpolyOpen_sub_subset_gaugeInterior' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_coord_le_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscStepFlow_oscBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscChainDom_isOpen_and_differentiableOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.EffectiveStability.OscChainOK.stepsOK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscChainTheta_oscBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.differentiableOn_oscChainRem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_oscChainRem_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.isOpen_oscBox' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscBox_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.chartChainMap_oscChartSteps' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.chartChainInv_oscChartSteps' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.chartChainTarget_oscChartSteps' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_realInclusion₂_sub_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscBox_subset_realInterior' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscStep_isCanonicalChart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscChartSteps_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscChain_isCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscChainMap_realInclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscChain_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.driftAbstract_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscBound_of_cpolydisc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.chainDrift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.osc_subset_oscBox' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscillatorChain_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscillatorStep_of_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.chainSmoke_zeroDrift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lint command (same capped prefix), `sh scripts/lint_sources.sh`, **exit 1**:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)
check_lean_modules: PASS (4518 Lean files, 0 comparator configurations)
.........................
----------------------------------------------------------------------
Ran 25 tests in 3.776s

OK
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (314 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

The only failing item is the expected stale generated root, expressly permitted by the audit
brief. The file named is `KAM/Root/EffectiveStability.lean`; it was left untouched. The module
check, all 25 guard tests, frozen-anchor guard, and 314 core ABI hashes pass. Lunar application
anchors were file-hash checked only, exactly as the lint output states; no application build or
application ABI closure is claimed.

Names command (source-only), exit 0:

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py \
  /root/code/KAM-inp-b2multi \
  KAM.EffectiveStability.OscillatorChain.Basic \
  KAM.EffectiveStability.OscillatorChain.Remainder \
  KAM.EffectiveStability.OscillatorChain.Domain \
  KAM.EffectiveStability.OscillatorChain.Drift \
  KAM.EffectiveStability.OscillatorChain \
  KAM.EffectiveStability.OscillatorChain.Smoke
```

```text
short-name check OK (no reused public short name)
```

Additional source checks:

- Character widths of every line in the six modules: `width violations: []` (strictly ≤ 100).
- Line counts: Basic 153, Remainder 165, Domain 229, Drift 139, facade 106, Smoke 126;
  total 918, largest 229, all under both the package's 600-line guidance and 1500-line hard cap.
- Each file has the required copyright, module command, public imports, module docstring and
  `@[expose] public noncomputable section`.
- `rg -n 'sorry|admit|axiom|unsafe|opaque|set_option|EuclideanSpace'
  KAM/EffectiveStability/OscillatorChain.lean KAM/EffectiveStability/OscillatorChain`:
  no matches (rg exit 1).
- Recursive source import walk from Smoke through KAM imports: 82 reachable KAM modules,
  20 frozen-definition modules, **zero provider modules and zero frozen-theorem modules**.
  Hence there is no SEALED/DRAFT_SORRY theorem import to justify. The axiom and kernel checks
  independently cover the actual elaborated proof dependencies.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md KAM/Root lakefile.lean`:
  empty (exit 0); no protected path changed.
- `git diff --check inp...HEAD`: the sole output is
  `docs/tracks/B/audits/B2-MULTI-handoff.md:52: trailing whitespace.` (exit 2; N4).
- `git diff 6821b4bb5 HEAD -- KAM/EffectiveStability/OscillatorChain.lean
  KAM/EffectiveStability/OscillatorChain`: empty, exit 0.

## Errata, deviations, and handoff

No new pinned-paper erratum, blueprint contradiction, B2-STEP defect, or unpaid analytic step was
found in this package. N1 is a defect in the new module's documentation, not a pinned source
erratum. The package proves finite-chain soundness and satisfies the requested reduction and
satisfiability checks; it does not close any unrelated N/P blueprint node, freeze a theorem,
or certify an Hénon–Heiles or planetary numerical instance. Rational step data, structural
`OscLieOK`, and the single Cauchy estimate on the summed remainder are disclosed formulations
consistent with the controlling brief. No implementation deviation was introduced by the audit.

Only this report is retained as an audit edit. The audit probe and temporary audit files under
`.lake/abi-scratch/` were removed after their results were copied here. No git add, commit, merge,
root regeneration, source repair, or frozen/manifest edit was performed. Nonblocking follow-up:
correct the two “onto” comments and handoff trailing whitespace when next editing those files;
a stronger smoke test can improve coverage without changing the theorem.
