# B4-TMULTI independent package audit 1

**Verdict: PASS WITH NOTES** for `KAM.EffectiveStability.torusChain_confinement`,
`torusStep_of_chain`, and `tchChainSmoke_zeroDrift`. No blocking proof or statement defect found.
No frozen anchor is assigned or certified seal-ready: this is ordinary Track B infrastructure.

## Scope and authority

Audit date: 2026-11-03. Worktree: `/root/code/KAM-inp-b4tmulti`.
HEAD: `2815c8e8b0f90d858c2eb6c9a76bf40c84bb2160`.
Comparison `inp`: `c1695ac83b4a334272bf339675975625f707d404`.
`git diff inp...HEAD` contains six new Lean modules (904 lines total) and the 73-line handoff.
The six Lean modules are unchanged from producer commit
`5529d264c7f6177a025e837e7951aa7338e8a967` through the inp-b1 merge to audited HEAD.

Read AGENTS.md, PLAN.md, DECISIONS.md, the named package-audit brief, the handoff/AUDIT FOCUS,
B4-TMULTI and B1-common briefs, the common prover brief, B SPEC/FREEZE-PROPOSAL/OWNER-DECISIONS,
program-b-plan §2.2 and §3.2 (external `/root/code/KAM` copy, §3.2 lines 341–420), the
OscillatorChain template, TorusStep, ChartChain, TorusDomain, FT, Cauchy, RealFlow and relevant
Canonical APIs. Compared reused conventions with blueprint-N Part 5 setting, flow, symplecticity
and Lie/Taylor nodes. The specific Track B contract governs rather than unrelated I/N/P anchors.
The local DECISIONS ends at D70; D71 is the packet's recorded overnight status, with scope
OD-B11 and checker interpretation OD-B12. No exact-text freeze approval is inferred.

Provider/frozen type and seal-body probes are **not applicable**: there is no provider or new
frozen declaration. Instead an independent conclusion probe was elaborated from B1-T's conclusion.
The user's exact worktree report destination overrides the generic brief's main-worktree destination.
Only this report and temporary `.lake/abi-scratch/` probes were written; no state-changing git.

## Notes and limits

- **N1 — one-step scope.** `TorusChain.lean:105–140` proves the requested singleton reduction,
  with exactly the B4-TSTEP solution/uniqueness/chart-image/drift conclusion. It is the rational
  step-record specialization with fixed `ftPiUB`, replicated scalar action radii, and a typed
  intermediate `s.out` checked by two Bool identities. It does not claim to reproduce B4-TSTEP's
  more general real step parameters and arbitrary admissible π upper bound. The two equalities
  imply the direct one-step evaluation identity. Division `(B/L!)/δc` equals `B/(L!*δc)`;
  L! is positive and δc>0. These choices are explicit in the handoff and allowed by the brief.
- **N2 — smoke coverage.** `Smoke.lean:37–65` really instantiates the full theorem with two
  steps; all finite hypotheses are discharged. Both generators are zero, ε=0, and
  `|J₀|≤0` forces zero initial action. The exported statement retains only an existential curve
  and zero drift, dropping ODE, initial-value and uniqueness clauses. It checks satisfiability
  and the theorem application, not noncommutativity, nonzero displacement or numerical usefulness.
  List order was checked independently with symbolic distinct steps and by reading the induction.
- **N3 — certificate scope.** The package is Prop-based finite-data soundness with explicit
  real inequalities; it is not a general-chain executable Bool checker or certificate generator.
  It proves confinement in transformed actions from chart initial data; it does not certify
  containment of a specified physical initial box or bounds on original observables.

## Mathematical review of the audit focus

Every main premise is finite data, typing, an exact Bool check, or an explicit rational/real
inequality. `TChStep` has no analytic proof fields. `TChStepOK` checks positivity, ε∈[0,1/2],
L≥1, FTFits, the strip/λ guard, and finitely many derivative majorants indexed by Fin n.
`TChChainOK` recursively checks the Lie sum against `s.out` and finally against Nact+P.
`TChDomOK` recursively checks radius inequalities. Neither the main theorem nor these predicates
assumes a flow estimate, an exact transformed Hamiltonian identity, a remainder bound, or confinement.
The action-only normal part is checked by `ftActOnly`; no divisors are needed for soundness (OD-B12).

For a list `s :: l`, Ψ=Φ_s∘Ψ_l, Ψinv=Ψinv_l∘Φ_s⁻¹, and
Rem(Q)=E_s(Q)∘Θ_l+Rem_l(s.out). The identity at Ψ_l(w) first replaces the outer Lie sum by
s.out, then applies the tail identity. Real inclusion commutes with the inner chain on the
proved cylinder. The empty-list base is the final exact equality check with zero remainder.
There is no unpropagated outer remainder or reversed polynomial order.

At a Cauchy-disc point, `tchBound_of_cpolydisc` gives |Im θ_i|≤δc and ‖J_i‖≤r_i+δc.
Induction adds precisely Σ_inner εσ′ and Σ_inner ερ′. Before the outer step its strict
TChDomOK inequalities put that image in `cstripOpen (σ−σ′/2) (ρ−ρ′/2)`, hence the half gauge
interior. The separate real budget b+εb+Σ_inner ερ′+ρ′≤ρ puts the real inner images in the
full gauge interior needed for a left inverse. Every application of the chosen flow is thereby
inside a proved existence domain, so no fallback branch supplies the result.
The displacement sums are in the same lifted coordinates and use a triangle inequality at
each intermediate point; no transformation derivative factor is being silently discarded.

`tchDom` is open by continuity of Θ on its open inner domain, not by global continuity of a
totalized flow. The induction proves holomorphy of Θ and of every pushed-forward remainder.
`norm_tchRem_le` applies the one-step Lie remainder bound at each inner image and adds B_k/L_k!.
FTFits is passed for the current polynomial and `fits_out` for the next. Order L means terms
j<L and remainder ad^L/L!, agreeing with plan §3.2 using m=L−1 and blueprint-N Taylor.
Strip widths are geometric period-one widths; π enters only the FT majorants/strip check.

Real canonical charts map each budget cylinder into the next and have the displayed left
inverse; the generic ChartChain result proves the composition canonical. Per-step lattice
equivariance is proved from the generator's periodicity, then composed. The main proof obtains
periodicity of R=H∘Ψ−Nact∘J using this equivariance and periodicity of ftEvalR H; the action
part is unchanged by lattice shifts. Periodicity is derived, not a certificate hypothesis.

At a stopped real point, εb>0 gives an open real neighbourhood where the telescoped identity
holds. Equality of Fréchet derivatives therefore legitimately replaces R by P+Re Rem.
The entire closed δc-polydisc lies in the open tchDom, and the **summed** remainder is bounded
there by M=tchChainBound. A single `abs_fderiv_realPart_fst_le` gives M/δc. The polynomial
part uses `abs_fderiv_ftEvalR_le`; hdrift pays their sum. There is no repeated Cauchy loss
per step and no missing boundary inclusion. No FTFits premise on Nact is needed: action-only
semantics holds on its whole carrier, and its evaluation is smooth independently of typing.

Finally B1-T is applied with H=ftEvalR H, V=univ and the composed charts. Physical initial value,
two-sided existence past T, uniqueness for every order-connected interval containing zero,
chart-image membership and both endpoint-inclusive action bounds are retained. An independent
probe used the conclusion extracted from `Torus.lean`, specialized to these objects, rather
than copying the package conclusion; it elaborated with all 22 explicit main binders in order.

## Declaration and definition inventory

All names below are in `KAM.EffectiveStability`. The node column names the B4-TMULTI
contract component; these are not invented I/N/P blueprint claims. Every new source-level
public theorem/definition/structure is listed. Structure projections are the displayed data
or finite-check fields, with no hidden analytic obligation. No new abbrev or instance occurs.

| Node / file | Declaration | Verdict | Classification or reason |
|---|---|---|---|
| TorusChain / theorem | `torusChain_confinement` | PASS | Exact B1-T conclusion specialized to ftEvalR H, univ and chain charts. |
| TorusChain / theorem | `tchChainMap_singleton` | PASS | Definitional equality to the one-step chart. |
| TorusChain / theorem | `tchChainInv_singleton` | PASS | Definitional equality to the one-step inverse. |
| TorusChain / theorem | `torusStep_of_chain` | PASS WITH NOTES | Singleton specialization; same one-step conclusion, data restrictions in N1. |
| Basic / structure | `TChStep` | PASS | Finite polynomial/rational/order data only; no proof fields. |
| Basic / def | `tchStepFlow` | PASS | Existing totalized complex time-one flow; justified on half interiors. |
| Basic / def | `tchTheta` | PASS | Outermost-first composition; empty list is identity. |
| Basic / def | `tchRem` | PASS | Exact sum E_s(Q) after inner Θ plus recursive remainder at s.out. |
| Basic / def | `tchTailA` | PASS | Rational sum of ε σ′ in the common angle coordinates. |
| Basic / def | `tchTailJ` | PASS | Rational sum of ε ρ′ in the common action coordinates. |
| Basic / def | `tchChainBound` | PASS | Rational sum of order-L adjoint majorants divided by L!. |
| Basic / structure | `TChStepOK` | PASS | Finite positivity/order/typing/strip/small-field majorant checks. |
| Basic / def | `TChChainOK` | PASS | Recursive per-step exact Bool identities and final Nact+P check. |
| Basic / def | `TChDomOK` | PASS | Finite real-chart and strict complex Cauchy radius inequalities. |
| Basic / def | `TChBound` | PASS | Auxiliary coordinate bound, not a certificate premise about a flow. |
| Basic / theorem | `replicate_getD_tchRad` | PASS | Fin n indexing is in bounds; no default radius used. |
| Basic / theorem | `TChStepOK.σ'_posℝ` | PASS | Rational positivity transferred to ℝ. |
| Basic / theorem | `TChStepOK.ρ'_posℝ` | PASS | Rational positivity transferred to ℝ. |
| Basic / theorem | `TChStepOK.σ'_ltℝ` | PASS | Strict strip inequality transferred to ℝ. |
| Basic / theorem | `TChStepOK.strip_ltℝ` | PASS | Exact rational strip guard transferred to ℝ. |
| Basic / theorem | `TChStepOK.lam_geℝ` | PASS | Exact rational λ guard transferred to ℝ. |
| Basic / theorem | `TChStepOK.σ_nonneg` | PASS | Derived from positive σ′<σ. |
| Basic / theorem | `TChStepOK.tchLam_pos` | PASS | Guard denominator positive; λ positive is derived. |
| Basic / theorem | `TChStepOK.stripLog` | PASS | Derives geometric strip bound using fixed π upper bound. |
| Basic / theorem | `TChStepOK.tchSmallField` | PASS | Proves analytic SmallField from finite derivative bounds. |
| Basic / theorem | `tchTailA_nonneg_of` | PASS | Induction on nonnegative ε σ′. |
| Basic / theorem | `tchTailJ_nonneg_of` | PASS | Induction on nonnegative ε ρ′. |
| Basic / theorem | `TChChainOK.tchStepsOK` | PASS | Extracts only per-step checked hypotheses. |
| Basic / def | `tchDom` | PASS | Intersection with inner Θ preimages of open half-interior strips. |
| Basic / theorem | `cstripSub_subset_gaugeInterior` | PASS | Strict half-strip bounds imply closed gauge-ball inclusion. |
| Basic / theorem | `tchNorm_coord_le` | PASS | Coordinate norms bounded by product/Pi sup norm. |
| Basic / theorem | `tchStepFlow_disp` | PASS | flow_a yields angle ε σ′ and action ε ρ′ bounds. |
| Basic / theorem | `tchStepFlow_bound` | PASS | Triangle inequalities add the displacement budgets. |
| Basic / theorem | `tchDom_isOpen_and_differentiableOn` | PASS | Inductive openness and holomorphy on the justified domain. |
| Basic / theorem | `tchTheta_bound` | PASS | Induction pays inner budgets before applying each step. |
| Domain / def | `tchChainMap` | PASS | Real time-one charts composed outermost first. |
| Domain / def | `tchChainInv` | PASS | Reverse composition of real time-minus-one charts. |
| Domain / def | `tchChartSteps` | PASS | ChartStep data with domains/targets enlarged by inner action budgets. |
| Domain / theorem | `chartChainMap_tchChartSteps` | PASS | Agrees with generic ChartChain map by recursion. |
| Domain / theorem | `chartChainInv_tchChartSteps` | PASS | Agrees with generic reversed inverse by recursion. |
| Domain / theorem | `tchNorm_ric_sub` | PASS | Real inclusion converts coordinate norms to absolute differences. |
| Domain / theorem | `cyl_subset_realInterior_tch` | PASS | Real full-interior inclusion needed for inverses. |
| Domain / theorem | `tchStep_isCanonicalChart` | PASS | Smoothness, MapsTo, symplecticity and left inverse proved. |
| Domain / theorem | `chartChainTarget_tchChartSteps_subset` | PASS | Targets match budget-enlarged cylinders; empty case handled. |
| Domain / theorem | `tchChartSteps_ok` | PASS | Proves all canonical-chart and composability obligations. |
| Domain / theorem | `tchChain_isCanonical` | PASS | Composed chart with MapsTo, not surjectivity onto budget cylinder. |
| Domain / theorem | `tchChainMap_realInclusion` | PASS | Real/complex charts agree at the justified inner images. |
| Domain / theorem | `tchChain_identity` | PASS | Exact telescoping, evaluates E_s at inner Θ; no remainder omitted. |
| Domain / theorem | `tchChainMap_angleShift` | PASS | Inducts per-step lattice equivariance on the chart domain. |
| Drift / theorem | `tchBound_of_cpolydisc` | PASS | Closed discs give imaginary-angle and action-norm budgets. |
| Drift / theorem | `tchChainDrift_le` | PASS | One Cauchy estimate on summed remainder plus polynomial bound. |
| Remainder / theorem | `differentiableOn_tchRem` | PASS | Composed holomorphic summands on tchDom; no typing needed here. |
| Remainder / theorem | `norm_tchRem_le` | PASS | FTFits current Q and fits_out at recursion; sum B/L!. |
| Smoke / def | `tchSmokeStep` | PASS | Concrete zero generator with H=J₀²/2, rational radii and order 1. |
| Smoke / theorem | `tchSmokeStep_ok` | PASS | Kernel/norm_num checks of concrete step data. |
| Smoke / theorem | `tchChainSmoke_zeroDrift` | PASS WITH NOTES | Applies actual theorem with two checked steps; limited coverage N2. |

One private theorem, `Domain.lean:70` `tchStep_gen_real`, merely reuses
`ftEvalC_realInclusion₂_im`; it introduces no hypothesis or escape.
All 16 new definitions/structures give their documented object on the full stated carrier.
For arbitrary unchecked chains, flow-valued definitions inherit the existing totalization:
`Canonical.flow` returns its input when no solution exists. The theorems prove existence-domain
inclusions before consuming flow semantics; they do not exploit that fallback. Negative data
are permitted as data but rejected by the relevant checks. Empty chain values (identity, zero
sum, universal domain) are the intended empty constructions.

## Checks and receipts

All Lean/Lake invocations, including the ABI phase of lint, used the wrapper

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

No overlapping audit Lean/Lake calls, heartbeat/depth overrides, clean, update, cache download
or application builds. One preliminary multi-target freshness build exited 0 (`3002 jobs`);
it was followed by the required separate targeted gate calls below, sequentially.

```sh
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-b4tmulti <Module>
```

| Module (in order; prefix `KAM.EffectiveStability.`) | Exact output | Exit |
|---|---|---|
| TorusChain.Basic | Build completed successfully (2970 jobs). | 0 |
| TorusChain.Remainder | Build completed successfully (2971 jobs). | 0 |
| TorusChain.Domain | Build completed successfully (2998 jobs). | 0 |
| TorusChain.Drift | Build completed successfully (2999 jobs). | 0 |
| TorusChain | Build completed successfully (3000 jobs). | 0 |
| TorusChain.Smoke | Build completed successfully (3002 jobs). | 0 |

No warnings. Each gate call acquired slot 1, at 03:11:36, :40, :43, :47, :50, :54 UTC respectively.

Probe commands, each inside the wrapper, sequentially:

```sh
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/B4TMultiAudit1.lean
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/B4TMultiConclusion1.lean
```

Both exit 0. The first prints all 40 public theorem axioms and also checks by rfl, for arbitrary
symbolic s,t, the two-step map order, reverse inverse order, and pushed-forward remainder formula.
The second checks the independently extracted full B1-T conclusion; it produces no output.
The first's output is reproduced below (line wrapping normalized):

```text
'KAM.EffectiveStability.torusChain_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchChainMap_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchChainInv_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusStep_of_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.replicate_getD_tchRad' depends on axioms: [propext, Quot.sound]
'KAM.EffectiveStability.TChStepOK.σ'_posℝ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.TChStepOK.ρ'_posℝ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.TChStepOK.σ'_ltℝ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.TChStepOK.strip_ltℝ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.TChStepOK.lam_geℝ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.TChStepOK.σ_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.TChStepOK.tchLam_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.TChStepOK.stripLog' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.TChStepOK.tchSmallField' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchTailA_nonneg_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchTailJ_nonneg_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.TChChainOK.tchStepsOK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.cstripSub_subset_gaugeInterior' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchNorm_coord_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchStepFlow_disp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchStepFlow_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchDom_isOpen_and_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchTheta_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.chartChainMap_tchChartSteps' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.chartChainInv_tchChartSteps' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchNorm_ric_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.cyl_subset_realInterior_tch' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchStep_isCanonicalChart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.chartChainTarget_tchChartSteps_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchChartSteps_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchChain_isCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchChainMap_realInclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchChain_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchChainMap_angleShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchBound_of_cpolydisc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchChainDrift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.differentiableOn_tchRem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_tchRem_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchSmokeStep_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchChainSmoke_zeroDrift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay, one invocation inside the wrapper:

```sh
lake env leanchecker --verbose KAM.EffectiveStability.TorusChain KAM.EffectiveStability.TorusChain.Basic KAM.EffectiveStability.TorusChain.Remainder KAM.EffectiveStability.TorusChain.Domain KAM.EffectiveStability.TorusChain.Drift KAM.EffectiveStability.TorusChain.Smoke
```

Exit **0**, output:

```text
replaying KAM.EffectiveStability.TorusChain.Domain
replaying KAM.EffectiveStability.TorusChain.Remainder
replaying KAM.EffectiveStability.TorusChain.Smoke
replaying KAM.EffectiveStability.TorusChain.Basic
replaying KAM.EffectiveStability.TorusChain.Drift
replaying KAM.EffectiveStability.TorusChain
```

Lint command, inside the same wrapper: `sh scripts/lint_sources.sh`.
Exit **1**, solely for the generated-root staleness explicitly allowed by the audit brief.
Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)
check_lean_modules: PASS (4542 Lean files, 0 comparator configurations)
.........................
----------------------------------------------------------------------
Ran 25 tests in 3.861s

OK
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (314 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

The generated root was left untouched as required. The 314 core ABI checks passed;
application anchors were checked by file hash only, as the output states. This is not an
application build or application-ABI receipt.

Additional checks:

- `python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-b4tmulti KAM.EffectiveStability.TorusChain.Basic KAM.EffectiveStability.TorusChain.Remainder KAM.EffectiveStability.TorusChain.Domain KAM.EffectiveStability.TorusChain.Drift KAM.EffectiveStability.TorusChain KAM.EffectiveStability.TorusChain.Smoke`:
  exit 0, `short-name check OK (no reused public short name)`.
- `git diff --check inp...HEAD`: exit 0, no output.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md KAM/Root lakefile.lean`:
  exit 0, empty. Protected paths unchanged.
- `git diff 5529d264c HEAD -- KAM/EffectiveStability/TorusChain.lean KAM/EffectiveStability/TorusChain`:
  exit 0, empty.
- Source inventory: line counts 142, 301, 243, 84, 67, 67 (facade, Basic, Domain, Drift,
  Remainder, Smoke); all below both the 600-line package cap and 1500-line hard cap.
  Python check of every character width returned `overlong: []` (no exceptions needed).
- Every new module has copyright, `module`, public imports, module docstring and
  `@[expose] public noncomputable section`.
- Forbidden-token/override/escape search over the six modules: no matches. Ambient carriers are
  `(Fin n → ℝ) × (Fin n → ℝ)` and their complex analogues, with Pi/product max norms.
- Recursive source import scan: 90 KAM modules, 20 frozen definition modules, no provider,
  no frozen theorem and no DRAFT_SORRY anchor imports. Manifest-state lookup uses `path`;
  an initial diagnostic used nonexistent key `file`, then was corrected and rerun successfully.

## Suspected errata, deviations and remaining uncertainty

No new suspected pinned-source or blueprint defect found. This audit checks the local finite-chain
contract and reuse of the existing analytic APIs; it is not a new verification of the cited paper
PDFs or an audit of unrelated I/N/P headlines. The positive result is tied to the exact commits
and hashes below. The formulation/coverage limits are N1–N3; none changes the requested main
conclusion. No source edits or deviations were introduced by the auditor.

| Lean source | SHA-256 |
|---|---|
| `KAM/EffectiveStability/TorusChain.lean` | `bcf247ce4e523ccc9e928fcfa8a483e3807e6a14ffec289130d0b36bd29838f7` |
| `KAM/EffectiveStability/TorusChain/Basic.lean` | `155030398d5822b80d16fc4e45701cc5f3d7ebe010be7761c866254ad68bb6c9` |
| `KAM/EffectiveStability/TorusChain/Domain.lean` | `d292aaf66aeaf8c0396b3cc9bc81ae1fb22073d8017e39ded543f0394cc67ad2` |
| `KAM/EffectiveStability/TorusChain/Drift.lean` | `e56975d68a8728c6f72752b621220a0fe163a204b236e1060f2d719829989402` |
| `KAM/EffectiveStability/TorusChain/Remainder.lean` | `ef02a31932dcc6b6fa037f807956d7f034861ef774f11f52d65e70523a7d4fe0` |
| `KAM/EffectiveStability/TorusChain/Smoke.lean` | `a989374bec40180d784ab7d3a2d3ade376c1d1514d962341f120d4e87acc2e8d` |

Final cleanup: both named scratch probes were deleted after successful elaboration.
`git status --short` shows only `?? docs/tracks/B/audits/B4-TMULTI-audit-1.md`.
The report is the sole retained audit edit; no commit, merge, freeze, seal or push was performed.
