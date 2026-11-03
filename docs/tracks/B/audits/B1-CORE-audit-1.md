# Independent B1-CORE audit 1

**Overall: PASS WITH NOTES.** The four implementation modules pass mathematical/API review, the targeted build, kernel replay and the complete public axiom inventory. No blocking proof defect found. N1 records an independent implicit-binder permutation; N2 carries an inherited documentation error. This certifies the B1-CORE infrastructure, not either complete B1 headline or a frozen seal.

## Identity, authority and scope

Worktree: `/root/code/KAM-inp-b1core`, branch `inp-b1core`, reviewed HEAD `2af754596485c240af41719e05a71bcddfd089af`. Comparison: `git diff inp...HEAD`, with `inp = 98ebd477197dcb292eb2938ec3c3aa669f444ae4`. Initial status was clean.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local AUDIT FOCUS handoff, both `/root/code/KAM-inp-b1/.drafts/B/brief-B1-{CORE,common}.md`, SPEC, FREEZE-PROPOSAL, program-b-plan §7 Brief 2, and the B0 statement review at `/root/code/KAM-inp-b1/docs/tracks/B/freeze/STATEMENT-REVIEW-1.md` (absent in this package worktree). Also inspected frozen OscillatorAction, ODE Basic/Maximal/Continuation and the corresponding blueprint-N Part 3 maximal/continuation statements. The Track B focus specializes the generic I/N/P brief: there are no B frozen anchors, registered providers, or B blueprint theorem nodes. Provider/frozen-type and proposed seal-body checks are therefore N/A. The requested helper signatures are the controlling local contract.

The three-dot diff contains 11 added files: four Lean implementation files (504 lines) and seven B0/handoff documentation files. Commit `0b61be41c` introduces the B0 material; `bbbb9bba3` introduces the four Lean modules; `2af754596` adds the audit handoff. Thus “no other file is touched” describes the implementation packet, not the complete three-dot diff. The inherited documentation was retained in scope, not silently dropped.

| Target | Verdict | Exact scope |
|---|---|---|
| B1-CORE / Domains | PASS | All literal definitions and domain/derivative lemmas below. |
| B1-CORE / StoppedDrift | PASS | Both time directions on the closed segment. |
| B1-CORE / FirstExit | PASS | Stopped drift implies confinement on the existing time set. |
| B1-CORE / ChartFlow | PASS WITH NOTES | Both requested existence engines; N1 concerns implicit binder order only. |
| B1-T proposed headline | PASS WITH NOTES for its CORE dependency only | Transport, cancellation, inverse identification and physical uniqueness are other packages; headline proof/seal not audited here. |
| B1-E proposed headline | PASS WITH NOTES for its CORE dependency only | Same limitation; zero-action compatibility of CORE checked. |

## Declaration-by-declaration review

All names below are in `KAM.EffectiveStability`. Every new public declaration is listed, including the extra helpers. Domain prose signatures were compared manually; all five complete theorem signatures printed in the CORE brief were additionally elaborated in a scratch probe.

| Node/module | Lean declaration (line) | Verdict | Reason / contract comparison |
|---|---|---|---|
| Domains | `cyl` (30) | PASS | Literal open cylinder on the full real product carrier. |
| Domains | `cylClosed` (33) | PASS | Literal closed cylinder; no compactness claim for its lifted angles. |
| Domains | `actionBox` (36) | PASS | Literal coordinatewise open absolute-value box. |
| Domains | `actionBoxClosed` (39) | PASS | Literal coordinatewise closed absolute-value box. |
| Domains | `osc` (42) | PASS | Literal strict oscillator-action sublevel set, q first and p second. |
| Domains | `oscClosed` (46) | PASS | Literal non-strict oscillator-action sublevel set; includes zero actions. |
| Domains | `oscAct` (50) | PASS | Exactly the frozen action with arguments w.2, w.1. |
| Domains | `oscAct_apply` (52) | PASS | Exact sum-of-squares normalization, factor 1/2. |
| Domains | `oscillatorAction_nonneg` (55) | PASS | All p,q and j; sum of squares, no positivity premise. |
| Domains | `isOpen_actionBox` (59) | PASS | Finite intersection of continuous strict sublevels. |
| Domains | `isOpen_cyl` (65) | PASS | Finite intersection after second projection. |
| Domains | `continuous_oscAct` (71) | PASS | Polynomial observable on the whole carrier. |
| Domains | `isOpen_osc` (76) | PASS | Finite intersection of strict action sublevels. |
| Domains | `cyl_eq_prod` (82) | PASS | Exactly univ ×ˢ actionBox c; no quotient or compact cylinder substitution. |
| Domains | `actionBoxClosed_eq_pi` (85) | PASS | Exact product of intervals [-c_j,c_j], including empty factors. |
| Domains | `isCompact_actionBoxClosed` (89) | PASS | Finite product of compact intervals; arbitrary real c. |
| Domains | `isCompact_oscClosed` (92) | PASS | Closed subset of two compact coordinate boxes of widths c_j+1. |
| Domains | `actionBoxClosed_subset_actionBox` (107) | PASS | Only positive epsilon; same widths enlarged by epsilon. |
| Domains | `cylClosed_subset_cyl` (111) | PASS | Only positive epsilon; second component unchanged. |
| Domains | `oscClosed_subset_osc` (115) | PASS | Only positive epsilon; action levels, not radii, enlarged. |
| Domains | `add_angleShift_mem_cyl` (119) | PASS | Integer shift of angles leaves actions unchanged. |
| Domains | `contDiff_oscAct` (123) | PASS | Global ContDiff ℝ ⊤, at least the requested regularity. |
| Domains | `oscActDeriv` (129) | PASS | Continuous linear map v ↦ (q_j v_qj + p_j v_pj)_j, proved the actual derivative. |
| Domains | `hasFDerivAt_oscAct` (135) | PASS | Product/chain rules give oscActDeriv at every w. |
| Domains | `fderiv_oscAct` (155) | PASS | Exact requested derivative, no division by actions. |
| StoppedDrift | `abs_sub_le_of_deriv_bound` (23) | PASS | Requested type elaborates verbatim; convex uIcc mean-value estimate handles either sign. |
| FirstExit | `firstExit_box_nonneg` (31) | PASS | Distinct forward helper; stopped bound used only after confinement up to s is proved. |
| FirstExit | `firstExit_box` (124) | PASS | Requested type elaborates verbatim; negative times handled by reflection. |
| FirstExit | `firstExit_box_of_deriv` (152) | PASS | Requested type elaborates verbatim; pointwise conditional derivative bound supplies genuine hstop. |
| ChartFlow | `exists_confined_aux` (33) | PASS | Explicit conditional helper; continuation premises are discharged by both concrete wrappers. |
| ChartFlow | `exists_confined_solution_compact` (83) | PASS WITH NOTES | PASS WITH NOTES: requested proposition; implicit n is prenexed before E (N1 below). |
| ChartFlow | `exists_confined_solution_periodic` (115) | PASS | Requested type elaborates verbatim; compact actions and periodic field, no compact lifted cylinder. |

## Definitions and hypotheses

Exactly eight new definitions, no abbrevs or structures: `cyl`, `cylClosed`, `actionBox`, `actionBoxClosed`, `osc`, `oscClosed`, `oscAct`, `oscActDeriv`. The first six are literal sets, oscAct is a literal polynomial observable, and oscActDeriv is a literal continuous linear map. All eight have their intended meaning on their entire carriers. There is no choice, junk branch, default, source subtype replacement, or implicit positivity restriction. The public exposed noncomputable section exposes bodies as required. Negative widths correctly yield empty factors/sets where appropriate; dimension zero correctly gives singleton phase/action spaces and vacuous index conditions.

Frozen `KAM.Planetary.oscillatorAction p q j = (p j ^ 2 + q j ^ 2)/2` is used with p=w.2 and q=w.1. Its project import closure contains only four frozen definition modules, all manifest SEALED: OscillatorAction, HamiltonianVectorField, SymplecticForm, IsDiophantine. The full project import closure has 15 modules and no provider or frozen theorem anchor. No DRAFT_SORRY import is present.

The compact engine's compact-sublevel and domain-inclusion assumptions are precisely the requested generic source premises, discharged by oscillator domains in the intended consumer. The periodic engine assumes precisely open U, C¹ field, integer-angle periodicity, closed action box inside U and its conditional component bound. Neither assumes confinement of an unknown trajectory. The generic `exists_confined_aux` is distinctly named and explicitly conditional on a maximal solution and two continuation implications. Those implications are not promoted to source facts: both concrete exports prove them using the existing ODE continuation results with compact sets. Maximality includes the usual solution/extension predicate, not an already granted requested horizon.

## First-exit proof trace

`FirstExit.lean:31-121`: fix t₁∈J with 0≤t₁≤T. Order connectedness supplies [0,t₁]⊆J. Define A to consist of s∈[0,t₁] for which confinement holds on [0,s]. The initial estimate and a+Tη<b make 0∈A. A is nonempty and bounded above, so s=sSup A lies in [0,t₁].

For u<s, the supremum property gives a larger member of A and hence confinement at u. Continuity on the closed interval supplies confinement at s by closure of each coordinate's closed sublevel set; s=0 is handled directly. Only now does hstop apply on [0,s]. It gives

`|f s j| ≤ |f 0 j| + |f s j - f 0 j| ≤ a j + η j*s ≤ a j + T*η j < b j`.

The **strict** last inequality yields a right neighborhood of s satisfying all finitely many strict coordinate bounds. If s<t₁, choose x strictly between s and min(neighborhood endpoint,t₁); combine the old bounds up to s with the new bounds after s. Then x∈A and x>s, contradicting the supremum. If s=t₁, confinement on the entire segment follows. This argument never invokes hstop on an unproved confined segment. Finite `Fin n` is used to obtain one neighborhood for all coordinates.

`FirstExit.lean:124-149`: reflect the time set by negation and use f(-s) for t≤0. The preimage is order connected, continuity composes, [0,s] reflects exactly to uIcc 0 (-s), and absolute time becomes -t. `FirstExit.lean:152-163` obtains continuity from coordinate derivatives and constructs hstop using the scalar mean-value lemma on uIcc 0 t. `hbound` is applied only at u∈J with the assumed stopped confinement. Thus it is a genuine stopped derivative estimate, not an unconditional orbit bound hidden in a premise.

## Continuation proof trace and consumers

`ChartFlow.lean:33-80`: apply firstExit_box_of_deriv on the actual maximal interval eIoo Tm Tp, using zero_mem_eIoo. This proves bounds only at existing times with |t|≤T. To show T<Tp, assume Tp≤T. Every nonnegative existing time t<Tp then satisfies |t|≤T, hence lies in the closed stopped region. The supplied right continuation implication gives Tp=⊤, contradicting Tp≤T. The left argument assumes -T≤Tm, obtains |t|≤T for all existing Tm<t≤0, and derives Tm=⊥, a contradiction. No value at an unproved maximal endpoint is used.

Real points q and r strictly between Tm and -T, and T and Tp, respectively, exist even for infinite endpoints. T₁=min(r,-q)>T has Ioo(-T₁,T₁)⊆eIoo Tm Tp. Now every |t|≤T belongs to the maximal interval, including both endpoints, and the already proved first-exit bounds apply. There is no initial assumption of existence through T, global confinement, or the desired T₁.

`ChartFlow.lean:83-111`: hmargin and nonnegative Tη give a≤b and hence x₀∈W by hKW. gen_maximal constructs the solution. Differentiability of g on W and the ODE give the ordinary derivative by chain rule. hdrift supplies the conditional derivative bound. The two continuation implications are proved by gen_continuation_compact with the literal sublevel compact set and t_star=0. This validates every premise of the auxiliary theorem.

`ChartFlow.lean:115-146`: the same construction uses the second component of z as observable; its derivative is (F(z t)).2. The compact set is actionBoxClosed b, not the lifted cylinder. gen_continuation_periodic is applied with hper and hbox and t_star=0. This matches blueprint-N's compact-action periodic continuation corollary and excludes finite-time angular escape without claiming bounded angles.

For the proposed B1-T consumer, use U=actionBox(b+ε), hbox from actionBoxClosed_subset_actionBox, and cyl_eq_prod; the field periodicity and action drift must still be supplied by B1-TRANSFER/HEAD. For B1-E use g=oscAct: its nonnegativity makes |oscAct|=oscAct, so the generic absolute-value sublevel is exactly oscClosed b. isCompact_oscClosed and oscClosed_subset_osc supply continuation, contDiff_oscAct gives differentiability, and fderiv_oscAct supplies the actual derivative. This is an API compatibility review, not a compiled full consumer proof.

## Edge cases

- **T=0:** only t=0 is in |t|≤T; first exit needs no positive horizon. The maximal solution already has Tm<0<Tp. The auxiliary argument still yields T₁>0. No division by T occurs.
- **η=0:** the segment estimate gives zero drift, and hmargin becomes a<b. Neither the scalar estimate nor first exit nor continuation divides by η or assumes η>0. For a constant observable the estimate is exactly 0≤0 on every segment, including negative times.
- **Backward time:** reflected first exit and the independent left-end continuation argument preserve |t| and use the correct EReal inequalities. On the simple affine test f(t)=ct the scalar inequality is equality |ct|=|c||t| for either sign of t.
- **Zero oscillator actions:** q_j=p_j=0 is admitted; oscActDeriv at that coordinate is zero. Closed sublevels and polynomial smoothness require neither polar coordinates nor positive actions. The compactness bound x²/2≤c ⇒ |x|≤c+1 follows from (|x|-1)²≥0, so also covers c=0 and empty negative-level sets.
- **n=0 / empty domains:** all coordinate conditions are vacuous and the phase space is a singleton. For positive dimension negative inner absolute-value widths contradict the actual initial-point premise; no illicit positivity premise is inserted. Closed/half-open/singleton J are allowed because first exit uses continuity within J and only segments known to lie in J.

## Notes, suspected defects and deviations

**N1 (nonblocking API note):** `ChartFlow.lean:83` has elaborated implicit prefix `{n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]`, whereas the CORE brief prints `{E} [instances] {n}`. Thus it is not literally the same fully explicit `@` function type as the brief. The initial exact-`@` probe exited 1 with `Type mismatch @exists_confined_solution_compact`, showing exactly this permutation; the other four probes passed. A second probe retains the complete requested proposition and uses only

```lean
fun {E} _ _ _ {n} =>
  KAM.EffectiveStability.exists_confined_solution_compact (E := E) (n := n)
```

as adapter; it passes. No premise, explicit binder order, carrier, constant dependence, conclusion or time quantifier differs. Named implicit calls and the intended HEAD assembly are unaffected. The brief permits the main names and shapes rather than a frozen ABI here; record this deviation from the handoff's “no changes” assertion. Any future exact frozen provider type must be independently matched at that stage.

**N2 (inherited documentation defect; not used in CORE):** `docs/tracks/B/OWNER-DECISIONS.md:10` says “so N's and R's regularity follow on the chart domain.” C² regularity does not follow from H∘Ψ being C² and R being differentiable: for n=1 take Ψ=id, H=0, N(J)=|J₀|^(3/2), R(φ,J)=-|J₀|^(3/2). The pullback identity holds, R is differentiable and periodic in angles, but N and R are not C² at J₀=0. The B0 review already records this as C1. Correct the explanation to say K is C² and K-R is differentiable; the required normal-part invariance/cancellation does not require C² N or R. No CORE proof assumes this false inference; no production text was repaired by this audit.

No new suspected pinned-paper erratum is established. This is a contract/proof audit of the elementary CORE package, not a renewed source-PDF audit of GLS17 or CL20. The inspected blueprint-N continuation facts agree with their use. The complete B1-T/B1-E proof, transport/cancellation and future freeze/seal remain outside the certificate supplied here. Track files refer to overnight D71; the local DECISIONS snapshot ends at D70, so this report treats that reference as the packet's recorded status, not independently verified exact-text freeze approval.

## Verification receipts

All Lean/Lake invocations were sequential and inside the exact focus wrapper

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

The build additionally passes through the prescribed inp compile gate, which invokes its own nice -n 5 lake build. No library-wide build, application build, cache operation, clean, protected edit, or git mutation was run.

Targeted build command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b1core KAM.EffectiveStability.ChartFlow
```

Exit 0, output:

```text
[inp-gate] slot 1 acquired 23:50:12 for KAM.EffectiveStability.ChartFlow
Build completed successfully (2853 jobs).
```

ChartFlow imports the other three audited modules, so this target checks their complete closure. These were the existing overlay artifacts; the command did not force a clean rebuild. No audited-file warnings were emitted.

Kernel replay command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env leanchecker --verbose KAM.EffectiveStability.ChartFlow KAM.EffectiveStability.Domains KAM.EffectiveStability.StoppedDrift KAM.EffectiveStability.FirstExit
```

Exit 0, exact output:

```text
replaying KAM.EffectiveStability.FirstExit
replaying KAM.EffectiveStability.StoppedDrift
replaying KAM.EffectiveStability.Domains
replaying KAM.EffectiveStability.ChartFlow
```

Final requested-type/axiom probe command (after the N1 investigation):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/B1CoreAudit.lean
```

Exit 0; five requested proposition checks, with the explicit N1 adapter only for compact continuation. Named proof binders in the probe were prefixed with `_` to suppress irrelevant unused-binder warnings; no linter or resource option was overridden. Exact complete axiom output:

```text
'KAM.EffectiveStability.exists_confined_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.exists_confined_solution_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.exists_confined_solution_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.cyl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.cylClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.actionBox' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.actionBoxClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.osc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscAct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscAct_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscillatorAction_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.isOpen_actionBox' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.isOpen_cyl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.continuous_oscAct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.isOpen_osc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.cyl_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.actionBoxClosed_eq_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.isCompact_actionBoxClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.isCompact_oscClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.actionBoxClosed_subset_actionBox' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.cylClosed_subset_cyl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscClosed_subset_osc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.add_angleShift_mem_cyl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.contDiff_oscAct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscActDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.hasFDerivAt_oscAct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.fderiv_oscAct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.firstExit_box_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.firstExit_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.firstExit_box_of_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.abs_sub_le_of_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

LINT_RECEIPT_PENDING
