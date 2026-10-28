# N12-14 independent package audit 1

Audit snapshot: 2026-10-28, `/root/code/KAM-inp-n1214`, HEAD `b2282ed6ec7daf0380638087acf0e8e3839bd94c`.

## Scope and authority

Read AGENTS.md, PLAN, DECISIONS (including D28), the package audit brief, N12-14 handoff, N12 design row and proof plan, both design audits, Part 12 blueprint, track-N statement, the two frozen averaging anchors and their relevant definitions. Used the lean-statement-audit method; this is an independent single-auditor review, with no delegation or production changes.

User instructions override the brief's generic report destination: this report is in the package worktree at the exact requested absolute path. Only `KAM/Nekhoroshev/Averaging/Stopped.lean` is audited as new implementation, following AUDIT FOCUS. `git diff inp...HEAD` was inspected: seven Lean modules and four earlier audit/handoff files; the other six modules are inherited dependencies. `git diff inp-n1213...HEAD` also includes six Lean modules because that branch is not the immediate N12-14 base. The Stopped module is new in both comparisons; the four N12-14 commits change only this module. Its SHA-256 is `398d2c2e9e513489f29ec85d8b79bbb0ed60fd0cdcc2c24ecd1d9195485e86c7` (384 physical lines; handoff's 383 is a harmless count discrepancy).

Comparisons used `inp=05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2` and `inp-n1213=8eb17a1ba2bce8c218d81a65f77f4c97ed9534a6`. The canonical signatures file is absent locally; read `/root/code/KAM-inp/.drafts/design/N12Signatures.lean`, and checked against the current local design Appendix A.

Overall verdict: **PASS WITH NOTES** for N12-14 infrastructure. `avgStopped` and `stopped` pass source/design fidelity and proof checks; the generated-root lint exception and the two blueprint clarifications are nonblocking. This is not an averaging-anchor seal or campaign closure.

## Declaration and proof review

All names below are in `KAM.Nekhoroshev`. Locators without a filename refer to Stopped.lean. PASS for a helper means its stated mathematical contract passes; conditional transport/integral helpers do not replace an unconditional source result.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| bpN:p12:s-trans#psi | avgStopped (36) | PASS | Literal design signature and body; corrector plus epsilon times killed time integral, ENNReal throughout. |
| st-meas | measurableSet_avgStay (48) | PASS | Relative openness plus Borel ambient subtype domain gives ambient Borel stay set. |
| st-meas | measurable_killed (74) | PASS | Arbitrary measurable envelope; flow continuity only on open flow domain, zero elsewhere. |
| Initial flow identity | avgFlow_zero (99) | PASS | Actual maximal solution initial value, domain guarded. |
| Initial flow domain | zero_mem_avgOmega (102) | PASS | Maximal interval contains zero. |
| Domain inclusion | mem_avgDomain_of_half (105) | PASS | R/2 ball inside R ball from R>0. |
| st-pt | mem_avgStay_of_lt_tau (110) | PASS | EReal supremum gives a later stay time; interval connectedness and prefix displacement give stay membership. |
| st-pt / st-int | flow_mem_of_stay (121) | PASS | Stay membership implies time <= tau; consumes exit confinement. |
| Envelope support | avgG_subset_actionBall (126) | PASS | 3R/4 closed ball inside R open ball. |
| st-int | lintegral_slice_le (137) | PASS | Restricts to measurable stay slice intersect D and supplies every transport premise. |
| st-int | lintegral_time_le (154) | PASS | Jointly measurable killed integrand; Tonelli, slice bound, interval measure 1/epsilon. |
| s-trans#data | exists_cell_cover (177) | PASS | Floors of bounded angle coordinates give finite integer cell cover; empty K allowed. |
| st-meas auxiliary | avgStoppedExt (205) | PASS | Explicit zero extension of both envelopes, with the same killed integral. |
| st-meas bridge | avgStopped_eq_ext (215) | PASS | Equality for every admissible initial action; stay confinement removes internal action indicator. |
| st-meas | measurable_avgStoppedExt (227) | PASS | envelope_regular and measurable_killed, followed by parameter lintegral. |
| st-int | lintegral_cell_le (235) | PASS | transport at zero for corrector; time-integral transport for envelope. |
| bpN:p12:stopped; st-meas, st-pt, st-int | stopped (283) | PASS | Exact design telescope; no extra premise; witnesses precede every size-one f1 and epsilon. |

`avgStopped` signature and full definition body, and `stopped` signature, are byte-identical to the canonical signatures. The final theorem assumes neither transport, envelopes, pointwise estimates nor confinement: it derives them from actual imports.

### Binder classification

The following exhausts `stopped`'s inputs, expanding the project-owned bundle. SOURCE references are Part 12 setting and stopped proposition, interpreted with design sections 2 and 4 and D28. No implicit instance adds a mathematical premise.

| Binder / expanded field | Bin | Authority / meaning |
|---|---|---|
| n : Nat (implicit) | TYPING | Dimension; design admits internal n>=1. |
| R : Real (implicit) | TYPING | Action radius. |
| s : Real (implicit) | TYPING | Analytic width. |
| h (implicit) | TYPING | Complex integrable Hamiltonian. |
| f (implicit) | TYPING | Complex perturbation, fixed standing data. |
| d.hn : 1 <= n | STANDING | Design section 2, Part 12 setting. |
| d.hR : 0 < R | STANDING | Positive action radius. |
| d.hs : 0 < s | STANDING | Positive analytic width. |
| d.hh : IsAnalyticIntegrable R s h | STANDING | Frozen analytic integrable predicate. |
| d.hf : IsAnalyticPerturbation R s 1 f | STANDING | Frozen unit-size perturbation predicate. |
| d.hrank : HasAveragingFrequencyRank (actionBall n R) h | STANDING | Frozen full/projective rank disjunction. |
| K : Set (AvgPhase n) | TYPING | Initial phase set, Pi max-norm product. |
| hK : IsCompact K | SOURCE | Compact lifted window, blueprint line 220. |
| hKI : forall x in K, x.2 in actionBall n (R/2) | SOURCE | Initial inner action collar. |

Counts: TYPING 6, STANDING 6, SOURCE 2, RULED 0, EXCESS 0 (14 expanded inputs). The bundle has exactly the six fields at Setting.lean:33-42. Frozen `IsAnalyticIntegrable` expands to holomorphy, continuity on closure, existence of a finite nonnegative bound, real values on the real domain, real C3 regularity. Frozen `IsAnalyticPerturbation` expands to nonnegative size, holomorphy, continuity on closure, integer periodicity, real values, and pointwise size bound. Frozen rank expands to the source full-rank alternative or nonzero frequency plus augmented-map surjectivity at every action. None is a result-shaped assumption.

The post-existential binders f1, hf1, epsilon, positivity and epsilon<=1 are universal conclusions, not assumptions constraining the witnesses. The final x, membership, t, 0<=t, t<=1/epsilon, t<=tau, u and u in Icc are the intended pointwise conclusion guards.

Helper inputs were also inspected individually in the declaration table: d/epsilon and any M2 are standing data or parameters; measurability of an arbitrary Phi, Borel D, membership in a cell, and initial action collar are the named conditional integration contracts. hM0 is only a nonnegative envelope parameter for auxiliary measurability/cell bounds. The final theorem obtains hM0 and the Hessian row-sum bound from envelopes, rather than assuming them. No excess premise is hidden in an instance or a helper alias.

### Consumption and endpoint checks

At 294-300 `envelopes d` supplies C1, Omega0, M2 and the uniform envelope bounds before introducing f1 or epsilon. At 301 the proof constructs `{d with hf := hf1}`; envelopes depend on h, not on the subsequently varied f1. The finite cover S is chosen from K; A1 is max(1, card(S)*(max(0,cPhi)+4*max(0,cW))). This is independent of epsilon and of every quantified f1. The selected witnesses may use the original standing d, as the exact design telescope allows; no claim of canonical choice independence in d is needed.

Measurability (305-312) proves equality with the zero-extended functional on all of K and then applies the K indicator. Neither global measurability of the chosen flow nor global regularity of the raw envelopes is asserted. Integration (313-359) partitions K into disjoint measurable intersections with the finite cells. Per-cell transport (250-268) at t=0 handles the initial corrector, including the necessary half-ball to G inclusion. Time-slice transport (150-151), Tonelli (163), time length (169-170), and epsilon*(1/epsilon)=1 (334-338) supply the second term. The final envelope inequalities are genuinely used, with no supremum/integral interchange.

For st-pt (360-378), exit supplies maximal-time strictness and confinement even at t=tau. pointwise is applied with kappa=sqrt(epsilon), the derived M2 bound, and all trajectory guards. Icc is replaced by Ico using the singleton endpoint's zero Lebesgue measure. For every v<t<=tau, mem_avgStay_of_lt_tau proves indicator=1; monotonicity enlarges the interval to [0,1/epsilon]. Thus no strict-stay assertion at the exit endpoint or unsupported flow value is used.

N12-09/11/12/13 are consumed through EnvelopeIntegrals, Exit, Pointwise and Transport as assigned. Their implementations are outside this focused re-audit; axiom closure and replay cover their imported proof dependencies mechanically.

## Definition classification

Exactly two new definitions; no new abbrev, structure, choice-defined object, or global instance.

| Definition | Classification and whole-carrier semantics |
|---|---|
| avgStopped | Literal ENNReal formula, exact design body, defined for arbitrary parameters and initial phase. Outside the intended positive-epsilon/domain theorem guards its total formula remains the declared object; theorem claims stay on the guarded domain. The stay indicator prevents reliance on arbitrary flow values. |
| avgStoppedExt | Explicit auxiliary literal zero extension, named separately from the source majorant. Its action-ball zero branches are intentional support restrictions, not replacements for the source object. Theorem avgStopped_eq_ext proves equality on the entire initial-action carrier used by stopped. No theorem substitutes this extension without that equality. |

For both: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS. Neither definition uses toReal, an arbitrary witness, or an unproved characterization.

## Anchor boundary

No provider export or frozen theorem is implemented by N12-14. Provider-type and seal-body probes are therefore N/A for this package, rather than passing vacuously for an anchor.

| Related manifest anchor | Verdict / proof status |
|---|---|
| nekhoroshev.d28.averaging_mean.v1 | PASS WITH NOTES as a package dependency only; DRAFT_SORRY, FROZEN_UNPROVED, not seal-ready. |
| nekhoroshev.d28.averaging_most.v1 | PASS WITH NOTES as a package dependency only; DRAFT_SORRY, FROZEN_UNPROVED, not seal-ready. |

The two anchors retain their manifest-bound `by sorry` bodies and were not imported into the audit probe. No root closure or new anchor statement audit is claimed. Recursive source import traversal from Stopped reaches 88 KAM modules, no providers, no frozen theorem modules, and 26 frozen definitions, all manifest state SEALED.

## Blueprint notes and suspected defects

No new mathematical defect or source erratum was found. Nonblocking documentation clarifications:

1. Blueprint p12:220,236 counts exactly the cells meeting K and states `A1=max(1,N_K(cPhi+4cW))`. Lean uses a possibly larger finite covering family S, hence a valid possibly larger constant. Design:239 expressly permits a covering-family implementation; design:289 and the exact theorem require only an existential positive A1. This is not a weakened estimate or wider dependence. It should not be described as computing the exact occupied-cell count.
2. Blueprint p12:241 says “S is open”. With nonnegative time, this means relative openness in the domain stated in Exit. Lean correctly uses that relative topology and proves ambient Borel measurability at 48-71. No ambient-open-set inference is used.

The inherited Nei76 equation (17) issue and declared integral-of-maximum repair remain recorded under D28 / E-NAVG-NEI-17. This focused audit checks the Part 12 implementation and local source contracts; it does not claim a new pinned-PDF audit. No code deviation introduced by this audit.

## Independent verification

The build, probe, and kernel replay completed successfully; lint passes all checks except the brief-authorized stale generated-root exception. All audit-owned Lean invocations use LEAN_NUM_THREADS=1 and nice -n 5. No protected source was edited, and no state-changing git command was used.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1214 KAM.Nekhoroshev.Averaging.Stopped
```

Exit 0. Gate receipt: `[inp-gate] slot 1 acquired 11:15:48 for KAM.Nekhoroshev.Averaging.Stopped`. Final output: `Build completed successfully (3246 jobs).` Cached dependency warnings were replayed (including deprecated tsum API in CorrectorRegular and unused Transport binder); no Stopped diagnostic. The wrapper invokes `nice -n 5 lake build` and the build snapshot was preserved.

2. Exact-design and axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1214Audit.lean
```

Exit 0. Probe imports only Stopped, copies the exact canonical `stopped` telescope under a fresh name, and supplies `by exact stopped d K hK hKI`. It also copies the full design `avgStopped` formula under a fresh name and checks `example : @audit_avgStopped = @avgStopped := rfl`. Thus neither a loose pretty-print match nor a placeholder is used as the signature witness. Every new public theorem and both definitions were printed in that same invocation. Complete axiom output:

```text
'KAM.Nekhoroshev.measurableSet_avgStay' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.measurable_killed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgFlow_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.zero_mem_avgOmega' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.mem_avgDomain_of_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.mem_avgStay_of_lt_tau' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.flow_mem_of_stay' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgG_subset_actionBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.lintegral_slice_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.lintegral_time_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.exists_cell_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgStopped_eq_ext' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.measurable_avgStoppedExt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.lintegral_cell_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgStopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgStoppedExt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay (one invocation, the only new module):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.Stopped
```

Exit 0. Complete output:

```text
replaying KAM.Nekhoroshev.Averaging.Stopped
```

4. Hygiene and integrity: the two protected-path comparisons

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff inp-n1213...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

both produced no output. Forbidden-token/resource-option search in Stopped produced no matches. Module header, public imports, docstring, exposed public noncomputable section, and the 384-line size pass. Full import-closure check found no draft anchor/provider. `git diff --check` passes. Appendix A is byte-identical to the canonical signatures file. No Lean source, frozen file, manifest or generated file was edited by this audit.

5. Full source lint (run after the build, exact-design probe, and kernel replay):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the explicitly allowed generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (558 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The generated root was deliberately not regenerated. A preliminary lint invocation was stopped during the source guard, before its ABI Lean stage, and superseded by this complete serialized run with the required environment and priority. All completed audit-owned Lean checks ran one at a time. The gate wait was expected and no cache, package, clean, update or full-library rebuild command was used.

The exact-design/axiom probe was removed from `.lake/abi-scratch/`; no auditor-owned temporary probe remains. Final `git diff --check` and `git diff --no-index --check /dev/null docs/tracks/N/audits/N12-14-audit-1.md` pass. Final status adds only this report to the pre-existing untracked handoff. The production module hash and HEAD were rechecked unchanged.

**Closeout: PASS WITH NOTES for N12-14; no blocking findings, no new suspected source errata, no frozen-anchor closure claim.**
