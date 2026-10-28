# P23-16 independent audit 1

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-p2316`.
Audited HEAD: `e7874f8e55f6eff775b39f60a2ebfe839728b0b8`.
Comparison refs: `inp=05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`,
`inp-p2314=027fdfe2d8ecbb1704737c21b4e986c369763fb9`.

## Scope and verdict

**Overall verdict: PASS WITH NOTES** for P23-16 / `KAM.Planetary.iterative`.
All targeted build, exact-design elaboration, axiom and kernel-replay checks passed.
Notes concern the permitted generated-root lint exception and the downstream witness release gate.
Scope is ONLY the four `KAM/Planetary/TwoScale/Iteration*.lean` files,
as required by the handoff's AUDIT FOCUS. The requested report location in this worktree overrides
the generic brief's main-worktree destination. No production file was edited.

`git diff inp...HEAD` includes the inherited P23-14 Setting/Step files as well as this package.
The four scoped files are additions against both refs; Setting and Step*.lean are unchanged against
`inp-p2314`. That branch has an older merge base, so its full three-dot diff also contains unrelated
packages and generated-root changes. Those are not P23-16 changes. The protected-path diff against
`inp` is empty.

Frozen-anchor verdict: **not applicable**. P23-16 proves the infrastructure lemma
`KAM.Planetary.iterative`, not a `KAM.Provider` export or frozen theorem. Consequently a frozen-type
provider equality or seal-body probe would be inapplicable. The independent probe instead copies
the exact design declaration under a fresh name and proves it with `by exact iterative H`.
This audit does not seal P-G or certify P23-17–22.

Read: AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, P23-16 handoff,
P23 design revision 2 and both DESIGN-P23 design audits, P3a L234–265, track P statement,
P-G frozen anchor, and the domain/carrier definitions used here. The local draft fixture is absent;
used `/root/code/KAM-inp/.drafts/design/P23Signatures.lean` L697–746 read-only instead.
Its SHA256 is `d067d47dbabfdf4913da3e2b76886eb29598f4502ad16318d328568d82380cd3`.

## Declaration / node review

Names below are relative to `KAM.Planetary`. Every explicit public theorem and every new
abbreviation/structure in the four files is covered. Generated structure projections expose exactly
the listed fields; they introduce no additional mathematical assertion.

| Node / role | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| Composition notation | `latticeShift` (IterationCompose:32) | PASS | Literal complex integer angle shift with zero action shift. |
| `it-comp` bundle | `PhaseProps` (IterationCompose:35) | PASS | Differentiability, injectivity, reality, period-one equivariance and symplectic derivative law on the stated domain. |
| `it-base` auxiliary | `PhaseProps.id` (IterationCompose:43) | PASS | Identity has each property on any set; no openness needed. |
| `it-comp` | `PhaseProps.comp` (IterationCompose:50) | PASS | Restricts to V, composes through MapsTo into W; openness of Vb and W justifies full fderiv chain rule. |
| `it-comp` domain | `isOpen_coefficientDom` (IterationCompose:71) | PASS | Product-strip/action-neighborhood openness for arbitrary parameters, including empty domains. |
| `it-base` | `KamHyp.restrict` (IterationCompose:81) | PASS | Inherits all source hypotheses along D′ ⊆ D, including weighted class/summability and bounds. |
| Reality auxiliary | `KamHyp.eHat_lt_small` (IterationReal:36) | PASS | Smallness and positive dimension give Ê < 1/160 without an extra assumption. |
| Max-norm auxiliary | `KamHyp.sup_norm_le` (IterationReal:44) | PASS | Two block sup-norm bounds imply the full bound. KamHyp is unused and removable, so this is stronger than the application needs after dropping that binder. |
| `it-step` reality | `KamHyp.ihat_real_of` (IterationReal:52) | PASS | Distinct conditional helper; its hypotheses are previously derived step outputs, not source premises added to iterative. See proof review below. |
| `seq` unfolding | `seq_succ` (IterationStage:30) | PASS | Definitional update for every ScaleData. |
| `seq` divisor | `seq_γ₁` (IterationStage:32) | PASS | γ₁ unchanged by update, all j. |
| `seq` divisor | `seq_γ₂` (IterationStage:37) | PASS | γ₂ unchanged by update, all j. |
| `seq` exponent | `seq_τ` (IterationStage:42) | PASS | τ unchanged by update, all j. |
| `seq` block ratio | `seq_ratio₁` (IterationStage:47) | PASS | Simultaneous doubling cancels; no positivity needed. |
| `seq` block ratio | `seq_ratio₂` (IterationStage:54) | PASS | Same exact ratio invariant. |
| `seq` block ratio | `seq_ratio_hat` (IterationStage:61) | PASS | Same exact ratio invariant for Mhat/M. |
| Induction data | `Stage` (IterationStage:69) | PASS | Actual D,h,f,Φ tuple; no fabricated default stage. |
| `it-ind` | `StageInv` (IterationStage:78) | PASS | Derived induction invariant: KamHyp, frequency image, phase laws, map-to and conjugacy. Established at zero and propagated. |
| `it-step` relation | `StepRel` (IterationStage:89) | PASS | Records exact recurrence, map domains and numerical estimates; produced by stage_step, never assumed by iterative. |
| `it-comp` restriction | `PhaseProps.mono` (IterationStage:120) | PASS | Every property restricts to a subset. |
| `it-base` | `stage_zero` (IterationStage:129) | PASS | Restricts H to dioBase; identity phase and conjugacy, no extra premise. |
| `it-step`, `it-comp`, `it-rates` | `stage_step` (IterationStage:139) | PASS | Obtains the Diophantine premise from invariant frequency image and applies P23-14 step once. Uses exactly its shared witnesses. |
| `bpP:p3:iterative`, all five proof steps | `iterative` (Iteration:29) | PASS | Exact design signature; one dependent sequence, all required map/reality/lattice invariants, constants and recurrences. |

## Statement and proof review

Whitespace-normalized comparison of the entire declaration signature with the design fixture returned
`True`. Binder order, existential witness order, let-bound domains, block constants, coefficient-width
conventions, frequency identity, real maps-to, image sets and strict error recurrence agree exactly.
The only source hypothesis is `H : KamHyp D sbar p h f`. StageInv and StepRel are inductive proof
data, not additional assumptions. No widening of constant dependence or meaning-changing carrier
was found. The generic composition/restriction/scale facts are stronger than their positive-width
applications because they work on arbitrary domains or arbitrary ScaleData.

The dependent recursion is on `{S : Stage a b // StageInv ... j S}`. Classical choice selects the
next stage and its Ψ/ĩ together, once for each predecessor; `Nat.rec` follows that selection.
`Ψ 0 = id` is merely an unused zeroth indexing convention and `is 0 = id` is the required
initialization. There is no fallback on failure and no independent existential sequence later
identified with another arbitrary choice. At each successor the original γ₁,γ₂,τ are recovered
from seq invariants and the invariant frequency image, paying step's Diophantine premise.

For composition, the next domain is
`coefficientDom Dp (R/16) (sbar+s/12)`, contained in the large step domain
`coefficientDom D (R/2) (sbar+s/6)` using step's neighborhood inclusion. Its image is in
`coefficientDom D R (sbar+s)`, hence in the previous stage domain since R ≤ ρ. Thus
Φⱼ ∘ Ψⱼ₊₁, its derivatives, conjugacy and maps-to are justified on the actual next-stage domain.
This implements the design G3 repair with the same total Ψ and restricted source domain.

The nontrivial extra reality proof is sound as written: block bounds, normalized ratios and
Ê < 1/160 give ‖J−I‖ < R/16 for J=ĩ(I). With q=Re J in Dp by the image definition,
‖J−q‖ < R/16. The new KamHyp gives a holomorphic, injective frequency map on the R/16
neighborhood of Dp, real on its real slice. Both J and conjugate J lie in the ball centered at q.
Schwarz reflection and the real original frequency show they have identical new frequencies;
injectivity forces J=conjugate J. This proves realBase-to-realBase for the same ĩ witness.
There is no unproved reality premise hidden in the new bundle.

The cutoff bound uses the 24-factor from step and ordinary induction. The two radius inequalities
come respectively from step's lower bound and the next KamHyp's R ≤ ρ, with
ρ(nextScale pj)=R(pj)/16. Smallness and perturbation bounds remain in each stage's KamHyp.
The design encodes the blueprint's frequency diffeomorphism through holomorphy, injectivity and
bounded invertible derivative in KamHyp rather than exporting a separately bundled diffeomorphism.
The iterated error-power and closed-form width consequences are derivable recurrence consequences;
the P23-16 signature requires the recurrences, which are preserved exactly.

## Definition classification

- `latticeShift`: transparent abbreviation, literal lattice vector on its whole carrier.
- `PhaseProps`: transparent Prop structure, conjunction of five map properties; not a source-hypothesis replacement.
- `Stage`: transparent data structure, four actual stage objects.
- `StageInv`: transparent Prop structure, induction invariant proved from H at every stage.
- `StepRel`: transparent Prop structure, actual successor relation proved by consuming step.

No other new def/abbrev/structure occurs. The local T is a dependent recursive witness sequence,
not a totalization of a failed analytic construction. Global functions are only constrained on
named domains, as in the design; no theorem exploits arbitrary off-domain values.

## Verification receipts

All Lean/Lake/checker invocations in this audit use `LEAN_NUM_THREADS=1` and `nice -n 5`, serially.
The targeted build is submitted through the required compile gate. No library clean/update/cache
operation or generated-root edit was made.

Build command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2316 KAM.Planetary.TwoScale.Iteration
```

Exit 0; relevant exact output:

```text
[inp-gate] slot 2 acquired 10:53:18 for KAM.Planetary.TwoScale.Iteration
Build completed successfully (9163 jobs).
```

The build replayed pre-existing warnings outside scope: unused variables in
Hamiltonian/Diophantine:124, StepNonres:203, Inverse:109–110, Averaging/Finite:160;
deprecated names in StepNonres:250,257 and StepPerturb:35. No warning was reported
in the four audited modules. No heartbeat or other budget override was used.

Probe command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2316Audit.lean
```

Exit 0. The probe imported only Iteration, copied the external design's entire `iterative`
declaration under `audit_iterative`, and replaced its draft body by `by exact iterative H`.
It then issued `#print axioms` for all 18 new public theorems. Exact output:

```text
'KAM.Planetary.PhaseProps.id' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PhaseProps.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_coefficientDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.KamHyp.restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.KamHyp.eHat_lt_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.KamHyp.sup_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.KamHyp.ihat_real_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.seq_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.seq_γ₁' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.seq_γ₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.seq_τ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.seq_ratio₁' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.seq_ratio₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.seq_ratio_hat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PhaseProps.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stage_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stage_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iterative' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No sorryAx or custom axiom occurs in these results.

Kernel-replay command (one invocation):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.TwoScale.Iteration KAM.Planetary.TwoScale.IterationCompose KAM.Planetary.TwoScale.IterationReal KAM.Planetary.TwoScale.IterationStage
```

Exit 0. Exact output:

```text
replaying KAM.Planetary.TwoScale.IterationStage
replaying KAM.Planetary.TwoScale.IterationReal
replaying KAM.Planetary.TwoScale.IterationCompose
replaying KAM.Planetary.TwoScale.Iteration
```

The temporary probe and redirected checker log under `.lake/abi-scratch/` were removed after
recording these receipts. No audit scratch file remains.

Lint command: `sh scripts/lint_sources.sh` (exit 1). Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (572 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This is precisely the brief's permitted stale-root exception. No regeneration was attempted.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
`git diff --check`: empty, exit 0.
A recursive scan of local KAM imports from Iteration found 117 KAM modules,
zero provider modules and zero frozen theorem modules. Thus no DRAFT_SORRY import,
and no SEALED-theorem manifest-state exception is needed.
The forbidden-token/override/EuclideanSpace scan of the scoped files found no matches.
All four have copyright, module, public import, module docstring and public section
(`@[expose] public noncomputable section`). Physical line counts:
Iteration 114; IterationCompose 96; IterationReal 139; IterationStage 212.

## Notes, uncertainties and errata

No suspected new pinned-source or blueprint defect was found within this package's scope.
The reality gap in step's exported interface is paid here from its outputs; adding it to step
would be an optional interface improvement, not an unpaid premise or source erratum.
G3 is the already declared domain treatment, implemented without a new deviation.
The blueprint's existing max-norm/inverse-domain repairs are not reclassified as new findings.
No claim of a fresh CP10 PDF audit is made: source-facing comparison here uses the pinned
blueprint and the exact previously audited design as requested by AUDIT FOCUS.

Downstream P23-17–21 must retain the same chosen witnesses and satisfy the private-interface
release gate in P23 design L292–303. This proof supplies common stage witnesses; it does not
prove convergence, limits, injectivity or final consumer applicability for those later packages.
Frozen P-G remains outside this infrastructure audit.

Final review: no unresolved verification item; only this report was added by the auditor.
