# N12-10b independent package audit 1

2026-10-28. Overall verdict: **PASS WITH NOTES** for the scoped infrastructure package.
`KAM.Nekhoroshev.flow` and `KAM.Nekhoroshev.flow_variational` both pass their exact design contracts.
No frozen anchor is proved or sealed by these modules; provider/frozen type and seal-body tests are
not applicable. This is not closure of either averaging root.

## Scope and snapshot

Audited only `KAM/Nekhoroshev/Averaging/FlowRegular.lean` and `Flow.lean`, as the handoff's AUDIT FOCUS
requires. Read AGENTS, PLAN, DECISIONS, the package brief, handoff, N12 design row/proof plan,
both design audits, Part 12 blueprint, Track N statement and relevant frozen definitions. Applied
statement-audit binder/body checks. No delegation or production changes. This report is deliberately
in the package worktree at the user's exact absolute path, overriding the generic brief's main-worktree
output instruction.

- HEAD: `a82e3461d75c79a4cad2d1ce7b505272b7f37d80`.
- Compared `inp`: `408ea7a6f026a1ecf1d0cf0e988bdc54494497f9`.
- `git diff inp...HEAD` warns of multiple merge bases and selects
  `6e36995edb8c5fb4ee4ec0ed914f4a0c55a9b7f1`. Its five-file diff contains Flow,
  FlowRegular, FlowChain, FlowSymplectic and LocalDependence. The latter three are dependency
  context, not independently recertified source-level packages in this focused audit.
- Flow SHA-256: `756f7faf6a948e2a47d064e0b9c83a35eee3fdf9a074fb9f3a717355cff78f02`.
- FlowRegular SHA-256: `c08193b3b2a8902941525648d6dc0e55d5460bcb3bd82d924d68af59c7e91dd2`.
- The signatures file is absent from this worktree's `.drafts/design/`; read the requested design
  signatures at `/root/code/KAM-inp/.drafts/design/N12Signatures.lean`. SHA-256:
  `0ad9cf0f84ffc435f1d85360516ad94f5ec100ff4a53c76d410f9e7d3b028369`, matching design audit 2.
  Both exported theorem heads match it after whitespace normalization. Fresh exact-type proof copies
  elaborate with `by exact flow d ε` and `by exact flow_variational d ε hp`.

## Declaration and node review

Names below have prefix `KAM.Nekhoroshev`. FR = FlowRegular; F = Flow.
All PASS judgments concern the stated scoped contract.

| Node / source clause | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| s-setting / open real domain | `isOpen_avgDomain'` (FR:33) | PASS | Product of open univ and open max-norm ball; no positivity needed. |
| s-setting / scaled perturbation | `data_smul'` (FR:37) | PASS | Derives Data at size abs ε from the analytic size-one input; no extra premise. |
| fl-short / Hamiltonian regularity | `avgH_contDiffOn` (FR:53) | PASS | Actual avgH is C² on Wdom by holo_input, with εf. |
| fl-short / field regularity | `avgField_contDiffOn` (FR:58) | PASS | ham_smooth_c1 and restriction to avgDomain supply C¹ field. |
| fl-short, fl-chain | `avgFlow_regOn` (FR:64) | PASS | Supplies open J,U and RegOn as conclusions via reg_all, using proved maximality and field regularity. |
| flow(b) | `flow_variational` (FR:72) | PASS | Exact design type; ordinary two-sided time derivative of the actual spatial fderiv. |
| flow(a), fl-chain | `isOpen_avgFlowDomain` (F:37) | PASS | Open product neighborhood lies inside the actual maximal flow domain. |
| flow(a) | `continuousOn_avgFlow` (F:45) | PASS | Joint continuity from open regular neighborhoods. |
| flow(b) | `continuousOn_fderiv_avgFlow` (F:53) | PASS | Joint continuity of actual spatial derivative on full flow domain. |
| flow(a) | `isOpen_avgOmega` (F:61) | PASS | Continuous time-section preimage of open domain. |
| flow(b) | `contDiffOn_avgFlow` (F:64) | PASS | Genuine HasFDerivAt plus continuous derivative imply C¹ slices. |
| fl-inverse | `avgFlow_inverse` (F:88) | PASS | Domain mapping and left inverse for every real t; shifted solution solves F itself. |
| fl-symp / flow(c) | `det_fderiv_avgFlow` (F:119) | PASS | Variational law, Hessian skewness, symplectic preservation, det ±1, connected-interval sign argument. |
| fl-transl / algebra | `angleShift_neg` (F:173) | PASS | Literal integer-shift identity; no analytic input. |
| fl-transl / domain | `avgDomain_image_shift` (F:177) | PASS | Angles unrestricted; action coordinate unchanged. |
| fl-transl / field | `avgField_shift` (F:191) | PASS | holo_real_d applied to derived scaled Data gives field periodicity. |
| fl-transl / maximality | `avgFlow_translate_fwd` (F:197) | PASS | gen_symmetry_translate plus actual maximality gives domain and value identity. |
| fl-transl / flow(d) | `avgFlow_translate` (F:216) | PASS | Opposite integer shift proves reverse membership; full domain equivalence. |
| bpN:p12:flow | `flow` (F:228) | PASS | Exact design conjunction; inverse at -t supplies the other inverse and surjectivity. |

Blueprint authority: `blueprint-N/parts/p12-averaging.tex:18-24,46-69`; N12 design sections 2, 4 and 6
(including row N12-10b and the flow proof paragraph). `flow` plus `flow_variational` retains every
(a)-(d) clause. Initial identity Y(0,x)=id follows from `avgMaximal_spec.init` on an open initial
neighborhood, explicitly proved inside F:131-138. Applying the inverse theorem at -t gives right
inverse and surjectivity, while continuous slices give the asserted homeomorphism. These consequences
are not extra hypotheses. Arbitrary real ε strengthens the blueprint's nonnegative-ε scope.

## Expanded binder audit

The common implicit telescope is n,R,s,h,f, followed by explicit d,ε. All are unchanged from design.
The next table expands the logical content of d; no hidden regularity, inverse or determinant result
is assumed. STANDING citations refer to p12:18-24 and the literal frozen predicates.

| Expanded input | Bin | Source / justification |
|---|---|---|
| n : ℕ | TYPING | Fin n source coordinates |
| R : ℝ | TYPING | action radius |
| s : ℝ | TYPING | geometric analytic width |
| h : (Fin n → ℂ) → ℂ | TYPING | integrable Hamiltonian |
| f : AvgComplexPhase n → ℂ | TYPING | phase perturbation |
| ε : ℝ | TYPING | parameter; all real values valid here |
| d.hn : 1 ≤ n | STANDING | p12 standing dimension |
| d.hR : 0 < R | STANDING | p12 radius |
| d.hs : 0 < s | STANDING | p12 width |
| d.hh.1 : holomorphy on actionNbhd | STANDING | frozen IsAnalyticIntegrable |
| d.hh.2.1 : continuity on closure | STANDING | same |
| d.hh.2.2.1 : nonnegative existential bound A, with norm bound on domain | STANDING | same; existential remains internal to premise |
| d.hh.2.2.2.1 : real values on realActionDomain | STANDING | same |
| d.hh.2.2.2.2 : real C³ | STANDING | same redundant analytic regularity guard |
| d.hf.1 : 0 ≤ 1 | STANDING | frozen IsAnalyticPerturbation at size one |
| d.hf.2.1 : holomorphy on complexDomain | STANDING | same |
| d.hf.2.2.1 : continuity on closure | STANDING | same |
| d.hf.2.2.2.1 : integer angle periodicity | STANDING | same |
| d.hf.2.2.2.2.1 : reality on real slice | STANDING | same |
| d.hf.2.2.2.2.2 : pointwise norm ≤ 1 | STANDING | same |
| d.hrank : alternative of everywhere-surjective Dω, or everywhere nonzero ω with surjective augmented (Dω,ω) map | STANDING | frozen HasAveragingFrequencyRank; both branches expanded here, no component lower bound |
| x : AvgPhase n, t : ℝ (variational theorem) | TYPING | point and time |
| hp : (t,x) ∈ avgFlowDomain | SOURCE | p12:53, derivative is asserted on D |

At the displayed field/atomic-clause granularity, flow counts: TYPING=6, STANDING=15,
SOURCE=0, RULED=0, EXCESS=0. flow_variational adds two TYPING inputs and one SOURCE input.
Bound variables internal to the displayed analytic/rank predicates range over their literal source
carriers and have no additional assumptions. Domain membership hp expands to x∈univ×actionBall R
and avgTm(x)<t<avgTp(x), using EReal endpoints. No positivity of ε, frequency lower bound,
compactness of angles, or differentiability of a chosen flow is introduced as an input.

Other public helpers use the same standing data when present, with only source point/time/shift inputs:
FR:33 uses n,R only; FR:64 adds p and p∈D; F:61,64 add t; F:88,119 add t,x,x∈Ω_t;
F:173,177 use integer k (and domain typing R for the latter); F:191 adds k,x,x∈W₀;
F:197 adds k,t,x,x∈Ω_t; F:216 adds k,t,x. These are TYPING and SOURCE inputs only,
with no EXCESS. No new public instance is introduced; local classical decidability is proof machinery.

## Definitions and dependency consumption

There are **no new def/abbrev/structure declarations in the two scoped files**. Their definition
classification is therefore empty: BODY_MATCH, PUBLIC_CARRIER, WELL_DEFINEDNESS, CHARACTERIZATION,
CHOICE_INDEPENDENCE are N/A for new scoped definitions; definition verdict PASS (empty set).

Inspected semantic dependencies: AvgPhase is the real Pi product with angles first; avgH is exactly
realHamiltonian(h,εf); avgDomain is univ×actionBall R; avgOmega is the time section of avgFlowDomain.
FlowDefs' existing choice and off-domain fallback are unchanged and excluded at every use by
avgMaximal_spec and maximal-domain membership. Open regular neighborhoods also supply local equality
when taking total fderiv; no fallback or off-interval value determines a claimed derivative.
RegOn is a literal regularity specification, produced by reg_all rather than assumed by these exports.
No such imported definition is being claimed as a newly audited implementation package here.

Consumption inspection: FR:69-70 supplies reg_all's open-domain, C¹-field and every-point maximal-solution
inputs. The generic interface concludes all RegOn clauses; its dependency route passes through
ext_dep/local flow, composition, continuation of regular neighborhoods and time reversal. The inverse
uses gen_symmetry_shift with the original F on the shifted open maximal interval; -t belongs because
0 belongs to the original interval. The determinant argument obtains skewness at actual orbit points
from C² on the larger Wdom, proves initial fderiv=id locally, and uses a zero intermediate determinant
to exclude the negative sign. Translation uses maximality, followed by -k for reverse domain inclusion.
No proof step is inserted into AveragingData. Imported helper internals are outside the assigned source
audit scope; their axiom closure is included in scoped exports and kernel replay.

Recursively enumerated project import closure: 26 frozen modules, all uniquely owned SEALED definitions;
zero frozen theorems, zero providers, zero DRAFT_SORRY imports. Protected diff is empty.

## Independent checks

All Lean/Lake invocations were sequential, with LEAN_NUM_THREADS=1 and nice -n 5. No heartbeat,
recursion or synthesis override; no clean/cache/update action. Temporary probe lives only in
`.lake/abi-scratch/N1210bAudit.lean` and is deleted after checking.

1. Targeted compile gate:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1210b KAM.Nekhoroshev.Averaging.Flow
   [inp-gate] slot 2 acquired 09:18:05 for KAM.Nekhoroshev.Averaging.Flow
   Build completed successfully (2967 jobs).
   exit 0
   ```

   Replayed upstream warnings: PicardFamilies:60,82,203,208 unused section variables; :268 haveI style;
   LocalDependence:45,186 unused section variables and :99 unused p. No warning in either scoped file.

2. Kernel replay, one invocation:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.FlowRegular KAM.Nekhoroshev.Averaging.Flow
   replaying KAM.Nekhoroshev.Averaging.Flow
   replaying KAM.Nekhoroshev.Averaging.FlowRegular
   exit 0
   ```

3. Exact design-type probes and all public theorem axiom checks:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1210bAudit.lean
   exit 0
   ```

   The probe imports Flow, declares the identical source variable telescope, copies each complete
   design theorem head under audit_flow / audit_flow_variational, and supplies the actual implementation.
   It then issues `#print axioms KAM.Nekhoroshev.<name>` for every name in the table above.
   Exact axiom output follows.

```text
'KAM.Nekhoroshev.isOpen_avgDomain'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.data_smul'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgH_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgField_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgFlow_regOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.flow_variational' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.isOpen_avgFlowDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.continuousOn_avgFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.continuousOn_fderiv_avgFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.isOpen_avgOmega' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.contDiffOn_avgFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgFlow_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.det_fderiv_avgFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.angleShift_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgDomain_image_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgField_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgFlow_translate_fwd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgFlow_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.flow' depends on axioms: [propext, Classical.choice, Quot.sound]
```

4. Source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (503 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1 (only the expressly permitted generated-root exception)
   ```

5. Mechanical source/protection checks: both scoped files have copyright, module, public imports,
   module docstring and public noncomputable section. FlowRegular has 82 lines, Flow 252; neither
   has a line over 100 Unicode characters. No forbidden token or set_option in either file.
   `git diff --check inp...HEAD` exits 0. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`
   is empty (apart from the merge-base warning on stderr). No generated file was regenerated.

## Notes, uncertainties and suspected defects

No material source/blueprint defect or suspected pinned-source erratum found in the scoped work.
No mathematical repair is requested. Recorded implementation deviations: the new FlowChain and
FlowSymplectic helper modules extend the planned import diagram; the concrete design-table paths remain
correct, and the dependency direction is acyclic. The public data_smul' repeats a private FlowDefs
lemma, a maintenance note rather than a statement issue. The finite-partition chaining plan is realized
by extension of regular neighborhoods and a supremum argument in the imported generic helper.

PASS WITH NOTES records the allowed stale generated root and upstream warnings, and the explicit
focused scope. N12-03c and the generic helper modules are dependencies, not separately certified by
this two-file source audit. No whole-campaign or frozen-root completion is inferred.
