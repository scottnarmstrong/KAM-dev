# SO-EXPR-B1 independent audit 1

Verdict: **PASS WITH NOTES** for the signed B1 slice. `HamExpr.jet_v0`, `HamExpr.jet_d1`, and
`HamExpr.jet_d2` pass independently, with precisely the signed hypotheses and conclusions.
There is no frozen anchor or provider to seal in this package. This verdict concerns the B1
semantic slice, not B2, SO-BALL, SO-REPLAY, or the final certificate theorem.

Audited HEAD `b67f81c3fc7ef65992f3ae6b749262e9fcb182a1` against `inp`
`6cad95806f4dbeafc1933f733daf875fdb3b097a`, using the full `git diff inp...HEAD`.
The diff consists of exactly the five new modules below (1582 inserted lines).
The pre-existing untracked handoff was preserved. Only this report is a repository edit;
all audit probes and logs were confined to `.lake/abi-scratch/` and removed after recording.

Authority: repository `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the local B1 handoff's AUDIT FOCUS.
The explicit user report destination overrides the generic brief's MAIN-worktree destination.
The focus limits the code audit to `Expr/{Slp,DiffCalculus,DiffBuild,DiffNode,Diff}.lean`.
SO has no local `statement.md` or `blueprint-SO/`; its controlling statements here are
`/root/code/KAM-inp/.drafts/design/SOSignatures.lean` §D, lines 634–680,
and `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md`, Revision 4,
§1.4 and the SO-EXPR package row at line 448. The campaign plan under
`/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md` was also consulted.
Unrelated I/N/P frozen theorem/provider equality and seal-body tests are not applicable.

## Signed surface and completeness

All names below are under `KAM.Certificate`.

| Signed declaration | Verdict | Evidence |
|---|---|---|
| `SlpOp` | PASS | Constructor names, order and argument types identical to signature lines 634–641. |
| `Slp` | PASS | One field `ops : List SlpOp`, identical to signature. |
| `Slp.val` | PASS | Exact signed binder order/type; actual fold implementation, not a placeholder. |
| `HamJet` | PASS | All five fields and their types identical, including `d3`. |
| `phaseNat` | PASS | Definition body identical: angles first, actions at offset `n`. |
| `HamExpr.jet` | PASS WITH NOTES | Exact signed type; kernel-reducible B1 compiler; `d3 := []` belongs to deferred B2. See optimization note below. |
| `HamExpr.jet_v0` | PASS | Exact signed declaration header; copied signed statement elaborates with `HamExpr.jet_v0 e z`. Unconditional at every point. |
| `HamExpr.jet_d1` | PASS | Exact signed declaration header; copied signed statement elaborates with `HamExpr.jet_d1 e hS hnv hz a`. All directions. |
| `HamExpr.jet_d2` | PASS | Exact signed declaration header; copied signed statement elaborates with `HamExpr.jet_d2 e hS hnv hz a b`. Exact iterated derivative and argument order. |

A whitespace-normalized comparison returned `True` for all five signed def/theorem headers,
all three inductive/structure bodies, and the `phaseNat` body. Fresh probes also imported the
facade and used the signed theorem text under anonymous fresh declarations with the direct
export applications above, plus `type_of%` checks. No additional typeclass, nonemptiness,
positivity, dimension, regularity, slot-validity or denominator hypotheses were introduced.
The direct exports have only `IsOpen S`, `e.NonvanishingOn S`, and `z ∈ S`, as signed.

Every `HamExpr` constructor is handled. Division compiles both operands before inversion;
powers compile the operand even at exponent zero; products compile both children even when
one is zero. The value invariant is global, so the empty-set invocation used in `jet_v0`
vacuates only the derivative obligation, not the value equality. On an open set, equality of
functions supplies equality of ambient derivatives via neighborhood equality. The calculus
rules establish the inverse, exponential and mixed product derivatives; the node/compiler
induction discharges all input invariants. `iteratedFDeriv_two_eq_jetDeriv` correctly identifies
`![u,v]` with `jetDeriv u (jetDeriv v f)`. `phaseBasis_eq_dirVec` transports precisely the signed
phase directions, without a norm or carrier substitution.

No hard step is assumed at an export. `Realizes`, `SlpEnt`, `SlpNode.Sound` and the premises
of `slpFinish_sound`/primitive assembly lemmas are explicit internal invariants, proved for
the actual compilation and never substituted for the signed result.

## Definition classification

The declaration inventory below includes every explicit public declaration (136 total;
86 theorems and 50 definitions/types/structures). The following classifications apply on
the whole declared carrier, with valid-node hypotheses stated separately where required.

- `SlpOp`, `Slp`, `HamJet`, `SlpNode`: ordinary syntax/data, not assumption bundles. Arbitrary
  slot lists are allowed; `SlpNode.Sound` is the explicit validity/semantic predicate.
- `slpConstVal`, `SlpOp.step`, `Slp.vals`, `Slp.val`: total intended semantics. Out-of-range
  action indices and slots return zero as documented; reciprocals use Lean's total inverse.
  Forward references see only the accumulated prefix. No proof exploits a junk value.
- `phaseNat`, `dirVec`, `negKey`: intended index conversion, coordinate directions (zero
  outside the phase range), and pointwise negated key, including short/long key lists.
- `jetDeriv`, `JetSmoothOn`: actual ambient complex Fréchet directional derivative and
  infinite differentiability on the set. Open-set assumptions justify ambient derivatives.
- `slpOv`, `SlotOk`, `Realizes`, `SlpEnt`, `SlpNode.Sound`: transparent evaluation/validity
  predicates. `none` denotes mathematical zero, while a present slot requires a strict bound.
  `SlpNode.Sound.val` is unconditional in the evaluation point.
- `slpEmit`, `slpAddO`, `slpMulO`, `slpScaleO`: append-only builders and legitimate zero
  folding. Dropping a derivative computation preserves the existing program prefix.
- `SlpComp`, `slpPure`, `slpCAdd`, `slpCMul`, `slpCScale`, `slpMapSt`, `slpTab1`, `slpTab2`:
  ordinary state threading and finite rectangular table construction. Arbitrary computations
  need the explicit `SlpEnt` specifications; none is assumed automatically valid.
- `SlpNode.get1/get2`, `slpFinish`, and all `slp*Node`, `slpInvTail`, `slpCombine`, `slpTrigChar`
  builders: intended slot lookup/assembly. Generic inputs need the documented soundness
  invariants. Each semantic claim is proved for the corresponding builder inputs.
- `slpCompile`, `HamExpr.jet`: structural compilation for every expression, followed by
  conversion of folded entries to the actual initial zero slot. The d3 table is deliberately
  empty for B1 and makes no third-order claim.

## Per-declaration inventory

Each row is a distinct explicit public declaration. “D §D” denotes the signed surface;
“B1 implementation” denotes the internal construction/calculus supporting that surface,
not an additional blueprint theorem falsely claimed to be implemented. Source links give
exact declaration lines; definitions are classified above.

| Node | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| D §D | [`SlpOp`](../../../../KAM/Certificate/Expr/Slp.lean#L28) | PASS | Signed surface matched. |
| D §D | [`Slp`](../../../../KAM/Certificate/Expr/Slp.lean#L37) | PASS | Signed surface matched. |
| B1 implementation | [`slpConstVal`](../../../../KAM/Certificate/Expr/Slp.lean#L41) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`SlpOp.step`](../../../../KAM/Certificate/Expr/Slp.lean#L45) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`Slp.vals`](../../../../KAM/Certificate/Expr/Slp.lean#L55) | PASS | Transparent intended data/construction; see classification. |
| D §D | [`Slp.val`](../../../../KAM/Certificate/Expr/Slp.lean#L59) | PASS | Signed surface matched. |
| D §D | [`HamJet`](../../../../KAM/Certificate/Expr/Slp.lean#L66) | PASS | Signed surface matched. |
| D §D | [`phaseNat`](../../../../KAM/Certificate/Expr/Slp.lean#L74) | PASS | Signed surface matched. |
| B1 implementation | [`Slp.vals_append_prefix`](../../../../KAM/Certificate/Expr/Slp.lean#L78) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`Slp.vals_append`](../../../../KAM/Certificate/Expr/Slp.lean#L87) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`Slp.vals_length`](../../../../KAM/Certificate/Expr/Slp.lean#L93) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`Slp.val_append`](../../../../KAM/Certificate/Expr/Slp.lean#L101) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`Slp.vals_snoc`](../../../../KAM/Certificate/Expr/Slp.lean#L110) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`Slp.val_snoc_self`](../../../../KAM/Certificate/Expr/Slp.lean#L116) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`jetDeriv`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L33) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`JetSmoothOn`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L36) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`JetSmoothOn.differentiableAt`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L39) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`JetSmoothOn.jetDeriv`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L43) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`JetSmoothOn.add`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L48) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`JetSmoothOn.mul`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L51) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`JetSmoothOn.cexp`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L54) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`JetSmoothOn.inv`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L57) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`JetSmoothOn.const`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L61) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`JetSmoothOn.congr`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L63) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`jetDeriv_const`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L66) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`jetDeriv_congr`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L69) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`jetDeriv_add`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L75) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`jetDeriv_mul`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L87) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`jetDeriv_cexp`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L101) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`jetDeriv_inv`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L111) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`dirVec`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L126) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`phaseBasis_eq_dirVec`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L130) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`phaseNat_lt`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L142) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`iteratedFDeriv_two_eq_jetDeriv`](../../../../KAM/Certificate/Expr/DiffCalculus.lean#L148) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpEmit`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L30) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpAddO`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L33) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpMulO`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L39) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpScaleO`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L44) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpOv`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L51) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`SlotOk`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L56) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`Realizes`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L61) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`SlotOk.mono`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L65) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`Realizes.mono`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L74) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`Realizes.congr`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L85) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`Realizes.none`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L89) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpEmit_prefix`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L92) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpEmit_realizes`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L95) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpAddO_spec`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L103) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpMulO_spec`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L127) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpScaleO_spec`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L151) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpMapSt`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L176) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpMapSt_spec`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L184) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`SlpComp`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L209) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpPure`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L212) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpCAdd`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L215) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpCMul`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L221) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpCScale`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L227) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`SlpEnt`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L232) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`SlpEnt.pure`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L236) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`SlpEnt.congr`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L240) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`SlpEnt.add`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L244) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`SlpEnt.mul`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L253) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`SlpEnt.scale`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L262) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpTab1`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L271) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpTab2`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L275) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpTab1_spec`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L279) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpTab2_spec`](../../../../KAM/Certificate/Expr/DiffBuild.lean#L294) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`JetSmoothOn.neg`](../../../../KAM/Certificate/Expr/DiffNode.lean#L34) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`jetDeriv_neg`](../../../../KAM/Certificate/Expr/DiffNode.lean#L37) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`jetDeriv2_mul`](../../../../KAM/Certificate/Expr/DiffNode.lean#L47) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`jetDeriv2_add`](../../../../KAM/Certificate/Expr/DiffNode.lean#L58) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`jetDeriv2_cexp`](../../../../KAM/Certificate/Expr/DiffNode.lean#L67) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`jetDeriv2_inv`](../../../../KAM/Certificate/Expr/DiffNode.lean#L79) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`jetDeriv_modePhase`](../../../../KAM/Certificate/Expr/DiffNode.lean#L99) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`jetSmoothOn_modePhase`](../../../../KAM/Certificate/Expr/DiffNode.lean#L117) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`jetDeriv_char`](../../../../KAM/Certificate/Expr/DiffNode.lean#L121) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`jetDeriv2_char`](../../../../KAM/Certificate/Expr/DiffNode.lean#L137) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`modePhase_dirVec`](../../../../KAM/Certificate/Expr/DiffNode.lean#L152) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`SlpNode`](../../../../KAM/Certificate/Expr/DiffNode.lean#L173) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`SlpNode.get1`](../../../../KAM/Certificate/Expr/DiffNode.lean#L179) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`SlpNode.get2`](../../../../KAM/Certificate/Expr/DiffNode.lean#L182) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`SlpNode.Sound`](../../../../KAM/Certificate/Expr/DiffNode.lean#L185) | PASS | Explicit invariant, constructed at use sites. |
| B1 implementation | [`SlpNode.Sound.mono`](../../../../KAM/Certificate/Expr/DiffNode.lean#L193) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`SlpNode.Sound.realizes_v`](../../../../KAM/Certificate/Expr/DiffNode.lean#L203) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpFinish`](../../../../KAM/Certificate/Expr/DiffNode.lean#L208) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpFinish_sound`](../../../../KAM/Certificate/Expr/DiffNode.lean#L214) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpConstNode`](../../../../KAM/Certificate/Expr/DiffNode.lean#L236) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpConstNode_sound`](../../../../KAM/Certificate/Expr/DiffNode.lean#L240) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`jetDeriv_action`](../../../../KAM/Certificate/Expr/DiffNode.lean#L256) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`dirVec_snd`](../../../../KAM/Certificate/Expr/DiffNode.lean#L265) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpActionNode`](../../../../KAM/Certificate/Expr/DiffNode.lean#L282) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpActionNode_sound`](../../../../KAM/Certificate/Expr/DiffNode.lean#L286) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpCharNode`](../../../../KAM/Certificate/Expr/DiffNode.lean#L312) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpCharNode_sound`](../../../../KAM/Certificate/Expr/DiffNode.lean#L321) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpAddNode`](../../../../KAM/Certificate/Expr/DiffNode.lean#L368) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpAddNode_sound`](../../../../KAM/Certificate/Expr/DiffNode.lean#L373) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpMulNode`](../../../../KAM/Certificate/Expr/DiffNode.lean#L398) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpMulNode_sound`](../../../../KAM/Certificate/Expr/DiffNode.lean#L409) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpExpNode`](../../../../KAM/Certificate/Expr/DiffNode.lean#L443) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpExpNode_sound`](../../../../KAM/Certificate/Expr/DiffNode.lean#L451) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpInvTail`](../../../../KAM/Certificate/Expr/DiffNode.lean#L479) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpConstVal_rat`](../../../../KAM/Certificate/Expr/DiffNode.lean#L488) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpInvTail_sound`](../../../../KAM/Certificate/Expr/DiffNode.lean#L491) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpInvNode`](../../../../KAM/Certificate/Expr/DiffNode.lean#L528) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpInvNode_sound`](../../../../KAM/Certificate/Expr/DiffNode.lean#L534) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpScaleNode`](../../../../KAM/Certificate/Expr/Diff.lean#L37) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpScaleNode_sound`](../../../../KAM/Certificate/Expr/Diff.lean#L41) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpExpScaleNode`](../../../../KAM/Certificate/Expr/Diff.lean#L51) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpExpScaleNode_sound`](../../../../KAM/Certificate/Expr/Diff.lean#L55) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpCombine`](../../../../KAM/Certificate/Expr/Diff.lean#L64) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpCombine_sound`](../../../../KAM/Certificate/Expr/Diff.lean#L70) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpPowNode`](../../../../KAM/Certificate/Expr/Diff.lean#L84) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpPowNode_sound`](../../../../KAM/Certificate/Expr/Diff.lean#L88) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`negKey`](../../../../KAM/Certificate/Expr/Diff.lean#L109) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`modePhase_negKey`](../../../../KAM/Certificate/Expr/Diff.lean#L111) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpTrigNode`](../../../../KAM/Certificate/Expr/Diff.lean#L122) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpTrigChar`](../../../../KAM/Certificate/Expr/Diff.lean#L128) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`slpDivNode`](../../../../KAM/Certificate/Expr/Diff.lean#L134) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`JetSmoothOn.charFn`](../../../../KAM/Certificate/Expr/Diff.lean#L137) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpTrigNode_sound`](../../../../KAM/Certificate/Expr/Diff.lean#L141) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpTrigChar_sound`](../../../../KAM/Certificate/Expr/Diff.lean#L153) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpDivNode_sound`](../../../../KAM/Certificate/Expr/Diff.lean#L165) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`cos_eq_exp`](../../../../KAM/Certificate/Expr/Diff.lean#L174) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`sin_eq_exp`](../../../../KAM/Certificate/Expr/Diff.lean#L182) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpCompile`](../../../../KAM/Certificate/Expr/Diff.lean#L191) | PASS | Transparent intended data/construction; see classification. |
| B1 implementation | [`HamExpr.jetSmoothOn`](../../../../KAM/Certificate/Expr/Diff.lean#L222) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`HamExpr.nonvanishingOn_empty`](../../../../KAM/Certificate/Expr/Diff.lean#L226) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpCompile_sound`](../../../../KAM/Certificate/Expr/Diff.lean#L240) | PASS | Kernel-checked supporting theorem; source premises only. |
| D §D | [`HamExpr.jet`](../../../../KAM/Certificate/Expr/Diff.lean#L332) | PASS WITH NOTES | Signed surface matched. |
| B1 implementation | [`slpCompile_prefix`](../../../../KAM/Certificate/Expr/Diff.lean#L340) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`zero_slot_val`](../../../../KAM/Certificate/Expr/Diff.lean#L344) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`slpOv_eq_val`](../../../../KAM/Certificate/Expr/Diff.lean#L353) | PASS | Kernel-checked supporting theorem; source premises only. |
| B1 implementation | [`list_getD_map`](../../../../KAM/Certificate/Expr/Diff.lean#L360) | PASS | Kernel-checked supporting theorem; source premises only. |
| D §D | [`HamExpr.jet_v0`](../../../../KAM/Certificate/Expr/Diff.lean#L364) | PASS | Signed surface matched. |
| D §D | [`HamExpr.jet_d1`](../../../../KAM/Certificate/Expr/Diff.lean#L368) | PASS | Signed surface matched. |
| D §D | [`HamExpr.jet_d2`](../../../../KAM/Certificate/Expr/Diff.lean#L384) | PASS | Signed surface matched. |

## Independent checks and exact receipts

All Lean/Lake invocations were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No source files were changed, no root regenerated, and no package caches or frozen files touched.
No resource overrides were used.

1. Targeted compile gate (exit **0**):

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-soexprb KAM.Certificate.Expr.Diff
```

```text
[inp-gate] slot 1 acquired 14:25:22 for KAM.Certificate.Expr.Diff
⚠ [2896/2901] Replayed KAM.Certificate.Expr.Basic
warning: KAM/Certificate/Expr/Basic.lean:85:5: Variable name `hS` is not explicitly referenced.
Build completed successfully (2901 jobs).
```

The build also printed the standard unused-variable suggestions and linter help for that
inherited Basic warning. None of the five audited files produced a warning.

2. Signed-statement, semantics, evaluability and axiom probe (final exit **0**):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOExprAudit.lean > .lake/abi-scratch/SOExprAudit.log 2>&1
```

The scratch file copied all three signed theorem statements, applied the actual exports,
and issued `#print axioms` for every explicit new public theorem. Its 86 output lines are
reproduced below. All dependencies belong to `{propext, Classical.choice, Quot.sound}`;
`slpEmit_prefix` uses no axioms and `list_getD_map` uses only `propext`.
Initial scratch-only elaboration mistakes (missing `noncomputable`, a simplification and
ambiguous dotted constructors) were corrected; they did not require a package change.

Additional successful kernel checks in that same probe:

- `Slp.val` unfolds to the fold/getD semantics, including out-of-range action, missing add
  operands and inverse of a missing operand. Total inverse at zero agrees with Lean semantics.
- `ex := (cosMode [1] + exp action0) / (1 + action0^2)` in dimension 1 has d1 length 2,
  d2 length 2, and d2 row lengths `[2,2]`, by `decide +kernel`.
- `sin (cos (cosMode [1,2] + sinMode [0,1]))` in dimension 2 has d1 length 4 and d2 row
  lengths `[4,4,4,4]`, by `decide +kernel`.
- Both `0 * (1/0)` and `(1/0)^0` retain an `inv` operation, by `decide +kernel`.
- The zero-dimensional constant expression has an empty d1 table, by `decide +kernel`.

These establish kernel reduction of the compiler's concrete syntax/table computations.
`Slp.val` is a noncomputable mathematical complex-valued denotation, as expected with π and
complex exponentials; this is not a claim that transcendental values execute numerically.
SO-BALL/SO-REPLAY supply separate executable arithmetic and performance gates.

```text
'KAM.Certificate.Slp.vals_append_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.vals_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.vals_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.val_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.vals_snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.val_snoc_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.JetSmoothOn.differentiableAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.JetSmoothOn.jetDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.JetSmoothOn.add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.JetSmoothOn.mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.JetSmoothOn.cexp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.JetSmoothOn.inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.JetSmoothOn.const' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.JetSmoothOn.congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_cexp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.phaseBasis_eq_dirVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.phaseNat_lt' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.iteratedFDeriv_two_eq_jetDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.SlotOk.mono' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.Realizes.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Realizes.congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Realizes.none' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpEmit_prefix' does not depend on any axioms
'KAM.Certificate.slpEmit_realizes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpAddO_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpMulO_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpScaleO_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpMapSt_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.SlpEnt.pure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.SlpEnt.congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.SlpEnt.add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.SlpEnt.mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.SlpEnt.scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpTab1_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpTab2_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.JetSmoothOn.neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv2_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv2_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv2_cexp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv2_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_modePhase' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetSmoothOn_modePhase' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_char' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv2_char' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modePhase_dirVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.SlpNode.Sound.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.SlpNode.Sound.realizes_v' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpFinish_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpConstNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_action' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.dirVec_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpActionNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpCharNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpAddNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpMulNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpExpNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpConstVal_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpInvTail_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpInvNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpScaleNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpExpScaleNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpCombine_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpPowNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modePhase_negKey' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.JetSmoothOn.charFn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpTrigNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpTrigChar_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpDivNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cos_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sin_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.jetSmoothOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.nonvanishingOn_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpCompile_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpCompile_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.zero_slot_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpOv_eq_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.list_getD_map' depends on axioms: [propext]
'KAM.Certificate.HamExpr.jet_v0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.jet_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.jet_d2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Single kernel replay invocation (exit **0**):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Expr.Slp KAM.Certificate.Expr.DiffCalculus KAM.Certificate.Expr.DiffBuild KAM.Certificate.Expr.DiffNode KAM.Certificate.Expr.Diff > .lake/abi-scratch/SOExprKernel.log 2>&1
```

```text
replaying KAM.Certificate.Expr.Diff
replaying KAM.Certificate.Expr.DiffNode
replaying KAM.Certificate.Expr.DiffBuild
replaying KAM.Certificate.Expr.DiffCalculus
replaying KAM.Certificate.Expr.Slp
```

4. Repository lint (exit **1**, solely the explicitly permitted generated-root exception):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh > .lake/abi-scratch/SOExprLint.log 2>&1
```

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1302 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

5. Protected paths and whitespace:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit **0**, no output. The full comparison changes only the five named audit files.
A direct forbidden-token/import scan with `rg` over those five files returned exit **1**,
no matches, for
`Provider|Frozen|DRAFT_SORRY|sorry|admit|axiom|unsafe|opaque|set_option|native_decide|EuclideanSpace`.
There are no direct provider or frozen-theorem imports. Inherited frozen definitions are
ordinary sealed definitions; the axiom probes exclude dependence on any unproved theorem.

| File | Lines | Maximum Unicode characters per line |
|---|---:|---:|
| `Slp.lean` | 125 | 99 |
| `DiffCalculus.lean` | 163 | 99 |
| `DiffBuild.lean` | 316 | 100 |
| `DiffNode.lean` | 566 | 100 |
| `Diff.lean` | 412 | 100 |

All five have copyright, `module`, public imports, module docstring, and exposed public
section. All declarations are inside `KAM.Certificate`; no root declarations or new global
notations/instances are introduced. A Python declaration-name scan compared all 136 explicit
relative declaration names against declarations in every other KAM module and Mathlib source
(using `def|abbrev|structure|inductive|theorem|lemma`, with visibility/noncomputability prefixes):
`Existing declaration relative-name collisions: []`. A supplemental `rg` search for generic
new names (`Realizes`, `SlotOk`, `dirVec`, `negKey`, `jetDeriv`, `JetSmoothOn`, `SlpComp`, `SlpEnt`,
`cos_eq_exp`, `sin_eq_exp`, `list_getD_map`) outside the five files likewise returned no matches.
No harmful name shadowing was found.

## Notes, source discrepancies, and limits

1. **Optimization wording exceeds this implementation.** `Slp.lean:64` repeats the signed
   HamJet docstring, “Forward-mode differentiation with sharing, zero/constant folding and
   dependency pruning”. `Diff.lean:16–17` instead says “No operation is ever dropped from the
   program (only derivative slots that vanish identically are folded)”, and the handoff explicitly
   defers pruning. Inspection confirms append-only construction, local zero/coefficient folding,
   and shared value/derivative slots for each recursively compiled child; there is no general
   dependency-pruning or common-subexpression-interning pass. This is an implementation/design
   optimization discrepancy, not a weakened signed theorem. The signed B1 semantic slice is
   complete; do not claim full implementation of every optimization in that docstring or any
   performance bound. Keeping source divisor validation slots satisfies the safety obligation
   of design §1.4 (lines 132–135); future pruning must preserve it.
2. **B2 remains outstanding by explicit scope.** `Diff.lean:338` assigns `d3 := []`. No
   `HamExpr.jet_d3` theorem is supplied or claimed. B1 passes only through order two, exactly as
   assigned in the handoff and the design package split; the full order-three jet is not delivered.
3. **Internal module split.** `DiffCalculus`, `DiffBuild`, `DiffNode` are additional implementation
   modules behind the `Diff` facade, a harmless organizational deviation from the design's two-file
   outline. Each stays below the size cap.
4. **No pinned mathematical-source erratum found.** This slice formalizes explicit expression
   semantics and standard calculus rather than a new quoted external source theorem. No frozen
   statement was found false, no premise was silently repaired, and no source defect was introduced.
5. **Future consumer obligations remain future work.** Prefix preservation and the two folding
   counterexample probes support divisor retention, but the general successful-ball-evaluation
   implication `nonvanishingOn_of_balls` belongs to SO-BALL. B1 does not prove that theorem or
   validate certificate replay costs. The unconditional `jet_v0` at zero denominators is the signed
   total-field equality; it supplies no holomorphy at those points.

Final disposition: accept the signed B1 package with the documented optimization, B2, and
permitted generated-root notes. No code repair is required for its signed first/second-order
soundness statements. No new theorem anchor is sealed by this audit.
