# SO-EXPR-B2 prover handoff (branch inp-soexprc, c1f58948; track SO package run by the main orchestrator)


## Files
- NEW `KAM/Certificate/Expr/DiffCalculus3.lean` (235 lines): the second-order rules MOVED here verbatim from
  DiffNode (`JetSmoothOn.neg`, `jetDeriv_neg`, `jetDeriv2_{mul,add,cexp,inv}`), plus new `jetDeriv_congr2`,
  `jetDeriv_cmul`, `jetDeriv3_{add,mul,cexp,inv}`, `jetDeriv_inv_sq/cube`, `iteratedFDeriv_three_eq_jetDeriv`.
- `DiffBuild.lean` (343): `slpTab3`, `slpTab3_spec`.
- `DiffNode.lean` (669): `SlpNode` gains `d3`/`get3`; `Sound` gains `d3`; `slpFinish` takes `c3`;
  all seven primitive nodes get third-derivative entries (`jetDeriv3_char`, `slpCross`, `slpMulD3`,
  `slpExpD3`, `slpInvD3`); `slpInvNode` now also emits `w⁴` (`slpInvPre`, `slpInvPre_spec`).
- `Diff.lean` (445): `HamExpr.jet.d3` filled; `HamExpr.jet_d3` proved exactly as signed.
  Wrapper nodes (scale, combine, pow, trig, div) and `slpCompile_sound` unchanged.

## Approach
Extend the existing jet node by one table; d3 entries follow the Leibniz/Faà di Bruno formulas
(product: 8 terms; exp: `E(f_i f_j f_k + f_ij f_k + f_j f_ik + f_i f_jk + f_ijk)`;
inv: `-6w⁴ f_i f_j f_k + 2w³(cross) - w² f_ijk`). `jet_d3` via `iteratedFDeriv_three_eq_jetDeriv`.

## Checks
- `inp_lake_build.sh ... KAM.Certificate.Expr.Diff`: Build completed successfully, no sorry/error.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI OK, no long lines.
  Only message: "KAM.lean is out of date" (new module DiffCalculus3; KAM.lean is generated, not touched by me).
- `#print axioms` of `HamExpr.jet_v0/jet_d1/jet_d2/jet_d3`: [propext, Classical.choice, Quot.sound] each.
- No set_option, no sorry/native_decide, all files < 700 lines, default heartbeats.

## Uncertainties / notes
- Deviation from the brief's "new files": I edited B1's DiffNode/DiffBuild/Diff (needed: d3 is a field of the
  node); second-order rules were moved to DiffCalculus3 so third-order rules can build on them (names unchanged).
- Output of `jet` grows as (2n)^3 table entries per node; no evaluation/`decide` check done here.
- B1 handoff file was absent in the worktree. No suspected errata in sources.

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md; design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md, Revision 4); draft signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean section D: HamExpr.jet_d3 (the third-order jet), extending SO-EXPR-B1 (landed on inp after its own PASS audit). SCOPE: audit ONLY what this branch adds or changes relative to inp (git diff inp -- KAM): about 31 new declarations, in Expr/{Diff,DiffBuild,DiffNode,DiffCalculus3}.lean. Declarations that landed with SO-EXPR-B1 (e.g. SlpEnt.pure, SlpEnt.mul, SlpEnt.scale, SlpNode.Sound.mono) are out of scope. Check that jet_d3 identifies the compiled program's third-order values with the third iterated derivative of HamExpr.eval in all directions on the open set where every divisor is nonvanishing, with no hypothesis beyond the signed ones. Orchestrator rename: JetSmoothOn.neg -> JetSmoothOn.jetNeg.

AUDIT FOCUS: signed declarations match verbatim; soundness with no added premise; the B2 slice complete. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib among the declarations THIS BRANCH ADDS, no harmful root shadow, lines <= 100, no native_decide or axiom.

## Round 2 (integration fix, commits 3627099d merge of inp + edec1f19)

At landing, SO-EXPR-B2 conflicted with SO-BALL (landed meanwhile; both built on SO-EXPR-B1): B2 changed
slpInvTail_sound (a new hw4 fourth-power witness, a third slpMulO in the inverse-case program) that Ball.lean's
inverse case called. The orchestrator merged inp into this branch; a prover then changed ONLY
KAM/Certificate/Expr/Ball.lean: the proof of slpInvNode_emit_prefix (statement unchanged) now goes through DiffNode's
slpInvPre_spec, plus two new helpers slpMulO_prefix_self and slpInvPre_emit_prefix. All four signed Ball declarations
are unchanged. Builds: Expr.Ball, Tests.Ball, Tests.ComplexExp, Expr.Diff all succeed.
ROUND 2 FOCUS (delta): audit ONLY the Ball.lean diff (git diff 3627099d -- KAM/Certificate/Expr/Ball.lean) and the merge
(no other file changed by it beyond inp's own content): are the signed Ball declarations byte-identical to the signed
versions, is the new proof sound with no added premise, are the two helpers hygienic (names, lines)? Verdict.
