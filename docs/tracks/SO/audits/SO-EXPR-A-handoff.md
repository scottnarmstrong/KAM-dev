# SO-EXPR-A prover handoff (branch inp-soexpr, 0d5b57af; track SO package run by the main orchestrator)


Files: `KAM/Certificate/Expr/Basic.lean` (new, 208 lines), namespace `KAM.Certificate`.
Declarations (types verbatim from SOSignatures §D): `HamExpr`, `modePhase`, `HamExpr.eval`,
`HamExpr.NonvanishingOn`, `HamExpr.contDiffOn_eval`, `HamExpr.eval_add_int`, `HamExpr.eval_real`,
`certDomain`, `isOpen_certDomain`, `certDomain_add_int`. Extra helpers: `contDiff_modePhase`,
`modePhase_add_int`, `HamExpr.exists_real_eval` (reality as an explicit real value).
Approach: structural induction; holomorphy via ContDiffOn algebra (div uses the NonvanishingOn
denominator clause); translation via `cos/sin_add_int_mul_two_pi`; openness via finite
intersections of strict inequalities. PhaseBasis imported (via `KAM.Certificate.PhaseBasis`), not redefined.
Checks: `inp_lake_build.sh ... KAM.Certificate.Expr.Basic` succeeds; no sorry. lint_sources.sh:
check_lean_modules PASS, frozen guard OK, ABI OK, no >100-col lines; only complaint is
"KAM.lean is out of date" (generated; not edited by rule 10).
Axioms (all five main results): [propext, Classical.choice, Quot.sound].
Uncertainties: one linter warning, `hS` unused in `contDiffOn_eval` (signature verbatim, hypothesis
is needed only by the signed shape; ContDiffOn on non-open S works too). Short-name grep clean
(only `CertPoly.eval_add_int`/`CertRealPoly.eval_real` share the suffix, namespaced differently).
Imports Trigonometric.Deriv and ExpDeriv explicitly. Errata/deviations: none.

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md; design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md, Revision 4); draft signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean. Signature file section D, the Expr/Basic slice (HamExpr, modePhase, HamExpr.eval, NonvanishingOn, contDiffOn_eval, eval_add_int, eval_real, certDomain and its lemmas). Owner ruling O2: division is included, by an expression certified nonvanishing on the domain. The branch is stacked on inp-sopbase (SO-PBASE, passed, landing); audit only Expr/Basic. Check that eval is the literal mathematical Hamiltonian (no fallback or default branch on division: what does eval return where the divisor vanishes, and is every theorem that matters stated under NonvanishingOn?), that contDiffOn_eval is analyticity-strength as the design needs, and that eval_real and eval_add_int are unconditional.

AUDIT FOCUS: the package's signed declarations match the draft signatures verbatim; every proof is sound with no added premise; the slice the design assigns to these modules is complete. Audit ONLY KAM/Certificate/Expr/Basic.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100, no native_decide or axiom.
