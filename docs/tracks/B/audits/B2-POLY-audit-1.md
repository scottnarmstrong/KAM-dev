# B2-POLY independent package audit 1

**Verdict: FAIL (F1: one source-width violation).** Mathematical interfaces: PASS WITH NOTES;
no mathematical counterexample to an exported statement found. No frozen anchor or provider is
part of this package, so provider/frozen type equality and seal-body probes are not applicable.
Nothing is declared seal-ready by this audit.

Audited worktree: `/root/code/KAM-inp-b2poly`. HEAD:
`168b370456fd6ad3a2518d48ba314755e800f961`; comparison ref `inp` at inspection:
`a8005126dc3cb9ad964977b2c575184ab9034b9c`; merge base:
`9aff52db9dd863219109b3e6d738965f36b2bca0`. Scope is precisely `git diff inp...HEAD`:
five new Poly modules and the package handoff. The user-specified report destination overrides
the generic audit brief's main-worktree destination. Only this report and temporary
`.lake/abi-scratch/` files are authored by this audit; no git mutation or source repair.

Read: AGENTS, PLAN, DECISIONS; the package audit brief and AUDIT FOCUS; B2-POLY and B1-common
briefs; Track B SPEC, OWNER-DECISIONS and FREEZE-PROPOSAL; program-b-plan §3.1–3.2;
all five new modules and the existing Canonical.Setting, HamiltonianVectorField and
OscillatorAction definitions. Track B has no `statement.md` or dedicated blueprint-B packet
here; the exact B2 brief controls these infrastructure statements, under OD-B7/B8/B9.
The I/N/P frozen-theorem boilerplate does not introduce a nonexistent B anchor.

## Findings

**F1 — FAIL, required landing hygiene.** `KAM/EffectiveStability/Poly.lean:16` is 101
Unicode characters (limit 100):

```text
Facade importing `Poly.Basic` (algebra, `cartNormalize`, `cartEqCheck`), `Poly.Deriv` (formal partial
```

Rewrap this docstring line. This is the only new-package lint failure beyond the expressly
permitted stale generated root. The handoff's post-handoff claim that the facade docstring
was rewrapped does not establish compliance on these audited bytes. No source was edited.

**N1 — accepted typing repair, with an implementation note.** `CartFits n P`
(`Basic.lean:342`) asserts only that exponent tails outside the evaluation dimension vanish.
It has no evaluation, bracket identity, bound or trajectory field, hence is not a
conclusion-shaped assumption. It is finitely decidable mathematically: for each monomial
check both lists only at indices `n ≤ k < max a.length b.length`; all larger entries are
zero by `getD`. This package supplies propagation lemmas, but no executable `Decidable`
instance/Boolean typing checker or finite-range equivalence. A future checker must supply
that finite test and its proof or establish Fits from its constructors; do not assume
that unrestricted `decide (CartFits n P)` is provided by this API.

The original unguarded B2 brief's bracket semantics is false: take `n = 1`, `P = q₁`,
`Q = p₁` (zero-based index 1, outside Fin 1). Both evaluations are constant 1, their
analytic bracket is 0, but the formal bracket evaluates to 1. Similarly `P = q₁`,
`r = s = [0]`, `z = 0` has evaluation 1 but majorant 0. Thus the brief's statement that
out-of-dimension exponents are ignored “that is fine” requires a qualification for these
operations. The handoff explicitly reports and repairs this defect. This is a design-brief
correction, not an erratum in a pinned published source.

The left-input Fits guard suffices for one bracket because every omitted summand has
both left derivatives zero. No guard is needed on its right input. Iteration propagates
Fits from both χ and P. Action-left bracket evaluation needs no Fits on P because the
action fits automatically. The bound theorem uses Fits on P to propagate it to that
formal bracket. These are sufficient structural conditions; no minimality claim is made
(e.g. zero-coefficient monomials can violate Fits harmlessly).

**N2 — scope and stronger interfaces.** `contDiff_eval` holds for every
`k : WithTop ℕ∞`, including analytic order, stronger than a single requested order.
Derivative and norm statements over `RCLike` cover real and complex carriers.
Explicit nonnegative-radius premises are redundant under the norm bounds and were
correctly removed. `cartEval_bracket_action` works in any commutative ℚ-algebra.
`cartEqCheck` promises soundness only, not completeness or a sorted canonical form.
Dimension is absent from CartPoly as required by the detailed representation brief;
OD-B8's earlier shorthand `CartPoly n` is implemented using separate Fits typing data.

## Mathematical and consumer review

Normalization preserves evaluation in every dimension and every commutative ℚ-algebra:
trimming preserves every padded exponent; insertion adds coefficients only for identical
keys; folding preserves the sum; filtering removes only zero coefficients. An empty
normalized difference therefore evaluates to zero. There is no Fits premise on this
soundness theorem, no hidden nonzero-point restriction and no reliance on a rational-only
sample test. Equality checking does not compare evaluations at finitely many points.

Formal derivatives decrement only positive stored exponents. The guard ensures that
`List.set` cannot silently miss an index; exponent zero contributes zero even at a zero
coordinate. Directional polynomial differentiation and uniqueness of the Fréchet
derivative establish the full formula; coordinate formulas specialize that formula.
No Fits guard is needed for indices in Fin n.

The bracket is ∂q P ∂p Q − ∂p P ∂q Q. The real frozen field is (∂p Q, −∂q Q),
so it equals DP[X_Q]. The complex bracket and repeated right bracketing match
`KAM.Canonical.poissonBracket` and `.adPow` definitionally in their order and sign.
`cartAction j` evaluates to `(p_j²+q_j²)/2`, with the frozen oscillator arguments
in the order `z.2 z.1`. Its bracket is exactly `q_j ∂p_j P − p_j ∂q_j P`;
substituting the derivative evaluation lemmas supplies B1-E's `hRη` expression.
This pays the polynomial part of a future residual bound, not the analytic tail,
chart, ODE continuation or the eventual one-step soundness theorem.

The majorant takes absolute rational coefficients, sums every monomial, and multiplies
padded radii over the maximum exponent-list length. At missing indices exponents zero
produce 1 even when the radius is zero. Fits removes factors outside Fin n; within
Fin n the norm hypotheses force the used radii nonnegative. Triangle/product
inequalities then give the asserted bound, including negative coefficients and n = 0.
Outside a valid nonnegative-radius box the total rational expression need not be a
nonnegative majorant; no theorem claims otherwise. The radius bridge follows from
p² + q² ≤ 2b ≤ r² and r ≥ 0, with zero actions permitted.

The KAM import closure has 27 modules, no provider, no frozen theorem. Its nine frozen
imports are definitions and all are SEALED: ComplexStrip, HamiltonianVectorField,
HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero,
SymplecticForm, and Planetary.OscillatorAction. There is no DRAFT_SORRY dependency.

## Definition classification and declaration review

Every new definition is classified in the following table, together with every new named
public theorem (118 rows: 33 definitions/abbreviations/structures and 85 theorems).
Names are fully qualified; line references are relative to `KAM/EffectiveStability/Poly/`.
PASS means the stated infrastructure fact/object matches the detailed brief, subject to N1/N2.
There are no fallback objects used to bypass a mathematical claim. Kernel arithmetic
operations live in an exposed noncomputable section, but their finite list/rational
bodies remain reducible and were exercised with `decide +kernel`.

| Node | Declaration | Location | Verdict | Classification / review |
|---|---|---|---|---|
| algebra / normalization / typing | `KAM.EffectiveStability.CartMono` | Basic.lean:38 | PASS | Finite exponent lists and exact rational coefficient; full intended carrier. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly` | Basic.lean:48 | PASS | Finite list of CartMono; dimension-free sparse sum. |
| algebra / normalization / typing | `KAM.EffectiveStability.addPad` | Basic.lean:51 | PASS | Direct finite list/rational algebra constructor; intended on whole carrier. |
| algebra / normalization / typing | `KAM.EffectiveStability.getD_addPad` | Basic.lean:56 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.unitExp` | Basic.lean:69 | PASS | Direct finite list/rational algebra constructor; intended on whole carrier. |
| algebra / normalization / typing | `KAM.EffectiveStability.getD_unitExp` | Basic.lean:71 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.trimExp` | Basic.lean:82 | PASS | Finite key merging/trimming/zero filtering; evaluation preserved. |
| algebra / normalization / typing | `KAM.EffectiveStability.getD_trimExp` | Basic.lean:86 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartMono.powProd` | Basic.lean:106 | PASS | Total finite-dimensional evaluation; ignores outside exponents as specified. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartMono.cartMonoEval` | Basic.lean:110 | PASS | Total finite-dimensional evaluation; ignores outside exponents as specified. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartMono.cartMonoMul` | Basic.lean:114 | PASS | Direct finite list/rational algebra constructor; intended on whole carrier. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartMono.cartMonoTrim` | Basic.lean:117 | PASS | Finite key merging/trimming/zero filtering; evaluation preserved. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartMono.powProd_congr` | Basic.lean:119 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartMono.powProd_addPad` | Basic.lean:125 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartMono.cartMonoEval_mul` | Basic.lean:134 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartMono.cartMonoEval_trim` | Basic.lean:140 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval` | Basic.lean:152 | PASS | Total finite-dimensional evaluation; ignores outside exponents as specified. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartAdd` | Basic.lean:155 | PASS | Direct finite list/rational algebra constructor; intended on whole carrier. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartNeg` | Basic.lean:158 | PASS | Direct finite list/rational algebra constructor; intended on whole carrier. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartSub` | Basic.lean:161 | PASS | Direct finite list/rational algebra constructor; intended on whole carrier. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartSmul` | Basic.lean:164 | PASS | Direct finite list/rational algebra constructor; intended on whole carrier. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartMul` | Basic.lean:167 | PASS | Direct finite list/rational algebra constructor; intended on whole carrier. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartConst` | Basic.lean:170 | PASS | Direct finite list/rational algebra constructor; intended on whole carrier. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartQVar` | Basic.lean:173 | PASS | Direct finite list/rational algebra constructor; intended on whole carrier. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartPVar` | Basic.lean:176 | PASS | Direct finite list/rational algebra constructor; intended on whole carrier. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartAction` | Basic.lean:179 | PASS | Direct finite list/rational algebra constructor; intended on whole carrier. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_nil` | Basic.lean:181 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_cons` | Basic.lean:184 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_add` | Basic.lean:188 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_neg` | Basic.lean:192 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_sub` | Basic.lean:200 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_smul` | Basic.lean:204 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_mul_mono` | Basic.lean:212 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_mul` | Basic.lean:218 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_const` | Basic.lean:226 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.powProd_unit_q` | Basic.lean:231 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.powProd_unit_p` | Basic.lean:242 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_qVar` | Basic.lean:252 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_pVar` | Basic.lean:256 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_action_eq` | Basic.lean:260 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_action` | Basic.lean:268 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartInsertMono` | Basic.lean:278 | PASS | Finite key merging/trimming/zero filtering; evaluation preserved. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_insertMono` | Basic.lean:283 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartMerge` | Basic.lean:296 | PASS | Finite key merging/trimming/zero filtering; evaluation preserved. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_merge` | Basic.lean:298 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_trimmap` | Basic.lean:306 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_filter_ne` | Basic.lean:312 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartNormalize` | Basic.lean:322 | PASS | Finite key merging/trimming/zero filtering; evaluation preserved. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_normalize` | Basic.lean:325 | PASS | All dimensions and commutative rational algebras; no Fits guard. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEqCheck` | Basic.lean:330 | PASS | Empty normalized difference test; unconditional all-carrier soundness. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_eq_of_eqCheck` | Basic.lean:332 | PASS | All dimensions and commutative rational algebras; no Fits guard. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.CartFits` | Basic.lean:342 | PASS | Structural tail-zero typing predicate; finite decision procedure not exported (N1). |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartFits_nil` | Basic.lean:345 | PASS | Structural typing propagation only; no analytic premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartFits_add` | Basic.lean:347 | PASS | Structural typing propagation only; no analytic premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartFits_neg` | Basic.lean:353 | PASS | Structural typing propagation only; no analytic premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartFits_sub` | Basic.lean:358 | PASS | Structural typing propagation only; no analytic premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartFits_smul` | Basic.lean:362 | PASS | Structural typing propagation only; no analytic premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartFits_mul` | Basic.lean:367 | PASS | Structural typing propagation only; no analytic premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartFits_const` | Basic.lean:376 | PASS | Structural typing propagation only; no analytic premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartFits_qVar` | Basic.lean:381 | PASS | Structural typing propagation only; no analytic premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartFits_pVar` | Basic.lean:387 | PASS | Structural typing propagation only; no analytic premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartFits_action` | Basic.lean:393 | PASS | Structural typing propagation only; no analytic premise. |
| algebra / normalization / typing | `KAM.EffectiveStability.CartPoly.cartEval_ofReal` | Basic.lean:405 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| formal derivatives | `KAM.EffectiveStability.getD_set_of_ne_zero` | Deriv.lean:32 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| formal derivatives | `KAM.EffectiveStability.CartMono.cartMonoDq` | Deriv.lean:46 | PASS | Exact formal derivative; empty list only for zero exponent. |
| formal derivatives | `KAM.EffectiveStability.CartMono.cartMonoDp` | Deriv.lean:51 | PASS | Exact formal derivative; empty list only for zero exponent. |
| formal derivatives | `KAM.EffectiveStability.CartPoly.cartDq` | Deriv.lean:60 | PASS | Exact formal derivative; empty list only for zero exponent. |
| formal derivatives | `KAM.EffectiveStability.CartPoly.cartDp` | Deriv.lean:63 | PASS | Exact formal derivative; empty list only for zero exponent. |
| formal derivatives | `KAM.EffectiveStability.CartPoly.cartDq_nil` | Deriv.lean:65 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| formal derivatives | `KAM.EffectiveStability.CartPoly.cartDp_nil` | Deriv.lean:66 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| formal derivatives | `KAM.EffectiveStability.CartPoly.cartDq_cons` | Deriv.lean:67 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| formal derivatives | `KAM.EffectiveStability.CartPoly.cartDp_cons` | Deriv.lean:70 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| formal derivatives | `KAM.EffectiveStability.CartPoly.cartEval_dq_mono` | Deriv.lean:77 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| formal derivatives | `KAM.EffectiveStability.CartPoly.cartEval_dp_mono` | Deriv.lean:101 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| formal derivatives | `KAM.EffectiveStability.CartPoly.contDiff_eval_mono` | Deriv.lean:130 | PASS | Every regularity order, including analytic; stronger than requested. |
| formal derivatives | `KAM.EffectiveStability.CartPoly.contDiff_eval` | Deriv.lean:141 | PASS | Every regularity order, including analytic; stronger than requested. |
| formal derivatives | `KAM.EffectiveStability.CartPoly.hasDerivAt_eval_mono` | Deriv.lean:152 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| formal derivatives | `KAM.EffectiveStability.CartPoly.hasDerivAt_eval` | Deriv.lean:183 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| formal derivatives | `KAM.EffectiveStability.CartPoly.fderiv_eval_apply` | Deriv.lean:204 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| formal derivatives | `KAM.EffectiveStability.CartPoly.fderiv_eval_q` | Deriv.lean:218 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| formal derivatives | `KAM.EffectiveStability.CartPoly.fderiv_eval_p` | Deriv.lean:226 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.cartWidth` | Bracket.lean:33 | PASS | Maximum stored list length; finite bracket support bound. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.length_le_width` | Bracket.lean:37 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.dq_eq_nil_of_getD` | Bracket.lean:48 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.dp_eq_nil_of_getD` | Bracket.lean:57 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.getD_eq_zero_of_length_le` | Bracket.lean:66 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.getD_eq_zero_of_width` | Bracket.lean:69 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.cartBracket` | Bracket.lean:75 | PASS | Finite formal Poisson bracket / repeated right bracket; semantics under Fits. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.cartAdPow` | Bracket.lean:80 | PASS | Finite formal Poisson bracket / repeated right bracket; semantics under Fits. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.cartFits_flatMap` | Bracket.lean:86 | PASS | Structural typing propagation only; no analytic premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.cartFits_dq` | Bracket.lean:95 | PASS | Structural typing propagation only; no analytic premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.cartFits_dp` | Bracket.lean:107 | PASS | Structural typing propagation only; no analytic premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.cartFits_bracket` | Bracket.lean:119 | PASS | Structural typing propagation only; no analytic premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.cartFits_adPow` | Bracket.lean:125 | PASS | Structural typing propagation only; no analytic premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.dq_eq_nil_of_fits` | Bracket.lean:131 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.dp_eq_nil_of_fits` | Bracket.lean:134 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.cartEval_flatMap` | Bracket.lean:141 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.sum_range_eq_of_zero` | Bracket.lean:149 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.dq_eq_nil_of_width` | Bracket.lean:160 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.dp_eq_nil_of_width` | Bracket.lean:163 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.cartEval_bracket` | Bracket.lean:167 | PASS | Correct sign, order and analytic consumer; typing guard justified (N1). |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.two_half` | Bracket.lean:187 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.cartEval_dq_action` | Bracket.lean:191 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.cartEval_dp_action` | Bracket.lean:212 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.cartEval_bracket_action` | Bracket.lean:235 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.cartEval_bracket_complex` | Bracket.lean:246 | PASS | Correct sign, order and analytic consumer; typing guard justified (N1). |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.cartEval_bracket_real` | Bracket.lean:255 | PASS | Correct sign, order and analytic consumer; typing guard justified (N1). |
| bracket / iteration | `KAM.EffectiveStability.CartPoly.cartEval_adPow_complex` | Bracket.lean:264 | PASS | Correct sign, order and analytic consumer; typing guard justified (N1). |
| majorants / radius bridge | `KAM.EffectiveStability.CartPoly.cartMonoBound` | Bound.lean:27 | PASS | Exact rational absolute-coefficient expression; majorant on guarded boxes. |
| majorants / radius bridge | `KAM.EffectiveStability.CartPoly.cartSupBound` | Bound.lean:32 | PASS | Exact rational absolute-coefficient expression; majorant on guarded boxes. |
| majorants / radius bridge | `KAM.EffectiveStability.CartPoly.norm_algebraMap_rat` | Bound.lean:36 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| majorants / radius bridge | `KAM.EffectiveStability.CartPoly.prod_range_eq_univ` | Bound.lean:39 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| majorants / radius bridge | `KAM.EffectiveStability.CartPoly.norm_eval_mono_le` | Bound.lean:51 | PASS | Genuine guarded majorant, padded zeros and absolute coefficients. |
| majorants / radius bridge | `KAM.EffectiveStability.CartPoly.norm_eval_le_supBound` | Bound.lean:81 | PASS | Genuine guarded majorant, padded zeros and absolute coefficients. |
| majorants / radius bridge | `KAM.EffectiveStability.CartPoly.abs_eval_le_supBound` | Bound.lean:97 | PASS | Genuine guarded majorant, padded zeros and absolute coefficients. |
| majorants / radius bridge | `KAM.EffectiveStability.CartPoly.abs_actionBracket_le_supBound` | Bound.lean:106 | PASS | Genuine guarded majorant, padded zeros and absolute coefficients. |
| majorants / radius bridge | `KAM.EffectiveStability.CartPoly.abs_le_of_action_le` | Bound.lean:116 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |
| majorants / radius bridge | `KAM.EffectiveStability.CartPoly.abs_le_of_oscillatorAction_le` | Bound.lean:122 | PASS | Checked literal auxiliary identity/estimate; no added analytic or conclusion premise. |

Facade `KAM/EffectiveStability/Poly.lean`: FAIL F1 (line width); module header, imports and public section otherwise PASS.
