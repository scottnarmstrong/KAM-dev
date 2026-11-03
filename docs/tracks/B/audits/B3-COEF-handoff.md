# Handoff B3-COEF (branch inp-b3coef, commit b96786d6b)

## Files (all under KAM/EffectiveStability/)
New: `Poly/Coeff.lean` (238 lines), `Poly/QSqrt2Smoke.lean` (66, not in the `Poly` facade, like other smoke modules).
Changed: `Poly.lean` (facade now also imports `Poly.Coeff`), `Poly/{Basic,Deriv,Bracket,Bound,Lie}.lean` (generalized).
No downstream module was edited; no file outside `KAM/EffectiveStability/Poly*`. Largest file 442 lines.

## Approach
- `class CertCoeff (K : Type) extends CommRing K` with fields `decEq : DecidableEq K` (exposed as an instance of
  priority 900, so `DecidableEq K` is available), `toReal : K →+* ℝ`, `toComplex : K →+* ℂ`,
  `toComplex_eq : toComplex k = ((toReal k : ℝ) : ℂ)`, `ofRat : ℚ →+* K`, `toReal_ofRat`, `absUB : K → ℚ`,
  `abs_toReal_le : |toReal k| ≤ absUB k`. Helper `ratCoeff (q : ℚ) : K := ofRat q`.
- Instances: `instCertCoeffRat` (`Rat.commRing`, identity semantics, `absUB = |·|`, marked `@[default_instance]`),
  `instCertCoeffQSqrt2` for `structure QSqrt2 where a b : ℚ` (`a + b√2`; exact `CommRing`, `DecidableEq` derived;
  `absUB x = |a| + |b| * (141422/100000)`, proof via `Real.sqrt 2 ≤ 141422/100000`).
- Evaluation stays generic over any `[CommRing R] [Algebra K R]` (K = ℚ: the old `[Algebra ℚ R]`, so old statements
  are the K = ℚ instances verbatim). For QSqrt2: `instAlgebraQSqrt2Real` / `instAlgebraQSqrt2Complex` are
  `toReal.toAlgebra` / `toComplex.toAlgebra` (so `cartEval` over ℝ/ℂ goes through `toReal`/`toComplex`),
  `IsScalarTower QSqrt2 ℝ ℂ`, `algebraMap_qsqrt2_real : algebraMap QSqrt2 ℝ x = a + b * √2` (rfl).
- Norm bounds: Prop class `CertNormLe K 𝕜` (`‖algebraMap K 𝕜 k‖ ≤ absUB k`) with instances for ℚ over every
  `RCLike 𝕜`, and QSqrt2 over ℝ and ℂ. Deriv/Bracket/Lie lemmas need only `[Algebra K 𝕜]`.
- Types: `CartMonoK K`, `CartPolyK K := List (CartMonoK K)`; `abbrev CartMono := CartMonoK ℚ`,
  `abbrev CartPoly := CartPolyK ℚ`. All `Poly/*` operations/lemmas are generic in `K` (names unchanged; the
  monomial-level ones moved to namespace `CartMonoK`: `CartMonoK.powProd/cartMonoEval/cartMonoMul/cartMonoTrim/
  cartMonoDq/cartMonoDp`; dot notation `m.cartMonoEval` still works for `m : CartMono` since it unfolds the abbrev).
- Scalars: `cartSmul (r : K)`, `cartConst (r : K)`; `cartAction` uses `ratCoeff (1/2)`; `cartLieSum` uses
  `cartSmul (ratCoeff (1/j!))`; `cartMonoBound` uses `CertCoeff.absUB m.c`; `cartSupBound` still returns `ℚ`.
- `cartEqCheck` soundness `cartEval_eq_of_eqCheck` is generic unchanged (dropped coefficients are `≠ 0` filtered in K).
- `@[default_instance] instCertCoeffRat` makes `cartAction 0`, `cartQVar 0`, `cartSmul 2 …` with no other
  information elaborate at K = ℚ, so old downstream code and the old smoke tests are textually untouched. In
  generic lemma statements where `K` is not determined by an argument I write `cartAction (K := K) j` etc.

## Signatures (key ones; all others are the old statements with `CartPoly → CartPolyK K`, `[Algebra ℚ R] → [Algebra K R]`)
```
structure CartMonoK (K : Type) where a b : List ℕ; c : K   deriving DecidableEq
def cartSmul (r : K) (P : CartPolyK K) : CartPolyK K
def cartConst (r : K) : CartPolyK K
theorem cartEval_smul (r : K) (P) (z) : cartEval (cartSmul r P) z = algebraMap K R r * cartEval P z
theorem cartEval_action [Algebra K ℝ] (j : Fin n) (z) : cartEval (cartAction j) z = oscillatorAction z.2 z.1 j
theorem cartEval_action_eq (j) (z) : cartEval (cartAction j) z = algebraMap K R (ratCoeff (1/2)) * (z.1 j ^ 2 + z.2 j ^ 2)
theorem cartEval_ofReal [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ] (P) (x) : …
theorem cartEval_bracket_real [Algebra K ℝ] … ; cartEval_bracket_complex [Algebra K ℂ] … ; cartEval_adPow_complex [Algebra K ℂ] …
theorem cartEval_lieSum_complex [Algebra K ℂ] … ; cartEval_actSubst_real [Algebra K ℝ] …
def cartMonoBound (m : CartMonoK K) (r s : List ℚ) : ℚ := CertCoeff.absUB m.c * ∏ …
theorem norm_eval_le_supBound [Algebra K 𝕜] [CertNormLe K 𝕜] (P) (hP : CartFits n P) (r s : List ℚ) (z) (hr) (hs) :
    ‖cartEval P z‖ ≤ ((cartSupBound P r s : ℚ) : ℝ)
theorem abs_eval_le_supBound [Algebra K ℝ] [CertNormLe K ℝ] …   ; abs_actionBracket_le_supBound [Algebra K ℝ] [CertNormLe K ℝ] …
theorem algebraMap_ratCoeff [Algebra K 𝕜] (q : ℚ) : algebraMap K 𝕜 (ratCoeff q) = (q : 𝕜)      (𝕜 a DivisionRing)
```
Signature changes relative to the old ℚ layer (all instance-level, invisible for K = ℚ): the real/complex lemmas take
explicit `[Algebra K ℝ]`/`[Algebra K ℂ]` (for ℚ these are the Mathlib instances); `norm_algebraMap_rat` is kept
verbatim for ℚ (used for the ℚ `CertNormLe` instance).

## Smoke tests (`Poly/QSqrt2Smoke.lean`, all `decide +kernel` over `QSqrt2`)
√2·√2 = 2; `{I₀ − (√2/2)I₁, q₁} = (√2/2) p₁`; `{·, p₁} = −(√2/2) q₁`; a negative check (`= false`);
antisymmetry of the bracket of the HH cubic `q₀²q₁ − q₁³/3` with the quadratic part; `{I₀,q₀} = −p₀`;
`cartSupBound hhQuad [1,1] [1,1] ≤ 2`; and the semantic theorem `hhQuadSmoke_eval : cartEval hhQuadSmoke z =
I₀ − (√2/2) I₁` over ℝ (through `toReal`). Each kernel check is below the 100 ms profiler threshold.

## Kernel timing (single thread, shared box; scratch benchmarks, not committed)
Benchmark: `cartEqCheck (cartSub (P^4) (P^4)) []` for a 4-term P, `cartEqCheck (ad_hh^3 I₁)` twice, `cartSupBound (ad_hh^4 I₁)`.
- OLD ℚ layer (before the change, machine under load): 2.6–3.3 s / 0.12–0.20 s / 0.24 s.
- NEW ℚ (generic layer at K = ℚ): 1.6–1.7 s / 0.11–0.22 s / 0.18 s. **No slowdown** (≤ 1×; the old run was noisier).
- NEW QSqrt2, same shapes: 2.3 s / 0.16–0.20 s / 0.28–0.30 s, i.e. ≈ 1.4× the ℚ time. Fine for the HH chain.
The 3× stop condition was not approached. The existing smoke tests in `Poly/Bound.lean`, `Poly/Lie.lean` pass unchanged.

## Checks
- Builds, one module per call via `b_build.sh`, in import order: `Poly.{Coeff,Basic,Deriv,Bracket,Bound,Lie}`, `Poly`,
  `Poly.QSqrt2Smoke`, and all 37 downstream modules that depend on Poly, unchanged: `FT.{Basic,Deriv,Bracket,Bound}`, `FT`,
  `OscillatorStep{,.Remainder,.Drift,.Smoke}`, `OscillatorChain{,.Basic,.Remainder,.Domain,.Drift,.Smoke}`,
  `OscillatorCheck`, `OscillatorChainCheck`, `OscillatorPhysical{,Smoke}`, `OscillatorChainPhysical{,Smoke}`,
  `Torus{Step.*,Chain.*,Check,ChainCheck,Physical,ChainPhysical,…Smoke}` (45 modules in total; log: 46 `Built` lines,
  0 errors, 0 warnings, final run after the last edit).
- `sh scripts/lint_sources.sh`: all checks PASS except one expected line, `KAM.lean is out of date; run
  scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)`: the two new modules `Poly.Coeff` and
  `Poly.QSqrt2Smoke` need the orchestrator's root regeneration (AGENTS rule 10 forbids me to edit the root).
- Line length (≤ 100): output `[]`. Short-name check: `main_shortname_check.py` → "short-name check OK (no reused
  public short name)" (after renaming `QSqrt2.toRealHom` to `QSqrt2.qsqrt2RealHom`, which collided with Mathlib).
- No `set_option`, `sorry`, `axiom`, `admit`, `unsafe`, `opaque` in `Poly/`.

## `#print axioms` (all `[propext, Classical.choice, Quot.sound]`)
cartEval_add, cartEval_mul, cartEval_normalize, cartEval_eq_of_eqCheck, cartEval_action, cartEval_ofReal, contDiff_eval,
fderiv_eval_apply, cartEval_bracket_real, cartEval_bracket_complex, cartEval_adPow_complex, norm_eval_le_supBound,
abs_eval_le_supBound, abs_actionBracket_le_supBound, cartEval_lieSum_complex, cartEval_actSubst_real, hhQuadSmoke_eval,
instCertCoeffQSqrt2, instCertCoeffRat, instCertNormLeQSqrt2Real, QSqrt2.abs_realVal_le.

## Design notes / uncertainties
1. `instCertCoeffRat` and `instCertCoeffQSqrt2` are `noncomputable` (their `toReal` fields use `ℝ`). Consequence: a plain
   `def x : CartPoly := cartAction 0 …` in a *computable* context now fails to compile ("depends on noncomputable
   instCertCoeffRat"). Everything in the repo is in `@[expose] public noncomputable section`, so nothing broke, and
   `decide +kernel` is unaffected. B3 data files must keep that section header. If computability is ever wanted, split the
   semantic fields (`toReal`, …) into a second class; the generic lemmas do not use them (they use `Algebra`/`CertNormLe`).
2. `CertCoeff ℚ` gives a second path to `CommRing ℚ`; unification with Mathlib's `Rat.commRing` works (all 45 modules build).
3. The semantics for real/complex statements is by `[Algebra K ℝ]`/`[Algebra K ℂ]` hypotheses rather than a global instance
   built from `toReal`: a global `Algebra K ℝ` instance would be a diamond with `Rat.algebra` for K = ℚ.
4. No errata in pinned sources; no deviation from the brief's required signatures except the instance-style real/complex
   binders noted above.

## AUDIT FOCUS (orchestrator)
1. ℚ API preservation: every pre-existing public declaration in `Poly/*` keeps its name and, at K = ℚ, a statement
   definitionally/textually equivalent to the one on `inp` (compare `git diff inp...HEAD`); no downstream edits.
2. `CertCoeff` soundness: `abs_toReal_le` for QSqrt2 (`√2 ≤ 141422/100000`), `toComplex_eq`, ring structure of QSqrt2
   (exact `(a+b√2)(c+d√2)`), `algebraMap_qsqrt2_real`; no way to obtain a wrong `absUB` majorant.
3. `cartSupBound`/`norm_eval_le_supBound` generic proof uses only `CertNormLe`; `cartEqCheck` soundness generic.
4. No diamonds that change meaning for K = ℚ (`Algebra ℚ ℝ` from Mathlib vs from CertCoeff); `@[default_instance]` risk.
5. Smoke tests are kernel (`decide +kernel`, never native_decide) and assert the intended HH quadratic semantics.
