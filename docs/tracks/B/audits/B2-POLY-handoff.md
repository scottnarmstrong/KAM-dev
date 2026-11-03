# Handoff B2-POLY (branch inp-b2poly, worktree /root/code/KAM-inp-b2poly)

## Files (all new, namespace `KAM.EffectiveStability`, `CartPoly.*`)
- `KAM/EffectiveStability/Poly/Basic.lean` (411 lines): `CartMono`, `CartPoly := List CartMono`, `addPad`, `unitExp`,
  `trimExp`, `CartMono.eval/mul/trim`, `CartPoly.eval/add/neg/sub/smul/mul/const/qVar/pVar/action`, `insertMono`, `merge`,
  `normalize`, `eqCheck`, `Fits`; lemmas `eval_add/neg/sub/smul/mul/const/qVar/pVar/action/normalize`,
  `eval_eq_of_eqCheck`, `eval_ofReal`, `Fits.*`.
- `Poly/Deriv.lean` (228): `dq`, `dp`, `contDiff_eval`, `fderiv_eval_apply`, `fderiv_eval_q`, `fderiv_eval_p`.
- `Poly/Bracket.lean` (265): `width`, `bracket`, `adPow`, `eval_bracket`, `eval_bracket_complex`, `eval_bracket_real`,
  `eval_adPow_complex`, `eval_bracket_action`, `eval_dq_action`, `eval_dp_action`, `Fits.dq/dp/bracket/adPow`.
- `Poly/Bound.lean` (143): `monoBound`, `supBound`, `norm_eval_le_supBound`, `abs_eval_le_supBound`,
  `abs_actionBracket_le_supBound`, `abs_le_of_action_le`, `abs_le_of_oscillatorAction_le`, smoke tests.
- `KAM/EffectiveStability/Poly.lean`: facade importing the four modules.

## Final signatures (R = commutative ring with `[Algebra ℚ R]`, 𝕜 = `[RCLike 𝕜]`, z : (Fin n → R) × (Fin n → R))
```lean
def CartPoly.cartEval (P : CartPoly) (z : (Fin n → R) × (Fin n → R)) : R := (P.map (·.cartEval z)).sum
-- CartMono.cartEval m z := algebraMap ℚ R m.c * ∏ i : Fin n, z.1 i ^ m.a.getD i 0 * z.2 i ^ m.b.getD i 0
def CartPoly.cartEqCheck (P Q : CartPoly) : Bool := (cartNormalize (cartSub P Q)).isEmpty
theorem cartEval_normalize (P) (z) : cartEval (cartNormalize P) z = cartEval P z
theorem cartEval_eq_of_eqCheck {P Q} (h : cartEqCheck P Q = true) (z) : cartEval P z = cartEval Q z
theorem cartEval_action (j : Fin n) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    cartEval (cartAction j) z = KAM.Planetary.oscillatorAction z.2 z.1 j
theorem cartEval_ofReal (P) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    cartEval P ((fun i => ((x.1 i : ℝ) : ℂ), fun i => ((x.2 i : ℝ) : ℂ)) : (Fin n → ℂ) × (Fin n → ℂ))
      = ((cartEval P x : ℝ) : ℂ)
theorem contDiff_eval (P) (k : WithTop ℕ∞) : ContDiff 𝕜 k (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => P.cartEval z)
theorem fderiv_eval_apply (P) (z v) : fderiv 𝕜 (fun z => P.cartEval z) z v =
    ∑ i : Fin n, (v.1 i * cartEval (cartDq i P) z + v.2 i * cartEval (cartDp i P) z)
theorem fderiv_eval_q (P) (z) (i : Fin n) : fderiv 𝕜 (fun z => P.cartEval z) z (Pi.single i 1, 0) = cartEval (cartDq i P) z
theorem fderiv_eval_p (P) (z) (i : Fin n) : fderiv 𝕜 (fun z => P.cartEval z) z (0, Pi.single i 1) = cartEval (cartDp i P) z
def cartBracket (P Q : CartPoly) : CartPoly :=
  (List.range (cartWidth P)).flatMap fun i => cartSub (cartMul (cartDq i P) (cartDp i Q)) (cartMul (cartDp i P) (cartDq i Q))
def cartAdPow (χ : CartPoly) : ℕ → CartPoly → CartPoly | 0, P => P | k+1, P => cartBracket (cartAdPow χ k P) χ
theorem cartEval_bracket_complex (P Q) (hP : CartFits n P) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    cartEval (cartBracket P Q) z = KAM.Canonical.poissonBracket (fun z => cartEval P z) (fun z => cartEval Q z) z
theorem cartEval_bracket_real (P Q) (hP : CartFits n P) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    cartEval (cartBracket P Q) z = fderiv ℝ (fun z => cartEval P z) z (KAM.hamiltonianVectorField (fun z => cartEval Q z) z)
theorem cartEval_adPow_complex (χ P) (hχ : CartFits n χ) (hP : CartFits n P) (k : ℕ) :
    (fun z : (Fin n → ℂ) × (Fin n → ℂ) => cartEval (cartAdPow χ k P) z) =
      KAM.Canonical.cartAdPow (fun z => cartEval χ z) k (fun z => cartEval P z)
theorem cartEval_bracket_action (j : Fin n) (P) (z) :   -- any R, no CartFits hypothesis needed
    cartEval (cartBracket (cartAction j) P) z = z.1 j * cartEval (cartDp j P) z - z.2 j * cartEval (cartDq j P) z
def cartSupBound (P : CartPoly) (r s : List ℚ) : ℚ  -- ∑ |c| ∏_{k<max len} r_k^{a_k} s_k^{b_k}
theorem norm_eval_le_supBound (P) (hP : CartFits n P) (r s : List ℚ) (z : (Fin n → 𝕜) × (Fin n → 𝕜))
    (hr : ∀ i : Fin n, ‖z.1 i‖ ≤ ((r.getD i 0 : ℚ) : ℝ)) (hs : ∀ i : Fin n, ‖z.2 i‖ ≤ ((s.getD i 0 : ℚ) : ℝ)) :
    ‖P.cartEval z‖ ≤ ((cartSupBound P r s : ℚ) : ℝ)
theorem abs_eval_le_supBound  -- same over ℝ with |·|
theorem abs_actionBracket_le_supBound (P) (hP : CartFits n P) (j : Fin n) (r : List ℚ) (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hq : ∀ i : Fin n, |z.1 i| ≤ ((r.getD i 0 : ℚ) : ℝ)) (hp : ∀ i : Fin n, |z.2 i| ≤ ((r.getD i 0 : ℚ) : ℝ)) :
    |z.1 j * cartEval (cartDp j P) z - z.2 j * cartEval (cartDq j P) z| ≤ ((cartSupBound (cartBracket (cartAction j) P) r r : ℚ) : ℝ)
theorem abs_le_of_action_le {q p b r : ℝ} (h : (p^2+q^2)/2 ≤ b) (hb : 2*b ≤ r^2) (hr : 0 ≤ r) : |q| ≤ r ∧ |p| ≤ r
theorem abs_le_of_oscillatorAction_le (z) (b r : Fin n → ℝ) (i : Fin n)
    (h : KAM.Planetary.oscillatorAction z.2 z.1 i ≤ b i) (hb : 2 * b i ≤ r i ^ 2) (hr : 0 ≤ r i) :
    |z.1 i| ≤ r i ∧ |z.2 i| ≤ r i
```

## Short-name renames (kam-b1 request)
Every public last name component is now unique (`main_shortname_check.py` exits 0). Scheme: `CartPoly.eval/add/neg/sub/smul/mul/
const/qVar/pVar/action/dq/dp/bracket/adPow/width/merge/normalize/eqCheck/insertMono/supBound/monoBound` became `cartEval`,
`cartAdd`, ... (`cartMonoBound`); `CartMono.eval/mul/trim/dq/dp` became `cartMonoEval/cartMonoMul/cartMonoTrim/cartMonoDq/cartMonoDp`;
`eval_*` lemmas became `cartEval_*` (e.g. `cartEval_add`, `cartEval_bracket_real`); `Fits` became `CartFits` with lemmas
`cartFits_add/neg/sub/smul/mul/const/qVar/pVar/action/nil/flatMap/dq/dp/bracket/adPow` (plain functions, no dot notation).
The signatures below use the new names; statements are unchanged. Lines wrapped to <= 100 columns.

## Deviations from the brief (all deliberate; please review)
1. **`CartFits n P` hypothesis** (typing data: all exponents at indices ≥ n vanish, `CartFits n P`). `eval` ignores indices ≥ n but
   formal `bracket`/`supBound` do not, so without it `eval_bracket_*`, `eval_adPow_complex`, `norm_eval_le_supBound` and the
   drift bound are false (e.g. `q_5` factor with n = 2). It is required on `P` only for the bracket (not on `Q`), on
   `χ` and `P` for `adPow`. Lemmas `cartFits_*` propagate it;
   `eval_bracket_action` needs no `Fits` (the action fits automatically; P's derivative sums are truncated by
   `dq_eq_nil_of_*`), but `abs_actionBracket_le_supBound` needs `CartFits n P` for the bound.
2. `bracket` sums over `i < width P` (computable, n-free); `width` = max exponent-list length.
3. `contDiff_eval` is stated for every order `k : WithTop ℕ∞` (so includes `∞` and `ω`), instead of the literal `⊤`.
4. Bound hypotheses: no `0 ≤ r.getD i 0` needed (follows from the norm bound); casts `((r.getD i 0 : ℚ) : ℝ)` are explicit.
   `supBound`'s product runs over `range (max a.length b.length)` (the `0^0 = 1` case is handled).
5. Derivative/bound theorems are over any `RCLike 𝕜` (covers ℝ and ℂ at once); `eval_bracket_action` is over any ℚ-algebra.
6. `eqCheck` uses `.isEmpty` (no `BEq CartMono`); soundness only (no completeness claim).
7. Smoke tests use `decide +kernel` (kernel evaluation; plain `decide` gets stuck in Meta-level whnf at `normalize`). NOT
   `native_decide`. Tests (in `Poly/Bound.lean`, section `Test`): `eqCheck (bracket (action 0) (qVar 0)) (neg (pVar 0))`,
   `bracket (qVar 0) (pVar 0) = const 1`, `bracket (action 1) (pVar 1) = qVar 1`, a square expansion, and a negative `false`
   test; whole `Bound.lean` elaborates in ~3.7 s wall incl. imports (`b_lean.sh`), tests negligible.

## Approach
Evaluation as `algebraMap c * ∏_i q_i^{a_i} p_i^{b_i}` with `powProd`; `addPad` + `getD_addPad` for products; `trimExp` +
`getD_trimExp`, `insertMono`-fold merge, zero-filter for `normalize`. Derivatives: line derivative
`t ↦ eval (z + t•v)` via `HasDerivAt.fun_finsetProd`, matched termwise with the formal `dq/dp` (`eval_dq_mono`), then
`fderiv` by uniqueness (smoothness from `contDiff_prod`). Bracket: flat-map over `range (width P)`, truncated to `Fin n`
via `sum_range_eq_of_zero` using `Fits`. Bounds: monomial-wise `norm_prod` + `prod_le_prod₀`, `prod_range_eq_univ` to
change the index set.

## Checks
- `b_build.sh` for `Poly.Basic`, `Poly.Deriv`, `Poly.Bracket`, `Poly.Bound`, `Poly` : all succeed, no warnings from my files
  (the final Bracket rebuild after the line-wrap fix prints only "Built").
- `sh scripts/lint_sources.sh`: no over-length lines, `check_lean_modules: PASS`, frozen-anchor guard OK, ABI hashes OK, but
  prints `KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean, KAM.lean)` (generated
  root files, I may not edit them: orchestrator must run the generator to add the 5 new modules).
- No `sorry/axiom/native_decide/set_option`; line counts 411/228/265/143/19 (< 1500).
- `#print axioms` (scratch file, not committed) of eval_normalize, eval_eq_of_eqCheck, eval_action, eval_ofReal,
  contDiff_eval, fderiv_eval_apply/_q/_p, eval_bracket_complex/_real, eval_adPow_complex, eval_bracket_action,
  norm_eval_le_supBound, abs_eval_le_supBound, abs_actionBracket_le_supBound, abs_le_of_oscillatorAction_le:
  all `[propext, Classical.choice, Quot.sound]`.
- Commit touches only `KAM/EffectiveStability/Poly*`.

## Uncertainties / design signals / errata
- No heartbeat or memory problems (each file elaborates in seconds, far under the 4 GB cap).
- Mathlib in the pinned version deprecates `if_pos/if_neg/if_true` (warnings), I avoided them.
- No errata in pinned sources found.

## Post-handoff changes (kam-b1)
Short-name renames to `cart*` (prover, 5d9621ae3); facade `public section` added and docstring rewrapped (kam-b1).

## AUDIT FOCUS (kam-b1)
Track B, program B2 (overnight D71; nothing frozen; scope OD-B7; OD-B8 new Cartesian type, OD-B9 exact ℚ). Brief:
/root/code/KAM-inp-b1/.drafts/B/brief-B2-POLY.md and brief-B1-common.md; design program-b-plan §3.1-3.2
(/root/code/KAM/docs/explorations/program-b-plan.md lines 300-420). Consumers: the one-step soundness theorem (next
package) via cartEqCheck soundness, cartEval_adPow_complex (= KAM.Canonical.adPow), cartEval_bracket_real, the
action-bracket bound (B1-E's hRη form) and cartSupBound. Check: (1) each theorem true as stated; the `CartFits n P`
typing hypothesis is decidable typing data, not conclusion-shaped, and is needed exactly where used; (2) the
SOUNDNESS of cartNormalize / cartEqCheck (a true `eqCheck` must imply equality of evaluations for every n and every
ℚ-algebra), the bracket sign convention vs KAM.Canonical.poissonBracket and KAM.hamiltonianVectorField, cartAction =
oscillatorAction; (3) cartSupBound is a genuine majorant (0^0, negative coefficients, padding); (4) the smoke tests
use kernel evaluation (`decide +kernel`), no native_decide/ofReduceBool (check #print axioms); (5) hygiene (AGENTS
rules 3, 4, 7; line length ≤ 100), names, axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
