/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Model.ExpBounds
public import KAM.Certificate.Arith.ComplexExp

/-!
# Exponential witnesses

An exp witness `E ≈ exp g₀` for the degree-zero polynomial part `g₀` of a model `g` (radius `η`)
certifies, with `|g₀| ≤ B` on `T_ρ`, the pin error `ε₀ ≥ |E(0) - exp g₀(0)|` and the residual
bounds `r_j ≥ sup_{T_ρ} |∂_j E - (∂_j g₀) E|`, the radius
`exp(2B) (ε₀ + (1/2 + ρ) Σ_j r_j) + exp(B) (exp(η) - 1)` for `exp g` (`expWitness_sound`).

* `B` is the weighted norm `|g₀|_w`; `exp(B)` and `exp(η) - 1` are the backend upper bounds
  `expm1Up` (halvings and Taylor order `cfg.halvings`, `cfg.taylorN`; fail closed when the
  halved argument exceeds `1`), and `exp(2B) = exp(B)²`.
* The pin (Revision 4, F10): `expPinBall g` encloses `g₀(0) = Σ_k ĝ₀(k)` (balanced ball sum,
  rounding in the radius); `out := certCExpReduced` of that ball with the witness's own halving
  count and order (`none` ⇒ the witness fails); `ε₀` bounds `|E(0) - out.1| + out.2` with the
  rounding of `E(0)` and of the subtraction (`expWitnessRadius_pin`). No smallness of `g₀(0)`
  is assumed.
* The residual of direction `j` is the model `∂_j E + (∂_j g₀)(-E)` (one advice-checked product,
  key `[1, j]`), bounded by `(2π)^deg (|P|_w + rad)`.

The proof: `F = E exp(-g₀)` is periodic, `|∂_j F| ≤ exp(B) r_j` on the strip, every point of the
strip is an integer translate of a point `θ'` with `|θ'_j| ≤ 1/2 + ρ`, so the mean value
inequality on the convex strip gives `|F - 1| ≤ exp(B) (ε₀ + (1/2 + ρ) Σ_j r_j)`; then
`exp g₀ - E = exp(g₀) (1 - F)` and `|exp g - exp g₀| ≤ exp(B) (exp(η) - 1)`.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM CertArith

/-- An exp witness: the polynomial `E ≈ exp g₀` and the pin's halving count and Taylor order
(certificate data, chosen by the generator from the size of `g₀(0)`). -/
structure ExpWitness (α : Type) where
  poly : CertPoly α
  pinHalvings : ℕ
  pinOrder : ℕ

section Defs

variable {α : Type} [CertArith α]

/-- A ball enclosing `g₀(0)`, the value at `θ = 0` of the polynomial part (sum of coefficients,
rounding in the radius). -/
def expPinBall {α : Type} [CertArith α] (g : CertModel α) : CC α × α :=
  ((CertPoly.coeffSumBall g.poly).c, (CertPoly.coeffSumBall g.poly).r)

/-- The pin error `ε₀ ≥ |E(0) - exp g₀(0)|` from the reduced exponential ball `out`: the ball
sum of `E(0)` plus the negated `out`, then `|centre|↑ + radius`. -/
def expPinErr (E : CertPoly α) (out : CC α × α) : α :=
  let d := CertBall.plus (CertPoly.coeffSumBall E) ⟨CC.negC out.1, out.2⟩
  upAdd d.c.normUp d.r

/-- The product terms `(∂_j g₀ / 2π)(-E)` with a sup-norm error: the advice under `[1, j]`
(`CertModel.polyProduct`), or the direct product if the advice is missing or fails. -/
def expResidualProduct (W : CertWeight) (cfg : ModelConfig α) (g₀ E : CertPoly α) (j : ℕ) :
    List (ErrTerm α) × α :=
  match CertModel.polyProduct W cfg [1, j] (itemsPoly (g₀.terms.filterMap (derivItem j)))
      E.negP with
  | some out => out
  | none =>
    (directItems (itemsPoly (g₀.terms.filterMap (derivItem j))).terms E.negP.terms, ofInt 0)

/-- An upper bound of `sup_{T_ρ} |∂_j E - (∂_j g₀) E|` given `eN ≥ sup |E|`: the terms of
`∂_j E / 2π` merged with the product terms, bounded in one weighted pass
`Σ (|c_k| + e_k) w^{|k|₁}`, plus the product error and `|∂_j g₀ rounding|_w · eN`, times an
upper bound of `2π`. -/
def expResidualUp (W : CertWeight) (cfg : ModelConfig α) (g₀ E : CertPoly α) (eN : α) (j : ℕ) :
    α :=
  let pr := expResidualProduct W cfg g₀ E j
  upMul (ofRatUp (2 * piUpQ))
    (upAdd (upAdd (sumUp (fun t => weightTermUp W t.1 (upAdd t.2.1.normUp t.2.2))
        (mergeErrTerms (E.terms.filterMap (derivItem j)) pr.1)) pr.2)
      (crossUp eN (errRadius W (g₀.terms.filterMap (derivItem j)))))

/-- The radius certified by the exp witness polynomial `E` once the pin ball `out` is known
(`none` if a real exponential bound fails). -/
def expWitnessRadiusOf (n : ℕ) (W : CertWeight) (cfg : ModelConfig α) (g : CertModel α)
    (E : CertPoly α) (out : CC α × α) : Option α :=
  match expm1Up cfg.halvings cfg.taylorN (g.poly.supNormUp W),
    expm1Up cfg.halvings cfg.taylorN g.rad with
  | some mB, some mη =>
    let eB := upAdd (ofInt 1) mB
    let eN := E.supNormUp W
    let res := sumUp (fun j : Fin n => expResidualUp W cfg g.poly E eN j.val) (List.finRange n)
    some (upAdd (upMul (upMul eB eB)
        (upAdd (expPinErr E out) (upMul (ofRatUp (1 / 2 + W.rho)) res)))
      (upMul eB mη))
  | _, _ => none

end Defs

/-- The radius certified for `exp g` by the witness `E` (or `none` if a check fails, including
a failed range reduction of the pin). -/
def expWitnessRadius {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (cfg : ModelConfig α)
    (g : CertModel α) (E : ExpWitness α) : Option α :=
  match certCExpReduced (expPinBall g).1 (expPinBall g).2 E.pinHalvings E.pinOrder with
  | some out => expWitnessRadiusOf n W cfg g E.poly out
  | none => none

theorem expPinBall_sound {α : Type} [CertArith α] [LawfulCertArith α] (n : ℕ)
    (g : CertModel α) :
    ‖g.poly.eval n 0 - (expPinBall g).1.toC‖ ≤ val (expPinBall g).2 := by
  have h := CertPoly.mem_coeffSumBall n g.poly
  unfold CertBall.Mem at h
  simp only [expPinBall]
  exact h

/-- The pin contract on a successful call: the reduced exponential succeeded on `expPinBall g`
and encloses `exp g₀(0)` (all reduction, rounding and squaring errors inside `out.2`). -/
theorem expWitnessRadius_pin {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {cfg : ModelConfig α} {g : CertModel α} {E : ExpWitness α} {r : α}
    (hE : expWitnessRadius n W cfg g E = some r) :
    ∃ out, certCExpReduced (expPinBall g).1 (expPinBall g).2 E.pinHalvings E.pinOrder = some out ∧
      ‖Complex.exp (g.poly.eval n 0) - out.1.toC‖ ≤ val out.2 := by
  unfold expWitnessRadius at hE
  split at hE
  · rename_i out hout
    exact ⟨out, hout, certCExpReduced_sound hout (expPinBall_sound n g)⟩
  · simp at hE

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α]

/-- The pin error bounds `|E(0) - exp g₀(0)|`. -/
theorem norm_sub_le_expPinErr (n : ℕ) (E : CertPoly α) (out : CC α × α) {w : ℂ}
    (hw : ‖w - out.1.toC‖ ≤ val out.2) : ‖E.eval n 0 - w‖ ≤ val (expPinErr E out) := by
  have h1 := CertPoly.mem_coeffSumBall n E
  have h2 : CertBall.Mem (-w) (⟨CC.negC out.1, out.2⟩ : CertBall α) := by
    unfold CertBall.Mem
    rw [CC.toC_negC, show -w - -out.1.toC = -(w - out.1.toC) by ring, norm_neg]
    exact hw
  have h3 := CertBall.mem_plus (w₁ := E.eval n 0) h1 h2
  set d := CertBall.plus (CertPoly.coeffSumBall E) ⟨CC.negC out.1, out.2⟩
  have hu := LawfulCertArith.upAdd_ge d.c.normUp d.r
  have hn := CC.norm_le_normUp d.c
  unfold CertBall.Mem at h3
  have : ‖E.eval n 0 - w‖ ≤ ‖E.eval n 0 + -w - d.c.toC‖ + ‖d.c.toC‖ := by
    rw [← sub_eq_add_neg]
    simpa using norm_sub_le_norm_sub_add_norm_sub (E.eval n 0 - w) d.c.toC 0
  exact this.trans (by simp only [expPinErr]; linarith)

omit [LawfulCertArith α] in
/-- The directional derivative of a polynomial: `∂_j P = 2π Σ i k_j c_k χ_k`. -/
theorem fderiv_eval_single {n : ℕ} (P : CertPoly α) (j : Fin n) (θ : Fin n → ℂ) :
    fderiv ℂ (P.eval n) θ (Pi.single j 1) = (2 * Real.pi) * (P.terms.map fun t =>
      Complex.I * ((certKeyFun n t.1 j : ℤ) : ℂ) * t.2.toC * character (certKeyFun n t.1) θ).sum := by
  obtain ⟨D, hD, hv⟩ := hasFDerivAt_termSum j θ P.terms
  have : P.eval n = fun θ => (P.terms.map fun t => t.2.toC * character (certKeyFun n t.1) θ).sum :=
    rfl
  rw [this, hD.fderiv, hv]

/-- One weighted pass bounds the value and the error budget of an error-term list. -/
theorem norm_errTermsEval_add_le {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (L : List (ErrTerm α)) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n W.rho) :
    ‖errTermsEval n L θ‖ + errTermsErr n L θ ≤
      val (sumUp (fun t => weightTermUp W t.1 (upAdd t.2.1.normUp t.2.2)) L) := by
  refine le_trans ?_ (sumUp_ge _ _)
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [errTermsEval_cons, errTermsErr_cons, List.map_cons, List.sum_cons]
    have h1 := weightTermUp_ge hW t.1 (upAdd t.2.1.normUp t.2.2) hθ
    have h2 := LawfulCertArith.upAdd_ge t.2.1.normUp t.2.2
    have h3 := CC.norm_le_normUp t.2.1
    have hχ := norm_nonneg (character (certKeyFun n t.1) θ)
    have h4 : ‖t.2.1.toC * character (certKeyFun n t.1) θ‖ +
        val t.2.2 * ‖character (certKeyFun n t.1) θ‖ ≤
        val (upAdd t.2.1.normUp t.2.2) * ‖character (certKeyFun n t.1) θ‖ := by
      rw [norm_mul, ← add_mul]
      exact mul_le_mul_of_nonneg_right (by linarith) hχ
    have := norm_add_le (t.2.1.toC * character (certKeyFun n t.1) θ) (errTermsEval n L θ)
    linarith

/-- The fused residual bound. -/
theorem norm_le_expResidualUp {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (cfg : ModelConfig α) (g₀ E : CertPoly α) {eN : α}
    (heN0 : 0 ≤ val eN) (j : Fin n) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n W.rho)
    (heN : ‖E.eval n θ‖ ≤ val eN) :
    ‖fderiv ℂ (E.eval n) θ (Pi.single j 1) -
        fderiv ℂ (g₀.eval n) θ (Pi.single j 1) * E.eval n θ‖ ≤
      val (expResidualUp W cfg g₀ E eN j.val) := by
  set dE := E.terms.filterMap (derivItem j.val)
  set dG := g₀.terms.filterMap (derivItem j.val)
  set pr := expResidualProduct W cfg g₀ E j.val
  set M := mergeErrTerms dE pr.1
  set SE := (E.terms.map fun t => Complex.I * ((certKeyFun n t.1 j : ℤ) : ℂ) * t.2.toC *
    character (certKeyFun n t.1) θ).sum
  set SG := (g₀.terms.map fun t => Complex.I * ((certKeyFun n t.1 j : ℤ) : ℂ) * t.2.toC *
    character (certKeyFun n t.1) θ).sum
  have hE := derivItems_spec j θ E.terms
  have hG := derivItems_spec j θ g₀.terms
  have hP : ‖(itemsPoly dG).eval n θ * E.negP.eval n θ - errTermsEval n pr.1 θ‖ ≤
      errTermsErr n pr.1 θ + val pr.2 := by
    simp only [pr, expResidualProduct]
    split
    · rename_i out hout
      exact CertModel.polyProduct_sound hW hout hθ
    · rw [LawfulCertArith.val_ofInt, Int.cast_zero, add_zero]
      exact directItems_spec n _ _ θ
  have hM := mergeErrTerms_spec n θ dE pr.1
  have hS := norm_errTermsEval_add_le hW M hθ
  have hR := errTermsErr_le_errRadius hW dG hθ
  have hR0 : 0 ≤ val (errRadius W dG) := sumUp_nonneg (fun _ => weightTermUp_nonneg hW _ _) _
  have hc := crossUp_ge eN (errRadius W dG) heN0 hR0
  have hneg := CertPoly.eval_negP n E θ
  rw [itemsPoly_eval] at hP
  rw [hneg] at hP
  -- the residual divided by `2π`
  have key : ‖SE - SG * E.eval n θ‖ ≤ errTermsErr n M θ + ‖errTermsEval n M θ‖ + val pr.2 +
      val (errRadius W dG) * val eN := by
    have e : SE - SG * E.eval n θ = (SE - errTermsEval n dE θ) +
        (errTermsEval n dE θ + errTermsEval n pr.1 θ - errTermsEval n M θ) +
        errTermsEval n M θ + (errTermsEval n dG θ * -E.eval n θ - errTermsEval n pr.1 θ) +
        (errTermsEval n dG θ - SG) * E.eval n θ := by ring
    rw [e]
    have n1 := norm_add_le ((SE - errTermsEval n dE θ) +
        (errTermsEval n dE θ + errTermsEval n pr.1 θ - errTermsEval n M θ) +
        errTermsEval n M θ + (errTermsEval n dG θ * -E.eval n θ - errTermsEval n pr.1 θ))
      ((errTermsEval n dG θ - SG) * E.eval n θ)
    have n2 := norm_add_le ((SE - errTermsEval n dE θ) +
        (errTermsEval n dE θ + errTermsEval n pr.1 θ - errTermsEval n M θ) +
        errTermsEval n M θ) (errTermsEval n dG θ * -E.eval n θ - errTermsEval n pr.1 θ)
    have n3 := norm_add_le ((SE - errTermsEval n dE θ) +
        (errTermsEval n dE θ + errTermsEval n pr.1 θ - errTermsEval n M θ))
      (errTermsEval n M θ)
    have n4 := norm_add_le (SE - errTermsEval n dE θ)
      (errTermsEval n dE θ + errTermsEval n pr.1 θ - errTermsEval n M θ)
    have n5 : ‖(errTermsEval n dG θ - SG) * E.eval n θ‖ ≤ val (errRadius W dG) * val eN := by
      rw [norm_mul, norm_sub_rev]
      exact mul_le_mul (hG.trans hR) heN (norm_nonneg _) hR0
    linarith
  have h2pi := LawfulCertArith.ofRatUp_ge (α := α) (2 * piUpQ)
  have hpi : 2 * Real.pi ≤ ((2 * piUpQ : ℚ) : ℝ) := by push_cast; linarith [pi_lt_piUpQ]
  have u1 := LawfulCertArith.upAdd_ge
    (sumUp (fun t => weightTermUp W t.1 (upAdd t.2.1.normUp t.2.2)) M) pr.2
  have u2 := LawfulCertArith.upAdd_ge
    (upAdd (sumUp (fun t => weightTermUp W t.1 (upAdd t.2.1.normUp t.2.2)) M) pr.2)
    (crossUp eN (errRadius W dG))
  have hX0 : 0 ≤ ‖SE - SG * E.eval n θ‖ := norm_nonneg _
  have hU : ‖SE - SG * E.eval n θ‖ ≤ val (upAdd (upAdd (sumUp (fun t => weightTermUp W t.1
      (upAdd t.2.1.normUp t.2.2)) M) pr.2) (crossUp eN (errRadius W dG))) := by linarith
  have h2pos : (0 : ℝ) ≤ val (ofRatUp (2 * piUpQ) : α) :=
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi).trans (hpi.trans h2pi)
  have hm := LawfulCertArith.upMul_ge _ _ h2pos (hX0.trans hU)
  rw [fderiv_eval_single, fderiv_eval_single]
  have e2 : (2 * (Real.pi : ℂ)) * SE - (2 * (Real.pi : ℂ)) * SG * E.eval n θ =
      (2 * (Real.pi : ℂ)) * (SE - SG * E.eval n θ) := by ring
  rw [e2, norm_mul]
  have h2 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by simp [abs_of_pos Real.pi_pos]
  rw [h2]
  exact (mul_le_mul (hpi.trans h2pi) hU hX0 h2pos).trans hm

/-- A linear functional on `Fin n → ℂ` is bounded by the sum of its values on the basis. -/
theorem norm_clm_le_sum_single {n : ℕ} (L : (Fin n → ℂ) →L[ℂ] ℂ) :
    ‖L‖ ≤ ∑ j, ‖L (Pi.single j 1)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : L v = ∑ j, v j * L (Pi.single j 1) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (Pi.single j (v j) : Fin n → ℂ) = v j • Pi.single j 1 by
      rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  rw [hv, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _)

/-- `‖exp z - 1‖ ≤ exp ‖z‖ - 1`. -/
theorem norm_exp_sub_one_le_exp_norm (z : ℂ) : ‖Complex.exp z - 1‖ ≤ Real.exp ‖z‖ - 1 := by
  simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z 1

/-- Every point of the strip is an integer translate of a point with `|Re θ'_j| ≤ 1/2`. -/
theorem exists_int_translate {n : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n ρ) :
    ∃ m : Fin n → ℤ, (θ + fun i => (m i : ℂ)) ∈ complexStrip n ρ ∧
      ‖θ + fun i => (m i : ℂ)‖ ≤ 1 / 2 + ρ := by
  refine ⟨fun i => -round (θ i).re, fun i => ?_, ?_⟩
  · simpa using hθ i
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hre : ((θ + fun i => ((-round (θ i).re : ℤ) : ℂ)) i).re = (θ i).re - round (θ i).re := by
      simp [sub_eq_add_neg]
    have him : ((θ + fun i => ((-round (θ i).re : ℤ) : ℂ)) i).im = (θ i).im := by simp
    rw [hre, him]
    exact add_le_add (abs_sub_round _) (hθ i).le

omit [LawfulCertArith α] in
/-- The analytic core: with `|g₀| ≤ B`, `|E(0) - exp g₀(0)| ≤ ε₀` and residual bounds
`sup |∂_j E - (∂_j g₀) E| ≤ c_j`, `|exp g₀ - E| ≤ exp(B)² (ε₀ + (1/2 + ρ) Σ_j c_j)` on `T_ρ`. -/
theorem norm_exp_sub_witness_le {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (g₀ E : CertPoly α) {B ε₀ : ℝ}
    {c : Fin n → ℝ} (hB : ∀ θ ∈ complexStrip n ρ, ‖g₀.eval n θ‖ ≤ B)
    (hε : ‖E.eval n 0 - Complex.exp (g₀.eval n 0)‖ ≤ ε₀)
    (hc : ∀ j, ∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ (E.eval n) θ (Pi.single j 1) -
      fderiv ℂ (g₀.eval n) θ (Pi.single j 1) * E.eval n θ‖ ≤ c j)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ) :
    ‖Complex.exp (g₀.eval n θ) - E.eval n θ‖ ≤
      Real.exp B ^ 2 * (ε₀ + (1 / 2 + ρ) * ∑ j, c j) := by
  set G := g₀.eval n
  set Ef := E.eval n
  set F : (Fin n → ℂ) → ℂ := fun x => Ef x * Complex.exp (-G x) with hFdef
  have h0 : (0 : Fin n → ℂ) ∈ complexStrip n ρ := fun i => by simpa using hρ
  have hexpB : ∀ x ∈ complexStrip n ρ, ‖Complex.exp (-G x)‖ ≤ Real.exp B := fun x hx =>
    (Complex.norm_exp_le_exp_norm _).trans
      (Real.exp_le_exp.mpr (by rw [norm_neg]; exact hB x hx))
  have hD : ∀ x, HasFDerivAt F (Ef x • (Complex.exp (-G x) • -fderiv ℂ G x) +
      Complex.exp (-G x) • fderiv ℂ Ef x) x := fun x =>
    ((E.differentiable_eval n x).hasFDerivAt).mul
      ((g₀.differentiable_eval n x).hasFDerivAt.neg.cexp)
  have hdiff : ∀ x, DifferentiableAt ℂ F x := fun x => (hD x).differentiableAt
  have hpart : ∀ x j, fderiv ℂ F x (Pi.single j 1) = Complex.exp (-G x) *
      (fderiv ℂ Ef x (Pi.single j 1) - fderiv ℂ G x (Pi.single j 1) * Ef x) := fun x j => by
    rw [(hD x).fderiv]
    simp only [_root_.add_apply, _root_.smul_apply,
      _root_.neg_apply, smul_eq_mul]
    ring
  have hc0 : ∀ j, 0 ≤ c j := fun j => (norm_nonneg _).trans (hc j 0 h0)
  have hbound : ∀ x ∈ complexStrip n ρ, ‖fderiv ℂ F x‖ ≤ Real.exp B * ∑ j, c j := by
    intro x hx
    refine (norm_clm_le_sum_single _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hpart, norm_mul]
    exact mul_le_mul (hexpB x hx) (hc j x hx) (norm_nonneg _) (Real.exp_pos _).le
  obtain ⟨m, hm, hmn⟩ := exists_int_translate hρ.le hθ
  have hFm : F (θ + fun i => (m i : ℂ)) = F θ := by
    simp only [hFdef, Ef, G, CertPoly.eval_add_int]
  have hmvt := (convex_complexStrip n ρ).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hdiff x) hbound h0 hm
  rw [hFm, sub_zero] at hmvt
  have hF0 : F 0 - 1 = Complex.exp (-G 0) * (Ef 0 - Complex.exp (G 0)) := by
    simp only [hFdef]
    rw [mul_sub, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    ring
  have hF0n : ‖F 0 - 1‖ ≤ Real.exp B * ε₀ := by
    rw [hF0, norm_mul]
    exact mul_le_mul (hexpB 0 h0) hε (norm_nonneg _) (Real.exp_pos _).le
  have hsplit : Complex.exp (G θ) - Ef θ = Complex.exp (G θ) * -((F θ - F 0) + (F 0 - 1)) := by
    simp only [hFdef]
    rw [show -((Ef θ * Complex.exp (-G θ) - Ef 0 * Complex.exp (-G 0)) +
        (Ef 0 * Complex.exp (-G 0) - 1)) = 1 - Ef θ * Complex.exp (-G θ) by ring,
      mul_sub, mul_one, mul_left_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
      mul_one]
  have hGθ : ‖Complex.exp (G θ)‖ ≤ Real.exp B :=
    (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (hB θ hθ))
  have hS0 : 0 ≤ ∑ j, c j := Finset.sum_nonneg fun j _ => hc0 j
  have hn1 : ‖F θ - F 0‖ ≤ Real.exp B * ∑ j, c j * (1 / 2 + ρ) := by
    rw [← Finset.sum_mul]
    refine hmvt.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmn hS0) (Real.exp_pos _).le
  rw [hsplit, norm_mul, norm_neg]
  have h3 := norm_add_le (F θ - F 0) (F 0 - 1)
  have heB := (Real.exp_pos B).le
  have hsum := add_le_add hn1 hF0n
  rw [← Finset.sum_mul] at hsum
  calc ‖Complex.exp (G θ)‖ * ‖F θ - F 0 + (F 0 - 1)‖ ≤
        Real.exp B * (Real.exp B * ((∑ j, c j) * (1 / 2 + ρ)) + Real.exp B * ε₀) :=
        mul_le_mul hGθ (h3.trans hsum) (norm_nonneg _) heB
    _ = Real.exp B ^ 2 * (ε₀ + (1 / 2 + ρ) * ∑ j, c j) := by ring

theorem expWitnessRadiusOf_sound {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (cfg : ModelConfig α) {g : CertModel α}
    {gf : (Fin n → ℂ) → ℂ} (hg : g.Encloses n W.rho gf) (hdeg : g.deg = 0) {E : CertPoly α}
    {out : CC α × α} (hpin : ‖Complex.exp (g.poly.eval n 0) - out.1.toC‖ ≤ val out.2) {r : α}
    (h : expWitnessRadiusOf n W cfg g E out = some r) :
    (⟨0, E, r⟩ : CertModel α).Encloses n W.rho (fun θ => Complex.exp (gf θ)) := by
  unfold expWitnessRadiusOf at h
  split at h
  swap
  · simp at h
  rename_i mB mη hmB hmη
  simp only [Option.some.injEq] at h
  subst h
  have hρ := CertWeight.rho_pos hW
  set B := g.poly.supNormUp W
  have hB0 := g.poly.supNormUp_nonneg hW
  have hη0 := hg.rad_nonneg hρ
  have hmB' := expm1Up_sound hB0 hmB
  have hmη' := expm1Up_sound hη0 hmη
  set eB : α := upAdd (ofInt 1) mB
  have heB : Real.exp (val B) ≤ val eB := by
    have := LawfulCertArith.upAdd_ge (ofInt 1 : α) mB
    rw [LawfulCertArith.val_ofInt] at this
    push_cast at this
    linarith
  have heB0 : 0 ≤ val eB := (Real.exp_pos _).le.trans heB
  have he2 := LawfulCertArith.upMul_ge eB eB heB0 heB0
  -- residuals
  set eN : α := E.supNormUp W
  have heN0 : 0 ≤ val eN := E.supNormUp_nonneg hW
  set R : Fin n → α := fun j => expResidualUp W cfg g.poly E eN j.val
  have hR : ∀ j, ∀ θ ∈ complexStrip n W.rho, ‖fderiv ℂ (E.eval n) θ (Pi.single j 1) -
      fderiv ℂ (g.poly.eval n) θ (Pi.single j 1) * E.eval n θ‖ ≤ val (R j) :=
    fun j θ hθ => norm_le_expResidualUp hW cfg g.poly E heN0 j hθ (E.norm_eval_le_supNormUp hW hθ)
  set res : α := sumUp (fun j : Fin n => R j) (List.finRange n)
  have hres : ∑ j, val (R j) ≤ val res := by
    have := sumUp_ge (fun j : Fin n => R j) (List.finRange n)
    rwa [← List.ofFn_eq_map, List.sum_ofFn] at this
  have h0 : (0 : Fin n → ℂ) ∈ complexStrip n W.rho := fun i => by simpa using hρ
  have hS0 : 0 ≤ ∑ j, val (R j) :=
    Finset.sum_nonneg fun j _ => (norm_nonneg _).trans (hR j 0 h0)
  -- pin
  have hε := norm_sub_le_expPinErr n E out hpin
  have hε0 : 0 ≤ val (expPinErr E out) := (norm_nonneg _).trans hε
  set half : α := ofRatUp (1 / 2 + W.rho)
  have hhalf : 1 / 2 + (W.rho : ℝ) ≤ val half := by
    have := LawfulCertArith.ofRatUp_ge (α := α) (1 / 2 + W.rho)
    push_cast at this
    exact this
  have hh0 : 0 ≤ val half := by linarith
  have hm1 := LawfulCertArith.upMul_ge half res hh0 (hS0.trans hres)
  set inner : α := upAdd (expPinErr E out) (upMul half res)
  have hin := LawfulCertArith.upAdd_ge (expPinErr E out) (upMul half res)
  have hinner : val (expPinErr E out) + (1 / 2 + (W.rho : ℝ)) * ∑ j, val (R j) ≤
      val inner := by
    have : (1 / 2 + (W.rho : ℝ)) * ∑ j, val (R j) ≤ val half * val res :=
      mul_le_mul hhalf hres hS0 hh0
    linarith
  have hin0 : 0 ≤ val inner := by
    have : 0 ≤ (1 / 2 + (W.rho : ℝ)) * ∑ j, val (R j) := by positivity
    linarith
  have hm2 := LawfulCertArith.upMul_ge (upMul eB eB) inner ((mul_nonneg heB0 heB0).trans he2)
    hin0
  have hmη0 : 0 ≤ val mη := by linarith [Real.add_one_le_exp (val g.rad)]
  have hm3 := LawfulCertArith.upMul_ge eB mη heB0 hmη0
  have hr := LawfulCertArith.upAdd_ge (upMul (upMul eB eB) inner) (upMul eB mη)
  -- the estimate
  intro θ hθ
  simp only [zpow_zero, one_mul]
  have hgθ := hg θ hθ
  rw [hdeg, zpow_zero, zpow_zero, one_mul, one_mul] at hgθ
  have hBθ : ∀ x ∈ complexStrip n W.rho, ‖g.poly.eval n x‖ ≤ val B := fun x hx =>
    g.poly.norm_eval_le_supNormUp hW hx
  have hcore := norm_exp_sub_witness_le hρ g.poly E hBθ hε hR hθ
  have hA : ‖Complex.exp (gf θ) - Complex.exp (g.poly.eval n θ)‖ ≤
      Real.exp (val B) * (Real.exp (val g.rad) - 1) := by
    have : Complex.exp (gf θ) - Complex.exp (g.poly.eval n θ) =
        Complex.exp (g.poly.eval n θ) * (Complex.exp (gf θ - g.poly.eval n θ) - 1) := by
      rw [mul_sub, ← Complex.exp_add, add_sub_cancel, mul_one]
    rw [this, norm_mul]
    refine mul_le_mul
      ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (hBθ θ hθ)))
      ((norm_exp_sub_one_le_exp_norm _).trans ?_) (norm_nonneg _) (Real.exp_pos _).le
    linarith [Real.exp_le_exp.mpr hgθ]
  have hsq : Real.exp (val B) ^ 2 ≤ val (upMul eB eB) := by
    rw [sq]; exact (mul_le_mul heB heB (Real.exp_pos _).le heB0).trans he2
  have hX : Real.exp (val B) ^ 2 * (val (expPinErr E out) +
      (1 / 2 + (W.rho : ℝ)) * ∑ j, val (R j)) ≤
      val (upMul (upMul eB eB) inner) :=
    (mul_le_mul hsq hinner (by positivity) ((sq_nonneg _).trans hsq)).trans hm2
  have hY : Real.exp (val B) * (Real.exp (val g.rad) - 1) ≤ val (upMul eB mη) :=
    (mul_le_mul heB hmη' (by linarith [Real.add_one_le_exp (val g.rad)]) heB0).trans hm3
  have := norm_sub_le_norm_sub_add_norm_sub (Complex.exp (gf θ))
    (Complex.exp (g.poly.eval n θ)) (E.eval n θ)
  linarith

theorem expWitness_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (cfg : ModelConfig α)
    {g : CertModel α} {gf : (Fin n → ℂ) → ℂ} (hg : g.Encloses n W.rho gf) (hdeg : g.deg = 0)
    {E : ExpWitness α} {r : α}
    (hE : expWitnessRadius n W cfg g E = some r) :
    (⟨0, E.poly, r⟩ : CertModel α).Encloses n W.rho (fun θ => Complex.exp (gf θ)) := by
  obtain ⟨out, hout, hpin⟩ := expWitnessRadius_pin hE
  unfold expWitnessRadius at hE
  simp only [hout] at hE
  exact expWitnessRadiusOf_sound hW cfg hg hdeg hpin hE

end Sound

end KAM.Certificate
