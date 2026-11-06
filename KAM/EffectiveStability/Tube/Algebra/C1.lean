/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.C1Close
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Algebra of `C¹` closeness on the angle plane (T2-CONF, N3)

Calculus rules for `C1Close f g e₀ e₁` (`Tube/C1Close.lean`): `f`, `g` differentiable on
`Fin 2 → ℝ`, `|f - g| ≤ e₀` and every partial derivative of `f - g` bounded by `e₁`.

* `C1Close.refl`, `C1Close.mono`, `C1Close.symm`, `C1Close.trans` (triangle inequality);
* `C1Close.add`, `C1Close.sub`, `C1Close.neg`, `C1Close.const_mul`, `C1Close.sum`;
* `C1Close.mul`, the product rule: from `C1Close f p e₀ e₁`, `C1Close g q d₀ d₁` and sup bounds
  `|p| ≤ P₀`, `|∂_a p| ≤ P₁`, `|q| ≤ Q₀`, `|∂_a q| ≤ Q₁`,
  `C1Close (f * g) (p * q) (P₀ d₀ + Q₀ e₀ + e₀ d₀) (P₁ d₀ + P₀ d₁ + Q₁ e₀ + Q₀ e₁ + e₁ d₀ + e₀ d₁)`;
* `C1Close.abs_le`, `C1Close.abs_pderiv_le`: sup bounds of `f` from those of its model.

The bounds are plain real expressions. `pderiv f φ a` abbreviates the partial derivative
`fderiv ℝ f φ (Pi.single a 1)`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

/-- The partial derivative `∂_a f φ = fderiv ℝ f φ (Pi.single a 1)` on the angle plane. -/
noncomputable abbrev pderiv (f : (Fin 2 → ℝ) → ℝ) (φ : Fin 2 → ℝ) (a : Fin 2) : ℝ :=
  fderiv ℝ f φ (Pi.single a 1)

namespace C1Close

variable {f g h p q : (Fin 2 → ℝ) → ℝ} {e₀ e₁ d₀ d₁ : ℝ}

theorem differentiable_left (H : C1Close f g e₀ e₁) : Differentiable ℝ f := H.1

theorem differentiable_right (H : C1Close f g e₀ e₁) : Differentiable ℝ g := H.2.1

theorem abs_sub_le (H : C1Close f g e₀ e₁) (φ : Fin 2 → ℝ) : |f φ - g φ| ≤ e₀ := H.2.2.1 φ

theorem abs_pderiv_sub_le (H : C1Close f g e₀ e₁) (φ : Fin 2 → ℝ) (a : Fin 2) :
    |pderiv f φ a - pderiv g φ a| ≤ e₁ := H.2.2.2 φ a

theorem e₀_nonneg (H : C1Close f g e₀ e₁) : 0 ≤ e₀ := (abs_nonneg _).trans (H.abs_sub_le 0)

theorem e₁_nonneg (H : C1Close f g e₀ e₁) : 0 ≤ e₁ := (abs_nonneg _).trans (H.abs_pderiv_sub_le 0 0)

/-- Build `C1Close` from its four fields, with the derivatives as `pderiv`. -/
theorem intro (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (h0 : ∀ φ, |f φ - g φ| ≤ e₀)
    (h1 : ∀ φ a, |pderiv f φ a - pderiv g φ a| ≤ e₁) : C1Close f g e₀ e₁ :=
  ⟨hf, hg, h0, h1⟩

/-- Reflexivity: a differentiable function is its own model with zero errors. -/
theorem refl (hg : Differentiable ℝ g) : C1Close g g 0 0 :=
  ⟨hg, hg, fun _ => by simp, fun _ _ => by simp⟩

/-- Monotonicity in the error bounds. -/
theorem mono (H : C1Close f g e₀ e₁) {e₀' e₁' : ℝ} (h₀ : e₀ ≤ e₀') (h₁ : e₁ ≤ e₁') :
    C1Close f g e₀' e₁' :=
  ⟨H.1, H.2.1, fun φ => (H.abs_sub_le φ).trans h₀, fun φ a => (H.abs_pderiv_sub_le φ a).trans h₁⟩

theorem symm (H : C1Close f g e₀ e₁) : C1Close g f e₀ e₁ :=
  ⟨H.2.1, H.1, fun φ => by rw [abs_sub_comm]; exact H.abs_sub_le φ,
    fun φ a => by rw [abs_sub_comm]; exact H.abs_pderiv_sub_le φ a⟩

/-- The triangle inequality. -/
theorem trans (H : C1Close f g e₀ e₁) (K : C1Close g h d₀ d₁) : C1Close f h (e₀ + d₀) (e₁ + d₁) :=
  ⟨H.1, K.2.1, fun φ => by
    have := abs_add_le (f φ - g φ) (g φ - h φ)
    rw [sub_add_sub_cancel] at this
    linarith [H.abs_sub_le φ, K.abs_sub_le φ], fun φ a => by
    have := abs_add_le (pderiv f φ a - pderiv g φ a) (pderiv g φ a - pderiv h φ a)
    rw [sub_add_sub_cancel] at this
    linarith [H.abs_pderiv_sub_le φ a, K.abs_pderiv_sub_le φ a]⟩

/-! ### Derivatives of sums and products, as `pderiv` -/

theorem pderiv_add (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (φ : Fin 2 → ℝ)
    (a : Fin 2) : pderiv (f + g) φ a = pderiv f φ a + pderiv g φ a := by
  simp only [pderiv]
  rw [fderiv_add (hf φ) (hg φ)]
  rfl

theorem pderiv_sub (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (φ : Fin 2 → ℝ)
    (a : Fin 2) : pderiv (f - g) φ a = pderiv f φ a - pderiv g φ a := by
  simp only [pderiv]
  rw [fderiv_sub (hf φ) (hg φ)]
  rfl

theorem pderiv_neg (φ : Fin 2 → ℝ) (a : Fin 2) : pderiv (-f) φ a = -pderiv f φ a := by
  simp only [pderiv]
  rw [fderiv_neg]
  rfl

theorem pderiv_const_mul (hf : Differentiable ℝ f) (c : ℝ) (φ : Fin 2 → ℝ) (a : Fin 2) :
    pderiv (fun x => c * f x) φ a = c * pderiv f φ a := by
  simp only [pderiv]
  rw [fderiv_const_mul (hf φ)]
  rfl

theorem pderiv_mul (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (φ : Fin 2 → ℝ)
    (a : Fin 2) : pderiv (f * g) φ a = f φ * pderiv g φ a + g φ * pderiv f φ a := by
  simp only [pderiv]
  rw [fderiv_mul (hf φ) (hg φ)]
  rfl

/-! ### Linear operations -/

theorem add (H : C1Close f p e₀ e₁) (K : C1Close g q d₀ d₁) :
    C1Close (f + g) (p + q) (e₀ + d₀) (e₁ + d₁) := by
  refine ⟨H.1.add K.1, H.2.1.add K.2.1, fun φ => ?_, fun φ a => ?_⟩
  · have := abs_add_le (f φ - p φ) (g φ - q φ)
    simp only [Pi.add_apply]
    rw [show f φ + g φ - (p φ + q φ) = f φ - p φ + (g φ - q φ) by ring]
    linarith [H.abs_sub_le φ, K.abs_sub_le φ]
  · have e := abs_add_le (pderiv f φ a - pderiv p φ a) (pderiv g φ a - pderiv q φ a)
    have := H.abs_pderiv_sub_le φ a
    have := K.abs_pderiv_sub_le φ a
    change |pderiv (f + g) φ a - pderiv (p + q) φ a| ≤ _
    rw [pderiv_add H.1 K.1, pderiv_add H.2.1 K.2.1,
      show pderiv f φ a + pderiv g φ a - (pderiv p φ a + pderiv q φ a) =
        pderiv f φ a - pderiv p φ a + (pderiv g φ a - pderiv q φ a) by ring]
    linarith

theorem neg (H : C1Close f p e₀ e₁) : C1Close (-f) (-p) e₀ e₁ := by
  refine ⟨H.1.neg, H.2.1.neg, fun φ => ?_, fun φ a => ?_⟩
  · simp only [Pi.neg_apply]
    rw [show -f φ - -p φ = -(f φ - p φ) by ring, abs_neg]
    exact H.abs_sub_le φ
  · change |pderiv (-f) φ a - pderiv (-p) φ a| ≤ _
    rw [pderiv_neg, pderiv_neg, show -pderiv f φ a - -pderiv p φ a =
      -(pderiv f φ a - pderiv p φ a) by ring, abs_neg]
    exact H.abs_pderiv_sub_le φ a

theorem sub (H : C1Close f p e₀ e₁) (K : C1Close g q d₀ d₁) :
    C1Close (f - g) (p - q) (e₀ + d₀) (e₁ + d₁) := by
  simpa [sub_eq_add_neg] using H.add K.neg

/-- Scalar multiplication. -/
theorem const_mul (H : C1Close f p e₀ e₁) (c : ℝ) :
    C1Close (fun x => c * f x) (fun x => c * p x) (|c| * e₀) (|c| * e₁) := by
  refine ⟨fun x => (H.1 x).const_mul c, fun x => (H.2.1 x).const_mul c, fun φ => ?_,
    fun φ a => ?_⟩
  · rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (H.abs_sub_le φ) (abs_nonneg c)
  · change |pderiv (fun x => c * f x) φ a - pderiv (fun x => c * p x) φ a| ≤ _
    rw [pderiv_const_mul H.1, pderiv_const_mul H.2.1, ← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (H.abs_pderiv_sub_le φ a) (abs_nonneg c)

/-- The zero model of the zero function. -/
theorem zero : C1Close (0 : (Fin 2 → ℝ) → ℝ) 0 0 0 := refl (differentiable_const 0)

/-- Finite sums. -/
theorem sum {ι : Type*} (s : Finset ι) {F P : ι → (Fin 2 → ℝ) → ℝ} {E₀ E₁ : ι → ℝ}
    (H : ∀ i ∈ s, C1Close (F i) (P i) (E₀ i) (E₁ i)) :
    C1Close (∑ i ∈ s, F i) (∑ i ∈ s, P i) (∑ i ∈ s, E₀ i) (∑ i ∈ s, E₁ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi]
    exact (H i (Finset.mem_insert_self i s)).add
      (ih fun j hj => H j (Finset.mem_insert_of_mem hj))

/-! ### The product rule -/

/-- The product rule for `C¹` models. With `|p| ≤ P₀`, `|∂_a p| ≤ P₁`, `|q| ≤ Q₀`, `|∂_a q| ≤ Q₁`:
`f g - p q = p (g - q) + q (f - p) + (f - p)(g - q)`, and
`∂(f g) - ∂(p q) = (f - p) ∂q + p (∂g - ∂q) + (f - p)(∂g - ∂q)
  + (g - q) ∂p + q (∂f - ∂p) + (g - q)(∂f - ∂p)`. -/
theorem mul (H : C1Close f p e₀ e₁) (K : C1Close g q d₀ d₁) {P₀ P₁ Q₀ Q₁ : ℝ}
    (hP₀ : ∀ φ, |p φ| ≤ P₀) (hP₁ : ∀ φ a, |pderiv p φ a| ≤ P₁)
    (hQ₀ : ∀ φ, |q φ| ≤ Q₀) (hQ₁ : ∀ φ a, |pderiv q φ a| ≤ Q₁) :
    C1Close (f * g) (p * q) (P₀ * d₀ + Q₀ * e₀ + e₀ * d₀)
      (P₁ * d₀ + P₀ * d₁ + Q₁ * e₀ + Q₀ * e₁ + e₁ * d₀ + e₀ * d₁) := by
  refine ⟨H.1.mul K.1, H.2.1.mul K.2.1, fun φ => ?_, fun φ a => ?_⟩
  · have he := H.abs_sub_le φ
    have hd := K.abs_sub_le φ
    simp only [Pi.mul_apply]
    rw [show f φ * g φ - p φ * q φ = p φ * (g φ - q φ) + q φ * (f φ - p φ) +
      (f φ - p φ) * (g φ - q φ) by ring]
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_ <;> rw [abs_mul]
    · exact mul_le_mul (hP₀ φ) hd (abs_nonneg _) ((abs_nonneg _).trans (hP₀ φ))
    · exact mul_le_mul (hQ₀ φ) he (abs_nonneg _) ((abs_nonneg _).trans (hQ₀ φ))
    · exact mul_le_mul he hd (abs_nonneg _) H.e₀_nonneg
  · have he := H.abs_sub_le φ
    have hd := K.abs_sub_le φ
    have he' := H.abs_pderiv_sub_le φ a
    have hd' := K.abs_pderiv_sub_le φ a
    change |pderiv (f * g) φ a - pderiv (p * q) φ a| ≤ _
    rw [pderiv_mul H.1 K.1, pderiv_mul H.2.1 K.2.1]
    set F := pderiv f φ a
    set G := pderiv g φ a
    set Pd := pderiv p φ a
    set Qd := pderiv q φ a
    rw [show f φ * G + g φ * F - (p φ * Qd + q φ * Pd) =
      (g φ - q φ) * Pd + p φ * (G - Qd) + (f φ - p φ) * Qd + q φ * (F - Pd) +
        (F - Pd) * (g φ - q φ) + (f φ - p φ) * (G - Qd) by ring]
    have t1 : |(g φ - q φ) * Pd| ≤ P₁ * d₀ := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul (hP₁ φ a) hd (abs_nonneg _) ((abs_nonneg _).trans (hP₁ φ a))
    have t2 : |p φ * (G - Qd)| ≤ P₀ * d₁ := by
      rw [abs_mul]
      exact mul_le_mul (hP₀ φ) hd' (abs_nonneg _) ((abs_nonneg _).trans (hP₀ φ))
    have t3 : |(f φ - p φ) * Qd| ≤ Q₁ * e₀ := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul (hQ₁ φ a) he (abs_nonneg _) ((abs_nonneg _).trans (hQ₁ φ a))
    have t4 : |q φ * (F - Pd)| ≤ Q₀ * e₁ := by
      rw [abs_mul]
      exact mul_le_mul (hQ₀ φ) he' (abs_nonneg _) ((abs_nonneg _).trans (hQ₀ φ))
    have t5 : |(F - Pd) * (g φ - q φ)| ≤ e₁ * d₀ := by
      rw [abs_mul]
      exact mul_le_mul he' hd (abs_nonneg _) H.e₁_nonneg
    have t6 : |(f φ - p φ) * (G - Qd)| ≤ e₀ * d₁ := by
      rw [abs_mul]
      exact mul_le_mul he hd' (abs_nonneg _) H.e₀_nonneg
    have a1 := abs_add_le ((g φ - q φ) * Pd) (p φ * (G - Qd))
    have a2 := abs_add_le ((g φ - q φ) * Pd + p φ * (G - Qd)) ((f φ - p φ) * Qd)
    have a3 := abs_add_le ((g φ - q φ) * Pd + p φ * (G - Qd) + (f φ - p φ) * Qd)
      (q φ * (F - Pd))
    have a4 := abs_add_le ((g φ - q φ) * Pd + p φ * (G - Qd) + (f φ - p φ) * Qd +
      q φ * (F - Pd)) ((F - Pd) * (g φ - q φ))
    have a5 := abs_add_le ((g φ - q φ) * Pd + p φ * (G - Qd) + (f φ - p φ) * Qd +
      q φ * (F - Pd) + (F - Pd) * (g φ - q φ)) ((f φ - p φ) * (G - Qd))
    linarith

/-! ### Sup bounds through a model -/

theorem abs_le (H : C1Close f p e₀ e₁) {P₀ : ℝ} (hP₀ : ∀ φ, |p φ| ≤ P₀) (φ : Fin 2 → ℝ) :
    |f φ| ≤ P₀ + e₀ := by
  have := abs_add_le (f φ - p φ) (p φ)
  rw [sub_add_cancel] at this
  linarith [H.abs_sub_le φ, hP₀ φ]

theorem abs_pderiv_le (H : C1Close f p e₀ e₁) {P₁ : ℝ} (hP₁ : ∀ φ a, |pderiv p φ a| ≤ P₁)
    (φ : Fin 2 → ℝ) (a : Fin 2) : |pderiv f φ a| ≤ P₁ + e₁ := by
  have := abs_add_le (pderiv f φ a - pderiv p φ a) (pderiv p φ a)
  rw [sub_add_cancel] at this
  linarith [H.abs_pderiv_sub_le φ a, hP₁ φ a]

/-- A lower bound of `f` through its model. -/
theorem le_of_le (H : C1Close f p e₀ e₁) {c : ℝ} (hc : ∀ φ, c ≤ p φ) (φ : Fin 2 → ℝ) :
    c - e₀ ≤ f φ := by
  have := H.abs_sub_le φ
  have := neg_abs_le (f φ - p φ)
  linarith [hc φ]

end C1Close

end KAM.EffectiveStability.Tube

end
