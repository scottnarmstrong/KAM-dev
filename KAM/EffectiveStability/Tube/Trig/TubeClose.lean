/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Algebra.C1
public import KAM.EffectiveStability.Tube.Algebra.Bounds

/-!
# `C¹` closeness on the tube (T2-CONF, N3)

Functions of `(u, φ)`, `u : Fin 3 → ℝ` the action deviations in the box `|u_j| ≤ r` (`InBox r u`)
and `φ : Fin 2 → ℝ` the reduced angles (arbitrary). `TubeClose F G r e₀ e₁ e₂`: on the box,
* the `φ`-slices `F u`, `G u` are differentiable and the `u`-slices `F · φ`, `G · φ` are
  differentiable at `u`;
* `|F - G| ≤ e₀`;
* both `φ`-partials of `F - G` are bounded by `e₁` (`pderiv`);
* all three `u`-partials of `F - G` are bounded by `e₂` (`upd`).

Algebra: `refl`, `mono`, `symm`, `trans`, `add`, `sub`, `neg`, `const_mul`, `sum`, the product
rule `mul` (value `P₀ d₀ + Q₀ e₀ + e₀ d₀`; each derivative family by `abs_leibniz_sub_le`), and
`of_c1Close` (a `u`-independent `C1Close` model).
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

/-- The box `|u_j| ≤ r` of action deviations. -/
def InBox (r : ℝ) (u : Fin 3 → ℝ) : Prop := ∀ j, |u j| ≤ r

/-- The `u`-partial `∂_{u_j} F(·, φ)` at `u`. -/
noncomputable def upd (F : (Fin 3 → ℝ) → (Fin 2 → ℝ) → ℝ) (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ)
    (j : Fin 3) : ℝ :=
  fderiv ℝ (fun v => F v φ) u (Pi.single j 1)

/-- `F` is `C¹`-close to `G` on the tube of radius `r`: values within `e₀`, `φ`-partials within
`e₁`, `u`-partials within `e₂`. -/
structure TubeClose (F G : (Fin 3 → ℝ) → (Fin 2 → ℝ) → ℝ) (r e₀ e₁ e₂ : ℝ) : Prop where
  diffφ_left : ∀ u, InBox r u → Differentiable ℝ (F u)
  diffφ_right : ∀ u, InBox r u → Differentiable ℝ (G u)
  diffu_left : ∀ u, InBox r u → ∀ φ, DifferentiableAt ℝ (fun v => F v φ) u
  diffu_right : ∀ u, InBox r u → ∀ φ, DifferentiableAt ℝ (fun v => G v φ) u
  val : ∀ u, InBox r u → ∀ φ, |F u φ - G u φ| ≤ e₀
  dφ : ∀ u, InBox r u → ∀ φ a, |pderiv (F u) φ a - pderiv (G u) φ a| ≤ e₁
  du : ∀ u, InBox r u → ∀ φ j, |upd F u φ j - upd G u φ j| ≤ e₂

/-- The tube functions that are differentiable in each slice on the box. -/
structure TubeDiff (F : (Fin 3 → ℝ) → (Fin 2 → ℝ) → ℝ) (r : ℝ) : Prop where
  φ : ∀ u, InBox r u → Differentiable ℝ (F u)
  u : ∀ u, InBox r u → ∀ φ, DifferentiableAt ℝ (fun v => F v φ) u

namespace TubeClose

variable {F G H K : (Fin 3 → ℝ) → (Fin 2 → ℝ) → ℝ} {r e₀ e₁ e₂ d₀ d₁ d₂ : ℝ}

theorem tubeDiff_left (h : TubeClose F G r e₀ e₁ e₂) : TubeDiff F r := ⟨h.diffφ_left, h.diffu_left⟩

theorem tubeDiff_right (h : TubeClose F G r e₀ e₁ e₂) : TubeDiff G r :=
  ⟨h.diffφ_right, h.diffu_right⟩

theorem refl (hF : TubeDiff F r) : TubeClose F F r 0 0 0 :=
  ⟨hF.φ, hF.φ, hF.u, hF.u, fun _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩

theorem mono (h : TubeClose F G r e₀ e₁ e₂) {e₀' e₁' e₂' : ℝ} (h₀ : e₀ ≤ e₀') (h₁ : e₁ ≤ e₁')
    (h₂ : e₂ ≤ e₂') : TubeClose F G r e₀' e₁' e₂' :=
  ⟨h.diffφ_left, h.diffφ_right, h.diffu_left, h.diffu_right,
    fun u hu φ => (h.val u hu φ).trans h₀, fun u hu φ a => (h.dφ u hu φ a).trans h₁,
    fun u hu φ j => (h.du u hu φ j).trans h₂⟩

theorem symm (h : TubeClose F G r e₀ e₁ e₂) : TubeClose G F r e₀ e₁ e₂ :=
  ⟨h.diffφ_right, h.diffφ_left, h.diffu_right, h.diffu_left,
    fun u hu φ => by rw [abs_sub_comm]; exact h.val u hu φ,
    fun u hu φ a => by rw [abs_sub_comm]; exact h.dφ u hu φ a,
    fun u hu φ j => by rw [abs_sub_comm]; exact h.du u hu φ j⟩

theorem trans (h : TubeClose F G r e₀ e₁ e₂) (k : TubeClose G H r d₀ d₁ d₂) :
    TubeClose F H r (e₀ + d₀) (e₁ + d₁) (e₂ + d₂) :=
  ⟨h.diffφ_left, k.diffφ_right, h.diffu_left, k.diffu_right,
    fun u hu φ => abs_sub_le_of_le (h.val u hu φ) (k.val u hu φ),
    fun u hu φ a => abs_sub_le_of_le (h.dφ u hu φ a) (k.dφ u hu φ a),
    fun u hu φ j => abs_sub_le_of_le (h.du u hu φ j) (k.du u hu φ j)⟩

/-! ### Derivative rules in the `u`-slices -/

theorem upd_add {u : Fin 3 → ℝ} {φ : Fin 2 → ℝ} (hF : DifferentiableAt ℝ (fun v => F v φ) u)
    (hG : DifferentiableAt ℝ (fun v => G v φ) u) (j : Fin 3) :
    upd (fun v ψ => F v ψ + G v ψ) u φ j = upd F u φ j + upd G u φ j := by
  simp only [upd]
  rw [fderiv_fun_add hF hG]
  rfl

theorem upd_neg {u : Fin 3 → ℝ} {φ : Fin 2 → ℝ} (j : Fin 3) :
    upd (fun v ψ => -F v ψ) u φ j = -upd F u φ j := by
  simp only [upd]
  rw [fderiv_fun_neg]
  rfl

theorem upd_const_mul {u : Fin 3 → ℝ} {φ : Fin 2 → ℝ}
    (hF : DifferentiableAt ℝ (fun v => F v φ) u) (c : ℝ) (j : Fin 3) :
    upd (fun v ψ => c * F v ψ) u φ j = c * upd F u φ j := by
  simp only [upd]
  rw [fderiv_const_mul hF]
  rfl

theorem upd_mul {u : Fin 3 → ℝ} {φ : Fin 2 → ℝ} (hF : DifferentiableAt ℝ (fun v => F v φ) u)
    (hG : DifferentiableAt ℝ (fun v => G v φ) u) (j : Fin 3) :
    upd (fun v ψ => F v ψ * G v ψ) u φ j = F u φ * upd G u φ j + G u φ * upd F u φ j := by
  simp only [upd]
  rw [fderiv_fun_mul hF hG]
  rfl

/-! ### Linear operations -/

theorem add (h : TubeClose F G r e₀ e₁ e₂) (k : TubeClose H K r d₀ d₁ d₂) :
    TubeClose (fun u φ => F u φ + H u φ) (fun u φ => G u φ + K u φ) r (e₀ + d₀) (e₁ + d₁)
      (e₂ + d₂) := by
  refine ⟨fun u hu => (h.diffφ_left u hu).add (k.diffφ_left u hu),
    fun u hu => (h.diffφ_right u hu).add (k.diffφ_right u hu),
    fun u hu φ => (h.diffu_left u hu φ).add (k.diffu_left u hu φ),
    fun u hu φ => (h.diffu_right u hu φ).add (k.diffu_right u hu φ),
    fun u hu φ => abs_add_sub_add_le (h.val u hu φ) (k.val u hu φ), fun u hu φ a => ?_,
    fun u hu φ j => ?_⟩
  · change |pderiv (F u + H u) φ a - pderiv (G u + K u) φ a| ≤ _
    rw [C1Close.pderiv_add (h.diffφ_left u hu) (k.diffφ_left u hu),
      C1Close.pderiv_add (h.diffφ_right u hu) (k.diffφ_right u hu)]
    exact abs_add_sub_add_le (h.dφ u hu φ a) (k.dφ u hu φ a)
  · rw [upd_add (h.diffu_left u hu φ) (k.diffu_left u hu φ),
      upd_add (h.diffu_right u hu φ) (k.diffu_right u hu φ)]
    exact abs_add_sub_add_le (h.du u hu φ j) (k.du u hu φ j)

theorem neg (h : TubeClose F G r e₀ e₁ e₂) :
    TubeClose (fun u φ => -F u φ) (fun u φ => -G u φ) r e₀ e₁ e₂ := by
  refine ⟨fun u hu => (h.diffφ_left u hu).neg, fun u hu => (h.diffφ_right u hu).neg,
    fun u hu φ => (h.diffu_left u hu φ).neg, fun u hu φ => (h.diffu_right u hu φ).neg,
    fun u hu φ => ?_, fun u hu φ a => ?_, fun u hu φ j => ?_⟩
  · rw [show -F u φ - -G u φ = -(F u φ - G u φ) by ring, abs_neg]; exact h.val u hu φ
  · change |pderiv (-F u) φ a - pderiv (-G u) φ a| ≤ _
    rw [C1Close.pderiv_neg, C1Close.pderiv_neg,
      show -pderiv (F u) φ a - -pderiv (G u) φ a = -(pderiv (F u) φ a - pderiv (G u) φ a) by
        ring, abs_neg]
    exact h.dφ u hu φ a
  · rw [upd_neg, upd_neg, show -upd F u φ j - -upd G u φ j = -(upd F u φ j - upd G u φ j) by
      ring, abs_neg]
    exact h.du u hu φ j

theorem sub (h : TubeClose F G r e₀ e₁ e₂) (k : TubeClose H K r d₀ d₁ d₂) :
    TubeClose (fun u φ => F u φ - H u φ) (fun u φ => G u φ - K u φ) r (e₀ + d₀) (e₁ + d₁)
      (e₂ + d₂) := by
  simpa [sub_eq_add_neg] using h.add k.neg

theorem const_mul (h : TubeClose F G r e₀ e₁ e₂) (c : ℝ) :
    TubeClose (fun u φ => c * F u φ) (fun u φ => c * G u φ) r (|c| * e₀) (|c| * e₁)
      (|c| * e₂) := by
  refine ⟨fun u hu => (h.diffφ_left u hu).const_mul c,
    fun u hu => (h.diffφ_right u hu).const_mul c,
    fun u hu φ => (h.diffu_left u hu φ).const_mul c,
    fun u hu φ => (h.diffu_right u hu φ).const_mul c, fun u hu φ => ?_, fun u hu φ a => ?_,
    fun u hu φ j => ?_⟩
  · rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (h.val u hu φ) (abs_nonneg c)
  · change |pderiv (fun x => c * F u x) φ a - pderiv (fun x => c * G u x) φ a| ≤ _
    rw [C1Close.pderiv_const_mul (h.diffφ_left u hu), C1Close.pderiv_const_mul (h.diffφ_right u hu),
      ← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (h.dφ u hu φ a) (abs_nonneg c)
  · rw [upd_const_mul (h.diffu_left u hu φ), upd_const_mul (h.diffu_right u hu φ), ← mul_sub,
      abs_mul]
    exact mul_le_mul_of_nonneg_left (h.du u hu φ j) (abs_nonneg c)

theorem zero : TubeClose (fun _ _ => (0 : ℝ)) (fun _ _ => 0) r 0 0 0 :=
  refl ⟨fun _ _ => differentiable_const 0, fun _ _ _ => differentiableAt_const 0⟩

/-- Finite sums. -/
theorem sum {ι : Type*} (s : Finset ι) {Fs Gs : ι → (Fin 3 → ℝ) → (Fin 2 → ℝ) → ℝ}
    {E₀ E₁ E₂ : ι → ℝ} (h : ∀ i ∈ s, TubeClose (Fs i) (Gs i) r (E₀ i) (E₁ i) (E₂ i)) :
    TubeClose (fun u φ => ∑ i ∈ s, Fs i u φ) (fun u φ => ∑ i ∈ s, Gs i u φ) r (∑ i ∈ s, E₀ i)
      (∑ i ∈ s, E₁ i) (∑ i ∈ s, E₂ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (r := r))
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! ### The product rule -/

/-- **The product rule on the tube.** With sup bounds on the box of the models `G`, `K` and of
their `φ`- and `u`-partials, the product is close with errors given by `abs_mul_sub_mul_le` and
`abs_leibniz_sub_le` in each derivative family. -/
theorem mul (h : TubeClose F G r e₀ e₁ e₂) (k : TubeClose H K r d₀ d₁ d₂)
    {P₀ P₁ P₂ Q₀ Q₁ Q₂ : ℝ}
    (hP₀ : ∀ u, InBox r u → ∀ φ, |G u φ| ≤ P₀)
    (hP₁ : ∀ u, InBox r u → ∀ φ a, |pderiv (G u) φ a| ≤ P₁)
    (hP₂ : ∀ u, InBox r u → ∀ φ j, |upd G u φ j| ≤ P₂)
    (hQ₀ : ∀ u, InBox r u → ∀ φ, |K u φ| ≤ Q₀)
    (hQ₁ : ∀ u, InBox r u → ∀ φ a, |pderiv (K u) φ a| ≤ Q₁)
    (hQ₂ : ∀ u, InBox r u → ∀ φ j, |upd K u φ j| ≤ Q₂) :
    TubeClose (fun u φ => F u φ * H u φ) (fun u φ => G u φ * K u φ) r
      (P₀ * d₀ + Q₀ * e₀ + e₀ * d₀)
      (P₁ * d₀ + P₀ * d₁ + Q₁ * e₀ + Q₀ * e₁ + e₁ * d₀ + e₀ * d₁)
      (P₂ * d₀ + P₀ * d₂ + Q₂ * e₀ + Q₀ * e₂ + e₂ * d₀ + e₀ * d₂) := by
  refine ⟨fun u hu => (h.diffφ_left u hu).mul (k.diffφ_left u hu),
    fun u hu => (h.diffφ_right u hu).mul (k.diffφ_right u hu),
    fun u hu φ => (h.diffu_left u hu φ).mul (k.diffu_left u hu φ),
    fun u hu φ => (h.diffu_right u hu φ).mul (k.diffu_right u hu φ),
    fun u hu φ => abs_mul_sub_mul_le (h.val u hu φ) (k.val u hu φ) (hP₀ u hu φ) (hQ₀ u hu φ),
    fun u hu φ a => ?_, fun u hu φ j => ?_⟩
  · change |pderiv (F u * H u) φ a - pderiv (G u * K u) φ a| ≤ _
    rw [C1Close.pderiv_mul (h.diffφ_left u hu) (k.diffφ_left u hu),
      C1Close.pderiv_mul (h.diffφ_right u hu) (k.diffφ_right u hu)]
    exact abs_leibniz_sub_le (h.val u hu φ) (k.val u hu φ) (h.dφ u hu φ a) (k.dφ u hu φ a)
      (hP₀ u hu φ) (hQ₀ u hu φ) (hP₁ u hu φ a) (hQ₁ u hu φ a)
  · rw [upd_mul (h.diffu_left u hu φ) (k.diffu_left u hu φ),
      upd_mul (h.diffu_right u hu φ) (k.diffu_right u hu φ)]
    exact abs_leibniz_sub_le (h.val u hu φ) (k.val u hu φ) (h.du u hu φ j) (k.du u hu φ j)
      (hP₀ u hu φ) (hQ₀ u hu φ) (hP₂ u hu φ j) (hQ₂ u hu φ j)

/-! ### Functions of the angles only -/

theorem upd_const_u {f : (Fin 2 → ℝ) → ℝ} (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (j : Fin 3) :
    upd (fun _ ψ => f ψ) u φ j = 0 := by
  simp [upd]

/-- A `C1Close` model of a function of the angles is a tube model with no `u`-error. -/
theorem of_c1Close {f p : (Fin 2 → ℝ) → ℝ} (h : C1Close f p e₀ e₁) :
    TubeClose (fun _ φ => f φ) (fun _ φ => p φ) r e₀ e₁ 0 :=
  ⟨fun _ _ => h.1, fun _ _ => h.2.1, fun _ _ _ => differentiableAt_const _,
    fun _ _ _ => differentiableAt_const _, fun _ _ φ => h.abs_sub_le φ,
    fun _ _ φ a => h.abs_pderiv_sub_le φ a,
    fun u _ φ j => by rw [upd_const_u, upd_const_u, sub_zero, abs_zero]⟩

end TubeClose

end KAM.EffectiveStability.Tube

end
