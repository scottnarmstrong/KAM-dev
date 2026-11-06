/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Initial.Partials

/-!
# Tube observables given by a list of model terms (T2-CONF, N8)

An observable `f(u, φ) = Σ_{e ∈ L} u^{μ_e} g_e(φ)` over a list `L` (`listObs`; the literal
observables
of the tube checker are of this form, one term per stored `u`-monomial):

* `hasFDerivAt_listObs`, `differentiable_listObs`, `listObs_add_two_pi` (`2π`-periodicity);
* `fderiv_listObs_u`, `fderiv_listObs_φ`: the joint derivative in the directions `(e_l, 0)`,
  `(0, e_b)`;
* `abs_fderiv_listObs_u_le`, `abs_fderiv_listObs_φ_le`: on the box `|u| ≤ ρ`, from coefficient
  bounds
  `|g_e| ≤ G_e`, `|∂_b g_e| ≤ G'_e`;
* `abs_listObs_sub_le`: the face form `|f(u, φ) - Σ_e u^{μ_e} κ_e| ≤ Σ_e ρ^{|μ_e|} D_e` from
  `|g_e - κ_e| ≤ D_e`.

`monOf` reads a monomial stored as `(m₀, m₁, m₂)`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

/-- A `u`-monomial stored as a triple. -/
def monOf (t : ℕ × ℕ × ℕ) : Fin 3 → ℕ := ![t.1, t.2.1, t.2.2]

variable {α : Type*}

/-- `f(u, φ) = Σ_{e ∈ L} u^{μ_e} g_e(φ)`. -/
def listObs (L : List α) (μ : α → Fin 3 → ℕ) (g : α → (Fin 2 → ℝ) → ℝ)
    (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  (L.map fun e => umon (μ e) p.1 * g e p.2).sum

/-- The derivative of one term. -/
def listObsD (μ : α → Fin 3 → ℕ) (g : α → (Fin 2 → ℝ) → ℝ) (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) (e : α) :
    (Fin 3 → ℝ) × (Fin 2 → ℝ) →L[ℝ] ℝ :=
  umon (μ e) p.1 • (fderiv ℝ (g e) p.2).comp (ContinuousLinearMap.snd ℝ (Fin 3 → ℝ) (Fin 2 → ℝ)) +
    g e p.2 • (fderiv ℝ (umon (μ e)) p.1).comp (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) (Fin 2 → ℝ))

theorem hasFDerivAt_listObs (L : List α) (μ : α → Fin 3 → ℕ) {g : α → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ e ∈ L, Differentiable ℝ (g e)) (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) :
    HasFDerivAt (listObs L μ g) (L.map (listObsD μ g p)).sum p := by
  induction L with
  | nil =>
    have h0 : listObs ([] : List α) μ g = fun _ => 0 := by funext p; simp [listObs]
    rw [h0]; simpa using hasFDerivAt_const (0 : ℝ) p
  | cons e L ih =>
    have heq : listObs (e :: L) μ g = fun p => umon (μ e) p.1 * g e p.2 + listObs L μ g p := by
      funext p; simp [listObs]
    rw [heq]
    simp only [List.map_cons, List.sum_cons]
    exact (hasFDerivAt_tmEvalPair_term (μ e) (hg e (by simp)) p).add
      (ih fun e' he' => hg e' (by simp [he']))

theorem differentiable_listObs (L : List α) (μ : α → Fin 3 → ℕ) {g : α → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ e ∈ L, Differentiable ℝ (g e)) : Differentiable ℝ (listObs L μ g) :=
  fun p => (hasFDerivAt_listObs L μ hg p).differentiableAt

theorem clm_list_sum_apply' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : List α) (D : α → E →L[ℝ] F) (v : E) :
    (L.map D).sum v = (L.map fun e => D e v).sum := by
  induction L with
  | nil => simp
  | cons e L ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; rfl

theorem fderiv_listObs_u (L : List α) (μ : α → Fin 3 → ℕ) {g : α → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ e ∈ L, Differentiable ℝ (g e)) (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) (l : Fin 3) :
    fderiv ℝ (listObs L μ g) p (Pi.single l 1, 0) =
      (L.map fun e => (μ e l : ℝ) * umon (μ e - Pi.single l 1) p.1 * g e p.2).sum := by
  rw [(hasFDerivAt_listObs L μ hg p).fderiv, clm_list_sum_apply']
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [listObsD, _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', map_zero, smul_eq_mul, mul_zero,
    zero_add, fderiv_umon]
  ring

theorem fderiv_listObs_φ (L : List α) (μ : α → Fin 3 → ℕ) {g : α → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ e ∈ L, Differentiable ℝ (g e)) (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) (b : Fin 2) :
    fderiv ℝ (listObs L μ g) p (0, Pi.single b 1) =
      (L.map fun e => umon (μ e) p.1 * fderiv ℝ (g e) p.2 (Pi.single b 1)).sum := by
  rw [(hasFDerivAt_listObs L μ hg p).fderiv, clm_list_sum_apply']
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [listObsD, _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', map_zero, smul_eq_mul, mul_zero,
    add_zero]

theorem abs_list_sum_le {β : Type*} (L : List β) (f g : β → ℝ) (h : ∀ e ∈ L, |f e| ≤ g e) :
    |(L.map f).sum| ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans
      (add_le_add (h e (by simp)) (ih fun e' he' => h e' (by simp [he'])))

/-- `|∂_{u_l} f| ≤ Σ_e μ_{e,l} ρ^{|μ_e - e_l|} G_e` on the box `|u| ≤ ρ`. -/
theorem abs_fderiv_listObs_u_le (L : List α) (μ : α → Fin 3 → ℕ) {g : α → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ e ∈ L, Differentiable ℝ (g e)) {G : α → ℝ} (hG : ∀ e ∈ L, ∀ φ, |g e φ| ≤ G e)
    {ρ : ℝ} {u : Fin 3 → ℝ} (hu : ∀ l, |u l| ≤ ρ) (φ : Fin 2 → ℝ) (l : Fin 3) :
    |fderiv ℝ (listObs L μ g) (u, φ) (Pi.single l 1, 0)| ≤
      (L.map fun e => (μ e l : ℝ) * ρ ^ mdeg (μ e - Pi.single l 1) * G e).sum := by
  rw [fderiv_listObs_u L μ hg]
  refine abs_list_sum_le L _ _ fun e he => ?_
  rw [abs_mul, abs_mul, Nat.abs_cast]
  have h1 := abs_umon_le (r := ρ) hu (μ e - Pi.single l 1)
  have h0 : (0 : ℝ) ≤ μ e l := Nat.cast_nonneg _
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 h0) (hG e he φ) (abs_nonneg _)
    (mul_nonneg h0 ((abs_nonneg _).trans h1))

/-- `|∂_{φ_b} f| ≤ Σ_e ρ^{|μ_e|} G'_e` on the box `|u| ≤ ρ`. -/
theorem abs_fderiv_listObs_φ_le (L : List α) (μ : α → Fin 3 → ℕ) {g : α → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ e ∈ L, Differentiable ℝ (g e)) {b : Fin 2} {G' : α → ℝ}
    (hG' : ∀ e ∈ L, ∀ φ, |fderiv ℝ (g e) φ (Pi.single b 1)| ≤ G' e)
    {ρ : ℝ} {u : Fin 3 → ℝ} (hu : ∀ l, |u l| ≤ ρ) (φ : Fin 2 → ℝ) :
    |fderiv ℝ (listObs L μ g) (u, φ) (0, Pi.single b 1)| ≤
      (L.map fun e => ρ ^ mdeg (μ e) * G' e).sum := by
  rw [fderiv_listObs_φ L μ hg]
  refine abs_list_sum_le L _ _ fun e he => ?_
  rw [abs_mul]
  exact mul_le_mul (abs_umon_le hu (μ e)) (hG' e he φ) (abs_nonneg _)
    ((abs_nonneg _).trans (abs_umon_le hu (μ e)))

/-- The face form: `|f(u, φ) - Σ_e u^{μ_e} κ_e| ≤ Σ_e ρ^{|μ_e|} D_e` from `|g_e - κ_e| ≤ D_e`. -/
theorem abs_listObs_sub_le (L : List α) (μ : α → Fin 3 → ℕ) (g : α → (Fin 2 → ℝ) → ℝ)
    {κ D : α → ℝ} (hD : ∀ e ∈ L, ∀ φ, |g e φ - κ e| ≤ D e) {ρ : ℝ} {u : Fin 3 → ℝ}
    (hu : ∀ l, |u l| ≤ ρ) (φ : Fin 2 → ℝ) :
    |listObs L μ g (u, φ) - (L.map fun e => umon (μ e) u * κ e).sum| ≤
      (L.map fun e => ρ ^ mdeg (μ e) * D e).sum := by
  have key : ∀ M : List α, (M.map fun e => umon (μ e) u * g e φ).sum -
      (M.map fun e => umon (μ e) u * κ e).sum =
      (M.map fun e => umon (μ e) u * (g e φ - κ e)).sum := by
    intro M
    induction M with
    | nil => simp
    | cons a M ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring
  have e : listObs L μ g (u, φ) - (L.map fun e => umon (μ e) u * κ e).sum =
      (L.map fun e => umon (μ e) u * (g e φ - κ e)).sum := key L
  rw [e]
  refine abs_list_sum_le L _ _ fun e he => ?_
  rw [abs_mul]
  exact mul_le_mul (abs_umon_le hu (μ e)) (hD e he φ) (abs_nonneg _)
    ((abs_nonneg _).trans (abs_umon_le hu (μ e)))

/-- `2π`-periodicity from that of the coefficients. -/
theorem listObs_add_two_pi (L : List α) (μ : α → Fin 3 → ℕ) {g : α → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ e ∈ L, ∀ (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ),
      g e (φ + fun a => 2 * Real.pi * m a) = g e φ) :
    ∀ (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ),
      listObs L μ g (u, φ + fun a => 2 * Real.pi * m a) = listObs L μ g (u, φ) := by
  intro u φ m
  unfold listObs
  congr 1
  exact List.map_congr_left fun e he => by simp only [hg e he]

end KAM.EffectiveStability.Tube

end
