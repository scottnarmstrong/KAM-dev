/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Analytic
public import KAM.Weighted.Parametric
public import KAM.Planetary.PlanarTorsion.RealFlow.PicardOp

/-!
# Planar quartic torsion: complex-time Picard convergence (package R2)

Blueprint P, Part 11b (`bpP:p11b:e-ode`, package R2).  Let `F : ℂⁿ → ℂⁿ` be holomorphic, bounded by
`M` and `L`-Lipschitz on the ball `D = B(c, ρ)`.  On `U = {|s| < T, ‖w - c‖ < r}` with
`M T + r ≤ ρ` and `L T ≤ 1/2` the Picard iterates `u₀ = w`, `uₖ₊₁ = p11cPicardOp (F ∘ uₖ)` are
holomorphic on `U`, stay in `D`, and converge uniformly (geometrically) to a map `u` that is
holomorphic on `U` (`KAM.Weighted.uniform_limit_holomorphic`, U5), solves
`u = p11cPicardOp (F ∘ u)`, and is real on real data when `F` is real on real points of `D`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology

namespace KAM.Planetary

variable {n : ℕ}

/-- Quantitative data for the complex Picard iteration. -/
structure P11cPicardData (F : (Fin n → ℂ) → Fin n → ℂ) (c : Fin n → ℂ) (ρ M L T r : ℝ) :
    Prop where
  holo : DifferentiableOn ℂ F (ball c ρ)
  bound : ∀ z ∈ ball c ρ, ‖F z‖ ≤ M
  lip : ∀ a ∈ ball c ρ, ∀ b ∈ ball c ρ, ‖F a - F b‖ ≤ L * ‖a - b‖
  M_nonneg : 0 ≤ M
  L_nonneg : 0 ≤ L
  T_pos : 0 < T
  r_pos : 0 < r
  MT : M * T + r ≤ ρ
  LT : L * T ≤ 1 / 2

theorem p11c_intervalIntegrable_scale {c : Fin n → ℂ} {T r : ℝ}
    {v : (Fin (n + 1) → ℂ) → Fin n → ℂ} (hv : ContinuousOn v (p11cDom n c T r))
    {ζ : Fin (n + 1) → ℂ} (hζ : ζ ∈ p11cDom n c T r) :
    IntervalIntegrable (fun σ : ℝ => v (p11cTimeScale n σ ζ)) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le zero_le_one]
  refine hv.comp ((continuous_p11cTimeScale_apply.comp
    (continuous_id.prodMk continuous_const)).continuousOn) fun σ hσ => ?_
  exact p11cTimeScale_mem hσ hζ

/-- Lipschitz dependence of the Picard operator on its integrand, in the sup norm. -/
theorem p11cPicardOp_sub_le {c : Fin n → ℂ} {T r : ℝ} {v v' : (Fin (n + 1) → ℂ) → Fin n → ℂ}
    (hv : ContinuousOn v (p11cDom n c T r)) (hv' : ContinuousOn v' (p11cDom n c T r)) {b : ℝ}
    (hb : ∀ ζ ∈ p11cDom n c T r, ‖v ζ - v' ζ‖ ≤ b) {ζ : Fin (n + 1) → ℂ}
    (hζ : ζ ∈ p11cDom n c T r) :
    ‖p11cPicardOp v ζ - p11cPicardOp v' ζ‖ ≤ ‖ζ 0‖ * b := by
  have h1 := p11c_intervalIntegrable_scale hv hζ
  have h2 := p11c_intervalIntegrable_scale hv' hζ
  have hint : ‖∫ σ in (0 : ℝ)..1, (v (p11cTimeScale n σ ζ) - v' (p11cTimeScale n σ ζ))‖ ≤ b := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun σ : ℝ => v (p11cTimeScale n σ ζ) - v' (p11cTimeScale n σ ζ)) (C := b)
      fun σ hσ => hb _ (p11cTimeScale_mem (by
        rw [uIoc_of_le zero_le_one] at hσ; exact ⟨hσ.1.le, hσ.2⟩) hζ)
    simpa using this
  unfold p11cPicardOp
  rw [add_sub_add_left_eq_sub, ← smul_sub, ← intervalIntegral.integral_sub h1 h2, norm_smul]
  exact mul_le_mul_of_nonneg_left hint (norm_nonneg _)

/-- The Picard iterates `u₀ = w`, `uₖ₊₁ = p11cPicardOp (F ∘ uₖ)`. -/
def p11cIter (F : (Fin n → ℂ) → Fin n → ℂ) : ℕ → (Fin (n + 1) → ℂ) → Fin n → ℂ
  | 0 => fun ζ => p11cSp n ζ
  | k + 1 => p11cPicardOp (fun ζ => F (p11cIter F k ζ))

/-- Imaginary parts of the components vanish: the vector is real. -/
def p11cIsReal (X : Fin n → ℂ) : Prop := ∀ i, (X i).im = 0

theorem p11cPicardOp_isReal {v : (Fin (n + 1) → ℂ) → Fin n → ℂ} {ζ : Fin (n + 1) → ℂ}
    (hint : IntervalIntegrable (fun σ : ℝ => v (p11cTimeScale n σ ζ)) volume 0 1)
    (hζ0 : (ζ 0).im = 0) (hζs : p11cIsReal (p11cSp n ζ))
    (hv : ∀ σ ∈ Icc (0 : ℝ) 1, p11cIsReal (v (p11cTimeScale n σ ζ))) :
    p11cIsReal (p11cPicardOp v ζ) := by
  intro i
  let Li : (Fin n → ℂ) →L[ℝ] ℝ :=
    Complex.imCLM.comp ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ)
  have hLi : ∀ X : Fin n → ℂ, Li X = (X i).im := fun X => rfl
  have h0 : Li (∫ σ in (0 : ℝ)..1, v (p11cTimeScale n σ ζ)) = 0 := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm Li hint]
    have hz : ∀ σ ∈ uIcc (0 : ℝ) 1, Li (v (p11cTimeScale n σ ζ)) = 0 := fun σ hσ => by
      rw [uIcc_of_le zero_le_one] at hσ
      simpa [hLi] using hv σ hσ i
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) hz]
    simp
  rw [hLi] at h0
  have := hζs i
  simp only [p11cPicardOp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_im,
    Complex.mul_im, p11cSp_apply] at this ⊢
  rw [h0, hζ0, this]
  ring

theorem p11cIter_zero (F : (Fin n → ℂ) → Fin n → ℂ) (ζ : Fin (n + 1) → ℂ) :
    p11cIter F 0 ζ = p11cSp n ζ := rfl

theorem p11cIter_succ (F : (Fin n → ℂ) → Fin n → ℂ) (k : ℕ) (ζ : Fin (n + 1) → ℂ) :
    p11cIter F (k + 1) ζ = p11cPicardOp (fun ζ => F (p11cIter F k ζ)) ζ := rfl

theorem p11cPicardOp_zero (ζ : Fin (n + 1) → ℂ) :
    p11cPicardOp (fun _ => (0 : Fin n → ℂ)) ζ = p11cSp n ζ := by
  simp [p11cPicardOp]

namespace P11cPicardData

variable {F : (Fin n → ℂ) → Fin n → ℂ} {c : Fin n → ℂ} {ρ M L T r : ℝ}
  (h : P11cPicardData F c ρ M L T r)
include h

theorem mem_ball {ζ : Fin (n + 1) → ℂ} (hζ : ζ ∈ p11cDom n c T r) {X : Fin n → ℂ}
    (hX : ‖X - p11cSp n ζ‖ ≤ M * ‖ζ 0‖) : X ∈ ball c ρ := by
  rw [mem_ball_iff_norm]
  have h1 : M * ‖ζ 0‖ ≤ M * T := mul_le_mul_of_nonneg_left hζ.1.le h.M_nonneg
  calc ‖X - c‖ = ‖(X - p11cSp n ζ) + (p11cSp n ζ - c)‖ := by congr 1; abel
    _ ≤ ‖X - p11cSp n ζ‖ + ‖p11cSp n ζ - c‖ := norm_add_le _ _
    _ < ρ := by linarith [hζ.2, h.MT]

theorem iter_spec (k : ℕ) : (∀ ζ ∈ p11cDom n c T r, ‖p11cIter F k ζ - p11cSp n ζ‖ ≤ M * ‖ζ 0‖) ∧
    DifferentiableOn ℂ (p11cIter F k) (p11cDom n c T r) := by
  induction k with
  | zero =>
    exact ⟨fun ζ _ => by simpa [p11cIter_zero] using mul_nonneg h.M_nonneg (norm_nonneg _),
      (p11cSp n).differentiableOn⟩
  | succ k ih =>
    obtain ⟨hb, hd⟩ := ih
    have hFi : DifferentiableOn ℂ (fun ζ => F (p11cIter F k ζ)) (p11cDom n c T r) :=
      h.holo.comp hd fun ζ hζ => h.mem_ball hζ (hb ζ hζ)
    refine ⟨fun ζ hζ => ?_, ?_⟩
    · have := p11cPicardOp_sub_le hFi.continuousOn (continuousOn_const (c := (0 : Fin n → ℂ)))
        (b := M) (fun ζ' hζ' => by
          simpa using h.bound _ (h.mem_ball hζ' (hb ζ' hζ'))) hζ
      rw [p11cPicardOp_zero] at this
      simpa [p11cIter_succ, mul_comm] using this
    · exact p11cPicardOp_differentiableOn hFi

theorem iter_mem {k : ℕ} {ζ : Fin (n + 1) → ℂ} (hζ : ζ ∈ p11cDom n c T r) :
    p11cIter F k ζ ∈ ball c ρ := h.mem_ball hζ ((h.iter_spec k).1 ζ hζ)

theorem iter_dist (k : ℕ) : ∀ ζ ∈ p11cDom n c T r,
    ‖p11cIter F (k + 1) ζ - p11cIter F k ζ‖ ≤ M * T * (1 / 2) ^ k := by
  induction k with
  | zero =>
    intro ζ hζ
    have := (h.iter_spec 1).1 ζ hζ
    have h1 : M * ‖ζ 0‖ ≤ M * T := mul_le_mul_of_nonneg_left hζ.1.le h.M_nonneg
    simpa [p11cIter_zero] using this.trans h1
  | succ k ih =>
    intro ζ hζ
    have hc := fun j => (h.iter_spec j).2.continuousOn
    have hcF : ∀ j, ContinuousOn (fun ζ => F (p11cIter F j ζ)) (p11cDom n c T r) := fun j =>
      (h.holo.comp (h.iter_spec j).2 fun ζ hζ => h.iter_mem hζ).continuousOn
    have hX : 0 ≤ M * T * (1 / 2) ^ k := by
      have := h.M_nonneg; have := h.T_pos; positivity
    have key := p11cPicardOp_sub_le (hcF (k + 1)) (hcF k)
      (b := L * (M * T * (1 / 2) ^ k))
      (fun ζ' hζ' => (h.lip _ (h.iter_mem hζ') _ (h.iter_mem hζ')).trans
        (mul_le_mul_of_nonneg_left (ih ζ' hζ') h.L_nonneg)) hζ
    rw [p11cIter_succ, p11cIter_succ]
    refine key.trans ?_
    calc ‖ζ 0‖ * (L * (M * T * (1 / 2) ^ k)) ≤ T * (L * (M * T * (1 / 2) ^ k)) :=
          mul_le_mul_of_nonneg_right hζ.1.le (mul_nonneg h.L_nonneg hX)
      _ = (L * T) * (M * T * (1 / 2) ^ k) := by ring
      _ ≤ (1 / 2) * (M * T * (1 / 2) ^ k) := mul_le_mul_of_nonneg_right h.LT hX
      _ = M * T * (1 / 2) ^ (k + 1) := by rw [pow_succ]; ring

end P11cPicardData

end KAM.Planetary
