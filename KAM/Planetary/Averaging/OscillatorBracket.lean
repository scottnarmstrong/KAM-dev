/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.OscillatorSetting
public import KAM.Weighted.Algebra
public import KAM.Weighted.Cauchy
public import KAM.Weighted.Parametric
public import KAM.Weighted.SupWeighted
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# P Parts 2-3: the oscillator Poisson bracket (`bpP:p2:osc-bracket`)

Flat layer: the Cauchy estimates of `KAM.Weighted` at a fixed flat parameter, with a separate
loss in each coordinate direction (one-dimensional discs), for a function on a strip times an
arbitrary open parameter set. Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-11.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

section Flat

variable {n N : ℕ}

theorem polyNbhd_singleton (x : Fin N → ℂ) (δ : ℝ) :
    polyNbhd ({x} : Set (Fin N → ℂ)) δ = ball x δ := by
  ext I
  simp [polyNbhd, mem_ball, dist_eq_norm]

/-- Holomorphic and `1`-periodic on the strip times the parameter set `P`. -/
def FClass (S : ℝ) (P : Set (Fin N → ℂ)) (F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ) : Prop :=
  DifferentiableOn ℂ F (KAM.complexStrip n S ×ˢ P) ∧
    ∀ j : Fin n, ∀ z ∈ KAM.complexStrip n S ×ˢ P, F (z.1 + Pi.single j 1, z.2) = F z

theorem FClass.inClass {S s δ : ℝ} {x : Fin N → ℂ} {P : Set (Fin N → ℂ)}
    {F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ} (h : FClass S P F) (hb : ball x δ ⊆ P) (hs : s ≤ S) :
    InClass ({x} : Set (Fin N → ℂ)) δ s F := by
  have hsub : Dom n ({x} : Set (Fin N → ℂ)) δ s ⊆ KAM.complexStrip n S ×ˢ P := by
    rintro z ⟨h1, h2⟩
    rw [polyNbhd_singleton] at h2
    exact ⟨fun i => (h1 i).trans_le hs, hb h2⟩
  exact ⟨h.1.mono hsub, fun j z hz => h.2 j z (hsub hz)⟩

theorem FClass.mono_width {S s : ℝ} {P : Set (Fin N → ℂ)} {F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ}
    (h : FClass S P F) (hs : s ≤ S) : FClass s P F := by
  have hsub : KAM.complexStrip n s ×ˢ P ⊆ KAM.complexStrip n S ×ˢ P :=
    prod_mono (fun θ hθ i => (hθ i).trans_le hs) subset_rfl
  exact ⟨h.1.mono hsub, fun j z hz => h.2 j z (hsub hz)⟩

theorem FClass.mono_set {S : ℝ} {P Q : Set (Fin N → ℂ)} {F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ}
    (h : FClass S P F) (hQ : Q ⊆ P) : FClass S Q F :=
  ⟨h.1.mono (prod_mono subset_rfl hQ), fun j z hz => h.2 j z (prod_mono subset_rfl hQ hz)⟩

theorem coeff_differentiableAt_of {S : ℝ} {P : Set (Fin N → ℂ)}
    {F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ} (hS : 0 < S) (hP : IsOpen P) (hF : FClass S P F)
    {J : Fin N → ℂ} (hJ : J ∈ P) (k : Fin n → ℤ) :
    DifferentiableAt ℂ (fun I => coeff F I k) J := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hP J hJ
  have hd := coeff_differentiableOn hS (hF.inClass hball le_rfl) k
  refine hd.differentiableAt ((isOpen_polyNbhd _ _).mem_nhds ?_)
  rw [polyNbhd_singleton]
  exact mem_ball_self hδ

theorem coeff_dI_eq_of {S : ℝ} {P : Set (Fin N → ℂ)}
    {F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ} (hS : 0 < S) (hP : IsOpen P) (hF : FClass S P F)
    {J : Fin N → ℂ} (hJ : J ∈ P) (i : Fin N) (k : Fin n → ℤ) :
    coeff (dI i F) J k = fderiv ℂ (fun I => coeff F I k) J (Pi.single i 1) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hP J hJ
  refine ((coefficients_deriv hS (hF.inClass hball le_rfl)).2 i).2 J ?_ k
  rw [polyNbhd_singleton]
  exact mem_ball_self hδ

/-- Angular Cauchy estimate at a fixed parameter, summed over the angles. -/
theorem wsum_dtheta_le {S₀ s A : ℝ} {P : Set (Fin N → ℂ)} {F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ}
    (hP : IsOpen P) (hF : FClass S₀ P F) (hb : ∀ I ∈ P, WSummable F S₀ I ∧ wsum F S₀ I ≤ A)
    (hs0 : 0 < s) (hs : s < S₀) {x : Fin N → ℂ} (hx : x ∈ P) :
    (∀ j, WSummable (dtheta j F) s x) ∧
      ∑ j, wsum (dtheta j F) s x ≤ A / (Real.exp 1 * (S₀ - s)) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hP x hx
  have hmem : x ∈ polyNbhd ({x} : Set (Fin N → ℂ)) δ := by
    rw [polyNbhd_singleton]; exact mem_ball_self hδ
  have hb' : WBound ({x} : Set (Fin N → ℂ)) δ S₀ F A := fun I hI => by
    rw [polyNbhd_singleton] at hI
    exact hb I (hball hI)
  obtain ⟨hj, hle⟩ := (cauchy_theta (hF.inClass hball le_rfl) hb' hs0 hs).1 x hmem
  refine ⟨hj, hle.trans ?_⟩
  exact div_le_div_of_nonneg_right (hb x hx).2 (by have := Real.exp_pos 1; nlinarith)

/-- Action Cauchy estimate in one coordinate direction `i` with its own loss `R`: a
one-dimensional disc `t ↦ x + t eᵢ` inside `P` suffices. -/
theorem wsum_dI_le {S A R : ℝ} {P : Set (Fin N → ℂ)} {F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ}
    (hP : IsOpen P) (hS : 0 < S) (hF : FClass S P F)
    (hb : ∀ I ∈ P, WSummable F S I ∧ wsum F S I ≤ A) {x : Fin N → ℂ} (hx : x ∈ P) (i : Fin N)
    (hR : 0 < R) (hline : ∀ t : ℂ, ‖t‖ < R → x + t • (Pi.single i 1 : Fin N → ℂ) ∈ P) :
    WSummable (dI i F) S x ∧ wsum (dI i F) S x ≤ A / R := by
  have hnn : ∀ k, 0 ≤ ‖coeff (dI i F) x k‖ * modeWeight S k := fun k =>
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  suffices hpart : ∀ Λ : Finset (Fin n → ℤ),
      ∑ k ∈ Λ, ‖coeff (dI i F) x k‖ * modeWeight S k ≤ A / R from
    ⟨summable_of_sum_le hnn hpart, (summable_of_sum_le hnn hpart).tsum_le_of_sum_le hpart⟩
  intro Λ
  choose g hgn hgv using fun k => exists_dual_vector'' ℂ (coeff (dI i F) x k)
  set e : Fin N → ℂ := Pi.single i 1 with he
  set w : (Fin n → ℤ) → ℝ := fun k => modeWeight S k with hw
  set H : ℂ → ℂ := fun t => ∑ k ∈ Λ, (w k : ℂ) * g k (coeff F (x + t • e) k) with hH
  have hline_d : ∀ t : ℂ, HasDerivAt (fun t : ℂ => x + t • e) e t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const e).const_add x
  have hcd : ∀ t : ℂ, ‖t‖ < R → ∀ k, DifferentiableAt ℂ (fun t : ℂ => coeff F (x + t • e) k) t :=
    fun t ht k =>
      DifferentiableAt.comp (g := fun I => coeff F I k) t
        (coeff_differentiableAt_of hS hP hF (hline t ht) k) (hline_d t).differentiableAt
  have hHdiff : DifferentiableOn ℂ H (ball 0 R) := by
    intro t ht
    rw [mem_ball_zero_iff] at ht
    refine DifferentiableAt.differentiableWithinAt ?_
    exact DifferentiableAt.fun_sum fun k _ =>
      ((g k).differentiableAt.comp t (hcd t ht k)).const_mul _
  have hHbound : ∀ t ∈ ball (0 : ℂ) R, ‖H t‖ ≤ A := by
    intro t ht
    rw [mem_ball_zero_iff] at ht
    obtain ⟨hsm, hle⟩ := hb _ (hline t ht)
    calc ‖H t‖ ≤ ∑ k ∈ Λ, ‖(w k : ℂ) * g k (coeff F (x + t • e) k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Λ, ‖coeff F (x + t • e) k‖ * modeWeight S k := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (show 0 ≤ w k from (Real.exp_pos _).le)]
          have h1 : ‖g k (coeff F (x + t • e) k)‖ ≤ ‖coeff F (x + t • e) k‖ :=
            ((g k).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hgn k))
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right h1 (show 0 ≤ w k from (Real.exp_pos _).le)
      _ ≤ ∑' k, ‖coeff F (x + t • e) k‖ * modeWeight S k :=
          hsm.sum_le_tsum Λ fun k _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ A := hle
  have hcauchy := general_cauchy hR hHdiff hHbound
  have hcoef : ∀ k, coeff (dI i F) x k = fderiv ℂ (fun I => coeff F I k) x e :=
    fun k => coeff_dI_eq_of hS hP hF hx i k
  have hder : HasDerivAt H (((∑ k ∈ Λ, ‖coeff (dI i F) x k‖ * modeWeight S k : ℝ)) : ℂ) 0 := by
    have hk : ∀ k ∈ Λ, HasDerivAt (fun t : ℂ => (w k : ℂ) * g k (coeff F (x + t • e) k))
        ((w k : ℂ) * ‖coeff (dI i F) x k‖) 0 := by
      intro k _
      have h0 : HasFDerivAt (fun I => coeff F I k) (fderiv ℂ (fun I => coeff F I k) x)
          (x + (0 : ℂ) • e) := by
        simpa using (coeff_differentiableAt_of hS hP hF hx k).hasFDerivAt
      have h1 := h0.comp_hasDerivAt (0 : ℂ) (hline_d 0)
      have h2 := ((g k).hasFDerivAt.comp_hasDerivAt (0 : ℂ) h1).const_mul (w k : ℂ)
      rw [← hcoef k, hgv k] at h2
      exact h2
    have := HasDerivAt.fun_sum hk
    convert this using 1
    simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hw, mul_comm]
  have hnorm : ‖deriv H 0‖ ≤ A / R := by
    rw [← fderiv_apply_one_eq_deriv]
    calc ‖fderiv ℂ H 0 1‖ ≤ ‖fderiv ℂ H 0‖ * ‖(1 : ℂ)‖ := (fderiv ℂ H 0).le_opNorm _
      _ ≤ A / R * 1 := by
          rw [norm_one]; exact mul_le_mul_of_nonneg_right hcauchy zero_le_one
      _ = A / R := mul_one _
  have hsum_nn : 0 ≤ ∑ k ∈ Λ, ‖coeff (dI i F) x k‖ * modeWeight S k :=
    Finset.sum_nonneg fun k _ => hnn k
  rw [hder.deriv, Complex.norm_real, Real.norm_of_nonneg hsum_nn] at hnorm
  exact hnorm

end Flat

end KAM.Planetary

end
