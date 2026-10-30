/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.SmallDiv.Bound
public import KAM.Strip.CohomologicalSum
import Mathlib.Tactic.Positivity

/-!
# `SDConst` from a bound on the small-divisor sum

`sdConst_of_sdSum` (blueprint `bp:p2s2sd:cs`): if every `ω ∈ Ω` is `(γ, τ)`-Diophantine and
`(2π)⁻¹ 2^{n/2} S(ω, δ)^{1/2} ≤ c γ⁻¹ δ^{-κ}`, then `c` is a small-divisor constant at the bite
`δ` on `Ω`. The solution clause is `norm_cohSolution_sdSum_le` componentwise; the a-priori clause
goes through the uniqueness theorems of `KAM.Strip.Cohomological` exactly as
`KAM.cohomological_apriori_operator_sum`; the real clause uses the closed strip.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.Sharp2

open KAM KAM.Torus KAM.Apost

variable {n : ℕ}

section Pieces

variable {ω : Fin n → ℝ} {γ τ r δ : ℝ} (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ)
  (hδ : 0 < δ) (hδr : δ ≤ r)
include hω hγ hτ hδ hδr

/-- The vector solution bound at a closed-strip point. -/
theorem norm_cohR_sdSum_le {p : ℕ} {g : (Fin n → ℂ) → Fin p → ℂ} {A : ℝ}
    (hg : DifferentiableOn ℂ g (complexStrip n r)) (hp : IsPeriodicOn g r)
    (hA : ∀ θ ∈ complexStrip n r, ‖g θ‖ ≤ A) (h0 : avg g = 0)
    {θ : Fin n → ℂ} (hθ : ∀ j, |(θ j).im| ≤ r - δ) :
    ‖cohR ω g θ‖ ≤ (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n) * Real.sqrt (sdSum ω δ) * A := by
  have hr : 0 < r := hδ.trans_le hδr
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ (ofReal_mem_complexStrip hr 0))
  have hS0 : 0 ≤ sdSum ω δ := by
    rw [sdSum_eq_smallDivisorSum]; exact smallDivisorSum_nonneg _ _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun l => ?_
  obtain ⟨hgl, hpl, h0l⟩ := component_holomorphic_periodic hr hg hp h0 l
  exact norm_cohSolution_sdSum_le hω hγ hτ hδ hδr hgl hpl
    (fun z hz => (norm_le_pi_norm (g z) l).trans (hA z hz)) hθ

end Pieces

section Apriori

variable {ω : Fin n → ℝ} {γ τ ρ δ : ℝ} (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ)
  (hδ : 0 < δ) (hδρ : δ < ρ)
include hω hγ hτ hδ hδρ

theorem apriori_sdSum_scalar {u : (Fin n → ℂ) → ℂ} {H : ℝ}
    (hu : DifferentiableOn ℂ u (complexStrip n ρ))
    (hup : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z)
    (hu0 : torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0)
    (hH : ∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ u θ (fun l => (ω l : ℂ))‖ ≤ H) :
    ∀ θ ∈ complexStrip n (ρ - δ),
      ‖u θ‖ ≤ (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n) * Real.sqrt (sdSum ω δ) * H := by
  have hρ : 0 < ρ := hδ.trans hδρ
  have hmono : complexStrip n (ρ - δ) ⊆ complexStrip n ρ := fun z hz j => by
    have := hz j
    linarith
  set g : (Fin n → ℂ) → ℂ := fun θ => fderiv ℂ u θ (fun l => (ω l : ℂ)) with hg_def
  have hg : DifferentiableOn ℂ g (complexStrip n ρ) :=
    (differentiableOn_fderiv_of_isOpen_pi (isOpen_complexStrip n ρ) hu).clm_apply
      (differentiableOn_const _)
  have hgp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z := fun i z hz => by
    simp only [hg_def, fderiv_add_single_of_periodic hup i hz]
  have hg0 : torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0 :=
    torusAverage_complex_direction_eq_zero hρ hu hup _
  intro θ hθ
  rw [eq_cohSolution hω hγ hτ hδ hδρ hg hgp hH hg0 (hu.mono hmono)
    (fun i z hz => hup i z (hmono hz)) hu0 (fun θ _ => rfl) hθ]
  exact norm_cohSolution_sdSum_le hω hγ hτ hδ hδρ.le hg hgp hH (fun j => (hθ j).le)

theorem apriori_sdSum_pi {p : ℕ} {u : (Fin n → ℂ) → Fin p → ℂ} {H : ℝ}
    (hu : DifferentiableOn ℂ u (complexStrip n ρ))
    (hup : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z)
    (hu0 : torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0)
    (hH : ∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ u θ (fun l => (ω l : ℂ))‖ ≤ H) :
    ∀ θ ∈ complexStrip n (ρ - δ),
      ‖u θ‖ ≤ (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n) * Real.sqrt (sdSum ω δ) * H := by
  intro θ hθ
  have hρ : 0 < ρ := hδ.trans hδρ
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH _ (ofReal_mem_complexStrip hρ 0))
  have hS0 : 0 ≤ sdSum ω δ := by
    rw [sdSum_eq_smallDivisorSum]; exact smallDivisorSum_nonneg _ _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun l => ?_
  obtain ⟨hul, hupl, hu0l⟩ := component_holomorphic_periodic hρ hu hup hu0 l
  refine apriori_sdSum_scalar hω hγ hτ hδ hδρ (u := fun z => u z l) hul hupl hu0l ?_ θ hθ
  intro θ' hθ'
  rw [← fderiv_apply_of_differentiableAt
    (hu.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθ'))]
  exact (norm_le_pi_norm _ l).trans (hH θ' hθ')

theorem apriori_sdSum_mat {p q : ℕ} {u : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ} {H : ℝ}
    (hu : DifferentiableOn ℂ u (complexStrip n ρ))
    (hup : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z)
    (hu0 : torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0)
    (hH : ∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ u θ (fun l => (ω l : ℂ))‖ ≤ H) :
    ∀ θ ∈ complexStrip n (ρ - δ),
      ‖u θ‖ ≤ (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n) * Real.sqrt (sdSum ω δ) * H := by
  intro θ hθ
  have hρ : 0 < ρ := hδ.trans hδρ
  obtain ⟨v, hv, hMv⟩ := (isGreatest_norm_mulVec (u θ)).1
  have hv1 : ‖v‖ ≤ 1 := by simpa using hv
  have hMv' : ‖(u θ).mulVec v‖ = ‖u θ‖ := hMv
  rw [← hMv']
  obtain ⟨hw, hwavg, hwd⟩ := mulVec_transfer hρ hu v ω
  refine apriori_sdSum_pi hω hγ hτ hδ hδρ (u := fun θ => (u θ).mulVec v) hw
    (fun i z hz => by simp only [hup i z hz]) ?_ ?_ θ hθ
  · rw [hwavg, hu0, Matrix.zero_mulVec]
  · intro θ' hθ'
    rw [hwd θ' hθ']
    exact (Matrix.linfty_opNorm_mulVec _ v).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hv1).trans (hH θ' hθ'))

end Apriori

/-- **`SDConst` from a bound on `S(ω, δ)`** (blueprint `bp:p2s2sd:cs`). -/
theorem sdConst_of_sdSum {κ γ δ c τ : ℝ} {Ω : Set (Fin n → ℝ)} (hc : 0 < c) (hδ : 0 < δ)
    (hγ : 0 < γ) (hτ : 0 ≤ τ) (hD : ∀ ω ∈ Ω, IsDiophantine γ τ ω)
    (hS : ∀ ω ∈ Ω, (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n) * Real.sqrt (sdSum ω δ) ≤
      c * γ⁻¹ * δ ^ (-κ)) : SDConst n κ γ δ c Ω where
  c_pos := hc
  delta_pos := hδ
  sol := by
    intro ω hω r hδr p g H hg hp hH h0 θ hθ
    have hr : 0 < r := hδ.trans hδr
    have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH _ (ofReal_mem_complexStrip hr 0))
    refine (norm_cohR_sdSum_le (hD ω hω) hγ hτ hδ hδr.le hg hp hH h0
      (fun j => (hθ j).le)).trans ?_
    calc _ ≤ c * γ⁻¹ * δ ^ (-κ) * H := mul_le_mul_of_nonneg_right (hS ω hω) hH0
      _ = _ := rfl
  apriori := by
    intro ω hω r hδr p q u H hu hp h0 hH θ hθ
    refine (apriori_sdSum_mat (hD ω hω) hγ hτ hδ hδr hu hp h0 hH θ hθ).trans ?_
    have hr : 0 < r := hδ.trans hδr
    have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH _ (ofReal_mem_complexStrip hr 0))
    exact mul_le_mul_of_nonneg_right (hS ω hω) hH0
  real := by
    intro ω hω r hδr p g H hg hp hH h0 θ
    have hr : 0 < r := hδ.trans_le hδr
    have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH _ (ofReal_mem_complexStrip hr 0))
    refine (norm_cohR_sdSum_le (hD ω hω) hγ hτ hδ hδr hg hp hH h0 (θ := fun i => (θ i : ℂ))
      (fun j => by simp; linarith)).trans ?_
    exact mul_le_mul_of_nonneg_right (hS ω hω) hH0

end KAM.Sharp2

end
