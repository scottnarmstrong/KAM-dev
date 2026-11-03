/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusRoute.Matrix
public import KAM.EffectiveStability.TorusRealSlice
public import KAM.EffectiveStability.TorusChart
public import KAM.Strip.AnalyticTaylor

/-!
# The complexified torus chart (track B, package B5-ROUTE, item 3)

For a holomorphic `K = (K^θ, K^I)` on a strip, write `A(θ) = DK^θ(θ)` (`torusCxJac`) and
`Ψ_ℂ(θ, J) = (K^θ θ, K^I θ + (A(θ)ᵀ)⁻¹ J)` (`torusCxChart`).

* `torusCxChart_differentiableOn`: `Ψ_ℂ` is holomorphic on `{θ ∈ T_{δφ}}` when the entries of
  `A - 1` are bounded by `κ` with `n κ < 1`.
* `norm_torusCxChart_sub_le`: `‖Ψ_ℂ(θ, J) - K θ‖ ≤ ‖J‖ / (1 - n κ)`.
* `torusCxChart_realInclusion`: for `K` real on reals, `Ψ_ℂ ∘ ι₂ = ι₂ ∘ Ψ` for the real chart
  `Ψ = torusChartMap (torusRealU K) (torusRealV K)`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open KAM Matrix

variable {n : ℕ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ρ δφ κ : ℝ}

/-- The matrix `A(θ)_{ij} = (DK^θ(θ) e_j)_i`. -/
def torusCxJac (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => fderiv ℂ (fun θ => (K θ).1) θ (Pi.single j 1) i

/-- The complexified chart `Ψ_ℂ(θ, J) = (K^θ θ, K^I θ + (A(θ)ᵀ)⁻¹ J)`. -/
def torusCxChart (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (w : (Fin n → ℂ) × (Fin n → ℂ)) : (Fin n → ℂ) × (Fin n → ℂ) :=
  ((K w.1).1, (K w.1).2 + (torusCxJac K w.1)ᵀ⁻¹ *ᵥ w.2)

theorem torusCxJac_differentiableOn (hK : DifferentiableOn ℂ K (complexStrip n ρ)) (i j : Fin n) :
    DifferentiableOn ℂ (fun θ => torusCxJac K θ i j) (complexStrip n ρ) := by
  have hU := isOpen_complexStrip n ρ
  have h1 : DifferentiableOn ℂ (fun θ => (K θ).1) (complexStrip n ρ) := hK.fst
  have h2 : DifferentiableOn ℂ (fderiv ℂ fun θ => (K θ).1) (complexStrip n ρ) :=
    ((KAM.analyticOnNhd_of_differentiableOn hU h1).fderiv_of_isOpen hU).differentiableOn
  have h3 : DifferentiableOn ℂ (fun θ => fderiv ℂ (fun θ => (K θ).1) θ (Pi.single j 1))
      (complexStrip n ρ) := h2.clm_apply (differentiableOn_const _)
  exact (differentiableOn_pi.mp h3) i

/-- Entries of `A - 1` are bounded by `κ` once `‖D(K^θ - id)‖ ≤ κ`. -/
theorem torusCxJac_sub_one_le {θ : Fin n → ℂ} (hK1 : DifferentiableAt ℂ (fun θ => (K θ).1) θ)
    (hκ : ‖fderiv ℂ (fun θ => (K θ).1 - θ) θ‖ ≤ κ) (i j : Fin n) :
    ‖torusCxJac K θ i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ κ := by
  have hd : fderiv ℂ (fun θ => (K θ).1 - θ) θ (Pi.single j 1) =
      fderiv ℂ (fun θ => (K θ).1) θ (Pi.single j 1) - Pi.single j 1 := by
    have := fderiv_fun_sub (𝕜 := ℂ) hK1 (differentiableAt_id (𝕜 := ℂ) (x := θ))
    rw [show (fun θ => (K θ).1 - θ) = fun y => (K y).1 - id y from rfl, this]
    simp
  have hs : ‖(Pi.single j (1 : ℂ) : Fin n → ℂ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
    by_cases h : k = j <;> simp [h]
  have h1 : ‖fderiv ℂ (fun θ => (K θ).1 - θ) θ (Pi.single j 1)‖ ≤ κ :=
    ((fderiv ℂ (fun θ => (K θ).1 - θ) θ).le_opNorm _).trans
      (by nlinarith [norm_nonneg (fderiv ℂ (fun θ => (K θ).1 - θ) θ)])
  have h2 := (norm_le_pi_norm (fderiv ℂ (fun θ => (K θ).1 - θ) θ (Pi.single j 1)) i).trans h1
  rw [hd] at h2
  simpa [torusCxJac, Matrix.one_apply, Pi.single_apply] using h2

variable (hκ0 : 0 ≤ κ) (hn : (n : ℝ) * κ < 1)

include hκ0 hn in
theorem torusCxChart_differentiableOn (hρ : δφ ≤ ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hA : ∀ θ ∈ complexStrip n δφ, ∀ i j,
      ‖torusCxJac K θ i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ κ) :
    DifferentiableOn ℂ (torusCxChart K) {w | w.1 ∈ complexStrip n δφ} := by
  have hsub : complexStrip n δφ ⊆ complexStrip n ρ := fun θ hθ i => (hθ i).trans_le hρ
  have hmaps : Set.MapsTo Prod.fst {w : (Fin n → ℂ) × (Fin n → ℂ) | w.1 ∈ complexStrip n δφ}
      (complexStrip n δφ) := fun w hw => hw
  have hinv : ∀ i j, DifferentiableOn ℂ (fun θ => (torusCxJac K θ)ᵀ⁻¹ i j) (complexStrip n δφ) :=
    fun i j => differentiableOn_matrix_inv_entry (f := fun θ => (torusCxJac K θ)ᵀ)
      (fun a b => (torusCxJac_differentiableOn hK b a).mono hsub)
      (fun θ hθ => transpose_det_ne_of_entry_bound hκ0 hn (hA θ hθ)) i j
  refine DifferentiableOn.prodMk ?_ ?_
  · exact (hK.fst.comp differentiableOn_fst (fun w hw => hsub (hmaps hw)))
  · refine differentiableOn_pi.2 fun i => ?_
    have h1 : DifferentiableOn ℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => (K w.1).2 i)
        {w | w.1 ∈ complexStrip n δφ} :=
      (differentiableOn_pi.mp (hK.snd.comp differentiableOn_fst (fun w hw => hsub (hmaps hw)))) i
    have h2 : DifferentiableOn ℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) =>
        ((torusCxJac K w.1)ᵀ⁻¹ *ᵥ w.2) i) {w | w.1 ∈ complexStrip n δφ} := by
      simp only [Matrix.mulVec, dotProduct]
      refine DifferentiableOn.fun_sum fun k _ => ?_
      refine DifferentiableOn.mul ?_ ?_
      · exact (hinv i k).comp differentiableOn_fst hmaps
      · exact (differentiableOn_pi.mp differentiableOn_snd) k
    exact h1.add h2

include hκ0 hn in
theorem norm_torusCxChart_sub_le {θ : Fin n → ℂ}
    (hA : ∀ i j, ‖torusCxJac K θ i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ κ) (J : Fin n → ℂ) :
    ‖(torusCxChart K (θ, J)).2 - (K θ).2‖ ≤ ‖J‖ / (1 - n * κ) := by
  simp only [torusCxChart, add_sub_cancel_left]
  exact norm_transpose_inv_mulVec_le hκ0 hn hA J

end KAM.EffectiveStability

end
