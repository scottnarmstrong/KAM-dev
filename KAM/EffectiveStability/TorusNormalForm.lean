/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusNormalForm.Drift
public import KAM.EffectiveStability.Torus

/-!
# Normal form `E0 + ω'·J + R` in the torus chart and B1-T's drift premise (track B, B5-NF)

* `TorusNormalForm.Taylor`: the sharp second-order Taylor bound along a segment.
* `TorusNormalForm.Basic`: the torus data `TorusNFTorus`, the remainder `torusNFRem`, and
  `D(hR ∘ Ψ)(φ, 0)(0, J) = ω'·J` (item 1).
* `TorusNormalForm.Remainder`: `R`, `D_J R`, `D_φ R`, `D_φ D_J R` vanish on the zero section
  and `R` is angle-periodic (item 2).
* `TorusNormalForm.Drift`: `|∂_φ R| ≤ C₃ ‖J‖² / 2` from the third-derivative bound (item 3).
* `torusNormalForm_confinement` (item 4): B1-T `torus_confinement` for the chart
  `Ψ = torusChartMap u v`, `N J = E0 + ω'·J` and `R = torusNFRem`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set

variable {n : ℕ} {u v : (Fin n → ℝ) → (Fin n → ℝ)} {κ : ℝ}

/-- **Item 4.** B1-T `torus_confinement` for the torus chart. Premises: the chart data, `hR` of
class `C²` on `V` and angle-periodic along the chart image, the torus data (invariance and energy,
B5-LAG's outputs), `hR ∘ Ψ` of class `C³` on the cylinder of radius `b + ε` with the third
derivative bounded by `C₃` (operator-norm bound in evaluated form; to be discharged by Cauchy
estimates in B5-ROUTE), and the drift margin `η j ≥ C₃ B² / 2` for `b j ≤ B`.
The conclusion is exactly that of `torus_confinement`. -/
theorem torusNormalForm_confinement (hchart : TorusChartData u v κ)
    (a b η : Fin n → ℝ) (ε T : ℝ) (hε : 0 < ε) (hT : 0 ≤ T)
    (hmargin : ∀ j, a j + T * η j < b j)
    (V : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hV : IsOpen V)
    (hR : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (hRV : ContDiffOn ℝ 2 hR V) (E0 : ℝ) (ω' : Fin n → ℝ)
    (hΨV : ∀ w : (Fin n → ℝ) × (Fin n → ℝ), (∀ j, |w.2 j| < b j + ε) →
      torusChartMap u v w ∈ V)
    (hper : ∀ (k : Fin n → ℤ) (w : (Fin n → ℝ) × (Fin n → ℝ)), (∀ j, |w.2 j| < b j + ε) →
      hR (torusChartMap u v w + KAM.ODE.angleShift k) = hR (torusChartMap u v w))
    (ht : TorusNFTorus u v hR E0 ω')
    (hG : ContDiffOn ℝ 3 (hR ∘ torusChartMap u v) (cyl fun j => b j + ε))
    (C₃ B : ℝ) (hC₃ : 0 ≤ C₃) (hB0 : 0 ≤ B) (hB : ∀ j, b j ≤ B)
    (hD3 : ∀ y ∈ cyl (fun j => b j + ε), ∀ x₁ x₂ x₃ : (Fin n → ℝ) × (Fin n → ℝ),
      |fderiv ℝ (fderiv ℝ (fderiv ℝ (hR ∘ torusChartMap u v))) y x₁ x₂ x₃| ≤
        C₃ * ‖x₁‖ * ‖x₂‖ * ‖x₃‖)
    (hηB : ∀ j, C₃ * B ^ 2 / 2 ≤ η j)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hw₀ : ∀ j, |w₀.2 j| ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = torusChartMap u v w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ V ∧ HasDerivAt z (KAM.hamiltonianVectorField hR (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = torusChartMap u v w₀ →
        (∀ t ∈ I, y t ∈ V ∧ HasDerivAt y (KAM.hamiltonianVectorField hR (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T →
        torusChartMap u v (torusChartInvMap u v (z t)) = z t ∧
        ∀ j, |(torusChartInvMap u v (z t)).2 j - w₀.2 j| ≤ η j * |t| ∧
          |(torusChartInvMap u v (z t)).2 j| ≤ a j + η j * T := by
  have hη : ∀ j, 0 ≤ η j := fun j => le_trans (by positivity) (hηB j)
  have hbpos : ∀ j, 0 < b j := fun j => by
    have h1 : 0 ≤ a j := le_trans (abs_nonneg _) (hw₀ j)
    nlinarith [hmargin j, mul_nonneg hT (hη j)]
  have hc : ∀ j, 0 < b j + ε := fun j => by linarith [hbpos j]
  have hbc : ∀ j, b j < b j + ε := fun j => by linarith
  have hcont : ContDiffOn ℝ 2 (torusChartMap u v) {w | ∀ j, |w.2 j| < b j + ε} :=
    (torusChartMap_contDiff hchart).contDiffOn
  refine torus_confinement a b η ε T hε hT hη hmargin V hV hR hRV (torusChartMap u v)
    (torusChartInvMap u v) hcont hΨV
    (fun w _ x y => torusChartMap_symplectic hchart w x y)
    (fun w _ => torusChartInvMap_map hchart w) (fun J => E0 + ∑ j, ω' j * J j)
    (torusNFRem hR u v E0 ω') ?_ ?_ ?_ ?_ w₀ hw₀
  · rw [torusNFRem_eq]
    exact (hG.differentiableOn (by norm_num)).sub
      ((differentiable_const E0 |>.add (torusNFLin ω').differentiable).differentiableOn)
  · intro k w hw
    exact torusNFRem_shift hchart hper k hw
  · intro w _
    simp only [torusNFRem]; ring
  · intro w hw j
    have hwb : w ∈ cylClosed b := hw
    have h1 := torusNF_drift hchart ht hG hc hD3 hbc hwb j
    have h2 : ‖w.2‖ ≤ B := (pi_norm_le_iff_of_nonneg hB0).2 fun i => by
      rw [Real.norm_eq_abs]; exact le_trans (hw i) (hB i)
    have h3 : ‖w.2‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    refine le_trans h1 (le_trans ?_ (hηB j))
    nlinarith [mul_le_mul_of_nonneg_left h3 hC₃]

end KAM.EffectiveStability

end
