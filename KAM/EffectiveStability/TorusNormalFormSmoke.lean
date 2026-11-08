/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusNormalForm

/-!
# Smoke test for the torus normal form (track B, B5-NF, item 5)

`u = v = 0` and the integrable linear Hamiltonian `hR (φ, J) = E0 + ω'·J`, with `C₃ = 0`: the
torus data hold, the remainder vanishes, and `torusNormalForm_confinement` applies with `η = 0`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set

variable {n : ℕ}

/-- The integrable linear Hamiltonian `E0 + ω'·J`. -/
def torusNFLinearHam (E0 : ℝ) (ω' : Fin n → ℝ) (w : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  E0 + torusNFLin ω' w

theorem torusNFLinearHam_fderiv (E0 : ℝ) (ω' : Fin n → ℝ) (w : (Fin n → ℝ) × (Fin n → ℝ)) :
    fderiv ℝ (torusNFLinearHam E0 ω') w = torusNFLin ω' :=
  ((torusNFLin ω').hasFDerivAt.const_add E0).fderiv

theorem torusNF_smoke_torus (E0 : ℝ) (ω' : Fin n → ℝ) :
    TorusNFTorus (fun _ => 0) (fun _ => (0 : Fin n → ℝ)) (torusNFLinearHam E0 ω') E0 ω' where
  hRdiff _ := (((torusNFLin ω').differentiable).const_add E0) _
  invariance φ := by
    have hg : torusNFGraph (fun _ => (0 : Fin n → ℝ)) (fun _ => (0 : Fin n → ℝ)) =
        fun φ => (φ, 0) := funext fun φ => by simp [torusNFGraph, torusChartX]
    rw [hg]
    have : HasFDerivAt (fun φ : Fin n → ℝ => (φ, (0 : Fin n → ℝ)))
        (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)) φ :=
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)).hasFDerivAt
    rw [this.fderiv]
    refine Prod.ext ?_ ?_ <;> funext i <;>
      simp [KAM.hamiltonianVectorField, torusNFLinearHam_fderiv, torusNFLin_apply,
        Pi.single_apply]
  energy φ := by
    simp [torusNFGraph, torusNFLinearHam, torusNFLin_apply, torusChartX]

theorem torusNF_smoke_rem (E0 : ℝ) (ω' : Fin n → ℝ) :
    torusNFRem (torusNFLinearHam E0 ω') (fun _ => (0 : Fin n → ℝ)) (fun _ => (0 : Fin n → ℝ))
      E0 ω' = 0 := by
  funext w
  simp [torusNFRem, torusChartMap_zero_data, torusNFLinearHam, torusNFLin_apply]

/-- Smoke test: the normal-form confinement for the integrable linear Hamiltonian, `C₃ = 0`,
`η = 0`; the chart is the identity, so the solution keeps its actions. -/
theorem torusNF_smoke_confinement (E0 : ℝ) (ω' : Fin n → ℝ) (a b : Fin n → ℝ) (ε T : ℝ)
    (hε : 0 < ε) (hT : 0 ≤ T) (hmargin : ∀ j, a j < b j)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hw₀ : ∀ j, |w₀.2 j| ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = w₀ ∧
      ∀ t : ℝ, |t| ≤ T → ∀ j, |(z t).2 j - w₀.2 j| ≤ 0 * |t| := by
  have hid : torusChartMap (fun _ => (0 : Fin n → ℝ)) (fun _ => (0 : Fin n → ℝ)) = id :=
    funext torusChartMap_zero_data
  have hidi : torusChartInvMap (fun _ => (0 : Fin n → ℝ)) (fun _ => (0 : Fin n → ℝ)) = id := by
    funext q
    have := torusChartInvMap_map (torusChartData_zero (n := n)) q
    simpa [torusChartMap_zero_data] using this
  have hsm : ContDiff ℝ 3 (torusNFLinearHam E0 ω') :=
    contDiff_const.add (torusNFLin ω').contDiff
  have h1 : fderiv ℝ (torusNFLinearHam E0 ω') = fun _ => torusNFLin ω' :=
    funext (torusNFLinearHam_fderiv E0 ω')
  have h2 : fderiv ℝ (fderiv ℝ (torusNFLinearHam E0 ω')) = fun _ => 0 := by
    rw [h1]; funext y; simp
  have h3 : fderiv ℝ (fderiv ℝ (fderiv ℝ (torusNFLinearHam E0 ω'))) = fun _ => 0 := by
    rw [h2]; funext y; simp
  obtain ⟨T₁, hT₁, z, hz0, -, -, hbd⟩ := torusNormalForm_confinement
    (torusChartData_zero (n := n)) a b (fun _ => 0) ε T hε hT (fun j => by simpa using hmargin j)
    univ isOpen_univ (torusNFLinearHam E0 ω') (hsm.of_le (by norm_num)).contDiffOn E0 ω'
    (fun _ _ => mem_univ _)
    (fun k w _ => by
      simp [hid, torusNFLinearHam, torusNFLin_apply, KAM.ODE.angleShift])
    (torusNF_smoke_torus E0 ω')
    (by rw [hid, Function.comp_id]; exact hsm.contDiffOn)
    0 ‖b‖ le_rfl (norm_nonneg _)
    (fun j => le_trans (le_abs_self _) (by simpa using norm_le_pi_norm b j))
    (fun y _ x₁ x₂ x₃ => by simp [hid, h3])
    (fun j => by simp) w₀ hw₀
  refine ⟨T₁, hT₁, z, by simpa [hid] using hz0, fun t ht j => ?_⟩
  have := ((hbd t ht).2 j).1
  simpa [hidi] using this

end KAM.EffectiveStability

end
