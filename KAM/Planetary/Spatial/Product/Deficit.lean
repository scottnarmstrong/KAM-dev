/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Product.Defs
public import KAM.Planetary.Spatial.Chart.Elements
public import KAM.Planetary.Spatial.Elements

/-!
# The n-body spatial product chart: (45) summed and the fixed-plane deficit

Source: `LP:MAIN L17 (533–578)` (last sentence of the statement) and
`LP:MAIN L18 (580–597)` (line 595), track LP, non-frozen. On the product domain:

* `spatialKeplerAction_spatialPoincareProd`: `Λ_i(Ψ w) = I_i`;
* `angularMomentum3_dot_e₃_spatialPoincareProd`: `L · e₃ = Σ_i (I_i − Γ_i − Z_i)`;
* `spatialFixedPlaneDeficit_spatialPoincareProd`: `C_{e₃} = Σ_i I_i − L · e₃ = Σ_i (Γ_i + Z_i)`,
  with `spatialFixedPlaneDeficit_eq_half_slow_sq` the form `½ Σ (x² + y² + u² + v²) = ½ |slow w|²`;
* `spatialStrongAMD_spatialPoincareProd_of_aligned`: if `L = |L| e₃` then
  `C = Σ_i (Γ_i + Z_i)` (MAIN (47), line 595); in general `C ≤ C_{e₃}`.

-/

@[expose] public noncomputable section

open Set Matrix

namespace KAM.Planetary.Spatial

open KAM KAM.Planetary

variable {n : ℕ}

/-- The fixed-plane deficit `C_{e₃} = Σ_i Λ_i − L · e₃` (`LP:MAIN L17`), `L` the total angular
momentum. -/
def spatialFixedPlaneDeficit (ν : Fin n → ℝ) (z : Phase (n * 3)) : ℝ :=
  (∑ i, spatialKeplerAction ν z i) - angularMomentum3 z ⬝ᵥ e₃

/-! ### The bridge from the model to the chart -/

/-- The model's Kepler energy of body `i` is the chart's `spatialEnergy` of its block. -/
theorem spatialKeplerEnergy_eq_spatialEnergy (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) :
    spatialKeplerEnergy ν z i = spatialEnergy (ν i) (bodyVector3 z.1 i, bodyVector3 z.2 i) := by
  unfold spatialKeplerEnergy spatialEnergy spaceLength
  rw [spaceSq_eq_dotProduct, spaceSq_eq_dotProduct]

/-- The model's angular momentum of body `i` is the chart's cross product. -/
theorem planetAngularMomentum3_eq_cross (z : Phase (n * 3)) (i : Fin n) :
    planetAngularMomentum3 z i = bodyVector3 z.1 i ⨯₃ bodyVector3 z.2 i :=
  spaceCross_eq_crossProduct _ _

/-! ### (45) summed -/

/-- MAIN (45), energy, in model terms: `ν_i E_i = −ν_i³/(2 I_i²)`. -/
theorem spatialKeplerEnergy_spatialPoincareProd {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) (i : Fin n) :
    spatialKeplerEnergy ν (spatialPoincareProd ν w) i =
      -ν i ^ 3 / (2 * (spatialBlock w i).2 0 ^ 2) := by
  rw [spatialKeplerEnergy_eq_spatialEnergy, spatialPoincareProd_block]
  exact spatialPoincare_energy (hν i) (hw i)

/-- The first slot of the action block is the fast action `I_i`. -/
theorem spatialBlock_snd_zero (w : Phase (n + (n + n))) (i : Fin n) :
    (spatialBlock w i).2 0 = spatialActions w i := by
  simp [spatialBlock, spatialActions, fast]

/-- Item 3: `Λ_i(Ψ w) = I_i`. -/
theorem spatialKeplerAction_spatialPoincareProd {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) (i : Fin n) :
    spatialKeplerAction ν (spatialPoincareProd ν w) i = spatialActions w i := by
  have hI : 0 < spatialActions w i := by rw [← spatialBlock_snd_zero]; exact (hw i).1
  have hνi := hν i
  have hax : spatialKeplerAxis ν (spatialPoincareProd ν w) i = (spatialActions w i / ν i) ^ 2 := by
    unfold spatialKeplerAxis
    rw [spatialKeplerEnergy_spatialPoincareProd hν hw i, spatialBlock_snd_zero]
    field_simp
  unfold spatialKeplerAction
  rw [hax, Real.sqrt_sq (div_pos hI hνi).le]
  field_simp

/-- Item 3: `(q_i ⨯₃ p_i) · e₃ = I_i − Γ_i − Z_i`, per body in model terms. -/
theorem planetAngularMomentum3_dot_e₃ {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) (i : Fin n) :
    planetAngularMomentum3 (spatialPoincareProd ν w) i ⬝ᵥ e₃ =
      spatialActions w i - spatialGammaBody w i - spatialZBody w i := by
  rw [planetAngularMomentum3_eq_cross]
  have := spatialPoincare_cross_dot_e₃ (hν i) (hw i)
  rw [← spatialPoincareProd_block] at this
  rw [this, spatialBlock_snd_zero]
  rfl

/-- Item 3: `L · e₃ = Σ_i (I_i − Γ_i − Z_i)`. -/
theorem angularMomentum3_dot_e₃_spatialPoincareProd {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) :
    angularMomentum3 (spatialPoincareProd ν w) ⬝ᵥ e₃ =
      ∑ i, (spatialActions w i - spatialGammaBody w i - spatialZBody w i) := by
  rw [angularMomentum3_eq_sum]
  simp only [dotProduct, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := planetAngularMomentum3_dot_e₃ hν hw i
  simpa [dotProduct] using this

/-- Item 3 (MAIN L17, last sentence): `C_{e₃} = Σ_i I_i − L · e₃ = Σ_i (Γ_i + Z_i)`. -/
theorem spatialFixedPlaneDeficit_spatialPoincareProd {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) :
    spatialFixedPlaneDeficit ν (spatialPoincareProd ν w) =
      ∑ i, (spatialGammaBody w i + spatialZBody w i) := by
  unfold spatialFixedPlaneDeficit
  rw [angularMomentum3_dot_e₃_spatialPoincareProd hν hw,
    Finset.sum_congr rfl fun i _ => spatialKeplerAction_spatialPoincareProd hν hw i,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Item 3: the deficit is half the squared slow norm,
`½ Σ_i (x_i² + y_i² + u_i² + v_i²) = ½ (|slow w.1|² + |slow w.2|²)`. -/
theorem sum_gamma_add_z_eq_half_slow_sq (w : Phase (n + (n + n))) :
    ∑ i, (spatialGammaBody w i + spatialZBody w i) =
      ((∑ k, slow w.1 k ^ 2) + ∑ k, slow w.2 k ^ 2) / 2 := by
  have h1 : ∑ k : Fin (n + n), slow w.1 k ^ 2 =
      ∑ i : Fin n, slow w.1 (Fin.castAdd n i) ^ 2 + ∑ i : Fin n, slow w.1 (Fin.natAdd n i) ^ 2 :=
    Fin.sum_univ_add _
  have h2 : ∑ k : Fin (n + n), slow w.2 k ^ 2 =
      ∑ i : Fin n, slow w.2 (Fin.castAdd n i) ^ 2 + ∑ i : Fin n, slow w.2 (Fin.natAdd n i) ^ 2 :=
    Fin.sum_univ_add _
  have e : ∀ i, spatialGammaBody w i + spatialZBody w i =
      (slow w.1 (Fin.castAdd n i) ^ 2 + slow w.2 (Fin.castAdd n i) ^ 2 +
        slow w.2 (Fin.natAdd n i) ^ 2 + slow w.1 (Fin.natAdd n i) ^ 2) / 2 := by
    intro i
    simp [spatialGammaBody, spatialZBody, spatialGamma, spatialZ, spatialBlock]
    ring
  rw [h1, h2, Finset.sum_congr rfl fun i _ => e i, ← Finset.sum_div]
  simp only [Finset.sum_add_distrib]
  ring

/-- The `slow`-norm form of the deficit identity. -/
theorem spatialFixedPlaneDeficit_eq_half_slow_sq {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) :
    spatialFixedPlaneDeficit ν (spatialPoincareProd ν w) =
      ((∑ k, slow w.1 k ^ 2) + ∑ k, slow w.2 k ^ 2) / 2 := by
  rw [spatialFixedPlaneDeficit_spatialPoincareProd hν hw, sum_gamma_add_z_eq_half_slow_sq]

theorem e₃_spaceLength : spaceLength e₃ = 1 := by
  simp [spaceLength, spaceSq_eq_dotProduct, e₃, dotProduct, Fin.sum_univ_three]

/-- `L · e₃ ≤ |L|`, so the strong AMD is at most the fixed-plane deficit. -/
theorem spatialStrongAMD_le_spatialFixedPlaneDeficit (ν : Fin n → ℝ) (z : Phase (n * 3)) :
    spatialStrongAMD ν z ≤ spatialFixedPlaneDeficit ν z := by
  unfold spatialStrongAMD spatialFixedPlaneDeficit
  have h := (abs_le.mp (abs_spaceDot_le (angularMomentum3 z) e₃)).2
  rw [e₃_spaceLength, mul_one, spaceDot_eq_dotProduct] at h
  linarith

/-- MAIN (47) and L18 line 595: when `L = |L| e₃` (aligned), the strong AMD is the deficit
`Σ_i (Γ_i + Z_i)`. -/
theorem spatialStrongAMD_spatialPoincareProd_of_aligned {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n)
    (hL : angularMomentum3 (spatialPoincareProd ν w) =
      spaceLength (angularMomentum3 (spatialPoincareProd ν w)) • e₃) :
    spatialStrongAMD ν (spatialPoincareProd ν w) =
      ∑ i, (spatialGammaBody w i + spatialZBody w i) := by
  rw [← spatialFixedPlaneDeficit_spatialPoincareProd hν hw]
  unfold spatialStrongAMD spatialFixedPlaneDeficit
  have : angularMomentum3 (spatialPoincareProd ν w) ⬝ᵥ e₃ =
      spaceLength (angularMomentum3 (spatialPoincareProd ν w)) := by
    conv_lhs => rw [hL]
    rw [smul_dotProduct]
    simp [e₃, dotProduct, Fin.sum_univ_three]
  rw [this]

end KAM.Planetary.Spatial

end
