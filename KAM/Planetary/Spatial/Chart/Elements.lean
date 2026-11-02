/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Symplectic
public import KAM.Planetary.Spatial.Chart.Defs

/-!
# The regular spatial Poincare chart: the elements (45)

Source: `LP:MAIN L17 (533–578)`, track LP, non-frozen. On (44):

* the Kepler energy of `spatialPoincare ν w` is `−ν³/(2I²)`;
* `q ⨯₃ p = G • (R e₃)`, `|q ⨯₃ p| = G` and `(q ⨯₃ p) ⬝ᵥ e₃ = I − Γ − Z`;
* the eccentricity vector is `R` applied to the planar one.

-/

@[expose] public noncomputable section

open Matrix

namespace KAM.Planetary.Spatial

open KAM KAM.Kepler KAM.Planetary

/-- Orthogonal matrices preserve the dot product. -/
theorem dotProduct_mulVec_mulVec_of_orth {M : Matrix (Fin 3) (Fin 3) ℝ} (h : Mᵀ * M = 1)
    (x y : Fin 3 → ℝ) : (M *ᵥ x) ⬝ᵥ (M *ᵥ y) = x ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h,
    Matrix.one_mulVec]

lemma planarEmbed_dot (Q P : Fin 2 → ℝ) : planarEmbed Q ⬝ᵥ planarEmbed P = planeDot Q P := by
  simp [planarEmbed, planeDot, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]

lemma planarEmbed_smul (a : ℝ) (Q : Fin 2 → ℝ) : planarEmbed (a • Q) = a • planarEmbed Q := by
  ext i; fin_cases i <;> simp [planarEmbed]

lemma planarEmbed_sub (Q P : Fin 2 → ℝ) : planarEmbed (Q - P) = planarEmbed Q - planarEmbed P := by
  ext i; fin_cases i <;> simp [planarEmbed]

lemma planarEmbed_dot_self (Q : Fin 2 → ℝ) : planarEmbed Q ⬝ᵥ planarEmbed Q = planeSq Q := by
  simp [planarEmbed, planeSq, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, sq]

section Elements

variable {ν : ℝ} {w : Phase 3}

lemma spatialRot_transpose_mul (hw : w ∈ spatialPoincareDom) :
    (spatialRot w)ᵀ * spatialRot w = 1 :=
  incRotation_transpose_mul (spatial_carrier hw).1 (spatial_carrier hw).2

lemma spatialPlanar_snd_zero (w : Phase 3) : (spatialPlanar w).2 0 = w.2 0 := by
  simp [spatialPlanar]

/-- The rotated state: a convenient name for the pair of spatial vectors of the chart. -/
lemma spatialPoincare_fst (ν : ℝ) (w : Phase 3) :
    (spatialPoincare ν w).1 = spatialRot w *ᵥ planarEmbed (poincare ν 1 (spatialPlanar w)).1 := rfl

lemma spatialPoincare_snd (ν : ℝ) (w : Phase 3) :
    (spatialPoincare ν w).2 = spatialRot w *ᵥ planarEmbed (poincare ν 1 (spatialPlanar w)).2 := rfl

/-- `spatialEnergy` of a rotated embedded planar state is the planar energy. -/
theorem spatialEnergy_rot {M : Matrix (Fin 3) (Fin 3) ℝ} (h : Mᵀ * M = 1) (ν : ℝ)
    (z : Phase 2) :
    spatialEnergy ν (M *ᵥ planarEmbed z.1, M *ᵥ planarEmbed z.2) = energyMK ν 1 z := by
  unfold spatialEnergy energyMK planeLength
  simp only [dotProduct_mulVec_mulVec_of_orth h, planarEmbed_dot_self, one_mul]

/-- MAIN (45), energy: `−ν³/(2I²)`. -/
theorem spatialPoincare_energy (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) :
    spatialEnergy ν (spatialPoincare ν w) = -ν ^ 3 / (2 * w.2 0 ^ 2) := by
  have hp := spatialPlanar_mem hw
  have h := (poincare_elements hν one_pos hp).2.1
  rw [spatialPlanar_snd_zero] at h
  unfold spatialPoincare
  rw [spatialEnergy_rot (spatialRot_transpose_mul hw), h]
  ring

/-- The planar angular momentum of the planar chart point is `G = I − Γ`. -/
lemma spatialPlanar_cross (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) :
    (poincare ν 1 (spatialPlanar w)).1 0 * (poincare ν 1 (spatialPlanar w)).2 1 -
      (poincare ν 1 (spatialPlanar w)).1 1 * (poincare ν 1 (spatialPlanar w)).2 0 =
      spatialAngMom w := by
  have h := (poincare_elements hν one_pos (spatialPlanar_mem hw)).2.2.2.2.1
  rw [spatialPlanar_snd_zero, spatialPlanar_gamma] at h
  exact h

/-- Item 2: `q ⨯₃ p = G • (R e₃)`. -/
theorem spatialPoincare_cross (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) :
    (spatialPoincare ν w).1 ⨯₃ (spatialPoincare ν w).2 =
      spatialAngMom w • (spatialRot w *ᵥ e₃) := by
  have hQP : planarEmbed (poincare ν 1 (spatialPlanar w)).1 ⨯₃
      planarEmbed (poincare ν 1 (spatialPlanar w)).2 = spatialAngMom w • e₃ := by
    rw [planarEmbed_cross, spatialPlanar_cross hν hw]
  exact incRotation_cross_eq_smul (spatial_carrier hw).1 (spatial_carrier hw).2 hQP

/-- Item 2 (MAIN (45)): `(q ⨯₃ p) ⬝ᵥ e₃ = I − Γ − Z`. -/
theorem spatialPoincare_cross_dot_e₃ (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) :
    ((spatialPoincare ν w).1 ⨯₃ (spatialPoincare ν w).2) ⬝ᵥ e₃ =
      w.2 0 - spatialGamma w - spatialZ w := by
  have hQP : planarEmbed (poincare ν 1 (spatialPlanar w)).1 ⨯₃
      planarEmbed (poincare ν 1 (spatialPlanar w)).2 = spatialAngMom w • e₃ := by
    rw [planarEmbed_cross, spatialPlanar_cross hν hw]
  have h := incRotation_cross_dot_e₃ (spatial_carrier hw).1 (spatial_carrier hw).2 hQP
  show ((spatialRot w *ᵥ _) ⨯₃ (spatialRot w *ᵥ _)) ⬝ᵥ e₃ = _
  rw [spatialRot, h]
  unfold spatialAngMom spatialZ
  ring

lemma e₃_dot_self : e₃ ⬝ᵥ e₃ = 1 := by simp [e₃, dotProduct, Fin.sum_univ_three]

/-- Item 2 (MAIN (45)): `(q ⨯₃ p) ⬝ᵥ (q ⨯₃ p) = G²`. -/
theorem spatialPoincare_cross_dot_self (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) :
    ((spatialPoincare ν w).1 ⨯₃ (spatialPoincare ν w).2) ⬝ᵥ
      ((spatialPoincare ν w).1 ⨯₃ (spatialPoincare ν w).2) = spatialAngMom w ^ 2 := by
  rw [spatialPoincare_cross hν hw, smul_dotProduct, dotProduct_smul,
    dotProduct_mulVec_mulVec_of_orth (spatialRot_transpose_mul hw), e₃_dot_self]
  simp [sq]

/-- Item 2 (MAIN (45)): `|q ⨯₃ p| = G`. -/
theorem spatialPoincare_cross_norm (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) :
    Real.sqrt (((spatialPoincare ν w).1 ⨯₃ (spatialPoincare ν w).2) ⬝ᵥ
      ((spatialPoincare ν w).1 ⨯₃ (spatialPoincare ν w).2)) = spatialAngMom w := by
  rw [spatialPoincare_cross_dot_self hν hw]
  exact Real.sqrt_sq (spatialAngMom_pos hw).le

end Elements

end KAM.Planetary.Spatial
