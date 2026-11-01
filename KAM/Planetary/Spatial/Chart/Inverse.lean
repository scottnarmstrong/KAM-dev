/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Bijective
public import KAM.Planetary.Spatial.Chart.Elements
public import KAM.Planetary.Spatial.Chart.Analytic

/-!
# The regular spatial Poincare chart: the explicit inverse (MAIN lines 571–576)

Package LP-SP-CHART, `LP:MAIN L17 (571–578)`, track LP, non-frozen. Item 3.

For a spatial state `z = (q, p)` put `c = q ⨯₃ p`, `G = |c|`, `x = c/G` (the `ŵ` of MAIN),
`cc = √((1 + x₃)/2)`, `u = −√G x₂/cc`, `v = −√G x₁/cc`, `R = incRotation u v G`. Then
`Rᵀ q, Rᵀ p` are the planar vectors to which the planar inverse `poincareInv` is applied.
`spatialPoincareInv` is the resulting explicit inverse; it is a left inverse of
`spatialPoincare` up to the `2π`-lattice shift, and a right inverse on the prograde
negative-energy region.
-/

@[expose] public noncomputable section

open Matrix Real

namespace KAM.Planetary.Spatial

open KAM KAM.Kepler KAM.Planetary

/-- `u = −√G x₂ / √((1 + x₃)/2)` of MAIN line 576 (`x` is `ŵ`, 0-indexed). -/
def spatialRecU (G : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  -Real.sqrt G * x 1 / Real.sqrt ((1 + x 2) / 2)

/-- `v = −√G x₁ / √((1 + x₃)/2)` of MAIN line 576. -/
def spatialRecV (G : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  -Real.sqrt G * x 0 / Real.sqrt ((1 + x 2) / 2)

/-- `G = |q ⨯₃ p|`. -/
def spatialStateG (z : Phase 3) : ℝ := Real.sqrt ((z.1 ⨯₃ z.2) ⬝ᵥ (z.1 ⨯₃ z.2))

/-- `ŵ = (q ⨯₃ p) / G`. -/
def spatialStateDir (z : Phase 3) : Fin 3 → ℝ := (spatialStateG z)⁻¹ • (z.1 ⨯₃ z.2)

/-- The rotation `R` reconstructed from the state. -/
def spatialStateRot (z : Phase 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  incRotation (spatialRecU (spatialStateG z) (spatialStateDir z))
    (spatialRecV (spatialStateG z) (spatialStateDir z)) (spatialStateG z)

/-- The planar state `(Rᵀ q, Rᵀ p)` (first two coordinates). -/
def spatialStatePlanar (z : Phase 3) : Phase 2 :=
  (![((spatialStateRot z)ᵀ *ᵥ z.1) 0, ((spatialStateRot z)ᵀ *ᵥ z.1) 1],
   ![((spatialStateRot z)ᵀ *ᵥ z.2) 0, ((spatialStateRot z)ᵀ *ᵥ z.2) 1])

/-- The explicit inverse of `spatialPoincare ν`. -/
def spatialPoincareInv (ν : ℝ) (z : Phase 3) : Phase 3 :=
  (![(poincareInv ν 1 (spatialStatePlanar z)).1 0, (poincareInv ν 1 (spatialStatePlanar z)).1 1,
      spatialRecV (spatialStateG z) (spatialStateDir z)],
   ![(poincareInv ν 1 (spatialStatePlanar z)).2 0, (poincareInv ν 1 (spatialStatePlanar z)).2 1,
      spatialRecU (spatialStateG z) (spatialStateDir z)])

section Recovery

variable {G : ℝ} {x : Fin 3 → ℝ}

lemma spatialRec_cc_pos (hx2 : 0 < x 2) : 0 < Real.sqrt ((1 + x 2) / 2) :=
  Real.sqrt_pos.2 (by linarith)

/-- `(u² + v²)/2 = G (1 − x₃)`. -/
lemma spatialRec_Z (hG : 0 < G) (hx : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1) (hx2 : 0 < x 2) :
    (spatialRecU G x ^ 2 + spatialRecV G x ^ 2) / 2 = G * (1 - x 2) := by
  have hsG : Real.sqrt G ^ 2 = G := Real.sq_sqrt hG.le
  have hcc : Real.sqrt ((1 + x 2) / 2) ^ 2 = (1 + x 2) / 2 := Real.sq_sqrt (by linarith)
  have hcc0 := spatialRec_cc_pos hx2
  unfold spatialRecU spatialRecV
  simp only [div_pow, mul_pow, neg_sq, hsG, hcc]
  have h1 : (1 + x 2) / 2 ≠ 0 := by positivity
  have h2 : x 0 ^ 2 + x 1 ^ 2 = 1 - x 2 ^ 2 := by linarith
  field_simp
  linear_combination hx

/-- `u, v` carry `(u² + v²)/2 < G`. -/
lemma spatialRec_lt (hG : 0 < G) (hx : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1) (hx2 : 0 < x 2) :
    (spatialRecU G x ^ 2 + spatialRecV G x ^ 2) / 2 < G := by
  rw [spatialRec_Z hG hx hx2]; nlinarith

lemma spatialRec_incCos (hG : 0 < G) (hx : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1) (hx2 : 0 < x 2) :
    incCos (spatialRecU G x) (spatialRecV G x) G = Real.sqrt ((1 + x 2) / 2) := by
  unfold incCos
  rw [incTilt_dot hG, spatialRec_Z hG hx hx2]
  congr 1
  field_simp
  ring

/-- The rotation built from `(u, v) = (spatialRecU, spatialRecV)` sends `e₃` to `x`. -/
lemma spatialRec_rot_e₃ (hG : 0 < G) (hx : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1) (hx2 : 0 < x 2) :
    incRotation (spatialRecU G x) (spatialRecV G x) G *ᵥ e₃ = x := by
  have hs : 0 < Real.sqrt G := Real.sqrt_pos.2 hG
  have hcc0 := spatialRec_cc_pos hx2
  rw [incRotation_mulVec_e₃ hG, spatialRec_incCos hG hx hx2, spatialRec_Z hG hx hx2]
  ext i
  fin_cases i
  · simp [spatialRecV]; field_simp
  · simp [spatialRecU]; field_simp
  · simp; field_simp; ring

end Recovery

section Direction

variable {z : Phase 3}

lemma spatialState_cross_apply_two (z : Phase 3) :
    (z.1 ⨯₃ z.2) ⬝ᵥ e₃ = (z.1 ⨯₃ z.2) 2 := by
  simp [e₃, dotProduct, Fin.sum_univ_three]

lemma spatialState_dot_self (z : Phase 3) :
    (z.1 ⨯₃ z.2) ⬝ᵥ (z.1 ⨯₃ z.2) =
      (z.1 ⨯₃ z.2) 0 ^ 2 + (z.1 ⨯₃ z.2) 1 ^ 2 + (z.1 ⨯₃ z.2) 2 ^ 2 := by
  simp [dotProduct, Fin.sum_univ_three, sq]

lemma spatialStateG_pos (hz : 0 < (z.1 ⨯₃ z.2) ⬝ᵥ e₃) : 0 < spatialStateG z := by
  rw [spatialState_cross_apply_two] at hz
  unfold spatialStateG
  refine Real.sqrt_pos.2 ?_
  rw [spatialState_dot_self]; nlinarith [sq_nonneg ((z.1 ⨯₃ z.2) 0), sq_nonneg ((z.1 ⨯₃ z.2) 1)]

lemma spatialStateG_sq (z : Phase 3) :
    spatialStateG z ^ 2 = (z.1 ⨯₃ z.2) ⬝ᵥ (z.1 ⨯₃ z.2) := by
  unfold spatialStateG
  refine Real.sq_sqrt ?_
  rw [spatialState_dot_self]; positivity

lemma spatialStateDir_apply (z : Phase 3) (i : Fin 3) :
    spatialStateDir z i = (z.1 ⨯₃ z.2) i / spatialStateG z := by
  simp [spatialStateDir, div_eq_inv_mul]

lemma spatialStateDir_sq (hz : 0 < (z.1 ⨯₃ z.2) ⬝ᵥ e₃) :
    spatialStateDir z 0 ^ 2 + spatialStateDir z 1 ^ 2 + spatialStateDir z 2 ^ 2 = 1 := by
  have hG := spatialStateG_pos hz
  have h := spatialStateG_sq z
  rw [spatialState_dot_self] at h
  simp only [spatialStateDir_apply, div_pow]
  field_simp
  linarith

lemma spatialStateDir_two_pos (hz : 0 < (z.1 ⨯₃ z.2) ⬝ᵥ e₃) : 0 < spatialStateDir z 2 := by
  have hG := spatialStateG_pos hz
  rw [spatialState_cross_apply_two] at hz
  rw [spatialStateDir_apply]; positivity

end Direction

section LeftInverse

variable {ν : ℝ} {w : Phase 3}

/-- The data of the state `spatialPoincare ν w` is that of `w`. -/
lemma spatialStateG_chart (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) :
    spatialStateG (spatialPoincare ν w) = spatialAngMom w :=
  spatialPoincare_cross_norm hν hw

lemma spatialStateDir_chart (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) :
    spatialStateDir (spatialPoincare ν w) = spatialRot w *ᵥ e₃ := by
  have hG := (spatial_carrier hw).1
  unfold spatialStateDir
  rw [spatialStateG_chart hν hw, spatialPoincare_cross hν hw, smul_smul,
    inv_mul_cancel₀ hG.ne', one_smul]

lemma spatialStateRot_chart (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) :
    spatialStateRot (spatialPoincare ν w) = spatialRot w := by
  have hc := spatial_carrier hw
  have hu : spatialRecU (spatialStateG (spatialPoincare ν w))
      (spatialStateDir (spatialPoincare ν w)) = w.2 2 := by
    rw [spatialStateG_chart hν hw, spatialStateDir_chart hν hw]
    exact (incRotation_recover_u (u := w.2 2) (v := w.1 2) (G := spatialAngMom w) hc.1 hc.2).symm
  have hv : spatialRecV (spatialStateG (spatialPoincare ν w))
      (spatialStateDir (spatialPoincare ν w)) = w.1 2 := by
    rw [spatialStateG_chart hν hw, spatialStateDir_chart hν hw]
    exact (incRotation_recover_v (u := w.2 2) (v := w.1 2) (G := spatialAngMom w) hc.1 hc.2).symm
  unfold spatialStateRot
  rw [hu, hv, spatialStateG_chart hν hw]
  rfl

lemma spatialStatePlanar_chart (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) :
    spatialStatePlanar (spatialPoincare ν w) = poincare ν 1 (spatialPlanar w) := by
  have hR := spatialRot_transpose_mul hw
  have h1 : (spatialRot w)ᵀ *ᵥ (spatialPoincare ν w).1 =
      planarEmbed (poincare ν 1 (spatialPlanar w)).1 := by
    rw [spatialPoincare_fst, Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
  have h2 : (spatialRot w)ᵀ *ᵥ (spatialPoincare ν w).2 =
      planarEmbed (poincare ν 1 (spatialPlanar w)).2 := by
    rw [spatialPoincare_snd, Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
  unfold spatialStatePlanar
  rw [spatialStateRot_chart hν hw, h1, h2]
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp [planarEmbed]

/-- MAIN lines 571–578: `spatialPoincareInv` is a left inverse modulo the `2π`-lattice. -/
theorem spatialPoincareInv_spatialPoincare (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) :
    ∃ k : ℤ, spatialPoincareInv ν (spatialPoincare ν w) = spatialShift k w := by
  obtain ⟨k, hk⟩ := poincareInv_poincare hν one_pos (spatialPlanar_mem hw)
  refine ⟨k, ?_⟩
  have hu : spatialRecU (spatialStateG (spatialPoincare ν w))
      (spatialStateDir (spatialPoincare ν w)) = w.2 2 := by
    have hc := spatial_carrier hw
    rw [spatialStateG_chart hν hw, spatialStateDir_chart hν hw]
    exact (incRotation_recover_u (u := w.2 2) (v := w.1 2) (G := spatialAngMom w) hc.1 hc.2).symm
  have hv : spatialRecV (spatialStateG (spatialPoincare ν w))
      (spatialStateDir (spatialPoincare ν w)) = w.1 2 := by
    have hc := spatial_carrier hw
    rw [spatialStateG_chart hν hw, spatialStateDir_chart hν hw]
    exact (incRotation_recover_v (u := w.2 2) (v := w.1 2) (G := spatialAngMom w) hc.1 hc.2).symm
  unfold spatialPoincareInv
  rw [hu, hv, spatialStatePlanar_chart hν hw, hk]
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp [spatialShift, spatialPlanar]

end LeftInverse

end KAM.Planetary.Spatial
