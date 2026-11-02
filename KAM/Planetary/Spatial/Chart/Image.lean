/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Chart.Inverse

/-!
# The image of the regular spatial Poincare chart, and injectivity modulo `2π`

Source: `LP:MAIN L17 (571–578)`, track LP, non-frozen. Item 3: `spatialPoincare ν`
maps (44) into the prograde negative-energy region `spatialRegion ν`, `spatialPoincareInv` is a
right inverse on that region (so the map is onto), and two points of (44) have the same image iff
they differ by a shift `λ ↦ λ + 2πk`.

-/

@[expose] public noncomputable section

open Matrix Real

namespace KAM.Planetary.Spatial

open KAM KAM.Kepler KAM.Planetary

variable {ν : ℝ}

/-- The energy of a rotated state is the energy of the state. -/
lemma spatialEnergy_mulVec {M : Matrix (Fin 3) (Fin 3) ℝ} (h : Mᵀ * M = 1) (ν : ℝ)
    (a b : Fin 3 → ℝ) : spatialEnergy ν (M *ᵥ a, M *ᵥ b) = spatialEnergy ν (a, b) := by
  unfold spatialEnergy
  simp only [dotProduct_mulVec_mulVec_of_orth h]

/-- Item 3: the chart maps (44) into the prograde negative-energy region. -/
theorem spatialPoincare_mem_region (hν : 0 < ν) {w : Phase 3} (hw : w ∈ spatialPoincareDom) :
    spatialPoincare ν w ∈ spatialRegion ν := by
  refine ⟨?_, ?_⟩
  · rw [spatialPoincare_energy hν hw]
    have := hw.1
    have h3 : 0 < ν ^ 3 := by positivity
    have : 0 < 2 * w.2 0 ^ 2 := by positivity
    rw [neg_div]; exact neg_neg_of_pos (div_pos h3 this)
  · rw [spatialPoincare_cross_dot_e₃ hν hw]
    have := hw.2
    linarith

lemma dotProduct_e₃_eq (x : Fin 3 → ℝ) : x ⬝ᵥ e₃ = x 2 := by
  simp [e₃, dotProduct, Fin.sum_univ_three]

lemma spatial_planeSq_nonneg (v : Fin 2 → ℝ) : 0 ≤ planeSq v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma spatial_planeLength_nonneg (v : Fin 2 → ℝ) : 0 ≤ planeLength v := Real.sqrt_nonneg _

section RightInverse

variable {z : Phase 3}

/-- The data of the reconstruction from a point of the region. -/
theorem spatialPoincareInv_chart (hν : 0 < ν) (hz : z ∈ spatialRegion ν) :
    spatialPoincareInv ν z ∈ spatialPoincareDom ∧
      spatialPoincare ν (spatialPoincareInv ν z) = z := by
  obtain ⟨hE, hc⟩ := hz
  have hG := spatialStateG_pos hc
  have hx := spatialStateDir_sq hc
  have hx2 := spatialStateDir_two_pos hc
  set G := spatialStateG z with hGdef
  set x := spatialStateDir z with hxdef
  set u := spatialRecU G x with hu
  set v := spatialRecV G x with hv
  have hZ : (u ^ 2 + v ^ 2) / 2 < G := spatialRec_lt hG hx hx2
  have hRe3 : incRotation u v G *ᵥ e₃ = x := spatialRec_rot_e₃ hG hx hx2
  have hRo : (incRotation u v G)ᵀ * incRotation u v G = 1 := incRotation_transpose_mul hG hZ
  have hRdet : (incRotation u v G).det = 1 := incRotation_det hG hZ
  have hRR : incRotation u v G * (incRotation u v G)ᵀ = 1 := mul_eq_one_comm.1 hRo
  have hRoT : ((incRotation u v G)ᵀ)ᵀ * (incRotation u v G)ᵀ = 1 := by
    rw [Matrix.transpose_transpose]; exact hRR
  have hRdetT : ((incRotation u v G)ᵀ).det = 1 := by rw [Matrix.det_transpose]; exact hRdet
  have hcx : z.1 ⨯₃ z.2 = G • x := by
    rw [hxdef, spatialStateDir, smul_inv_smul₀ hG.ne']
  set q' := (incRotation u v G)ᵀ *ᵥ z.1 with hq'
  set p' := (incRotation u v G)ᵀ *ᵥ z.2 with hp'
  have hcr : q' ⨯₃ p' = G • e₃ := by
    rw [hq', hp', mulVec_cross_mulVec _ hRoT hRdetT, hcx, Matrix.mulVec_smul, ← hRe3,
      Matrix.mulVec_mulVec, hRo, Matrix.one_mulVec]
  have hq2 : q' 2 = 0 := by
    have h := dot_self_cross q' p'
    rw [hcr, dotProduct_smul, dotProduct_e₃_eq] at h
    simpa [hG.ne'] using h
  have hp2 : p' 2 = 0 := by
    have h := dot_cross_self q' p'
    rw [hcr, dotProduct_smul, dotProduct_e₃_eq] at h
    simpa [hG.ne'] using h
  have hcz : q' 0 * p' 1 - q' 1 * p' 0 = G := by
    have h := congrFun hcr 2
    simpa [cross_apply, e₃] using h
  -- the planar state
  have hrot : spatialStateRot z = incRotation u v G := rfl
  have hzp : spatialStatePlanar z = (![q' 0, q' 1], ![p' 0, p' 1]) := by
    unfold spatialStatePlanar
    rw [hrot]
  have hq'e : planarEmbed (![q' 0, q' 1]) = q' := by
    ext i; fin_cases i <;> simp [planarEmbed, hq2]
  have hp'e : planarEmbed (![p' 0, p' 1]) = p' := by
    ext i; fin_cases i <;> simp [planarEmbed, hp2]
  have hEzp : energyMK ν 1 (spatialStatePlanar z) < 0 := by
    have h1 := spatialEnergy_rot (M := (1 : Matrix (Fin 3) (Fin 3) ℝ)) (by simp) ν
      (spatialStatePlanar z)
    rw [hzp] at h1 ⊢
    simp only [Matrix.one_mulVec, hq'e, hp'e] at h1
    rw [← h1, hq', hp', spatialEnergy_mulVec hRoT]
    exact hE
  have hlen : 0 < planeLength (spatialStatePlanar z).1 := by
    rcases (spatial_planeLength_nonneg (spatialStatePlanar z).1).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : planeLength (spatialStatePlanar z).1 = 0 := h.symm
      unfold energyMK at hEzp
      rw [h0, div_zero, sub_zero] at hEzp
      have : 0 ≤ planeSq (spatialStatePlanar z).2 / (2 * ν) := by
        have := spatial_planeSq_nonneg (spatialStatePlanar z).2
        positivity
      linarith
  have hcrz : 0 < planeCross (spatialStatePlanar z).1 (spatialStatePlanar z).2 := by
    rw [hzp]
    show 0 < ![q' 0, q' 1] 0 * ![p' 0, p' 1] 1 - ![q' 0, q' 1] 1 * ![p' 0, p' 1] 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hcz]; exact hG
  obtain ⟨hdom', hchart'⟩ := poincare_poincareInv hν one_pos ⟨hlen, hEzp, hcrz⟩
  set w' := poincareInv ν 1 (spatialStatePlanar z) with hw'
  have hwdef : spatialPoincareInv ν z = ((![w'.1 0, w'.1 1, v], ![w'.2 0, w'.2 1, u]) : Phase 3) :=
    rfl
  have hpl : spatialPlanar (spatialPoincareInv ν z) = w' := by
    rw [hwdef]
    refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp [spatialPlanar]
  have hel := (poincare_elements hν one_pos hdom').2.2.2.2.1
  rw [hchart'] at hel
  have hGw : w'.2 0 - poincareGamma w' = G := by
    rw [← hel]
    show planeCross (spatialStatePlanar z).1 (spatialStatePlanar z).2 = G
    rw [hzp]
    show ![q' 0, q' 1] 0 * ![p' 0, p' 1] 1 - ![q' 0, q' 1] 1 * ![p' 0, p' 1] 0 = G
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hcz]
  have hang : spatialAngMom (spatialPoincareInv ν z) = G := by
    unfold spatialAngMom
    rw [← spatialPlanar_gamma, hpl, hwdef]
    simpa using hGw
  have hmem : spatialPoincareInv ν z ∈ spatialPoincareDom := by
    refine ⟨?_, ?_⟩
    · rw [hwdef]; exact hdom'.1
    · have h1 : spatialGamma (spatialPoincareInv ν z) = poincareGamma w' := by
        rw [← spatialPlanar_gamma, hpl]
      have h2 : (spatialPoincareInv ν z).2 0 = w'.2 0 := by rw [hwdef]; simp
      have h3 : spatialZ (spatialPoincareInv ν z) = (u ^ 2 + v ^ 2) / 2 := by
        rw [hwdef]; simp [spatialZ]
      rw [h1, h2, h3]
      linarith
  refine ⟨hmem, ?_⟩
  have hR : spatialRot (spatialPoincareInv ν z) = incRotation u v G := by
    unfold spatialRot
    rw [hang, hwdef]
    rfl
  unfold spatialPoincare
  rw [hpl, hchart', hR, hzp]
  simp only [hq'e, hp'e]
  refine Prod.ext ?_ ?_
  · show _ *ᵥ q' = z.1
    rw [hq', Matrix.mulVec_mulVec, hRR, Matrix.one_mulVec]
  · show _ *ᵥ p' = z.2
    rw [hp', Matrix.mulVec_mulVec, hRR, Matrix.one_mulVec]

end RightInverse

/-- Item 3 (MAIN 571–578): the chart maps (44) onto the prograde negative-energy region. -/
theorem spatialPoincare_image (hν : 0 < ν) :
    spatialPoincare ν '' spatialPoincareDom = spatialRegion ν := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact spatialPoincare_mem_region hν hw
  · intro z hz
    obtain ⟨hmem, hchart⟩ := spatialPoincareInv_chart hν hz
    exact ⟨_, hmem, hchart⟩

/-- Item 3: injectivity modulo `λ ↦ λ + 2πk`. -/
theorem spatialPoincare_eq_iff (hν : 0 < ν) {w w' : Phase 3} (hw : w ∈ spatialPoincareDom)
    (hw' : w' ∈ spatialPoincareDom) :
    spatialPoincare ν w = spatialPoincare ν w' ↔
      ∃ k : ℤ, w'.1 = ![w.1 0 + 2 * π * k, w.1 1, w.1 2] ∧ w'.2 = w.2 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := spatialPoincareInv_spatialPoincare hν hw
    obtain ⟨k', hk'⟩ := spatialPoincareInv_spatialPoincare hν hw'
    rw [h] at hk
    have e := hk.symm.trans hk'
    simp only [spatialShift, Prod.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    refine ⟨k - k', ?_, ?_⟩
    · funext i
      fin_cases i
      · have := congrFun e1 0
        simp at this ⊢
        linarith
      · simpa using (congrFun e1 1).symm
      · simpa using (congrFun e1 2).symm
    · exact e2.symm
  · rintro ⟨k, h1, h2⟩
    have : w' = spatialShift k w := Prod.ext h1 h2
    rw [this, spatialPoincare_periodic hν hw k]

end KAM.Planetary.Spatial
