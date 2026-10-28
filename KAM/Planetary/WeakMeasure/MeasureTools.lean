/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakMeasure.Basic

/-!
# Measure tools for the weak-measure layer (blueprint `bpP:p11a:f-meas`, P11A-W5)

Two Lebesgue-measure helpers on the ambient Pi carriers:

* `p11_measurePreserving_orthogonal`: the affine map `x ↦ y₀ + Q x` with `Q Qᵀ = 1` preserves
  Lebesgue measure on `Fin n → ℝ` (determinant image measure);
* `p11_volume_le_of_sections`: Tonelli on `ℝ × ℝ^m ≃ ℝ^(m+1)`: a measurable set whose `t`-sections
  (last coordinate) have measure `≤ c` and whose remaining coordinates lie in `[-R, R]` has measure
  `≤ (2R)^m c`.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped Matrix

namespace KAM.Planetary

section Orthogonal

variable {n : ℕ}

theorem p11_det_abs_eq_one {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q * Qᵀ = 1) :
    Q.det ≠ 0 ∧ |(Q.det)⁻¹| = 1 := by
  have h : Q.det * Q.det = 1 := by
    have := congrArg Matrix.det hQ
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have hne : Q.det ≠ 0 := fun h0 => by simp [h0] at h
  refine ⟨hne, ?_⟩
  have : |Q.det| * |Q.det| = 1 := by rw [← abs_mul, h, abs_one]
  have h1 : |Q.det| = 1 := by nlinarith [abs_nonneg Q.det]
  rw [abs_inv, h1, inv_one]

/-- The linear map `x ↦ Q x` with `Q Qᵀ = 1` preserves Lebesgue measure. -/
theorem p11_measurePreserving_mulVec {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q * Qᵀ = 1) :
    MeasurePreserving (fun x : Fin n → ℝ => Q.mulVec x) volume volume := by
  obtain ⟨hne, habs⟩ := p11_det_abs_eq_one hQ
  refine ⟨by fun_prop, ?_⟩
  have := Real.map_matrix_volume_pi_eq_smul_volume_pi hne
  rw [habs, ENNReal.ofReal_one, one_smul] at this
  exact this

/-- The affine map `x ↦ y₀ + Q x` with `Q Qᵀ = 1` preserves Lebesgue measure. -/
theorem p11_measurePreserving_orthogonal {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q * Qᵀ = 1)
    (y0 : Fin n → ℝ) :
    MeasurePreserving (fun x : Fin n → ℝ => y0 + Q.mulVec x) volume volume :=
  (measurePreserving_add_left volume y0).comp (p11_measurePreserving_mulVec hQ)

end Orthogonal

section Tonelli

variable {m : ℕ}

/-- Tonelli bound on `ℝ^(m+1)` split as the last coordinate `t` against `x' ∈ ℝ^m`. -/
theorem p11_volume_le_of_sections {S : Set (Fin (m + 1) → ℝ)} (hS : MeasurableSet S)
    {R c : ℝ} (hR : 0 ≤ R)
    (hproj : ∀ x ∈ S, ∀ j : Fin m, |x (Fin.castSucc j)| ≤ R)
    (hsec : ∀ x' : Fin m → ℝ, volume {t : ℝ | Fin.snoc x' t ∈ S} ≤ ENNReal.ofReal c) :
    volume S ≤ ENNReal.ofReal ((2 * R) ^ m * c) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m) with he
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
  set T : Set (ℝ × (Fin m → ℝ)) := e.symm ⁻¹' S with hT
  have hTm : MeasurableSet T := e.symm.measurable hS
  have h1 : volume S = volume T := by
    have := hmp.symm e |>.measure_preimage_equiv S
    simpa [hT] using this.symm
  have hsnoc : ∀ (t : ℝ) (x' : Fin m → ℝ), e.symm (t, x') = Fin.snoc x' t := by
    intro t x'
    simp [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  have hvol : (volume : Measure (ℝ × (Fin m → ℝ))) = volume.prod volume := rfl
  rw [h1, hvol, Measure.prod_apply_symm hTm]
  have hmem : ∀ x', (fun t : ℝ => (t, x')) ⁻¹' T = {t : ℝ | Fin.snoc x' t ∈ S} := by
    intro x'; ext t; simp [hT, hsnoc]
  simp_rw [hmem]
  set B : Set (Fin m → ℝ) := Set.pi univ fun _ => Icc (-R) R with hB
  have hzero : ∀ x' ∉ B, volume {t : ℝ | Fin.snoc x' t ∈ S} = 0 := by
    intro x' hx'
    have : {t : ℝ | Fin.snoc x' t ∈ S} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro ht
      apply hx'
      intro j _
      have := hproj _ ht j
      simp only [Fin.snoc_castSucc] at this
      exact abs_le.1 this
    rw [this, measure_empty]
  have hBm : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hBvol : volume B = ENNReal.ofReal (2 * R) ^ m := by
    rw [hB, volume_pi_pi]
    simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2; ring
  calc ∫⁻ x', volume {t : ℝ | Fin.snoc x' t ∈ S}
      ≤ ∫⁻ x', B.indicator (fun _ => ENNReal.ofReal c) x' := by
        refine lintegral_mono fun x' => ?_
        by_cases hx : x' ∈ B
        · simpa [hx] using hsec x'
        · simp [hx, hzero x' hx]
    _ = ENNReal.ofReal c * volume B := lintegral_indicator_const hBm _
    _ = ENNReal.ofReal ((2 * R) ^ m * c) := by
        rw [hBvol, ← ENNReal.ofReal_pow (by linarith), mul_comm,
          ← ENNReal.ofReal_mul (pow_nonneg (by linarith) m)]

end Tonelli

end KAM.Planetary
