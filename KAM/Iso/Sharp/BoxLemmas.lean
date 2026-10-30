/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.BoxTorsion
public import KAM.Iso.Apost.TorsionDiff
public import KAM.Iso.Apost.G1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Parameter boxes (isoenergetic): the bordered torsion and the energy under a change of `H`

For a fixed torus `K` and frequency `ω`, the bordered torsion
`𝖳_H = (T_H ω; Y_H 0)` depends on `H` only through `T_H` (via `A = DX_H ∘ K`, see
`KAM.Sharp.torsion_sub_param`) and the last row `Y_H = DH(K) N`. Hence
`𝖳_{H'} - 𝖳_H = (T_{H'} - T_H, 0; Y_{H'} - Y_H, 0)`, with `∑ |Y_{H'} - Y_H| ≤ ‖N‖ ‖DH'(Kθ) -
  DH(Kθ)‖`
(`KAM.Iso.Sharp.sum_norm_energyRow_sub_param_le`), and the average energy moves by at most
`sup |H' - H|` on the image of `K` (`KAM.Iso.Sharp.norm_energyAverage_sub_param_le`).
-/

public section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory

namespace KAM.Iso.Sharp

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost

variable {n : ℕ}

/-- `Y_{H'} - Y_H = ∑_s N_{sb} (DH' - DH)(e_s)` for a fixed torus. -/
theorem energyRow_sub_param (H H' : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ) (b : Fin n) :
    energyRow H' K θ b - energyRow H K θ b =
      ∑ s, normalMat K θ s b *
        (fderiv ℂ H' (K θ) - fderiv ℂ H (K θ)) ((sumVec n).symm (Pi.single s 1)) := by
  rw [ExtendedAux.energyRow_apply, ExtendedAux.energyRow_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [ContinuousLinearMap.sub_apply]
  ring

/-- `∑_b |Y_{H'} - Y_H| ≤ ‖N‖ ‖DH'(Kθ) - DH(Kθ)‖`. -/
theorem sum_norm_energyRow_sub_param_le (H H' : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ) {B a : ℝ}
    (hN : ‖normalMat K θ‖ ≤ B) (hφ : ‖fderiv ℂ H' (K θ) - fderiv ℂ H (K θ)‖ ≤ a) :
    ∑ j, ‖energyRow H' K θ j - energyRow H K θ j‖ ≤ B * a := by
  have hφs := (ExtendedAux.sum_norm_apply_le_opNorm
    (fderiv ℂ H' (K θ) - fderiv ℂ H (K θ))).trans hφ
  have hB : 0 ≤ B := (norm_nonneg _).trans hN
  calc ∑ j, ‖energyRow H' K θ j - energyRow H K θ j‖
      = ∑ j, ‖∑ s, normalMat K θ s j *
          (fderiv ℂ H' (K θ) - fderiv ℂ H (K θ)) ((sumVec n).symm (Pi.single s 1))‖ :=
        Finset.sum_congr rfl fun j _ => by rw [energyRow_sub_param]
    _ ≤ ‖normalMat K θ‖ * ∑ s, ‖(fderiv ℂ H' (K θ) - fderiv ℂ H (K θ))
          ((sumVec n).symm (Pi.single s 1))‖ := Apost.TorsionDiff.sum_norm_mul_le _ _
    _ ≤ B * a := mul_le_mul hN hφs (Finset.sum_nonneg fun _ _ => norm_nonneg _) hB

/-- The pointwise block estimate for the bordered torsion at a fixed torus and frequency:
`‖𝖳_{H'} - 𝖳_H‖ ≤ max {a, e}` if `‖T_{H'} - T_H‖ ≤ a` and `∑ |Y_{H'} - Y_H| ≤ e`. -/
theorem norm_extendedTorsion_sub_param_le (H H' : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (θ : Fin n → ℂ) {a e : ℝ}
    (hT : ‖torsion H' K ω θ - torsion H K ω θ‖ ≤ a)
    (hY : ∑ j, ‖energyRow H' K θ j - energyRow H K θ j‖ ≤ e) :
    ‖KAM.Iso.extendedTorsion H' K ω θ - KAM.Iso.extendedTorsion H K ω θ‖ ≤ max a e := by
  rw [extendedTorsion_eq_bordMat, extendedTorsion_eq_bordMat, Apost.TorsionDiff.bordMat_sub]
  have hc0 : ‖(fun a => (ω a : ℂ)) - (fun a => (ω a : ℂ))‖ ≤ 0 := by
    rw [sub_self, norm_zero]
  have := Apost.TorsionDiff.norm_bordMat_le _ _ _ hT hc0 hY
    ((Finset.sum_nonneg fun _ _ => norm_nonneg _).trans hY)
  rwa [add_zero] at this

/-- The averaged bordered torsions for `H'` and `H` on the same torus differ by at most `A` if
their (continuous) tori do. -/
theorem norm_extendedTorsionAverage_sub_param_le (H H' : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) {A : ℝ}
    (hc : Continuous (fun x : Fin n → ℝ => KAM.Iso.extendedTorsion H K ω (fun i => (x i : ℂ))))
    (hc' : Continuous (fun x : Fin n → ℝ => KAM.Iso.extendedTorsion H' K ω (fun i => (x i : ℂ))))
    (hb : ∀ x : Fin n → ℝ, ‖KAM.Iso.extendedTorsion H' K ω (fun i => (x i : ℂ)) -
      KAM.Iso.extendedTorsion H K ω (fun i => (x i : ℂ))‖ ≤ A) :
    ‖KAM.Iso.extendedTorsionAverage H' K ω - KAM.Iso.extendedTorsionAverage H K ω‖ ≤ A := by
  have heq : KAM.Iso.extendedTorsionAverage H' K ω - KAM.Iso.extendedTorsionAverage H K ω =
      torusAverage (fun x : Fin n → ℝ => KAM.Iso.extendedTorsion H' K ω (fun i => (x i : ℂ)) -
        KAM.Iso.extendedTorsion H K ω (fun i => (x i : ℂ))) := by
    ext i j
    have hF : Continuous (fun x : Fin n → ℝ =>
        KAM.Iso.extendedTorsion H' K ω (fun i => (x i : ℂ)) -
          KAM.Iso.extendedTorsion H K ω (fun i => (x i : ℂ))) := hc'.sub hc
    rw [TorsionDiff.torusAverage_matrix_apply_fintype hF i j, Matrix.sub_apply]
    simp only [Matrix.sub_apply]
    exact (integral_sub (integrableOn_unitCube_of_continuous (hc'.matrix_elem i j))
      (integrableOn_unitCube_of_continuous (hc.matrix_elem i j))).symm
  rw [heq]
  exact norm_torusAverage_le fun x _ => hb x

/-- The average energies of `H'` and `H` on the same torus differ by at most `A` if `H' ∘ K` and
`H ∘ K` (continuous on `ℝⁿ`) differ by at most `A` on the real torus. -/
theorem norm_energyAverage_sub_param_le (H H' : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) {A : ℝ}
    (hc : Continuous (fun x : Fin n → ℝ => H (K fun j => (x j : ℂ))))
    (hc' : Continuous (fun x : Fin n → ℝ => H' (K fun j => (x j : ℂ))))
    (hb : ∀ x : Fin n → ℝ, ‖H' (K fun j => (x j : ℂ)) - H (K fun j => (x j : ℂ))‖ ≤ A) :
    ‖KAM.Iso.energyAverage H' K - KAM.Iso.energyAverage H K‖ ≤ A := by
  have heq : KAM.Iso.energyAverage H' K - KAM.Iso.energyAverage H K =
      torusAverage (fun x : Fin n → ℝ =>
        H' (K fun j => (x j : ℂ)) - H (K fun j => (x j : ℂ))) := by
    unfold KAM.Iso.energyAverage torusAverage
    rw [integral_sub (integrableOn_unitCube_of_continuous hc')
      (integrableOn_unitCube_of_continuous hc)]
  rw [heq]
  exact norm_torusAverage_le fun x _ => hb x

end KAM.Iso.Sharp

end
