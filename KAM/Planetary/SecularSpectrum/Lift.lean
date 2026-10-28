/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Basic
public import KAM.Planetary.SecularSpectrum.Lift.Symplectic

/-!
# Secular spectrum: the action-dependent analytic symplectic lift

Blueprint P, Part 9 (`bpP:p9:lift`): for an analytic family `R` of rotations on an open set `W`
of actions, `liftMap R` and `liftInv R` are mutually inverse real-analytic symplectic maps of
`liftDomain W` which preserve the action block and the Euclidean lengths of the slow blocks, and
commute with fast-angle translations.  The definitions (`liftMap`, `liftInv`, `liftDomain`) are in
`Lift.Basic`; the proof cuts `stepP:p9:lift-bij`, `stepP:p9:lift-anti`, `stepP:p9:lift-form`,
`stepP:p9:lift-mc` are in `Lift.Basic`, `Lift.Analytic`, `Lift.Calculus`, `Lift.Hessian`,
`Lift.Deriv`, `Lift.Core` and `Lift.Symplectic`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

theorem lift {W : Set (Vec n)} (hW : IsOpen W) {R : Vec n → Mat n}
    (hAn : AnalyticOnNhd ℝ R W) (hR : ∀ I ∈ W, isSO (R I)) :
    AnalyticOnNhd ℝ (liftMap R) (liftDomain W) ∧
    AnalyticOnNhd ℝ (liftInv R) (liftDomain W) ∧
    IsSymplecticOn 1 (liftMap R) (liftDomain W) ∧
    IsSymplecticOn 1 (liftInv R) (liftDomain W) ∧
    (∀ w ∈ liftDomain W, liftInv R (liftMap R w) = w ∧ liftMap R (liftInv R w) = w ∧
      fast (liftMap R w).2 = fast w.2 ∧
      length2 (slow (liftMap R w).1) = length2 (slow w.1) ∧
      length2 (slow (liftMap R w).2) = length2 (slow w.2)) ∧
    (∀ w ∈ liftDomain W, ∀ c : Vec n,
      liftMap R (w + (Fin.append c 0,0)) = liftMap R w + (Fin.append c 0,0)) := by
  have hopen := isOpen_liftDomain hW
  have hAnT := analyticOnNhd_transpose hAn
  have hRT : ∀ I ∈ W, isSO ((R I).transpose) := fun I hI => isSO_transpose (hR I hI)
  have heq : ∀ w ∈ liftDomain W, liftInv R w = liftMap (fun I => (R I).transpose) w :=
    fun w hw => liftInv_eq_liftMap_transpose hW hAn hR hw
  have hev : ∀ w ∈ liftDomain W,
      liftInv R =ᶠ[𝓝 w] liftMap (fun I => (R I).transpose) := fun w hw => by
    filter_upwards [hopen.mem_nhds hw] with y hy using heq y hy
  have hsymp : ∀ {S : Vec n → Mat n}, AnalyticOnNhd ℝ S W → (∀ I ∈ W, isSO (S I)) →
      IsSymplecticOn 1 (liftMap S) (liftDomain W) := by
    intro S hS hSR z hz u v
    rw [fderiv_liftMap_eq hW hS hz, fderiv_liftMap_eq hW hS hz, symplecticForm_dLift hW hS hSR hz,
      one_mul]
  refine ⟨fun w hw => analyticAt_liftMap hW hAn hw,
    fun w hw => (analyticAt_liftMap hW hAnT hw).congr (hev w hw).symm,
    hsymp hAn hR, ?_, ?_, ?_⟩
  · intro z hz u v
    rw [(hev z hz).fderiv_eq]
    exact hsymp hAnT hRT z hz u v
  · intro w hw
    have h := hR _ hw
    exact ⟨liftInv_liftMap_of_isSO h, liftMap_liftInv_of_isSO h, fast_snd_liftMap R w,
      length2_slow_fst_liftMap h, length2_slow_snd_liftMap h⟩
  · intro w _ c
    exact liftMap_add_append R w c

end SecularSpectrum

end KAM.Planetary

end
