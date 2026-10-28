/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.Lift.Hessian

/-!
# Secular spectrum: the derivative of the lift

Blueprint P, Part 9 (`stepP:p9:lift-anti`): the explicit derivative `dLift R z u` of `liftMap R`
at `z` in the direction `u`, obtained as a line derivative; the action-dependent angle shift
contributes the terms with the full derivative of `R` and its entrywise second derivative.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

section Deriv

lemma hasDerivAt_assemble {I φ p q : ℝ → Vec n} {I' φ' p' q' : Vec n} {t : ℝ}
    (hI : HasDerivAt I I' t) (hφ : HasDerivAt φ φ' t) (hp : HasDerivAt p p' t)
    (hq : HasDerivAt q q' t) :
    HasDerivAt (fun s => assemble (I s) (φ s) (p s) (q s)) (assemble I' φ' p' q') t := by
  refine HasDerivAt.prodMk (hasDerivAt_pi.2 fun k => ?_) (hasDerivAt_pi.2 fun k => ?_)
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp only [Fin.append_left, Fin.append_right]
    · exact hasDerivAt_vec_entry hφ j
    · exact hasDerivAt_vec_entry hq j
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp only [Fin.append_left, Fin.append_right]
    · exact hasDerivAt_vec_entry hI j
    · exact hasDerivAt_vec_entry hp j

/-- Angle block of the derivative of the lift at `z` in direction `u`. -/
def dTheta (R : Vec n → Mat n) (z u : Phase (n+n)) : Vec n :=
  let I : Vec n := fast z.2
  let ξ : Vec n := slow z.1
  let η : Vec n := slow z.2
  let Ru : Mat n := fderiv ℝ R I (fast u.2)
  let D : Fin n → Mat n := fun l => fderiv ℝ R I (Pi.single l 1)
  let E : Fin n → Mat n := fun l => hess R I (fast u.2) (Pi.single l 1)
  fun l => fast u.1 l -
    (slow u.2 ⬝ᵥ ((D l * (R I).transpose).mulVec ξ) +
      η ⬝ᵥ (((E l * (R I).transpose + D l * Ru.transpose).mulVec ξ) +
        (D l * (R I).transpose).mulVec (slow u.1)))

/-- Second slow block of the derivative of the lift. -/
def dP (R : Vec n → Mat n) (z u : Phase (n+n)) : Vec n :=
  (R (fast z.2)).transpose.mulVec (slow u.2) +
    (fderiv ℝ R (fast z.2) (fast u.2)).transpose.mulVec (slow z.2)

/-- First slow block of the derivative of the lift. -/
def dQ (R : Vec n → Mat n) (z u : Phase (n+n)) : Vec n :=
  (R (fast z.2)).transpose.mulVec (slow u.1) +
    (fderiv ℝ R (fast z.2) (fast u.2)).transpose.mulVec (slow z.1)

/-- The derivative of the lift at `z` in direction `u`. -/
def dLift (R : Vec n → Mat n) (z u : Phase (n+n)) : Phase (n+n) :=
  assemble (fast u.2) (dTheta R z u) (dP R z u) (dQ R z u)

lemma hasDerivAt_phase_line (z u : Phase (n+n)) :
    HasDerivAt (fun s : ℝ => z + s • u) u 0 := by
  simpa using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add z

lemma hasDerivAt_liftMap_line {W : Set (Vec n)} (hW : IsOpen W) {R : Vec n → Mat n}
    (hAn : AnalyticOnNhd ℝ R W) {z : Phase (n+n)} (hz : z ∈ liftDomain W) (u : Phase (n+n)) :
    HasDerivAt (fun t : ℝ => liftMap R (z + t • u)) (dLift R z u) 0 := by
  set I : Vec n := fast z.2 with hIdef
  have hI : I ∈ W := hz
  have hR := hasDerivAt_comp_line (hAn I hI).differentiableAt (fast u.2)
  have hRt := hasDerivAt_mat_transpose hR
  have hq : HasDerivAt (fun s : ℝ => slow z.1 + s • slow u.1) (slow u.1) 0 := by
    simpa using hasDerivAt_line (slow z.1) (slow u.1) 0
  have hp : HasDerivAt (fun s : ℝ => slow z.2 + s • slow u.2) (slow u.2) 0 := by
    simpa using hasDerivAt_line (slow z.2) (slow u.2) 0
  have hθ0 : HasDerivAt (fun s : ℝ => fast z.1 + s • fast u.1) (fast u.1) 0 := by
    simpa using hasDerivAt_line (fast z.1) (fast u.1) 0
  have hI' : HasDerivAt (fun s : ℝ => I + s • fast u.2) (fast u.2) 0 := by
    simpa using hasDerivAt_line I (fast u.2) 0
  have hfn : ∀ t : ℝ, liftMap R (z + t • u) = assemble (I + t • fast u.2)
      (fun l => (fast z.1 + t • fast u.1) l - (slow z.2 + t • slow u.2) ⬝ᵥ
        ((fderiv ℝ R (I + t • fast u.2) (Pi.single l 1) * (R (I + t • fast u.2)).transpose).mulVec
          (slow z.1 + t • slow u.1)))
      ((R (I + t • fast u.2)).transpose.mulVec (slow z.2 + t • slow u.2))
      ((R (I + t • fast u.2)).transpose.mulVec (slow z.1 + t • slow u.1)) := by
    intro t
    simp only [liftMap, hIdef]
    congr 1
  simp only [hfn]
  have hpp := hasDerivAt_mat_mulVec hRt hp
  have hqq := hasDerivAt_mat_mulVec hRt hq
  have hA : ∀ l, HasDerivAt (fun s : ℝ => fderiv ℝ R (I + s • fast u.2) (Pi.single l 1) *
      (R (I + s • fast u.2)).transpose)
      (hess R I (fast u.2) (Pi.single l 1) * (R I).transpose +
        fderiv ℝ R I (Pi.single l 1) * (fderiv ℝ R I (fast u.2)).transpose) 0 := fun l => by
    have := hasDerivAt_mat_mul (hasDerivAt_fderiv_line hW hAn hI (fast u.2) (Pi.single l 1))
      hRt
    simpa using this
  have hw : ∀ l, HasDerivAt (fun s : ℝ => (fderiv ℝ R (I + s • fast u.2) (Pi.single l 1) *
      (R (I + s • fast u.2)).transpose).mulVec (slow z.1 + s • slow u.1)) _ 0 :=
    fun l => hasDerivAt_mat_mulVec (hA l) hq
  have hθ : HasDerivAt (fun s : ℝ => fun l => (fast z.1 + s • fast u.1) l -
      (slow z.2 + s • slow u.2) ⬝ᵥ ((fderiv ℝ R (I + s • fast u.2) (Pi.single l 1) *
        (R (I + s • fast u.2)).transpose).mulVec (slow z.1 + s • slow u.1))) _ 0 :=
    hasDerivAt_pi.2 fun l => (hasDerivAt_vec_entry hθ0 l).sub (hasDerivAt_vec_dot hp (hw l))
  refine HasDerivAt.congr_deriv (hasDerivAt_assemble hI' hθ hpp hqq) ?_
  simp only [dLift, dTheta, dP, dQ]
  congr 1
  · funext l
    simp [hIdef, dotProduct, add_comm]
  · simp only [zero_smul, add_zero]; exact add_comm _ _
  · simp only [zero_smul, add_zero]; exact add_comm _ _

lemma fderiv_liftMap_eq {W : Set (Vec n)} (hW : IsOpen W) {R : Vec n → Mat n}
    (hAn : AnalyticOnNhd ℝ R W) {z : Phase (n+n)} (hz : z ∈ liftDomain W) (u : Phase (n+n)) :
    fderiv ℝ (liftMap R) z u = dLift R z u := by
  have hd : DifferentiableAt ℝ (liftMap R) z := (analyticAt_liftMap hW hAn hz).differentiableAt
  have h0 : HasFDerivAt (liftMap R) (fderiv ℝ (liftMap R) z) (z + (0:ℝ) • u) := by
    simpa using hd.hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => liftMap R (z + t • u)) (fderiv ℝ (liftMap R) z u) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => z + s • u) (0:ℝ) h0 (hasDerivAt_phase_line z u)
  exact h1.unique (hasDerivAt_liftMap_line hW hAn hz u)

end Deriv

end SecularSpectrum

end KAM.Planetary

end
