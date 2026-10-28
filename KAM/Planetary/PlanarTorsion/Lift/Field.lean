/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Lift.Defs

/-!
# Planar quartic torsion: the full Hamiltonian field of the lift (package T11)

Blueprint P, Part 11b (`bpP:p11b:lm-ham`).  For `H w = chi (I w) (z w)` on `Phase (2 + 2)` the
Hamiltonian field at `assemble I lam z.2 z.1` is `(∂_I chi, ∂_p chi ; 0, -∂_q chi)`, i.e. the
slow field of `chi I` in the slow components, the actions are constants of motion and the angles
move with velocity `∂_I chi`.  `p11cL_orbit_solution` assembles a solution of the full field from a
solution of the slow field and the angle integral of `∂_I chi`.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

variable {O : Set (Fin 2 → ℝ)}

/-- The coordinate map `w ↦ (I w, z w)` as a continuous linear map. -/
def p11cL_L : Phase (2 + 2) →L[ℝ] (Fin 2 → ℝ) × Phase 2 :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.pi fun i : Fin 2 =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 + 2) => ℝ) (Fin.castAdd 2 i)).comp
        (ContinuousLinearMap.snd ℝ (Fin (2 + 2) → ℝ) (Fin (2 + 2) → ℝ)))
    (ContinuousLinearMap.prod
      (ContinuousLinearMap.pi fun i : Fin 2 =>
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 + 2) => ℝ) (Fin.natAdd 2 i)).comp
          (ContinuousLinearMap.fst ℝ (Fin (2 + 2) → ℝ) (Fin (2 + 2) → ℝ)))
      (ContinuousLinearMap.pi fun i : Fin 2 =>
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 + 2) => ℝ) (Fin.natAdd 2 i)).comp
          (ContinuousLinearMap.snd ℝ (Fin (2 + 2) → ℝ) (Fin (2 + 2) → ℝ))))

theorem p11cL_L_apply (w : Phase (2 + 2)) : p11cL_L w = (p11cL_act w, p11cL_slow w) := rfl

theorem p11cL_single_cc (i k : Fin 2) :
    (Pi.single (Fin.castAdd 2 i) (1 : ℝ) : Fin (2 + 2) → ℝ) (Fin.castAdd 2 k) =
      (Pi.single i 1 : Fin 2 → ℝ) k := by
  have := k.isLt; have := i.isLt
  by_cases h : k = i
  · subst h; simp
  · have h1 : Fin.castAdd 2 k ≠ Fin.castAdd 2 i := fun e => h (Fin.castAdd_injective _ _ e)
    rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h]

theorem p11cL_single_cn (i k : Fin 2) :
    (Pi.single (Fin.castAdd 2 i) (1 : ℝ) : Fin (2 + 2) → ℝ) (Fin.natAdd 2 k) = 0 := by
  have h1 : Fin.natAdd 2 k ≠ Fin.castAdd 2 i := by
    intro e
    have := congrArg Fin.val e
    simp at this
    have := i.isLt
    omega
  exact Pi.single_eq_of_ne h1 _

theorem p11cL_single_nc (i k : Fin 2) :
    (Pi.single (Fin.natAdd 2 i) (1 : ℝ) : Fin (2 + 2) → ℝ) (Fin.castAdd 2 k) = 0 := by
  have h1 : Fin.castAdd 2 k ≠ Fin.natAdd 2 i := by
    intro e
    have := congrArg Fin.val e
    simp at this
    have := k.isLt
    omega
  exact Pi.single_eq_of_ne h1 _

theorem p11cL_single_nn (i k : Fin 2) :
    (Pi.single (Fin.natAdd 2 i) (1 : ℝ) : Fin (2 + 2) → ℝ) (Fin.natAdd 2 k) =
      (Pi.single i 1 : Fin 2 → ℝ) k := by
  by_cases h : k = i
  · subst h; simp
  · have h1 : Fin.natAdd 2 k ≠ Fin.natAdd 2 i := fun e => h (Fin.natAdd_injective _ _ e)
    rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h]

theorem p11cL_ham_analytic (chi : QuarticFamily O) :
    AnalyticOnNhd ℝ (p11cL_ham chi) (p11cL_dom O) := fun w hw =>
  (p11cQ_eval_analytic chi (p11cL_L w) ⟨hw, mem_univ _⟩).comp (p11cL_L.analyticAt w)

theorem p11cL_dom_isOpen (hO : IsOpen O) : IsOpen (p11cL_dom O) :=
  hO.preimage (continuous_pi fun i => (continuous_apply _).comp continuous_snd)

theorem p11cL_fderiv_ham (chi : QuarticFamily O) {w : Phase (2 + 2)} (hw : w ∈ p11cL_dom O)
    (v : Phase (2 + 2)) :
    fderiv ℝ (p11cL_ham chi) w v =
      fderiv ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => chi.eval u.1 u.2)
        (p11cL_L w) (p11cL_L v) := by
  have hd : DifferentiableAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => chi.eval u.1 u.2)
      (p11cL_L w) := (p11cQ_eval_analytic chi (p11cL_L w) ⟨hw, mem_univ _⟩).differentiableAt
  have h := (hd.hasFDerivAt.comp w p11cL_L.hasFDerivAt).fderiv
  have h2 : fderiv ℝ (p11cL_ham chi) w =
      (fderiv ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => chi.eval u.1 u.2) (p11cL_L w)).comp
        p11cL_L := h
  rw [h2]
  rfl

theorem p11cL_fderiv_slice (chi : QuarticFamily O) {I : Fin 2 → ℝ} (hI : I ∈ O) (z v : Phase 2) :
    fderiv ℝ (chi.eval I) z v =
      fderiv ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => chi.eval u.1 u.2) (I, z) (0, v) := by
  have hd : DifferentiableAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => chi.eval u.1 u.2) (I, z) :=
    (p11cQ_eval_analytic chi _ ⟨hI, mem_univ _⟩).differentiableAt
  have h := (hd.hasFDerivAt.comp z ((hasFDerivAt_const I z).prodMk (hasFDerivAt_id z))).fderiv
  have h2 : fderiv ℝ (chi.eval I) z =
      (fderiv ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => chi.eval u.1 u.2) (I, z)).comp
        ((0 : Phase 2 →L[ℝ] (Fin 2 → ℝ)).prod (ContinuousLinearMap.id ℝ (Phase 2))) := h
  rw [h2]
  simp

theorem p11cL_partial_eq (chi : QuarticFamily O) {I : Fin 2 → ℝ} (hI : I ∈ O) (y : Phase 2)
    (i : Fin 2) :
    fderiv ℝ (fun J => chi.eval J y) I (Pi.single i 1) = p11cL_dI chi (I, y) i := by
  have hd : DifferentiableAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => chi.eval u.1 u.2) (I, y) :=
    (p11cQ_eval_analytic chi _ ⟨hI, mem_univ _⟩).differentiableAt
  have hf : HasFDerivAt (fun J : Fin 2 → ℝ => (J, y))
      ((ContinuousLinearMap.id ℝ (Fin 2 → ℝ)).prod (0 : (Fin 2 → ℝ) →L[ℝ] Phase 2)) I :=
    (hasFDerivAt_id I).prodMk (hasFDerivAt_const y I)
  have h := (HasFDerivAt.comp (g := fun u : (Fin 2 → ℝ) × Phase 2 => chi.eval u.1 u.2)
    (f := fun J : Fin 2 → ℝ => (J, y)) I hd.hasFDerivAt hf).fderiv
  have h2 : fderiv ℝ (fun J => chi.eval J y) I =
      (fderiv ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => chi.eval u.1 u.2) (I, y)).comp
        ((ContinuousLinearMap.id ℝ (Fin 2 → ℝ)).prod (0 : (Fin 2 → ℝ) →L[ℝ] Phase 2)) := h
  rw [h2]
  simp [p11cL_dI]

theorem p11cL_dI_analyticAt (chi : QuarticFamily O) {u : (Fin 2 → ℝ) × Phase 2} (hu : u.1 ∈ O)
    (i : Fin 2) : AnalyticAt ℝ (fun v => p11cL_dI chi v i) u := by
  have hD : AnalyticAt ℝ (fderiv ℝ (fun v : (Fin 2 → ℝ) × Phase 2 => chi.eval v.1 v.2)) u :=
    (p11cQ_eval_analytic chi u ⟨hu, mem_univ _⟩).fderiv
  exact ((ContinuousLinearMap.apply ℝ ℝ ((Pi.single i 1 : Fin 2 → ℝ), (0 : Phase 2))).analyticAt
    _).comp hD

theorem p11cL_L_mom_c (i : Fin 2) :
    p11cL_L ((0 : Fin (2 + 2) → ℝ), Pi.single (Fin.castAdd 2 i) (1 : ℝ)) =
      (Pi.single i 1, (0 : Phase 2)) := by
  refine Prod.ext (funext fun k => ?_) (Prod.ext (funext fun k => ?_) (funext fun k => ?_))
  · exact p11cL_single_cc i k
  · rfl
  · exact p11cL_single_cn i k

theorem p11cL_L_mom_n (i : Fin 2) :
    p11cL_L ((0 : Fin (2 + 2) → ℝ), Pi.single (Fin.natAdd 2 i) (1 : ℝ)) =
      (0, ((0 : Fin 2 → ℝ), Pi.single i 1)) := by
  refine Prod.ext (funext fun k => ?_) (Prod.ext (funext fun k => ?_) (funext fun k => ?_))
  · exact p11cL_single_nc i k
  · rfl
  · exact p11cL_single_nn i k

theorem p11cL_L_pos_c (i : Fin 2) :
    p11cL_L (Pi.single (Fin.castAdd 2 i) (1 : ℝ), (0 : Fin (2 + 2) → ℝ)) = 0 := by
  refine Prod.ext (funext fun k => rfl) (Prod.ext (funext fun k => ?_) (funext fun k => rfl))
  exact p11cL_single_cn i k

theorem p11cL_L_pos_n (i : Fin 2) :
    p11cL_L (Pi.single (Fin.natAdd 2 i) (1 : ℝ), (0 : Fin (2 + 2) → ℝ)) =
      (0, (Pi.single i 1, (0 : Fin 2 → ℝ))) := by
  refine Prod.ext (funext fun k => rfl) (Prod.ext (funext fun k => ?_) (funext fun k => rfl))
  exact p11cL_single_nn i k

/-- The Hamiltonian field of the full lift at an assembled point. -/
theorem p11cL_field_assemble (chi : QuarticFamily O) {I : Fin 2 → ℝ} (hI : I ∈ O)
    (lam : Fin 2 → ℝ) (z : Phase 2) :
    hamiltonianVectorField (p11cL_ham chi) (assemble I lam z.2 z.1) =
      (Fin.append (fun i => p11cL_dI chi (I, z) i) (hamiltonianVectorField (chi.eval I) z).1,
        Fin.append (0 : Fin 2 → ℝ) (hamiltonianVectorField (chi.eval I) z).2) := by
  have hw : assemble I lam z.2 z.1 ∈ p11cL_dom O := by
    show p11cL_act _ ∈ O
    rw [p11cL_act_assemble]; exact hI
  have hL : p11cL_L (assemble I lam z.2 z.1) = (I, z) := by
    rw [p11cL_L_apply, p11cL_act_assemble, p11cL_slow_assemble]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;> refine Fin.addCases ?_ ?_ j <;>
    intro i
  · simp only [hamiltonianVectorField, p11cL_fderiv_ham chi hw, hL, p11cL_L_mom_c,
      Fin.append_left]
    rfl
  · simp only [hamiltonianVectorField, p11cL_fderiv_ham chi hw, hL, p11cL_L_mom_n,
      Fin.append_right, p11cL_fderiv_slice chi hI]
  · simp only [hamiltonianVectorField, p11cL_fderiv_ham chi hw, hL, p11cL_L_pos_c,
      Fin.append_left]
    simp
  · simp only [hamiltonianVectorField, p11cL_fderiv_ham chi hw, hL, p11cL_L_pos_n,
      Fin.append_right, p11cL_fderiv_slice chi hI]

end KAM.Planetary

end
