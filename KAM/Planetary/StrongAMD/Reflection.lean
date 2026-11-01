/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Momentum
public import KAM.Planetary.Newtonian.Models
public import KAM.Frozen.Planetary.Defs.IsMovingSolutionOn

/-!
# Orientation reversal of a planar phase

Package LP-MOM, orientation remark of `LP:MAIN L3 (130–139)` ("choose the plane's orientation so
that `L > 0`"); track LP, non-frozen; the statement surface is proposed in
docs/tracks/LP/FREEZE-PROPOSAL.md.

`reflectPhase` negates the second coordinate of every body vector of both `q` and `p` (a linear
symplectic isometry).  Kepler energy, axis, action, eccentricity, pair distances, `NoCollision`, the
moving Hamiltonian and `strongAMD` are invariant, `L_i` and `L` change sign, `reflectPhase` is an
involution, and `IsMovingSolutionOn ν μ J z ↔ IsMovingSolutionOn ν μ J (reflectPhase ∘ z)`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary KAM.Kepler
open scoped BigOperators

variable {n : ℕ}

/-- The reflection `(x, y) ↦ (x, -y)` of the plane. -/
def reflectPlane (w : Fin 2 → ℝ) : Fin 2 → ℝ := fun k => if k = 1 then -w k else w k

/-- Sign `-1` on the second coordinate of each body, `+1` on the first. -/
def reflectSign (j : Fin (n * 2)) : ℝ := if (finProdFinEquiv.symm j).2 = 1 then -1 else 1

/-- Reflection of a coordinate vector: negate the second coordinate of every body. -/
def reflectVec (v : Fin (n * 2) → ℝ) : Fin (n * 2) → ℝ := fun j => reflectSign j * v j

/-- Orientation reversal of a planar phase. -/
def reflectPhase (z : Phase (n * 2)) : Phase (n * 2) := (reflectVec z.1, reflectVec z.2)

@[simp] theorem reflectPhase_fst (z : Phase (n * 2)) : (reflectPhase z).1 = reflectVec z.1 := rfl
@[simp] theorem reflectPhase_snd (z : Phase (n * 2)) : (reflectPhase z).2 = reflectVec z.2 := rfl

theorem reflectSign_mul_self (j : Fin (n * 2)) : reflectSign j * reflectSign j = 1 := by
  unfold reflectSign; split_ifs <;> norm_num

theorem reflectVec_reflectVec (v : Fin (n * 2) → ℝ) : reflectVec (reflectVec v) = v := by
  ext j
  simp only [reflectVec, ← mul_assoc, reflectSign_mul_self, one_mul]

/-- `reflectPhase` is an involution. -/
theorem reflectPhase_reflectPhase (z : Phase (n * 2)) : reflectPhase (reflectPhase z) = z := by
  ext j <;> simp [reflectVec_reflectVec]

theorem reflectPlane_reflectPlane (w : Fin 2 → ℝ) : reflectPlane (reflectPlane w) = w := by
  ext k; fin_cases k <;> simp [reflectPlane]

theorem reflectPlane_sub (v w : Fin 2 → ℝ) :
    reflectPlane (v - w) = reflectPlane v - reflectPlane w := by
  ext k; fin_cases k <;> simp [reflectPlane]; ring

theorem reflectPlane_add (v w : Fin 2 → ℝ) :
    reflectPlane (v + w) = reflectPlane v + reflectPlane w := by
  ext k; fin_cases k <;> simp [reflectPlane]; ring

theorem reflectPlane_smul (c : ℝ) (v : Fin 2 → ℝ) :
    reflectPlane (c • v) = c • reflectPlane v := by
  ext k; fin_cases k <;> simp [reflectPlane]

theorem planeSq_reflectPlane (w : Fin 2 → ℝ) : planeSq (reflectPlane w) = planeSq w := by
  simp [planeSq, Fin.sum_univ_two, reflectPlane]

theorem planeLength_reflectPlane (w : Fin 2 → ℝ) :
    planeLength (reflectPlane w) = planeLength w := by
  simp [planeLength, planeSq_reflectPlane]

theorem planeDot_reflectPlane (v w : Fin 2 → ℝ) :
    planeDot (reflectPlane v) (reflectPlane w) = planeDot v w := by
  simp [planeDot, Fin.sum_univ_two, reflectPlane]

theorem planeCross_reflectPlane (v w : Fin 2 → ℝ) :
    planeCross (reflectPlane v) (reflectPlane w) = -planeCross v w := by
  simp [planeCross, reflectPlane]; ring

theorem bodyVector_reflectVec (v : Fin (n * 2) → ℝ) (i : Fin n) :
    bodyVector (reflectVec v) i = reflectPlane (bodyVector v i) := by
  ext k
  simp [bodyVector, reflectVec, reflectSign, reflectPlane]

theorem bodyVector_reflectPhase_fst (z : Phase (n * 2)) (i : Fin n) :
    bodyVector (reflectPhase z).1 i = reflectPlane (bodyVector z.1 i) :=
  bodyVector_reflectVec _ _

theorem bodyVector_reflectPhase_snd (z : Phase (n * 2)) (i : Fin n) :
    bodyVector (reflectPhase z).2 i = reflectPlane (bodyVector z.2 i) :=
  bodyVector_reflectVec _ _

section Invariants

variable (ν : Fin n → ℝ) (z : Phase (n * 2)) (i : Fin n)

theorem planeLength_reflectPhase_fst :
    planeLength (bodyVector (reflectPhase z).1 i) = planeLength (bodyVector z.1 i) := by
  rw [bodyVector_reflectPhase_fst, planeLength_reflectPlane]

theorem planeLength_reflectPhase_sub (j : Fin n) :
    planeLength (bodyVector (reflectPhase z).1 i - bodyVector (reflectPhase z).1 j) =
      planeLength (bodyVector z.1 i - bodyVector z.1 j) := by
  rw [bodyVector_reflectPhase_fst, bodyVector_reflectPhase_fst, ← reflectPlane_sub,
    planeLength_reflectPlane]

theorem keplerEnergy_reflectPhase : keplerEnergy ν (reflectPhase z) i = keplerEnergy ν z i := by
  unfold keplerEnergy
  rw [bodyVector_reflectPhase_fst, bodyVector_reflectPhase_snd, planeSq_reflectPlane,
    planeLength_reflectPlane]

theorem keplerAxis_reflectPhase : keplerAxis ν (reflectPhase z) i = keplerAxis ν z i := by
  unfold keplerAxis
  rw [keplerEnergy_reflectPhase]

theorem keplerAction_reflectPhase : keplerAction ν (reflectPhase z) i = keplerAction ν z i := by
  unfold keplerAction
  rw [keplerAxis_reflectPhase]

theorem keplerEccVector_reflectPhase :
    keplerEccVector ν (reflectPhase z) i = reflectPlane (keplerEccVector ν z i) := by
  unfold keplerEccVector
  simp only [bodyVector_reflectPhase_fst, bodyVector_reflectPhase_snd, planeSq_reflectPlane,
    planeLength_reflectPlane, planeDot_reflectPlane, reflectPlane_sub, reflectPlane_smul]

theorem planeLength_keplerEccVector_reflectPhase :
    planeLength (keplerEccVector ν (reflectPhase z) i) = planeLength (keplerEccVector ν z i) := by
  rw [keplerEccVector_reflectPhase, planeLength_reflectPlane]

theorem planeCross_reflectPhase :
    planeCross (bodyVector (reflectPhase z).1 i) (bodyVector (reflectPhase z).2 i) =
      -planeCross (bodyVector z.1 i) (bodyVector z.2 i) := by
  rw [bodyVector_reflectPhase_fst, bodyVector_reflectPhase_snd, planeCross_reflectPlane]

theorem totalMomentum_reflectPhase : totalMomentum (reflectPhase z) = -totalMomentum z := by
  unfold totalMomentum
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => planeCross_reflectPhase z i

theorem strongAMD_reflectPhase : strongAMD ν (reflectPhase z) = strongAMD ν z := by
  unfold strongAMD
  rw [totalMomentum_reflectPhase, abs_neg]
  simp only [keplerAction_reflectPhase]

theorem noCollision_reflectVec_iff (q : Fin (n * 2) → ℝ) :
    NoCollision (reflectVec q) ↔ NoCollision q := by
  unfold NoCollision
  simp only [bodyVector_reflectVec, ← reflectPlane_sub, planeLength_reflectPlane]

theorem movingHamiltonian_reflectPhase (G m0 μ : ℝ) :
    movingHamiltonian G m0 ν μ (reflectPhase z) = movingHamiltonian G m0 ν μ z := by
  unfold movingHamiltonian
  simp only [bodyVector_reflectPhase_fst, bodyVector_reflectPhase_snd, planeSq_reflectPlane,
    planeLength_reflectPlane, planeDot_reflectPlane, ← reflectPlane_sub]

end Invariants

section ODE

/-- `reflectVec` as a continuous linear map. -/
def reflectVecCLM : (Fin (n * 2) → ℝ) →L[ℝ] (Fin (n * 2) → ℝ) :=
  ContinuousLinearMap.pi fun j => reflectSign j • ContinuousLinearMap.proj j

/-- `reflectPhase` as a continuous linear map. -/
def reflectPhaseCLM : Phase (n * 2) →L[ℝ] Phase (n * 2) :=
  (reflectVecCLM.comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (reflectVecCLM.comp (ContinuousLinearMap.snd ℝ _ _))

theorem reflectPhaseCLM_apply (z : Phase (n * 2)) :
    reflectPhaseCLM z = reflectPhase z := by
  refine Prod.ext ?_ ?_ <;> funext j <;> simp [reflectPhaseCLM, reflectVecCLM, reflectVec]

theorem reflectVec_single (i : Fin (n * 2)) :
    reflectVec (Pi.single i (1 : ℝ)) = reflectSign i • Pi.single i (1 : ℝ) := by
  funext j
  by_cases h : j = i
  · subst h; simp [reflectVec]
  · simp [reflectVec, h]

@[simp] theorem reflectVec_zero : reflectVec (0 : Fin (n * 2) → ℝ) = 0 := by
  funext j; simp [reflectVec]

theorem single_eq_reflectSign_smul (i : Fin (n * 2)) :
    (Pi.single i (1 : ℝ) : Fin (n * 2) → ℝ) = reflectSign i • reflectVec (Pi.single i (1 : ℝ)) := by
  rw [reflectVec_single, smul_smul, reflectSign_mul_self, one_smul]

theorem differentiableAt_reflectPhase {H : Phase (n * 2) → ℝ}
    (hH : ∀ w, H (reflectPhase w) = H w) {z : Phase (n * 2)} (hd : DifferentiableAt ℝ H z) :
    DifferentiableAt ℝ H (reflectPhase z) := by
  have e : (H ∘ reflectPhaseCLM) = H := funext fun w => by simp [reflectPhaseCLM_apply, hH]
  have h1 : DifferentiableAt ℝ H (reflectPhaseCLM (reflectPhase z)) := by
    rw [reflectPhaseCLM_apply, reflectPhase_reflectPhase]; exact hd
  have h2 := h1.comp (reflectPhase z) reflectPhaseCLM.differentiableAt
  rwa [e] at h2

/-- Equivariance of the Hamiltonian vector field of a reflection-invariant Hamiltonian. -/
theorem hamiltonianVectorField_reflectPhase {H : Phase (n * 2) → ℝ}
    (hH : ∀ w, H (reflectPhase w) = H w) {z : Phase (n * 2)} (hd : DifferentiableAt ℝ H z) :
    KAM.hamiltonianVectorField H (reflectPhase z) =
      reflectPhase (KAM.hamiltonianVectorField H z) := by
  have hd' := differentiableAt_reflectPhase hH hd
  have e : (H ∘ reflectPhaseCLM) = H := funext fun w => by simp [reflectPhaseCLM_apply, hH]
  have hd'' : DifferentiableAt ℝ H (reflectPhaseCLM z) := by
    rwa [reflectPhaseCLM_apply]
  have hchain : fderiv ℝ H z = (fderiv ℝ H (reflectPhase z)).comp reflectPhaseCLM := by
    have := fderiv_comp z hd'' reflectPhaseCLM.differentiableAt
    rw [e, reflectPhaseCLM.fderiv, reflectPhaseCLM_apply] at this
    exact this
  have key : ∀ v, fderiv ℝ H (reflectPhase z) (reflectPhase v) = fderiv ℝ H z v := fun v => by
    rw [hchain]; simp [reflectPhaseCLM_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · have he : ((0 : Fin (n * 2) → ℝ), (Pi.single i (1 : ℝ) : Fin (n * 2) → ℝ)) =
        reflectSign i • reflectPhase (0, Pi.single i 1) := by
      refine Prod.ext ?_ ?_
      · show (0 : Fin (n * 2) → ℝ) = reflectSign i • reflectVec 0
        simp
      · exact single_eq_reflectSign_smul i
    have h1 : fderiv ℝ H (reflectPhase z) (0, Pi.single i 1) =
        reflectSign i * fderiv ℝ H z (0, Pi.single i 1) := by
      calc fderiv ℝ H (reflectPhase z) (0, Pi.single i 1)
          = fderiv ℝ H (reflectPhase z) (reflectSign i • reflectPhase (0, Pi.single i 1)) := by
            rw [← he]
        _ = _ := by rw [map_smul, key, smul_eq_mul]
    simpa [KAM.hamiltonianVectorField, reflectVec] using h1
  · have he : ((Pi.single i (1 : ℝ) : Fin (n * 2) → ℝ), (0 : Fin (n * 2) → ℝ)) =
        reflectSign i • reflectPhase (Pi.single i 1, 0) := by
      refine Prod.ext ?_ ?_
      · exact single_eq_reflectSign_smul i
      · show (0 : Fin (n * 2) → ℝ) = reflectSign i • reflectVec 0
        simp
    have h1 : fderiv ℝ H (reflectPhase z) (Pi.single i 1, 0) =
        reflectSign i * fderiv ℝ H z (Pi.single i 1, 0) := by
      calc fderiv ℝ H (reflectPhase z) (Pi.single i 1, 0)
          = fderiv ℝ H (reflectPhase z) (reflectSign i • reflectPhase (Pi.single i 1, 0)) := by
            rw [← he]
        _ = _ := by rw [map_smul, key, smul_eq_mul]
    simp only [KAM.hamiltonianVectorField, reflectPhase_snd, reflectVec]
    rw [h1]; ring

/-- A moving solution reflects to a moving solution. -/
theorem isMovingSolutionOn_reflectPhase_of {ν : Fin n → ℝ} {μ : ℝ} {J : Set ℝ}
    {z : ℝ → Phase (n * 2)} (h : IsMovingSolutionOn ν μ J z) :
    IsMovingSolutionOn ν μ J (fun t => reflectPhase (z t)) := by
  obtain ⟨hs, hnc⟩ := h
  have hH : ∀ w, movingHamiltonian 1 1 ν μ (reflectPhase w) = movingHamiltonian 1 1 ν μ w :=
    fun w => movingHamiltonian_reflectPhase ν w 1 1 μ
  refine ⟨fun t ht => ⟨Set.mem_univ _, ?_, ?_⟩, fun t ht => ?_⟩
  · exact differentiableAt_reflectPhase hH (hs t ht).2.1
  · have h1 := reflectPhaseCLM.hasFDerivAt.comp_hasDerivAt t (hs t ht).2.2
    have e : (reflectPhaseCLM ∘ z) = fun t => reflectPhase (z t) :=
      funext fun t => reflectPhaseCLM_apply _
    rw [e, reflectPhaseCLM_apply, ← hamiltonianVectorField_reflectPhase hH (hs t ht).2.1] at h1
    exact h1
  · exact (noCollision_reflectVec_iff _).2 (hnc t ht)

/-- Orientation reversal preserves moving solutions (`LP:MAIN L3 (130–139)`, orientation remark). -/
theorem isMovingSolutionOn_reflectPhase_iff {ν : Fin n → ℝ} {μ : ℝ} {J : Set ℝ}
    {z : ℝ → Phase (n * 2)} :
    IsMovingSolutionOn ν μ J z ↔ IsMovingSolutionOn ν μ J (fun t => reflectPhase (z t)) := by
  refine ⟨isMovingSolutionOn_reflectPhase_of, fun h => ?_⟩
  have := isMovingSolutionOn_reflectPhase_of h
  simpa [reflectPhase_reflectPhase] using this

end ODE

end KAM.Planetary.StrongAMD

end
