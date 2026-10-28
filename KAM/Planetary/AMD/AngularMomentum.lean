/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.AMD.MovingODE
public import KAM.Kepler.Plane
public import KAM.Planetary.Newtonian.Models
public import KAM.Frozen.Planetary.Defs.TotalMomentum
public import KAM.Frozen.Planetary.Defs.IsMovingSolutionOn

/-!
# AMD confinement: conservation of the total angular momentum

Blueprint `bpP:p14:ang-mom`. `interval_constancy` is the interval-local conservation wrapper (a
function with zero derivative at every point of an order-connected set is constant on it).
The ordered-pair cancellation `sum_mass_mul_cross_fKernel` is the action-reaction identity for the
planar cross product, and `ang_mom` combines the Hamilton equations of the moving system with it.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace KAM.Planetary

variable {n : ℕ}

theorem interval_constancy {J : Set ℝ} (hJ : J.OrdConnected)
    {f : ℝ → ℝ} (hf : ∀ t ∈ J, HasDerivAt f 0 t) :
    ∀ s ∈ J, ∀ t ∈ J, f t = f s := by
  have key : ∀ a ∈ J, ∀ b ∈ J, a ≤ b → f b = f a := by
    intro a ha b hb hab
    have hsub : Set.Icc a b ⊆ J := hJ.out ha hb
    exact constant_of_has_deriv_right_zero
      (fun x hx => (hf x (hsub hx)).continuousAt.continuousWithinAt)
      (fun x hx => (hf x (hsub (Set.Ico_subset_Icc_self hx))).hasDerivWithinAt) b
      ⟨hab, le_rfl⟩
  intro s hs t ht
  rcases le_total s t with h | h
  · exact key s hs t ht h
  · exact (key t ht s hs h).symm

/-- Ordered-pair cancellation: the internal forces exert no net torque. -/
theorem sum_mass_mul_cross_fKernel (m : Fin n → ℝ) (q : Fin n → Fin 2 → ℝ) :
    ∑ i, m i * planeCross (q i) (fKernel m q i) = 0 := by
  set g : Fin n → Fin n → ℝ := fun i j =>
    m i * (m j / planeLength (q j - q i) ^ 3) * planeCross (q i) (q j) with hg
  have hanti : ∀ i j, g j i = -g i j := by
    intro i j
    simp only [hg, planeCross]
    rw [planeLength_sub_comm (q i) (q j)]
    ring
  have hS : ∀ i, m i * planeCross (q i) (fKernel m q i) = ∑ j, g i j := by
    intro i
    unfold fKernel planeCross
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_filter_of_ne]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hg, planeCross]
      ring
    · intro j _ hj hji
      exact hj (by subst hji; simp)
  simp only [hS]
  have : ∑ i, ∑ j, g i j = -∑ i, ∑ j, g i j := by
    calc ∑ i, ∑ j, g i j = ∑ j, ∑ i, g i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -g j i :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => hanti j i
      _ = -∑ i, ∑ j, g i j := by simp [Finset.sum_neg_distrib]
  exact self_eq_neg.mp this

/-- The momentum-rate of one body's angular momentum along the moving vector field. -/
private theorem cross_rate_eq (m : Fin n → ℝ) (mu : ℝ) {z : Phase (n * 2)}
    (hz : NoCollision z.1) (i : Fin n) :
    planeCross (bodyVector (KAM.hamiltonianVectorField (movingHamiltonian 1 1 m mu) z).1 i)
        (bodyVector z.2 i) +
      planeCross (bodyVector z.1 i)
        (bodyVector (KAM.hamiltonianVectorField (movingHamiltonian 1 1 m mu) z).2 i) =
    mu * ((∑ j, bodyVector z.2 j 0) * bodyVector z.2 i 1 -
        (∑ j, bodyVector z.2 j 1) * bodyVector z.2 i 0) +
      mu * (m i * planeCross (bodyVector z.1 i)
        (fKernel m (fun j => bodyVector z.1 j) i)) := by
  have h0 := hamiltonianVectorField_moving 1 1 m mu hz i 0
  have h1 := hamiltonianVectorField_moving 1 1 m mu hz i 1
  have e0 : bodyVector (KAM.hamiltonianVectorField (movingHamiltonian 1 1 m mu) z).1 i 0 =
      bodyVector z.2 i 0 / m i + mu / 1 * ∑ j, bodyVector z.2 j 0 := h0.1
  have e1 : bodyVector (KAM.hamiltonianVectorField (movingHamiltonian 1 1 m mu) z).1 i 1 =
      bodyVector z.2 i 1 / m i + mu / 1 * ∑ j, bodyVector z.2 j 1 := h1.1
  have f0 : bodyVector (KAM.hamiltonianVectorField (movingHamiltonian 1 1 m mu) z).2 i 0 =
      -(1 * 1 * m i) * (((planeLength (bodyVector z.1 i)) ^ 3)⁻¹ * bodyVector z.1 i 0) +
      (mu * 1 * m i) * fKernel m (fun j => bodyVector z.1 j) i 0 := by
    have := h0.2
    simp only [gKernel, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have f1 : bodyVector (KAM.hamiltonianVectorField (movingHamiltonian 1 1 m mu) z).2 i 1 =
      -(1 * 1 * m i) * (((planeLength (bodyVector z.1 i)) ^ 3)⁻¹ * bodyVector z.1 i 1) +
      (mu * 1 * m i) * fKernel m (fun j => bodyVector z.1 j) i 1 := by
    have := h1.2
    simp only [gKernel, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this
  unfold planeCross
  rw [e0, e1, f0, f1]
  ring

theorem ang_mom {m : Fin n → ℝ} {mu : ℝ} {J : Set ℝ}
    (hJ : J.OrdConnected) {z : ℝ → Phase (n * 2)} (hz : IsMovingSolutionOn m mu J z) :
    ∀ s ∈ J, ∀ t ∈ J, totalMomentum (z t) = totalMomentum (z s) := by
  refine interval_constancy hJ (f := fun s => totalMomentum (z s)) fun t ht => ?_
  have hd := (hz.1 t ht).2.2
  have hnc := hz.2 t ht
  have hi : ∀ i : Fin n, HasDerivAt
      (fun s => planeCross (bodyVector (z s).1 i) (bodyVector (z s).2 i))
      (planeCross (bodyVector (KAM.hamiltonianVectorField (movingHamiltonian 1 1 m mu)
          (z t)).1 i) (bodyVector (z t).2 i) +
        planeCross (bodyVector (z t).1 i) (bodyVector (KAM.hamiltonianVectorField
          (movingHamiltonian 1 1 m mu) (z t)).2 i)) t := by
    intro i
    obtain ⟨hq, hp⟩ := hasDerivAt_bodyVector hd i
    have hq0 := hasDerivAt_pi.1 hq 0
    have hq1 := hasDerivAt_pi.1 hq 1
    have hp0 := hasDerivAt_pi.1 hp 0
    have hp1 := hasDerivAt_pi.1 hp 1
    refine ((hq0.mul hp1).sub (hq1.mul hp0)).congr_deriv ?_
    unfold planeCross
    ring
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hi i
  refine hsum.congr_deriv ?_
  simp only [cross_rate_eq m mu hnc, Finset.sum_add_distrib, ← Finset.mul_sum,
    mul_sub, Finset.sum_sub_distrib, sum_mass_mul_cross_fKernel]
  ring

end KAM.Planetary

end
