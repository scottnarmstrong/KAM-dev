/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Canonical.Setting
public import KAM.Strip.RealRestriction
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import KAM.Frozen.Defs.SymplecticForm
public import KAM.Frozen.Defs.RealHamiltonian
public import KAM.Kepler.Basic

/-! # P11B tori: complex/real Hamiltonian-field bridges

Pure bridges used by `limit_torus`: one-variable Cauchy bound for a directional derivative,
the identity `dH(w) = -Ω(X_H, w)` for the complexified frozen form `Canonical.symplFormC`,
covariance `DΦ X_{G∘Φ} = X_G ∘ Φ` for a symplectic near-identity map, and the passage from the
complex Hamiltonian field to the frozen real field `hamiltonianVectorField` at real points.
-/

@[expose] public noncomputable section
open Set Real Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

section Cauchy

/-- One-variable Cauchy estimate for a directional derivative on a complex line. -/
theorem tori_cauchy_dir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ρ : E → ℂ}
    {z v : E} {r M : ℝ} (hr : 0 < r)
    (hd : ∀ w : ℂ, ‖w‖ ≤ r → DifferentiableAt ℂ ρ (z + w • v))
    (hM : ∀ w : ℂ, ‖w‖ = r → ‖ρ (z + w • v)‖ ≤ M) :
    ‖fderiv ℂ ρ z v‖ ≤ M / r := by
  set g : ℂ → ℂ := fun w => ρ (z + w • v) with hg
  have hgd : ∀ w : ℂ, ‖w‖ ≤ r → DifferentiableAt ℂ g w := fun w hw => by
    have h1 : HasDerivAt (fun w : ℂ => z + w • v) v w := by
      simpa using ((hasDerivAt_id w).smul_const v).const_add z
    exact (hd w hw).hasFDerivAt.comp_hasDerivAt w h1 |>.differentiableAt
  have hcl : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) r) := by
    refine ⟨fun w hw => (hgd w (by simpa using hw.out.le)).differentiableWithinAt,
      fun w hw => ?_⟩
    have : w ∈ Metric.closedBall (0 : ℂ) r := by
      rw [closure_ball _ hr.ne'] at hw; exact hw
    exact (hgd w (by simpa using this)).continuousAt.continuousWithinAt
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := 0) hr hcl
    (C := M) (fun w hw => by simpa [hg] using hM w (by simpa using hw))
  have h1 : HasDerivAt g (fderiv ℂ ρ z v) 0 := by
    have h1 : HasDerivAt (fun w : ℂ => z + w • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
    have := (hd 0 (by simpa using hr.le))
    have h2 := this.hasFDerivAt.comp_hasDerivAt (0 : ℂ) h1
    simp only [zero_smul, add_zero] at h2
    exact h2
  rw [h1.deriv] at h
  exact h

end Cauchy

section Symplectic
variable {n : ℕ}

theorem tori_symplFormC_nondeg {y : (Fin n → ℂ) × (Fin n → ℂ)}
    (h : ∀ w, Canonical.symplFormC y w = 0) : y = 0 := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · have := h (0, Pi.single i 1)
    simpa [Canonical.symplFormC, Pi.single_apply] using this
  · have := h (Pi.single i 1, 0)
    simpa [Canonical.symplFormC, Pi.single_apply] using this

theorem tori_clm_apply (L : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ℂ) (w : (Fin n → ℂ) × (Fin n → ℂ)) :
    L w = ∑ i, w.1 i * L (Pi.single i 1, 0) + ∑ i, w.2 i * L (0, Pi.single i 1) := by
  have h1 : w = ∑ i, w.1 i • ((Pi.single i 1 : Fin n → ℂ), (0 : Fin n → ℂ)) +
      ∑ i, w.2 i • ((0 : Fin n → ℂ), (Pi.single i 1 : Fin n → ℂ)) := by
    ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h1]
  have e1 : ∀ (a : ℂ) (e : Fin n → ℂ), L (a • e, 0) = a * L (e, 0) := fun a e => by
    have := L.map_smul a (e, 0)
    simpa using this
  have e2 : ∀ (a : ℂ) (e : Fin n → ℂ), L (0, a • e) = a * L (0, e) := fun a e => by
    have := L.map_smul a (0, e)
    simpa using this
  simp only [map_add, map_sum, Prod.smul_mk, smul_zero, e1, e2]

/-- `dH(w) = -Ω(X_H, w)` for the complexified frozen form. -/
theorem tori_fderiv_eq_symplFormC (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (z w : (Fin n → ℂ) × (Fin n → ℂ)) :
    fderiv ℂ H z w = - Canonical.symplFormC (hamiltonianVectorFieldℂ H z) w := by
  rw [tori_clm_apply (fderiv ℂ H z) w]
  simp only [Canonical.symplFormC, hamiltonianVectorFieldℂ, neg_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem tori_symplFormC_sub (u v w : (Fin n → ℂ) × (Fin n → ℂ)) :
    Canonical.symplFormC (u - v) w = Canonical.symplFormC u w - Canonical.symplFormC v w := by
  simp only [Canonical.symplFormC, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A near-identity continuous linear map of a finite-dimensional space is surjective. -/
theorem tori_surjective_of_near_id (T : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ]
    ((Fin n → ℂ) × (Fin n → ℂ)))
    (hT : ‖T - ContinuousLinearMap.id ℂ ((Fin n → ℂ) × (Fin n → ℂ))‖ < 1) :
    Function.Surjective T := by
  have hinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).2 fun v hv => ?_
    by_contra hne
    have hn : 0 < ‖v‖ := norm_pos_iff.2 hne
    have h1 : ‖v‖ = ‖(T - ContinuousLinearMap.id ℂ ((Fin n → ℂ) × (Fin n → ℂ))) v‖ := by
      simp [hv]
    have h2 := (T - ContinuousLinearMap.id ℂ ((Fin n → ℂ) × (Fin n → ℂ))).le_opNorm v
    nlinarith
  have : Function.Injective (T : ((Fin n → ℂ) × (Fin n → ℂ)) →ₗ[ℂ]
      ((Fin n → ℂ) × (Fin n → ℂ))) := hinj
  exact LinearMap.surjective_of_injective this

/-- Covariance of the complex Hamiltonian field under a symplectic near-identity map. -/
theorem tori_field_cov {Φ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {G : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hΦ : DifferentiableAt ℂ Φ z) (hG : DifferentiableAt ℂ G (Φ z))
    (hs : ∀ u v, Canonical.symplFormC (fderiv ℂ Φ z u) (fderiv ℂ Φ z v) =
      Canonical.symplFormC u v)
    (hsurj : Function.Surjective (fderiv ℂ Φ z)) :
    fderiv ℂ Φ z (hamiltonianVectorFieldℂ (G ∘ Φ) z) = hamiltonianVectorFieldℂ G (Φ z) := by
  have hc : fderiv ℂ (G ∘ Φ) z = (fderiv ℂ G (Φ z)).comp (fderiv ℂ Φ z) :=
    fderiv_comp z hG hΦ
  rw [← sub_eq_zero]
  refine tori_symplFormC_nondeg fun w' => ?_
  obtain ⟨w, rfl⟩ := hsurj w'
  rw [tori_symplFormC_sub, hs]
  have e1 := tori_fderiv_eq_symplFormC (G ∘ Φ) z w
  have e2 := tori_fderiv_eq_symplFormC G (Φ z) (fderiv ℂ Φ z w)
  rw [hc] at e1
  simp only [ContinuousLinearMap.comp_apply] at e1
  rw [e2] at e1
  linear_combination e1

end Symplectic

section Real
variable {n : ℕ}

theorem tori_phaseToC_eq (y : Phase n) : phaseToC y = KAM.realInclusion₂ n y := by
  ext i <;> simp [phaseToC]

end Real

end KAM.Planetary

end
