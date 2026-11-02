/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.ODE.Hamiltonian
public import KAM.Frozen.Defs.SymplecticForm
public import KAM.Frozen.Defs.HamiltonianVectorField
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Symplectic chart transport and observable transfer (track B, package B1-TRANSFER)

* `symplecticForm_hamiltonianVectorField`: `ω (X_H z) v = - dH(z) v`; `symplecticForm_nondegenerate`.
* `bijective_of_symplectic`: symplectic linear maps are bijective.
* `fderiv_apply_hamiltonianVectorField_comp`: `DΨ X_{H∘Ψ} = X_H ∘ Ψ` for a symplectic chart `Ψ`;
  `hasDerivAt_comp_chart` is the curve version.
* `contDiffOn_hamiltonianVectorField`: `C²` Hamiltonians have `C¹` vector fields.
* `observable_transfer_bound`: the algebraic core of observable transfer.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open KAM

variable {n : ℕ}

private theorem clm_fst_eq (ℓ : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] ℝ) (a : Fin n → ℝ) :
    ℓ (a, 0) = ∑ i, a i * ℓ (Pi.single i 1, 0) := by
  have : ((a, 0) : (Fin n → ℝ) × (Fin n → ℝ)) = ∑ i, a i • ((Pi.single i 1 : Fin n → ℝ), 0) := by
    ext j
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  rw [this, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]

private theorem clm_snd_eq (ℓ : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] ℝ) (b : Fin n → ℝ) :
    ℓ (0, b) = ∑ i, b i * ℓ (0, Pi.single i 1) := by
  have : ((0, b) : (Fin n → ℝ) × (Fin n → ℝ)) = ∑ i, b i • ((0 : Fin n → ℝ), Pi.single i 1) := by
    ext j
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [this, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]

/-- `ω (X_H z) v = - dH(z) v`. -/
theorem symplecticForm_hamiltonianVectorField (H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (z v : (Fin n → ℝ) × (Fin n → ℝ)) :
    symplecticForm (hamiltonianVectorField H z) v = - fderiv ℝ H z v := by
  have hv : v = (v.1, 0) + (0, v.2) := by ext <;> simp
  conv_rhs => rw [hv, map_add, clm_fst_eq, clm_snd_eq]
  simp only [symplecticForm, hamiltonianVectorField]
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The standard symplectic form is nondegenerate. -/
theorem symplecticForm_nondegenerate {u : (Fin n → ℝ) × (Fin n → ℝ)}
    (h : ∀ v, symplecticForm u v = 0) : u = 0 := by
  ext i
  · have := h (0, Pi.single i 1)
    simpa [symplecticForm, Pi.single_apply] using this
  · have := h (Pi.single i 1, 0)
    simpa [symplecticForm, Pi.single_apply] using this

/-- Symplectic linear maps are bijective. -/
theorem bijective_of_symplectic {L : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) × (Fin n → ℝ)}
    (h : ∀ u v, symplecticForm (L u) (L v) = symplecticForm u v) : Function.Bijective L := by
  have hinj : Function.Injective L.toLinearMap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    refine symplecticForm_nondegenerate fun v => ?_
    rw [← h]
    have : L u = 0 := hu
    simp [this, symplecticForm]
  exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩

/-- Chart transport: a symplectic chart intertwines Hamiltonian vector fields. -/
theorem fderiv_apply_hamiltonianVectorField_comp {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {Ψ : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} {w : (Fin n → ℝ) × (Fin n → ℝ)}
    (hH : DifferentiableAt ℝ H (Ψ w)) (hΨ : DifferentiableAt ℝ Ψ w)
    (hsymp : ∀ u v, KAM.symplecticForm (fderiv ℝ Ψ w u) (fderiv ℝ Ψ w v) = KAM.symplecticForm u v) :
    fderiv ℝ Ψ w (KAM.hamiltonianVectorField (H ∘ Ψ) w) = KAM.hamiltonianVectorField H (Ψ w) := by
  obtain ⟨-, hsurj⟩ := bijective_of_symplectic hsymp
  have hd : fderiv ℝ (H ∘ Ψ) w = (fderiv ℝ H (Ψ w)).comp (fderiv ℝ Ψ w) :=
    fderiv_comp w hH hΨ
  have := symplecticForm_nondegenerate (u := fderiv ℝ Ψ w (KAM.hamiltonianVectorField (H ∘ Ψ) w) -
    KAM.hamiltonianVectorField H (Ψ w)) fun v => by
    obtain ⟨u, rfl⟩ := hsurj v
    have e1 := symplecticForm_hamiltonianVectorField (H ∘ Ψ) w u
    have e2 := symplecticForm_hamiltonianVectorField H (Ψ w) (fderiv ℝ Ψ w u)
    have e3 := hsymp (KAM.hamiltonianVectorField (H ∘ Ψ) w) u
    rw [hd] at e1
    simp only [ContinuousLinearMap.comp_apply] at e1
    unfold symplecticForm at e1 e2 e3 ⊢
    simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      at *
    linarith
  exact sub_eq_zero.1 this

/-- Curve version of chart transport. -/
theorem hasDerivAt_comp_chart {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {Ψ : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    {c : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} {t : ℝ}
    (hc : HasDerivAt c (KAM.hamiltonianVectorField (H ∘ Ψ) (c t)) t)
    (hΨ : DifferentiableAt ℝ Ψ (c t)) (hH : DifferentiableAt ℝ H (Ψ (c t)))
    (hsymp : ∀ u v, KAM.symplecticForm (fderiv ℝ Ψ (c t) u) (fderiv ℝ Ψ (c t) v) =
      KAM.symplecticForm u v) :
    HasDerivAt (Ψ ∘ c) (KAM.hamiltonianVectorField H (Ψ (c t))) t := by
  have := hΨ.hasFDerivAt.comp_hasDerivAt t hc
  rwa [fderiv_apply_hamiltonianVectorField_comp hH hΨ hsymp] at this

/-- `C²` Hamiltonians have `C¹` Hamiltonian vector fields. -/
theorem contDiffOn_hamiltonianVectorField {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {V : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hH : ContDiffOn ℝ 2 H V) (hV : IsOpen V) :
    ContDiffOn ℝ 1 (KAM.hamiltonianVectorField H) V :=
  KAM.ODE.ham_smooth_c1 hV hH

/-- Observable transfer: the algebraic core. -/
theorem observable_transfer_bound {m : ℕ} (A : (Fin n → ℝ) × (Fin n → ℝ) → Fin m → ℝ)
    (L : Matrix (Fin m) (Fin n) ℝ) (d : Fin m → ℝ) (η : Fin n → ℝ) (t : ℝ)
    (x₀ x : (Fin n → ℝ) × (Fin n → ℝ)) (J₀ J : Fin n → ℝ)
    (h₀ : ∀ i, |A x₀ i - (L.mulVec J₀) i| ≤ d i) (h : ∀ i, |A x i - (L.mulVec J) i| ≤ d i)
    (hJ : ∀ j, |J j - J₀ j| ≤ η j * |t|) :
    ∀ i, |A x i - A x₀ i| ≤ 2 * d i + |t| * ∑ j, |L i j| * η j := by
  intro i
  have hm : |(L.mulVec J) i - (L.mulVec J₀) i| ≤ |t| * ∑ j, |L i j| * η j := by
    have : (L.mulVec J) i - (L.mulVec J₀) i = ∑ j, L i j * (J j - J₀ j) := by
      simp [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
    rw [this, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    calc |L i j| * |J j - J₀ j| ≤ |L i j| * (η j * |t|) := by gcongr; exact hJ j
      _ = |t| * (|L i j| * η j) := by ring
  have a1 := h i
  have a2 := h₀ i
  rw [abs_le] at a1 a2 hm ⊢
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, hm.1, hm.2]

end KAM.EffectiveStability

end
