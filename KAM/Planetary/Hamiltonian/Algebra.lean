/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Defs.SymplecticForm
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Planetary.Defs.Phase

/-!
# Symplectic algebra on `Phase d`

`bpP:p1:conv#data` (the linear Hamiltonian field `X_ℓ`) and `bpP:p1:omega-algebra`: antisymmetry and
nondegeneracy of `Ω`, the identity `Ω(w, X_ℓ) = ℓ w`, and the consequences for conformally
symplectic linear maps (bijectivity, `|det A| = |c|^d`, `A X_{ℓ∘A} = c X_ℓ`). Matrices are avoided
in the statements; the determinant identity is proved through the Gram matrix of `Ω` in the product
basis.
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function

namespace KAM.Planetary

open KAM

section Algebra

variable {d : ℕ}

/-- `bpP:p1:conv#data`: `X_ℓ = ((ℓ(0, eᵢ))ᵢ, (-ℓ(eᵢ, 0))ᵢ)` for a linear form `ℓ`. -/
def linearField (ℓ : Phase d →L[ℝ] ℝ) : Phase d :=
  (fun i => ℓ (0, Pi.single i 1), fun i => -ℓ (Pi.single i 1, 0))

/-- `X_H(z) = X_{DH(z)}` (definitional; with Lean totality `X_H z = 0` off differentiability). -/
theorem hamiltonianVectorField_eq_linearField (H : Phase d → ℝ) (z : Phase d) :
    hamiltonianVectorField H z = linearField (fderiv ℝ H z) := rfl

/-- (a) `M₀ᵀ = -M₀` in bilinear form. -/
theorem symplecticForm_antisymm (v w : Phase d) : symplecticForm v w = -symplecticForm w v := by
  unfold symplecticForm
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- (a) nondegeneracy (in the second slot; the first-slot form is `eq_zero_of_symplecticForm`). -/
theorem eq_zero_of_symplecticForm_right {v : Phase d} (h : ∀ w, symplecticForm w v = 0) :
    v = 0 := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · have := h (0, Pi.single i 1)
    simpa [symplecticForm, Pi.single_apply] using this
  · have := h (Pi.single i 1, 0)
    simpa [symplecticForm, Pi.single_apply] using this

/-- Expansion of a linear form in the coordinate vectors. -/
private theorem apply_eq_sum (ℓ : Phase d →L[ℝ] ℝ) (w : Phase d) :
    ℓ w = ∑ i, (w.1 i * ℓ (Pi.single i 1, 0) + w.2 i * ℓ (0, Pi.single i 1)) := by
  have h1 : w = ∑ i, ((w.1 i) • ((Pi.single i 1 : Fin d → ℝ), (0 : Fin d → ℝ)) +
      (w.2 i) • ((0 : Fin d → ℝ), (Pi.single i 1 : Fin d → ℝ))) := by
    refine Prod.ext ?_ ?_
    · ext j
      simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · ext j
      simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h1]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- (a) `Ω(w, X_ℓ) = ℓ w`. -/
theorem symplecticForm_linearField (ℓ : Phase d →L[ℝ] ℝ) (w : Phase d) :
    symplecticForm w (linearField ℓ) = ℓ w := by
  rw [apply_eq_sum ℓ w]
  unfold symplecticForm linearField
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem symplecticForm_sub_right (u v w : Phase d) :
    symplecticForm u (v - w) = symplecticForm u v - symplecticForm u w := by
  simp only [symplecticForm, ← Finset.sum_sub_distrib, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- (a) uniqueness of `X_ℓ`. -/
theorem eq_linearField_iff (ℓ : Phase d →L[ℝ] ℝ) (v : Phase d) :
    (∀ w, symplecticForm w v = ℓ w) ↔ v = linearField ℓ := by
  constructor
  · intro h
    rw [← sub_eq_zero]
    refine eq_zero_of_symplecticForm_right fun w => ?_
    rw [symplecticForm_sub_right, h, symplecticForm_linearField, sub_self]
  · rintro rfl w
    exact symplecticForm_linearField ℓ w

/-- (a) last clause: `Ω(w, X_H z) = DH(z) w` for every `z` (both sides `0` off
differentiability). -/
theorem symplecticForm_hamiltonianVectorField (H : Phase d → ℝ) (z w : Phase d) :
    symplecticForm w (hamiltonianVectorField H z) = fderiv ℝ H z w :=
  symplecticForm_linearField _ w

/-- (b) a conformally symplectic matrix (`c ≠ 0`) is invertible. -/
theorem bijective_of_symplectic {c : ℝ} (hc : c ≠ 0) {A : Phase d →L[ℝ] Phase d}
    (hA : ∀ u v, symplecticForm (A u) (A v) = c * symplecticForm u v) : Bijective A := by
  have hinj : Injective (A : Phase d →ₗ[ℝ] Phase d) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    apply eq_zero_of_symplecticForm_right
    intro w
    have := hA w u
    have hu' : A u = 0 := hu
    rw [hu'] at this
    have h0 : symplecticForm (A w) (0 : Phase d) = 0 := by simp [symplecticForm]
    rw [h0] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hc
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The form `Ω` as a bilinear form. -/
private def omegaForm (d : ℕ) : LinearMap.BilinForm ℝ (Phase d) :=
  LinearMap.mk₂ ℝ symplecticForm
    (fun u v w => by
      simp only [symplecticForm, Prod.fst_add, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun a u w => by
      simp only [symplecticForm, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun u v w => by
      simp only [symplecticForm, Prod.fst_add, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun a u w => by
      simp only [symplecticForm, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)

private theorem omegaForm_apply (u v : Phase d) : omegaForm d u v = symplecticForm u v := rfl

private theorem omegaForm_nondegenerate : (omegaForm d).Nondegenerate := by
  refine ⟨fun u hu => ?_, fun v hv => ?_⟩
  · have : ∀ w, symplecticForm w u = 0 := fun w => by
      rw [symplecticForm_antisymm]; simpa [omegaForm_apply] using congrArg Neg.neg (hu w)
    exact eq_zero_of_symplecticForm_right this
  · exact eq_zero_of_symplecticForm_right fun w => hv w

/-- (b) `|det A| = |c|^d`. -/
theorem abs_det_of_symplectic {c : ℝ} (hc : c ≠ 0) {A : Phase d →L[ℝ] Phase d}
    (hA : ∀ u v, symplecticForm (A u) (A v) = c * symplecticForm u v) :
    |LinearMap.det (A : Phase d →ₗ[ℝ] Phase d)| = |c| ^ d := by
  let b : Module.Basis (Fin d ⊕ Fin d) ℝ (Phase d) :=
    (Pi.basisFun ℝ (Fin d)).prod (Pi.basisFun ℝ (Fin d))
  have hcomp : (omegaForm d).comp (A : Phase d →ₗ[ℝ] Phase d) (A : Phase d →ₗ[ℝ] Phase d) =
      c • omegaForm d :=
    LinearMap.BilinForm.ext fun u v => hA u v
  have hM := congrArg (LinearMap.BilinForm.toMatrix b) hcomp
  rw [LinearMap.BilinForm.toMatrix_comp b b, map_smul] at hM
  have hdet := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul,
    LinearMap.det_toMatrix] at hdet
  have hJ : (LinearMap.BilinForm.toMatrix b (omegaForm d)).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp omegaForm_nondegenerate
  have hsq : LinearMap.det (A : Phase d →ₗ[ℝ] Phase d) ^ 2 = (c ^ d) ^ 2 := by
    have h2 : (LinearMap.det (A : Phase d →ₗ[ℝ] Phase d) * (LinearMap.BilinForm.toMatrix b
        (omegaForm d)).det * LinearMap.det (A : Phase d →ₗ[ℝ] Phase d)) =
        c ^ (Fintype.card (Fin d ⊕ Fin d)) *
          (LinearMap.BilinForm.toMatrix b (omegaForm d)).det := by
      simpa using hdet
    simp only [Fintype.card_sum, Fintype.card_fin] at h2
    apply mul_right_cancel₀ hJ
    calc _ = _ := by ring
      _ = _ := h2
      _ = _ := by ring
  rw [← abs_pow]
  exact (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq

private theorem linearField_smul (c : ℝ) (ℓ : Phase d →L[ℝ] ℝ) :
    linearField (c • ℓ) = c • linearField ℓ := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [linearField]

/-- (b) `X_{ℓ∘A} = c A⁻¹ X_ℓ`, stated inverse-free: `A X_{ℓ∘A} = c X_ℓ`. -/
theorem apply_linearField_comp_of_symplectic {c : ℝ} (hc : c ≠ 0) {A : Phase d →L[ℝ] Phase d}
    (hA : ∀ u v, symplecticForm (A u) (A v) = c * symplecticForm u v) (ℓ : Phase d →L[ℝ] ℝ) :
    A (linearField (ℓ.comp A)) = c • linearField ℓ := by
  rw [← linearField_smul, ← eq_linearField_iff]
  intro w
  obtain ⟨w', rfl⟩ := (bijective_of_symplectic hc hA).2 w
  rw [hA, symplecticForm_linearField]
  simp

/-- (c) the chart condition does not depend on the sign of the form (CP09 prints `-Ω`). -/
theorem symplectic_neg_iff {c : ℝ} {A : Phase d →L[ℝ] Phase d} :
    (∀ u v, symplecticForm (A u) (A v) = c * symplecticForm u v) ↔
      ∀ u v, -symplecticForm (A u) (A v) = c * -symplecticForm u v := by
  simp only [mul_neg, neg_inj]

end Algebra

end KAM.Planetary

end
