/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.Setting
public import KAM.Strip.Regularity
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# The complexified symplectic form: algebra and the Hessian identity

Helper module of `KAM.Canonical.Symplectic` (blueprint-N Part 5, node
`bpN:p5:symplectic`).

* `KAM.Canonical.symplFormC_eq_of_left`: `symplFormC` is nondegenerate.
* `KAM.Canonical.symplFormC_hamiltonianJ`: `symplFormC (J ℓ) w = -ℓ w`.
* `KAM.Canonical.det_eq_one_or_neg_one`: a linear map preserving `symplFormC` has `det = ±1`.
* `KAM.Canonical.symplFormC_fderiv_field`: `symplFormC (DX_φ(x) u) w = -D²φ(x)(u, w)`; hence
  `DX_φ(x)` is `symplFormC`-skew (`symplFormC_fderiv_field_skew`), by the symmetry of `D²φ`.
* `KAM.Canonical.hasDerivAt_symplFormC`: the product rule for `symplFormC`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Canonical

variable {n : ℕ}

/-! ### Elementary algebra of `symplFormC` -/

theorem symplFormC_add_left (a b w : (Fin n → ℂ) × (Fin n → ℂ)) :
    symplFormC (a + b) w = symplFormC a w + symplFormC b w := by
  simp only [symplFormC, Prod.fst_add, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem symplFormC_smul_left (c : ℂ) (a w : (Fin n → ℂ) × (Fin n → ℂ)) :
    symplFormC (c • a) w = c * symplFormC a w := by
  simp only [symplFormC, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem symplFormC_neg_left (a w : (Fin n → ℂ) × (Fin n → ℂ)) :
    symplFormC (-a) w = - symplFormC a w := by
  simp only [symplFormC, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem symplFormC_antisymm (a w : (Fin n → ℂ) × (Fin n → ℂ)) :
    symplFormC a w = - symplFormC w a := by
  simp only [symplFormC, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem symplFormC_add_right (a b w : (Fin n → ℂ) × (Fin n → ℂ)) :
    symplFormC w (a + b) = symplFormC w a + symplFormC w b := by
  rw [symplFormC_antisymm, symplFormC_add_left, symplFormC_antisymm w a,
    symplFormC_antisymm w b]
  ring

theorem symplFormC_smul_right (c : ℂ) (a w : (Fin n → ℂ) × (Fin n → ℂ)) :
    symplFormC w (c • a) = c * symplFormC w a := by
  rw [symplFormC_antisymm, symplFormC_smul_left, symplFormC_antisymm w a]
  ring

theorem symplFormC_sub_left (a b w : (Fin n → ℂ) × (Fin n → ℂ)) :
    symplFormC (a - b) w = symplFormC a w - symplFormC b w := by
  rw [sub_eq_add_neg, symplFormC_add_left, symplFormC_neg_left]
  ring

/-- Nondegeneracy: a vector pairing to zero with everything is zero. -/
theorem symplFormC_eq_zero_of_forall {a : (Fin n → ℂ) × (Fin n → ℂ)}
    (h : ∀ w, symplFormC a w = 0) : a = 0 := by
  have h1 : ∀ i, a.2 i = 0 := fun i => by
    have := h (Pi.single i 1, 0)
    simpa [symplFormC, Pi.single_apply] using this
  have h2 : ∀ i, a.1 i = 0 := fun i => by
    have := h (0, Pi.single i 1)
    simpa [symplFormC, Pi.single_apply] using this
  exact Prod.ext (funext h2) (funext h1)

theorem symplFormC_eq_of_left {a b : (Fin n → ℂ) × (Fin n → ℂ)}
    (h : ∀ w, symplFormC a w = symplFormC b w) : a = b := by
  have : a - b = 0 := symplFormC_eq_zero_of_forall fun w => by
    rw [symplFormC_sub_left, h w, sub_self]
  exact sub_eq_zero.1 this

/-- A `ℂ`-linear functional on `ℂⁿ × ℂⁿ` is determined by its values on the basis vectors. -/
theorem clm_apply_prod' (L : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ℂ) (a b : Fin n → ℂ) :
    L (a, b) = ∑ i, a i * L (Pi.single i 1, 0) + ∑ i, b i * L (0, Pi.single i 1) := by
  have h1 : ((a, b) : (Fin n → ℂ) × (Fin n → ℂ)) =
      ∑ i, a i • ((Pi.single i 1 : Fin n → ℂ), (0 : Fin n → ℂ)) +
        ∑ i, b i • ((0 : Fin n → ℂ), (Pi.single i 1 : Fin n → ℂ)) := by
    ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h1]
  rw [map_add, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- `symplFormC (J ℓ) w = -ℓ w`. -/
theorem symplFormC_hamiltonianJ (ℓ : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ℂ)
    (w : (Fin n → ℂ) × (Fin n → ℂ)) : symplFormC (KAM.hamiltonianJ ℓ) w = - ℓ w := by
  obtain ⟨a, b⟩ := w
  rw [clm_apply_prod', symplFormC, KAM.hamiltonianJ, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp; ring

/-! ### The determinant -/

/-- The bilinear form `symplFormC`. -/
def symplBilin (n : ℕ) : LinearMap.BilinForm ℂ ((Fin n → ℂ) × (Fin n → ℂ)) :=
  LinearMap.mk₂ ℂ symplFormC symplFormC_add_left
    (fun c a w => by rw [symplFormC_smul_left, smul_eq_mul])
    (fun m a b => symplFormC_add_right a b m)
    (fun c a w => by rw [symplFormC_smul_right, smul_eq_mul])

theorem symplBilin_apply (v w : (Fin n → ℂ) × (Fin n → ℂ)) :
    symplBilin n v w = symplFormC v w := by simp [symplBilin]

/-- A `ℂ`-linear endomorphism preserving `symplFormC` has determinant `±1`. -/
theorem det_eq_one_or_neg_one (Y : ((Fin n → ℂ) × (Fin n → ℂ)) →ₗ[ℂ] ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : ∀ v w, symplFormC (Y v) (Y w) = symplFormC v w) :
    LinearMap.det Y = 1 ∨ LinearMap.det Y = -1 := by
  classical
  let b := (Pi.basisFun ℂ (Fin n)).prod (Pi.basisFun ℂ (Fin n))
  have hnd : (symplBilin n).Nondegenerate := by
    refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun x hx => ?_
    exact symplFormC_eq_zero_of_forall fun w => by simpa [symplBilin_apply] using hx w
  have hdet : (LinearMap.BilinForm.toMatrix b (symplBilin n)).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hnd
  have hcomp : (symplBilin n).comp Y Y = symplBilin n := by
    refine LinearMap.ext₂ fun v w => ?_
    simpa [symplBilin_apply] using h v w
  have hm := LinearMap.BilinForm.toMatrix_comp b b (symplBilin n) Y Y
  rw [hcomp] at hm
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at hd
  have : LinearMap.det Y * LinearMap.det Y = 1 := by
    have h2 : (LinearMap.BilinForm.toMatrix b (symplBilin n)).det *
        (LinearMap.det Y * LinearMap.det Y) =
        (LinearMap.BilinForm.toMatrix b (symplBilin n)).det * 1 := by
      rw [mul_one]
      calc _ = LinearMap.det Y * (LinearMap.BilinForm.toMatrix b (symplBilin n)).det *
            LinearMap.det Y := by ring
        _ = _ := hd.symm
    exact mul_left_cancel₀ hdet h2
  exact mul_self_eq_one_iff.1 this

/-- A `symplFormC`-preserving map intertwines `J (η ∘ Y)` and `J η`: `Y J (η ∘ Y) = J η`. -/
theorem map_hamiltonianJ_comp (Y : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ)))
    (hY : ∀ v w, symplFormC (Y v) (Y w) = symplFormC v w)
    (η : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ℂ) :
    Y (KAM.hamiltonianJ (η.comp Y)) = KAM.hamiltonianJ η := by
  have hinj : Function.Injective
      ((Y : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))) :
        ((Fin n → ℂ) × (Fin n → ℂ)) →ₗ[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))) := by
    intro a b hab
    refine symplFormC_eq_of_left fun w => ?_
    rw [← hY a w, ← hY b w]
    have : Y a = Y b := hab
    rw [this]
  obtain ⟨w', hw'⟩ := LinearMap.surjective_of_injective hinj (KAM.hamiltonianJ η)
  have hw'' : Y w' = KAM.hamiltonianJ η := hw'
  have : KAM.hamiltonianJ (η.comp Y) = w' := by
    refine symplFormC_eq_of_left fun w => ?_
    rw [symplFormC_hamiltonianJ, ← hY w' w, hw'', symplFormC_hamiltonianJ]
    simp
  rw [this, hw'']

/-! ### The Hessian identity -/

/-- The product rule for `symplFormC` along curves. -/
theorem hasDerivAt_symplFormC {a b : ℝ → (Fin n → ℂ) × (Fin n → ℂ)}
    {a' b' : (Fin n → ℂ) × (Fin n → ℂ)} {τ : ℝ} (ha : HasDerivAt a a' τ)
    (hb : HasDerivAt b b' τ) :
    HasDerivAt (fun σ => symplFormC (a σ) (b σ))
      (symplFormC a' (b τ) + symplFormC (a τ) b') τ := by
  have hfst : ∀ c : ℝ → (Fin n → ℂ) × (Fin n → ℂ), ∀ c', HasDerivAt c c' τ →
      ∀ i, HasDerivAt (fun σ => (c σ).1 i) (c'.1 i) τ := fun c c' hc i =>
    hasDerivAt_pi.1 ((ContinuousLinearMap.fst ℝ (Fin n → ℂ) (Fin n → ℂ)).hasFDerivAt.comp_hasDerivAt
      τ hc) i
  have hsnd : ∀ c : ℝ → (Fin n → ℂ) × (Fin n → ℂ), ∀ c', HasDerivAt c c' τ →
      ∀ i, HasDerivAt (fun σ => (c σ).2 i) (c'.2 i) τ := fun c c' hc i =>
    hasDerivAt_pi.1 ((ContinuousLinearMap.snd ℝ (Fin n → ℂ) (Fin n → ℂ)).hasFDerivAt.comp_hasDerivAt
      τ hc) i
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    ((hsnd a a' ha i).mul (hfst b b' hb i)).sub ((hfst a a' ha i).mul (hsnd b b' hb i))
  convert hsum using 1
  · funext σ
    simp [symplFormC]
  · simp only [symplFormC, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- The derivative of a Hamiltonian field: `symplFormC (DX_φ(x) u) w = -D²φ(x)(u, w)`. -/
theorem symplFormC_fderiv_field {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U)
    {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hφ : DifferentiableOn ℂ φ U)
    {x : (Fin n → ℂ) × (Fin n → ℂ)} (hx : x ∈ U) (u w : (Fin n → ℂ) × (Fin n → ℂ)) :
    symplFormC (fderiv ℂ (KAM.hamiltonianVectorFieldℂ φ) x u) w =
      - fderiv ℂ (fderiv ℂ φ) x u w := by
  have hD : DifferentiableAt ℂ (fderiv ℂ φ) x :=
    ((KAM.holomorphic_regularity_of_finiteDimensional hU hφ).1.differentiableAt (hU.mem_nhds hx))
  set D' := fderiv ℂ (fderiv ℂ φ) x with hD'
  have hcomp : ∀ a : (Fin n → ℂ) × (Fin n → ℂ),
      HasFDerivAt (fun z => fderiv ℂ φ z a) ((ContinuousLinearMap.apply ℂ ℂ a).comp D') x :=
    fun a => (ContinuousLinearMap.apply ℂ ℂ a).hasFDerivAt.comp x hD.hasFDerivAt
  have hX : HasFDerivAt (KAM.hamiltonianVectorFieldℂ φ)
      ((ContinuousLinearMap.pi fun i =>
          (ContinuousLinearMap.apply ℂ ℂ (0, Pi.single i 1)).comp D').prod
        (ContinuousLinearMap.pi fun i =>
          -((ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1, 0)).comp D'))) x := by
    refine HasFDerivAt.prodMk ?_ ?_
    · exact hasFDerivAt_pi'.2 fun i => hcomp _
    · exact hasFDerivAt_pi'.2 fun i => (hcomp _).neg
  rw [hX.fderiv]
  simp only [symplFormC, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.apply_apply,
    neg_apply]
  obtain ⟨a, b⟩ := w
  rw [clm_apply_prod' (D' u), ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only; ring

/-- `D²φ(x)` is symmetric for holomorphic `φ`. -/
theorem fderiv_fderiv_symm {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U)
    {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hφ : DifferentiableOn ℂ φ U)
    {x : (Fin n → ℂ) × (Fin n → ℂ)} (hx : x ∈ U) (u w : (Fin n → ℂ) × (Fin n → ℂ)) :
    fderiv ℂ (fderiv ℂ φ) x u w = fderiv ℂ (fderiv ℂ φ) x w u := by
  have hc : ContDiffAt ℂ 2 φ x :=
    ((KAM.contDiffOn_infty_of_differentiableOn hU hφ).contDiffAt (hU.mem_nhds hx)).of_le
      ((by norm_num : (2 : WithTop ℕ∞) ≤ 2).trans (WithTop.coe_le_coe.2 le_top))
  exact (hc.isSymmSndFDerivAt (by simp)) u w

/-- The linearisation of a Hamiltonian field is `symplFormC`-skew:
`ω(DX_φ(x) u, w) + ω(u, DX_φ(x) w) = 0`. -/
theorem symplFormC_fderiv_field_skew {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U)
    {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hφ : DifferentiableOn ℂ φ U)
    {x : (Fin n → ℂ) × (Fin n → ℂ)} (hx : x ∈ U) (u w : (Fin n → ℂ) × (Fin n → ℂ)) :
    symplFormC (fderiv ℂ (KAM.hamiltonianVectorFieldℂ φ) x u) w +
      symplFormC u (fderiv ℂ (KAM.hamiltonianVectorFieldℂ φ) x w) = 0 := by
  rw [symplFormC_antisymm u, symplFormC_fderiv_field hU hφ hx,
    symplFormC_fderiv_field hU hφ hx, fderiv_fderiv_symm hU hφ hx u w]
  ring

end KAM.Canonical

end
