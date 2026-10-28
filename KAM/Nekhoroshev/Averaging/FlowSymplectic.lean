/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.Setting
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The real symplectic form: algebra, the Hessian identity, and the determinant

Helper module of `KAM.Nekhoroshev.Averaging.Flow` (blueprint N Part 12, `stepN:p12:fl-symp`).

* `KAM.Nekhoroshev.sympl`: `ω (a, w) = Σ (a₁ᵢ w₂ᵢ - a₂ᵢ w₁ᵢ)` on `ℝⁿ × ℝⁿ`; `sympl_hamField`:
  `ω (X_ℓ, w) = ℓ w`.
* `KAM.Nekhoroshev.sympl_fderiv_field_skew`: `DX_H (x)` is `ω`-skew when `H` is `C²` at `x`
  (symmetry of `D²H`).
* `KAM.Nekhoroshev.sympl_const_of_skew`: a solution of `Φ' = A Φ` with skew `A` preserves `ω`.
* `KAM.Nekhoroshev.det_eq_one_or_neg_one`: an `ω`-preserving linear map has determinant `±1`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Nekhoroshev

variable {n : ℕ}

/-- The standard symplectic form on `ℝⁿ × ℝⁿ`. -/
def sympl (a w : AvgPhase n) : ℝ := ∑ i, (a.1 i * w.2 i - a.2 i * w.1 i)

theorem sympl_add_left (a b w : AvgPhase n) : sympl (a + b) w = sympl a w + sympl b w := by
  simp only [sympl, Prod.fst_add, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sympl_smul_left (c : ℝ) (a w : AvgPhase n) : sympl (c • a) w = c * sympl a w := by
  simp only [sympl, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sympl_antisymm (a w : AvgPhase n) : sympl a w = - sympl w a := by
  simp only [sympl, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sympl_add_right (a b w : AvgPhase n) : sympl a (b + w) = sympl a b + sympl a w := by
  rw [sympl_antisymm, sympl_add_left, sympl_antisymm b, sympl_antisymm w]; ring

theorem sympl_smul_right (c : ℝ) (a w : AvgPhase n) : sympl a (c • w) = c * sympl a w := by
  rw [sympl_antisymm, sympl_smul_left, sympl_antisymm w]; ring

theorem sympl_eq_zero_of_forall {a : AvgPhase n} (h : ∀ w, sympl a w = 0) : a = 0 := by
  ext j
  · simpa [sympl, Pi.single_apply] using h (0, Pi.single j 1)
  · have := h (Pi.single j 1, 0)
    simpa [sympl, Pi.single_apply] using this

/-- A linear functional on `ℝⁿ × ℝⁿ` is determined by its values on the basis vectors. -/
theorem clm_apply_prod (L : AvgPhase n →L[ℝ] ℝ) (a b : Fin n → ℝ) :
    L (a, b) = ∑ i, a i * L (Pi.single i 1, 0) + ∑ i, b i * L (0, Pi.single i 1) := by
  have h1 : ((a, b) : AvgPhase n) =
      ∑ i, a i • ((Pi.single i 1 : Fin n → ℝ), (0 : Fin n → ℝ)) +
        ∑ i, b i • ((0 : Fin n → ℝ), (Pi.single i 1 : Fin n → ℝ)) := by
    ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h1]
  rw [map_add, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- `ω (X_ℓ, w) = ℓ w` for the Hamiltonian vector of a functional `ℓ`. -/
theorem sympl_hamField (ℓ : AvgPhase n →L[ℝ] ℝ) (w : AvgPhase n) :
    sympl ((fun i => ℓ (0, Pi.single i 1), fun i => -ℓ (Pi.single i 1, 0)) : AvgPhase n) w =
      ℓ w := by
  obtain ⟨a, b⟩ := w
  rw [clm_apply_prod, sympl, ← Finset.sum_add_distrib]
  simp only [neg_mul, sub_neg_eq_add]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The linearisation of a Hamiltonian field is `ω`-skew (symmetry of `D²H`). -/
theorem sympl_fderiv_field_skew {H : AvgPhase n → ℝ} {x : AvgPhase n}
    (hc : ContDiffAt ℝ 2 H x) (u w : AvgPhase n) :
    sympl (fderiv ℝ (KAM.hamiltonianVectorField H) x u) w +
      sympl u (fderiv ℝ (KAM.hamiltonianVectorField H) x w) = 0 := by
  have hD : DifferentiableAt ℝ (fderiv ℝ H) x :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  set D' := fderiv ℝ (fderiv ℝ H) x with hD'
  have hcomp : ∀ a : AvgPhase n,
      HasFDerivAt (fun z => fderiv ℝ H z a) ((ContinuousLinearMap.apply ℝ ℝ a).comp D') x :=
    fun a => (ContinuousLinearMap.apply ℝ ℝ a).hasFDerivAt.comp x hD.hasFDerivAt
  have hX : HasFDerivAt (KAM.hamiltonianVectorField H)
      ((ContinuousLinearMap.pi fun i =>
          (ContinuousLinearMap.apply ℝ ℝ (0, Pi.single i 1)).comp D').prod
        (ContinuousLinearMap.pi fun i =>
          -((ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1, 0)).comp D'))) x := by
    refine HasFDerivAt.prodMk ?_ ?_
    · exact hasFDerivAt_pi'.2 fun i => hcomp _
    · exact hasFDerivAt_pi'.2 fun i => (hcomp _).neg
  have key : ∀ v w : AvgPhase n, sympl (fderiv ℝ (KAM.hamiltonianVectorField H) x v) w = D' v w := by
    intro v w
    rw [hX.fderiv]
    exact sympl_hamField (D' v) w
  have hsymm : IsSymmSndFDerivAt ℝ H x := hc.isSymmSndFDerivAt (by simp)
  rw [sympl_antisymm u, key, key, hsymm u w]
  ring

/-- The product rule for `sympl` along curves. -/
theorem hasDerivAt_sympl {a b : ℝ → AvgPhase n} {a' b' : AvgPhase n} {τ : ℝ}
    (ha : HasDerivAt a a' τ) (hb : HasDerivAt b b' τ) :
    HasDerivAt (fun σ => sympl (a σ) (b σ)) (sympl a' (b τ) + sympl (a τ) b') τ := by
  have hfst : ∀ c : ℝ → AvgPhase n, ∀ c', HasDerivAt c c' τ →
      ∀ i, HasDerivAt (fun σ => (c σ).1 i) (c'.1 i) τ := fun c c' hc i =>
    hasDerivAt_pi.1 ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)).hasFDerivAt.comp_hasDerivAt
      τ hc) i
  have hsnd : ∀ c : ℝ → AvgPhase n, ∀ c', HasDerivAt c c' τ →
      ∀ i, HasDerivAt (fun σ => (c σ).2 i) (c'.2 i) τ := fun c c' hc i =>
    hasDerivAt_pi.1 ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)).hasFDerivAt.comp_hasDerivAt
      τ hc) i
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    ((hfst a a' ha i).mul (hsnd b b' hb i)).sub ((hsnd a a' ha i).mul (hfst b b' hb i))
  convert hsum using 1
  · funext σ
    simp [sympl]
  · simp only [sympl, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- A solution of `Φ' = A Φ` with `ω`-skew `A` preserves `ω` on a connected open interval. -/
theorem sympl_const_of_skew {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {Φ A : ℝ → AvgPhase n →L[ℝ] AvgPhase n}
    (hΦ : ∀ s ∈ I, HasDerivAt Φ ((A s).comp (Φ s)) s)
    (hA : ∀ s ∈ I, ∀ u w, sympl (A s u) w + sympl u (A s w) = 0) {s₀ : ℝ} (hs₀ : s₀ ∈ I)
    {s : ℝ} (hs : s ∈ I) (u w : AvgPhase n) :
    sympl (Φ s u) (Φ s w) = sympl (Φ s₀ u) (Φ s₀ w) := by
  have hd : ∀ s ∈ I, HasDerivAt (fun σ => sympl (Φ σ u) (Φ σ w)) 0 s := by
    intro s hs
    have h1 := (ContinuousLinearMap.apply ℝ (AvgPhase n) u).hasFDerivAt.comp_hasDerivAt s (hΦ s hs)
    have h2 := (ContinuousLinearMap.apply ℝ (AvgPhase n) w).hasFDerivAt.comp_hasDerivAt s (hΦ s hs)
    refine (hasDerivAt_sympl h1 h2).congr_deriv ?_
    simpa using hA s hs (Φ s u) (Φ s w)
  exact hI.is_const_of_deriv_eq_zero hIc (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) hs hs₀

/-- The bilinear form `sympl`. -/
def symplBilin (n : ℕ) : LinearMap.BilinForm ℝ (AvgPhase n) :=
  LinearMap.mk₂ ℝ sympl sympl_add_left
    (fun c a w => by rw [sympl_smul_left, smul_eq_mul])
    (fun m a b => sympl_add_right m a b)
    (fun c a w => by rw [sympl_smul_right, smul_eq_mul])

theorem symplBilin_apply (v w : AvgPhase n) : symplBilin n v w = sympl v w := by
  simp [symplBilin]

/-- A linear endomorphism preserving `sympl` has determinant `±1`. -/
theorem det_eq_one_or_neg_one (Y : AvgPhase n →ₗ[ℝ] AvgPhase n)
    (h : ∀ v w, sympl (Y v) (Y w) = sympl v w) :
    LinearMap.det Y = 1 ∨ LinearMap.det Y = -1 := by
  classical
  let b := (Pi.basisFun ℝ (Fin n)).prod (Pi.basisFun ℝ (Fin n))
  have hnd : (symplBilin n).Nondegenerate := by
    refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun x hx => ?_
    exact sympl_eq_zero_of_forall fun w => by simpa [symplBilin_apply] using hx w
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

end KAM.Nekhoroshev

end
