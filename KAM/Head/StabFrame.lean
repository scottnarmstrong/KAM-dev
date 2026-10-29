/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Unperturbed
public import KAM.Head.Parameters
import KAM.Apost.PerturbationTorsion
import KAM.Apost.Identities
import KAM.Strip.HigherCauchy

/-!
# STAB, the frame side: the tangent frame, the Gram matrix and the normal frame of a nearby torus

Blueprint Part 4, `bp:p4:stab` (internal module of `KAM/Head/Stab.lean`), steps
`step:p4:stab-small`, `step:p4:stab-cauchy`, `step:p4:stab-gram` and `step:p4:stab-frame`.
Let `K` be holomorphic on `T_ρ` with `|K - K⁰_{I_*}| ≤ η` there, `0 < δ`, and put `L = DK`,
`G = LᵀL`, `B = G⁻¹`, `N = Ω₀ L B`, `a = n η / δ`. All matrices carry the row-sum operator norm.

* `KAM.Head.Stab.eta_small` (`step:p4:stab-small`): `η ≤ η_*(δ)` gives `c_T η δ⁻² ≤ 1/(16 L₊)` and
  `12 n a ≤ 1`.
* `KAM.Head.Stab.tangent_close` (`step:p4:stab-cauchy`): `|L - L⁰| ≤ a` and `|(L - L⁰)ᵀ| ≤ 2 n η/δ`
  on `T_{ρ-δ}` (the Cauchy estimate for `K - K⁰`).
* `KAM.Head.Stab.norm_dL_le` (`step:p4:stab-cauchy`): `|∂_ω L| ≤ 4 n W η δ⁻²` on `T_{ρ-δ}` for
  `|ω| ≤ W`. The second derivative of `K` is that of `K - K⁰`, since `K⁰` is affine, and
  `KAM.norm_iteratedFDeriv_two_le_of_mem_complexStrip` bounds it by `4 η δ⁻²`. This is sharper than
  the blueprint's `b = 4 n² W η δ⁻²`.
* `KAM.Head.Stab.norm_gram_sub_one_le`, `KAM.Head.Stab.gram_inv` (`step:p4:stab-gram`):
  `|G - Id| ≤ 5 n a`, `G` invertible, `|G⁻¹| ≤ 2`, `|G⁻¹ - Id| ≤ 10 n a`.
* `KAM.Head.Stab.norm_normal_sub_le`, `KAM.Head.Stab.norm_dN_le` (`step:p4:stab-frame`):
  `|N - N⁰| ≤ 12 n a`, and `|∂_ω N| ≤ 66 n b` from `|∂_ω L| ≤ b`.
* `KAM.Head.Stab.frame_basic` and `KAM.Head.Stab.frame_deriv` collect these on the strip.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology KAM.Torus

namespace KAM.Head

namespace Stab

variable {n : ℕ}

/-- `(L⁰)ᵀ L⁰ = Id`. -/
theorem frameL0_transpose_mul_self : (frameL0 n)ᵀ * frameL0 n = 1 := by
  unfold frameL0
  rw [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows]
  simp

/-- Gram matrix: `‖LᵀL - Id‖ ≤ 5 n a`. -/
theorem norm_gram_sub_one_le (hn : 0 < n) {L : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ} {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hD : ‖L - frameL0 n‖ ≤ a)
    (hDt : ‖(L - frameL0 n)ᵀ‖ ≤ 2 * n * a) : ‖Lᵀ * L - 1‖ ≤ 5 * n * a := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set D := L - frameL0 n with hDdef
  have hL : L = frameL0 n + D := by rw [hDdef]; abel
  have key : Lᵀ * L - 1 = (frameL0 n)ᵀ * D + Dᵀ * frameL0 n + Dᵀ * D := by
    rw [hL, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      frameL0_transpose_mul_self]
    abel
  have h1 : ‖(frameL0 n)ᵀ * D‖ ≤ a := by
    calc _ ≤ ‖(frameL0 n)ᵀ‖ * ‖D‖ := Matrix.linfty_opNorm_mul _ _
      _ ≤ 1 * a := by rw [norm_frameL0_transpose hn]; gcongr
      _ = a := one_mul a
  have h2 : ‖Dᵀ * frameL0 n‖ ≤ 2 * n * a := by
    calc _ ≤ ‖Dᵀ‖ * ‖frameL0 n‖ := Matrix.linfty_opNorm_mul _ _
      _ ≤ 2 * n * a * 1 := by rw [norm_frameL0 hn]; gcongr
      _ = 2 * n * a := mul_one _
  have h3 : ‖Dᵀ * D‖ ≤ 2 * n * a * a := by
    calc _ ≤ ‖Dᵀ‖ * ‖D‖ := Matrix.linfty_opNorm_mul _ _
      _ ≤ 2 * n * a * a := by gcongr
  rw [key]
  calc _ ≤ ‖(frameL0 n)ᵀ * D + Dᵀ * frameL0 n‖ + ‖Dᵀ * D‖ := norm_add_le _ _
    _ ≤ ‖(frameL0 n)ᵀ * D‖ + ‖Dᵀ * frameL0 n‖ + ‖Dᵀ * D‖ := by gcongr; exact norm_add_le _ _
    _ ≤ a + 2 * n * a + 2 * n * a * a := by gcongr
    _ ≤ 5 * n * a := by
        nlinarith [mul_nonneg ha0 (sub_nonneg.2 ha1), mul_nonneg ha0 (sub_nonneg.2 hn1)]


/-- Neumann step for the Gram matrix. -/
theorem gram_inv (hn : 0 < n) {G : Matrix (Fin n) (Fin n) ℂ} {a : ℝ}
    (h12 : 12 * n * a ≤ 1) (hG : ‖G - 1‖ ≤ 5 * n * a) :
    IsUnit G ∧ ‖G⁻¹‖ ≤ 2 ∧ ‖G⁻¹ - 1‖ ≤ 10 * n * a := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) ℂ)⁻¹‖ = 1 := by
    rw [inv_one]; exact unperturbed_norm_one hn
  have hsm : ‖(1 : Matrix (Fin n) (Fin n) ℂ)⁻¹‖ * ‖G - 1‖ ≤ 1 / 2 := by
    rw [h1, one_mul]; nlinarith
  have hG' : (1 : Matrix (Fin n) (Fin n) ℂ) + (G - 1) = G := add_sub_cancel _ _
  have e1 := KAM.matrix_isUnit_add_of_inv_norm_mul_le_half (isUnit_one) hsm
  have e2 := KAM.matrix_norm_inv_add_le (isUnit_one) hsm
  have e3 := KAM.matrix_norm_inv_add_sub_inv_le (isUnit_one) hsm
  rw [hG'] at e1 e2 e3
  rw [h1] at e2 e3
  refine ⟨e1, by linarith, ?_⟩
  rw [inv_one] at e3
  calc _ ≤ 2 * 1 ^ 2 * ‖G - 1‖ := e3
    _ ≤ 10 * n * a := by nlinarith

/-- The normal frame: `‖Ω₀ L B - N⁰‖ ≤ 12 n a`. -/
theorem norm_normal_sub_le (hn : 0 < n) {L : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ}
    {B : Matrix (Fin n) (Fin n) ℂ} {a : ℝ} (ha0 : 0 ≤ a) (hD : ‖L - frameL0 n‖ ≤ a)
    (hB : ‖B‖ ≤ 2) (hB1 : ‖B - 1‖ ≤ 10 * n * a) :
    ‖omegaZeroMatrix n * L * B - frameN0 n‖ ≤ 12 * n * a := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have key : omegaZeroMatrix n * L * B - frameN0 n =
      omegaZeroMatrix n * ((L - frameL0 n) * B + frameL0 n * (B - 1)) := by
    rw [← omegaZeroMatrix_mul_frameL0]
    simp only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one]
    abel
  rw [key, norm_omegaZeroMatrix_mul]
  calc _ ≤ ‖(L - frameL0 n) * B‖ + ‖frameL0 n * (B - 1)‖ := norm_add_le _ _
    _ ≤ a * 2 + 1 * (10 * n * a) := by
        gcongr
        · exact (Matrix.linfty_opNorm_mul _ _).trans (by gcongr)
        · refine (Matrix.linfty_opNorm_mul _ _).trans ?_
          rw [norm_frameL0 hn]; gcongr
    _ ≤ 12 * n * a := by nlinarith [mul_nonneg ha0 (sub_nonneg.2 hn1)]

/-- The directional derivative of the normal frame, from the derivative of the tangent frame. -/
theorem norm_dN_le (hn : 0 < n) {L dL : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ}
    {B dG dB : Matrix (Fin n) (Fin n) ℂ} {b : ℝ} (hL : ‖L‖ ≤ 2) (hB : ‖B‖ ≤ 2)
    (hdL : ‖dL‖ ≤ b) (hdG : dG = dLᵀ * L + Lᵀ * dL) (hdB : dB = -(B * dG * B)) :
    ‖omegaZeroMatrix n * dL * B + omegaZeroMatrix n * L * dB‖ ≤ 66 * n * b := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb0 : 0 ≤ b := (norm_nonneg _).trans hdL
  have hLt : ‖Lᵀ‖ ≤ 2 * n * 2 :=
    (KAM.Apost.FrameAux.norm_transpose_le_two_mul L).trans (by gcongr)
  have hdLt : ‖dLᵀ‖ ≤ 2 * n * b :=
    (KAM.Apost.FrameAux.norm_transpose_le_two_mul dL).trans (by gcongr)
  have hdG' : ‖dG‖ ≤ 8 * n * b := by
    rw [hdG]
    calc _ ≤ ‖dLᵀ * L‖ + ‖Lᵀ * dL‖ := norm_add_le _ _
      _ ≤ 2 * n * b * 2 + 2 * n * 2 * b := by
          gcongr
          · exact (Matrix.linfty_opNorm_mul _ _).trans (by gcongr)
          · exact (Matrix.linfty_opNorm_mul _ _).trans (by gcongr)
      _ = 8 * n * b := by ring
  have hdB' : ‖dB‖ ≤ 32 * n * b := by
    rw [hdB, norm_neg]
    calc _ ≤ ‖B * dG‖ * ‖B‖ := Matrix.linfty_opNorm_mul _ _
      _ ≤ (‖B‖ * ‖dG‖) * ‖B‖ := by gcongr; exact Matrix.linfty_opNorm_mul _ _
      _ ≤ (2 * (8 * n * b)) * 2 := by gcongr
      _ = 32 * n * b := by ring
  rw [Matrix.mul_assoc _ L dB]
  calc _ ≤ ‖omegaZeroMatrix n * dL * B‖ + ‖omegaZeroMatrix n * (L * dB)‖ := norm_add_le _ _
    _ = ‖dL * B‖ + ‖L * dB‖ := by
        rw [Matrix.mul_assoc, norm_omegaZeroMatrix_mul, norm_omegaZeroMatrix_mul]
    _ ≤ b * 2 + 2 * (32 * n * b) := by
        gcongr
        · exact (Matrix.linfty_opNorm_mul _ _).trans (by gcongr)
        · exact (Matrix.linfty_opNorm_mul _ _).trans (by gcongr)
    _ ≤ 66 * n * b := by nlinarith [mul_nonneg hb0 (sub_nonneg.2 hn1)]


section Strip

variable {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {I : Fin n → ℝ} {ρ δ η : ℝ}

/-- Cauchy estimate for `DK - L⁰` and its transpose. -/
theorem tangent_close (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hclose : ∀ θ ∈ complexStrip n ρ, ‖K θ - unperturbedTorus I θ‖ ≤ η) (hδ : 0 < δ) :
    ∀ θ ∈ complexStrip n (ρ - δ), ‖tangentMat K θ - frameL0 n‖ ≤ n * η / δ ∧
      ‖(tangentMat K θ - frameL0 n)ᵀ‖ ≤ 2 * n * η / δ := by
  intro θ hθ
  have hK0 : DifferentiableOn ℂ (unperturbedTorus I) (complexStrip n ρ) :=
    (differentiable_unperturbedTorus I).differentiableOn
  have e1 := KAM.Apost.PerturbationAux.norm_fderiv_sub_le hK0 hK hclose hδ θ hθ
  have e2 := KAM.Apost.PerturbationAux.norm_transpose_tangentMat_sub_le hK0 hK hclose hδ θ hθ
  rw [tangentMat_unperturbedTorus] at e2
  refine ⟨?_, e2⟩
  rw [← tangentMat_unperturbedTorus I θ, KAM.Apost.PerturbationAux.norm_tangentMat_sub]
  exact e1

/-- Near a point of `T_ρ`, `D(DK) = D(DΔ)` for `Δ = K - K⁰`. -/
theorem fderiv_fderiv_eq (I : Fin n → ℝ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ) :
    fderiv ℂ (fderiv ℂ K) θ =
      fderiv ℂ (fderiv ℂ (fun y => K y - unperturbedTorus I y)) θ := by
  have hopen := isOpen_complexStrip n ρ
  have hev : fderiv ℂ K =ᶠ[nhds θ] fun y => fderiv ℂ (fun y => K y - unperturbedTorus I y) y +
      ContinuousLinearMap.inl ℂ (Fin n → ℂ) (Fin n → ℂ) := by
    filter_upwards [hopen.mem_nhds hθ] with y hy
    rw [fderiv_fun_sub (hK.differentiableAt (hopen.mem_nhds hy))
      ((differentiable_unperturbedTorus I) y), fderiv_unperturbedTorus, sub_add_cancel]
  rw [hev.fderiv_eq, fderiv_add_const]

/-- `‖D²K‖ ≤ 4η/δ²` on `T_{ρ-δ}`. -/
theorem norm_fderiv_fderiv_le (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hclose : ∀ θ ∈ complexStrip n ρ, ‖K θ - unperturbedTorus I θ‖ ≤ η) (hδ : 0 < δ)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ - δ)) :
    ‖fderiv ℂ (fderiv ℂ K) θ‖ ≤ 4 * η / δ ^ 2 := by
  have hθρ : θ ∈ complexStrip n ρ := fun i => (hθ i).trans_le (by linarith)
  rw [fderiv_fderiv_eq I hK hθρ]
  have hΔ : DifferentiableOn ℂ (fun y => K y - unperturbedTorus I y) (complexStrip n ρ) :=
    hK.sub (differentiable_unperturbedTorus I).differentiableOn
  have h := KAM.norm_iteratedFDeriv_two_le_of_mem_complexStrip hΔ hclose hδ hθ
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h
  exact h


/-- `‖∂_ω L‖ ≤ 4 n W η / δ²` on `T_{ρ-δ}`, for `‖ω‖ ≤ W`. -/
theorem norm_dL_le (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hclose : ∀ θ ∈ complexStrip n ρ, ‖K θ - unperturbedTorus I θ‖ ≤ η) (hδ : 0 < δ)
    {ω : Fin n → ℝ} {W : ℝ} (hω : ‖ω‖ ≤ W) :
    ∀ θ ∈ complexStrip n (ρ - δ),
      ‖fderiv ℂ (tangentMat K) θ (fun l => (ω l : ℂ))‖ ≤ 4 * n * W * η / δ ^ 2 := by
  intro θ hθ
  have hθρ : θ ∈ complexStrip n ρ := fun i => (hθ i).trans_le (by linarith)
  have hη : 0 ≤ η := (norm_nonneg _).trans (hclose θ hθρ)
  have hW : 0 ≤ W := (norm_nonneg ω).trans hω
  have hB0 : 0 ≤ 4 * n * W * η / δ ^ 2 := by positivity
  have hDK : DifferentiableAt ℂ (fderiv ℂ K) θ :=
    (holomorphic_regularity (isOpen_complexStrip n ρ) hK).1.differentiableAt
      ((isOpen_complexStrip n ρ).mem_nhds hθρ)
  have h2 := norm_fderiv_fderiv_le hK hclose hδ hθ
  have hv : ‖(fun l => (ω l : ℂ))‖ ≤ W := by
    rw [KAM.Apost.FrameAux.norm_ofReal_vec]; exact hω
  have hentry : ∀ (s : Fin n ⊕ Fin n) (j : Fin n),
      ‖fderiv ℂ (tangentMat K) θ (fun l => (ω l : ℂ)) s j‖ ≤ 4 * η / δ ^ 2 * W := by
    intro s j
    rw [KAM.Apost.Identities.fderiv_tangentMat_apply hK hθρ _ s j]
    have hcl : fderiv ℂ (fun y => fderiv ℂ K y (Pi.single j 1)) θ (fun l => (ω l : ℂ)) =
        fderiv ℂ (fderiv ℂ K) θ (fun l => (ω l : ℂ)) (Pi.single j 1) := by
      rw [fderiv_clm_apply hDK (differentiableAt_const _)]
      simp
    rw [hcl]
    calc _ ≤ ‖sumVec n (fderiv ℂ (fderiv ℂ K) θ (fun l => (ω l : ℂ)) (Pi.single j 1))‖ :=
          norm_le_pi_norm _ s
      _ = ‖fderiv ℂ (fderiv ℂ K) θ (fun l => (ω l : ℂ)) (Pi.single j 1)‖ := norm_sumVec _
      _ ≤ ‖fderiv ℂ (fderiv ℂ K) θ (fun l => (ω l : ℂ))‖ * ‖(Pi.single j 1 : Fin n → ℂ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℂ (fderiv ℂ K) θ‖ * ‖(fun l => (ω l : ℂ))‖) * 1 := by
          have h1 : ‖(Pi.single j 1 : Fin n → ℂ)‖ ≤ 1 := by
            rw [Pi.norm_single, norm_one]
          exact mul_le_mul (ContinuousLinearMap.le_opNorm _ _) h1 (norm_nonneg _)
            (by positivity)
      _ ≤ 4 * η / δ ^ 2 * W := by
          rw [mul_one]; gcongr
  refine (norm_le_iff_forall_rowSum hB0).2 fun s => ?_
  calc ∑ j, ‖fderiv ℂ (tangentMat K) θ (fun l => (ω l : ℂ)) s j‖
      ≤ ∑ _j : Fin n, 4 * η / δ ^ 2 * W := Finset.sum_le_sum fun j _ => hentry s j
    _ = 4 * n * W * η / δ ^ 2 := by simp; ring


/-- `D(LᵀL) v = (D L v)ᵀ L + Lᵀ (D L v)`. -/
theorem fderiv_gramMatrix_eq (hK : DifferentiableOn ℂ K (complexStrip n ρ)) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n ρ) (v : Fin n → ℂ) :
    fderiv ℂ (gramMatrix K) θ v = (fderiv ℂ (tangentMat K) θ v)ᵀ * tangentMat K θ +
      (tangentMat K θ)ᵀ * fderiv ℂ (tangentMat K) θ v := by
  have hL : DifferentiableAt ℂ (tangentMat K) θ :=
    (differentiableOn_tangentMat hK).differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθ)
  have hfun : gramMatrix K = fun y => (tangentMat K y)ᵀ * tangentMat K y :=
    funext (gramMatrix_eq_tangentMat_transpose_mul K)
  rw [hfun, fderiv_matrix_mul_apply hL.matrix_transpose hL, fderiv_matrix_transpose_apply]

/-- `D N v = Ω₀ (D L v) B + Ω₀ L (D B v)`, `B = G⁻¹`. -/
theorem fderiv_normalMat_eq (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hG : ∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K θ).det) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n ρ) (v : Fin n → ℂ) :
    fderiv ℂ (normalMat K) θ v = omegaZeroMatrix n * fderiv ℂ (tangentMat K) θ v *
        (gramMatrix K θ)⁻¹ +
      omegaZeroMatrix n * tangentMat K θ * fderiv ℂ (fun y => (gramMatrix K y)⁻¹) θ v := by
  have hopen := isOpen_complexStrip n ρ
  have hL : DifferentiableAt ℂ (tangentMat K) θ :=
    (differentiableOn_tangentMat hK).differentiableAt (hopen.mem_nhds hθ)
  have hB : DifferentiableAt ℂ (fun y => (gramMatrix K y)⁻¹) θ :=
    (holomorphic_inverse hopen (differentiableOn_gramMatrix hK)
      fun θ hθ => (hG θ hθ).ne_zero).1.differentiableAt (hopen.mem_nhds hθ)
  have hA : DifferentiableAt ℂ (fun y => omegaZeroMatrix n * tangentMat K y) θ :=
    (differentiableAt_const _).matrix_mul hL
  have hfun : normalMat K = fun y => (omegaZeroMatrix n * tangentMat K y) * (gramMatrix K y)⁻¹ :=
    rfl
  rw [hfun, fderiv_matrix_mul_apply hA hB, fderiv_matrix_const_mul_apply _ hL]


/-- Items (a), (c) of STAB and the normal frame, at the points of `T_{ρ-δ}`, in terms of
`a = n η / δ` with `12 n a ≤ 1`. -/
theorem frame_basic (hn : 0 < n) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hclose : ∀ θ ∈ complexStrip n ρ, ‖K θ - unperturbedTorus I θ‖ ≤ η) (hδ : 0 < δ)
    (h12 : 12 * n * (n * η / δ) ≤ 1) :
    ∀ θ ∈ complexStrip n (ρ - δ),
      (‖tangentMat K θ - frameL0 n‖ ≤ n * η / δ ∧ ‖tangentMat K θ‖ ≤ 2) ∧
      (IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ 2) ∧
      (‖normalMat K θ - frameN0 n‖ ≤ 12 * n * (n * η / δ) ∧ ‖normalMat K θ‖ ≤ 2) := by
  intro θ hθ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hθρ : θ ∈ complexStrip n ρ := fun i => (hθ i).trans_le (by linarith)
  have hη : 0 ≤ η := (norm_nonneg _).trans (hclose θ hθρ)
  have ha0 : 0 ≤ (n : ℝ) * η / δ := by positivity
  have ha1 : (n : ℝ) * η / δ ≤ 1 := by nlinarith
  obtain ⟨hD, hDt⟩ := tangent_close hK hclose hδ θ hθ
  have hDt' : ‖(tangentMat K θ - frameL0 n)ᵀ‖ ≤ 2 * n * ((n : ℝ) * η / δ) := by
    refine hDt.trans ?_
    have : 2 * (n : ℝ) * η / δ = 2 * (n * η / δ) := by ring
    rw [this]
    nlinarith
  have hG1 := norm_gram_sub_one_le hn ha0 ha1 hD hDt'
  rw [← gramMatrix_eq_tangentMat_transpose_mul] at hG1
  obtain ⟨hGu, hGi, hGi1⟩ := gram_inv hn h12 hG1
  have hN := norm_normal_sub_le hn ha0 hD hGi hGi1
  have hL2 : ‖tangentMat K θ‖ ≤ 2 := by
    calc _ = ‖frameL0 n + (tangentMat K θ - frameL0 n)‖ := by rw [add_sub_cancel]
      _ ≤ ‖frameL0 n‖ + ‖tangentMat K θ - frameL0 n‖ := norm_add_le _ _
      _ ≤ 1 + 1 := by rw [norm_frameL0 hn]; linarith
      _ = 2 := by norm_num
  have hN2 : ‖normalMat K θ‖ ≤ 2 := by
    calc _ = ‖frameN0 n + (normalMat K θ - frameN0 n)‖ := by rw [add_sub_cancel]
      _ ≤ ‖frameN0 n‖ + ‖normalMat K θ - frameN0 n‖ := norm_add_le _ _
      _ ≤ 1 + 1 := by rw [norm_frameN0 hn]; exact add_le_add le_rfl (hN.trans h12)
      _ = 2 := by norm_num
  exact ⟨⟨hD, hL2⟩, ⟨(Matrix.isUnit_iff_isUnit_det _).1 hGu, hGi⟩, ⟨hN, hN2⟩⟩


/-- `‖∂_ω N‖ ≤ 66 n (4 n W η/δ²)` on `T_{ρ-δ}` (step `step:p4:stab-frame`). -/
theorem frame_deriv (hn : 0 < n) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hclose : ∀ θ ∈ complexStrip n ρ, ‖K θ - unperturbedTorus I θ‖ ≤ η) (hδ : 0 < δ)
    (h12 : 12 * n * (n * η / δ) ≤ 1) {ω : Fin n → ℝ} {W : ℝ} (hω : ‖ω‖ ≤ W) :
    ∀ θ ∈ complexStrip n (ρ - δ),
      ‖fderiv ℂ (normalMat K) θ (fun l => (ω l : ℂ))‖ ≤ 66 * n * (4 * n * W * η / δ ^ 2) := by
  have hb := frame_basic hn hK hclose hδ h12
  have hsub : complexStrip n (ρ - δ) ⊆ complexStrip n ρ := fun θ hθ i =>
    (hθ i).trans_le (by linarith)
  have hKs : DifferentiableOn ℂ K (complexStrip n (ρ - δ)) := hK.mono hsub
  have hGs : ∀ θ ∈ complexStrip n (ρ - δ), IsUnit (gramMatrix K θ).det :=
    fun θ hθ => (hb θ hθ).2.1.1
  obtain ⟨-, -, hdB⟩ := KAM.Head.gramMatrix_inverse_regular hKs
    (fun θ hθ => (hGs θ hθ).ne_zero) ω
  intro θ hθ
  rw [fderiv_normalMat_eq hKs hGs hθ]
  exact norm_dN_le hn (hb θ hθ).1.2 (hb θ hθ).2.1.2 (norm_dL_le hK hclose hδ hω θ hθ)
    (fderiv_gramMatrix_eq hKs hθ _) (hdB θ hθ)

end Strip


section Constants

variable {s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}

theorem three_n_le_cT (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) :
    304 * (n : ℝ) ^ 3 ≤ cT s₀ r₀ B h := by
  have hM := Parameters.Mconst_pos (B := B) (h := h) hs₀ hr₀
  have hW := Parameters.Winf_nonneg (B := B) (h := h) hs₀ hr₀
  have h3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  unfold cT
  nlinarith [mul_nonneg h3 hM.le, mul_nonneg h3 hW]

theorem eta_small (hn : 2 ≤ n) (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) {δ η : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hη0 : 0 ≤ η) (hη : η ≤ etaStar s₀ r₀ B h Lh δ) :
    cT s₀ r₀ B h * η / δ ^ 2 ≤ 1 / (16 * Lplus Lh) ∧ 12 * n * (n * η / δ) ≤ 1 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hc := Parameters.cT_pos (B := B) (h := h) hn hs₀ hr₀
  have hL := Parameters.Lplus_pos Lh
  have hL1 := one_le_Lplus Lh
  have hc3 := three_n_le_cT (B := B) (h := h) hs₀ hr₀
  have hη' := (Parameters.etaStar_le_div s₀ r₀ B h Lh δ)
  have hη'' : η * (16 * cT s₀ r₀ B h * Lplus Lh) ≤ δ ^ 2 :=
    (le_div_iff₀ (by positivity)).1 (hη.trans hη')
  refine ⟨?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · have hn2 : (n : ℝ) ^ 2 ≤ cT s₀ r₀ B h := by
      have : (n : ℝ) ^ 2 ≤ 304 * (n : ℝ) ^ 3 := by
        nlinarith [sq_nonneg (n : ℝ), mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.2 hn1)]
      linarith
    have h1 : 16 * (n : ℝ) ^ 2 * η ≤ δ := by
      have e1 : 16 * (n : ℝ) ^ 2 * η ≤ η * (16 * cT s₀ r₀ B h * Lplus Lh) := by
        nlinarith [mul_nonneg hη0 (sub_nonneg.2 hn2), mul_nonneg hη0 (sub_nonneg.2 hL1),
          mul_nonneg (mul_nonneg hη0 hc.le) (sub_nonneg.2 hL1)]
      nlinarith
    rw [show (12 : ℝ) * n * (n * η / δ) = 12 * n ^ 2 * η / δ by ring, div_le_one hδ]
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) hη0]

end Constants

end Stab

end KAM.Head

end
