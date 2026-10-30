/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Apost.Identities
public import KAM.Apost.Frame
import Mathlib.Tactic.Abel

/-!
# The torsion as a polynomial in `(A, L, B, DE)`

Blueprint `bp:p2s:torsion-identity` (HL19 Lemma 4.8, the route through `∂_ω L = AL - DE`). For a
torus `K` holomorphic on `T_r` with `K(T_r) ⊆ 𝔅` and `det G ≠ 0` on `T_r`, and **any** frequency
`ω' ∈ ℝⁿ` (no Diophantine property is used), with `F = DE_{ω'}`:

* `∂_{ω'} B = -B (∂_{ω'} G) B`, `∂_{ω'} G = (AL - F)ᵀ L + Lᵀ (AL - F)`;
* `∂_{ω'} N = Ω₀ (AL - F) B - N ((AL - F)ᵀ L + Lᵀ (AL - F)) B`;
* `T_{ω'} = 𝒯(A, L, B, F)` (`KAM.Sharp.torsionPoly`).

The proof follows the blueprint steps:

* `step:p2s:ti-dl`: `KAM.Sharp.TorsionPoly.fderiv_tangentMat_eq`, the identity
  `∂_{ω'} L = AL - F` of
  `KAM.Apost.Identities.fi_dL` at an arbitrary frequency (the standing frequency of `hS` is not
  used);
* `step:p2s:ti-db`: `fderiv_gramMatrix_eq`, `fderiv_invGram_eq` (differentiate `B G = 1` near `θ`);
* `step:p2s:ti-dn`: `fderiv_normalMat_eq`;
* `step:p2s:ti-t`: `normalMat_transpose_mul_omega` (`Nᵀ Ω₀ = B Lᵀ`) and `torsion_alg`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp

open KAM KAM.Torus KAM.Apost

variable {n : ℕ}

/-- The torsion polynomial `𝒯(A, L, B, F)` of `bp:p2s:sec-torsion`. -/
def torsionPoly (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (L F : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  B * Lᵀ * (A * omegaZeroMatrix n * L * B - omegaZeroMatrix n * A * L * B +
      omegaZeroMatrix n * F * B) +
    B * (Lᵀ * omegaZeroMatrix n * L) * B * (Lᵀ * (Aᵀ + A) * L - Fᵀ * L - Lᵀ * F) * B

namespace TorsionPoly

variable {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r : ℝ} {θ : Fin n → ℂ}

/-- Step `step:p2s:ti-dl`: `∂_{ω'} L = A L - DE_{ω'}` at any frequency `ω'` (the proof of
`KAM.Apost.Identities.fi_dL`, whose statement is tied to the frequency of the standing data). -/
theorem fderiv_tangentMat_eq (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅) (hθ : θ ∈ complexStrip n r) (ω' : Fin n → ℝ) :
    fderiv ℂ (tangentMat K) θ (fun l => (ω' l : ℂ)) =
      linMat h K θ * tangentMat K θ - errDerivMat h K ω' θ := by
  have hX := (differentiableOn_ham hS).differentiableAt (hS.isOpen.mem_nhds (hK𝔅 θ hθ))
  have hKd := hK.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)
  have hcomp : fderiv ℂ (fun y => hamiltonianVectorFieldℂ h (K y)) θ =
      (fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ)).comp (fderiv ℂ K θ) :=
    (hX.hasFDerivAt.comp θ hKd.hasFDerivAt).fderiv
  have hE : DifferentiableAt ℂ (invarianceError h K ω') θ :=
    (Identities.differentiableAt_ham_comp hS hK hK𝔅 hθ).sub
      (Identities.differentiableAt_fderiv_apply hK hθ _)
  ext s j
  have hA : sumVec n (fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ) (fderiv ℂ K θ (Pi.single j 1)))
      = linMat h K θ *ᵥ fun t => tangentMat K θ t j := by
    rw [linMat, ← sqMat_mulVec]
    congr 1
  rw [Matrix.sub_apply, Identities.fderiv_tangentMat_apply hK hθ,
    Identities.fderiv_tangent_column_omega (h := h) (ω := ω') hK hθ j,
    fderiv_fun_sub (Identities.differentiableAt_ham_comp hS hK hK𝔅 hθ) hE, hcomp, errDerivMat,
    Identities.colMat_apply]
  simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply, map_sub,
    Pi.sub_apply, hA]
  rfl

/-- `B = G⁻¹` is holomorphic on the strip. -/
theorem differentiableOn_invGram (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    DifferentiableOn ℂ (fun y => (gramMatrix K y)⁻¹) (complexStrip n r) :=
  (holomorphic_inverse (isOpen_complexStrip n r) (differentiableOn_gramMatrix hK)
    fun θ hθ => (hG θ hθ).ne_zero).1

/-- Step `step:p2s:ti-db`: `∂_v G = (∂_v L)ᵀ L + Lᵀ ∂_v L`. -/
theorem fderiv_gramMatrix_eq (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hθ : θ ∈ complexStrip n r) (v : Fin n → ℂ) :
    fderiv ℂ (gramMatrix K) θ v =
      (fderiv ℂ (tangentMat K) θ v)ᵀ * tangentMat K θ +
        (tangentMat K θ)ᵀ * fderiv ℂ (tangentMat K) θ v := by
  have hL : DifferentiableAt ℂ (tangentMat K) θ :=
    (differentiableOn_tangentMat hK).differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)
  have hfun : gramMatrix K = fun y => (tangentMat K y)ᵀ * tangentMat K y :=
    funext (gramMatrix_eq_tangentMat_transpose_mul K)
  rw [hfun, fderiv_matrix_mul_apply hL.matrix_transpose hL, fderiv_matrix_transpose_apply]

/-- Step `step:p2s:ti-db`: `∂_v B = -B (∂_v G) B`, from `B G = 1` near `θ`. -/
theorem fderiv_invGram_eq (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) (hθ : θ ∈ complexStrip n r)
    (v : Fin n → ℂ) :
    fderiv ℂ (fun y => (gramMatrix K y)⁻¹) θ v =
      -((gramMatrix K θ)⁻¹ * fderiv ℂ (gramMatrix K) θ v * (gramMatrix K θ)⁻¹) := by
  have hnhds := (isOpen_complexStrip n r).mem_nhds hθ
  have hB : DifferentiableAt ℂ (fun y => (gramMatrix K y)⁻¹) θ :=
    (differentiableOn_invGram hK hG).differentiableAt hnhds
  have hGd : DifferentiableAt ℂ (gramMatrix K) θ :=
    (differentiableOn_gramMatrix hK).differentiableAt hnhds
  have hconst : (fun y => (gramMatrix K y)⁻¹ * gramMatrix K y)
      =ᶠ[𝓝 θ] fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) := by
    filter_upwards [hnhds] with y hy
    exact Matrix.nonsing_inv_mul _ (hG y hy)
  have h0 : fderiv ℂ (fun y => (gramMatrix K y)⁻¹ * gramMatrix K y) θ v = 0 := by
    rw [hconst.fderiv_eq]
    simp
  rw [fderiv_matrix_mul_apply hB hGd] at h0
  have hGB : gramMatrix K θ * (gramMatrix K θ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hG θ hθ)
  have key : fderiv ℂ (fun y => (gramMatrix K y)⁻¹) θ v =
      (fderiv ℂ (fun y => (gramMatrix K y)⁻¹) θ v * gramMatrix K θ) * (gramMatrix K θ)⁻¹ := by
    rw [Matrix.mul_assoc, hGB, Matrix.mul_one]
  rw [key, eq_neg_of_add_eq_zero_left h0, Matrix.neg_mul]

/-- Step `step:p2s:ti-dn`: `∂_v N = Ω₀ (∂_v L) B + Ω₀ L ∂_v B`. -/
theorem fderiv_normalMat_eq (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) (hθ : θ ∈ complexStrip n r)
    (v : Fin n → ℂ) :
    fderiv ℂ (normalMat K) θ v =
      omegaZeroMatrix n * fderiv ℂ (tangentMat K) θ v * (gramMatrix K θ)⁻¹ +
        omegaZeroMatrix n * tangentMat K θ * fderiv ℂ (fun y => (gramMatrix K y)⁻¹) θ v := by
  have hnhds := (isOpen_complexStrip n r).mem_nhds hθ
  have hL : DifferentiableAt ℂ (tangentMat K) θ :=
    (differentiableOn_tangentMat hK).differentiableAt hnhds
  have hB : DifferentiableAt ℂ (fun y => (gramMatrix K y)⁻¹) θ :=
    (differentiableOn_invGram hK hG).differentiableAt hnhds
  have hOL : DifferentiableAt ℂ (fun y => omegaZeroMatrix n * tangentMat K y) θ :=
    (differentiableAt_const _).matrix_mul hL
  have hfun : normalMat K = fun y => (omegaZeroMatrix n * tangentMat K y) * (gramMatrix K y)⁻¹ :=
    rfl
  rw [hfun, fderiv_matrix_mul_apply hOL hB, fderiv_matrix_const_mul_apply _ hL]

/-- Step `step:p2s:ti-t`: `Nᵀ Ω₀ = B Lᵀ`. -/
theorem normalMat_transpose_mul_omega (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (θ : Fin n → ℂ) :
    (normalMat K θ)ᵀ * omegaZeroMatrix n = (gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ := by
  rw [normalMat, Matrix.transpose_mul, Matrix.transpose_mul, Identities.gram_inv_transpose,
    omegaZeroMatrix_transpose]
  simp only [Matrix.mul_assoc, Matrix.neg_mul, omegaZeroMatrix_mul_self, Matrix.mul_neg, neg_neg,
    Matrix.mul_one]

/-- Step `step:p2s:ti-t`, the algebra: with `Nᵀ Ω₀ = B Lᵀ`, `N = Ω₀ L B` and the derivative of
`N` of `fderiv_normalMat_eq`, `Nᵀ Ω₀ (A N - ∂N) = 𝒯(A, L, B, F)`. -/
theorem torsion_alg (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (L F : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    B * Lᵀ * (A * (omegaZeroMatrix n * L * B) -
        (omegaZeroMatrix n * (A * L - F) * B + omegaZeroMatrix n * L *
          -(B * ((A * L - F)ᵀ * L + Lᵀ * (A * L - F)) * B))) =
      torsionPoly A L F B := by
  simp only [torsionPoly, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.mul_assoc]
  abel

end TorsionPoly

variable {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

/-- Blueprint `bp:p2s:torsion-identity`, at any frequency `ω'` (no Diophantine property used). -/
theorem torsion_identity (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) (ω' : Fin n → ℝ) :
    ∀ θ ∈ complexStrip n r,
      fderiv ℂ (fun y => (gramMatrix K y)⁻¹) θ (fun l => (ω' l : ℂ)) =
        -((gramMatrix K θ)⁻¹ *
          ((linMat h K θ * tangentMat K θ - errDerivMat h K ω' θ)ᵀ * tangentMat K θ +
            (tangentMat K θ)ᵀ * (linMat h K θ * tangentMat K θ - errDerivMat h K ω' θ)) *
          (gramMatrix K θ)⁻¹) ∧
      fderiv ℂ (normalMat K) θ (fun l => (ω' l : ℂ)) =
        omegaZeroMatrix n * (linMat h K θ * tangentMat K θ - errDerivMat h K ω' θ) *
            (gramMatrix K θ)⁻¹ -
          normalMat K θ *
            ((linMat h K θ * tangentMat K θ - errDerivMat h K ω' θ)ᵀ * tangentMat K θ +
              (tangentMat K θ)ᵀ * (linMat h K θ * tangentMat K θ - errDerivMat h K ω' θ)) *
            (gramMatrix K θ)⁻¹ ∧
      torsion h K ω' θ = torsionPoly (linMat h K θ) (tangentMat K θ) (errDerivMat h K ω' θ)
        (gramMatrix K θ)⁻¹ := by
  intro θ hθ
  have _hr : 0 < r := hr
  have hdL := TorsionPoly.fderiv_tangentMat_eq hS hK hK𝔅 hθ ω'
  have hdB : fderiv ℂ (fun y => (gramMatrix K y)⁻¹) θ (fun l => (ω' l : ℂ)) =
      -((gramMatrix K θ)⁻¹ *
        ((linMat h K θ * tangentMat K θ - errDerivMat h K ω' θ)ᵀ * tangentMat K θ +
          (tangentMat K θ)ᵀ * (linMat h K θ * tangentMat K θ - errDerivMat h K ω' θ)) *
        (gramMatrix K θ)⁻¹) := by
    rw [TorsionPoly.fderiv_invGram_eq hK hG hθ, TorsionPoly.fderiv_gramMatrix_eq hK hθ, hdL]
  have hdN : fderiv ℂ (normalMat K) θ (fun l => (ω' l : ℂ)) =
      omegaZeroMatrix n * (linMat h K θ * tangentMat K θ - errDerivMat h K ω' θ) *
          (gramMatrix K θ)⁻¹ -
        normalMat K θ *
          ((linMat h K θ * tangentMat K θ - errDerivMat h K ω' θ)ᵀ * tangentMat K θ +
            (tangentMat K θ)ᵀ * (linMat h K θ * tangentMat K θ - errDerivMat h K ω' θ)) *
          (gramMatrix K θ)⁻¹ := by
    rw [TorsionPoly.fderiv_normalMat_eq hK hG hθ, hdB, hdL]
    simp only [normalMat, Matrix.mul_neg, Matrix.mul_assoc, sub_eq_add_neg]
  refine ⟨hdB, hdN, ?_⟩
  have hN : DifferentiableAt ℂ (normalMat K) θ :=
    (differentiableOn_normalMat hK hG).differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)
  rw [torsion_eq_mat h K ω' hN, TorsionPoly.normalMat_transpose_mul_omega,
    normalFieldMat, TorsionPoly.fderiv_normalMat_eq hK hG hθ, hdB, hdL]
  exact TorsionPoly.torsion_alg _ _ _ _

end KAM.Sharp

end
