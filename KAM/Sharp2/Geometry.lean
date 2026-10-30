/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.Frame
public import KAM.Sharp2.SmallDiv.Defs

/-!
# Geometry controlled by the normal error

Blueprint `bp:p2s2:sec-geo`.

* `norm_invarianceError_le_eta` (`bp:p2s2:recovery`, FH24 Lemma 3.3): the invariance error `E` is
  recovered from its tangent and normal parts `ηᴸ`, `ηᴺ`. Writing `E = L ξᴸ + N ξᴺ`, the identities
  `Lᵀ Ω₀ N = -I`, `Nᵀ Ω₀ L = I` give `ηᴺ = Ω_K ξᴸ - ξᴺ` and `ηᴸ = -ξᴸ - Ω_N ξᴺ`; with
  `|Ω_K|, |Ω_N| ≤ q < 1` this solves for `ξ` (`frame_surj`) and bounds it.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Sharp2

open KAM KAM.Torus KAM.Apost

section Recovery

variable {n : ℕ} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}

/-- `P (x, y) = L x + N y`, and the two projections of `Lᵀ Ω₀ ·` and `Nᵀ Ω₀ ·` of it. -/
theorem frame_proj (hG : IsUnit (gramMatrix K θ).det) (x y : Fin n → ℂ) :
    ((tangentMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ (frameMat K θ *ᵥ Sum.elim x y) =
        lagrangeMat K θ *ᵥ x - y ∧
      ((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ (frameMat K θ *ᵥ Sum.elim x y) =
        x + ((normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ y := by
  have h1 := Identities.fi_LtON K hG
  have h2 := Identities.fi_NtOL K hG
  rw [frameMat, Matrix.fromCols_mulVec_sumElim]
  constructor
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, lagrangeMat,
      Matrix.neg_mulVec, Matrix.one_mulVec, sub_eq_add_neg]
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

/-- Under `|Ω_K|, |Ω_N| ≤ q < 1` the frame `P = (L N)` is onto. -/
theorem frame_surj (hG : IsUnit (gramMatrix K θ).det) {q : ℝ} (hq : q < 1)
    (hΩK : ‖lagrangeMat K θ‖ ≤ q) (hΩN : ‖(normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ‖ ≤ q)
    (e : Fin n ⊕ Fin n → ℂ) : ∃ x y : Fin n → ℂ, frameMat K θ *ᵥ Sum.elim x y = e := by
  have hq0 : 0 ≤ q := (norm_nonneg _).trans hΩK
  have key : ∀ x y : Fin n → ℂ, frameMat K θ *ᵥ Sum.elim x y = 0 → x = 0 ∧ y = 0 := by
    intro x y hxy
    obtain ⟨p1, p2⟩ := frame_proj hG x y
    rw [hxy, Matrix.mulVec_zero] at p1 p2
    have hy : y = lagrangeMat K θ *ᵥ x := (sub_eq_zero.mp p1.symm).symm
    have hx : x = -(((normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ y) :=
      eq_neg_of_add_eq_zero_left p2.symm
    have e1 : ‖y‖ ≤ q * ‖x‖ := by
      rw [hy]
      exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right hΩK (norm_nonneg _))
    have e2 : ‖x‖ ≤ q * ‖y‖ := by
      rw [hx, norm_neg]
      exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right hΩN (norm_nonneg _))
    have hy0 : ‖y‖ = 0 := by
      have : ‖y‖ ≤ q ^ 2 * ‖y‖ := by
        calc ‖y‖ ≤ q * ‖x‖ := e1
          _ ≤ q * (q * ‖y‖) := mul_le_mul_of_nonneg_left e2 hq0
          _ = q ^ 2 * ‖y‖ := by ring
      have hq2 : q ^ 2 < 1 := by nlinarith
      nlinarith [norm_nonneg y]
    have hy' : y = 0 := norm_eq_zero.mp hy0
    refine ⟨?_, hy'⟩
    rw [hx, hy', Matrix.mulVec_zero, neg_zero]
  have hU : IsUnit (frameMat K θ) := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro a b hab
    have hz : frameMat K θ *ᵥ (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
    have hab' : a - b = Sum.elim ((a - b) ∘ Sum.inl) ((a - b) ∘ Sum.inr) := by
      ext i; cases i <;> rfl
    rw [hab'] at hz
    obtain ⟨hx, hy⟩ := key _ _ hz
    have : a - b = 0 := by
      rw [hab', hx, hy]; ext i; cases i <;> rfl
    exact sub_eq_zero.mp this
  obtain ⟨v, hv⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hU) e
  refine ⟨v ∘ Sum.inl, v ∘ Sum.inr, ?_⟩
  rw [Sum.elim_comp_inl_inr]
  exact hv

end Recovery

/-- Blueprint `bp:p2s2:recovery`: the invariance error from its tangent and normal parts
(FH24 Lemma 3.3). -/
theorem norm_invarianceError_le_eta {n : ℕ} {σK σN q εL εN r : ℝ} {ω : Fin n → ℝ}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hq : q < 1)
    (hL : ∀ θ ∈ complexStrip n r, ‖tangentMat K θ‖ ≤ σK)
    (hN : ∀ θ ∈ complexStrip n r, ‖normalMat K θ‖ ≤ σN)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det)
    (hΩK : ∀ θ ∈ complexStrip n r, ‖lagrangeMat K θ‖ ≤ q)
    (hΩN : ∀ θ ∈ complexStrip n r, ‖(normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ‖ ≤ q)
    (hηL : ∀ θ ∈ complexStrip n r, ‖etaL h K ω θ‖ ≤ εL)
    (hηN : ∀ θ ∈ complexStrip n r, ‖etaN h K ω θ‖ ≤ εN) :
    ∀ θ ∈ complexStrip n r, ‖invarianceError h K ω θ‖ ≤
      (σK + σN * q) / (1 - q ^ 2) * εL + (σN + σK * q) / (1 - q ^ 2) * εN := by
  intro θ hθ
  have hq0 : 0 ≤ q := (norm_nonneg _).trans (hΩK θ hθ)
  have hσK : 0 ≤ σK := (norm_nonneg _).trans (hL θ hθ)
  have hσN : 0 ≤ σN := (norm_nonneg _).trans (hN θ hθ)
  have hεL : 0 ≤ εL := (norm_nonneg _).trans (hηL θ hθ)
  have hεN : 0 ≤ εN := (norm_nonneg _).trans (hηN θ hθ)
  have hd : 0 < 1 - q ^ 2 := by nlinarith
  obtain ⟨x, y, hxy⟩ := frame_surj (hG θ hθ) hq (hΩK θ hθ) (hΩN θ hθ)
    (sumVec n (invarianceError h K ω θ))
  obtain ⟨p1, p2⟩ := frame_proj (hG θ hθ) x y
  rw [hxy] at p1 p2
  have hN' : etaN h K ω θ = lagrangeMat K θ *ᵥ x - y := p1
  have hL' : etaL h K ω θ = -(x + ((normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ y) := by
    rw [etaL, p2]
  have e1 : ‖y‖ ≤ q * ‖x‖ + εN := by
    have : y = lagrangeMat K θ *ᵥ x - etaN h K ω θ := by rw [hN']; abel
    rw [this]
    refine (norm_sub_le _ _).trans (add_le_add ?_ (hηN θ hθ))
    exact (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_right (hΩK θ hθ) (norm_nonneg _))
  have e2 : ‖x‖ ≤ εL + q * ‖y‖ := by
    have : x = -etaL h K ω θ - ((normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ y := by
      rw [hL']; abel
    rw [this]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_neg]; exact hηL θ hθ
    · exact (Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_right (hΩN θ hθ) (norm_nonneg _))
  have hx : ‖x‖ ≤ (εL + q * εN) / (1 - q ^ 2) := by
    rw [le_div_iff₀ hd]
    nlinarith [norm_nonneg x, norm_nonneg y]
  have hy : ‖y‖ ≤ (εN + q * εL) / (1 - q ^ 2) := by
    rw [le_div_iff₀ hd]
    nlinarith [norm_nonneg x, norm_nonneg y]
  have hE : ‖invarianceError h K ω θ‖ ≤ σK * ‖x‖ + σN * ‖y‖ := by
    rw [← norm_sumVec, ← hxy, frameMat, Matrix.fromCols_mulVec_sumElim]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_right (hL θ hθ) (norm_nonneg _))
    · exact (Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_right (hN θ hθ) (norm_nonneg _))
  calc _ ≤ σK * ‖x‖ + σN * ‖y‖ := hE
    _ ≤ σK * ((εL + q * εN) / (1 - q ^ 2)) + σN * ((εN + q * εL) / (1 - q ^ 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hx hσK) (mul_le_mul_of_nonneg_left hy hσN)
    _ = _ := by field_simp; ring

section Lagrange

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ γ₀ : ℝ} {r : ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}

/-- `ηᴺ` is holomorphic on `T_r`. -/
theorem differentiableOn_etaN (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅) :
    DifferentiableOn ℂ (etaN h K ω) (complexStrip n r) := by
  have hE := FrameAux.differentiableOn_invarianceError hS hK hK𝔅
  have hL := differentiableOn_tangentMat hK
  exact ((hL.matrix_transpose).matrix_mul (differentiableOn_const _)).matrix_mulVec
    ((sumVecIso n).differentiable.comp_differentiableOn hE)

/-- The derivative matrix `(∂_j ηᴺ_i)` of `ηᴺ`. -/
def etaNDeriv (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (θ : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => fderiv ℂ (etaN h K ω) θ (Pi.single j 1) i

/-- `∂_ω Ω_K = -(Dηᴺ - (Dηᴺ)ᵀ)`: the symmetric part of `Dηᴺ` is the Hessian of `K` against `Ω₀ E`
(`bp:p2s2:omega`, step `step:p2s2:om-id`). -/
theorem fderiv_lagrangeMat_eq_etaN (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hθ : θ ∈ complexStrip n r) :
    fderiv ℂ (lagrangeMat K) θ (fun l => (ω l : ℂ)) =
      -(etaNDeriv h K ω θ - (etaNDeriv h K ω θ)ᵀ) := by
  have hLd : DifferentiableAt ℂ (tangentMat K) θ :=
    (differentiableOn_tangentMat hK).differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)
  have hLtO : DifferentiableAt ℂ (fun y => (tangentMat K y)ᵀ * omegaZeroMatrix n) θ :=
    hLd.matrix_transpose.matrix_mul (differentiableAt_const _)
  have hEd := Identities.differentiableAt_invarianceError hS hK hK𝔅 hθ
  have hed : DifferentiableAt ℂ (fun y => sumVec n (invarianceError h K ω y)) θ :=
    (sumVecIso n).differentiable.differentiableAt.comp θ hEd
  rw [Identities.fi_dLagrange hS hK hK𝔅 hθ]
  have hM : ∀ i j, etaNDeriv h K ω θ i j =
      (((fderiv ℂ (tangentMat K) θ (Pi.single j 1))ᵀ * omegaZeroMatrix n) *ᵥ
        sumVec n (invarianceError h K ω θ)) i +
      ((tangentMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ) i j := by
    intro i j
    have hf : etaN h K ω = fun y => ((tangentMat K y)ᵀ * omegaZeroMatrix n) *ᵥ
        sumVec n (invarianceError h K ω y) := rfl
    rw [etaNDeriv, Matrix.of_apply, hf, fderiv_matrix_mulVec_apply hLtO hed,
      fderiv_matrix_mul_const_apply hLd.matrix_transpose, fderiv_matrix_transpose_apply,
      Pi.add_apply, Geometry.errDerivMat_eq_of, Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  have hsym : ∀ i j, (((fderiv ℂ (tangentMat K) θ (Pi.single j 1))ᵀ * omegaZeroMatrix n) *ᵥ
        sumVec n (invarianceError h K ω θ)) i =
      (((fderiv ℂ (tangentMat K) θ (Pi.single i 1))ᵀ * omegaZeroMatrix n) *ᵥ
        sumVec n (invarianceError h K ω θ)) j := by
    intro i j
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    refine congrArg (· * _) (Finset.sum_congr rfl fun t _ => ?_)
    rw [Exactness.fderiv_tangentMat_symm hK hθ j i t]
  set X := (tangentMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ with hX
  have hD : etaNDeriv h K ω θ - (etaNDeriv h K ω θ)ᵀ = X - Xᵀ := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.transpose_apply, hM i j, hM j i, hsym i j]
    ring
  have hXt : Xᵀ = -((errDerivMat h K ω θ)ᵀ * omegaZeroMatrix n * tangentMat K θ) := by
    rw [hX, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      omegaZeroMatrix_transpose]
    simp [Matrix.mul_assoc]
  rw [hD, hXt]
  abel


/-- The row sums of `Dηᴺ - (Dηᴺ)ᵀ` are at most `2 (n - 1) ε / δ` on `T_{r-δ}` (Cauchy). -/
theorem norm_etaNDeriv_sub_transpose_le (hn : 1 ≤ n) (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    {εN δ : ℝ} (hδ : 0 < δ) (hηN : ∀ θ ∈ complexStrip n r, ‖etaN h K ω θ‖ ≤ εN) :
    ∀ θ ∈ complexStrip n (r - δ),
      ‖etaNDeriv h K ω θ - (etaNDeriv h K ω θ)ᵀ‖ ≤ 2 * (n - 1) * (δ⁻¹ * εN) := by
  intro θ hθ
  have hε : 0 ≤ εN := (norm_nonneg _).trans (hηN θ (Geometry.complexStrip_sub_subset hδ.le hθ))
  have hcoord := (cauchy_strip (differentiableOn_etaN hS hK hK𝔅) hηN hδ).1
  have hent : ∀ i j, ‖etaNDeriv h K ω θ i j‖ ≤ δ⁻¹ * εN := fun i j =>
    (norm_le_pi_norm _ i).trans (hcoord j θ hθ)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnn : 0 ≤ 2 * ((n : ℝ) - 1) * (δ⁻¹ * εN) := by
    have : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
    have : 0 ≤ δ⁻¹ * εN := mul_nonneg (inv_nonneg.2 hδ.le) hε
    positivity
  refine (norm_le_iff_forall_rowSum hnn).2 fun i => ?_
  calc ∑ j, ‖(etaNDeriv h K ω θ - (etaNDeriv h K ω θ)ᵀ) i j‖
      ≤ ∑ j, (if j = i then 0 else 2 * (δ⁻¹ * εN)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hji : j = i
        · subst hji; simp
        · simp only [hji, ↓reduceIte, Matrix.sub_apply, Matrix.transpose_apply]
          calc _ ≤ ‖etaNDeriv h K ω θ i j‖ + ‖etaNDeriv h K ω θ j i‖ := norm_sub_le _ _
            _ ≤ δ⁻¹ * εN + δ⁻¹ * εN := add_le_add (hent _ _) (hent _ _)
            _ = _ := by ring
    _ = 2 * ((n : ℝ) - 1) * (δ⁻¹ * εN) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
        have : (Finset.univ.filter fun j : Fin n => ¬ j = i).card = n - 1 := by
          rw [Finset.filter_not, Finset.filter_eq' Finset.univ i]
          simp only [Finset.mem_univ, ↓reduceIte]
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
            Fintype.card_fin, Finset.card_singleton]
        rw [this, Nat.cast_sub hn]; push_cast; ring

/-- **Blueprint `bp:p2s2:omega` (with the Hamiltonian hypotheses of `Standing`).** The Lagrangian
defect is controlled by the normal error alone (FH24 Lemma 3.1); the Russmann-Cauchy constant is
`c₁ / (s^κ (1 - s))` with `c₁` a small-divisor constant at the bite `s δ`.

Deviation from `APOST-SHARP-V2-SIGNATURES.lean.txt`: the hypothesis `hh : DifferentiableOn ℂ h
{z | ∃ θ ∈ T_r, z = K θ}` there (holomorphy on the image `K(T_r)`, a set with empty interior)
gives no derivative of `h` at all, and the identity `∂_ω Ω_K = -(Dηᴺ - (Dηᴺ)ᵀ)` needs `D²h`
symmetric on an open set; it is replaced by `Standing` (open `𝔅`, `h` holomorphic on `𝔅`, ...)
and `K(T_r) ⊆ 𝔅`, the same hypotheses as every v1 geometry lemma. -/
theorem norm_lagrangeMat_le_etaN_of_standing (hn : 1 ≤ n) {κ δ s c₁ εN : ℝ} {Ω : Set (Fin n → ℝ)}
    (hc : SDConst n κ γ (s * δ) c₁ Ω) (hω : ω ∈ Ω) (hs0 : 0 < s) (hs1 : s < 1) (hδr : δ < r)
    (hS : Standing n τ M σK σB σT 𝔅 h ω γ₀)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hηN : ∀ θ ∈ complexStrip n r, ‖etaN h K ω θ‖ ≤ εN) :
    ∀ θ ∈ complexStrip n (r - δ),
      ‖lagrangeMat K θ‖ ≤ 2 * (n - 1) * (c₁ / (s ^ κ * (1 - s))) * γ⁻¹ * δ ^ (-(κ + 1)) * εN := by
  intro θ hθ
  have hδ : 0 < δ := by
    have := hc.delta_pos
    exact pos_of_mul_pos_right this hs0.le |>.trans_le le_rfl
  have hr : 0 < r := hδ.trans hδr
  have hd : 0 < (1 - s) * δ := mul_pos (by linarith) hδ
  set r' := r - (1 - s) * δ with hr'
  have hsub : complexStrip n r' ⊆ complexStrip n r := fun z hz =>
    Geometry.complexStrip_sub_subset hd.le hz
  have hsδ : s * δ < r' := by rw [hr']; nlinarith
  have hrr : r' - s * δ = r - δ := by rw [hr']; ring
  have hdiff : DifferentiableOn ℂ (lagrangeMat K) (complexStrip n r') :=
    (Exactness.differentiableOn_lagrangeMat hK).mono hsub
  have hper : IsPeriodicOn (lagrangeMat K) r' := fun i z hz =>
    periodic_lagrangeMat hKp i z (hsub hz)
  have havg : avg (lagrangeMat K) = 0 := (exactness hS hr hK hKp hK𝔅).1
  have hderiv : ∀ z ∈ complexStrip n r',
      ‖fderiv ℂ (lagrangeMat K) z (fun l => (ω l : ℂ))‖ ≤ 2 * (n - 1) * (((1 - s) * δ)⁻¹ * εN) := by
    intro z hz
    rw [fderiv_lagrangeMat_eq_etaN hS hK hK𝔅 (hsub hz), norm_neg]
    exact norm_etaNDeriv_sub_transpose_le hn hS hK hK𝔅 hd hηN z hz
  have hap := hc.apriori ω hω hsδ (lagrangeMat K) _ hdiff hper havg hderiv θ (by rw [hrr]; exact hθ)
  refine hap.trans (le_of_eq ?_)
  have hsκ : 0 < s ^ κ := Real.rpow_pos_of_pos hs0 _
  have h1s : 0 < 1 - s := by linarith
  have e1 : (s * δ) ^ (-κ) = (s ^ κ)⁻¹ * δ ^ (-κ) := by
    rw [Real.mul_rpow hs0.le hδ.le, Real.rpow_neg hs0.le]
  have e2 : δ ^ (-(κ + 1)) = δ ^ (-κ) * δ⁻¹ := by
    rw [show -(κ + 1) = -κ + (-1) by ring, Real.rpow_add hδ, Real.rpow_neg_one]
  rw [e1, e2]
  field_simp

end Lagrange

end KAM.Sharp2

end
