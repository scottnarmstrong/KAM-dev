/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.SmallDiv.Defs
public import KAM.Sharp.Frame
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Geometry of route A with refined data

The geometry lemmas of route A (items L1 and L2 of `bp:p2s2:constantsA`):

* `fderiv_lagrange_eq`, `norm_fderiv_lagrange_le`: `∂_ω Ω_K = ∂ηᴺ - (∂ηᴺ)ᵀ`, with the sign of
  `KAM.Apost.Identities.fi_dLagrange` (the sign in `bp:p2s2:omega` is the one of its own `Ω_K`; the
  norm is unaffected), so the row sums of `∂_ω Ω_K` are at most `2(n - 1) ε_N/δ` on `T_{r-δ}`;
* `norm_lagrangeMat_le`: `|Ω_K| ≤ 2(n - 1) c ε_N/(γ δ^{κ+1})` on `T_{r-2δ}` for a small-divisor
  constant `c` at the bite `δ` (`bp:p2s2:omega` with the Cauchy bite `δ`);
* `norm_symDefect_le`: `|E_sym| ≤ max {1, σ_B²} |Ω_K|`;
* `norm_redDefect_le`: `|E_red| ≤ n max {σ_{Nᵀ}, σ_{Lᵀ} + 2σ_N} ε/δ`, the refined form of
  `KAM.Sharp.FrameSharp.geo_ered_sep`.

These are the route-A statements; the route-B statement of the same identity is B2's
`norm_lagrangeMat_le_etaN`, which has a different bite pattern.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2.RouteA

open KAM KAM.Torus KAM.Apost KAM.Sharp

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r δ ε : ℝ} {θ : Fin n → ℂ}

/-- The first term of `∂_j ηᴺ`: `∑_s (∂_j L)_{s i} (Ω₀ Z)_s`, symmetric in `i, j`. -/
theorem mixed_symm (hK : DifferentiableOn ℂ K (complexStrip n r)) (hθ : θ ∈ complexStrip n r)
    (w : Fin n ⊕ Fin n → ℂ) (i j : Fin n) :
    ((fderiv ℂ (tangentMat K) θ (Pi.single j 1))ᵀ *ᵥ w) i =
      ((fderiv ℂ (tangentMat K) θ (Pi.single i 1))ᵀ *ᵥ w) j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Identities.fderiv_tangentMat_apply hK hθ, Identities.fderiv_tangentMat_apply hK hθ,
    fderiv_apply_comm_of_differentiableOn (isOpen_complexStrip n r) hK hθ]

/-- `∂_j ηᴺ_i = ∑_s (∂_j L)_{s i} (Ω₀ Z)_s + (Lᵀ Ω₀ DE)_{ij}`, `Z = sumVec E`. -/
theorem fderiv_etaN_entry (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hθ : θ ∈ complexStrip n r) (i j : Fin n) :
    fderiv ℂ (etaN h K ω) θ (Pi.single j 1) i =
      ((fderiv ℂ (tangentMat K) θ (Pi.single j 1))ᵀ *ᵥ
        (omegaZeroMatrix n *ᵥ sumVec n (invarianceError h K ω θ))) i +
      ((tangentMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ) i j := by
  have hnhds := (isOpen_complexStrip n r).mem_nhds hθ
  have hL : DifferentiableAt ℂ (tangentMat K) θ :=
    (differentiableOn_tangentMat hK).differentiableAt hnhds
  have hLt : DifferentiableAt ℂ (fun y => (tangentMat K y)ᵀ) θ := hL.matrix_transpose
  have hLtO : DifferentiableAt ℂ (fun y => (tangentMat K y)ᵀ * omegaZeroMatrix n) θ :=
    hLt.matrix_mul (differentiableAt_const _)
  have hE : DifferentiableAt ℂ (invarianceError h K ω) θ :=
    Identities.differentiableAt_invarianceError hS hK hK𝔅 hθ
  have hZ : DifferentiableAt ℂ (fun y => sumVec n (invarianceError h K ω y)) θ :=
    (sumVecIso n).differentiable.differentiableAt.comp θ hE
  have hfun : etaN h K ω =
      fun y => ((tangentMat K y)ᵀ * omegaZeroMatrix n) *ᵥ sumVec n (invarianceError h K ω y) := rfl
  rw [hfun, fderiv_matrix_mulVec_apply hLtO hZ, fderiv_matrix_mul_const_apply hLt,
    fderiv_matrix_transpose_apply]
  have hF : fderiv ℂ (fun y => sumVec n (invarianceError h K ω y)) θ (Pi.single j 1) =
      fun s => errDerivMat h K ω θ s j := by
    funext s
    rw [Geometry.errDerivMat_eq_of]
    rfl
  rw [hF, Pi.add_apply, ← Matrix.mulVec_mulVec]
  congr 1

/-- `∂_ω Ω_K = ∂ηᴺ - (∂ηᴺ)ᵀ`, entrywise. -/
theorem fderiv_lagrange_eq (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hθ : θ ∈ complexStrip n r) (i j : Fin n) :
    fderiv ℂ (lagrangeMat K) θ (fun l => (ω l : ℂ)) i j =
      fderiv ℂ (etaN h K ω) θ (Pi.single i 1) j - fderiv ℂ (etaN h K ω) θ (Pi.single j 1) i := by
  rw [Identities.fi_dLagrange hS hK hK𝔅 hθ, fderiv_etaN_entry hS hK hK𝔅 hθ i j,
    fderiv_etaN_entry hS hK hK𝔅 hθ j i, mixed_symm hK hθ _ j i]
  have hT : (errDerivMat h K ω θ)ᵀ * omegaZeroMatrix n * tangentMat K θ =
      -((tangentMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, omegaZeroMatrix_transpose,
        Matrix.transpose_transpose]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  rw [hT, Matrix.sub_apply, Matrix.neg_apply, Matrix.neg_apply, Matrix.transpose_apply]
  ring

/-- The row sums of `∂_ω Ω_K` are at most `2(n - 1) ε_N/δ` on `T_{r-δ}` (`bp:p2s2:omega`,
step `step:p2s2:om-b`: the diagonal vanishes, every other entry is at most `2 ε_N/δ`). -/
theorem norm_fderiv_lagrange_le (hS : Standing n τ M σK σB σT 𝔅 h ω γ) (hn : 1 ≤ n)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hη : DifferentiableOn ℂ (etaN h K ω) (complexStrip n r)) {εN : ℝ}
    (hb : ∀ θ ∈ complexStrip n r, ‖etaN h K ω θ‖ ≤ εN) (hδ : 0 < δ)
    (hθ : θ ∈ complexStrip n (r - δ)) :
    ‖fderiv ℂ (lagrangeMat K) θ (fun l => (ω l : ℂ))‖ ≤ 2 * ((n : ℝ) - 1) * εN / δ := by
  have hθr : θ ∈ complexStrip n r := Geometry.complexStrip_sub_subset hδ.le hθ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hεN : 0 ≤ εN := (norm_nonneg _).trans (hb θ hθr)
  have hC := (cauchy_strip hη hb hδ).1
  have hent : ∀ i j : Fin n, ‖fderiv ℂ (etaN h K ω) θ (Pi.single i 1) j‖ ≤ δ⁻¹ * εN :=
    fun i j => (norm_le_pi_norm _ j).trans (hC i θ hθ)
  have hoff : ∀ i j : Fin n, ‖fderiv ℂ (lagrangeMat K) θ (fun l => (ω l : ℂ)) i j‖ ≤
      if j = i then 0 else 2 * (δ⁻¹ * εN) := by
    intro i j
    rw [fderiv_lagrange_eq hS hK hK𝔅 hθr]
    split_ifs with hji
    · subst hji
      simp
    · refine (norm_sub_le _ _).trans ?_
      linarith [hent i j, hent j i]
  have h0 : 0 ≤ 2 * ((n : ℝ) - 1) * εN / δ := by
    have : 0 ≤ (n : ℝ) - 1 := by linarith
    positivity
  refine (norm_le_iff_forall_rowSum h0).2 fun i => ?_
  calc ∑ j, ‖fderiv ℂ (lagrangeMat K) θ (fun l => (ω l : ℂ)) i j‖
      ≤ ∑ j, (if j = i then 0 else 2 * (δ⁻¹ * εN)) := Finset.sum_le_sum fun j _ => hoff i j
    _ = ((n : ℝ) - 1) * (2 * (δ⁻¹ * εN)) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
          Finset.filter_ne' Finset.univ i, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hn, Nat.cast_one]
    _ = 2 * ((n : ℝ) - 1) * εN / δ := by field_simp

/-- `bp:p2s2:omega` with the Cauchy bite `δ`: `|Ω_K| ≤ 2(n - 1) c ε_N/(γ δ^{κ+1})` on `T_{r-2δ}`. -/
theorem norm_lagrangeMat_le {κ c εN : ℝ} {Ω : Set (Fin n → ℝ)}
    (hS : Standing n τ M σK σB σT 𝔅 h ω γ) (hn : 1 ≤ n) (hc : SDConst n κ γ δ c Ω) (hω : ω ∈ Ω)
    (hr : 0 < r) (h2δ : 2 * δ < r) (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKp : IsPrimaryOnStrip K r) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hη : DifferentiableOn ℂ (etaN h K ω) (complexStrip n r))
    (hb : ∀ θ ∈ complexStrip n r, ‖etaN h K ω θ‖ ≤ εN) :
    ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖lagrangeMat K θ‖ ≤ 2 * ((n : ℝ) - 1) * c * εN / (γ * δ ^ (κ + 1)) := by
  intro θ hθ
  have hδ := hc.delta_pos
  have hγ := hS.gamma_pos
  have hθ' : θ ∈ complexStrip n (r - δ - δ) := by
    rwa [show r - δ - δ = r - 2 * δ by ring]
  have hdiff : DifferentiableOn ℂ (lagrangeMat K) (complexStrip n (r - δ)) :=
    (Exactness.differentiableOn_lagrangeMat hK).mono
      fun _ hz => Geometry.complexStrip_sub_subset hδ.le hz
  have hper : IsPeriodicOn (lagrangeMat K) (r - δ) := fun i z hz =>
    periodic_lagrangeMat hKp i z (Geometry.complexStrip_sub_subset hδ.le hz)
  have havg : avg (lagrangeMat K) = 0 := (exactness hS hr hK hKp hK𝔅).1
  have hcoh := hc.apriori ω hω (r := r - δ) (by linarith) (lagrangeMat K)
    (2 * ((n : ℝ) - 1) * εN / δ) hdiff hper havg
    (fun θ hθ => norm_fderiv_lagrange_le hS hn hK hK𝔅 hη hb hδ hθ) θ hθ'
  have hδκ : 0 < δ ^ κ := Real.rpow_pos_of_pos hδ _
  calc ‖lagrangeMat K θ‖ ≤ c * γ⁻¹ * δ ^ (-κ) * (2 * ((n : ℝ) - 1) * εN / δ) := hcoh
    _ = 2 * ((n : ℝ) - 1) * c * εN / (γ * δ ^ (κ + 1)) := by
      rw [Real.rpow_neg hδ.le, Real.rpow_add_one hδ.ne']
      field_simp

/-- `|E_sym| ≤ max {1, σ_B²} |Ω_K|`. -/
theorem norm_symDefect_le {sB w : ℝ} (hG : IsUnit (gramMatrix K θ).det)
    (hB : ‖(gramMatrix K θ)⁻¹‖ ≤ sB) (hΩ : ‖lagrangeMat K θ‖ ≤ w) :
    ‖symDefect K θ‖ ≤ max 1 (sB ^ 2) * w := by
  have hsB : 0 ≤ sB := (norm_nonneg _).trans hB
  have hw : 0 ≤ w := (norm_nonneg _).trans hΩ
  have hBB : ‖(gramMatrix K θ)⁻¹‖ ^ 2 ≤ sB ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hB 2
  rw [Identities.fi_symDefect K hG, Tools.norm_fromBlocks_diagonal]
  refine max_le ?_ ?_
  · calc ‖lagrangeMat K θ‖ ≤ 1 * w := by rw [one_mul]; exact hΩ
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hw
  · calc ‖(gramMatrix K θ)⁻¹ * lagrangeMat K θ * (gramMatrix K θ)⁻¹‖
        ≤ ‖(gramMatrix K θ)⁻¹‖ * ‖lagrangeMat K θ‖ * ‖(gramMatrix K θ)⁻¹‖ :=
          (Matrix.linfty_opNorm_mul _ _).trans
            (mul_le_mul_of_nonneg_right (Matrix.linfty_opNorm_mul _ _) (norm_nonneg _))
      _ = ‖(gramMatrix K θ)⁻¹‖ ^ 2 * ‖lagrangeMat K θ‖ := by ring
      _ ≤ sB ^ 2 * w := mul_le_mul hBB hΩ (norm_nonneg _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hw

/-- The refined `|E_red| ≤ n max {σ_{Nᵀ}, σ_{Lᵀ} + 2σ_N} ε/δ` from `|DE| ≤ nε/δ`,
`|(DE)ᵀ| ≤ 2nε/δ` and the caps of `Lᵀ`, `N`, `Nᵀ`. -/
theorem norm_redDefect_le {sLt sN sNt : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hDE : ‖errDerivMat h K ω θ‖ ≤ n * ε / δ) (hDEt : ‖(errDerivMat h K ω θ)ᵀ‖ ≤ 2 * n * ε / δ)
    (hLt : ‖(tangentMat K θ)ᵀ‖ ≤ sLt) (hN : ‖normalMat K θ‖ ≤ sN)
    (hNt : ‖(normalMat K θ)ᵀ‖ ≤ sNt) :
    ‖redDefect h K ω θ‖ ≤ (n : ℝ) * max sNt (sLt + 2 * sN) * ε / δ := by
  have nm := @FrameSharp.norm_mul_le_of_le
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsLt : 0 ≤ sLt := (norm_nonneg _).trans hLt
  have hsN : 0 ≤ sN := (norm_nonneg _).trans hN
  have hsNt : 0 ≤ sNt := (norm_nonneg _).trans hNt
  have hεδ : 0 ≤ ε / δ := div_nonneg hε hδ.le
  have hmx : 0 ≤ (n : ℝ) * (ε / δ) := by positivity
  have r1 : ‖(normalMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ‖ ≤
      sNt * (n * ε / δ) := by
    refine nm ?_ hDE
    rw [norm_mul_omegaZeroMatrix]
    exact hNt
  have a1 : ‖(tangentMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ‖ ≤ sLt * (n * ε / δ) := by
    refine nm ?_ hDE
    rw [norm_mul_omegaZeroMatrix]
    exact hLt
  have a2 : ‖(errDerivMat h K ω θ)ᵀ * omegaZeroMatrix n * normalMat K θ‖ ≤
      2 * n * ε / δ * sN := by
    refine nm ?_ hN
    rw [norm_mul_omegaZeroMatrix]
    exact hDEt
  have e1 : sNt * (n * ε / δ) = sNt * (n * (ε / δ)) := by ring
  have e2 : sLt * (n * ε / δ) + 2 * n * ε / δ * sN = (sLt + 2 * sN) * (n * (ε / δ)) := by ring
  have e3 : (n : ℝ) * max sNt (sLt + 2 * sN) * ε / δ = max sNt (sLt + 2 * sN) * (n * (ε / δ)) := by
    ring
  unfold redDefect
  refine (norm_fromBlocks_le _ _ _ _).trans ?_
  rw [norm_zero, add_zero, norm_neg, e3]
  refine max_le ?_ ?_
  · rw [e1] at r1
    exact r1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hmx)
  · have := add_le_add a1 a2
    rw [e2] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hmx)

end KAM.Sharp2.RouteA

end
