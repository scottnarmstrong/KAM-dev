/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Apost.Hamiltonian
public import KAM.Apost.Constants
public import KAM.Apost.Tools
public import KAM.Strip.Bridges
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The frequency bound and the bounds on the frame

Blueprint Part 2, Lemmas `bp:p2:frequency` (`KAM.Apost.frequency`) and `bp:p2:frame-basic`
(`KAM.Apost.frame_basic`). Write `𝔪 = mSize M σK σB σT`, `L = DK`, `B = G⁻¹`, `N = Ω₀ L B` and
`P = (L N)`.

* `frequency`: if `K` maps `T_r` into `𝔅` and satisfies (A3), (A4), (A6) there with `ε ≤ 1`, then
  `γ ≤ |ω| ≤ 2 n σ_K σ_B (M + ε) ≤ Θ`. From `E = X_h(K) - L ω` and `B Lᵀ L = I` one gets
  `ω = B Lᵀ (X_h(K) - E)` (`KAM.Apost.FrameAux.ofReal_eq_inv_mul_transpose_mulVec`); the upper
  bound is a product of norms, the lower bound is the Diophantine inequality at `k = e₁`.
* `frame_basic`: for `K` holomorphic on `T_r` with (A2)–(A4):
  (a) `L, G, E, A, Ω_K, B, N, P, X_N, T, E_sym, Q, η` are holomorphic on `T_r`, `B` is symmetric and
  `T` is continuous on `ℝⁿ`;
  (b) `|L| ≤ 𝔪`, `|Lᵀ| ≤ 2n𝔪`, `|B| ≤ 𝔪`, `|N| ≤ 𝔪²`, `|Nᵀ| ≤ 2n𝔪²`, `|P| ≤ 2𝔪²`, `|A| ≤ 𝔪`;
  (c) `|ηᴸ| ≤ 2n𝔪²ε`, `|ηᴺ| ≤ 2n𝔪ε` when `|E| ≤ ε`;
  (d) `|X_N| ≤ C_X/δ`, `|T| ≤ C_T/δ` on `T_{r-δ}` when `|ω| ≤ Θ`, by the Cauchy estimate for
  `∂_ω N` (`KAM.cauchy_corollaries_directional_real`).

Each item is a separate helper lemma in the namespace `KAM.Apost.FrameAux`; the two nodes assemble
them as conjunctions in the order of the blueprint. The matrix norm is the operator norm of
`open scoped Matrix.Norms.Operator` (maximum absolute row sum), the vector norm is the max norm.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology

namespace KAM.Apost

open KAM.Torus

namespace FrameAux

/-! ### Norm bookkeeping -/

section Norms

variable {n : ℕ}

/-- The real vector `ω` as a complex vector has the same max norm. -/
theorem norm_ofReal_vec (ω : Fin n → ℝ) : ‖fun i => (ω i : ℂ)‖ = ‖ω‖ := by
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    rw [Complex.norm_real]
    exact norm_le_pi_norm ω i
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    simpa using norm_le_pi_norm (fun i => (ω i : ℂ)) i

/-- `‖L‖ = ‖DK‖`: the matrix `L` has the operator norm of the derivative. -/
theorem norm_tangentMat (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ) :
    ‖tangentMat K θ‖ = ‖fderiv ℂ K θ‖ :=
  norm_colMat _

/-- `‖A‖ = ‖DX_h ∘ K‖`: the matrix `A` has the operator norm of the derivative of `X_h`. -/
theorem norm_linMat (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ) :
    ‖linMat h K θ‖ = ‖fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ)‖ :=
  norm_sqMat _

/-- The transpose of a matrix with `2n` rows has norm at most `2n` times the norm. -/
theorem norm_transpose_le_two_mul {κ : Type*} [Fintype κ] (A : Matrix (Fin n ⊕ Fin n) κ ℂ) :
    ‖Aᵀ‖ ≤ 2 * n * ‖A‖ := by
  refine (norm_transpose_le_card_mul A).trans (le_of_eq ?_)
  rw [Fintype.card_sum, Fintype.card_fin]
  push_cast
  ring

/-- The max norm of a `sumVec` image of a difference is at most the sum of the norms. -/
theorem norm_sumVec_sub_le (u v : (Fin n → ℂ) × (Fin n → ℂ)) :
    ‖sumVec n u - sumVec n v‖ ≤ ‖u‖ + ‖v‖ := by
  rw [← map_sub, norm_sumVec]
  exact norm_sub_le u v

end Norms

/-! ### The frequency bound (`bp:p2:frequency`) -/

section Frequency

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- Step `step:p2:freq-solve`: `ω = B Lᵀ (X_h(K) - E)` at every `θ` with `det G` a unit. -/
theorem ofReal_eq_inv_mul_transpose_mulVec {θ : Fin n → ℂ} (hG : IsUnit (gramMatrix K θ).det) :
    (fun l => (ω l : ℂ)) = ((gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ) *ᵥ
      (sumVec n (hamiltonianVectorFieldℂ h (K θ)) - sumVec n (invarianceError h K ω θ)) := by
  rw [sumVec_invarianceError h K ω θ, sub_sub_cancel, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    ← gramMatrix_eq_tangentMat_transpose_mul, inv_gramMatrix_mul K hG, Matrix.one_mulVec]

/-- Step `step:p2:freq-upper` at one point `θ`. -/
theorem norm_le_of_pointwise {θ : Fin n → ℂ} {ε : ℝ} (hG : IsUnit (gramMatrix K θ).det)
    (hX : ‖hamiltonianVectorFieldℂ h (K θ)‖ ≤ M) (hE : ‖invarianceError h K ω θ‖ ≤ ε)
    (hL : ‖fderiv ℂ K θ‖ ≤ σK) (hB : ‖(gramMatrix K θ)⁻¹‖ ≤ σB) :
    ‖ω‖ ≤ 2 * n * σK * σB * (M + ε) := by
  have hK0 : 0 ≤ σK := (norm_nonneg _).trans hL
  have hB0 : 0 ≤ σB := (norm_nonneg _).trans hB
  have hv : ‖sumVec n (hamiltonianVectorFieldℂ h (K θ)) - sumVec n (invarianceError h K ω θ)‖ ≤
      M + ε := (norm_sumVec_sub_le _ _).trans (add_le_add hX hE)
  have hLT : ‖(tangentMat K θ)ᵀ‖ ≤ 2 * n * σK :=
    (norm_transpose_le_two_mul _).trans (by
      rw [norm_tangentMat]
      gcongr)
  have hBL : ‖(gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ‖ ≤ σB * (2 * n * σK) :=
    (Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul hB hLT (norm_nonneg _) hB0)
  have hε0 : 0 ≤ M + ε := (norm_nonneg _).trans hv
  rw [← norm_ofReal_vec, ofReal_eq_inv_mul_transpose_mulVec (h := h) hG]
  calc _ ≤ ‖(gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ‖ * _ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ σB * (2 * n * σK) * (M + ε) := mul_le_mul hBL hv (norm_nonneg _) (by positivity)
    _ = 2 * n * σK * σB * (M + ε) := by ring

/-- Step `step:p2:freq-lower`: `γ ≤ |ω|`, the Diophantine inequality at `k = e₁`. -/
theorem le_norm_of_dio (hn : 2 ≤ n) {τ : ℝ} (hdio : IsDiophantine γ τ ω) : γ ≤ ‖ω‖ := by
  have hn0 : 0 < n := by omega
  set i₀ : Fin n := ⟨0, hn0⟩ with hi₀
  have hk : (Pi.single i₀ (1 : ℤ) : Fin n → ℤ) ≠ 0 := by
    intro h0
    have := congrFun h0 i₀
    simp at this
  have h1 := hdio _ hk
  have hsum : (∑ i, |(((Pi.single i₀ (1 : ℤ) : Fin n → ℤ) i : ℤ) : ℝ)|) = 1 := by
    rw [Finset.sum_eq_single i₀ (fun j _ hj => by simp [hj]) (by simp)]
    simp
  have hsum2 : (∑ i, (((Pi.single i₀ (1 : ℤ) : Fin n → ℤ) i : ℤ) : ℝ) * ω i) = ω i₀ := by
    simp [Pi.single_apply]
  rw [hsum, hsum2, Real.one_rpow, div_one] at h1
  exact h1.trans ((le_abs_self _).trans (by simpa using norm_le_pi_norm ω i₀))

/-- The arithmetic `2nσ_Kσ_B(M + ε) ≤ Θ` for `M + ε ≤ 2𝔪`. -/
theorem two_mul_le_Theta (hP : Params n τ M σK σB σT) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1) :
    2 * n * σK * σB * (M + ε) ≤ Theta n M σK σB σT := by
  have hm := one_le_mSize (M := M) (σK := σK) (σB := σB) (σT := σT)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hK := σK_le_mSize (M := M) (σK := σK) (σB := σB) (σT := σT)
  have hB := σB_le_mSize (M := M) (σK := σK) (σB := σB) (σT := σT)
  have hM := M_le_mSize (M := M) (σK := σK) (σB := σB) (σT := σT)
  have hK0 := hP.σK_pos.le
  have hB0 := hP.σB_pos.le
  have hMε : M + ε ≤ 2 * mSize M σK σB σT := by linarith
  have hMε0 : 0 ≤ M + ε := by have := hP.M_pos; positivity
  calc 2 * n * σK * σB * (M + ε)
      ≤ 2 * n * mSize M σK σB σT * mSize M σK σB σT * (2 * mSize M σK σB σT) := by gcongr
    _ = Theta n M σK σB σT := by unfold Theta; ring

end Frequency

/-! ### Pointwise bounds (`step:p2:fb-bounds`, `step:p2:fb-eta`) -/

section Bounds

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}

theorem mSize_nonneg : 0 ≤ mSize M σK σB σT := zero_le_one.trans one_le_mSize

/-- `‖L‖ ≤ σ_K ≤ 𝔪`. -/
theorem norm_tangentMat_le (hL : ‖fderiv ℂ K θ‖ ≤ σK) :
    ‖tangentMat K θ‖ ≤ mSize M σK σB σT :=
  (norm_tangentMat K θ).le.trans (hL.trans σK_le_mSize)

/-- `‖Lᵀ‖ ≤ 2n𝔪`. -/
theorem norm_transpose_tangentMat_le (hL : ‖fderiv ℂ K θ‖ ≤ σK) :
    ‖(tangentMat K θ)ᵀ‖ ≤ 2 * n * mSize M σK σB σT :=
  (norm_transpose_le_two_mul _).trans
    (mul_le_mul_of_nonneg_left (norm_tangentMat_le hL) (by positivity))

/-- `‖B‖ ≤ σ_B ≤ 𝔪`. -/
theorem norm_inv_gramMatrix_le (hB : ‖(gramMatrix K θ)⁻¹‖ ≤ σB) :
    ‖(gramMatrix K θ)⁻¹‖ ≤ mSize M σK σB σT :=
  hB.trans σB_le_mSize

/-- `‖N‖ ≤ ‖Ω₀‖ ‖L‖ ‖B‖ ≤ 𝔪²`. -/
theorem norm_normalMat_le (hL : ‖fderiv ℂ K θ‖ ≤ σK) (hB : ‖(gramMatrix K θ)⁻¹‖ ≤ σB) :
    ‖normalMat K θ‖ ≤ mSize M σK σB σT ^ 2 := by
  calc ‖normalMat K θ‖
      ≤ ‖omegaZeroMatrix n * tangentMat K θ‖ * ‖(gramMatrix K θ)⁻¹‖ :=
        Matrix.linfty_opNorm_mul _ _
    _ = ‖tangentMat K θ‖ * ‖(gramMatrix K θ)⁻¹‖ := by rw [norm_omegaZeroMatrix_mul]
    _ ≤ mSize M σK σB σT * mSize M σK σB σT :=
        mul_le_mul (norm_tangentMat_le hL) (norm_inv_gramMatrix_le hB) (norm_nonneg _)
          mSize_nonneg
    _ = mSize M σK σB σT ^ 2 := (sq _).symm

/-- `‖Nᵀ‖ ≤ 2n𝔪²`. -/
theorem norm_transpose_normalMat_le (hL : ‖fderiv ℂ K θ‖ ≤ σK)
    (hB : ‖(gramMatrix K θ)⁻¹‖ ≤ σB) :
    ‖(normalMat K θ)ᵀ‖ ≤ 2 * n * mSize M σK σB σT ^ 2 :=
  (norm_transpose_le_two_mul _).trans
    (mul_le_mul_of_nonneg_left (norm_normalMat_le hL hB) (by positivity))

/-- `‖P‖ ≤ ‖L‖ + ‖N‖ ≤ 2𝔪²`. -/
theorem norm_frameMat_le (hL : ‖fderiv ℂ K θ‖ ≤ σK) (hB : ‖(gramMatrix K θ)⁻¹‖ ≤ σB) :
    ‖frameMat K θ‖ ≤ 2 * mSize M σK σB σT ^ 2 := by
  have hm : (1 : ℝ) ≤ mSize M σK σB σT := one_le_mSize
  have h1 := norm_tangentMat_le (M := M) (σB := σB) (σT := σT) hL
  have h2 := norm_normalMat_le (M := M) (σT := σT) hL hB
  calc ‖frameMat K θ‖ ≤ ‖tangentMat K θ‖ + ‖normalMat K θ‖ := Tools.norm_fromCols_le_add _ _
    _ ≤ mSize M σK σB σT + mSize M σK σB σT ^ 2 := add_le_add h1 h2
    _ ≤ 2 * mSize M σK σB σT ^ 2 := by nlinarith

/-- `‖A‖ ≤ M ≤ 𝔪` when `K θ ∈ 𝔅`. -/
theorem norm_linMat_le (hS : Standing n τ M σK σB σT 𝔅 h ω γ) (hθ : K θ ∈ 𝔅) :
    ‖linMat h K θ‖ ≤ mSize M σK σB σT :=
  (norm_linMat h K θ).le.trans ((hS.bounds _ hθ).2.1.trans M_le_mSize)

/-- Step `step:p2:fb-eta`: `‖ηᴸ‖ ≤ ‖Nᵀ‖ ‖Ω₀‖ ‖E‖ ≤ 2n𝔪²ε`. -/
theorem norm_etaL_le (hL : ‖fderiv ℂ K θ‖ ≤ σK) (hB : ‖(gramMatrix K θ)⁻¹‖ ≤ σB) {ε : ℝ}
    (hE : ‖invarianceError h K ω θ‖ ≤ ε) :
    ‖etaL h K ω θ‖ ≤ 2 * n * mSize M σK σB σT ^ 2 * ε := by
  unfold etaL
  rw [norm_neg]
  refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
  rw [norm_mul_omegaZeroMatrix, norm_sumVec]
  exact mul_le_mul (norm_transpose_normalMat_le hL hB) hE (norm_nonneg _) (by positivity)

/-- Step `step:p2:fb-eta`: `‖ηᴺ‖ ≤ ‖Lᵀ‖ ‖Ω₀‖ ‖E‖ ≤ 2n𝔪ε`. -/
theorem norm_etaN_le (hL : ‖fderiv ℂ K θ‖ ≤ σK) {ε : ℝ}
    (hE : ‖invarianceError h K ω θ‖ ≤ ε) :
    ‖etaN h K ω θ‖ ≤ 2 * n * mSize M σK σB σT * ε := by
  unfold etaN
  refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
  rw [norm_mul_omegaZeroMatrix, norm_sumVec]
  exact mul_le_mul (norm_transpose_tangentMat_le hL) hE (norm_nonneg _)
    (mul_nonneg (by positivity) mSize_nonneg)

end Bounds

/-! ### Holomorphy (`step:p2:fb-holo`) -/

section Holomorphy

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r : ℝ}

/-- `E = X_h ∘ K - DK ω` is holomorphic on `T_r` when `K` is and `K(T_r) ⊆ 𝔅`. -/
theorem differentiableOn_invarianceError (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅) :
    DifferentiableOn ℂ (invarianceError h K ω) (complexStrip n r) := by
  have h1 : DifferentiableOn ℂ (fun θ => hamiltonianVectorFieldℂ h (K θ)) (complexStrip n r) :=
    (differentiableOn_ham hS).comp hK hK𝔅
  have h2 : DifferentiableOn ℂ (fun θ => fderiv ℂ K θ (fun i => (ω i : ℂ))) (complexStrip n r) :=
    (holomorphic_regularity (isOpen_complexStrip n r) hK).1.clm_apply (differentiableOn_const _)
  exact h1.sub h2

/-- `A = DX_h ∘ K` is holomorphic on `T_r` when `K` is and `K(T_r) ⊆ 𝔅`. -/
theorem differentiableOn_linMat (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅) :
    DifferentiableOn ℂ (linMat h K) (complexStrip n r) := by
  rw [differentiableOn_matrix_iff_entries]
  intro s t
  have h1 : DifferentiableOn ℂ (fun θ => fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ))
      (complexStrip n r) := (differentiableOn_fderiv_ham hS).comp hK hK𝔅
  have h2 : DifferentiableOn ℂ (fun θ => sumVec n (fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ)
      ((sumVec n).symm (Pi.single t 1)))) (complexStrip n r) :=
    (sumVecIso n).differentiable.comp_differentiableOn (h1.clm_apply (differentiableOn_const _))
  have h3 := differentiableOn_pi.1 h2 s
  simpa only [linMat, KAM.Head.sqMat_apply_entry] using h3

/-- `P = (L N)` is holomorphic when `L` and `N` are. -/
theorem differentiableOn_frameMat (hL : DifferentiableOn ℂ (tangentMat K) (complexStrip n r))
    (hN : DifferentiableOn ℂ (normalMat K) (complexStrip n r)) :
    DifferentiableOn ℂ (frameMat K) (complexStrip n r) := by
  rw [differentiableOn_matrix_iff_entries]
  rintro s (j | j)
  · exact differentiableOn_matrix_iff_entries.1 hL s j
  · exact differentiableOn_matrix_iff_entries.1 hN s j

/-- `X_N = A N - ∂_ω N` is holomorphic when `A` and `N` are. -/
theorem differentiableOn_normalFieldMat (hA : DifferentiableOn ℂ (linMat h K) (complexStrip n r))
    (hN : DifferentiableOn ℂ (normalMat K) (complexStrip n r)) :
    DifferentiableOn ℂ (normalFieldMat h K ω) (complexStrip n r) := by
  have hD : DifferentiableOn ℂ (fun θ => fderiv ℂ (normalMat K) θ (fun l => (ω l : ℂ)))
      (complexStrip n r) :=
    (holomorphic_regularity (isOpen_complexStrip n r) hN).1.clm_apply (differentiableOn_const _)
  exact (hA.matrix_mul hN).sub hD

/-- `T = Nᵀ Ω₀ X_N` is holomorphic on `T_r` (`bp:p2:frozen-agreement`). -/
theorem differentiableOn_torsion (hN : DifferentiableOn ℂ (normalMat K) (complexStrip n r))
    (hX : DifferentiableOn ℂ (normalFieldMat h K ω) (complexStrip n r)) :
    DifferentiableOn ℂ (torsion h K ω) (complexStrip n r) :=
  ((hN.matrix_transpose.matrix_mul (differentiableOn_const _)).matrix_mul hX).congr fun _ hθ =>
    torsion_eq_mat h K ω (hN.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ))

/-- `E_sym = Pᵀ Ω₀ P - Ω₀` is holomorphic when `P` is. -/
theorem differentiableOn_symDefect (hP : DifferentiableOn ℂ (frameMat K) (complexStrip n r)) :
    DifferentiableOn ℂ (symDefect K) (complexStrip n r) :=
  ((hP.matrix_transpose.matrix_mul (differentiableOn_const _)).matrix_mul hP).sub
    (differentiableOn_const _)

/-- `Q = -Ω₀ Pᵀ Ω₀` is holomorphic when `P` is. -/
theorem differentiableOn_reducer (hP : DifferentiableOn ℂ (frameMat K) (complexStrip n r)) :
    DifferentiableOn ℂ (reducer K) (complexStrip n r) :=
  (((differentiableOn_const _).matrix_mul hP.matrix_transpose).matrix_mul
    (differentiableOn_const _)).neg

/-- `η = Ω₀ Pᵀ Ω₀ E` is holomorphic when `P` and `E` are. -/
theorem differentiableOn_eta (hP : DifferentiableOn ℂ (frameMat K) (complexStrip n r))
    (hE : DifferentiableOn ℂ (invarianceError h K ω) (complexStrip n r)) :
    DifferentiableOn ℂ (eta h K ω) (complexStrip n r) :=
  (((differentiableOn_const _).matrix_mul hP.matrix_transpose).matrix_mul
    (differentiableOn_const _)).matrix_mulVec
    ((sumVecIso n).differentiable.comp_differentiableOn hE)

/-- `G` is symmetric, hence so is `B = G⁻¹`. -/
theorem transpose_inv_gramMatrix (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (θ : Fin n → ℂ) : ((gramMatrix K θ)⁻¹)ᵀ = (gramMatrix K θ)⁻¹ := by
  have hG : (gramMatrix K θ)ᵀ = gramMatrix K θ := by
    conv_lhs => rw [gramMatrix_eq_tangentMat_transpose_mul K θ]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose,
      ← gramMatrix_eq_tangentMat_transpose_mul K θ]
  rw [Matrix.transpose_nonsing_inv, hG]

/-- `T` is continuous on `ℝⁿ` (so `⟨T⟩` is defined), since it is holomorphic on `T_r ⊇ ℝⁿ`. -/
theorem continuous_torsion_real (hr : 0 < r)
    (hT : DifferentiableOn ℂ (torsion h K ω) (complexStrip n r)) :
    Continuous (fun x : Fin n → ℝ => torsion h K ω (fun i => (x i : ℂ))) :=
  hT.continuousOn.comp_continuous
    (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))
    (ofReal_mem_complexStrip hr)

end Holomorphy

/-! ### The torsion bound (`step:p2:fb-torsion`) -/

section Torsion

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r δ : ℝ}

/-- The arithmetic of `step:p2:fb-torsion`:
`𝔪 · 𝔪² + s δ⁻¹ 𝔪² ≤ 5n²𝔪⁵/δ` when `s ≤ n Θ = 4n²𝔪³`, `𝔪, n ≥ 1` and `δ ≤ 1`. -/
theorem arith_normalField {m ν s : ℝ} (hm : 1 ≤ m) (hν : 1 ≤ ν) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hs : s ≤ ν * (4 * ν * m ^ 3)) :
    m * m ^ 2 + s * δ⁻¹ * m ^ 2 ≤ 5 * ν ^ 2 * m ^ 5 / δ := by
  have hd : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδ1
  have hν2 : 1 ≤ ν ^ 2 := one_le_pow₀ hν
  have hm3 : m ^ 3 ≤ m ^ 5 := pow_le_pow_right₀ hm (by norm_num)
  have hm0 : 0 ≤ m := zero_le_one.trans hm
  have hA : m * m ^ 2 ≤ ν ^ 2 * m ^ 5 * δ⁻¹ :=
    calc m * m ^ 2 = m ^ 3 := by ring
      _ ≤ m ^ 5 := hm3
      _ = 1 * m ^ 5 * 1 := by ring
      _ ≤ ν ^ 2 * m ^ 5 * δ⁻¹ := by gcongr
  have hB : s * δ⁻¹ * m ^ 2 ≤ 4 * ν ^ 2 * m ^ 5 * δ⁻¹ :=
    calc s * δ⁻¹ * m ^ 2 ≤ (ν * (4 * ν * m ^ 3)) * δ⁻¹ * m ^ 2 := by gcongr
      _ = 4 * ν ^ 2 * m ^ 5 * δ⁻¹ := by ring
  calc m * m ^ 2 + s * δ⁻¹ * m ^ 2 ≤ 5 * ν ^ 2 * m ^ 5 * δ⁻¹ := by linarith
    _ = 5 * ν ^ 2 * m ^ 5 / δ := by rw [div_eq_mul_inv]

/-- Step `step:p2:fb-torsion`, first half: `‖X_N‖ ≤ C_X/δ` on `T_{r-δ}`, from the Cauchy estimate
for `∂_ω N` and the frequency bound `|ω| ≤ Θ`. -/
theorem norm_normalFieldMat_le (hP : Params n τ M σK σB σT)
    (hN : DifferentiableOn ℂ (normalMat K) (complexStrip n r))
    (hNb : ∀ θ ∈ complexStrip n r, ‖normalMat K θ‖ ≤ mSize M σK σB σT ^ 2)
    (hAb : ∀ θ ∈ complexStrip n r, ‖linMat h K θ‖ ≤ mSize M σK σB σT)
    (hω : ‖ω‖ ≤ Theta n M σK σB σT) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n (r - δ)) :
    ‖normalFieldMat h K ω θ‖ ≤ C_X n M σK σB σT / δ := by
  have hθr : θ ∈ complexStrip n r := fun i => (hθ i).trans (by linarith)
  have hdir := cauchy_corollaries_directional_real hN hNb hδ ω θ hθ
  have hsum : ∑ ℓ, |ω ℓ| ≤ n * Theta n M σK σB σT :=
    calc ∑ ℓ, |ω ℓ| ≤ ∑ _ℓ : Fin n, ‖ω‖ :=
          Finset.sum_le_sum fun ℓ _ => by simpa using norm_le_pi_norm ω ℓ
      _ = n * ‖ω‖ := by simp
      _ ≤ n * Theta n M σK σB σT := by gcongr
  have hdir' : ‖fderiv ℂ (normalMat K) θ (fun l => (ω l : ℂ))‖ ≤
      (n * Theta n M σK σB σT) * δ⁻¹ * mSize M σK σB σT ^ 2 :=
    hdir.trans (by gcongr)
  calc ‖normalFieldMat h K ω θ‖
      ≤ ‖linMat h K θ * normalMat K θ‖ + ‖fderiv ℂ (normalMat K) θ (fun l => (ω l : ℂ))‖ :=
        norm_sub_le _ _
    _ ≤ mSize M σK σB σT * mSize M σK σB σT ^ 2 +
        (n * Theta n M σK σB σT) * δ⁻¹ * mSize M σK σB σT ^ 2 :=
        add_le_add ((Matrix.linfty_opNorm_mul _ _).trans
          (mul_le_mul (hAb θ hθr) (hNb θ hθr) (norm_nonneg _) mSize_nonneg)) hdir'
    _ ≤ C_X n M σK σB σT / δ := by
        refine arith_normalField one_le_mSize hP.one_le_cast hδ hδ1 (le_of_eq ?_)
        unfold Theta
        rfl

/-- Step `step:p2:fb-torsion`, second half: `‖T‖ ≤ ‖Nᵀ‖ ‖X_N‖ ≤ C_T/δ`. -/
theorem norm_torsion_le {θ : Fin n → ℂ}
    (hT : torsion h K ω θ = (normalMat K θ)ᵀ * omegaZeroMatrix n * normalFieldMat h K ω θ)
    (hNT : ‖(normalMat K θ)ᵀ‖ ≤ 2 * n * mSize M σK σB σT ^ 2)
    (hX : ‖normalFieldMat h K ω θ‖ ≤ C_X n M σK σB σT / δ) :
    ‖torsion h K ω θ‖ ≤ C_T n M σK σB σT / δ := by
  rw [hT]
  calc ‖(normalMat K θ)ᵀ * omegaZeroMatrix n * normalFieldMat h K ω θ‖
      ≤ ‖(normalMat K θ)ᵀ * omegaZeroMatrix n‖ * ‖normalFieldMat h K ω θ‖ :=
        Matrix.linfty_opNorm_mul _ _
    _ = ‖(normalMat K θ)ᵀ‖ * ‖normalFieldMat h K ω θ‖ := by rw [norm_mul_omegaZeroMatrix]
    _ ≤ (2 * n * mSize M σK σB σT ^ 2) * (C_X n M σK σB σT / δ) :=
        mul_le_mul hNT hX (norm_nonneg _) (by positivity)
    _ = C_T n M σK σB σT / δ := by unfold C_T; ring

end Torsion

end FrameAux

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

/-- Blueprint `bp:p2:frequency`. -/
theorem frequency (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {r ε : ℝ} (hr : 0 < r) (hε : ε ≤ 1)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hA3 : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ σK)
    (hA4 : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB)
    (hA6 : ∀ θ ∈ complexStrip n r, ‖invarianceError h K ω θ‖ ≤ ε) :
    γ ≤ ‖ω‖ ∧ ‖ω‖ ≤ 2 * n * σK * σB * (M + ε) ∧
      2 * n * σK * σB * (M + ε) ≤ Theta n M σK σB σT := by
  have h0 : (0 : Fin n → ℂ) ∈ complexStrip n r := fun i => by simpa using hr
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hA6 0 h0)
  exact ⟨FrameAux.le_norm_of_dio hS.two_le hS.dio,
    FrameAux.norm_le_of_pointwise (hA4 0 h0).1 (hS.bounds _ (hK𝔅 0 h0)).1 (hA6 0 h0) (hA3 0 h0)
      (hA4 0 h0).2,
    FrameAux.two_mul_le_Theta hS.toParams hε0 hε⟩

/-- Blueprint `bp:p2:frame-basic`, items (a)–(d). -/
theorem frame_basic (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {r β : ℝ} (hr : 0 < r) (hβ : 0 < β)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hA2 : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ 𝔅)
    (hA3 : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ σK)
    (hA4 : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB) :
    (DifferentiableOn ℂ (tangentMat K) (complexStrip n r) ∧
      DifferentiableOn ℂ (gramMatrix K) (complexStrip n r) ∧
      DifferentiableOn ℂ (invarianceError h K ω) (complexStrip n r) ∧
      DifferentiableOn ℂ (linMat h K) (complexStrip n r) ∧
      DifferentiableOn ℂ (lagrangeMat K) (complexStrip n r) ∧
      DifferentiableOn ℂ (fun θ => (gramMatrix K θ)⁻¹) (complexStrip n r) ∧
      DifferentiableOn ℂ (normalMat K) (complexStrip n r) ∧
      DifferentiableOn ℂ (frameMat K) (complexStrip n r) ∧
      DifferentiableOn ℂ (normalFieldMat h K ω) (complexStrip n r) ∧
      DifferentiableOn ℂ (torsion h K ω) (complexStrip n r) ∧
      DifferentiableOn ℂ (symDefect K) (complexStrip n r) ∧
      DifferentiableOn ℂ (reducer K) (complexStrip n r) ∧
      DifferentiableOn ℂ (eta h K ω) (complexStrip n r) ∧
      (∀ θ ∈ complexStrip n r, ((gramMatrix K θ)⁻¹)ᵀ = (gramMatrix K θ)⁻¹) ∧
      Continuous (fun x : Fin n → ℝ => torsion h K ω (fun i => (x i : ℂ)))) ∧
    (∀ θ ∈ complexStrip n r,
      ‖tangentMat K θ‖ ≤ mSize M σK σB σT ∧ ‖(tangentMat K θ)ᵀ‖ ≤ 2 * n * mSize M σK σB σT ∧
      ‖(gramMatrix K θ)⁻¹‖ ≤ mSize M σK σB σT ∧ ‖normalMat K θ‖ ≤ mSize M σK σB σT ^ 2 ∧
      ‖(normalMat K θ)ᵀ‖ ≤ 2 * n * mSize M σK σB σT ^ 2 ∧
      ‖frameMat K θ‖ ≤ 2 * mSize M σK σB σT ^ 2 ∧ ‖linMat h K θ‖ ≤ mSize M σK σB σT) ∧
    (∀ ε, (∀ θ ∈ complexStrip n r, ‖invarianceError h K ω θ‖ ≤ ε) →
      ∀ θ ∈ complexStrip n r, ‖etaL h K ω θ‖ ≤ 2 * n * mSize M σK σB σT ^ 2 * ε ∧
        ‖etaN h K ω θ‖ ≤ 2 * n * mSize M σK σB σT * ε) ∧
    (‖ω‖ ≤ Theta n M σK σB σT → ∀ δ, 0 < δ → δ ≤ 1 → δ < r →
      ∀ θ ∈ complexStrip n (r - δ), ‖normalFieldMat h K ω θ‖ ≤ C_X n M σK σB σT / δ ∧
        ‖torsion h K ω θ‖ ≤ C_T n M σK σB σT / δ) := by
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅 := fun θ hθ => hA2 θ hθ (Metric.mem_ball_self hβ)
  have hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hA4 θ hθ).1
  have hLd := differentiableOn_tangentMat hK
  have hNd := differentiableOn_normalMat hK hG
  have hEd := FrameAux.differentiableOn_invarianceError hS hK hK𝔅
  have hAd := FrameAux.differentiableOn_linMat hS hK hK𝔅
  have hPd := FrameAux.differentiableOn_frameMat hLd hNd
  have hXd := FrameAux.differentiableOn_normalFieldMat (ω := ω) hAd hNd
  have hTd := FrameAux.differentiableOn_torsion hNd hXd
  have hNb : ∀ θ ∈ complexStrip n r, ‖normalMat K θ‖ ≤ mSize M σK σB σT ^ 2 :=
    fun θ hθ => FrameAux.norm_normalMat_le (hA3 θ hθ) (hA4 θ hθ).2
  have hAb : ∀ θ ∈ complexStrip n r, ‖linMat h K θ‖ ≤ mSize M σK σB σT :=
    fun θ hθ => FrameAux.norm_linMat_le hS (hK𝔅 θ hθ)
  refine ⟨⟨hLd, differentiableOn_gramMatrix hK, hEd, hAd, ?_, ?_, hNd, hPd, hXd, hTd,
    FrameAux.differentiableOn_symDefect hPd, FrameAux.differentiableOn_reducer hPd,
    FrameAux.differentiableOn_eta hPd hEd, fun θ _ => FrameAux.transpose_inv_gramMatrix K θ,
    FrameAux.continuous_torsion_real hr hTd⟩, ?_, ?_, ?_⟩
  · exact (hLd.matrix_transpose.matrix_mul (differentiableOn_const _)).matrix_mul hLd
  · exact (holomorphic_inverse (isOpen_complexStrip n r) (differentiableOn_gramMatrix hK)
      fun θ hθ => (hG θ hθ).ne_zero).1
  · intro θ hθ
    exact ⟨FrameAux.norm_tangentMat_le (hA3 θ hθ), FrameAux.norm_transpose_tangentMat_le (hA3 θ hθ),
      FrameAux.norm_inv_gramMatrix_le (hA4 θ hθ).2, hNb θ hθ,
      FrameAux.norm_transpose_normalMat_le (hA3 θ hθ) (hA4 θ hθ).2,
      FrameAux.norm_frameMat_le (hA3 θ hθ) (hA4 θ hθ).2, hAb θ hθ⟩
  · intro ε hε θ hθ
    exact ⟨FrameAux.norm_etaL_le (hA3 θ hθ) (hA4 θ hθ).2 (hε θ hθ),
      FrameAux.norm_etaN_le (hA3 θ hθ) (hε θ hθ)⟩
  · intro hω δ hδ hδ1 hδr θ hθ
    have hθr : θ ∈ complexStrip n r := fun i => (hθ i).trans (by linarith)
    have hX := FrameAux.norm_normalFieldMat_le hS.toParams hNd hNb hAb hω hδ hδ1 hθ
    exact ⟨hX, FrameAux.norm_torsion_le
      (torsion_eq_mat h K ω (hNd.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθr)))
      (FrameAux.norm_transpose_normalMat_le (hA3 θ hθr) (hA4 θ hθr).2) hX⟩

end KAM.Apost

end
