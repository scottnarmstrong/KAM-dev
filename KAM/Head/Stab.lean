/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.StabFrame
import KAM.Head.H1
import KAM.Head.HamiltonianField
import KAM.Matrix.Neumann
import KAM.Apost.PerturbationTorsion

/-!
# STAB: stability of the frame, the torsion and the twist under a small displacement

Blueprint Part 4, `bp:p4:stab`. Let `K` be holomorphic on `T_ρ` with
`|K - K⁰_{I_*}| ≤ η ≤ η_*(δ)`. The frame side (steps `step:p4:stab-small`, `-cauchy`, `-gram` and
`-frame`: the tangent frame, the Gram matrix, the normal frame and the bounds on `∂_ω L`,
`∂_ω N`) is in `KAM/Head/StabFrame.lean`. This file proves the remaining steps and assembles the
node.

* `KAM.Head.Stab.ball_subset_domainD` (`step:p4:stab-ball`): `B_μ(K θ) ⊆ 𝔇` since
  `B_μ(K θ) ⊆ B_{δ_*}(K⁰ θ)` and `KAM.Head.ball_unperturbedTorus_subset_domainD`.
* `KAM.Head.Stab.norm_fderivX_sub_le`, `KAM.Head.Stab.normalField_close` (`step:p4:stab-xn`): the
  mean value inequality for `DX_𝐡` on the convex ball `B_{δ_*}(K⁰ θ) ⊆ 𝔇`, where `|D²X_𝐡| ≤ M`
  (`KAM.Head.h1`), then `|X_N - X_N⁰| ≤ (2M + 12 n² M + 264 n² W_∞) η δ⁻² ≤ c_T η δ⁻²`.
* `KAM.Head.Stab.torsion_close` (`step:p4:stab-torsion`):
  `T - T⁰ = (N - N⁰)ᵀ Ω₀ X_N + (N⁰)ᵀ Ω₀ (X_N - X_N⁰)`, with the frozen torsion rewritten as
  `Nᵀ Ω₀ X_N` by `KAM.Torus.torsion_eq_mat`.
* `KAM.Head.Stab.twist_close` (`step:p4:stab-twist`): `|⟨T⟩ - ⟨T⁰⟩| ≤ c_T η δ⁻²` over the real unit
  cube, then the Neumann lemma with `|⟨T⁰⟩⁻¹| ≤ 2 L₊` (`KAM.Head.unperturbed`).
* `KAM.Head.stab` (`step:p4:stab-h2h4`): items (a)–(d) and, for `K` primary and real on reals, the
  hypotheses H2–H4 of G1 on `T_{ρ-δ}` in the frozen row-sum form (the row sums are bounded by the
  operator norms).

The proof is slightly sharper than the blueprint: `|∂_ω L| ≤ 4 n W η δ⁻²` instead of
`4 n² W η δ⁻²`, so the intermediate constants are smaller; the final constant is the blueprint's
`c_T = 304 n³ (M + W_∞ + 1)`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology KAM.Torus

namespace KAM.Head

namespace Stab

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
  {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ} {I : Fin n → ℝ}

/-! ### Step `step:p4:stab-ball` -/

/-- The ball of radius `μ` around `K θ` lies in `𝔇` when `|K θ - K⁰ θ| ≤ μ`, `θ ∈ T_{s/4}`. -/
theorem ball_subset_domainD (hr₀ : 0 < r₀) (hI : I ∈ B) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n (stripWidth s₀ / 4)) {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : ‖z - unperturbedTorus I θ‖ ≤ muParam s₀ r₀) :
    Metric.ball z (muParam s₀ r₀) ⊆ domainD n s₀ r₀ B := by
  refine Set.Subset.trans ?_ (ball_unperturbedTorus_subset_domainD hr₀ hI hθ)
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
  have h2 : muParam s₀ r₀ + muParam s₀ r₀ = deltaStar s₀ r₀ := by unfold muParam; ring
  calc ‖w - unperturbedTorus I θ‖ = ‖(w - z) + (z - unperturbedTorus I θ)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖w - z‖ + ‖z - unperturbedTorus I θ‖ := norm_add_le _ _
    _ < deltaStar s₀ r₀ := by linarith

/-! ### Step `step:p4:stab-xn` -/

/-- `‖DX_𝐡(z) - DX_𝐡(K⁰ θ)‖ ≤ M ‖z - K⁰ θ‖` for `z` in the ball of radius `δ_*` around `K⁰ θ`
(mean value inequality for `DX_𝐡`, with `|D²X_𝐡| ≤ M` on `𝔇`). -/
theorem norm_fderivX_sub_le (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε) (hε : ε ≤ 1)
    (hI : I ∈ B) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (stripWidth s₀ / 4))
    {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ Metric.ball (unperturbedTorus I θ) (deltaStar s₀ r₀)) :
    ‖fderiv ℂ (hamiltonianVectorFieldℂ (hbold h f)) z -
        fderiv ℂ (hamiltonianVectorFieldℂ (hbold h f)) (unperturbedTorus I θ)‖ ≤
      Mconst s₀ r₀ B h * ‖z - unperturbedTorus I θ‖ := by
  have hU := ball_unperturbedTorus_subset_domainD hD.r₀_pos hI hθ
  have hopen := isOpen_domainD n s₀ r₀ B
  obtain ⟨-, -, -, -, -, hM⟩ := h1 hD hP hε
  have hX : DifferentiableOn ℂ (hamiltonianVectorFieldℂ (hbold h f)) (domainD n s₀ r₀ B) :=
    differentiableOn_hamiltonianVectorField hopen (h1_differentiableOn hD hP)
  have hdX : DifferentiableOn ℂ (fderiv ℂ (hamiltonianVectorFieldℂ (hbold h f)))
      (domainD n s₀ r₀ B) := differentiableOn_fderiv_of_isOpen hopen hX
  have hA : ∀ x ∈ Metric.ball (unperturbedTorus I θ) (deltaStar s₀ r₀),
      ‖fderiv ℂ (fderiv ℂ (hamiltonianVectorFieldℂ (hbold h f))) x‖ ≤ Mconst s₀ r₀ B h := by
    intro x hx
    have := (hM x (hU hx)).2.2.2
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact this
  have hseg : segment ℝ (unperturbedTorus I θ) (unperturbedTorus I θ + (z - unperturbedTorus I θ))
      ⊆ Metric.ball (unperturbedTorus I θ) (deltaStar s₀ r₀) := by
    rw [add_sub_cancel]
    exact (convex_ball _ _).segment_subset (Metric.mem_ball_self
      (deltaStar_pos hD.s₀_pos hD.r₀_pos)) hz
  have := KAM.increments_open Metric.isOpen_ball (hdX.mono hU) hA hseg
  rwa [add_sub_cancel] at this


/-- `X_N⁰ = A⁰ N⁰`: the derivative term vanishes since `N⁰` is constant. -/
theorem normalFieldMat_unperturbed (I : Fin n → ℝ) (ω : Fin n → ℝ) (θ : Fin n → ℂ) :
    normalFieldMat (hbold h f) (unperturbedTorus I) ω θ =
      linMat (hbold h f) (unperturbedTorus I) θ * frameN0 n := by
  have hconst : normalMat (unperturbedTorus I) = fun _ => frameN0 n :=
    funext (normalMat_unperturbedTorus I)
  rw [normalFieldMat, hconst, fderiv_fun_const]
  simp

section Pointwise

variable (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε) (hε : ε ≤ 1) (hI : I ∈ B)
include hD hP hε hI

/-- `|A - A⁰| ≤ M η` where `A = DX_𝐡 ∘ K`, for `θ ∈ T_{s/4}` and `|K θ - K⁰ θ| ≤ η ≤ μ`. -/
theorem norm_linMat_sub_le {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n (stripWidth s₀ / 4)) {η : ℝ} (hη : η ≤ muParam s₀ r₀)
    (hKθ : ‖K θ - unperturbedTorus I θ‖ ≤ η) :
    ‖linMat (hbold h f) K θ - linMat (hbold h f) (unperturbedTorus I) θ‖ ≤
      Mconst s₀ r₀ B h * η := by
  have hμ : muParam s₀ r₀ < deltaStar s₀ r₀ := by
    have := deltaStar_pos hD.s₀_pos hD.r₀_pos
    unfold muParam; linarith
  have hz : K θ ∈ Metric.ball (unperturbedTorus I θ) (deltaStar s₀ r₀) := by
    rw [Metric.mem_ball, dist_eq_norm]; linarith
  have h1' := norm_fderivX_sub_le hD hP hε hI hθ hz
  have hM := (Parameters.Mconst_pos (B := B) (h := h) hD.s₀_pos hD.r₀_pos).le
  unfold linMat
  rw [← KAM.Apost.PerturbationAux.sqMat_sub, norm_sqMat]
  exact h1'.trans (mul_le_mul_of_nonneg_left hKθ hM)

/-- `|A⁰| ≤ M` for `θ ∈ T_{s/4}`. -/
theorem norm_linMat_unperturbed_le {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (stripWidth s₀ / 4)) :
    ‖linMat (hbold h f) (unperturbedTorus I) θ‖ ≤ Mconst s₀ r₀ B h := by
  obtain ⟨-, -, -, -, -, hM⟩ := h1 hD hP hε
  have hθ2 : θ ∈ complexStrip n (stripWidth s₀ / 2) := fun i =>
    (hθ i).trans_le (by have := stripWidth_pos hD.s₀_pos; linarith)
  unfold linMat
  rw [norm_sqMat]
  exact (hM _ (unperturbed_mem_domainD hD hI hθ2)).2.2.1

end Pointwise

/-- Pure matrix algebra for `step:p4:stab-torsion`:
`N'ᵀ Ω X' - Nᵀ Ω X = (N' - N)ᵀ Ω X' + Nᵀ Ω (X' - X)`. -/
theorem norm_torsion_combo_le (N' N X' X : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ) {a b c e : ℝ}
    (hNt : ‖Nᵀ‖ ≤ a) (hX : ‖X' - X‖ ≤ b) (hNN : ‖(N' - N)ᵀ‖ ≤ c) (hX' : ‖X'‖ ≤ e) :
    ‖N'ᵀ * omegaZeroMatrix n * X' - Nᵀ * omegaZeroMatrix n * X‖ ≤ c * e + a * b := by
  have key : N'ᵀ * omegaZeroMatrix n * X' - Nᵀ * omegaZeroMatrix n * X =
      (N' - N)ᵀ * omegaZeroMatrix n * X' + Nᵀ * omegaZeroMatrix n * (X' - X) := by
    simp only [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [key]
  have h1 : ‖(N' - N)ᵀ * omegaZeroMatrix n * X'‖ ≤ c * e := by
    refine (Matrix.linfty_opNorm_mul _ _).trans ?_
    rw [norm_mul_omegaZeroMatrix]
    exact mul_le_mul hNN hX' (norm_nonneg _) ((norm_nonneg _).trans hNN)
  have h2 : ‖Nᵀ * omegaZeroMatrix n * (X' - X)‖ ≤ a * b := by
    refine (Matrix.linfty_opNorm_mul _ _).trans ?_
    rw [norm_mul_omegaZeroMatrix]
    exact mul_le_mul hNt hX (norm_nonneg _) ((norm_nonneg _).trans hNt)
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-! ### The constant inequalities of `step:p4:stab-xn` and `step:p4:stab-torsion` -/

/-- `2 M + 12 n² M + 264 n² W ≤ 304 n³ (M + W + 1)`. -/
theorem xn_const_le (hn : 2 ≤ n) {M W : ℝ} (hM : 0 ≤ M) (hW : 0 ≤ W) :
    2 * M + 12 * (n : ℝ) ^ 2 * M + 264 * (n : ℝ) ^ 2 * W ≤ 304 * (n : ℝ) ^ 3 * (M + W + 1) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have e1 : 2 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by nlinarith [sq_nonneg (n : ℝ)]
  have e2 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_nonneg hM (by nlinarith : (0 : ℝ) ≤ 304 * (n : ℝ) ^ 3 - 12 * (n : ℝ) ^ 2 - 2),
    mul_nonneg hW (by nlinarith : (0 : ℝ) ≤ 304 * (n : ℝ) ^ 3 - 264 * (n : ℝ) ^ 2)]

/-- `2 M + 12 n² M + 264 n² W + 24 n³ (M + 1) ≤ 304 n³ (M + W + 1)`. -/
theorem torsion_const_le (hn : 2 ≤ n) {M W : ℝ} (hM : 0 ≤ M) (hW : 0 ≤ W) :
    2 * M + 12 * (n : ℝ) ^ 2 * M + 264 * (n : ℝ) ^ 2 * W + 24 * (n : ℝ) ^ 3 * (M + 1) ≤
      304 * (n : ℝ) ^ 3 * (M + W + 1) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have e1 : 2 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by nlinarith [sq_nonneg (n : ℝ)]
  have e2 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have e3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  nlinarith [mul_nonneg hM (by nlinarith : (0 : ℝ) ≤ 280 * (n : ℝ) ^ 3 - 12 * (n : ℝ) ^ 2 - 2),
    mul_nonneg hW (by nlinarith : (0 : ℝ) ≤ 304 * (n : ℝ) ^ 3 - 264 * (n : ℝ) ^ 2)]


/-- The real arithmetic of `step:p4:stab-xn`. -/
theorem xn_arith {M W δ η : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hη : 0 ≤ η) :
    M * η * 2 + M * (12 * n * (n * η / δ)) + 66 * n * (4 * n * W * η / δ ^ 2) ≤
      (2 * M + 12 * (n : ℝ) ^ 2 * M + 264 * (n : ℝ) ^ 2 * W) * (η / δ ^ 2) := by
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hη1 : η ≤ η / δ ^ 2 := by
    rw [le_div_iff₀ hδ2]
    exact mul_le_of_le_one_right hη (by nlinarith)
  have hη2 : η / δ ≤ η / δ ^ 2 :=
    div_le_div_of_nonneg_left hη hδ2 (by nlinarith)
  have e1 : M * η * 2 + M * (12 * n * (n * η / δ)) + 66 * n * (4 * n * W * η / δ ^ 2) =
      2 * M * η + 12 * (n : ℝ) ^ 2 * M * (η / δ) + 264 * (n : ℝ) ^ 2 * W * (η / δ ^ 2) := by
    field_simp
    ring
  rw [e1]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left hη1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM),
    mul_le_mul_of_nonneg_left hη2 (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12)
      (sq_nonneg (n : ℝ))) hM)]

/-- The real arithmetic of `step:p4:stab-torsion`. -/
theorem torsion_arith (hn : 2 ≤ n) {M W δ η : ℝ} (hM : 0 ≤ M) (hW : 0 ≤ W) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hη : 0 ≤ η) :
    2 * n * (12 * n * (n * η / δ)) * (M + 1) +
      1 * ((2 * M + 12 * (n : ℝ) ^ 2 * M + 264 * (n : ℝ) ^ 2 * W) * (η / δ ^ 2)) ≤
      304 * (n : ℝ) ^ 3 * (M + W + 1) * η / δ ^ 2 := by
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hη2 : η / δ ≤ η / δ ^ 2 :=
    div_le_div_of_nonneg_left hη hδ2 (by nlinarith)
  have e1 : 2 * n * (12 * n * (n * η / δ)) * (M + 1) = 24 * (n : ℝ) ^ 3 * (M + 1) * (η / δ) := by
    field_simp
    ring
  have e2 : 304 * (n : ℝ) ^ 3 * (M + W + 1) * η / δ ^ 2 =
      304 * (n : ℝ) ^ 3 * (M + W + 1) * (η / δ ^ 2) := by ring
  rw [e1, e2]
  have hc := torsion_const_le hn hM hW
  have he : 0 ≤ η / δ ^ 2 := by positivity
  have h3 : 0 ≤ 24 * (n : ℝ) ^ 3 * (M + 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hη2 h3, mul_le_mul_of_nonneg_right hc he]


/-! ### The strip estimates -/

section Strip

variable {ρ δ η : ℝ} {ω : Fin n → ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
  (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε) (hε : ε ≤ 1) (hI : I ∈ B)

include hD hP hε hI in
/-- Step `step:p4:stab-xn`: `|X_N - X_N⁰| ≤ (2M + 12 n² M + 264 n² W_∞) η δ⁻²` on `T_{ρ-δ}`. -/
theorem normalField_close (hω : ‖ω‖ ≤ Winf s₀ r₀ B h) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hρ : ρ ≤ stripWidth s₀ / 4) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hclose : ∀ θ ∈ complexStrip n ρ, ‖K θ - unperturbedTorus I θ‖ ≤ η)
    (hημ : η ≤ muParam s₀ r₀) (h12 : 12 * n * (n * η / δ) ≤ 1) :
    ∀ θ ∈ complexStrip n (ρ - δ),
      ‖normalFieldMat (hbold h f) K ω θ - normalFieldMat (hbold h f) (unperturbedTorus I) ω θ‖ ≤
        (2 * Mconst s₀ r₀ B h + 12 * (n : ℝ) ^ 2 * Mconst s₀ r₀ B h +
          264 * (n : ℝ) ^ 2 * Winf s₀ r₀ B h) * (η / δ ^ 2) := by
  intro θ hθ
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hD.two_le
  have hθρ : θ ∈ complexStrip n ρ := fun i => (hθ i).trans_le (by linarith)
  have hθ4 : θ ∈ complexStrip n (stripWidth s₀ / 4) := fun i => (hθρ i).trans_le hρ
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hclose θ hθρ)
  have hM := (Parameters.Mconst_pos (B := B) (h := h) hD.s₀_pos hD.r₀_pos).le
  have hb := frame_basic hn0 hK hclose hδ h12 θ hθ
  have hd := frame_deriv hn0 hK hclose hδ h12 hω θ hθ
  have hA := norm_linMat_sub_le hD hP hε hI hθ4 hημ (hclose θ hθρ)
  have hA0 := norm_linMat_unperturbed_le hD hP hε hI hθ4
  have key : normalFieldMat (hbold h f) K ω θ -
      normalFieldMat (hbold h f) (unperturbedTorus I) ω θ =
      (linMat (hbold h f) K θ - linMat (hbold h f) (unperturbedTorus I) θ) * normalMat K θ +
        linMat (hbold h f) (unperturbedTorus I) θ * (normalMat K θ - frameN0 n) -
          fderiv ℂ (normalMat K) θ (fun l => (ω l : ℂ)) := by
    rw [normalFieldMat_unperturbed, normalFieldMat]
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [key]
  refine (KAM.Apost.PerturbationAux.norm_normalField_combo_le _ _ _ _ _ hA hA0 hb.2.2.2 hb.2.2.1
    hd).trans ?_
  exact xn_arith hM hδ hδ1 hη0


include hD hP hε hI in
/-- Step `step:p4:stab-torsion`: `|T - T⁰| ≤ c_T η δ⁻²` on `T_{ρ-δ}`, where `c_T η δ⁻² ≤ 1`. -/
theorem torsion_close (hω : ‖ω‖ ≤ Winf s₀ r₀ B h) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hρ : ρ ≤ stripWidth s₀ / 4) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hclose : ∀ θ ∈ complexStrip n ρ, ‖K θ - unperturbedTorus I θ‖ ≤ η)
    (hημ : η ≤ muParam s₀ r₀) (h12 : 12 * n * (n * η / δ) ≤ 1)
    (hcT : cT s₀ r₀ B h * η / δ ^ 2 ≤ 1) :
    ∀ θ ∈ complexStrip n (ρ - δ),
      ‖torsion (hbold h f) K ω θ - torsion (hbold h f) (unperturbedTorus I) ω θ‖ ≤
        cT s₀ r₀ B h * η / δ ^ 2 := by
  intro θ hθ
  have hn := hD.two_le
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hθρ : θ ∈ complexStrip n ρ := fun i => (hθ i).trans_le (by linarith)
  have hθ4 : θ ∈ complexStrip n (stripWidth s₀ / 4) := fun i => (hθρ i).trans_le hρ
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hclose θ hθρ)
  have hM := (Parameters.Mconst_pos (B := B) (h := h) hD.s₀_pos hD.r₀_pos).le
  have hW := Parameters.Winf_nonneg (B := B) (h := h) hD.s₀_pos hD.r₀_pos
  have hbasic := frame_basic hn0 hK hclose hδ h12
  have hKs : DifferentiableOn ℂ K (complexStrip n (ρ - δ)) :=
    hK.mono fun θ hθ i => (hθ i).trans_le (by linarith)
  have hNdiff : DifferentiableOn ℂ (normalMat K) (complexStrip n (ρ - δ)) :=
    differentiableOn_normalMat hKs fun θ hθ => (hbasic θ hθ).2.1.1
  have hNd : DifferentiableAt ℂ (normalMat K) θ :=
    hNdiff.differentiableAt ((isOpen_complexStrip n (ρ - δ)).mem_nhds hθ)
  have hN0d : DifferentiableAt ℂ (normalMat (unperturbedTorus I)) θ := by
    have : normalMat (unperturbedTorus I) = fun _ => frameN0 n :=
      funext (normalMat_unperturbedTorus I)
    rw [this]; exact differentiableAt_const _
  have hb := hbasic θ hθ
  have hXd := normalField_close hD hP hε hI hω hδ hδ1 hρ hK hclose hημ h12 θ hθ
  have hE : 2 * Mconst s₀ r₀ B h + 12 * (n : ℝ) ^ 2 * Mconst s₀ r₀ B h +
      264 * (n : ℝ) ^ 2 * Winf s₀ r₀ B h ≤ cT s₀ r₀ B h := xn_const_le hn hM hW
  have he0 : 0 ≤ η / δ ^ 2 := by positivity
  have hXb : ‖normalFieldMat (hbold h f) K ω θ‖ ≤ Mconst s₀ r₀ B h + 1 := by
    have h0 : ‖normalFieldMat (hbold h f) (unperturbedTorus I) ω θ‖ ≤ Mconst s₀ r₀ B h := by
      rw [normalFieldMat_unperturbed]
      calc _ ≤ ‖linMat (hbold h f) (unperturbedTorus I) θ‖ * ‖frameN0 n‖ :=
            Matrix.linfty_opNorm_mul _ _
        _ ≤ Mconst s₀ r₀ B h * 1 := by
            rw [norm_frameN0 hn0]
            exact mul_le_mul_of_nonneg_right (norm_linMat_unperturbed_le hD hP hε hI hθ4)
              zero_le_one
        _ = Mconst s₀ r₀ B h := mul_one _
    have h1 : ((2 * Mconst s₀ r₀ B h + 12 * (n : ℝ) ^ 2 * Mconst s₀ r₀ B h +
        264 * (n : ℝ) ^ 2 * Winf s₀ r₀ B h) * (η / δ ^ 2)) ≤ 1 := by
      calc _ ≤ cT s₀ r₀ B h * (η / δ ^ 2) := mul_le_mul_of_nonneg_right hE he0
        _ = cT s₀ r₀ B h * η / δ ^ 2 := by ring
        _ ≤ 1 := hcT
    calc ‖normalFieldMat (hbold h f) K ω θ‖
        = ‖normalFieldMat (hbold h f) (unperturbedTorus I) ω θ +
            (normalFieldMat (hbold h f) K ω θ -
              normalFieldMat (hbold h f) (unperturbedTorus I) ω θ)‖ := by rw [add_sub_cancel]
      _ ≤ _ + _ := norm_add_le _ _
      _ ≤ Mconst s₀ r₀ B h + 1 := add_le_add h0 (hXd.trans h1)
  have hNt : ‖(normalMat (unperturbedTorus I) θ)ᵀ‖ ≤ 1 := by
    rw [normalMat_unperturbedTorus, norm_frameN0_transpose hn0]
  have hNN : ‖(normalMat K θ - normalMat (unperturbedTorus I) θ)ᵀ‖ ≤
      2 * n * (12 * n * (n * η / δ)) := by
    rw [normalMat_unperturbedTorus]
    exact (KAM.Apost.FrameAux.norm_transpose_le_two_mul _).trans
      (mul_le_mul_of_nonneg_left hb.2.2.1 (by positivity))
  rw [torsion_eq_mat _ _ _ hNd, torsion_eq_mat _ _ _ hN0d]
  refine (norm_torsion_combo_le _ _ _ _ hNt hXd hNN hXb).trans ?_
  exact torsion_arith hn hM hW hδ hδ1 hη0


include hD hP hε hI in
/-- Step `step:p4:stab-twist`: `⟨T⟩` is invertible with `|⟨T⟩⁻¹| ≤ 4 L₊`. -/
theorem twist_close (hεF : Lplus Lh * Fconst n s₀ r₀ 2 * ε ≤ 1 / 2)
    (hω : ‖ω‖ ≤ Winf s₀ r₀ B h) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδρ : δ < ρ)
    (hρ : ρ ≤ stripWidth s₀ / 4) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hclose : ∀ θ ∈ complexStrip n ρ, ‖K θ - unperturbedTorus I θ‖ ≤ η)
    (hημ : η ≤ muParam s₀ r₀) (h12 : 12 * n * (n * η / δ) ≤ 1)
    (hcT : cT s₀ r₀ B h * η / δ ^ 2 ≤ 1 / (16 * Lplus Lh)) :
    IsUnit (torsionAverage (hbold h f) K ω).det ∧
      ‖(torsionAverage (hbold h f) K ω)⁻¹‖ ≤ 4 * Lplus Lh := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hD.two_le
  have hL := Parameters.Lplus_pos Lh
  have hL1 := one_le_Lplus Lh
  have hρδ : 0 < ρ - δ := by linarith
  have hsub : complexStrip n (ρ - δ) ⊆ complexStrip n ρ := fun θ hθ i =>
    (hθ i).trans_le (by linarith)
  have hbasic := frame_basic hn0 hK hclose hδ h12
  have hKs : DifferentiableOn ℂ K (complexStrip n (ρ - δ)) := hK.mono hsub
  have hK𝔇 : ∀ θ ∈ complexStrip n (ρ - δ), K θ ∈ domainD n s₀ r₀ B := fun θ hθ =>
    ball_subset_domainD hD.r₀_pos hI (fun i => (hsub hθ i).trans_le hρ)
      ((hclose θ (hsub hθ)).trans hημ) (Metric.mem_ball_self (muParam_pos hD.s₀_pos hD.r₀_pos))
  have hTc := (torsion_regular_design hD.s₀_pos hD.r₀_pos hD.holo hP.holo hP.periodic hρδ hKs
    hK𝔇 (fun θ hθ => (hbasic θ hθ).2.1.1) ω).2.2.1.2.2
  have hT0c := unperturbed_continuous_torsion hD hP hI ω
  have hTcl := torsion_close hD hP hε hI hω hδ hδ1 hρ hK hclose hημ h12
    (hcT.trans (by rw [div_le_one (by positivity)]; nlinarith))
  have hΔ : ‖torsionAverage (hbold h f) K ω - torsionAverage (hbold h f) (unperturbedTorus I) ω‖ ≤
      cT s₀ r₀ B h * η / δ ^ 2 :=
    KAM.Apost.PerturbationAux.norm_torsionAverage_sub_le hT0c hTc
      fun x => hTcl _ (KAM.ofReal_mem_complexStrip hρδ x)
  obtain ⟨hA0u, hA0i⟩ := unperturbed_twist hD hP hI ω hεF
  have hA0u' : IsUnit (torsionAverage (hbold h f) (unperturbedTorus I) ω) :=
    (Matrix.isUnit_iff_isUnit_det _).2 hA0u
  have hsm : ‖(torsionAverage (hbold h f) (unperturbedTorus I) ω)⁻¹‖ *
      ‖torsionAverage (hbold h f) K ω - torsionAverage (hbold h f) (unperturbedTorus I) ω‖ ≤
        1 / 2 := by
    calc _ ≤ (2 * Lplus Lh) * (1 / (16 * Lplus Lh)) :=
          mul_le_mul hA0i (hΔ.trans hcT) (norm_nonneg _) (by positivity)
      _ = 1 / 8 := by field_simp; ring
      _ ≤ 1 / 2 := by norm_num
  have e1 := KAM.matrix_isUnit_add_of_inv_norm_mul_le_half hA0u' hsm
  have e2 := KAM.matrix_norm_inv_add_le hA0u' hsm
  rw [add_sub_cancel] at e1 e2
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).1 e1, e2.trans (by linarith)⟩

end Strip

end Stab

/-! ### The node -/

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
  {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}

/-- Blueprint `bp:p4:stab` (STAB), items (a)–(d) and the hypotheses H2–H4 of G1 in the frozen
row-sum form. -/
theorem stab (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε) (hε : ε ≤ 1)
    (hεF : Lplus Lh * Fconst n s₀ r₀ 2 * ε ≤ 1 / 2) {I : Fin n → ℝ} (hI : I ∈ B)
    {ω : Fin n → ℝ} (hω : ‖ω‖ ≤ Winf s₀ r₀ B h) {δ ρ η : ℝ} (hδ : 0 < δ) (hδρ : δ < ρ)
    (hρ : ρ ≤ stripWidth s₀ / 4) {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hclose : ∀ θ ∈ complexStrip n ρ, ‖K θ - unperturbedTorus I θ‖ ≤ η)
    (hη : η ≤ etaStar s₀ r₀ B h Lh δ) :
    (∀ θ ∈ complexStrip n (ρ - δ),
      -- (a)
      (‖tangentMat K θ - frameL0 n‖ ≤ n * η / δ ∧ ‖fderiv ℂ K θ‖ ≤ 2) ∧
      -- (b)
      Metric.ball (K θ) (muParam s₀ r₀) ⊆ domainD n s₀ r₀ B ∧
      -- (c)
      (IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ 2) ∧
      -- (d), pointwise
      ‖torsion (hbold h f) K ω θ - torsion (hbold h f) (unperturbedTorus I) ω θ‖ ≤
        cT s₀ r₀ B h * η / δ ^ 2) ∧
    -- (d), the twist
    (IsUnit (torsionAverage (hbold h f) K ω).det ∧
      ‖(torsionAverage (hbold h f) K ω)⁻¹‖ ≤ 4 * Lplus Lh) ∧
    -- H2–H4 of G1 on `T_{ρ-δ}`
    (IsPrimaryOnStrip K ρ → IsRealOnReals K →
      DifferentiableOn ℂ K (complexStrip n (ρ - δ)) ∧ IsPrimaryOnStrip K (ρ - δ) ∧
      IsRealOnReals K ∧
      (∀ θ ∈ complexStrip n (ρ - δ), Metric.ball (K θ) (muParam s₀ r₀) ⊆ domainD n s₀ r₀ B) ∧
      (∀ θ ∈ complexStrip n (ρ - δ), ‖fderiv ℂ K θ‖ ≤ sigmaK s₀ r₀ - muParam s₀ r₀) ∧
      (∀ θ ∈ complexStrip n (ρ - δ), IsUnit (gramMatrix K θ).det ∧
        ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ sigmaB s₀ r₀ - muParam s₀ r₀) ∧
      IsUnit (torsionAverage (hbold h f) K ω).det ∧
      ∀ i, ∑ j, ‖(torsionAverage (hbold h f) K ω)⁻¹ i j‖ ≤
        sigmaT Lh s₀ r₀ - muParam s₀ r₀) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hD.two_le
  have hρ0 : 0 < ρ := hδ.trans hδρ
  have hδ1 : δ ≤ 1 := by
    have := stripWidth_le_one s₀
    linarith
  have hη0 : 0 ≤ η := (norm_nonneg _).trans
    (hclose _ (KAM.ofReal_mem_complexStrip hρ0 0))
  obtain ⟨hcT, h12⟩ := Stab.eta_small hD.two_le hD.s₀_pos hD.r₀_pos hδ hδ1 hη0 hη
  have hημ : η ≤ muParam s₀ r₀ := hη.trans (Parameters.etaStar_le_muParam s₀ r₀ B h Lh δ)
  have hsub : complexStrip n (ρ - δ) ⊆ complexStrip n ρ := fun θ hθ i =>
    (hθ i).trans_le (by linarith)
  have hbasic := Stab.frame_basic hn0 hK hclose hδ h12
  have hball : ∀ θ ∈ complexStrip n (ρ - δ),
      Metric.ball (K θ) (muParam s₀ r₀) ⊆ domainD n s₀ r₀ B := fun θ hθ =>
    Stab.ball_subset_domainD hD.r₀_pos hI (fun i => (hsub hθ i).trans_le hρ)
      ((hclose θ (hsub hθ)).trans hημ)
  have hL1 := one_le_Lplus Lh
  have hcT1 : cT s₀ r₀ B h * η / δ ^ 2 ≤ 1 :=
    hcT.trans (by rw [div_le_one (by positivity)]; nlinarith)
  have htors := Stab.torsion_close hD hP hε hI hω hδ hδ1 hρ hK hclose hημ h12 hcT1
  have htw := Stab.twist_close hD hP hε hI hεF hω hδ hδ1 hδρ hρ hK hclose hημ h12 hcT
  have hfd : ∀ θ ∈ complexStrip n (ρ - δ), ‖fderiv ℂ K θ‖ ≤ 2 := fun θ hθ => by
    have := (hbasic θ hθ).1.2
    rwa [tangentMat, norm_colMat] at this
  refine ⟨fun θ hθ => ⟨⟨(hbasic θ hθ).1.1, hfd θ hθ⟩, hball θ hθ, (hbasic θ hθ).2.1,
    htors θ hθ⟩, htw, fun hprim hreal => ?_⟩
  refine ⟨hK.mono hsub, fun θ hθ k => hprim θ (hsub hθ) k, hreal, hball, ?_, ?_, htw.1, ?_⟩
  · intro θ hθ
    have : sigmaK s₀ r₀ - muParam s₀ r₀ = 2 := by unfold sigmaK; ring
    rw [this]
    exact hfd θ hθ
  · intro θ hθ
    have : sigmaB s₀ r₀ - muParam s₀ r₀ = 2 := by unfold sigmaB; ring
    rw [this]
    exact ⟨(hbasic θ hθ).2.1.1, fun i => (rowSum_le_norm _ i).trans (hbasic θ hθ).2.1.2⟩
  · intro i
    have : sigmaT Lh s₀ r₀ - muParam s₀ r₀ = 4 * Lplus Lh := by unfold sigmaT; ring
    rw [this]
    exact (KAM.rowSum_le_norm _ i).trans htw.2

end KAM.Head

end
