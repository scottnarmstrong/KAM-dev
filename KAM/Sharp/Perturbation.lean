/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.PerturbationParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Perturbation through the torsion polynomial

Blueprint `bp:p2s:perturbation` (`KAM.Sharp.perturbation_poly`): a torus `K̃` holomorphic on
`T_{r-2δ}`, `d`-close to `K`, with invariance error `≤ ε̃ ≤ ε` at any frequency `ω̃`, has
(a) the ball margin `β - d`; (b), (c) the frame bounds on `T_{r-3δ}`; (d) a torsion `T̃_{ω̃}` within
`twistD` of `T_ω` at every real point; (e) an invertible averaged torsion close to `⟨T_ω⟩`.

The proof follows the blueprint:

* `step:p2s:pt-domain`, `pt-l`, `pt-b`: `KAM.Sharp.frame_items_sharp` (Cauchy estimates for `K̃ - K`,
  `G̃ - G = L̃ᵀ (L̃ - L) + (L̃ - L)ᵀ L`, Neumann with ratio `ϑ`);
* `step:p2s:pt-tt`, `pt-ab`, `pt-f`, `pt-c`: `KAM.Sharp.torsion_diff_real` (both torsions through
  `KAM.Sharp.torsion_identity`; `𝒯_ab` by `prod5_sub_le`, `𝒯_F` and `𝒯_c` by their sizes, the
  Lagrangian defect of `K` from `KAM.Sharp.geometry_sep`);
* `step:p2s:pt-avg`: `norm_torsionAverage_sub_le_any` and `neumann_ratio`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology

namespace KAM.Sharp

open KAM KAM.Torus KAM.Apost

variable {n : ℕ} {κ cR M σK σB σT : ℝ}
variable {τ : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {ω : Fin n → ℝ} {γ : ℝ}

theorem vth_eq : vth = 1 / 8 := rfl
theorem vthh_eq : vthh = 8 / 7 := rfl
theorem one_add_vth_le_vthh : 1 + vth ≤ vthh := by rw [vth_eq, vthh_eq]; norm_num
theorem one_le_vthh : 1 ≤ vthh := by rw [vthh_eq]; norm_num

/-- Steps `step:p2s:pt-l`, `pt-b`: the frame of `K̃` on `T_{r-3δ}`. -/
theorem frame_items_sharp (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {r β ε δ : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : KAM.Iso.Linear.AdmissibleNoTwist σK σB 𝔅 h ω r β ε K) (hδ : 0 < δ)
    {K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {d : ℝ}
    (hK' : DifferentiableOn ℂ K' (complexStrip n (r - 2 * δ)))
    (hd : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖K' θ - K θ‖ ≤ d)
    (hs1 : n * d / δ ≤ vth * σK) (hs2 : σB * cGram n σK * d / δ ≤ vth) :
    ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖fderiv ℂ K' θ - fderiv ℂ K θ‖ ≤ n * d / δ ∧
      ‖(tangentMat K' θ - tangentMat K θ)ᵀ‖ ≤ 2 * n * d / δ ∧
      ‖fderiv ℂ K' θ‖ ≤ vthh * σK ∧
      ‖(tangentMat K' θ)ᵀ‖ ≤ 2 * n * ((1 + vth) * σK) ∧
      IsUnit (gramMatrix K' θ).det ∧ ‖(gramMatrix K' θ)⁻¹‖ ≤ vthh * σB ∧
      ‖(gramMatrix K' θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤ cB n σK σB * d / δ := by
  intro θ hθ
  have hr := hK.r_pos
  have hσK := hS.σK_pos
  have hσB := hS.σB_pos
  have hn1 : (1 : ℝ) ≤ n := by have := hS.two_le; exact_mod_cast (by omega : 1 ≤ n)
  have hsub2r : complexStrip n (r - 2 * δ) ⊆ complexStrip n r :=
    PerturbationAux.complexStrip_mono (by linarith)
  have hθr : θ ∈ complexStrip n r := PerturbationAux.complexStrip_mono (by linarith) hθ
  have hθ' : θ ∈ complexStrip n (r - 2 * δ - δ) := by
    rw [show r - 2 * δ - δ = r - 3 * δ by ring]; exact hθ
  have hKd := hK.holo.mono hsub2r
  -- step `pt-l`
  have hdL := PerturbationAux.norm_fderiv_sub_le hKd hK' hd hδ θ hθ'
  have hdLt := PerturbationAux.norm_transpose_tangentMat_sub_le hKd hK' hd hδ θ hθ'
  have hLθ : ‖fderiv ℂ K θ‖ ≤ σK := hK.deriv_le θ hθr
  have hL : ‖tangentMat K θ‖ ≤ σK := (FrameAux.norm_tangentMat K θ).le.trans hLθ
  have hLt : ‖(tangentMat K θ)ᵀ‖ ≤ 2 * n * σK :=
    (FrameAux.norm_transpose_le_two_mul _).trans (mul_le_mul_of_nonneg_left hL (by positivity))
  have hdL' : ‖tangentMat K' θ - tangentMat K θ‖ ≤ n * d / δ := by
    rw [PerturbationAux.norm_tangentMat_sub]; exact hdL
  have hv0 : 0 ≤ vth := by rw [vth_eq]; norm_num
  have h1 : ‖fderiv ℂ K' θ‖ ≤ vthh * σK := by
    calc ‖fderiv ℂ K' θ‖ = ‖fderiv ℂ K θ + (fderiv ℂ K' θ - fderiv ℂ K θ)‖ := by
          rw [add_sub_cancel]
      _ ≤ σK + vth * σK := (norm_add_le _ _).trans (add_le_add hLθ (hdL.trans hs1))
      _ = (1 + vth) * σK := by ring
      _ ≤ vthh * σK := mul_le_mul_of_nonneg_right one_add_vth_le_vthh hσK.le
  have hLt' : ‖(tangentMat K' θ)ᵀ‖ ≤ 2 * n * ((1 + vth) * σK) := by
    have e : (tangentMat K' θ)ᵀ = (tangentMat K θ)ᵀ + (tangentMat K' θ - tangentMat K θ)ᵀ := by
      rw [Matrix.transpose_sub]; abel
    have h2 : 2 * (n : ℝ) * d / δ ≤ 2 * n * (vth * σK) := by
      calc 2 * (n : ℝ) * d / δ = 2 * (n * d / δ) := by ring
        _ ≤ 2 * (vth * σK) := by linarith
        _ ≤ 2 * n * (vth * σK) :=
            mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hv0 hσK.le)
    rw [e]
    calc _ ≤ 2 * n * σK + 2 * n * (vth * σK) :=
          (norm_add_le _ _).trans (add_le_add hLt (hdLt.trans h2))
      _ = 2 * n * ((1 + vth) * σK) := by ring
  -- step `pt-b`: Gram matrix and its inverse
  have hGd : ‖gramMatrix K' θ - gramMatrix K θ‖ ≤ cGram n σK * d / δ := by
    rw [PerturbationAux.gramMatrix_sub]
    calc _ ≤ ‖(tangentMat K' θ)ᵀ‖ * ‖tangentMat K' θ - tangentMat K θ‖ +
          ‖(tangentMat K' θ - tangentMat K θ)ᵀ‖ * ‖tangentMat K θ‖ :=
          (norm_add_le _ _).trans (add_le_add (Matrix.linfty_opNorm_mul _ _)
            (Matrix.linfty_opNorm_mul _ _))
      _ ≤ 2 * n * ((1 + vth) * σK) * (n * d / δ) + 2 * n * d / δ * σK :=
          add_le_add (mul_le_mul hLt' hdL' (norm_nonneg _) (by positivity))
            (mul_le_mul hdLt hL (norm_nonneg _) ((norm_nonneg _).trans hdLt))
      _ = cGram n σK * d / δ := by unfold cGram; ring
  obtain ⟨hGu, hBθ⟩ := hK.gram θ hθr
  have hA : IsUnit (gramMatrix K θ) := (Matrix.isUnit_iff_isUnit_det _).2 hGu
  have hsmall : ‖(gramMatrix K θ)⁻¹‖ * ‖gramMatrix K' θ - gramMatrix K θ‖ ≤ vth :=
    calc _ ≤ σB * (cGram n σK * d / δ) :=
          mul_le_mul hBθ hGd (norm_nonneg _) hσB.le
      _ = σB * cGram n σK * d / δ := by ring
      _ ≤ vth := hs2
  obtain ⟨hU, hBn, hBdiff⟩ := neumann_ratio hA (q := vth) (by rw [vth_eq]; norm_num) hsmall
  rw [add_sub_cancel] at hU hBn hBdiff
  have h17 : (1 : ℝ) - vth = 7 / 8 := by rw [vth_eq]; norm_num
  refine ⟨hdL, hdLt, h1, hLt', (Matrix.isUnit_iff_isUnit_det _).1 hU, ?_, ?_⟩
  · calc _ ≤ ‖(gramMatrix K θ)⁻¹‖ / (1 - vth) := hBn
      _ ≤ σB / (1 - vth) := div_le_div_of_nonneg_right hBθ (by rw [h17]; norm_num)
      _ = vthh * σB := by rw [h17, vthh_eq]; ring
  · have hBB : ‖(gramMatrix K θ)⁻¹‖ ^ 2 ≤ σB ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hBθ 2
    calc _ ≤ ‖(gramMatrix K θ)⁻¹‖ ^ 2 * ‖gramMatrix K' θ - gramMatrix K θ‖ / (1 - vth) := hBdiff
      _ ≤ σB ^ 2 * (cGram n σK * d / δ) / (1 - vth) :=
          div_le_div_of_nonneg_right (mul_le_mul hBB hGd (norm_nonneg _) (by positivity))
            (by rw [h17]; norm_num)
      _ = cB n σK σB * d / δ := by unfold cB; rw [h17, vthh_eq]; ring

/-- Step `step:p2s:pt-ab`, constants: twice `ϑ̂⁴ ∑_i Δ_i ∏_{j≠i} x_j`, with
`x = (σ_B, 2nσ_K, M, σ_K, σ_B)` and `Δ = (C_B D, 2n D, M d, n D, C_B D)`, `d ≤ D = d/δ`, is at most
`C_Δab D`. -/
theorem arith_ab {d D : ℝ} (hσK : 0 < σK) (hσB : 0 < σB) (hM : 0 ≤ M) (hdD : d ≤ D) :
    vthh ^ 4 * (cB n σK σB * D * (2 * n * σK) * M * σK * σB +
        σB * (2 * n * D) * M * σK * σB + σB * (2 * n * σK) * (M * d) * σK * σB +
        σB * (2 * n * σK) * M * (n * D) * σB + σB * (2 * n * σK) * M * σK * (cB n σK σB * D)) +
      vthh ^ 4 * (cB n σK σB * D * (2 * n * σK) * M * σK * σB +
        σB * (2 * n * D) * M * σK * σB + σB * (2 * n * σK) * (M * d) * σK * σB +
        σB * (2 * n * σK) * M * (n * D) * σB + σB * (2 * n * σK) * M * σK * (cB n σK σB * D)) ≤
      cDab n M σK σB * D := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h3 : σB * (2 * n * σK) * (M * d) * σK * σB ≤ σB * (2 * n * σK) * (M * D) * σK * σB := by
    gcongr
  have hv4 : 0 ≤ vthh ^ 4 := by rw [vthh_eq]; positivity
  have hS : cB n σK σB * D * (2 * n * σK) * M * σK * σB +
        σB * (2 * n * D) * M * σK * σB + σB * (2 * n * σK) * (M * d) * σK * σB +
        σB * (2 * n * σK) * M * (n * D) * σB + σB * (2 * n * σK) * M * σK * (cB n σK σB * D) ≤
      cB n σK σB * D * (2 * n * σK) * M * σK * σB +
        σB * (2 * n * D) * M * σK * σB + σB * (2 * n * σK) * (M * D) * σK * σB +
        σB * (2 * n * σK) * M * (n * D) * σB + σB * (2 * n * σK) * M * σK * (cB n σK σB * D) := by
    linarith
  have key : vthh ^ 4 * (cB n σK σB * D * (2 * n * σK) * M * σK * σB +
        σB * (2 * n * D) * M * σK * σB + σB * (2 * n * σK) * (M * D) * σK * σB +
        σB * (2 * n * σK) * M * (n * D) * σB + σB * (2 * n * σK) * M * σK * (cB n σK σB * D)) * 2 =
      cDab n M σK σB * D := by
    unfold cDab
    field_simp
    ring
  have := mul_le_mul_of_nonneg_left hS hv4
  linarith

/-- Steps `step:p2s:pt-tt`–`pt-c`: at every real point, `|T̃_{ω̃} - T_ω| ≤ twistD`. -/
theorem torsion_diff_real (hC : CohData n τ κ cR) (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    {r β ε δ : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : KAM.Iso.Linear.AdmissibleNoTwist σK σB 𝔅 h ω r β ε K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h3δ : 3 * δ < r) (hεδ : ε ≤ δ) {K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ω' : Fin n → ℝ} {d ε' : ℝ} (hK' : DifferentiableOn ℂ K' (complexStrip n (r - 2 * δ)))
    (hd : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖K' θ - K θ‖ ≤ d) (hdβ : d < β)
    (hE' : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖invarianceError h K' ω' θ‖ ≤ ε') (hε' : ε' ≤ ε)
    (hs1 : n * d / δ ≤ vth * σK) (hs2 : σB * cGram n σK * d / δ ≤ vth) (x : Fin n → ℝ) :
    ‖torsion h K' ω' (fun i => (x i : ℂ)) - torsion h K ω (fun i => (x i : ℂ))‖ ≤
      twistD n κ cR M σK σB γ ε δ d := by
  have hr := hK.r_pos
  have hγ := hS.gamma_pos
  have hσK := hS.σK_pos
  have hσB := hS.σB_pos
  have hM := hS.M_pos
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : 1 ≤ n := by have := hS.two_le; omega
  have hr2 : 0 < r - 2 * δ := by linarith
  have hr3 : 0 < r - 3 * δ := by linarith
  have hsub2r : complexStrip n (r - 2 * δ) ⊆ complexStrip n r :=
    PerturbationAux.complexStrip_mono (by linarith)
  have hsub32 : complexStrip n (r - 3 * δ) ⊆ complexStrip n (r - 2 * δ) :=
    PerturbationAux.complexStrip_mono (by linarith)
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅 := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  have hθ := ofReal_mem_complexStrip hr3 x
  set θ : Fin n → ℂ := fun i => (x i : ℂ) with hθdef
  have hθ2 := hsub32 hθ
  have hθr := hsub2r hθ2
  have hθ1 : θ ∈ complexStrip n (r - δ) := PerturbationAux.complexStrip_mono (by linarith) hθ
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd θ hθ2)
  have hε0 := hK.ε_nonneg
  have hε'0 : 0 ≤ ε' := (norm_nonneg _).trans (hE' θ hθ2)
  have hdβ' : 0 < β - d := by linarith
  have hK'𝔅 : ∀ θ ∈ complexStrip n (r - 2 * δ), K' θ ∈ 𝔅 := fun θ hθ =>
    PerturbationAux.ball_subset_of_close (hK.ball_sub θ (hsub2r hθ)) (hd θ hθ)
      (Metric.mem_ball_self hdβ')
  -- the frames at `θ`
  have hfi := frame_items_sharp hS hK hδ hK' hd hs1 hs2
  obtain ⟨hdL, hdLt, hL'θ, hLt', hG'θ, hB'θ, hdB⟩ := hfi θ hθ
  have hG'3 : ∀ θ ∈ complexStrip n (r - 3 * δ), IsUnit (gramMatrix K' θ).det := fun θ hθ =>
    (hfi θ hθ).2.2.2.2.1
  obtain ⟨hL, hLt, -, -, -, hΩ0, -, hA, -, hAt, -, -⟩ :=
    frame_bounds hS (hK𝔅 θ hθr) (hK.deriv_le θ hθr) (hGu θ hθr) (hK.gram θ hθr).2 ω
  obtain ⟨hL', -, -, -, -, -, -, hA', -, hA't, -, -⟩ :=
    frame_bounds hS (hK'𝔅 θ hθ2) hL'θ hG'θ hB'θ ω'
  have hB := (hK.gram θ hθr).2
  -- the derivatives of the errors
  obtain ⟨hF, hFt⟩ := Geometry.geo_de hS hK.holo hK𝔅 hK.error_le hδ θ hθ1
  have hθ2' : θ ∈ complexStrip n (r - 2 * δ - δ) := by
    rw [show r - 2 * δ - δ = r - 3 * δ by ring]; exact hθ
  obtain ⟨hF', hF't⟩ := geo_de_any hS hK' hK'𝔅 hE' hδ θ hθ2'
  -- the Lagrangian defect of `K`
  have hΩ := ((geometry_sep hC hS hK hδ hδ1 (by linarith)).2 θ hθ2).1
  -- both torsions as torsion polynomials
  rw [(torsion_identity hS hr3 (hK'.mono hsub32) (fun θ hθ => hK'𝔅 θ (hsub32 hθ)) hG'3 ω' θ
      hθ).2.2, (torsion_identity hS hr hK.holo hK𝔅 hGu ω θ hθr).2.2, torsionPoly_split,
    torsionPoly_split]
  set A := linMat h K θ
  set A' := linMat h K' θ
  set L := tangentMat K θ
  set L' := tangentMat K' θ
  set F := errDerivMat h K ω θ
  set F' := errDerivMat h K' ω' θ
  set B := (gramMatrix K θ)⁻¹
  set B' := (gramMatrix K' θ)⁻¹
  set D := d / δ with hD
  have hD0 : 0 ≤ D := div_nonneg hd0 hδ.le
  have hdD : d ≤ D := by rw [hD]; exact (le_div_iff₀ hδ).2 (mul_le_of_le_one_right hd0 hδ1)
  have hvv := one_le_vthh
  have hvv0 : 0 ≤ vthh := zero_le_one.trans hvv
  -- the part `𝒯_ab` (step `pt-ab`)
  have hdA : ‖A' - A‖ ≤ M * d :=
    norm_linMat_sub_le_M hS (hK.ball_sub θ hθr) (hd θ hθ2) hdβ
  have hX3 : ‖A * omegaZeroMatrix n‖ ≤ M := by rw [norm_mul_omegaZeroMatrix]; exact hA
  have hX3' : ‖A' * omegaZeroMatrix n‖ ≤ vthh * M := by
    rw [norm_mul_omegaZeroMatrix]; exact hA'.trans (le_mul_of_one_le_left hM.le hvv)
  have hdX3 : ‖A' * omegaZeroMatrix n - A * omegaZeroMatrix n‖ ≤ M * d := by
    rw [← Matrix.sub_mul, norm_mul_omegaZeroMatrix]; exact hdA
  have hY3 : ‖omegaZeroMatrix n * A‖ ≤ M := by rw [norm_omegaZeroMatrix_mul]; exact hA
  have hY3' : ‖omegaZeroMatrix n * A'‖ ≤ vthh * M := by
    rw [norm_omegaZeroMatrix_mul]; exact hA'.trans (le_mul_of_one_le_left hM.le hvv)
  have hdY3 : ‖omegaZeroMatrix n * A' - omegaZeroMatrix n * A‖ ≤ M * d := by
    rw [← Matrix.mul_sub, norm_omegaZeroMatrix_mul]; exact hdA
  have hB' : ‖B'‖ ≤ vthh * σB := hB'θ
  have hdB' : ‖B' - B‖ ≤ cB n σK σB * D := by rw [hD, ← mul_div_assoc]; exact hdB
  have hLtv : ‖L'ᵀ‖ ≤ vthh * (2 * n * σK) := by
    refine hLt'.trans ?_
    calc 2 * (n : ℝ) * ((1 + vth) * σK) ≤ 2 * n * (vthh * σK) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right one_add_vth_le_vthh hσK.le)
            (by positivity)
      _ = vthh * (2 * n * σK) := by ring
  have hdLt' : ‖L'ᵀ - Lᵀ‖ ≤ 2 * n * D := by
    rw [← Matrix.transpose_sub, hD, ← mul_div_assoc]; exact hdLt
  have hdL'' : ‖L' - L‖ ≤ n * D := by
    rw [PerturbationAux.norm_tangentMat_sub, hD, ← mul_div_assoc]; exact hdL
  have hLv : ‖L'‖ ≤ vthh * σK := hL'
  have t1 := prod5_sub_le hvv hB hB' hdB' hLt hLtv hdLt' hX3 hX3' hdX3 hL hLv hdL'' hB hB' hdB'
  have t2 := prod5_sub_le hvv hB hB' hdB' hLt hLtv hdLt' hY3 hY3' hdY3 hL hLv hdL'' hB hB' hdB'
  have hab : ‖tAB A' L' B' - tAB A L B‖ ≤ cDab n M σK σB * D := by
    have e : tAB A' L' B' - tAB A L B =
        (B' * L'ᵀ * (A' * omegaZeroMatrix n) * L' * B' - B * Lᵀ * (A * omegaZeroMatrix n) * L * B) -
          (B' * L'ᵀ * (omegaZeroMatrix n * A') * L' * B' -
            B * Lᵀ * (omegaZeroMatrix n * A) * L * B) := by
      unfold tAB; abel
    rw [e]
    exact ((norm_sub_le _ _).trans (add_le_add t1 t2)).trans
      (arith_ab hσK hσB hM.le hdD)
  -- the part `𝒯_F` (step `pt-f`)
  have hfF : ‖tF L' F' B'‖ ≤ vthh * σB * (vthh * (2 * n * σK)) * (n * ε' / δ * (vthh * σB)) :=
    norm_tF_le hLtv hF' hB'
  have hfF0 : ‖tF L F B‖ ≤ σB * (2 * n * σK) * (n * ε / δ * σB) := norm_tF_le hLt hF hB
  have hF2 : ‖tF L' F' B' - tF L F B‖ ≤ (1 + vthh ^ 3) * cT1 n σK σB * ε / δ := by
    have hεε : ε' / δ ≤ ε / δ := div_le_div_of_nonneg_right hε' hδ.le
    have h3 : 0 ≤ vthh ^ 3 * (2 * (n : ℝ) ^ 2 * σK * σB ^ 2) := by positivity
    calc ‖tF L' F' B' - tF L F B‖ ≤ ‖tF L' F' B'‖ + ‖tF L F B‖ := norm_sub_le _ _
      _ ≤ vthh * σB * (vthh * (2 * n * σK)) * (n * ε' / δ * (vthh * σB)) +
          σB * (2 * n * σK) * (n * ε / δ * σB) := add_le_add hfF hfF0
      _ = vthh ^ 3 * (2 * (n : ℝ) ^ 2 * σK * σB ^ 2) * (ε' / δ) +
          2 * (n : ℝ) ^ 2 * σK * σB ^ 2 * (ε / δ) := by ring
      _ ≤ vthh ^ 3 * (2 * (n : ℝ) ^ 2 * σK * σB ^ 2) * (ε / δ) +
          2 * (n : ℝ) ^ 2 * σK * σB ^ 2 * (ε / δ) :=
          add_le_add (mul_le_mul_of_nonneg_left hεε h3) le_rfl
      _ = (1 + vthh ^ 3) * cT1 n σK σB * ε / δ := by unfold cT1; ring
  -- the part `𝒯_c` (step `pt-c`)
  have hεδ1 : ε / δ ≤ 1 := (div_le_one hδ).2 hεδ
  have hε'δ1 : ε' / δ ≤ 1 := (div_le_one hδ).2 (hε'.trans hεδ)
  have hW : ‖Lᵀ * (Aᵀ + A) * L - Fᵀ * L - Lᵀ * F‖ ≤ wT n M σK := by
    refine (norm_W_le hA hAt hL hLt hF hFt).trans ?_
    have : 2 * (n : ℝ) * (n + 1) * σK * (ε / δ) ≤ 2 * n * (n + 1) * σK :=
      mul_le_of_le_one_right (by positivity) hεδ1
    calc _ = 4 * n * M * σK ^ 2 + 2 * n * (n + 1) * σK * (ε / δ) := by ring
      _ ≤ 4 * n * M * σK ^ 2 + 2 * n * (n + 1) * σK := by linarith
      _ = wT n M σK := by unfold wT; ring
  have hW' : ‖L'ᵀ * (A'ᵀ + A') * L' - F'ᵀ * L' - L'ᵀ * F'‖ ≤ vthh ^ 2 * wT n M σK := by
    refine (norm_W_le hA' hA't hLv hLtv hF' hF't).trans ?_
    have h1 : vthh * (2 * (n : ℝ) * (n + 1) * σK) * (ε' / δ) ≤ vthh * (2 * n * (n + 1) * σK) :=
      mul_le_of_le_one_right (by positivity) hε'δ1
    have h2 : vthh * (2 * (n : ℝ) * (n + 1) * σK) ≤ vthh ^ 2 * (2 * n * (n + 1) * σK) := by
      have : vthh ≤ vthh ^ 2 := by rw [vthh_eq]; norm_num
      exact mul_le_mul_of_nonneg_right this (by positivity)
    calc _ = vthh ^ 2 * (4 * n * M * σK ^ 2) + vthh * (2 * n * (n + 1) * σK) * (ε' / δ) := by
          ring
      _ ≤ vthh ^ 2 * (4 * n * M * σK ^ 2) + vthh ^ 2 * (2 * n * (n + 1) * σK) := by linarith
      _ = vthh ^ 2 * wT n M σK := by unfold wT; ring
  set Ωb := cOm n cR σK * ε / (γ * δ ^ (κ + 1)) with hΩb
  have hΩb0 : 0 ≤ Ωb := (norm_nonneg _).trans hΩ
  have hdΩ : ‖L'ᵀ * omegaZeroMatrix n * L' - Lᵀ * omegaZeroMatrix n * L‖ ≤
      2 * n * σK * (vthh + n) * D := by
    have e : L'ᵀ * omegaZeroMatrix n * L' - Lᵀ * omegaZeroMatrix n * L =
        (L'ᵀ - Lᵀ) * omegaZeroMatrix n * L' + Lᵀ * omegaZeroMatrix n * (L' - L) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]; abel
    rw [e]
    have nm := @FrameSharp.norm_mul_le_of_le
    have a1 : ‖(L'ᵀ - Lᵀ) * omegaZeroMatrix n * L'‖ ≤ 2 * n * D * (vthh * σK) := by
      refine nm ?_ hLv
      rw [norm_mul_omegaZeroMatrix]; exact hdLt'
    have a2 : ‖Lᵀ * omegaZeroMatrix n * (L' - L)‖ ≤ 2 * n * σK * (n * D) := by
      refine nm ?_ hdL''
      rw [norm_mul_omegaZeroMatrix]; exact hLt
    calc _ ≤ 2 * n * D * (vthh * σK) + 2 * n * σK * (n * D) := (norm_add_le _ _).trans
          (add_le_add a1 a2)
      _ = 2 * n * σK * (vthh + n) * D := by ring
  have hΩ' : ‖L'ᵀ * omegaZeroMatrix n * L'‖ ≤ Ωb + 2 * n * σK * (vthh + n) * D := by
    calc _ = ‖Lᵀ * omegaZeroMatrix n * L +
          (L'ᵀ * omegaZeroMatrix n * L' - Lᵀ * omegaZeroMatrix n * L)‖ := by rw [add_sub_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hΩ hdΩ)
  have hc1 := norm_tC_le (A := A') (F := F') hB' hΩ' hW'
  have hc0 := norm_tC_le (A := A) (F := F) hB hΩ hW
  have hC2 : ‖tC A' L' F' B' - tC A L F B‖ ≤
      cDc n M σK σB * D + (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * Ωb := by
    refine (norm_sub_le _ _).trans ((add_le_add hc1 hc0).trans (le_of_eq ?_))
    unfold cDc
    ring
  -- the total
  have e : tAB A' L' B' + tF L' F' B' + tC A' L' F' B' - (tAB A L B + tF L F B + tC A L F B) =
      (tAB A' L' B' - tAB A L B) + (tF L' F' B' - tF L F B) + (tC A' L' F' B' - tC A L F B) := by
    abel
  rw [e]
  refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hab hF2))
    hC2)).trans (le_of_eq ?_)
  unfold twistD
  rw [hD, hΩb]
  ring

/-- Blueprint `bp:p2s:perturbation`: `K'` is any holomorphic map on `T_{r-2δ}` close to `K`, with
invariance error `≤ ε'` at any frequency `ω'`. -/
theorem perturbation_poly (hC : CohData n τ κ cR) (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    {r β ε δ : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : KAM.Iso.Linear.AdmissibleNoTwist σK σB 𝔅 h ω r β ε K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h3δ : 3 * δ < r) (hεδ : ε ≤ δ) {K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ω' : Fin n → ℝ} {d ε' : ℝ} (hK' : DifferentiableOn ℂ K' (complexStrip n (r - 2 * δ)))
    (hd : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖K' θ - K θ‖ ≤ d) (hdβ : d < β)
    (hE' : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖invarianceError h K' ω' θ‖ ≤ ε') (hε' : ε' ≤ ε)
    (hs1 : n * d / δ ≤ vth * σK) (hs2 : σB * cGram n σK * d / δ ≤ vth) :
    (∀ θ ∈ complexStrip n (r - 2 * δ), Metric.ball (K' θ) (β - d) ⊆ 𝔅) ∧
    (∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖fderiv ℂ K' θ - fderiv ℂ K θ‖ ≤ n * d / δ ∧ ‖fderiv ℂ K' θ‖ ≤ vthh * σK ∧
      IsUnit (gramMatrix K' θ).det ∧ ‖(gramMatrix K' θ)⁻¹‖ ≤ vthh * σB ∧
      ‖(gramMatrix K' θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤ cB n σK σB * d / δ) ∧
    Continuous (fun x : Fin n → ℝ => torsion h K' ω' (fun i => (x i : ℂ))) ∧
    (∀ x : Fin n → ℝ, ‖torsion h K' ω' (fun i => (x i : ℂ)) - torsion h K ω (fun i => (x i : ℂ))‖ ≤
      twistD n κ cR M σK σB γ ε δ d) ∧
    (IsUnit (torsionAverage h K ω).det → ‖(torsionAverage h K ω)⁻¹‖ ≤ σT →
      σT * twistD n κ cR M σK σB γ ε δ d ≤ vth →
      IsUnit (torsionAverage h K' ω').det ∧ ‖(torsionAverage h K' ω')⁻¹‖ ≤ vthh * σT ∧
      ‖(torsionAverage h K' ω')⁻¹ - (torsionAverage h K ω)⁻¹‖ ≤
        vthh * σT ^ 2 * twistD n κ cR M σK σB γ ε δ d) := by
  have hr := hK.r_pos
  have hr3 : 0 < r - 3 * δ := by linarith
  have hsub2r : complexStrip n (r - 2 * δ) ⊆ complexStrip n r :=
    PerturbationAux.complexStrip_mono (by linarith)
  have hsub32 : complexStrip n (r - 3 * δ) ⊆ complexStrip n (r - 2 * δ) :=
    PerturbationAux.complexStrip_mono (by linarith)
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅 := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  -- (a)
  have hball : ∀ θ ∈ complexStrip n (r - 2 * δ), Metric.ball (K' θ) (β - d) ⊆ 𝔅 := fun θ hθ =>
    PerturbationAux.ball_subset_of_close (hK.ball_sub θ (hsub2r hθ)) (hd θ hθ)
  have hd0 : 0 ≤ d :=
    (norm_nonneg _).trans (hd _ (ofReal_mem_complexStrip (by linarith) (0 : Fin n → ℝ)))
  have hK'𝔅 : ∀ θ ∈ complexStrip n (r - 2 * δ), K' θ ∈ 𝔅 := fun θ hθ =>
    hball θ hθ (Metric.mem_ball_self (by linarith))
  -- (b), (c)
  have hfi := frame_items_sharp hS hK hδ hK' hd hs1 hs2
  have hG'3 : ∀ θ ∈ complexStrip n (r - 3 * δ), IsUnit (gramMatrix K' θ).det := fun θ hθ =>
    (hfi θ hθ).2.2.2.2.1
  -- continuity of the two torsions on `ℝⁿ`
  have hT' : DifferentiableOn ℂ (torsion h K' ω') (complexStrip n (r - 3 * δ)) := by
    have hNd := differentiableOn_normalMat (hK'.mono hsub32) hG'3
    exact FrameAux.differentiableOn_torsion hNd (FrameAux.differentiableOn_normalFieldMat
      (FrameAux.differentiableOn_linMat hS (hK'.mono hsub32) fun θ hθ => hK'𝔅 θ (hsub32 hθ)) hNd)
  have hc' := FrameAux.continuous_torsion_real hr3 hT'
  have hT : DifferentiableOn ℂ (torsion h K ω) (complexStrip n r) :=
    PerturbationAux.differentiableOn_torsion_of hS hK.holo hK𝔅 hGu
  have hc := FrameAux.continuous_torsion_real hr hT
  -- (d)
  have hdiff := torsion_diff_real hC hS hK hδ hδ1 h3δ hεδ hK' hd hdβ hE' hε' hs1 hs2
  refine ⟨hball, fun θ hθ => ?_, hc', hdiff, fun hTu hTσ hsm => ?_⟩
  · obtain ⟨h1, -, h3, -, h5, h6, h7⟩ := hfi θ hθ
    exact ⟨h1, h3, h5, h6, h7⟩
  -- (e): step `pt-avg`
  have havg := norm_torsionAverage_sub_le_any hc hc' hdiff
  have hA : IsUnit (torsionAverage h K ω) := (Matrix.isUnit_iff_isUnit_det _).2 hTu
  have hσT := hS.σT_pos
  have hsmall : ‖(torsionAverage h K ω)⁻¹‖ *
      ‖torsionAverage h K' ω' - torsionAverage h K ω‖ ≤ vth :=
    (mul_le_mul hTσ havg (norm_nonneg _) hσT.le).trans hsm
  obtain ⟨hU, hBn, hBdiff⟩ := neumann_ratio hA (q := vth) (by rw [vth_eq]; norm_num) hsmall
  rw [add_sub_cancel] at hU hBn hBdiff
  have h17 : (1 : ℝ) - vth = 7 / 8 := by rw [vth_eq]; norm_num
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).1 hU, ?_, ?_⟩
  · calc _ ≤ ‖(torsionAverage h K ω)⁻¹‖ / (1 - vth) := hBn
      _ ≤ σT / (1 - vth) := div_le_div_of_nonneg_right hTσ (by rw [h17]; norm_num)
      _ = vthh * σT := by rw [h17, vthh_eq]; ring
  · have hTT : ‖(torsionAverage h K ω)⁻¹‖ ^ 2 ≤ σT ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hTσ 2
    calc _ ≤ ‖(torsionAverage h K ω)⁻¹‖ ^ 2 *
          ‖torsionAverage h K' ω' - torsionAverage h K ω‖ / (1 - vth) := hBdiff
      _ ≤ σT ^ 2 * twistD n κ cR M σK σB γ ε δ d / (1 - vth) :=
          div_le_div_of_nonneg_right (mul_le_mul hTT havg (norm_nonneg _) (by positivity))
            (by rw [h17]; norm_num)
      _ = vthh * σT ^ 2 * twistD n κ cR M σK σB γ ε δ d := by rw [h17, vthh_eq]; ring

end KAM.Sharp

end
