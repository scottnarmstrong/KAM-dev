/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.TorsionPoly
public import KAM.Sharp.CohData
public import KAM.Sharp.Constants
public import KAM.Apost.Geometry
public import KAM.Iso.Linear.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Frame bounds with separate sizes, and the geometry of an approximately invariant torus

* Blueprint `bp:p2s:frame-bounds` (`KAM.Sharp.frame_bounds`): pointwise bounds of `L`, `Lᵀ`, `N`,
  `Nᵀ`, `Ω_K`, `P`, `A`, `Aᵀ` and of `ηᴸ`, `ηᴺ` in the separate sizes `σ_K, σ_B, M`, the identities
  `Nᵀ Ω₀ = B Lᵀ`, `Aᵀ = Ω₀ A Ω₀` and the bound `|P ξ| ≤ σ_K |ξᴸ| + σ_K σ_B |ξᴺ|`.
* Blueprint `bp:p2s:geometry` (`KAM.Sharp.geometry_sep`): Lemma `bp:p2:geometry` with the constants
  `C_Ω = 2n(n+1) c_R σ_K`, `C_sym = max {1, σ_B²} C_Ω`, `C_red = 2nσ_K max {nσ_B, n + σ_B}` and
  general small-divisor data, for a torus without any torsion hypothesis
  (`KAM.Iso.Linear.AdmissibleNoTwist`).

The proof follows the blueprint: `step:p2s:fb-frame`, `fb-a`, `fb-eta` for `frame_bounds`;
`step:p2s:geo-de` (`KAM.Apost.Geometry.geo_de`), `geo-dom` (`geo_domegak_sep`, `geo_ered_sep`) and
`geo-om` (`CohData.apriori` on `T_{r-δ}`) for `geometry_sep`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp

open KAM KAM.Torus KAM.Apost

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

namespace FrameSharp

variable {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}

/-- `‖X * Y‖ ≤ a b` from `‖X‖ ≤ a`, `‖Y‖ ≤ b` (row-sum operator norm). -/
theorem norm_mul_le_of_le {ι κ' μ' : Type*} [Fintype ι] [Fintype κ'] [Fintype μ']
    {X : Matrix ι κ' ℂ} {Y : Matrix κ' μ' ℂ} {a b : ℝ} (hX : ‖X‖ ≤ a) (hY : ‖Y‖ ≤ b) :
    ‖X * Y‖ ≤ a * b :=
  (Matrix.linfty_opNorm_mul X Y).trans
    (mul_le_mul hX hY (norm_nonneg _) ((norm_nonneg _).trans hX))

/-- Step `step:p2s:fb-a`: `Aᵀ = Ω₀ A Ω₀` in the canonical case. -/
theorem linMat_transpose (hS : Standing n τ M σK σB σT 𝔅 h ω γ) (hK𝔅 : K θ ∈ 𝔅) :
    (linMat h K θ)ᵀ = omegaZeroMatrix n * linMat h K θ * omegaZeroMatrix n := by
  have hA : (linMat h K θ)ᵀ * omegaZeroMatrix n + omegaZeroMatrix n * linMat h K θ = 0 :=
    (ham_symplectic hS (K θ) hK𝔅).2.2
  have h1 : (linMat h K θ)ᵀ * omegaZeroMatrix n = -(omegaZeroMatrix n * linMat h K θ) :=
    eq_neg_of_add_eq_zero_left hA
  calc (linMat h K θ)ᵀ = -((linMat h K θ)ᵀ * (omegaZeroMatrix n * omegaZeroMatrix n)) := by
        rw [omegaZeroMatrix_mul_self, Matrix.mul_neg, Matrix.mul_one, neg_neg]
    _ = -((linMat h K θ)ᵀ * omegaZeroMatrix n * omegaZeroMatrix n) := by rw [Matrix.mul_assoc]
    _ = omegaZeroMatrix n * linMat h K θ * omegaZeroMatrix n := by
        rw [h1, Matrix.neg_mul, neg_neg]

end FrameSharp

/-- Blueprint `bp:p2s:frame-bounds`. -/
theorem frame_bounds (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ} (hK𝔅 : K θ ∈ 𝔅)
    {sK sB : ℝ} (hL : ‖fderiv ℂ K θ‖ ≤ sK) (hG : IsUnit (gramMatrix K θ).det)
    (hB : ‖(gramMatrix K θ)⁻¹‖ ≤ sB) (ω' : Fin n → ℝ) :
    ‖tangentMat K θ‖ ≤ sK ∧ ‖(tangentMat K θ)ᵀ‖ ≤ 2 * n * sK ∧ ‖normalMat K θ‖ ≤ sK * sB ∧
    (normalMat K θ)ᵀ * omegaZeroMatrix n = (gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ ∧
    ‖(normalMat K θ)ᵀ‖ ≤ 2 * n * sK * sB ∧ ‖lagrangeMat K θ‖ ≤ 2 * n * sK ^ 2 ∧
    ‖frameMat K θ‖ ≤ sK * (1 + sB) ∧ ‖linMat h K θ‖ ≤ M ∧
    (linMat h K θ)ᵀ = omegaZeroMatrix n * linMat h K θ * omegaZeroMatrix n ∧
    ‖(linMat h K θ)ᵀ‖ ≤ M ∧
    (∀ ε, ‖invarianceError h K ω' θ‖ ≤ ε →
      etaL h K ω' θ = -(((gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ) *ᵥ
        sumVec n (invarianceError h K ω' θ)) ∧
      ‖etaL h K ω' θ‖ ≤ 2 * n * sK * sB * ε ∧ ‖etaN h K ω' θ‖ ≤ 2 * n * sK * ε) ∧
    ∀ ξL ξN : Fin n → ℂ, ‖frameMat K θ *ᵥ Sum.elim ξL ξN‖ ≤ sK * ‖ξL‖ + sK * sB * ‖ξN‖ := by
  -- `det G ≠ 0` is part of the blueprint statement; `Nᵀ Ω₀ = B Lᵀ` holds for the total inverse.
  have _hG : IsUnit (gramMatrix K θ).det := hG
  have hsK : 0 ≤ sK := (norm_nonneg _).trans hL
  have hsB : 0 ≤ sB := (norm_nonneg _).trans hB
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- step `fb-frame`
  have h1 : ‖tangentMat K θ‖ ≤ sK := (FrameAux.norm_tangentMat K θ).le.trans hL
  have h2 : ‖(tangentMat K θ)ᵀ‖ ≤ 2 * n * sK :=
    (FrameAux.norm_transpose_le_two_mul _).trans (mul_le_mul_of_nonneg_left h1 (by positivity))
  have h3 : ‖normalMat K θ‖ ≤ sK * sB := by
    unfold normalMat
    refine FrameSharp.norm_mul_le_of_le ?_ hB
    rw [norm_omegaZeroMatrix_mul]
    exact h1
  have h4 := TorsionPoly.normalMat_transpose_mul_omega K θ
  have h5 : ‖(normalMat K θ)ᵀ‖ ≤ 2 * n * sK * sB := by
    refine (FrameAux.norm_transpose_le_two_mul _).trans ?_
    rw [mul_assoc (2 * (n : ℝ))]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have h6 : ‖lagrangeMat K θ‖ ≤ 2 * n * sK ^ 2 := by
    unfold lagrangeMat
    have : ‖(tangentMat K θ)ᵀ * omegaZeroMatrix n‖ ≤ 2 * n * sK := by
      rw [norm_mul_omegaZeroMatrix]
      exact h2
    calc ‖(tangentMat K θ)ᵀ * omegaZeroMatrix n * tangentMat K θ‖ ≤ 2 * n * sK * sK :=
          FrameSharp.norm_mul_le_of_le this h1
      _ = 2 * n * sK ^ 2 := by ring
  have h7 : ‖frameMat K θ‖ ≤ sK * (1 + sB) := by
    unfold frameMat
    calc ‖Matrix.fromCols (tangentMat K θ) (normalMat K θ)‖
        ≤ ‖tangentMat K θ‖ + ‖normalMat K θ‖ := Tools.norm_fromCols_le_add _ _
      _ ≤ sK + sK * sB := add_le_add h1 h3
      _ = sK * (1 + sB) := by ring
  -- step `fb-a`
  have h8 : ‖linMat h K θ‖ ≤ M := by
    rw [FrameAux.norm_linMat]
    exact (hS.bounds _ hK𝔅).2.1
  have h9 := FrameSharp.linMat_transpose hS (θ := θ) hK𝔅
  have h10 : ‖(linMat h K θ)ᵀ‖ ≤ M := by
    rw [h9, norm_mul_omegaZeroMatrix, norm_omegaZeroMatrix_mul]
    exact h8
  -- step `fb-eta`
  have h11 : ∀ ε, ‖invarianceError h K ω' θ‖ ≤ ε →
      etaL h K ω' θ = -(((gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ) *ᵥ
        sumVec n (invarianceError h K ω' θ)) ∧
      ‖etaL h K ω' θ‖ ≤ 2 * n * sK * sB * ε ∧ ‖etaN h K ω' θ‖ ≤ 2 * n * sK * ε := by
    intro ε hE
    have hε : 0 ≤ ε := (norm_nonneg _).trans hE
    refine ⟨by rw [etaL, h4], ?_, ?_⟩
    · unfold etaL
      rw [norm_neg]
      refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
      rw [norm_mul_omegaZeroMatrix, norm_sumVec]
      exact mul_le_mul h5 hE (norm_nonneg _) (by positivity)
    · unfold etaN
      refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
      rw [norm_mul_omegaZeroMatrix, norm_sumVec]
      exact mul_le_mul h2 hE (norm_nonneg _) (by positivity)
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, fun ξL ξN => ?_⟩
  unfold frameMat
  rw [Matrix.fromCols_mulVec_sumElim]
  calc ‖tangentMat K θ *ᵥ ξL + normalMat K θ *ᵥ ξN‖
      ≤ ‖tangentMat K θ *ᵥ ξL‖ + ‖normalMat K θ *ᵥ ξN‖ := norm_add_le _ _
    _ ≤ ‖tangentMat K θ‖ * ‖ξL‖ + ‖normalMat K θ‖ * ‖ξN‖ :=
        add_le_add (Matrix.linfty_opNorm_mulVec _ _) (Matrix.linfty_opNorm_mulVec _ _)
    _ ≤ sK * ‖ξL‖ + sK * sB * ‖ξN‖ :=
        add_le_add (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))

namespace FrameSharp

variable {r ε δ : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- Step `step:p2s:geo-dom`: `|∂_ω Ω_K| ≤ 2n(n+1) σ_K ε/δ` on `T_{r-δ}`. -/
theorem geo_domegak_sep (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hA3 : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ σK)
    (hA6 : ∀ θ ∈ complexStrip n r, ‖invarianceError h K ω θ‖ ≤ ε) (hδ : 0 < δ) :
    ∀ θ ∈ complexStrip n (r - δ),
      ‖fderiv ℂ (lagrangeMat K) θ (fun l => (ω l : ℂ))‖ ≤ 2 * n * (n + 1) * σK * ε / δ := by
  intro θ hθ
  have hθr := Geometry.complexStrip_sub_subset hδ.le hθ
  obtain ⟨hDE, hDEt⟩ := Geometry.geo_de hS hK hK𝔅 hA6 hδ θ hθ
  have hL : ‖tangentMat K θ‖ ≤ σK := (FrameAux.norm_tangentMat K θ).le.trans (hA3 θ hθr)
  have hLt : ‖(tangentMat K θ)ᵀ‖ ≤ 2 * n * σK :=
    (FrameAux.norm_transpose_le_two_mul _).trans
      (mul_le_mul_of_nonneg_left hL (by positivity))
  rw [Identities.fi_dLagrange hS hK hK𝔅 hθr]
  have e1 : ‖(errDerivMat h K ω θ)ᵀ * omegaZeroMatrix n * tangentMat K θ‖ ≤
      2 * n * ε / δ * σK := by
    refine norm_mul_le_of_le ?_ hL
    rw [norm_mul_omegaZeroMatrix]
    exact hDEt
  have e2 : ‖(tangentMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ‖ ≤
      2 * n * σK * (n * ε / δ) := by
    refine norm_mul_le_of_le ?_ hDE
    rw [norm_mul_omegaZeroMatrix]
    exact hLt
  calc ‖-((errDerivMat h K ω θ)ᵀ * omegaZeroMatrix n * tangentMat K θ) -
        (tangentMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ‖
      ≤ ‖(errDerivMat h K ω θ)ᵀ * omegaZeroMatrix n * tangentMat K θ‖ +
          ‖(tangentMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
    _ ≤ 2 * n * ε / δ * σK + 2 * n * σK * (n * ε / δ) := add_le_add e1 e2
    _ = 2 * n * (n + 1) * σK * ε / δ := by ring

/-- Step `step:p2s:geo-dom`: `|E_red| ≤ C_red ε/δ` on `T_{r-δ}`. -/
theorem geo_ered_sep (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hA3 : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ σK)
    (hA4 : ∀ θ ∈ complexStrip n r, ‖(gramMatrix K θ)⁻¹‖ ≤ σB)
    (hA6 : ∀ θ ∈ complexStrip n r, ‖invarianceError h K ω θ‖ ≤ ε) (hδ : 0 < δ) :
    ∀ θ ∈ complexStrip n (r - δ), ‖redDefect h K ω θ‖ ≤ cRed n σK σB * ε / δ := by
  intro θ hθ
  have hθr := Geometry.complexStrip_sub_subset hδ.le hθ
  obtain ⟨hDE, hDEt⟩ := Geometry.geo_de hS hK hK𝔅 hA6 hδ θ hθ
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hA6 θ hθr)
  have hσK : 0 ≤ σK := (norm_nonneg _).trans (hA3 θ hθr)
  have hσB : 0 ≤ σB := (norm_nonneg _).trans (hA4 θ hθr)
  have hL : ‖tangentMat K θ‖ ≤ σK := (FrameAux.norm_tangentMat K θ).le.trans (hA3 θ hθr)
  have hLt : ‖(tangentMat K θ)ᵀ‖ ≤ 2 * n * σK :=
    (FrameAux.norm_transpose_le_two_mul _).trans
      (mul_le_mul_of_nonneg_left hL (by positivity))
  have hN : ‖normalMat K θ‖ ≤ σK * σB := by
    unfold normalMat
    refine norm_mul_le_of_le ?_ (hA4 θ hθr)
    rw [norm_omegaZeroMatrix_mul]
    exact hL
  have hεδ : 0 ≤ ε / δ := div_nonneg hε hδ.le
  -- first block row: `Nᵀ Ω₀ DE = B Lᵀ DE`
  have r1 : ‖(normalMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ‖ ≤
      2 * n * σK * (n * σB) * (ε / δ) := by
    rw [TorsionPoly.normalMat_transpose_mul_omega]
    calc ‖(gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ * errDerivMat h K ω θ‖
        ≤ σB * (2 * n * σK) * (n * ε / δ) :=
          norm_mul_le_of_le (norm_mul_le_of_le (hA4 θ hθr) hLt) hDE
      _ = 2 * n * σK * (n * σB) * (ε / δ) := by ring
  -- second block row
  have r2 : ‖-((tangentMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ)‖ +
      ‖(errDerivMat h K ω θ)ᵀ * omegaZeroMatrix n * normalMat K θ‖ ≤
      2 * n * σK * (n + σB) * (ε / δ) := by
    rw [norm_neg]
    have a1 : ‖(tangentMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ‖ ≤
        2 * n * σK * (n * ε / δ) := by
      refine norm_mul_le_of_le ?_ hDE
      rw [norm_mul_omegaZeroMatrix]
      exact hLt
    have a2 : ‖(errDerivMat h K ω θ)ᵀ * omegaZeroMatrix n * normalMat K θ‖ ≤
        2 * n * ε / δ * (σK * σB) := by
      refine norm_mul_le_of_le ?_ hN
      rw [norm_mul_omegaZeroMatrix]
      exact hDEt
    calc _ ≤ 2 * n * σK * (n * ε / δ) + 2 * n * ε / δ * (σK * σB) := add_le_add a1 a2
      _ = 2 * n * σK * (n + σB) * (ε / δ) := by ring
  have hmax1 : 2 * n * σK * (n * σB) * (ε / δ) ≤ cRed n σK σB * (ε / δ) := by
    unfold cRed
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _)
      (by positivity)) hεδ
  have hmax2 : 2 * n * σK * (n + σB) * (ε / δ) ≤ cRed n σK σB * (ε / δ) := by
    unfold cRed
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _)
      (by positivity)) hεδ
  unfold redDefect
  calc _ ≤ max (‖(normalMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ‖ +
        ‖(0 : Matrix (Fin n) (Fin n) ℂ)‖)
        (‖-((tangentMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ)‖ +
          ‖(errDerivMat h K ω θ)ᵀ * omegaZeroMatrix n * normalMat K θ‖) :=
        norm_fromBlocks_le _ _ _ _
    _ ≤ cRed n σK σB * (ε / δ) := by
        rw [norm_zero, add_zero]
        exact max_le (r1.trans hmax1) (r2.trans hmax2)
    _ = cRed n σK σB * ε / δ := by ring

end FrameSharp

/-- Blueprint `bp:p2s:geometry` (no torsion hypothesis). -/
theorem geometry_sep {κ cR : ℝ} (hC : CohData n τ κ cR) (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    {r β ε δ : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : KAM.Iso.Linear.AdmissibleNoTwist σK σB 𝔅 h ω r β ε K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h2δ : 2 * δ < r) :
    (∀ θ ∈ complexStrip n (r - δ),
      ‖errDerivMat h K ω θ‖ ≤ n * ε / δ ∧ ‖(errDerivMat h K ω θ)ᵀ‖ ≤ 2 * n * ε / δ ∧
      ‖fderiv ℂ (lagrangeMat K) θ (fun l => (ω l : ℂ))‖ ≤ 2 * n * (n + 1) * σK * ε / δ ∧
      ‖redDefect h K ω θ‖ ≤ cRed n σK σB * ε / δ) ∧
    ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖lagrangeMat K θ‖ ≤ cOm n cR σK * ε / (γ * δ ^ (κ + 1)) ∧
      ‖symDefect K θ‖ ≤ cSym n cR σK σB * ε / (γ * δ ^ (κ + 1)) := by
  have hr := hK.r_pos
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅 := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  have hB : ∀ θ ∈ complexStrip n r, ‖(gramMatrix K θ)⁻¹‖ ≤ σB := fun θ hθ => (hK.gram θ hθ).2
  have hdom := FrameSharp.geo_domegak_sep hS hK.holo hK𝔅 hK.deriv_le hK.error_le hδ
  have hΩ : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖lagrangeMat K θ‖ ≤ cOm n cR σK * ε / (γ * δ ^ (κ + 1)) := by
    intro θ hθ
    have hθ' : θ ∈ complexStrip n (r - δ - δ) := by
      have : r - δ - δ = r - 2 * δ := by ring
      rw [this]
      exact hθ
    have hdiff : DifferentiableOn ℂ (lagrangeMat K) (complexStrip n (r - δ)) :=
      (Exactness.differentiableOn_lagrangeMat hK.holo).mono
        fun _ hz => Geometry.complexStrip_sub_subset hδ.le hz
    have hper : IsPeriodicOn (lagrangeMat K) (r - δ) := fun i z hz =>
      periodic_lagrangeMat hK.primary i z (Geometry.complexStrip_sub_subset hδ.le hz)
    have havg : avg (lagrangeMat K) = 0 := (exactness hS hr hK.holo hK.primary hK𝔅).1
    have hcoh := hC.apriori hS.gamma_pos hS.dio (r := r - δ) hδ hδ1 (by linarith) (lagrangeMat K)
      _ hdiff hper havg hdom θ hθ'
    have hγ := hS.gamma_pos
    have hδκ : 0 < δ ^ κ := Real.rpow_pos_of_pos hδ _
    calc ‖lagrangeMat K θ‖ ≤ cR * γ⁻¹ * δ ^ (-κ) * (2 * n * (n + 1) * σK * ε / δ) := hcoh
      _ = cOm n cR σK * ε / (γ * δ ^ (κ + 1)) := by
        rw [Real.rpow_neg hδ.le, Real.rpow_add_one hδ.ne']
        unfold cOm
        field_simp
  refine ⟨fun θ hθ => ?_, fun θ hθ => ?_⟩
  · obtain ⟨h1, h2⟩ := Geometry.geo_de hS hK.holo hK𝔅 hK.error_le hδ θ hθ
    exact ⟨h1, h2, hdom θ hθ,
      FrameSharp.geo_ered_sep hS hK.holo hK𝔅 hK.deriv_le hB hK.error_le hδ θ hθ⟩
  · have hθr : θ ∈ complexStrip n r := fun i => lt_of_lt_of_le (hθ i) (by linarith)
    refine ⟨hΩ θ hθ, ?_⟩
    have hBθ := hB θ hθr
    have hσB : 0 ≤ σB := (norm_nonneg _).trans hBθ
    have hBB : ‖(gramMatrix K θ)⁻¹‖ ^ 2 ≤ σB ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hBθ 2
    rw [Identities.fi_symDefect K (hK.gram θ hθr).1, Tools.norm_fromBlocks_diagonal]
    have hΩθ := hΩ θ hθ
    have hcS : cSym n cR σK σB * ε / (γ * δ ^ (κ + 1)) =
        max 1 (σB ^ 2) * (cOm n cR σK * ε / (γ * δ ^ (κ + 1))) := by
      unfold cSym
      ring
    rw [hcS]
    have hX0 : 0 ≤ cOm n cR σK * ε / (γ * δ ^ (κ + 1)) := (norm_nonneg _).trans hΩθ
    refine max_le ?_ ?_
    · calc ‖lagrangeMat K θ‖ ≤ 1 * (cOm n cR σK * ε / (γ * δ ^ (κ + 1))) := by
            rw [one_mul]
            exact hΩθ
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
    · calc ‖(gramMatrix K θ)⁻¹ * lagrangeMat K θ * (gramMatrix K θ)⁻¹‖
          ≤ ‖(gramMatrix K θ)⁻¹‖ * ‖lagrangeMat K θ‖ * ‖(gramMatrix K θ)⁻¹‖ :=
            (Matrix.linfty_opNorm_mul _ _).trans
              (mul_le_mul_of_nonneg_right (Matrix.linfty_opNorm_mul _ _) (norm_nonneg _))
        _ = ‖(gramMatrix K θ)⁻¹‖ ^ 2 * ‖lagrangeMat K θ‖ := by ring
        _ ≤ σB ^ 2 * (cOm n cR σK * ε / (γ * δ ^ (κ + 1))) :=
            mul_le_mul hBB hΩθ (norm_nonneg _) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hX0

end KAM.Sharp

end
