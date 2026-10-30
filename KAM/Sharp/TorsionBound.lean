/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.Frame
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The torsion bound without `1/δ`

Blueprint `bp:p2s:torsion-bound` (`KAM.Sharp.torsion_bound`): for a torus with the hypotheses of
`bp:p2s:geometry` (no torsion hypothesis), `0 < δ ≤ 1`, `δ < r` and `ε ≤ δ`, on `T_{r-δ}`
`|T| ≤ C_T0 + C_T1 ε/δ + C_T2 ε/(γ δ^{κ+1})`.

The proof follows the blueprint:

* `step:p2s:tb-om`: the Lagrangian defect on `T_{r-δ}` is `KAM.Sharp.geometry_sep` with loss `δ/2`,
  `|Ω_K| ≤ 2^{κ+1} C_Ω ε/(γ δ^{κ+1})`; the derivative of the error is `KAM.Apost.Geometry.geo_de`
  with loss `δ`;
* `step:p2s:tb-parts`: `T = 𝒯(A, L, B, DE)` (`KAM.Sharp.torsion_identity`) and the bound of the
  torsion
  polynomial in terms of bounds of its arguments, `KAM.Sharp.norm_torsionPoly_le` (also used by the
  perturbation lemma, package A4).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp

open KAM KAM.Torus KAM.Apost

variable {n : ℕ}

/-- The bound of the torsion polynomial `𝒯(A, L, B, F)` (step `step:p2s:tb-parts`) in terms of
bounds of `A`, `Aᵀ`, `L`, `Lᵀ`, `F`, `Fᵀ`, `B` and `Ω = Lᵀ Ω₀ L`: the three parts `𝒯_ab`, `𝒯_F`,
`𝒯_c` contribute `sB (2n sK) (2 M sK sB)`, `sB (2n sK) f sB` and
`sB w sB (2n sK (2M) sK + ft sK + 2n sK f) sB`. -/
theorem norm_torsionPoly_le {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    {L F : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin n) ℂ}
    {M sK sB f ft w : ℝ} (hA : ‖A‖ ≤ M) (hAt : ‖Aᵀ‖ ≤ M) (hL : ‖L‖ ≤ sK)
    (hLt : ‖Lᵀ‖ ≤ 2 * n * sK) (hF : ‖F‖ ≤ f) (hFt : ‖Fᵀ‖ ≤ ft) (hB : ‖B‖ ≤ sB)
    (hΩ : ‖Lᵀ * omegaZeroMatrix n * L‖ ≤ w) :
    ‖torsionPoly A L F B‖ ≤
      sB * (2 * n * sK) * (M * sK * sB + M * sK * sB + f * sB) +
        sB * w * sB * (2 * n * sK * (2 * M) * sK + ft * sK + 2 * n * sK * f) * sB := by
  have nm := @FrameSharp.norm_mul_le_of_le
  have hM : 0 ≤ M := (norm_nonneg _).trans hA
  have hAO : ‖A * omegaZeroMatrix n‖ ≤ M := by rw [norm_mul_omegaZeroMatrix]; exact hA
  have hOA : ‖omegaZeroMatrix n * A‖ ≤ M := by rw [norm_omegaZeroMatrix_mul]; exact hA
  have hOF : ‖omegaZeroMatrix n * F‖ ≤ f := by rw [norm_omegaZeroMatrix_mul]; exact hF
  have hAA : ‖Aᵀ + A‖ ≤ 2 * M := (norm_add_le _ _).trans (by linarith)
  -- `𝒯_ab + 𝒯_F`
  have t1 : ‖A * omegaZeroMatrix n * L * B‖ ≤ M * sK * sB := nm (nm hAO hL) hB
  have t2 : ‖omegaZeroMatrix n * A * L * B‖ ≤ M * sK * sB := nm (nm hOA hL) hB
  have t3 : ‖omegaZeroMatrix n * F * B‖ ≤ f * sB := nm hOF hB
  have tin : ‖A * omegaZeroMatrix n * L * B - omegaZeroMatrix n * A * L * B +
      omegaZeroMatrix n * F * B‖ ≤ M * sK * sB + M * sK * sB + f * sB :=
    (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add t1 t2)) t3)
  have p1 : ‖B * Lᵀ * (A * omegaZeroMatrix n * L * B - omegaZeroMatrix n * A * L * B +
      omegaZeroMatrix n * F * B)‖ ≤ sB * (2 * n * sK) * (M * sK * sB + M * sK * sB + f * sB) :=
    nm (nm hB hLt) tin
  -- `𝒯_c`
  have w1 : ‖Lᵀ * (Aᵀ + A) * L‖ ≤ 2 * n * sK * (2 * M) * sK := nm (nm hLt hAA) hL
  have w2 : ‖Fᵀ * L‖ ≤ ft * sK := nm hFt hL
  have w3 : ‖Lᵀ * F‖ ≤ 2 * n * sK * f := nm hLt hF
  have win : ‖Lᵀ * (Aᵀ + A) * L - Fᵀ * L - Lᵀ * F‖ ≤
      2 * n * sK * (2 * M) * sK + ft * sK + 2 * n * sK * f :=
    (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add w1 w2)) w3)
  have p2 : ‖B * (Lᵀ * omegaZeroMatrix n * L) * B * (Lᵀ * (Aᵀ + A) * L - Fᵀ * L - Lᵀ * F) * B‖ ≤
      sB * w * sB * (2 * n * sK * (2 * M) * sK + ft * sK + 2 * n * sK * f) * sB :=
    nm (nm (nm (nm hB hΩ) hB) win) hB
  unfold torsionPoly
  exact (norm_add_le _ _).trans (add_le_add p1 p2)

variable {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

/-- Step `step:p2s:tb-om`, constants: `C_Ω ε/(γ (δ/2)^{κ+1}) = 2^{κ+1} C_Ω ε/(γ δ^{κ+1})`. -/
theorem half_loss_eq {κ c ε δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) :
    c * ε / (γ * (δ / 2) ^ (κ + 1)) = (2 : ℝ) ^ (κ + 1) * c * (ε / (γ * δ ^ (κ + 1))) := by
  have hδκ : 0 < δ ^ (κ + 1) := Real.rpow_pos_of_pos hδ _
  have h2κ : 0 < (2 : ℝ) ^ (κ + 1) := Real.rpow_pos_of_pos two_pos _
  rw [Real.div_rpow hδ.le zero_le_two]
  field_simp

/-- Blueprint `bp:p2s:torsion-bound`. -/
theorem torsion_bound {κ cR : ℝ} (hC : CohData n τ κ cR) (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    {r β ε δ : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : KAM.Iso.Linear.AdmissibleNoTwist σK σB 𝔅 h ω r β ε K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδr : δ < r) (hεδ : ε ≤ δ) :
    ∀ θ ∈ complexStrip n (r - δ), ‖torsion h K ω θ‖ ≤
      cT0 n M σK σB + cT1 n σK σB * ε / δ + cT2 n κ cR M σK σB * ε / (γ * δ ^ (κ + 1)) := by
  intro θ hθ
  have hr := hK.r_pos
  have hγ := hS.gamma_pos
  have hθr : θ ∈ complexStrip n r := Geometry.complexStrip_sub_subset hδ.le hθ
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅 := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  have hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  have hε : 0 ≤ ε := hK.ε_nonneg
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- the frame at `θ`
  obtain ⟨hL, hLt, -, -, -, -, -, hA, -, hAt, -, -⟩ :=
    frame_bounds hS (hK𝔅 θ hθr) (hK.deriv_le θ hθr) (hG θ hθr) (hK.gram θ hθr).2 ω
  have hσK : 0 ≤ σK := (norm_nonneg _).trans hL
  have hσB : 0 ≤ σB := (norm_nonneg _).trans (hK.gram θ hθr).2
  -- step `tb-om`
  obtain ⟨hF, hFt⟩ := Geometry.geo_de hS hK.holo hK𝔅 hK.error_le hδ θ hθ
  have hθ2 : θ ∈ complexStrip n (r - 2 * (δ / 2)) := by
    have : r - 2 * (δ / 2) = r - δ := by ring
    rw [this]
    exact hθ
  have hΩ := ((geometry_sep hC hS hK (half_pos hδ) (by linarith) (by linarith)).2 θ hθ2).1
  rw [half_loss_eq hγ hδ] at hΩ
  have hΩ' : ‖(tangentMat K θ)ᵀ * omegaZeroMatrix n * tangentMat K θ‖ ≤
      (2 : ℝ) ^ (κ + 1) * cOm n cR σK * (ε / (γ * δ ^ (κ + 1))) := hΩ
  -- step `tb-parts`
  rw [(torsion_identity hS hr hK.holo hK𝔅 hG ω θ hθr).2.2]
  refine (norm_torsionPoly_le hA hAt hL hLt hF hFt (hK.gram θ hθr).2 hΩ').trans ?_
  -- the arithmetic
  set X := ε / δ with hX
  set Y := ε / (γ * δ ^ (κ + 1)) with hY
  have hX0 : 0 ≤ X := div_nonneg hε hδ.le
  have hX1 : X ≤ 1 := (div_le_one hδ).2 hεδ
  have hY0 : 0 ≤ Y := div_nonneg hε (mul_pos hγ (Real.rpow_pos_of_pos hδ _)).le
  have hcOm : 0 ≤ cOm n cR σK := by
    unfold cOm
    have := hC.cR_pos
    positivity
  have hW : 0 ≤ (2 : ℝ) ^ (κ + 1) * cOm n cR σK * Y :=
    mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos two_pos _).le hcOm) hY0
  have hnX : (n : ℝ) * ε / δ = n * X := by rw [hX]; ring
  have hnX2 : 2 * (n : ℝ) * ε / δ = 2 * n * X := by rw [hX]; ring
  rw [hnX, hnX2]
  have hin : 2 * n * σK * (2 * M) * σK + 2 * n * X * σK + 2 * n * σK * (n * X) ≤ wT n M σK := by
    unfold wT
    have : 2 * (n : ℝ) * X * σK + 2 * n * σK * (n * X) ≤ 2 * n * (n + 1) * σK := by
      have e : 2 * (n : ℝ) * X * σK + 2 * n * σK * (n * X) = 2 * n * (n + 1) * σK * X := by ring
      rw [e]
      exact mul_le_of_le_one_right (by positivity) hX1
    linarith
  have hpart2 : σB * ((2 : ℝ) ^ (κ + 1) * cOm n cR σK * Y) * σB *
      (2 * n * σK * (2 * M) * σK + 2 * n * X * σK + 2 * n * σK * (n * X)) * σB ≤
      cT2 n κ cR M σK σB * ε / (γ * δ ^ (κ + 1)) := by
    have hcT2 : cT2 n κ cR M σK σB * ε / (γ * δ ^ (κ + 1)) =
        σB * ((2 : ℝ) ^ (κ + 1) * cOm n cR σK * Y) * σB * wT n M σK * σB := by
      unfold cT2
      rw [hY]
      ring
    rw [hcT2]
    have hpos : 0 ≤ σB * ((2 : ℝ) ^ (κ + 1) * cOm n cR σK * Y) * σB :=
      mul_nonneg (mul_nonneg hσB hW) hσB
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hin hpos) hσB
  have hpart1 : σB * (2 * n * σK) * (M * σK * σB + M * σK * σB + n * X * σB) =
      cT0 n M σK σB + cT1 n σK σB * ε / δ := by
    unfold cT0 cT1
    rw [hX]
    ring
  linarith [hpart1, hpart2]

end KAM.Sharp

end
