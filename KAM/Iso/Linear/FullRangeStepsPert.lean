/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.FullRange

/-!
# Part 1 step exports: perturbation of the frame (graph gap GAP-I1b)

Literal exports of the proof-step nodes of `bpI:p1:perturbation-noA5` (`pt-small`, `pt-domain`,
`pt-frame`, `pt-torsion`) under the source setting `SettingSrc` (`τ ≥ 0`), built from track K's
perturbation helper lemmas. The `σ`'s are free reals: the constants depend on them only through
`𝔪`, unchanged by replacing each `σ` by `max σ 1` (`mSize_max_one`).
-/

public section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Iso.Linear

open KAM KAM.Torus KAM.Apost

variable {n : ℕ} {τ M γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {σK σB σT : ℝ} {r δ β d : ℝ}
  {K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- `bpI:p1:perturbation-noA5`, step `pt-small`: `C_{ΔT} ≥ max {n, C_G, C_{ΔN}}`;
`n d/δ ≤ 𝔪`, `𝔪 C_G d/δ ≤ 1/2`, `C_{ΔN} d/δ ≤ 𝔪²`, `𝔪 C_{ΔT} d/δ² ≤ 1/2`. -/
theorem step_pt_small (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hd : ∀ θ ∈ complexStrip n r, ‖K' θ - K θ‖ ≤ d)
    (hsmall : 2 * mSize M σK σB σT * C_DT n M σK σB σT * d / δ ^ 2 ≤ 1) :
    max (n : ℝ) (max (C_G n M σK σB σT) (C_DN n M σK σB σT)) ≤ C_DT n M σK σB σT ∧
    (n : ℝ) * d / δ ≤ mSize M σK σB σT ∧
    mSize M σK σB σT * C_G n M σK σB σT * d / δ ≤ 1 / 2 ∧
    C_DN n M σK σB σT * d / δ ≤ mSize M σK σB σT ^ 2 ∧
    mSize M σK σB σT * C_DT n M σK σB σT * d / δ ^ 2 ≤ 1 / 2 := by
  have hP := (hS.setting (σK := max σK 1) (σB := max σB 1) (σT := max σT 1) (by positivity)
    (by positivity) (by positivity)).toStanding.toParams
  have h0 : (0 : Fin n → ℂ) ∈ complexStrip n r := fun i => by simpa using hr
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd 0 h0)
  have hsmall' : 2 * mSize M (max σK 1) (max σB 1) (max σT 1) *
      C_DT n M (max σK 1) (max σB 1) (max σT 1) * d / δ ^ 2 ≤ 1 := by
    simpa only [C_DT, C_DX, C_DN, C_B, C_G, C_X, Theta, mSize_max_one] using hsmall
  have h := perturbation_small hP hδ hδ1 hd0 hsmall'
  have h1 := n_le_C_DT hP
  have h2 := C_G_le_C_DT hP
  have h3 := C_DN_le_C_DT hP
  simp only [C_DT, C_DX, C_DN, C_B, C_G, C_X, Theta, mSize_max_one] at h h1 h2 h3 ⊢
  exact ⟨max_le h1 (max_le h2 h3), h⟩

/-- `bpI:p1:perturbation-noA5`, step `pt-domain`: `B_{β-d}(K̃(θ)) ⊆ B_β(K(θ)) ⊆ D` and
`|Ã - A| ≤ M d ≤ 𝔪 d` on `T_r`. -/
theorem step_pt_domain (hS : SettingSrc n τ M D H ω γ)
    (hball : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ D)
    (hd : ∀ θ ∈ complexStrip n r, ‖K' θ - K θ‖ ≤ d) (hdβ : d < β) :
    ∀ θ ∈ complexStrip n r, Metric.ball (K' θ) (β - d) ⊆ Metric.ball (K θ) β ∧
      Metric.ball (K θ) β ⊆ D ∧ ‖linMat H K' θ - linMat H K θ‖ ≤ M * d ∧
      M * d ≤ mSize M σK σB σT * d := by
  intro θ hθ
  have hSt := (hS.setting one_pos one_pos one_pos).toStanding
  have hdθ := hd θ hθ
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hdθ
  refine ⟨Metric.ball_subset_ball' ?_, hball θ hθ, ?_, mul_le_mul_of_nonneg_right M_le_mSize hd0⟩
  · rw [dist_eq_norm]
    linarith
  · have h1 := (ham_mvt hSt (K θ) (K' θ - K θ) β (hball θ hθ) (lt_of_le_of_lt hdθ hdβ)).1
    rw [add_sub_cancel] at h1
    have heq : linMat H K' θ - linMat H K θ =
        sqMat (fderiv ℂ (hamiltonianVectorFieldℂ H) (K' θ) -
          fderiv ℂ (hamiltonianVectorFieldℂ H) (K θ)) :=
      (PerturbationAux.sqMat_sub _ _).symm
    rw [heq, norm_sqMat]
    exact h1.trans (mul_le_mul_of_nonneg_left hdθ hS.M_pos.le)

/-- `bpI:p1:perturbation-noA5`, step `pt-frame`: on `T_{r-δ}`, `|L̃ - L| ≤ n d/δ`,
`|(L̃ - L)ᵀ| ≤ 2n d/δ`, `|L̃| ≤ 2𝔪`, `|L̃ᵀ| ≤ 4n𝔪`; `G̃` is invertible, `|B̃| ≤ 2𝔪`,
`|B̃ - B| ≤ C_B d/δ`. -/
theorem step_pt_frame (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hDK : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ σK)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB)
    (hK' : DifferentiableOn ℂ K' (complexStrip n r)) (hd : ∀ θ ∈ complexStrip n r, ‖K' θ - K θ‖ ≤ d)
    (hsmall : 2 * mSize M σK σB σT * C_DT n M σK σB σT * d / δ ^ 2 ≤ 1) :
    ∀ θ ∈ complexStrip n (r - δ),
      ‖tangentMat K' θ - tangentMat K θ‖ ≤ n * d / δ ∧
      ‖(tangentMat K' θ - tangentMat K θ)ᵀ‖ ≤ 2 * n * d / δ ∧
      ‖tangentMat K' θ‖ ≤ 2 * mSize M σK σB σT ∧
      ‖(tangentMat K' θ)ᵀ‖ ≤ 4 * n * mSize M σK σB σT ∧
      IsUnit (gramMatrix K' θ).det ∧ ‖(gramMatrix K' θ)⁻¹‖ ≤ 2 * mSize M σK σB σT ∧
      ‖(gramMatrix K' θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤ C_B n M σK σB σT * d / δ := by
  have hP := (hS.setting (σK := max σK 1) (σB := max σB 1) (σT := max σT 1) (by positivity)
    (by positivity) (by positivity)).toStanding.toParams
  have h0 : (0 : Fin n → ℂ) ∈ complexStrip n r := fun i => by simpa using hr
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd 0 h0)
  have hs := (step_pt_small (σK := σK) (σB := σB) (σT := σT) hS hr hδ hδ1 hd hsmall).2.1
  have hsmall' : 2 * mSize M (max σK 1) (max σB 1) (max σT 1) *
      C_DT n M (max σK 1) (max σB 1) (max σT 1) * d / δ ^ 2 ≤ 1 := by
    simpa only [C_DT, C_DX, C_DN, C_B, C_G, C_X, Theta, mSize_max_one] using hsmall
  have hDK' : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ max σK 1 := fun θ hθ =>
    (hDK θ hθ).trans (le_max_left _ _)
  have hG' : ∀ θ ∈ complexStrip n r,
      IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ max σB 1 := fun θ hθ =>
    ⟨(hG θ hθ).1, (hG θ hθ).2.trans (le_max_left _ _)⟩
  obtain ⟨hb, hc, -⟩ := PerturbationAux.frame_items hP hδ hδ1 hd0 hK hDK' hG' hK' hd hsmall'
  have hXt := PerturbationAux.norm_transpose_tangentMat_sub_le hK hK' hd hδ
  intro θ hθ
  have hθr : θ ∈ complexStrip n r := PerturbationAux.complexStrip_mono (by linarith) hθ
  have hs' : (n : ℝ) * d / δ ≤ mSize M (max σK 1) (max σB 1) (max σT 1) := by
    rwa [mSize_max_one]
  have h4 := PerturbationAux.norm_transpose_tangentMat_le_four hP (hDK' θ hθr) (hXt θ hθ) hs'
  rw [mSize_max_one] at h4
  have hΔ : ‖tangentMat K' θ - tangentMat K θ‖ ≤ n * d / δ := by
    rw [PerturbationAux.norm_tangentMat_sub]
    exact hb θ hθ
  have hL : ‖tangentMat K' θ‖ ≤ 2 * mSize M σK σB σT := by
    have hσ : ‖tangentMat K θ‖ ≤ mSize M σK σB σT := by
      rw [FrameAux.norm_tangentMat]
      exact (hDK θ hθr).trans σK_le_mSize
    calc ‖tangentMat K' θ‖
        = ‖tangentMat K θ + (tangentMat K' θ - tangentMat K θ)‖ := by rw [add_sub_cancel]
      _ ≤ ‖tangentMat K θ‖ + ‖tangentMat K' θ - tangentMat K θ‖ := norm_add_le _ _
      _ ≤ 2 * mSize M σK σB σT := by linarith
  exact ⟨hΔ, hXt θ hθ, hL, h4, (hc θ hθ).1, by simpa only [mSize_max_one] using (hc θ hθ).2.1, by
    simpa only [C_B, C_G, mSize_max_one] using (hc θ hθ).2.2⟩

/-- `bpI:p1:perturbation-noA5`, step `pt-torsion`: on `T_{r-δ}`, `|Ñ - N| ≤ C_{ΔN} d/δ`,
`|Ñ| ≤ 2𝔪²`, `|Ñᵀ| ≤ 4n𝔪²`; on `T_{r-2δ}`, `|X̃_Ñ - X_N| ≤ C_{ΔX} d/δ²` and
`|T̃ - T| ≤ C_{ΔT} d/δ²`. -/
theorem step_pt_torsion (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ‖ω‖ ≤ Theta n M σK σB σT) (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hball : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ D)
    (hDK : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ σK)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB)
    (hK' : DifferentiableOn ℂ K' (complexStrip n r)) (hd : ∀ θ ∈ complexStrip n r, ‖K' θ - K θ‖ ≤ d)
    (hdβ : d < β) (hsmall : 2 * mSize M σK σB σT * C_DT n M σK σB σT * d / δ ^ 2 ≤ 1) :
    (∀ θ ∈ complexStrip n (r - δ), ‖normalMat K' θ - normalMat K θ‖ ≤ C_DN n M σK σB σT * d / δ ∧
      ‖normalMat K' θ‖ ≤ 2 * mSize M σK σB σT ^ 2 ∧
      ‖(normalMat K' θ)ᵀ‖ ≤ 4 * n * mSize M σK σB σT ^ 2) ∧
    ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖normalFieldMat H K' ω θ - normalFieldMat H K ω θ‖ ≤ C_DX n M σK σB σT * d / δ ^ 2 ∧
      ‖torsion H K' ω θ - torsion H K ω θ‖ ≤ C_DT n M σK σB σT * d / δ ^ 2 := by
  have hSt := (hS.setting (σK := max σK 1) (σB := max σB 1) (σT := max σT 1) (by positivity)
    (by positivity) (by positivity)).toStanding
  have hP := hSt.toParams
  have h0 : (0 : Fin n → ℂ) ∈ complexStrip n r := fun i => by simpa using hr
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd 0 h0)
  have hβ : 0 < β := lt_of_le_of_lt hd0 hdβ
  have hsmall' : 2 * mSize M (max σK 1) (max σB 1) (max σT 1) *
      C_DT n M (max σK 1) (max σB 1) (max σT 1) * d / δ ^ 2 ≤ 1 := by
    simpa only [C_DT, C_DX, C_DN, C_B, C_G, C_X, Theta, mSize_max_one] using hsmall
  have hω' : ‖ω‖ ≤ Theta n M (max σK 1) (max σB 1) (max σT 1) := by
    simpa only [Theta, mSize_max_one] using hω
  have hDK' : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ max σK 1 := fun θ hθ =>
    (hDK θ hθ).trans (le_max_left _ _)
  have hG' : ∀ θ ∈ complexStrip n r,
      IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ max σB 1 := fun θ hθ =>
    ⟨(hG θ hθ).1, (hG θ hθ).2.trans (le_max_left _ _)⟩
  have hsub : complexStrip n (r - δ) ⊆ complexStrip n r :=
    PerturbationAux.complexStrip_mono (by linarith)
  obtain ⟨-, hc, hdN⟩ := PerturbationAux.frame_items hP hδ hδ1 hd0 hK hDK' hG' hK' hd hsmall'
  have hG1 : ∀ θ ∈ complexStrip n (r - δ), IsUnit (gramMatrix K' θ).det :=
    fun θ hθ => (hc θ hθ).1
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ D := fun θ hθ =>
    hball θ hθ (Metric.mem_ball_self hβ)
  have hAb : ∀ θ ∈ complexStrip n r, ‖linMat H K θ‖ ≤ mSize M (max σK 1) (max σB 1) (max σT 1) :=
    fun θ hθ => FrameAux.norm_linMat_le hSt (hK𝔅 θ hθ)
  have hXX := PerturbationAux.norm_normalField_sub_le_strip hSt hδ hδ1 hd0 hω' hK hball
    (fun θ hθ => (hG θ hθ).1) hK' hd hdβ hG1 hdN hAb
  have he := PerturbationAux.norm_torsion_sub_le hSt hδ hδ1 hω' hK hK𝔅 hDK' hG' hK' hG1 hdN hXX
  refine ⟨fun θ hθ => ⟨?_, ?_, ?_⟩, fun θ hθ => ⟨?_, ?_⟩⟩
  · simpa only [C_DN, C_B, C_G, mSize_max_one] using (hdN θ hθ).1
  · simpa only [mSize_max_one] using (hdN θ hθ).2
  · have h2 : ‖normalMat K' θ‖ ≤ 2 * mSize M σK σB σT ^ 2 := by
      simpa only [mSize_max_one] using (hdN θ hθ).2
    calc ‖(normalMat K' θ)ᵀ‖ ≤ 2 * n * ‖normalMat K' θ‖ := FrameAux.norm_transpose_le_two_mul _
      _ ≤ 2 * n * (2 * mSize M σK σB σT ^ 2) := by gcongr
      _ = 4 * n * mSize M σK σB σT ^ 2 := by ring
  · simpa only [C_DX, C_DN, C_B, C_G, Theta, mSize_max_one] using hXX θ hθ
  · simpa only [C_DT, C_DX, C_DN, C_B, C_G, C_X, Theta, mSize_max_one] using he θ hθ

end KAM.Iso.Linear
