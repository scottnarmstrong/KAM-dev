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

end KAM.Iso.Linear
