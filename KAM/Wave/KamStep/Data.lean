/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.LatticeBN
public import KAM.Wave.Homological.Schur
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Step data: the constants and the smallness consequences (`bpW:w5:data`)

Unmodified step: `t = 2τ+4`, `c_F = 9 C₁ b_W(τ)`, `c₀ = 16 c_F`, `M_F = c_F ε/(α σ^{t-1})`,
`C₂ = 896 + 168 c_F`, with `C₁ = 7 + 10 K_S`. Modified (preparatory) step: `t♮ = 2τ+5`,
`c♮_F = 9 C₁ b♮(τ)`, `c♮₀ = 16 c♮_F`, `C♮₂ = 896 + 168 c♮_F`.

Results: the constants are positive; the smallness condition `ε ≤ ασ^tη²/c₀` gives
`M_F ≤ σ η²/16`, hence `M_F ≤ σ/1024`, `M_F/(σ/4) ≤ 1/256 ≤ 1/64`, `16 M_F/σ ≤ η²`
(`bpW:w5:flow`, step `f-margin`); the solve bound `3C₁B_σ/α · 3ε ≤ M_F`
(`bpW:w5:solve`, step `s-out`), in both cases; and the arithmetic of the step estimate
(`bpW:w5:step`, steps `st-1`, `st-2`).
-/

@[expose] public section

namespace KAM.Wave

/-- `C₁ = 7 + 10 K_S` (W4 Lemma 1). -/
noncomputable def stepC1 : ℝ := 7 + 10 * homKS

/-- The exponent `t = 2τ + 4`. -/
def stepExpT (τ : ℝ) : ℝ := 2 * τ + 4

/-- `c_F = 9 C₁ b_W(τ)`. -/
noncomputable def stepCF (τ : ℝ) : ℝ := 9 * stepC1 * waveBWconst τ

/-- `c₀ = 16 c_F`. -/
noncomputable def stepC0 (τ : ℝ) : ℝ := 16 * stepCF τ

/-- `C₂ = 896 + 168 c_F`. -/
noncomputable def stepC2 (τ : ℝ) : ℝ := 896 + 168 * stepCF τ

/-- The modified exponent `t♮ = 2τ + 5`. -/
def stepTn (τ : ℝ) : ℝ := 2 * τ + 5

/-- `c♮_F = 9 C₁ b♮(τ)`. -/
noncomputable def stepCFn (τ : ℝ) : ℝ := 9 * stepC1 * waveBNconst τ

/-- `c♮₀ = 16 c♮_F`. -/
noncomputable def stepC0n (τ : ℝ) : ℝ := 16 * stepCFn τ

/-- `C♮₂ = 896 + 168 c♮_F`. -/
noncomputable def stepC2n (τ : ℝ) : ℝ := 896 + 168 * stepCFn τ

/-- `M_F = c ε /(α σ^{t-1})` for a constant `c ∈ {c_F, c♮_F}` and exponent `t`. -/
noncomputable def stepMF (c t α σ ε : ℝ) : ℝ := c * ε / (α * σ ^ (t - 1))

theorem stepC1_pos : 0 < stepC1 := by
  have := one_le_homKS; unfold stepC1; linarith

theorem waveC_pos {q : ℝ} (hq : 0 ≤ q) : 0 < waveC q := by
  unfold waveC
  split_ifs
  · positivity
  · have := Real.pi_pos
    have h : 0 < q + 1 := by linarith
    positivity

theorem waveBWconst_pos {τ : ℝ} (hτ : 0 ≤ τ) : 0 < waveBWconst τ := by
  unfold waveBWconst
  have := waveC_pos (q := 0) le_rfl
  have := waveC_pos (q := 1) zero_le_one
  have := waveC_pos (q := 2 * τ) (by linarith)
  have := waveC_pos (q := 2 * τ + 1) (by linarith)
  linarith

theorem waveBNconst_pos {τ : ℝ} (hτ : 0 ≤ τ) : 0 < waveBNconst τ := by
  unfold waveBNconst
  have := waveC_pos (q := 0) le_rfl
  have := waveC_pos (q := 2) (by norm_num)
  have := waveC_pos (q := 2 * τ) (by linarith)
  have := waveC_pos (q := 2 * τ + 2) (by linarith)
  linarith

theorem stepCF_pos {τ : ℝ} (hτ : 0 ≤ τ) : 0 < stepCF τ := by
  unfold stepCF; have := stepC1_pos; have := waveBWconst_pos hτ; positivity

theorem stepCFn_pos {τ : ℝ} (hτ : 0 ≤ τ) : 0 < stepCFn τ := by
  unfold stepCFn; have := stepC1_pos; have := waveBNconst_pos hτ; positivity

theorem stepC0_pos {τ : ℝ} (hτ : 0 ≤ τ) : 0 < stepC0 τ := by
  unfold stepC0; have := stepCF_pos hτ; positivity

theorem stepC0n_pos {τ : ℝ} (hτ : 0 ≤ τ) : 0 < stepC0n τ := by
  unfold stepC0n; have := stepCFn_pos hτ; positivity

/-- **The smallness condition** `ε ≤ α σ^t η²/c₀` (with `c₀ = 16 c`) gives `M_F ≤ σ η²/16`. -/
theorem stepMF_le_of_small {c t α σ η ε : ℝ} (hc : 0 < c) (hα : 0 < α) (hσ : 0 < σ)
    (hε : ε ≤ α * σ ^ t * η ^ 2 / (16 * c)) :
    stepMF c t α σ ε ≤ σ * η ^ 2 / 16 := by
  unfold stepMF
  have hpow : 0 < σ ^ (t - 1) := Real.rpow_pos_of_pos hσ _
  have hσt : σ ^ t = σ * σ ^ (t - 1) := by
    rw [show t = 1 + (t - 1) by ring, Real.rpow_add hσ, Real.rpow_one]; ring_nf
  rw [div_le_iff₀ (by positivity)]
  have h1 : c * ε ≤ c * (α * σ ^ t * η ^ 2 / (16 * c)) := mul_le_mul_of_nonneg_left hε hc.le
  have h2 : c * (α * σ ^ t * η ^ 2 / (16 * c)) = α * σ ^ t * η ^ 2 / 16 := by field_simp
  rw [h2, hσt] at h1
  calc c * ε ≤ α * (σ * σ ^ (t - 1)) * η ^ 2 / 16 := h1
    _ = σ * η ^ 2 / 16 * (α * σ ^ (t - 1)) := by ring

/-- Consequences for the flow margins (`bpW:w5:flow`, step `f-margin`): with `0 < η ≤ 1/8`,
`δ = σ/4`: `M_F ≤ σ/1024`, `M_F/δ ≤ 1/256` and `16 M_F/σ ≤ η²`. -/
theorem stepMF_margins {M σ η : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hη8 : η ≤ 1 / 8)
    (hM : M ≤ σ * η ^ 2 / 16) :
    M ≤ σ / 1024 ∧ M / (σ / 4) ≤ 1 / 256 ∧ 16 * M / σ ≤ η ^ 2 := by
  have hη2 : η ^ 2 ≤ 1 / 64 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ hσ]; nlinarith

/-- **Solve bound** (`bpW:w5:solve`, step `s-out`), unmodified: for `0 < σ ≤ 1`,
`(3 C₁ B^W_σ/α) (3 ε) ≤ M_F`. -/
theorem stepSolve_bound {τ α σ ε : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hε : 0 ≤ ε) :
    3 * stepC1 * waveBW τ σ / α * (3 * ε) ≤ stepMF (stepCF τ) (stepExpT τ) α σ ε := by
  have hB := waveBW_le hτ hσ hσ1
  have hC1 := stepC1_pos
  unfold stepMF stepCF stepExpT
  have e : (2 * τ + 4 - 1) = 2 * τ + 3 := by ring
  rw [e]
  have hpow : 0 < σ ^ (2 * τ + 3) := Real.rpow_pos_of_pos hσ _
  calc 3 * stepC1 * waveBW τ σ / α * (3 * ε) ≤
        3 * stepC1 * (waveBWconst τ / σ ^ (2 * τ + 3)) / α * (3 * ε) := by gcongr
    _ = 9 * stepC1 * waveBWconst τ * ε / (α * σ ^ (2 * τ + 3)) := by field_simp; ring

/-- **Solve bound, modified** (`bpW:w5:w4-modified` (iii) with `bpW:w5:solve`):
`(3 C₁ B^♮_σ/α)(3ε) ≤ c♮_F ε/(α σ^{2τ+4})`, i.e. `M_F` with `t♮ = 2τ+5`. -/
theorem stepSolve_bound_mod {τ α σ ε : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hε : 0 ≤ ε) :
    3 * stepC1 * waveBN τ σ / α * (3 * ε) ≤ stepMF (stepCFn τ) (stepTn τ) α σ ε := by
  have hB := waveBN_le hτ hσ hσ1
  have hC1 := stepC1_pos
  unfold stepMF stepCFn stepTn
  have e : (2 * τ + 5 - 1) = 2 * τ + 4 := by ring
  rw [e]
  have hpow : 0 < σ ^ (2 * τ + 4) := Real.rpow_pos_of_pos hσ _
  calc 3 * stepC1 * waveBN τ σ / α * (3 * ε) ≤
        3 * stepC1 * (waveBNconst τ / σ ^ (2 * τ + 4)) / α * (3 * ε) := by gcongr
    _ = 9 * stepC1 * waveBNconst τ * ε / (α * σ ^ (2 * τ + 4)) := by field_simp; ring

/-- **Arithmetic of the step estimate** (`bpW:w5:step`, steps `st-1`, `st-2`): with
`M_F = c ε/(α σ^{t-1})` (`c = c_F` or `c♮_F`),
`896 η ε + 7 · 24 ε M_F/(σ η²) ≤ C₂ (ε²/(α σ^t η²) + η ε)`, `C₂ = 896 + 168 c`. -/
theorem stepEstimate_arith {c t α σ η ε : ℝ} (hα : 0 < α) (hσ : 0 < σ) (hη : 0 < η)
    (hc : 0 ≤ c) (hε : 0 ≤ ε) :
    896 * η * ε + 7 * 24 * ε * stepMF c t α σ ε / (σ * η ^ 2) ≤
      (896 + 168 * c) * (ε ^ 2 / (α * σ ^ t * η ^ 2) + η * ε) := by
  have hpow : 0 < σ ^ (t - 1) := Real.rpow_pos_of_pos hσ _
  have hσt : σ ^ t = σ * σ ^ (t - 1) := by
    rw [show t = 1 + (t - 1) by ring, Real.rpow_add hσ, Real.rpow_one]; ring_nf
  unfold stepMF
  have e : 7 * 24 * ε * (c * ε / (α * σ ^ (t - 1))) / (σ * η ^ 2) =
      168 * c * (ε ^ 2 / (α * σ ^ t * η ^ 2)) := by
    rw [hσt]; field_simp; ring
  rw [e]
  have h1 : 0 ≤ ε ^ 2 / (α * σ ^ t * η ^ 2) := by
    rw [hσt]; positivity
  have h2 : 0 ≤ η * ε := by positivity
  nlinarith [mul_nonneg hc h1, mul_nonneg hc h2]

end KAM.Wave
