/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.Constants
public import KAM.Wave.Iteration.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# W6: the Lipschitz frequencies, conditional form (blueprint `bpW:w6:freq-lip`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:freq-lip` (milestone W6), steps `fl-size`, `fl-lip`.

`w6IsFreqPair_of_bounds` is a **conditional helper** (it is not the label `freq-lip`, which is
about the outputs of the wave iteration and needs W5's step through `bpW:w6:prep-step` (ii) and
`bpW:w6:convergence` (ii)). It is the arithmetic of the two steps: given on a Borel `D ⊆ Π`
* frequencies `ω₀ = ω⁰ + ω̂`, `Ω₀ = Ω⁰ + Ω̂` with `|ω̂| ≤ 6πε`, `λ|ω̂|^L ≤ 6πε`,
  `J |Ω̂_J| ≤ 3ε`, `J λ |Ω̂_J|^L ≤ 3ε` (`λ = α/M`), and
* frequencies `(ω, Ω)` with `|ω - ω₀| ≤ 8πε₀`, `λ₀ |ω - ω₀|^L ≤ 64πε₀`,
  `J^{1/2}|Ω_J - Ω_{0,J}| ≤ 4ε₀`, `λ₀ J^{1/2}|Ω_J - Ω_{0,J}|^L ≤ 16ε₀` (`λ₀ = α̌/M₀ = α̌/(2M)`),

with `0 < α ≤ α₀`, `0 ≤ ε ≤ γα`, `0 ≤ ε₀ ≤ γ₁α̌`, the pair `(ω, Ω)` satisfies (H1)–(H2) of W7 on `D`
with `ε_ω = 6πγα + 8πε₀`, `ε₁ = 3γα`, `ε₂ = 4ε₀`, `θ = 425(1+M) max(γ, γ₁)`. Lipschitz seminorms are
written as pointwise inequalities; `J = normLab j` is the Dirichlet label.
`w6AdmissibleFamilyOfPairs` packages such pairs with the thresholds `K_ν` of `bpW:w6:sequences`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

theorem w6_le_div_mul_of_mul_le {L x c d : ℝ} (hL : 0 < L) (h : L * x ≤ c * d) :
    x ≤ c / L * d := by
  rw [div_mul_eq_mul_div, le_div_iff₀ hL]; linarith

theorem normLab_inv_le_rpow (j : ℕ) : (normLab j)⁻¹ ≤ normLab j ^ (-(1 / 2 : ℝ)) := by
  have hJ := normLab_ge j
  have hJ0 : 0 < normLab j := by linarith
  rw [Real.rpow_neg hJ0.le]
  apply inv_anti₀ (Real.rpow_pos_of_pos hJ0 _)
  calc normLab j ^ (1 / 2 : ℝ) ≤ normLab j ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ = normLab j := Real.rpow_one _

theorem rpow_half_mul_le {j : ℕ} {x c : ℝ} (h : normLab j ^ (1 / 2 : ℝ) * x ≤ c) :
    x ≤ c * normLab j ^ (-(1 / 2 : ℝ)) := by
  have hJ0 : 0 < normLab j := normLab_pos j
  have hp := Real.rpow_pos_of_pos hJ0 (1 / 2 : ℝ)
  rw [Real.rpow_neg hJ0.le, ← div_eq_mul_inv, le_div_iff₀ hp]; linarith

section

variable {m : ℝ} {hm : 0 < m}

/-- The coefficient of the `ω`-Lipschitz bound: `6πε/λ + 64πε₀/λ₀ ≤ θ`. -/
theorem w6_lipcoef_omega {α ε ε₀ : ℝ} (hα : 0 < α) (hα0 : α ≤ measAlpha0 m hm)
    (hεγ : ε ≤ w6Gamma m hm * α) (hε₀γ : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) :
    6 * π * ε / (α / w6M m hm) + 64 * π * ε₀ / (alphaCheck α / w6M0 m hm) ≤ w6Theta m hm := by
  obtain ⟨hc0, -, -, -, -, -⟩ := alpha_facts m hm hα hα0
  have hM := w6M_pos m hm
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_le_four
  set g := max (w6Gamma m hm) (w6Gamma1 m hm) with hg
  have hg1 : w6Gamma m hm ≤ g := le_max_left _ _
  have hg2 : w6Gamma1 m hm ≤ g := le_max_right _ _
  have e1 : 6 * π * ε / (α / w6M m hm) = 6 * π * w6M m hm * (ε / α) := by field_simp
  have e2 : 64 * π * ε₀ / (alphaCheck α / w6M0 m hm) =
      128 * π * w6M m hm * (ε₀ / alphaCheck α) := by
    unfold w6M0; field_simp; ring
  have b1 : ε / α ≤ g := by rw [div_le_iff₀ hα]; nlinarith
  have b2 : ε₀ / alphaCheck α ≤ g := by rw [div_le_iff₀ hc0]; nlinarith
  rw [e1, e2]
  have hg0 : 0 ≤ g := le_trans (w6Gamma_pos m hm).le hg1
  calc 6 * π * w6M m hm * (ε / α) + 128 * π * w6M m hm * (ε₀ / alphaCheck α)
      ≤ 6 * π * w6M m hm * g + 128 * π * w6M m hm * g := by gcongr
    _ = 134 * π * (w6M m hm * g) := by ring
    _ ≤ 425 * (w6M m hm * g) := by
        have : 0 ≤ w6M m hm * g := by positivity
        have : 134 * π ≤ 425 := by nlinarith [Real.pi_lt_d2]
        nlinarith
    _ ≤ w6Theta m hm := by unfold w6Theta; rw [← hg]; nlinarith

/-- The coefficient of the `Ω`-Lipschitz bound: `3ε/λ + 16ε₀/λ₀ ≤ θ`. -/
theorem w6_lipcoef_Omega {α ε ε₀ : ℝ} (hα : 0 < α) (hα0 : α ≤ measAlpha0 m hm) (hε : 0 ≤ ε)
    (hεγ : ε ≤ w6Gamma m hm * α) (hε₀ : 0 ≤ ε₀) (hε₀γ : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) :
    3 * ε / (α / w6M m hm) + 16 * ε₀ / (alphaCheck α / w6M0 m hm) ≤ w6Theta m hm := by
  have h := w6_lipcoef_omega hα hα0 hεγ hε₀γ
  obtain ⟨hc0, -, -, -, -, -⟩ := alpha_facts m hm hα hα0
  have hM := w6M_pos m hm
  have hM0 := w6M0_pos m hm
  have hπ := Real.pi_gt_three
  have h1 : 3 * ε / (α / w6M m hm) ≤ 6 * π * ε / (α / w6M m hm) := by
    apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
  have h2 : 16 * ε₀ / (alphaCheck α / w6M0 m hm) ≤ 64 * π * ε₀ / (alphaCheck α / w6M0 m hm) := by
    apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
  linarith

/-- **Lipschitz frequencies, conditional helper** (blueprint `bpW:w6:freq-lip`, steps `fl-size`,
`fl-lip`): the shift and drift bounds give (H1)–(H2) with the constants of `bpW:w6:freq-lip`. -/
theorem w6IsFreqPair_of_bounds {Pi D : Set (Fin 2 → ℝ)} {α ε ε₀ : ℝ}
    (hDm : MeasurableSet D) (hDsub : D ⊆ Pi) (hα : 0 < α) (hα0 : α ≤ measAlpha0 m hm)
    (hε : 0 ≤ ε) (hεγ : ε ≤ w6Gamma m hm * α) (hε₀ : 0 ≤ ε₀)
    (hε₀γ : ε₀ ≤ w6Gamma1 m hm * alphaCheck α)
    {ωh ω0 ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ωh Ω0 Ω : (Fin 2 → ℝ) → ℕ → ℝ}
    (hω0 : ∀ ξ ∈ D, ω0 ξ = omegaTan m hm ξ + ωh ξ)
    (hΩ0 : ∀ ξ ∈ D, ∀ j, Ω0 ξ j = omegaNor m hm ξ j + Ωh ξ j)
    (hωh : ∀ ξ ∈ D, ‖ωh ξ‖ ≤ 6 * π * ε)
    (hωhL : ∀ ξ ∈ D, ∀ ζ ∈ D, α / w6M m hm * ‖ωh ξ - ωh ζ‖ ≤ 6 * π * ε * ‖ξ - ζ‖)
    (hΩh : ∀ ξ ∈ D, ∀ j, normLab j * |Ωh ξ j| ≤ 3 * ε)
    (hΩhL : ∀ ξ ∈ D, ∀ ζ ∈ D, ∀ j,
      α / w6M m hm * (normLab j * |Ωh ξ j - Ωh ζ j|) ≤ 3 * ε * ‖ξ - ζ‖)
    (hω : ∀ ξ ∈ D, ‖ω ξ - ω0 ξ‖ ≤ 8 * π * ε₀)
    (hωL : ∀ ξ ∈ D, ∀ ζ ∈ D, alphaCheck α / w6M0 m hm * ‖(ω ξ - ω0 ξ) - (ω ζ - ω0 ζ)‖ ≤
      64 * π * ε₀ * ‖ξ - ζ‖)
    (hΩ : ∀ ξ ∈ D, ∀ j, normLab j ^ (1 / 2 : ℝ) * |Ω ξ j - Ω0 ξ j| ≤ 4 * ε₀)
    (hΩL : ∀ ξ ∈ D, ∀ ζ ∈ D, ∀ j, alphaCheck α / w6M0 m hm *
      (normLab j ^ (1 / 2 : ℝ) * |(Ω ξ j - Ω0 ξ j) - (Ω ζ j - Ω0 ζ j)|) ≤ 16 * ε₀ * ‖ξ - ζ‖) :
    IsFreqPair m hm Pi α D ω Ω (6 * π * w6Gamma m hm * α + 8 * π * ε₀) (3 * w6Gamma m hm * α)
      (4 * ε₀) (w6Theta m hm) := by
  obtain ⟨hεω, hε1, hε2, hθ⟩ := w6freqLip_consts (m := m) (hm := hm) hα hα0 hε₀ hε₀γ
  obtain ⟨hc0, -, -, -, -, -⟩ := alpha_facts m hm hα hα0
  have hM := w6M_pos m hm
  have hM0 := w6M0_pos m hm
  have hlam : 0 < α / w6M m hm := div_pos hα hM
  have hlam0 : 0 < alphaCheck α / w6M0 m hm := div_pos hc0 hM0
  have hπ := Real.pi_pos
  have hcω := w6_lipcoef_omega (m := m) (hm := hm) hα hα0 hεγ hε₀γ
  have hcΩ := w6_lipcoef_Omega (m := m) (hm := hm) hα hα0 hε hεγ hε₀ hε₀γ
  have hgα : 6 * π * ε ≤ 6 * π * w6Gamma m hm * α := by
    have := mul_le_mul_of_nonneg_left hεγ (by positivity : (0 : ℝ) ≤ 6 * π); linarith
  refine ⟨hDm, hDsub, hεω, hε1, hε2, hθ, ?_, ?_, ?_, ?_⟩
  · -- (H1), sup
    intro ξ hξ
    have e : ω ξ - omegaTan m hm ξ = (ω ξ - ω0 ξ) + ωh ξ := by rw [hω0 ξ hξ]; abel
    rw [e]
    calc ‖(ω ξ - ω0 ξ) + ωh ξ‖ ≤ ‖ω ξ - ω0 ξ‖ + ‖ωh ξ‖ := norm_add_le _ _
      _ ≤ 8 * π * ε₀ + 6 * π * ε := add_le_add (hω ξ hξ) (hωh ξ hξ)
      _ ≤ 6 * π * w6Gamma m hm * α + 8 * π * ε₀ := by linarith
  · -- (H1), Lipschitz
    intro ξ hξ ζ hζ
    have e : (ω ξ - omegaTan m hm ξ) - (ω ζ - omegaTan m hm ζ) =
        ((ω ξ - ω0 ξ) - (ω ζ - ω0 ζ)) + (ωh ξ - ωh ζ) := by
      rw [hω0 ξ hξ, hω0 ζ hζ]; abel
    rw [e]
    have h1 := w6_le_div_mul_of_mul_le hlam0 (hωL ξ hξ ζ hζ)
    have h2 := w6_le_div_mul_of_mul_le hlam (hωhL ξ hξ ζ hζ)
    have hn := norm_nonneg (ξ - ζ)
    calc _ ≤ ‖(ω ξ - ω0 ξ) - (ω ζ - ω0 ζ)‖ + ‖ωh ξ - ωh ζ‖ := norm_add_le _ _
      _ ≤ 64 * π * ε₀ / (alphaCheck α / w6M0 m hm) * ‖ξ - ζ‖ +
          6 * π * ε / (α / w6M m hm) * ‖ξ - ζ‖ := add_le_add h1 h2
      _ = (6 * π * ε / (α / w6M m hm) + 64 * π * ε₀ / (alphaCheck α / w6M0 m hm)) *
          ‖ξ - ζ‖ := by ring
      _ ≤ w6Theta m hm * ‖ξ - ζ‖ := mul_le_mul_of_nonneg_right hcω hn
  · -- (H2), sup
    intro ξ hξ j
    have hJ0 := normLab_pos j
    have e : Ω ξ j - omegaNor m hm ξ j = (Ω ξ j - Ω0 ξ j) + Ωh ξ j := by rw [hΩ0 ξ hξ j]; ring
    rw [e]
    have h1 := rpow_half_mul_le (hΩ ξ hξ j)
    have h2 : |Ωh ξ j| ≤ 3 * ε * (normLab j)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hJ0]; linarith [hΩh ξ hξ j]
    have h3 : 3 * ε * (normLab j)⁻¹ ≤ 3 * w6Gamma m hm * α * (normLab j)⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hJ0.le)
    calc |(Ω ξ j - Ω0 ξ j) + Ωh ξ j| ≤ |Ω ξ j - Ω0 ξ j| + |Ωh ξ j| := abs_add_le _ _
      _ ≤ 4 * ε₀ * normLab j ^ (-(1 / 2 : ℝ)) + 3 * w6Gamma m hm * α * (normLab j)⁻¹ := by
          linarith
      _ = _ := by ring
  · -- (H2), Lipschitz
    intro ξ hξ ζ hζ j
    have hJ0 := normLab_pos j
    have hJr := normLab_inv_le_rpow j
    have hJp : 0 ≤ normLab j ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hJ0.le _
    have hn := norm_nonneg (ξ - ζ)
    have e : (Ω ξ j - omegaNor m hm ξ j) - (Ω ζ j - omegaNor m hm ζ j) =
        ((Ω ξ j - Ω0 ξ j) - (Ω ζ j - Ω0 ζ j)) + (Ωh ξ j - Ωh ζ j) := by
      rw [hΩ0 ξ hξ j, hΩ0 ζ hζ j]; ring
    rw [e]
    -- drift part: `≤ (16ε₀/λ₀) J^{-1/2} |ξ-ζ|`
    have h1 : |(Ω ξ j - Ω0 ξ j) - (Ω ζ j - Ω0 ζ j)| ≤
        16 * ε₀ / (alphaCheck α / w6M0 m hm) * ‖ξ - ζ‖ * normLab j ^ (-(1 / 2 : ℝ)) := by
      apply rpow_half_mul_le
      exact w6_le_div_mul_of_mul_le hlam0 (by linarith [hΩL ξ hξ ζ hζ j])
    -- shift part: `≤ (3ε/λ) J^{-1} |ξ-ζ| ≤ (3ε/λ) J^{-1/2} |ξ-ζ|`
    have h2 : |Ωh ξ j - Ωh ζ j| ≤
        3 * ε / (α / w6M m hm) * ‖ξ - ζ‖ * normLab j ^ (-(1 / 2 : ℝ)) := by
      have h := w6_le_div_mul_of_mul_le hlam (hΩhL ξ hξ ζ hζ j)
      have h' : |Ωh ξ j - Ωh ζ j| ≤ 3 * ε / (α / w6M m hm) * ‖ξ - ζ‖ * (normLab j)⁻¹ := by
        rw [show 3 * ε / (α / w6M m hm) * ‖ξ - ζ‖ * (normLab j)⁻¹ =
          3 * ε / (α / w6M m hm) * ‖ξ - ζ‖ / normLab j by ring, le_div_iff₀ hJ0]; linarith
      refine h'.trans ?_
      have : 0 ≤ 3 * ε / (α / w6M m hm) * ‖ξ - ζ‖ := by positivity
      exact mul_le_mul_of_nonneg_left hJr this
    calc _ ≤ |(Ω ξ j - Ω0 ξ j) - (Ω ζ j - Ω0 ζ j)| + |Ωh ξ j - Ωh ζ j| := abs_add_le _ _
      _ ≤ (3 * ε / (α / w6M m hm) + 16 * ε₀ / (alphaCheck α / w6M0 m hm)) *
          (normLab j ^ (-(1 / 2 : ℝ)) * ‖ξ - ζ‖) := by nlinarith
      _ ≤ w6Theta m hm * (normLab j ^ (-(1 / 2 : ℝ)) * ‖ξ - ζ‖) :=
          mul_le_mul_of_nonneg_right hcΩ (by positivity)
      _ = _ := by ring

/-- An admissible family (W7's `AdmissibleFamily`) from pairs satisfying (H1)–(H2) at every stage,
with the thresholds `K_ν ≥ 2^ν` of `bpW:w6:sequences`. -/
def w6AdmissibleFamilyOfPairs {Pi : Set (Fin 2 → ℝ)} {α : ℝ} (d : W6SeqData) (hd : d.SeqValid)
    (D : ℕ → Set (Fin 2 → ℝ)) (ω : ℕ → (Fin 2 → ℝ) → Fin 2 → ℝ) (Ω : ℕ → (Fin 2 → ℝ) → ℕ → ℝ)
    (εω ε1 ε2 θ : ℝ) (hpair : ∀ ν, IsFreqPair m hm Pi α (D ν) (ω ν) (Ω ν) εω ε1 ε2 θ) :
    AdmissibleFamily m hm Pi α where
  D := D
  ω := ω
  Ω := Ω
  K := d.K
  εω := εω
  ε1 := ε1
  ε2 := ε2
  θ := θ
  pair := hpair
  K_ge := W6SeqData.two_pow_le_K hd

end

end KAM.Wave
