/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.Measure
public import KAM.Wave.Measure.Coords
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# W6: frequency bounds in the limit (`bpW:w6:convergence` (ii), `bpW:w6:final-freq`)

Blueprint labels `bpW:w6:convergence` (step `c-freq`, the limit of the divisor
bound) and `bpW:w6:final-freq` (milestone W6).

* `w6_divisor_limit` (step `c-freq`): if `|⟨k, ω_ν⟩ + ⟨l, Ω_ν⟩| ≥ a_ν ⟨l⟩/A_k` for every `ν`, with
  `a_ν ≥ c`, and `ω_ν → ω_*`, `Ω_{ν,j} → Ω_{*,j}` for every `j`, then
  `|⟨k, ω_*⟩ + ⟨l, Ω_*⟩| ≥ c ⟨l⟩/A_k`. No hypothesis on how the frequencies were obtained.
* `w6FinalFreq_of_limits`: a **hypothesis-taking variant** (not the label `final-freq`, which is
  about the outputs of the wave iteration and needs W5's step): for an admissible family `F` (W7)
  whose `ω_ν` converge on a set `S ⊆ ⋂ D_ν` to `ω_*` and satisfy the stage-wise conditions with
  `l = 0` at levels `a_ν ≥ α̌/2`, the three conclusions of `bpW:w6:final-freq` hold on `S`.
-/

@[expose] public noncomputable section

open Real Filter Topology

namespace KAM.Wave

theorem tendsto_w6ZoneFun {ωs : ℕ → Fin 2 → ℝ} {Ωs : ℕ → ℕ → ℝ} {ω : Fin 2 → ℝ} {Ω : ℕ → ℝ}
    (hω : Tendsto ωs atTop (𝓝 ω)) (hΩ : ∀ j, Tendsto (fun ν => Ωs ν j) atTop (𝓝 (Ω j)))
    (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) :
    Tendsto (fun ν => ∑ i, (k i : ℝ) * ωs ν i + linF l (Ωs ν)) atTop
      (𝓝 (∑ i, (k i : ℝ) * ω i + linF l Ω)) := by
  refine Tendsto.add ?_ ?_
  · exact tendsto_finsetSum _ fun i _ =>
      tendsto_const_nhds.mul ((continuous_apply i).continuousAt.tendsto.comp hω)
  · unfold linF Finsupp.sum
    exact tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul (hΩ j)

/-- **The divisor bound in the limit** (blueprint `bpW:w6:convergence` (ii), step `c-freq`). -/
theorem w6_divisor_limit {ωs : ℕ → Fin 2 → ℝ} {Ωs : ℕ → ℕ → ℝ} {ω : Fin 2 → ℝ} {Ω : ℕ → ℝ}
    {a : ℕ → ℝ} {c : ℝ} (hω : Tendsto ωs atTop (𝓝 ω))
    (hΩ : ∀ j, Tendsto (fun ν => Ωs ν j) atTop (𝓝 (Ω j))) (ha : ∀ ν, c ≤ a ν)
    (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ)
    (hb : ∀ ν, a ν * japL l / kAk k ≤ |∑ i, (k i : ℝ) * ωs ν i + linF l (Ωs ν)|) :
    c * japL l / kAk k ≤ |∑ i, (k i : ℝ) * ω i + linF l Ω| := by
  have hL := (tendsto_w6ZoneFun hω hΩ k l).abs
  refine ge_of_tendsto hL (Eventually.of_forall fun ν => le_trans ?_ (hb ν))
  have hA : 0 < kAk k := lt_of_lt_of_le one_pos (kAk_pos k)
  have hJ : 0 ≤ japL l := le_trans zero_le_one (japL_ge_one l)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (ha ν) hJ) hA.le

/-- **Final frequencies, hypothesis-taking variant** (the conclusions of `bpW:w6:final-freq` for a
limit of an admissible family): if `S ⊆ D_ν` for all `ν`, `ω_ν → ω_*` on `S`, and
`|⟨k, ω_ν⟩| ≥ a_ν/A_k` (`k ≠ 0`) on `S` with `a_ν ≥ α̌/2`, then on `S`:
`|⟨k, ω_*⟩| ≥ α̌/(2A_k)` (`k ≠ 0`), `|ω_* - ω⁰|_∞ ≤ ε_ω`, and `ω_*` is Lipschitz with constant
`N_A + θ`. -/
theorem w6FinalFreq_of_limits (m : ℝ) (hm : 0 < m) {Pi : Set (Fin 2 → ℝ)} {α : ℝ}
    (F : AdmissibleFamily m hm Pi α) {S : Set (Fin 2 → ℝ)} (hS : ∀ ν, S ⊆ F.D ν)
    (ωs : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (hlim : ∀ ξ ∈ S, Tendsto (fun ν => F.ω ν ξ) atTop (𝓝 (ωs ξ)))
    (a : ℕ → ℝ) (ha : ∀ ν, alphaCheck α / 2 ≤ a ν)
    (hmel : ∀ ξ ∈ S, ∀ ν, ∀ k : Fin 2 → ℤ, k ≠ 0 → a ν / kAk k ≤ |∑ i, (k i : ℝ) * F.ω ν ξ i|) :
    (∀ ξ ∈ S, ∀ k : Fin 2 → ℤ, k ≠ 0 →
      alphaCheck α / (2 * kAk k) ≤ |∑ i, (k i : ℝ) * ωs ξ i|) ∧
    (∀ ξ ∈ S, ‖ωs ξ - omegaTan m hm ξ‖ ≤ F.εω) ∧
    (∀ ξ ∈ S, ∀ ζ ∈ S, ‖ωs ξ - ωs ζ‖ ≤ (measNA m hm + F.θ) * ‖ξ - ζ‖) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ξ hξ k hk
    have h := w6_divisor_limit (Ωs := fun _ _ => 0) (Ω := fun _ => 0) (hlim ξ hξ)
      (fun _ => tendsto_const_nhds) ha k 0 (fun ν => by
        rw [japL_zero]
        have := hmel ξ hξ ν k hk
        simpa [linF] using this)
    rw [japL_zero] at h
    have e : alphaCheck α / (2 * kAk k) = alphaCheck α / 2 * 1 / kAk k := by ring
    rw [e]
    simpa [linF] using h
  · intro ξ hξ
    have hL : Tendsto (fun ν => ‖F.ω ν ξ - omegaTan m hm ξ‖) atTop
        (𝓝 ‖ωs ξ - omegaTan m hm ξ‖) :=
      ((hlim ξ hξ).sub tendsto_const_nhds).norm
    exact le_of_tendsto' hL fun ν => (F.pair ν).h1_sup ξ (hS ν hξ)
  · intro ξ hξ ζ hζ
    have hL : Tendsto (fun ν => ‖(F.ω ν ξ - omegaTan m hm ξ) - (F.ω ν ζ - omegaTan m hm ζ)‖)
        atTop (𝓝 ‖(ωs ξ - omegaTan m hm ξ) - (ωs ζ - omegaTan m hm ζ)‖) :=
      (((hlim ξ hξ).sub tendsto_const_nhds).sub ((hlim ζ hζ).sub tendsto_const_nhds)).norm
    have h1 : ‖(ωs ξ - omegaTan m hm ξ) - (ωs ζ - omegaTan m hm ζ)‖ ≤ F.θ * ‖ξ - ζ‖ :=
      le_of_tendsto' hL fun ν => (F.pair ν).h1_lip ξ (hS ν hξ) ζ (hS ν hζ)
    have h2 := norm_omegaTan_sub_le m hm ξ ζ
    have e : ωs ξ - ωs ζ = ((ωs ξ - omegaTan m hm ξ) - (ωs ζ - omegaTan m hm ζ)) +
        (omegaTan m hm ξ - omegaTan m hm ζ) := by abel
    rw [e]
    calc _ ≤ ‖(ωs ξ - omegaTan m hm ξ) - (ωs ζ - omegaTan m hm ζ)‖ +
          ‖omegaTan m hm ξ - omegaTan m hm ζ‖ := norm_add_le _ _
      _ ≤ F.θ * ‖ξ - ζ‖ + measNA m hm * ‖ξ - ζ‖ := add_le_add h1 h2
      _ = (measNA m hm + F.θ) * ‖ξ - ζ‖ := by ring

end KAM.Wave
