/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.OscillatorFinite
public import KAM.Planetary.Averaging.OscillatorCompositionIntegral
public import KAM.Planetary.Averaging.OscillatorCompositionSeries
public import KAM.Planetary.Averaging.OscillatorStepComplete
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# P Part 2: literal graph-node exports for the oscillator averaging steps

Unsigned exports stating the literal conclusions of `stepP:p2:oi-ratio`, `stepP:p2:oi-range`,
`stepP:p2:ar-apply` and `stepP:p2:ar-collect` from the source hypotheses (graph-gap package
GAP-P2). Here `b = 1 + m`, `δ_ν = min (ρσ) (ρpρq)` and `ᾱ` is the (positive) weight of the source.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

section OiNodes

variable {n m : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S ρ ρp ρq σ Φ A ᾱ δ : ℝ}
  {φ u : CHam (n + m)}

/-- The oscillator composition data from the source premises: `|φ| ≤ δ/ᾱ` and
`δ ≤ ᾱ δ_ν / (16 b)`. -/
theorem OscComposeData.ofDeltaBound (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hw : 0 < ρ ∧ 2 * ρ < r ∧ 0 < ρp ∧ 2 * ρp < rp ∧ 0 < ρq ∧ 2 * ρq < rq ∧
      0 < σ ∧ 2 * σ < S)
    (hc : oscClass D r rp rq S φ) (hb : oscBound D r rp rq S φ Φ) (hΦ : 0 ≤ Φ)
    (hᾱ : 0 < ᾱ) (hΦδ : Φ ≤ δ / ᾱ)
    (hδ : δ ≤ ᾱ * min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ)))) :
    OscComposeData D r rp rq S ρ ρp ρq σ Φ φ := by
  refine ⟨hn, hm, hw, hc, hb, hΦ, hΦδ.trans ?_⟩
  rw [div_le_iff₀ hᾱ]
  calc δ ≤ ᾱ * min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ))) := hδ
    _ = min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ))) * ᾱ := by ring

/-- `stepP:p2:oi-ratio`, Lie series: with `θ_φ = 2 e b |φ| / δ_ν = e b η`, `η = 2|φ|/δ_ν`,
`e² b η / 4 ≤ e b η`, the iterates satisfy `|ad_φ^h u| / h! ≤ θ_φ^h |u|` and
`|u ∘ X¹_φ| ≤ (1 - θ_φ)⁻¹ |u|` (in the class, at two losses). -/
theorem p2_oi_ratio (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hw : 0 < ρ ∧ 2 * ρ < r ∧ 0 < ρp ∧ 2 * ρp < rp ∧ 0 < ρq ∧ 2 * ρq < rq ∧
      0 < σ ∧ 2 * σ < S)
    (hc : oscClass D r rp rq S φ) (hb : oscBound D r rp rq S φ Φ) (hΦ : 0 ≤ Φ)
    (hᾱ : 0 < ᾱ) (hΦδ : Φ ≤ δ / ᾱ)
    (hδ : δ ≤ ᾱ * min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ))))
    (hu : oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u)
    (hbu : oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u A) (hA : 0 ≤ A) :
    let η := 2 * Φ / min (ρ * σ) (ρp * ρq)
    let θ := 2 * exp 1 * (1 + (m : ℝ)) * Φ / min (ρ * σ) (ρp * ρq)
    θ = exp 1 * (1 + (m : ℝ)) * η ∧
    exp 1 ^ 2 * (1 + (m : ℝ)) * η / 4 ≤ exp 1 * (1 + (m : ℝ)) * η ∧
    (∀ j : ℕ,
      oscClass D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
        (fun z => ((j.factorial : ℂ)⁻¹) * adPow φ j u z) ∧
      oscBound D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
        (fun z => ((j.factorial : ℂ)⁻¹) * adPow φ j u z) (θ ^ j * A)) ∧
    oscClass D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
      (fun z => u (flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) 1 z)) ∧
    oscBound D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
      (fun z => u (flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) 1 z)) ((1 - θ)⁻¹ * A) := by
  intro η θ
  have H := OscComposeData.ofDeltaBound hn hm hw hc hb hΦ hᾱ hΦδ hδ
  obtain ⟨hρ, -, hρp, -, hρq, -, hσ, -⟩ := hw
  have hd : 0 < min (ρ * σ) (ρp * ρq) := lt_min (by positivity) (by positivity)
  obtain ⟨-, hq0, -, hqθ, -⟩ := osc_hat_ratio H
  have he : 0 < exp 1 := exp_pos 1
  have he4 : exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hη : 0 ≤ η := by positivity
  refine ⟨by simp only [θ, η]; ring, ?_, fun j => ?_, ?_⟩
  · have hb0 : 0 ≤ exp 1 * (1 + (m : ℝ)) * η := by positivity
    nlinarith
  · obtain ⟨c1, c2⟩ := osc_term_bound H hu hbu hA j
    exact ⟨c1, c2.mono_gen le_rfl le_rfl le_rfl le_rfl
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hqθ j) hA)⟩
  · have := osc_composition_t H hu hbu hA (t := 1) ⟨by norm_num, le_rfl⟩
    simpa [θ] using this.1
  · have := (osc_composition_t H hu hbu hA (t := 1) ⟨by norm_num, le_rfl⟩).2
    simpa [θ] using this

/-- `stepP:p2:oi-ratio`, integral remainders: the same bound `(1 - θ_φ)⁻¹` holds for the
integral remainders along the flow. -/
theorem p2_oi_ratio_integral (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hw : 0 < ρ ∧ 2 * ρ < r ∧ 0 < ρp ∧ 2 * ρp < rp ∧ 0 < ρq ∧ 2 * ρq < rq ∧
      0 < σ ∧ 2 * σ < S)
    (hc : oscClass D r rp rq S φ) (hb : oscBound D r rp rq S φ Φ) (hΦ : 0 ≤ Φ)
    (hᾱ : 0 < ᾱ) (hΦδ : Φ ≤ δ / ᾱ)
    (hδ : δ ≤ ᾱ * min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ))))
    {v : ℝ → CHam (n + m)} {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1,
      oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (v t) ∧
      oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (v t) B)
    (hcv : ContinuousOn (fun p : ℝ × CPhase (n + m) => v p.1 p.2)
      (Icc 0 1 ×ˢ oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)))
    (hDc : ContinuousOn (fun p : ℝ × CPhase (n + m) => fderiv ℂ (v p.1) p.2)
      (Icc 0 1 ×ˢ oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ))) :
    let R := fun z => ∫ t in (0 : ℝ)..1, v t (flow (KAM.hamiltonianVectorFieldℂ φ)
      (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) t z)
    oscClass D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) R ∧
    oscBound D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) R
      ((1 - 2 * exp 1 * (1 + (m : ℝ)) * Φ / min (ρ * σ) (ρp * ρq))⁻¹ * B) :=
  osc_composition_integral (OscComposeData.ofDeltaBound hn hm hw hc hb hΦ hᾱ hΦδ hδ) hB hv hcv
    hDc

/-- `stepP:p2:oi-range`, numerics and series: `θ_φ ≤ 2 e b δ / (ᾱ δ_ν) ≤ e/8 < 0.34`,
`(16/9) θ_φ < 0.61 < 1`, and the Lie series equals the composition on the two-loss domain. -/
theorem p2_oi_range (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hw : 0 < ρ ∧ 2 * ρ < r ∧ 0 < ρp ∧ 2 * ρp < rp ∧ 0 < ρq ∧ 2 * ρq < rq ∧
      0 < σ ∧ 2 * σ < S)
    (hc : oscClass D r rp rq S φ) (hb : oscBound D r rp rq S φ Φ) (hΦ : 0 ≤ Φ)
    (hᾱ : 0 < ᾱ) (hΦδ : Φ ≤ δ / ᾱ)
    (hδ : δ ≤ ᾱ * min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ))))
    (hu : oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u)
    (hbu : oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u A) (hA : 0 ≤ A) :
    let θ := 2 * exp 1 * (1 + (m : ℝ)) * Φ / min (ρ * σ) (ρp * ρq)
    θ ≤ 2 * exp 1 * (1 + (m : ℝ)) * δ / (ᾱ * min (ρ * σ) (ρp * ρq)) ∧
    2 * exp 1 * (1 + (m : ℝ)) * δ / (ᾱ * min (ρ * σ) (ρp * ρq)) ≤ exp 1 / 8 ∧
    exp 1 / 8 < 0.34 ∧ 16 / 9 * θ < 0.61 ∧ (0.61 : ℝ) < 1 ∧
    ∀ z ∈ oscDom D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ),
      u (flow (KAM.hamiltonianVectorFieldℂ φ)
          (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) 1 z) =
        ∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * adPow φ j u z := by
  intro θ
  have H := OscComposeData.ofDeltaBound hn hm hw hc hb hΦ hᾱ hΦδ hδ
  obtain ⟨hρ, -, hρp, -, hρq, -, hσ, -⟩ := hw
  have hd : 0 < min (ρ * σ) (ρp * ρq) := lt_min (by positivity) (by positivity)
  have he : 0 < exp 1 := exp_pos 1
  have he' : exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : θ ≤ 2 * exp 1 * (1 + (m : ℝ)) * δ / (ᾱ * min (ρ * σ) (ρp * ρq)) := by
    have : Φ / min (ρ * σ) (ρp * ρq) ≤ δ / (ᾱ * min (ρ * σ) (ρp * ρq)) := by
      rw [div_le_div_iff₀ hd (by positivity)]
      have := mul_le_mul_of_nonneg_right hΦδ hd.le
      rw [div_mul_eq_mul_div, le_div_iff₀ hᾱ] at this
      linarith
    have e1 : θ = 2 * exp 1 * (1 + (m : ℝ)) * (Φ / min (ρ * σ) (ρp * ρq)) := by
      simp only [θ]; ring
    have e2 : 2 * exp 1 * (1 + (m : ℝ)) * δ / (ᾱ * min (ρ * σ) (ρp * ρq)) =
        2 * exp 1 * (1 + (m : ℝ)) * (δ / (ᾱ * min (ρ * σ) (ρp * ρq))) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h2 : 2 * exp 1 * (1 + (m : ℝ)) * δ / (ᾱ * min (ρ * σ) (ρp * ρq)) ≤ exp 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδ (by positivity : (0 : ℝ) ≤
      16 * (1 + (m : ℝ)))) he.le
    have e : 16 * (1 + (m : ℝ)) * (ᾱ * min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ)))) =
        ᾱ * min (ρ * σ) (ρp * ρq) := by field_simp
    rw [e] at this
    nlinarith
  have h3 : exp 1 / 8 < 0.34 := by linarith
  refine ⟨h1, h2, h3, ?_, by norm_num, ?_⟩
  · linarith
  · exact osc_series_eq H hu hbu hA

/-- `stepP:p2:oi-range`, items (a) and (b) as in `N iterative` (with `ᾱ = 2 π α`): the
displacement bounds and the bound of the new remainder with the factor `1 - θ_φ`. -/
theorem p2_oi_range_ab {J : ℕ} {K α : ℝ} {h : (Fin n → ℂ) → ℂ} {f : CHam (n + m)}
    {gj : Fin J → CHam (n + m)} {rj rpj rqj Sj Mj : Fin J → ℝ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hα : 0 < α) (hK : 0 ≤ K)
    (hwidths : 0 < ρ ∧ 2 * ρ < r ∧ 0 < ρp ∧ 2 * ρp < rp ∧
      0 < ρq ∧ 2 * ρq < rq ∧ 0 < σ ∧ 2 * σ < S)
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D r))
    (hdiv : DivisorBound (KAM.actionNbhd D r) K {0} h α)
    (hf : oscClass D r rp rq S f) (hδ : oscBound D r rp rq S f δ)
    (hδpos : 0 ≤ δ) (hsmall : δ ≤ (2 * π * α) * min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ))))
    (hg : ∀ j, oscClass D (rj j) (rpj j) (rqj j) (Sj j) (gj j) ∧
      oscBound D (rj j) (rpj j) (rqj j) (Sj j) (gj j) (Mj j) ∧
      r ≤ rj j ∧ rp ≤ rpj j ∧ rq ≤ rqj j ∧ S ≤ Sj j) :
    let Ψ := oscStepMap D r rp rq S ρ ρp ρq σ K h f
    let g := fun z => ∑ j, gj j z
    let gp := fun z => g z + coeff (oscFunction f) (oscPack z).2 0
    let fp := fun z => h (firstBlock (b := m) (Ψ z).2) + g (Ψ z) + f (Ψ z) -
      h (firstBlock (b := m) z.2) - gp z
    let d := min (ρ * σ) (ρp * ρq)
    let Rsum := ∑ j, max (max (ρ / (rj j - r + ρ)) (σ / (Sj j - S + σ)))
      (max (ρp / (rpj j - rp + ρp)) (ρq / (rqj j - rq + ρq))) * Mj j
    let U := oscDom D (r - 3 * ρ / 2) (rp - 3 * ρp / 2)
      (rq - 3 * ρq / 2) (S - 3 * σ / 2)
    (∀ z ∈ U,
      ‖firstBlock (b := m) ((Ψ z).1 - z.1)‖ ≤ δ / (2 * π * α * ρ) ∧
      ‖firstBlock (b := m) ((Ψ z).2 - z.2)‖ ≤ δ / (exp 1 * (2 * π * α) * σ) ∧
      ‖lastBlock (a := n) ((Ψ z).1 - z.1)‖ ≤ δ / (2 * π * α * ρp) ∧
      ‖lastBlock (a := n) ((Ψ z).2 - z.2)‖ ≤ δ / (2 * π * α * ρq)) ∧
    oscBound D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) fp
      ((1 - 2 * exp 1 * (1 + (m : ℝ)) * δ / (2 * π * α * d))⁻¹ *
        (2 * (1 + (m : ℝ)) / (2 * π * α * d) * (Rsum + δ) + exp (-(2 * π * K * σ))) * δ) := by
  intro Ψ g gp fp d Rsum U
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, b, a, -⟩ :=
    osc_iter hn hm hα hK hwidths hh hdiv hf hδ hδpos hsmall hg
  exact ⟨a, b⟩

end OiNodes

end KAM.Planetary

end
