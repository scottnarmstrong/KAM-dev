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

/-- Conditional helper (not a node export; the generator bound is a premise): Lie series: with `θ_φ = 2 e b |φ| / δ_ν = e b η`, `η = 2|φ|/δ_ν`,
`e² b η / 4 ≤ e b η`, the iterates satisfy `|ad_φ^h u| / h! ≤ θ_φ^h |u|` and
`|u ∘ X¹_φ| ≤ (1 - θ_φ)⁻¹ |u|` (in the class, at two losses). -/
theorem osc_ratio_of_gen_bound (hn : 1 ≤ n) (hm : 1 ≤ m)
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
    simpa [θ, oscTheta] using this

/-- Conditional helper (generator bound a premise): integral remainders: the same bound `(1 - θ_φ)⁻¹` holds for the
integral remainders along the flow. -/
theorem osc_ratio_integral_of_gen_bound (hn : 1 ≤ n) (hm : 1 ≤ m)
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

/-- Conditional helper (generator bound a premise): numerics and series: `θ_φ ≤ 2 e b δ / (ᾱ δ_ν) ≤ e/8 < 0.34`,
`(16/9) θ_φ < 0.61 < 1`, and the Lie series equals the composition on the two-loss domain. -/
theorem osc_range_of_gen_bound (hn : 1 ≤ n) (hm : 1 ≤ m)
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

section ArNodes

variable {n m : ℕ} {D : Set (Fin n → ℝ)} {r ε₀ s₀ ε μ α K : ℝ} {h : (Fin n → ℂ) → ℂ}
  {P : CHam (n + m)}

/-- `e^{-κ/6} = ε⁵` for the source choice `K = (15 / (π s₀)) log (1/ε)`, `κ = 2 π K s₀`. -/
private theorem ar_exp_kappa (hs₀ : 0 < s₀) (hε : 0 < ε) (hK : K = 15 / (π * s₀) * log (1 / ε)) :
    exp (-(2 * π * K * s₀) / 6) = ε ^ 5 := by
  subst hK
  have : -(2 * π * (15 / (π * s₀) * Real.log (1 / ε)) * s₀) / 6 = ((5 : ℕ) : ℝ) * Real.log ε := by
    rw [one_div, Real.log_inv]
    have := Real.pi_pos
    push_cast
    field_simp
    ring
  rw [this, Real.exp_nat_mul, Real.exp_log hε]

/-- The joint hypotheses of oscillator averaging from the source premises of `ar-apply`. -/
private theorem ar_hyp (hn : 1 ≤ n) (hm : 1 ≤ m) (hr : 0 < r) (hε₀ : 0 < ε₀) (hs₀ : 0 < s₀)
    (hε : 0 < ε ∧ ε < exp (-1 / 5)) (hμ : 0 < μ) (hα : 0 < α)
    (hK : K = 15 / (π * s₀) * log (1 / ε))
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D r))
    (hreal : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd D r →
      (h (KAM.realInclusion n I)).im = 0)
    (hPc : oscClass D r ε₀ ε₀ s₀ P) (hPb : oscBound D r ε₀ ε₀ s₀ P 1)
    (hPr : RealOn (oscDom D r ε₀ ε₀ s₀) P)
    (hdiv : DivisorBound (KAM.actionNbhd D r) K {0} h α)
    (hR2 : 2 ^ 12 * (1 + (m : ℝ)) * K * s₀ * μ ≤ α * min (r * s₀) (ε₀ ^ 2)) :
    OscHyp D r ε₀ ε₀ 0 s₀ K α μ h (μ • P) := by
  have hlog : 1 / 5 < Real.log (1 / ε) := by
    rw [one_div ε, Real.log_inv]
    have := (Real.log_lt_iff_lt_exp hε.1).2 hε.2
    linarith
  have hπ := Real.pi_pos
  have hK2 : 2 * π * K * s₀ = 30 * Real.log (1 / ε) := by
    subst hK; field_simp; ring
  have hKpos : 0 < K := by
    subst hK; exact mul_pos (by positivity) (by linarith)
  have hsm : ∀ w, (μ • P) w = (μ : ℂ) * P w := fun w => by simp [Complex.real_smul]
  have hfun : (μ • P : CHam (n + m)) = fun w => (μ : ℂ) * P w := funext hsm
  refine ⟨hn, hm, ⟨hr, hε₀, hε₀, hs₀, hKpos, hα⟩, le_rfl, hμ.le, by rw [hK2]; linarith, hh,
    hreal, ?_, ?_, ?_, hdiv, ?_⟩
  · rw [hfun, zero_add]; exact hPc.const_mul _
  · rw [hfun, zero_add]
    have := osc_bound_const_mul (μ : ℂ) hPb
    simpa [abs_of_pos hμ] using this
  · intro x hx
    simp only [zero_add] at hx
    have := hPr x hx
    simp only [hsm, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      this, mul_zero]
  · rw [sq ε₀] at hR2
    nlinarith [hR2]

/-- `stepP:p2:ar-apply`: Proposition `osc-averaging` for `f = μ P`, `s̄ = 0`, `s = s₀`, `r_p = r_q
= ε₀`, with `K` chosen by `e^{-κ/6} = ε⁵`: there is a symplectic periodic `φ̄` on the half domain
with `H ∘ φ̄ = H₀ + g + f_*`, `g` independent of `θ`, and `f̂₀ = μ ⟨P⟩`. -/
theorem p2_ar_apply (hn : 1 ≤ n) (hm : 1 ≤ m) (hr : 0 < r) (hε₀ : 0 < ε₀) (hs₀ : 0 < s₀)
    (hε : 0 < ε ∧ ε < exp (-1 / 5)) (hμ : 0 < μ) (hα : 0 < α)
    (hK : K = 15 / (π * s₀) * log (1 / ε))
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D r))
    (hreal : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd D r →
      (h (KAM.realInclusion n I)).im = 0)
    (hPc : oscClass D r ε₀ ε₀ s₀ P) (hPb : oscBound D r ε₀ ε₀ s₀ P 1)
    (hPr : RealOn (oscDom D r ε₀ ε₀ s₀) P)
    (hdiv : DivisorBound (KAM.actionNbhd D r) K {0} h α)
    (hR2 : 2 ^ 12 * (1 + (m : ℝ)) * K * s₀ * μ ≤ α * min (r * s₀) (ε₀ ^ 2)) :
    ∃ (Ψ : CPhase (n + m) → CPhase (n + m)) (g fs : CHam (n + m)),
      let V := oscDom D (r / 2) (ε₀ / 2) (ε₀ / 2) (s₀ / 6)
      DifferentiableOn ℂ Ψ V ∧ Set.InjOn Ψ V ∧ MapsTo Ψ V (oscDom D r ε₀ ε₀ s₀) ∧
      (∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v) ∧
      (∀ z ∈ V, ∀ k : Fin n → ℤ,
        Ψ (z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) =
          Ψ z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) ∧
      oscClass D (r / 2) (ε₀ / 2) (ε₀ / 2) (s₀ / 6) g ∧ RealOn V g ∧
      (∀ x ∈ oscParams (m := m) D (r / 2) (ε₀ / 2) (ε₀ / 2), ∀ θ θ',
        oscUnpack (θ, x) ∈ V → oscUnpack (θ', x) ∈ V →
          g (oscUnpack (θ, x)) = g (oscUnpack (θ', x))) ∧
      (∀ z ∈ V, h (firstBlock (b := m) (Ψ z).2) + (μ • P) (Ψ z) =
        h (firstBlock (b := m) z.2) + g z + fs z) ∧
      (∀ z : CPhase (n + m), coeff (oscFunction (μ • P)) (oscPack z).2 0 =
        (μ : ℂ) * coeff (oscFunction P) (oscPack z).2 0) := by
  have H := ar_hyp hn hm hr hε₀ hs₀ hε hμ hα hK hh hreal hPc hPb hPr hdiv hR2
  obtain ⟨Ψ, g, fs, hV⟩ := osc_averaging H
  dsimp only at hV
  simp only [zero_add] at hV
  obtain ⟨c1, c2, c3, c4, c5, -, c7, c8, c9, c10, -, -, -, -, -⟩ := hV
  exact ⟨Ψ, g, fs, c1, c2, c3, c4, c5, c7, c8, c9, c10, coeff_smul_osc μ P⟩

/-- `stepP:p2:ar-collect`: for `P̃ = (g - μ ⟨P⟩) + f_*` (the remainder of `ar-apply`), `|P̃|` is at
most the sum `400 b μ² / (ᾱ d) + e^{-κ/6} μ` of the two bounds of the proposition, and
`e^{-κ/6} μ = μ ε⁵`. -/
theorem p2_ar_collect (hn : 1 ≤ n) (hm : 1 ≤ m) (hr : 0 < r) (hε₀ : 0 < ε₀) (hs₀ : 0 < s₀)
    (hε : 0 < ε ∧ ε < exp (-1 / 5)) (hμ : 0 < μ) (hα : 0 < α)
    (hK : K = 15 / (π * s₀) * log (1 / ε))
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D r))
    (hreal : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd D r →
      (h (KAM.realInclusion n I)).im = 0)
    (hPc : oscClass D r ε₀ ε₀ s₀ P) (hPb : oscBound D r ε₀ ε₀ s₀ P 1)
    (hPr : RealOn (oscDom D r ε₀ ε₀ s₀) P)
    (hdiv : DivisorBound (KAM.actionNbhd D r) K {0} h α)
    (hR2 : 2 ^ 12 * (1 + (m : ℝ)) * K * s₀ * μ ≤ α * min (r * s₀) (ε₀ ^ 2)) :
    ∃ (g fs Pt : CHam (n + m)),
      (∀ z ∈ oscDom D (r / 2) (ε₀ / 2) (ε₀ / 2) (s₀ / 6),
        Pt z = g z - (μ : ℂ) * coeff (oscFunction P) (oscPack z).2 0 + fs z) ∧
      oscClass D (r / 2) (ε₀ / 2) (ε₀ / 2) (s₀ / 6) Pt ∧
      oscBound D (r / 2) (ε₀ / 2) (ε₀ / 2) (s₀ / 6) Pt
        (400 * (1 + (m : ℝ)) * μ ^ 2 / (2 * π * α * min (r * s₀) (ε₀ ^ 2)) +
          exp (-(2 * π * K * s₀) / 6) * μ) ∧
      exp (-(2 * π * K * s₀) / 6) * μ = μ * ε ^ 5 := by
  have H := ar_hyp hn hm hr hε₀ hs₀ hε hμ hα hK hh hreal hPc hPb hPr hdiv hR2
  have hexp := ar_exp_kappa hs₀ hε.1 hK
  obtain ⟨Ψ, g, fs, R, hV⟩ := averaged_remainder hε hμ (by rw [← hK]; exact H) hPb
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hR, hRc, hRb, -, -⟩ := hV
  have hex : exp (-(2 * π * K * s₀) / 6) * μ = μ * ε ^ 5 := by rw [hexp, mul_comm]
  refine ⟨g, fs, R, hR, hRc, ?_, hex⟩
  rw [hex]
  exact hRb

end ArNodes

end KAM.Planetary

end
