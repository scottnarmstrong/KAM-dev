/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Canonical.Lie
public import KAM.Planetary.Averaging.OscillatorCompositionSeries
public import KAM.Planetary.Averaging.OscillatorFlowProps
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# P Parts 2-3: identification of the oscillator Lie series (`stepP:p2:oi-transfer`)

On the one-loss domain `𝒪` of `oscStepMap` the flow of the generator `φ` is the literal flow of
`oscStepMap`.

* `osc_trajectory_hat`: trajectories from the two-loss domain stay in the `7/4`-loss domain;
* `osc_series_eq`: `u ∘ X¹_φ = ∑ ad_φ^j u / j!` on the two-loss domain (Taylor's formula along the
  flow on `𝒪`, with the adjoint estimate for the `3/4`-loss, whose ratio is `16/9` of the ratio of
  the full loss, `< 1`);
* `osc_composition_t`: `u ∘ X^t_φ` for `t ∈ [-1, 1]` is the series `∑ t^j ad_φ^j u / j!`, in the class
  with the weighted bound `(1 - |t| θ)⁻¹ A` (Taylor along the same flow, rescaled in time).

Design `docs/tracks/P/design/P23-LEAN-DESIGN.md` (Revision 3), package P23-13e.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real Filter Finset
open scoped Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

section OscComposition
variable {n m : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S ρ ρp ρq σ Φ A : ℝ}
  {φ u : CHam (n + m)}

/-- The flow hypotheses of `OscFlowHyp` from the source premises (`E = Φ`). -/
theorem OscComposeData.toFlowHyp (H : OscComposeData D r rp rq S ρ ρp ρq σ Φ φ) :
    OscFlowHyp D r rp rq S ρ ρp ρq σ Φ φ := by
  obtain ⟨hρ, hρr, hρp, hρpr, hρq, hρqr, hσ, hσS⟩ := H.widths
  have hd : 0 < min (ρ * σ) (ρp * ρq) := lt_min (by positivity) (by positivity)
  have h4 := (osc_ratio_range m hd H.phi_nonneg H.small).2.2.2.2
  exact ⟨hρ, by linarith, hρp, by linarith, hρq, by linarith, hσ, by linarith,
    H.phi_class, H.phi_bound, H.phi_nonneg, h4.trans (by norm_num)⟩

theorem OscComposeData.displacement (H : OscComposeData D r rp rq S ρ ρp ρq σ Φ φ) :
    Φ / min (ρ * σ) (ρp * ρq) ≤ 1 / 4 := by
  obtain ⟨hρ, -, hρp, -, hρq, -, hσ, -⟩ := H.widths
  have hd : 0 < min (ρ * σ) (ρp * ρq) := lt_min (by positivity) (by positivity)
  exact (osc_ratio_range m hd H.phi_nonneg H.small).2.2.2.2

/-- Flow domain remains the literal one-loss domain of oscStepMap. -/
theorem osc_trajectory_hat (H : OscComposeData D r rp rq S ρ ρp ρq σ Φ φ) :
    ∀ z ∈ oscDom D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ),
    ∀ t ∈ Icc (-1 : ℝ) 1,
      flow (KAM.hamiltonianVectorFieldℂ φ)
          (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) t z ∈
        oscDom D (r - 7 * ρ / 4) (rp - 7 * ρp / 4)
          (rq - 7 * ρq / 4) (S - 7 * σ / 4) := by
  intro z hz t ht
  have F := H.toFlowHyp
  have hz1 : z ∈ gaugeInterior F.W (oscO (m := m) D r rp rq S ρ ρp ρq σ) (1 / 2) :=
    fun w hw => F.one hz w (hw.trans (by norm_num))
  have hd := (flow_a F.smallField hz1).2.2.2 t ht
  rw [F.norm_W] at hd
  have hdisp := H.displacement
  have hab : |t| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  have hg : oscGauge ρ ρp ρq σ (flow (KAM.hamiltonianVectorFieldℂ φ)
      (oscO (m := m) D r rp rq S ρ ρp ρq σ) t z - z) ≤ 1 / 4 := by
    refine hd.trans ?_
    have h0 : 0 ≤ Φ / min (ρ * σ) (ρp * ρq) := div_nonneg H.phi_nonneg
      (lt_min (mul_pos H.widths.1 H.widths.2.2.2.2.2.2.2.1)
        (mul_pos H.widths.2.2.1 H.widths.2.2.2.2.1)).le
    nlinarith
  have := oscDom_of_gauge_le F.hρ F.hρp F.hρq F.hσ hz hg
  have e1 : r - 2 * ρ + ρ * (1 / 4) = r - 7 * ρ / 4 := by ring
  have e2 : rp - 2 * ρp + ρp * (1 / 4) = rp - 7 * ρp / 4 := by ring
  have e3 : rq - 2 * ρq + ρq * (1 / 4) = rq - 7 * ρq / 4 := by ring
  have e4 : S - 2 * σ + σ * (1 / 4) = S - 7 * σ / 4 := by ring
  rwa [e1, e2, e3, e4] at this

/-- The ratio of the `3/4`-loss. -/
theorem osc_hat_ratio (H : OscComposeData D r rp rq S ρ ρp ρq σ Φ φ) :
    oscLieRatio m Φ (min (ρ * (3 / 4) * (σ * (3 / 4))) (ρp * (3 / 4) * (ρq * (3 / 4)))) =
        16 / 9 * oscLieRatio m Φ (min (ρ * σ) (ρp * ρq)) ∧
    0 ≤ oscLieRatio m Φ (min (ρ * σ) (ρp * ρq)) ∧
    16 / 9 * oscLieRatio m Φ (min (ρ * σ) (ρp * ρq)) < 1 ∧
    oscLieRatio m Φ (min (ρ * σ) (ρp * ρq)) ≤ oscTheta m Φ (min (ρ * σ) (ρp * ρq)) ∧
    oscTheta m Φ (min (ρ * σ) (ρp * ρq)) < 1 := by
  obtain ⟨hρ, -, hρp, -, hρq, -, hσ, -⟩ := H.widths
  have hd : 0 < min (ρ * σ) (ρp * ρq) := lt_min (by positivity) (by positivity)
  obtain ⟨hq0, hqθ, hθ, h169, -⟩ := osc_ratio_range m hd H.phi_nonneg H.small
  have e : min (ρ * (3 / 4) * (σ * (3 / 4))) (ρp * (3 / 4) * (ρq * (3 / 4))) =
      9 / 16 * min (ρ * σ) (ρp * ρq) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 9 / 16)]
    congr 1 <;> ring
  have hθ0 := hq0.trans hqθ
  refine ⟨?_, hq0, by nlinarith, hqθ, by nlinarith⟩
  rw [e]
  unfold oscLieRatio
  field_simp
  ring

/-- Terms of the series on the two-loss domain. -/
theorem osc_term_bound (H : OscComposeData D r rp rq S ρ ρp ρq σ Φ φ)
    (hu : oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u)
    (hb : oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u A) (hA : 0 ≤ A) (j : ℕ) :
    oscClass D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
      (fun z => ((j.factorial : ℂ)⁻¹) * adPow φ j u z) ∧
    oscBound D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
      (fun z => ((j.factorial : ℂ)⁻¹) * adPow φ j u z)
      (oscLieRatio m Φ (min (ρ * σ) (ρp * ρq)) ^ j * A) := by
  obtain ⟨hρ, hρr, hρp, hρpr, hρq, hρqr, hσ, hσS⟩ := H.widths
  have e1 : r - ρ - ρ = r - 2 * ρ := by ring
  have e2 : rp - ρp - ρp = rp - 2 * ρp := by ring
  have e3 : rq - ρq - ρq = rq - 2 * ρq := by ring
  have e4 : S - σ - σ = S - 2 * σ := by ring
  obtain ⟨hc, hbd⟩ := osc_adjoint_bound (r := r - ρ) (rp := rp - ρp) (rq := rq - ρq)
    (S := S - σ) (r₀ := r) (rp₀ := rp) (rq₀ := rq) (S₀ := S) (ρ := ρ) (ρp := ρp) (ρq := ρq)
    (σ := σ) (Φ := Φ) H.hn H.hm H.phi_class hu H.phi_bound hb H.phi_nonneg hA
    ⟨hρ, by linarith, hρp, by linarith, hρq, by linarith, hσ, by linarith⟩
    ⟨by linarith, by linarith, by linarith, by linarith⟩ j
  rw [e1, e2, e3, e4] at hc hbd
  exact ⟨hc.const_mul _, hbd⟩

/-- Bound of the iterates along trajectories from the two-loss domain, via the `3/4`-loss. -/
theorem osc_traj_bound (H : OscComposeData D r rp rq S ρ ρp ρq σ Φ φ)
    (hu : oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u)
    (hb : oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u A) (hA : 0 ≤ A)
    {N : ℕ} {z : CPhase (n + m)}
    (hz : z ∈ oscDom D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ))
    {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    ‖adPow φ N u (flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) s z)‖ ≤
      (N.factorial : ℝ) *
        ((16 / 9 * oscLieRatio m Φ (min (ρ * σ) (ρp * ρq))) ^ N * A) := by
  obtain ⟨hρ, hρr, hρp, hρpr, hρq, hρqr, hσ, hσS⟩ := H.widths
  obtain ⟨hhat, -, -, -, -⟩ := osc_hat_ratio H
  obtain ⟨hc, hbd⟩ := osc_adjoint_bound (r := r - ρ) (rp := rp - ρp) (rq := rq - ρq)
    (S := S - σ) (r₀ := r) (rp₀ := rp) (rq₀ := rq) (S₀ := S) (ρ := ρ * (3 / 4))
    (ρp := ρp * (3 / 4)) (ρq := ρq * (3 / 4)) (σ := σ * (3 / 4)) (Φ := Φ) H.hn H.hm
    H.phi_class hu H.phi_bound hb H.phi_nonneg hA
    ⟨by positivity, by linarith, by positivity, by linarith, by positivity, by linarith,
      by positivity, by linarith⟩
    ⟨by linarith, by linarith, by linarith, by linarith⟩ N
  have hmem := osc_trajectory_hat H z hz s hs
  have e1 : r - 7 * ρ / 4 = r - ρ - ρ * (3 / 4) := by ring
  have e2 : rp - 7 * ρp / 4 = rp - ρp - ρp * (3 / 4) := by ring
  have e3 : rq - 7 * ρq / 4 = rq - ρq - ρq * (3 / 4) := by ring
  have e4 : S - 7 * σ / 4 = S - σ - σ * (3 / 4) := by ring
  rw [e1, e2, e3, e4] at hmem
  rw [hhat] at hbd
  have h4 := oscBound.norm_le (hc.const_mul ((N.factorial : ℂ)⁻¹)) hbd _ hmem
  have hf : (0 : ℝ) < N.factorial := Nat.cast_pos.2 (Nat.factorial_pos N)
  calc _ = (N.factorial : ℝ) * ‖((N.factorial : ℂ)⁻¹) * adPow φ N u
          (flow (KAM.hamiltonianVectorFieldℂ φ)
            (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) s z)‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 hf.le

end OscComposition

end KAM.Planetary

end
