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
      (lt_min (mul_pos H.widths.1 H.widths.2.2.2.2.2.2.1)
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


/-- Taylor's formula along the `𝒪`-flow at time `t ∈ [-1, 1]`: the partial sums of
`∑ t^j ad_φ^j u / j!` converge to `u (X^t z)`. -/
theorem osc_taylor_t (H : OscComposeData D r rp rq S ρ ρp ρq σ Φ φ)
    (hu : oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u)
    (hb : oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u A) (hA : 0 ≤ A)
    {z : CPhase (n + m)}
    (hz : z ∈ oscDom D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ))
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun N : ℕ => ∑ j ∈ range N,
        ((t : ℂ) ^ j * ((j.factorial : ℂ)⁻¹)) * adPow φ j u z) atTop
      (𝓝 (u (flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) t z))) := by
  have F := H.toFlowHyp
  obtain ⟨-, hq0, hq1, -, -⟩ := osc_hat_ratio H
  set q := oscLieRatio m Φ (min (ρ * σ) (ρp * ρq)) with hq
  have hz1 : z ∈ gaugeInterior F.W (oscO (m := m) D r rp rq S ρ ρp ρq σ) (1 / 2) :=
    fun w hw => F.one hz w (hw.trans (by norm_num))
  have hu1 : DifferentiableOn ℂ u (oscO (m := m) D r rp rq S ρ ρp ρq σ) := hu.1
  have htraj : ∀ s ∈ Icc (-1 : ℝ) 1, flow (KAM.hamiltonianVectorFieldℂ φ)
      (oscO (m := m) D r rp rq S ρ ρp ρq σ) s z ∈ oscO (m := m) D r rp rq S ρ ρp ρq σ :=
    fun s hs => oscDom_mono (by linarith [H.widths.1]) (by linarith [H.widths.2.2.1])
      (by linarith [H.widths.2.2.2.2.1]) (by linarith [H.widths.2.2.2.2.2.2.1])
      (osc_trajectory_hat H z hz s hs)
  have hab : |t| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  set G : ℕ → ℝ → ℂ := fun j s => (t : ℂ) ^ j *
    adPow φ j u (flow (KAM.hamiltonianVectorFieldℂ φ)
      (oscO (m := m) D r rp rq S ρ ρp ρq σ) (s * t) z) with hG
  have hst : ∀ s ∈ Icc (0 : ℝ) 1, s * t ∈ Icc (-1 : ℝ) 1 := by
    intro s hs
    have h1 : |s * t| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hs.1]; nlinarith [hs.2, abs_nonneg t]
    exact ⟨(abs_le.1 h1).1, (abs_le.1 h1).2⟩
  have hder : ∀ j, ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (G j) (G (j + 1) s) s := by
    intro j s hs
    have h1 := hasDerivAt_adPow_flow F.φ_diff F.smallField (isOpen_oscDom _ _ _ _ _)
      subset_rfl hu1 hz1 htraj j (s * t) (hst s hs)
    have h2 : HasDerivAt (fun s : ℝ => s * t) t s := by
      simpa using (hasDerivAt_id s).mul_const t
    have h3 := (h1.scomp s h2).const_mul ((t : ℂ) ^ j)
    refine HasDerivAt.congr_deriv (f := G j) h3 ?_
    simp only [hG]
    rw [Complex.real_smul]
    ring
  have h0 : flow (KAM.hamiltonianVectorFieldℂ φ) (oscO (m := m) D r rp rq S ρ ρp ρq σ) 0 z = z :=
    (flow_a F.smallField hz1).1
  have hx0 : 0 ≤ |t| * (16 / 9 * q) := by positivity
  have hx1 : |t| * (16 / 9 * q) < 1 := by nlinarith [abs_nonneg t]
  have hbound : ∀ M : ℕ, ‖∑ j ∈ range (M + 1), ((t : ℂ) ^ j * ((j.factorial : ℂ)⁻¹)) *
      adPow φ j u z - u (flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscO (m := m) D r rp rq S ρ ρp ρq σ) t z)‖ ≤ (|t| * (16 / 9 * q)) ^ (M + 1) * A := by
    intro M
    have hmain := taylor_integral_aux hder M
    have hG01 : G 0 1 = u (flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscO (m := m) D r rp rq S ρ ρp ρq σ) t z) := by simp [hG, adPow]
    have hsum : ∑ j ∈ range (M + 1), ((j.factorial : ℂ)⁻¹) * G j 0 =
        ∑ j ∈ range (M + 1), ((t : ℂ) ^ j * ((j.factorial : ℂ)⁻¹)) * adPow φ j u z :=
      Finset.sum_congr rfl fun j _ => by simp only [hG, zero_mul, h0]; ring
    rw [hG01, hsum] at hmain
    set R := ∫ s in (0 : ℝ)..1, ((((1 - s) ^ M / (M.factorial : ℝ) : ℝ) : ℂ)) * G (M + 1) s
    have hwint : IntervalIntegrable (fun s : ℝ => (1 - s) ^ M / (M.factorial : ℝ))
        MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable; fun_prop
    have hI : ∫ s in (0 : ℝ)..1, (1 - s) ^ M / (M.factorial : ℝ) = 1 / ((M + 1).factorial : ℝ) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _ => hasDerivAt_taylorWeight M s) hwint]
      simp
    set B : ℝ := |t| ^ (M + 1) * (((M + 1).factorial : ℝ) * ((16 / 9 * q) ^ (M + 1) * A)) with hB
    have hR : ‖R‖ ≤ B / ((M + 1).factorial : ℝ) := by
      calc ‖R‖ ≤ ∫ s in (0 : ℝ)..1, (1 - s) ^ M / (M.factorial : ℝ) * B := by
            refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
              (Filter.Eventually.of_forall fun s hs => ?_) (hwint.mul_const B)
            have hw : 0 ≤ (1 - s) ^ M / (M.factorial : ℝ) := by
              have : 0 ≤ 1 - s := by linarith [hs.2]
              positivity
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
            refine mul_le_mul_of_nonneg_left ?_ hw
            have := osc_traj_bound H hu hb hA (N := M + 1) hz (hst s ⟨hs.1.le, hs.2⟩)
            simp only [hG, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, hB]
            exact mul_le_mul_of_nonneg_left this (by positivity)
        _ = B / ((M + 1).factorial : ℝ) := by
            rw [intervalIntegral.integral_mul_const, hI]; ring
    have hf : (0 : ℝ) < ((M + 1).factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos _)
    have e : B / ((M + 1).factorial : ℝ) = (|t| * (16 / 9 * q)) ^ (M + 1) * A := by
      rw [hB]; field_simp; ring
    have e2 : ∑ j ∈ range (M + 1), ((t : ℂ) ^ j * ((j.factorial : ℂ)⁻¹)) * adPow φ j u z -
        u (flow (KAM.hamiltonianVectorFieldℂ φ)
          (oscO (m := m) D r rp rq S ρ ρp ρq σ) t z) = -R := by
      rw [hmain]; ring
    rw [e2, norm_neg]
    exact hR.trans_eq e
  rw [← tendsto_add_atTop_iff_nat 1, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) hbound ?_
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one hx0 hx1).comp (tendsto_add_atTop_nat 1)
  simpa using this.mul_const A

theorem osc_series_eq (H : OscComposeData D r rp rq S ρ ρp ρq σ Φ φ)
    (hu : oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u)
    (hb : oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u A) (hA : 0 ≤ A) :
    ∀ z ∈ oscDom D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ),
      u (flow (KAM.hamiltonianVectorFieldℂ φ)
          (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) 1 z) =
        ∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * adPow φ j u z := by
  intro z hz
  have h1 := osc_taylor_t H hu hb hA hz (t := 1) ⟨by norm_num, le_rfl⟩
  obtain ⟨hs, -⟩ := osc_lie_series H hu hb hA
  have h2 := (hs z hz).tendsto_sum_nat
  simp only [Complex.ofReal_one, one_pow, one_mul] at h1
  exact tendsto_nhds_unique h1 h2

theorem osc_composition_t (H : OscComposeData D r rp rq S ρ ρp ρq σ Φ φ)
    (hu : oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u)
    (hb : oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u A) (hA : 0 ≤ A)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    let C := fun z => u (flow (KAM.hamiltonianVectorFieldℂ φ)
      (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) t z)
    oscClass D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) C ∧
    oscBound D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) C
      ((1 - |t| * oscTheta m Φ (min (ρ * σ) (ρp * ρq)))⁻¹ * A) := by
  intro C
  obtain ⟨-, hq0, hq1, hqθ, hθ1⟩ := osc_hat_ratio H
  set q := oscLieRatio m Φ (min (ρ * σ) (ρp * ρq)) with hq
  set θ := oscTheta m Φ (min (ρ * σ) (ρp * ρq)) with hθ
  have hab : |t| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  have hS2 : 0 < S - 2 * σ := by linarith [H.widths.2.2.2.2.2.2.1, H.widths.2.2.2.2.2.2.2]
  have hterm := osc_term_bound H hu hb hA
  set v : ℕ → CHam (n + m) := fun j z => (t : ℂ) ^ j * (((j.factorial : ℂ)⁻¹) * adPow φ j u z)
    with hv_def
  have hv : ∀ j, oscClass D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) (v j) :=
    fun j => (hterm j).1.const_mul _
  have hbv : ∀ j, oscBound D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) (v j)
      ((|t| * q) ^ j * A) := fun j => by
    have := osc_bound_const_mul ((t : ℂ) ^ j) (hterm j).2
    simpa [norm_pow, mul_pow, mul_assoc] using this
  have hx0 : 0 ≤ |t| * q := by positivity
  have hx1 : |t| * q < 1 := by nlinarith [abs_nonneg t]
  have hb0 : ∀ j : ℕ, 0 ≤ (|t| * q) ^ j * A := fun j => mul_nonneg (pow_nonneg hx0 j) hA
  have hs : Summable fun j : ℕ => (|t| * q) ^ j * A :=
    (summable_geometric_of_lt_one hx0 hx1).mul_right A
  obtain ⟨hcl, hbl, -⟩ := osc_bound_tsum hS2 hv hbv hb0 hs
  have hsum : ∑' j : ℕ, (|t| * q) ^ j * A = (1 - |t| * q)⁻¹ * A := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one hx0 hx1]
  have hCeq : ∀ z ∈ oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ),
      C z = ∑' j : ℕ, v j z := by
    intro z hz
    have h1 := osc_taylor_t H hu hb hA hz ht
    have hsz : Summable fun j : ℕ => v j z :=
      Summable.of_norm_bounded hs fun j => oscBound.norm_le (hv j) (hbv j) z hz
    have h2 := hsz.hasSum.tendsto_sum_nat
    have e : ∀ N : ℕ, ∑ j ∈ range N, ((t : ℂ) ^ j * ((j.factorial : ℂ)⁻¹)) * adPow φ j u z =
        ∑ j ∈ range N, v j z := fun N =>
      Finset.sum_congr rfl fun j _ => by simp only [hv_def]; ring
    simp only [e] at h1
    exact tendsto_nhds_unique h1 h2
  refine ⟨hcl.congr fun z hz => (hCeq z hz).symm, ?_⟩
  have hb' := oscBound.congr hS2 (fun z hz => (hCeq z hz).symm) hbl
  rw [hsum] at hb'
  have hθ0 : 0 ≤ θ := hq0.trans hqθ
  have hpos : 0 < 1 - |t| * θ := by nlinarith [abs_nonneg t]
  have hle : (1 - |t| * q)⁻¹ * A ≤ (1 - |t| * θ)⁻¹ * A :=
    mul_le_mul_of_nonneg_right
      (inv_anti₀ hpos (by nlinarith [abs_nonneg t, mul_le_mul_of_nonneg_left hqθ (abs_nonneg t)]))
      hA
  exact oscBound.mono_gen hb' le_rfl le_rfl le_rfl le_rfl hle

end OscComposition

end KAM.Planetary

end
