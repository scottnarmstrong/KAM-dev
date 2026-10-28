/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# P Part 5: scalar limits for the radius thresholds (`bpP:p5:rstar`)

`r^m (log 1/r)^q → 0` as `r → 0+`, the monotonicity of `r^2 (log 1/r)^q` below `e^{-q}`, and the
packaging of `∀ᶠ r in 𝓝[>] 0` into a uniform radius. Design
`docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-TH.
-/

@[expose] public noncomputable section

open Filter Topology Set

namespace KAM.Planetary

theorem tendsto_rpow_mul_log_rpow (m q : ℝ) (hm : 0 < m) :
    Tendsto (fun r : ℝ => r^m * (Real.log (1/r))^q) (𝓝[>] 0) (𝓝 0) := by
  have h := ((isLittleO_log_rpow_rpow_atTop q hm).tendsto_div_nhds_zero).comp
    tendsto_inv_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : 0 < r := hr
  simp only [Function.comp, one_div, Real.inv_rpow hr0.le, div_inv_eq_mul]
  ring

theorem le_log_inv_of_le_exp_neg {q r : ℝ} (hr0 : 0 < r) (hr : r ≤ Real.exp (-q)) :
    q ≤ Real.log (1/r) := by
  rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hr0]
  have := mul_le_mul_of_nonneg_left hr (Real.exp_pos q).le
  rw [← Real.exp_add] at this
  simpa using this

theorem eventually_lt_of_continuousAt {f : ℝ → ℝ} {c : ℝ} (hf : ContinuousAt f 0) (h0 : f 0 < c) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), f r < c :=
  (hf.eventually (gt_mem_nhds h0)).filter_mono nhdsWithin_le_nhds

theorem eventually_exists_radius {p : ℝ → Prop} (h : ∀ᶠ r in 𝓝[>] (0:ℝ), p r) :
    ∃ R : ℝ, 0 < R ∧ ∀ r, 0 < r → r < R → p r := by
  obtain ⟨u, hu, hs⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 h
  exact ⟨u, hu, fun r hr0 hru => hs ⟨hr0, hru⟩⟩

theorem sq_log_mono {r R q : ℝ} (hr : 0 < r) (hrR : r < R) (hq : 0 < q)
    (hqL : q ≤ Real.log (1/R)) :
    r^2 * (Real.log (1/r))^q ≤ R^2 * (Real.log (1/R))^q := by
  have hR : 0 < R := hr.trans hrR
  set L := Real.log (1/R) with hL
  have hL0 : 0 < L := hq.trans_le hqL
  set u := Real.log (R/r) with hu
  have hu0 : 0 ≤ u := Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith)
  have hM : Real.log (1/r) = L + u := by
    rw [hL, hu, ← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
  have hrR' : r = R * Real.exp (-u) := by
    rw [hu, Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  have hu1 : 0 ≤ u/L := by positivity
  have h1 : (L+u)^q = L^q * (1+u/L)^q := by
    rw [← Real.mul_rpow hL0.le (by positivity)]; congr 1; field_simp
  have h2 : (1+u/L)^q ≤ Real.exp u := by
    calc (1+u/L)^q ≤ (Real.exp (u/L))^q :=
          Real.rpow_le_rpow (by positivity) (by linarith [Real.add_one_le_exp (u/L)]) hq.le
      _ = Real.exp (u/L*q) := (Real.exp_mul _ _).symm
      _ ≤ Real.exp u := by
          apply Real.exp_le_exp.2
          have : q/L ≤ 1 := (div_le_one hL0).2 hqL
          calc u/L*q = u*(q/L) := by ring
            _ ≤ u*1 := mul_le_mul_of_nonneg_left this hu0
            _ = u := mul_one u
  have h3 : Real.exp (-u)^2 * (1+u/L)^q ≤ 1 := by
    have e : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have e1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    calc Real.exp (-u)^2 * (1+u/L)^q ≤ Real.exp (-u)^2 * Real.exp u :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.exp (-u) * (Real.exp (-u) * Real.exp u) := by ring
      _ ≤ 1 := by rw [e, mul_one]; exact e1
  have hLq : 0 ≤ R^2 * L^q := by positivity
  rw [hM, h1, hrR']
  calc (R * Real.exp (-u))^2 * (L^q * (1+u/L)^q)
      = (R^2 * L^q) * (Real.exp (-u)^2 * (1+u/L)^q) := by ring
    _ ≤ (R^2 * L^q) * 1 := mul_le_mul_of_nonneg_left h3 hLq
    _ = R^2 * L^q := mul_one _

end KAM.Planetary

end
