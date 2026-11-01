/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorOneVar
public import KAM.Wave.Analytic.HoloAnalytic
public import KAM.Wave.KamStep.HoloFderiv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Taylor coefficients commute with a parameter derivative (blueprint-W `bpW:w5:taylor`, step `t-field`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

For a scalar function `Φ` analytic on an open set `S ∋ 0` of `ℂ²`, the Taylor coefficients of order
`k ≤ 2` of `t ↦ Φ(t e₀ + ε e₁)` are differentiable in `ε` at `0`, with derivative the `k`-th Taylor
coefficient of `t ↦ ∂_ε Φ(t e₀)` (mixed partial derivatives of an analytic function commute).
-/

@[expose] public section

open Filter Topology

namespace KAM.Wave

/-- The coordinate vectors of `ℂ²`. -/
noncomputable abbrev e0 : Fin 2 → ℂ := Pi.single 0 1
noncomputable abbrev e1 : Fin 2 → ℂ := Pi.single 1 1

variable {S : Set (Fin 2 → ℂ)} {Φ : (Fin 2 → ℂ) → ℂ}

/-- Mixed partials of an analytic function commute. -/
theorem mixed_symm {G : (Fin 2 → ℂ) → ℂ} (hS : IsOpen S) (hG : AnalyticOnNhd ℂ G S)
    (v w : Fin 2 → ℂ) {q : Fin 2 → ℂ} (hq : q ∈ S) :
    fderiv ℂ (fun y => fderiv ℂ G y v) q w = fderiv ℂ (fun y => fderiv ℂ G y w) q v := by
  have h1 := hG.fderiv_of_isOpen hS q hq
  have hd : DifferentiableAt ℂ (fderiv ℂ G) q := h1.differentiableAt
  have hev : ∀ᶠ y in 𝓝 q, HasFDerivAt G (fderiv ℂ G y) y := by
    filter_upwards [hS.mem_nhds hq] with y hy
    exact ((hG y hy).differentiableAt).hasFDerivAt
  have hsym := second_derivative_symmetric_of_eventually (𝕜 := ℂ) hev hd.hasFDerivAt
  have e : ∀ u : Fin 2 → ℂ, fderiv ℂ (fun y => fderiv ℂ G y u) q =
      (ContinuousLinearMap.apply ℂ ℂ u).comp (fderiv ℂ (fderiv ℂ G) q) := by
    intro u
    exact ((ContinuousLinearMap.apply ℂ ℂ u).hasFDerivAt.comp q hd.hasFDerivAt).fderiv
  rw [e v, e w]
  simpa using hsym w v

theorem hasDerivAt_line {G : (Fin 2 → ℂ) → ℂ} {q v : Fin 2 → ℂ} {t : ℂ}
    (hG : DifferentiableAt ℂ G (q + t • v)) :
    HasDerivAt (fun s : ℂ => G (q + s • v)) (fderiv ℂ G (q + t • v) v) t := by
  have h1 : HasDerivAt (fun s : ℂ => q + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add q
  exact hG.hasFDerivAt.comp_hasDerivAt t h1

/-- The partial derivative functions of an analytic function are analytic. -/
theorem analyticOnNhd_partial {G : (Fin 2 → ℂ) → ℂ} (hS : IsOpen S) (hG : AnalyticOnNhd ℂ G S)
    (v : Fin 2 → ℂ) : AnalyticOnNhd ℂ (fun y => fderiv ℂ G y v) S := fun y hy =>
  (ContinuousLinearMap.apply ℂ ℂ v).analyticAt _ |>.comp (hG.fderiv_of_isOpen hS y hy)

theorem hasDerivAt_taylorCoeff_zero (hS : IsOpen S) (hΦ : AnalyticOnNhd ℂ Φ S) (h0 : (0 : Fin 2 → ℂ) ∈ S) :
    HasDerivAt (fun ε : ℂ => taylorCoeff (fun t : ℂ => Φ (t • e0 + ε • e1)) 0)
      (taylorCoeff (fun t : ℂ => fderiv ℂ Φ (t • e0) e1) 0) 0 := by
  have h := hasDerivAt_line (G := Φ) (q := 0) (v := e1) (t := 0) (by simpa using (hΦ 0 h0).differentiableAt)
  simpa [taylorCoeff] using h

theorem line_eventually_mem (hS : IsOpen S) (h0 : (0 : Fin 2 → ℂ) ∈ S) :
    ∀ᶠ ε in 𝓝 (0 : ℂ), ε • e1 ∈ S := by
  have hc : ContinuousAt (fun ε : ℂ => ε • e1) 0 := (continuous_id.smul continuous_const).continuousAt
  exact hc.eventually (hS.mem_nhds (by simpa using h0))

theorem hasDerivAt_taylorCoeff_one (hS : IsOpen S) (hΦ : AnalyticOnNhd ℂ Φ S)
    (h0 : (0 : Fin 2 → ℂ) ∈ S) :
    HasDerivAt (fun ε : ℂ => taylorCoeff (fun t : ℂ => Φ (t • e0 + ε • e1)) 1)
      (taylorCoeff (fun t : ℂ => fderiv ℂ Φ (t • e0) e1) 1) 0 := by
  have hD1 := analyticOnNhd_partial hS hΦ e0
  have hD2 := analyticOnNhd_partial hS hΦ e1
  -- α₁(ε) = ∂₀Φ(ε e₁)
  have hα : ∀ᶠ ε in 𝓝 (0 : ℂ), taylorCoeff (fun t : ℂ => Φ (t • e0 + ε • e1)) 1 =
      fderiv ℂ Φ (ε • e1) e0 := by
    filter_upwards [line_eventually_mem hS h0] with ε hε
    rw [taylorCoeff_one]
    have := hasDerivAt_line (G := Φ) (q := ε • e1) (v := e0) (t := 0)
      (by simpa using (hΦ _ hε).differentiableAt)
    have e : (fun t : ℂ => Φ (t • e0 + ε • e1)) = fun s : ℂ => Φ (ε • e1 + s • e0) := by
      funext t; rw [add_comm]
    rw [e]
    simpa using this.deriv
  have h1 : HasDerivAt (fun ε : ℂ => fderiv ℂ Φ (ε • e1) e0) (fderiv ℂ (fun y => fderiv ℂ Φ y e0) 0 e1) 0 := by
    have := hasDerivAt_line (G := fun y => fderiv ℂ Φ y e0) (q := 0) (v := e1) (t := 0)
      (by simpa using (hD1 0 h0).differentiableAt)
    simpa using this
  have hβ : taylorCoeff (fun t : ℂ => fderiv ℂ Φ (t • e0) e1) 1 =
      fderiv ℂ (fun y => fderiv ℂ Φ y e1) 0 e0 := by
    rw [taylorCoeff_one]
    have := hasDerivAt_line (G := fun y => fderiv ℂ Φ y e1) (q := 0) (v := e0) (t := 0)
      (by simpa using (hD2 0 h0).differentiableAt)
    simpa using this.deriv
  rw [hβ, ← mixed_symm hS hΦ e0 e1 h0]
  exact h1.congr_of_eventuallyEq hα

theorem line0_eventually_mem (hS : IsOpen S) (h0 : (0 : Fin 2 → ℂ) ∈ S) :
    ∀ᶠ t in 𝓝 (0 : ℂ), t • e0 ∈ S := by
  have hc : ContinuousAt (fun t : ℂ => t • e0) 0 := (continuous_id.smul continuous_const).continuousAt
  exact hc.eventually (hS.mem_nhds (by simpa using h0))

theorem taylorCoeff_two {g : ℂ → ℂ} : taylorCoeff g 2 = (2 : ℂ)⁻¹ * deriv (deriv g) 0 := by
  simp [taylorCoeff, iteratedDeriv_succ, iteratedDeriv_one, Nat.factorial]

theorem hasDerivAt_taylorCoeff_two (hS : IsOpen S) (hΦ : AnalyticOnNhd ℂ Φ S)
    (h0 : (0 : Fin 2 → ℂ) ∈ S) :
    HasDerivAt (fun ε : ℂ => taylorCoeff (fun t : ℂ => Φ (t • e0 + ε • e1)) 2)
      (taylorCoeff (fun t : ℂ => fderiv ℂ Φ (t • e0) e1) 2) 0 := by
  have hD1 := analyticOnNhd_partial hS hΦ e0
  have hD2 := analyticOnNhd_partial hS hΦ e1
  have hF1 : AnalyticOnNhd ℂ (fun y => fderiv ℂ (fun z => fderiv ℂ Φ z e0) y e0) S :=
    analyticOnNhd_partial hS hD1 e0
  -- α₂(ε) = ½ ∂₀∂₀Φ(ε e₁)
  have hα : ∀ᶠ ε in 𝓝 (0 : ℂ), taylorCoeff (fun t : ℂ => Φ (t • e0 + ε • e1)) 2 =
      (2 : ℂ)⁻¹ * fderiv ℂ (fun z => fderiv ℂ Φ z e0) (ε • e1) e0 := by
    filter_upwards [line_eventually_mem hS h0] with ε hε
    rw [taylorCoeff_two]
    congr 1
    have hin : ∀ᶠ t in 𝓝 (0 : ℂ), t • e0 + ε • e1 ∈ S := by
      have hc : ContinuousAt (fun t : ℂ => t • e0 + ε • e1) 0 :=
        ((continuous_id.smul continuous_const).add continuous_const).continuousAt
      exact hc.eventually (hS.mem_nhds (by simpa using hε))
    have hd1 : (deriv fun t : ℂ => Φ (t • e0 + ε • e1)) =ᶠ[𝓝 0]
        fun t : ℂ => fderiv ℂ Φ (t • e0 + ε • e1) e0 := by
      filter_upwards [hin] with t ht
      have := hasDerivAt_line (G := Φ) (q := ε • e1) (v := e0) (t := t)
        (by rw [add_comm]; exact (hΦ _ ht).differentiableAt)
      have e : (fun t : ℂ => Φ (t • e0 + ε • e1)) = fun s : ℂ => Φ (ε • e1 + s • e0) := by
        funext t; rw [add_comm]
      rw [e, this.deriv, add_comm]
    rw [hd1.deriv_eq]
    have := hasDerivAt_line (G := fun z => fderiv ℂ Φ z e0) (q := ε • e1) (v := e0) (t := 0)
      (by simpa using (hD1 _ hε).differentiableAt)
    have e : (fun t : ℂ => fderiv ℂ Φ (t • e0 + ε • e1) e0) =
        fun s : ℂ => fderiv ℂ Φ (ε • e1 + s • e0) e0 := by
      funext t; rw [add_comm]
    rw [e]
    simpa using this.deriv
  have h1 : HasDerivAt (fun ε : ℂ => (2 : ℂ)⁻¹ *
      fderiv ℂ (fun z => fderiv ℂ Φ z e0) (ε • e1) e0)
      ((2 : ℂ)⁻¹ * fderiv ℂ (fun y => fderiv ℂ (fun z => fderiv ℂ Φ z e0) y e0) 0 e1) 0 := by
    have := hasDerivAt_line (G := fun y => fderiv ℂ (fun z => fderiv ℂ Φ z e0) y e0) (q := 0)
      (v := e1) (t := 0) (by simpa using (hF1 0 h0).differentiableAt)
    simpa using this.const_mul (2 : ℂ)⁻¹
  -- β₂
  have hβ : taylorCoeff (fun t : ℂ => fderiv ℂ Φ (t • e0) e1) 2 =
      (2 : ℂ)⁻¹ * fderiv ℂ (fun y => fderiv ℂ (fun z => fderiv ℂ Φ z e1) y e0) 0 e0 := by
    rw [taylorCoeff_two]
    congr 1
    have hd1 : (deriv fun t : ℂ => fderiv ℂ Φ (t • e0) e1) =ᶠ[𝓝 0]
        fun t : ℂ => fderiv ℂ (fun z => fderiv ℂ Φ z e1) (t • e0) e0 := by
      filter_upwards [line0_eventually_mem hS h0] with t ht
      have := hasDerivAt_line (G := fun z => fderiv ℂ Φ z e1) (q := 0) (v := e0) (t := t)
        (by simpa using (hD2 _ ht).differentiableAt)
      simpa using this.deriv
    rw [hd1.deriv_eq]
    have hF2 : AnalyticOnNhd ℂ (fun y => fderiv ℂ (fun z => fderiv ℂ Φ z e1) y e0) S :=
      analyticOnNhd_partial hS hD2 e0
    have := hasDerivAt_line (G := fun y => fderiv ℂ (fun z => fderiv ℂ Φ z e1) y e0) (q := 0)
      (v := e0) (t := 0) (by simpa using (hF2 0 h0).differentiableAt)
    simpa using this.deriv
  -- symmetric identifications
  have hM : (fun y => fderiv ℂ (fun z => fderiv ℂ Φ z e1) y e0) =ᶠ[𝓝 (0 : Fin 2 → ℂ)]
      fun y => fderiv ℂ (fun z => fderiv ℂ Φ z e0) y e1 := by
    filter_upwards [hS.mem_nhds h0] with y hy
    exact mixed_symm hS hΦ e1 e0 hy
  rw [hβ, hM.fderiv_eq]
  have hsym := mixed_symm hS hD1 e0 e1 h0
  rw [← hsym]
  exact h1.congr_of_eventuallyEq hα

/-- **The sum of the Taylor coefficients of order `≤ 2` commutes with the parameter derivative.** -/
theorem hasDerivAt_taylorSum_param (hS : IsOpen S) (hΦ : AnalyticOnNhd ℂ Φ S)
    (h0 : (0 : Fin 2 → ℂ) ∈ S) :
    HasDerivAt (fun ε : ℂ => ∑ k ∈ Finset.range 3,
        taylorCoeff (fun t : ℂ => Φ (t • e0 + ε • e1)) k)
      (∑ k ∈ Finset.range 3, taylorCoeff (fun t : ℂ => fderiv ℂ Φ (t • e0) e1) k) 0 := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  exact ((hasDerivAt_taylorCoeff_zero hS hΦ h0).add (hasDerivAt_taylorCoeff_one hS hΦ h0)).add
    (hasDerivAt_taylorCoeff_two hS hΦ h0)

end KAM.Wave
