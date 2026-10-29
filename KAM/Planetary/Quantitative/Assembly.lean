/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.AssemblyTori
public import KAM.Planetary.WeakKAM.Evaluation
public import KAM.Planetary.WeakKAM.Displacement

/-!
# Quantitative weak KAM: assembly (P11C-Q6)

`weak_kam_quantitative` (`bpP:p11a:weak-kam-quantitative`, `stepP:p11a:qt-order` ... `qt-k6`):
the uniform displacement constant is chosen first from `(N, mu, tau, s, C1)`; the case `eps = 0`
is `zero_case`; for `eps > 0` the selection data of `d` and `h` is built, `evaluation_bilipschitz`
(with `free_radius`, `limit_torus`, `displacement`) supplies the family at the adapted schedule,
and its clauses are repackaged as a `QuantitativeFamily`.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology
namespace KAM.Planetary
open KAM KAM.Kepler KAM.ODE

variable {N : ℕ}

/-- The uniform displacement constant: `selectionCDelta` as a function of `(N,mu,tau,s,C1)`. -/
def p11c_cDelta (N mu : ℕ) (tau s C1 : ℝ) : ℝ :=
  selectionCQ N * 2 ^ N * (max 1 (16 / (π * s) *
    (Real.log (16 * selectionCN N / selectionVarpi N mu tau) +
      N * Real.log (32 * N / s)))) ^ tau * Real.sqrt (2 * N * C1) /
    (128 * π * (s / 24) ^ (N + 1))

theorem p11c_cDelta_eq (ds : SelectionData N) :
    selectionCDelta ds = p11c_cDelta N ds.μ ds.τ ds.strip ds.C₁ := rfl

theorem p11c_cDelta_pos {mu : ℕ} {tau s C1 : ℝ} (hN : 1 ≤ N) (hs : 0 < s) (hC : 1 ≤ C1) :
    0 < p11c_cDelta N mu tau s C1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hCQ : 0 < selectionCQ N := by unfold selectionCQ; positivity
  have hT : 0 < max 1 (16 / (π * s) *
    (Real.log (16 * selectionCN N / selectionVarpi N mu tau) +
      N * Real.log (32 * N / s))) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hC' : 0 < 2 * (N : ℝ) * C1 := by positivity
  unfold p11c_cDelta
  have := Real.sqrt_pos.2 hC'
  positivity

/-- Location of the upstream defect: the action displacement is below `2 * ϑ`. -/
theorem p11c_asm_action_lt (ds : SelectionData N) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible ds) (f : SelectionPhaseC N → ℂ)
    (o : SelectionDisplacement ds f ε) :
    ∀ b ∈ o.Kinf, ∀ θ, ‖(o.defect b θ).2‖ < 2 * ds.ϑ := by
  intro b hb θ
  obtain ⟨hadm, hs, -⟩ := free_radius ds ε he hsmall
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast ds.n_pos
  have hsq : 1 ≤ Real.sqrt N := by simpa using Real.sqrt_le_sqrt hn1
  have he' : 0 < (selectionAdapted ds ε).ε₀ := by show 0 < 2 * ε; positivity
  have hQ0 := wbud_Q₀_nonneg (weakBudgetCtx_of ds _ hadm rfl rfl rfl rfl rfl rfl hs he')
  have hw := hadm.weighted
  have hXi := disp_Xi_ge ds
  have hQ : selectionQ₀ (selectionAdapted ds ε) ≤ 1 := by nlinarith
  have hs0 : (selectionAdapted ds ε).s₀ ≤ ds.ϑ := by
    have h1 := hadm.radius
    have h2 := hadm.t_le
    have h3 : (selectionAdapted ds ε).t₀ ≤ ds.ϑ := h2.trans (div_le_self ds.theta_pos.le hsq)
    have h4 : (selectionAdapted ds ε).t₀ / (8 * N) ≤ (selectionAdapted ds ε).t₀ :=
      div_le_self hadm.t_pos.le (by linarith)
    linarith
  have := o.action_displacement b hb θ
  have hpos : 0 < ds.ϑ := ds.theta_pos
  nlinarith

end KAM.Planetary

end
