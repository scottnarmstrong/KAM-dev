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

theorem p11c_asm_cell (H : Set (Fin N → ℝ)) : unitCube N ×ˢ H = selectionHalfCell H := by
  ext z
  simp only [unitCube, selectionHalfCell, mem_prod, mem_univ_pi, mem_ofPred_eq]
  tauto

theorem p11c_asm_closed_cell (H : Set (Fin N → ℝ)) :
    (Set.pi univ fun _ => Icc (0 : ℝ) 1) ×ˢ H = selectionClosedCell H := by
  ext z
  simp only [selectionClosedCell, mem_prod, mem_univ_pi, mem_ofPred_eq]
  tauto

theorem p11c_asm_zpow10 : (2 : ℝ) ^ (-10 : ℤ) = (2 : ℝ)⁻¹ ^ 10 := by norm_num
theorem p11c_asm_zpow18 : (2 : ℝ) ^ (-18 : ℤ) = (2 : ℝ)⁻¹ ^ 18 := by norm_num
theorem p11c_asm_zpow2N : (2 : ℝ) ^ (-(2 * N : ℤ)) = (2 : ℝ)⁻¹ ^ (2 * N) := by
  rw [zpow_neg, inv_pow]; norm_cast

/-- The lattice torus of the upstream evaluation over a good parameter. -/
theorem p11c_asm_lattice (ds : SelectionData N) (m0 : ℝ) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible ds) (f : SelectionPhaseC N → ℂ)
    (hpert : SelectionPerturbation ds f ε) (o : SelectionEvaluationOutput ds f ε)
    {b : Fin N → ℝ} (hb : b ∈ o.Kinf) (hbK : b ∈ ds.K) :
    IsLatticeTorus angleShift (realHamiltonian ds.h f) (p11c_realDomain (qbcOfSelection ds m0))
      (o.ωstar b) (selectionEvaluation o.defect b) := by
  have hc : (0 : ℝ) < 1 - (2 : ℝ)⁻¹ ^ 11 := by norm_num
  have hmem : ∀ θ, selectionEvaluation o.defect b θ ∈
      p11c_realDomain (qbcOfSelection ds m0) := fun θ => by
    refine ⟨b, hbK, ?_⟩
    have e : realInclusion N (selectionEvaluation o.defect b θ).2 -
        (fun i => (b i : ℂ)) = realInclusion N (o.defect b θ).2 := by
      funext i; simp [selectionEvaluation]
    show ‖realInclusion N (selectionEvaluation o.defect b θ).2 - fun i => (b i : ℂ)‖ <
      2 * ds.ϑ
    rw [e]
    refine lt_of_le_of_lt ?_ (p11c_asm_action_lt ds ε he hsmall f o.toSelectionDisplacement
      b hb θ)
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
      simpa using norm_le_pi_norm (o.defect b θ).2 i
  refine ⟨⟨o.analytic b hb, fun θ => ⟨hmem θ, ?_⟩⟩, fun θ k => ?_, fun θ θ' hθ => ?_,
    fun θ => ?_, fun θ v w => o.lagrangian b hb θ v w, fun θ t => o.orbit b hb θ t⟩
  · exact p11c_asm_diffAt (qbcOfSelection ds m0) ds.strip_pos ds.h f ds.holo hpert.holo (hmem θ)
  · ext i
    · simp [selectionEvaluation, angleShift, o.periodic b hb θ k]
      ring
    · simp [selectionEvaluation, angleShift, o.periodic b hb θ k]
  · refine ⟨0, ?_⟩
    have h1 := o.embedding_bound b hb θ θ'
    rw [hθ, sub_self, norm_zero] at h1
    have : ‖θ - θ'‖ ≤ 0 := by nlinarith [norm_nonneg (θ - θ')]
    have : θ = θ' := sub_eq_zero.1 (norm_le_zero_iff.1 this)
    subst this
    funext i
    simp
  · rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 := o.immersion_bound b hb θ v
    rw [hv, norm_zero] at h1
    have : ‖v‖ ≤ 0 := by nlinarith [norm_nonneg v]
    exact norm_le_zero_iff.1 this

/-- Positive branch at selection level: the family at the adapted schedule. -/
theorem p11c_asm_family (ds : SelectionData N) (m0 : ℝ)
    (hv : (qbcOfSelection ds m0).NumericalValid) (hM : selectionM₀ ds ≤ m0)
    (f : SelectionPhaseC N → ℂ) (ε : ℝ) (he : 0 < ε)
    (hth : ε ≤ thresholds (qbcOfSelection ds m0)) (hpert : SelectionPerturbation ds f ε) :
    Nonempty (QuantitativeFamily (qbcOfSelection ds m0) (realHamiltonian ds.h f)
      (selectionCDelta ds) ε) := by
  have hsmall : ε ≤ selectionAdmissible ds := hth.trans (polyBudget_threshold_le hv hM)
  obtain ⟨o⟩ := evaluation_bilipschitz ds ε he hsmall f hpert
  have hg : (qbcOfSelection ds m0).gamma = selectionGamma ds := qbc_gamma_sel ds m0 ds.beta_pos
  have hHK : ∀ b ∈ o.Hinf, b ∈ ds.K := fun b hb => by
    rw [o.Hinf_eq] at hb; exact hb.1
  have hbK : ∀ b ∈ o.Hinf, b ∈ o.Kinf := fun b hb => o.H_subset hb
  have hsel : ∀ (b θ : Fin N → ℝ), selectionEvaluation o.defect b θ - (θ, b) = o.defect b θ :=
    fun b θ => by simp [selectionEvaluation]
  refine ⟨QuantitativeFamily.mk o.Hinf (selectionEvaluation o.defect) o.ωstar o.compact_H hHK ?_
    (fun b hb => p11c_asm_lattice ds m0 ε he hsmall f hpert o (hbK b hb) (hHK b hb))
    (fun b hb => ?_) (fun b hb θ => ?_) (fun b hb b' hb' θ θ' => ?_)
    (fun b hb b' hb' θ θ' => ?_) ?_ ?_ ?_⟩
  · exact tsub_le_iff_right.1 o.measure_H
  · rw [hg]
    exact o.diophantine b hb
  · rw [hsel, p11c_displacement, hg]
    refine le_min ?_ ?_
    · rw [p11c_asm_zpow18]; exact o.delta_absolute.trans' (o.displacement b (hbK b hb) θ)
    · exact (o.displacement b (hbK b hb) θ).trans o.delta_power
  · rw [p11c_asm_zpow10]; exact (o.bilipschitz b (hbK b hb) b' (hbK b' hb') θ θ').1
  · rw [p11c_asm_zpow10]; exact (o.bilipschitz b (hbK b hb) b' (hbK b' hb') θ θ').2
  · show MeasurableSet ((fun z : Phase N => selectionEvaluation o.defect z.2 z.1) ''
      (unitCube N ×ˢ o.Hinf))
    rw [p11c_asm_cell]
    exact o.image_measurable _ o.compact_H o.H_subset
  · show ENNReal.ofReal ((2 : ℝ) ^ (-(2 * N : ℤ))) * volume o.Hinf ≤ volume
      ((fun z : Phase N => selectionEvaluation o.defect z.2 z.1) '' (unitCube N ×ˢ o.Hinf))
    rw [p11c_asm_cell, p11c_asm_zpow2N]
    exact o.measure_coarse _ o.compact_H o.H_subset
  · show IsCompact ((fun z : Phase N => selectionEvaluation o.defect z.2 z.1) ''
      ((Set.pi univ fun _ => Icc (0 : ℝ) 1) ×ˢ o.Hinf))
    rw [p11c_asm_closed_cell]
    exact o.closed_image_compact _ o.compact_H o.H_subset

end KAM.Planetary

end
