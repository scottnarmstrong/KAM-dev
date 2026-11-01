/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.NewHamLip
public import KAM.Wave.KamStep.ParamIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The transported time integral is a smoothing Hamiltonian (blueprint-W `bpW:w5:new-ham` (ii))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`newHam_integral_smoothing`: for a family `g_t` of smoothing Hamiltonians (`Dg_t = B(ι Zg_t, ·)`),
uniformly bounded and Lipschitz in `t`, the function `w ↦ ∫₀¹ g_t(φ^t w) dt` is holomorphic with
derivative `B(ι Y(w), ·)`, `Y(w) = ∫₀¹ (1 + N_t(w))⁻¹ Zg_t(φ^t w) dt` (holomorphic, `p_+`-valued).
-/

@[expose] public section

open Set Metric Filter Topology MeasureTheory intervalIntegral

namespace KAM.Wave

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  {ι : G →L[ℂ] F} {Z : F → G} {V U : Set F} {M δ : ℝ}

theorem differentiableOn_transNop (h : FlowHyp (smoothField ι Z) V U M δ)
    (hZ : DifferentiableOn ℂ Z V) (hb : ∀ z ∈ V, ‖Z z‖ ≤ M) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    DifferentiableOn ℂ (fun w => transNop ι Z t w) U := by
  have h1 := differentiableOn_fderiv_of_holomorphic h.isOpen_U (differentiableOn_smoothDisp h hZ hb
      ht)
  exact h1.clm_comp (differentiableOn_const ι)

/-- **`∫₀¹ g_t ∘ φ^t` is a smoothing Hamiltonian** (`bpW:w5:new-ham` (ii), `n-field`). -/
theorem newHam_integral_smoothing (h : FlowHyp (smoothField ι Z) V U M δ)
    (hZ : DifferentiableOn ℂ Z V) (hb : ∀ z ∈ V, ‖Z z‖ ≤ M) (hι : ∀ g, ‖ι g‖ ≤ ‖g‖)
    (B : F →L[ℂ] F →L[ℂ] ℂ)
    (hskew : ∀ z ∈ V, ∀ x y, B (fderiv ℂ (smoothField ι Z) z x) y +
      B x (fderiv ℂ (smoothField ι Z) z y) = 0)
    {V₂ : Set F} (hV₂ : IsOpen V₂) {δ₂ : ℝ} (hδ₂ : 0 < δ₂) (hMδ₂ : M < δ₂)
    {U' : Set F} (hU' : IsOpen U') (hU'U : U' ⊆ U)
    (hballV₂ : ∀ w ∈ U', ∀ z ∈ ball w δ₂, ball z δ₂ ⊆ V₂) {q : ℝ} (hq : q < 1)
    (hN : ∀ w ∈ U', ∀ t ∈ Icc (0 : ℝ) 1, ‖transNop ι Z t w‖ ≤ q)
    {g : ℝ → F → ℂ} {Zg : ℝ → F → G} {Y0 Lt Gb Lg : ℝ} (hY0 : 0 ≤ Y0) (hLt : 0 ≤ Lt)
    (hGb : 0 ≤ Gb) (hLg : 0 ≤ Lg)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ V₂, HasFDerivAt (g t) (B (ι (Zg t z))) z)
    (hZg : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (Zg t) V₂)
    (hZgb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ V₂, ‖Zg t z‖ ≤ Y0)
    (hZgt : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, ∀ z ∈ V₂,
      ‖Zg t z - Zg t' z‖ ≤ Lt * |t - t'|)
    (hgb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ V₂, ‖g t z‖ ≤ Gb)
    (hgt : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, ∀ z ∈ V₂,
      ‖g t z - g t' z‖ ≤ Lg * |t - t'|) :
    DifferentiableOn ℂ (fun w => ∫ t in (0 : ℝ)..1, g t (holoFlow (smoothField ι Z) t w)) U' ∧
      DifferentiableOn ℂ (fun w => ∫ t in (0 : ℝ)..1, yfam ι Z Zg t w) U' ∧
      ∀ w ∈ U', HasFDerivAt (fun w => ∫ t in (0 : ℝ)..1, g t (holoFlow (smoothField ι Z) t w))
        ((B.comp ι) (∫ t in (0 : ℝ)..1, yfam ι Z Zg t w)) w := by
  have hq1 : ∀ w ∈ U', ∀ t ∈ Icc (0 : ℝ) 1, ‖transNop ι Z t w‖ < 1 := fun w hw t ht =>
    lt_of_le_of_lt (hN w hw t ht) hq
  have hL : 0 ≤ M / δ := div_nonneg h.M_pos.le h.delta_pos.le
  have hI : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Icc (-1 : ℝ) 1 := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  have hflow_ball : ∀ w ∈ U', ∀ t ∈ Icc (0 : ℝ) 1,
      holoFlow (smoothField ι Z) t w ∈ ball w δ₂ := by
    intro w hw t ht
    rw [mem_ball_iff_norm]
    refine lt_of_le_of_lt (norm_holoFlow_sub_le h (hU'U hw) (hI t ht)) ?_
    have : |t| ≤ 1 := abs_le.mpr ⟨(hI t ht).1, (hI t ht).2⟩
    nlinarith [h.M_pos]
  refine smoothing_integral hU' (B.comp ι) (P := fun t w => g t (holoFlow (smoothField ι Z) t w))
    (Y := fun t w => yfam ι Z Zg t w) (Lp := Gb / δ₂ * M + Lg)
    (Ly := ((Y0 / δ₂ * M + Lt) + M / δ * Real.exp (M / δ) * (Y0 / (1 - q))) / (1 - q))
    (by have := h.M_pos; have := h.delta_pos; positivity) ?_ ?_ ?_ ?_ ?_
  · -- Ly ≥ 0
    have := h.M_pos; have := h.delta_pos; have : 0 < 1 - q := by linarith
    positivity
  · -- derivative of the transported function
    intro t ht w hw
    have hwU := hU'U hw
    have hφmem : holoFlow (smoothField ι Z) t w ∈ V₂ :=
      hballV₂ w hw _ (hflow_ball w hw t ht) (mem_ball_self hδ₂)
    refine hasFDerivAt_comp_flow_smooth h hZ hb B hskew hwU (hI t ht) (Gf := g t) (Zg := Zg t)
      (hg t ht _ hφmem) ?_
    exact transSolve_spec (hq1 w hw t ht) _
  · -- holomorphy of the fields
    intro t ht
    intro w hw
    have hwU := hU'U hw
    have hNd : DifferentiableAt ℂ (fun w => transNop ι Z t w) w :=
      (differentiableOn_transNop h hZ hb (hI t ht)).differentiableAt (h.isOpen_U.mem_nhds hwU)
    have hφd : DifferentiableAt ℂ (holoFlow (smoothField ι Z) t) w :=
      ((holomorphicOn_holoFlow h (hI t ht)).differentiableAt (h.isOpen_U.mem_nhds hwU))
    have hφmem : holoFlow (smoothField ι Z) t w ∈ V₂ :=
      hballV₂ w hw _ (hflow_ball w hw t ht) (mem_ball_self hδ₂)
    have hZd : DifferentiableAt ℂ (Zg t) (holoFlow (smoothField ι Z) t w) :=
      (hZg t ht).differentiableAt (hV₂.mem_nhds hφmem)
    exact (differentiableAt_transSolve_apply hNd (hZd.comp w hφd) (hq1 w hw t
        ht)).differentiableWithinAt
  · -- Lipschitz in t of the scalar family
    intro w hw t ht t' ht'
    have hwU := hU'U hw
    have hgd : DifferentiableOn ℂ (g t) V₂ := fun z hz =>
      (hg t ht z hz).differentiableAt.differentiableWithinAt
    have hlip := lipschitz_of_margin hδ₂ hGb hV₂ hgd (hgb t ht) (convex_ball w δ₂)
      (hballV₂ w hw)
    have hflow := norm_flow_time_sub_le h hZ hb hι hwU (hI t ht) (hI t' ht')
    have hmem' : holoFlow (smoothField ι Z) t' w ∈ V₂ :=
      hballV₂ w hw _ (hflow_ball w hw t' ht') (mem_ball_self hδ₂)
    show ‖g t (holoFlow (smoothField ι Z) t w) - g t' (holoFlow (smoothField ι Z) t' w)‖ ≤ _
    calc _ = ‖(g t (holoFlow (smoothField ι Z) t w) - g t (holoFlow (smoothField ι Z) t' w)) +
          (g t (holoFlow (smoothField ι Z) t' w) - g t' (holoFlow (smoothField ι Z) t' w))‖ := by
            congr 1; abel
      _ ≤ _ := norm_add_le _ _
      _ ≤ Gb / δ₂ * ‖holoFlow (smoothField ι Z) t w - holoFlow (smoothField ι Z) t' w‖ +
            Lg * |t - t'| :=
          add_le_add (hlip _ (hflow_ball w hw t ht) _ (hflow_ball w hw t' ht'))
            (hgt t ht t' ht' _ hmem')
      _ ≤ Gb / δ₂ * (M * |t - t'|) + Lg * |t - t'| := by gcongr
      _ = _ := by ring
  · intro w hw t ht t' ht'
    exact norm_yfam_time_sub_le h hZ hb hι hL hV₂ hδ₂ hMδ₂ hq hY0 hLt hZg hZgb hZgt (hU'U hw)
      (hballV₂ w hw) (hN w hw) ht ht'

end KAM.Wave
