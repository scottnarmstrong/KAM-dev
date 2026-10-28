/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.IterationPred
public import KAM.Planetary.WeakKAM.FiniteDivisor

/-! # P11B iteration: the frequency of a finite chain

The gradient of the Hamiltonian is real at real points; the frequency `ω_ν = ∇h + ∑ Δω_j` of a
finite chain is holomorphic and real on the collar `K_ν + t_ν`, and `‖Dω_ν‖ ≤ 2 C₁` there.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

theorem selectionReal_eq_realInclusion (b : SelectionR n) :
    selectionReal b = KAM.realInclusion n b := by
  funext i
  simp [selectionReal]

/-- The complex gradient of a Hamiltonian that is real on real points is real there. -/
theorem selection_gradient_real (d : SelectionData n) {y : SelectionR n}
    (hy : selectionReal y ∈ actionNbhd d.K (2 * d.ϑ)) (i : Fin n) :
    (fderiv ℂ d.h (selectionReal y) (Pi.single i 1)).im = 0 := by
  have hU : IsOpen (actionNbhd d.K (2 * d.ϑ)) := p11_isOpen_actionNbhd d.K (2 * d.ϑ)
  have hd : HasFDerivAt d.h (fderiv ℂ d.h (selectionReal y)) (selectionReal y) :=
    (d.holo.differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  set ψ : ℝ → SelectionC n := fun x => selectionReal (y + x • Pi.single i 1) with hψ
  have hψe : ψ = fun x : ℝ => selectionReal y + x • (Pi.single i 1 : SelectionC n) := by
    funext x j
    by_cases hj : j = i <;> simp [hψ, selectionReal, hj]
  have hψd : HasDerivAt ψ (Pi.single i 1 : SelectionC n) 0 := by
    rw [hψe]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : SelectionC n)).const_add
      (selectionReal y)
  have hψ0 : ψ 0 = selectionReal y := by simp [hψ]
  have hφ := (hd.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hψd hψ0.symm
  have hφi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hφ
  have hev : ∀ᶠ x in 𝓝 (0 : ℝ), ψ x ∈ actionNbhd d.K (2 * d.ϑ) := by
    refine hψd.continuousAt.eventually_mem (hU.mem_nhds ?_)
    rw [hψ0]; exact hy
  have h0 : HasDerivAt (fun x : ℝ => Complex.imCLM ((d.h ∘ ψ) x)) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with x hx
    exact d.real _ hx
  have := hφi.unique h0
  simpa using this

section Chain
variable {d : SelectionData n} {a : SelectionSchedule n} (c : WeakBudgetCtx d a)
  {ch : SelectionChain n} {ν : ℕ} (hc : SelectionExtensionChain d a ch ν)
include c hc

theorem selection_collar_sub_V :
    actionNbhd (ch.K ν) (selectiont a ν) ⊆ actionNbhd d.K (2 * d.ϑ) := by
  have h0 := selection_chain_antitone hc (Nat.zero_le ν) (le_refl ν)
  rw [hc.initial] at h0
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast c.hyp.hn
  have hsq : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn
  have ht0 : selectiont a ν ≤ a.t₀ := by
    have := iter_t_anti c (Nat.zero_le ν)
    have e : selectiont a 0 = a.t₀ := by simp [selectiont]
    rwa [e] at this
  have hϑ := d.theta_pos
  have := c.adm.t_le
  have h2 : a.t₀ ≤ d.ϑ := this.trans (div_le_self hϑ.le hsq)
  exact selectionCollar_mono h0 (by linarith)

theorem selection_collar_mono_stage {i : ℕ} (hi : i ≤ ν) :
    actionNbhd (ch.K ν) (selectiont a ν) ⊆ actionNbhd (ch.K i) (selectiont a i) :=
  selectionCollar_mono (selection_chain_antitone hc hi le_rfl) (iter_t_anti c hi)

theorem selection_frequency_differentiableOn :
    DifferentiableOn ℂ (selectionFrequency d ch ν) (actionNbhd (ch.K ν) (selectiont a ν)) := by
  have hg := (selectionInitial_gradient_differentiableOn d).mono (selection_collar_sub_V c hc)
  unfold selectionFrequency
  refine DifferentiableOn.add hg ?_
  refine DifferentiableOn.fun_sum fun i hi => ?_
  have hi' : i < ν := Finset.mem_range.1 hi
  exact (hc.holomorphic i hi').mono (selection_collar_mono_stage c hc hi'.le)

theorem selection_frequency_real {b : SelectionR n}
    (hb : selectionReal b ∈ actionNbhd (ch.K ν) (selectiont a ν)) (i : Fin n) :
    (selectionFrequency d ch ν (selectionReal b) i).im = 0 := by
  unfold selectionFrequency
  simp only [Pi.add_apply, Finset.sum_apply, Complex.add_im, Complex.im_sum]
  rw [selection_gradient_real d (selection_collar_sub_V c hc hb) i]
  refine (zero_add _).trans (Finset.sum_eq_zero fun j hj => ?_)
  have hj' : j < ν := Finset.mem_range.1 hj
  have := hc.real j hj' b (selection_collar_mono_stage c hc hj'.le hb)
  rw [this]
  simp [selectionReal]

/-- `‖D ω_ν‖ ≤ 2 C₁` on the collar `K_ν + t_ν` (`(P_ν)(a)`). -/
theorem selection_frequency_derivative_le :
    ∀ b ∈ actionNbhd (ch.K ν) (selectiont a ν),
      ‖fderiv ℂ (selectionFrequency d ch ν) b‖ ≤ 2 * d.C₁ := by
  intro b hb
  have h := c.hyp
  have hU : ∀ i, IsOpen (actionNbhd (ch.K i) (selectiont a i)) := fun i =>
    p11_isOpen_actionNbhd _ _
  have hbV := selection_collar_sub_V c hc hb
  have hgrad : DifferentiableAt ℂ (fun z i => fderiv ℂ d.h z (Pi.single i 1)) b :=
    (selectionInitial_gradient_differentiableOn d).differentiableAt
      ((p11_isOpen_actionNbhd d.K (2 * d.ϑ)).mem_nhds hbV)
  have hsum : ∀ i ∈ Finset.range ν, DifferentiableAt ℂ (ch.Δω i) b := fun i hi =>
    ((hc.holomorphic i (Finset.mem_range.1 hi)).differentiableAt
      ((hU i).mem_nhds (selection_collar_mono_stage c hc (Finset.mem_range.1 hi).le hb)))
  have hfd : fderiv ℂ (selectionFrequency d ch ν) b =
      fderiv ℂ (fun z i => fderiv ℂ d.h z (Pi.single i 1)) b +
        ∑ i ∈ Finset.range ν, fderiv ℂ (ch.Δω i) b := by
    have e : selectionFrequency d ch ν = fun z =>
        (fun i => fderiv ℂ d.h z (Pi.single i 1)) + ∑ i ∈ Finset.range ν, ch.Δω i z := by
      funext z; simp [selectionFrequency]
    rw [e]
    rw [fderiv_fun_add hgrad (DifferentiableAt.fun_sum hsum), fderiv_fun_sum hsum]
  have hcol : ∀ i ∈ Finset.range ν, ‖fderiv ℂ (ch.Δω i) b‖ ≤
      4 * selectionε a i / (selections a i * selectiont a i) := by
    intro i hi
    have hi' : i < ν := Finset.mem_range.1 hi
    have ht : 0 < selectiont a i := wbud_t_pos c i
    have htν : selectiont a ν ≤ selectiont a i / 2 := by
      have := (schedule_props a h.hn h.hμ h.hτ h.hγ h.hT h.ht h.hs h.he h.hstrip h.hC
        (by have := h.inc; have := h.col; have := h.hC; have := h.ht; nlinarith) h.inc h.col
        i 0).2.2.1
      exact (iter_t_anti c (Nat.succ_le_of_lt hi')).trans this
    have hbi : b ∈ actionNbhd (ch.K i) (selectiont a i / 2) :=
      selectionCollar_mono (selection_chain_antitone hc hi'.le le_rfl) htν hb
    have hℓ : 0 ≤ selectionell a i := by
      have := wbud_s_pos h i
      have := wbud_ε_pos h i
      unfold selectionell; positivity
    have := param_cauchy (by linarith : 0 < selectiont a i / 2) (by linarith : selectiont a i / 2 <
      selectiont a i) hℓ (hc.holomorphic i hi') (fun z hz => hc.bound i hi' z hz) (j := 1)
      le_rfl b hbi
    rw [norm_iteratedFDeriv_one] at this
    refine this.trans (le_of_eq ?_)
    have hs := wbud_s_pos h i
    unfold selectionell
    field_simp
    ring
  have hsumle : ∑ i ∈ Finset.range ν, ‖fderiv ℂ (ch.Δω i) b‖ ≤ d.C₁ := by
    refine (Finset.sum_le_sum hcol).trans ?_
    exact (schedule_props a h.hn h.hμ h.hτ h.hγ h.hT h.ht h.hs h.he h.hstrip h.hC
      (by have := h.inc; have := h.col; have := h.hC; have := h.ht; nlinarith) h.inc h.col
      ν 0).2.2.2.2.2.2.2.2.2.1
  rw [hfd]
  calc _ ≤ ‖fderiv ℂ (fun z i => fderiv ℂ d.h z (Pi.single i 1)) b‖ +
        ‖∑ i ∈ Finset.range ν, fderiv ℂ (ch.Δω i) b‖ := norm_add_le _ _
    _ ≤ d.C₁ + d.C₁ := add_le_add (d.hessian b hbV)
        ((norm_sum_le _ _).trans hsumle)
    _ = 2 * d.C₁ := by ring

end Chain

end KAM.Planetary

end
