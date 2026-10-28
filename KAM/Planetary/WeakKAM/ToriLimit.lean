/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.ToriReal
public import KAM.Strip.AnalyticTaylor

/-! # P11B tori: frequencies and decay of the first jet

Source step `lt-field`/`lt-lim` inputs: the frequencies `ω_ν(b)` at a real parameter are real and
converge to `ω_*(b)`, and the Cauchy bounds `ε_ν/s_ν`, `ε_ν/r` of the first jet tend to zero.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

section Frequency
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}

/-- The derivative of the real-valued `h` in a real direction is real. -/
theorem tori_h_deriv_real (d : SelectionData n) {b : SelectionR n} (hb : b ∈ d.K) (i : Fin n) :
    (fderiv ℂ d.h (selectionReal b) (Pi.single i 1)).im = 0 := by
  have hopen : IsOpen (actionNbhd d.K (2 * d.ϑ)) := KAM.Head.isOpen_actionNbhd _ _
  have hmem : ∀ t : ℝ, |t| < 2 * d.ϑ →
      selectionReal (b + t • (Pi.single i 1 : SelectionR n)) ∈ actionNbhd d.K (2 * d.ϑ) :=
    fun t ht => ⟨b, hb, by
      have : selectionReal (b + t • (Pi.single i 1 : SelectionR n)) -
          (fun j => ((b j : ℝ) : ℂ)) = selectionReal (t • (Pi.single i 1 : SelectionR n)) := by
        funext j; simp [selectionReal]
      rw [this, norm_selectionReal]
      calc ‖t • (Pi.single i 1 : SelectionR n)‖ ≤ ‖t‖ * ‖(Pi.single i 1 : SelectionR n)‖ :=
            norm_smul_le _ _
        _ ≤ |t| * 1 := by
            refine mul_le_mul (by simp) ?_ (norm_nonneg _) (abs_nonneg _)
            refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
            by_cases h : j = i <;> simp [h]
        _ < 2 * d.ϑ := by simpa using ht⟩
  have hh : DifferentiableAt ℂ d.h (selectionReal b) :=
    d.holo.differentiableAt (hopen.mem_nhds (by simpa using hmem 0 (by simp [d.theta_pos])))
  have hγ : HasDerivAt (fun t : ℝ => selectionReal (b + t • (Pi.single i 1 : SelectionR n)))
      (selectionReal (Pi.single i 1 : SelectionR n)) 0 := by
    have : HasDerivAt (fun t : ℝ => b + t • (Pi.single i 1 : SelectionR n))
        (Pi.single i 1 : SelectionR n) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : SelectionR n)).const_add b
    exact ((KAM.realInclusion n).hasFDerivAt.comp_hasDerivAt (0 : ℝ) this)
  have hsingle : selectionReal (Pi.single i 1 : SelectionR n) =
      (Pi.single i 1 : SelectionC n) := by
    funext j; by_cases h : j = i <;> simp [selectionReal, h]
  have hg : HasDerivAt (fun t : ℝ => d.h (selectionReal (b + t • (Pi.single i 1 : SelectionR n))))
      (fderiv ℂ d.h (selectionReal b) (Pi.single i 1)) 0 := by
    have hh' : HasFDerivAt d.h (fderiv ℂ d.h (selectionReal b))
        (selectionReal (b + (0 : ℝ) • (Pi.single i 1 : SelectionR n))) := by
      simpa using hh.hasFDerivAt
    have h1 := (hh'.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) hγ
    rw [hsingle] at h1
    exact h1
  have him : HasDerivAt (fun t : ℝ =>
      (d.h (selectionReal (b + t • (Pi.single i 1 : SelectionR n)))).im)
      ((fderiv ℂ d.h (selectionReal b) (Pi.single i 1)).im) 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg
  have hz : HasDerivAt (fun t : ℝ =>
      (d.h (selectionReal (b + t • (Pi.single i 1 : SelectionR n)))).im) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq ?_
    have : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < 2 * d.ϑ := by
      have := (continuous_abs.tendsto (0 : ℝ))
      exact this.eventually (gt_mem_nhds (by simp [d.theta_pos]))
    filter_upwards [this] with t ht
    exact d.real _ (hmem t ht)
  exact him.unique hz

theorem tori_real_of_im {w : SelectionC n} (h : ∀ i, (w i).im = 0) :
    selectionReal (selectionRe w) = w := by
  funext i
  exact Complex.ext (by simp [selectionReal, selectionRe]) (by simp [selectionReal, h i])

variable (cx : WeakBudgetCtx d a) (L : SelectionLimit d f a) {b : SelectionR n}

theorem tori_mem_K (hb : b ∈ L.Kinf) (ν : ℕ) : b ∈ L.K ν := by
  have : b ∈ ⋂ j, L.K j := L.Kinf_eq ▸ hb
  exact mem_iInter.1 this ν

theorem tori_mem_d (hb : b ∈ L.Kinf) : b ∈ d.K := by
  have h0 := tori_mem_K L hb 0
  rwa [(L.chain 0).initial] at h0

include cx in
theorem tori_freq_real (hb : b ∈ L.Kinf) (ν : ℕ) :
    selectionReal (selectionRe (selectionFrequency d L.toSelectionChain ν (selectionReal b))) =
      selectionFrequency d L.toSelectionChain ν (selectionReal b) := by
  refine tori_real_of_im fun i => ?_
  have hΔ : ∀ j < ν, ∀ i, (L.Δω j (selectionReal b) i).im = 0 := fun j hj i => by
    have hm : selectionReal b ∈ actionNbhd (L.K j) (selectiont a j) :=
      ⟨b, tori_mem_K L hb j, by
        rw [show selectionReal b - (fun i => ((b i : ℝ) : ℂ)) = 0 from sub_self _, norm_zero]
        exact wbud_t_pos cx j⟩
    rw [(L.chain ν).real j hj b hm]
    simp [selectionReal]
  unfold selectionFrequency
  simp only [Pi.add_apply, Complex.add_im, Finset.sum_apply, Complex.im_sum]
  rw [tori_h_deriv_real d (tori_mem_d L hb) i, zero_add]
  exact Finset.sum_eq_zero fun j hj => hΔ j (Finset.mem_range.1 hj) i

include cx in
theorem tori_freq_tendsto (hb : b ∈ L.Kinf) :
    Tendsto (fun ν => selectionFrequency d L.toSelectionChain ν (selectionReal b)) atTop
      (𝓝 (selectionReal (L.ωstar b))) := by
  have h := L.frequency_uniform.tendsto_at hb
  have hc : Continuous (selectionRealLI n) := (selectionRealLI n).continuous
  have h2 := (hc.tendsto _).comp h
  refine h2.congr fun ν => ?_
  simp only [Function.comp_apply, selectionRealLI_apply]
  exact tori_freq_real cx L hb ν

include cx in
/-- The Cauchy bounds `ε_ν/s_ν` and `ε_ν/r` of the first jet tend to zero. -/
theorem tori_jet_small :
    Tendsto (fun ν => selectionε a ν / (selections a ν / 2) + selectionε a ν / (a.strip / 4))
      atTop (𝓝 0) := by
  have h := cx.hyp
  obtain ⟨hq, hq5, -, -, hρ⟩ := schedule_ratios h.hn h.hμ h.hτ
  obtain ⟨hv0, hv1⟩ := selectionVarpi_pos_le_one n a.μ h.hτ
  have hρdef : selectionVarrho n a.μ a.τ = selectionVarpi n a.μ a.τ / selectionQ n a.μ a.τ :=
    rfl
  have hρ0 : 0 ≤ selectionVarpi n a.μ a.τ / selectionQ n a.μ a.τ := by positivity
  have hρ1 : selectionVarpi n a.μ a.τ / selectionQ n a.μ a.τ < 1 := by
    rw [← hρdef]
    refine hρ.trans_lt ?_
    have : (2 : ℝ) ^ (-(a.τ + 1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith [h.hτ])
    linarith
  have hQ1 : selectionQ n a.μ a.τ < 1 := by
    have : (2 : ℝ)⁻¹ ^ 5 = 1 / 32 := by norm_num
    linarith
  have hv : selectionVarpi n a.μ a.τ < 1 := by
    have := (div_lt_one hq).1 hρ1
    linarith
  have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  have h3 := tendsto_pow_atTop_nhds_zero_of_lt_one hv0.le hv
  have e1 : ∀ ν, selectionε a ν / (selections a ν / 2) = 2 * (a.ε₀ / a.s₀) *
      (selectionVarpi n a.μ a.τ / selectionQ n a.μ a.τ) ^ ν := fun ν => by
    have hs0 := h.hs
    unfold selectionε selections
    rw [div_pow]
    field_simp
  have e2 : ∀ ν, selectionε a ν / (a.strip / 4) =
      4 * a.ε₀ / a.strip * selectionVarpi n a.μ a.τ ^ ν := fun ν => by
    have := h.hstrip
    unfold selectionε
    field_simp
  simp only [e1, e2]
  have := (h1.const_mul (2 * (a.ε₀ / a.s₀))).add (h3.const_mul (4 * a.ε₀ / a.strip))
  simpa using this

end Frequency

end KAM.Planetary

end
