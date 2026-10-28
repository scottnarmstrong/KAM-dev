/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.JetsPolar

/-!
# P Part 5: the fourth-order jet is unique (`bpP:p5:be-coef`)

`fourth_jet_unique`: an analytic function that is `o(‖x‖⁴)` at `0` has vanishing iterated
derivatives of every order `≤ 4` there (the Taylor polynomial is fixed by the little-o bound,
not merely its value). Proof: the one-variable statement along every line through `0`
(analytic order), then polarization for the symmetric iterated derivative.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-JET.
-/

@[expose] public noncomputable section

open Set Function Filter Topology

namespace KAM.Planetary

theorem iteratedDeriv_eq_zero_of_isLittleO {h : ℝ → ℝ} (hh : AnalyticAt ℝ h 0)
    (ho : ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ t : ℝ, |t| < delta → |h t| ≤ eps * |t| ^ 4) :
    ∀ i : ℕ, i < 5 → iteratedDeriv i h 0 = 0 := by
  have h5 : ((5 : ℕ) : ℕ∞) ≤ analyticOrderAt h 0 := by
    by_contra hlt
    replace hlt := not_le.1 hlt
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    have hn5 : n < 5 := by
      rw [← hn] at hlt
      exact_mod_cast hlt
    obtain ⟨g, hg, hg0, hev⟩ := hh.analyticOrderAt_eq_natCast.1 hn.symm
    have hg0' : 0 < |g 0| := abs_pos.2 hg0
    obtain ⟨δ, hδ, hb⟩ := ho (|g 0| / 4) (by positivity)
    have hgc : ∀ᶠ t in 𝓝 (0 : ℝ), |g 0| / 2 < |g t| := by
      have := hg.continuousAt.norm.eventually (lt_mem_nhds (a := |g 0| / 2)
        (show |g 0| / 2 < ‖g 0‖ by rw [Real.norm_eq_abs]; linarith))
      simpa only [Real.norm_eq_abs] using this
    have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < min δ 1 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (lt_min hδ one_pos)] with t ht
      simpa using ht
    obtain ⟨t, ⟨⟨h1, h2⟩, h3⟩, ht0⟩ := (((hev.and hgc).and hsmall).filter_mono
      (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))).and self_mem_nhdsWithin |>.exists
    have htpos : 0 < |t| := abs_pos.2 ht0
    have hb' := hb t (lt_of_lt_of_le h3 (min_le_left _ _))
    rw [h1, smul_eq_mul, abs_mul, abs_pow] at hb'
    have h4 : |t| ^ 4 = |t| ^ n * |t| ^ (4 - n) := by
      rw [← pow_add]; congr 1; omega
    rw [h4, mul_comm (|g 0| / 4), mul_assoc] at hb'
    have hb'' : |g t| ≤ |g 0| / 4 * |t| ^ (4 - n) := by
      have hp : 0 < |t| ^ n := by positivity
      have := hb'
      rw [sub_zero] at this
      nlinarith [mul_comm (|t| ^ n) (|g t|)]
    have hle : |t| ^ (4 - n) ≤ 1 :=
      pow_le_one₀ (abs_nonneg t) (le_of_lt (lt_of_lt_of_le h3 (min_le_right _ _)))
    nlinarith
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hh).1 h5

/-- General real normed-space form of `fourth_jet_unique`. -/
theorem fourth_jet_unique_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : AnalyticAt ℝ f 0)
    (ho : ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ x, ‖x‖ < delta → |f x| ≤ eps * ‖x‖ ^ 4) :
    ∀ k : ℕ, k ≤ 4 → iteratedFDeriv ℝ k f 0 = 0 := by
  intro k hk
  obtain ⟨U, hUa, hUo, hU0⟩ := eventually_nhds_iff.1 hf.eventually_analyticAt
  have hcd : ContDiffOn ℝ (k : ℕ∞) f U := fun x hx => (hUa x hx).contDiffAt.contDiffWithinAt
  refine eq_zero_of_diag_of_symm k _ (fun σ v => ?_) (fun y => ?_)
  · exact hf.contDiffAt.iteratedFDeriv_comp_perm v σ
  · set L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight y with hL
    have hLx : ∀ t, L t = t • y := fun t => by simp [hL]
    have hh : AnalyticAt ℝ (f ∘ L) 0 :=
      hf.comp_of_eq (L.analyticAt 0) (by simp [hLx])
    have hlt : ∀ i : ℕ, i < 5 → iteratedDeriv i (f ∘ L) 0 = 0 := by
      refine iteratedDeriv_eq_zero_of_isLittleO hh fun eps heps => ?_
      obtain ⟨δ, hδ, hb⟩ := ho (eps / (‖y‖ ^ 4 + 1)) (by positivity)
      refine ⟨δ / (‖y‖ + 1), by positivity, fun t ht => ?_⟩
      have hty : ‖t • y‖ < δ := by
        rw [norm_smul, Real.norm_eq_abs]
        rw [lt_div_iff₀ (by positivity)] at ht
        nlinarith [norm_nonneg y, abs_nonneg t]
      have := hb _ hty
      simp only [Function.comp, hLx]
      refine this.trans ?_
      rw [norm_smul, Real.norm_eq_abs, mul_pow]
      have h1 : eps / (‖y‖ ^ 4 + 1) * ‖y‖ ^ 4 ≤ eps := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [pow_nonneg (norm_nonneg y) 4]
      calc eps / (‖y‖ ^ 4 + 1) * (|t| ^ 4 * ‖y‖ ^ 4)
          = (eps / (‖y‖ ^ 4 + 1) * ‖y‖ ^ 4) * |t| ^ 4 := by ring
        _ ≤ eps * |t| ^ 4 := mul_le_mul_of_nonneg_right h1 (by positivity)
    have hcomp := iteratedFDeriv_comp_clm_of_isOpen hUo hcd L (x := 0)
      (by simpa [hLx] using hU0) (le_refl k)
    have h1 := hlt k (by omega)
    rw [iteratedDeriv_eq_iteratedFDeriv, hcomp] at h1
    simpa [hLx] using h1

/-- `o(norm x^4)` fixes all analytic Taylor coefficients through degree four. -/
theorem fourth_jet_unique {N : ℕ} {f : (Fin N → ℝ) → ℝ}
    (hf : AnalyticAt ℝ f 0)
    (ho : ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ x, ‖x‖ < delta → |f x| ≤ eps*‖x‖^4) :
    ∀ k : ℕ, k ≤ 4 → iteratedFDeriv ℝ k f 0 = 0 :=
  fourth_jet_unique_gen hf ho

end KAM.Planetary

end
