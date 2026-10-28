/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# Quadratic part: one-variable calculus along rays

Blueprint P, Part 8, `stepP:p8:qf-assembly` (package S8-Q): the second derivative of a function
along a ray is its Hessian form, and an analytic function that is `O(|s|^m)` has vanishing jet of
order `< m`.
-/

@[expose] public noncomputable section
open Set Filter Function Metric
open scoped Topology
namespace KAM.Planetary
namespace SecularForm

/-- The second derivative of `s ↦ f (s • w)` at `0` is the Hessian form of `f` at `0`. -/
theorem iteratedDeriv_two_ray {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f 0) (w : E) :
    iteratedDeriv 2 (fun s : ℝ => f (s • w)) 0 = fderiv ℝ (fderiv ℝ f) 0 w w := by
  have hL : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s • w) w s := fun s => by
    simpa using (hasDerivAt_id s).smul_const w
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hev : ∀ᶠ y in 𝓝 (0 : E), DifferentiableAt ℝ f y :=
    (hf.eventually (by norm_num)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hc : ContinuousAt (fun s : ℝ => s • w) 0 := (hL 0).continuousAt
  have hev' : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (s • w) :=
    hc.eventually (by simpa using hev)
  have hder : deriv (fun s : ℝ => f (s • w)) =ᶠ[𝓝 0] fun s => fderiv ℝ f (s • w) w := by
    filter_upwards [hev'] with s hs
    exact (hs.hasFDerivAt.comp_hasDerivAt s (hL s)).deriv
  have h0 : (0 : ℝ) • w = 0 := zero_smul _ _
  have hd2 : HasDerivAt (fun s : ℝ => fderiv ℝ f (s • w) w) (fderiv ℝ (fderiv ℝ f) 0 w w) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ f (s • w)) (fderiv ℝ (fderiv ℝ f) 0 w) 0 := by
      have h' : DifferentiableAt ℝ (fderiv ℝ f) ((0 : ℝ) • w) := by rw [h0]; exact hdf
      have := h'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hL 0)
      simp only [h0] at this
      exact this
    exact h1.clm_apply (hasDerivAt_const _ w) |>.congr_deriv (by simp)
  rw [iteratedDeriv_succ, iteratedDeriv_one, hder.deriv_eq]
  exact hd2.deriv

/-- An analytic function that is `O(|s|^m)` near `0` has vanishing derivatives of order `< m`. -/
theorem iteratedDeriv_eq_zero_of_bound {χ : ℝ → ℝ} (hχ : AnalyticAt ℝ χ 0) (m : ℕ) {K ε : ℝ}
    (hε : 0 < ε) (h : ∀ s : ℝ, |s| < ε → |χ s| ≤ K * |s| ^ m) :
    ∀ k < m, iteratedDeriv k χ 0 = 0 := by
  rw [← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hχ]
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨k, hk⟩ : ∃ k : ℕ, analyticOrderAt χ 0 = k := by
    have hne : analyticOrderAt χ 0 ≠ ⊤ := fun htop => by rw [htop] at hlt; exact absurd hlt (by simp)
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
    exact ⟨k, hk.symm⟩
  obtain ⟨g, hg, hg0, hfg⟩ := (hχ.analyticOrderAt_eq_natCast).1 hk
  have hkm : k < m := by rw [hk] at hlt; exact_mod_cast hlt
  have hgc : ContinuousAt g 0 := hg.continuousAt
  have hgpos : ∀ᶠ s in 𝓝 (0 : ℝ), |g 0| / 2 < |g s| := by
    have := hgc.abs.eventually (lt_mem_nhds (by linarith [abs_pos.2 hg0] : |g 0| / 2 < |g 0|))
    exact this
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), |g 0| / 2 * s ^ k ≤ K * s ^ m := by
    have hlt' : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < ε :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hε)
    filter_upwards [nhdsWithin_le_nhds hfg, nhdsWithin_le_nhds hgpos, hlt', self_mem_nhdsWithin]
      with s hs1 hs2 hs3 hs4
    have hs0 : 0 < s := hs4
    have hb := h s (by rw [abs_of_pos hs0]; exact hs3)
    rw [hs1, abs_of_pos hs0] at hb
    simp only [sub_zero, smul_eq_mul, abs_mul, abs_pow, abs_of_pos hs0] at hb
    calc |g 0| / 2 * s ^ k ≤ |g s| * s ^ k := by gcongr
      _ = s ^ k * |g s| := mul_comm _ _
      _ ≤ K * s ^ m := hb
  have hlim : Tendsto (fun s : ℝ => K * s ^ (m - k)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => K * s ^ (m - k)) (𝓝 0) (𝓝 (K * 0 ^ (m - k))) :=
      (continuous_const.mul (continuous_id.pow _)).tendsto 0
    rw [zero_pow (by omega), mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hpos : 0 < |g 0| / 2 := by linarith [abs_pos.2 hg0]
  have hev2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), K * s ^ (m - k) < |g 0| / 2 :=
    hlim (Iio_mem_nhds hpos)
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ := ((hsmall.and hev2).and self_mem_nhdsWithin).exists
  have hs0 : 0 < s := hs3
  have hpk : 0 < s ^ k := pow_pos hs0 k
  have hm : s ^ m = s ^ k * s ^ (m - k) := by rw [← pow_add]; congr 1; omega
  rw [hm] at hs1
  nlinarith

/-- The second derivative at `0` of `A + c s²`. -/
theorem iteratedDeriv_two_quadratic (A c : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => A + c * s ^ 2) 0 = 2 * c := by
  have h1 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => A + c * s ^ 2) (c * (2 * s)) s := fun s => by
    simpa using ((hasDerivAt_pow 2 s).const_mul c).const_add A
  have h2 : deriv (fun s : ℝ => A + c * s ^ 2) = fun s => c * (2 * s) :=
    funext fun s => (h1 s).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, h2]
  have : HasDerivAt (fun s : ℝ => c * (2 * s)) (c * 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).const_mul c
  rw [this.deriv]; ring

/-- The second derivative of an analytic function that is `A + c s² + O(|s|³)`. -/
theorem iteratedDeriv_two_of_bound {φ : ℝ → ℝ} (hφ : AnalyticAt ℝ φ 0) (A c : ℝ) {K ε : ℝ}
    (hε : 0 < ε) (h : ∀ s : ℝ, |s| < ε → |φ s - (A + c * s ^ 2)| ≤ K * |s| ^ 3) :
    iteratedDeriv 2 φ 0 = 2 * c := by
  have hp : AnalyticAt ℝ (fun s : ℝ => A + c * s ^ 2) 0 := by fun_prop
  have hχ : AnalyticAt ℝ (fun s : ℝ => φ s - (A + c * s ^ 2)) 0 := hφ.sub hp
  have h0 := iteratedDeriv_eq_zero_of_bound hχ 3 hε h 2 (by norm_num)
  have hsub : iteratedDeriv 2 (fun s : ℝ => φ s - (A + c * s ^ 2)) 0 =
      iteratedDeriv 2 φ 0 - iteratedDeriv 2 (fun s : ℝ => A + c * s ^ 2) 0 :=
    iteratedDeriv_sub (hφ.contDiffAt) (hp.contDiffAt)
  have hpoly : iteratedDeriv 2 (fun s : ℝ => A + c * s ^ 2) 0 = 2 * c :=
    iteratedDeriv_two_quadratic A c
  linarith

end SecularForm
end KAM.Planetary
end
