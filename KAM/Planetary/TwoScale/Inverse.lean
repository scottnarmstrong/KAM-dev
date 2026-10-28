/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Regularity

/-!
# Two-scale KAM: inverse function tools

`bpP:p3:ext-ift`, `bpP:p3:ext-neumann`, `bpP:p3:ball`: the multivariable global inverse on an open
set where a holomorphic injective map has bijective derivative (`ext_ift`), the Neumann inverse of
`id + B` for `‖B‖ ≤ 1/2` (`ext_neumann`), and the quantitative image-ball lemma (`ball`): path lift
along radial segments, closed-and-open continuation, and the convex mean-value bound for the local
inverse.
-/

public section

open Metric Filter Set
open scoped Topology ContDiff

namespace KAM.Planetary

/-- Multivariable global inverse on the open image; existence is proved, not assumed. -/
theorem ext_ift {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    {F : (Fin n → ℂ) → (Fin n → ℂ)} (hF : DifferentiableOn ℂ F Ω) (hinj : Set.InjOn F Ω)
    (hD : ∀ x ∈ Ω, Function.Bijective (fderiv ℂ F x)) :
    IsOpen (F '' Ω) ∧ ∃ G : (Fin n → ℂ) → (Fin n → ℂ),
      DifferentiableOn ℂ G (F '' Ω) ∧ MapsTo G (F '' Ω) Ω ∧
      (∀ x ∈ Ω, G (F x) = x) ∧ (∀ y ∈ F '' Ω, F (G y) = y) ∧
      ∀ y ∈ F '' Ω, ∀ v, fderiv ℂ G y (fderiv ℂ F (G y) v) = v := by
  classical
  have hsm : ContDiffOn ℂ ∞ F Ω := KAM.contDiffOn_infty_of_differentiableOn hΩ hF
  have hstrict : ∀ x ∈ Ω, HasStrictFDerivAt F (fderiv ℂ F x) x := fun x hx =>
    (hsm.contDiffAt (hΩ.mem_nhds hx)).hasStrictFDerivAt (by simp)
  have hequiv : ∀ x ∈ Ω, ∃ e : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ),
      (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ F x := fun x hx =>
    ⟨ContinuousLinearEquiv.ofBijective (fderiv ℂ F x)
      (LinearMap.ker_eq_bot.mpr (hD x hx).1) (LinearMap.range_eq_top.mpr (hD x hx).2), rfl⟩
  have hnhds : ∀ x ∈ Ω, F '' Ω ∈ 𝓝 (F x) := fun x hx => by
    obtain ⟨e, he⟩ := hequiv x hx
    have hs : HasStrictFDerivAt F (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) x := by
      rw [he]; exact hstrict x hx
    rw [← hs.map_nhds_eq_of_equiv]
    exact image_mem_map (hΩ.mem_nhds hx)
  set G : (Fin n → ℂ) → (Fin n → ℂ) := fun y => Function.invFunOn F Ω y with hG
  have hGl : ∀ x ∈ Ω, G (F x) = x := fun x hx => hinj.leftInvOn_invFunOn hx
  have hGm : ∀ y ∈ F '' Ω, G y ∈ Ω := fun y hy => Function.invFunOn_mem hy
  have hGr : ∀ y ∈ F '' Ω, F (G y) = y := fun y hy => Function.invFunOn_eq hy
  have hGd : ∀ x ∈ Ω, ∃ e : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ),
      (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ F x ∧
        HasStrictFDerivAt G (e.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) (F x) := fun x hx => by
    obtain ⟨e, he⟩ := hequiv x hx
    have hs : HasStrictFDerivAt F (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) x := by
      rw [he]; exact hstrict x hx
    refine ⟨e, he, hs.to_local_left_inverse ?_⟩
    filter_upwards [hΩ.mem_nhds hx] with z hz using hGl z hz
  refine ⟨?_, G, ?_, hGm, hGl, hGr, ?_⟩
  · rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hx, rfl⟩
    exact hnhds x hx
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, -, hs⟩ := hGd x hx
    exact hs.hasFDerivAt.differentiableAt.differentiableWithinAt
  · rintro _ ⟨x, hx, rfl⟩ v
    obtain ⟨e, he, hs⟩ := hGd x hx
    rw [hGl x hx, hs.hasFDerivAt.fderiv, ← he]
    simp

theorem ext_neumann {n : ℕ} (B : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) (hB : ‖B‖ ≤ 1 / 2) :
    ∃ A : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ),
      (A : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = ContinuousLinearMap.id ℂ _ + B ∧
      ‖(A.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))‖ ≤ 2 := by
  have hu : IsUnit (1 - (-B) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :=
    IsUnit.one_sub_of_norm_lt_one (by rw [norm_neg]; linarith)
  obtain ⟨u, hu⟩ := hu
  have hu' : (u : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = ContinuousLinearMap.id ℂ _ + B := by
    rw [hu]; simp [sub_neg_eq_add]; rfl
  let A : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearEquiv.equivOfInverse (u : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
      ((u⁻¹ : ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ))ˣ) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
      (fun v => by
        rw [← mul_apply_eq_comp, u.inv_mul]; rfl)
      (fun v => by
        rw [← mul_apply_eq_comp, u.mul_inv]; rfl)
  have hA : (A : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = ContinuousLinearMap.id ℂ _ + B := hu'
  refine ⟨A, hA, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun w => ?_
  have hv : A (A.symm w) = w := A.apply_symm_apply w
  have hAv : A (A.symm w) = A.symm w + B (A.symm w) := by
    have := congrArg (fun T : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => T (A.symm w)) hA
    simpa using this
  have h1 : ‖B (A.symm w)‖ ≤ 1 / 2 * ‖A.symm w‖ :=
    (B.le_opNorm _).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  have h2 : ‖A.symm w‖ - ‖B (A.symm w)‖ ≤ ‖w‖ := by
    calc ‖A.symm w‖ - ‖B (A.symm w)‖ ≤ ‖A.symm w + B (A.symm w)‖ := by
          have := norm_sub_norm_le (A.symm w) (-B (A.symm w))
          simpa [sub_neg_eq_add] using this
      _ = ‖w‖ := by rw [← hAv, hv]
  show ‖A.symm w‖ ≤ 2 * ‖w‖
  linarith

/-- Ball continuation includes positivity absent from the prose statement. -/
theorem ball {n : ℕ} {Ω : Set (Fin n → ℂ)} {F : (Fin n → ℂ) → (Fin n → ℂ)}
    (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω) (hinj : Set.InjOn F Ω)
    {m δ : ℝ} (hm : 0 < m) (hδ : 0 < δ)
    (hder : ∀ x ∈ Ω, ∃ A : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ),
      (A : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ F x ∧
        ‖(A.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))‖ ≤ m)
    {x₀ : Fin n → ℂ} (hx : Metric.ball x₀ δ ⊆ Ω) :
    Metric.ball (F x₀) (δ / m) ⊆ F '' Metric.ball x₀ δ ∧
    ∀ x ∈ Metric.ball x₀ δ, ∀ y ∈ Metric.ball x₀ δ,
      F x ∈ Metric.ball (F x₀) (δ / m) → F y ∈ Metric.ball (F x₀) (δ / m) →
      ‖x - y‖ ≤ m * ‖F x - F y‖ := by
  have hFb : DifferentiableOn ℂ F (Metric.ball x₀ δ) := hF.mono hx
  have hDb : ∀ z ∈ Metric.ball x₀ δ, Function.Bijective (fderiv ℂ F z) := fun z hz => by
    obtain ⟨A, hA, -⟩ := hder z (hx hz)
    rw [← hA]; exact A.bijective
  obtain ⟨hWopen, G, hGd, hGm, hGl, hGr, hGf⟩ :=
    ext_ift Metric.isOpen_ball hFb (hinj.mono hx) hDb
  set W := F '' Metric.ball x₀ δ with hW
  -- ball_inv: the inverse has derivative of norm `≤ m`
  have hGnorm : ∀ y ∈ W, ‖fderiv ℂ G y‖ ≤ m := by
    intro y hy
    obtain ⟨A, hA, hAm⟩ := hder (G y) (hx (hGm hy))
    have : fderiv ℂ G y = (A.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) := by
      refine ContinuousLinearMap.ext fun w => ?_
      have h := hGf y hy (A.symm w)
      rw [← hA] at h
      simpa using h
    rw [this]; exact hAm
  have hlip : ∀ s ⊆ W, Convex ℝ s → ∀ p ∈ s, ∀ q ∈ s, ‖G p - G q‖ ≤ m * ‖p - q‖ := by
    intro s hs hconv p hp q hq
    exact hconv.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hGd z (hs hz)).differentiableAt (hWopen.mem_nhds (hs hz)))
      (fun z hz => hGnorm z (hs hz)) hq hp
  have hcover : Metric.ball (F x₀) (δ / m) ⊆ W := by
    intro y hy
    set c := F x₀ with hc
    set d := ‖y - c‖ with hd
    have hdlt : d < δ / m := by simpa [dist_eq_norm] using hy
    have hR : m * d < δ := by rwa [lt_div_iff₀' hm] at hdlt
    have hd0 : 0 ≤ d := norm_nonneg _
    have hKsub : closedBall x₀ (m * d) ⊆ Metric.ball x₀ δ := closedBall_subset_ball hR
    have hKc : IsCompact (closedBall x₀ (m * d)) := isCompact_closedBall _ _
    let T : Set ℝ := {t | ∃ x, ‖x - x₀‖ ≤ m * t * d ∧ F x = c + t • (y - c)}
    have hTclosed : IsClosed (T ∩ Icc 0 1) := by
      let K : Set ((Fin n → ℂ) × ℝ) := closedBall x₀ (m * d) ×ˢ Icc 0 1
      have hK : IsCompact K := hKc.prod isCompact_Icc
      have hcont : ContinuousOn (fun p : (Fin n → ℂ) × ℝ => F p.1 - (c + p.2 • (y - c))) K :=
        ((hF.continuousOn.mono (hKsub.trans hx)).comp continuousOn_fst
          (fun p hp => hp.1)).sub (by fun_prop)
      have hZ1 : IsClosed (K ∩ (fun p : (Fin n → ℂ) × ℝ => F p.1 - (c + p.2 • (y - c))) ⁻¹' {0}) :=
        hcont.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton
      have hZ2 : IsClosed {p : (Fin n → ℂ) × ℝ | ‖p.1 - x₀‖ ≤ m * p.2 * d} :=
        isClosed_le (by fun_prop) (by fun_prop)
      have hZ := hZ1.inter hZ2
      have hZc : IsCompact ((K ∩ (fun p : (Fin n → ℂ) × ℝ => F p.1 - (c + p.2 • (y - c))) ⁻¹' {0}) ∩
          {p : (Fin n → ℂ) × ℝ | ‖p.1 - x₀‖ ≤ m * p.2 * d}) :=
        hK.of_isClosed_subset hZ (fun p hp => hp.1.1)
      have himg : T ∩ Icc 0 1 = Prod.snd '' ((K ∩ (fun p : (Fin n → ℂ) × ℝ =>
          F p.1 - (c + p.2 • (y - c))) ⁻¹' {0}) ∩
          {p : (Fin n → ℂ) × ℝ | ‖p.1 - x₀‖ ≤ m * p.2 * d}) := by
        ext t
        constructor
        · rintro ⟨⟨x, h1, h2⟩, ht⟩
          refine ⟨(x, t), ⟨⟨⟨?_, ht⟩, ?_⟩, h1⟩, rfl⟩
          · show x ∈ closedBall x₀ (m * d)
            rw [mem_closedBall_iff_norm]
            have : m * t * d ≤ m * d := by
              have := mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hm.le hd0)
              nlinarith
            exact h1.trans this
          · simp [h2]
        · rintro ⟨⟨x, t'⟩, ⟨⟨⟨-, ht⟩, hg⟩, h1⟩, rfl⟩
          refine ⟨⟨x, h1, ?_⟩, ht⟩
          have : F x - (c + t' • (y - c)) = 0 := hg
          exact sub_eq_zero.mp this
      rw [himg]
      exact (hZc.image continuous_snd).isClosed
    have h0 : (0 : ℝ) ∈ T := ⟨x₀, by simp, by simp [hc]⟩
    have hopen : ∀ t ∈ T ∩ Ico (0:ℝ) 1, T ∈ 𝓝[>] t := by
      rintro t ⟨⟨x, h1, h2⟩, ht0, ht1⟩
      have hxb : x ∈ Metric.ball x₀ δ := by
        refine hKsub ?_
        rw [mem_closedBall_iff_norm]
        have : m * t * d ≤ m * d := by
          have := mul_le_mul_of_nonneg_left ht1.le (mul_nonneg hm.le hd0)
          nlinarith
        exact h1.trans this
      have hxW : F x ∈ W := ⟨x, hxb, rfl⟩
      obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hWopen _ hxW
      have hpos : 0 < ε / (d + 1) := by positivity
      filter_upwards [Ioo_mem_nhdsGT (show t < t + ε / (d + 1) by linarith)] with s hs
      have hst : s - t < ε / (d + 1) := by linarith [hs.2]
      have hsd : ‖(s - t) • (y - c)‖ = (s - t) * d := by
        rw [norm_smul, Real.norm_of_nonneg (by linarith [hs.1])]
      have hlt : (s - t) * (d + 1) < ε := (lt_div_iff₀ (by positivity)).mp hst
      have hp : c + s • (y - c) ∈ Metric.ball (F x) ε := by
        rw [mem_ball_iff_norm, h2]
        have : c + s • (y - c) - (c + t • (y - c)) = (s - t) • (y - c) := by
          rw [sub_smul]; abel
        rw [this, hsd]
        nlinarith
      refine ⟨G (c + s • (y - c)), ?_, hGr _ (hεW hp)⟩
      have hl := hlip (Metric.ball (F x) ε) hεW (convex_ball _ _) _ hp _ (mem_ball_self hε)
      rw [hGl x hxb] at hl
      have hnorm : ‖c + s • (y - c) - F x‖ = (s - t) * d := by
        rw [h2]
        have : c + s • (y - c) - (c + t • (y - c)) = (s - t) • (y - c) := by
          rw [sub_smul]; abel
        rw [this, hsd]
      rw [hnorm] at hl
      calc ‖G (c + s • (y - c)) - x₀‖
          ≤ ‖G (c + s • (y - c)) - x‖ + ‖x - x₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ m * ((s - t) * d) + m * t * d := add_le_add hl h1
        _ = m * s * d := by ring
    have hall := hTclosed.Icc_subset_of_forall_mem_nhdsWithin h0 hopen
    obtain ⟨x, h1, h2⟩ := hall (show (1 : ℝ) ∈ Icc (0:ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
    refine ⟨x, hKsub ?_, ?_⟩
    · rw [mem_closedBall_iff_norm]; simpa using h1
    · rw [h2]; simp
  refine ⟨hcover, ?_⟩
  intro x hxb y hyb hFx hFy
  have h := hlip (Metric.ball (F x₀) (δ / m)) hcover (convex_ball _ _) _ hFx _ hFy
  rwa [hGl x hxb, hGl y hyb] at h

end KAM.Planetary
