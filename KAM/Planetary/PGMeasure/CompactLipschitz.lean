/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.HasFastDiffeomorphism
public import KAM.Frozen.Planetary.Defs.FastFrequency
public import KAM.Planetary.PG.Setting

/-!
# P Part 4: derivative regularity, compact Lipschitz bounds, the frozen inverse
(`bpP:p4:ext-deriv`, `bpP:p4:lip-compact`, `bpP:p4:lip-inverse`)

`ext_deriv` is the classical regularity of analytic maps. `lip_compact` is the printed partial-C1
compact-pair estimate; `lip_compact_c1` is the separately named joint-C1 corollary (conditional
helper, not a substitute for the source result). `lip_inverse` extracts a Lipschitz constant and a
norm bound for the frozen inverse of `fastFrequency H0` on the image of `closure V`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P4-LI.
-/

public section

open Set Metric Filter Topology

namespace KAM.Planetary

/-- Classical derivative regularity used by P4. -/
theorem ext_deriv {p q : ℕ} {U : Set (Fin p → ℝ)} {f : (Fin p → ℝ) → Fin q → ℝ}
    (hf : AnalyticOnNhd ℝ f U) :
    AnalyticOnNhd ℝ (fderiv ℝ f) U ∧ ContDiffOn ℝ 1 f U :=
  ⟨hf.fderiv, hf.contDiffOn_of_completeSpace⟩

/-- Local uniform Lipschitz bound in the second variable near a point of `O`. -/
private theorem lip_local {p m q : ℕ}
    {O : Set ((Fin p → ℝ) × (Fin m → ℝ))} {f : (Fin p → ℝ) × (Fin m → ℝ) → Fin q → ℝ}
    (hO : IsOpen O)
    (hd : ∀ z ∈ O, DifferentiableAt ℝ (fun x => f (z.1,x)) z.2)
    (hdf : ContinuousOn (fun z => fderiv ℝ (fun x => f (z.1,x)) z.2) O)
    {z : (Fin p → ℝ) × (Fin m → ℝ)} (hz : z ∈ O) :
    ∃ ε > 0, ∃ M : ℝ, ∀ t ∈ ball z.1 ε, ∀ x ∈ ball z.2 ε, ∀ y ∈ ball z.2 ε,
      ‖f (t,x) - f (t,y)‖ ≤ M * ‖x - y‖ := by
  have hc : ContinuousAt (fun z => fderiv ℝ (fun x => f (z.1,x)) z.2) z :=
    (hdf z hz).continuousAt (hO.mem_nhds hz)
  have h1 : ∀ᶠ w in 𝓝 z, w ∈ O ∧
      ‖fderiv ℝ (fun x => f (w.1,x)) w.2‖ < ‖fderiv ℝ (fun x => f (z.1,x)) z.2‖ + 1 :=
    (hO.eventually_mem hz).and (hc.norm.eventually (gt_mem_nhds (lt_add_one _)))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 h1
  refine ⟨ε, hε, ‖fderiv ℝ (fun x => f (z.1,x)) z.2‖ + 1, fun t ht x hx y hy => ?_⟩
  have hmem : ∀ x ∈ ball z.2 ε, (t, x) ∈ ball z ε := fun x hx => by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨Metric.mem_ball.1 ht, Metric.mem_ball.1 hx⟩
  have hbt : ∀ x ∈ ball z.2 ε, ‖fderiv ℝ (fun x => f (t,x)) x‖ ≤
      ‖fderiv ℝ (fun x => f (z.1,x)) z.2‖ + 1 := fun x hx => (hball _ (hmem x hx)).2.le
  have hdt : ∀ x ∈ ball z.2 ε, DifferentiableAt ℝ (fun x => f (t,x)) x := fun x hx =>
    hd _ (hball _ (hmem x hx)).1
  exact Convex.norm_image_sub_le_of_norm_fderiv_le hdt hbt (convex_ball _ _) hy hx

/-- Exact partial-C1 source version. -/
theorem lip_compact {p m q : ℕ} {T : Set (Fin p → ℝ)} {X : Set (Fin m → ℝ)}
    {O : Set ((Fin p → ℝ) × (Fin m → ℝ))} {f : (Fin p → ℝ) × (Fin m → ℝ) → Fin q → ℝ}
    (hT : IsCompact T) (hX : IsCompact X) (hO : IsOpen O) (hsub : T ×ˢ X ⊆ O)
    (hf : ContinuousOn f O)
    (hd : ∀ z ∈ O, DifferentiableAt ℝ (fun x => f (z.1,x)) z.2)
    (hdf : ContinuousOn (fun z => fderiv ℝ (fun x => f (z.1,x)) z.2) O) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ T, ∀ x ∈ X, ∀ y ∈ X, ‖f (t,x)-f (t,y)‖ ≤ L*‖x-y‖ := by
  by_contra hcon
  push Not at hcon
  have hch : ∀ n : ℕ, ∃ w : (Fin p → ℝ) × (Fin m → ℝ) × (Fin m → ℝ),
      w ∈ T ×ˢ (X ×ˢ X) ∧ (n : ℝ) * ‖w.2.1 - w.2.2‖ < ‖f (w.1, w.2.1) - f (w.1, w.2.2)‖ := by
    intro n
    obtain ⟨t, ht, x, hx, y, hy, h⟩ := hcon n (Nat.cast_nonneg n)
    exact ⟨(t, x, y), ⟨ht, hx, hy⟩, h⟩
  choose w hw hlt using hch
  obtain ⟨C, hC⟩ := (hT.prod hX).exists_bound_of_continuousOn (hf.mono hsub)
  obtain ⟨w0, hw0, φ, hφ, hlim⟩ := (hT.prod (hX.prod hX)).tendsto_subseq hw
  obtain ⟨t0, x0, y0⟩ := w0
  have h1 : Tendsto (fun n => (w (φ n)).1) atTop (𝓝 t0) :=
    (continuous_fst.tendsto _).comp hlim
  have h2 : Tendsto (fun n => (w (φ n)).2.1) atTop (𝓝 x0) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hlim
  have h3 : Tendsto (fun n => (w (φ n)).2.2) atTop (𝓝 y0) :=
    ((continuous_snd.comp continuous_snd).tendsto _).comp hlim
  -- the pairs collapse to a point
  have hbd : ∀ n : ℕ, (n : ℝ) * ‖(w (φ n)).2.1 - (w (φ n)).2.2‖ ≤ 2 * C := by
    intro n
    have hz := hw (φ n)
    have hx := hC _ (show ((w (φ n)).1, (w (φ n)).2.1) ∈ T ×ˢ X from ⟨hz.1, hz.2.1⟩)
    have hy := hC _ (show ((w (φ n)).1, (w (φ n)).2.2) ∈ T ×ˢ X from ⟨hz.1, hz.2.2⟩)
    have hle : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    have hn := hlt (φ n)
    have := norm_sub_le (f ((w (φ n)).1, (w (φ n)).2.1)) (f ((w (φ n)).1, (w (φ n)).2.2))
    nlinarith [norm_nonneg ((w (φ n)).2.1 - (w (φ n)).2.2)]
  have hzero : Tendsto (fun n => ‖(w (φ n)).2.1 - (w (φ n)).2.2‖) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat (2 * C))
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn']
    linarith [hbd n]
  have hxy : x0 = y0 := by
    have := tendsto_nhds_unique (h2.sub h3).norm hzero
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  subst hxy
  have hz0 : (t0, x0) ∈ O := hsub ⟨hw0.1, hw0.2.1⟩
  obtain ⟨ε, hε, M, hM⟩ := lip_local hO hd hdf hz0
  have e1 := h1.eventually (Metric.ball_mem_nhds t0 hε)
  have e2 := h2.eventually (Metric.ball_mem_nhds x0 hε)
  have e3 := h3.eventually (Metric.ball_mem_nhds x0 hε)
  obtain ⟨n, hn1, hn2, hn3, hn4⟩ := (e1.and (e2.and (e3.and (eventually_ge_atTop ⌈M⌉₊)))).exists
  have hle : M ≤ (φ n : ℝ) :=
    (Nat.le_ceil M).trans (by exact_mod_cast hn4.trans (hφ.id_le n))
  have := hM _ hn1 _ hn2 _ hn3
  have hlt2 := hlt (φ n)
  nlinarith [norm_nonneg ((w (φ n)).2.1 - (w (φ n)).2.2)]

/-- Joint C1 is stronger input than the printed partial-C1 premise; conditional helper only. -/
theorem lip_compact_c1 {p m q : ℕ} {T : Set (Fin p → ℝ)} {X : Set (Fin m → ℝ)}
    {O : Set ((Fin p → ℝ) × (Fin m → ℝ))} {f : (Fin p → ℝ) × (Fin m → ℝ) → Fin q → ℝ}
    (hT : IsCompact T) (hX : IsCompact X) (hO : IsOpen O) (hsub : T ×ˢ X ⊆ O)
    (hf : ContDiffOn ℝ 1 f O) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ T, ∀ x ∈ X, ∀ y ∈ X, ‖f (t,x)-f (t,y)‖ ≤ L*‖x-y‖ := by
  have hD : ∀ z ∈ O, HasFDerivAt (fun x => f (z.1,x))
      ((fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin m → ℝ))) z.2 := by
    intro z hz
    have hdf : DifferentiableAt ℝ f z :=
      (hf.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds hz)
    have hi : HasFDerivAt (fun x : Fin m → ℝ => ((z.1, x) : (Fin p → ℝ) × (Fin m → ℝ)))
        (ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin m → ℝ)) z.2 :=
      (hasFDerivAt_prodMk_right z.1 z.2)
    exact (show HasFDerivAt f (fderiv ℝ f z) (z.1, z.2) from hdf.hasFDerivAt).comp z.2 hi
  refine lip_compact hT hX hO hsub hf.continuousOn (fun z hz => (hD z hz).differentiableAt) ?_
  have hc := hf.continuousOn_fderiv_of_isOpen hO le_rfl
  refine (hc.clm_comp continuousOn_const).congr fun z hz => (hD z hz).fderiv

/-- Chosen inverse and its constants come from the frozen-inverse specification. -/
theorem lip_inverse {a : ℕ} {H0 : (Fin a → ℝ) → ℝ} {V W : Set (Fin a → ℝ)}
    (hW : IsOpen W) (hVb : Bornology.IsBounded V) (hVW : closure V ⊆ W)
    (hf : HasFastDiffeomorphism H0 W) :
    ∃ (g : (Fin a → ℝ) → Fin a → ℝ) (L R : ℝ), 1 ≤ L ∧ 0 < R ∧
      ContinuousOn (fastFrequency H0) W ∧ IsCompact (fastFrequency H0 '' closure V) ∧
      (∀ I ∈ W, g (fastFrequency H0 I) = I) ∧
      (∀ y ∈ fastFrequency H0 '' closure V, ‖y‖ ≤ R) ∧
      ∀ y ∈ fastFrequency H0 '' closure V, ∀ y' ∈ fastFrequency H0 '' closure V,
        ‖g y-g y'‖ ≤ L*‖y-y'‖ := by
  obtain ⟨hA, hopen, g, hg, hginv, hgW⟩ := hf
  have hcont : ContinuousOn (fastFrequency H0) W := by
    have h := hA.fderiv.continuousOn
    exact continuousOn_pi.2 fun i => h.clm_apply continuousOn_const
  have hK : IsCompact (fastFrequency H0 '' closure V) :=
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hVb.closure).image_of_continuousOn
      (hcont.mono hVW)
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  have hsub : ({0} : Set (Fin 0 → ℝ)) ×ˢ (fastFrequency H0 '' closure V) ⊆
      (univ : Set (Fin 0 → ℝ)) ×ˢ (fastFrequency H0 '' W) :=
    fun z hz => ⟨mem_univ _, image_mono hVW hz.2⟩
  have hcd : ContDiffOn ℝ 1 (fun z : (Fin 0 → ℝ) × (Fin a → ℝ) => g z.2)
      ((univ : Set (Fin 0 → ℝ)) ×ˢ (fastFrequency H0 '' W)) :=
    hg.comp contDiff_snd.contDiffOn fun z hz => hz.2
  obtain ⟨L, hL0, hL⟩ := lip_compact_c1 (isCompact_singleton) hK (isOpen_univ.prod hopen) hsub hcd
  refine ⟨g, max L 1, max C 1, le_max_right _ _, lt_max_of_lt_right one_pos, hcont, hK, hginv,
    fun y hy => (hC y hy).trans (le_max_left _ _), fun y hy y' hy' => ?_⟩
  exact (hL 0 rfl y hy y' hy').trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

end KAM.Planetary

end
