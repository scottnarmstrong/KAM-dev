/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.ToriEstimates

/-!
# Two-scale KAM: immersion and Lagrangian property (`bpP:p3:lagr`)

`tori_lagr_of_limit` is the private conditional helper for the local obligation `lagr`. The angle
displacement `u` of the torus `φ = Φ(·, I_*)` has derivative bounded by `3 Ê s / s̄ ≤ 3Ê/4 ≤
(3/4) n Ê` (`stepP:p3:lg-cauchy`, Cauchy on the polydisc of radius `s̄/4π` of the strip), so the
lower block `1 + Du` is injective; `φ` is real-analytic (restriction of the complex extension); and
`φ^*(Σ dIᵢ ∧ dθᵢ) = 0` because the finite-stage tori `Φ_j(·, I_*)` are Lagrangian
(`stage_lagr`) and their first derivatives converge (`stepP:p3:lg-lim`). Design package P23-20.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {sbar : ℝ} {p : ScaleData} {h : (Fin (a + b) → ℂ) → ℂ}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {Φ : ℕ → CPhase (a + b) → CPhase (a + b)}
  {is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)}
  {i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)} {Φinf : Phase (a + b) → Phase (a + b)}

/-- `symplFormC` is continuous along convergent sequences. -/
theorem tendsto_symplFormC {n : ℕ} {x y : ℕ → CPhase n} {x' y' : CPhase n}
    (hx : Tendsto x atTop (𝓝 x')) (hy : Tendsto y atTop (𝓝 y')) :
    Tendsto (fun j => symplFormC (x j) (y j)) atTop (𝓝 (symplFormC x' y')) := by
  unfold symplFormC
  refine tendsto_finset_sum _ fun k _ => ?_
  have hx1 := (tendsto_pi_nhds.1 (Prod.tendsto_iff _ _ |>.1 hx).1) k
  have hx2 := (tendsto_pi_nhds.1 (Prod.tendsto_iff _ _ |>.1 hx).2) k
  have hy1 := (tendsto_pi_nhds.1 (Prod.tendsto_iff _ _ |>.1 hy).1) k
  have hy2 := (tendsto_pi_nhds.1 (Prod.tendsto_iff _ _ |>.1 hy).2) k
  exact (hx2.mul hy1).sub (hx1.mul hy2)

theorem symplFormC_realInclusion₂ {n : ℕ} (v w : Phase n) :
    symplFormC (KAM.realInclusion₂ n v) (KAM.realInclusion₂ n w) =
      ((KAM.symplecticForm v w : ℝ) : ℂ) := by
  simp [symplFormC, KAM.symplecticForm]

/-- The local obligation `lagr` of `two_scale_kam` (private conditional helper, P23-20), for the
torus `φ(θ) = Φ(θ, ǐ(I₀))`, `I₀ ∈ D₀`: it is real-analytic; the angle displacement has
`‖D_θ u‖ ≤ (3/4) n Ê`; `Dφ` is injective; and `φ^*(Σ dIᵢ ∧ dθᵢ) = 0`. -/
theorem tori_lagr_of_limit {D : Set (Fin (a + b) → ℝ)} {f : CHam (a + b)}
    (H : KamHyp D sbar p h f) (T : ToriLimit sbar p h Ds hs Φ is i Φinf)
    {I₀ : Fin (a + b) → ℝ} (hI₀ : I₀ ∈ Ds 0) :
    AnalyticOnNhd ℝ (fun θ => Φinf (θ, i I₀)) univ ∧
    (∀ θ, ‖fderiv ℝ (fun θ => (Φinf (θ, i I₀)).1 - θ) θ‖ ≤
      3 / 4 * ((a + b : ℕ) : ℝ) * eHat p) ∧
    (∀ θ, Function.Injective (fderiv ℝ (fun θ => Φinf (θ, i I₀)) θ)) ∧
    (∀ θ u v, KAM.symplecticForm (fderiv ℝ (fun θ => Φinf (θ, i I₀)) θ u)
      (fderiv ℝ (fun θ => Φinf (θ, i I₀)) θ v) = 0) := by
  have hmem : i I₀ ∈ i '' Ds 0 := ⟨I₀, hI₀, rfl⟩
  obtain ⟨KC, k1, k2, k3, k4⟩ := tori_complex_ext H T hmem
  have hs0 := H.positive.2.1
  have hsb := H.widths.1
  have hw : 0 < geometricWidth sbar := by unfold geometricWidth; have : 0 < sbar := by linarith
                                          positivity
  have hreal : KAM.IsRealOnReals KC := fun θ => ⟨Φinf (θ, i I₀), k2 θ⟩
  obtain ⟨hAn, hD, -, -⟩ := KAM.real_restriction hw k1 hreal
  have hφ : KAM.realRestriction KC = fun θ => Φinf (θ, i I₀) := by
    funext θ
    simp [KAM.realRestriction, k2 θ]
  rw [hφ] at hAn hD
  have hz0 : ∀ θ : Fin (a + b) → ℝ, KAM.realInclusion (a + b) θ ∈
      KAM.complexStrip (a + b) (geometricWidth sbar) :=
    fun θ => KAM.realInclusion_mem_complexStrip hw θ
  -- derivative bound on the angle displacement
  have hbd : ∀ θ, ‖fderiv ℝ (fun θ => (Φinf (θ, i I₀)).1 - θ) θ‖ ≤ 3 / 4 * eHat p := by
    intro θ
    set K' : (Fin (a + b) → ℂ) → CPhase (a + b) := fun θ => ((KC θ).1 - θ, 0) with hK'
    have hK'd : DifferentiableOn ℂ K' (KAM.complexStrip (a + b) (geometricWidth sbar)) :=
      ((differentiable_fst.comp_differentiableOn k1).sub
        differentiableOn_id).prodMk (differentiableOn_const _)
    have hreal' : KAM.IsRealOnReals K' := fun x => by
      have e1 : (KC fun i => (x i : ℂ)).1 = fun c => (((Φinf (x, i I₀)).1 c : ℝ) : ℂ) :=
        congrArg Prod.fst (k2 x)
      refine ⟨((Φinf (x, i I₀)).1 - x, 0), ?_⟩
      simp only [hK']
      rw [e1]
      ext c <;> simp
    obtain ⟨-, -, hN, -⟩ := KAM.real_restriction hw hK'd hreal'
    have hcau := KAM.norm_fderiv_le_of_mem_complexStrip (n := a + b)
      (δ := geometricWidth sbar / 2) (A := 3 / (4 * π) * eHat p * p.s) hK'd
      (fun y hy => by
        simp only [hK', Prod.norm_def, norm_zero]
        exact max_le (k3 y hy) (by have := eHat_pos H; positivity))
      (by positivity) (z := KAM.realInclusion (a + b) θ)
      (fun k => by simp; positivity)
    have hφd := (hD θ).1
    have hu : DifferentiableAt ℝ (fun θ => (Φinf (θ, i I₀)).1 - θ) θ :=
      (differentiable_fst.differentiableAt.comp θ hφd).sub differentiableAt_id
    have hrr : KAM.realRestriction K' = fun x => ((Φinf (x, i I₀)).1 - x, 0) := by
      funext x; simp [KAM.realRestriction, hK', k2 x]
    have hN' := hN θ
    rw [hrr] at hN'
    have hder : fderiv ℝ (fun x => ((Φinf (x, i I₀)).1 - x, (0 : Fin (a + b) → ℝ))) θ =
        (fderiv ℝ (fun θ => (Φinf (θ, i I₀)).1 - θ) θ).prod
          (0 : (Fin (a + b) → ℝ) →L[ℝ] (Fin (a + b) → ℝ)) :=
      (hu.hasFDerivAt.prodMk (hasFDerivAt_const _ _)).fderiv
    rw [hder] at hN'
    have hsb' : 0 < sbar := by linarith
    have hq : 3 / (4 * π) * eHat p * p.s / (geometricWidth sbar / 2) ≤ 3 / 4 * eHat p := by
      unfold geometricWidth
      have he := eHat_pos H
      rw [div_le_iff₀ (by positivity)]
      have : 3 / (4 * π) * eHat p * p.s = 3 * eHat p * p.s / (4 * π) := by ring
      rw [this, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [mul_pos he hs0, mul_pos he hsb', H.widths.1]
    refine le_trans ?_ (hN'.trans (hcau.trans hq))
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    calc ‖fderiv ℝ (fun θ => (Φinf (θ, i I₀)).1 - θ) θ v‖
        ≤ ‖((fderiv ℝ (fun θ => (Φinf (θ, i I₀)).1 - θ) θ).prod
          (0 : (Fin (a + b) → ℝ) →L[ℝ] (Fin (a + b) → ℝ))) v‖ := by
          rw [ContinuousLinearMap.prod_apply, Prod.norm_def]
          exact le_max_left _ _
      _ ≤ _ := ContinuousLinearMap.le_opNorm _ _
  have hn1 : (1 : ℝ) ≤ ((a + b : ℕ) : ℝ) := by
    have := H.a_pos; exact_mod_cast (by omega : 1 ≤ a + b)
  have he := eHat_pos H
  have hqn : ∀ θ, ‖fderiv ℝ (fun θ => (Φinf (θ, i I₀)).1 - θ) θ‖ ≤
      3 / 4 * ((a + b : ℕ) : ℝ) * eHat p := fun θ => (hbd θ).trans (by nlinarith)
  have hsmall : 3 / 4 * ((a + b : ℕ) : ℝ) * eHat p < 1 := by
    have h1 := H.small
    have h2 : 2 ^ 13 * ((a + b : ℕ) : ℝ) ≤ kamConstant (a + b) p.τ := le_max_left _ _
    nlinarith [mul_le_mul_of_nonneg_right h2 he.le]
  refine ⟨hAn, hqn, fun θ u u' hu => ?_, fun θ u v => ?_⟩
  · -- injectivity of the lower block
    have hφd := (hD θ).1
    have hg : HasFDerivAt (fun θ => (Φinf (θ, i I₀)).1 - θ)
        (((ContinuousLinearMap.fst ℝ _ _).comp (fderiv ℝ (fun θ => Φinf (θ, i I₀)) θ)) -
          ContinuousLinearMap.id ℝ _) θ :=
      ((ContinuousLinearMap.fst ℝ (Fin (a + b) → ℝ) (Fin (a + b) → ℝ)).hasFDerivAt.comp θ
        hφd.hasFDerivAt).sub (hasFDerivAt_id θ)
    have e : ∀ w, fderiv ℝ (fun θ => (Φinf (θ, i I₀)).1 - θ) θ w =
        (fderiv ℝ (fun θ => Φinf (θ, i I₀)) θ w).1 - w := by
      intro w; rw [hg.fderiv]; rfl
    have hw : fderiv ℝ (fun θ => Φinf (θ, i I₀)) θ (u - u') = 0 := by
      rw [map_sub, hu, sub_self]
    have e1 := e (u - u')
    rw [hw] at e1
    simp only [Prod.fst_zero, Pi.zero_apply, zero_sub] at e1
    have hle : ‖u - u'‖ ≤ 3 / 4 * ((a + b : ℕ) : ℝ) * eHat p * ‖u - u'‖ := by
      calc ‖u - u'‖ = ‖fderiv ℝ (fun θ => (Φinf (θ, i I₀)).1 - θ) θ (u - u')‖ := by
            rw [e1, norm_neg]
        _ ≤ ‖fderiv ℝ (fun θ => (Φinf (θ, i I₀)).1 - θ) θ‖ * ‖u - u'‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ _ := by gcongr; exact hqn θ
    have h0 : ‖u - u'‖ = 0 := by nlinarith [norm_nonneg (u - u')]
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)
  · have hz := hz0 θ
    have lim := tendsto_symplFormC (k4 _ hz (KAM.realInclusion (a + b) u))
      (k4 _ hz (KAM.realInclusion (a + b) v))
    have hzero : ∀ j, symplFormC
        (fderiv ℂ (fun θ => Φ j (θ, KAM.realInclusion (a + b) (i I₀))) _
          (KAM.realInclusion (a + b) u))
        (fderiv ℂ (fun θ => Φ j (θ, KAM.realInclusion (a + b) (i I₀))) _
          (KAM.realInclusion (a + b) v)) = 0 := fun j =>
      T.stage_lagr j _ hmem _ hz _ _
    simp_rw [hzero] at lim
    have h0 := tendsto_nhds_unique lim tendsto_const_nhds
    rw [← (hD θ).2 u, ← (hD θ).2 v, symplFormC_realInclusion₂] at h0
    exact_mod_cast h0

end KAM.Planetary

end
