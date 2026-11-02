/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.HoloExt
public import HD11964.ChiRot

/-!
# HD 11964: the derivatives of `P` and the complex extension of `G₂` (HD11964-HOLO, (1d))

* `cEmbL`: the real-linear embedding of chart states into the complex variables (`θ = λ/2π`).
* `chartOkAt_eventually`: the chart conditions are open.
* `fderiv_chartPert_eq` (1d-P): at a real state with the chart conditions and `Re d² > 0`, the
  real derivative of `P` in a direction `v` is the complex derivative of `P_C` in `cEmbL v` (the
  link between DESIGN A's complex derivatives `dTh`, `dU` and the bracket's real ones).
* `trigSlice_ext`: the slices of the first derivatives of a trigonometric polynomial
  `Re Σ_{k ∈ S} B_k e^{i k·λ}` with angle-invariant coefficients extend to entire periodic
  functions (`Π_S P`, `χ*`).
* `g2Ext_of`, `g2Ext_HD`, `g2Ext_HD_A`, `g2Ext_HD_B` (1d): the slice of
  `G₂ = {P − ½ Π_S P, χ₁}` extends holomorphically and `1`-periodically to the per-slab strips,
  with (1b) as the named premise `NoCollisionOn`.
-/

@[expose] public noncomputable section

open Set Filter KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Application.LambdaDrift
open scoped Real Topology ComplexConjugate

namespace HD11964.Cover

/-! ### The real embedding -/

/-- The fast-angle part of `cEmbL`. -/
def angL : (Fin (2 + 2) → ℝ) →L[ℝ] (Fin 2 → ℂ) :=
  ContinuousLinearMap.pi fun j => Complex.ofRealCLM.comp
    ((2 * π)⁻¹ • ContinuousLinearMap.proj (Fin.castAdd 2 j))

/-- The first-block part of `cEmbL`. -/
def fstL : (Fin (2 + 2) → ℝ) →L[ℝ] (Fin 2 → ℂ) :=
  ContinuousLinearMap.pi fun j =>
    Complex.ofRealCLM.comp (ContinuousLinearMap.proj (Fin.castAdd 2 j))

/-- The second-block part of `cEmbL`. -/
def sndL : (Fin (2 + 2) → ℝ) →L[ℝ] (Fin 2 → ℂ) :=
  ContinuousLinearMap.pi fun j => Complex.ofRealCLM.comp (ContinuousLinearMap.proj (Fin.natAdd 2 j))

/-- **The real-linear embedding** `z ↦ (λ/2π, Λ, ξ, η)` of chart states into `CVar`. -/
def cEmbL : Phase (2 + 2) →L[ℝ] CVar :=
  (angL.comp (ContinuousLinearMap.fst ℝ _ _)).prod ((fstL.comp (ContinuousLinearMap.snd ℝ _ _)).prod
    ((sndL.comp (ContinuousLinearMap.fst ℝ _ _)).prod (sndL.comp (ContinuousLinearMap.snd ℝ _ _))))

theorem cEmbL_apply (z : Phase (2 + 2)) :
    cEmbL z = realVar z fun j => ((fast z.1 j / (2 * π) : ℝ) : ℂ) := by
  simp only [cEmbL, realVar, angL, fstL, sndL, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  refine Prod.ext (funext fun j => ?_) (Prod.ext (funext fun j => ?_)
    (Prod.ext (funext fun j => ?_) (funext fun j => ?_))) <;>
    simp [fast, slow, div_eq_inv_mul]

theorem cEmbL_withAngles (w : Phase (2 + 2)) (t : Fin 2 → ℝ) :
    cEmbL (withAngles w fun j => 2 * π * t j) = realVar w fun j => (t j : ℂ) := by
  rw [cEmbL_apply]
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  simp only [realVar, withAngles_fst_fast, withAngles_fst_slow, withAngles_snd]
  refine Prod.ext (funext fun j => ?_) rfl
  simp only
  rw [mul_div_cancel_left₀ _ hpi]

/-! ### The chart conditions are open -/

theorem planetOk_eventually {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {y₀ : ℝ} {lam Λ ξ η : E → ℂ} {x₀ : E} (hlam : AnalyticAt ℂ lam x₀)
    (hΛ : AnalyticAt ℂ Λ x₀) (hξ : AnalyticAt ℂ ξ x₀) (hη : AnalyticAt ℂ η x₀)
    (h : PlanetOk y₀ (lam x₀) (Λ x₀) (ξ x₀) (η x₀)) :
    ∀ᶠ x in 𝓝 x₀, PlanetOk y₀ (lam x) (Λ x) (ξ x) (η x) := by
  have hΛ0 := h.ne_zero
  have hslit := h.rad_mem
  have hR : AnalyticAt ℂ (fun x => radC (Λ x) (ξ x) (η x)) x₀ := by
    unfold radC; fun_prop (disch := simp [hΛ0])
  have hv0 : AnalyticAt ℂ (fun x => eccC (Λ x) (ξ x) (η x) 0) x₀ := by
    simp only [eccC, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
    fun_prop (disch := assumption)
  have hv1 : AnalyticAt ℂ (fun x => eccC (Λ x) (ξ x) (η x) 1) x₀ := by
    simp only [eccC, Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul]
    fun_prop (disch := assumption)
  have hk : AnalyticAt ℂ (fun x => 1 + kC (Λ x) (ξ x) (η x)) x₀ := by
    unfold kC; fun_prop (disch := simp [hΛ0])
  have hlc := hlam.continuousAt
  have hv0c := hv0.continuousAt
  have hv1c := hv1.continuousAt
  have hI : ContinuousAt (fun x => |(lam x).im| + (|(eccC (Λ x) (ξ x) (η x) 0).re| +
      |(eccC (Λ x) (ξ x) (η x) 1).re|) * Real.sinh y₀ + (|(eccC (Λ x) (ξ x) (η x) 0).im| +
      |(eccC (Λ x) (ξ x) (η x) 1).im|) * Real.cosh y₀) x₀ := by fun_prop
  have hC : ContinuousAt (fun x => (‖eccC (Λ x) (ξ x) (η x) 0‖ + ‖eccC (Λ x) (ξ x) (η x) 1‖) *
      Real.cosh y₀) x₀ := by fun_prop
  filter_upwards [hΛ.continuousAt.eventually_ne hΛ0,
    hR.continuousAt.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds h.rad_mem),
    hk.continuousAt.eventually_ne h.one_add_k, hI.eventually (gt_mem_nhds h.invariant),
    hC.eventually (gt_mem_nhds h.contraction)] with x h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h.y_pos, h4, h5⟩

/-- **The chart conditions are open.** -/
theorem chartOkAt_eventually {y : Fin 2 → ℝ} {x₀ : CVar} (h : ChartOkAt y x₀) :
    ∀ᶠ x in 𝓝 x₀, ChartOkAt y x :=
  Filter.eventually_all.2 fun j => planetOk_eventually
    (analyticAt_const.mul (analyticAt_proj_fst j)) (analyticAt_proj_Λ j) (analyticAt_proj_ξ j)
    (analyticAt_proj_η j) (h j)

/-! ### (1d-P) Real derivatives are complex derivatives -/

/-- Near a real state with the chart conditions, `P_C ∘ cEmbL = P`. -/
theorem pertCC_cEmbL_eventually {y : Fin 2 → ℝ} {z : Phase (2 + 2)}
    (hz : z ∈ poincareProdDom 2) (h : ChartOkAt y (cEmbL z)) :
    (fun z' => pertCC y (cEmbL z')) =ᶠ[𝓝 z] fun z' => ((chartPert nu mu z' : ℝ) : ℂ) := by
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  filter_upwards [(cEmbL.continuous.tendsto z).eventually (chartOkAt_eventually h),
    (lpChart_isOpen_dom 2).mem_nhds hz] with z' h1 h2
  rw [cEmbL_apply] at h1 ⊢
  rw [pertCC_realVar_ofReal h2 _ h1]
  congr 2
  have e : (fun j => 2 * π * (fast z'.1 j / (2 * π))) = fast z'.1 := by
    funext j; field_simp
  rw [e, withAngles_self]

/-- **(1d-P) The real derivative of `P` is the complex derivative of `P_C`** at a real state with
the chart conditions and `Re d² > 0`. -/
theorem fderiv_chartPert_eq {y : Fin 2 → ℝ} {z : Phase (2 + 2)} (hz : z ∈ poincareProdDom 2)
    (h : ChartOkAt y (cEmbL z)) (hd : 0 < (distSqCC y (cEmbL z)).re) (v : Phase (2 + 2)) :
    ((fderiv ℝ (chartPert nu mu) z v : ℝ) : ℂ) = fderiv ℂ (pertCC y) (cEmbL z) (cEmbL v) := by
  have hF : HasFDerivAt (pertCC y) (fderiv ℂ (pertCC y) (cEmbL z)) (cEmbL z) :=
    (pertCC_analyticAt h hd).differentiableAt.hasFDerivAt
  have hFR : HasFDerivAt (fun z' => pertCC y (cEmbL z'))
      (((fderiv ℂ (pertCC y) (cEmbL z)).restrictScalars ℝ).comp cEmbL) z :=
    (hF.restrictScalars ℝ).comp z cEmbL.hasFDerivAt
  have hG := hFR.congr_of_eventuallyEq (pertCC_cEmbL_eventually hz h).symm
  have hd2 : DifferentiableAt ℝ (chartPert nu mu) z := by
    have := (Complex.reCLM.hasFDerivAt.comp z hG).differentiableAt
    simpa [Function.comp_def] using this
  have h3 : HasFDerivAt (fun z' => ((chartPert nu mu z' : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (chartPert nu mu) z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hd2.hasFDerivAt
  have := congrArg (fun L => L v) (hG.unique h3)
  simpa using this.symm

/-! ### Trigonometric polynomials with angle-invariant coefficients -/

/-- `θ(z) = λ/2π`. -/
def angC (z : Phase (2 + 2)) : Fin 2 → ℂ := fun i => ((fast z.1 i / (2 * π) : ℝ) : ℂ)

theorem angC_add (a b : Phase (2 + 2)) : angC (a + b) = angC a + angC b := by
  funext i; simp [angC, fast, add_div]

theorem angC_withAngles (w : Phase (2 + 2)) (t : Fin 2 → ℝ) :
    angC (withAngles w fun j => 2 * π * t j) = fun j => (t j : ℂ) := by
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  funext i
  simp only [angC, withAngles_fst_fast]
  rw [mul_div_cancel_left₀ _ hpi]

theorem withAngles_eq_of {z z' : Phase (2 + 2)} (h1 : slow z.1 = slow z'.1) (h2 : z.2 = z'.2)
    (lam : Fin 2 → ℝ) : withAngles z lam = withAngles z' lam := by
  simp only [withAngles, h1, h2]

theorem charE_neg_ofReal (k : Fin 2 → ℤ) (t : Fin 2 → ℝ) :
    charE (-k) (fun j => (t j : ℂ)) = conj (charE k fun j => (t j : ℂ)) := by
  simp only [charE, ← Complex.exp_conj, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_I,
    Pi.neg_apply, Int.cast_neg, map_ofNat, map_intCast]
  congr 1
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

/-- **The slices of the first derivatives of `Re Σ_{k ∈ S} B_k e^{i k·λ}`** (angle-invariant `B_k`,
differentiable at `w`) extend to entire `1`-periodic functions of `θ`. -/
theorem trigSlice_ext {S : Finset (Fin 2 → ℤ)} {B : (Fin 2 → ℤ) → Phase (2 + 2) → ℂ}
    {g : Phase (2 + 2) → ℝ} (hg : ∀ z, g z = (∑ k ∈ S, B k z * charE k (angC z)).re)
    (hB : ∀ k z (lam : Fin 2 → ℝ), B k (withAngles z lam) = B k z) {w : Phase (2 + 2)}
    (hBd : ∀ k ∈ S, DifferentiableAt ℝ (B k) w) (v : Phase (2 + 2)) :
    ∃ T : (Fin 2 → ℂ) → ℂ, Differentiable ℂ T ∧ (∀ j θ, T (θ + Pi.single j 1) = T θ) ∧
      ∀ t : Fin 2 → ℝ, T (fun j => (t j : ℂ)) =
        ((fderiv ℝ g (withAngles w fun j => 2 * π * t j) v : ℝ) : ℂ) := by
  set H : (Fin 2 → ℤ) → Phase (2 + 2) → ℂ := fun k h => B k (w + h) * charE k (angC h) with hH
  have hHd : ∀ k ∈ S, DifferentiableAt ℝ (H k) 0 := by
    intro k hk
    have h1 : DifferentiableAt ℝ (fun h : Phase (2 + 2) => B k (w + h)) 0 := by
      have h0 : DifferentiableAt ℝ (fun h : Phase (2 + 2) => w + h) 0 :=
        (differentiableAt_const w).add differentiableAt_fun_id
      have hw0 : DifferentiableAt ℝ (B k) ((fun h : Phase (2 + 2) => w + h) 0) := by
        simpa using hBd k hk
      exact hw0.comp (0 : Phase (2 + 2)) h0
    have h2 : DifferentiableAt ℝ (fun h : Phase (2 + 2) => charE k (angC h)) 0 :=
      ((contDiff_charE_angles k).differentiable (by simp)).differentiableAt
    exact h1.mul h2
  have hshift : ∀ (t : Fin 2 → ℝ) (h : Phase (2 + 2)),
      g ((withAngles w fun j => 2 * π * t j) + h) =
        (∑ k ∈ S, charE k (fun j => (t j : ℂ)) * H k h).re := by
    intro t h
    rw [hg]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : B k ((withAngles w fun j => 2 * π * t j) + h) = B k (w + h) := by
      have hs : slow ((withAngles w fun j => 2 * π * t j) + h).1 = slow (w + h).1 := by
        have e : ∀ a b : Phase (2 + 2), slow (a + b).1 = slow a.1 + slow b.1 := fun a b => by
          funext i; simp [slow]
        rw [e, e, withAngles_fst_slow]
      have h2 : ((withAngles w fun j => 2 * π * t j) + h).2 = (w + h).2 := by
        simp [withAngles_snd]
      rw [← withAngles_self ((withAngles w fun j => 2 * π * t j) + h),
        withAngles_eq_of hs h2, hB]
    rw [e1, angC_add, charE_add, angC_withAngles]
    simp only [hH]
    ring
  set c : (Fin 2 → ℤ) → ℂ := fun k => fderiv ℝ (H k) 0 v with hc
  have hd : ∀ t : Fin 2 → ℝ, fderiv ℝ g (withAngles w fun j => 2 * π * t j) v =
      (∑ k ∈ S, charE k (fun j => (t j : ℂ)) * c k).re := by
    intro t
    have e : fderiv ℝ g (withAngles w fun j => 2 * π * t j) =
        fderiv ℝ (fun h => g ((withAngles w fun j => 2 * π * t j) + h)) 0 := by
      rw [fderiv_comp_add_left, add_zero]
    have hsum : HasFDerivAt (fun h => ∑ k ∈ S, charE k (fun j => (t j : ℂ)) * H k h)
        (∑ k ∈ S, charE k (fun j => (t j : ℂ)) • fderiv ℝ (H k) 0) 0 :=
      HasFDerivAt.fun_sum fun k hk => (hHd k hk).hasFDerivAt.const_mul _
    have hre := Complex.reCLM.hasFDerivAt.comp (0 : Phase (2 + 2)) hsum
    rw [e, funext (hshift t)]
    have e2 : (fun h => (∑ k ∈ S, charE k (fun j => (t j : ℂ)) * H k h).re) =
        Complex.reCLM ∘ fun h => ∑ k ∈ S, charE k (fun j => (t j : ℂ)) * H k h := rfl
    rw [e2, hre.fderiv]
    simp [hc]
  refine ⟨fun θ => (∑ k ∈ S, c k * charE k θ + ∑ k ∈ S, conj (c k) * charE (-k) θ) / 2, ?_, ?_,
    ?_⟩
  · simp only [div_eq_mul_inv]
    apply Differentiable.mul_const
    apply Differentiable.fun_add
    · exact Differentiable.fun_sum fun k _ => (differentiable_charE k).const_mul (c k)
    · exact Differentiable.fun_sum fun k _ => (differentiable_charE (-k)).const_mul (conj (c k))
  · intro j θ
    simp only [charE_add_single]
  · intro t
    dsimp only
    rw [hd]
    have e : ∑ k ∈ S, conj (c k) * charE (-k) (fun j => (t j : ℂ)) =
        conj (∑ k ∈ S, charE k (fun j => (t j : ℂ)) * c k) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [charE_neg_ofReal, map_mul]; ring
    rw [e, show ∑ k ∈ S, c k * charE k (fun j => (t j : ℂ)) =
      ∑ k ∈ S, charE k (fun j => (t j : ℂ)) * c k from
        Finset.sum_congr rfl fun k _ => mul_comm _ _, Complex.add_conj]
    push_cast
    ring

/-! ### The extensions of the first derivatives of `P`, `Π_S P` and `χ₁` -/

/-- The extension of the slice `θ ↦ ∂_v P(withAngles w (2πθ))`. -/
def dPC (y : Fin 2 → ℝ) (w v : Phase (2 + 2)) (θ : Fin 2 → ℂ) : ℂ :=
  fderiv ℂ (pertCC y) (realVar w θ) (cEmbL v)

theorem realVar_add_single (w : Phase (2 + 2)) (θ : Fin 2 → ℂ) (j : Fin 2) :
    realVar w (θ + Pi.single j 1) = realVar w θ + ((Pi.single j 1, 0) : CVar) :=
  Prod.ext rfl (add_zero _).symm

theorem dPC_analyticAt {y : Fin 2 → ℝ} {w v : Phase (2 + 2)} {θ : Fin 2 → ℂ}
    (h : ChartOkAt y (realVar w θ)) (hd : 0 < (distSqCC y (realVar w θ)).re) :
    AnalyticAt ℂ (dPC y w v) θ := by
  have hA := (pertCC_analyticAt h hd).fderiv
  have hr : AnalyticAt ℂ (fun θ : Fin 2 → ℂ => realVar w θ) θ :=
    analyticAt_id.prod analyticAt_const
  exact ((ContinuousLinearMap.apply ℂ ℂ (cEmbL v)).analyticAt _).comp (hA.comp hr)

theorem dPC_add_single {y : Fin 2 → ℝ} {w v : Phase (2 + 2)} {θ : Fin 2 → ℂ}
    (h : ChartOkAt y (realVar w θ)) (j : Fin 2) : dPC y w v (θ + Pi.single j 1) = dPC y w v θ := by
  unfold dPC
  rw [realVar_add_single]
  have hev : (fun x => pertCC y (x + ((Pi.single j 1, 0) : CVar))) =ᶠ[𝓝 (realVar w θ)]
      pertCC y := by
    filter_upwards [chartOkAt_eventually h] with x hx
    have e : x + ((Pi.single j 1, 0) : CVar) = (x.1 + Pi.single j 1, x.2) :=
      Prod.ext rfl (add_zero _)
    rw [e]
    exact pertCC_add_single hx j
  rw [← fderiv_comp_add_right, hev.fderiv_eq]

theorem dPC_ofReal {y : Fin 2 → ℝ} {w : Phase (2 + 2)} (hw : w ∈ poincareProdDom 2)
    (t : Fin 2 → ℝ) (h : ChartOkAt y (realVar w fun j => (t j : ℂ)))
    (hd : 0 < (distSqCC y (realVar w fun j => (t j : ℂ))).re) (v : Phase (2 + 2)) :
    dPC y w v (fun j => (t j : ℂ)) =
      ((fderiv ℝ (chartPert nu mu) (withAngles w fun j => 2 * π * t j) v : ℝ) : ℂ) := by
  unfold dPC
  rw [← cEmbL_withAngles] at h hd ⊢
  rw [fderiv_chartPert_eq (withAngles_mem_dom hw _) h hd v]

/-- The slices of the first derivatives of `Π_S P` extend (entire, periodic). -/
theorem projS_slice_ext {w : Phase (2 + 2)} (hw : w ∈ openHD) (v : Phase (2 + 2)) :
    ∃ T : (Fin 2 → ℂ) → ℂ, Differentiable ℂ T ∧ (∀ j θ, T (θ + Pi.single j 1) = T θ) ∧
      ∀ t : Fin 2 → ℝ, T (fun j => (t j : ℂ)) =
        ((fderiv ℝ (projS modesHD (chartPert nu mu)) (withAngles w fun j => 2 * π * t j) v : ℝ) :
          ℂ) :=
  trigSlice_ext (B := fun k z => chartCoeff (chartPert nu mu) k z) (fun z => rfl)
    (fun k z lam => chartCoeff_withAngles _ k z lam)
    (fun k _ => ((contDiffOn_chartCoeff isOpen_openHD isAngleSaturated_openHD
      contDiffOn_chartPert_HD k).contDiffAt (isOpen_openHD.mem_nhds hw)).differentiableAt
        (by simp)) v

/-- The slices of the first derivatives of `χ₁` extend (entire, periodic). -/
theorem chi1_slice_ext {w : Phase (2 + 2)} (hw : w ∈ openHD) (v : Phase (2 + 2)) :
    ∃ T : (Fin 2 → ℂ) → ℂ, Differentiable ℂ T ∧ (∀ j θ, T (θ + Pi.single j 1) = T θ) ∧
      ∀ t : Fin 2 → ℝ, T (fun j => (t j : ℂ)) =
        ((fderiv ℝ chi1HD (withAngles w fun j => 2 * π * t j) v : ℝ) : ℂ) := by
  have hΛ : ∀ i, fast w.2 i ≠ 0 := fast_ne_zero_of_mem_dom (openHD_subset_dom hw)
  refine trigSlice_ext (B := fun k z => chartCoeff (chartPert nu mu) k z *
    (Complex.I * ∑ i, (k i : ℂ) * keplerFreq nu (fast z.2) i)⁻¹) (fun z => rfl)
    (fun k z lam => by simp only [chartCoeff_withAngles, withAngles_snd]) (fun k hk => ?_) v
  exact (((contDiffOn_chartCoeff isOpen_openHD isAngleSaturated_openHD
    contDiffOn_chartPert_HD k).contDiffAt (isOpen_openHD.mem_nhds hw)).mul
      (contDiffAt_divisorInv (contDiffAt_keplerFreq nu hΛ)
        (isModeSet_HD.2.2 k hk w hw))).differentiableAt (by simp)

/-! ### (1d) The complex extension of `G₂` -/

/-- **(1d)** in the drafted form: the slice of `G₂` at `w` extends holomorphically and
`1`-periodically to the strip. -/
def G2Ext (ρ : Fin 2 → ℝ) (w : Phase (2 + 2)) : Prop :=
  ∃ Gc : (Fin 2 → ℂ) → ℂ, DifferentiableOn ℂ Gc (stripA ρ) ∧
    (∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ stripA ρ → Gc (θ + Pi.single j 1) = Gc θ) ∧
    ∀ t : Fin 2 → ℝ, Gc (fun j => (t j : ℂ)) = (G2HD (withAngles w fun j => 2 * π * t j) : ℂ)

/-- The first derivative of `P - ½ Π_S P` at a state of `openHD`. -/
theorem fderiv_pert_sub_half {z : Phase (2 + 2)} (hz : z ∈ openHD) (v : Phase (2 + 2)) :
    fderiv ℝ (fun y => chartPert nu mu y - projS modesHD (chartPert nu mu) y / 2) z v =
      fderiv ℝ (chartPert nu mu) z v - fderiv ℝ (projS modesHD (chartPert nu mu)) z v / 2 := by
  have hP : DifferentiableAt ℝ (chartPert nu mu) z :=
    (contDiffOn_chartPert_HD.contDiffAt (isOpen_openHD.mem_nhds hz)).differentiableAt (by simp)
  have hQ : DifferentiableAt ℝ (projS modesHD (chartPert nu mu)) z :=
    ((contDiffOn_projS isOpen_openHD isAngleSaturated_openHD modesHD
      contDiffOn_chartPert_HD).contDiffAt (isOpen_openHD.mem_nhds hz)).differentiableAt (by simp)
  have h := hP.hasFDerivAt.sub (hQ.hasFDerivAt.const_mul (1 / 2 : ℝ))
  have e : (fun y => chartPert nu mu y - projS modesHD (chartPert nu mu) y / 2) =
      fun y => chartPert nu mu y - 1 / 2 * projS modesHD (chartPert nu mu) y := by
    funext y; ring
  rw [e, show (fun y => chartPert nu mu y - 1 / 2 * projS modesHD (chartPert nu mu) y) =
    chartPert nu mu - fun y => 1 / 2 * projS modesHD (chartPert nu mu) y from rfl, h.fderiv]
  simp only [FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **(1d) on a strip from (1a) and (1b)**, at a state of `openHD`. -/
theorem g2Ext_of {y ρ κ : Fin 2 → ℝ} {w : Phase (2 + 2)} (hw : w ∈ openHD)
    (hK : ∀ j, KAM.Kepler.KeplerData {lam : ℂ | |lam.im| < 2 * π * ρ j}
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.1 j : ℝ) : ℂ))
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.2 j : ℝ) : ℂ))
      (fun lam => lam) (y j) (κ j))
    (hρ : ∀ j, 0 < ρ j) (hcol : NoCollisionOn y ρ w) : G2Ext ρ w := by
  have hdom := openHD_subset_dom hw
  choose TP hTPd hTPp hTPr using fun v => projS_slice_ext hw v
  choose TX hTXd hTXp hTXr using fun v => chi1_slice_ext hw v
  set A : Phase (2 + 2) → (Fin 2 → ℂ) → ℂ := fun v θ => dPC y w v θ - TP v θ / 2 with hA
  refine ⟨fun θ => ∑ k : Fin (2 + 2), (A (Pi.single k 1, 0) θ * TX (0, Pi.single k 1) θ -
    A (0, Pi.single k 1) θ * TX (Pi.single k 1, 0) θ), fun θ hθ => ?_, fun j θ hθ => ?_,
    fun t => ?_⟩
  · have hok := chartOkAt_of_keplerData hdom hK hθ
    have hd : 0 < (distSqCC y (realVar w θ)).re := hcol θ hθ
    have hP : ∀ v, DifferentiableAt ℂ (dPC y w v) θ := fun v =>
      (dPC_analyticAt hok hd).differentiableAt
    have hAd : ∀ v, DifferentiableAt ℂ (A v) θ := fun v => by
      simp only [hA, div_eq_mul_inv]
      exact (hP v).sub (((hTPd v).differentiableAt).mul_const _)
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.fun_sum fun k _ => ?_
    exact ((hAd _).mul (hTXd _).differentiableAt).sub ((hAd _).mul (hTXd _).differentiableAt)
  · have hok := chartOkAt_of_keplerData hdom hK hθ
    simp only [hA, dPC_add_single hok, hTPp, hTXp]
  · have hz : (withAngles w fun j => 2 * π * t j) ∈ openHD := isAngleSaturated_openHD w hw _
    have hok := chartOkAt_of_keplerData hdom hK (ofReal_mem_stripA hρ t)
    have hd : 0 < (distSqCC y (realVar w fun j => (t j : ℂ))).re := hcol _ (ofReal_mem_stripA hρ t)
    simp only [hA, dPC_ofReal hdom t hok hd, hTPr, hTXr]
    rw [G2HD, pb_eq_sum]
    simp only [fderiv_pert_sub_half hz]
    push_cast
    rfl

/-- **(1d), uniform strip** `ρ = (1/40, 3/20)`. -/
theorem g2Ext_HD {w : Phase (2 + 2)} (hw : w ∈ holoDomHD)
    (hcol : NoCollisionOn yHolo rhoHolo w) : G2Ext rhoHolo w :=
  g2Ext_of (region_subset_openHD (by norm_num) hw.1) (fun j => keplerData_HD j hw)
    (fun j => by fin_cases j <;> norm_num [rhoHolo]) hcol

/-- **(1d), slabs 0–4** (`|ξ_c| ≤ 0.1431`): `ρ = (7/200, 3/20)`. -/
theorem g2Ext_HD_A {w : Phase (2 + 2)} (hw : w ∈ holoDomHD) (hξ : |slow w.1 0| ≤ 1431 / 10000)
    (hcol : NoCollisionOn yHoloA rhoHoloA w) : G2Ext rhoHoloA w :=
  g2Ext_of (region_subset_openHD (by norm_num) hw.1) (fun j => keplerData_HD_A j hw hξ)
    (fun j => by fin_cases j <;> norm_num [rhoHoloA]) hcol

/-- **(1d), slab 5** (`|ξ_c| ≤ 0.1612`): `ρ = (3/100, 3/20)`. -/
theorem g2Ext_HD_B {w : Phase (2 + 2)} (hw : w ∈ holoDomHD) (hξ : |slow w.1 0| ≤ 1612 / 10000)
    (hcol : NoCollisionOn yHoloB rhoHoloB w) : G2Ext rhoHoloB w :=
  g2Ext_of (region_subset_openHD (by norm_num) hw.1) (fun j => keplerData_HD_B j hw hξ)
    (fun j => by fin_cases j <;> norm_num [rhoHoloB]) hcol

end HD11964.Cover

end
