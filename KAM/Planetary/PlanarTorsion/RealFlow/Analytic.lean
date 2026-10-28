/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Analytic
public import KAM.ODE.Basic
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Planetary.Preparation.AnalyticExtension
public import KAM.Planetary.PlanarTorsion.RealFlow.PicardData

/-!
# Planar quartic torsion: real analytic parametric flow (package R2)

Blueprint P, Part 11b (`bpP:p11b:e-ode`, package R2).  For a real analytic vector field `f` near
`x ∈ ℝⁿ` the local flow `Φ (t, y)` is jointly real analytic on `Ioo (-T) T ×ˢ ball x r`.  The proof
extends `f` to a holomorphic `F` on a complex ball (`p11_complexification`), runs the complex-time
Picard iteration of `PicardComplex` (holomorphic iterates, geometric uniform convergence,
holomorphic limit by `KAM.Weighted.uniform_limit_holomorphic`), restricts the limit to real time
and real data, and differentiates the resulting integral equation.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology

namespace KAM.Planetary

variable {n : ℕ}

/-- The real-linear embedding `(t, y) ↦ (t, y₁, …, yₙ) ∈ ℂⁿ⁺¹`. -/
def p11cPt (n : ℕ) : ℝ × (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => (Fin.cons (z.1 : ℂ) (fun i => (z.2 i : ℂ)) : Fin (n + 1) → ℂ)
      map_add' := fun a b => by
        ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      map_smul' := fun a z => by
        ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp }

@[simp] theorem p11cPt_zero (z : ℝ × (Fin n → ℝ)) : p11cPt n z 0 = z.1 := by
  simp [p11cPt]

@[simp] theorem p11cPt_succ (z : ℝ × (Fin n → ℝ)) (i : Fin n) : p11cPt n z i.succ = z.2 i := by
  simp [p11cPt]

theorem p11cSp_p11cPt (z : ℝ × (Fin n → ℝ)) : p11cSp n (p11cPt n z) = realInclusion n z.2 := by
  ext i; simp

theorem p11cTimeScale_p11cPt (σ t : ℝ) (y : Fin n → ℝ) :
    p11cTimeScale n σ (p11cPt n (t, y)) = p11cPt n (σ * t, y) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [p11cTimeScale_zero]
  · have := congrFun (p11cSp_timeScale (n := n) σ (p11cPt n (t, y))) j
    simpa using this

theorem p11cIsReal_realInclusion (y : Fin n → ℝ) : p11cIsReal (realInclusion n y) := fun i => by
  simp

theorem p11c_eq_realInclusion {X : Fin n → ℂ} (h : p11cIsReal X) :
    X = realInclusion n (realPartCLM n X) := by
  ext i; exact Complex.ext (by simp) (by simpa using h i)

/-- From the integral equation `Φ t = y + t ∫₀¹ g (σ t) dσ` to `Φ' = g`. -/
theorem p11c_hasDerivAt_of_integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g Φ : ℝ → E} {y : E} {T : ℝ} (hg : ContinuousOn g (Ioo (-T) T))
    (heq : ∀ t ∈ Ioo (-T) T, Φ t = y + t • ∫ σ in (0 : ℝ)..1, g (σ * t)) :
    ∀ t ∈ Ioo (-T) T, HasDerivAt Φ (g t) t := by
  have hint : ∀ t ∈ Ioo (-T) T, Φ t = y + ∫ τ in (0 : ℝ)..t, g τ := by
    intro t ht
    rw [heq t ht]
    by_cases h0 : t = 0
    · simp [h0]
    · congr 1
      have := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1) g h0
      simp only [mul_zero, mul_one] at this
      simp_rw [mul_comm _ t] at *
      rw [this, smul_inv_smul₀ h0]
  intro t₀ ht₀
  have hsub : uIcc (0 : ℝ) t₀ ⊆ Ioo (-T) T :=
    (ordConnected_Ioo).uIcc_subset ⟨by linarith [ht₀.1, ht₀.2], by linarith [ht₀.1, ht₀.2]⟩ ht₀
  have hF : HasDerivAt (fun t => ∫ τ in (0 : ℝ)..t, g τ) (g t₀) t₀ :=
    intervalIntegral.integral_hasDerivAt_right (hg.mono hsub |>.intervalIntegrable)
      (hg.stronglyMeasurableAtFilter isOpen_Ioo _ ht₀)
      ((hg.continuousAt (isOpen_Ioo.mem_nhds ht₀)))
  refine (hF.const_add y).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ht₀] with t ht using hint t ht

/-- Joint real analyticity of the local flow of a real analytic vector field on `ℝⁿ`. -/
theorem p11c_analytic_flow_fin {f : (Fin n → ℝ) → Fin n → ℝ} {W : Set (Fin n → ℝ)}
    {x : Fin n → ℝ} (hf : AnalyticAt ℝ f x) (hW : W ∈ 𝓝 x) :
    ∃ r T : ℝ, 0 < r ∧ 0 < T ∧ ∃ Φ : ℝ → (Fin n → ℝ) → Fin n → ℝ,
      AnalyticOnNhd ℝ (fun u : ℝ × (Fin n → ℝ) => Φ u.1 u.2) (Ioo (-T) T ×ˢ ball x r) ∧
      ∀ y ∈ ball x r, Φ 0 y = y ∧ KAM.ODE.IsSolutionIn f W (Ioo (-T) T) (fun t => Φ t y) := by
  obtain ⟨R₀, hR₀, F, hFd, hFr⟩ := p11_complexification hf
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hW
  have hRpos : 0 < min R₀ ε := lt_min hR₀ hε
  obtain ⟨M, L, T, r, hT, hr, hD⟩ := p11c_picardData_exists hRpos
    (hFd.mono (ball_subset_ball (min_le_left _ _)))
  set ρ := min R₀ ε / 2 with hρ
  have hρR₀ : ρ ≤ R₀ := by linarith [min_le_left R₀ ε]
  have hρε : ρ ≤ ε := by linarith [min_le_right R₀ ε]
  set c := realInclusion n x with hc
  set u := P11cPicardData.lim F with hu
  have hUo : IsOpen (p11cDom n c T r) := isOpen_p11cDom c T r
  have hmemU : ∀ t : ℝ, ∀ y : Fin n → ℝ, |t| < T → y ∈ ball x r →
      p11cPt n (t, y) ∈ p11cDom n c T r := by
    intro t y ht hy
    refine ⟨by simpa using ht, ?_⟩
    rw [p11cSp_p11cPt, ← map_sub, norm_realInclusion]
    exact mem_ball_iff_norm.1 hy
  have hreal : ∀ z ∈ ball c ρ, p11cIsReal z → p11cIsReal (F z) := by
    intro z hz hzr
    have hz' := p11c_eq_realInclusion hzr
    have hy : ‖realPartCLM n z - x‖ < R₀ := by
      rw [mem_ball_iff_norm, hz', hc, ← map_sub, norm_realInclusion] at hz
      linarith
    rw [hz', hFr _ hy]
    exact p11cIsReal_realInclusion _
  -- the real flow
  let Φ : ℝ → (Fin n → ℝ) → Fin n → ℝ := fun t y => realPartCLM n (u (p11cPt n (t, y)))
  have hK : ∀ t y, |t| < T → y ∈ ball x r →
      u (p11cPt n (t, y)) = realInclusion n (Φ t y) ∧ ‖Φ t y - x‖ < ρ ∧
      F (u (p11cPt n (t, y))) = realInclusion n (f (Φ t y)) := by
    intro t y ht hy
    have hU := hmemU t y ht hy
    have hr' : p11cIsReal (u (p11cPt n (t, y))) :=
      hD.lim_isReal hreal hU (by simp) (by rw [p11cSp_p11cPt]; exact p11cIsReal_realInclusion _)
    have h1 := p11c_eq_realInclusion hr'
    have h2 : ‖Φ t y - x‖ < ρ := by
      have : ‖u (p11cPt n (t, y)) - c‖ < ρ := mem_ball_iff_norm.1 (hD.lim_mem hU)
      rw [h1, hc, ← map_sub, norm_realInclusion] at this
      exact this
    refine ⟨h1, h2, ?_⟩
    have : u (p11cPt n (t, y)) = realInclusion n (Φ t y) := h1
    rw [this, hFr _ (h2.trans_le hρR₀)]
  have hFu : ContinuousOn (fun ζ => F (u ζ)) (p11cDom n c T r) :=
    (hD.holo.comp hD.lim_differentiableOn fun ζ hζ => hD.lim_mem hζ).continuousOn
  have hcontΦ : ∀ y ∈ ball x r, ContinuousOn (fun t => Φ t y) (Ioo (-T) T) := by
    intro y hy t ht
    have hz : ContinuousAt (fun τ : ℝ => p11cPt n (τ, y)) t := by fun_prop
    have hu' : ContinuousAt u (p11cPt n (t, y)) :=
      (hD.lim_differentiableOn.continuousOn).continuousAt
        (hUo.mem_nhds (hmemU t y (abs_lt.2 ht) hy))
    exact ((realPartCLM n).continuous.continuousAt.comp
      (hu'.comp (f := fun τ : ℝ => p11cPt n (τ, y)) hz)).continuousWithinAt
  refine ⟨r, T, hr, hT, Φ, ?_, fun y hy => ?_⟩
  · -- joint analyticity
    intro z hz
    have hU := hmemU z.1 z.2 (abs_lt.2 hz.1) hz.2
    have han : AnalyticAt ℂ u (p11cPt n z) :=
      analyticOnNhd_of_differentiableOn hUo hD.lim_differentiableOn _ hU
    have h1 : AnalyticAt ℝ (fun w : ℝ × (Fin n → ℝ) => u (p11cPt n w)) z :=
      (han.restrictScalars (𝕜 := ℝ)).comp ((p11cPt n).analyticAt z)
    exact ((realPartCLM n).analyticAt _).comp h1
  · have hy0 : (0 : ℝ) ∈ Ioo (-T) T := ⟨by linarith, hT⟩
    have hb := hD.lim_bound (hmemU 0 y (by simpa using hT) hy)
    have hb2 : ‖u (p11cPt n (0, y)) - p11cSp n (p11cPt n (0, y))‖ ≤ 0 :=
      hb.trans (by simp)
    have hb3 := sub_eq_zero.1 (norm_le_zero_iff.1 hb2)
    have hΦ0 : Φ 0 y = y := by
      show realPartCLM n (u (p11cPt n (0, y))) = y
      rw [hb3, p11cSp_p11cPt, realPartCLM_realInclusion]
    refine ⟨hΦ0, fun t ht => ?_⟩
    obtain ⟨hK1, hK2, hK3⟩ := hK t y (abs_lt.2 ht) hy
    have hxW : Φ t y ∈ W := hεW (by rw [mem_ball_iff_norm]; exact hK2.trans_le hρε)
    refine ⟨hxW, ?_⟩
    -- integral equation
    have heq : ∀ t ∈ Ioo (-T) T, Φ t y = y + t • ∫ σ in (0 : ℝ)..1, f (Φ (σ * t) y) := by
      intro t ht
      have hU := hmemU t y (abs_lt.2 ht) hy
      have hfix := hD.lim_fixed hU
      have hint := p11c_intervalIntegrable_scale hFu hU
      have hσ : ∀ σ ∈ Icc (0 : ℝ) 1, |σ * t| < T := fun σ hσ => by
        rw [abs_mul, abs_of_nonneg hσ.1]
        calc σ * |t| ≤ 1 * |t| := mul_le_mul_of_nonneg_right hσ.2 (abs_nonneg _)
          _ < T := by simpa using abs_lt.2 ht
      have := congrArg (realPartCLM n) hfix
      simp only [p11cPicardOp, map_add, p11cPt_zero, p11cSp_p11cPt, realPartCLM_realInclusion] at this
      rw [realPartCLM_ofReal_smul,
        ← ContinuousLinearMap.intervalIntegral_comp_comm (realPartCLM n) hint] at this
      refine this.trans ?_
      congr 2
      refine intervalIntegral.integral_congr fun σ hσ' => ?_
      rw [uIcc_of_le zero_le_one] at hσ'
      simp only [p11cTimeScale_p11cPt]
      rw [(hK _ y (hσ σ hσ') hy).2.2, realPartCLM_realInclusion]
    have hg : ContinuousOn (fun τ => f (Φ τ y)) (Ioo (-T) T) := by
      refine ContinuousOn.congr (f := fun τ => realPartCLM n (F (u (p11cPt n (τ, y))))) ?_ ?_
      · intro τ hτ
        have hz : ContinuousAt (fun τ : ℝ => p11cPt n (τ, y)) τ := by fun_prop
        have := hFu.continuousAt (hUo.mem_nhds (hmemU τ y (abs_lt.2 hτ) hy))
        exact ((realPartCLM n).continuous.continuousAt.comp
          (this.comp (f := fun τ : ℝ => p11cPt n (τ, y)) hz)).continuousWithinAt
      · intro τ hτ
        simp only [(hK τ y (abs_lt.2 hτ) hy).2.2, realPartCLM_realInclusion]
    exact p11c_hasDerivAt_of_integral_eq (Φ := fun t => Φ t y) hg heq t ht

/-- The Hamiltonian vector field of a function analytic at `x` is analytic at `x`. -/
theorem p11c_hamField_analyticAt {d : ℕ} {H : Phase d → ℝ} {x : Phase d}
    (hH : AnalyticAt ℝ H x) : AnalyticAt ℝ (hamiltonianVectorField H) x := by
  have hD : AnalyticAt ℝ (fderiv ℝ H) x := hH.fderiv
  have hc : ∀ v : Phase d, AnalyticAt ℝ (fun z => fderiv ℝ H z v) x := fun v =>
    ((ContinuousLinearMap.apply ℝ ℝ v).analyticAt _).comp hD
  refine AnalyticAt.prod (AnalyticAt.pi fun i => hc _) (AnalyticAt.pi fun i => ?_)
  exact (hc _).neg

/-- The coordinate identification `Phase d ≃L[ℝ] ℝ^(d+d)`. -/
def p11cPhaseEquiv (d : ℕ) : Phase d ≃L[ℝ] (Fin (d + d) → ℝ) :=
  ((LinearEquiv.sumArrowLequivProdArrow (Fin d) (Fin d) ℝ ℝ).symm.trans
    (LinearEquiv.funCongrLeft ℝ ℝ (finSumFinEquiv (m := d) (n := d)).symm)).toContinuousLinearEquiv

/-- Joint real analyticity of the local Hamiltonian flow (the analytic and solution clauses of
`real_analytic_hamiltonian_local_flow`; symplecticity is the subject of package R3). -/
theorem p11c_analytic_hamiltonian_flow {d : ℕ} {W : Set (Phase d)} (hW : IsOpen W)
    {H : Phase d → ℝ} (hH : AnalyticOnNhd ℝ H W) {x : Phase d} (hx : x ∈ W) :
    ∃ r T : ℝ, 0 < r ∧ 0 < T ∧ ∃ Φ : ℝ → Phase d → Phase d,
      AnalyticOnNhd ℝ (fun u : ℝ × Phase d => Φ u.1 u.2) (Ioo (-T) T ×ˢ ball x r) ∧
      ∀ y ∈ ball x r, Φ 0 y = y ∧
        KAM.ODE.IsSolutionIn (hamiltonianVectorField H) W (Ioo (-T) T) (fun t => Φ t y) := by
  set e := p11cPhaseEquiv d with he
  set f : (Fin (d + d) → ℝ) → Fin (d + d) → ℝ :=
    fun v => e (hamiltonianVectorField H (e.symm v)) with hf
  have hfa : AnalyticAt ℝ f (e x) := by
    have h1 : AnalyticAt ℝ (hamiltonianVectorField H) (e.symm (e x)) := by
      rw [e.symm_apply_apply]; exact p11c_hamField_analyticAt (hH x hx)
    exact (e.analyticAt _).comp (h1.comp (e.symm.analyticAt (e x)))
  have hW' : e.symm ⁻¹' W ∈ 𝓝 (e x) :=
    e.symm.continuous.continuousAt.preimage_mem_nhds (by rw [e.symm_apply_apply]; exact hW.mem_nhds hx)
  obtain ⟨r', T, hr', hT, Φ', han, hsol⟩ := p11c_analytic_flow_fin hfa hW'
  set N := ‖(e : Phase d →L[ℝ] (Fin (d + d) → ℝ))‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have hball : ∀ y ∈ ball x (r' / (N + 1)), e y ∈ ball (e x) r' := by
    intro y hy
    rw [mem_ball_iff_norm, lt_div_iff₀ (by positivity)] at hy
    rw [mem_ball_iff_norm, ← map_sub]
    have : ‖e (y - x)‖ ≤ N * ‖y - x‖ :=
      (e : Phase d →L[ℝ] (Fin (d + d) → ℝ)).le_opNorm (y - x)
    nlinarith [norm_nonneg (y - x)]
  refine ⟨r' / (N + 1), T, by positivity, hT, fun t y => e.symm (Φ' t (e y)), ?_, fun y hy => ?_⟩
  · intro z hz
    have h1 := han (z.1, e z.2) ⟨hz.1, hball z.2 hz.2⟩
    have h2 : AnalyticAt ℝ (fun w : ℝ × Phase d => (w.1, e w.2)) z :=
      AnalyticAt.prod analyticAt_fst ((e.analyticAt _).comp analyticAt_snd)
    exact (e.symm.analyticAt _).comp
      (AnalyticAt.comp (g := fun u : ℝ × (Fin (d + d) → ℝ) => Φ' u.1 u.2)
        (f := fun w : ℝ × Phase d => (w.1, e w.2)) h1 h2)
  · obtain ⟨h0, hs⟩ := hsol (e y) (hball y hy)
    refine ⟨by simp [h0], fun t ht => ?_⟩
    obtain ⟨hm, hd⟩ := hs t ht
    refine ⟨hm, ?_⟩
    have h2 := e.symm.hasFDerivAt.comp_hasDerivAt t hd
    exact h2.congr_deriv (by simp [hf])

end KAM.Planetary
