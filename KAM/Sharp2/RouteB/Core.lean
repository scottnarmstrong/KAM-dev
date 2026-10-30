/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteB.Run
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The theorem of route B (blueprint `bp:p2s2:g1`, route B)

`RunHyp.core`: from `routeBOk` at `X⋆` and a flagged initial state of stage `0` with normalized
error `X_i ≤ X⋆` (weighted error `γ δ₀^{τ+1} X_i`), the engine `StageScheme.converge_ratio`
(SHARP2-B5R) applied to `schemeB` gives a holomorphic, primary, real limit torus on `T_{ρ∞}` with

* `E(K∞) = 0`: the iterates are flagged (`iterB_spec`), so the engine's admissibility of the
  iterates is `Good`; their local data (`RunHyp.loc`) give `|E(K_s)| ≤ C_E μ̄_s → 0` on
  `T_{r_s-δ_s} ⊇ T_{ρ∞}`, and the derivatives converge (`tendsto_fderiv_of_uniform`), so
  `KAM.Apost.lim_invariance` applies;
* `|DK∞| ≤ σ_K` (the cap of `DK`) and `|K∞ - K₀| ≤` the ball sum at `X_i`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology MeasureTheory

namespace KAM.Sharp2.RouteB

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.ModStepB

variable {n : ℕ} {N : NumB n} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)} {γ σT μm : ℝ}
  {K0 : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- The engine's normalized errors are `N.xS`. -/
theorem engine_xS (hN : N.Wf) {γ Xi : ℝ} (hγ : 0 < γ) :
    xSeqR N.a (N.τ + 1) (fun s => (stageC N (biteSR N.a N.ρ N.ρinf s)).Q)
        (γ * N.δ0 ^ (N.τ + 1) * Xi / (γ * bite0R N.a N.ρ N.ρinf ^ (N.τ + 1))) = N.xS Xi := by
  have hQ : (fun s => (stageC N (biteSR N.a N.ρ N.ρinf s)).Q) = N.Qs :=
    funext fun s => by rw [show biteSR N.a N.ρ N.ρinf s = N.δ s from rfl, stageC_sched hN]; rfl
  have hp : 0 < γ * N.δ0 ^ (N.τ + 1) := mul_pos hγ (Real.rpow_pos_of_pos hN.δ0_pos _)
  have hX : γ * N.δ0 ^ (N.τ + 1) * Xi / (γ * bite0R N.a N.ρ N.ρinf ^ (N.τ + 1)) = Xi := by
    change γ * N.δ0 ^ (N.τ + 1) * Xi / (γ * N.δ0 ^ (N.τ + 1)) = Xi
    rw [mul_div_cancel_left₀ _ hp.ne']
  rw [hQ, hX]
  rfl

/-- The tail decay of the run at `X_i ≤ X⋆`. -/
theorem xS_tail (hN : N.Wf) {σ m₀ : Fin 7 → ℝ} {β Xi Xs : ℝ} (hOk : routeBOk N σ m₀ β Xs)
    (hXi0 : 0 ≤ Xi) (hXi : Xi ≤ Xs) :
    ∀ s, N.kp ≤ s → N.xS Xi s ≤ N.xS Xi N.kp * N.ybar ^ (s - N.kp) := by
  refine xSeqR_tail hN.a_pos hN.ybar.1.le hN.ybar.2.le (Qs_nonneg hN) hXi0
    (fun s hs => by rw [show N.Qs s = N.Qs N.kp by
      simp only [NumB.Qs, hN.inp_tail hs]]) ?_
  refine le_trans ?_ hOk.J2
  exact mul_le_mul_of_nonneg_left (xS_mono hN hXi0 hXi _)
    (mul_nonneg (Real.rpow_nonneg hN.a_pos.le _) (Qs_nonneg hN _))

/-- The step conditions hold along the run at `X_i ≤ X⋆`, at any normalized error `≤ X_s(X_i)`. -/
theorem cond_run (hN : N.Wf) {σ m₀ : Fin 7 → ℝ} {β Xi Xs : ℝ} (hOk : routeBOk N σ m₀ β Xs)
    (hXi0 : 0 ≤ Xi) (hXi : Xi ≤ Xs) {s : ℕ} {X : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ N.xS Xi s) :
    stepCondB (N.inp s) X := by
  by_cases hs : s < N.kp
  · exact stepCondB_anti (hN.inp_ok s) hX0 (hX.trans (xS_mono hN hXi0 hXi s)) (hOk.J1 s hs)
  · have hs' := not_lt.1 hs
    rw [hN.inp_tail hs']
    refine hOk.J1t X hX0 (hX.trans ?_)
    have h1 := xS_tail hN hOk hXi0 hXi s hs'
    have h2 : N.xS Xi N.kp * N.ybar ^ (s - N.kp) ≤ N.xS Xi N.kp :=
      mul_le_of_le_one_right (xS_nonneg hN hXi0 _) (pow_le_one₀ hN.ybar.1.le hN.ybar.2.le)
    exact h1.trans (h2.trans (xS_mono hN hXi0 hXi _))

/-- The ball sum of the engine is `N.ballSum`. -/
theorem engine_ball (hN : N.Wf) {γ Xi : ℝ} (hγ : 0 < γ) :
    stageBallR N.a N.τ γ N.ρ N.ρinf (γ * N.δ0 ^ (N.τ + 1) * Xi) N.ybar (stageC N) N.kp
      (N.stage N.kp) = N.ballSum Xi := by
  unfold stageBallR
  rw [engine_xS hN hγ]
  unfold NumB.ballSum
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show biteSR N.a N.ρ N.ρinf s = N.δ s from rfl, stageC_sched hN]
  rfl

/-- Blueprint `bp:p2s2:g1`, route B: the run from a flagged initial state. -/
theorem RunHyp.core (R : RunHyp N 𝔅 h ω Ω γ σT μm K0) {τ0 M0 σK0 σB0 σT0 γ0 : ℝ}
    (hS : Standing n τ0 M0 σK0 σB0 σT0 𝔅 h ω γ0) {β0 Xi Xs : ℝ} {m₀ : Fin 7 → ℝ}
    (hOk : routeBOk N (capB N σT μm 0) m₀ β0 Xs) (hXi0 : 0 ≤ Xi) (hXi : Xi ≤ Xs)
    (h0 : Good N 𝔅 h ω γ Xi K0 0 N.ρ β0 (γ * N.δ0 ^ (N.τ + 1) * Xi) m₀ K0) :
    ∃ Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip n N.ρinf) ∧ IsPrimaryOnStrip Kinf N.ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip n N.ρinf, invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip n N.ρinf, ‖fderiv ℂ Kinf θ‖ ≤ N.sK) ∧
      ∀ θ ∈ complexStrip n N.ρinf, ‖Kinf θ - K0 θ‖ ≤ N.ballSum Xi := by
  have hN := R.wf
  have hγ := R.γ_pos
  have hn : 0 < n := by have := hN.two_le; omega
  have hNw := R.isNewton (Xi := Xi)
  have hx₀ : (schemeB N 𝔅 h ω γ Xi K0).Adm N.ρ β0 (γ * N.δ0 ^ (N.τ + 1) * Xi) m₀
      ((0, true, K0) : StB n) := h0
  have hXe := engine_xS hN (Xi := Xi) hγ
  have hBe := engine_ball hN (Xi := Xi) hγ
  have hrw : ∀ s, stageC N (biteSR N.a N.ρ N.ρinf s) = N.stage s := fun s =>
    stageC_sched hN s
  have hy1 : 0 < 1 - N.ybar := by linarith [hN.ybar.2]
  obtain ⟨Kinf, -, hholo, hprim, hreal, hadm, hconv, hclose⟩ :=
    StageScheme.converge_ratio (S := schemeB N 𝔅 h ω γ Xi K0) (κ := N.τ) (γ := γ) (ρ := N.ρ)
      (ρinf := N.ρinf) (β₀ := β0) (μ₀ := γ * N.δ0 ^ (N.τ + 1) * Xi) (a := N.a) (ybar := N.ybar)
      (C := stageC N) (σ := capB N σT μm 0) (m₀ := m₀) (x₀ := ((0, true, K0) : StB n)) N.kp
      (N.stage N.kp) hNw hN.a_gt hN.ybar.1 hN.ybar.2 hγ hN.ρinf_pos hN.ρinf_lt hx₀
      (fun δ _ hδk => by
        rw [stageC_tail hN hδk]
        exact ⟨le_rfl, fun X hX => hX, le_rfl, le_rfl, fun i => le_rfl⟩)
      (fun s hs => by
        rw [hXe, hrw]
        exact cond_run hN hOk hXi0 hXi (xS_nonneg hN hXi0 s) le_rfl)
      (by
        rw [hXe]
        refine le_trans ?_ hOk.J2
        exact mul_le_mul_of_nonneg_left (xS_mono hN hXi0 hXi _)
          (mul_nonneg (Real.rpow_nonneg hN.a_pos.le _) (Qs_nonneg hN _)))
      (fun i => by
        rw [hXe]
        refine le_trans ?_ (hOk.J3 i)
        have hw : ∀ s, 0 ≤ N.rate s i * N.wt s i := fun s => by
          have := (stageC_nonneg hN (N.δ s)).2.2.2 i
          rwa [stageC_sched hN] at this
        refine add_le_add (add_le_add le_rfl (Finset.sum_le_sum fun s _ => ?_)) ?_
        · rw [hrw]
          exact mul_le_mul_of_nonneg_left (xS_mono hN hXi0 hXi s) (hw s)
        · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
            (xS_mono hN hXi0 hXi _) (hw _)) hy1.le)
      (fun δ _ _ => by
        obtain ⟨h1, h2, -, h4⟩ := stageC_nonneg hN δ
        exact ⟨h1, h2, h4⟩)
      (fun X hX0 hX => by
        rw [hXe] at hX
        exact cond_run hN hOk hXi0 hXi (s := N.kp) hX0 hX)
      (by rw [hBe]; exact (ballSum_mono hN hXi0 hXi).trans_lt hOk.J4)
  -- the iterates
  set Ks : ℕ → (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) :=
    fun s => (iterB N 𝔅 h ω γ Xi K0 s).2.2 with hKs
  have hgood : ∀ s, ∃ β w m, Good N 𝔅 h ω γ Xi K0 s (N.r s) β w m (Ks s) ∧
      ∀ i, m i ≤ capB N σT μm 0 i := by
    intro s
    obtain ⟨r, β, w, m, hA, -, hm⟩ := hadm s
    have hA' : (schemeB N 𝔅 h ω γ Xi K0).Adm r β w m (iterB N 𝔅 h ω γ Xi K0 s) := hA
    obtain ⟨h1, h2⟩ := iterB_spec (N := N) (𝔅 := 𝔅) (h := h) (ω := ω) (γ := γ) (Xi := Xi)
      (K0 := K0) s
    have hG : Good N 𝔅 h ω γ Xi K0 s r β w m (Ks s) := by
      simp only [schemeB, h2, ↓reduceIte, h1] at hA'
      exact hA'
    have hr := hG.r_eq
    subst hr
    exact ⟨β, w, m, hG, hm⟩
  have hsub : ∀ s, complexStrip n N.ρinf ⊆ complexStrip n (N.r s - N.δ s) := fun s =>
    Triangular.strip_mono (by
      have := hN.r_succ s; have := hN.r_gt (s + 1); have := hN.δ_pos s; linarith)
  have hsubr : ∀ s, complexStrip n N.ρinf ⊆ complexStrip n (N.r s) := fun s =>
    Triangular.strip_mono (hN.r_gt s).le
  -- the errors along the run
  obtain ⟨τ1, M1, γ1, hS1⟩ := R.std
  set ε : ℕ → ℝ := fun s => sCE (N.inp s) * (γ * N.δ s ^ (N.τ + 1) * N.xS Xi s) with hε
  have hE : ∀ s, ∀ θ ∈ complexStrip n N.ρinf, ‖invarianceError h (Ks s) ω θ‖ ≤ ε s := by
    intro s θ hθ
    obtain ⟨β, w, m, hG, hm⟩ := hgood s
    have hw0 := hG.μ_nonneg
    have hX : w / (γ * N.δ s ^ (N.τ + 1)) ≤ N.xS Xi s := by
      rw [div_le_iff₀ (R.gd1_pos s)]; linarith [hG.μ_le]
    obtain ⟨c', L⟩ := R.loc hG (cond_run hN hOk hXi0 hXi (div_nonneg hw0 (R.gd1_pos s).le) hX)
      hm
    have h1 := L.E_le hS1 θ (hsub s hθ)
    rw [R.mu_eq s] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hG.μ_le (nn_sCE (hN.inp_ok s)))
  have hεt : Tendsto ε atTop (𝓝 0) := by
    set C := sCE (N.inp N.kp) * γ * N.xS Xi N.kp with hC
    have hC0 : 0 ≤ C := mul_nonneg (mul_nonneg (nn_sCE (hN.inp_ok _)) hγ.le)
      (xS_nonneg hN hXi0 _)
    have hg : Tendsto (fun s : ℕ => C * N.ybar ^ (s - N.kp)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hN.ybar.1.le hN.ybar.2).comp
        (tendsto_sub_atTop_nat N.kp)).const_mul C
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun s => ?_) ?_ hg
    · exact mul_nonneg (nn_sCE (hN.inp_ok s)) (mul_nonneg (mul_nonneg hγ.le
        (Real.rpow_nonneg (hN.δ_pos s).le _)) (xS_nonneg hN hXi0 s))
    · refine Filter.eventually_atTop.2 ⟨N.kp, fun s hs => ?_⟩
      have hCE : sCE (N.inp s) = sCE (N.inp N.kp) := by rw [hN.inp_tail hs]
      have hδ1 : N.δ s ^ (N.τ + 1) ≤ 1 :=
        Real.rpow_le_one (hN.δ_pos s).le (hN.δ_le_one s) (by linarith [hN.τ_pos])
      have hxt := xS_tail hN hOk hXi0 hXi s hs
      have hx0 := xS_nonneg hN hXi0 s
      have hce := nn_sCE (hN.inp_ok N.kp)
      show sCE (N.inp s) * (γ * N.δ s ^ (N.τ + 1) * N.xS Xi s) ≤ C * N.ybar ^ (s - N.kp)
      rw [hCE, hC]
      calc sCE (N.inp N.kp) * (γ * N.δ s ^ (N.τ + 1) * N.xS Xi s) ≤
          sCE (N.inp N.kp) * (γ * 1 * N.xS Xi s) := by gcongr
        _ ≤ sCE (N.inp N.kp) * (γ * 1 * (N.xS Xi N.kp * N.ybar ^ (s - N.kp))) := by gcongr
        _ = _ := by ring
  -- the derivatives
  have hKsd : ∀ s, DifferentiableOn ℂ (Ks s) (complexStrip n N.ρinf) := fun s => by
    obtain ⟨β, w, m, hG, -⟩ := hgood s
    exact hG.holo.mono (hsubr s)
  have hconv' : TendstoUniformlyOn Ks Kinf atTop (complexStrip n N.ρinf) := hconv
  have hclose' : ∀ θ ∈ complexStrip n N.ρinf, ‖Kinf θ - K0 θ‖ ≤ N.ballSum Xi := fun θ hθ => by
    have := hclose θ hθ
    rwa [hBe] at this
  have hρ0 : complexStrip n N.ρinf ⊆ complexStrip n N.ρ :=
    Triangular.strip_mono hN.ρinf_lt.le
  refine ⟨Kinf, hholo, hprim, hreal, fun θ hθ => ?_, fun θ hθ => ?_, hclose'⟩
  · have hmem : Kinf θ ∈ 𝔅 := by
      refine h0.ball θ (hρ0 hθ) ?_
      rw [Metric.mem_ball, dist_eq_norm]
      exact (hclose' θ hθ).trans_lt ((ballSum_mono hN hXi0 hXi).trans_lt hOk.J4)
    exact lim_invariance hS (Ks := Ks) (L := Kinf) (ε := ε) hmem (hconv'.tendsto_at hθ)
      (tendsto_fderiv_of_uniform hn hKsd hholo hconv' hθ) (fun s => hE s θ hθ) hεt
  · refine le_of_tendsto (tendsto_fderiv_of_uniform hn hKsd hholo hconv' hθ).norm
      (Eventually.of_forall fun s => ?_)
    obtain ⟨β, w, m, hG, hm⟩ := hgood s
    rw [← norm_colMat]
    exact (hG.L θ (hsubr s hθ)).trans (hm 0)

end KAM.Sharp2.RouteB

end
