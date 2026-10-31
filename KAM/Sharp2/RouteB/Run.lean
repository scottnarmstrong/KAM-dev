/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteB.Step
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The run of route B: (N1), (N2), the flag along the run, monotonicity in `X₀`

* `RunHyp.isNewton`: `schemeB` satisfies (N1), (N2) of `StageScheme.IsNewton` with the constants
  `stageC N` and the caps `capB N σ_T μ 0`; at the matched pair `(r_s, δ_s)` of a flagged state it
  is `RunHyp.good_step`, elsewhere the torus is unchanged and the flag cleared;
* `iterB_spec`: along the run `x_{s+1} = Φ(r_s, δ_s; x_s)` from `(0, true, K₀)`, the state is
  `(s, true, K_s)`;
* `xS_mono`, `xS_scale`, `ballSum_mono`, `ballSum_scale`: the normalized errors and the ball sum
  are nondecreasing in `X₀`, and `X_s(t X) ≤ t X_s(X)` for `t ∈ [0, 1]` (the prefix recursion is
  quadratic);
* `tendsto_fderiv_of_uniform`: uniform convergence of holomorphic maps on a strip gives
  convergence of the derivatives at every point of the strip (Cauchy on the difference).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology MeasureTheory

namespace KAM.Sharp2.RouteB

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.ModStepB

variable {n : ℕ} {N : NumB n} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)} {γ σT μm Xi : ℝ}
  {K0 : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- (N1), (N2) for the scheme of route B. -/
theorem RunHyp.isNewton (R : RunHyp N 𝔅 h ω Ω γ σT μm K0) :
    (schemeB N 𝔅 h ω γ Xi K0).IsNewton N.τ γ (bite0R N.a N.ρ N.ρinf) (stageC N)
      (capB N σT μm 0) where
  regular := by
    intro r β w m x hx
    rcases x with ⟨s, b, K⟩
    cases b
    · exact hx
    · exact ⟨hx.μ_nonneg, hx.holo, hx.primary, hx.real⟩
  step := by
    intro r β w δ m x hx hδ hδm h3 hcond hβ hcap
    rcases x with ⟨s, b, K⟩
    have hnn := stageC_nonneg R.wf δ
    have hX0 : 0 ≤ w := by
      cases b
      · exact hx.1
      · exact hx.μ_nonneg
    have hg : 0 < γ * δ ^ N.τ := mul_pos R.γ_pos (Real.rpow_pos_of_pos hδ _)
    have hg1 : 0 < γ * δ ^ (N.τ + 1) := mul_pos R.γ_pos (Real.rpow_pos_of_pos hδ _)
    by_cases hm : b = true ∧ r = N.r s ∧ δ = N.δ s
    · obtain ⟨rfl, rfl, rfl⟩ := hm
      have hG : Good N 𝔅 h ω γ Xi K0 s (N.r s) β w m K := hx
      rw [stageC_sched R.wf] at hcond hβ hcap ⊢
      obtain ⟨hG', hcl⟩ := R.good_step hG hcond hβ hcap
      have hstep : (schemeB N 𝔅 h ω γ Xi K0).step (N.r s) (N.δ s) (s, true, K) =
          (s + 1, true, modNewton h K ω (N.r s - 2 * N.δ s)) := by
        simp [schemeB]
      rw [hstep]
      refine ⟨hG', hcl, ?_⟩
      show |(0 : ℝ) - 0| ≤ _
      rw [sub_self, abs_zero]
      have := (stageC_nonneg R.wf (N.δ s)).2.2.1
      rw [stageC_sched R.wf] at this
      exact mul_nonneg this hX0
    · have hstep : (schemeB N 𝔅 h ω γ Xi K0).step r δ (s, b, K) = (s + 1, false, K) := by
        simp only [schemeB]
        split_ifs
        rfl
      rw [hstep]
      have hreg : DifferentiableOn ℂ K (complexStrip n r) ∧ IsPrimaryOnStrip K r ∧
          IsRealOnReals K := by
        cases b
        · exact hx.2
        · exact ⟨hx.holo, hx.primary, hx.real⟩
      refine ⟨junk_mono (by linarith) (by have := hnn.1; positivity) hreg, fun θ _ => ?_, ?_⟩
      · show ‖K θ - K θ‖ ≤ _
        rw [sub_self, norm_zero]
        have := hnn.2.1
        positivity
      · show |(0 : ℝ) - 0| ≤ _
        rw [sub_self, abs_zero]
        exact mul_nonneg hnn.2.2.1 hX0

/-- The iterates of route B. -/
def iterB (N : NumB n) (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ω : Fin n → ℝ) (γ Xi : ℝ)
    (K0 : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (s : ℕ) : StB n :=
  Nat.rec ((0, true, K0) : StB n) (fun j x => (schemeB N 𝔅 h ω γ Xi K0).step
    (stripSR N.a N.ρ N.ρinf j) (biteSR N.a N.ρ N.ρinf j) x) s

/-- Along the run the state is `(s, true, K_s)`. -/
theorem iterB_spec (s : ℕ) :
    (iterB N 𝔅 h ω γ Xi K0 s).1 = s ∧ (iterB N 𝔅 h ω γ Xi K0 s).2.1 = true := by
  induction s with
  | zero => exact ⟨rfl, rfl⟩
  | succ s ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : iterB N 𝔅 h ω γ Xi K0 (s + 1) = (schemeB N 𝔅 h ω γ Xi K0).step
        (stripSR N.a N.ρ N.ρinf s) (biteSR N.a N.ρ N.ρinf s) (iterB N 𝔅 h ω γ Xi K0 s) := rfl
    rcases hx : iterB N 𝔅 h ω γ Xi K0 s with ⟨s', b, K⟩
    rw [hx] at h1 h2
    simp only at h1 h2
    subst h1 h2
    rw [e, hx]
    simp [schemeB, NumB.r, NumB.δ]

/-! ### Monotonicity in the initial normalized error -/

theorem Qs_nonneg (hN : N.Wf) (s : ℕ) : 0 ≤ N.Qs s := by
  have := (stageC_nonneg hN (N.δ s)).1
  rwa [stageC_sched hN] at this

theorem xS_nonneg (hN : N.Wf) {X : ℝ} (hX : 0 ≤ X) (s : ℕ) : 0 ≤ N.xS X s :=
  xSeqR_nonneg hN.a_pos (Qs_nonneg hN) hX s

theorem xS_mono (hN : N.Wf) {X Y : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y) (s : ℕ) :
    N.xS X s ≤ N.xS Y s := by
  induction s with
  | zero => exact hXY
  | succ s ih =>
    show N.a ^ (N.τ + 1) * N.Qs s * N.xS X s ^ 2 ≤ N.a ^ (N.τ + 1) * N.Qs s * N.xS Y s ^ 2
    have hc : 0 ≤ N.a ^ (N.τ + 1) * N.Qs s :=
      mul_nonneg (Real.rpow_nonneg hN.a_pos.le _) (Qs_nonneg hN s)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (xS_nonneg hN hX s) ih 2) hc

theorem xS_scale (hN : N.Wf) {X t : ℝ} (hX : 0 ≤ X) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (s : ℕ) :
    N.xS (t * X) s ≤ t * N.xS X s := by
  induction s with
  | zero => exact le_rfl
  | succ s ih =>
    show N.a ^ (N.τ + 1) * N.Qs s * N.xS (t * X) s ^ 2 ≤
      t * (N.a ^ (N.τ + 1) * N.Qs s * N.xS X s ^ 2)
    have hc : 0 ≤ N.a ^ (N.τ + 1) * N.Qs s :=
      mul_nonneg (Real.rpow_nonneg hN.a_pos.le _) (Qs_nonneg hN s)
    have h0 := xS_nonneg hN (mul_nonneg ht0 hX) s
    have h1 := xS_nonneg hN hX s
    have hsq : N.xS (t * X) s ^ 2 ≤ t * N.xS X s ^ 2 := by
      calc N.xS (t * X) s ^ 2 ≤ (t * N.xS X s) ^ 2 := pow_le_pow_left₀ h0 ih 2
        _ = t * (t * N.xS X s ^ 2) := by ring
        _ ≤ 1 * (t * N.xS X s ^ 2) :=
            mul_le_mul_of_nonneg_right ht1 (by positivity)
        _ = t * N.xS X s ^ 2 := one_mul _
    calc _ ≤ N.a ^ (N.τ + 1) * N.Qs s * (t * N.xS X s ^ 2) := mul_le_mul_of_nonneg_left hsq hc
      _ = _ := by ring

theorem CDK_nonneg (hN : N.Wf) (s : ℕ) : 0 ≤ (stepConstsB (N.inp s)).CDK :=
  (stepConstsB_nonneg (hN.inp_ok s)).2.1

theorem ballSum_mono (hN : N.Wf) {X Y : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y) :
    N.ballSum X ≤ N.ballSum Y := by
  have hy1 : 0 < 1 - N.ybar := by linarith [hN.ybar.2]
  unfold NumB.ballSum
  refine add_le_add (Finset.sum_le_sum fun s _ => ?_) ?_
  · exact mul_le_mul_of_nonneg_left (xS_mono hN hX hXY s)
      (mul_nonneg (CDK_nonneg hN s) (hN.δ_pos s).le)
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (xS_mono hN hX hXY _)
      (mul_nonneg (CDK_nonneg hN _) (hN.δ_pos _).le)) hy1.le

theorem ballSum_scale (hN : N.Wf) {X t : ℝ} (hX : 0 ≤ X) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    N.ballSum (t * X) ≤ t * N.ballSum X := by
  have hy1 : 0 < 1 - N.ybar := by linarith [hN.ybar.2]
  unfold NumB.ballSum
  rw [mul_add, Finset.mul_sum]
  refine add_le_add (Finset.sum_le_sum fun s _ => ?_) ?_
  · calc _ ≤ (stepConstsB (N.inp s)).CDK * N.δ s * (t * N.xS X s) :=
          mul_le_mul_of_nonneg_left (xS_scale hN hX ht0 ht1 s)
            (mul_nonneg (CDK_nonneg hN s) (hN.δ_pos s).le)
      _ = _ := by ring
  · rw [mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ hy1.le
    calc _ ≤ (stepConstsB (N.inp N.kp)).CDK * N.δ N.kp * (t * N.xS X N.kp) :=
          mul_le_mul_of_nonneg_left (xS_scale hN hX ht0 ht1 _)
            (mul_nonneg (CDK_nonneg hN _) (hN.δ_pos _).le)
      _ = _ := by ring

/-! ### Convergence of the derivatives -/

/-- A point of an open strip lies in a strictly smaller strip. -/
theorem exists_strip_margin (hn : 0 < n) {ρ : ℝ} {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ) :
    ∃ d, 0 < d ∧ θ ∈ complexStrip n (ρ - d) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min (fun i : Fin n => ρ - |(θ i).im|)
  have hpos : 0 < ρ - |(θ i₀).im| := by linarith [hθ i₀]
  refine ⟨(ρ - |(θ i₀).im|) / 2, by linarith, fun i => ?_⟩
  have := hi₀ i
  linarith

/-- Uniform convergence of holomorphic maps on a strip gives convergence of the derivatives at
every point of the strip (Cauchy on `K_s - L`). -/
theorem tendsto_fderiv_of_uniform (hn : 0 < n) {ρ : ℝ}
    {Ks : ℕ → (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {L : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hKs : ∀ s, DifferentiableOn ℂ (Ks s) (complexStrip n ρ))
    (hL : DifferentiableOn ℂ L (complexStrip n ρ))
    (hconv : TendstoUniformlyOn Ks L atTop (complexStrip n ρ)) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n ρ) :
    Tendsto (fun s => fderiv ℂ (Ks s) θ) atTop (𝓝 (fderiv ℂ L θ)) := by
  obtain ⟨d, hd, hθd⟩ := exists_strip_margin hn hθ
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hε' : 0 < ε * d / (n + 1) := by positivity
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hconv _ hε')
  refine ⟨S, fun s hs => ?_⟩
  have hb : ∀ y ∈ complexStrip n ρ, ‖Ks s y - L y‖ ≤ ε * d / (n + 1) := fun y hy => by
    rw [← dist_eq_norm, dist_comm]; exact (hS s hs y hy).le
  have hg : DifferentiableOn ℂ (fun y => Ks s y - L y) (complexStrip n ρ) := (hKs s).sub hL
  have hc := (cauchy_strip hg hb hd).2 θ hθd
  have hnhds := (isOpen_complexStrip n ρ).mem_nhds hθ
  rw [fderiv_fun_sub ((hKs s).differentiableAt hnhds) (hL.differentiableAt hnhds)] at hc
  rw [dist_eq_norm]
  calc _ ≤ n * d⁻¹ * (ε * d / (n + 1)) := hc
    _ = ε * (n / (n + 1)) := by field_simp
    _ < ε * 1 := mul_lt_mul_of_pos_left (by rw [div_lt_one hn1]; linarith) hε
    _ = ε := mul_one ε

end KAM.Sharp2.RouteB

end
