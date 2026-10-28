/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.ODE.Basic
public import KAM.Nekhoroshev.Averaging.PicardDerivatives
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Local C¹ dependence on initial data

Blueprint N Part 12 (`bpN:p12:ext-dep#derivative-limit`, `#identify`, and `ext_dep` itself).

For `F` of class `C¹` on an open set `W` of a finite-dimensional real space we construct a local
flow `y` on `(-a, a) × ball x₀ r` that is jointly continuous, has jointly continuous
`x`-derivative, and satisfies the variational (Volterra) equation.

* `KAM.Nekhoroshev.voltIter`: the derivative iterates `Y₀ = id`,
  `Y_{m+1} = id + ∫ DF (u_m) ∘ Y_m`.
* `KAM.Nekhoroshev.voltIter_spec`: `Y_m` is continuous, bounded by `1 / (1 - a Λ)`, and is the
  `x`-derivative of the Picard iterate `u_m`.
* `KAM.Nekhoroshev.voltIter_uniform`: `Y_m` converges uniformly to the Volterra family `Y`
  (from the recurrence `‖Y_{m+1} - Y‖ ≤ q ‖Y_m - Y‖ + a d_m / (1 - q)`, `d_m → 0`).
* `KAM.Nekhoroshev.ext_dep`: the local dependence theorem.
-/

@[expose] public noncomputable section

open Set Metric Function Filter
open scoped NNReal Topology Interval Classical

namespace KAM.Nekhoroshev

section Iterates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : E → E} {F' : E → E →L[ℝ] E} {x₀ : E} {a r ρ Λ : ℝ}

/-- Continuity of a parameter-dependent interval integral over the box `[-a, a] × closedBall x₀ r`
on which the integrand is only continuous. -/
theorem continuousOn_intervalIntegral_param {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : ℝ → E → V} (ha : 0 ≤ a)
    (hg : ContinuousOn (fun p : ℝ × E => g p.1 p.2) (Icc (-a) a ×ˢ closedBall x₀ r)) :
    ContinuousOn (fun p : ℝ × E => ∫ τ in (0 : ℝ)..p.1, g τ p.2)
      (Icc (-a) a ×ˢ closedBall x₀ r) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous fun q : ↥(Icc (-a) a ×ˢ closedBall x₀ r) × ℝ =>
      g (Set.projIcc (-a) a (neg_le_self ha) q.2 : ℝ) (q.1 : ℝ × E).2 := by
    refine hg.comp_continuous (f := fun q : ↥(Icc (-a) a ×ˢ closedBall x₀ r) × ℝ =>
      ((Set.projIcc (-a) a (neg_le_self ha) q.2 : ℝ), (q.1 : ℝ × E).2)) ?_ fun q =>
      ⟨(Set.projIcc (-a) a (neg_le_self ha) q.2).2, (mem_prod.1 q.1.2).2⟩
    exact ((continuous_subtype_val.comp continuous_projIcc).comp continuous_snd).prodMk
      (continuous_snd.comp (continuous_subtype_val.comp continuous_fst))
  have h2 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume)
    (f := fun (q : ↥(Icc (-a) a ×ˢ closedBall x₀ r)) τ =>
      g (Set.projIcc (-a) a (neg_le_self ha) τ : ℝ) (q : ℝ × E).2) (a₀ := 0) hc
    (continuous_fst.comp continuous_subtype_val)
  refine h2.congr fun q => ?_
  have hq := (mem_prod.1 q.2).1
  refine intervalIntegral.integral_congr fun τ hτ => ?_
  have hτ' : τ ∈ Icc (-a) a :=
    uIcc_subset_Icc ⟨by linarith [hq.1, hq.2], by linarith [hq.1, hq.2]⟩ hq hτ
  simp only [Set.projIcc_of_mem _ hτ']

/-- The derivative iterates: `Y₀ = id`, `Y_{m+1} t x = id + ∫₀ᵗ DF (u m τ x) ∘ Y_m τ x`. -/
def voltIter (F' : E → E →L[ℝ] E) (u : ℕ → ℝ → E → E) : ℕ → ℝ → E → E →L[ℝ] E
  | 0 => fun _ _ => ContinuousLinearMap.id ℝ E
  | m + 1 => fun t x => ContinuousLinearMap.id ℝ E +
      ∫ τ in (0 : ℝ)..t, (F' (u m τ x)).comp (voltIter F' u m τ x)

/-- Numerical and regularity data for the Picard iterates `u` and the derivative `F'` of `F`. -/
structure IterData (F : E → E) (F' : E → E →L[ℝ] E) (u : ℕ → ℝ → E → E)
    (x₀ : E) (a r ρ Λ : ℝ) : Prop where
  nonneg_time : 0 ≤ a
  nonneg_bound : 0 ≤ Λ
  contracts : a * Λ < 1
  hasFDeriv : ∀ z ∈ closedBall x₀ ρ, HasFDerivAt F (F' z) z
  cont' : ContinuousOn F' (closedBall x₀ ρ)
  bound' : ∀ z ∈ closedBall x₀ ρ, ‖F' z‖ ≤ Λ
  start : ∀ t x, u 0 t x = x
  cont : ∀ m, ContinuousOn (fun p : ℝ × E => u m p.1 p.2) (Icc (-a) a ×ˢ closedBall x₀ r)
  mem : ∀ m, ∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r, u m t x ∈ closedBall x₀ ρ
  step : ∀ m, ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc (-a) a,
    u (m + 1) t x = x + ∫ τ in (0 : ℝ)..t, F (u m τ x)

/-- Continuity of the composite integrand `τ ↦ DF (U τ x) ∘ Z τ x` in `(τ, x)`. -/
theorem continuousOn_comp_integrand {U : ℝ → E → E} {Z : ℝ → E → E →L[ℝ] E}
    (hF' : ContinuousOn F' (closedBall x₀ ρ))
    (hU : ContinuousOn (fun p : ℝ × E => U p.1 p.2) (Icc (-a) a ×ˢ closedBall x₀ r))
    (hm : ∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r, U t x ∈ closedBall x₀ ρ)
    (hZ : ContinuousOn (fun p : ℝ × E => Z p.1 p.2) (Icc (-a) a ×ˢ closedBall x₀ r)) :
    ContinuousOn (fun p : ℝ × E => (F' (U p.1 p.2)).comp (Z p.1 p.2))
      (Icc (-a) a ×ˢ closedBall x₀ r) :=
  ((hF'.comp hU fun p hp => hm _ hp.1 _ hp.2).clm_comp hZ)

theorem voltIter_spec [CompleteSpace E] {u : ℕ → ℝ → E → E}
    (d : IterData F F' u x₀ a r ρ Λ) (m : ℕ) :
    ContinuousOn (fun p : ℝ × E => voltIter F' u m p.1 p.2) (Icc (-a) a ×ˢ closedBall x₀ r) ∧
    (∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r, ‖voltIter F' u m t x‖ ≤ 1 / (1 - a * Λ)) ∧
    ∀ t ∈ Icc (-a) a, ∀ x ∈ ball x₀ r, HasFDerivAt (u m t) (voltIter F' u m t x) x := by
  have ha := d.nonneg_time
  have hpos : 0 < 1 - a * Λ := by linarith [d.contracts]
  induction m with
  | zero =>
    refine ⟨continuousOn_const, fun t _ x _ => ?_, fun t _ x _ => ?_⟩
    · have h0 : (1 : ℝ) ≤ 1 / (1 - a * Λ) := by
        rw [le_div_iff₀ hpos]; nlinarith [mul_nonneg ha d.nonneg_bound]
      exact le_trans ContinuousLinearMap.norm_id_le h0
    · have : u 0 t = id := funext (d.start t)
      rw [this]; exact hasFDerivAt_id x
  | succ m ih =>
    obtain ⟨hc, hb, hd⟩ := ih
    have hint : ContinuousOn (fun p : ℝ × E => (F' (u m p.1 p.2)).comp (voltIter F' u m p.1 p.2))
        (Icc (-a) a ×ˢ closedBall x₀ r) :=
      continuousOn_comp_integrand d.cont' (d.cont m) (d.mem m) hc
    have hsub : ∀ t ∈ Icc (-a) a, [[0, t]] ⊆ Icc (-a) a := fun t ht =>
      uIcc_subset_Icc ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩ ht
    have hcont : ∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r, ContinuousOn
        (fun τ => (F' (u m τ x)).comp (voltIter F' u m τ x)) [[0, t]] := fun t ht x hx =>
      (hint.comp (continuousOn_id.prodMk continuousOn_const) fun τ hτ => ⟨hsub t ht hτ, hx⟩).mono
        le_rfl
    refine ⟨?_, ?_, ?_⟩
    · have h5 := (continuousOn_const (c := ContinuousLinearMap.id ℝ E)).add
        (continuousOn_intervalIntegral_param (g := fun τ x =>
          (F' (u m τ x)).comp (voltIter F' u m τ x)) ha hint)
      exact h5.congr fun p _ => rfl
    · intro t ht x hx
      show ‖ContinuousLinearMap.id ℝ E + ∫ τ in (0 : ℝ)..t, _‖ ≤ _
      have h1 : ‖∫ τ in (0 : ℝ)..t, (F' (u m τ x)).comp (voltIter F' u m τ x)‖ ≤
          Λ * (1 / (1 - a * Λ)) * |t - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun τ hτ => ?_
        have hτ' : τ ∈ Icc (-a) a := hsub t ht (uIoc_subset_uIcc hτ)
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (d.bound' _ (d.mem m τ hτ' x hx)) (hb τ hτ' x hx) (norm_nonneg _)
            d.nonneg_bound)
      have h2 : |t - 0| ≤ a := by
        rw [sub_zero, abs_le]; exact ⟨ht.1, ht.2⟩
      calc _ ≤ ‖ContinuousLinearMap.id ℝ E‖ + _ := norm_add_le _ _
        _ ≤ 1 + Λ * (1 / (1 - a * Λ)) * a := by
          have h0 : ‖ContinuousLinearMap.id ℝ E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
          have h4 : Λ * (1 / (1 - a * Λ)) * |t - 0| ≤ Λ * (1 / (1 - a * Λ)) * a :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg d.nonneg_bound (one_div_nonneg.2 hpos.le))
          linarith
        _ = 1 / (1 - a * Λ) := by
          have hne : 1 - a * Λ ≠ 0 := hpos.ne'
          rw [eq_div_iff hne]
          have : (1 + Λ * (1 / (1 - a * Λ)) * a) * (1 - a * Λ) =
              (1 - a * Λ) + a * Λ * ((1 / (1 - a * Λ)) * (1 - a * Λ)) := by ring
          rw [this, one_div, inv_mul_cancel₀ hne]; ring
    · intro t ht x hx
      have hB : ball x₀ r ∈ 𝓝 x := isOpen_ball.mem_nhds hx
      have hBc : ∀ z ∈ ball x₀ r, z ∈ closedBall x₀ r := fun z hz => ball_subset_closedBall hz
      have hFc : ContinuousOn F (closedBall x₀ ρ) := fun w hw =>
        (d.hasFDeriv w hw).continuousAt.continuousWithinAt
      have k1 : ∀ τ ∈ [[0, t]], ∀ z ∈ ball x₀ r, HasFDerivAt (u m τ) (voltIter F' u m τ z) z :=
        fun τ hτ z hz => hd τ (hsub t ht hτ) z hz
      have k2 : ∀ τ ∈ [[0, t]], ∀ z ∈ ball x₀ r, HasFDerivAt F (F' (u m τ z)) (u m τ z) :=
        fun τ hτ z hz => d.hasFDeriv _ (d.mem m τ (hsub t ht hτ) z (hBc z hz))
      have k3 : ∀ τ ∈ [[0, t]], ∀ z ∈ ball x₀ r, ‖F' (u m τ z)‖ ≤ Λ :=
        fun τ hτ z hz => d.bound' _ (d.mem m τ (hsub t ht hτ) z (hBc z hz))
      have k4 : ∀ τ ∈ [[0, t]], ∀ z ∈ ball x₀ r, ‖voltIter F' u m τ z‖ ≤ 1 / (1 - a * Λ) :=
        fun τ hτ z hz => hb τ (hsub t ht hτ) z (hBc z hz)
      have k5 : ∀ z ∈ ball x₀ r, ContinuousOn (fun τ => F (u m τ z)) [[0, t]] := by
        intro z hz
        have hu : ContinuousOn (fun τ => u m τ z) [[0, t]] :=
          ((d.cont m).comp (continuousOn_id.prodMk continuousOn_const)
            fun τ hτ => ⟨hsub t ht hτ, hBc z hz⟩)
        exact hFc.comp hu fun τ hτ => d.mem m τ (hsub t ht hτ) z (hBc z hz)
      have key := hasFDerivAt_intervalIntegral_comp (F := F) (F' := F') (U := u m)
        (U' := voltIter F' u m) (t := t) (B := ball x₀ r) (x := x) (Λ := Λ)
        (M := 1 / (1 - a * Λ)) hB k1 k2 k3 k4 k5 (hcont t ht x (hBc x hx))
      have h3 := (hasFDerivAt_id x).add key
      refine h3.congr_of_eventuallyEq ?_
      filter_upwards [hB] with z hz
      exact d.step m z (hBc z hz) t ht

end Iterates

end KAM.Nekhoroshev
