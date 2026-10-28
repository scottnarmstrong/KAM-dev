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

theorem uIcc_zero_subset_Icc (ha : 0 ≤ a) {t : ℝ} (ht : t ∈ Icc (-a) a) :
    [[0, t]] ⊆ Icc (-a) a :=
  uIcc_subset_Icc ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩ ht

theorem continuousOn_uIcc_of_joint {V : Type*} [TopologicalSpace V] {g : ℝ → E → V}
    (ha : 0 ≤ a)
    (hg : ContinuousOn (fun p : ℝ × E => g p.1 p.2) (Icc (-a) a ×ˢ closedBall x₀ r))
    {t : ℝ} (ht : t ∈ Icc (-a) a) {x : E} (hx : x ∈ closedBall x₀ r) :
    ContinuousOn (fun τ => g τ x) [[0, t]] :=
  hg.comp (continuousOn_id.prodMk continuousOn_const) fun _ hτ =>
    ⟨uIcc_zero_subset_Icc ha ht hτ, hx⟩

/-- One step of the recurrence `‖Y_{m+1} - Y‖ ≤ q ‖Y_m - Y‖ + a d_m / (1 - q)`. -/
theorem voltIter_step [CompleteSpace E] {u : ℕ → ℝ → E → E} (d : IterData F F' u x₀ a r ρ Λ)
    {y : ℝ → E → E} {Y : ℝ → E → E →L[ℝ] E}
    (hyc : ContinuousOn (fun p : ℝ × E => y p.1 p.2) (Icc (-a) a ×ˢ closedBall x₀ r))
    (hym : ∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r, y t x ∈ closedBall x₀ ρ)
    (hYc : ContinuousOn (fun p : ℝ × E => Y p.1 p.2) (Icc (-a) a ×ˢ closedBall x₀ r))
    (hYb : ∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r, ‖Y t x‖ ≤ 1 / (1 - a * Λ))
    (hYeq : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc (-a) a,
      Y t x = ContinuousLinearMap.id ℝ E + ∫ τ in (0 : ℝ)..t, (F' (y τ x)).comp (Y τ x))
    {m : ℕ} {ε dd : ℝ}
    (hε : ∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r, ‖voltIter F' u m t x - Y t x‖ ≤ ε)
    (hdd : ∀ τ ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r, ‖F' (u m τ x) - F' (y τ x)‖ ≤ dd) :
    ∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r,
      ‖voltIter F' u (m + 1) t x - Y t x‖ ≤ a * Λ * ε + a * dd / (1 - a * Λ) := by
  have ha := d.nonneg_time
  intro t ht x hx
  have hf : ContinuousOn (fun τ => (F' (u m τ x)).comp (voltIter F' u m τ x)) [[0, t]] :=
    continuousOn_uIcc_of_joint (g := fun τ x => (F' (u m τ x)).comp (voltIter F' u m τ x)) ha
      (continuousOn_comp_integrand d.cont' (d.cont m) (d.mem m) (voltIter_spec d m).1) ht hx
  have hg : ContinuousOn (fun τ => (F' (y τ x)).comp (Y τ x)) [[0, t]] :=
    continuousOn_uIcc_of_joint (g := fun τ x => (F' (y τ x)).comp (Y τ x)) ha
      (continuousOn_comp_integrand d.cont' hyc hym hYc) ht hx
  have e : voltIter F' u (m + 1) t x - Y t x = ∫ τ in (0 : ℝ)..t,
      ((F' (u m τ x)).comp (voltIter F' u m τ x) - (F' (y τ x)).comp (Y τ x)) := by
    rw [intervalIntegral.integral_sub hf.intervalIntegrable hg.intervalIntegrable, hYeq x hx t ht]
    show ContinuousLinearMap.id ℝ E + _ - _ = _
    abel
  have hpt : ∀ τ ∈ Icc (-a) a, ‖(F' (u m τ x)).comp (voltIter F' u m τ x) -
      (F' (y τ x)).comp (Y τ x)‖ ≤ Λ * ε + dd * (1 / (1 - a * Λ)) := by
    intro τ hτ
    have : (F' (u m τ x)).comp (voltIter F' u m τ x) - (F' (y τ x)).comp (Y τ x) =
        (F' (u m τ x)).comp (voltIter F' u m τ x - Y τ x) +
          (F' (u m τ x) - F' (y τ x)).comp (Y τ x) := by
      rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]; abel
    rw [this]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (d.bound' _ (d.mem m τ hτ x hx)) (hε τ hτ x hx) (norm_nonneg _)
          d.nonneg_bound)
    · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hdd τ hτ x hx) (hYb τ hτ x hx) (norm_nonneg _)
          ((norm_nonneg _).trans (hdd τ hτ x hx)))
  have h0a : (0 : ℝ) ∈ Icc (-a) a := ⟨by linarith, ha⟩
  have hC : 0 ≤ Λ * ε + dd * (1 / (1 - a * Λ)) := (norm_nonneg _).trans (hpt 0 h0a)
  rw [e]
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun τ => (F' (u m τ x)).comp (voltIter F' u m τ x) - (F' (y τ x)).comp (Y τ x))
    (C := Λ * ε + dd * (1 / (1 - a * Λ)))
    fun τ hτ => hpt τ (uIcc_zero_subset_Icc ha ht (uIoc_subset_uIcc hτ))
  have h2 : |t - 0| ≤ a := by rw [sub_zero, abs_le]; exact ⟨ht.1, ht.2⟩
  calc _ ≤ _ := h1
    _ ≤ (Λ * ε + dd * (1 / (1 - a * Λ))) * a := mul_le_mul_of_nonneg_left h2 hC
    _ = a * Λ * ε + a * dd / (1 - a * Λ) := by ring

/-- `bpN:p12:ext-dep#derivative-limit` (convergence part): the derivative iterates converge
uniformly to the Volterra family, using only the recurrence and uniform continuity of `DF`
on the compact trap (not contraction of the pair `(y, Y)`). -/
theorem voltIter_uniform [CompleteSpace E] [ProperSpace E] {u : ℕ → ℝ → E → E}
    (d : IterData F F' u x₀ a r ρ Λ) {y : ℝ → E → E} {Y : ℝ → E → E →L[ℝ] E} (L : ℝ)
    (hconv : ∀ m, ∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r,
      ‖u m t x - y t x‖ ≤ a * L * (a * Λ) ^ m / (1 - a * Λ))
    (hyc : ContinuousOn (fun p : ℝ × E => y p.1 p.2) (Icc (-a) a ×ˢ closedBall x₀ r))
    (hym : ∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r, y t x ∈ closedBall x₀ ρ)
    (hYc : ContinuousOn (fun p : ℝ × E => Y p.1 p.2) (Icc (-a) a ×ˢ closedBall x₀ r))
    (hYb : ∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r, ‖Y t x‖ ≤ 1 / (1 - a * Λ))
    (hYeq : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc (-a) a,
      Y t x = ContinuousLinearMap.id ℝ E + ∫ τ in (0 : ℝ)..t, (F' (y τ x)).comp (Y τ x))
    {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r,
      ‖voltIter F' u m t x - Y t x‖ ≤ η := by
  have ha := d.nonneg_time
  have hq0 : 0 ≤ a * Λ := mul_nonneg ha d.nonneg_bound
  have hq1 := d.contracts
  have hpos : 0 < 1 - a * Λ := by linarith
  have hη2 : 0 < η / 2 := by linarith
  set B : ℝ := 2 / (1 - a * Λ) with hB
  set dstar : ℝ := (η / 2) * (1 - a * Λ) ^ 2 / (a + 1) with hdstar
  have hdpos : 0 < dstar := by positivity
  obtain ⟨θ, hθ, hθ'⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall x₀ ρ).uniformContinuousOn_of_continuous d.cont') dstar hdpos
  have ht0 : Tendsto (fun m : ℕ => a * L * (a * Λ) ^ m / (1 - a * Λ)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (a * L)).div_const
      (1 - a * Λ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht0.eventually (gt_mem_nhds hθ))
  have hdm : ∀ m ≥ N, ∀ τ ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r,
      ‖F' (u m τ x) - F' (y τ x)‖ ≤ dstar := by
    intro m hm τ hτ x hx
    have := hθ' (u m τ x) (d.mem m τ hτ x hx) (y τ x) (hym τ hτ x hx)
      (by rw [dist_eq_norm]; exact (hconv m τ hτ x hx).trans_lt (hN m hm))
    rw [← dist_eq_norm]; exact this.le
  have hiter : ∀ k : ℕ, ∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r,
      ‖voltIter F' u (N + k) t x - Y t x‖ ≤ (a * Λ) ^ k * B + η / 2 := by
    intro k
    induction k with
    | zero =>
      intro t ht x hx
      have h1 := (voltIter_spec d N).2.1 t ht x hx
      have h2 := hYb t ht x hx
      have : ‖voltIter F' u (N + 0) t x - Y t x‖ ≤ B := by
        calc _ ≤ ‖voltIter F' u N t x‖ + ‖Y t x‖ := norm_sub_le _ _
          _ ≤ 1 / (1 - a * Λ) + 1 / (1 - a * Λ) := add_le_add h1 h2
          _ = B := by rw [hB]; ring
      simpa using this.trans (le_add_of_nonneg_right hη2.le)
    | succ k ih =>
      have := voltIter_step d hyc hym hYc hYb hYeq (m := N + k) ih
        (fun τ hτ x hx => hdm (N + k) (Nat.le_add_right _ _) τ hτ x hx)
      intro t ht x hx
      refine (this t ht x hx).trans ?_
      have h3 : a * dstar / (1 - a * Λ) ≤ (η / 2) * (1 - a * Λ) := by
        rw [hdstar, div_le_iff₀ hpos]
        have : a * ((η / 2) * (1 - a * Λ) ^ 2 / (a + 1)) =
            (η / 2) * (1 - a * Λ) * (1 - a * Λ) * (a / (a + 1)) := by ring
        rw [this]
        have h4 : a / (a + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        have h5 : 0 ≤ (η / 2) * (1 - a * Λ) * (1 - a * Λ) := by positivity
        nlinarith
      calc a * Λ * ((a * Λ) ^ k * B + η / 2) + a * dstar / (1 - a * Λ)
          ≤ a * Λ * ((a * Λ) ^ k * B + η / 2) + (η / 2) * (1 - a * Λ) := by linarith
        _ = (a * Λ) ^ (k + 1) * B + η / 2 := by ring
  have ht1 : Tendsto (fun k : ℕ => (a * Λ) ^ k * B) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const B
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 (ht1.eventually (gt_mem_nhds hη2))
  refine ⟨N + k0, fun m hm t ht x hx => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right N k0) hm)
  have hk : k0 ≤ k := by omega
  exact (hiter k t ht x hx).trans (by have := hk0 k hk; linarith)

/-- `bpN:p12:ext-dep#identify`: the uniform limit `Y` of the derivative iterates is the
`x`-derivative of the Picard limit `y` on the open ball. -/
theorem hasFDerivAt_limit [CompleteSpace E] [ProperSpace E] {u : ℕ → ℝ → E → E}
    (d : IterData F F' u x₀ a r ρ Λ) {y : ℝ → E → E} {Y : ℝ → E → E →L[ℝ] E} (L : ℝ)
    (hconv : ∀ m, ∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r,
      ‖u m t x - y t x‖ ≤ a * L * (a * Λ) ^ m / (1 - a * Λ))
    (hyc : ContinuousOn (fun p : ℝ × E => y p.1 p.2) (Icc (-a) a ×ˢ closedBall x₀ r))
    (hym : ∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r, y t x ∈ closedBall x₀ ρ)
    (hYc : ContinuousOn (fun p : ℝ × E => Y p.1 p.2) (Icc (-a) a ×ˢ closedBall x₀ r))
    (hYb : ∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r, ‖Y t x‖ ≤ 1 / (1 - a * Λ))
    (hYeq : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc (-a) a,
      Y t x = ContinuousLinearMap.id ℝ E + ∫ τ in (0 : ℝ)..t, (F' (y τ x)).comp (Y τ x))
    {t : ℝ} (ht : t ∈ Icc (-a) a) {x : E} (hx : x ∈ ball x₀ r) :
    HasFDerivAt (y t) (Y t x) x := by
  have ha := d.nonneg_time
  have hpos : 0 < 1 - a * Λ := by linarith [d.contracts]
  refine hasFDerivAt_of_tendstoUniformlyOn (𝕜 := ℝ) (l := atTop) (f := fun m => u m t)
    (f' := fun m z => voltIter F' u m t z) (g := y t) (g' := fun z => Y t z)
    isOpen_ball ?_ (fun m z hz => (voltIter_spec d m).2.2 t ht z hz) ?_ hx
  · rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    obtain ⟨N, hN⟩ := voltIter_uniform d L hconv hyc hym hYc hYb hYeq (half_pos hη)
    filter_upwards [eventually_ge_atTop N] with m hm z hz
    rw [dist_eq_norm]
    exact (hN m hm t ht z (ball_subset_closedBall hz)).trans_lt (half_lt_self hη) |>.trans_eq' (by
      rw [norm_sub_rev])
  · intro z hz
    have hz' := ball_subset_closedBall hz
    have ht0 : Tendsto (fun m : ℕ => a * L * (a * Λ) ^ m / (1 - a * Λ)) atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg ha d.nonneg_bound)
        d.contracts).const_mul (a * L)).div_const (1 - a * Λ)
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
      (fun m => ?_) ht0)
    exact hconv m t ht z hz'

end Iterates

section ExtDep

open MeasureTheory

/-- `bpN:p12:ext-dep`: local `C¹` dependence on initial data for a `C¹` vector field on an open
set of a finite-dimensional real space. -/
theorem ext_dep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [ProperSpace E] {W : Set E} (hW : IsOpen W)
    {F : E → E} (hF : ContDiffOn ℝ 1 F W)
    {x₀ : E} (hx : x₀ ∈ W) :
    ∃ a r : ℝ, 0 < a ∧ 0 < r ∧ ball x₀ r ⊆ W ∧
      ∃ y : ℝ → E → E,
        ContinuousOn (fun p : ℝ × E => y p.1 p.2)
          (Ioo (-a) a ×ˢ ball x₀ r) ∧
        ContinuousOn (fun p : ℝ × E => fderiv ℝ (y p.1) p.2)
          (Ioo (-a) a ×ˢ ball x₀ r) ∧
        ∀ x ∈ ball x₀ r, y 0 x = x ∧
          KAM.ODE.IsSolutionIn F W (Ioo (-a) a) (fun t => y t x) ∧
          ∀ t ∈ Ioo (-a) a, HasFDerivAt (y t) (fderiv ℝ (y t) x) x ∧
            fderiv ℝ (y t) x = ContinuousLinearMap.id ℝ E +
              ∫ u in (0 : ℝ)..t, (fderiv ℝ F (y u x)).comp (fderiv ℝ (y u) x) := by
  obtain ⟨ε0, hε0, hball⟩ := Metric.isOpen_iff.1 hW x₀ hx
  set δ : ℝ := ε0 / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hKW : closedBall x₀ δ ⊆ W :=
    (closedBall_subset_ball (by linarith)).trans hball
  have hFd : ∀ z ∈ W, HasFDerivAt F (fderiv ℝ F z) z := fun z hz =>
    ((hF.contDiffAt (hW.mem_nhds hz)).differentiableAt one_ne_zero).hasFDerivAt
  have hF'c : ContinuousOn (fderiv ℝ F) W := hF.continuousOn_fderiv_of_isOpen hW le_rfl
  obtain ⟨L, hL⟩ := (isCompact_closedBall x₀ δ).exists_bound_of_continuousOn
    (hF.continuousOn.mono hKW)
  obtain ⟨Λ, hΛ⟩ := (isCompact_closedBall x₀ δ).exists_bound_of_continuousOn
    (hF'c.mono hKW)
  set L0 : ℝ := max L 0 with hL0
  set Λn : ℝ≥0 := Real.toNNReal Λ with hΛn
  have hL0n : 0 ≤ L0 := le_max_right _ _
  have hΛn0 : (0 : ℝ) ≤ (Λn : ℝ) := Λn.2
  have hLb : ∀ z ∈ closedBall x₀ δ, ‖F z‖ ≤ L0 := fun z hz => (hL z hz).trans (le_max_left _ _)
  have hΛb : ∀ z ∈ closedBall x₀ δ, ‖fderiv ℝ F z‖ ≤ (Λn : ℝ) := fun z hz =>
    (hΛ z hz).trans (Real.le_coe_toNNReal Λ)
  set a : ℝ := min (δ / (2 * (L0 + 1))) (1 / (2 * ((Λn : ℝ) + 1))) with ha_def
  have hapos : 0 < a := lt_min (by positivity) (by positivity)
  have haL : a * L0 ≤ δ / 2 := by
    have h1 : a ≤ δ / (2 * (L0 + 1)) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have haΛ : a * (Λn : ℝ) ≤ 1 / 2 := by
    have h1 : a ≤ 1 / (2 * ((Λn : ℝ) + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hPB : PicardBounds F x₀ a (δ / 2) δ L0 Λn :=
    { nonneg_time := hapos.le
      nonneg_bound := hL0n
      radius := by linarith
      bound := hLb
      lipschitz := (convex_closedBall x₀ δ).lipschitzOnWith_of_nnnorm_fderiv_le
        (fun z hz => (hFd z (hKW hz)).differentiableAt) fun z hz => by
          have := hΛb z hz
          rw [← NNReal.coe_le_coe, coe_nnnorm]; exact this
      contracts := by linarith }
  obtain ⟨u, y, hu0, hucont, humem, hustep, hycont, hymem, hyeq, hconv, hyder⟩ :=
    picard_family hPB
  have hd : IterData F (fderiv ℝ F) u x₀ a (δ / 2) δ (Λn : ℝ) :=
    { nonneg_time := hapos.le
      nonneg_bound := hΛn0
      contracts := by linarith
      hasFDeriv := fun z hz => hFd z (hKW hz)
      cont' := hF'c.mono hKW
      bound' := hΛb
      start := hu0
      cont := hucont
      mem := humem
      step := hustep }
  obtain ⟨Y, hYc, hYb, hYeq⟩ := linear_family (E := E) (x₀ := x₀) (r := δ / 2) (a := a)
    (Λ := (Λn : ℝ)) (G := fun t x => fderiv ℝ F (y t x)) hapos.le hΛn0 (by linarith)
    ((hF'c.mono hKW).comp hycont fun p hp => hymem _ hp.1 _ hp.2)
    (fun t ht x hx => hΛb _ (hymem t ht x hx))
  have hder : ∀ t ∈ Icc (-a) a, ∀ x ∈ ball x₀ (δ / 2), HasFDerivAt (y t) (Y t x) x :=
    fun t ht x hx => hasFDerivAt_limit hd L0 hconv hycont hymem hYc hYb hYeq ht hx
  have hmono : Ioo (-a) a ×ˢ ball x₀ (δ / 2) ⊆ Icc (-a) a ×ˢ closedBall x₀ (δ / 2) :=
    prod_mono Ioo_subset_Icc_self ball_subset_closedBall
  refine ⟨a, δ / 2, hapos, by positivity, (ball_subset_closedBall.trans
    ((closedBall_subset_closedBall (by linarith)).trans hKW)), y, hycont.mono hmono, ?_, ?_⟩
  · refine (hYc.mono hmono).congr fun p hp => ?_
    exact (hder p.1 (Ioo_subset_Icc_self hp.1) p.2 hp.2).fderiv
  · intro x hx
    have hxc : x ∈ closedBall x₀ (δ / 2) := ball_subset_closedBall hx
    have h0 : (0 : ℝ) ∈ Icc (-a) a := ⟨by linarith, hapos.le⟩
    refine ⟨?_, ?_, ?_⟩
    · have := hyeq x hxc 0 h0
      simpa using this
    · intro t ht
      exact ⟨hKW (hymem t (Ioo_subset_Icc_self ht) x hxc),
        hyder x hxc t ht⟩
    · intro t ht
      have ht' := Ioo_subset_Icc_self ht
      have hfd := hder t ht' x hx
      refine ⟨by rw [hfd.fderiv]; exact hfd, ?_⟩
      rw [hfd.fderiv, hYeq x hxc t ht']
      congr 1
      refine intervalIntegral.integral_congr fun u' hu' => ?_
      have hu'' := uIcc_zero_subset_Icc hapos.le ht' hu'
      rw [(hder u' hu'' x hx).fderiv]

end ExtDep

end KAM.Nekhoroshev
