/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Order.IntermediateValue

/-!
# W8: external facts (blueprint `bpW:w8:ext`)

Blueprint labels `bpW:w8:ext`, `bpW:w8:ext-inner`, `bpW:w8:ext-mono`,
`bpW:w8:ext-compact`, `bpW:w8:ext-exp`, `bpW:w8:ext-sqrt`, `bpW:w8:ext-dist`, `bpW:w8:ext-rpow`,
`bpW:w8:ext-local` (milestone W8).

Each item of the list `(W8-E1)`–`(W8-E8)` is recorded here in the form in which W8 uses it, proved
from the Mathlib declarations the blueprint names.
-/

public section

open Filter Set Topology

namespace KAM.Wave

/-! ### (W8-E1) Inner products along curves (`bpW:w8:ext-inner`) -/

/-- (blueprint `bpW:w8:ext-inner`) Derivative of `s ↦ ⟨c₁ s, c₂ s⟩` for curves in `ℓ²_ℝ`. -/
theorem w8ext_hasDerivAt_inner {c₁ c₂ : ℝ → lp (fun _ : ℕ+ => ℝ) 2}
    {c₁' c₂' : lp (fun _ : ℕ+ => ℝ) 2} {t : ℝ} (h₁ : HasDerivAt c₁ c₁' t)
    (h₂ : HasDerivAt c₂ c₂' t) :
    HasDerivAt (fun s => inner ℝ (c₁ s) (c₂ s)) (inner ℝ c₁' (c₂ t) + inner ℝ (c₁ t) c₂') t := by
  have := h₁.inner ℝ h₂
  rwa [add_comm] at this

/-- (blueprint `bpW:w8:ext-inner`) `⟨f, g⟩ = Σ_j f_j g_j` in `ℓ²_ℝ`, the terms being summable. -/
theorem w8ext_inner_eq_tsum (f g : lp (fun _ : ℕ+ => ℝ) 2) :
    (Summable fun j => f j * g j) ∧ inner ℝ f g = ∑' j, f j * g j := by
  have hs := lp.summable_inner (𝕜 := ℝ) f g
  have e : ∀ j, inner ℝ (f j) (g j) = f j * g j := fun j => by
    simp [RCLike.inner_apply, mul_comm]
  simp only [e] at hs
  refine ⟨hs, ?_⟩
  rw [lp.inner_eq_tsum]
  exact tsum_congr e

/-- (blueprint `bpW:w8:ext-inner`) Cauchy–Schwarz in `ℓ²_ℝ`. -/
theorem w8ext_abs_inner_le (f g : lp (fun _ : ℕ+ => ℝ) 2) :
    |inner ℝ f g| ≤ ‖f‖ * ‖g‖ :=
  abs_real_inner_le_norm f g

/-! ### (W8-E2) Sign of the derivative (`bpW:w8:ext-mono`) -/

/-! ### (W8-E3) Compactness (`bpW:w8:ext-compact`) -/

/-- (blueprint `bpW:w8:ext-compact`) A continuous map is bounded on `[-T, T]`. -/
theorem w8ext_bounded_Icc {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {T : ℝ}
    (hf : ContinuousOn f (Icc (-T) T)) : ∃ R, ∀ t ∈ Icc (-T) T, ‖f t‖ ≤ R :=
  isCompact_Icc.exists_bound_of_continuousOn hf

/-- (blueprint `bpW:w8:ext-compact`) Analytic maps are continuous. -/
theorem w8ext_continuous_of_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ∀ t, AnalyticAt ℝ f t) : Continuous f :=
  continuous_iff_continuousAt.2 fun t => (hf t).continuousAt

/-! ### (W8-E4) Complex exponential and integers (`bpW:w8:ext-exp`) -/

/-- (blueprint `bpW:w8:ext-exp`) `e^z = 1` iff `z ∈ 2πiℤ`. -/
theorem w8ext_exp_eq_one_iff (z : ℂ) :
    Complex.exp z = 1 ↔ ∃ n : ℤ, z = n * (2 * Real.pi * Complex.I) :=
  Complex.exp_eq_one_iff

/-- (blueprint `bpW:w8:ext-exp`) `|e^{ix}| = 1` and `|e^{ix} - 1| ≤ |x|` for real `x`. -/
theorem w8ext_norm_exp_I (x : ℝ) :
    ‖Complex.exp (x * Complex.I)‖ = 1 ∧ ‖Complex.exp (Complex.I * x) - 1‖ ≤ |x| :=
  ⟨Complex.norm_exp_ofReal_mul_I x, by
    simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := x)⟩

/-- (blueprint `bpW:w8:ext-exp`) A continuous integer-valued real function on a preconnected
space is constant. -/
theorem w8ext_const_of_intValued {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) (hZ : ∀ x, ∃ k : ℤ, f x = k) (x y : X) : f x = f y := by
  by_contra hne
  -- WLOG `f x < f y`
  have key : ∀ a b : X, f a < f b → False := by
    intro a b hab
    obtain ⟨k, hk⟩ := hZ a
    obtain ⟨l, hl⟩ := hZ b
    have hkl : k < l := by exact_mod_cast (hk ▸ hl ▸ hab)
    have hmem : (k : ℝ) + 1 / 2 ∈ Icc (f a) (f b) := by
      rw [hk, hl]
      have : (k : ℝ) + 1 ≤ l := by exact_mod_cast hkl
      constructor <;> linarith
    obtain ⟨c, hc⟩ := intermediate_value_univ a b hf hmem
    obtain ⟨m, hm⟩ := hZ c
    rw [hm] at hc
    have h1 : (k : ℝ) < m := by linarith
    have h2 : (m : ℝ) < k + 1 := by linarith
    have h1' : k < m := by exact_mod_cast h1
    have h2' : m < k + 1 := by exact_mod_cast h2
    omega
  rcases lt_or_gt_of_ne hne with h | h
  · exact key x y h
  · exact key y x h

/-- (blueprint `bpW:w8:ext-exp`) If `t ↦ t c` is bounded on `ℝ`, then `c = 0`. -/
theorem w8ext_eq_zero_of_bounded_mul {c B : ℝ} (h : ∀ t : ℝ, |t * c| ≤ B) : c = 0 := by
  by_contra hc
  have hcpos : 0 < |c| := abs_pos.2 hc
  have := h ((|B| + 1) / |c|)
  rw [abs_mul, abs_of_pos (by positivity : 0 < (|B| + 1) / |c|), div_mul_cancel₀ _ hcpos.ne']
    at this
  linarith [le_abs_self B]

/-! ### (W8-E5) Square roots (`bpW:w8:ext-sqrt`) -/

/-- (blueprint `bpW:w8:ext-sqrt`) For `a > 0` and `a + b ≥ 0`: `|√(a+b) - √a| ≤ |b| / √a`. -/
theorem w8ext_abs_sqrt_sub_le {a b : ℝ} (ha : 0 < a) (hab : 0 ≤ a + b) :
    |Real.sqrt (a + b) - Real.sqrt a| ≤ |b| / Real.sqrt a := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0 ≤ Real.sqrt (a + b) := Real.sqrt_nonneg _
  have hprod : (Real.sqrt (a + b) - Real.sqrt a) * (Real.sqrt (a + b) + Real.sqrt a) = b := by
    have h1 := Real.sq_sqrt hab
    have h2 := Real.sq_sqrt ha.le
    nlinarith
  rw [le_div_iff₀ hsa]
  calc |Real.sqrt (a + b) - Real.sqrt a| * Real.sqrt a
      ≤ |Real.sqrt (a + b) - Real.sqrt a| * (Real.sqrt (a + b) + Real.sqrt a) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = |b| := by
        conv_rhs => rw [← hprod]
        rw [abs_mul, abs_of_pos (by linarith : 0 < Real.sqrt (a + b) + Real.sqrt a)]

/-! ### (W8-E6) Distance to a set (`bpW:w8:ext-dist`) -/

/-- (blueprint `bpW:w8:ext-dist`) `{x : dist(x, S) > a}` is open; `dist(·, S)` vanishes on `S` and
is at most `dist x y` for `y ∈ S`. -/
theorem w8ext_infDist {X : Type*} [PseudoMetricSpace X] (S : Set X) (a : ℝ) :
    IsOpen {x | a < Metric.infDist x S} ∧ (∀ x ∈ S, Metric.infDist x S = 0) ∧
      ∀ x, ∀ y ∈ S, Metric.infDist x S ≤ dist x y :=
  ⟨isOpen_lt continuous_const (Metric.continuous_infDist_pt S),
    fun _ hx => Metric.infDist_zero_of_mem hx, fun _ _ hy => Metric.infDist_le_dist_of_mem hy⟩

/-! ### (W8-E7) Real powers (`bpW:w8:ext-rpow`) -/

/-- (blueprint `bpW:w8:ext-rpow`) `C r^a → 0` as `r → 0⁺`, for `a > 0`. -/
theorem w8ext_tendsto_const_mul_rpow {a : ℝ} (ha : 0 < a) (C : ℝ) :
    Tendsto (fun r : ℝ => C * r ^ a) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun r : ℝ => r ^ a) (𝓝 0) (𝓝 0) := by
    have := Real.continuousAt_rpow_const 0 a (Or.inr ha.le)
    rwa [ContinuousAt, Real.zero_rpow ha.ne'] at this
  simpa using (h.mono_left nhdsWithin_le_nhds).const_mul C

/-! ### (W8-E8) Local definitions (`bpW:w8:ext-local`) -/

/-- (blueprint `bpW:w8:ext-local`) Continuity on `S` is local, and passes to a map agreeing on
each local piece. -/
theorem w8ext_continuousOn_of_local {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {S : Set X}
    (h : ∀ x ∈ S, ∃ O, IsOpen O ∧ x ∈ O ∧ ∃ g : X → Y, ContinuousOn g (S ∩ O) ∧
      EqOn f g (S ∩ O)) :
    ContinuousOn f S := by
  refine continuousOn_of_locally_continuousOn fun x hx => ?_
  obtain ⟨O, hO, hxO, g, hg, hfg⟩ := h x hx
  exact ⟨O, hO, hxO, hg.congr hfg⟩

end KAM.Wave

end
