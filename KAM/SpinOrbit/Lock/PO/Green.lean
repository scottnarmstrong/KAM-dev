/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The Dirichlet Green operator on odd one-periodic functions (LOCK-PO)

Unfrozen helper code (design SO-LOCK §2.1).

* `taylor_two_abs_le`: the second-order Taylor bound `|u y - u x - u' x (y - x)| ≤ M (y - x)² / 2`
  from `|u''| ≤ M`.
* `dirichlet_bound`: if `u'' = f`, `|f| ≤ M` and `u` vanishes at every half-integer, then
  `|u| ≤ M / 32` and `|u'| ≤ M / 4` (the Dirichlet problem on intervals of length `1/2`).
* `half_int_zero`: an odd one-periodic function vanishes at every half-integer.
* `prim f x = ∫₀ˣ f`, `greenD f = prim f - 2 ∫₀^{1/2} prim f`, `green f = prim (greenD f)`:
  for continuous odd one-periodic `f`, `green f` is odd, one-periodic, `(green f)' = greenD f`,
  `(greenD f)' = f` (`green_odd`, `green_periodic`, `hasDerivAt_green`, `hasDerivAt_greenD`).
-/

@[expose] public noncomputable section

open Set intervalIntegral

namespace KAM.SpinOrbit.Lock

/-! ### Second-order Taylor bound and the Dirichlet estimate -/

private theorem abs_deriv_sub_le {u' f : ℝ → ℝ} {M : ℝ} (hu' : ∀ x, HasDerivAt u' (f x) x)
    (hf : ∀ x, |f x| ≤ M) (x s : ℝ) : |u' s - u' x| ≤ M * |s - x| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := u') (f' := f) (s := univ)
    (fun y _ => (hu' y).hasDerivWithinAt) (fun y _ => by simpa using hf y) convex_univ
    (mem_univ x) (mem_univ s)
  simpa using this

/-- Second-order Taylor bound from a bound on the second derivative. -/
theorem taylor_two_abs_le {u u' f : ℝ → ℝ} {M : ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : ∀ x, HasDerivAt u' (f x) x) (hf : ∀ x, |f x| ≤ M) (x y : ℝ) :
    |u y - u x - u' x * (y - x)| ≤ M * (y - x) ^ 2 / 2 := by
  have hL := abs_deriv_sub_le hu' hf x
  -- `h₊ = M (s - x)² / 2 - R(s)` and `h₋ = M (s - x)² / 2 + R(s)` with `R` the remainder.
  have hd : ∀ (σ : ℝ) s, HasDerivAt
      (fun s => M * (s - x) ^ 2 / 2 + σ * (u s - u x - u' x * (s - x)))
      (M * (s - x) + σ * (u' s - u' x)) s := fun σ s => by
    have hlin : HasDerivAt (fun s => s - x) 1 s := (hasDerivAt_id' s).sub_const x
    have h1 : HasDerivAt (fun s => M * (s - x) ^ 2 / 2) (M * (s - x)) s := by
      have := ((hlin.pow 2).const_mul M).div_const 2
      convert this using 1; push_cast; ring
    have h2 : HasDerivAt (fun s => u s - u x - u' x * (s - x)) (u' s - u' x) s := by
      have := ((hu s).sub_const (u x)).sub (hlin.const_mul (u' x))
      convert this using 1; ring
    exact h1.add (h2.const_mul σ)
  have key : ∀ σ : ℝ, |σ| ≤ 1 → 0 ≤ M * (y - x) ^ 2 / 2 + σ * (u y - u x - u' x * (y - x)) := by
    intro σ hσ
    set h := fun s => M * (s - x) ^ 2 / 2 + σ * (u s - u x - u' x * (s - x)) with hh
    have hx : h x = 0 := by simp [hh]
    have hσd : ∀ s, |σ * (u' s - u' x)| ≤ M * |s - x| := fun s => by
      rw [abs_mul]
      have := hL s
      have h0 : 0 ≤ |u' s - u' x| := abs_nonneg _
      nlinarith [abs_nonneg σ]
    rcases le_total x y with hxy | hxy
    · have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici x)
        (f := h) (fun s _ => (hd σ s).continuousAt.continuousWithinAt)
        (fun s _ => (hd σ s).hasDerivWithinAt) (fun s hs => by
          rw [interior_Ici] at hs
          have := hσd s
          rw [abs_of_pos (sub_pos.2 hs)] at this
          linarith [neg_abs_le (σ * (u' s - u' x))])
      have := hmono self_mem_Ici hxy hxy
      simpa [hx] using this
    · have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic x)
        (f := h) (fun s _ => (hd σ s).continuousAt.continuousWithinAt)
        (fun s _ => (hd σ s).hasDerivWithinAt) (fun s hs => by
          rw [interior_Iic] at hs
          have := hσd s
          rw [abs_of_neg (sub_neg.2 hs)] at this
          linarith [le_abs_self (σ * (u' s - u' x))])
      have := hanti hxy self_mem_Iic hxy
      simpa [hx] using this
  rw [abs_le]
  constructor
  · linarith [key 1 (by norm_num)]
  · linarith [key (-1) (by norm_num)]

/-- The Dirichlet estimate on the intervals `[k/2, k/2 + 1/2]`: `|u| ≤ M/32`, `|u'| ≤ M/4`. -/
theorem dirichlet_bound {u u' f : ℝ → ℝ} {M : ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : ∀ x, HasDerivAt u' (f x) x) (hf : ∀ x, |f x| ≤ M)
    (hzero : ∀ n : ℤ, u (n / 2) = 0) (x : ℝ) : |u x| ≤ M / 32 ∧ |u' x| ≤ M / 4 := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hf 0)
  set k : ℤ := ⌊2 * x⌋
  have hk1 : (k : ℝ) ≤ 2 * x := Int.floor_le _
  have hk2 : 2 * x < k + 1 := Int.lt_floor_add_one _
  set t := x - k / 2 with ht
  set s := (((k + 1 : ℤ) : ℝ) / 2) - x with hs
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have hs0 : 0 ≤ s := by rw [hs]; push_cast; linarith
  have hts : t + s = 1 / 2 := by rw [ht, hs]; push_cast; ring
  have hA := taylor_two_abs_le hu hu' hf x (k / 2)
  have hB := taylor_two_abs_le hu hu' hf x (((k + 1 : ℤ) : ℝ) / 2)
  rw [hzero k] at hA
  rw [hzero (k + 1)] at hB
  have ha : (k : ℝ) / 2 - x = -t := by rw [ht]; ring
  have hb : ((k + 1 : ℤ) : ℝ) / 2 - x = s := by rw [hs]
  rw [ha] at hA
  rw [hb] at hB
  rw [abs_le] at hA hB
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  have hst : s * t ≤ 1 / 16 := by nlinarith [sq_nonneg (s - t)]
  have hsq : t ^ 2 + s ^ 2 ≤ 1 / 4 := by nlinarith
  have e1 : u x / 2 = -(s * (0 - u x - u' x * -t) + t * (0 - u x - u' x * s)) := by
    linear_combination (-(u x)) * hts
  have e2 : u' x / 2 = (0 - u x - u' x * -t) - (0 - u x - u' x * s) := by
    linear_combination (-(u' x)) * hts
  have p1 := mul_le_mul_of_nonneg_left hA1 hs0
  have p2 := mul_le_mul_of_nonneg_left hA2 hs0
  have p3 := mul_le_mul_of_nonneg_left hB1 ht0
  have p4 := mul_le_mul_of_nonneg_left hB2 ht0
  have hMst : M * (s * t) ≤ M / 16 := mul_le_mul_of_nonneg_left hst hM |>.trans_eq (by ring)
  have hMsq : M * (t ^ 2 + s ^ 2) ≤ M / 4 := mul_le_mul_of_nonneg_left hsq hM |>.trans_eq (by ring)
  refine ⟨abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-- An odd one-periodic function vanishes at every half-integer. -/
theorem half_int_zero {u : ℝ → ℝ} (hp : Function.Periodic u 1) (ho : ∀ x, u (-x) = -u x)
    (n : ℤ) : u (n / 2) = 0 := by
  have h : u (n / 2) = u (-(n / 2)) := by
    have := hp.int_mul n (-(n / 2 : ℝ))
    rw [show -((n : ℝ) / 2) + n * 1 = n / 2 by ring] at this
    exact this
  rw [ho] at h
  linarith

/-! ### Primitives and the Green operator -/

/-- The primitive `x ↦ ∫₀ˣ f`. -/
def prim (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, f s

theorem hasDerivAt_prim {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (prim f) (f x) x :=
  integral_hasDerivAt_right (hf.intervalIntegrable _ _) (hf.stronglyMeasurableAtFilter _ _)
    hf.continuousAt

theorem continuous_prim {f : ℝ → ℝ} (hf : Continuous f) : Continuous (prim f) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_prim hf x).continuousAt

theorem prim_zero (f : ℝ → ℝ) : prim f 0 = 0 := by simp [prim]

/-- The primitive of an even function is odd. -/
theorem prim_neg_of_even {f : ℝ → ℝ} (he : ∀ x, f (-x) = f x) (x : ℝ) :
    prim f (-x) = -prim f x := by
  have h := integral_comp_neg (a := 0) (b := x) f
  simp only [he, neg_zero] at h
  unfold prim
  rw [h, integral_symm]

/-- The primitive of an odd function is even. -/
theorem prim_neg_of_odd {f : ℝ → ℝ} (ho : ∀ x, f (-x) = -f x) (x : ℝ) :
    prim f (-x) = prim f x := by
  have h := integral_comp_neg (a := 0) (b := x) f
  simp only [ho, neg_zero, intervalIntegral.integral_neg] at h
  unfold prim
  rw [integral_symm, ← h, neg_neg]

/-- The primitive of a continuous one-periodic function with zero mean is one-periodic. -/
theorem prim_periodic {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1)
    (hmean : ∫ s in (0 : ℝ)..1, f s = 0) : Function.Periodic (prim f) 1 := by
  intro x
  unfold prim
  rw [← integral_add_adjacent_intervals (hf.intervalIntegrable 0 x) (hf.intervalIntegrable x _),
    hp.intervalIntegral_add_eq x 0, zero_add, hmean, add_zero]

/-- A continuous one-periodic function whose primitive is even (or odd) has mean
`prim f (1/2) - prim f (-1/2)`. -/
private theorem integral_period {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    ∫ s in (0 : ℝ)..1, f s = prim f (1 / 2) - prim f (-(1 / 2)) := by
  have := hp.intervalIntegral_add_eq 0 (-(1 / 2))
  rw [zero_add, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at this
  rw [this, prim, prim, ← integral_add_adjacent_intervals (hf.intervalIntegrable (-(1 / 2)) 0)
    (hf.intervalIntegrable 0 (1 / 2)), integral_symm]
  ring

/-- The derivative of the Green operator: `greenD f = prim f - 2 ∫₀^{1/2} prim f`. -/
def greenD (f : ℝ → ℝ) (x : ℝ) : ℝ := prim f x - 2 * prim (prim f) (1 / 2)

/-- The Dirichlet Green operator: the odd one-periodic solution of `u'' = f`. -/
def green (f : ℝ → ℝ) : ℝ → ℝ := prim (greenD f)

theorem continuous_greenD {f : ℝ → ℝ} (hf : Continuous f) : Continuous (greenD f) :=
  (continuous_prim hf).sub continuous_const

theorem hasDerivAt_greenD {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (greenD f) (f x) x :=
  (hasDerivAt_prim hf x).sub_const _

theorem hasDerivAt_green {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (green f) (greenD f x) x :=
  hasDerivAt_prim (continuous_greenD hf) x

theorem continuous_green {f : ℝ → ℝ} (hf : Continuous f) : Continuous (green f) :=
  continuous_prim (continuous_greenD hf)

theorem greenD_even {f : ℝ → ℝ} (ho : ∀ x, f (-x) = -f x) (x : ℝ) :
    greenD f (-x) = greenD f x := by
  simp [greenD, prim_neg_of_odd ho]

theorem green_odd {f : ℝ → ℝ} (ho : ∀ x, f (-x) = -f x) (x : ℝ) :
    green f (-x) = -green f x :=
  prim_neg_of_even (greenD_even ho) x

theorem greenD_periodic {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1)
    (ho : ∀ x, f (-x) = -f x) : Function.Periodic (greenD f) 1 := by
  have hpr : Function.Periodic (prim f) 1 := prim_periodic hf hp (by
    rw [integral_period hf hp, prim_neg_of_odd ho]; ring)
  intro x
  simp [greenD, hpr x]

theorem green_periodic {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1)
    (ho : ∀ x, f (-x) = -f x) : Function.Periodic (green f) 1 := by
  have hc := continuous_greenD hf
  refine prim_periodic hc (greenD_periodic hf hp ho) ?_
  rw [integral_period hc (greenD_periodic hf hp ho), prim_neg_of_even (greenD_even ho)]
  have h : prim (greenD f) (1 / 2) = 0 := by
    have e : prim (greenD f) (1 / 2) =
        prim (prim f) (1 / 2) - (1 / 2 - 0) * (2 * prim (prim f) (1 / 2)) := by
      show ∫ s in (0 : ℝ)..1 / 2, (prim f s - 2 * prim (prim f) (1 / 2)) = _
      rw [intervalIntegral.integral_sub ((continuous_prim hf).intervalIntegrable _ _)
        intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
      rfl
    rw [e]; ring
  rw [h]; ring

end KAM.SpinOrbit.Lock

end
