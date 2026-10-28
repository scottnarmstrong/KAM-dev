/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries.Pair

/-!
# Planar quartic torsion: a small big-O calculus for real powers (P11C, package T18)

Blueprint P, Part 11b (`bpP:p11b:asymptotics`): products of `a ^ r` powers, division by `a`, and
the lower-bound transfer used for the projector estimates, all along `a → 0⁺`.
-/

@[expose] public noncomputable section
open Set Filter Asymptotics Real
open scoped Topology
namespace KAM.Planetary

theorem p11cAe_pos : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a := self_mem_nhdsWithin

theorem p11cAe_lt_one : ∀ᶠ a : ℝ in 𝓝[>] 0, a < 1 :=
  nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))

/-- Product of two power bounds. -/
theorem p11cAe_mul {f g : ℝ → ℝ} {r s : ℝ} (hf : f =O[𝓝[>] 0] fun a : ℝ => a ^ r)
    (hg : g =O[𝓝[>] 0] fun a : ℝ => a ^ s) :
    (fun a => f a * g a) =O[𝓝[>] 0] fun a : ℝ => a ^ (r + s) :=
  (hf.mul hg).congr' EventuallyEq.rfl
    (p11cAe_pos.mono fun a ha => (Real.rpow_add ha r s).symm)

/-- A constant multiple of a power is `O` of the power. -/
theorem p11cAe_const_mul (c : ℝ) (r : ℝ) :
    (fun a : ℝ => c * a ^ r) =O[𝓝[>] 0] fun a : ℝ => a ^ r :=
  (isBigO_refl _ _).const_mul_left c

/-- Division by `a` lowers the exponent by one. -/
theorem p11cAe_div {f : ℝ → ℝ} {r : ℝ} (hf : f =O[𝓝[>] 0] fun a : ℝ => a ^ (r + 1)) :
    (fun a => f a / a) =O[𝓝[>] 0] fun a : ℝ => a ^ r := by
  obtain ⟨c, hc⟩ := hf.bound
  refine IsBigO.of_bound c ?_
  filter_upwards [hc, p11cAe_pos] with a ha h0
  rw [norm_div, Real.norm_of_nonneg h0.le, div_le_iff₀ h0, Real.norm_of_nonneg
    (Real.rpow_nonneg h0.le _), mul_assoc, ← Real.rpow_add_one h0.ne']
  rwa [Real.norm_of_nonneg (Real.rpow_nonneg h0.le _)] at ha

/-- Natural power as a real power. -/
theorem p11cAe_natPow (n : ℕ) : (fun a : ℝ => a ^ n) = fun a : ℝ => a ^ (n : ℝ) := by
  funext a; exact (Real.rpow_natCast a n).symm

/-- `√a = a ^ (1/2)`. -/
theorem p11cAe_sqrt : (fun a : ℝ => √a) = fun a : ℝ => a ^ (1 / 2 : ℝ) := by
  funext a; exact Real.sqrt_eq_rpow a

/-- Lower bound transfer: if `f = -k a ^ r + O(a ^ s)` with `r < s` and `k > 0`, then
`-f ≥ (k / 2) a ^ r` near `0⁺`. -/
theorem p11cAe_lower {f : ℝ → ℝ} {k r s : ℝ} (hk : 0 < k) (hrs : r < s)
    (hf : (fun a => f a + k * a ^ r) =O[𝓝[>] 0] fun a : ℝ => a ^ s) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, k / 2 * a ^ r ≤ -f a := by
  obtain ⟨c, hc⟩ := hf.bound
  have hlt : ∀ᶠ a : ℝ in 𝓝[>] 0, a ^ (s - r) < k / (2 * (|c| + 1)) := by
    have hcont : ContinuousAt (fun a : ℝ => a ^ (s - r)) 0 :=
      Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))
    have h0 : (fun a : ℝ => a ^ (s - r)) 0 = 0 := by
      simp [Real.zero_rpow (by linarith : s - r ≠ 0)]
    have hm : Iio (k / (2 * (|c| + 1))) ∈ 𝓝 ((fun a : ℝ => a ^ (s - r)) 0) :=
      Iio_mem_nhds (by rw [h0]; positivity)
    exact nhdsWithin_le_nhds (hcont.eventually_mem hm)
  filter_upwards [hc, hlt, p11cAe_pos] with a ha hl h0
  rw [Real.norm_of_nonneg (Real.rpow_nonneg h0.le _)] at ha
  have e : a ^ s = a ^ (s - r) * a ^ r := by
    rw [← Real.rpow_add h0]; ring_nf
  have hr : 0 < a ^ r := Real.rpow_pos_of_pos h0 r
  have h1 : |f a + k * a ^ r| ≤ |c| * (a ^ (s - r) * a ^ r) := by
    calc |f a + k * a ^ r| = ‖f a + k * a ^ r‖ := rfl
      _ ≤ c * a ^ s := ha
      _ ≤ |c| * a ^ s := mul_le_mul_of_nonneg_right (le_abs_self c) (Real.rpow_nonneg h0.le _)
      _ = _ := by rw [e]
  have h2 : |c| * a ^ (s - r) ≤ k / 2 := by
    have : |c| * a ^ (s - r) ≤ |c| * (k / (2 * (|c| + 1))) :=
      mul_le_mul_of_nonneg_left hl.le (abs_nonneg c)
    refine this.trans ?_
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg c]
  have h3 : |f a + k * a ^ r| ≤ k / 2 * a ^ r := by
    calc _ ≤ |c| * (a ^ (s - r) * a ^ r) := h1
      _ = (|c| * a ^ (s - r)) * a ^ r := by ring
      _ ≤ k / 2 * a ^ r := mul_le_mul_of_nonneg_right h2 hr.le
  have := (abs_le.1 h3).2
  linarith

end KAM.Planetary

end
