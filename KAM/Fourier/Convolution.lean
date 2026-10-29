/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Fourier.Derivative
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multiplication of weighted Fourier coefficients

Convolution is absolutely convergent for weighted summable coefficient families
at a nonnegative radius. It preserves weighted summability and satisfies the
submultiplicative estimate `weightedNorm s (convolution a b) ≤ ‖a‖_s * ‖b‖_s`.
These are the multiplication estimates underlying the planned Fourier Banach algebra;
the complete normed-algebra structure and the function-space bridge are separate.
-/

@[expose] public section

noncomputable section

namespace KAM.Fourier

variable {n : ℕ}

/-- The coefficient convolution corresponding to multiplication of Fourier series. -/
def convolution (a b : (Fin n → ℤ) → ℂ) (k : Fin n → ℤ) : ℂ :=
  ∑' l, a l * b (k - l)

theorem modeSize_add_le (k l : Fin n → ℤ) : modeSize (k + l) ≤ modeSize k + modeSize l := by
  unfold modeSize
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  simpa using abs_add_le (k j : ℝ) (l j : ℝ)

theorem modeSize_le_add_sub (k l : Fin n → ℤ) :
    modeSize k ≤ modeSize l + modeSize (k - l) := by
  have he : l + (k - l) = k := by abel
  simpa only [he] using modeSize_add_le l (k - l)

/-- The exponential weight is submultiplicative at nonnegative radii. -/
theorem exp_modeSize_le_mul {s : ℝ} (hs : 0 ≤ s) (k l : Fin n → ℤ) :
    Real.exp (s * modeSize k) ≤
      Real.exp (s * modeSize l) * Real.exp (s * modeSize (k - l)) := by
  rw [← Real.exp_add, ← mul_add]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (modeSize_le_add_sub k l) hs)

theorem convolution_term_weight_le {s : ℝ} (hs : 0 ≤ s)
    (a b : (Fin n → ℤ) → ℂ) (k l : Fin n → ℤ) :
    ‖a l * b (k - l)‖ * Real.exp (s * modeSize k) ≤
      (‖a l‖ * Real.exp (s * modeSize l)) *
        (‖b (k - l)‖ * Real.exp (s * modeSize (k - l))) := by
  rw [norm_mul]
  calc
    (‖a l‖ * ‖b (k - l)‖) * Real.exp (s * modeSize k) ≤
        (‖a l‖ * ‖b (k - l)‖) *
          (Real.exp (s * modeSize l) * Real.exp (s * modeSize (k - l))) :=
      mul_le_mul_of_nonneg_left (exp_modeSize_le_mul hs k l) (by positivity)
    _ = (‖a l‖ * Real.exp (s * modeSize l)) *
        (‖b (k - l)‖ * Real.exp (s * modeSize (k - l))) := by ring

/-- Change from output mode and summation index to the two input modes. -/
private def convolutionEquiv : ((Fin n → ℤ) × (Fin n → ℤ)) ≃
    ((Fin n → ℤ) × (Fin n → ℤ)) where
  toFun p := (p.2, p.1 - p.2)
  invFun p := (p.1 + p.2, p.1)
  left_inv p := by ext j <;> simp
  right_inv p := by ext j <;> simp

private theorem summable_product_majorant {s : ℝ} {a b : (Fin n → ℤ) → ℂ}
    (ha : SummableWeighted s a) (hb : SummableWeighted s b) :
    Summable (fun p : (Fin n → ℤ) × (Fin n → ℤ) =>
      (‖a p.1‖ * Real.exp (s * modeSize p.1)) *
        (‖b p.2‖ * Real.exp (s * modeSize p.2))) := by
  exact ha.mul_of_nonneg hb (fun _ => by positivity) (fun _ => by positivity)

private theorem summable_convolution_majorant {s : ℝ} {a b : (Fin n → ℤ) → ℂ}
    (ha : SummableWeighted s a) (hb : SummableWeighted s b) :
    Summable (fun p : (Fin n → ℤ) × (Fin n → ℤ) =>
      (‖a p.2‖ * Real.exp (s * modeSize p.2)) *
        (‖b (p.1 - p.2)‖ * Real.exp (s * modeSize (p.1 - p.2)))) := by
  exact (convolutionEquiv (n := n)).summable_iff.mpr (summable_product_majorant ha hb)

/-- Every convolution coefficient is absolutely convergent. -/
theorem summable_norm_convolution {s : ℝ} (hs : 0 ≤ s) {a b : (Fin n → ℤ) → ℂ}
    (ha : SummableWeighted s a) (hb : SummableWeighted s b) (k : Fin n → ℤ) :
    Summable (fun l => ‖a l * b (k - l)‖) := by
  have h := Summable.of_nonneg_of_le (fun _ => by positivity)
    (convolution_term_weight_le hs a b k) ((summable_convolution_majorant ha hb).prod_factor k)
  exact (summable_mul_right_iff (Real.exp_ne_zero (s * modeSize k))).mp h

theorem convolution_weight_le {s : ℝ} (hs : 0 ≤ s) {a b : (Fin n → ℤ) → ℂ}
    (ha : SummableWeighted s a) (hb : SummableWeighted s b) (k : Fin n → ℤ) :
    ‖convolution a b k‖ * Real.exp (s * modeSize k) ≤
      ∑' l, (‖a l‖ * Real.exp (s * modeSize l)) *
        (‖b (k - l)‖ * Real.exp (s * modeSize (k - l))) := by
  have hr := summable_norm_convolution hs ha hb k
  calc
    ‖convolution a b k‖ * Real.exp (s * modeSize k) ≤
        (∑' l, ‖a l * b (k - l)‖) * Real.exp (s * modeSize k) :=
      mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hr) (Real.exp_nonneg _)
    _ = ∑' l, ‖a l * b (k - l)‖ * Real.exp (s * modeSize k) := tsum_mul_right.symm
    _ ≤ ∑' l, (‖a l‖ * Real.exp (s * modeSize l)) *
        (‖b (k - l)‖ * Real.exp (s * modeSize (k - l))) :=
      Summable.tsum_le_tsum (convolution_term_weight_le hs a b k)
        (hr.mul_right _) ((summable_convolution_majorant ha hb).prod_factor k)

/-- Multiplication preserves weighted absolute summability at nonnegative radii. -/
theorem SummableWeighted.convolution {s : ℝ} (hs : 0 ≤ s) {a b : (Fin n → ℤ) → ℂ}
    (ha : SummableWeighted s a) (hb : SummableWeighted s b) :
    SummableWeighted s (convolution a b) := by
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (convolution_weight_le hs ha hb) (summable_convolution_majorant ha hb).prod

/-- The weighted Fourier coefficient norm is submultiplicative under convolution. -/
theorem weightedNorm_convolution_le {s : ℝ} (hs : 0 ≤ s) {a b : (Fin n → ℤ) → ℂ}
    (ha : SummableWeighted s a) (hb : SummableWeighted s b) :
    weightedNorm s (convolution a b) ≤ weightedNorm s a * weightedNorm s b := by
  have hm := summable_convolution_majorant ha hb
  calc
    weightedNorm s (convolution a b) ≤
        ∑' k, ∑' l, (‖a l‖ * Real.exp (s * modeSize l)) *
          (‖b (k - l)‖ * Real.exp (s * modeSize (k - l))) :=
      Summable.tsum_le_tsum (convolution_weight_le hs ha hb) (ha.convolution hs hb) hm.prod
    _ = ∑' p : (Fin n → ℤ) × (Fin n → ℤ),
        (‖a p.2‖ * Real.exp (s * modeSize p.2)) *
          (‖b (p.1 - p.2)‖ * Real.exp (s * modeSize (p.1 - p.2))) := hm.tsum_prod.symm
    _ = ∑' p : (Fin n → ℤ) × (Fin n → ℤ),
        (‖a p.1‖ * Real.exp (s * modeSize p.1)) *
          (‖b p.2‖ * Real.exp (s * modeSize p.2)) :=
      (convolutionEquiv (n := n)).tsum_eq (fun p =>
        (‖a p.1‖ * Real.exp (s * modeSize p.1)) *
          (‖b p.2‖ * Real.exp (s * modeSize p.2)))
    _ = weightedNorm s a * weightedNorm s b :=
      (ha.tsum_mul_tsum hb (ha.mul_of_nonneg hb (fun _ => by positivity)
        (fun _ => by positivity))).symm

/-- Convolution is commutative, by exchanging the two input modes. -/
theorem convolution_comm (a b : (Fin n → ℤ) → ℂ) : convolution a b = convolution b a := by
  funext k
  have h := (Equiv.subLeft k).tsum_eq (fun l => a l * b (k - l))
  simpa [convolution, mul_comm] using h.symm

theorem convolution_add {s : ℝ} (hs : 0 ≤ s) {a b c : (Fin n → ℤ) → ℂ}
    (ha : SummableWeighted s a) (hb : SummableWeighted s b) (hc : SummableWeighted s c) :
    convolution a (b + c) = convolution a b + convolution a c := by
  funext k
  simp only [convolution, Pi.add_apply, mul_add]
  exact (summable_norm_convolution hs ha hb k).of_norm.tsum_add
    (summable_norm_convolution hs ha hc k).of_norm

theorem convolution_smul_left (a b : (Fin n → ℤ) → ℂ) (c : ℂ) :
    convolution (c • a) b = c • convolution a b := by
  funext k
  simp [convolution, mul_assoc, tsum_mul_left]

/-- The coefficients of the constant function one. -/
def unitCoeff (k : Fin n → ℤ) : ℂ := if k = 0 then 1 else 0

@[simp] theorem convolution_unit_left (a : (Fin n → ℤ) → ℂ) :
    convolution unitCoeff a = a := by
  funext k
  calc
    convolution unitCoeff a k = unitCoeff 0 * a (k - 0) :=
      tsum_eq_single 0 (fun l hl => by simp [unitCoeff, hl])
    _ = a k := by simp [unitCoeff]

@[simp] theorem convolution_unit_right (a : (Fin n → ℤ) → ℂ) :
    convolution a unitCoeff = a := by
  rw [convolution_comm, convolution_unit_left]

end KAM.Fourier
