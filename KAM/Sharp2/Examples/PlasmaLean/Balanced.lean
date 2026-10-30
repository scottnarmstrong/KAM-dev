/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Freq.SmallDivisorFiber
public import KAM.Sharp2.SmallDiv.Bound
public import KAM.Sharp2.SmallDiv.Solution
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The fibered small-divisor checker in balanced form

`KAM.CertificateSharp.SdsData.fiberBound` sums over the modes `0 < |k'| ≤ N` of `ω' ∈ ℝ¹` as a
`Finset.sum`, a linear fold: the kernel's recursion follows the list, and it runs out of stack
between `N = 764` and `N = 1529`. For a cut-off `N = 2^l` the same finite sum is computed here by
bisection (`balSum`, `balAll`), of depth `l`, which also keeps the intermediate rationals small.

* `balSum_eq`, `balAll_iff`: the balanced sum is the sum;
* `sum_modeBox_one`, `forall_modeBox_one`: the modes of `modeBox 1 N` are `±(j + 1)`, `j < N`;
* `balCheck`, `balBound`: the test and the bound of `sdsFiberBound_sound`;
* `smallDivisorSum_le_bal`: soundness;
* `sdConst_two_of_sdSum`: from a rational bound of `S(ω, b)`, `n = 2`, `τ = 1`, to `SDConst`.
-/

@[expose] public section

namespace KAM.Sharp2.Examples

open KAM KAM.Certificate KAM.CertificateSharp

/-- `∑_{i < 2^l} f (a + i)`, by bisection. -/
def balSum (f : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, a => f a
  | l + 1, a => balSum f l a + balSum f l (a + 2 ^ l)

/-- `∀ i < 2^l, p (a + i)`, by bisection. -/
def balAll (p : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, a => p a
  | l + 1, a => balAll p l a && balAll p l (a + 2 ^ l)

theorem balSum_eq (f : ℕ → ℚ) (l a : ℕ) :
    balSum f l a = ∑ i ∈ Finset.range (2 ^ l), f (a + i) := by
  induction l generalizing a with
  | zero => simp [balSum]
  | succ l ih =>
    rw [balSum, ih, ih, pow_succ, mul_two, Finset.sum_range_add]
    simp only [add_assoc]

theorem balAll_iff (p : ℕ → Bool) (l a : ℕ) :
    balAll p l a = true ↔ ∀ i < 2 ^ l, p (a + i) = true := by
  induction l generalizing a with
  | zero => simp [balAll]
  | succ l ih =>
    rw [balAll, Bool.and_eq_true, ih, ih]
    refine ⟨fun ⟨h1, h2⟩ i hi => ?_, fun h => ⟨fun i hi => ?_, fun i hi => ?_⟩⟩
    · by_cases his : i < 2 ^ l
      · exact h1 i his
      · have := h2 (i - 2 ^ l) (by rw [pow_succ] at hi; omega)
        rwa [show a + 2 ^ l + (i - 2 ^ l) = a + i by omega] at this
    · exact h i (by rw [pow_succ]; omega)
    · have := h (2 ^ l + i) (by rw [pow_succ]; omega)
      rwa [← add_assoc] at this

/-- The mode `j + 1` of `ℝ¹`. -/
def posMode (j : ℕ) : Fin 1 → ℤ := fun _ => ((j + 1 : ℕ) : ℤ)

/-- The mode `-(j + 1)` of `ℝ¹`. -/
def negMode (j : ℕ) : Fin 1 → ℤ := fun _ => -((j + 1 : ℕ) : ℤ)

theorem modeNat_one (k : Fin 1 → ℤ) : modeNat k = (k 0).natAbs := by simp [modeNat]

theorem eq_const_one (k : Fin 1 → ℤ) : k = fun _ => k 0 := by
  funext i
  rw [Subsingleton.elim i 0]

theorem modeBox_one (N : ℕ) : modeBox 1 N =
    (Finset.range N).image posMode ∪ (Finset.range N).image negMode := by
  ext k
  rw [mem_modeBox, modeNat_one, Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨hk, hN⟩
    have h0 : k 0 ≠ 0 := fun h => hk (by rw [eq_const_one k, h]; rfl)
    rcases lt_or_gt_of_ne h0 with h | h
    · refine Or.inr ⟨(k 0).natAbs - 1, by rw [Finset.mem_range]; omega, ?_⟩
      rw [eq_const_one k]
      funext _
      simp only [negMode]
      omega
    · refine Or.inl ⟨(k 0).natAbs - 1, by rw [Finset.mem_range]; omega, ?_⟩
      rw [eq_const_one k]
      funext _
      simp only [posMode]
      omega
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> rw [Finset.mem_range] at hj
    · refine ⟨fun h => ?_, ?_⟩
      · have := congrFun h 0
        simp only [posMode, Pi.zero_apply] at this
        omega
      · simp only [posMode]
        omega
    · refine ⟨fun h => ?_, ?_⟩
      · have := congrFun h 0
        simp only [negMode, Pi.zero_apply] at this
        omega
      · simp only [negMode]
        omega

theorem posMode_inj : Function.Injective posMode := fun i j h => by
  have := congrFun h 0
  simp only [posMode] at this
  omega

theorem negMode_inj : Function.Injective negMode := fun i j h => by
  have := congrFun h 0
  simp only [negMode] at this
  omega

theorem sum_modeBox_one (F : (Fin 1 → ℤ) → ℚ) (N : ℕ) :
    ∑ k ∈ modeBox 1 N, F k = ∑ j ∈ Finset.range N, (F (posMode j) + F (negMode j)) := by
  have hdisj : Disjoint ((Finset.range N).image posMode) ((Finset.range N).image negMode) := by
    rw [Finset.disjoint_left]
    rintro _ h1 h2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨j, -, h⟩ := Finset.mem_image.mp h2
    have := congrFun h 0
    simp only [posMode, negMode] at this
    omega
  rw [modeBox_one, Finset.sum_union hdisj, Finset.sum_image fun _ _ _ _ h => posMode_inj h,
    Finset.sum_image fun _ _ _ _ h => negMode_inj h, Finset.sum_add_distrib]

theorem forall_modeBox_one {P : (Fin 1 → ℤ) → Prop} {N : ℕ}
    (h : ∀ j < N, P (posMode j) ∧ P (negMode j)) : ∀ k ∈ modeBox 1 N, P k := by
  intro k hk
  rw [modeBox_one, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hk
  rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact (h j (Finset.mem_range.mp hj)).1
  · exact (h j (Finset.mem_range.mp hj)).2

section Fiber

variable (d : SdsData)

/-- The summand of `SdsData.fiberSum`. -/
def fiberTerm (k : Fin 1 → ℤ) : ℚ :=
  d.E1 ^ (modeNat k + (fiberP d.box k).natAbs) * ((fiberLb d.box k) ^ 2)⁻¹ +
    d.E1 ^ modeNat k * ((if fiberP d.box k = 0 then 0
      else (((fiberP d.box k).natAbs : ℚ) - 1 / 2) ^ 2)⁻¹ + d.E1 * fiberC0Q)

/-- The test of `SdsData.fiberCheck` at one mode. -/
def fiberOk (k : Fin 1 → ℤ) : Bool :=
  decide (0 < fiberLb d.box k) &&
    decide (|boxDot d.box k + fiberP d.box k| + boxRad d.box k ≤ 1 / 2)

/-- `SdsData.fiberCheck` in balanced form, for `N = 2^l`. -/
def balCheck (l : ℕ) : Bool :=
  decide (0 < d.γ) && decide (0 < d.δ) && decide (0 < d.cLo) && decide (1 ≤ d.E1 * d.expLow) &&
    balAll (fun j => fiberOk d (posMode j) && fiberOk d (negMode j)) l 0

/-- `SdsData.fiberBound` in balanced form, for `N = 2^l`. -/
def balBound (l : ℕ) : ℚ :=
  d.E1 * (99225 / 30000) +
    balSum (fun j => fiberTerm d (posMode j) + fiberTerm d (negMode j)) l 0 + d.tailBound

variable {d} {l : ℕ}

theorem fiberCheck_of_bal (hN : d.N = 2 ^ l) (h : balCheck d l = true) :
    d.fiberCheck (m := 1) = true := by
  simp only [balCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hγ, hδ⟩, hc⟩, hE⟩, hall⟩ := h
  rw [balAll_iff] at hall
  have key : ∀ k ∈ modeBox 1 d.N,
      0 < fiberLb d.box k ∧ |boxDot d.box k + fiberP d.box k| + boxRad d.box k ≤ 1 / 2 := by
    refine forall_modeBox_one fun j hj => ?_
    have := hall j (hN ▸ hj)
    simp only [zero_add, fiberOk, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  simp only [SdsData.fiberCheck, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨hγ, hδ⟩, hc⟩, hE⟩, key⟩

theorem fiberBound_eq_bal (hN : d.N = 2 ^ l) : d.fiberBound (m := 1) = balBound d l := by
  have e : d.fiberSum (m := 1) = ∑ k ∈ modeBox 1 d.N, fiberTerm d k := rfl
  rw [SdsData.fiberBound, balBound, e, sum_modeBox_one, hN, balSum_eq]
  simp only [zero_add]

end Fiber

/-- **Soundness of the balanced checker.** -/
theorem smallDivisorSum_le_bal (d : SdsData) {l : ℕ} (hN : d.N = 2 ^ l)
    (h : balCheck d l = true) {B : ℚ} (hB : balBound d l ≤ B) {ω' : Fin 1 → ℝ}
    (hω : FreqEncloses 1 d.box ω') (hdio : IsDiophantine (d.γ : ℝ) 1 (Fin.snoc ω' 1)) :
    smallDivisorSum (Fin.snoc ω' 1 : Fin 2 → ℝ) (d.δ : ℝ) ≤ (B : ℝ) := by
  have h1 := sdsFiberBound_sound d (fiberCheck_of_bal hN h) hω hdio
  rw [fiberBound_eq_bal hN] at h1
  exact h1.trans (by exact_mod_cast hB)

/-- From a bound of `S(ω, b)` to a small-divisor constant, `n = 2`, `τ = 1`: the rational test is
`B (γ b)² ≤ (3.1415 c)²`. -/
theorem sdConst_two_of_sdSum {ω : Fin 2 → ℝ} {γ b c B : ℝ} (hγ : 0 < γ) (hb : 0 < b) (hc : 0 < c)
    (hdio : IsDiophantine γ 1 ω) (hS : sdSum ω b ≤ B)
    (hnum : B * (γ * b) ^ 2 ≤ (31415 / 10000 * c) ^ 2) :
    SDConst 2 1 γ b c {ω} := by
  refine sdConst_of_sdSum hc hb hγ zero_le_one (fun ω' hω' => hω' ▸ hdio) ?_
  intro ω' hω'
  rw [Set.mem_singleton_iff.mp hω']
  have hpi := Real.pi_gt_d4
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hgb : 0 < γ * b := mul_pos hγ hb
  have hs4 : Real.sqrt (2 ^ 2) = 2 := by
    rw [Real.sqrt_sq (by norm_num)]
  have hsq : Real.sqrt (sdSum ω b) * (γ * b) ≤ 31415 / 10000 * c := by
    have h1 : sdSum ω b * (γ * b) ^ 2 ≤ (31415 / 10000 * c) ^ 2 :=
      (mul_le_mul_of_nonneg_right hS (sq_nonneg _)).trans hnum
    have h2 : Real.sqrt (sdSum ω b) * (γ * b) =
        Real.sqrt (sdSum ω b * (γ * b) ^ 2) := by
      rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hgb.le]
    rw [h2]
    exact Real.sqrt_le_iff.mpr ⟨by positivity, h1⟩
  have hgoal : (2 * Real.pi)⁻¹ * 2 * Real.sqrt (sdSum ω b) ≤ c * γ⁻¹ * b⁻¹ := by
    have e1 : (2 * Real.pi)⁻¹ * 2 * Real.sqrt (sdSum ω b) = Real.sqrt (sdSum ω b) / Real.pi := by
      field_simp
    have e2 : c * γ⁻¹ * b⁻¹ = c / (γ * b) := by field_simp
    rw [e1, e2, div_le_div_iff₀ hpi0 hgb]
    have h3 : 31415 / 10000 * c ≤ c * Real.pi := by nlinarith
    linarith
  rw [hs4, Real.rpow_neg_one]
  exact hgoal

end KAM.Sharp2.Examples

end
