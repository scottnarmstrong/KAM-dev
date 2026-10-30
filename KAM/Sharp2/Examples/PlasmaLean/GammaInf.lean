/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Examples.PlasmaLean.Frequency
public import KAM.CertificateSharp.Step0.GammaInf
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# `Γ_∞` at PlasmaLean's frequency (package B10c)

The fibered certificate `KAM.smallDivisorSup_snoc_le` for the clock frequency `ω* = (ι, 1)`, with
one entry per `0 < |k'| ≤ N`: the nearest integer `p(k')` of `-k'ι`, the lower bound
`|k'c + p| - |k'| r ≤ |k'ι + p|` from the enclosure `|ι - c| ≤ r`, and the weights
`E₁^j ≥ e^{-2πδj}`
(a Taylor test of degree four). `GInfData.check` is the rational test,
`GInfData.sound` its soundness: `Γ_∞(ω*, δ) ≤ claim`.

* `gammaInf_d0`: `Γ_∞(ω*, δ₀) ≤ 5.51`, `δ₀ = 333/100000` (the maximum `5.50` is at `k = (-29, 4)`);
* `gammaInf_rho`: `Γ_∞(ω*, ρ) ≤ 1.54`, `ρ = 1/50` (the maximum `1.533` is at `k = (-7, 1)`).
-/

@[expose] public section

namespace KAM.Sharp2.Examples

open KAM KAM.Certificate KAM.CertificateSharp

/-- The centre of the enclosure of `ι`. -/
def iotaC : ℚ := 137430725939 / 10 ^ 12

/-- The radius of the enclosure of `ι`. -/
def iotaR : ℚ := 1 / 10 ^ 12

theorem abs_iota_sub_le : |iota - (iotaC : ℝ)| ≤ (iotaR : ℝ) := by
  have hl := sqrt5_lo
  have hh := sqrt5_hi
  rw [abs_le]
  simp only [iota, iotaC, iotaR]
  push_cast
  constructor <;> linarith

/-- The data of a fibered `Γ_∞` claim at `ω*`. -/
structure GInfData where
  /-- The loss of `Γ_∞(ω*, δ)`. -/
  δ : ℚ
  /-- The cut-off of the fibers. -/
  N : ℕ
  /-- A rational upper bound of `e^{-2πδ}`. -/
  E1 : ℚ
  /-- The claimed bound. -/
  claim : ℚ

namespace GInfData

variable (d : GInfData)

/-- The Taylor polynomial `1 + y + y²/2 + y³/6 + y⁴/24` at `y = 6.283 δ`, a lower bound of
`e^{2πδ}`. -/
def expLow : ℚ :=
  1 + 6283 / 1000 * d.δ + (6283 / 1000 * d.δ) ^ 2 / 2 + (6283 / 1000 * d.δ) ^ 3 / 6 +
    (6283 / 1000 * d.δ) ^ 4 / 24

/-- The nearest integer of `-z ι`. -/
def pk (z : ℤ) : ℤ := ⌊-((z : ℚ) * iotaC) + 1 / 2⌋

/-- `|z c + p(z)|`. -/
def dist (z : ℤ) : ℚ := |(z : ℚ) * iotaC + (pk z : ℚ)|

/-- The lower bound of `|z ι + p(z)|`. -/
def lb (z : ℤ) : ℚ := dist z - |(z : ℚ)| * iotaR

/-- The test of the fiber `k' = z`. -/
def fiberOk (z : ℤ) : Bool :=
  decide (dist z + |(z : ℚ)| * iotaR ≤ 1 / 2) && decide (0 < lb z) &&
    decide (d.E1 ^ (z.natAbs + (pk z).natAbs) ≤ d.claim * (628 / 100 * lb z)) &&
    decide (d.E1 ^ z.natAbs ≤ d.claim * (314 / 100))

/-- The rational test: the side conditions and every fiber `0 < |z| ≤ N`. -/
def check : Bool :=
  decide (0 < d.δ) && decide (1 ≤ 628 / 100 * d.δ * (d.N + 1)) &&
    decide (1 ≤ d.E1 * d.expLow) &&
    decide (((d.N : ℚ) + 1) * d.E1 ^ (d.N + 1) ≤ d.claim * (628 / 100 * gammaStar)) &&
    decide (d.E1 ≤ d.claim * (628 / 100)) &&
    (List.range d.N).all fun j => d.fiberOk ((j : ℤ) + 1) && d.fiberOk (-((j : ℤ) + 1))

theorem frequencyDot_one (k : Fin 1 → ℤ) :
    Diophantine.frequencyDot ![iota] k = (k 0 : ℝ) * iota := by
  simp [Diophantine.frequencyDot]

/-- `|z ι + p| ≤ |z c + p| + |z| r` and `≥ |z c + p| - |z| r`. -/
theorem abs_dot_bounds (z : ℤ) :
    |(z : ℝ) * iota + (pk z : ℝ)| ≤ (dist z : ℝ) + |(z : ℝ)| * iotaR ∧
      (lb z : ℝ) ≤ |(z : ℝ) * iota + (pk z : ℝ)| := by
  have hd : |(z : ℝ) * iota - (z : ℝ) * iotaC| ≤ |(z : ℝ)| * iotaR := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left abs_iota_sub_le (abs_nonneg _)
  have hdist : ((dist z : ℚ) : ℝ) = |(z : ℝ) * iotaC + (pk z : ℝ)| := by
    simp [dist]
  have e : (z : ℝ) * iota + (pk z : ℝ) =
      ((z : ℝ) * iotaC + (pk z : ℝ)) + ((z : ℝ) * iota - (z : ℝ) * iotaC) := by ring
  constructor
  · rw [e, hdist]
    exact (abs_add_le _ _).trans (add_le_add le_rfl hd)
  · have hlb : ((lb z : ℚ) : ℝ) = (dist z : ℝ) - |(z : ℝ)| * iotaR := by
      simp [lb]
    rw [hlb, hdist, e]
    have := abs_sub_abs_le_abs_sub ((z : ℝ) * iotaC + (pk z : ℝ))
      (-((z : ℝ) * iota - (z : ℝ) * iotaC))
    rw [abs_neg, sub_neg_eq_add] at this
    linarith

theorem modeNat_one (k : Fin 1 → ℤ) : modeNat k = (k 0).natAbs := by
  simp [modeNat]

/-- Every fiber `0 < |k'| ≤ N` passes when the list test passes. -/
theorem fiberOk_of_check (h : (List.range d.N).all
      (fun j => d.fiberOk ((j : ℤ) + 1) && d.fiberOk (-((j : ℤ) + 1))) = true)
    {k : Fin 1 → ℤ} (hk : k ∈ modeBox 1 d.N) : d.fiberOk (k 0) = true := by
  rw [List.all_eq_true] at h
  obtain ⟨hk0, hkN⟩ := mem_modeBox.mp hk
  rw [modeNat_one] at hkN
  have hz : k 0 ≠ 0 := fun h0 => hk0 (funext fun i => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simpa using h0)
  have hpos : 0 < (k 0).natAbs := Int.natAbs_pos.mpr hz
  have hj := h ((k 0).natAbs - 1) (List.mem_range.mpr (by omega))
  rw [Bool.and_eq_true] at hj
  have e : (((k 0).natAbs - 1 : ℕ) : ℤ) + 1 = ((k 0).natAbs : ℤ) := by omega
  rw [e] at hj
  rcases Int.natAbs_eq (k 0) with h1 | h1
  · rw [h1]; exact hj.1
  · rw [h1]; exact hj.2

variable {d}

/-- The exponential test: `1 ≤ E₁ (1 + y + … + y⁴/24)`, `y = 6.283 δ`, gives `e^{-2πδ} ≤ E₁`. -/
theorem exp_neg_le_E1' (hδ : 0 < (d.δ : ℝ)) (h : 1 ≤ d.E1 * d.expLow) :
    Real.exp (-(2 * Real.pi * d.δ)) ≤ (d.E1 : ℝ) := by
  have hpi := Real.pi_gt_d4
  set y : ℝ := 6283 / 1000 * d.δ with hy
  have hy0 : 0 ≤ y := by positivity
  have hyb : y ≤ 2 * Real.pi * d.δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
  have hP : 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 ≤ Real.exp (2 * Real.pi * d.δ) := by
    set x : ℝ := 2 * Real.pi * d.δ with hx
    have h1 := Real.sum_le_exp_of_nonneg (hy0.trans hyb) 5
    have e1 : ∑ i ∈ Finset.range 5, x ^ i / (i.factorial : ℝ) =
        1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [e1] at h1
    have hmono : 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 ≤
        1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 := by
      gcongr
    exact hmono.trans h1
  have hcast : ((d.expLow : ℚ) : ℝ) = 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 := by
    simp only [expLow, hy]
    push_cast
    ring
  have h' : (1 : ℝ) ≤ d.E1 * (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24) := by
    have := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at this
    rwa [← hcast]
  have hP0 : 0 < 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 := by positivity
  have hinv : (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24)⁻¹ ≤ (d.E1 : ℝ) := by
    rw [inv_eq_one_div, div_le_iff₀ hP0]
    exact h'
  calc Real.exp (-(2 * Real.pi * d.δ)) = (Real.exp (2 * Real.pi * d.δ))⁻¹ := Real.exp_neg _
    _ ≤ (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24)⁻¹ := inv_anti₀ hP0 hP
    _ ≤ (d.E1 : ℝ) := hinv

/-- **Soundness of the fibered `Γ_∞` test.** -/
theorem sound (h : d.check = true) : smallDivisorSup omegaStar (d.δ : ℝ) ≤ (d.claim : ℝ) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hδ, hN⟩, hE1⟩, htail⟩, hB1⟩, hlist⟩ := h
  have hbox : ∀ k ∈ modeBox 1 d.N, dist (k 0) + |((k 0 : ℤ) : ℚ)| * iotaR ≤ 1 / 2 ∧
      0 < lb (k 0) ∧ d.E1 ^ (modeNat k + (pk (k 0)).natAbs) ≤ d.claim * (628 / 100 * lb (k 0)) ∧
      d.E1 ^ modeNat k ≤ d.claim * (314 / 100) := fun k hk => by
    have h1 := fiberOk_of_check d hlist hk
    simp only [fiberOk, Bool.and_eq_true, decide_eq_true_eq] at h1
    rw [modeNat_one]
    exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩
  have hγ' : (0 : ℝ) < gammaStar := by norm_num [gammaStar]
  have hδ' : (0 : ℝ) < d.δ := by exact_mod_cast hδ
  have hpi := Real.pi_gt_d2
  have hE : Real.exp (-(2 * Real.pi * d.δ)) ≤ (d.E1 : ℝ) := exp_neg_le_E1' hδ' hE1
  have hE10 : (0 : ℝ) ≤ d.E1 := (Real.exp_pos _).le.trans hE
  have hEj : ∀ j : ℕ, Real.exp (-(2 * Real.pi * d.δ) * j) ≤ (d.E1 : ℝ) ^ j := fun j => by
    calc Real.exp (-(2 * Real.pi * d.δ) * j) = Real.exp (-(2 * Real.pi * d.δ)) ^ j := by
          rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ (d.E1 : ℝ) ^ j := pow_le_pow_left₀ (Real.exp_pos _).le hE j
  have hN' : (1 : ℝ) ≤ 2 * Real.pi * d.δ * (d.N + 1) := by
    have : (1 : ℝ) ≤ 628 / 100 * d.δ * (d.N + 1) := by
      have h := (Rat.cast_le (K := ℝ)).mpr hN
      push_cast at h
      exact h
    have hN0 : (0 : ℝ) ≤ (d.N : ℝ) + 1 := by positivity
    nlinarith
  have hc0 : (0 : ℝ) ≤ d.claim := by
    have h := (Rat.cast_le (K := ℝ)).mpr hB1
    push_cast at h
    nlinarith
  have hdio : IsDiophantine (gammaStar : ℝ) 1 (Fin.snoc ![iota] 1 : Fin 2 → ℝ) := by
    rw [snoc_iota]; exact isDiophantine_omegaStar
  have key := smallDivisorSup_snoc_le (m := 1) (ω' := ![iota]) hdio hγ' zero_le_one hδ' hN'
    (fun k => pk (k 0)) (fun k => (lb (k 0) : ℝ))
    (fun k hk => by
      rw [frequencyDot_one]
      have h1 := (abs_dot_bounds (k 0)).1
      have h2 := (Rat.cast_le (K := ℝ)).mpr (hbox k hk).1
      push_cast at h2
      linarith)
    (fun k hk => by
      rw [frequencyDot_one]
      refine ⟨by exact_mod_cast (hbox k hk).2.1, (abs_dot_bounds (k 0)).2⟩)
    (fun j => (d.E1 : ℝ) ^ j) hEj (B := (d.claim : ℝ))
    (by
      rw [pow_one, div_le_iff₀ (by positivity)]
      have h := (Rat.cast_le (K := ℝ)).mpr hB1
      push_cast at h
      nlinarith)
    (fun k hk => by
      obtain ⟨-, hL, hEk, hEk'⟩ := hbox k hk
      have hL' : (0 : ℝ) < lb (k 0) := by exact_mod_cast hL
      have hEk2 : (d.E1 : ℝ) ^ (modeNat k + (pk (k 0)).natAbs) ≤
          d.claim * (628 / 100 * lb (k 0)) := by
        have h := (Rat.cast_le (K := ℝ)).mpr hEk
        push_cast at h
        exact h
      have hEk3 : (d.E1 : ℝ) ^ modeNat k ≤ d.claim * (314 / 100) := by
        have h := (Rat.cast_le (K := ℝ)).mpr hEk'
        push_cast at h
        exact h
      refine ⟨?_, ?_⟩
      · rw [div_le_iff₀ (by positivity)]
        have h2 : (628 / 100 : ℝ) * lb (k 0) ≤ 2 * Real.pi * lb (k 0) :=
          mul_le_mul_of_nonneg_right (by linarith) hL'.le
        nlinarith
      · rw [div_le_iff₀ Real.pi_pos]
        nlinarith)
  rw [← snoc_iota]
  refine key.trans (max_le le_rfl ?_)
  -- the tail
  have htail' : ((d.N : ℝ) + 1) * (d.E1 : ℝ) ^ (d.N + 1) ≤ d.claim * (628 / 100 * gammaStar) := by
    have h := (Rat.cast_le (K := ℝ)).mpr htail
    push_cast at h
    exact h
  have hexp : Real.exp (-(2 * Real.pi * d.δ) * ((d.N : ℝ) + 1)) ≤ (d.E1 : ℝ) ^ (d.N + 1) := by
    have := hEj (d.N + 1)
    push_cast at this
    exact this
  unfold sdSupTail
  rw [Real.rpow_one, div_le_iff₀ (by positivity)]
  have hN0 : (0 : ℝ) ≤ (d.N : ℝ) + 1 := by positivity
  calc ((d.N : ℝ) + 1) * Real.exp (-(2 * Real.pi * d.δ) * ((d.N : ℝ) + 1))
      ≤ ((d.N : ℝ) + 1) * (d.E1 : ℝ) ^ (d.N + 1) := mul_le_mul_of_nonneg_left hexp hN0
    _ ≤ d.claim * (628 / 100 * gammaStar) := htail'
    _ ≤ d.claim * (2 * Real.pi * gammaStar) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        nlinarith

end GInfData

/-- The claim at `δ₀`. -/
def gInfD0 : GInfData := { δ := 333 / 100000, N := 175, E1 := 9793 / 10000, claim := 551 / 100 }

/-- The claim at `ρ`. -/
def gInfRho : GInfData := { δ := 1 / 50, N := 25, E1 := 882 / 1000, claim := 154 / 100 }

theorem gInfD0_check : gInfD0.check = true := by decide +kernel

theorem gInfRho_check : gInfRho.check = true := by decide +kernel

/-- `Γ_∞(ω*, δ₀) ≤ 5.51`. -/
theorem gammaInf_d0 : smallDivisorSup omegaStar (333 / 100000) ≤ 551 / 100 := by
  have h := GInfData.sound gInfD0_check
  simp only [gInfD0] at h
  push_cast at h
  exact h

/-- `Γ_∞(ω*, ρ) ≤ 1.54`. -/
theorem gammaInf_rho : smallDivisorSup omegaStar (1 / 50) ≤ 154 / 100 := by
  have h := GInfData.sound gInfRho_check
  simp only [gInfRho] at h
  push_cast at h
  exact h

end KAM.Sharp2.Examples

end
