/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Fourier.ExpSums
public import KAM.Measure.Lattice
public import KAM.Planetary.MaximalStep.Constants

/-!
# Fourier cutoff: the constant and the lattice tail (P11A-C1)

Steps `stepP:p11a:fc-const`, `fc-count`, `fc-poly` and `fc-assemble` of `bpP:p11a:fourier-cutoff`:
`1 ≤ p11C n`, and the tail estimate
`∑_{|k|₁ > T} e^{-2π d |k|₁} ≤ p11Error n T d`, from `KAM.Measure.lattice_count` (through
`card_l1Sphere_le`) and `KAM.Fourier.exp_sums`.
-/

@[expose] public noncomputable section
open Set Filter Finset
open scoped BigOperators Topology
namespace KAM.Planetary

/-- `stepP:p11a:fc-const`: `c_N ≥ 1`. -/
theorem p11C_ge_one {n : ℕ} (hn : 1 ≤ n) : 1 ≤ p11C n := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hp : Real.pi < 3.15 := Real.pi_lt_d2
  have hp0 : 3 < Real.pi := Real.pi_gt_three
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hep : Real.exp 1 * Real.pi < 9 := by nlinarith
  have hpos : 0 < Real.exp 1 * Real.pi := by positivity
  have hf : 1 ≤ 2 * (1 + 1 / Real.pi) := by
    have : 0 < 1 / Real.pi := by positivity
    linarith
  unfold p11C
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · interval_cases n
    · simpa using hf
    · have ha : (1 : ℝ) / 2 ≤ 3 * ((2 : ℕ) : ℝ) / (Real.exp 1 * Real.pi) := by
        rw [le_div_iff₀ hpos]; push_cast; nlinarith
      have : 0 < 1 / Real.pi := by positivity
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at ha ⊢
      nlinarith
  · have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast h3
    have ha : 1 ≤ 3 * (n : ℝ) / (Real.exp 1 * Real.pi) := by
      rw [le_div_iff₀ hpos]; linarith
    have := one_le_pow₀ (n := n - 1) ha
    nlinarith

/-- Geometric tail `∑_{m ≥ j₀} q^m = q^{j₀}/(1-q)`. -/
private theorem tsum_geom_tail {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) (j0 : ℕ) :
    Summable (fun m : ℕ => if j0 ≤ m then q ^ m else 0) ∧
      ∑' m : ℕ, (if j0 ≤ m then q ^ m else 0) = q ^ j0 / (1 - q) := by
  have hg := summable_geometric_of_lt_one h0 h1
  have hs : Summable (fun m : ℕ => if j0 ≤ m then q ^ m else 0) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hg
    · split_ifs <;> positivity
    · split_ifs
      · exact le_rfl
      · positivity
  refine ⟨hs, ?_⟩
  have h := hs.sum_add_tsum_nat_add j0
  have hz : ∑ i ∈ Finset.range j0, (if j0 ≤ i then q ^ i else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by simp [not_le.mpr (Finset.mem_range.mp hi)]
  rw [hz, zero_add] at h
  rw [← h]
  have : ∀ i : ℕ, (if j0 ≤ i + j0 then q ^ (i + j0) else 0) = q ^ j0 * q ^ i := fun i => by
    rw [if_pos (by omega), pow_add, mul_comm]
  simp only [this]
  rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1, div_eq_mul_inv]

/-- Real-variable form of `stepP:p11a:fc-assemble`. -/
private theorem assemble_ineq {n : ℕ} (hn : 1 ≤ n) {d : ℝ} (hd : 0 < d) :
    2 * 3 ^ (n - 1) * (((n - 1 : ℕ) : ℝ) / (Real.exp 1 * (Real.pi * d))) ^ (n - 1) *
        (1 + 1 / (Real.pi * d)) ≤ p11C n * (1 + (d ^ n)⁻¹) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set w : ℝ := d⁻¹ with hw
  have hw0 : 0 < w := inv_pos.mpr hd
  have hdw : (d ^ n)⁻¹ = w ^ n := by rw [hw, inv_pow]
  have h1 : 1 / (Real.pi * d) = w / Real.pi := by rw [hw]; field_simp
  have hkey : w ^ (n - 1) * (1 + w / Real.pi) ≤ (1 + 1 / Real.pi) * (1 + w ^ n) := by
    have hn1 : w ^ n = w ^ (n - 1) * w := by
      rw [← pow_succ]; congr 1; omega
    have hA : w ^ (n - 1) ≤ 1 + w ^ n := by
      rcases le_total w 1 with h | h
      · have := pow_le_one₀ hw0.le h (n := n - 1)
        have : 0 ≤ w ^ n := by positivity
        linarith
      · have := pow_le_pow_right₀ h (Nat.sub_le n 1)
        have : w ^ (n - 1) ≤ w ^ n := by
          rw [hn1]; nlinarith [pow_pos hw0 (n - 1)]
        linarith
    have hB : w ^ (n - 1) * (w / Real.pi) = w ^ n / Real.pi := by rw [hn1]; ring
    have hC : w ^ n / Real.pi ≤ (1 / Real.pi) * (1 + w ^ n) := by
      rw [div_eq_mul_inv, one_div]
      have : 0 ≤ (Real.pi)⁻¹ := by positivity
      nlinarith [pow_pos hw0 n]
    calc w ^ (n - 1) * (1 + w / Real.pi) = w ^ (n - 1) + w ^ (n - 1) * (w / Real.pi) := by ring
      _ ≤ (1 + w ^ n) + (1 / Real.pi) * (1 + w ^ n) := by rw [hB]; linarith
      _ = _ := by ring
  have hlhs : 2 * 3 ^ (n - 1) * (((n - 1 : ℕ) : ℝ) / (Real.exp 1 * (Real.pi * d))) ^ (n - 1) =
      2 * (3 * ((n - 1 : ℕ) : ℝ) / (Real.exp 1 * Real.pi)) ^ (n - 1) * w ^ (n - 1) := by
    have e1 : (3 : ℝ) ^ (n - 1) * (((n - 1 : ℕ) : ℝ) / (Real.exp 1 * (Real.pi * d))) ^ (n - 1) =
        (3 * ((n - 1 : ℕ) : ℝ) / (Real.exp 1 * Real.pi)) ^ (n - 1) * w ^ (n - 1) := by
      rw [← mul_pow, ← mul_pow]
      congr 1
      rw [hw]; field_simp
    calc 2 * 3 ^ (n - 1) * (((n - 1 : ℕ) : ℝ) / (Real.exp 1 * (Real.pi * d))) ^ (n - 1)
        = 2 * ((3 : ℝ) ^ (n - 1) *
          (((n - 1 : ℕ) : ℝ) / (Real.exp 1 * (Real.pi * d))) ^ (n - 1)) := by ring
      _ = _ := by rw [e1]; ring
  have hbase : (3 * ((n - 1 : ℕ) : ℝ) / (Real.exp 1 * Real.pi)) ^ (n - 1) ≤
      (3 * (n : ℝ) / (Real.exp 1 * Real.pi)) ^ (n - 1) := by
    gcongr
    exact Nat.sub_le n 1
  have hP : 0 ≤ (3 * ((n - 1 : ℕ) : ℝ) / (Real.exp 1 * Real.pi)) ^ (n - 1) := by positivity
  rw [hlhs, h1, hdw]
  unfold p11C
  have hQ : 0 ≤ w ^ (n - 1) * (1 + w / Real.pi) := by positivity
  calc 2 * (3 * ((n - 1 : ℕ) : ℝ) / (Real.exp 1 * Real.pi)) ^ (n - 1) * w ^ (n - 1) *
        (1 + w / Real.pi)
      = 2 * (3 * ((n - 1 : ℕ) : ℝ) / (Real.exp 1 * Real.pi)) ^ (n - 1) *
        (w ^ (n - 1) * (1 + w / Real.pi)) := by ring
    _ ≤ 2 * (3 * (n : ℝ) / (Real.exp 1 * Real.pi)) ^ (n - 1) *
        ((1 + 1 / Real.pi) * (1 + w ^ n)) := by gcongr
    _ = _ := by ring

/-- The lattice sum over shells: the `ℓ¹` tail `∑_{|k|₁>T} e^{-x|k|₁}` is bounded by the shell
count times `e^{-x m}`. -/
private theorem sum_tail_finset_le {n : ℕ} (hn : 1 ≤ n) {T d : ℝ} (hT : 0 ≤ T) (hd : 0 < d)
    (F : Finset (Fin n → ℤ)) :
    ∑ k ∈ F, (if T < KAM.Fourier.modeSize k then
        Real.exp (-(2 * Real.pi * d) * KAM.Fourier.modeSize k) else 0) ≤ p11Error n T d := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set K : ℝ := (((n - 1 : ℕ) : ℝ) / (Real.exp 1 * (Real.pi * d))) ^ (n - 1) with hK
  set q : ℝ := Real.exp (-(Real.pi * d)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith [mul_pos hpi hd])
  set g : (Fin n → ℤ) → ℕ := fun k => (∑ i, |k i|).toNat with hg
  have hms : ∀ k, KAM.Fourier.modeSize k = (g k : ℝ) := fun k => by
    have h0 : 0 ≤ ∑ i, |k i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have : ((g k : ℕ) : ℤ) = ∑ i, |k i| := Int.toNat_of_nonneg h0
    unfold KAM.Fourier.modeSize
    have h2 : (((g k : ℕ) : ℤ) : ℝ) = ((∑ i, |k i| : ℤ) : ℝ) := by rw [this]
    simp only [Int.cast_natCast, Int.cast_sum, Int.cast_abs] at h2
    exact h2.symm
  set M : ℕ := F.sup g with hM
  have hmaps : ∀ k ∈ F, g k ∈ Finset.range (M + 1) := fun k hk =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := g) hk))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  set j0 : ℕ := ⌊T⌋₊ + 1 with hj0
  have hTj : ∀ m : ℕ, T < m ↔ j0 ≤ m := fun m => by
    rw [hj0, Nat.succ_le_iff, Nat.floor_lt hT]
  -- fibrewise bound
  have hfib : ∀ m ∈ Finset.range (M + 1),
      ∑ k ∈ F with g k = m, (if T < KAM.Fourier.modeSize k then
        Real.exp (-(2 * Real.pi * d) * KAM.Fourier.modeSize k) else 0) ≤
        (2 * 3 ^ (n - 1) * K) * (if j0 ≤ m then q ^ m else 0) := by
    intro m _
    by_cases hm : T < (m : ℝ)
    · have hj : j0 ≤ m := (hTj m).mp hm
      have hm1 : 1 ≤ m := by
        have : 0 < (m : ℝ) := lt_of_le_of_lt hT hm
        exact_mod_cast this
      have hterm : ∀ k ∈ F.filter (fun k => g k = m),
          (if T < KAM.Fourier.modeSize k then
            Real.exp (-(2 * Real.pi * d) * KAM.Fourier.modeSize k) else 0) =
            q ^ m * q ^ m := by
        intro k hk
        have hgk := (Finset.mem_filter.mp hk).2
        rw [hms k, hgk, if_pos hm, hq, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1; ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, if_pos hj]
      have hcard : (F.filter (fun k => g k = m)).card ≤ 2 * 3 ^ (n - 1) * m ^ (n - 1) := by
        refine le_trans (Finset.card_le_card ?_) (KAM.Measure.card_l1Sphere_le hn hm1)
        intro k hk
        have hgk := (Finset.mem_filter.mp hk).2
        refine KAM.Measure.mem_l1Sphere.mpr ?_
        have h0 : 0 ≤ ∑ i, |k i| := Finset.sum_nonneg fun i _ => abs_nonneg _
        simp only [hg] at hgk
        omega
      have hpoly : (m : ℝ) ^ (n - 1) * q ^ m ≤ K := by
        have h := (KAM.Fourier.exp_sums n).1 (m : ℝ) (Real.pi * d) ((n - 1 : ℕ) : ℝ)
          (Nat.cast_nonneg _) (by positivity) (Nat.cast_nonneg _)
        rw [Real.rpow_natCast, Real.rpow_natCast] at h
        have hqm : q ^ m = Real.exp (-(Real.pi * d) * m) := by
          rw [hq, ← Real.exp_nat_mul]; congr 1; ring
        rw [hqm]; exact h
      have hc : ((F.filter (fun k => g k = m)).card : ℝ) ≤ 2 * 3 ^ (n - 1) * (m : ℝ) ^ (n - 1) := by
        exact_mod_cast hcard
      calc ((F.filter (fun k => g k = m)).card : ℝ) * (q ^ m * q ^ m)
          ≤ (2 * 3 ^ (n - 1) * (m : ℝ) ^ (n - 1)) * (q ^ m * q ^ m) := by gcongr
        _ = (2 * 3 ^ (n - 1)) * ((m : ℝ) ^ (n - 1) * q ^ m) * q ^ m := by ring
        _ ≤ (2 * 3 ^ (n - 1)) * K * q ^ m := by gcongr
    · have hz : ∀ k ∈ F.filter (fun k => g k = m),
          (if T < KAM.Fourier.modeSize k then
            Real.exp (-(2 * Real.pi * d) * KAM.Fourier.modeSize k) else 0) = 0 := by
        intro k hk
        have hgk := (Finset.mem_filter.mp hk).2
        rw [hms k, hgk, if_neg hm]
      rw [Finset.sum_eq_zero hz, if_neg (fun h => hm ((hTj m).mpr h))]
      simp
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [← Finset.mul_sum]
  obtain ⟨hs, ht⟩ := tsum_geom_tail hq0 hq1 j0
  have hsum : ∑ m ∈ Finset.range (M + 1), (if j0 ≤ m then q ^ m else 0) ≤ q ^ j0 / (1 - q) := by
    rw [← ht]
    exact hs.sum_le_tsum _ (fun m _ => by split_ifs <;> positivity)
  have hqj : q ^ j0 ≤ Real.exp (-(Real.pi * T * d)) := by
    rw [hq, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have : T < j0 := by
      have := Nat.lt_floor_add_one T
      simpa [hj0] using this
    nlinarith [mul_pos hpi hd]
  have h1q : 1 / (1 - q) ≤ 1 + 1 / (Real.pi * d) := by
    have hx : 0 < Real.pi * d := by positivity
    have h1 : 0 < 1 - q := by linarith
    rw [div_le_iff₀ h1]
    have hexp : q * (1 + Real.pi * d) ≤ 1 := by
      have := Real.add_one_le_exp (Real.pi * d)
      calc q * (1 + Real.pi * d) ≤ q * Real.exp (Real.pi * d) := by
            gcongr; linarith
        _ = 1 := by rw [hq, ← Real.exp_add]; simp
    have : (1 + 1 / (Real.pi * d)) * (1 - q) = 1 + 1 / (Real.pi * d) - q * (1 + 1 / (Real.pi * d)) -
        q * 0 := by ring
    have h2 : 1 ≤ (1 + 1 / (Real.pi * d)) * (1 - q) := by
      have hxx : 1 / (Real.pi * d) * (q * (1 + Real.pi * d)) ≤ 1 / (Real.pi * d) := by
        have : 0 ≤ 1 / (Real.pi * d) := by positivity
        nlinarith
      have e : (1 + 1 / (Real.pi * d)) * (1 - q) =
          1 + 1 / (Real.pi * d) - 1 / (Real.pi * d) * (q * (1 + Real.pi * d)) - q * 0 := by
        field_simp; ring
      linarith
    exact h2
  have hApos : 0 ≤ 2 * 3 ^ (n - 1) * K := by positivity
  have hass := assemble_ineq hn hd
  have hE : 0 ≤ Real.exp (-(Real.pi * T * d)) := (Real.exp_pos _).le
  have hexpeq : Real.exp (-Real.pi * T * d) = Real.exp (-(Real.pi * T * d)) := by ring_nf
  unfold p11Error
  have hqj' : q ^ j0 / (1 - q) ≤ Real.exp (-(Real.pi * T * d)) * (1 + 1 / (Real.pi * d)) := by
    have h1 : 0 < 1 - q := by linarith
    calc q ^ j0 / (1 - q) = q ^ j0 * (1 / (1 - q)) := by ring
      _ ≤ Real.exp (-(Real.pi * T * d)) * (1 + 1 / (Real.pi * d)) := by gcongr
  calc 2 * 3 ^ (n - 1) * K * ∑ m ∈ Finset.range (M + 1), (if j0 ≤ m then q ^ m else 0)
      ≤ 2 * 3 ^ (n - 1) * K * (Real.exp (-(Real.pi * T * d)) * (1 + 1 / (Real.pi * d))) := by
        gcongr; exact hsum.trans hqj'
    _ = (2 * 3 ^ (n - 1) * K * (1 + 1 / (Real.pi * d))) * Real.exp (-(Real.pi * T * d)) := by ring
    _ ≤ (p11C n * (1 + (d ^ n)⁻¹)) * Real.exp (-(Real.pi * T * d)) := by
        gcongr
    _ = _ := by rw [hexpeq]

/-- `stepP:p11a:fc-assemble`: the tail of the lattice sum is at most `p11Error n T d`. -/
theorem p11_tail_le {n : ℕ} (hn : 1 ≤ n) {T d : ℝ} (hT : 0 ≤ T) (hd : 0 < d) :
    ∑' k : Fin n → ℤ, (if T < KAM.Fourier.modeSize k then
        Real.exp (-(2 * Real.pi * d) * KAM.Fourier.modeSize k) else 0) ≤ p11Error n T d := by
  refine tsum_le_of_sum_le' ?_ (sum_tail_finset_le hn hT hd)
  unfold p11Error p11C
  have := p11C_ge_one hn
  unfold p11C at this
  positivity

end KAM.Planetary
