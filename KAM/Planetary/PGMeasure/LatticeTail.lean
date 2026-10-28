/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Measure.Lattice

/-!
# Lattice sums: full sum and real-cutoff tail

Blueprint `bpP:p4:lattice-tail`: for `τ > n` the series `∑_{k ≠ 0} |k|₁^(-τ)` converges with sum at
most `S(n, τ) = 2 · 3^(n-1) (τ+1-n)/(τ-n)` (`stepP:p4:lt-a`, from `KAM.Measure.lattice_sum`), and
for every real cutoff `m ≥ 1` the tail `∑_{|k|₁ > m} |k|₁^(-τ-1)` is at most
`2 · 3^(n-1)/(τ+1-n) · (2/m)^(τ+1-n)` (`stepP:p4:lt-b`: shell count, then telescoping comparison).
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Planetary

variable {n : ℕ}

/-- The lattice weight `|k|₁^(-τ)`. -/
def latticeWeight (tau : ℝ) (k : Fin n → ℤ) : ℝ := (∑ i, |(k i : ℝ)|) ^ (-tau)

/-- Telescoping step: `q x^(-q-1) ≤ (x-1)^(-q) - x^(-q)` for `q ≥ 1`, `x > 1`. -/
theorem rpow_neg_succ_le {q : ℝ} (hq : 1 ≤ q) {y : ℝ} (hy : 0 < y) :
    q * (y + 1) ^ (-(q + 1)) ≤ y ^ (-q) - (y + 1) ^ (-q) := by
  have hy1 : 0 < y + 1 := by linarith
  have hb := one_add_mul_self_le_rpow_one_add (s := 1 / y) (by
    have : 0 < 1 / y := by positivity
    linarith) hq
  have hdiv : (1 + 1 / y) = (y + 1) / y := by field_simp
  rw [hdiv, Real.div_rpow hy1.le hy.le] at hb
  have hP : 0 < (y + 1) ^ q := Real.rpow_pos_of_pos hy1 _
  have hQ : 0 < y ^ q := Real.rpow_pos_of_pos hy _
  have e1 : (y + 1) ^ (-(q + 1)) = ((y + 1) ^ q)⁻¹ / (y + 1) := by
    rw [Real.rpow_neg hy1.le, Real.rpow_add hy1, Real.rpow_one, mul_comm, mul_inv,
      div_eq_mul_inv, mul_comm]
  rw [e1, Real.rpow_neg hy.le, Real.rpow_neg hy1.le]
  rw [le_div_iff₀ hQ] at hb
  generalize (y + 1) ^ q = P at *
  generalize y ^ q = Q at *
  have h1 : q * Q / (y + 1) ≤ q * Q / y :=
    div_le_div_of_nonneg_left (by positivity) hy (by linarith)
  have key : q * Q / (y + 1) ≤ P - Q := by
    have : q * Q / y = (1 + q * (1 / y)) * Q - Q := by field_simp; ring
    linarith
  have hid : Q⁻¹ - P⁻¹ - q * (P⁻¹ / (y + 1)) = (P - Q - q * Q / (y + 1)) / (P * Q) := by
    field_simp
  have : 0 ≤ (P - Q - q * Q / (y + 1)) / (P * Q) :=
    div_nonneg (by linarith) (by positivity)
  linarith

/-- Telescoping bound on the shell tail `∑_{J < r ≤ M} r^(-q-1) ≤ J^(-q)/q`. -/
theorem sum_Ioc_rpow_neg_le {q : ℝ} (hq : 1 ≤ q) {J : ℕ} (hJ : 1 ≤ J) (M : ℕ) :
    ∑ r ∈ Finset.Ioc J M, (r : ℝ) ^ (-(q + 1)) ≤ (J : ℝ) ^ (-q) / q := by
  have hq0 : 0 < q := by linarith
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  rcases le_total M J with hMJ | hMJ
  · rw [Finset.Ioc_eq_empty (not_lt.mpr hMJ), Finset.sum_empty]
    exact div_nonneg (Real.rpow_nonneg hJ0.le _) hq0.le
  have key : ∀ M : ℕ, J ≤ M → ∑ r ∈ Finset.Ioc J M, (r : ℝ) ^ (-(q + 1)) ≤
      ((J : ℝ) ^ (-q) - (M : ℝ) ^ (-q)) / q := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      rw [Finset.sum_Ioc_succ_top hM]
      have hM1 : (0 : ℝ) < M := by exact_mod_cast hJ.trans hM
      have h := rpow_neg_succ_le hq hM1
      push_cast
      have : (M + 1 : ℝ) ^ (-(q + 1)) ≤ ((M : ℝ) ^ (-q) - (M + 1 : ℝ) ^ (-q)) / q := by
        rw [le_div_iff₀ hq0]; linarith
      calc _ ≤ ((J : ℝ) ^ (-q) - (M : ℝ) ^ (-q)) / q +
            ((M : ℝ) ^ (-q) - (M + 1 : ℝ) ^ (-q)) / q := add_le_add ih this
        _ = _ := by ring
  refine (key M hMJ).trans ?_
  gcongr
  exact sub_le_self _ (Real.rpow_nonneg (Nat.cast_nonneg M) _)

/-- Finite-subset form of the tail bound. -/
theorem tail_finset_le (hn : 0 < n) {tau : ℝ} (ht : (n : ℝ) < tau) {m : ℝ} (hm : 1 ≤ m)
    (F : Finset (Fin n → ℤ)) (hF : ∀ k ∈ F, m < ∑ i, |(k i : ℝ)|) :
    ∑ k ∈ F, (∑ i, |(k i : ℝ)|) ^ (-tau - 1) ≤
      (2 * 3 ^ (n - 1) / (tau + 1 - n)) * (2 / m) ^ (tau + 1 - n) := by
  have hn1 : 1 ≤ n := hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hτ : (n : ℝ) - 1 < tau := by linarith
  set q : ℝ := tau + 1 - n with hqdef
  have hq : 1 ≤ q := by rw [hqdef]; linarith
  have hq0 : 0 < q := by linarith
  have hm0 : 0 < m := by linarith
  set J : ℕ := ⌊m⌋₊ with hJdef
  have hJ1 : 1 ≤ J := Nat.le_floor (by simpa using hm)
  have hJm : (J : ℝ) ≤ m := Nat.floor_le hm0.le
  have hmJ : m < J + 1 := Nat.lt_floor_add_one m
  set g : (Fin n → ℤ) → ℕ := fun k => (∑ i, |k i|).toNat with hg
  set M : ℕ := max J (F.sup g) with hM
  have hcast : ∀ k : Fin n → ℤ, ∑ i, |(k i : ℝ)| = ((∑ i, |k i| : ℤ) : ℝ) := fun k => by
    push_cast; rfl
  have hnn : ∀ k : Fin n → ℤ, 0 ≤ ∑ i, |k i| := fun k => Finset.sum_nonneg fun i _ => abs_nonneg _
  have hgk : ∀ k ∈ F, J < g k := fun k hk => by
    have h1 : (J : ℝ) < ((∑ i, |k i| : ℤ) : ℝ) := by rw [← hcast]; linarith [hF k hk]
    have h2 : (J : ℤ) < ∑ i, |k i| := by exact_mod_cast h1
    simp only [hg]; omega
  have hmaps : ∀ k ∈ F, g k ∈ Finset.Ioc J M := fun k hk =>
    Finset.mem_Ioc.mpr ⟨hgk k hk, (Finset.le_sup (f := g) hk).trans (le_max_right _ _)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ r ∈ Finset.Ioc J M,
      ∑ k ∈ F with g k = r, (∑ i, |(k i : ℝ)|) ^ (-tau - 1) ≤
        2 * 3 ^ (n - 1) * (r : ℝ) ^ (-(q + 1)) := fun r _ => by
    have := KAM.Measure.sum_sphere_le hn1 hτ r (F.filter fun k => g k = r) fun k hk => by
      have hk' := (Finset.mem_filter.mp hk).2
      have h0 := hnn k
      simp only [hg] at hk'
      omega
    refine this.trans (le_of_eq ?_)
    rw [hqdef]; congr 2; ring
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [← Finset.mul_sum]
  have h1 := sum_Ioc_rpow_neg_le hq hJ1 M
  have h2 : (J : ℝ) ^ (-q) ≤ (2 / m) ^ q := by
    have hJ2 : m / 2 ≤ J := by
      have : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
      linarith
    have : (2 / m) ^ q = (m / 2) ^ (-q) := by
      rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]; simp
    rw [this]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hJ2 (by linarith)
  calc 2 * 3 ^ (n - 1) * ∑ r ∈ Finset.Ioc J M, (r : ℝ) ^ (-(q + 1))
      ≤ 2 * 3 ^ (n - 1) * ((J : ℝ) ^ (-q) / q) := by gcongr
    _ ≤ 2 * 3 ^ (n - 1) * ((2 / m) ^ q / q) := by gcongr
    _ = _ := by ring

/-- Blueprint `bpP:p4:lattice-tail`. -/
theorem lattice_tail (hn : 0 < n) {tau : ℝ} (ht : (n:ℝ) < tau) :
    Summable (fun k : {k : Fin n → ℤ // k ≠ 0} => latticeWeight tau k.val) ∧
    (∑' k : {k : Fin n → ℤ // k ≠ 0}, latticeWeight tau k.val) ≤
      2*3^(n-1)*(tau+1-n)/(tau-n) ∧
    ∀ m : ℝ, 1 ≤ m →
      (∑' k : {k : Fin n → ℤ // m < ∑ i, |(k i : ℝ)|}, latticeWeight (tau+1) k.val) ≤
      (2*3^(n-1)/(tau+1-n))*(2/m)^(tau+1-n) := by
  have hn1 : 1 ≤ n := hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  obtain ⟨hs, hle⟩ := KAM.Measure.lattice_sum hn1 (τ := tau - 1) (by linarith)
  have hw : ∀ k : Fin n → ℤ, latticeWeight tau k = (∑ i, |(k i : ℝ)|) ^ (-(tau - 1) - 1) :=
    fun k => by unfold latticeWeight; congr 1; ring
  simp only [hw]
  refine ⟨hs, hle.trans (le_of_eq ?_), ?_⟩
  · have : tau - 1 + 2 - n = tau + 1 - n := by ring
    have h2 : tau - 1 + 1 - n = tau - n := by ring
    rw [this, h2, mul_div_assoc]
  · intro m hm
    have hnn : ∀ k : Fin n → ℤ, 0 ≤ latticeWeight (tau + 1) k := fun k =>
      Real.rpow_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) _
    have hq : 0 < tau + 1 - n := by linarith
    refine tsum_le_of_sum_le' (by positivity) fun F => ?_
    have := tail_finset_le hn ht hm (F.map (Function.Embedding.subtype _))
      (fun k hk => by
        obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hk
        exact x.2)
    rw [Finset.sum_map] at this
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold latticeWeight; congr 1; ring

/-- The lattice-sum constant `S(n, τ) = 2 · 3^(n-1) (τ+1-n)/(τ-n)`. -/
def latticeS (n : ℕ) (tau : ℝ) : ℝ := 2*3^(n-1)*(tau+1-n)/(tau-n)

end KAM.Planetary

end
