/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.DivisorCore
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# The divisor lower bound (blueprint-W `bpW:w3:divisor`)

Package W3-DIVISOR-F, blueprint label `bpW:w3:divisor`.

`birk_divisor_bound`: for `x ∈ (ℤ∖0)⁴` satisfying the selection rule
(`∃ ε ∈ {±1}⁴, Σ ε_t |x_t| = 0`) and
not paired, `|δ_x| ≥ m/(27 (n² + m)^{3/2})`, `n = min |x_t|`. `birk_divisor_bound_tan`: if
`x ∈ 𝒯`, `𝔤_x ≠ 0` and `x` not paired then `|δ_x| ≥ δ_*(m) = m/(27 (4+m)^{3/2})` (`birkDeltaStar`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m)

theorem birkDivisor_vec4 (q0 q1 q2 q3 : BirkIdx) :
    birkDivisor m hm ![q0, q1, q2, q3] = birkLam m hm q0 + birkLam m hm q1 + birkLam m hm q2 +
      birkLam m hm q3 := by
  simp [birkDivisor, Fin.sum_univ_four]

include hm

/-- The sorted case, all sixteen sign patterns. -/
theorem birk_divisor_sorted (q0 q1 q2 q3 : BirkIdx) (ha : 1 ≤ (q0.2 : ℕ))
    (h01 : (q0.2 : ℕ) ≤ q1.2) (h12 : (q1.2 : ℕ) ≤ q2.2) (h23 : (q2.2 : ℕ) ≤ q3.2)
    (hsel : (q3.2 : ℕ) = q0.2 + q1.2 + q2.2 ∨ (q3.2 : ℕ) + q0.2 = q1.2 + q2.2)
    (hnp : ¬ birkPaired ![q0, q1, q2, q3]) :
    m / (27 * birkL m (q0.2 : ℕ) ^ 3) ≤ |birkDivisor m hm ![q0, q1, q2, q3]| := by
  obtain ⟨b0, a⟩ := q0
  obtain ⟨b1, b⟩ := q1
  obtain ⟨b2, c⟩ := q2
  obtain ⟨b3, d⟩ := q3
  simp only at ha h01 h12 h23 hsel ⊢
  have hb : 1 ≤ (b : ℕ) := ha.trans h01
  have hc : 1 ≤ (c : ℕ) := hb.trans h12
  have hd : 1 ≤ (d : ℕ) := hc.trans h23
  have lab := birkL_mono m hm h01
  have lbc := birkL_mono m hm h12
  have lcd := birkL_mono m hm h23
  have hC0 := birkDiv_C0 m hm ha hb hc hd
  have hC1 : m / (27 * birkL m a ^ 3) ≤ birkL m a + birkL m b + birkL m c - birkL m d :=
    birkDiv_C1 m hm ha h01 h12 h23 (by omega)
  have hC3 := birkDiv_C3 m hm ha h01 h12 h23
  have hC2 := birkDiv_C2 m hm ha h01 h12 h23
  have hC1i := birkDiv_C1i (d := d) m hm ha h01 h12 h23
  have hC1ii := birkDiv_C1ii (d := d) m hm ha h01 h12
  have hβ : 0 ≤ m / (27 * birkL m a ^ 3) := by have := birkL_pos m hm a; positivity
  rw [birkDivisor_vec4]
  have hC1' : ¬ ((a : ℕ) = b ∧ (c : ℕ) = d) →
      m / (27 * birkL m a ^ 3) ≤ birkL m a + birkL m d - birkL m b - birkL m c := fun hne => by
    rcases hsel with h | h
    · exact hC1ii h
    · exact hC1i h hne
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    simp only [birkLam, lam_eq_birkL, Bool.false_eq_true, ite_true, ite_false, one_mul, neg_mul,
      Bool.true_eq_false]
  · exact le_abs.2 (Or.inr (by linarith))
  · exact le_abs.2 (Or.inr (by linarith))
  · exact le_abs.2 (Or.inr (by linarith))
  · have hn : ¬ ((a : ℕ) = b ∧ (b : ℕ) = c ∧ (c : ℕ) = d) := fun ⟨h1, h2, h3⟩ => hnp (by
      have e1 := PNat.eq h1; have e2 := PNat.eq h2; have e3 := PNat.eq h3
      subst e1 e2 e3
      simp [birkPaired, birkPosAbs, birkNegAbs, Fin.sum_univ_four])
    exact le_abs.2 (Or.inl (by linarith [hC3 hn]))
  · exact le_abs.2 (Or.inr (by linarith))
  · have hn : ¬ ((a : ℕ) = b ∧ (c : ℕ) = d) := fun ⟨h1, h3⟩ => hnp (by
      have e1 := PNat.eq h1; have e3 := PNat.eq h3
      subst e1 e3
      simp [birkPaired, birkPosAbs, birkNegAbs, Fin.sum_univ_four])
    exact le_abs.2 (Or.inl (by linarith [hC2 hn]))
  · have hn : ¬ ((a : ℕ) = b ∧ (c : ℕ) = d) := fun ⟨h1, h3⟩ => hnp (by
      have e1 := PNat.eq h1; have e3 := PNat.eq h3
      subst e1 e3
      simp [birkPaired, birkPosAbs, birkNegAbs, Fin.sum_univ_four])
    exact le_abs.2 (Or.inr (by linarith [hC1' hn]))
  · exact le_abs.2 (Or.inl (by linarith))
  · exact le_abs.2 (Or.inr (by linarith))
  · have hn : ¬ ((a : ℕ) = b ∧ (c : ℕ) = d) := fun ⟨h1, h3⟩ => hnp (by
      have e1 := PNat.eq h1; have e3 := PNat.eq h3
      subst e1 e3
      simp [birkPaired, birkPosAbs, birkNegAbs, Fin.sum_univ_four])
    exact le_abs.2 (Or.inl (by linarith [hC1' hn]))
  · have hn : ¬ ((a : ℕ) = b ∧ (c : ℕ) = d) := fun ⟨h1, h3⟩ => hnp (by
      have e1 := PNat.eq h1; have e3 := PNat.eq h3
      subst e1 e3
      simp [birkPaired, birkPosAbs, birkNegAbs, Fin.sum_univ_four])
    exact le_abs.2 (Or.inr (by linarith [hC2 hn]))
  · exact le_abs.2 (Or.inl (by linarith))
  · have hn : ¬ ((a : ℕ) = b ∧ (b : ℕ) = c ∧ (c : ℕ) = d) := fun ⟨h1, h2, h3⟩ => hnp (by
      have e1 := PNat.eq h1; have e2 := PNat.eq h2; have e3 := PNat.eq h3
      subst e1 e2 e3
      simp [birkPaired, birkPosAbs, birkNegAbs, Fin.sum_univ_four])
    exact le_abs.2 (Or.inr (by linarith [hC3 hn]))
  · exact le_abs.2 (Or.inl (by linarith))
  · exact le_abs.2 (Or.inl (by linarith))
  · exact le_abs.2 (Or.inl (by linarith))

theorem birkL_pow_three (k : ℕ) : birkL m k ^ 3 = (((k : ℕ) : ℝ) ^ 2 + m) ^ (3 / 2 : ℝ) := by
  have h : (0 : ℝ) ≤ ((k : ℕ) : ℝ) ^ 2 + m := by have := sq_nonneg (k : ℝ); linarith
  unfold birkL
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h]
  norm_num

/-- (`bpW:w3:divisor`) `|δ_x| ≥ m / (27 (n² + m)^{3/2})` for `x` satisfying the selection rule and
not
paired, `n = min |x_t|` (attained at `t₀`). -/
theorem birk_divisor_bound (x : Fin 4 → BirkIdx)
    (hsel : ∃ ε : Fin 4 → Bool,
      ∑ t, (if ε t then (1 : ℤ) else -1) * (((x t).2 : ℕ) : ℤ) = 0)
    (hnp : ¬ birkPaired x) (t0 : Fin 4) (ht0 : ∀ t, (x t0).2 ≤ (x t).2) :
    m / (27 * ((((x t0).2 : ℕ) : ℝ) ^ 2 + m) ^ (3 / 2 : ℝ)) ≤ |birkDivisor m hm x| := by
  set σ := Tuple.sort (fun t => (((x t).2 : ℕ+) : ℕ)) with hσ
  have hmono : Monotone ((fun t => (((x t).2 : ℕ+) : ℕ)) ∘ σ) :=
    Tuple.monotone_sort (fun t => (((x t).2 : ℕ+) : ℕ))
  set y : Fin 4 → BirkIdx := fun i => x (σ i) with hy
  have h01 : (((y 0).2 : ℕ+) : ℕ) ≤ ((y 1).2 : ℕ+) := hmono (by decide)
  have h12 : (((y 1).2 : ℕ+) : ℕ) ≤ ((y 2).2 : ℕ+) := hmono (by decide)
  have h23 : (((y 2).2 : ℕ+) : ℕ) ≤ ((y 3).2 : ℕ+) := hmono (by decide)
  have hyvec : y = ![y 0, y 1, y 2, y 3] := by funext i; fin_cases i <;> rfl
  have hdiv : birkDivisor m hm y = birkDivisor m hm x :=
    Equiv.sum_comp σ (fun t => birkLam m hm (x t))
  have hpair : ¬ birkPaired y := fun h => hnp ((birkPaired_perm σ x).1 h)
  have hpos : ∀ i, 1 ≤ (((y i).2 : ℕ+) : ℕ) := fun i => (y i).2.pos
  -- selection rule for the sorted tuple
  have hsel' : (((y 3).2 : ℕ+) : ℕ) = ((y 0).2 : ℕ+) + ((y 1).2 : ℕ+) + ((y 2).2 : ℕ+) ∨
      (((y 3).2 : ℕ+) : ℕ) + ((y 0).2 : ℕ+) = ((y 1).2 : ℕ+) + ((y 2).2 : ℕ+) := by
    obtain ⟨ε, hε⟩ := hsel
    have hε' : ∑ i, (if ε (σ i) then (1 : ℤ) else -1) * ((((y i).2 : ℕ+) : ℕ) : ℤ) = 0 := by
      rw [← hε]
      exact Equiv.sum_comp σ (fun t => (if ε t then (1 : ℤ) else -1) * (((x t).2 : ℕ) : ℤ))
    simp only [Fin.sum_univ_four] at hε'
    have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2; have p3 := hpos 3
    generalize (((y 0).2 : ℕ+) : ℕ) = a at *
    generalize (((y 1).2 : ℕ+) : ℕ) = b at *
    generalize (((y 2).2 : ℕ+) : ℕ) = c at *
    generalize (((y 3).2 : ℕ+) : ℕ) = d at *
    cases ε (σ 0) <;> cases ε (σ 1) <;> cases ε (σ 2) <;> cases ε (σ 3) <;> simp at hε' <;> omega
  have key := birk_divisor_sorted m hm (y 0) (y 1) (y 2) (y 3) (hpos 0) h01 h12 h23 hsel'
    (by rw [← hyvec]; exact hpair)
  rw [← hyvec, hdiv] at key
  -- identification of the minimum
  have hmin : (((y 0).2 : ℕ+) : ℕ) = (((x t0).2 : ℕ+) : ℕ) := by
    apply le_antisymm
    · have : (((x t0).2 : ℕ+) : ℕ) = (((y (σ.symm t0)).2 : ℕ+) : ℕ) := by simp [hy]
      rw [this]
      exact hmono (Fin.zero_le _)
    · exact ht0 (σ 0)
  rw [hmin, birkL_pow_three m hm] at key
  exact key

omit hm in
/-- `δ_*(m) = m / (27 (4 + m)^{3/2})`. -/
def birkDeltaStar (m : ℝ) : ℝ := m / (27 * (4 + m) ^ (3 / 2 : ℝ))

theorem quarticSel_exists_eps (x : Fin 4 → BirkIdx)
    (h : QuarticSel ((x 0).2 : ℕ) ((x 1).2 : ℕ) ((x 2).2 : ℕ) ((x 3).2 : ℕ)) :
    ∃ ε : Fin 4 → Bool, ∑ t, (if ε t then (1 : ℤ) else -1) * (((x t).2 : ℕ) : ℤ) = 0 := by
  unfold QuarticSel at h
  rcases h with h | h | h | h | h | h | h
  · exact ⟨![true, false, false, true], by simp [Fin.sum_univ_four]; omega⟩
  · exact ⟨![true, false, true, false], by simp [Fin.sum_univ_four]; omega⟩
  · exact ⟨![true, true, false, false], by simp [Fin.sum_univ_four]; omega⟩
  · exact ⟨![true, false, false, false], by simp [Fin.sum_univ_four]; omega⟩
  · exact ⟨![false, true, false, false], by simp [Fin.sum_univ_four]; omega⟩
  · exact ⟨![false, false, true, false], by simp [Fin.sum_univ_four]; omega⟩
  · exact ⟨![false, false, false, true], by simp [Fin.sum_univ_four]; omega⟩

/-- (`bpW:w3:divisor`, consequence) For `x ∈ 𝒯`, `𝔤_x ≠ 0`, `x` not paired: `|δ_x| ≥ δ_*(m)`. -/
theorem birk_divisor_bound_tan (x : Fin 4 → BirkIdx) (hT : x ∈ birkTanSet)
    (hg : birkG m hm x ≠ 0) (hnp : ¬ birkPaired x) : birkDeltaStar m ≤ |birkDivisor m hm x| := by
  have hg' : sineQuarticCoeff (x 0).2 (x 1).2 (x 2).2 (x 3).2 ≠ 0 := by
    intro h; apply hg; unfold birkG waveTriCoef waveQuartic; rw [h]; simp
  have hsel := quarticSel_exists_eps m hm x (quarticSel_of_quarticCoeff_ne_zero _ _ _ _ hg')
  obtain ⟨t0, -, ht0⟩ := Finset.exists_min_image Finset.univ (fun t => ((x t).2 : ℕ+)) ⟨0,
      Finset.mem_univ _⟩
  have key := birk_divisor_bound m hm x hsel hnp t0 (fun t => ht0 t (Finset.mem_univ t))
  refine le_trans ?_ key
  obtain ⟨t1, ht1⟩ := hT
  have hn : (((x t0).2 : ℕ+) : ℕ) ≤ 2 := (PNat.coe_le_coe _ _).2 (ht0 t1 (Finset.mem_univ _))
      |>.trans ht1
  have hn' : ((((x t0).2 : ℕ+) : ℕ) : ℝ) ^ 2 ≤ 4 := by
    have : ((((x t0).2 : ℕ+) : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hn
    nlinarith [Nat.cast_nonneg (α := ℝ) (((x t0).2 : ℕ+) : ℕ)]
  unfold birkDeltaStar
  have h0 : (0 : ℝ) ≤ ((((x t0).2 : ℕ+) : ℕ) : ℝ) ^ 2 + m := by positivity
  have hr := Real.rpow_le_rpow h0 (by linarith : ((((x t0).2 : ℕ+) : ℕ) : ℝ) ^ 2 + m ≤ 4 + m)
    (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hp : 0 < (((((x t0).2 : ℕ+) : ℕ) : ℝ) ^ 2 + m) ^ (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  exact div_le_div_of_nonneg_left hm.le (by positivity) (by gcongr)

end KAM.Wave

end
