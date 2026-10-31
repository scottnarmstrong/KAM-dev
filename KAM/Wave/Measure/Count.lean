/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.ZetaSum
public import KAM.Wave.Measure.Family
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# W7: counting (blueprint `bpW:w7:count`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

(i) the finite set `lamPlusFin N ⊇ {l ∈ Λ⁺ : ⟨l⟩ ≤ N}` has at most `4 N²` elements; (ii) for
`K_ν ≥ 2^ν` each `k ≠ 0` occurs for at most `|k|` values of `ν`; (iii) is `tsum_lattice_le`.
We also prove `∑_{j < N} (j+1)^{-1/4} ≤ (4/3) N^{3/4}` used in the preparatory zones.
-/

@[expose] public noncomputable section

open Real Finsupp

namespace KAM.Wave

/-- Candidates for `Λ⁺` of size `≤ N`: `±e_a`, `±2e_a`, `±(e_a + e_b)`, `a, b < N`. -/
def lamPlusFin (N : ℕ) : Finset (ℕ →₀ ℤ) :=
  ((Finset.range N ×ˢ ({1, -1, 2, -2} : Finset ℤ)).image fun x => single x.1 x.2) ∪
  ((Finset.range N ×ˢ Finset.range N ×ˢ ({1, -1} : Finset ℤ)).image
    fun x => single x.1 x.2.2 + single x.2.1 x.2.2)

/-- (i) `#Λ⁺_{≤N} ≤ 4 N²`. -/
theorem card_lamPlusFin_le {N : ℕ} (hN : 2 ≤ N) : (lamPlusFin N).card ≤ 4 * N ^ 2 := by
  unfold lamPlusFin
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : ((Finset.range N ×ˢ ({1, -1, 2, -2} : Finset ℤ)).image
      fun x => single x.1 x.2).card ≤ 4 * N := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Finset.card_range]
    have : ({1, -1, 2, -2} : Finset ℤ).card ≤ 4 := Finset.card_le_four
    nlinarith
  have h2 : ((Finset.range N ×ˢ Finset.range N ×ˢ ({1, -1} : Finset ℤ)).image
      fun x => single x.1 x.2.2 + single x.2.1 x.2.2).card ≤ 2 * N ^ 2 := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Finset.card_product, Finset.card_range]
    have : ({1, -1} : Finset ℤ).card ≤ 2 := Finset.card_le_two
    nlinarith
  nlinarith

theorem mem_lamPlusFin {l : ℕ →₀ ℤ} (hl : IsLam l) (hnm : ¬ IsLamMinus l) {x : ℝ}
    (hx : japL l ≤ x) : l ∈ lamPlusFin ⌊x⌋₊ := by
  unfold lamPlusFin
  rw [Finset.mem_union]
  rcases lam_cases l hl with ⟨a, σ, hσ, rfl⟩ | ⟨a, b, σ, hab, hσ, rfl⟩ | hm
  · left
    rw [japL_single a hσ] at hx
    have h1 : (1 : ℝ) ≤ |(σ : ℝ)| := by rcases hσ with rfl | rfl | rfl | rfl <;> norm_num
    have h3 := normLab_pos a
    have h4 : ((a + 3 : ℕ) : ℝ) ≤ x := by
      unfold normLab at hx h3
      push_cast
      nlinarith [abs_nonneg (σ : ℝ)]
    have h5 := Nat.le_floor h4
    refine Finset.mem_image.2 ⟨(a, σ), ?_, rfl⟩
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨by omega, by rcases hσ with rfl | rfl | rfl | rfl <;> simp⟩
  · right
    rw [japL_pair hab.ne hσ] at hx
    have h4 : ((a + b + 6 : ℕ) : ℝ) ≤ x := by
      unfold normLab at hx
      push_cast; linarith
    have h5 := Nat.le_floor h4
    refine Finset.mem_image.2 ⟨(a, b, σ), ?_, rfl⟩
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨by omega, by omega, ?_⟩
    rcases hσ with rfl | rfl <;> simp
  · exact absurd hm hnm

theorem kAbs_eq_nat (k : Fin 2 → ℤ) : kAbs k = (((k 0).natAbs + (k 1).natAbs : ℕ) : ℝ) := by
  simp only [kAbs, Fin.sum_univ_two]
  push_cast
  have h : ∀ z : ℤ, ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := fun z => by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h, h]

/-- (ii) each `k ≠ 0` occurs for at most `|k|` values of `ν`. -/
theorem tsum_Kprev_le {Pi : Set (Fin 2 → ℝ)} {α : ℝ} (m : ℝ) (hm : 0 < m)
    (F : AdmissibleFamily m hm Pi α) {k : Fin 2 → ℤ} (hk : k ≠ 0) (c : ENNReal) :
    ∑' ν : ℕ, (if F.Kprev m hm ν < kAbs k then c else 0) ≤ ENNReal.ofReal (kAbs k) * c := by
  classical
  set n : ℕ := (k 0).natAbs + (k 1).natAbs with hn
  have hkn : kAbs k = n := kAbs_eq_nat k
  have hsub : ∀ ν ∉ Finset.range n, (if F.Kprev m hm ν < kAbs k then c else 0) = 0 := by
    intro ν hν
    simp only [ite_eq_right_iff]
    intro hlt
    exfalso
    apply hν
    rw [Finset.mem_range]
    rcases ν with _ | e
    · have : 0 < n := by
        have := one_le_kAbs hk
        rw [hkn] at this
        exact_mod_cast this
      exact this
    · have h1 : (2 : ℝ) ^ e ≤ F.K e := F.K_ge e
      have h2 : (e : ℝ) + 1 ≤ 2 ^ e := by
        have := Nat.lt_two_pow_self (n := e)
        exact_mod_cast this
      have h3 : F.Kprev m hm (e + 1) = F.K e := rfl
      rw [h3, hkn] at hlt
      have : ((e + 1 : ℕ) : ℝ) < n := by push_cast; linarith
      exact_mod_cast this
  rw [tsum_eq_sum hsub]
  calc ∑ ν ∈ Finset.range n, (if F.Kprev m hm ν < kAbs k then c else 0)
      ≤ ∑ ν ∈ Finset.range n, c := Finset.sum_le_sum fun ν _ => by split_ifs <;> simp
    _ = ENNReal.ofReal (kAbs k) * c := by
        rw [Finset.sum_const, Finset.card_range, hkn, nsmul_eq_mul, ENNReal.ofReal_natCast]

/-- `∑_{j<N} (j+1)^{-1/4} ≤ (4/3) N^{3/4}`. -/
theorem sum_rpow_neg_quarter_le (N : ℕ) :
    ∑ j ∈ Finset.range N, ((j : ℝ) + 1) ^ (-(1 / 4 : ℝ)) ≤ 4 / 3 * (N : ℝ) ^ (3 / 4 : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    -- Bernoulli: (N/(N+1))^{3/4} ≤ 1 - (3/4)/(N+1)
    have hb := rpow_one_add_le_one_add_mul_self (s := -1 / ((N : ℝ) + 1)) (p := 3 / 4)
      (by rw [le_div_iff₀ hN1]; linarith) (by norm_num) (by norm_num)
    have e1 : 1 + -1 / ((N : ℝ) + 1) = (N : ℝ) / ((N : ℝ) + 1) := by field_simp; ring
    rw [e1, Real.div_rpow (Nat.cast_nonneg N) hN1.le] at hb
    have hpos : 0 < ((N : ℝ) + 1) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hN1 _
    rw [div_le_iff₀ hpos] at hb
    have e2 : ((N : ℝ) + 1) ^ (3 / 4 : ℝ) = ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ (-(1 / 4 : ℝ)) := by
      rw [show (3 / 4 : ℝ) = 1 + (-(1 / 4 : ℝ)) by norm_num, Real.rpow_add hN1, Real.rpow_one]
    have hmain : (N : ℝ) ^ (3 / 4 : ℝ) ≤ ((N : ℝ) + 1) ^ (3 / 4 : ℝ) -
        3 / 4 * ((N : ℝ) + 1) ^ (-(1 / 4 : ℝ)) := by
      have := hb
      rw [e2] at this ⊢
      have hq := Real.rpow_pos_of_pos hN1 (-(1 / 4 : ℝ))
      have e3 : (1 + 3 / 4 * (-1 / ((N : ℝ) + 1))) * ((N + 1) * ((N : ℝ) + 1) ^ (-(1 / 4 : ℝ))) =
          ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ (-(1 / 4 : ℝ)) - 3 / 4 * ((N : ℝ) + 1) ^ (-(1 / 4 : ℝ)) := by
        field_simp; ring
      rw [e3] at this
      exact this
    push_cast
    nlinarith

end KAM.Wave

end
