/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.SmallDiv.Defs
public import KAM.Strip.CohomologicalSumCert
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Ordered divisors (blueprint `bp:p2s2sd:shell`)

For `ω` `(γ, τ)`-Diophantine and `M ≥ 1`, `∑_{0<|k|₁≤M} |k·ω|⁻² ≤ A_τ γ⁻² M^{2τ}` with
`A_τ = 2^{2τ+1} ζ(2, 2^τ)` (`shellConst`). The values `k·ω > 0` of the modes with `|k|₁ ≤ M`
are `d`-separated with `d = γ(2M)^{-τ}` and at least `2^τ d`; `sum_inv_sq_sorted` bounds the sum of
inverse squares of such a finite set by `d⁻² ∑_j (2^τ + j)⁻²`.
-/

@[expose] public noncomputable section

namespace KAM.Sharp2

open KAM

/-- `(a + j)⁻²` is summable for `a ≥ 1`. -/
theorem summable_shell {a : ℝ} (ha : 1 ≤ a) : Summable fun j : ℕ => (a + j)⁻¹ ^ 2 := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
  refine h.of_nonneg_of_le (fun j => by positivity) fun j => ?_
  have : ((j + 1 : ℕ) : ℝ) ≤ a + j := by push_cast; linarith
  rw [inv_pow, one_div]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) this 2)

theorem shellConst_pos {τ : ℝ} (hτ : 0 ≤ τ) : 0 < shellConst τ := by
  have h1 : (1 : ℝ) ≤ 2 ^ τ := Real.one_le_rpow (by norm_num) hτ
  unfold shellConst
  have := (summable_shell h1).tsum_pos (fun j => by positivity) 0 (by positivity)
  positivity

/-- A finite set of reals with minimum `≥ x₀ > 0` and gaps `≥ d > 0`: sum of inverse squares. -/
theorem sum_inv_sq_sorted {x₀ d : ℝ} (hx₀ : 0 < x₀) (hd : 0 < d) (V : Finset ℝ)
    (hmin : ∀ x ∈ V, x₀ ≤ x) (hgap : ∀ x ∈ V, ∀ y ∈ V, x < y → d ≤ y - x) :
    (∑ x ∈ V, (x ^ 2)⁻¹ ≤ ∑ j ∈ Finset.range V.card, ((x₀ + j * d) ^ 2)⁻¹) ∧
      ∀ a ∈ V, (∀ x ∈ V, x ≤ a) → x₀ + ((V.card : ℝ) - 1) * d ≤ a := by
  induction V using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl _ (hlt a h)
    obtain ⟨ih1, ih2⟩ := ih (fun x hx => hmin x (Finset.mem_insert_of_mem hx))
      (fun x hx y hy => hgap x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy))
    have hlow : x₀ + (s.card : ℝ) * d ≤ a := by
      rcases s.eq_empty_or_nonempty with he | hne
      · subst he; simpa using hmin a (Finset.mem_insert_self _ _)
      · obtain ⟨b, hb, hbmax⟩ := s.exists_max_image id hne
        have h1 := ih2 b hb fun x hx => hbmax x hx
        have h2 := hgap b (Finset.mem_insert_of_mem hb) a (Finset.mem_insert_self _ _) (hlt b hb)
        linarith
    have hcard : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem has
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_insert has, hcard, Finset.sum_range_succ]
      have hpos : 0 < x₀ + (s.card : ℝ) * d := by positivity
      have : (a ^ 2)⁻¹ ≤ ((x₀ + (s.card : ℝ) * d) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hlow 2)
      linarith
    · intro b hb hbmax
      have hba : b = a := by
        have hab : a ≤ b := hbmax a (Finset.mem_insert_self _ _)
        rcases Finset.mem_insert.mp hb with h | hbs
        · exact h
        · exact absurd hab (not_le.mpr (hlt b hbs))
      subst hba
      rw [hcard]
      push_cast
      linarith

section Shell

variable {n : ℕ} {ω : Fin n → ℝ} {γ τ : ℝ}

theorem frequencyDot_sub (ω : Fin n → ℝ) (k k' : Fin n → ℤ) :
    Diophantine.frequencyDot ω (k' - k) =
      Diophantine.frequencyDot ω k' - Diophantine.frequencyDot ω k := by
  unfold Diophantine.frequencyDot
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp [sub_mul]

theorem frequencyDot_neg (ω : Fin n → ℝ) (k : Fin n → ℤ) :
    Diophantine.frequencyDot ω (-k) = -Diophantine.frequencyDot ω k := by
  unfold Diophantine.frequencyDot
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp

theorem modeNat_neg (k : Fin n → ℤ) : modeNat (-k) = modeNat k := by
  simp [modeNat]

theorem modeNat_sub_le (k k' : Fin n → ℤ) : modeNat (k' - k) ≤ modeNat k' + modeNat k := by
  unfold modeNat
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => by simpa using Int.natAbs_sub_le (k' j) (k j)

/-- The Diophantine lower bound in terms of `modeNat`. -/
theorem dio_modeNat (hω : IsDiophantine γ τ ω) {k : Fin n → ℤ} (hk : k ≠ 0) :
    γ / (modeNat k : ℝ) ^ τ ≤ |Diophantine.frequencyDot ω k| := by
  have := hω k hk
  have e : (∑ i, |(k i : ℝ)|) = (modeNat k : ℝ) := by
    simp [modeNat, Nat.cast_sum]
  rw [e] at this
  exact this

theorem dio_le_of_modeNat (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    {k : Fin n → ℤ} (hk : k ≠ 0) {M : ℝ} (hM : (modeNat k : ℝ) ≤ M) :
    γ / M ^ τ ≤ |Diophantine.frequencyDot ω k| := by
  refine le_trans ?_ (dio_modeNat hω hk)
  have hpos : (0 : ℝ) < modeNat k := by
    refine Nat.cast_pos.mpr (Nat.pos_of_ne_zero fun h => hk (funext fun j => ?_))
    have h' : ∑ j, (k j).natAbs = 0 := h
    have := Finset.sum_eq_zero_iff.mp h' j (Finset.mem_univ j)
    simpa using Int.natAbs_eq_zero.mp this
  exact div_le_div_of_nonneg_left hγ.le (by positivity) (Real.rpow_le_rpow hpos.le hM hτ)

/-- **Ordered divisors**: `∑_{0<|k|₁≤M} |k·ω|⁻² ≤ A_τ γ⁻² M^{2τ}`. -/
theorem shell_sum_le (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) {M : ℕ} (hM : 1 ≤ M) :
    ∑ k ∈ modeBox n M, ((Diophantine.frequencyDot ω k) ^ 2)⁻¹ ≤
      shellConst τ * (γ ^ 2)⁻¹ * (M : ℝ) ^ (2 * τ) := by
  classical
  set f : (Fin n → ℤ) → ℝ := Diophantine.frequencyDot ω with hf
  set K := modeBox n M with hK
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hnz : ∀ k ∈ K, k ≠ 0 := fun k hk => (mem_modeBox.mp hk).1
  have hf0 : ∀ k ∈ K, f k ≠ 0 := fun k hk => hω.condition.nonresonant hγ k (hnz k hk)
  set P := K.filter (fun k => 0 < f k) with hP
  set Q := K.filter (fun k => ¬ 0 < f k) with hQ
  have hsplit : ∑ k ∈ K, ((f k) ^ 2)⁻¹ = ∑ k ∈ P, ((f k) ^ 2)⁻¹ + ∑ k ∈ Q, ((f k) ^ 2)⁻¹ :=
    (Finset.sum_filter_add_sum_filter_not K (fun k => 0 < f k) _).symm
  have hQP : ∑ k ∈ Q, ((f k) ^ 2)⁻¹ = ∑ k ∈ P, ((f k) ^ 2)⁻¹ := by
    refine Finset.sum_nbij' (fun k => -k) (fun k => -k) ?_ ?_ (fun k _ => neg_neg k)
      (fun k _ => neg_neg k) ?_
    · intro k hk
      obtain ⟨hkK, hkn⟩ := Finset.mem_filter.mp hk
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · obtain ⟨h1, h2⟩ := mem_modeBox.mp hkK
        exact mem_modeBox.mpr ⟨neg_ne_zero.mpr h1, by rwa [modeNat_neg]⟩
      · have := hf0 k hkK
        simp only [hf, frequencyDot_neg]
        exact neg_pos.mpr (lt_of_le_of_ne (not_lt.mp hkn) this)
    · intro k hk
      obtain ⟨hkK, hkp⟩ := Finset.mem_filter.mp hk
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · obtain ⟨h1, h2⟩ := mem_modeBox.mp hkK
        exact mem_modeBox.mpr ⟨neg_ne_zero.mpr h1, by rwa [modeNat_neg]⟩
      · simp only [hf, frequencyDot_neg]
        exact not_lt.mpr (neg_nonpos.mpr hkp.le)
    · intro k _
      simp only [hf, frequencyDot_neg, neg_sq]
  set d : ℝ := γ / (2 * (M : ℝ)) ^ τ with hd
  have h2Mτ : (2 * (M : ℝ)) ^ τ = 2 ^ τ * (M : ℝ) ^ τ := Real.mul_rpow (by norm_num) hM0.le
  have hMτ : 0 < (M : ℝ) ^ τ := Real.rpow_pos_of_pos hM0 τ
  have h2τ : 0 < (2 : ℝ) ^ τ := Real.rpow_pos_of_pos (by norm_num) τ
  have hd0 : 0 < d := by rw [hd]; positivity
  set x₀ : ℝ := γ / (M : ℝ) ^ τ with hx₀
  have hx₀0 : 0 < x₀ := by rw [hx₀]; positivity
  have hx₀d : x₀ = 2 ^ τ * d := by
    rw [hx₀, hd, h2Mτ]; field_simp
  -- the positive values
  have hinj : Set.InjOn f P := by
    intro k hk k' hk' hkk
    by_contra hne
    have hne' : k' - k ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have := hω.condition.nonresonant hγ _ hne'
    apply this
    rw [hf] at hkk
    simp only [frequencyDot_sub]
    rw [hkk, sub_self]
  have hsumV : ∑ k ∈ P, ((f k) ^ 2)⁻¹ = ∑ x ∈ P.image f, (x ^ 2)⁻¹ :=
    by rw [Finset.sum_image hinj]
  have hmem : ∀ k ∈ P, k ≠ 0 ∧ modeNat k ≤ M ∧ 0 < f k := fun k hk => by
    obtain ⟨hkK, hkp⟩ := Finset.mem_filter.mp hk
    obtain ⟨h1, h2⟩ := mem_modeBox.mp hkK
    exact ⟨h1, h2, hkp⟩
  have hmin : ∀ x ∈ P.image f, x₀ ≤ x := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨h1, h2, h3⟩ := hmem k hk
    have := dio_le_of_modeNat hω hγ hτ h1 (M := M) (by exact_mod_cast h2)
    rwa [abs_of_pos h3] at this
  have hgap : ∀ x ∈ P.image f, ∀ y ∈ P.image f, x < y → d ≤ y - x := by
    intro x hx y hy hxy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨h1, h2, h3⟩ := hmem k hk
    obtain ⟨h1', h2', h3'⟩ := hmem k' hk'
    have hne : k' - k ≠ 0 := by
      intro h0
      have : k' = k := sub_eq_zero.mp h0
      subst this
      exact lt_irrefl _ hxy
    have hmn : (modeNat (k' - k) : ℝ) ≤ 2 * M := by
      have := modeNat_sub_le k k'
      have : (modeNat (k' - k) : ℝ) ≤ (modeNat k' : ℝ) + modeNat k := by exact_mod_cast this
      have h2r : (modeNat k : ℝ) ≤ M := by exact_mod_cast h2
      have h2r' : (modeNat k' : ℝ) ≤ M := by exact_mod_cast h2'
      linarith
    have hb := dio_le_of_modeNat hω hγ hτ hne hmn
    have hxy' : Diophantine.frequencyDot ω k < Diophantine.frequencyDot ω k' := hxy
    rw [frequencyDot_sub, abs_of_pos (sub_pos.mpr hxy')] at hb
    exact hb
  obtain ⟨hsort, -⟩ := sum_inv_sq_sorted hx₀0 hd0 (P.image f) hmin hgap
  have hsum_ζ : ∑ x ∈ P.image f, (x ^ 2)⁻¹ ≤ (d ^ 2)⁻¹ * ∑' j : ℕ, ((2 : ℝ) ^ τ + j)⁻¹ ^ 2 := by
    refine hsort.trans ?_
    have hs := summable_shell (a := (2 : ℝ) ^ τ) (Real.one_le_rpow (by norm_num) hτ)
    have hterm : ∀ j : ℕ, ((x₀ + j * d) ^ 2)⁻¹ = (d ^ 2)⁻¹ * ((2 : ℝ) ^ τ + j)⁻¹ ^ 2 := by
      intro j
      rw [hx₀d, show 2 ^ τ * d + j * d = d * (2 ^ τ + j) by ring, mul_pow, mul_inv, inv_pow]
    simp only [hterm]
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (hs.sum_le_tsum _ fun j _ => by positivity)
  rw [hsplit, hQP, ← two_mul]
  refine (mul_le_mul_of_nonneg_left (hsumV ▸ hsum_ζ) (by norm_num)).trans (le_of_eq ?_)
  unfold shellConst
  have e2 : (2 : ℝ) ^ (2 * τ) = ((2 : ℝ) ^ τ) ^ 2 := by
    rw [show 2 * τ = τ * 2 by ring, Real.rpow_mul (by norm_num), Real.rpow_two]
  have eM : (M : ℝ) ^ (2 * τ) = ((M : ℝ) ^ τ) ^ 2 := by
    rw [show 2 * τ = τ * 2 by ring, Real.rpow_mul hM0.le, Real.rpow_two]
  have e3 : (2 : ℝ) ^ (2 * τ + 1) = ((2 : ℝ) ^ τ) ^ 2 * 2 := by
    rw [Real.rpow_add (by norm_num), e2, Real.rpow_one]
  have hd2 : (d ^ 2)⁻¹ = ((2 : ℝ) ^ τ) ^ 2 * ((M : ℝ) ^ τ) ^ 2 * (γ ^ 2)⁻¹ := by
    rw [hd, h2Mτ]
    field_simp
  rw [hd2, e3, eM]
  ring

end Shell

end KAM.Sharp2

end
