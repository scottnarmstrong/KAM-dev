/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Normal.Nondegeneracy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# W7: integer data, weights and the case split of `Λ` (blueprint `bpW:w7:indexdef`)

Normal modes are indexed by `ν : ℕ`, the Dirichlet mode `j = ν + 3` (`normLab ν`); `l : ℕ →₀ ℤ` is
the finitely supported integer vector on the normal modes. We define `⟨l⟩` (`japL`), `|l|_δ`
(`absWt`), the modified weight `ŵ` (`hatW`), `Λ` (`IsLam`), `Λ⁻` (`IsLamMinus`) and `A_k`
(`kAk`), and prove that every `l ∈ Λ` is `±e_a`, `±2e_a`, `±(e_a + e_b)` or `±(e_i - e_j)`.
-/

@[expose] public noncomputable section

open Finsupp

namespace KAM.Wave

/-- The Dirichlet label `j = ν + 3` of the normal mode `ν`. -/
def normLab (ν : ℕ) : ℝ := (ν : ℝ) + 3

theorem normLab_ge (ν : ℕ) : 3 ≤ normLab ν := by unfold normLab; have := (Nat.cast_nonneg ν : (0:ℝ)
                                                   ≤ ν); linarith

theorem normLab_pos (ν : ℕ) : 0 < normLab ν := by linarith [normLab_ge ν]

/-- `⟨l⟩ = max (1, |∑_j j l_j|)` (blueprint `bpW:w7:indexdef` (iii)). -/
def japL (l : ℕ →₀ ℤ) : ℝ := max 1 |linF l normLab|

/-- `|l|_δ = ∑_j |l_j| j^δ` (blueprint `bpW:w7:indexdef` (iv)). -/
def absWt (l : ℕ →₀ ℤ) (δ : ℝ) : ℝ := l.sum fun ν v => |(v : ℝ)| * normLab ν ^ δ

/-- `Λ = {l : 1 ≤ |l| ≤ 2}`. -/
def IsLam (l : ℕ →₀ ℤ) : Prop := 1 ≤ l1Norm l ∧ l1Norm l ≤ 2

/-- `Λ⁻`: `l = ±(e_i - e_j)`, `i > j` (blueprint `bpW:w7:indexdef` (ii)). -/
def IsLamMinus (l : ℕ →₀ ℤ) : Prop :=
  ∃ (i j : ℕ) (σ : ℤ), j < i ∧ (σ = 1 ∨ σ = -1) ∧ l = single i σ + single j (-σ)

/-- The modified weight `ŵ(l)` (blueprint `bpW:w7:indexdef` (vii)), with weight exponent `β = 1/4`:
`(i - j) j^{-1/4}` on `Λ⁻` (`j` the smaller label) and `⟨l⟩` otherwise. -/
def hatW (l : ℕ →₀ ℤ) : ℝ :=
  open scoped Classical in
  if IsLamMinus l then japL l * normLab (sInf {ν | l ν ≠ 0}) ^ (-(1 / 4 : ℝ)) else japL l

/-- `|k| = |k₁| + |k₂|` as a real number. -/
def kAbs (k : Fin 2 → ℤ) : ℝ := ∑ i, |(k i : ℝ)|

/-- `A_k = 1 + |k|^τ`, `τ = 24`. -/
def kAk (k : Fin 2 → ℤ) : ℝ := 1 + kAbs k ^ 24

theorem kAbs_nonneg (k : Fin 2 → ℤ) : 0 ≤ kAbs k := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem kAbs_neg (k : Fin 2 → ℤ) : kAbs (-k) = kAbs k := by simp [kAbs]

theorem one_le_kAbs {k : Fin 2 → ℤ} (hk : k ≠ 0) : 1 ≤ kAbs k := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h; push Not at h; exact hk (funext h)
  have h1 : (1 : ℝ) ≤ |(k i : ℝ)| := by
    have : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
    exact_mod_cast this
  calc (1 : ℝ) ≤ |(k i : ℝ)| := h1
    _ ≤ kAbs k := Finset.single_le_sum (f := fun i => |(k i : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)

theorem kAk_pos (k : Fin 2 → ℤ) : 1 ≤ kAk k := by
  unfold kAk; have := kAbs_nonneg k; have : 0 ≤ kAbs k ^ 24 := by positivity
  linarith

theorem kAk_neg (k : Fin 2 → ℤ) : kAk (-k) = kAk k := by simp [kAk, kAbs_neg]

theorem kAbs_pow_le_kAk (k : Fin 2 → ℤ) : kAbs k ^ 24 ≤ kAk k := by unfold kAk; linarith

theorem kAk_le {k : Fin 2 → ℤ} (hk : k ≠ 0) : kAk k ≤ 2 * kAbs k ^ 24 := by
  have := one_le_kAbs hk
  have : 1 ≤ kAbs k ^ 24 := one_le_pow₀ this
  unfold kAk; linarith

/-! ### Evaluation on pairs -/

theorem sum_single_pair {a b : ℕ} (hab : a ≠ b) (σ τ : ℤ) (g : ℕ → ℤ → ℝ)
    (hg : ∀ x, g x 0 = 0) : (single a σ + single b τ).sum g = g a σ + g b τ := by
  rw [Finsupp.sum_of_support_subset (s := {a, b})]
  · rw [Finset.sum_pair hab]
    simp [hab, Ne.symm hab]
  · intro x hx
    have := Finsupp.support_add hx
    simp only [Finset.mem_union] at this
    rcases this with h | h
    · have := Finsupp.support_single_subset h; simp at this; simp [this]
    · have := Finsupp.support_single_subset h; simp at this; simp [this]
  · intro x _; exact hg x

theorem linF_pair {a b : ℕ} (hab : a ≠ b) (σ τ : ℤ) (f : ℕ → ℝ) :
    linF (single a σ + single b τ) f = σ * f a + τ * f b := by
  unfold linF
  rw [sum_single_pair hab σ τ (fun j v => (v : ℝ) * f j) (by simp)]

theorem absWt_single (a : ℕ) (σ : ℤ) (δ : ℝ) :
    absWt (single a σ) δ = |(σ : ℝ)| * normLab a ^ δ := by
  unfold absWt
  rw [Finsupp.sum_single_index]; simp

theorem absWt_pair {a b : ℕ} (hab : a ≠ b) (σ τ : ℤ) (δ : ℝ) :
    absWt (single a σ + single b τ) δ =
      |(σ : ℝ)| * normLab a ^ δ + |(τ : ℝ)| * normLab b ^ δ := by
  unfold absWt
  rw [sum_single_pair hab σ τ (fun ν v => |(v : ℝ)| * normLab ν ^ δ) (by simp)]

/-! ### The case split -/

theorem lam_cases (l : ℕ →₀ ℤ) (h : IsLam l) :
    (∃ (a : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1 ∨ σ = 2 ∨ σ = -2) ∧ l = single a σ) ∨
    (∃ (a b : ℕ) (σ : ℤ), a < b ∧ (σ = 1 ∨ σ = -1) ∧ l = single a σ + single b σ) ∨
    IsLamMinus l := by
  obtain ⟨h1, h2⟩ := h
  have : l1Norm l = 1 ∨ l1Norm l = 2 := by omega
  rcases this with h | h
  · obtain ⟨ν, σ, hσ, rfl⟩ := l1Norm_one l h
    exact Or.inl ⟨ν, σ, by omega, rfl⟩
  · rcases l1Norm_two l h with ⟨ν, σ, hσ, rfl⟩ | ⟨a, b, σ, τ, hab, hσ, hτ, rfl⟩
    · exact Or.inl ⟨ν, σ, by omega, rfl⟩
    · right
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl
      · rcases lt_or_gt_of_ne hab with hlt | hgt
        · exact Or.inl ⟨a, b, 1, hlt, Or.inl rfl, rfl⟩
        · refine Or.inl ⟨b, a, 1, hgt, Or.inl rfl, add_comm _ _⟩
      · -- e_a - e_b
        right
        rcases lt_or_gt_of_ne hab with hlt | hgt
        · exact ⟨b, a, -1, hlt, Or.inr rfl, by simp [add_comm]⟩
        · exact ⟨a, b, 1, hgt, Or.inl rfl, rfl⟩
      · right
        rcases lt_or_gt_of_ne hab with hlt | hgt
        · exact ⟨b, a, 1, hlt, Or.inl rfl, by simp [add_comm]⟩
        · exact ⟨a, b, -1, hgt, Or.inr rfl, by simp⟩
      · rcases lt_or_gt_of_ne hab with hlt | hgt
        · exact Or.inl ⟨a, b, -1, hlt, Or.inr rfl, rfl⟩
        · refine Or.inl ⟨b, a, -1, hgt, Or.inr rfl, add_comm _ _⟩

theorem IsLam_of_minus {l : ℕ →₀ ℤ} (h : IsLamMinus l) : IsLam l := by
  obtain ⟨i, j, σ, hji, hσ, rfl⟩ := h
  have hne : j ≠ i := hji.ne
  have : l1Norm (single i σ + single j (-σ)) = 2 := by
    rw [l1Norm_eq_sum]
    have : (single i σ + single j (-σ)).support ⊆ {i, j} := by
      intro x hx
      have := Finsupp.support_add hx
      simp only [Finset.mem_union] at this
      rcases this with h | h
      · have := Finsupp.support_single_subset h; simp at this; simp [this]
      · have := Finsupp.support_single_subset h; simp at this; simp [this]
    rw [Finset.sum_subset this]
    · rw [Finset.sum_pair hji.ne']
      rcases hσ with rfl | rfl <;> simp [hne, Ne.symm hne]
    · intro x hx hx'
      have : (single i σ + single j (-σ)) x = 0 := by
        by_contra hc; exact hx' (Finsupp.mem_support_iff.2 hc)
      rw [this]; rfl
  unfold IsLam; omega

theorem linF_minus {i j : ℕ} (hji : j < i) (σ : ℤ) (f : ℕ → ℝ) :
    linF (single i σ + single j (-σ)) f = σ * (f i - f j) := by
  rw [linF_pair hji.ne']; push_cast; ring

theorem japL_minus {i j : ℕ} (hji : j < i) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    japL (single i σ + single j (-σ)) = (i : ℝ) - j := by
  unfold japL
  rw [linF_minus hji]
  have h1 : (1 : ℝ) ≤ (i : ℝ) - j := by
    have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hji
    linarith
  have hpos : 0 ≤ normLab i - normLab j := by
    unfold normLab; have : (j : ℝ) ≤ i := by exact_mod_cast hji.le
    linarith
  have : |(σ : ℝ) * (normLab i - normLab j)| = (i : ℝ) - j := by
    rw [abs_mul]
    have h3 : |(σ : ℝ)| = 1 := by rcases hσ with rfl | rfl <;> simp
    rw [h3, one_mul, abs_of_nonneg hpos]; unfold normLab; ring
  rw [this]; exact max_eq_right h1

theorem japL_single (a : ℕ) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1 ∨ σ = 2 ∨ σ = -2) :
    japL (single a σ) = |(σ : ℝ)| * normLab a := by
  unfold japL
  rw [show linF (single a σ) normLab = σ * normLab a from by
    unfold linF; rw [Finsupp.sum_single_index]; simp]
  rw [abs_mul]
  have h3 := normLab_ge a
  rw [abs_of_pos (normLab_pos a)]
  refine max_eq_right ?_
  rcases hσ with rfl | rfl | rfl | rfl <;> simp <;> linarith

theorem japL_pair {a b : ℕ} (hab : a ≠ b) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    japL (single a σ + single b σ) = normLab a + normLab b := by
  unfold japL
  rw [linF_pair hab]
  have h3 := normLab_ge a
  have h4 := normLab_ge b
  have : |(σ : ℝ) * normLab a + (σ : ℝ) * normLab b| = normLab a + normLab b := by
    rw [← mul_add, abs_mul]
    have h3 : |(σ : ℝ)| = 1 := by rcases hσ with rfl | rfl <;> simp
    rw [h3, one_mul, abs_of_nonneg (by linarith)]
  rw [this]; exact max_eq_right (by linarith)

theorem japL_ge_one (l : ℕ →₀ ℤ) : 1 ≤ japL l := le_max_left _ _

theorem japL_neg (l : ℕ →₀ ℤ) : japL (-l) = japL l := by
  unfold japL
  have : linF (-l) normLab = - linF l normLab := by
    unfold linF; simp [Finsupp.sum_neg_index]
  rw [this, abs_neg]

theorem isLamMinus_neg {l : ℕ →₀ ℤ} (h : IsLamMinus l) : IsLamMinus (-l) := by
  obtain ⟨i, j, σ, hji, hσ, rfl⟩ := h
  refine ⟨i, j, -σ, hji, ?_, ?_⟩
  · rcases hσ with rfl | rfl <;> simp
  · rw [neg_add, ← Finsupp.single_neg, ← Finsupp.single_neg]

theorem isLamMinus_neg_iff (l : ℕ →₀ ℤ) : IsLamMinus (-l) ↔ IsLamMinus l :=
  ⟨fun h => by simpa using isLamMinus_neg h, isLamMinus_neg⟩

theorem sInf_minus {i j : ℕ} (hji : j < i) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    sInf {ν | (single i σ + single j (-σ)) ν ≠ 0} = j := by
  have hj : j ∈ {ν | (single i σ + single j (-σ)) ν ≠ 0} := by
    simp only [Set.mem_ofPred_eq]
    rcases hσ with rfl | rfl <;> simp [hji.ne']
  refine le_antisymm (Nat.sInf_le hj) (le_csInf ⟨j, hj⟩ ?_)
  intro x hx
  simp only [Set.mem_ofPred_eq, Finsupp.add_apply, Finsupp.single_apply] at hx
  by_contra hlt
  push Not at hlt
  have h1 : i ≠ x := by omega
  have h2 : j ≠ x := by omega
  simp [h1, h2] at hx

theorem hatW_minus {i j : ℕ} (hji : j < i) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    hatW (single i σ + single j (-σ)) = ((i : ℝ) - j) * normLab j ^ (-(1 / 4 : ℝ)) := by
  unfold hatW
  have hm : IsLamMinus (single i σ + single j (-σ)) := ⟨i, j, σ, hji, hσ, rfl⟩
  simp only [hm, ↓reduceIte]
  rw [japL_minus hji hσ, sInf_minus hji σ hσ]

theorem hatW_neg (l : ℕ →₀ ℤ) : hatW (-l) = hatW l := by
  unfold hatW
  by_cases h : IsLamMinus l
  · have h' := isLamMinus_neg h
    have hs : {ν | (-l) ν ≠ 0} = {ν | l ν ≠ 0} := by ext ν; simp
    simp only [h, h', ↓reduceIte]
    rw [hs, japL_neg]
  · have h' : ¬ IsLamMinus (-l) := by rwa [isLamMinus_neg_iff]
    simp only [h, h', ↓reduceIte]
    rw [japL_neg]

theorem hatW_le_japL (l : ℕ →₀ ℤ) : hatW l ≤ japL l := by
  unfold hatW
  split_ifs
  · have h3 := normLab_ge (sInf {ν | l ν ≠ 0})
    have : normLab (sInf {ν | l ν ≠ 0}) ^ (-(1 / 4 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have := japL_ge_one l
    nlinarith
  · exact le_rfl

theorem hatW_pos (l : ℕ →₀ ℤ) : 0 < hatW l := by
  unfold hatW
  split_ifs
  · have := japL_ge_one l
    have := Real.rpow_pos_of_pos (normLab_pos (sInf {ν | l ν ≠ 0})) (-(1 / 4 : ℝ))
    positivity
  · exact lt_of_lt_of_le one_pos (japL_ge_one l)

theorem normLab_rpow_le_one {ν : ℕ} {δ : ℝ} (hδ : δ ≤ 0) : normLab ν ^ δ ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith [normLab_ge ν]) hδ

theorem absWt_nonneg (l : ℕ →₀ ℤ) (δ : ℝ) : 0 ≤ absWt l δ :=
  Finset.sum_nonneg fun ν _ => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (normLab_pos ν).le _)

theorem absWt_le_two {l : ℕ →₀ ℤ} (h : IsLam l) {δ : ℝ} (hδ : δ ≤ 0) : absWt l δ ≤ 2 := by
  rcases lam_cases l h with ⟨a, σ, hσ, rfl⟩ | ⟨a, b, σ, hab, hσ, rfl⟩ | hm
  · rw [absWt_single]
    have := normLab_rpow_le_one (ν := a) hδ
    have := Real.rpow_nonneg (normLab_pos a).le δ
    have h2 : |(σ : ℝ)| ≤ 2 := by rcases hσ with rfl | rfl | rfl | rfl <;> norm_num
    nlinarith [abs_nonneg (σ : ℝ)]
  · rw [absWt_pair hab.ne]
    have h1 := normLab_rpow_le_one (ν := a) hδ
    have h2 := normLab_rpow_le_one (ν := b) hδ
    have := Real.rpow_nonneg (normLab_pos a).le δ
    have := Real.rpow_nonneg (normLab_pos b).le δ
    have h3 : |(σ : ℝ)| = 1 := by rcases hσ with rfl | rfl <;> simp
    rw [h3]; linarith
  · obtain ⟨i, j, σ, hji, hσ, rfl⟩ := hm
    rw [absWt_pair hji.ne']
    have h1 := normLab_rpow_le_one (ν := i) hδ
    have h2 := normLab_rpow_le_one (ν := j) hδ
    have h3 : |(σ : ℝ)| = 1 := by rcases hσ with rfl | rfl <;> simp
    have h4 : |((-σ : ℤ) : ℝ)| = 1 := by rcases hσ with rfl | rfl <;> simp
    rw [h3, h4]; linarith

/-- `|l|_{-1} ≤ |l|_{-1/2}`. -/
theorem absWt_mono {l : ℕ →₀ ℤ} {δ δ' : ℝ} (h : δ ≤ δ') : absWt l δ ≤ absWt l δ' := by
  unfold absWt
  refine Finset.sum_le_sum fun ν _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [normLab_ge ν]) h

theorem absWt_minus {i j : ℕ} (hji : j < i) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (δ : ℝ) :
    absWt (single i σ + single j (-σ)) δ = normLab i ^ δ + normLab j ^ δ := by
  rw [absWt_pair hji.ne']
  have h3 : |(σ : ℝ)| = 1 := by rcases hσ with rfl | rfl <;> simp
  have h4 : |((-σ : ℤ) : ℝ)| = 1 := by rcases hσ with rfl | rfl <;> simp
  rw [h3, h4]; ring

end KAM.Wave

end
