/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Normal.QuarticCoeff
public import KAM.Wave.Normal.AngleAvg
public import KAM.Frozen.Wave.Defs.Lam

/-!
# The averaged quartic part `⟨G⟩` in the actions (blueprint `bpW:w0n:AB`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

For `N` modes, actions `I : Fin N → ℝ≥0` and angles `φ ∈ [0, 2π]ᴺ`, put `q_j = √(2 I_j) cos φ_j`
(so `z_j = √I_j e^{-iφ_j}`, `q_j = (z_j + z̄_j)/√2`) and
`G(q) = ¼ ∑_{ijkl} g_{ijkl} q̂_i q̂_j q̂_k q̂_l`, `q̂_j = q_j / √λ_j`
(blueprint Lemma `bpW:w0n:gradient`). `KAM.Wave.avgG` is the average of `G` over the angles. The
main result `KAM.Wave.avgG_eq` is the closed form `bpW:w0n:avgG`,

  `⟨G⟩ = 3/(16π) · (4 (∑_j I_j/λ_j)² - ∑_j I_j²/λ_j²)`,

and `KAM.Wave.partial_avgG_eq` is Theorem `bpW:w0n:AB` for `J = {1, 2}`: the part of `⟨G⟩`
containing at least one tangential action equals `½⟨AI, I⟩ + ⟨BI, Z⟩` with the corrected
coefficients `A_ii = 9/(8πλ_i²)`, `A_12 = A_21 = 3/(2πλ_1λ_2)`, `B_ji = 3/(2πλ_jλ_i)`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

/-- The mode `j + 1 ∈ ℕ+` indexed by `j : Fin N`. -/
def modeIdx {N : ℕ} (j : Fin N) : ℕ+ := ⟨j.val + 1, Nat.succ_pos _⟩

theorem modeIdx_injective {N : ℕ} : Function.Injective (modeIdx (N := N)) := by
  intro i j h
  have := congrArg (fun x : ℕ+ => (x : ℕ)) h
  simp only [modeIdx, PNat.mk_coe] at this
  exact Fin.ext (by omega)

/-- `g_{iikk}` for the modes `i, k`. -/
theorem sineQuarticCoeff_pair_val (a b : ℕ+) :
    sineQuarticCoeff a a b b = 1 / π + (if a = b then 1 / (2 * π) else 0) := by
  by_cases hab : a = b
  · subst hab
    rw [sineQuarticCoeff_diag]
    simp
    field_simp
    norm_num
  · rw [sineQuarticCoeff_diag_pair a b hab]
    simp [hab]

theorem sineQuarticCoeff_pair_val_b (a b : ℕ+) :
    sineQuarticCoeff a b a b = 1 / π + (if a = b then 1 / (2 * π) else 0) := by
  rw [← sineQuarticCoeff_pair_val, sineQuarticCoeff_eq, sineQuarticCoeff_eq]
  have := a.pos
  have := b.pos
  split_ifs <;> first | (exfalso; omega) | ring

theorem sineQuarticCoeff_pair_val_c (a b : ℕ+) :
    sineQuarticCoeff a b b a = 1 / π + (if a = b then 1 / (2 * π) else 0) := by
  rw [← sineQuarticCoeff_pair_val, sineQuarticCoeff_eq, sineQuarticCoeff_eq]
  have := a.pos
  have := b.pos
  split_ifs <;> first | (exfalso; omega) | ring

/-- The quartic coefficient of two mode indices. -/
def gN {N : ℕ} (i j k l : Fin N) : ℝ :=
  sineQuarticCoeff (modeIdx i) (modeIdx j) (modeIdx k) (modeIdx l)

theorem gN_pair {N : ℕ} (i k : Fin N) :
    gN i i k k = 1 / π + (if i = k then 1 / (2 * π) else 0) := by
  unfold gN
  rw [sineQuarticCoeff_pair_val]
  simp [modeIdx_injective.eq_iff]

theorem gN_pair_b {N : ℕ} (i k : Fin N) :
    gN i k i k = 1 / π + (if i = k then 1 / (2 * π) else 0) := by
  unfold gN
  rw [sineQuarticCoeff_pair_val_b]
  simp [modeIdx_injective.eq_iff]

theorem gN_pair_c {N : ℕ} (i k : Fin N) :
    gN i k k i = 1 / π + (if i = k then 1 / (2 * π) else 0) := by
  unfold gN
  rw [sineQuarticCoeff_pair_val_c]
  simp [modeIdx_injective.eq_iff]

theorem gN_diag {N : ℕ} (i : Fin N) : gN i i i i = 3 / (2 * π) := by
  unfold gN; exact sineQuarticCoeff_diag _

section sums
variable {N : ℕ} (F : Fin N → Fin N → Fin N → Fin N → ℝ)

theorem sum_ite_pair_ij_kl :
    ∑ i, ∑ j, ∑ k, ∑ l, (if i = j ∧ k = l then F i j k l else 0) = ∑ i, ∑ k, F i i k k := by
  simp [ite_and]

theorem sum_ite_pair_ik_jl :
    ∑ i, ∑ j, ∑ k, ∑ l, (if i = k ∧ j = l then F i j k l else 0) = ∑ i, ∑ j, F i j i j := by
  simp [ite_and]

theorem sum_ite_pair_il_jk :
    ∑ i, ∑ j, ∑ k, ∑ l, (if i = l ∧ j = k then F i j k l else 0) = ∑ i, ∑ j, F i j j i := by
  simp [ite_and]

theorem sum_ite_all :
    ∑ i, ∑ j, ∑ k, ∑ l, (if i = j ∧ j = k ∧ k = l then F i j k l else 0) = ∑ i, F i i i i := by
  simp [ite_and]

end sums

/-- The quartic moment sum: `∑ g a_i a_j a_k a_l E[cos cos cos cos]`
`= 3/(4π) (∑ a²)² - 3/(16π) ∑ a⁴`. -/
theorem sum_quartic_moment {N : ℕ} (a : Fin N → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, (gN i j k l * (a i * a j * a k * a l)) *
      ((1 / 4) * ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0)
        + (if i = l ∧ j = k then 1 else 0)) - (3 / 8) * (if i = j ∧ j = k ∧ k = l then 1 else 0))
      = 3 / (4 * π) * (∑ t, a t ^ 2) ^ 2 - 3 / (16 * π) * ∑ t, a t ^ 4 := by
  have hpt : ∀ i j k l : Fin N, (gN i j k l * (a i * a j * a k * a l)) *
      ((1 / 4) * ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0)
        + (if i = l ∧ j = k then 1 else 0)) - (3 / 8) * (if i = j ∧ j = k ∧ k = l then 1 else 0))
      = (1 / 4) * (if i = j ∧ k = l then gN i j k l * (a i * a j * a k * a l) else 0)
        + (1 / 4) * (if i = k ∧ j = l then gN i j k l * (a i * a j * a k * a l) else 0)
        + (1 / 4) * (if i = l ∧ j = k then gN i j k l * (a i * a j * a k * a l) else 0)
        - (3 / 8) * (if i = j ∧ j = k ∧ k = l then gN i j k l * (a i * a j * a k * a l) else 0) :=
            by
    intro i j k l
    split_ifs <;> ring
  simp_rw [hpt]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_ite_pair_ij_kl (fun i j k l => gN i j k l * (a i * a j * a k * a l)),
    sum_ite_pair_ik_jl (fun i j k l => gN i j k l * (a i * a j * a k * a l)),
    sum_ite_pair_il_jk (fun i j k l => gN i j k l * (a i * a j * a k * a l)),
    sum_ite_all (fun i j k l => gN i j k l * (a i * a j * a k * a l))]
  simp only [gN_pair, gN_pair_b, gN_pair_c, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hS : ∀ f : Fin N → Fin N → ℝ, (∀ i k, f i k = a i ^ 2 * a k ^ 2) →
      ∑ i, ∑ k, f i k = (∑ t, a t ^ 2) ^ 2 := by
    intro f hf
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hf i k
  have h1 := hS (fun i k => a i * a i * a k * a k) (fun i k => by ring)
  have h2 := hS (fun i k => a i * a k * a i * a k) (fun i k => by ring)
  have h3 := hS (fun i k => a i * a k * a k * a i) (fun i k => by ring)
  have h4 : ∑ i, a i * a i * a i * a i = ∑ t, a t ^ 4 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2, h3, h4]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The frequency `λ_{j+1}` of the `j`-th mode, `j : Fin N`. -/
def lamMode {N : ℕ} (m : ℝ) (hm : 0 < m) (j : Fin N) : ℝ := lam m hm (modeIdx j)

theorem lamMode_pos {N : ℕ} (m : ℝ) (hm : 0 < m) (j : Fin N) : 0 < lamMode m hm j :=
  Real.sqrt_pos.2 (by positivity)

/-- The quartic functional `G(q) = ¼ ∑_{ijkl} g_{ijkl} q̂_i q̂_j q̂_k q̂_l`, `q̂_j = q_j/√λ_j`,
on the first `N` modes (blueprint Lemma `bpW:w0n:gradient`). -/
def quarticG {N : ℕ} (m : ℝ) (hm : 0 < m) (q : Fin N → ℝ) : ℝ :=
  (1 / 4) * ∑ i, ∑ j, ∑ k, ∑ l, gN i j k l *
    (q i / Real.sqrt (lamMode m hm i) * (q j / Real.sqrt (lamMode m hm j))
      * (q k / Real.sqrt (lamMode m hm k)) * (q l / Real.sqrt (lamMode m hm l)))

/-- The average of `G(q)` over the angles, `q_j = √(2 I_j) cos φ_j`. -/
def avgG {N : ℕ} (m : ℝ) (hm : 0 < m) (I : Fin N → ℝ) : ℝ :=
  angleAvg N (fun φ => quarticG m hm (fun j => Real.sqrt (2 * I j) * Real.cos (φ j)))

/-- The full angle average of `G` (blueprint `bpW:w0n:avgG`):
`⟨G⟩ = 3/(16π) (4 (∑ I_j/λ_j)² - ∑ I_j²/λ_j²)`. -/
theorem avgG_eq {N : ℕ} (m : ℝ) (hm : 0 < m) (I : Fin N → ℝ) (hI : ∀ j, 0 ≤ I j) :
    avgG m hm I = 3 / (16 * π) *
      (4 * (∑ j, I j / lamMode m hm j) ^ 2 - ∑ j, (I j / lamMode m hm j) ^ 2) := by
  set a : Fin N → ℝ := fun j => Real.sqrt (2 * I j) / Real.sqrt (lamMode m hm j) with ha
  have hpt : ∀ φ : Fin N → ℝ, quarticG m hm (fun j => Real.sqrt (2 * I j) * Real.cos (φ j)) =
      (1 / 4) * ∑ i, ∑ j, ∑ k, ∑ l, (gN i j k l * (a i * a j * a k * a l)) *
        (Real.cos (φ i) * Real.cos (φ j) * Real.cos (φ k) * Real.cos (φ l)) := by
    intro φ
    unfold quarticG
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [ha]
    ring
  unfold avgG
  simp_rw [hpt]
  have hc : ∀ (c : ℝ) (F : (Fin N → ℝ) → ℝ), angleAvg N (fun φ => c * F φ) = c * angleAvg N F :=
    fun c F => MeasureTheory.integral_const_mul c F
  rw [hc, angleAvg_sum_cos_four]
  simp only [angleAvg_cos_four]
  rw [sum_quartic_moment]
  have hsq : ∀ j, a j ^ 2 = 2 * (I j / lamMode m hm j) := by
    intro j
    simp only [ha]
    rw [div_pow, Real.sq_sqrt (by linarith [hI j]), Real.sq_sqrt (lamMode_pos m hm j).le]
    ring
  have h2 : ∑ t, a t ^ 2 = 2 * ∑ j, I j / lamMode m hm j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => hsq j
  have h4 : ∑ t, a t ^ 4 = 4 * ∑ j, (I j / lamMode m hm j) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show a j ^ 4 = (a j ^ 2) ^ 2 by ring, hsq]; ring
  rw [h2, h4]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The frequency `λ_{i+1}` of the tangential mode `i ∈ {1, 2}` (`i : Fin 2`). -/
def lamTan (m : ℝ) (hm : 0 < m) (i : Fin 2) : ℝ := lam m hm ⟨i.val + 1, Nat.succ_pos _⟩

/-- The frequency `λ_{j+3}` of the normal mode `j : Fin n` (`j ≥ 3` in the blueprint). -/
def lamNor (m : ℝ) (hm : 0 < m) {n : ℕ} (j : Fin n) : ℝ := lam m hm ⟨j.val + 3, Nat.succ_pos _⟩

/-- The tangential action matrix `A` of blueprint `bpW:w0n:AB`: `A_ii = 9/(8π λ_i²)`,
`A_12 = A_21 = 3/(2π λ_1 λ_2)`. -/
def actionA (m : ℝ) (hm : 0 < m) (i i' : Fin 2) : ℝ :=
  if i = i' then 9 / (8 * π * lamTan m hm i ^ 2)
  else 3 / (2 * π * lamTan m hm i * lamTan m hm i')

/-- The coupling matrix `B` of blueprint `bpW:w0n:AB`: `B_ji = 3/(2π λ_j λ_i)`. -/
def actionB (m : ℝ) (hm : 0 < m) {n : ℕ} (j : Fin n) (i : Fin 2) : ℝ :=
  3 / (2 * π * lamNor m hm j * lamTan m hm i)

theorem lamTan_pos (m : ℝ) (hm : 0 < m) (i : Fin 2) : 0 < lamTan m hm i :=
  Real.sqrt_pos.2 (by positivity)

theorem lamNor_pos (m : ℝ) (hm : 0 < m) {n : ℕ} (j : Fin n) : 0 < lamNor m hm j :=
  Real.sqrt_pos.2 (by positivity)

theorem lamMode_castAdd (m : ℝ) (hm : 0 < m) (n : ℕ) (i : Fin 2) :
    lamMode m hm (Fin.castAdd n i) = lamTan m hm i := rfl

theorem lamMode_natAdd (m : ℝ) (hm : 0 < m) (n : ℕ) (j : Fin n) :
    lamMode m hm (Fin.natAdd 2 j) = lamNor m hm j := by
  unfold lamMode lamNor modeIdx
  congr 1
  apply PNat.eq
  simp only [Fin.val_natAdd, PNat.mk_coe]
  omega

/-- **Action coefficients (blueprint `bpW:w0n:AB`)**, for `J = {1, 2}` and every `m > 0`: the part
of the angle-averaged `G` containing at least one tangential action (`I = (I_1, I_2)`) is
`½⟨AI, I⟩ + ⟨BI, Z⟩`, `Z = (I_j)_{j ≥ 3}`, with the corrected coefficients. The remaining part
(no tangential action) is `⟨G^nor⟩`. -/
theorem partial_avgG_eq (m : ℝ) (hm : 0 < m) {n : ℕ} (I : Fin 2 → ℝ) (Z : Fin n → ℝ)
    (hI : ∀ i, 0 ≤ I i) (hZ : ∀ j, 0 ≤ Z j) :
    avgG m hm (Fin.append I Z) - avgG m hm (Fin.append (0 : Fin 2 → ℝ) Z) =
      (1 / 2) * ∑ i, ∑ i', actionA m hm i i' * I i * I i'
        + ∑ j, ∑ i, actionB m hm j i * I i * Z j := by
  have hnn : ∀ I' : Fin 2 → ℝ, (∀ i, 0 ≤ I' i) → ∀ j, 0 ≤ (Fin.append I' Z) j := by
    intro I' hI' j
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simpa using hI' i
    · simpa using hZ j
  rw [avgG_eq m hm _ (hnn I hI), avgG_eq m hm _ (hnn 0 (fun _ => le_rfl))]
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, lamMode_castAdd,
    lamMode_natAdd, Pi.zero_apply, zero_div, Finset.sum_const_zero, zero_pow two_ne_zero, zero_add]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hB : ∑ j, ∑ i, actionB m hm j i * I i * Z j =
      3 / (2 * π) * ((∑ i, I i / lamTan m hm i) * ∑ j, Z j / lamNor m hm j) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := (lamTan_pos m hm i).ne'
    have := (lamNor_pos m hm j).ne'
    unfold actionB
    field_simp
  rw [hB]
  have h0 := (lamTan_pos m hm 0).ne'
  have h1 := (lamTan_pos m hm 1).ne'
  simp only [Fin.sum_univ_two, actionA]
  simp
  field_simp
  ring

end KAM.Wave

end
