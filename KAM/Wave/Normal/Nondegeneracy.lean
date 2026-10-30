/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Normal.ActionCoeff
public import KAM.Wave.Normal.FinsuppAbs

/-!
# Nondegeneracy for every `m > 0` (blueprint `bpW:w0n:nondeg`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

With `J = {1, 2}`, `ω(I) = λ_J + A I` and `Ω(I) = λ_N + B I` (the corrected coefficients of
`KAM/Wave/Normal/ActionCoeff.lean`), we prove for every `m > 0`
* (i) `det A = -63/(64 π² λ_1² λ_2²) = -63/(64 π² (1+m)(4+m)) ≠ 0` (`KAM.Wave.det_actionA`);
* (ii) `⟨l, λ_N⟩ ≠ 0` for `1 ≤ |l| ≤ 2` (`KAM.Wave.pairing_ne_zero`);
* (iii) (A₃): for `1 ≤ |l| ≤ 2` and every `k ∈ ℤ²`, the affine function
  `I ↦ ⟨k, ω(I)⟩ + ⟨l, Ω(I)⟩` is not identically zero (`KAM.Wave.A3_holds`).

Normal modes `j ≥ 3` are indexed by `ν = j - 3 : ℕ`, and `l ∈ ℤ^N` by `l : ℕ →₀ ℤ`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

/-- The frequency `λ_{ν+3}` of the `ν`-th normal mode. -/
def lamN (m : ℝ) (hm : 0 < m) (ν : ℕ) : ℝ := lam m hm ⟨ν + 3, Nat.succ_pos _⟩

theorem lamN_sq (m : ℝ) (hm : 0 < m) (ν : ℕ) : lamN m hm ν ^ 2 = ((ν : ℝ) + 3) ^ 2 + m := by
  unfold lamN lam
  rw [Real.sq_sqrt (by positivity)]
  simp

theorem lamN_gt (m : ℝ) (hm : 0 < m) (ν : ℕ) : 3 < lamN m hm ν := by
  have h0 : 0 ≤ lamN m hm ν := Real.sqrt_nonneg _
  have := lamN_sq m hm ν
  have : (0 : ℝ) ≤ ν := Nat.cast_nonneg ν
  nlinarith

theorem lamN_injective (m : ℝ) (hm : 0 < m) : Function.Injective (lamN m hm) := by
  intro a b h
  have h2 := congrArg (· ^ 2) h
  simp only [lamN_sq] at h2
  have : (a : ℝ) = b := by nlinarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a), (Nat.cast_nonneg b : (0 :
      ℝ) ≤ b)]
  exact_mod_cast this

theorem lamTan_zero_sq (m : ℝ) (hm : 0 < m) : lamTan m hm 0 ^ 2 = 1 + m := by
  unfold lamTan lam
  rw [Real.sq_sqrt (by positivity)]
  simp

theorem lamTan_one_sq (m : ℝ) (hm : 0 < m) : lamTan m hm 1 ^ 2 = 4 + m := by
  unfold lamTan lam
  rw [Real.sq_sqrt (by positivity)]
  norm_num

/-- The coupling `B_{νi} = 3/(2π λ_ν λ_i)` indexed by the normal mode `ν : ℕ`. -/
def actionBN (m : ℝ) (hm : 0 < m) (ν : ℕ) (i : Fin 2) : ℝ :=
  3 / (2 * π * lamN m hm ν * lamTan m hm i)

/-- The matrix `A`. -/
def actionAMat (m : ℝ) (hm : 0 < m) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i i' => actionA m hm i i'

/-- `A = (3/(8π)) D (4·𝟏𝟏ᵀ - Id) D` with `D = diag (λ_1⁻¹, λ_2⁻¹)`. -/
theorem actionA_eq (m : ℝ) (hm : 0 < m) (i i' : Fin 2) :
    actionA m hm i i' = 3 / (8 * π) * (1 / lamTan m hm i) *
      (4 - (if i = i' then 1 else 0)) * (1 / lamTan m hm i') := by
  have := (lamTan_pos m hm i).ne'
  have := (lamTan_pos m hm i').ne'
  have hpi : π ≠ 0 := Real.pi_ne_zero
  unfold actionA
  by_cases h : i = i'
  · subst h; simp; field_simp; norm_num
  · simp [h]; field_simp; norm_num

/-- **(i)** `det A = -63/(64 π² λ_1² λ_2²) = -63/(64 π² (1+m)(4+m)) ≠ 0` (blueprint
`bpW:w0n:nondeg`). -/
theorem det_actionA (m : ℝ) (hm : 0 < m) :
    (actionAMat m hm).det = -(63 / (64 * π ^ 2 * (1 + m) * (4 + m))) ∧
      (actionAMat m hm).det = -(63 / (64 * π ^ 2 * lamTan m hm 0 ^ 2 * lamTan m hm 1 ^ 2)) ∧
      (actionAMat m hm).det ≠ 0 := by
  have h0 := (lamTan_pos m hm 0).ne'
  have h1 := (lamTan_pos m hm 1).ne'
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hd : (actionAMat m hm).det = -(63 / (64 * π ^ 2 * lamTan m hm 0 ^ 2 * lamTan m hm 1 ^ 2)) :=
      by
    rw [Matrix.det_fin_two]
    simp only [actionAMat, Matrix.of_apply, actionA]
    simp
    field_simp
    ring
  refine ⟨?_, hd, ?_⟩
  · rw [hd, lamTan_zero_sq, lamTan_one_sq]
  · rw [hd]
    have : 0 < 63 / (64 * π ^ 2 * lamTan m hm 0 ^ 2 * lamTan m hm 1 ^ 2) := by
      have := lamTan_pos m hm 0
      have := lamTan_pos m hm 1
      positivity
    linarith

/-- The pairing `⟨l, f⟩ = ∑_ν l_ν f_ν` of a finitely supported integer vector with a real
sequence. -/
def linF (l : ℕ →₀ ℤ) (f : ℕ → ℝ) : ℝ := l.sum fun j v => (v : ℝ) * f j

theorem linF_single (ν : ℕ) (σ : ℤ) (f : ℕ → ℝ) : linF (Finsupp.single ν σ) f = σ * f ν := by
  unfold linF
  rw [Finsupp.sum_single_index]
  simp

theorem linF_add_single (a b : ℕ) (σ τ : ℤ) (f : ℕ → ℝ) :
    linF (Finsupp.single a σ + Finsupp.single b τ) f = σ * f a + τ * f b := by
  unfold linF
  rw [Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring)]
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]

/-- Common shape of the sign cases: `σ λ_a + τ λ_b ≠ 0` for `a ≠ b`, `σ, τ ∈ {±1}`. -/
theorem sign_pair_ne_zero (m : ℝ) (hm : 0 < m) {a b : ℕ} (hab : a ≠ b) {σ τ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    (σ : ℝ) * lamN m hm a + τ * lamN m hm b ≠ 0 := by
  have ha := lamN_gt m hm a
  have hb := lamN_gt m hm b
  have hne : lamN m hm a ≠ lamN m hm b := fun h => hab (lamN_injective m hm h)
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> simp
  · linarith
  · exact sub_ne_zero.2 hne
  · intro h; exact hne (by linarith)
  · linarith

/-- **(ii)** `⟨l, λ_N⟩ ≠ 0` for `1 ≤ |l| ≤ 2` (blueprint `bpW:w0n:nondeg`). -/
theorem pairing_ne_zero (m : ℝ) (hm : 0 < m) (l : ℕ →₀ ℤ) (h1 : 1 ≤ l1Norm l)
    (h2 : l1Norm l ≤ 2) : linF l (lamN m hm) ≠ 0 := by
  have hcases : l1Norm l = 1 ∨ l1Norm l = 2 := by omega
  rcases hcases with h | h
  · obtain ⟨ν, σ, hσ, rfl⟩ := l1Norm_one l h
    rw [linF_single]
    have := lamN_gt m hm ν
    rcases hσ with rfl | rfl <;> simp <;> linarith
  · rcases l1Norm_two l h with ⟨ν, σ, hσ, rfl⟩ | ⟨a, b, σ, τ, hab, hσ, hτ, rfl⟩
    · rw [linF_single]
      have := lamN_gt m hm ν
      rcases hσ with rfl | rfl <;> simp <;> linarith
    · rw [linF_add_single]
      exact sign_pair_ne_zero m hm hab hσ hτ

theorem linF_add_mul (l : ℕ →₀ ℤ) (f g : ℕ → ℝ) (c : ℝ) :
    linF l (fun ν => f ν + c * g ν) = linF l f + c * linF l g := by
  unfold linF Finsupp.sum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem linF_add_mul_mul (l : ℕ →₀ ℤ) (f g : ℕ → ℝ) (c d : ℝ) :
    linF l (fun ν => f ν + c * g ν + d * g ν) = linF l f + (c + d) * linF l g := by
  have := linF_add_mul l (fun ν => f ν + c * g ν) g d
  rw [this, linF_add_mul]; ring

/-- Properties of `s = ⟨l, λ_N⁻¹⟩` for `|l| = 1` or `2` (single basis vector). -/
theorem s_single_props (m : ℝ) (hm : 0 < m) (ν : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1 ∨ σ = 2 ∨ σ = -2) :
    linF (Finsupp.single ν σ) (fun j => 1 / lamN m hm j) ≠ 0 ∧
      |linF (Finsupp.single ν σ) (fun j => 1 / lamN m hm j)| ≤ 2 / 3 := by
  rw [linF_single]
  have h3 := lamN_gt m hm ν
  have hpos : 0 < lamN m hm ν := by linarith
  have hle : 1 / lamN m hm ν ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3.le
  have hp : 0 < 1 / lamN m hm ν := by positivity
  refine ⟨mul_ne_zero (by rcases hσ with rfl | rfl | rfl | rfl <;> norm_num) hp.ne', ?_⟩
  rw [abs_mul, abs_of_pos hp]
  have : |(σ : ℝ)| ≤ 2 := by rcases hσ with rfl | rfl | rfl | rfl <;> norm_num
  calc |(σ : ℝ)| * (1 / lamN m hm ν) ≤ 2 * (1 / 3) := by gcongr
    _ = 2 / 3 := by norm_num

theorem s_pair_props (m : ℝ) (hm : 0 < m) {a b : ℕ} (hab : a ≠ b) {σ τ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    linF (Finsupp.single a σ + Finsupp.single b τ) (fun j => 1 / lamN m hm j) ≠ 0 ∧
      |linF (Finsupp.single a σ + Finsupp.single b τ) (fun j => 1 / lamN m hm j)| ≤ 2 / 3 := by
  rw [linF_add_single]
  simp only [one_div]
  have ha := lamN_gt m hm a
  have hb := lamN_gt m hm b
  have hpa : 0 < (lamN m hm a)⁻¹ := inv_pos.2 (by linarith)
  have hpb : 0 < (lamN m hm b)⁻¹ := inv_pos.2 (by linarith)
  have hla : (lamN m hm a)⁻¹ ≤ 3⁻¹ := inv_anti₀ (by norm_num) ha.le
  have hlb : (lamN m hm b)⁻¹ ≤ 3⁻¹ := inv_anti₀ (by norm_num) hb.le
  have hne : (lamN m hm a)⁻¹ ≠ (lamN m hm b)⁻¹ := fun h =>
    hab (lamN_injective m hm (inv_injective h))
  constructor
  · rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> simp
    · linarith
    · exact sub_ne_zero.2 hne
    · intro h; exact hne (by linarith)
    · linarith
  · rw [abs_le]
    rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> simp <;> constructor <;> linarith

/-- Algebraic core of (A₃): the two vanishing linear coefficients give `k_i/λ_i = c`, `7c = -4s`. -/
theorem core_c {l0 l1 s : ℝ} {k0 k1 : ℤ}
    (X : 3 * k0 / l0 + 4 * k1 / l1 + 4 * s = 0) (Y : 4 * k0 / l0 + 3 * k1 / l1 + 4 * s = 0) :
    (k0 : ℝ) / l0 = k1 / l1 ∧ 7 * ((k0 : ℝ) / l0) + 4 * s = 0 := by
  have hX : 3 * ((k0 : ℝ) / l0) + 4 * ((k1 : ℝ) / l1) + 4 * s = 0 := by
    rw [← X]; ring
  have hY : 4 * ((k0 : ℝ) / l0) + 3 * ((k1 : ℝ) / l1) + 4 * s = 0 := by
    rw [← Y]; ring
  constructor <;> linarith

/-- Case `|l| = 2`: `0 < |s| ≤ 2/3` is incompatible with the vanishing of the linear part. -/
theorem core_alpha {l0 l1 c s : ℝ} {k0 k1 : ℤ} (hk0 : (k0 : ℝ) = c * l0) (hk1 : (k1 : ℝ) = c * l1)
    (h01 : l0 < l1) (h1 : l1 < l0 + 1) (hc2 : 7 * c + 4 * s = 0)
    (hs : |s| ≤ 2 / 3) (hs0 : s ≠ 0) : False := by
  have hd : ((k1 - k0 : ℤ) : ℝ) = c * (l1 - l0) := by push_cast; rw [hk0, hk1]; ring
  have hcb : |c| ≤ 8 / 21 := by
    obtain ⟨hs1, hs2⟩ := abs_le.1 hs
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hlt : |((k1 - k0 : ℤ) : ℝ)| < 1 := by
    rw [hd, abs_mul, abs_of_pos (by linarith : 0 < l1 - l0)]
    have : l1 - l0 < 1 := by linarith
    nlinarith [abs_nonneg c]
  have hz : k1 - k0 = 0 := by
    have : |k1 - k0| < 1 := by exact_mod_cast hlt
    exact Int.abs_lt_one_iff.1 this
  rw [hz] at hd
  simp only [Int.cast_zero] at hd
  have hc0 : c = 0 := by
    rcases mul_eq_zero.1 hd.symm with h | h
    · exact h
    · linarith
  exact hs0 (by rw [hc0] at hc2; linarith)

/-- Case `|l| = 1`: the vanishing of the full affine function forces `7 Λ² = 4(λ_1² + λ_2²)`
and then `k_1² < 1`, a contradiction. -/
theorem core_beta {l0 l1 c s L Λ σ : ℝ} {k0 k1 : ℤ} (hl0 : 0 < l0) (hk0 : (k0 : ℝ) = c * l0)
    (hk1 : (k1 : ℝ) = c * l1) (hc2 : 7 * c + 4 * s = 0)
    (E0 : (k0 : ℝ) * l0 + k1 * l1 + L = 0) (hL : L = σ * Λ) (hs : s = σ / Λ) (hΛ : 3 < Λ)
    (hσ : σ = 1 ∨ σ = -1) : False := by
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hΛ0 : Λ ≠ 0 := by linarith
  have h7 : 7 * c * Λ = -4 * σ := by
    rw [hs] at hc2
    field_simp at hc2
    nlinarith
  have hE0 : c * (l0 ^ 2 + l1 ^ 2) + σ * Λ = 0 := by
    rw [hk0, hk1, hL] at E0; nlinarith
  have hE : σ * (7 * Λ ^ 2 - 4 * (l0 ^ 2 + l1 ^ 2)) = 0 := by
    have : 7 * Λ * (c * (l0 ^ 2 + l1 ^ 2) + σ * Λ) = 0 := by rw [hE0]; ring
    nlinarith
  have hE' : 7 * Λ ^ 2 = 4 * (l0 ^ 2 + l1 ^ 2) := by
    rcases mul_eq_zero.1 hE with h | h
    · exact absurd h hσ0
    · linarith
  have hcsq : c ^ 2 * (28 * (l0 ^ 2 + l1 ^ 2)) = 16 := by
    have : (7 * c * Λ) ^ 2 = 16 := by rw [h7]; nlinarith
    nlinarith
  have hk0sq : (k0 : ℝ) ^ 2 < 1 := by
    rw [hk0]
    have : (c * l0) ^ 2 = c ^ 2 * l0 ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg (c * l1), sq_nonneg c, sq_nonneg l1]
  have hk00 : k0 = 0 := by
    by_contra hne
    have : 1 ≤ k0 ^ 2 := by
      rcases lt_or_gt_of_ne hne with h | h <;> nlinarith
    have : (1 : ℝ) ≤ (k0 : ℝ) ^ 2 := by exact_mod_cast this
    linarith
  have hc0 : c = 0 ∨ l0 = 0 := by
    apply mul_eq_zero.1
    rw [← hk0, hk00]; simp
  have hc00 : c = 0 := hc0.resolve_right hl0.ne'
  rw [hc00] at h7
  exact hσ0 (by linarith)

/-- The tangential frequency `ω_i(I) = λ_i + (A I)_i`. -/
def omegaTan (m : ℝ) (hm : 0 < m) (I : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  lamTan m hm i + ∑ i', actionA m hm i i' * I i'

/-- The normal frequency `Ω_ν(I) = λ_ν + (B I)_ν`. -/
def omegaNor (m : ℝ) (hm : 0 < m) (I : Fin 2 → ℝ) (ν : ℕ) : ℝ :=
  lamN m hm ν + ∑ i, actionBN m hm ν i * I i

/-- The affine function `I ↦ ⟨k, ω(I)⟩ + ⟨l, Ω(I)⟩` of condition (A₃). -/
def affineForm (m : ℝ) (hm : 0 < m) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) (I : Fin 2 → ℝ) : ℝ :=
  ∑ i, (k i : ℝ) * omegaTan m hm I i + linF l (omegaNor m hm I)

theorem affineForm_expand (m : ℝ) (hm : 0 < m) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) (I : Fin 2 → ℝ) :
    affineForm m hm k l I =
      ((k 0 : ℝ) * lamTan m hm 0 + (k 1 : ℝ) * lamTan m hm 1 + linF l (lamN m hm))
        + I 0 * ((k 0 : ℝ) * actionA m hm 0 0 + (k 1 : ℝ) * actionA m hm 1 0
          + 3 / (2 * π * lamTan m hm 0) * linF l (fun j => 1 / lamN m hm j))
        + I 1 * ((k 0 : ℝ) * actionA m hm 0 1 + (k 1 : ℝ) * actionA m hm 1 1
          + 3 / (2 * π * lamTan m hm 1) * linF l (fun j => 1 / lamN m hm j)) := by
  have hN : omegaNor m hm I = fun ν => lamN m hm ν + (3 / (2 * π * lamTan m hm 0) * I 0)
      * (1 / lamN m hm ν) + (3 / (2 * π * lamTan m hm 1) * I 1) * (1 / lamN m hm ν) := by
    funext ν
    have := (lamN_gt m hm ν)
    have h0 := (lamTan_pos m hm 0).ne'
    have h1 := (lamTan_pos m hm 1).ne'
    have hpi : π ≠ 0 := Real.pi_ne_zero
    have : lamN m hm ν ≠ 0 := by linarith
    simp only [omegaNor, Fin.sum_univ_two, actionBN]
    field_simp
    ring
  unfold affineForm
  rw [hN, linF_add_mul_mul]
  simp only [Fin.sum_univ_two, omegaTan]
  ring

theorem lam_facts (m : ℝ) (hm : 0 < m) :
    0 < lamTan m hm 0 ∧ lamTan m hm 0 < lamTan m hm 1 ∧ lamTan m hm 1 < lamTan m hm 0 + 1 := by
  have p0 := lamTan_pos m hm 0
  have p1 := lamTan_pos m hm 1
  have q0 := lamTan_zero_sq m hm
  have q1 := lamTan_one_sq m hm
  have g0 : 1 < lamTan m hm 0 := by nlinarith
  refine ⟨p0, by nlinarith, by nlinarith⟩

/-- **(iii)** Condition (A₃) for `J = {1, 2}` and every `m > 0`: for `1 ≤ |l| ≤ 2` and every
`k ∈ ℤ²` the affine function `I ↦ ⟨k, ω(I)⟩ + ⟨l, Ω(I)⟩` is not identically zero. -/
theorem A3_holds (m : ℝ) (hm : 0 < m) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) (h1 : 1 ≤ l1Norm l)
    (h2 : l1Norm l ≤ 2) : ∃ I : Fin 2 → ℝ, affineForm m hm k l I ≠ 0 := by
  by_contra H
  push Not at H
  obtain ⟨hl0, hl01, hl1⟩ := lam_facts m hm
  have e00 := H ![0, 0]
  have e10 := H ![1, 0]
  have e01 := H ![0, 1]
  rw [affineForm_expand] at e00 e10 e01
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, add_zero, one_mul] at e00 e10 e01
  set l0 := lamTan m hm 0 with hl0def
  set l1 := lamTan m hm 1 with hl1def
  set s := linF l (fun j => 1 / lamN m hm j) with hsdef
  set L := linF l (lamN m hm) with hLdef
  have Q0 : (k 0 : ℝ) * actionA m hm 0 0 + (k 1 : ℝ) * actionA m hm 1 0
      + 3 / (2 * π * l0) * s = 0 := by linarith
  have Q1 : (k 0 : ℝ) * actionA m hm 0 1 + (k 1 : ℝ) * actionA m hm 1 1
      + 3 / (2 * π * l1) * s = 0 := by linarith
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have h0ne := hl0.ne'
  have h1ne : l1 ≠ 0 := by linarith
  have X : 3 * (k 0 : ℝ) / l0 + 4 * (k 1 : ℝ) / l1 + 4 * s = 0 := by
    have : 3 * (k 0 : ℝ) / l0 + 4 * (k 1 : ℝ) / l1 + 4 * s
        = ((k 0 : ℝ) * actionA m hm 0 0 + (k 1 : ℝ) * actionA m hm 1 0
          + 3 / (2 * π * l0) * s) * (8 * π * l0 / 3) := by
      simp only [actionA]; simp; simp only [← hl0def, ← hl1def]; field_simp; ring
    rw [this, Q0, zero_mul]
  have Y : 4 * (k 0 : ℝ) / l0 + 3 * (k 1 : ℝ) / l1 + 4 * s = 0 := by
    have : 4 * (k 0 : ℝ) / l0 + 3 * (k 1 : ℝ) / l1 + 4 * s
        = ((k 0 : ℝ) * actionA m hm 0 1 + (k 1 : ℝ) * actionA m hm 1 1
          + 3 / (2 * π * l1) * s) * (8 * π * l1 / 3) := by
      simp only [actionA]; simp; simp only [← hl0def, ← hl1def]; field_simp; ring
    rw [this, Q1, zero_mul]
  obtain ⟨hc1, hc2⟩ := core_c X Y
  set c := (k 0 : ℝ) / l0 with hcdef
  have hk0 : (k 0 : ℝ) = c * l0 := by rw [hcdef]; field_simp
  have hk1 : (k 1 : ℝ) = c * l1 := by
    have : (k 1 : ℝ) / l1 = c := hc1.symm
    rw [← this]; field_simp
  have E0 : (k 0 : ℝ) * l0 + (k 1 : ℝ) * l1 + L = 0 := by linarith
  have hcases : l1Norm l = 1 ∨ l1Norm l = 2 := by omega
  rcases hcases with h | h
  · obtain ⟨ν, σ, hσ, rfl⟩ := l1Norm_one l h
    have hs' : s = (σ : ℝ) / lamN m hm ν := by
      rw [hsdef, linF_single]; ring
    have hL' : L = (σ : ℝ) * lamN m hm ν := by rw [hLdef, linF_single]
    exact core_beta hl0 hk0 hk1 hc2 E0 hL' hs' (lamN_gt m hm ν)
      (by rcases hσ with rfl | rfl <;> simp)
  · rcases l1Norm_two l h with ⟨ν, σ, hσ, rfl⟩ | ⟨a, b, σ, τ, hab, hσ, hτ, rfl⟩
    · have := s_single_props m hm ν σ (by rcases hσ with h | h <;> simp [h])
      exact core_alpha hk0 hk1 hl01 hl1 hc2 this.2 this.1
    · have := s_pair_props m hm hab hσ hτ
      exact core_alpha hk0 hk1 hl01 hl1 hc2 this.2 this.1

/-- **Nondegeneracy for every `m > 0`** (blueprint `bpW:w0n:nondeg`), `J = {1, 2}`:
(i) `det A ≠ 0`, (ii) (A₂) and (iii) (A₃). -/
theorem nondegeneracy (m : ℝ) (hm : 0 < m) :
    (actionAMat m hm).det ≠ 0 ∧
      (∀ l : ℕ →₀ ℤ, 1 ≤ l1Norm l → l1Norm l ≤ 2 → linF l (lamN m hm) ≠ 0) ∧
      (∀ (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ), 1 ≤ l1Norm l → l1Norm l ≤ 2 →
        ∃ I : Fin 2 → ℝ, affineForm m hm k l I ≠ 0) :=
  ⟨(det_actionA m hm).2.2, fun l h1 h2 => pairing_ne_zero m hm l h1 h2,
    fun k l h1 h2 => A3_holds m hm k l h1 h2⟩

end KAM.Wave

end
