/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Poschel.Setting
public import KAM.Nekhoroshev.Interfaces.CoverParams
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Constants and elementary relations of Theorem 1 (`bpN:p9:setting`, `bpN:p9:elementary`)

The constants `A = 11M/m`, `ε₀ = m r₀² / (2^10 A^{2n})`, `K = (ε₀/ε)^a` with `a = 1/(2n)`, the
covering parameters `theoremCover` (`p = 9/8`, `b = 1/8`), and the lemma `elementary` collecting
the real arithmetic of the source Lemma "Elementary relations" together with the validity of
`theoremCover`. The arithmetic is proved by abstract real lemmas on named reals.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.Canonical KAM.Stability

variable {n : ℕ}

/-- The constant `A = 11 M / m`. -/
def thmA (m M : ℝ) : ℝ := 11 * M / m
/-- The constant `ε₀ = m r₀² / (2^10 A^{2n})`. -/
def thmEps0 (n : ℕ) (r0 m M : ℝ) : ℝ := m * r0 ^ 2 / (2 ^ 10 * thmA m M ^ (2 * n))
/-- The constant `K = (ε₀/ε)^a`, `a = 1/(2n)`. -/
def thmK (n : ℕ) (r0 m M eps : ℝ) : ℝ := (thmEps0 n r0 m M / eps) ^ HeadParams.expo n

/-- The covering parameters of Theorem 1: `p = 9/8`, `b = 1/8`. -/
def theoremCover (n : ℕ) (r0 m M eps : ℝ) : CoverParams n :=
  ⟨9 / 8, 1 / 8, r0, M, m, thmK n r0 m M eps, thmA m M⟩

section Arith

private theorem one_le_ratio {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) : 1 ≤ M / m :=
  (one_le_div hm).2 hmM

private theorem A_ge {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) : 11 ≤ thmA m M := by
  have := one_le_ratio hm hmM
  unfold thmA
  rw [mul_div_assoc]
  linarith

private theorem A_pos {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) : 0 < thmA m M :=
  lt_of_lt_of_le (by norm_num) (A_ge hm hmM)

private theorem sqrt_two_le : Real.sqrt 2 ≤ 2 :=
  Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩

private theorem A_ge_cover {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) :
    9 * M / m + Real.sqrt 2 ≤ thmA m M := by
  have h1 := one_le_ratio hm hmM
  have h2 := sqrt_two_le
  unfold thmA
  rw [mul_div_assoc, mul_div_assoc]
  linarith

private theorem cover_ratio {m M : ℝ} (hm : 0 < m) :
    9 / 8 * M / (1 / 8 * m) = 9 * M / m := by
  field_simp

private theorem r0_le_four {r0 ell m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) (hell : 0 < ell)
    (hr : r0 ≤ ell / (2 * M)) : r0 ≤ 4 * ell / m := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  refine hr.trans ?_
  rw [div_le_div_iff₀ (by positivity) hm]
  nlinarith [mul_pos hell hm, mul_pos hell hM]

private theorem eps0_pos {n : ℕ} {r0 m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) (hr0 : 0 < r0) :
    0 < thmEps0 n r0 m M := by
  have := A_pos hm hmM
  unfold thmEps0
  positivity

private theorem K_pow {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    (x ^ HeadParams.expo n) ^ (2 * n) = x := by
  have hn' : (2 * (n : ℝ)) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  unfold HeadParams.expo
  push_cast
  rw [one_div, inv_mul_cancel₀ hn', Real.rpow_one]

end Arith

section Theorem1
variable {P : Set (Fin n → ℝ)} {r0 s m M ell : ℝ}
  {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

theorem elementary (S : Theorem1Setting P r0 s m M ell h f)
    {eps : ℝ} (heps : 0 < eps) (heps0 : eps ≤ thmEps0 n r0 m M) :
    let A := thmA m M
    let K := thmK n r0 m M eps
    11 ≤ A ∧ 9 * M / m + Real.sqrt 2 ≤ A ∧
    r0 / A ≤ r0 / 11 ∧ r0 ≤ 4 * ell / m ∧
    1 ≤ K ∧ K ^ (2 * n) = thmEps0 n r0 m M / eps ∧
    (eps / thmEps0 n r0 m M) ^ HeadParams.expo n = 1 / K ∧
    eps = m * (r0 / (A * K) ^ n) ^ 2 / 2 ^ 10 ∧
    thmEps0 n r0 m M ≤ m * r0 ^ 2 / 2 ^ 10 ∧
    0 < K / Real.sqrt n ∧ Real.sqrt n * (K / Real.sqrt n) = K ∧
    K / Real.sqrt n ≤ K ∧ (theoremCover n r0 m M eps).Valid := by
  intro A K
  have hn1 : 1 ≤ n := by have := S.hn; omega
  have hm := S.hm
  have hmM := S.hmM
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hr0 := S.hr0
  have hA : 11 ≤ A := A_ge hm hmM
  have hApos : 0 < A := A_pos hm hmM
  have he0 : 0 < thmEps0 n r0 m M := eps0_pos hm hmM hr0
  have hratio : 1 ≤ thmEps0 n r0 m M / eps := (one_le_div heps).2 heps0
  have hKge : 1 ≤ K := Real.one_le_rpow hratio (by unfold HeadParams.expo; positivity)
  have hKpow : K ^ (2 * n) = thmEps0 n r0 m M / eps := K_pow hn1 (by positivity)
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hKge
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hsqsq : Real.sqrt n * (K / Real.sqrt n) = K := by field_simp
  have hA2 : 1 ≤ A ^ (2 * n) := one_le_pow₀ (by linarith)
  refine ⟨hA, A_ge_cover hm hmM, ?_, r0_le_four hm hmM S.hell S.radius, hKge, hKpow, ?_, ?_, ?_,
    div_pos hKpos hsq, hsqsq, ?_, ?_⟩
  · exact div_le_div_of_nonneg_left hr0.le (by norm_num) hA
  · have : eps / thmEps0 n r0 m M = (thmEps0 n r0 m M / eps)⁻¹ := (inv_div _ _).symm
    rw [this, Real.inv_rpow (div_nonneg he0.le heps.le), one_div]
  · have h2 : (r0 / (A * K) ^ n) ^ 2 = r0 ^ 2 / (A ^ (2 * n) * K ^ (2 * n)) := by
      rw [div_pow, ← pow_mul, mul_pow, mul_comm n 2, pow_mul, mul_pow, ← pow_mul, ← pow_mul]
    rw [h2, hKpow]
    unfold thmEps0
    field_simp
  · unfold thmEps0
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < m * r0 ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hA2 this.le]
  · have : K / Real.sqrt n ≤ K / 1 := div_le_div_of_nonneg_left hKpos.le one_pos
      (by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        simpa using Real.one_le_sqrt.2 this)
    simpa using this
  · refine ⟨hn1, by norm_num [theoremCover], by norm_num [theoremCover], hr0, hM, hm, hKge, ?_⟩
    show 9 / 8 * M / (1 / 8 * m) + Real.sqrt 2 ≤ thmA m M
    rw [cover_ratio hm]
    exact A_ge_cover hm hmM

end Theorem1

end KAM.Nekhoroshev
