/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Defs.IsDiophantine
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

/-!
# Diophantine vectors from a real cubic irrational

Let `P = t³ + p₂ t² + p₁ t + p₀ ∈ ℤ[t]` have no rational root and `P(θ) = 0`, `θ ∈ ℝ`. For an
integer matrix `A` with `det A ≠ 0` and `D > 0`, the vector `ω_i = (A_{i0} + A_{i1} θ + A_{i2} θ²)/D`
is `(γ, 2)`-Diophantine for an explicit rational `γ` (`isDiophantine_of_cubicDioOk`). The argument is
the norm form, without complex conjugates:

* `noRatRoot_of`: the rational root theorem (a rational root of the monic `P` is an integer dividing
  `p₀`), so a finite check excludes rational roots;
* `cubic_indep`: `v₀ + v₁ θ + v₂ θ² ≠ 0` for rational `v ≠ 0` (reduce `θ² = sθ + t`; then `P(θ) = 0`
  is linear in `θ`, or `P` has the rational root `-(s + p₂)`);
* `beta_mul_cof`: `β(u) Y(u) = N(u)` for `β(u) = u₀ + u₁ θ + u₂ θ²`, the integer norm `N` and the
  cofactor `Y = y₀ + y₁ θ + y₂ θ²` (integer quadratic forms in `u`), from `P(θ) = 0`;
* `cubN_ne_zero`: `N(u) ≠ 0` for `u ≠ 0` (`N` is the determinant of multiplication by `β(u)`; a
  kernel vector `v` gives `β(u) β(v) = 0`, excluded by independence);
* `Y(u) = uᵀ H(θ) u` with `H` symmetric in `½ℤ[θ]` (`cubicH`), and for `u = Aᵀ k`,
  `Y = kᵀ W k` with `W = A H Aᵀ = W₀ + W₁ θ + W₂ θ²` (`cubicW`, rational), so
  `|k·ω| = |β(u)|/D ≥ 1/(D |Y|) ≥ 1/(D W̄ |k|₁²)` once `|W_ij(θ)| ≤ W̄`;
* `cubicDioOk`: the rational test (no integer root in `[-|p₀|, |p₀|]`, `p₀ ≠ 0`, `det A ≠ 0`, and
  `γ D |W_ij(θ)| ≤ 1` on the enclosure `|θ - θc| ≤ θr` through `polyAbsUp`).

This is the conjugate bound `γ = 1/(D m₁ m₂)` of the SJS plan (§5.3) without leaving `ℝ`, and never
worse than it (`|W_ij| ≤ m₁ m₂`). `isDiophantine_smulT` (scaling, any `τ`) and
`isDiophantine_mono` transfer the constant.
-/

@[expose] public section

namespace KAM.CertificateSharp.Cubic

open Matrix

/-! ### Transfer lemmas -/

theorem isDiophantine_mono {n : ℕ} {γ γ' τ : ℝ} {ω : Fin n → ℝ} (h : KAM.IsDiophantine γ τ ω)
    (hγ : γ' ≤ γ) : KAM.IsDiophantine γ' τ ω := by
  intro k hk
  refine le_trans ?_ (h k hk)
  have : 0 < ∑ i, |(k i : ℝ)| := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hk
    exact lt_of_lt_of_le (abs_pos.mpr (by exact_mod_cast hj))
      (Finset.single_le_sum (f := fun i => |(k i : ℝ)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j))
  exact div_le_div_of_nonneg_right hγ (Real.rpow_nonneg this.le _)

/-- Scaling at any exponent: `c • ω` is `(γ |c|, τ)`-Diophantine. -/
theorem isDiophantine_smulT {n : ℕ} {γ τ : ℝ} {ω : Fin n → ℝ} (h : KAM.IsDiophantine γ τ ω)
    (c : ℝ) : KAM.IsDiophantine (γ * |c|) τ (c • ω) := by
  intro k hk
  have := h k hk
  have e : ∑ i, (k i : ℝ) * (c • ω) i = c * ∑ i, (k i : ℝ) * ω i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [e, abs_mul, mul_div_right_comm, mul_comm |c|]
  exact mul_le_mul_of_nonneg_right this (abs_nonneg _)

/-! ### The cubic -/

variable (p0 p1 p2 : ℤ)

/-- The rational test: `p₀ ≠ 0` and no integer root in `[-|p₀|, |p₀|]`. -/
def noIntRootIn : Bool :=
  decide (p0 ≠ 0) && (List.range (2 * p0.natAbs + 1)).all fun i =>
    let z : ℤ := (i : ℤ) - p0.natAbs
    decide (z ^ 3 + p2 * z ^ 2 + p1 * z + p0 ≠ 0)

variable {p0 p1 p2}

/-- **The rational root theorem**, monic cubic: a rational root is an integer. -/
theorem int_of_rat_root {q : ℚ} (h : q ^ 3 + p2 * q ^ 2 + p1 * q + p0 = 0) :
    (q.num : ℚ) = q := by
  have hq : q = q.num / q.den := (Rat.num_div_den q).symm
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have key : (q.num : ℚ) ^ 3 + p2 * q.num ^ 2 * q.den + p1 * q.num * q.den ^ 2 +
      p0 * q.den ^ 3 = 0 := by
    rw [hq] at h
    field_simp at h
    linear_combination h
  have keyZ : q.num ^ 3 + p2 * q.num ^ 2 * q.den + p1 * q.num * q.den ^ 2 + p0 * q.den ^ 3 = 0 := by
    exact_mod_cast key
  have hdvd : (q.den : ℤ) ∣ q.num ^ 3 :=
    ⟨-(p2 * q.num ^ 2 + p1 * q.num * q.den + p0 * q.den ^ 2), by linear_combination keyZ⟩
  have hdvd' : q.den ∣ q.num.natAbs ^ 3 := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa [Int.natAbs_pow] using this
  have hcop : Nat.Coprime (q.num.natAbs ^ 3) q.den := Nat.Coprime.pow_left 3 q.reduced
  have hd1 : q.den = 1 := Nat.Coprime.eq_one_of_dvd hcop.symm hdvd'
  exact Rat.den_eq_one_iff q |>.mp hd1

/-- A passing `noIntRootIn` excludes rational roots. -/
theorem noRatRoot_of (h : noIntRootIn p0 p1 p2 = true) (q : ℚ) :
    q ^ 3 + p2 * q ^ 2 + p1 * q + p0 ≠ 0 := by
  intro hq
  simp only [noIntRootIn, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨hp0, hall⟩ := h
  have hz := int_of_rat_root hq
  set z : ℤ := q.num with hzdef
  have hzq : (z : ℚ) ^ 3 + p2 * z ^ 2 + p1 * z + p0 = 0 := by rw [hz]; exact hq
  have hzZ : z ^ 3 + p2 * z ^ 2 + p1 * z + p0 = 0 := by exact_mod_cast hzq
  have hdiv : z ∣ p0 := ⟨-(z ^ 2 + p2 * z + p1), by linear_combination hzZ⟩
  have hle : z.natAbs ≤ p0.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hp0)
    (Int.natAbs_dvd_natAbs.mpr hdiv)
  have := hall (z + p0.natAbs).toNat (by omega)
  rw [show (((z + p0.natAbs).toNat : ℕ) : ℤ) - p0.natAbs = z by omega] at this
  exact this hzZ

/-- **Independence** of `1, θ, θ²` over `ℚ`. -/
theorem cubic_indep {θ : ℝ} (hP : θ ^ 3 + p2 * θ ^ 2 + p1 * θ + p0 = 0)
    (hno : ∀ q : ℚ, q ^ 3 + p2 * q ^ 2 + p1 * q + p0 ≠ 0) {v0 v1 v2 : ℚ}
    (h : (v0 : ℝ) + v1 * θ + v2 * θ ^ 2 = 0) : v0 = 0 ∧ v1 = 0 ∧ v2 = 0 := by
  -- a rational value of `θ` is excluded
  have hrat : ∀ q : ℚ, θ ≠ q := fun q hθ => hno q (by
    have : ((q ^ 3 + p2 * q ^ 2 + p1 * q + p0 : ℚ) : ℝ) = 0 := by
      push_cast; rw [← hθ]; exact hP
    exact_mod_cast this)
  by_cases hv2 : v2 = 0
  · subst hv2
    by_cases hv1 : v1 = 0
    · subst hv1
      simp only [Rat.cast_zero, zero_mul, add_zero] at h
      exact ⟨by exact_mod_cast h, rfl, rfl⟩
    · exfalso
      refine hrat (-v0 / v1) ?_
      have hv1' : (v1 : ℝ) ≠ 0 := by exact_mod_cast hv1
      push_cast
      field_simp
      linear_combination h
  · exfalso
    have hv2' : (v2 : ℝ) ≠ 0 := by exact_mod_cast hv2
    set s : ℚ := -v1 / v2 with hs
    set t : ℚ := -v0 / v2 with ht
    have hθ2 : θ ^ 2 = s * θ + t := by
      rw [hs, ht]; push_cast; field_simp; linear_combination h
    set α : ℚ := s ^ 2 + t + p2 * s + p1 with hα
    set β : ℚ := s * t + p2 * t + p0 with hβ
    have hlin : (α : ℝ) * θ + β = 0 := by
      rw [hα, hβ]; push_cast; linear_combination hP - ((θ : ℝ) + s + p2) * hθ2
    by_cases hα0 : α = 0
    · have hβ0 : β = 0 := by
        rw [hα0] at hlin; push_cast at hlin; exact_mod_cast (by linarith : (β : ℝ) = 0)
      refine hno (-(s + p2)) ?_
      linear_combination (-(s + p2)) * hα0 + hβ0
    · have hα' : (α : ℝ) ≠ 0 := by exact_mod_cast hα0
      refine hrat (-β / α) ?_
      push_cast
      field_simp
      linear_combination hlin

/-! ### Norm and cofactor -/

variable (p0 p1 p2)

/-- The norm `N(u) = det M_u` of `β(u) = u₀ + u₁ θ + u₂ θ²`. -/
def cubN (u : Fin 3 → ℤ) : ℤ :=
  p0 ^ 2 * u 2 ^ 3 - p0 * p1 * u 1 * u 2 ^ 2 - 2 * p0 * p2 * u 0 * u 2 ^ 2 +
    p0 * p2 * u 1 ^ 2 * u 2 + 3 * p0 * u 0 * u 1 * u 2 - p0 * u 1 ^ 3 + p1 ^ 2 * u 0 * u 2 ^ 2 -
    p1 * p2 * u 0 * u 1 * u 2 - 2 * p1 * u 0 ^ 2 * u 2 + p1 * u 0 * u 1 ^ 2 +
    p2 ^ 2 * u 0 ^ 2 * u 2 - p2 * u 0 ^ 2 * u 1 + u 0 ^ 3

/-- The cofactor `Y(u) = y₀ + y₁ θ + y₂ θ²` (the first column of `adj M_u`). -/
noncomputable def cubY (θ : ℝ) (u : Fin 3 → ℤ) : ℝ :=
  ((-p0 * p2 * u 2 ^ 2 + p0 * u 1 * u 2 + p1 ^ 2 * u 2 ^ 2 - p1 * p2 * u 1 * u 2 -
      2 * p1 * u 0 * u 2 + p1 * u 1 ^ 2 + p2 ^ 2 * u 0 * u 2 - p2 * u 0 * u 1 + u 0 ^ 2 : ℤ) : ℝ) +
    ((-p0 * u 2 ^ 2 + p1 * p2 * u 2 ^ 2 - p2 ^ 2 * u 1 * u 2 + p2 * u 1 ^ 2 - u 0 * u 1 : ℤ) : ℝ) *
      θ +
    ((p1 * u 2 ^ 2 - p2 * u 1 * u 2 - u 0 * u 2 + u 1 ^ 2 : ℤ) : ℝ) * θ ^ 2

/-- `β(v) = v₀ + v₁ θ + v₂ θ²`. -/
noncomputable def cubB {K : Type*} [Field K] [Algebra K ℝ] (θ : ℝ) (v : Fin 3 → K) : ℝ :=
  algebraMap K ℝ (v 0) + algebraMap K ℝ (v 1) * θ + algebraMap K ℝ (v 2) * θ ^ 2

variable {p0 p1 p2}

theorem beta_mul_cof {θ : ℝ} (hP : θ ^ 3 + p2 * θ ^ 2 + p1 * θ + p0 = 0) (u : Fin 3 → ℤ) :
    ((u 0 : ℝ) + u 1 * θ + u 2 * θ ^ 2) * cubY p0 p1 p2 θ u = (cubN p0 p1 p2 u : ℝ) := by
  unfold cubY cubN
  push_cast
  linear_combination (-(p0 : ℝ) * u 2 ^ 3 + p1 * θ * u 2 ^ 3 + p1 * u 1 * u 2 ^ 2 -
    p2 * θ * u 1 * u 2 ^ 2 + p2 * u 0 * u 2 ^ 2 - p2 * u 1 ^ 2 * u 2 - θ * u 0 * u 2 ^ 2 +
    θ * u 1 ^ 2 * u 2 - 2 * u 0 * u 1 * u 2 + u 1 ^ 3) * hP

variable (p0 p1 p2) in
/-- The matrix of multiplication by `β(u)` on `(1, θ, θ²)`. -/
def mulMat (u : Fin 3 → ℤ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(u 0 : ℚ), -p0 * u 2, p0 * p2 * u 2 - p0 * u 1;
    u 1, -p1 * u 2 + u 0, -p0 * u 2 + p1 * p2 * u 2 - p1 * u 1;
    u 2, -p2 * u 2 + u 1, -p1 * u 2 + p2 ^ 2 * u 2 - p2 * u 1 + u 0]

theorem det_mulMat (u : Fin 3 → ℤ) : (mulMat p0 p1 p2 u).det = (cubN p0 p1 p2 u : ℚ) := by
  rw [Matrix.det_fin_three]
  simp only [mulMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const]
  unfold cubN
  push_cast
  ring

/-- **The norm does not vanish** on `ℤ³ \ 0`. -/
theorem cubN_ne_zero {θ : ℝ} (hP : θ ^ 3 + p2 * θ ^ 2 + p1 * θ + p0 = 0)
    (hno : ∀ q : ℚ, q ^ 3 + p2 * q ^ 2 + p1 * q + p0 ≠ 0) {u : Fin 3 → ℤ} (hu : u ≠ 0) :
    cubN p0 p1 p2 u ≠ 0 := by
  intro hN
  have hdet : (mulMat p0 p1 p2 u).det = 0 := by rw [det_mulMat, hN]; simp
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have e : ∀ i, (mulMat p0 p1 p2 u *ᵥ v) i = 0 := fun i => by rw [hv]; rfl
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  simp only [mulMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const] at e0 e1 e2
  have r0 := congrArg (fun x : ℚ => (x : ℝ)) e0
  have r1 := congrArg (fun x : ℚ => (x : ℝ)) e1
  have r2 := congrArg (fun x : ℚ => (x : ℝ)) e2
  push_cast at r0 r1 r2
  have hprod : ((u 0 : ℝ) + u 1 * θ + u 2 * θ ^ 2) * ((v 0 : ℝ) + v 1 * θ + v 2 * θ ^ 2) = 0 := by
    linear_combination r0 + θ * r1 + θ ^ 2 * r2 +
      (-(p2 : ℝ) * u 2 * v 2 + θ * u 2 * v 2 + u 1 * v 2 + u 2 * v 1) * hP
  rcases mul_eq_zero.mp hprod with hb | hb
  · obtain ⟨h0, h1, h2⟩ := cubic_indep hP hno (v0 := (u 0 : ℚ)) (v1 := (u 1 : ℚ))
      (v2 := (u 2 : ℚ)) (by push_cast; exact hb)
    apply hu
    funext i
    fin_cases i
    · exact_mod_cast h0
    · exact_mod_cast h1
    · exact_mod_cast h2
  · obtain ⟨h0, h1, h2⟩ := cubic_indep hP hno hb
    apply hv0
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

/-! ### The quadratic form of the cofactor -/

variable (p0 p1 p2)

/-- `H_l` of `Y(u) = Σ_l θ^l uᵀ H_l u` (symmetric, entries in `½ℤ`). -/
def cubicH (l : Fin 3) : Fin 3 → Fin 3 → ℚ :=
  match l with
  | 0 => !![1, -p2 / 2, (p2 ^ 2 - 2 * p1) / 2; -p2 / 2, p1, (p0 - p1 * p2) / 2;
      (p2 ^ 2 - 2 * p1) / 2, (p0 - p1 * p2) / 2, p1 ^ 2 - p0 * p2]
  | 1 => !![0, -1 / 2, 0; -1 / 2, p2, -p2 ^ 2 / 2; 0, -p2 ^ 2 / 2, p1 * p2 - p0]
  | 2 => !![0, 0, -1 / 2; 0, 1, -p2 / 2; -1 / 2, -p2 / 2, p1]

/-- `W_l = A H_l Aᵀ`. -/
def cubicW (A : Fin 3 → Fin 3 → ℤ) (l i j : Fin 3) : ℚ :=
  ∑ a : Fin 3, ∑ b : Fin 3, (A i a : ℚ) * A j b * cubicH p0 p1 p2 l a b

variable {p0 p1 p2}

theorem cubY_eq (θ : ℝ) (u : Fin 3 → ℤ) :
    cubY p0 p1 p2 θ u = ∑ a : Fin 3, ∑ b : Fin 3,
      (∑ l : Fin 3, (cubicH p0 p1 p2 l a b : ℝ) * θ ^ (l : ℕ)) * u a * u b := by
  simp only [cubY, cubicH, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Fin.val_zero, Fin.val_one, Fin.val_two]
  push_cast
  ring

theorem quad_transfer (h A : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ) :
    ∑ a : Fin 3, ∑ b : Fin 3, h a b * (∑ i : Fin 3, k i * A i a) * (∑ j : Fin 3, k j * A j b) =
      ∑ i : Fin 3, ∑ j : Fin 3, k i * k j * (∑ a : Fin 3, ∑ b : Fin 3, A i a * A j b * h a b) := by
  simp only [Fin.sum_univ_three]
  ring

theorem cubicW_eq (A : Fin 3 → Fin 3 → ℤ) (θ : ℝ) (i j : Fin 3) :
    ∑ a : Fin 3, ∑ b : Fin 3, (A i a : ℝ) * A j b *
        (∑ l : Fin 3, (cubicH p0 p1 p2 l a b : ℝ) * θ ^ (l : ℕ)) =
      (cubicW p0 p1 p2 A 0 i j : ℝ) + cubicW p0 p1 p2 A 1 i j * θ +
        cubicW p0 p1 p2 A 2 i j * θ ^ 2 := by
  simp only [cubicW, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
  push_cast
  ring

/-- `|Σ_{ij} k_i k_j W_ij| ≤ W̄ |k|₁²`. -/
theorem abs_quad_le (W : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ) {Wb : ℝ}
    (hW : ∀ i j, |W i j| ≤ Wb) :
    |∑ i : Fin 3, ∑ j : Fin 3, k i * k j * W i j| ≤ Wb * (∑ i : Fin 3, |k i|) ^ 2 := by
  have hWb : 0 ≤ Wb := (abs_nonneg _).trans (hW 0 0)
  calc |∑ i : Fin 3, ∑ j : Fin 3, k i * k j * W i j|
      ≤ ∑ i : Fin 3, ∑ j : Fin 3, |k i| * |k j| * Wb := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hW i j) (by positivity)
    _ = Wb * (∑ i : Fin 3, |k i|) ^ 2 := by
        simp only [Fin.sum_univ_three]
        ring

/-- `|w₀ + w₁ θ + w₂ θ²|` from above on `|θ - θc| ≤ θr`. -/
def polyAbsUp (w0 w1 w2 θc θr : ℚ) : ℚ :=
  |w0 + w1 * θc + w2 * θc ^ 2| + θr * (|w1| + |w2| * (2 * |θc| + θr))

theorem abs_poly_le {w0 w1 w2 θc θr : ℚ} {θ : ℝ} (hθ : |θ - θc| ≤ θr) :
    |(w0 : ℝ) + w1 * θ + w2 * θ ^ 2| ≤ (polyAbsUp w0 w1 w2 θc θr : ℝ) := by
  have e : (w0 : ℝ) + w1 * θ + w2 * θ ^ 2 =
      ((w0 : ℝ) + w1 * θc + w2 * (θc : ℝ) ^ 2) + (θ - θc) * (w1 + w2 * (θ + θc)) := by ring
  have hr0 : (0 : ℝ) ≤ θr := (abs_nonneg _).trans hθ
  have hs : |θ + (θc : ℝ)| ≤ 2 * |(θc : ℝ)| + θr := by
    calc |θ + (θc : ℝ)| = |(θ - θc) + 2 * θc| := by ring_nf
      _ ≤ |θ - θc| + |2 * (θc : ℝ)| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul, abs_two]; linarith
  rw [e]
  refine (abs_add_le _ _).trans ?_
  unfold polyAbsUp
  push_cast
  refine add_le_add le_rfl ?_
  rw [abs_mul]
  refine mul_le_mul hθ ?_ (abs_nonneg _) hr0
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hs (abs_nonneg _)

/-! ### The test and its soundness -/

/-- The determinant of a `3 × 3` integer matrix. -/
def det3 (A : Fin 3 → Fin 3 → ℤ) : ℤ :=
  A 0 0 * (A 1 1 * A 2 2 - A 1 2 * A 2 1) - A 0 1 * (A 1 0 * A 2 2 - A 1 2 * A 2 0) +
    A 0 2 * (A 1 0 * A 2 1 - A 1 1 * A 2 0)

/-- The vector `ω_i = (A_{i0} + A_{i1} θ + A_{i2} θ²)/D`. -/
noncomputable def cubicVec (A : Fin 3 → Fin 3 → ℤ) (D : ℚ) (θ : ℝ) : Fin 3 → ℝ :=
  fun i => ((A i 0 : ℝ) + A i 1 * θ + A i 2 * θ ^ 2) / D

variable (p0 p1 p2)

/-- **The rational test** of `(γ, 2)` for `cubicVec A D θ`, `P(θ) = 0`, `|θ - θc| ≤ θr`. -/
def cubicDioOk (θc θr : ℚ) (A : Fin 3 → Fin 3 → ℤ) (D γ : ℚ) : Bool :=
  noIntRootIn p0 p1 p2 && decide (det3 A ≠ 0) && decide (0 < D) && decide (0 < γ) &&
    decide (∀ i j : Fin 3, γ * D * polyAbsUp (cubicW p0 p1 p2 A 0 i j) (cubicW p0 p1 p2 A 1 i j)
      (cubicW p0 p1 p2 A 2 i j) θc θr ≤ 1)

variable {p0 p1 p2}

/-- **Soundness**: `cubicVec A D θ` is `(γ, 2)`-Diophantine. -/
theorem isDiophantine_of_cubicDioOk {θc θr : ℚ} {A : Fin 3 → Fin 3 → ℤ} {D γ : ℚ}
    (h : cubicDioOk p0 p1 p2 θc θr A D γ = true) {θ : ℝ}
    (hP : θ ^ 3 + p2 * θ ^ 2 + p1 * θ + p0 = 0) (hθ : |θ - θc| ≤ θr) :
    KAM.IsDiophantine (γ : ℝ) 2 (cubicVec A D θ) := by
  simp only [cubicDioOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hno, hdet⟩, hD⟩, hγ⟩, hW⟩ := h
  have hno' := noRatRoot_of hno
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
  intro k hk
  set u : Fin 3 → ℤ := fun j => ∑ i : Fin 3, k i * A i j with hu
  -- `u = Aᵀ k ≠ 0`
  have hu0 : u ≠ 0 := by
    intro h0
    set Mt : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of fun j i => (A i j : ℚ) with hMt
    have hk' : (fun i => (k i : ℚ)) ≠ 0 := by
      intro h1
      apply hk
      funext i
      have := congrFun h1 i
      simp only [Pi.zero_apply] at this
      simpa using this
    have hmv : Mt *ᵥ (fun i => (k i : ℚ)) = 0 := by
      funext j
      have := congrFun h0 j
      simp only [hu, Pi.zero_apply] at this
      simp only [hMt, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
      have e : ∑ i : Fin 3, (A i j : ℚ) * (k i : ℚ) = ((∑ i : Fin 3, k i * A i j : ℤ) : ℚ) := by
        push_cast; exact Finset.sum_congr rfl fun i _ => by ring
      rw [e, this]; simp
    have hd0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hk', hmv⟩
    apply hdet
    have : ((det3 A : ℤ) : ℚ) = 0 := by
      rw [← hd0, Matrix.det_fin_three]
      simp only [hMt, Matrix.of_apply, det3]
      push_cast
      ring
    exact_mod_cast this
  -- the dot product
  have hdot : ∑ i, (k i : ℝ) * cubicVec A D θ i =
      ((u 0 : ℝ) + u 1 * θ + u 2 * θ ^ 2) / D := by
    simp only [cubicVec, hu, Fin.sum_univ_three]
    push_cast
    field_simp
    ring
  -- the norm
  have hN := beta_mul_cof hP u
  have hN1 : (1 : ℝ) ≤ |(cubN p0 p1 p2 u : ℝ)| := by
    exact_mod_cast Int.one_le_abs (cubN_ne_zero hP hno' hu0)
  -- the cofactor: `|Y(u)| ≤ W̄ |k|₁²` with `W̄ = 1/(γ D)`
  have hγD : (0 : ℚ) < γ * D := mul_pos hγ hD
  set Wb : ℝ := ((1 / (γ * D) : ℚ) : ℝ) with hWbdef
  have hWij : ∀ i j, |∑ a : Fin 3, ∑ b : Fin 3, (A i a : ℝ) * A j b *
      (∑ l : Fin 3, (cubicH p0 p1 p2 l a b : ℝ) * θ ^ (l : ℕ))| ≤ Wb := by
    intro i j
    rw [cubicW_eq]
    refine (abs_poly_le hθ).trans ?_
    have hc := hW i j
    have : polyAbsUp (cubicW p0 p1 p2 A 0 i j) (cubicW p0 p1 p2 A 1 i j)
        (cubicW p0 p1 p2 A 2 i j) θc θr ≤ 1 / (γ * D) := by
      rw [le_div_iff₀ hγD, mul_comm]; exact hc
    rw [hWbdef]
    exact_mod_cast this
  have hY : |cubY p0 p1 p2 θ u| ≤ Wb * (∑ i : Fin 3, |(k i : ℝ)|) ^ 2 := by
    rw [cubY_eq]
    have hu' : ∀ a, ((u a : ℤ) : ℝ) = ∑ i : Fin 3, (k i : ℝ) * (A i a : ℝ) := fun a => by
      simp only [hu]; push_cast; rfl
    simp only [hu']
    rw [quad_transfer]
    exact abs_quad_le _ _ hWij
  -- conclusion
  set β : ℝ := (u 0 : ℝ) + u 1 * θ + u 2 * θ ^ 2 with hβ
  have hprod : 1 ≤ |β| * |cubY p0 p1 p2 θ u| := by rw [← abs_mul, hN]; exact hN1
  set S : ℝ := ∑ i : Fin 3, |(k i : ℝ)| with hS
  have hSpos : 0 < S := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hk
    exact lt_of_lt_of_le (abs_pos.mpr (by exact_mod_cast hj))
      (Finset.single_le_sum (f := fun i => |(k i : ℝ)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j))
  have h1 : 1 ≤ |β| * (Wb * S ^ 2) :=
    hprod.trans (mul_le_mul_of_nonneg_left hY (abs_nonneg _))
  have hWγD : Wb * ((γ : ℝ) * D) = 1 := by
    rw [hWbdef]; push_cast; field_simp
  rw [hdot, Real.rpow_two, abs_div, abs_of_pos hD', div_le_div_iff₀ (by positivity) hD']
  have h2 : (γ : ℝ) * D ≤ |β| * (Wb * S ^ 2) * ((γ : ℝ) * D) :=
    le_mul_of_one_le_left (by positivity) h1
  calc (γ : ℝ) * D ≤ |β| * (Wb * S ^ 2) * ((γ : ℝ) * D) := h2
    _ = |β| * S ^ 2 * (Wb * ((γ : ℝ) * D)) := by ring
    _ = |β| * S ^ 2 := by rw [hWγD, mul_one]

end KAM.CertificateSharp.Cubic

end
