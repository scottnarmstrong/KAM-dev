/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Normal.Analysis.SineProducts

/-!
# The selection rule for the quartic overlaps `g_{ijkl}`
(local helper for blueprint `bpW:w0n:cubic-bound`, step `stepW:w0n:selection`; the closed form is
`bpW:w0n:quartic-coeff`, whose own package is separate)

Infrastructure used by several nodes; the dependency graph is still being built.

`KAM.Wave.waveQuartic_eq_signed` is the signed form (`bpW:w0n:g-signed`)
`g_{ijkl} = (1/2π) Σ_{ε ∈ {±1}³} s(ε) [l = ε₁ i + ε₂ j + ε₃ k]`, `s(ε) = -ε₁ε₂ε₃`, and
`KAM.Wave.abs_waveQuartic_le_signs` the consequence `|g_{ijkl}| ≤ (1/2π) Σ_ε [l = ε₁ i + ε₂ j + ε₃
k]`.
Both are proved here directly from the product-to-sum formula, so that no other package is
needed.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

/-- The sign `±1` attached to a Boolean. -/
def waveSign (b : Bool) : ℤ := if b then 1 else -1

lemma wave_integral_cos_mul_cos_int (A B : ℤ) :
    ∫ x in (0 : ℝ)..π, Real.cos (A * x) * Real.cos (B * x)
      = (π / 2) * ((if A = B then 1 else 0) + (if A = -B then 1 else 0)) := by
  have hc1 : ∀ n : ℤ, IntervalIntegrable (fun x : ℝ => Real.cos (n * x)) MeasureTheory.volume 0 π :=
    fun n => (by fun_prop : Continuous fun x : ℝ => Real.cos (n * x)).intervalIntegrable _ _
  have e : ∀ x : ℝ, Real.cos (A * x) * Real.cos (B * x) =
      (1 / 2) * (Real.cos (((A - B : ℤ) : ℝ) * x) + Real.cos (((A + B : ℤ) : ℝ) * x)) := by
    intro x
    push_cast
    have h1 : ((A : ℝ) - B) * x = A * x - B * x := by ring
    have h2 : ((A : ℝ) + B) * x = A * x + B * x := by ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hc1 _) (hc1 _),
    wave_integral_cos_int_mul, wave_integral_cos_int_mul]
  have h1 : (A - B = 0) ↔ (A = B) := by omega
  have h2 : (A + B = 0) ↔ (A = -B) := by omega
  simp only [h1, h2]
  split_ifs <;> ring

/-- Four-fold product of sine modes as a product of two differences of cosines. -/
lemma wave_sineMode_mul4_eq (i j k l : ℕ+) (x : ℝ) :
    sineMode i x * sineMode j x * sineMode k x * sineMode l x =
      (1 / π ^ 2) *
        ((Real.cos ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) * x) -
            Real.cos ((((i : ℕ) : ℤ) + ((j : ℕ) : ℤ) : ℤ) * x)) *
          (Real.cos ((((k : ℕ) : ℤ) - ((l : ℕ) : ℤ) : ℤ) * x) -
            Real.cos ((((k : ℕ) : ℤ) + ((l : ℕ) : ℤ) : ℤ) * x))) := by
  have hpi := Real.pi_pos
  have h1 := Real.two_mul_sin_mul_sin ((i : ℝ) * x) ((j : ℝ) * x)
  have h2 := Real.two_mul_sin_mul_sin ((k : ℝ) * x) ((l : ℝ) * x)
  have hs : Real.sqrt (2 / π) * Real.sqrt (2 / π) = 2 / π := Real.mul_self_sqrt (by positivity)
  have c1 : ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : ℝ) * x = (i : ℝ) * x - (j : ℝ) * x := by
    push_cast; ring
  have c2 : ((((i : ℕ) : ℤ) + ((j : ℕ) : ℤ) : ℤ) : ℝ) * x = (i : ℝ) * x + (j : ℝ) * x := by
    push_cast; ring
  have c3 : ((((k : ℕ) : ℤ) - ((l : ℕ) : ℤ) : ℤ) : ℝ) * x = (k : ℝ) * x - (l : ℝ) * x := by
    push_cast; ring
  have c4 : ((((k : ℕ) : ℤ) + ((l : ℕ) : ℤ) : ℤ) : ℝ) * x = (k : ℝ) * x + (l : ℝ) * x := by
    push_cast; ring
  rw [c1, c2, c3, c4, ← h1, ← h2]
  unfold sineMode
  have e : Real.sqrt (2 / π) * Real.sin (↑↑i * x) * (Real.sqrt (2 / π) * Real.sin (↑↑j * x)) *
        (Real.sqrt (2 / π) * Real.sin (↑↑k * x)) * (Real.sqrt (2 / π) * Real.sin (↑↑l * x)) =
      (Real.sqrt (2 / π) * Real.sqrt (2 / π)) * (Real.sqrt (2 / π) * Real.sqrt (2 / π)) *
        (Real.sin (↑↑i * x) * Real.sin (↑↑j * x) * (Real.sin (↑↑k * x) * Real.sin (↑↑l * x))) := by
    ring
  rw [e, hs]
  field_simp

/-- The bracket form of the quartic overlap (product-to-sum, cosine integrals). -/
lemma waveQuartic_eq_brackets (i j k l : ℕ+) :
    waveQuartic i j k l = (1 / (2 * π)) *
      (((if ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) = ((k : ℕ) : ℤ) - ((l : ℕ) : ℤ) then (1 : ℝ) else 0) +
          (if ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) = -(((k : ℕ) : ℤ) - ((l : ℕ) : ℤ)) then 1 else 0))
        - ((if ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) = ((k : ℕ) : ℤ) + ((l : ℕ) : ℤ) then 1 else 0) +
          (if ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) = -(((k : ℕ) : ℤ) + ((l : ℕ) : ℤ)) then 1 else 0))
        - ((if ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ) = ((k : ℕ) : ℤ) - ((l : ℕ) : ℤ) then 1 else 0) +
          (if ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ) = -(((k : ℕ) : ℤ) - ((l : ℕ) : ℤ)) then 1 else 0))
        + ((if ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ) = ((k : ℕ) : ℤ) + ((l : ℕ) : ℤ) then 1 else 0) +
          (if ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ) = -(((k : ℕ) : ℤ) + ((l : ℕ) : ℤ)) then 1 else 0))) :=
              by
  have hpi := Real.pi_pos
  have hc1 : ∀ A B : ℤ, IntervalIntegrable (fun x : ℝ => Real.cos (A * x) * Real.cos (B * x))
      MeasureTheory.volume 0 π := fun A B =>
    (by fun_prop : Continuous fun x : ℝ => Real.cos (A * x) * Real.cos (B * x)).intervalIntegrable
        _ _
  unfold waveQuartic
  simp_rw [wave_sineMode_mul4_eq]
  rw [intervalIntegral.integral_const_mul]
  generalize ((i : ℕ) : ℤ) = I'
  generalize ((j : ℕ) : ℤ) = J'
  generalize ((k : ℕ) : ℤ) = K'
  generalize ((l : ℕ) : ℤ) = L'
  have ex : ∀ x : ℝ, (Real.cos (((I' - J' : ℤ) : ℝ) * x) - Real.cos (((I' + J' : ℤ) : ℝ) * x)) *
        (Real.cos (((K' - L' : ℤ) : ℝ) * x) - Real.cos (((K' + L' : ℤ) : ℝ) * x)) =
      Real.cos (((I' - J' : ℤ) : ℝ) * x) * Real.cos (((K' - L' : ℤ) : ℝ) * x)
        - Real.cos (((I' - J' : ℤ) : ℝ) * x) * Real.cos (((K' + L' : ℤ) : ℝ) * x)
        - Real.cos (((I' + J' : ℤ) : ℝ) * x) * Real.cos (((K' - L' : ℤ) : ℝ) * x)
        + Real.cos (((I' + J' : ℤ) : ℝ) * x) * Real.cos (((K' + L' : ℤ) : ℝ) * x) :=
    fun x => by ring
  simp_rw [ex]
  rw [intervalIntegral.integral_add (((hc1 _ _).sub (hc1 _ _)).sub (hc1 _ _)) (hc1 _ _),
    intervalIntegral.integral_sub ((hc1 _ _).sub (hc1 _ _)) (hc1 _ _),
    intervalIntegral.integral_sub (hc1 _ _) (hc1 _ _),
    wave_integral_cos_mul_cos_int, wave_integral_cos_mul_cos_int, wave_integral_cos_mul_cos_int,
    wave_integral_cos_mul_cos_int]
  field_simp

lemma waveSigned_indicator_alg (I J K L : ℤ) :
    ∑ ε : Bool × Bool × Bool,
      ((-(waveSign ε.1 * waveSign ε.2.1 * waveSign ε.2.2) : ℤ) : ℝ) *
        (if L = waveSign ε.1 * I + waveSign ε.2.1 * J + waveSign ε.2.2 * K then (1 : ℝ) else 0)
    = ((if I - J = K - L then 1 else 0) + (if I - J = -(K - L) then 1 else 0))
      - ((if I - J = K + L then 1 else 0) + (if I - J = -(K + L) then 1 else 0))
      - ((if I + J = K - L then 1 else 0) + (if I + J = -(K - L) then 1 else 0))
      + ((if I + J = K + L then 1 else 0) + (if I + J = -(K + L) then 1 else 0)) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, waveSign]
  simp only [ite_true, Bool.false_eq_true, ite_false]
  have e1 : (L = 1 * I + 1 * J + 1 * K) ↔ (I + J = -(K - L)) := by omega
  have e2 : (L = 1 * I + 1 * J + -1 * K) ↔ (I + J = K + L) := by omega
  have e3 : (L = 1 * I + -1 * J + 1 * K) ↔ (I - J = -(K - L)) := by omega
  have e4 : (L = 1 * I + -1 * J + -1 * K) ↔ (I - J = K + L) := by omega
  have e5 : (L = -1 * I + 1 * J + 1 * K) ↔ (I - J = K - L) := by omega
  have e6 : (L = -1 * I + 1 * J + -1 * K) ↔ (I - J = -(K + L)) := by omega
  have e7 : (L = -1 * I + -1 * J + 1 * K) ↔ (I + J = K - L) := by omega
  have e8 : (L = -1 * I + -1 * J + -1 * K) ↔ (I + J = -(K + L)) := by omega
  simp only [e1, e2, e3, e4, e5, e6, e7, e8]
  push_cast
  ring

/-- The signed form of the quartic overlap (`bpW:w0n:g-signed`). -/
theorem waveQuartic_eq_signed (i j k l : ℕ+) :
    waveQuartic i j k l = (1 / (2 * π)) * ∑ ε : Bool × Bool × Bool,
      ((-(waveSign ε.1 * waveSign ε.2.1 * waveSign ε.2.2) : ℤ) : ℝ) *
        (if ((l : ℕ) : ℤ) = waveSign ε.1 * ((i : ℕ) : ℤ) + waveSign ε.2.1 * ((j : ℕ) : ℤ)
            + waveSign ε.2.2 * ((k : ℕ) : ℤ) then 1 else 0) := by
  rw [waveQuartic_eq_brackets, waveSigned_indicator_alg]

lemma abs_waveSign_prod (ε : Bool × Bool × Bool) :
    |((-(waveSign ε.1 * waveSign ε.2.1 * waveSign ε.2.2) : ℤ) : ℝ)| = 1 := by
  rcases ε with ⟨b1, b2, b3⟩
  cases b1 <;> cases b2 <;> cases b3 <;> simp [waveSign]

/-- `|g_{ijkl}| ≤ (1/2π) Σ_ε [l = ε₁ i + ε₂ j + ε₃ k]` (`bpW:w0n:g-signed`). -/
theorem abs_waveQuartic_le_signs (i j k l : ℕ+) :
    |waveQuartic i j k l| ≤ (1 / (2 * π)) * ∑ ε : Bool × Bool × Bool,
      (if ((l : ℕ) : ℤ) = waveSign ε.1 * ((i : ℕ) : ℤ) + waveSign ε.2.1 * ((j : ℕ) : ℤ)
            + waveSign ε.2.2 * ((k : ℕ) : ℤ) then (1 : ℝ) else 0) := by
  have hpi := Real.pi_pos
  rw [waveQuartic_eq_signed, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * π))]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [abs_mul, abs_waveSign_prod, one_mul]
  split_ifs <;> simp

end KAM.Wave

end
