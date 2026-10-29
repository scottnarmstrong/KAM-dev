/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowAverage
public import KAM.Planetary.Preparation.SlowDivisor

/-!
# Slow averaging: sup bound of the bracket `C + ΣΩρ/2π + Ẑ` (P11A-P7d)

`p11_slow_MW`: an `ε`-independent bound `p11SlowMW C` of `p11SlowW C Z` on the domain of `Z`,
given the sup bound of `Ẑ` and `η₁ ≤ 1`; it is the hypothesis `hMW` of `p11_slow_divisor`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric Filter
open scoped BigOperators
namespace KAM.Planetary

section MW

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- `‖C(J)‖ ≤ M_F` near `J₀` (`C` is the fast mean of `F` at `z = 0`). -/
theorem p11_C_norm_le (hC : P11SecularSpec D C) {J : P11CVec n}
    (hJ : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC)) : ‖C.C J‖ ≤ C.MF := by
  obtain ⟨-, -, hFb, -⟩ := secular_extract hC
  obtain ⟨-, -, -, -, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  rw [p11C_eq_fastMean hC hJ]
  unfold p11FastMean
  refine KAM.norm_torusAverage_le fun θ _ => ?_
  have hmem : (Fin.append (KAM.realInclusion n θ) (0 : P11CVec n),
      Fin.append J (0 : P11CVec n)) ∈ p11WorkingDom n C.J0 (2 * C.sigma) (2 * C.rC) C.rz := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := KAM.ofReal_mem_complexStrip (n := n) (ρ := 2 * C.sigma) (by linarith) θ
      simpa [Fin.append_left] using this
    · simpa [Fin.append_left] using mem_ball_iff_norm.1 hJ
    · simpa [Fin.append_right, show (fun _ : Fin n => (0:ℂ)) = 0 from rfl] using hrz0
    · simpa [Fin.append_right, show (fun _ : Fin n => (0:ℂ)) = 0 from rfl] using hrz0
  refine (hFb _ hmem).trans ?_
  have hc : 1 ≤ KAM.Weighted.coth (Real.pi * C.sigma) := by
    unfold KAM.Weighted.coth
    have hs : 0 < Real.sinh (Real.pi * C.sigma) := Real.sinh_pos_iff.2 (by positivity)
    rw [le_div_iff₀ hs, one_mul]
    exact (Real.sinh_lt_cosh _).le
  exact div_le_self (by linarith) (one_le_pow₀ hc)

/-- The `ε`-independent bound of the bracket `W`. -/
def p11SlowMW (C : P11SecularData n) : ℝ :=
  C.MF + n * (C.L * (Real.pi * C.rz ^ 2 / 16)) + 2 ^ (2 * n) * (C.MF / 16 + 1)

theorem p11SlowMW_nonneg (hC : P11SecularSpec D C) : 0 ≤ p11SlowMW C := by
  obtain ⟨-, -, hL1, -, -, -, -, hrz0, -, hMF⟩ := fast_consts hC
  unfold p11SlowMW
  positivity

theorem p11_slow_MW (hC : P11SecularSpec D C) {eps : ℝ} {Z : P11CVec (n + n) → ℂ}
    (hη : p11eta1 C eps ≤ 1) (hs1 : p11s1 C eps ≤ C.rC)
    (hZb : ∀ I ∈ p11SlowZDom C eps, ‖Z I‖ ≤ 2 ^ (2 * n) * (C.MF / 16 + p11eta1 C eps)) :
    ∀ I ∈ p11SlowZDom C eps, ‖p11SlowW C Z I‖ ≤ p11SlowMW C := by
  obtain ⟨-, -, -, -, hOm⟩ := secular_extract hC
  obtain ⟨-, -, hL1, hrC0, -, -, -, hrz0, hrz1, hMF⟩ := fast_consts hC
  intro I hI
  obtain ⟨hJ, hR⟩ := hI
  have hJ' : (fun i : Fin n => I (Fin.castAdd n i)) ∈
      ball (KAM.realInclusion n C.J0) (2 * C.rC) :=
    mem_ball_iff_norm.2 (by
      have := p11s1_le C eps
      linarith [p11s1_le C eps, hJ])
  have h1 := p11_C_norm_le hC hJ'
  have h2 : ‖∑ i : Fin n, C.Omega (fun j : Fin n => I (Fin.castAdd n j)) i / (2 * Real.pi) *
      I (Fin.natAdd n i)‖ ≤ n * (C.L * (Real.pi * C.rz ^ 2 / 16)) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i : Fin n, ‖C.Omega (fun j : Fin n => I (Fin.castAdd n j)) i / (2 * Real.pi) *
        I (Fin.natAdd n i)‖ ≤ C.L * (Real.pi * C.rz ^ 2 / 16) := by
      intro i
      rw [norm_mul]
      have hO := hOm _ hJ'
      have e : C.Omega (fun j : Fin n => I (Fin.castAdd n j)) i / (2 * Real.pi) =
          ((2 * Real.pi : ℂ)⁻¹ • C.Omega (fun j : Fin n => I (Fin.castAdd n j))) i := by
        simp [div_eq_inv_mul]
      rw [e]
      refine mul_le_mul ((norm_le_pi_norm _ i).trans hO) ?_ (norm_nonneg _) (by linarith)
      exact (norm_le_pi_norm _ i).trans hR.le
    refine (Finset.sum_le_sum fun i _ => this i).trans ?_
    simp
  have h3 := (hZb _ ⟨hJ, hR⟩).trans (by gcongr : 2 ^ (2 * n) * (C.MF / 16 + p11eta1 C eps) ≤
    2 ^ (2 * n) * (C.MF / 16 + 1))
  unfold p11SlowW p11SlowMW
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3).trans (le_of_eq ?_)
  ring

end MW

end KAM.Planetary

end
