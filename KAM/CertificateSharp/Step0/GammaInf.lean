/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Freq.SmallDivisorSum
public import KAM.Strip.CohomologicalL1Cert
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# A rational upper bound of `Γ_∞(ω, δ)` from a frequency box

`Γ_∞(ω, δ) = sup_{k≠0} e^{-2πδ|k|₁}/(2π|k·ω|)` (`KAM.smallDivisorSup`, SHARP-L9) is the constant
of the ℓ¹ cohomological estimate used by `CertModel.cohSolve`. `SupData.check` verifies over `ℚ`,
for `τ = 1`, `δ`, a cut-off `N` and a claim `Γ`:
* every mode `0 < |k|₁ ≤ N` (`KAM.modeBox`) has a positive box lower bound `L_k` of `|k·ω|`
  (`boxLb`, package C2) and `E₁^{|k|₁} ≤ Γ · 6.28 L_k`;
* the Diophantine tail `(N+1) E₁^{N+1} ≤ Γ · 6.28 γ` (`KAM.sdSupTail`);
* `1 ≤ 6.28 δ (N+1)`, and `E₁ ≥ e^{-2πδ}` by the Taylor test of `SdsData.expLow`.

`supBound_sound`: for every `ω` in the box that is `(γ, 1)`-Diophantine, `Γ_∞(ω, δ) ≤ Γ` (real
analysis: `KAM.smallDivisorSup_le_box_tail`). The cost is `#modeBox ≈ 2N²` for `n = 2`; the
fibered certificate `KAM.smallDivisorSup_snoc_le` (one entry per `k'`) is the cheaper route for
clock frequencies and is not wired here.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Certificate

variable {n : ℕ}

/-- The data of a `Γ_∞` claim: box, Diophantine `γ` (`τ = 1`), `δ`, cut-off, Taylor degree, the
exponential bound `E₁ ≥ e^{-2πδ}` and the claimed `Γ`. -/
structure SupData where
  /-- The frequency box. -/
  box : FreqBox
  /-- The Diophantine constant (`τ = 1`). -/
  γ : ℚ
  /-- The loss `δ` of `Γ_∞(ω, δ)`. -/
  δ : ℚ
  /-- The mode cut-off. -/
  N : ℕ
  /-- The degree of the exponential lower polynomial. -/
  J : ℕ
  /-- A rational upper bound of `e^{-2πδ}`. -/
  E1 : ℚ
  /-- The claimed upper bound of `Γ_∞(ω, δ)`. -/
  claim : ℚ

namespace SupData

variable (d : SupData)

/-- The same data as a small-divisor-sum record (for its exponential test). -/
def toSds : SdsData := { box := d.box, γ := d.γ, δ := d.δ, N := d.N, J := d.J, E1 := d.E1 }

/-- The side conditions, over `ℚ`. -/
def check : Bool :=
  decide (0 < d.γ) && decide (0 < d.δ) && decide (1 ≤ 628 / 100 * d.δ * (d.N + 1)) &&
    decide (1 ≤ d.E1 * d.toSds.expLow) &&
    decide (((d.N : ℚ) + 1) * d.E1 ^ (d.N + 1) ≤ d.claim * (628 / 100 * d.γ)) &&
    decide (∀ k ∈ modeBox n d.N,
      0 < boxLb d.box k ∧ d.E1 ^ modeNat k ≤ d.claim * (628 / 100 * boxLb d.box k))

end SupData

/-- **Soundness of the rational `Γ_∞` bound.** -/
theorem supBound_sound (d : SupData) (h : d.check (n := n) = true) {ω : Fin n → ℝ}
    (hω : FreqEncloses n d.box ω) (hdio : IsDiophantine (d.γ : ℝ) 1 ω) :
    smallDivisorSup ω (d.δ : ℝ) ≤ (d.claim : ℝ) := by
  simp only [SupData.check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hγ, hδ⟩, hN⟩, hE1⟩, htail⟩, hbox⟩ := h
  have hγ' : (0 : ℝ) < d.γ := by exact_mod_cast hγ
  have hδ' : (0 : ℝ) < d.δ := by exact_mod_cast hδ
  have hpi := Real.pi_gt_d2
  have hE : Real.exp (-(2 * Real.pi * d.δ)) ≤ (d.E1 : ℝ) := exp_neg_le_E1 d.toSds hδ' hE1
  have hEj : ∀ j : ℕ, Real.exp (-(2 * Real.pi * d.δ) * j) ≤ (d.E1 : ℝ) ^ j := fun j => by
    calc Real.exp (-(2 * Real.pi * d.δ) * j) = Real.exp (-(2 * Real.pi * d.δ)) ^ j := by
          rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ (d.E1 : ℝ) ^ j := pow_le_pow_left₀ (Real.exp_pos _).le hE j
  have hN' : (1 : ℝ) ≤ 2 * Real.pi * d.δ * (d.N + 1) := by
    have : (1 : ℝ) ≤ 628 / 100 * d.δ * (d.N + 1) := by
      have h := (Rat.cast_le (K := ℝ)).mpr hN
      push_cast at h
      exact h
    have hN0 : (0 : ℝ) ≤ (d.N : ℝ) + 1 := by positivity
    nlinarith
  have key := smallDivisorSup_le_box_tail hdio hγ' zero_le_one hN'
    (fun k => (boxLb d.box k : ℝ))
    (fun k hk => ⟨by exact_mod_cast (hbox k hk).1, boxLb_le hω k⟩)
    (fun j => (d.E1 : ℝ) ^ j) hEj (B := (d.claim : ℝ)) (fun k hk => by
      obtain ⟨hL, hEk⟩ := hbox k hk
      have hL' : (0 : ℝ) < boxLb d.box k := by exact_mod_cast hL
      have hEk' : (d.E1 : ℝ) ^ modeNat k ≤ d.claim * (628 / 100 * boxLb d.box k) := by
        have h := (Rat.cast_le (K := ℝ)).mpr hEk
        push_cast at h
        exact h
      have hc0 : (0 : ℝ) ≤ d.claim := by
        have h0 : (0 : ℝ) ≤ (d.E1 : ℝ) ^ modeNat k :=
          pow_nonneg ((Real.exp_pos _).le.trans hE) _
        by_contra hneg
        push Not at hneg
        nlinarith
      show (d.E1 : ℝ) ^ modeNat k / (2 * Real.pi * boxLb d.box k) ≤ d.claim
      rw [div_le_iff₀ (by positivity)]
      have h2 : (628 / 100 : ℝ) * boxLb d.box k ≤ 2 * Real.pi * boxLb d.box k :=
        mul_le_mul_of_nonneg_right (by linarith) hL'.le
      have h3 := mul_le_mul_of_nonneg_left h2 hc0
      linarith)
  refine key.trans (max_le le_rfl ?_)
  -- the tail
  have htail' : ((d.N : ℝ) + 1) * (d.E1 : ℝ) ^ (d.N + 1) ≤ d.claim * (628 / 100 * d.γ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr htail
    push_cast at h
    exact h
  have hc0 : (0 : ℝ) ≤ d.claim := by
    have h0 : (0 : ℝ) ≤ ((d.N : ℝ) + 1) * (d.E1 : ℝ) ^ (d.N + 1) :=
      mul_nonneg (by positivity) (pow_nonneg ((Real.exp_pos _).le.trans hE) _)
    by_contra hneg
    push Not at hneg
    nlinarith
  have hexp : Real.exp (-(2 * Real.pi * d.δ) * ((d.N : ℝ) + 1)) ≤ (d.E1 : ℝ) ^ (d.N + 1) := by
    have := hEj (d.N + 1)
    push_cast at this
    exact this
  unfold sdSupTail
  rw [Real.rpow_one, div_le_iff₀ (by positivity)]
  have hN0 : (0 : ℝ) ≤ (d.N : ℝ) + 1 := by positivity
  calc ((d.N : ℝ) + 1) * Real.exp (-(2 * Real.pi * d.δ) * ((d.N : ℝ) + 1))
      ≤ ((d.N : ℝ) + 1) * (d.E1 : ℝ) ^ (d.N + 1) := mul_le_mul_of_nonneg_left hexp hN0
    _ ≤ d.claim * (628 / 100 * d.γ) := htail'
    _ ≤ d.claim * (2 * Real.pi * d.γ) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        nlinarith

end KAM.CertificateSharp

end
