/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.Divisor

/-!
# The generating Hamiltonian: coefficients (blueprint-W `bpW:w3:Fdef`, `bpW:w3:F` Step Coefficients)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-DIVISOR-F, blueprint labels `bpW:w3:Fdef`, `bpW:w3:F`.

`birkFx x = 𝔤_x / δ_x` for `x ∈ 𝒯` not paired and `0` otherwise (Lean: division by `0` is `0`);
`birkFcoef = i δ_* f_x`. `birkFcoef_isCoef`: `c` satisfies `IsBirkQuartCoef` (symmetric, `c_{-x} = conj c_x`,
`|c_x| ≤ |𝔤_x|`), so `𝔉 = δ_*⁻¹ 𝔓_c`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m)

/-- `f_x = 𝔤_x / δ_x` on `𝒯 ∖ paired`, `0` elsewhere. -/
def birkFx (x : Fin 4 → BirkIdx) : ℝ :=
  open Classical in if x ∈ birkTanSet ∧ ¬ birkPaired x then birkG m hm x / birkDivisor m hm x else 0

/-- The coefficient `c_x = i δ_* f_x` of `𝔉 = δ_*⁻¹ 𝔓_c`. -/
def birkFcoef (x : Fin 4 → BirkIdx) : ℂ :=
  Complex.I * (birkDeltaStar m : ℂ) * ((birkFx m hm x : ℝ) : ℂ)

theorem birkDivisor_perm (σ : Equiv.Perm (Fin 4)) (x : Fin 4 → BirkIdx) :
    birkDivisor m hm (fun i => x (σ i)) = birkDivisor m hm x :=
  Equiv.sum_comp σ (fun t => birkLam m hm (x t))

theorem birkLam_neg (q : BirkIdx) : birkLam m hm (birkNeg q) = -birkLam m hm q := by
  obtain ⟨b, j⟩ := q; cases b <;> simp [birkLam, birkNeg]

theorem birkDivisor_neg (x : Fin 4 → BirkIdx) :
    birkDivisor m hm (birkNegPi x) = -birkDivisor m hm x := by
  unfold birkDivisor
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun t _ => birkLam_neg m hm (x t)

theorem birkFx_perm (σ : Equiv.Perm (Fin 4)) (x : Fin 4 → BirkIdx) :
    birkFx m hm (fun i => x (σ i)) = birkFx m hm x := by
  classical
  have hT : (fun i => x (σ i)) ∈ birkTanSet ↔ x ∈ birkTanSet :=
    ⟨fun ⟨t, ht⟩ => ⟨σ t, ht⟩, fun ⟨t, ht⟩ => ⟨σ.symm t, by simpa using ht⟩⟩
  unfold birkFx
  simp only [hT, birkPaired_perm, birkG_perm, birkDivisor_perm]

theorem birkFx_neg (x : Fin 4 → BirkIdx) : birkFx m hm (birkNegPi x) = -birkFx m hm x := by
  classical
  have hT : birkNegPi x ∈ birkTanSet ↔ x ∈ birkTanSet :=
    ⟨fun ⟨t, ht⟩ => ⟨t, by simpa [birkNegPi] using ht⟩, fun ⟨t, ht⟩ => ⟨t, by simpa [birkNegPi] using ht⟩⟩
  unfold birkFx
  simp only [hT, birkPaired_neg, birkG_neg, birkDivisor_neg]
  by_cases h : x ∈ birkTanSet ∧ ¬ birkPaired x
  · simp [h, div_neg]
  · simp [h]

theorem abs_birkFx_le (x : Fin 4 → BirkIdx) : |birkFx m hm x| ≤ |birkG m hm x| / birkDeltaStar m := by
  classical
  have hs : 0 < birkDeltaStar m := by
    unfold birkDeltaStar; positivity
  unfold birkFx
  by_cases h : x ∈ birkTanSet ∧ ¬ birkPaired x
  · rw [if_pos h, abs_div]
    by_cases hg : birkG m hm x = 0
    · simp [hg]
    · have := birk_divisor_bound_tan m hm x h.1 hg h.2
      exact div_le_div_of_nonneg_left (abs_nonneg _) hs this
  · rw [if_neg h]; simp; positivity

theorem birkFcoef_isCoef : IsBirkQuartCoef m hm (birkFcoef m hm) where
  perm σ x := by simp only [birkFcoef, birkFx_perm]
  conj_neg x := by
    simp only [birkFcoef, birkFx_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast; ring
  bound x := by
    have hs : 0 < birkDeltaStar m := by unfold birkDeltaStar; positivity
    unfold birkFcoef
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hs]
    have := abs_birkFx_le m hm x
    rw [le_div_iff₀ hs] at this
    linarith

end KAM.Wave

end
