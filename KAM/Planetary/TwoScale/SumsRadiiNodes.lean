/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.TheoremTorus

/-!
# Two-scale KAM: literal export of the radii node (GAP-PX)

Unsigned export stating the literal conclusion of `stepP:p3:sum-radii` from the original KAM
hypotheses `KamHyp`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

/-- `stepP:p3:sum-radii` from the original KAM hypotheses only: for `k ≥ 1`,
`ρ̂_k ≤ ρ̂_0 16^{-k}` and `s_k = s 12^{-k}`. -/
theorem sum_radii (_H : KamHyp D sbar p h f) {k : ℕ} (_hk : 1 ≤ k) :
    rhoHat (seq p k) ≤ rhoHat p * (16 : ℝ)⁻¹ ^ k ∧ (seq p k).s = p.s * (12 : ℝ)⁻¹ ^ k := by
  constructor
  · induction k with
    | zero => omega
    | succ m ih =>
      have hstep : rhoHat (seq p (m + 1)) ≤ rhoHat (seq p m) / 16 :=
        rhoHat_le_rho (seq p (m + 1))
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simpa using hstep.trans_eq (by ring)
      · have := ih hm
        calc rhoHat (seq p (m + 1)) ≤ rhoHat (seq p m) / 16 := hstep
          _ ≤ rhoHat p * (16 : ℝ)⁻¹ ^ m / 16 := by gcongr
          _ = rhoHat p * (16 : ℝ)⁻¹ ^ (m + 1) := by ring
  · clear _hk
    induction k with
    | zero => simp [seq]
    | succ m ih =>
      show (seq p m).s / 12 = _
      rw [ih]; ring

end KAM.Planetary
