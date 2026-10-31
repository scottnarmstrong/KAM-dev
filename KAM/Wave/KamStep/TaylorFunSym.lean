/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorFun
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Symmetry of the weighted pairing (blueprint-W `bpW:w5:solve`, step `s-class`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepPair_swap`: if the weighted matrices satisfy `A_ij = A'_ji` then
`⟨A x, y⟩ = ⟨A' y, x⟩` for the weighted pairing `stepPr` (used for `D²F` symmetry of the field of a
Taylor polynomial: `P`, `P'` symmetric and `Q^T` the transpose of `Q`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- **Transposed matrices pair transposed**: if `B₁_ij = B₂_ji` then `⟨B₁x,y⟩₀ = ⟨B₂y,x⟩₀`. -/
theorem homPairL2_swap_of_entries {B₁ B₂ : HomOp}
    (hB : ∀ i j, kamEntry B₁ i j = kamEntry B₂ j i) (x y : HomL2) :
    homPairL2 (B₁ x) y = homPairL2 (B₂ y) x := by
  set S : HomL2 →L[ℂ] ℂ := ((homPairL2.flip y).comp B₁) - homPairL2 (B₂ y) with hS
  have h0 : S = 0 := by
    refine homCLM_eq_zero_of_basis S fun j => ?_
    have e1 : homPairL2 (B₁ (kamBasis ℂ j)) y = ∑' i : ℕ+, kamEntry B₁ i j * y i := by
      rw [homPairL2_apply, homPairF]
      rfl
    have e2 : homPairL2 (B₂ y) (kamBasis ℂ j) = ∑' i : ℕ+, kamEntry B₂ j i * y i := by
      rw [homPairL2_single_right]
      exact ((homOp_hasSum B₂ y j).tsum_eq).symm
    simp only [hS, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, e1, e2]
    rw [sub_eq_zero]
    exact tsum_congr fun i => by rw [hB i j]
  have := congrArg (fun L : HomL2 →L[ℂ] ℂ => L x) h0
  simp only [hS, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, sub_eq_zero] at this
  exact this

variable {a p pb : ℝ}

/-- The weighted pairing is the `D`-twisted unweighted one. -/
theorem stepPr_eq_homPairL2 (ha : 0 ≤ a) (hpp : 0 ≤ p + pb) (c z : HomL2) :
    stepPr ha hpp c z = homPairL2 (homLamDiag_gen ha hpp c) z := rfl

/-- `⟨A x, y⟩ = ⟨A' y, x⟩` for weighted pairings when the matrices of `A, A'` are transposes. -/
theorem stepPr_swap (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {A A' : HomOp}
    (h : ∀ i j, homNormalEntry_gen a p pb A i j = homNormalEntry_gen a p pb A' j i)
    (x y : HomL2) :
    stepPr ha (homPP hp hpb) (A x) y = stepPr ha (homPP hp hpb) (A' y) x := by
  rw [stepPr_eq_homPairL2, stepPr_eq_homPairL2]
  refine homPairL2_swap_of_entries (B₁ := homLamCLM_gen ha (homPP hp hpb) A)
    (B₂ := homLamCLM_gen ha (homPP hp hpb) A') (fun i j => ?_) x y
  rw [homLam_entry_eq_gen ha hp hpb, homLam_entry_eq_gen ha hp hpb, h i j, mul_comm]

end KAM.Wave
