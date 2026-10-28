/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.StepsSeq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The Normal Form Lemma: the induction (`nf-first`, `nf-case`, `nf-N`, `nf-induct`)

For `i ≤ N`, the invariant `NFInv i` makes step `i` an `IterHyp` (`nf_hyp`: admissibility, `nf-first`,
(6.2)) and gives `NFInv (i+1)` (`nf_inv_succ`: Case A of `nf-case` for `i = 0`, the induction claim
`εᵢ₊₁ ≤ εᵢ/4` with the decomposition norm of `nf-induct` for `i ≥ 1`). Design
`docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-8 (session 1).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.NormalForm

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

section Induct

variable {D : Set (Fin n → ℂ)} {r s K α L p ε : ℝ} {Λ : Set (Fin n → ℤ)}
  {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {N : ℕ}

/-- `N = ⌊κ/(12 ln 2)⌋` with `κ = 2πKs`: the floor facts. -/
theorem nf_floor (H : NFHyp D r s K α L p ε Λ h f)
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊) :
    (N : ℝ) * (12 * Real.log 2) ≤ 2 * Real.pi * K * s ∧
      2 * Real.pi * K * s < ((N : ℝ) + 1) * (12 * Real.log 2) ∧
      8 * (N : ℝ) ≤ 2 * Real.pi * K * s :=
  floor_facts (by linarith [H.hii]) hN

/-- (6.2) for `N ≥ 1`. -/
theorem nf_sixtwo (H : NFHyp D r s K α L p ε Λ h f)
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊) (hN1 : 1 ≤ N) :
    ε ≤ 2 * Real.pi * α * r * s / (2 ^ 10 * conjExp p * N) ∧
      iterU α p (nfEps1 α p r s ε) (r / (8 * N)) (s / (4 * N)) ≤ 1 / 2 ^ 8 := by
  have h6 := eps_le_sixtwo H.hp H.hα H.hK H.hr H.hs H.hε0 H.hi hN1 (nf_floor H hN).2.2
  exact ⟨h6, eps1_sixtwo H.hp H.hα H.hr H.hs H.hε0 hN1 h6⟩

/-- The decomposition norm of `g_{i-1}` is nonnegative and small (`nf-induct`, "size of `|g_{i-1}|_*`"). -/
theorem nf_star (H : NFHyp D r s K α L p ε Λ h f)
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊) {i : ℕ} (hi : i ≤ N) (hi1 : 1 ≤ i) :
    0 ≤ starNorm (nfR r N i) (nfS s N i) (nfRho r N i) (nfSig s N i) (nfRj r N i) (nfSj s N i)
        (nfMj (nfEps1 α p r s ε) ε i) ∧
      iterU α p (starNorm (nfR r N i) (nfS s N i) (nfRho r N i) (nfSig s N i) (nfRj r N i)
        (nfSj s N i) (nfMj (nfEps1 α p r s ε) ε i)) (nfRho r N i) (nfSig s N i) ≤ 1 / 2 ^ 4 := by
  have hN1 : 1 ≤ N := hi1.trans hi
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hε6, hε1⟩ := nf_sixtwo H hN hN1
  have hε₁0 := nfEps1_nonneg H.hp H.hα H.hr H.hs (ε := ε)
  have hρ : 0 < r / (8 * (N : ℝ)) := by have := H.hr; positivity
  have hσ : 0 < s / (4 * (N : ℝ)) := by have := H.hs; positivity
  rw [nfRho_ne_zero (by omega), nfSig_ne_zero (by omega)]
  set w : ℕ → ℝ := fun j => 1 / 2 * ((r / (8 * N)) / (nfR r N j - nfR r N i + r / (8 * N)) +
    (s / (4 * N)) / (nfS s N j - nfS s N i + s / (4 * N))) with hw
  have hsum : starNorm (nfR r N i) (nfS s N i) (r / (8 * N)) (s / (4 * N)) (nfRj r N i)
      (nfSj s N i) (nfMj (nfEps1 α p r s ε) ε i) =
      ∑ j ∈ Finset.range i, w j * nfB (nfEps1 α p r s ε) ε j := by
    unfold starNorm nfRj nfSj nfMj
    exact Fin.sum_univ_eq_sum_range (fun j => w j * nfB (nfEps1 α p r s ε) ε j) i
  rw [hsum]
  have hwpos : ∀ j ∈ Finset.range i, 0 ≤ w j := by
    intro j hj
    have hji : j ≤ i := (Finset.mem_range.mp hj).le
    have h1 : nfR r N i ≤ nfR r N j := nfR_anti H.hr.le N hji
    have h2 : nfS s N i ≤ nfS s N j := nfS_anti H.hs.le N hji
    simp only [hw]
    have a1 : 0 ≤ (r / (8 * N)) / (nfR r N j - nfR r N i + r / (8 * N)) :=
      div_nonneg hρ.le (by linarith)
    have a2 : 0 ≤ (s / (4 * N)) / (nfS s N j - nfS s N i + s / (4 * N)) :=
      div_nonneg hσ.le (by linarith)
    linarith
  refine ⟨Finset.sum_nonneg fun j hj => mul_nonneg (hwpos j hj)
    (nfB_nonneg hε₁0 H.hε0 j), ?_⟩
  refine star_small H.hp H.hα H.hr H.hs H.hε0 hN1 hε6 hε1 ?_
  refine star_sum_le H.hε0 hε₁0 (by positivity) i w ?_ ?_
  · intro _
    exact w0_le hN1 H.hr H.hs (nfR_le_three H.hr.le hi1) (nfS_le_two H.hs.le hi1)
  · intro j _ hji
    have h1 : nfR r N i ≤ nfR r N j := nfR_anti H.hr.le N hji.le
    have h2 : nfS s N i ≤ nfS s N j := nfS_anti H.hs.le N hji.le
    simp only [hw]
    have a1 : (r / (8 * N)) / (nfR r N j - nfR r N i + r / (8 * N)) ≤ 1 :=
      div_le_one_of_le₀ (by linarith) (by linarith)
    have a2 : (s / (4 * N)) / (nfS s N j - nfS s N i + s / (4 * N)) ≤ 1 :=
      div_le_one_of_le₀ (by linarith) (by linarith)
    linarith

end Induct

end KAM.NormalForm

end
