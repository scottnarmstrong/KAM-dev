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

/-- Step `i ≤ N` is an `IterHyp` (admissibility, `nf-first` for `i = 0`, (6.2) for `i ≥ 1`). -/
theorem nf_hyp (H : NFHyp D r s K α L p ε Λ h f)
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊) {i : ℕ} (hi : i ≤ N)
    (hinv : NFInv D r s K α p ε Λ h f N i) :
    IterHyp D (nfR r N i) (nfS s N i) (nfRho r N i) (nfSig s N i) K α p
      (nfB (nfEps1 α p r s ε) ε i) Λ h (nfG D r s K Λ h f N i) (nfF D r s K Λ h f N i)
      (nfGj D r s K Λ h f N i) (nfRj r N i) (nfSj s N i) (nfMj (nfEps1 α p r s ε) ε i) := by
  have hρ := nfRho_pos H.hr hi
  have hσ := nfSig_pos H.hs hi
  have hρr := nfR_gt_two_rho H.hr hi
  have hσs := nfS_gt_two_sig H.hs hi
  have hσ0 := nfSig_nonneg H.hs.le N i
  have hsi : 0 < nfS s N i := by linarith
  have hRle : nfR r N i ≤ r := nfR_anti H.hr.le N (Nat.zero_le i)
  have hε₁0 := nfEps1_nonneg H.hp H.hα H.hr H.hs (ε := ε)
  have hu : iterU α p (nfB (nfEps1 α p r s ε) ε i) (nfRho r N i) (nfSig s N i) ≤ 1 / 4 := by
    rcases Nat.eq_zero_or_pos i with h0 | h1
    · subst h0
      have e1 : nfRho r N 0 = r / 8 := by simp [nfRho]
      have e2 : nfSig s N 0 = s / 6 := by simp [nfSig]
      rw [e1, e2]
      exact (iterU_first H.hp H.hα H.hK H.hr H.hs H.hε0 H.hi H.hii).trans (by norm_num)
    · have hN1 : 1 ≤ N := h1.trans_le hi
      have hρ' : 0 < r / (8 * (N : ℝ)) := by rw [← nfRho_ne_zero h1.ne']; exact hρ
      have hσ' : 0 < s / (4 * (N : ℝ)) := by rw [← nfSig_ne_zero h1.ne']; exact hσ
      rw [nfRho_ne_zero h1.ne', nfSig_ne_zero h1.ne']
      have hm := iterU_mono H.hp H.hα hρ' hσ' (nfB_le_eps1 hε₁0 h1 (ε := ε))
      have := (nf_sixtwo H hN hN1).2
      have h8 : (1 : ℝ) / 2 ^ 8 ≤ 1 / 4 := by norm_num
      linarith
  refine iterHyp_of_source H.hp H.hα H.hK.le H.hL hsi hρ hρr hσ hσs
    (H.hh.mono (polyNbhd_mono hRle)) H.hnr (H.hlip.mono' hRle) ?_
    (isDecomp_nfG H.hr.le H.hs.le hinv) hinv.1 hinv.2.1
    (nfB_nonneg hε₁0 H.hε0 i) ((small_iff_iterU H.hp H.hα hρ hσ).2 hu)
  calc K * L * nfR r N i ≤ K * L * r :=
        mul_le_mul_of_nonneg_left hRle (mul_nonneg H.hK.le H.hL)
    _ ≤ α / p := H.hrad

/-- The induction step: `NFInv i → NFInv (i+1)` for `i ≤ N` in Case A. -/
theorem nf_inv_succ (H : NFHyp D r s K α L p ε Λ h f)
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊)
    (hA : Real.exp (-(2 * Real.pi * K * s) / 6) ≤ iterU α p ε (r / 8) (s / 6)) {i : ℕ}
    (hi : i ≤ N) (hinv : NFInv D r s K α p ε Λ h f N i) :
    NFInv D r s K α p ε Λ h f N (i + 1) := by
  have IH := nf_hyp H hN hi hinv
  obtain ⟨-, c2, c3, c4⟩ := iterative_direct_c IH
  have hd := iterative_direct_d IH
  refine ⟨c4, ?_, fun j hj => ?_⟩
  · have hd' : WBound D (nfR r N (i + 1)) (nfS s N (i + 1)) (nfF D r s K Λ h f N (i + 1))
        (nfBound α p K (nfRho r N i) (nfSig s N i) (nfB (nfEps1 α p r s ε) ε i)
          (starNorm (nfR r N i) (nfS s N i) (nfRho r N i) (nfSig s N i) (nfRj r N i)
            (nfSj s N i) (nfMj (nfEps1 α p r s ε) ε i))) := hd
    refine hd'.mono le_rfl le_rfl ?_
    rcases Nat.eq_zero_or_pos i with h0 | h1
    · subst h0
      have e1 : nfRho r N 0 = r / 8 := by simp [nfRho]
      have e2 : nfSig s N 0 = s / 6 := by simp [nfSig]
      have e3 : starNorm (nfR r N 0) (nfS s N 0) (nfRho r N 0) (nfSig s N 0) (nfRj r N 0)
          (nfSj s N 0) (nfMj (nfEps1 α p r s ε) ε 0) = 0 := by simp [starNorm]
      have e4 : nfB (nfEps1 α p r s ε) ε 1 = nfEps1 α p r s ε := by simp [nfB]
      rw [e3, e1, e2, e4]
      exact nfBound_caseA H.hp H.hα H.hK H.hr H.hs H.hε0 H.hi H.hii hA
    · have hN1 : 1 ≤ N := h1.trans_le hi
      have hε₁0 := nfEps1_nonneg H.hp H.hα H.hr H.hs (ε := ε)
      have hρ := nfRho_pos H.hr hi
      have hσ := nfSig_pos H.hs hi
      obtain ⟨hS0, hS⟩ := nf_star H hN hi h1
      have hρ' : 0 < r / (8 * (N : ℝ)) := by rw [← nfRho_ne_zero h1.ne']; exact hρ
      have hσ' : 0 < s / (4 * (N : ℝ)) := by rw [← nfSig_ne_zero h1.ne']; exact hσ
      have hδ : iterU α p (nfB (nfEps1 α p r s ε) ε i) (nfRho r N i) (nfSig s N i) ≤ 1 / 2 ^ 8 := by
        rw [nfRho_ne_zero h1.ne', nfSig_ne_zero h1.ne']
        exact (iterU_mono H.hp H.hα hρ' hσ' (nfB_le_eps1 hε₁0 h1 (ε := ε))).trans
          (nf_sixtwo H hN hN1).2
      have hex : Real.exp (-(2 * Real.pi * K * nfSig s N i)) ≤ 1 / 8 := by
        rw [nfSig_ne_zero h1.ne']
        exact exp_sigma_le hN1 (nf_floor H hN).1
      have := induct_step H.hp H.hα hρ hσ (nfB_nonneg hε₁0 H.hε0 i) hS0 hδ hS hex
      refine this.trans_eq ?_
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp only [nfB]
      rw [pow_succ]
      field_simp
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · exact hinv.2.2 j hj'
    · exact ⟨c2, c3⟩

/-- All invariants up to step `N + 1` in Case A. -/
theorem nf_inv_all (H : NFHyp D r s K α L p ε Λ h f)
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊)
    (hA : Real.exp (-(2 * Real.pi * K * s) / 6) ≤ iterU α p ε (r / 8) (s / 6)) :
    ∀ i ≤ N + 1, NFInv D r s K α p ε Λ h f N i := by
  intro i
  induction i with
  | zero => exact fun _ => nfInv_zero H
  | succ i ih => exact fun hi => nf_inv_succ H hN hA (by omega) (ih (by omega))

end Induct

end KAM.NormalForm

end
