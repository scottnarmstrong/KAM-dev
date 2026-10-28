/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.Iterative
public import KAM.Nekhoroshev.NormalForm.Arith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The Normal Form Lemma: the step sequence (`bpN:p6:normal-form`, Case A)

`nfState i = (g_{i-1}, f_i)` by recursion (`g_i = iterG`, `f_{i+1} = iterF` with the losses
`ρᵢ, σᵢ` of `Arith`), the decomposition `g_{i-1} = ∑_{j<i} P_Λ T_K f_j` as an `IsDecomp` with
`Fin i` parts (`rⱼ = nfR j`, `Mⱼ = nfB j`), the invariant `NFInv i` and the induction claim:
step `i` is an `IterHyp` (`nf_hyp`) and `NFInv (i+1)` follows (`nf_inv_succ`). Design
`docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-8 (session 1).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.NormalForm

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

/-- The source premises of the Normal Form Lemma used by the construction. -/
structure NFHyp (D : Set (Fin n → ℂ)) (r s K α L p ε : ℝ) (Λ : Set (Fin n → ℤ))
    (h : (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : Prop where
  hp : 1 < p
  hα : 0 < α
  hK : 0 < K
  hL : 0 ≤ L
  hr : 0 < r
  hs : 0 < s
  hh : DifferentiableOn ℂ h (polyNbhd D r)
  hnr : IsNonresonant D K α Λ h
  hlip : FreqLipschitz D r L h
  hrad : K * L * r ≤ α / p
  hf : InClass D r s f
  hfb : WBound D r s f ε
  hε0 : 0 ≤ ε
  hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K)
  hii : 6 ≤ 2 * Real.pi * K * s

section Defs

variable (D : Set (Fin n → ℂ)) (r s K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
  (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (N : ℕ)

/-- `nfState i = (g_{i-1}, f_i)`: `g_{-1} = 0`, `f_0 = f`, `g_i = g_{i-1} + P_Λ T_K f_i`,
`f_{i+1} = H_i ∘ Φ_i - h - g_i` with the losses `(ρᵢ, σᵢ)` and radii `(rᵢ, sᵢ)` of `Arith`. -/
def nfState : ℕ → ((Fin n → ℂ) × (Fin n → ℂ) → ℂ) × ((Fin n → ℂ) × (Fin n → ℂ) → ℂ)
  | 0 => (fun _ => 0, f)
  | i + 1 =>
    (iterG K Λ (nfState i).1 (nfState i).2,
      iterF D (nfR r N i) (nfS s N i) (nfRho r N i) (nfSig s N i) K Λ h (nfState i).1
        (nfState i).2)

/-- `g_{i-1}`. -/
def nfG (i : ℕ) : (Fin n → ℂ) × (Fin n → ℂ) → ℂ := (nfState D r s K Λ h f N i).1

/-- `f_i`. -/
def nfF (i : ℕ) : (Fin n → ℂ) × (Fin n → ℂ) → ℂ := (nfState D r s K Λ h f N i).2

/-- The `i`-th canonical map `Φᵢ`. -/
def nfPhi (i : ℕ) : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) :=
  iterMap D (nfR r N i) (nfS s N i) (nfRho r N i) (nfSig s N i) K Λ h (nfF D r s K Λ h f N i)

/-- The parts of the decomposition of `g_{i-1}`: `P_Λ T_K f_j`, `j < i`. -/
def nfGj (i : ℕ) : Fin i → (Fin n → ℂ) × (Fin n → ℂ) → ℂ :=
  fun j => homRes K Λ (nfF D r s K Λ h f N j)

end Defs

/-- Radii of the parts. -/
def nfRj (r : ℝ) (N i : ℕ) : Fin i → ℝ := fun j => nfR r N j

/-- Widths of the parts. -/
def nfSj (s : ℝ) (N i : ℕ) : Fin i → ℝ := fun j => nfS s N j

/-- Bounds of the parts. -/
def nfMj (ε₁ ε : ℝ) (i : ℕ) : Fin i → ℝ := fun j => nfB ε₁ ε j

section Seq

variable {D : Set (Fin n → ℂ)} {r s K α L p ε : ℝ} {Λ : Set (Fin n → ℤ)}
  {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {N : ℕ}

theorem nfG_zero : nfG D r s K Λ h f N 0 = fun _ => 0 := rfl

theorem nfF_zero : nfF D r s K Λ h f N 0 = f := rfl

theorem nfG_succ (i : ℕ) :
    nfG D r s K Λ h f N (i + 1) = iterG K Λ (nfG D r s K Λ h f N i) (nfF D r s K Λ h f N i) := rfl

theorem nfF_succ (i : ℕ) :
    nfF D r s K Λ h f N (i + 1) =
      iterF D (nfR r N i) (nfS s N i) (nfRho r N i) (nfSig s N i) K Λ h (nfG D r s K Λ h f N i)
        (nfF D r s K Λ h f N i) := rfl

/-- `g_{i-1} = ∑_{j<i} P_Λ T_K f_j`. -/
theorem nfG_eq_sum (i : ℕ) :
    nfG D r s K Λ h f N i =
      fun z => ∑ j ∈ Finset.range i, homRes K Λ (nfF D r s K Λ h f N j) z := by
  induction i with
  | zero => funext z; simp [nfG_zero]
  | succ i ih =>
    funext z
    rw [nfG_succ, Finset.sum_range_succ, ← congrFun ih z]
    rfl

theorem nfB_nonneg {ε₁ ε : ℝ} (hε₁ : 0 ≤ ε₁) (hε : 0 ≤ ε) (i : ℕ) : 0 ≤ nfB ε₁ ε i := by
  cases i with
  | zero => exact hε
  | succ i => exact div_nonneg hε₁ (by positivity)

theorem nfB_le_eps1 {ε₁ ε : ℝ} (hε₁ : 0 ≤ ε₁) {i : ℕ} (hi : 1 ≤ i) : nfB ε₁ ε i ≤ ε₁ := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  exact div_le_self hε₁ (one_le_pow₀ (by norm_num))

/-- The invariant at step `i`: `f_i ∈ O(rᵢ, sᵢ)` with `|f_i| ≤ Bᵢ`, and the parts `P_Λ T_K f_j`
(`j < i`) are in their classes with their bounds. -/
def NFInv (D : Set (Fin n → ℂ)) (r s K α p ε : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (N i : ℕ) : Prop :=
  InClass D (nfR r N i) (nfS s N i) (nfF D r s K Λ h f N i) ∧
  WBound D (nfR r N i) (nfS s N i) (nfF D r s K Λ h f N i) (nfB (nfEps1 α p r s ε) ε i) ∧
  ∀ j < i, InClass D (nfR r N j) (nfS s N j) (homRes K Λ (nfF D r s K Λ h f N j)) ∧
    WBound D (nfR r N j) (nfS s N j) (homRes K Λ (nfF D r s K Λ h f N j))
      (nfB (nfEps1 α p r s ε) ε j)

theorem nfInv_zero (H : NFHyp D r s K α L p ε Λ h f) : NFInv D r s K α p ε Λ h f N 0 :=
  ⟨H.hf, H.hfb, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

/-- The decomposition of `g_{i-1}` (`gⱼ = P_Λ T_K f_j` on `(rⱼ, sⱼ)`, `Mⱼ = Bⱼ`). -/
theorem isDecomp_nfG (hr : 0 ≤ r) (hs : 0 ≤ s) {i : ℕ} (hinv : NFInv D r s K α p ε Λ h f N i) :
    IsDecomp D (nfR r N i) (nfS s N i) (nfG D r s K Λ h f N i) (nfGj D r s K Λ h f N i)
      (nfRj r N i) (nfSj s N i) (nfMj (nfEps1 α p r s ε) ε i) where
  eq_sum := by
    rw [nfG_eq_sum]
    funext z
    exact (Fin.sum_univ_eq_sum_range
      (fun j => homRes K Λ (nfF D r s K Λ h f N j) z) i).symm
  r_le j := nfR_anti hr N (Nat.le_of_lt j.2)
  s_le j := nfS_anti hs N (Nat.le_of_lt j.2)
  inClass j := (hinv.2.2 j j.2).1
  bound j := (hinv.2.2 j j.2).2

theorem FreqLipschitz.mono' {D : Set (Fin n → ℂ)} {r r' L : ℝ} {h : (Fin n → ℂ) → ℂ}
    (H : FreqLipschitz D r L h) (hr : r' ≤ r) : FreqLipschitz D r' L h :=
  fun I₀ hI₀ I hI hlt => H I₀ hI₀ I (polyNbhd_mono hr hI) (hlt.trans_le hr)

end Seq

end KAM.NormalForm

end
