/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.IterArith
public import KAM.Wave.Measure.Pair
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the conditions with `k = 0` (blueprint `bpW:w6:k0`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:k0` (milestone W6).

Normal modes are indexed as in W7 (`KAM/Wave/Measure`): `j : ℕ` with Dirichlet label
`normLab j = j + 3`, which is W5's `j + 2` for W5's index `j ≥ 1`; so W5's weight `(j+2)^{1/2}` is
`normLab j ^ (1/2)`.

`w6K0_of_increments` is the lemma in the inductive form in which the proof of
`bpW:w6:iter-lemma`/`bpW:w6:convergence` (step `c-ind`) uses it at stage `ν`: for the sequences of
Definition `bpW:w6:sequences` with `ε₀ ≤ γ₀ α₀ σ₀^t`, sets `Π_0 ⊇ Π_1 ⊇ …`, normal frequencies `Ω_μ`
whose increments `sup_j (j+2)^{1/2} |Ω_{μ+1,j} - Ω_{μ,j}| ≤ 3ε_μ` on `Π_μ` hold at the earlier
stages `μ < ν` (the bound of the iterative lemma at those stages), and
`|⟨l, Ω_0⟩| ≥ 2β₀⟨l⟩` (`l ∈ Λ`) on `Π_0` with `β₀ ≥ α₀`, `8ε₀ ≤ β₀`: the Melnikov condition
with `k = 0` holds at stage `ν` on `Π_ν`, and
`sup_j (j+2)^{1/2}|Ω_{ν,j} - Ω_{0,j}| ≤ ∑_{μ<ν} 3ε_μ ≤ 4ε₀`.
The increments are hypotheses about the earlier stages only; nothing about stage `ν` is assumed.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

theorem l1Norm_cast_eq (l : ℕ →₀ ℤ) : (l1Norm l : ℝ) = l.sum fun _ v => |(v : ℝ)| := by
  unfold l1Norm Finsupp.sum
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.cast_natAbs, Int.cast_abs]

/-- `|⟨l, f⟩| ≤ |l| c` when every `|f_j| ≤ c`. -/
theorem abs_linF_le_l1Norm_mul (l : ℕ →₀ ℤ) (f : ℕ → ℝ) {c : ℝ} (hf : ∀ j, |f j| ≤ c) :
    |linF l f| ≤ (l1Norm l : ℝ) * c := by
  have h := abs_linF_le_absWt l f (fun _ => c) hf
  refine h.trans (le_of_eq ?_)
  rw [l1Norm_cast_eq]
  unfold Finsupp.sum
  rw [Finset.sum_mul]

theorem kAk_zero : kAk 0 = 1 := by simp [kAk, kAbs]

theorem one_le_normLab_rpow_half (j : ℕ) : 1 ≤ normLab j ^ (1 / 2 : ℝ) :=
  Real.one_le_rpow (by linarith [normLab_ge j]) (by norm_num)

namespace W6SeqData

variable {d : W6SeqData}

/-- **The conditions with `k = 0`** (blueprint `bpW:w6:k0`), at stage `ν`, given the increment
bounds of the earlier stages. -/
theorem w6K0_of_increments (hd : d.Valid) (hsmall : d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T)
    {β₀ : ℝ} (hβ : d.al0 ≤ β₀) (h8 : 8 * d.eps0 ≤ β₀)
    (Pis : ℕ → Set (Fin 2 → ℝ)) (hPis : Antitone Pis) (Ω : ℕ → (Fin 2 → ℝ) → ℕ → ℝ)
    (h0 : ∀ ξ ∈ Pis 0, ∀ l : ℕ →₀ ℤ, IsLam l → 2 * β₀ * japL l ≤ |linF l (Ω 0 ξ)|)
    (ν : ℕ)
    (hinc : ∀ μ < ν, ∀ ξ ∈ Pis μ, ∀ j : ℕ,
      normLab j ^ (1 / 2 : ℝ) * |Ω (μ + 1) ξ j - Ω μ ξ j| ≤ 3 * d.eps μ) :
    (∀ ξ ∈ Pis ν, ∀ j : ℕ,
      normLab j ^ (1 / 2 : ℝ) * |Ω ν ξ j - Ω 0 ξ j| ≤ ∑ μ ∈ Finset.range ν, 3 * d.eps μ) ∧
    (∑ μ ∈ Finset.range ν, 3 * d.eps μ ≤ 4 * d.eps0) ∧
    (∀ ξ ∈ Pis ν, ∀ l : ℕ →₀ ℤ, IsLam l →
      d.alpha ν * japL l / kAk 0 ≤ |linF l (Ω ν ξ)|) := by
  -- the drift bound at every stage `n ≤ ν`
  have hdrift : ∀ n ≤ ν, ∀ ξ ∈ Pis n, ∀ j : ℕ,
      normLab j ^ (1 / 2 : ℝ) * |Ω n ξ j - Ω 0 ξ j| ≤ ∑ μ ∈ Finset.range n, 3 * d.eps μ := by
    intro n
    induction n with
    | zero => intro _ ξ _ j; simp
    | succ n ih =>
      intro hn ξ hξ j
      have hξn : ξ ∈ Pis n := hPis (Nat.le_succ n) hξ
      have h1 := ih (Nat.le_of_succ_le hn) ξ hξn j
      have h2 := hinc n (Nat.lt_of_succ_le hn) ξ hξn j
      have hw : 0 ≤ normLab j ^ (1 / 2 : ℝ) := (zero_le_one.trans (one_le_normLab_rpow_half j))
      have htri : |Ω (n + 1) ξ j - Ω 0 ξ j| ≤ |Ω (n + 1) ξ j - Ω n ξ j| + |Ω n ξ j - Ω 0 ξ j| := by
        have := abs_add_le (Ω (n + 1) ξ j - Ω n ξ j) (Ω n ξ j - Ω 0 ξ j)
        rwa [show Ω (n + 1) ξ j - Ω n ξ j + (Ω n ξ j - Ω 0 ξ j) = Ω (n + 1) ξ j - Ω 0 ξ j by
          ring] at this
      rw [Finset.sum_range_succ]
      calc normLab j ^ (1 / 2 : ℝ) * |Ω (n + 1) ξ j - Ω 0 ξ j|
          ≤ normLab j ^ (1 / 2 : ℝ) * (|Ω (n + 1) ξ j - Ω n ξ j| + |Ω n ξ j - Ω 0 ξ j|) :=
            mul_le_mul_of_nonneg_left htri hw
        _ = normLab j ^ (1 / 2 : ℝ) * |Ω n ξ j - Ω 0 ξ j| +
            normLab j ^ (1 / 2 : ℝ) * |Ω (n + 1) ξ j - Ω n ξ j| := by ring
        _ ≤ _ := add_le_add h1 h2
  have hsum := sum_three_eps_le hd hsmall ν
  refine ⟨hdrift ν le_rfl, hsum, ?_⟩
  intro ξ hξ l hl
  have hξ0 : ξ ∈ Pis 0 := hPis (Nat.zero_le ν) hξ
  -- `|Ω_{ν,j} - Ω_{0,j}| ≤ 4ε₀`
  have hj : ∀ j, |Ω ν ξ j - Ω 0 ξ j| ≤ 4 * d.eps0 := by
    intro j
    have h := hdrift ν le_rfl ξ hξ j
    have h1 := one_le_normLab_rpow_half j
    have h0' : 0 ≤ |Ω ν ξ j - Ω 0 ξ j| := abs_nonneg _
    nlinarith
  have hlin := abs_linF_le_l1Norm_mul l (fun j => Ω ν ξ j - Ω 0 ξ j) hj
  rw [linF_sub'] at hlin
  have hl2 : (l1Norm l : ℝ) ≤ 2 := by exact_mod_cast hl.2
  have hε := hd.eps0_pos
  have hdiff : |linF l (Ω ν ξ) - linF l (Ω 0 ξ)| ≤ β₀ := by
    have : (l1Norm l : ℝ) * (4 * d.eps0) ≤ 2 * (4 * d.eps0) :=
      mul_le_mul_of_nonneg_right hl2 (by positivity)
    linarith
  have hJ := japL_ge_one l
  have hβ0 : 0 < β₀ := by linarith
  have hlow := h0 ξ hξ0 l hl
  have htri : |linF l (Ω 0 ξ)| ≤ |linF l (Ω ν ξ)| + |linF l (Ω ν ξ) - linF l (Ω 0 ξ)| := by
    have := abs_sub_abs_le_abs_sub (linF l (Ω 0 ξ)) (linF l (Ω ν ξ))
    rw [abs_sub_comm (linF l (Ω 0 ξ))] at this
    linarith
  have hα := alpha_le hd ν
  have hα0 := (alpha_pos hd ν).le
  rw [kAk_zero, div_one]
  have : d.alpha ν * japL l ≤ β₀ * japL l := mul_le_mul_of_nonneg_right (hα.trans hβ) (by linarith)
  nlinarith

end W6SeqData

end KAM.Wave
