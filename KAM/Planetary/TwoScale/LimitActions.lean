/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.LimitActionsChain

/-!
# Two-scale KAM: the limit actions (`bpP:p3:limit-actions`)

The private conditional helper `limit_actions_of_steps` (design package P23-17) for the local
obligation `limit_actions` of `two_scale_kam`: on the shared stage witnesses of `iterative`
(`ActionSteps`), the chain `ǐ_j = ĩ_j ∘ ⋯ ∘ ĩ_1` converges uniformly on `D₀` to `ǐ`, with
* (i) `|ǐ_i − id_i| ≤ 20 (M̄_i/M̄) Ê₀ ρ̂₀` blockwise and the tail `|ǐ − ǐ_j| ≤ 20 ρ̂_j Ê_j`;
* (ii) `ǐ(D₀)` lies in the real `ρ_j/2`-tube of every `D_j`, and within `20 Ê₀ ρ̂₀` of `D₀`;
* (iii) the defect `ǐ − id` is `2560 n Ê₀`-Lipschitz, `2560 n Ê₀ < 1/3`; hence `ǐ` is injective
  and bi-Lipschitz;
* (iv) `ω_j(ǐ_j(I)) = ω₀(I)`.
The hypotheses are not source premises: they are the proved recurrence of `iterative`
(`iterative_actionSteps`). The scalar `sums` and the telescoping/Lipschitz recursion are used
as proved.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {sbar : ℝ} {p : ScaleData} {h : (Fin (a + b) → ℂ) → ℂ}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)}

namespace ActionSteps

theorem e_nonneg (S : ActionSteps sbar p h Ds hs fs is) (j : ℕ) : 0 ≤ eHat (seq p j) :=
  (S.hyp j).eHat_nonneg

theorem rho_pos (S : ActionSteps sbar p h Ds hs fs is) (j : ℕ) : 0 < rhoHat (seq p j) :=
  (S.hyp j).R_pos

/-- The scalar package `sums`, applied to `Ê_j`, `ρ̂_j`. -/
theorem scalar_sums (S : ActionSteps sbar p h Ds hs fs is) :
    (∀ m, Summable (fun k => eHat (seq p (m + k))) ∧
      ∑' k, eHat (seq p (m + k)) ≤ 2 * eHat (seq p m)) ∧
    (∀ k, rhoHat (seq p k) ≤ rhoHat (seq p 0) / 16 ^ k) := by
  have h0 : eHat (seq p 0) < 1 / 2 := by
    have := (S.hyp 0).eHat_lt_small; linarith
  have := sums (e := fun j => eHat (seq p j)) (R := fun j => rhoHat (seq p j))
    (s := fun j => (seq p j).s) (c := 0) S.e_nonneg h0
    (fun j => (S.eHat_sq j).le) le_rfl (by simpa using h0.le)
    (fun j => ⟨(S.rho_pos j).le, S.rho_hi j⟩) (fun j => rfl)
  exact ⟨this.2.1, fun k => (this.2.2.2.2 k).1⟩

theorem rho_le_zero (S : ActionSteps sbar p h Ds hs fs is) (j : ℕ) :
    rhoHat (seq p j) ≤ rhoHat (seq p 0) := by
  refine (S.scalar_sums.2 j).trans ?_
  have := S.rho_pos 0
  exact div_le_self this.le (one_le_pow₀ (by norm_num))

theorem rho_anti (S : ActionSteps sbar p h Ds hs fs is) (j m : ℕ) :
    rhoHat (seq p (j + m)) ≤ rhoHat (seq p j) := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    have := S.rho_pos (j + m)
    calc rhoHat (seq p (j + (m + 1))) ≤ rhoHat (seq p (j + m)) / 16 := S.rho_hi (j + m)
      _ ≤ rhoHat (seq p (j + m)) := by linarith
      _ ≤ _ := ih

theorem partial_sum_le (S : ActionSteps sbar p h Ds hs fs is) (j : ℕ) :
    ∑ k ∈ Finset.range j, eHat (seq p k) ≤ 2 * eHat (seq p 0) := by
  have h := S.scalar_sums.1 0
  simp only [zero_add] at h
  exact (h.1.sum_le_tsum _ (fun k _ => S.e_nonneg k)).trans h.2

/-- Blockwise bound on `ǐ_j − id`, uniform in `j`. -/
theorem chain_block_le (S : ActionSteps sbar p h Ds hs fs is) {I : Fin (a + b) → ℝ}
    (hI : I ∈ Ds 0) (j : ℕ) :
    ‖firstBlock (b := b) (actionChain is j I - I)‖ ≤
      20 * (p.Mbar₁ / p.Mbar) * eHat (seq p 0) * rhoHat (seq p 0) ∧
    ‖lastBlock (a := a) (actionChain is j I - I)‖ ≤
      20 * (p.Mbar₂ / p.Mbar) * eHat (seq p 0) * rhoHat (seq p 0) := by
  have hr0 := S.rho_pos 0
  have hnn : ∀ r : ℝ, 0 ≤ r → ∀ (v : ℕ → ℝ), (∀ k, ‖v k‖ ≤ 10 * r * eHat (seq p k) * rhoHat (seq p k)) →
      ∀ j, ∑ k ∈ Finset.range j, ‖v k‖ ≤ 20 * r * eHat (seq p 0) * rhoHat (seq p 0) := by
    intro r hr v hv j
    calc ∑ k ∈ Finset.range j, ‖v k‖
        ≤ ∑ k ∈ Finset.range j, (10 * r * rhoHat (seq p 0)) * eHat (seq p k) := by
          refine Finset.sum_le_sum fun k _ => (hv k).trans ?_
          have := S.rho_le_zero k
          have := S.e_nonneg k
          nlinarith [mul_nonneg hr (S.e_nonneg k)]
      _ = (10 * r * rhoHat (seq p 0)) * ∑ k ∈ Finset.range j, eHat (seq p k) := by
          rw [Finset.mul_sum]
      _ ≤ (10 * r * rhoHat (seq p 0)) * (2 * eHat (seq p 0)) := by
          gcongr; exact S.partial_sum_le j
      _ = _ := by ring
  have hp1 : 0 ≤ p.Mbar₁ / p.Mbar := div_nonneg (S.hyp 0).positive.2.2.2.2.2.2.2.1.le
    (S.hyp 0).positive.2.2.2.2.2.2.1.le
  have hp2 : 0 ≤ p.Mbar₂ / p.Mbar := div_nonneg (S.hyp 0).positive.2.2.2.2.2.2.2.2.le
    (S.hyp 0).positive.2.2.2.2.2.2.1.le
  -- telescoping, first block
  have tele : ∀ (B : (Fin (a + b) → ℝ) → ℝ), (∀ u v, B (u + v) ≤ B u + B v) → B 0 = 0 →
      ∀ (r : ℝ), 0 ≤ r → (∀ k, B (actionChain is (k + 1) I - actionChain is k I) ≤
        10 * r * eHat (seq p k) * rhoHat (seq p k)) → (∀ k, 0 ≤ B (actionChain is (k + 1) I - actionChain is k I)) →
      ∀ j, B (actionChain is j I - I) ≤ 20 * r * eHat (seq p 0) * rhoHat (seq p 0) := by
    intro B hB B0 r hr hv hnn' j
    have : ∀ j, B (actionChain is j I - I) ≤
        ∑ k ∈ Finset.range j, B (actionChain is (k + 1) I - actionChain is k I) := by
      intro j
      induction j with
      | zero => simp [actionChain, B0]
      | succ j ih =>
        rw [Finset.sum_range_succ]
        have : actionChain is (j + 1) I - I =
            (actionChain is (j + 1) I - actionChain is j I) + (actionChain is j I - I) := by abel
        rw [this]
        calc _ ≤ _ := hB _ _
          _ ≤ _ := by linarith
    refine (this j).trans ?_
    have := hnn r hr (fun k => B (actionChain is (k + 1) I - actionChain is k I))
      (fun k => by rw [Real.norm_of_nonneg (hnn' k)]; exact hv k) j
    have e : ∑ k ∈ Finset.range j, B (actionChain is (k + 1) I - actionChain is k I) =
        ∑ k ∈ Finset.range j, ‖B (actionChain is (k + 1) I - actionChain is k I)‖ :=
      Finset.sum_congr rfl fun k _ => (Real.norm_of_nonneg (hnn' k)).symm
    rw [e]; exact this
  refine ⟨tele (fun v => ‖firstBlock (b := b) v‖) (fun u v => norm_add_le (firstBlock (b := b) u) (firstBlock (b := b) v)) (by show ‖firstBlock (b := b) (0 : Fin (a + b) → ℝ)‖ = 0; rw [norm_eq_zero]; rfl)
      _ hp1 (fun k => by
        have := (S.chain_step hI k).1; linarith) (fun k => norm_nonneg _) j,
    tele (fun v => ‖lastBlock (a := a) v‖) (fun u v => norm_add_le (lastBlock (a := a) u) (lastBlock (a := a) v)) (by show ‖lastBlock (a := a) (0 : Fin (a + b) → ℝ)‖ = 0; rw [norm_eq_zero]; rfl)
      _ hp2 (fun k => by
        have := (S.chain_step hI k).2; linarith) (fun k => norm_nonneg _) j⟩

end ActionSteps

end KAM.Planetary

end
