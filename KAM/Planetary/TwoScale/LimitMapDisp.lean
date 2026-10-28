/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.LimitMapPhi

/-!
# Two-scale KAM: displacement bounds for `Φ_j` (`bpP:p3:limit-phi`, `stepP:p3:lp-tele`)

The telescoping `Φ_j z − z = Σ_k (Ψ_k y_k − y_k)` on the complex stage domain
`V_j = coefficientDom (D_j) ρ_j (s̄ + s_j)`, uniformly in `j` (`(3/2) Ê₀` after summation), and the
bound `∏ (1 + ς_k) − 1 ≤ 768 n Ê₀`. Design package P23-18.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {sbar : ℝ} {p : ScaleData}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)}

namespace PsiSteps

theorem rho_le_zero (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) :
    rhoHat (seq p j) ≤ rhoHat p := by
  refine (P.rho_upper j).trans ?_
  have := (P.hyp 0).R_pos
  exact div_le_self this.le (one_le_pow₀ (by norm_num))

theorem s_le_zero (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) : (seq p j).s ≤ p.s := by
  rw [seq_s]
  have := (P.hyp 0).positive.2.1
  exact div_le_self this.le (one_le_pow₀ (by norm_num))

theorem partial_sum_le (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) :
    ∑ k ∈ Finset.range j, eHat (seq p k) ≤ 2 * eHat p := by
  have h0 : eHat (seq p 0) < 1 / 2 := by have := (P.hyp 0).eHat_lt_small; linarith
  have hsum := sums (e := fun j => eHat (seq p j)) (R := fun j => rhoHat (seq p j))
    (s := fun j => (seq p j).s) (c := 0)
    (fun j => (P.hyp j).eHat_nonneg) h0 (fun j => (P.eHat_sq j).le) le_rfl (by simp)
    (fun j => ⟨(P.rho_pos j).le, P.rho_hi j⟩) (fun j => rfl)
  have h := hsum.2.1 0
  simp only [zero_add] at h
  exact (h.1.sum_le_tsum _ (fun k _ => (P.hyp k).eHat_nonneg)).trans h.2

/-- Complex telescoping of `Φ_j − id` on the stage domain. -/
theorem phi_disp_complex (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) :
    ∀ z ∈ coefficientDom (Ds j) (seq p j).ρ (sbar + (seq p j).s),
      ‖firstBlock (b := b) ((Φ j z).2 - z.2)‖ ≤
        3 / 4 * (p.Mhat / p.M) * rhoHat p * ∑ k ∈ Finset.range j, eHat (seq p k) ∧
      ‖lastBlock (a := a) ((Φ j z).2 - z.2)‖ ≤
        3 / 4 * rhoHat p * ∑ k ∈ Finset.range j, eHat (seq p k) ∧
      2 * π * ‖(Φ j z).1 - z.1‖ ≤ 3 / 4 * p.s * ∑ k ∈ Finset.range j, eHat (seq p k) := by
  have hR0 : 0 < rhoHat p := (P.hyp 0).R_pos
  have hs0 : 0 < p.s := (P.hyp 0).positive.2.1
  have hM : p.Mhat ≤ p.M := (P.hyp 0).normalized.1
  have hM0 : 0 < p.M := (P.hyp 0).positive.2.2.2.2.1
  have hMh : 0 < p.Mhat := (P.hyp 0).positive.2.2.2.2.2.1
  have hr : 0 ≤ p.Mhat / p.M := by positivity
  induction j with
  | zero =>
    intro z _
    have e : Φ 0 z = z := by rw [P.Phi_zero]; rfl
    have h1 : firstBlock (b := b) (0 : Fin (a + b) → ℂ) = 0 := rfl
    have h2 : lastBlock (a := a) (0 : Fin (a + b) → ℂ) = 0 := rfl
    simp [e, h1, h2]
  | succ j ih =>
    intro z hz
    have hzV : z ∈ coefficientDom (Ds (j + 1)) (rhoHat (seq p j) / 16)
        (sbar + (seq p j).s / 12) := hz
    have hΨz := P.psi_maps j hzV
    have hΨz' : Ψ (j + 1) z ∈ coefficientDom (Ds j) (seq p j).ρ (sbar + (seq p j).s) :=
      coefficientDom_mono_of_le (P.hyp j).R_le_ρ le_rfl hΨz
    obtain ⟨i1, i2, i3⟩ := ih _ hΨz'
    obtain ⟨b1, b2, b3⟩ := P.psi_bd j z hzV
    have he := (P.hyp j).eHat_nonneg
    have hRj := P.rho_le_zero j
    have hsj := P.s_le_zero j
    have hsum := Finset.sum_range_succ (fun k => eHat (seq p k)) j
    have e1 : (Φ (j + 1) z).2 - z.2 = ((Φ j (Ψ (j + 1) z)).2 - (Ψ (j + 1) z).2) +
        ((Ψ (j + 1) z).2 - z.2) := by
      rw [P.Phi_succ, Function.comp_apply]; abel
    have e2 : (Φ (j + 1) z).1 - z.1 = ((Φ j (Ψ (j + 1) z)).1 - (Ψ (j + 1) z).1) +
        ((Ψ (j + 1) z).1 - z.1) := by
      rw [P.Phi_succ, Function.comp_apply]; abel
    refine ⟨?_, ?_, ?_⟩
    · have : firstBlock (b := b) ((Φ (j + 1) z).2 - z.2) =
          firstBlock (b := b) ((Φ j (Ψ (j + 1) z)).2 - (Ψ (j + 1) z).2) +
            firstBlock (b := b) ((Ψ (j + 1) z).2 - z.2) := by rw [e1]; rfl
      rw [this]
      refine (norm_add_le _ _).trans ?_
      have : 3 / 4 * (p.Mhat / p.M) * eHat (seq p j) * rhoHat (seq p j) ≤
          3 / 4 * (p.Mhat / p.M) * eHat (seq p j) * rhoHat p := by gcongr
      rw [hsum]; nlinarith
    · have : lastBlock (a := a) ((Φ (j + 1) z).2 - z.2) =
          lastBlock (a := a) ((Φ j (Ψ (j + 1) z)).2 - (Ψ (j + 1) z).2) +
            lastBlock (a := a) ((Ψ (j + 1) z).2 - z.2) := by rw [e1]; rfl
      rw [this]
      refine (norm_add_le _ _).trans ?_
      have : 3 / 4 * eHat (seq p j) * rhoHat (seq p j) ≤ 3 / 4 * eHat (seq p j) * rhoHat p := by
        gcongr
      rw [hsum]; nlinarith
    · rw [e2]
      refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)).trans ?_
      have : 3 / 4 * eHat (seq p j) * (seq p j).s ≤ 3 / 4 * eHat (seq p j) * p.s := by gcongr
      rw [hsum]; nlinarith

end PsiSteps

end KAM.Planetary

end
