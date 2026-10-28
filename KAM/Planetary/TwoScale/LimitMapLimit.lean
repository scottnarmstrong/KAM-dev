/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.LimitMapDisp

/-!
# Two-scale KAM: the uniform limit of `Φ_j` on `ℝⁿ × D_*` (`bpP:p3:limit-phi`, `stepP:p3:lp-cauchy`)

`Φ_{j+1} − Φ_j = Φ_j ∘ Ψ_{j+1} − Φ_j` is at most `(11/10) · (3/4) Ê_j` in the rescaled norm on
`W_* = ℝⁿ × D_*` (`D_*` in every real half-radius stage domain), hence the maps converge uniformly
to `Φ`, and the Lipschitz and lattice properties pass to the limit. Design package P23-18.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {sbar : ℝ} {p : ScaleData}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)}

namespace PsiSteps

/-- `∏ (1 + ς_k) − 1 ≤ 768 n Ê₀`, and `768 n Ê₀ < 1/10`. -/
theorem lp_le (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) :
    ∏ k ∈ Finset.range j, (1 + psiConst a b p k) - 1 ≤ 768 * ((a + b : ℕ) : ℝ) * eHat p := by
  obtain ⟨-, -, -, hsm, htsum, hsmall⟩ := psi_lip_of_steps P
  have hn : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) := Nat.cast_nonneg _
  have he0 : 0 ≤ eHat p := (P.hyp 0).eHat_nonneg
  have hsum : ∑ k ∈ Finset.range j, psiConst a b p k ≤ 384 * ((a + b : ℕ) : ℝ) * eHat p :=
    ((hsm.sum_le_tsum _ (fun k _ => P.psiConst_nonneg k)).trans htsum)
  have step1 : ∏ k ∈ Finset.range j, (1 + psiConst a b p k) ≤
      Real.exp (∑ k ∈ Finset.range j, psiConst a b p k) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun k _ => ?_) (fun k _ => ?_)
    · linarith [P.psiConst_nonneg k]
    · have := Real.add_one_le_exp (psiConst a b p k); linarith
  set x := 384 * ((a + b : ℕ) : ℝ) * eHat p with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 / 20 := hsmall
  have h2 : Real.exp x ≤ 1 / (1 - x) := Real.exp_bound_div_one_sub_of_interval hx0 (by linarith)
  have h3 : 1 / (1 - x) ≤ 1 + 2 * x := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have : ∏ k ∈ Finset.range j, (1 + psiConst a b p k) ≤ 1 + 2 * x :=
    step1.trans ((Real.exp_le_exp.2 hsum).trans (h2.trans h3))
  rw [hx] at this
  linarith

theorem lam_small (P : PsiSteps sbar p Ds hs fs Ψ Φ) :
    768 * ((a + b : ℕ) : ℝ) * eHat p < 1 / 10 := by
  have := P.kam_small.2
  have hn : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) := Nat.cast_nonneg _
  have he0 : 0 ≤ eHat p := (P.hyp 0).eHat_nonneg
  nlinarith [mul_nonneg hn he0]

/-- Successive differences of the real maps `Φ_j`. -/
theorem phi_step_diff (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) {x : Phase (a + b)}
    (hx1 : x ∈ phaseTube (Ds (j + 1)) ((seq p (j + 1)).ρ / 2))
    (hx0 : x ∈ phaseTube (Ds j) ((seq p j).ρ / 2)) :
    ‖psiR (Φ (j + 1)) x - psiR (Φ j) x‖ ≤
      max (p.s / (2 * π)) (rhoHat p) * (33 / 40 * eHat (seq p j)) := by
  have h0 : 0 < rhoHat p := (P.hyp 0).R_pos
  have hs0 : 0 < p.s := (P.hyp 0).positive.2.1
  have he := (P.hyp j).eHat_nonneg
  have hK : 0 ≤ max (p.s / (2 * π)) (rhoHat p) := le_max_of_le_right h0.le
  have hx' := (P.psi_step j hx1).2.1
  rw [P.phiR_succ j hx1]
  set x' := psiR (Ψ (j + 1)) x
  have hlip := P.phi_lip j x' hx' x hx0
  have hdisp := P.psi_disp j hx1
  have hL := P.lp_le j
  have hlam := P.lam_small
  have hN : limitmap_data (rhoHat p) p.s (psiR (Φ j) x' - psiR (Φ j) x) ≤
      (1 + (∏ k ∈ Finset.range j, (1 + psiConst a b p k) - 1)) *
        limitmap_data (rhoHat p) p.s (x' - x) := by
    have e : psiR (Φ j) x' - psiR (Φ j) x =
        (x' - x) + ((psiR (Φ j) x' - x') - (psiR (Φ j) x - x)) := by abel
    rw [e]
    refine (limitmap_data_add_le h0 hs0 _ _).trans ?_
    linarith
  have hN0 := limitmap_data_nonneg h0 hs0 (x' - x)
  have h12 : (1 : ℝ) / 12 ^ j ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hd2 : limitmap_data (rhoHat p) p.s (x' - x) ≤ 3 / 4 * eHat (seq p j) := by
    have e : x' - x = psiR (Ψ (j + 1)) x - x := rfl
    rw [e]
    refine hdisp.trans ?_
    have : 3 / 4 * eHat (seq p j) / 12 ^ j = 3 / 4 * eHat (seq p j) * (1 / 12 ^ j) := by ring
    rw [this]
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) he]
  have hbound : limitmap_data (rhoHat p) p.s (psiR (Φ j) x' - psiR (Φ j) x) ≤
      33 / 40 * eHat (seq p j) := by
    refine hN.trans ?_
    have h1 : (1 + (∏ k ∈ Finset.range j, (1 + psiConst a b p k) - 1)) ≤ 11 / 10 := by linarith
    have h2 : 0 ≤ 1 + (∏ k ∈ Finset.range j, (1 + psiConst a b p k) - 1) := by
      have := P.lp_nonneg j; linarith
    calc _ ≤ (11 / 10) * (3 / 4 * eHat (seq p j)) :=
          mul_le_mul h1 hd2 hN0 (by norm_num)
      _ = _ := by ring
  refine (norm_le_limitmap_data h0 hs0 _).trans ?_
  exact mul_le_mul_of_nonneg_left hbound hK

theorem e_sums (P : PsiSteps sbar p Ds hs fs Ψ Φ) (m : ℕ) :
    Summable (fun k => eHat (seq p (m + k))) ∧
      ∑' k, eHat (seq p (m + k)) ≤ 2 * eHat (seq p m) := by
  have h0 : eHat (seq p 0) < 1 / 2 := by have := (P.hyp 0).eHat_lt_small; linarith
  exact (sums (e := fun j => eHat (seq p j)) (R := fun j => rhoHat (seq p j))
    (s := fun j => (seq p j).s) (c := 0)
    (fun j => (P.hyp j).eHat_nonneg) h0 (fun j => (P.eHat_sq j).le) le_rfl (by simp)
    (fun j => ⟨(P.rho_pos j).le, P.rho_hi j⟩) (fun j => rfl)).2.1 m

/-- Pointwise limit of the real maps on `W_* = ℝⁿ × D_*`, with the tail bound. -/
theorem phi_limit (P : PsiSteps sbar p Ds hs fs Ψ Φ) {Dstar : Set (Fin (a + b) → ℝ)}
    (hD : ∀ j, Dstar ⊆ realTube (Ds j) ((seq p j).ρ / 2)) :
    ∃ Φinf : Phase (a + b) → Phase (a + b),
      (∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))),
        Tendsto (fun j => psiR (Φ j) x) atTop (𝓝 (Φinf x))) ∧
      ∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))), ∀ j,
        ‖Φinf x - psiR (Φ j) x‖ ≤
          2 * (max (p.s / (2 * π)) (rhoHat p) * (33 / 40)) * eHat (seq p j) := by
  classical
  have h0 : 0 < rhoHat p := (P.hyp 0).R_pos
  have hK : 0 ≤ max (p.s / (2 * π)) (rhoHat p) := le_max_of_le_right h0.le
  set K := max (p.s / (2 * π)) (rhoHat p) with hKdef
  have hex : ∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))), ∃ l,
      Tendsto (fun j => psiR (Φ j) x) atTop (𝓝 l) ∧
      ∀ j, ‖l - psiR (Φ j) x‖ ≤ 2 * (K * (33 / 40)) * eHat (seq p j) := by
    intro x hx
    have hxj : ∀ j, x ∈ phaseTube (Ds j) ((seq p j).ρ / 2) := fun j => ⟨trivial, hD j hx.2⟩
    have hd : ∀ n, dist (psiR (Φ n) x) (psiR (Φ n.succ) x) ≤ K * (33 / 40 * eHat (seq p n)) :=
      fun n => by
        rw [dist_comm, dist_eq_norm]; exact P.phi_step_diff n (hxj (n + 1)) (hxj n)
    have hsm : Summable (fun n => K * (33 / 40 * eHat (seq p n))) := by
      have := (P.e_sums 0).1
      simp only [zero_add] at this
      exact (this.mul_left (33 / 40)).mul_left K
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_of_summable _ hd hsm)
    refine ⟨l, hl, fun j => ?_⟩
    have := dist_le_tsum_of_dist_le_of_tendsto _ hd hsm hl j
    rw [dist_comm, dist_eq_norm] at this
    refine this.trans ?_
    have hsm' := (P.e_sums j).1
    calc ∑' m, K * (33 / 40 * eHat (seq p (j + m)))
        = K * (33 / 40) * ∑' m, eHat (seq p (j + m)) := by
          rw [← tsum_mul_left]; congr 1; ext m; ring
      _ ≤ K * (33 / 40) * (2 * eHat (seq p j)) := by
          gcongr; exact (P.e_sums j).2
      _ = _ := by ring
  choose! l hl using hex
  exact ⟨l, fun x hx => (hl x hx).1, fun x hx => (hl x hx).2⟩

end PsiSteps

end KAM.Planetary

end
