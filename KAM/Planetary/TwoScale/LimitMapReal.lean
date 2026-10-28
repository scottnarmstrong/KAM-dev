/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.LimitMapLimit
public import KAM.ODE.Basic

/-!
# Two-scale KAM: the real limit map `Φ` (`bpP:p3:limit-phi`, items (i)–(iii) on `ℝⁿ × D_*`)

`limit_phi_real_of_steps`: uniform convergence of `Φ_j` on `W_* = ℝⁿ × D_*`, the rescaled
Lipschitz bound `768 n Ê₀ < 1/10` with the bi-Lipschitz factors `9/10`, `11/10`, injectivity, the
full lattice identity and the three block sup bounds. Design package P23-18.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {sbar : ℝ} {p : ScaleData}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)}

theorem continuous_limitmap_data {n : ℕ} (R s : ℝ) :
    Continuous (limitmap_data (n := n) R s) := by
  unfold limitmap_data
  fun_prop

namespace PsiSteps

/-- The real part of `bpP:p3:limit-phi`: all items on `ℝⁿ × D_*` (the complex angle extension is
`limit_phi_strip_of_steps`). `D_*` is any set in every real half-radius stage domain. -/
theorem limit_phi_real_of_steps (P : PsiSteps sbar p Ds hs fs Ψ Φ)
    {Dstar : Set (Fin (a + b) → ℝ)} (hD : ∀ j, Dstar ⊆ realTube (Ds j) ((seq p j).ρ / 2)) :
    ∃ Φinf : Phase (a + b) → Phase (a + b),
      TendstoUniformlyOn (fun j => psiR (Φ j)) Φinf atTop (univ ×ˢ Dstar) ∧
      (∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))), ∀ y ∈ (univ ×ˢ Dstar : Set (Phase (a + b))),
        limitmap_data (rhoHat p) p.s ((Φinf x - x) - (Φinf y - y)) ≤
          768 * ((a + b : ℕ) : ℝ) * eHat p * limitmap_data (rhoHat p) p.s (x - y)) ∧
      768 * ((a + b : ℕ) : ℝ) * eHat p < 1 / 10 ∧
      (∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))), ∀ y ∈ (univ ×ˢ Dstar : Set (Phase (a + b))),
        9 / 10 * limitmap_data (rhoHat p) p.s (x - y) ≤
            limitmap_data (rhoHat p) p.s (Φinf x - Φinf y) ∧
          limitmap_data (rhoHat p) p.s (Φinf x - Φinf y) ≤
            11 / 10 * limitmap_data (rhoHat p) p.s (x - y)) ∧
      Set.InjOn Φinf (univ ×ˢ Dstar) ∧
      (∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))), ∀ k : Fin (a + b) → ℤ,
        Φinf (x + KAM.ODE.angleShift k) = Φinf x + KAM.ODE.angleShift k) ∧
      (∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))),
        ‖firstBlock (b := b) ((Φinf x - x).2)‖ ≤ 3 / 2 * (p.Mhat / p.M) * eHat p * rhoHat p ∧
        ‖lastBlock (a := a) ((Φinf x - x).2)‖ ≤ 3 / 2 * eHat p * rhoHat p ∧
        2 * π * ‖(Φinf x - x).1‖ ≤ 3 / 2 * eHat p * p.s) := by
  obtain ⟨Φinf, hlim, htail⟩ := P.phi_limit hD
  have h0 : 0 < rhoHat p := (P.hyp 0).R_pos
  have hs0 : 0 < p.s := (P.hyp 0).positive.2.1
  have hlam := P.lam_small
  have hxj : ∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))), ∀ j,
      x ∈ phaseTube (Ds j) ((seq p j).ρ / 2) := fun x hx j => ⟨trivial, hD j hx.2⟩
  have hLip : ∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))),
      ∀ y ∈ (univ ×ˢ Dstar : Set (Phase (a + b))),
      limitmap_data (rhoHat p) p.s ((Φinf x - x) - (Φinf y - y)) ≤
        768 * ((a + b : ℕ) : ℝ) * eHat p * limitmap_data (rhoHat p) p.s (x - y) := by
    intro x hx y hy
    have ht : Tendsto (fun j => limitmap_data (rhoHat p) p.s
        ((psiR (Φ j) x - x) - (psiR (Φ j) y - y))) atTop
        (𝓝 (limitmap_data (rhoHat p) p.s ((Φinf x - x) - (Φinf y - y)))) :=
      ((continuous_limitmap_data _ _).tendsto _).comp
        (((hlim x hx).sub_const x).sub ((hlim y hy).sub_const y))
    refine le_of_tendsto' ht fun j => ?_
    refine (P.phi_lip j x (hxj x hx j) y (hxj y hy j)).trans ?_
    exact mul_le_mul_of_nonneg_right (P.lp_le j) (limitmap_data_nonneg h0 hs0 _)
  have hbi : ∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))),
      ∀ y ∈ (univ ×ˢ Dstar : Set (Phase (a + b))),
      9 / 10 * limitmap_data (rhoHat p) p.s (x - y) ≤
          limitmap_data (rhoHat p) p.s (Φinf x - Φinf y) ∧
        limitmap_data (rhoHat p) p.s (Φinf x - Φinf y) ≤
          11 / 10 * limitmap_data (rhoHat p) p.s (x - y) := by
    intro x hx y hy
    have hl := hLip x hx y hy
    have hN0 := limitmap_data_nonneg h0 hs0 (x - y)
    have e1 : Φinf x - Φinf y = (x - y) + ((Φinf x - x) - (Φinf y - y)) := by abel
    have e2 : x - y = (Φinf x - Φinf y) - ((Φinf x - x) - (Φinf y - y)) := by abel
    constructor
    · have := limitmap_data_sub_le h0 hs0 (Φinf x - Φinf y) ((Φinf x - x) - (Φinf y - y))
      rw [← e2] at this
      nlinarith
    · rw [e1]
      refine (limitmap_data_add_le h0 hs0 _ _).trans ?_
      nlinarith
  refine ⟨Φinf, ?_, hLip, hlam, hbi, ?_, ?_, ?_⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hT : Tendsto (fun j => 2 * (max (p.s / (2 * π)) (rhoHat p) * (33 / 40)) *
        eHat (seq p j)) atTop (𝓝 0) := by
      have := (P.e_sums 0).1.tendsto_atTop_zero
      simp only [zero_add] at this
      simpa using this.const_mul (2 * (max (p.s / (2 * π)) (rhoHat p) * (33 / 40)))
    filter_upwards [hT.eventually (gt_mem_nhds hε)] with j hj x hx
    rw [dist_eq_norm]
    exact (htail x hx j).trans_lt hj
  · intro x hx y hy hxy
    have := (hbi x hx y hy).1
    rw [hxy, sub_self] at this
    have h00 : limitmap_data (rhoHat p) p.s (0 : Phase (a + b)) = 0 := by
      unfold limitmap_data; simp
    rw [h00] at this
    have := limitmap_data_nonneg h0 hs0 (x - y)
    have hz : limitmap_data (rhoHat p) p.s (x - y) = 0 := by linarith [(hbi x hx y hy).1]
    exact sub_eq_zero.1 (limitmap_data_eq_zero h0 hs0 hz)
  · intro x hx k
    have hx' : x + KAM.ODE.angleShift k ∈ (univ ×ˢ Dstar : Set (Phase (a + b))) :=
      ⟨trivial, by simpa [KAM.ODE.angleShift] using hx.2⟩
    have hper : ∀ j, psiR (Φ j) (x + KAM.ODE.angleShift k) =
        psiR (Φ j) x + KAM.ODE.angleShift k := by
      intro j
      apply KAM.realInclusion₂_injective
      have : KAM.realInclusion₂ (a + b) (x + KAM.ODE.angleShift k) =
          KAM.realInclusion₂ (a + b) x + ((fun i => (k i : ℂ)), 0) := by
        ext i <;> simp [KAM.ODE.angleShift]
      rw [P.phi_real_pt j (hxj _ hx' j), this,
        P.phi_per j _ (P.incl_mem_stage j (hxj x hx j)) k, ← P.phi_real_pt j (hxj x hx j), map_add]
      rfl
    refine tendsto_nhds_unique (hlim _ hx') ?_
    simp only [hper]
    exact (hlim x hx).add_const _
  · intro x hx
    have hr1 : Tendsto (fun j => ‖firstBlock (b := b) ((psiR (Φ j) x - x).2)‖) atTop
        (𝓝 ‖firstBlock (b := b) ((Φinf x - x).2)‖) := by
      have hc : Continuous fun v : Fin (a + b) → ℝ => ‖firstBlock (b := b) v‖ :=
        (continuous_pi fun k => continuous_apply _).norm
      exact (hc.tendsto _).comp (((continuous_snd.tendsto _).comp
        ((hlim x hx).sub_const x)))
    have hr2 : Tendsto (fun j => ‖lastBlock (a := a) ((psiR (Φ j) x - x).2)‖) atTop
        (𝓝 ‖lastBlock (a := a) ((Φinf x - x).2)‖) := by
      have hc : Continuous fun v : Fin (a + b) → ℝ => ‖lastBlock (a := a) v‖ :=
        (continuous_pi fun k => continuous_apply _).norm
      exact (hc.tendsto _).comp (((continuous_snd.tendsto _).comp
        ((hlim x hx).sub_const x)))
    have hr3 : Tendsto (fun j => 2 * π * ‖(psiR (Φ j) x - x).1‖) atTop
        (𝓝 (2 * π * ‖(Φinf x - x).1‖)) :=
      (((continuous_fst.norm).tendsto _).comp ((hlim x hx).sub_const x)).const_mul _
    exact ⟨le_of_tendsto' hr1 fun j => (P.phi_disp_real j (hxj x hx j)).1,
      le_of_tendsto' hr2 fun j => (P.phi_disp_real j (hxj x hx j)).2.1,
      le_of_tendsto' hr3 fun j => (P.phi_disp_real j (hxj x hx j)).2.2⟩

end PsiSteps

end KAM.Planetary

end
