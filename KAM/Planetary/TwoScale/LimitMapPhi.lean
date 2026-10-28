/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.LimitMapPack

/-!
# Two-scale KAM: the composed maps `Φ_j` on the real half-radius domains (`bpP:p3:limit-phi`)

The real restrictions `Φ_j = Ψ_1 ∘ ⋯ ∘ Ψ_j` satisfy `Φ_{j+1} = Φ_j ∘ Ψ_{j+1}` on `𝒟_{j+1} × ℝⁿ`
(`phiR_succ`), and the rescaled Lipschitz constant of `Φ_j − id` is
`∏_{k<j} (1 + ς_k) − 1 ≤ 768 n Ê₀` (`stepP:p3:lp-cauchy`, the composition rule of
`stepP:p3:la-lip`). Design package P23-18.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

theorem coefficientDom_mono_of_le {n : ℕ} {D : Set (Fin n → ℝ)} {r r' σ σ' : ℝ} (hr : r ≤ r')
    (hσ : σ ≤ σ') : coefficientDom D r σ ⊆ coefficientDom D r' σ' := by
  rw [(conv_data D r σ).2, (conv_data D r' σ').2]
  rintro z ⟨h1, ⟨J, hJ, h2⟩⟩
  refine ⟨fun i => (h1 i).trans_le (by gcongr), J, hJ, h2.trans_le hr⟩

theorem realTube_mono {n : ℕ} {D : Set (Fin n → ℝ)} {r r' : ℝ} (hr : r ≤ r') :
    realTube D r ⊆ realTube D r' := by
  intro v hv
  obtain ⟨J, hJ, h⟩ := hv
  exact ⟨J, hJ, h.trans_le hr⟩

/-- The sum `ς_k = 192 n c^k Ê_k` of `stepP:p3:pl-lip`. -/
def psiConst (a b : ℕ) (p : ScaleData) (k : ℕ) : ℝ :=
  192 * ((a + b : ℕ) : ℝ) * (((24 : ℝ) ^ (p.τ + 1) / 6) ^ k * eHat (seq p k))

variable {a b : ℕ} {sbar : ℝ} {p : ScaleData}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)}

namespace PsiSteps

theorem rho_stage_pos (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) : 0 < (seq p j).ρ :=
  (P.hyp j).positive.2.2.1

theorem incl_mem_stage (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) {x : Phase (a + b)}
    (hx : x ∈ phaseTube (Ds j) ((seq p j).ρ / 2)) :
    KAM.realInclusion₂ (a + b) x ∈
      coefficientDom (Ds j) (seq p j).ρ (sbar + (seq p j).s) := by
  have hs0 : 0 < (seq p j).s := (P.hyp j).positive.2.1
  have hsbar : 4 * (seq p j).s ≤ sbar := (P.hyp j).widths.1
  have := P.rho_stage_pos j
  exact real_mem_coefDom (by linarith) (realTube_mono (by linarith) hx.2)

theorem phi_real_pt (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) {x : Phase (a + b)}
    (hx : x ∈ phaseTube (Ds j) ((seq p j).ρ / 2)) :
    KAM.realInclusion₂ (a + b) (psiR (Φ j) x) = Φ j (KAM.realInclusion₂ (a + b) x) := by
  obtain ⟨y, hy⟩ := P.phi_real j x (P.incl_mem_stage j hx)
  have : psiR (Φ j) x = y := by
    unfold psiR; rw [← hy, KAM.realPartCLM₂_realInclusion₂]
  rw [this, hy]

theorem phiR_zero (P : PsiSteps sbar p Ds hs fs Ψ Φ) (x : Phase (a + b)) :
    psiR (Φ 0) x = x := by
  unfold psiR; rw [P.Phi_zero]; simp

theorem phiR_succ (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) {x : Phase (a + b)}
    (hx : x ∈ phaseTube (Ds (j + 1)) ((seq p (j + 1)).ρ / 2)) :
    psiR (Φ (j + 1)) x = psiR (Φ j) (psiR (Ψ (j + 1)) x) := by
  unfold psiR
  rw [P.Phi_succ, Function.comp_apply, ← (P.psi_step j hx).1]
  rfl

theorem psiConst_nonneg (P : PsiSteps sbar p Ds hs fs Ψ Φ) (k : ℕ) : 0 ≤ psiConst a b p k := by
  have := (P.hyp k).eHat_nonneg
  have hτ : 0 ≤ ((24 : ℝ) ^ (p.τ + 1) / 6) := by positivity
  unfold psiConst; positivity

theorem lp_nonneg (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) :
    0 ≤ ∏ k ∈ Finset.range j, (1 + psiConst a b p k) - 1 := by
  have : 1 ≤ ∏ k ∈ Finset.range j, (1 + psiConst a b p k) := by
    have := Finset.prod_le_prod₀ (s := Finset.range j) (f := fun _ => (1 : ℝ))
      (g := fun k => 1 + psiConst a b p k) (fun _ _ => zero_le_one)
      (fun k _ => by linarith [P.psiConst_nonneg k])
    simpa using this
  linarith

/-- The composition rule of `stepP:p3:lp-cauchy`: the rescaled Lipschitz constant of `Φ_j − id`
on `𝒟_j × ℝⁿ` is at most `∏_{k<j} (1 + ς_k) − 1`. -/
theorem phi_lip (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) :
    ∀ x ∈ phaseTube (Ds j) ((seq p j).ρ / 2), ∀ y ∈ phaseTube (Ds j) ((seq p j).ρ / 2),
      limitmap_data (rhoHat p) p.s ((psiR (Φ j) x - x) - (psiR (Φ j) y - y)) ≤
        (∏ k ∈ Finset.range j, (1 + psiConst a b p k) - 1) *
          limitmap_data (rhoHat p) p.s (x - y) := by
  have h0 : 0 < rhoHat p := (P.hyp 0).R_pos
  have hs0 : 0 < p.s := (P.hyp 0).positive.2.1
  have hN0 : limitmap_data (rhoHat p) p.s (0 : Phase (a + b)) = 0 := by
    unfold limitmap_data; simp
  induction j with
  | zero =>
    intro x _ y _
    rw [P.phiR_zero, P.phiR_zero]
    simp [hN0]
  | succ j ih =>
    intro x hx y hy
    have hx' := (P.psi_step j hx).2.1
    have hy' := (P.psi_step j hy).2.1
    rw [P.phiR_succ j hx, P.phiR_succ j hy]
    set x' := psiR (Ψ (j + 1)) x
    set y' := psiR (Ψ (j + 1)) y
    have hΨ := (psi_lip_of_steps P).2.2.1 j x hx y hy
    have h1 := ih x' hx' y' hy'
    have hς : 0 ≤ psiConst a b p j := P.psiConst_nonneg j
    have hΨ' : limitmap_data (rhoHat p) p.s ((x' - x) - (y' - y)) ≤
        psiConst a b p j * limitmap_data (rhoHat p) p.s (x - y) := hΨ
    have hxy : limitmap_data (rhoHat p) p.s (x' - y') ≤
        (1 + psiConst a b p j) * limitmap_data (rhoHat p) p.s (x - y) := by
      have e : x' - y' = (x - y) + ((x' - x) - (y' - y)) := by abel
      rw [e]
      refine (limitmap_data_add_le h0 hs0 _ _).trans ?_
      linarith
    have e2 : (psiR (Φ j) x' - x) - (psiR (Φ j) y' - y) =
        ((psiR (Φ j) x' - x') - (psiR (Φ j) y' - y')) + ((x' - x) - (y' - y)) := by abel
    rw [e2]
    refine (limitmap_data_add_le h0 hs0 _ _).trans ?_
    have hprod : 1 ≤ ∏ k ∈ Finset.range j, (1 + psiConst a b p k) := by
      have := Finset.prod_le_prod₀ (s := Finset.range j) (f := fun _ => (1 : ℝ))
        (g := fun k => 1 + psiConst a b p k) (fun _ _ => zero_le_one)
        (fun k _ => by linarith [P.psiConst_nonneg k])
      simpa using this
    have hLp : 0 ≤ ∏ k ∈ Finset.range j, (1 + psiConst a b p k) - 1 := by linarith
    have h2 := mul_le_mul_of_nonneg_left hxy hLp
    rw [Finset.prod_range_succ]
    nlinarith

end PsiSteps

end KAM.Planetary

end
