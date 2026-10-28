/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.LimitMapStrip

/-!
# Two-scale KAM: the limit map (`bpP:p3:psi-lip`, `bpP:p3:limit-phi`), facade and joint check

Facade over `LimitMapScale` (rescaled norm `limitmap_data`), `LimitMapPsi` (`PsiSteps`,
`iterative_steps`, domains and displacement), `LimitMapLip`/`LimitMapPack` (`psi_lip_of_steps`),
`LimitMapPhi`/`LimitMapDisp`/`LimitMapLimit`/`LimitMapReal` (composition rule, uniform limit
`limit_phi_real_of_steps`) and `LimitMapStrip` (`limit_phi_strip_of_steps`). These are private
conditional interfaces (design finding N2): the only hypotheses are `ActionSteps`/`PsiSteps`,
proved outputs of `iterative` on the same witnesses, and `D_*` the image of `D₀` under the limit
action map of `limit_actions_of_steps`. `limit_map_of_iterative` is the joint applicability check.
Design package P23-18.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- Joint applicability check: on the witnesses of one application of `iterative`, the helpers
`limit_actions_of_steps`, `limit_phi_real_of_steps` and `limit_phi_strip_of_steps` apply in
sequence (`D_* = ǐ(D₀)`), yielding the limit map `Φ` on `ℝⁿ × D_*`. -/
theorem limit_map_of_iterative {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)} (H : KamHyp D sbar p h f) :
    ∃ (Ds : ℕ → Set (Fin (a + b) → ℝ)) (hs : ℕ → (Fin (a + b) → ℂ) → ℂ)
      (fs : ℕ → CHam (a + b)) (Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b))
      (is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)),
      Ds 0 = dioBase D h p ∧
      ∃ i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ),
        TendstoUniformlyOn (actionChain is) i atTop (Ds 0) ∧
        ∃ Φinf : Phase (a + b) → Phase (a + b),
          TendstoUniformlyOn (fun j => psiR (Φ j)) Φinf atTop (univ ×ˢ (i '' Ds 0)) ∧
          (∀ x ∈ (univ ×ˢ (i '' Ds 0) : Set (Phase (a + b))),
            ∀ y ∈ (univ ×ˢ (i '' Ds 0) : Set (Phase (a + b))),
            limitmap_data (rhoHat p) p.s ((Φinf x - x) - (Φinf y - y)) ≤
              768 * ((a + b : ℕ) : ℝ) * eHat p * limitmap_data (rhoHat p) p.s (x - y)) ∧
          (∀ x ∈ (univ ×ˢ (i '' Ds 0) : Set (Phase (a + b))), ∀ k : Fin (a + b) → ℤ,
            Φinf (x + KAM.ODE.angleShift k) = Φinf x + KAM.ODE.angleShift k) ∧
          ∀ I ∈ i '' Ds 0, ∀ c : Fin (a + b), ∃ G, StripLimit (a + b) (geometricWidth sbar)
            (3 / 2 * eHat p * p.s / (2 * π))
            (PsiSteps.stripSeq Φ ((ContinuousLinearMap.proj c).comp
              (ContinuousLinearMap.fst ℂ _ _)) I)
            (fun x => (((Φinf (x, I) - (x, I)).1 c : ℝ) : ℂ)) G := by
  obtain ⟨Ds, hs, fs, Ψ, Φ, is, h0, S, P⟩ := iterative_steps H
  obtain ⟨i, hconv, -, -, -, hloc, -⟩ := limit_actions_of_steps S
  have hD : ∀ j, i '' Ds 0 ⊆ realTube (Ds j) ((seq p j).ρ / 2) := by
    rintro j _ ⟨I, hI, rfl⟩
    exact hloc I hI j
  obtain ⟨Φinf, hU, hL, -, -, -, hper, -⟩ := P.limit_phi_real_of_steps hD
  exact ⟨Ds, hs, fs, Ψ, Φ, is, h0, i, hconv, Φinf, hU, hL, hper,
    fun I hI c => (P.limit_phi_strip_of_steps hD hU I hI).1 c⟩

#print axioms psi_lip_of_steps
#print axioms PsiSteps.limit_phi_real_of_steps
#print axioms PsiSteps.limit_phi_strip_of_steps
#print axioms iterative_steps
#print axioms limit_map_of_iterative

end KAM.Planetary

end
