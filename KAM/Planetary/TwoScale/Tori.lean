/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.ToriInvariance

/-!
# Two-scale KAM: the tori (`bpP:p3:estimates`, `bpP:p3:lagr`, `bpP:p3:invariance`), facade

Private conditional interfaces (design finding N2); no signed declaration. Inventory (local
obligation → helper → application in the joint construction `tori_of_iterative`):

* `estimates` → `tori_estimates_of_limit` (with `tori_complex_ext`, `ToriEstimates`);
* `lagr` → `tori_lagr_of_limit` (`ToriLagr`);
* `invariance` → `tori_invariance_of_limit` (`ToriInvariance`; parts `ToriInvStage`, `ToriInvConj`,
  `ToriInvField`, `ToriInvLimit`, including the common inner domain for close pairs).

The only hypotheses are `ActionSteps`/`PsiSteps`/`StageSteps` (proved outputs of `iterative`) and
`ToriLimit` (proved outputs of the P23-17/P23-18 helpers), all on the same witnesses;
`tori_of_iterative` is the applicability check. Design package P23-20.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- Joint applicability check: on the witnesses of one application of `iterative`, with the limit
maps `(i, Φinf)` of the P23-17/P23-18 helpers, the three helpers apply for every `I₀ ∈ D₀`. -/
theorem tori_of_iterative {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)} (H : KamHyp D sbar p h f) :
    ∃ (Ds : ℕ → Set (Fin (a + b) → ℝ)) (hs : ℕ → (Fin (a + b) → ℂ) → ℂ)
      (fs : ℕ → CHam (a + b)) (Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b))
      (is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ))
      (i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)) (Φinf : Phase (a + b) → Phase (a + b)),
      Ds 0 = dioBase D h p ∧ ToriLimit sbar p h Ds hs Φ is i Φinf ∧
      ∀ I₀ ∈ Ds 0,
        (∃ KC : (Fin (a + b) → ℂ) → CPhase (a + b),
          DifferentiableOn ℂ KC (KAM.complexStrip (a + b) (geometricWidth sbar)) ∧
          (∀ θ, KC (KAM.realInclusion (a + b) θ) =
            KAM.realInclusion₂ (a + b) (Φinf (θ, i I₀))) ∧
          (∀ θ ∈ KAM.complexStrip (a + b) (geometricWidth sbar),
            ‖(KC θ).1 - θ‖ ≤ 3 / (4 * π) * eHat p * p.s)) ∧
        (∀ θ, (Φinf (θ, i I₀)).2 ∈ realTube D (32 * eHat p * rhoHat p)) ∧
        (AnalyticOnNhd ℝ (fun θ => Φinf (θ, i I₀)) univ ∧
          (∀ θ, ‖fderiv ℝ (fun θ => (Φinf (θ, i I₀)).1 - θ) θ‖ ≤
            3 / 4 * ((a + b : ℕ) : ℝ) * eHat p) ∧
          (∀ θ, Function.Injective (fderiv ℝ (fun θ => Φinf (θ, i I₀)) θ)) ∧
          ∀ θ u v, KAM.symplecticForm (fderiv ℝ (fun θ => Φinf (θ, i I₀)) θ u)
            (fderiv ℝ (fun θ => Φinf (θ, i I₀)) θ v) = 0) ∧
        ∀ θ t, HasDerivAt (fun s : ℝ => Φinf (θ + s • realFreq h I₀, i I₀))
          (KAM.hamiltonianVectorField (fun z : Phase (a + b) =>
            (h (KAM.realInclusion (a + b) z.2) + f (KAM.realInclusion₂ (a + b) z)).re)
            (Φinf (θ + t • realFreq h I₀, i I₀))) t := by
  obtain ⟨Ds, hs, fs, Ψ, Φ, is, i, Φinf, h0, S, P, Q, T⟩ := tori_limit_of_iterative H
  have hD0 : Ds 0 ⊆ D := by rw [h0]; exact Set.inter_subset_left
  refine ⟨Ds, hs, fs, Ψ, Φ, is, i, Φinf, h0, T, fun I₀ hI₀ => ?_⟩
  obtain ⟨e1, -, e3⟩ := tori_estimates_of_limit H hD0 T hI₀
  exact ⟨(tori_estimates_of_limit H hD0 T hI₀).1, e3, tori_lagr_of_limit H T hI₀,
    tori_invariance_of_limit H P Q hD0 T hI₀⟩

#print axioms tori_estimates_of_limit
#print axioms tori_lagr_of_limit
#print axioms tori_invariance_of_limit
#print axioms tori_of_iterative

end KAM.Planetary

end
