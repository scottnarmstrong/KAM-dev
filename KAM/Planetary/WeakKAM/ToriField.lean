/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.ToriLimit

/-! # P11B tori: the real Hamiltonian field along the limit tori

From the complex invariance identity `X_{H₀}(K_b(θ)) = DK_b(θ) ω_*` to the frozen real field
`hamiltonianVectorField (realHamiltonian h f)` at the real point `(θ, b) + defect b θ`, using
`KAM.hamiltonianVectorField_eq_of_real` (source step `lt-lim`, final identification).
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

/-- The complex Hamiltonian `h(I) + f(θ, I)`. -/
def toriF (d : SelectionData n) (f : SelectionPhaseC n → ℂ) (y : SelectionPhaseC n) : ℂ :=
  d.h y.2 + f y

theorem toriH0_eq (d : SelectionData n) (f : SelectionPhaseC n → ℂ) (b : SelectionR n) :
    toriH0 d f b = fun y => toriF d f (y + (0, selectionReal b)) - d.h (selectionReal b) := by
  funext y
  have hy : y + ((0 : SelectionC n), selectionReal b) = (y.1, y.2 + selectionReal b) := by
    ext <;> simp
  simp only [toriH0, selectionInitial, toriF, hy]
  rw [add_comm (selectionReal b) y.2]

theorem tori_H0_field (d : SelectionData n) (f : SelectionPhaseC n → ℂ) (b : SelectionR n)
    (y : SelectionPhaseC n) :
    hamiltonianVectorFieldℂ (toriH0 d f b) y =
      hamiltonianVectorFieldℂ (toriF d f) (y + (0, selectionReal b)) := by
  have h : fderiv ℂ (toriH0 d f b) y = fderiv ℂ (toriF d f) (y + (0, selectionReal b)) := by
    rw [toriH0_eq, fderiv_sub_const]
    exact fderiv_comp_add_right _
  unfold hamiltonianVectorFieldℂ
  rw [h]

section Field
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}
variable (cx : WeakBudgetCtx d a) (L : SelectionLimit d f a) {b : SelectionR n} {ε : ℝ}

theorem tori_eval_C (hb : b ∈ L.Kinf) (θ : SelectionR n) :
    realInclusion₂ n (selectionEvaluation L.defect b θ) =
      L.limitC b (selectionReal θ) + (0, selectionReal b) := by
  rw [tori_eval_eq L hb, map_add, ← isRealOnReals_iff.mp (tori_isReal L hb) θ]
  rfl

include cx in
theorem tori_invariance_real (hf : SelectionPerturbation d f ε) (hb : b ∈ L.Kinf)
    (θ : SelectionR n) :
    fderiv ℝ (selectionEvaluation L.defect b) θ (L.ωstar b) =
      hamiltonianVectorField (fun z : Phase n => realHamiltonian d.h f z)
        (selectionEvaluation L.defect b θ) := by
  have hopen : IsOpen (actionNbhd d.K (2 * d.ϑ)) := KAM.Head.isOpen_actionNbhd _ _
  have hV : IsOpen (complexStrip n d.strip ×ˢ actionNbhd d.K (2 * d.ϑ)) :=
    (KAM.isOpen_complexStrip n _).prod hopen
  have hFd : DifferentiableOn ℂ (toriF d f) (complexStrip n d.strip ×ˢ actionNbhd d.K (2 * d.ϑ)) :=
    (d.holo.comp differentiableOn_snd (fun y hy => hy.2)).add hf.holo
  have hreal : ∀ y : Phase n, realInclusion₂ n y ∈
      complexStrip n d.strip ×ˢ actionNbhd d.K (2 * d.ϑ) →
        (toriF d f (realInclusion₂ n y)).im = 0 :=
    fun y hy => by
      have e1 : (d.h (realInclusion n y.2)).im = 0 := d.real y.2 hy.2
      have e2 : (f (realInclusion n y.1, realInclusion n y.2)).im = 0 :=
        hf.real y (by rw [tori_phaseToC_eq]; exact hy)
      show (d.h (realInclusion n y.2) + f (realInclusion n y.1, realInclusion n y.2)).im = 0
      rw [Complex.add_im, e1, e2, add_zero]
  have hmem := tori_limit_mem cx L hb θ
  have hz : realInclusion₂ n (selectionEvaluation L.defect b θ) ∈
      complexStrip n d.strip ×ˢ actionNbhd d.K (2 * d.ϑ) := by
    rw [tori_eval_C L hb]
    refine ⟨?_, ?_⟩
    · simpa using hmem.1
    · refine ⟨b, tori_mem_d L hb, ?_⟩
      have : (L.limitC b (selectionReal θ) + (0, selectionReal b)).2 -
          (fun i => ((b i : ℝ) : ℂ)) = (L.limitC b (selectionReal θ)).2 := by
        funext i; simp [selectionReal]
      rw [this]
      linarith [hmem.2, d.theta_pos]
  have hH : ∀ᶠ y in 𝓝 (selectionEvaluation L.defect b θ),
      realHamiltonian d.h f y = (toriF d f (realInclusion₂ n y)).re :=
    Filter.Eventually.of_forall fun y => rfl
  have key := hamiltonianVectorField_eq_of_real hV hFd hreal hz hH
  refine realInclusion₂_injective n ?_
  rw [key, tori_fderiv_real L hb θ, ← tori_invariance_C cx L hf hb θ, tori_H0_field,
    tori_eval_C L hb]

end Field

end KAM.Planetary

end
