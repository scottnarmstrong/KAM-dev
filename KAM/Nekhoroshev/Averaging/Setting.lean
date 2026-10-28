/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Nekhoroshev.Defs.HasAveragingFrequencyRank
public import KAM.Frozen.Nekhoroshev.Defs.AveragingError
public import KAM.Nekhoroshev.Interfaces.HoloReal

/-!
# Part N12: standing data of the averaging lemma (`bpN:p12:s-setting#data`)

`AveragingData` carries only the source premises of Part 12 (it is not Part 1's perturbation-size
`Data`). The real phase domain `avgDomain`, the inner action compactum `avgG`, the perturbed
Hamiltonian `avgH`, the real partial fields `avgA`, `avgB` of `Re (f ∘ ι)` and the frequency
differential `avgM` are defined here, together with the finite compact bounds `Ω₀`, `M₂`
(`avg_compact_bounds`) on the closed action ball.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace KAM.Nekhoroshev

abbrev AvgPhase (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)
abbrev AvgComplexPhase (n : ℕ) := (Fin n → ℂ) × (Fin n → ℂ)

/-- Source premises only; this is not Part 1's perturbation-size `Data`. -/
structure AveragingData (n : ℕ) (R s : ℝ)
    (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ) : Prop where
  hn : 1 ≤ n
  hR : 0 < R
  hs : 0 < s
  hh : IsAnalyticIntegrable R s h
  hf : IsAnalyticPerturbation R s 1 f
  hrank : HasAveragingFrequencyRank (actionBall n R) h

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ}
  {f : AvgComplexPhase n → ℂ}

def avgDomain (n : ℕ) (R : ℝ) : Set (AvgPhase n) := univ ×ˢ actionBall n R
def avgG (n : ℕ) (R : ℝ) : Set (Fin n → ℝ) := closedBall 0 (3 * R / 4)
def avgH (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ) (ε : ℝ) :=
  KAM.realHamiltonian h (fun w => (ε : ℂ) * f w)
def avgA (f : AvgComplexPhase n → ℂ) (z : AvgPhase n) : Fin n → ℝ :=
  fun j => -(fderiv ℝ (fun y : AvgPhase n => (f (KAM.realInclusion₂ n y)).re)
    z (Pi.single j 1, 0))
def avgB (f : AvgComplexPhase n → ℂ) (z : AvgPhase n) : Fin n → ℝ :=
  fun j => fderiv ℝ (fun y : AvgPhase n => (f (KAM.realInclusion₂ n y)).re)
    z (0, Pi.single j 1)
def avgM (h : (Fin n → ℂ) → ℂ) (I : Fin n → ℝ) (i j : Fin n) : ℝ :=
  fderiv ℝ (KAM.frequencyMap h) I (Pi.single j 1) i

/-- The standing data give `Part 1`'s `Data` at size one. -/
theorem AveragingData.toData (d : AveragingData n R s h f) : Data n R s 1 h f :=
  ⟨d.hR, d.hs, d.hh, d.hf⟩

theorem avgDomain_subset_Wdom (d : AveragingData n R s h f) :
    avgDomain n R ⊆ Wdom n R s := fun _ hz =>
  ⟨mem_univ _, ball_subset_ball (by linarith [d.hs]) hz.2⟩

private theorem closedBall_subset_realActionDomain (d : AveragingData n R s h f) :
    closedBall (0 : Fin n → ℝ) R ⊆ realActionDomain n R s := by
  rw [realActionDomain_eq d.hR d.hs]
  exact closedBall_subset_ball (by linarith [d.hs])

private theorem contDiffOn_freq (d : AveragingData n R s h f) :
    ContDiffOn ℝ 2 (KAM.frequencyMap h) (realActionDomain n R s) := by
  have hg : ContDiffOn ℝ 3 (realPart h) (realActionDomain n R s) := d.hh.2.2.2.2
  have hU := isOpen_realActionDomain (n := n) d.hR d.hs
  have hd : ContDiffOn ℝ 2 (fderiv ℝ (realPart h)) (realActionDomain n R s) :=
    hg.fderiv_of_isOpen hU (by norm_num)
  refine contDiffOn_pi.2 fun i => ?_
  exact ContDiffOn.clm_apply hd (contDiffOn_const (c := (Pi.single i (1 : ℝ) : Fin n → ℝ)))

/-- The finite compact bounds `Ω₀` (frequency map) and `M₂` (row sums of `avgM`) on
`closedBall 0 R`. -/
theorem avg_compact_bounds (d : AveragingData n R s h f) :
    ∃ Ω₀ M₂ : ℝ, 0 ≤ Ω₀ ∧ 0 ≤ M₂ ∧
      (∀ I ∈ closedBall (0 : Fin n → ℝ) R, ‖KAM.frequencyMap h I‖ ≤ Ω₀) ∧
      (∀ I ∈ closedBall (0 : Fin n → ℝ) R, ∀ i, ∑ j, |avgM h I i j| ≤ M₂) := by
  have hU := isOpen_realActionDomain (n := n) d.hR d.hs
  have hK : IsCompact (closedBall (0 : Fin n → ℝ) R) := isCompact_closedBall _ _
  have hsub := closedBall_subset_realActionDomain d
  have hf2 := contDiffOn_freq d
  have hfc : ContinuousOn (KAM.frequencyMap h) (realActionDomain n R s) := hf2.continuousOn
  have hdc : ContinuousOn (fderiv ℝ (KAM.frequencyMap h)) (realActionDomain n R s) :=
    hf2.continuousOn_fderiv_of_isOpen hU (by norm_num)
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn (hfc.mono hsub)
  have hent : ∀ i j, ContinuousOn (fun I => avgM h I i j) (realActionDomain n R s) := by
    intro i j
    exact (continuous_apply i).comp_continuousOn
      (ContinuousOn.clm_apply hdc (continuousOn_const (c := (Pi.single j (1 : ℝ) : Fin n → ℝ))))
  have htot : ContinuousOn (fun I => ∑ i, ∑ j, |avgM h I i j|) (realActionDomain n R s) :=
    continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => (hent i j).abs
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn (htot.mono hsub)
  refine ⟨max 0 C₁, max 0 C₂, le_max_left _ _, le_max_left _ _, fun I hI => ?_, fun I hI i => ?_⟩
  · exact (hC₁ I hI).trans (le_max_right _ _)
  · calc ∑ j, |avgM h I i j| ≤ ∑ i, ∑ j, |avgM h I i j| :=
          Finset.single_le_sum (f := fun i => ∑ j, |avgM h I i j|)
            (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)
      _ ≤ ‖∑ i, ∑ j, |avgM h I i j|‖ := Real.le_norm_self _
      _ ≤ C₂ := hC₂ I hI
      _ ≤ max 0 C₂ := le_max_right _ _

end KAM.Nekhoroshev

end
