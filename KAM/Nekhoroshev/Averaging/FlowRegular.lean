/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.FlowChain
public import KAM.Nekhoroshev.Averaging.FlowDefs

/-!
# Part N12: regularity of the maximal flow (`bpN:p12:flow`, `fl-short`, `fl-chain`, part (b))

The generic chaining of `KAM.Nekhoroshev.FlowChain` applied to the Hamiltonian field of `avgH h f ε`
on `avgDomain n R`, whose maximal solutions are the chosen `avgMaximal`.

* `KAM.Nekhoroshev.avgField_contDiffOn`: the field is `C¹` on the (open) domain.
* `KAM.Nekhoroshev.avgFlow_regOn`: a regular neighborhood of every point of `avgFlowDomain`.
* `KAM.Nekhoroshev.flow_variational`: the time derivative of the initial derivative.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace KAM.Nekhoroshev

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

theorem isOpen_avgDomain' (n : ℕ) (R : ℝ) : IsOpen (avgDomain n R) :=
  isOpen_univ.prod isOpen_ball

/-- `ε f` is an analytic perturbation of size `|ε|` when `f` has size one. -/
private theorem data_smul' (d : AveragingData n R s h f) (ε : ℝ) :
    Data n R s |ε| h (fun w => (ε : ℂ) * f w) := by
  obtain ⟨h0, hdiff, hcont, hper, him, hnorm⟩ := d.hf
  refine ⟨d.hR, d.hs, d.hh, abs_nonneg ε, ?_, ?_, ?_, ?_, ?_⟩
  · exact (differentiableOn_const _).mul hdiff
  · exact continuousOn_const.mul hcont
  · intro z hz k
    simp only [hper z hz k]
  · intro θ I hI
    simp [him θ I hI]
  · intro z hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |ε| * ‖f z‖ ≤ |ε| * 1 := by gcongr; exact hnorm z hz
      _ = |ε| := mul_one _

/-- The averaging Hamiltonian is `C²` on `Wdom`, hence on the action domain. -/
theorem avgH_contDiffOn (d : AveragingData n R s h f) (ε : ℝ) :
    ContDiffOn ℝ 2 (avgH h f ε) (Wdom n R s) :=
  (holo_input (data_smul' d ε)).1.of_le (by simp)

/-- The Hamiltonian field of `avgH h f ε` is `C¹` on the action domain. -/
theorem avgField_contDiffOn (d : AveragingData n R s h f) (ε : ℝ) :
    ContDiffOn ℝ 1 (KAM.hamiltonianVectorField (avgH h f ε)) (avgDomain n R) :=
  (KAM.ODE.ham_smooth_c1 (isOpen_univ.prod isOpen_ball) (avgH_contDiffOn d ε)).mono
    (avgDomain_subset_Wdom d)

/-- A regular neighborhood of each point of the flow domain. -/
theorem avgFlow_regOn (d : AveragingData n R s h f) (ε : ℝ) {p : ℝ × AvgPhase n}
    (hp : p ∈ avgFlowDomain h f R ε) :
    ∃ (J : Set ℝ) (U : Set (AvgPhase n)), IsOpen J ∧ IsOpen U ∧ p.1 ∈ J ∧ p.2 ∈ U ∧
      FlowChain.RegOn (KAM.hamiltonianVectorField (avgH h f ε)) (avgDomain n R)
        (avgTm h f R ε) (avgTp h f R ε) (fun x t => avgFlow h f R ε t x) J U :=
  FlowChain.reg_all (isOpen_avgDomain' n R) (avgField_contDiffOn d ε)
    (fun _ hx => avgMaximal_spec d ε hx) hp.1 hp.2

theorem flow_variational (d : AveragingData n R s h f) (ε : ℝ)
    {x : AvgPhase n} {t : ℝ} (hp : (t, x) ∈ avgFlowDomain h f R ε) :
    HasDerivAt (fun u => fderiv ℝ (avgFlow h f R ε u) x)
      ((fderiv ℝ (KAM.hamiltonianVectorField (avgH h f ε)) (avgFlow h f R ε t x)).comp
        (fderiv ℝ (avgFlow h f R ε t) x)) t := by
  obtain ⟨J, U, -, -, htJ, hxU, hR⟩ := avgFlow_regOn d ε hp
  exact (hR.2.2.2.2 x hxU t htJ).2

end KAM.Nekhoroshev

end
