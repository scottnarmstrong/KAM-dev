/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.FlowRegular
public import KAM.Nekhoroshev.Averaging.FlowSymplectic

/-!
# Part N12: the averaging flow (`bpN:p12:flow`)

Openness of the flow domain, joint continuity of the flow and of its spatial derivative, `C¹`
time slices, the inverse `φ₋ₜ ∘ φₜ = id`, translation equivariance under `ℤⁿ` angle shifts, and
the symplectic determinant `det Dφₜ = 1`. The regularity comes from `FlowRegular`
(`avgFlow_regOn`); the determinant from `FlowSymplectic`.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff Topology
open KAM.ODE (IsSolutionIn IsMaximalSolution eIoo)

namespace KAM.Nekhoroshev

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

section Regularity

variable (d : AveragingData n R s h f) (ε : ℝ)
include d

theorem isOpen_avgFlowDomain : IsOpen (avgFlowDomain h f R ε) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  obtain ⟨J, U, hJ, hU, hpJ, hpU, hR⟩ := avgFlow_regOn d ε hp
  refine Filter.mem_of_superset (prod_mem_nhds (hJ.mem_nhds hpJ) (hU.mem_nhds hpU)) ?_
  rintro q ⟨hq1, hq2⟩
  exact ⟨hR.1 hq2, hR.2.1 q.2 hq2 hq1⟩

theorem continuousOn_avgFlow :
    ContinuousOn (fun p : ℝ × AvgPhase n => avgFlow h f R ε p.1 p.2)
      (avgFlowDomain h f R ε) := by
  intro p hp
  obtain ⟨J, U, hJ, hU, hpJ, hpU, hR⟩ := avgFlow_regOn d ε hp
  exact (hR.2.2.1.continuousAt
    (prod_mem_nhds (hJ.mem_nhds hpJ) (hU.mem_nhds hpU))).continuousWithinAt

theorem continuousOn_fderiv_avgFlow :
    ContinuousOn (fun p : ℝ × AvgPhase n => fderiv ℝ (avgFlow h f R ε p.1) p.2)
      (avgFlowDomain h f R ε) := by
  intro p hp
  obtain ⟨J, U, hJ, hU, hpJ, hpU, hR⟩ := avgFlow_regOn d ε hp
  exact (hR.2.2.2.1.continuousAt
    (prod_mem_nhds (hJ.mem_nhds hpJ) (hU.mem_nhds hpU))).continuousWithinAt

theorem isOpen_avgOmega (t : ℝ) : IsOpen (avgOmega h f R ε t) :=
  (isOpen_avgFlowDomain d ε).preimage (continuous_const.prodMk continuous_id)

theorem contDiffOn_avgFlow (t : ℝ) :
    ContDiffOn ℝ 1 (avgFlow h f R ε t) (avgOmega h f R ε t) := by
  have hΩ := isOpen_avgOmega d ε t
  have hdiff : ∀ x ∈ avgOmega h f R ε t,
      HasFDerivAt (avgFlow h f R ε t) (fderiv ℝ (avgFlow h f R ε t) x) x := by
    intro x hx
    obtain ⟨J, U, -, -, htJ, hxU, hR⟩ := avgFlow_regOn d ε (p := (t, x)) hx
    exact (hR.2.2.2.2 x hxU t htJ).1
  have hc : ContinuousOn (fderiv ℝ (avgFlow h f R ε t)) (avgOmega h f R ε t) :=
    (continuousOn_fderiv_avgFlow d ε).comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => hx)
  have := (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hΩ).2
    ⟨fun x hx => (hdiff x hx).differentiableAt.differentiableWithinAt, by simp,
      contDiffOn_zero.2 hc⟩
  simpa using this

end Regularity

section Inverse

variable (d : AveragingData n R s h f) (ε : ℝ)
include d

/-- The flow maps `Ω_t` into `Ω_{-t}` and `φ₋ₜ` inverts `φₜ` there. -/
theorem avgFlow_inverse {t : ℝ} {x : AvgPhase n} (hx : x ∈ avgOmega h f R ε t) :
    avgFlow h f R ε t x ∈ avgOmega h f R ε (-t) ∧
      avgFlow h f R ε (-t) (avgFlow h f R ε t x) = x := by
  have hmx := avgMaximal_spec d ε hx.1
  have hpW := (hmx.isSolution t hx.2).1
  have hmp := avgMaximal_spec d ε hpW
  have hI : IsOpen ((fun u => u + t) ⁻¹' eIoo (avgTm h f R ε x) (avgTp h f R ε x)) :=
    (KAM.ODE.isOpen_eIoo _ _).preimage (continuous_id.add continuous_const)
  have hIc : ((fun u => u + t) ⁻¹' eIoo (avgTm h f R ε x) (avgTp h f R ε x)).OrdConnected :=
    (KAM.ODE.ordConnected_eIoo _ _).preimage_mono fun a b hab => add_le_add_left hab _
  have h0 : (0 : ℝ) ∈ (fun u => u + t) ⁻¹' eIoo (avgTm h f R ε x) (avgTp h f R ε x) := by
    simpa using hx.2
  have := FlowChain.shift_sol (isOpen_avgDomain' n R) (avgField_contDiffOn d ε) hmp (t₀ := 0)
    (KAM.ODE.zero_mem_eIoo hmp) hI hIc h0
    (w := fun u => avgFlow h f R ε (u + t) x) (KAM.ODE.gen_symmetry_shift hmx.isSolution t)
    (by simpa using hmp.init.symm) (-t) (by simpa using KAM.ODE.zero_mem_eIoo hmx)
  obtain ⟨h1, h2⟩ := this
  refine ⟨⟨hpW, by simpa using h1⟩, ?_⟩
  have h3 : avgFlow h f R ε (-t) (avgFlow h f R ε t x) = avgFlow h f R ε (-t + t) x := by
    simpa using h2
  rw [h3, neg_add_cancel]
  exact hmx.init

end Inverse

end KAM.Nekhoroshev

end
