/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.Field
public import KAM.Nekhoroshev.Interfaces.HoloReal
public import KAM.ODE.Maximal
public import KAM.ODE.Hamiltonian

/-!
# Part N12: the maximal flow of the averaging field (`bpN:p12:s-flow#data`)

`avgMaximal` chooses the existing maximal-solution representation `KAM.ODE.IsMaximalSolution` of
the Hamiltonian field of `avgH h f ε` in `avgDomain n R` (default data `(0, 0, const)` when none
exists, e.g. outside the domain). `avgTm`, `avgTp`, `avgFlow`, `avgFlowDomain`, `avgOmega` are
read off from it, and `avgMaximal_spec` shows the choice is a maximal solution for every
`x ∈ avgDomain n R` (existence by `KAM.ODE.gen_maximal`; no differentiability premise).
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace KAM.Nekhoroshev

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

/-- Choice of the EXISTING maximal-solution representation, with default data outside W. -/
def avgMaximal (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ)
    (R ε : ℝ) (x : AvgPhase n) : EReal × EReal × (ℝ → AvgPhase n) :=
  if hex : ∃ p : EReal × EReal × (ℝ → AvgPhase n),
      KAM.ODE.IsMaximalSolution (KAM.hamiltonianVectorField (avgH h f ε))
        (avgDomain n R) x p.1 p.2.1 p.2.2 then Classical.choose hex
  else (0, 0, fun _ => x)
def avgTm (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ) (R ε : ℝ)
    (x : AvgPhase n) : EReal := (avgMaximal h f R ε x).1
def avgTp (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ) (R ε : ℝ)
    (x : AvgPhase n) : EReal := (avgMaximal h f R ε x).2.1
def avgFlow (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ) (R ε : ℝ)
    (t : ℝ) (x : AvgPhase n) : AvgPhase n := (avgMaximal h f R ε x).2.2 t
def avgFlowDomain (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ)
    (R ε : ℝ) : Set (ℝ × AvgPhase n) :=
  {p | p.2 ∈ avgDomain n R ∧
    p.1 ∈ KAM.ODE.eIoo (avgTm h f R ε p.2) (avgTp h f R ε p.2)}
def avgOmega (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ)
    (R ε t : ℝ) : Set (AvgPhase n) := {x | (t, x) ∈ avgFlowDomain h f R ε}

private theorem isOpen_avgDomain (n : ℕ) (R : ℝ) : IsOpen (avgDomain n R) :=
  isOpen_univ.prod isOpen_ball

/-- `ε f` is an analytic perturbation of size `|ε|` when `f` has size one. -/
private theorem data_smul (d : AveragingData n R s h f) (ε : ℝ) :
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

theorem avgMaximal_spec (d : AveragingData n R s h f) (ε : ℝ)
    {x : AvgPhase n} (hx : x ∈ avgDomain n R) :
    KAM.ODE.IsMaximalSolution (KAM.hamiltonianVectorField (avgH h f ε))
      (avgDomain n R) x (avgTm h f R ε x) (avgTp h f R ε x)
      (fun t => avgFlow h f R ε t x) := by
  have hW : IsOpen (Wdom n R s) := isOpen_univ.prod isOpen_ball
  have hsub : avgDomain n R ⊆ Wdom n R s := avgDomain_subset_Wdom d
  have hc : ContDiffOn ℝ 2 (avgH h f ε) (Wdom n R s) :=
    (holo_input (data_smul d ε)).1.of_le (by simp)
  have hF : ContDiffOn ℝ 1 (KAM.hamiltonianVectorField (avgH h f ε)) (avgDomain n R) :=
    (KAM.ODE.ham_smooth_c1 hW hc).mono hsub
  obtain ⟨hex, -⟩ := KAM.ODE.gen_maximal (isOpen_avgDomain n R) hF hx
  obtain ⟨Tm, Tp, z, hz⟩ := hex
  have hex' : ∃ p : EReal × EReal × (ℝ → AvgPhase n),
      KAM.ODE.IsMaximalSolution (KAM.hamiltonianVectorField (avgH h f ε))
        (avgDomain n R) x p.1 p.2.1 p.2.2 := ⟨(Tm, Tp, z), hz⟩
  have := Classical.choose_spec hex'
  simpa [avgTm, avgTp, avgFlow, avgMaximal, hex'] using this
end KAM.Nekhoroshev

end
