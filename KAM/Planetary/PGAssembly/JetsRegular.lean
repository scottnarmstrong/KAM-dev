/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.JetsSlice
public import KAM.Planetary.PGAssembly.JetsIdent
public import KAM.Planetary.PGAssembly.RealSlice

/-!
# P Part 5: regularity of the jets in the actions (`bpP:p5:be-an`)

On the tube `actionNbhd (closure V) (δ/2)`: `jetP0`, `jetOmega`, `jetBeta` are holomorphic in `I`
for each `mu` and jointly continuous in `(mu, I)`; `jetBeta` is symmetric (permutation symmetry
of the fourth derivative of the analytic average).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-JET.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology
open scoped BigOperators

namespace KAM.Planetary

variable {a b : ℕ}

theorem tube_eq_zero_slice (d : PGData a b) :
    {I : Fin a → ℂ | (I, (0 : PGComplexPhase b)) ∈ avgDom d} =
      KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2) :=
  Set.ext fun _ => ⟨fun h => h.1, mem_avgDom_zero d⟩

theorem jetP0_differentiableOn (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) :
    DifferentiableOn ℂ (jetP0 d mu) (KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) :=
  (avgFun_differentiableOn d hmu).comp
    (differentiable_id.prodMk (differentiable_const _)).differentiableOn
    (fun _ hI => mem_avgDom_zero d hI)

theorem jetOmega_differentiableOn (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) (j : Fin b) :
    DifferentiableOn ℂ (fun I => jetOmega d mu I j)
      (KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) := by
  have := differentiableOn_slice_jet (isOpen_avgDom d) (avgFun_differentiableOn d hmu) 2
    (fun _ => ((0 : Fin b → ℂ), (Pi.single j 1 : Fin b → ℂ)))
  rw [tube_eq_zero_slice] at this
  exact this

theorem jetBeta_differentiableOn (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) (i j : Fin b) :
    DifferentiableOn ℂ (fun I => jetBeta d mu I i j)
      (KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) := by
  have h4 := fun w : Fin 4 → PGComplexPhase b =>
    differentiableOn_slice_jet (isOpen_avgDom d) (avgFun_differentiableOn d hmu) 4 w
  rw [tube_eq_zero_slice] at h4
  by_cases hij : i = j
  · simp only [jetBeta, hij, ite_true]
    exact (h4 (fun _ => ((0 : Fin b → ℂ), (Pi.single j 1 : Fin b → ℂ)))).const_smul (1 / 3 : ℂ)
      |>.congr fun I _ => by rfl
  · simp only [jetBeta, hij, ite_false]
    exact h4 _

theorem jet_continuousOn (d : PGData a b) :
    ContinuousOn (fun z : ℝ × (Fin a → ℂ) => jetP0 d z.1 z.2)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) ∧
    (∀ j, ContinuousOn (fun z : ℝ × (Fin a → ℂ) => jetOmega d z.1 z.2 j)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2))) ∧
    (∀ i j, ContinuousOn (fun z : ℝ × (Fin a → ℂ) => jetBeta d z.1 z.2 i j)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2))) := by
  have hT : IsCompact (Icc (0 : ℝ) d.mu0) := isCompact_Icc
  have hd : ∀ μ ∈ Icc (0 : ℝ) d.mu0, DifferentiableOn ℂ (avgFun d μ) (avgDom d) :=
    fun μ hμ => avgFun_differentiableOn d hμ
  have hc := avgFun_continuousOn d
  have hj := fun (k : ℕ) (w : Fin k → PGComplexPhase b) =>
    continuousOn_slice_jet hT (isOpen_avgDom d) hd hc k w
  simp only [tube_eq_zero_slice] at hj
  refine ⟨?_, fun j => ?_, fun i j => ?_⟩
  · have := hj 0 (fun _ => 0)
    refine (this.congr fun z _ => ?_)
    simp [jetP0, complexAverage, avgFun]
  · exact hj 2 (fun _ => ((0 : Fin b → ℂ), (Pi.single j 1 : Fin b → ℂ)))
  · by_cases hij : i = j
    · simp only [jetBeta, hij, ite_true]
      exact (hj 4 (fun _ => ((0 : Fin b → ℂ), (Pi.single j 1 : Fin b → ℂ)))).const_smul
        (1 / 3 : ℂ) |>.congr fun z _ => by rfl
    · simp only [jetBeta, hij, ite_false]
      exact hj 4 _

theorem jetBeta_isSymm (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℂ} (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) :
    (jetBeta d mu I).IsSymm := by
  have hA := complexAverage_analyticAt d hmu hI
  ext i j
  simp only [Matrix.transpose_apply]
  by_cases hij : i = j
  · rw [hij]
  · have hji : j ≠ i := Ne.symm hij
    simp only [jetBeta, hij, hji, ite_false]
    set σ : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3 with hσ
    have := hA.contDiffAt.iteratedFDeriv_comp_perm
      (fun k : Fin 4 => if k.val < 2 then
        ((0 : Fin b → ℂ), (Pi.single i (1 : ℂ) : Fin b → ℂ)) else
        ((0 : Fin b → ℂ), (Pi.single j (1 : ℂ) : Fin b → ℂ))) σ (n := 4)
    refine Eq.trans ?_ this
    congr 1
    funext k
    fin_cases k <;> simp [hσ, Equiv.swap_apply_def]

end KAM.Planetary

end
