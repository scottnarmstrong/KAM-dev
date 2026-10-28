/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.Extension
public import KAM.Planetary.PGAssembly.JetsParam
public import KAM.Planetary.PGAssembly.JetsFamily

/-!
# P Part 5: holomorphy and continuity of the complex average (`bpP:p5:be-an`)

On the product domain `avgDom d = {(I, x) | I ∈ actionNbhd (closure V) (δ/2), ‖x‖ < r}` the
complex average `(I, x) ↦ complexAverage d mu I x` is holomorphic for every `mu ∈ [0, mu0]` and
jointly continuous in `(mu, I, x)`. Proof: the integrand is `P mu` composed with an affine map,
`holomorphic_parametric_integral` for holomorphy; dominated convergence (the bound `MP`) for the
joint continuity in `mu`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-JET.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Filter Topology

namespace KAM.Planetary

variable {a b : ℕ}

/-- The jet domain carrier `ℂᵃ × (ℂᵇ × ℂᵇ)`. -/
abbrev JetE (a b : ℕ) := (Fin a → ℂ) × PGComplexPhase b

theorem isOpen_extensionDomain (d : PGData a b) (delta : ℝ) : IsOpen (extensionDomain d delta) := by
  have : extensionDomain d delta = ⋃ w : Phase (a + b), ⋃ (_ : blockFast w.2 ∈ closure d.V ∧
      ‖(blockSlow w.2, blockSlow w.1)‖ ≤ d.r0 / 2), ball (KAM.realInclusion₂ (a + b) w) delta := by
    ext z
    simp [extensionDomain, dist_eq_norm, and_assoc]
  rw [this]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball

def avgDom (d : PGData a b) : Set (JetE a b) :=
  {z | z.1 ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2) ∧ ‖z.2‖ < pgOscRadius d}

theorem isOpen_avgDom (d : PGData a b) : IsOpen (avgDom d) :=
  ((isOpen_actionNbhd _ _).preimage continuous_fst).inter
    (isOpen_lt continuous_snd.norm continuous_const)

/-- The complex average as a function on the product domain. -/
def avgFun (d : PGData a b) (mu : ℝ) (z : JetE a b) : ℂ := complexAverage d mu z.1 z.2

/-- The integrand of the complex average. -/
def avgInt (d : PGData a b) (mu : ℝ) (phi : Fin a → ℝ) (z : JetE a b) : ℂ :=
  (pgExtension d).P mu (assembleComplex z.1 (KAM.realInclusion a phi) z.2.2 z.2.1)

/-- The linear part of `assembleComplex` in the variables `(I, x)`. -/
def assembleLin (a b : ℕ) : JetE a b →L[ℂ] PGComplexPhase (a + b) :=
  (ContinuousLinearMap.pi fun i : Fin (a + b) =>
      Fin.addCases (motive := fun _ => JetE a b →L[ℂ] ℂ) (fun _ => 0)
        (fun j => (ContinuousLinearMap.proj j).comp
          ((ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))) i).prod
    (ContinuousLinearMap.pi fun i : Fin (a + b) =>
      Fin.addCases (motive := fun _ => JetE a b →L[ℂ] ℂ)
        (fun j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℂ _ _))
        (fun j => (ContinuousLinearMap.proj j).comp
          ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))) i)

theorem assembleComplex_eq_add (phi : Fin a → ℝ) (z : JetE a b) :
    assembleComplex z.1 (KAM.realInclusion a phi) z.2.2 z.2.1 =
      assembleComplex 0 (KAM.realInclusion a phi) 0 0 + assembleLin a b z := by
  refine Prod.ext ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [assembleComplex, assembleLin]

theorem avgInt_mem (d : PGData a b) {z : JetE a b} (hz : z ∈ avgDom d) (phi : Fin a → ℝ) :
    assembleComplex z.1 (KAM.realInclusion a phi) z.2.2 z.2.1 ∈
      extensionDomain d (pgExtension d).delta := by
  have hpi := Real.pi_pos
  have hd := (pgExtension d).delta_pos
  have h := strip_mem_extensionDomain d hd hz.1
    (z.2.1.elim0 |> fun _ => hz.2.trans_le (min_le_right _ _) |> fun h => h) 
    (θ := fun j => ((phi j / (2 * Real.pi) : ℝ) : ℂ)) (fun j => by simpa using by positivity)
  sorry

end KAM.Planetary

end
