/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Weighted.Norm
public import KAM.Strip.FourierSeries
public import KAM.Frozen.Planetary.Defs.SecularAverage
public import KAM.Planetary.PGAssembly.ExtensionDefs
public import KAM.Planetary.PGAssembly.ExtensionExists
public import KAM.Planetary.PGAssembly.ExtensionConsts

/-!
# P Part 5: the thin periodic complex extension (`bpP:p5:ext`, `bpP:p5:consts`)

Facade of package P5-EX. `ext` (with the steps `ext-loc`, `ext-glue`, `ext-per`, `ext-H0` in
`ExtensionTubeData`, `ExtensionTubeP`, `ExtensionProps`, `ExtensionExists`), the selected
extension `pgExtension`, the width/radius `pgWidth`, `pgOscRadius`, the complex angular average
`complexAverage` with its attachment `complexAverage_real` to the frozen `secularAverage`, and
the fixed weighted bound `consts` (from `ExtensionConsts`).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md` (revision 4), package P5-EX.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped BigOperators

namespace KAM.Planetary

variable {a b n : ℕ}

theorem ext (d : PGData a b) : Nonempty (PGExtension d) := pgExtension_exists d

def pgExtension (d : PGData a b) : PGExtension d := Classical.choice (ext d)

def pgWidth (d : PGData a b) : ℝ := (pgExtension d).delta/2

def pgOscRadius (d : PGData a b) : ℝ := min (d.r0/2) ((pgExtension d).delta/4)

def complexAverage (d : PGData a b) (mu : ℝ) (I : Fin a → ℂ)
    (x : PGComplexPhase b) : ℂ :=
  ((2*Real.pi : ℂ)^a)⁻¹ * ∫ phi in (pi univ fun _ : Fin a => Icc (0:ℝ) (2*Real.pi)),
    (pgExtension d).P mu (assembleComplex I (KAM.realInclusion a phi) x.2 x.1)

/-- Attachment to the actual frozen normalized secular average, only on its constrained domain. -/
theorem complexAverage_real (d : PGData a b) (mu : ℝ) (hmu : mu ∈ Icc 0 d.mu0)
    (I : Fin a → ℝ) (hI : I ∈ d.V) (p q : Fin b → ℝ) (hx : ‖(p,q)‖ < pgOscRadius d) :
    complexAverage d mu (KAM.realInclusion a I) (KAM.realInclusion b q,KAM.realInclusion b p) =
      (secularAverage d.P mu I p q : ℂ) := by
  have hr : ‖(p, q)‖ < d.r0 / 2 := hx.trans_le (min_le_left _ _)
  have hp : ∀ j, |p j| < d.r0 / 2 := fun j => by
    have h := norm_le_pi_norm p j
    rw [Real.norm_eq_abs] at h
    exact h.trans_lt ((le_max_left _ _).trans_lt (by rwa [Prod.norm_def] at hr))
  have hq : ∀ j, |q j| < d.r0 / 2 := fun j => by
    have h := norm_le_pi_norm q j
    rw [Real.norm_eq_abs] at h
    exact h.trans_lt ((le_max_right _ _).trans_lt (by rwa [Prod.norm_def] at hr))
  have hint : ∀ phi : Fin a → ℝ,
      (pgExtension d).P mu (assembleComplex (KAM.realInclusion a I) (KAM.realInclusion a phi)
        (KAM.realInclusion b p) (KAM.realInclusion b q)) = (d.P mu (assemble I phi p q) : ℂ) := by
    intro phi
    rw [assembleComplex_real]
    have hfast : blockFast (assemble I phi p q).2 = I :=
      funext fun i => Fin.append_left _ _ i
    refine (pgExtension d).agrees mu hmu _ (subset_closure ⟨?_, fun j => ?_⟩) ?_
    · show blockFast (assemble I phi p q).2 ∈ d.V
      rw [hfast]; exact hI
    · have e1 : slow (assemble I phi p q).2 j = p j := Fin.append_right _ _ j
      have e2 : slow (assemble I phi p q).1 j = q j := Fin.append_right _ _ j
      rw [e1, e2]
      have h1 : p j ^ 2 < (d.r0 / 2) ^ 2 := by
        rw [← sq_abs]; exact pow_lt_pow_left₀ (hp j) (abs_nonneg _) (by norm_num)
      have h2 : q j ^ 2 < (d.r0 / 2) ^ 2 := by
        rw [← sq_abs]; exact pow_lt_pow_left₀ (hq j) (abs_nonneg _) (by norm_num)
      nlinarith [d.hr0]
    · refine ⟨assemble I phi p q, ?_, ?_, ?_⟩
      · rw [hfast]; exact subset_closure hI
      · have e1 : blockSlow (assemble I phi p q).2 = p := funext fun i => Fin.append_right _ _ i
        have e2 : blockSlow (assemble I phi p q).1 = q := funext fun i => Fin.append_right _ _ i
        rw [e1, e2]; exact hr.le
      · simp [(pgExtension d).delta_pos]
  unfold complexAverage
  simp only [hint]
  simp [secularAverage, integral_complex_ofReal, zpow_neg]

theorem consts (d : PGData a b) : ∃ LP : ℝ, 1 ≤ LP ∧
    ∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2),
    ∀ x : PGComplexPhase b, ‖x‖ < pgOscRadius d →
      KAM.Fourier.SummableWeighted (pgWidth d)
        (KAM.torusCoeff (fun phi => (pgExtension d).P mu
          (assembleComplex I ((2*Real.pi:ℂ) • KAM.realInclusion a phi) x.2 x.1))) ∧
      KAM.Fourier.weightedNorm (pgWidth d)
        (KAM.torusCoeff (fun phi => (pgExtension d).P mu
          (assembleComplex I ((2*Real.pi:ℂ) • KAM.realInclusion a phi) x.2 x.1))) ≤ LP := by
  refine ⟨max 1 (KAM.Weighted.coth ((pgExtension d).delta / 4) ^ a * (pgExtension d).MP),
    le_max_left _ _, ?_⟩
  intro mu hmu I hI x hx
  obtain ⟨h1, h2⟩ := (pgExtension d).summable_torus hmu hI (hx.trans_le (min_le_right _ _))
  refine ⟨h1, h2.trans (le_trans (le_of_eq ?_) (le_max_right _ _))⟩
  have hpi := Real.pi_pos
  have e : Real.pi * ((pgExtension d).delta / (4 * Real.pi)) = (pgExtension d).delta / 4 := by
    field_simp
  rw [e]
  rfl

end KAM.Planetary

end
