/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.CylinderCell
public import KAM.Frozen.Planetary.Defs.OscillatorAction
public import KAM.Planetary.PG.Setting
public import KAM.Planetary.PGMeasure.Collar
public import KAM.Planetary.Hamiltonian.Chart
public import KAM.Planetary.Poincare.Lattice

/-!
# P Parts 4-5: the general oscillator polar chart and the disc measure

`bpP:p4:s-disc#chart`, `bpP:p4:disc-measure`.  The chart `oscillatorPolar` extends the P7 `polarMap`
to arbitrary `a, b` (`oscillatorPolar_eq_polarMap` at `a = b`), `disc_measure_chart` gives
analyticity,
symplecticity, the unit Jacobian, injectivity on one cell and lattice injectivity,
`disc_measure_image` the area formula for the cell map, and `disc_measure`, `disc_measure_shell` the
cell volume, the null-centre coverage and the shell estimate.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P4-POL.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped BigOperators ContDiff

namespace KAM.Planetary

variable {a b n : ℕ}

/-- General a,b extension of the existing Kepler `polarMap`; same formula at a=b. -/
def oscillatorPolar (z : Phase (a+b)) : Phase (a+b) :=
  assemble (blockFast z.2) (blockFast z.1)
    (fun j => Real.sqrt (2*blockSlow z.2 j)*Real.cos (blockSlow z.1 j))
    (fun j => Real.sqrt (2*blockSlow z.2 j)*Real.sin (blockSlow z.1 j))

theorem oscillatorPolar_eq_polarMap (z : Phase (n+n)) :
    oscillatorPolar (a:=n) (b:=n) z = polarMap z := rfl

def polarCellMap (z : Phase (a+b)) : Phase (a+b) :=
  oscillatorPolar ((2*Real.pi) • z.1,z.2)


/-! ### Derivative of the chart -/

/-- Coordinate `i` of the angle block as a continuous linear functional. -/
private def angCLM (a b : ℕ) (i : Fin (a+b)) : Phase (a+b) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (a+b) => ℝ) i).comp
    (ContinuousLinearMap.fst ℝ _ _)

/-- Coordinate `i` of the action block as a continuous linear functional. -/
private def actCLM (a b : ℕ) (i : Fin (a+b)) : Phase (a+b) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (a+b) => ℝ) i).comp
    (ContinuousLinearMap.snd ℝ _ _)

private theorem angCLM_apply (i : Fin (a+b)) (u : Phase (a+b)) : angCLM a b i u = u.1 i := rfl

private theorem actCLM_apply (i : Fin (a+b)) (u : Phase (a+b)) : actCLM a b i u = u.2 i := rfl

private theorem hasFDerivAt_sinTerm {z : Phase (a+b)} (j : Fin b) (hR : 0 < z.2 (Fin.natAdd a j)) :
    ∃ L : Phase (a+b) →L[ℝ] ℝ,
      HasFDerivAt (fun w : Phase (a+b) =>
        Real.sqrt (2 * w.2 (Fin.natAdd a j)) * Real.sin (w.1 (Fin.natAdd a j))) L z ∧
      ∀ u : Phase (a+b), L u =
        (Real.sqrt (2 * z.2 (Fin.natAdd a j)))⁻¹ * Real.sin (z.1 (Fin.natAdd a j)) *
            u.2 (Fin.natAdd a j) +
          Real.sqrt (2 * z.2 (Fin.natAdd a j)) * Real.cos (z.1 (Fin.natAdd a j)) *
            u.1 (Fin.natAdd a j) := by
  have h2R : (2 * z.2 (Fin.natAdd a j)) ≠ 0 := by positivity
  have hs : HasFDerivAt (fun w : Phase (a+b) => Real.sqrt (2 * w.2 (Fin.natAdd a j)))
      ((1 / (2 * Real.sqrt (2 * z.2 (Fin.natAdd a j)))) •
        ((2 : ℝ) • actCLM a b (Fin.natAdd a j))) z :=
    (((actCLM a b (Fin.natAdd a j)).hasFDerivAt.const_mul 2)).sqrt h2R
  have hsin : HasFDerivAt (fun w : Phase (a+b) => Real.sin (w.1 (Fin.natAdd a j)))
      (Real.cos (z.1 (Fin.natAdd a j)) • angCLM a b (Fin.natAdd a j)) z :=
    (angCLM a b (Fin.natAdd a j)).hasFDerivAt.sin
  refine ⟨_, hs.mul hsin, fun u => ?_⟩
  have hpos : 0 < Real.sqrt (2 * z.2 (Fin.natAdd a j)) := Real.sqrt_pos.2 (by positivity)
  simp only [add_apply, smul_apply, smul_eq_mul,
    angCLM_apply, actCLM_apply]
  field_simp
  ring

private theorem hasFDerivAt_cosTerm {z : Phase (a+b)} (j : Fin b) (hR : 0 < z.2 (Fin.natAdd a j)) :
    ∃ L : Phase (a+b) →L[ℝ] ℝ,
      HasFDerivAt (fun w : Phase (a+b) =>
        Real.sqrt (2 * w.2 (Fin.natAdd a j)) * Real.cos (w.1 (Fin.natAdd a j))) L z ∧
      ∀ u : Phase (a+b), L u =
        (Real.sqrt (2 * z.2 (Fin.natAdd a j)))⁻¹ * Real.cos (z.1 (Fin.natAdd a j)) *
            u.2 (Fin.natAdd a j) -
          Real.sqrt (2 * z.2 (Fin.natAdd a j)) * Real.sin (z.1 (Fin.natAdd a j)) *
            u.1 (Fin.natAdd a j) := by
  have h2R : (2 * z.2 (Fin.natAdd a j)) ≠ 0 := by positivity
  have hs : HasFDerivAt (fun w : Phase (a+b) => Real.sqrt (2 * w.2 (Fin.natAdd a j)))
      ((1 / (2 * Real.sqrt (2 * z.2 (Fin.natAdd a j)))) •
        ((2 : ℝ) • actCLM a b (Fin.natAdd a j))) z :=
    (((actCLM a b (Fin.natAdd a j)).hasFDerivAt.const_mul 2)).sqrt h2R
  have hcos : HasFDerivAt (fun w : Phase (a+b) => Real.cos (w.1 (Fin.natAdd a j)))
      (-Real.sin (z.1 (Fin.natAdd a j)) • angCLM a b (Fin.natAdd a j)) z :=
    (angCLM a b (Fin.natAdd a j)).hasFDerivAt.cos
  refine ⟨_, hs.mul hcos, fun u => ?_⟩
  have hpos : 0 < Real.sqrt (2 * z.2 (Fin.natAdd a j)) := Real.sqrt_pos.2 (by positivity)
  simp only [add_apply, smul_apply, smul_eq_mul,
    angCLM_apply, actCLM_apply]
  field_simp
  ring

/-- The Fréchet derivative of `oscillatorPolar` on the positive-action domain, componentwise. -/
theorem hasFDerivAt_oscillatorPolar {z : Phase (a+b)} (hz : ∀ j : Fin b, 0 < blockSlow z.2 j) :
    ∃ L : Phase (a+b) →L[ℝ] Phase (a+b),
      HasFDerivAt (oscillatorPolar (a:=a) (b:=b)) L z ∧
      (∀ u : Phase (a+b), ∀ i : Fin a,
        (L u).1 (Fin.castAdd b i) = u.1 (Fin.castAdd b i) ∧
        (L u).2 (Fin.castAdd b i) = u.2 (Fin.castAdd b i)) ∧
      (∀ u : Phase (a+b), ∀ j : Fin b,
        (L u).1 (Fin.natAdd a j) =
          (Real.sqrt (2 * z.2 (Fin.natAdd a j)))⁻¹ * Real.sin (z.1 (Fin.natAdd a j)) *
              u.2 (Fin.natAdd a j) +
            Real.sqrt (2 * z.2 (Fin.natAdd a j)) * Real.cos (z.1 (Fin.natAdd a j)) *
              u.1 (Fin.natAdd a j) ∧
        (L u).2 (Fin.natAdd a j) =
          (Real.sqrt (2 * z.2 (Fin.natAdd a j)))⁻¹ * Real.cos (z.1 (Fin.natAdd a j)) *
              u.2 (Fin.natAdd a j) -
            Real.sqrt (2 * z.2 (Fin.natAdd a j)) * Real.sin (z.1 (Fin.natAdd a j)) *
              u.1 (Fin.natAdd a j)) := by
  choose Ls hLs hLsu using fun j : Fin b => hasFDerivAt_sinTerm (z := z) j (hz j)
  choose Lc hLc hLcu using fun j : Fin b => hasFDerivAt_cosTerm (z := z) j (hz j)
  let L1 : Fin (a+b) → (Phase (a+b) →L[ℝ] ℝ) := fun i =>
    Fin.addCases (motive := fun _ => Phase (a+b) →L[ℝ] ℝ)
      (fun k => angCLM a b (Fin.castAdd b k)) (fun j => Ls j) i
  let L2 : Fin (a+b) → (Phase (a+b) →L[ℝ] ℝ) := fun i =>
    Fin.addCases (motive := fun _ => Phase (a+b) →L[ℝ] ℝ)
      (fun k => actCLM a b (Fin.castAdd b k)) (fun j => Lc j) i
  have h1 : HasFDerivAt (fun w : Phase (a+b) => (oscillatorPolar w).1)
      (ContinuousLinearMap.pi L1) z := by
    refine hasFDerivAt_pi'.2 fun i => ?_
    refine Fin.addCases (fun k => ?_) (fun j => ?_) i
    · have : HasFDerivAt (fun w : Phase (a+b) => w.1 (Fin.castAdd b k))
        (angCLM a b (Fin.castAdd b k)) z := (angCLM a b (Fin.castAdd b k)).hasFDerivAt
      simpa [L1, oscillatorPolar, assemble, Fin.append_left, blockFast, angCLM_apply] using this
    · simpa [L1, oscillatorPolar, assemble, Fin.append_right, blockSlow] using hLs j
  have h2 : HasFDerivAt (fun w : Phase (a+b) => (oscillatorPolar w).2)
      (ContinuousLinearMap.pi L2) z := by
    refine hasFDerivAt_pi'.2 fun i => ?_
    refine Fin.addCases (fun k => ?_) (fun j => ?_) i
    · have : HasFDerivAt (fun w : Phase (a+b) => w.2 (Fin.castAdd b k))
        (actCLM a b (Fin.castAdd b k)) z := (actCLM a b (Fin.castAdd b k)).hasFDerivAt
      simpa [L2, oscillatorPolar, assemble, Fin.append_left, blockFast, actCLM_apply] using this
    · simpa [L2, oscillatorPolar, assemble, Fin.append_right, blockSlow] using hLc j
  refine ⟨(ContinuousLinearMap.pi L1).prod (ContinuousLinearMap.pi L2), h1.prodMk h2, ?_, ?_⟩
  · intro u i
    simp [L1, L2, angCLM_apply, actCLM_apply]
  · intro u j
    simp [L1, L2, hLsu, hLcu]


/-! ### Coordinates of the chart -/

@[simp] theorem oscillatorPolar_fst_castAdd (z : Phase (a+b)) (i : Fin a) :
    (oscillatorPolar z).1 (Fin.castAdd b i) = z.1 (Fin.castAdd b i) := by
  simp [oscillatorPolar, assemble, Fin.append_left, blockFast]

@[simp] theorem oscillatorPolar_snd_castAdd (z : Phase (a+b)) (i : Fin a) :
    (oscillatorPolar z).2 (Fin.castAdd b i) = z.2 (Fin.castAdd b i) := by
  simp [oscillatorPolar, assemble, Fin.append_left, blockFast]

@[simp] theorem oscillatorPolar_fst_natAdd (z : Phase (a+b)) (j : Fin b) :
    (oscillatorPolar z).1 (Fin.natAdd a j) =
      Real.sqrt (2 * z.2 (Fin.natAdd a j)) * Real.sin (z.1 (Fin.natAdd a j)) := by
  simp [oscillatorPolar, assemble, Fin.append_right, blockSlow]

@[simp] theorem oscillatorPolar_snd_natAdd (z : Phase (a+b)) (j : Fin b) :
    (oscillatorPolar z).2 (Fin.natAdd a j) =
      Real.sqrt (2 * z.2 (Fin.natAdd a j)) * Real.cos (z.1 (Fin.natAdd a j)) := by
  simp [oscillatorPolar, assemble, Fin.append_right, blockSlow]

/-- Two phase points with equal coordinates in both index blocks are equal. -/
theorem phase_ext_blocks {z z' : Phase (a+b)}
    (h1 : ∀ i : Fin a, z.1 (Fin.castAdd b i) = z'.1 (Fin.castAdd b i))
    (h2 : ∀ i : Fin a, z.2 (Fin.castAdd b i) = z'.2 (Fin.castAdd b i))
    (h3 : ∀ j : Fin b, z.1 (Fin.natAdd a j) = z'.1 (Fin.natAdd a j))
    (h4 : ∀ j : Fin b, z.2 (Fin.natAdd a j) = z'.2 (Fin.natAdd a j)) : z = z' := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    refine Fin.addCases (fun k => ?_) (fun j => ?_) i <;> simp [h1, h2, h3, h4]

private theorem analyticAt_oscillatorPolar {z : Phase (a+b)}
    (hz : ∀ j : Fin b, 0 < blockSlow z.2 j) : AnalyticAt ℝ (oscillatorPolar (a:=a) (b:=b)) z := by
  have hs : ∀ j : Fin b,
      AnalyticAt ℝ (fun w : Phase (a+b) => Real.sqrt (2 * w.2 (Fin.natAdd a j))) z := fun j =>
    (((analyticAt_const.mul ((actCLM a b (Fin.natAdd a j)).analyticAt z)).contDiffAt
      (n := ω)).sqrt (by have := hz j; simp only [blockSlow] at this
                         show 2 * z.2 (Fin.natAdd a j) ≠ 0
                         positivity)).analyticAt
  refine AnalyticAt.prod (AnalyticAt.pi fun i => ?_) (AnalyticAt.pi fun i => ?_)
  · refine Fin.addCases (fun k => ?_) (fun j => ?_) i
    · have h : AnalyticAt ℝ (fun x : Phase (a+b) => x.1 (Fin.castAdd b k)) z :=
        (angCLM a b (Fin.castAdd b k)).analyticAt z
      simpa [blockFast] using h
    · have h : AnalyticAt ℝ (fun w : Phase (a+b) =>
          Real.sqrt (2 * w.2 (Fin.natAdd a j)) * Real.sin (w.1 (Fin.natAdd a j))) z :=
        (hs j).mul (Real.analyticAt_sin.comp ((angCLM a b (Fin.natAdd a j)).analyticAt z))
      show AnalyticAt ℝ (fun w : Phase (a+b) => (oscillatorPolar w).1 (Fin.natAdd a j)) z
      simp only [oscillatorPolar_fst_natAdd]
      exact h
  · refine Fin.addCases (fun k => ?_) (fun j => ?_) i
    · have h : AnalyticAt ℝ (fun x : Phase (a+b) => x.2 (Fin.castAdd b k)) z :=
        (actCLM a b (Fin.castAdd b k)).analyticAt z
      simpa [blockFast] using h
    · have h : AnalyticAt ℝ (fun w : Phase (a+b) =>
          Real.sqrt (2 * w.2 (Fin.natAdd a j)) * Real.cos (w.1 (Fin.natAdd a j))) z :=
        (hs j).mul (Real.analyticAt_cos.comp ((angCLM a b (Fin.natAdd a j)).analyticAt z))
      show AnalyticAt ℝ (fun w : Phase (a+b) => (oscillatorPolar w).2 (Fin.natAdd a j)) z
      simp only [oscillatorPolar_snd_natAdd]
      exact h

private theorem oscillatorPolar_symplectic {z : Phase (a+b)}
    (hz : ∀ j : Fin b, 0 < blockSlow z.2 j) (u v : Phase (a+b)) :
    KAM.symplecticForm (fderiv ℝ (oscillatorPolar (a:=a) (b:=b)) z u)
      (fderiv ℝ (oscillatorPolar (a:=a) (b:=b)) z v) = 1 * KAM.symplecticForm u v := by
  obtain ⟨L, hL, hfast, hslow⟩ := hasFDerivAt_oscillatorPolar hz
  rw [hL.fderiv]
  simp only [KAM.symplecticForm, Fin.sum_univ_add, one_mul]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hfast u i).1, (hfast u i).2, (hfast v i).1, (hfast v i).2]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hR : 0 < z.2 (Fin.natAdd a j) := hz j
    rw [(hslow u j).1, (hslow u j).2, (hslow v j).1, (hslow v j).2]
    have hs : Real.sqrt (2 * z.2 (Fin.natAdd a j)) * (Real.sqrt (2 * z.2 (Fin.natAdd a j)))⁻¹ = 1 :=
      mul_inv_cancel₀ (by positivity)
    have hsc := Real.sin_sq_add_cos_sq (z.1 (Fin.natAdd a j))
    set w := u.1 (Fin.natAdd a j) * v.2 (Fin.natAdd a j) -
      u.2 (Fin.natAdd a j) * v.1 (Fin.natAdd a j) with hw
    linear_combination
      (-w * (Real.sin (z.1 (Fin.natAdd a j)) ^ 2 + Real.cos (z.1 (Fin.natAdd a j)) ^ 2)) * hs -
      w * hsc

end KAM.Planetary

end
