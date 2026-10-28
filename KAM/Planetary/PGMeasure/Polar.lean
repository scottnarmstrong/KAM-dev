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
to arbitrary `a, b` (`oscillatorPolar_eq_polarMap` at `a = b`), `disc_measure_chart` gives analyticity,
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
    linear_combination
      (-(u.1 (Fin.natAdd a j) * v.2 (Fin.natAdd a j) - u.2 (Fin.natAdd a j) * v.1 (Fin.natAdd a j)) *
        (Real.sin (z.1 (Fin.natAdd a j)) ^ 2 + Real.cos (z.1 (Fin.natAdd a j)) ^ 2)) * hs -
      (u.1 (Fin.natAdd a j) * v.2 (Fin.natAdd a j) - u.2 (Fin.natAdd a j) * v.1 (Fin.natAdd a j)) * hsc


@[simp] theorem polarCellMap_fst_castAdd (z : Phase (a+b)) (i : Fin a) :
    (polarCellMap z).1 (Fin.castAdd b i) = 2 * Real.pi * z.1 (Fin.castAdd b i) := by
  simp [polarCellMap]

@[simp] theorem polarCellMap_snd_castAdd (z : Phase (a+b)) (i : Fin a) :
    (polarCellMap z).2 (Fin.castAdd b i) = z.2 (Fin.castAdd b i) := by
  simp [polarCellMap]

@[simp] theorem polarCellMap_fst_natAdd (z : Phase (a+b)) (j : Fin b) :
    (polarCellMap z).1 (Fin.natAdd a j) =
      Real.sqrt (2 * z.2 (Fin.natAdd a j)) * Real.sin (2 * Real.pi * z.1 (Fin.natAdd a j)) := by
  simp [polarCellMap]

@[simp] theorem polarCellMap_snd_natAdd (z : Phase (a+b)) (j : Fin b) :
    (polarCellMap z).2 (Fin.natAdd a j) =
      Real.sqrt (2 * z.2 (Fin.natAdd a j)) * Real.cos (2 * Real.pi * z.1 (Fin.natAdd a j)) := by
  simp [polarCellMap]

/-! ### Injectivity -/

private theorem polar2_eq {R R' x y : ℝ} (hR : 0 < R) (hR' : 0 < R')
    (hc : Real.sqrt (2 * R) * Real.cos x = Real.sqrt (2 * R') * Real.cos y)
    (hs : Real.sqrt (2 * R) * Real.sin x = Real.sqrt (2 * R') * Real.sin y) :
    R = R' ∧ Real.cos x = Real.cos y ∧ Real.sin x = Real.sin y := by
  have e1 := Real.sq_sqrt (show 0 ≤ 2 * R by positivity)
  have e2 := Real.sq_sqrt (show 0 ≤ 2 * R' by positivity)
  have ec := Real.cos_sq_add_sin_sq x
  have ec' := Real.cos_sq_add_sin_sq y
  have h1 : 2 * R = 2 * R' := by
    linear_combination (-1 : ℝ) * e1 + e2 - Real.sqrt (2 * R) ^ 2 * ec +
      Real.sqrt (2 * R') ^ 2 * ec' +
      (Real.sqrt (2 * R) * Real.cos x + Real.sqrt (2 * R') * Real.cos y) * hc +
      (Real.sqrt (2 * R) * Real.sin x + Real.sqrt (2 * R') * Real.sin y) * hs
  have hRR : R = R' := by linarith
  subst hRR
  have hpos : 0 < Real.sqrt (2 * R) := Real.sqrt_pos.2 (by positivity)
  exact ⟨rfl, mul_left_cancel₀ hpos.ne' hc, mul_left_cancel₀ hpos.ne' hs⟩

private theorem exists_int_of_cos_sin {x y : ℝ} (hc : Real.cos x = Real.cos y)
    (hs : Real.sin x = Real.sin y) : ∃ k : ℤ, y = x + 2 * Real.pi * k := by
  have h : Real.cos (y - x) = 1 := by
    rw [Real.cos_sub, ← hc, ← hs]
    nlinarith [Real.cos_sq_add_sin_sq x]
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).1 h
  exact ⟨k, by linarith⟩

private theorem unit_angle_inj {x y : ℝ} (hx : 0 ≤ x ∧ x < 1) (hy : 0 ≤ y ∧ y < 1)
    (hc : Real.cos (2 * Real.pi * x) = Real.cos (2 * Real.pi * y))
    (hs : Real.sin (2 * Real.pi * x) = Real.sin (2 * Real.pi * y)) : x = y := by
  obtain ⟨k, hk⟩ := exists_int_of_cos_sin hc hs
  have hk' : y = x + k := by
    have := Real.pi_pos
    have h2 : 2 * Real.pi * y = 2 * Real.pi * (x + k) := by rw [hk]; ring
    exact mul_left_cancel₀ (by positivity) h2
  have h1 : (k : ℝ) < 1 := by linarith [hx.1, hy.2]
  have h2 : (-1 : ℝ) < k := by linarith [hy.1, hx.2]
  have h1' : k < 1 := by exact_mod_cast h1
  have h2' : -1 < k := by exact_mod_cast h2
  have : k = 0 := by omega
  rw [hk', this]; simp

theorem polarCellMap_injOn :
    InjOn (polarCellMap (a:=a) (b:=b))
      {z : Phase (a+b) | (∀ j : Fin b, 0 < blockSlow z.2 j) ∧ z.1 ∈ unitCube (a+b)} := by
  rintro z ⟨hz, hzc⟩ z' ⟨hz', hzc'⟩ h
  have hpi := Real.pi_pos
  have c1 := fun i => congrArg (fun w : Phase (a+b) => w.1 (Fin.castAdd b i)) h
  have c2 := fun i => congrArg (fun w : Phase (a+b) => w.2 (Fin.castAdd b i)) h
  have c3 := fun j => congrArg (fun w : Phase (a+b) => w.1 (Fin.natAdd a j)) h
  have c4 := fun j => congrArg (fun w : Phase (a+b) => w.2 (Fin.natAdd a j)) h
  simp only [polarCellMap_fst_castAdd, polarCellMap_snd_castAdd, polarCellMap_fst_natAdd,
    polarCellMap_snd_natAdd] at c1 c2 c3 c4
  refine phase_ext_blocks (fun i => ?_) c2 (fun j => ?_) (fun j => ?_)
  · exact mul_left_cancel₀ (by positivity) (c1 i)
  · have hR : 0 < z.2 (Fin.natAdd a j) := hz j
    have hR' : 0 < z'.2 (Fin.natAdd a j) := hz' j
    obtain ⟨-, h2, h3⟩ := polar2_eq hR hR' (c4 j) (c3 j)
    exact unit_angle_inj (by simpa [unitCube] using hzc (Fin.natAdd a j) (mem_univ _))
      (by simpa [unitCube] using hzc' (Fin.natAdd a j) (mem_univ _)) h2 h3
  · have hR : 0 < z.2 (Fin.natAdd a j) := hz j
    have hR' : 0 < z'.2 (Fin.natAdd a j) := hz' j
    exact (polar2_eq hR hR' (c4 j) (c3 j)).1

/-! ### Lattice injectivity -/

theorem oscillatorPolar_lattice {z z' : Phase (a+b)}
    (hz : ∀ j : Fin b, 0 < blockSlow z.2 j) (hz' : ∀ j : Fin b, 0 < blockSlow z'.2 j)
    (k : Fin a → ℤ) (h : oscillatorPolar z' = oscillatorPolar z + fastShift k) :
    ∃ m : Fin (a+b) → ℤ, z' = z + KAM.Planetary.fullShift m := by
  have c1 := fun i => congrArg (fun w : Phase (a+b) => w.1 (Fin.castAdd b i)) h
  have c2 := fun i => congrArg (fun w : Phase (a+b) => w.2 (Fin.castAdd b i)) h
  have c3 := fun j => congrArg (fun w : Phase (a+b) => w.1 (Fin.natAdd a j)) h
  have c4 := fun j => congrArg (fun w : Phase (a+b) => w.2 (Fin.natAdd a j)) h
  simp only [oscillatorPolar_fst_castAdd, oscillatorPolar_snd_castAdd, oscillatorPolar_fst_natAdd,
    oscillatorPolar_snd_natAdd, Prod.fst_add, Prod.snd_add, Pi.add_apply, fastShift,
    Fin.append_left, Fin.append_right, Pi.zero_apply, add_zero] at c1 c2 c3 c4
  have hj : ∀ j : Fin b, z'.2 (Fin.natAdd a j) = z.2 (Fin.natAdd a j) ∧
      ∃ m : ℤ, z'.1 (Fin.natAdd a j) = z.1 (Fin.natAdd a j) + 2 * Real.pi * m := fun j => by
    obtain ⟨h1, h2, h3⟩ := polar2_eq (hz' j) (hz j) (c4 j) (c3 j)
    exact ⟨h1, exists_int_of_cos_sin h2.symm h3.symm⟩
  choose hj1 m hm using hj
  refine ⟨Fin.append k m, phase_ext_blocks (fun i => ?_) (fun i => ?_) (fun j => ?_) (fun j => ?_)⟩
  · simp [fullShift, c1 i, Fin.append_left]
  · simp [fullShift, c2 i]
  · simp [fullShift, hm j, Fin.append_right]
  · simp [fullShift, hj1 j]


theorem abs_det_fderiv_oscillatorPolar {z : Phase (a+b)}
    (hz : ∀ j : Fin b, 0 < blockSlow z.2 j) :
    |(fderiv ℝ (oscillatorPolar (a:=a) (b:=b)) z).det| = 1 := by
  have h := KAM.Planetary.abs_det_of_symplectic (c := 1) one_ne_zero
    (A := fderiv ℝ (oscillatorPolar (a:=a) (b:=b)) z) (oscillatorPolar_symplectic hz)
  simpa [ContinuousLinearMap.det] using h

theorem disc_measure_chart :
    IsChart 1 (oscillatorPolar (a:=a) (b:=b)) {z : Phase (a+b) | ∀ j : Fin b, 0 < blockSlow z.2 j} ∧
    InjOn (polarCellMap (a:=a) (b:=b))
      {z : Phase (a+b) | (∀ j : Fin b, 0 < blockSlow z.2 j) ∧ z.1 ∈ unitCube (a+b)} ∧
    (∀ z : Phase (a+b), (∀ j : Fin b, 0 < blockSlow z.2 j) →
      |(fderiv ℝ (oscillatorPolar (a:=a) (b:=b)) z).det| = 1) ∧
    (∀ z z' : Phase (a+b), (∀ j : Fin b, 0 < blockSlow z.2 j) →
      (∀ j : Fin b, 0 < blockSlow z'.2 j) → ∀ k : Fin a → ℤ,
      oscillatorPolar z' = oscillatorPolar z + fastShift k →
        ∃ m : Fin (a+b) → ℤ, z'=z+fullShift m) :=
  ⟨⟨fun z hz => analyticAt_oscillatorPolar hz, fun z hz u v => oscillatorPolar_symplectic hz u v⟩,
    polarCellMap_injOn, fun z hz => abs_det_fderiv_oscillatorPolar hz,
    fun z z' hz hz' k h => oscillatorPolar_lattice hz hz' k h⟩


/-! ### The area formula for the cell map -/

private theorem polarCellMap_chart :
    IsChart (2 * Real.pi * 1) (polarCellMap (a:=a) (b:=b))
      {z : Phase (a+b) | ∀ j : Fin b, 0 < blockSlow z.2 j} :=
  ((isChart_angleScale (d := a+b) (by positivity : 0 < 2 * Real.pi)).mono
    (subset_univ _)).comp disc_measure_chart.1 (fun _ hz => hz)

theorem disc_measure_image {X : Set (Phase (a+b))} (hX : MeasurableSet X)
    (hpos : ∀ z ∈ X, ∀ j : Fin b, 0 < blockSlow z.2 j)
    (hcell : ∀ z ∈ X, z.1 ∈ unitCube (a+b)) :
    MeasurableSet (polarCellMap '' X) ∧
    volume (polarCellMap '' X) = ENNReal.ofReal ((2*Real.pi)^(a+b))*volume X := by
  have : (volume : Measure (Phase (a+b))).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hπ : 0 < 2 * Real.pi := by positivity
  have hf' : ∀ x ∈ X, HasFDerivWithinAt (polarCellMap (a:=a) (b:=b))
      (fderiv ℝ (polarCellMap (a:=a) (b:=b)) x) X x := fun x hx =>
    ((polarCellMap_chart.1 x (hpos x hx)).differentiableAt.hasFDerivAt).hasFDerivWithinAt
  have hinj : InjOn (polarCellMap (a:=a) (b:=b)) X :=
    polarCellMap_injOn.mono (fun z hz => (⟨hpos z hz, hcell z hz⟩ :
      (∀ j : Fin b, 0 < blockSlow z.2 j) ∧ z.1 ∈ unitCube (a+b)))
  refine ⟨measurable_image_of_fderivWithin hX hf' hinj, ?_⟩
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume hX hf' hinj]
  have hdet : ∀ x ∈ X, ENNReal.ofReal |(fderiv ℝ (polarCellMap (a:=a) (b:=b)) x).det| =
      ENNReal.ofReal ((2 * Real.pi) ^ (a+b)) := fun x hx => by
    have h := polarCellMap_chart.abs_det_fderiv (by positivity) (hpos x hx)
    rw [mul_one] at h
    simpa [ContinuousLinearMap.det] using congrArg ENNReal.ofReal h
  rw [setLIntegral_congr_fun hX hdet, setLIntegral_const]


/-! ### The polar preimage of a cylinder cell -/

/-- The set of polar data `(angle cell, fast action in V, slow action in box)`. -/
private def discPre (V : Set (Fin a → ℝ)) (box : Set (Fin b → ℝ)) : Set (Phase (a+b)) :=
  {z | blockFast z.2 ∈ V ∧ blockSlow z.2 ∈ box ∧ z.1 ∈ unitCube (a+b)}

private theorem discPre_eq (V : Set (Fin a → ℝ)) (box : Set (Fin b → ℝ)) :
    discPre V box = unitCube (a+b) ×ˢ joinedActions V box := by
  ext z
  simp only [discPre, joinedActions, Set.mem_ofPred_eq, mem_prod]
  tauto

private theorem measurable_blockFast :
    Measurable (fun J : Fin (a+b) → ℝ => blockFast J) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

private theorem measurable_blockSlow :
    Measurable (fun J : Fin (a+b) → ℝ => blockSlow J) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

private theorem measurableSet_unitCube (d : ℕ) : MeasurableSet (unitCube d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

private theorem volume_unitCube' (d : ℕ) : volume (unitCube d) = 1 := by
  simp [unitCube, volume_pi_pi]

private theorem measurableSet_joinedActions {V : Set (Fin a → ℝ)} {box : Set (Fin b → ℝ)}
    (hV : MeasurableSet V) (hbox : MeasurableSet box) :
    MeasurableSet (joinedActions V box) :=
  (measurable_blockFast hV).inter (measurable_blockSlow hbox)

private theorem measurableSet_discPre {V : Set (Fin a → ℝ)} {box : Set (Fin b → ℝ)}
    (hV : MeasurableSet V) (hbox : MeasurableSet box) : MeasurableSet (discPre V box) := by
  rw [discPre_eq]
  exact (measurableSet_unitCube _).prod (measurableSet_joinedActions hV hbox)

private theorem volume_discPre {V : Set (Fin a → ℝ)} {box : Set (Fin b → ℝ)} :
    volume (discPre V box) = volume V * volume box := by
  rw [discPre_eq, Measure.volume_eq_prod, Measure.prod_prod,
    volume_unitCube', one_mul, volume_joinedActions]

private theorem volume_polarCellMap_discPre {V : Set (Fin a → ℝ)} {box : Set (Fin b → ℝ)}
    (hV : MeasurableSet V) (hbox : MeasurableSet box) (hpos : ∀ y ∈ box, ∀ j, 0 < y j) :
    volume (polarCellMap '' discPre V box) =
      ENNReal.ofReal ((2*Real.pi)^(a+b)) * (volume V * volume box) := by
  rw [(disc_measure_image (measurableSet_discPre hV hbox) (fun z hz j => hpos _ hz.2.1 j)
    (fun z hz => hz.2.2)).2, volume_discPre]

private theorem polarCellMap_mem_cylinderCell {V : Set (Fin a → ℝ)} {r : ℝ} {w : Phase (a+b)}
    (hw : w ∈ discPre V (actionShell b 0 (r^2/2))) :
    polarCellMap w ∈ cylinderCell (b:=b) V r := by
  obtain ⟨hV, hR, hc⟩ := hw
  refine ⟨⟨?_, fun j => ?_⟩, fun i => ?_⟩
  · convert hV using 1
    funext i
    simp [fast, blockFast]
  · have hj : w.2 (Fin.natAdd a j) < r^2/2 := (hR j (mem_univ j)).2
    show (polarCellMap w).2 (Fin.natAdd a j) ^ 2 + (polarCellMap w).1 (Fin.natAdd a j) ^ 2 < r ^ 2
    have h0 : 0 ≤ 2 * w.2 (Fin.natAdd a j) := by
      have := (hR j (mem_univ j)).1
      simp only [blockSlow] at this; linarith
    have e := Real.sq_sqrt h0
    have ec := Real.sin_sq_add_cos_sq (2 * Real.pi * w.1 (Fin.natAdd a j))
    rw [polarCellMap_snd_natAdd, polarCellMap_fst_natAdd]
    calc _ = Real.sqrt (2 * w.2 (Fin.natAdd a j)) ^ 2 *
          (Real.sin (2 * Real.pi * w.1 (Fin.natAdd a j)) ^ 2 +
            Real.cos (2 * Real.pi * w.1 (Fin.natAdd a j)) ^ 2) := by ring
      _ < r ^ 2 := by rw [ec, e, mul_one]; linarith
  · have h := hc (Fin.castAdd b i) (mem_univ _)
    simp only [mem_Ico] at h
    show 0 ≤ (polarCellMap w).1 (Fin.castAdd b i) ∧ (polarCellMap w).1 (Fin.castAdd b i) < 2 * Real.pi
    rw [polarCellMap_fst_castAdd]
    have := Real.pi_pos
    constructor <;> nlinarith [h.1, h.2]

private theorem exists_angle {p q : ℝ} (h : p ≠ 0 ∨ q ≠ 0) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 2 * Real.pi ∧ Real.sqrt (p^2 + q^2) * Real.cos θ = p ∧
      Real.sqrt (p^2 + q^2) * Real.sin θ = q := by
  let x : ℂ := ⟨p, q⟩
  have hn : ‖x‖ = Real.sqrt (p^2 + q^2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; simp [x, sq]
  have hc : ‖x‖ * Real.cos (Complex.arg x) = p := Complex.norm_mul_cos_arg x
  have hs : ‖x‖ * Real.sin (Complex.arg x) = q := Complex.norm_mul_sin_arg x
  rw [hn] at hc hs
  have hx : x ≠ 0 := by
    intro h0
    rcases h with h | h
    · exact h (congrArg Complex.re h0)
    · exact h (congrArg Complex.im h0)
  have h1 := Complex.arg_le_pi x
  have h2 := Complex.neg_pi_lt_arg x
  have := Real.pi_pos
  by_cases h0 : 0 ≤ Complex.arg x
  · exact ⟨Complex.arg x, h0, by linarith, hc, hs⟩
  · refine ⟨Complex.arg x + 2 * Real.pi, by linarith, by linarith, ?_, ?_⟩
    · rw [Real.cos_add_two_pi]; exact hc
    · rw [Real.sin_add_two_pi]; exact hs

private theorem exists_preimage {V : Set (Fin a → ℝ)} {r : ℝ} {z : Phase (a+b)}
    (hz : z ∈ cylinderCell (b:=b) V r)
    (hne : ∀ j : Fin b, z.2 (Fin.natAdd a j) ≠ 0 ∨ z.1 (Fin.natAdd a j) ≠ 0) :
    ∃ w ∈ discPre V (actionShell b 0 (r^2/2)), polarCellMap w = z ∧
      ∀ j : Fin b, w.2 (Fin.natAdd a j) =
        (z.2 (Fin.natAdd a j) ^ 2 + z.1 (Fin.natAdd a j) ^ 2) / 2 := by
  obtain ⟨⟨hV, hd⟩, hcell⟩ := hz
  choose θ hθ0 hθ1 hθc hθs using fun j : Fin b => exists_angle (hne j)
  have hpi := Real.pi_pos
  let w : Phase (a+b) :=
    (Fin.append (fun i => z.1 (Fin.castAdd b i) / (2 * Real.pi)) (fun j => θ j / (2 * Real.pi)),
     Fin.append (fun i => z.2 (Fin.castAdd b i))
       (fun j => (z.2 (Fin.natAdd a j) ^ 2 + z.1 (Fin.natAdd a j) ^ 2) / 2))
  have hwR : ∀ j : Fin b, w.2 (Fin.natAdd a j) =
      (z.2 (Fin.natAdd a j) ^ 2 + z.1 (Fin.natAdd a j) ^ 2) / 2 := fun j => by
    simp [w, Fin.append_right]
  have hpos : ∀ j : Fin b, 0 < w.2 (Fin.natAdd a j) := fun j => by
    rw [hwR]
    rcases hne j with h | h
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg (z.1 (Fin.natAdd a j))]
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg (z.2 (Fin.natAdd a j))]
  refine ⟨w, ⟨?_, fun j _ => ⟨hpos j, ?_⟩, fun i _ => ?_⟩, ?_, hwR⟩
  · convert hV using 1
    funext i
    simp [w, blockFast, Fin.append_left, fast]
  · have := hd j
    simp only [slow] at this
    show w.2 (Fin.natAdd a j) < r ^ 2 / 2
    rw [hwR]; linarith
  · refine Fin.addCases (fun k => ?_) (fun j => ?_) i
    · have h := hcell k
      simp only [fast] at h
      simp only [w, Fin.append_left, mem_Ico]
      exact ⟨by positivity [h.1], by rw [div_lt_one (by positivity)]; exact h.2⟩
    · simp only [w, Fin.append_right, mem_Ico]
      exact ⟨by positivity [hθ0 j], by rw [div_lt_one (by positivity)]; exact hθ1 j⟩
  · refine phase_ext_blocks (fun i => ?_) (fun i => ?_) (fun j => ?_) (fun j => ?_)
    · simp [w, Fin.append_left]; field_simp
    · simp [w, Fin.append_left]
    · rw [polarCellMap_fst_natAdd, hwR j]
      have e : 2 * Real.pi * w.1 (Fin.natAdd a j) = θ j := by
        simp [w, Fin.append_right]; field_simp
      rw [e, show 2 * ((z.2 (Fin.natAdd a j) ^ 2 + z.1 (Fin.natAdd a j) ^ 2) / 2) =
        z.2 (Fin.natAdd a j) ^ 2 + z.1 (Fin.natAdd a j) ^ 2 by ring]
      exact hθs j
    · rw [polarCellMap_snd_natAdd, hwR j]
      have e : 2 * Real.pi * w.1 (Fin.natAdd a j) = θ j := by
        simp [w, Fin.append_right]; field_simp
      rw [e, show 2 * ((z.2 (Fin.natAdd a j) ^ 2 + z.1 (Fin.natAdd a j) ^ 2) / 2) =
        z.2 (Fin.natAdd a j) ^ 2 + z.1 (Fin.natAdd a j) ^ 2 by ring]
      exact hθc j


/-! ### Null centres, volumes of boxes -/

private theorem volume_coord_zero (m : ℕ) (k : Fin m) :
    volume {y : Fin m → ℝ | y k = 0} = 0 := by
  have h : {y : Fin m → ℝ | y k = 0} = Set.pi univ (fun i => if i = k then ({0} : Set ℝ) else univ) := by
    ext y
    simp only [Set.mem_ofPred_eq, mem_pi, mem_univ, true_implies]
    constructor
    · intro hy i
      by_cases hi : i = k
      · subst hi; simpa using hy
      · simp [hi]
    · intro hy
      simpa using hy k
  rw [h, volume_pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)

private theorem volume_slowCoord_zero (j : Fin b) :
    volume {z : Phase (a+b) | z.2 (Fin.natAdd a j) = 0} = 0 := by
  have h : {z : Phase (a+b) | z.2 (Fin.natAdd a j) = 0} =
      (univ : Set (Fin (a+b) → ℝ)) ×ˢ {y | y (Fin.natAdd a j) = 0} := by
    ext z; simp
  rw [h, Measure.volume_eq_prod, Measure.prod_prod, volume_coord_zero, mul_zero]

private theorem volume_centres : volume {z : Phase (a+b) |
    ∃ j : Fin b, z.2 (Fin.natAdd a j) = 0 ∧ z.1 (Fin.natAdd a j) = 0} = 0 := by
  refine measure_mono_null (fun z hz => ?_) (measure_iUnion_null (fun j : Fin b =>
    volume_slowCoord_zero (a := a) j))
  obtain ⟨j, hj, -⟩ := hz
  exact mem_iUnion.2 ⟨j, hj⟩

private theorem volume_actionShell (c : ℝ) :
    volume (actionShell b 0 c) = ENNReal.ofReal c ^ b := by
  simp [actionShell, volume_pi_pi]

private theorem measurableSet_actionShell (l u : ℝ) : MeasurableSet (actionShell b l u) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

/-- The shell box with the `j`th action capped at `l`. -/
private def capBox (b : ℕ) (j : Fin b) (l c : ℝ) : Set (Fin b → ℝ) :=
  Set.pi univ (fun k : Fin b => if k = j then Ioc 0 l else Ioo 0 c)

private theorem volume_capBox (j : Fin b) (l c : ℝ) :
    volume (capBox b j l c) = ENNReal.ofReal l * ENNReal.ofReal c ^ (b-1) := by
  rw [capBox, volume_pi_pi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  have h : ∏ k ∈ Finset.univ.erase j, volume (if k = j then Ioc (0:ℝ) l else Ioo 0 c) =
      ∏ k ∈ Finset.univ.erase j, ENNReal.ofReal c := Finset.prod_congr rfl fun k hk => by
    simp [Finset.ne_of_mem_erase hk]
  rw [h, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j)]
  simp

private theorem measurableSet_capBox (j : Fin b) (l c : ℝ) : MeasurableSet (capBox b j l c) :=
  MeasurableSet.univ_pi fun k => by
    by_cases h : k = j <;> simp [h, measurableSet_Ioc, measurableSet_Ioo]

private theorem pos_capBox (j : Fin b) (l c : ℝ) : ∀ y ∈ capBox b j l c, ∀ k, 0 < y k := by
  intro y hy k
  have : y k ∈ (if k = j then Ioc 0 l else Ioo 0 c) := hy k (mem_univ k)
  by_cases h : k = j
  · subst h; simp only [↓reduceIte] at this; exact this.1
  · simp only [h, ↓reduceIte] at this; exact this.1

/-! ### Cell volume, null coverage and the shell estimate -/

private theorem cell_diff_subset {V : Set (Fin a → ℝ)} {r : ℝ} :
    cylinderCell (b:=b) V r \ polarCellMap '' discPre V (actionShell b 0 (r^2/2)) ⊆
      {z : Phase (a+b) | ∃ j : Fin b, z.2 (Fin.natAdd a j) = 0 ∧ z.1 (Fin.natAdd a j) = 0} := by
  intro z ⟨hz, hn⟩
  by_contra hc
  refine hn ?_
  obtain ⟨w, hw, hwz, -⟩ := exists_preimage hz (fun j => by
    by_contra h
    push Not at h
    exact hc ⟨j, h.1, h.2⟩)
  exact ⟨w, hw, hwz⟩

theorem disc_measure {V : Set (Fin a → ℝ)} (hV : MeasurableSet V)
    {r : ℝ} (hr : 0 < r) :
    volume (cylinderCell (b:=b) V r) =
      ENNReal.ofReal ((2*Real.pi)^(a+b)*(r^2/2)^b)*volume V ∧
    volume (cylinderCell (b:=b) V r \ polarCellMap ''
      {z : Phase (a+b) | blockFast z.2 ∈ V ∧
        blockSlow z.2 ∈ actionShell b 0 (r^2/2) ∧
        z.1 ∈ unitCube (a+b)}) = 0 := by
  have hnull : volume (cylinderCell (b:=b) V r \ polarCellMap ''
      discPre V (actionShell b 0 (r^2/2))) = 0 :=
    measure_mono_null cell_diff_subset volume_centres
  refine ⟨?_, hnull⟩
  have himg : polarCellMap '' discPre V (actionShell b 0 (r^2/2)) ⊆ cylinderCell (b:=b) V r := by
    rintro _ ⟨w, hw, rfl⟩
    exact polarCellMap_mem_cylinderCell hw
  have hvol := volume_polarCellMap_discPre (b := b) hV (measurableSet_actionShell 0 (r^2/2))
    (fun y hy j => (hy j (mem_univ j)).1)
  have hle : volume (cylinderCell (b:=b) V r) ≤
      volume (polarCellMap '' discPre V (actionShell b 0 (r^2/2))) := by
    calc volume (cylinderCell (b:=b) V r)
        ≤ volume (polarCellMap '' discPre V (actionShell b 0 (r^2/2)) ∪
            (cylinderCell (b:=b) V r \ polarCellMap '' discPre V (actionShell b 0 (r^2/2)))) :=
          measure_mono (fun z hz => by
            by_cases h : z ∈ polarCellMap '' discPre V (actionShell b 0 (r^2/2))
            · exact Or.inl h
            · exact Or.inr ⟨hz, h⟩)
      _ ≤ _ + _ := measure_union_le _ _
      _ = _ := by rw [hnull, add_zero]
  have hc : (0:ℝ) ≤ r^2/2 := by positivity
  have heq : volume (cylinderCell (b:=b) V r) =
      volume (polarCellMap '' discPre V (actionShell b 0 (r^2/2))) :=
    le_antisymm hle (measure_mono himg)
  rw [heq, hvol, volume_actionShell, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hc]
  ring

theorem disc_measure_shell {V : Set (Fin a → ℝ)} (hV : MeasurableSet V)
    {r l : ℝ} (hr : 0 < r) (hl : 0 < l) (hlr : l < r^2/2) :
    volume {z ∈ cylinderCell (b:=b) V r | ∃ j : Fin b,
      oscillatorAction (blockSlow z.2) (blockSlow z.1) j ≤ l} ≤
      ENNReal.ofReal (b*l/(r^2/2))*volume (cylinderCell (b:=b) V r) := by
  have hc : 0 < r^2/2 := by positivity
  rw [(disc_measure (b := b) hV hr).1]
  have hsub : {z ∈ cylinderCell (b:=b) V r | ∃ j : Fin b,
      oscillatorAction (blockSlow z.2) (blockSlow z.1) j ≤ l} ⊆
      {z : Phase (a+b) | ∃ j : Fin b, z.2 (Fin.natAdd a j) = 0 ∧ z.1 (Fin.natAdd a j) = 0} ∪
        ⋃ j : Fin b, polarCellMap '' discPre V (capBox b j l (r^2/2)) := by
    rintro z ⟨hz, j, hj⟩
    by_cases hn : ∃ j : Fin b, z.2 (Fin.natAdd a j) = 0 ∧ z.1 (Fin.natAdd a j) = 0
    · exact Or.inl hn
    · refine Or.inr (mem_iUnion.2 ?_)
      obtain ⟨w, ⟨hw1, hw2, hw3⟩, hwz, hwR⟩ := exists_preimage hz (fun j => by
        by_contra h
        push Not at h
        exact hn ⟨j, h.1, h.2⟩)
      refine ⟨j, w, ⟨hw1, fun k _ => ?_, hw3⟩, hwz⟩
      by_cases hk : k = j
      · subst hk
        have h1 := hwR k
        have h2 : oscillatorAction (blockSlow z.2) (blockSlow z.1) k ≤ l := hj
        simp only [oscillatorAction, blockSlow] at h2
        have h3 := (hw2 k (mem_univ k)).1
        simp only [blockSlow] at h3
        simp only [↓reduceIte]
        exact ⟨h3, by simp only [blockSlow]; rw [h1]; exact h2⟩
      · simp only [hk, ↓reduceIte]
        exact hw2 k (mem_univ k)
  have hI : ∀ j : Fin b, volume (polarCellMap '' discPre V (capBox b j l (r^2/2))) =
      ENNReal.ofReal ((2*Real.pi)^(a+b)) * (volume V *
        (ENNReal.ofReal l * ENNReal.ofReal (r^2/2) ^ (b-1))) := fun j => by
    rw [volume_polarCellMap_discPre hV (measurableSet_capBox j _ _) (pos_capBox j _ _),
      volume_capBox]
  calc _ ≤ volume ({z : Phase (a+b) | ∃ j : Fin b, z.2 (Fin.natAdd a j) = 0 ∧
        z.1 (Fin.natAdd a j) = 0} ∪ ⋃ j : Fin b, polarCellMap '' discPre V (capBox b j l (r^2/2))) :=
        measure_mono hsub
    _ ≤ volume {z : Phase (a+b) | ∃ j : Fin b, z.2 (Fin.natAdd a j) = 0 ∧
        z.1 (Fin.natAdd a j) = 0} + volume (⋃ j : Fin b,
          polarCellMap '' discPre V (capBox b j l (r^2/2))) := measure_union_le _ _
    _ ≤ 0 + ∑ j : Fin b, volume (polarCellMap '' discPre V (capBox b j l (r^2/2))) := by
        rw [volume_centres]; exact add_le_add le_rfl (measure_iUnion_fintype_le _ _)
    _ = (b : ENNReal) * (ENNReal.ofReal ((2*Real.pi)^(a+b)) * (volume V *
        (ENNReal.ofReal l * ENNReal.ofReal (r^2/2) ^ (b-1)))) := by
        simp only [hI, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, zero_add]
    _ ≤ _ := by
        rcases Nat.eq_zero_or_pos b with h0 | hb
        · subst h0; simp
        · obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
          have hid : ((b'+1 : ℕ) : ℝ) * l / (r^2/2) * ((2*Real.pi)^(a+(b'+1)) * (r^2/2)^(b'+1)) =
              ((b'+1 : ℕ) : ℝ) * ((2*Real.pi)^(a+(b'+1)) * l * (r^2/2)^b') := by
            rw [pow_succ (r^2/2) b']
            field_simp
          have hR : ENNReal.ofReal (((b'+1 : ℕ) : ℝ) * l / (r^2/2)) *
              (ENNReal.ofReal ((2*Real.pi)^(a+(b'+1)) * (r^2/2)^(b'+1)) * volume V) =
              ENNReal.ofReal (((b'+1 : ℕ) : ℝ) * ((2*Real.pi)^(a+(b'+1)) * l * (r^2/2)^b')) *
                volume V := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hid]
          rw [hR]
          simp only [ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ 2*Real.pi),
            ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2*Real.pi)^(a+(b'+1))),
            ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2*Real.pi)^(a+(b'+1)) * l),
            ENNReal.ofReal_mul hl.le, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_pow hc.le, ENNReal.ofReal_natCast, Nat.succ_sub_one, Nat.succ_eq_add_one]
          refine le_of_eq ?_
          ring

end KAM.Planetary

end
