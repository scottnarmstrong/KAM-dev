/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# W7: slicing lemma and Borel sets (blueprint `bpW:w7:slab`, `bpW:w7:ext-borel`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

`volume_le_of_coord_slices` is Tonelli along a coordinate line: a measurable `S ⊆ ℝ²` of diameter
`≤ ρ` whose lines in direction `e_i` have diameter `≤ d` has measure `≤ d ρ`. `measSlab_measure_le`
is blueprint Lemma `bpW:w7:slab`: if `|φ| < η` on `S` and `φ` grows at least like `σ |t|` along
the coordinate lines, then `volume S ≤ 2 η ρ / σ`.
`measurableSet_abs_lt_of_continuousOn` is the Borel statement of `bpW:w7:ext-borel`.
-/

@[expose] public section

open MeasureTheory Set

namespace KAM.Wave

/-- Tonelli along the first coordinate, for subsets of `ℝ × ℝ`. -/
theorem volume_le_of_slices_prod {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) {d ρ : ℝ}
    (hd : 0 ≤ d) (hproj : ∀ p ∈ S, ∀ q ∈ S, |p.2 - q.2| ≤ ρ)
    (hline : ∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → |p.1 - q.1| ≤ d) :
    volume S ≤ ENNReal.ofReal (d * ρ) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  set P : Set ℝ := Prod.snd '' S with hP
  have hPne : P.Nonempty := hne.image _
  have hPbdd : BddBelow P := by
    obtain ⟨p0, hp0⟩ := hne
    refine ⟨p0.2 - ρ, ?_⟩
    rintro y ⟨q, hq, rfl⟩
    have := hproj p0 hp0 q hq
    rw [abs_le] at this
    linarith
  set y0 := sInf P with hy0
  have hyIcc : ∀ p ∈ S, p.2 ∈ Icc y0 (y0 + ρ) := by
    intro p hp
    refine ⟨csInf_le hPbdd ⟨p, hp, rfl⟩, ?_⟩
    have : p.2 - ρ ≤ y0 := by
      refine le_csInf hPne ?_
      rintro y ⟨q, hq, rfl⟩
      have := hproj p hp q hq
      rw [abs_le] at this
      linarith
    linarith
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hS]
  have hslice : ∀ y : ℝ, volume ((fun x => (x, y)) ⁻¹' S) ≤
      (Icc y0 (y0 + ρ)).indicator (fun _ => ENNReal.ofReal d) y := by
    intro y
    by_cases hy : y ∈ Icc y0 (y0 + ρ)
    · rw [indicator_of_mem hy]
      refine (Real.volume_le_diam _).trans ?_
      refine Metric.ediam_le fun a ha b hb => ?_
      have := hline (a, y) ha (b, y) hb rfl
      rw [edist_dist, Real.dist_eq]
      exact ENNReal.ofReal_le_ofReal this
    · rw [indicator_of_notMem hy]
      have : (fun x => (x, y)) ⁻¹' S = ∅ := by
        ext x
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        intro hx
        exact hy (hyIcc _ hx)
      rw [this]; simp
  calc ∫⁻ y, volume ((fun x => (x, y)) ⁻¹' S)
      ≤ ∫⁻ y, (Icc y0 (y0 + ρ)).indicator (fun _ => ENNReal.ofReal d) y :=
        lintegral_mono hslice
    _ = ENNReal.ofReal d * volume (Icc y0 (y0 + ρ)) := by
        rw [lintegral_indicator_const measurableSet_Icc]
    _ = ENNReal.ofReal (d * ρ) := by
        rw [Real.volume_Icc, ENNReal.ofReal_mul hd]
        congr 2; ring

/-- Tonelli along the coordinate line `e_i` in `Fin 2 → ℝ`. -/
theorem volume_le_of_coord_slices (i : Fin 2) {S : Set (Fin 2 → ℝ)} (hS : MeasurableSet S)
    {d ρ : ℝ} (hd : 0 ≤ d) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ ρ)
    (hline : ∀ x ∈ S, ∀ y ∈ S, (∀ j, j ≠ i → x j = y j) → |x i - y i| ≤ d) :
    volume S ≤ ENNReal.ofReal (d * ρ) := by
  set e := (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) with he
  have hmp := volume_preserving_finTwoArrow ℝ
  set S' : Set (ℝ × ℝ) := e.symm ⁻¹' S with hS'
  have hS'm : MeasurableSet S' := e.symm.measurable hS
  have hvol : volume S = volume S' := by
    have h1 := hmp.measure_preimage_equiv S'
    have h2 : e ⁻¹' S' = S := by ext x; simp [hS']
    rw [h2] at h1
    exact h1
  have hmem : ∀ p : ℝ × ℝ, p ∈ S' ↔ ![p.1, p.2] ∈ S := by
    intro p; simp [hS', he, MeasurableEquiv.finTwoArrow_symm_apply]
  have hcoord : ∀ x y : Fin 2 → ℝ, ∀ j, |x j - y j| ≤ dist x y := fun x y j => by
    have := dist_le_pi_dist x y j
    rwa [Real.dist_eq] at this
  rw [hvol]
  fin_cases i
  · refine volume_le_of_slices_prod hS'm hd ?_ ?_
    · intro p hp q hq
      rw [hmem] at hp hq
      have := (hcoord _ _ 1).trans (hdiam _ hp _ hq)
      simpa using this
    · intro p hp q hq hpq
      rw [hmem] at hp hq
      have := hline _ hp _ hq (by
        intro j hj
        have : j = 1 := by fin_cases j <;> simp_all
        subst this; simpa using hpq)
      simpa using this
  · -- swap the roles of the two coordinates
    have hsw : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
      have := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure
          ℝ)))
      simpa [Measure.volume_eq_prod] using this
    set S'' : Set (ℝ × ℝ) := Prod.swap ⁻¹' S' with hS''
    have hS''m : MeasurableSet S'' := measurable_swap hS'm
    have hv2 : volume S' = volume S'' := by
      rw [hS'', hsw.measure_preimage hS'm.nullMeasurableSet]
    rw [hv2]
    have hmem2 : ∀ p : ℝ × ℝ, p ∈ S'' ↔ ![p.2, p.1] ∈ S := by
      intro p; rw [hS'', mem_preimage, hmem]; rfl
    refine volume_le_of_slices_prod hS''m hd ?_ ?_
    · intro p hp q hq
      rw [hmem2] at hp hq
      have := (hcoord _ _ 0).trans (hdiam _ hp _ hq)
      simpa using this
    · intro p hp q hq hpq
      rw [hmem2] at hp hq
      have := hline _ hp _ hq (by
        intro j hj
        have : j = 0 := by fin_cases j <;> simp_all
        subst this; simpa using hpq)
      simpa using this

/-- **Slicing lemma** (blueprint `bpW:w7:slab`): a measurable `S ⊆ ℝ²` of diameter `≤ ρ` on which
`|φ| < η` and `|φ ζ - φ ζ'| ≥ σ |ζ_i - ζ'_i|` for points on a common line `e_i` has measure at most
`2 η ρ / σ`. -/
theorem measSlab_measure_le (i : Fin 2) {S : Set (Fin 2 → ℝ)} (hS : MeasurableSet S) {ρ σ η : ℝ}
    (hσ : 0 < σ) (hη : 0 ≤ η) (φ : (Fin 2 → ℝ) → ℝ)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ ρ) (hsmall : ∀ x ∈ S, |φ x| < η)
    (hgrow : ∀ x ∈ S, ∀ y ∈ S, (∀ j, j ≠ i → x j = y j) → σ * |x i - y i| ≤ |φ x - φ y|) :
    volume S ≤ ENNReal.ofReal (2 * η * ρ / σ) := by
  have := volume_le_of_coord_slices i hS (d := 2 * η / σ) (ρ := ρ) (by positivity) hdiam
    (fun x hx y hy hxy => by
      have h1 := hgrow x hx y hy hxy
      have h2 : |φ x - φ y| ≤ 2 * η := by
        calc |φ x - φ y| ≤ |φ x| + |φ y| := abs_sub _ _
          _ ≤ 2 * η := by linarith [hsmall x hx, hsmall y hy]
      rw [le_div_iff₀ hσ]
      nlinarith)
  convert this using 2
  field_simp

/-- **Borel sets** (blueprint `bpW:w7:ext-borel`): `{ξ ∈ D : |f ξ| < η}` is Borel for Borel `D` and
`f` continuous on `D`. -/
theorem measurableSet_abs_lt_of_continuousOn {D : Set (Fin 2 → ℝ)} (hD : MeasurableSet D)
    {f : (Fin 2 → ℝ) → ℝ} (hf : ContinuousOn f D) (η : ℝ) :
    MeasurableSet {ξ ∈ D | |f ξ| < η} := by
  obtain ⟨u, hu, hu'⟩ := continuousOn_iff'.1 hf (Set.Ioo (-η) η) isOpen_Ioo
  have : {ξ ∈ D | |f ξ| < η} = u ∩ D := by
    rw [← hu']
    ext ξ
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioo, abs_lt]
    tauto
  rw [this]
  exact hu.measurableSet.inter hD

end KAM.Wave

end
