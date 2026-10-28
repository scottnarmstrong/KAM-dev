/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Measure.Lipschitz
public import KAM.Planetary.PGAssembly.Lower
public import KAM.Planetary.PGAssembly.CutMeasure

/-!
# P Part 5: deleting a small family of tori (`bpP:p5:strictness`)

The parameter measure `stMeasure` is the push-forward of Lebesgue measure on the output
representative `outputRepresentative` along the measurable inverse `stParam` of the injective
parametrisation `J ↦ range (raw J)`; on σ-compact sets `B ⊆ D₀` it is the mass
`B ↦ meas (S_B ∩ F) / (2π)^n` (`stepP:p5:st-add`, additivity). Coordinate slices of `D₀` are null
because the raw family is Lipschitz on the lower-dimensional set `slice × [0,1)^n`
(`stepP:p5:st-null`). `finite_measure_coordinate_cut` (in `CutMeasure`) makes the cut mass
continuous, and the intermediate value theorem produces the half-space cut of mass
`min (total/2) (√r meas F/2)` (`stepP:p5:st-ivt`). The complement of the cut is a union of whole
tori with the stated strict bounds (`stepP:p5:st-conc`, `strictness`). `strictness` is copied
verbatim from `P45Signatures.lean`. Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, P5-ST.
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter Topology KAM.ODE

namespace KAM.Planetary

variable {a b : ℕ}

section Param

variable (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)

open scoped Classical in
/-- The parameter of the unique torus of the raw family through `z` (`0` off the raw union). -/
def stParam (z : Phase (a+b)) : Fin (a+b) → ℝ :=
  if hz : ∃ J, J ∈ pgD0 d r mu ∧ z ∈ range ((pgFamily d r mu h).raw J) then hz.choose else 0

variable {d r mu h}

theorem stParam_eq {J : Fin (a+b) → ℝ} (hJ : J ∈ pgD0 d r mu) {z : Phase (a+b)}
    (hz : z ∈ range ((pgFamily d r mu h).raw J)) : stParam d r mu h z = J := by
  have hex : ∃ J, J ∈ pgD0 d r mu ∧ z ∈ range ((pgFamily d r mu h).raw J) := ⟨J, hJ, hz⟩
  rw [stParam, dite_cond_eq_true (eq_true hex)]
  obtain ⟨h1, θ', hθ'⟩ := hex.choose_spec
  obtain ⟨θ, hθ⟩ := hz
  obtain ⟨-, -, -, hinj, -⟩ := ct_spec d r mu h
  refine hinj _ h1 J hJ θ' θ ?_
  simp only [physicalTorus, Function.comp_apply]
  rw [hθ', hθ]

theorem stParam_preimage (A : Set (Fin (a+b) → ℝ)) :
    stParam d r mu h ⁻¹' A ∩ rawUnion d r mu h (pgD0 d r mu) =
      rawUnion d r mu h (pgD0 d r mu ∩ A) := by
  ext z
  constructor
  · rintro ⟨hA, hz⟩
    obtain ⟨J, hJ, hzr⟩ := mem_iUnion₂.1 hz
    have := stParam_eq hJ hzr
    rw [mem_preimage, this] at hA
    exact mem_iUnion₂.2 ⟨J, ⟨hJ, hA⟩, hzr⟩
  · intro hz
    obtain ⟨J, ⟨hJD, hJA⟩, hzr⟩ := mem_iUnion₂.1 hz
    exact ⟨by rw [mem_preimage, stParam_eq hJD hzr]; exact hJA, mem_iUnion₂.2 ⟨J, hJD, hzr⟩⟩

theorem stSigma_inter_closed {X C : Set (Fin (a+b) → ℝ)} (hX : IsSigmaCompact X)
    (hC : IsClosed C) : IsSigmaCompact (X ∩ C) := by
  obtain ⟨K, hK, rfl⟩ := hX
  rw [iUnion_inter]
  exact isSigmaCompact_iUnion_of_isCompact _ fun i => (hK i).inter_right hC

theorem stParam_measurable : Measurable (stParam d r mu h) := by
  refine measurable_of_isClosed fun C hC => ?_
  have hD := fam_isSigmaCompact_D0 h
  have hset : stParam d r mu h ⁻¹' C = rawUnion d r mu h (pgD0 d r mu ∩ C) ∪
      ((rawUnion d r mu h (pgD0 d r mu))ᶜ ∩ {_z | (0 : Fin (a+b) → ℝ) ∈ C}) := by
    ext z
    by_cases hz : z ∈ rawUnion d r mu h (pgD0 d r mu)
    · rw [← stParam_preimage]
      simp [hz]
    · have h0 : stParam d r mu h z = 0 := by
        rw [stParam, dite_cond_eq_false (eq_false (by
          rintro ⟨J, hJ, hzr⟩
          exact hz (mem_iUnion₂.2 ⟨J, hJ, hzr⟩)))]
      have hn : z ∉ rawUnion d r mu h (pgD0 d r mu ∩ C) := fun hz' =>
        hz (by
          obtain ⟨J, hJ, hzr⟩ := mem_iUnion₂.1 hz'
          exact mem_iUnion₂.2 ⟨J, hJ.1, hzr⟩)
      simp [hz, hn, h0]
  rw [hset]
  refine (measurableSet_of_isSigmaCompact ?_).union ?_
  · exact ct_rawUnion_sigmaCompact d r mu h (stSigma_inter_closed hD hC) inter_subset_left
  · exact (measurableSet_of_isSigmaCompact (ct_rawUnion_sigmaCompact d r mu h hD
      fun _ hJ => hJ)).compl.inter (MeasurableSet.const _)

/-- The parameter measure (`stepP:p5:st-add`). -/
def stMeasure (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    Measure (Fin (a+b) → ℝ) :=
  (volume.restrict (outputRepresentative d r mu h (pgD0 d r mu))).map (stParam d r mu h)

theorem stCell_ne_top (d : PGData a b) (hr : 0 < r) :
    volume (cylinderCell (b := b) d.V r) ≠ ⊤ := by
  rw [(disc_measure (b := b) d.hV.measurableSet hr).1]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top d.hVb.measure_lt_top.ne

theorem stRep_ne_top (h : admissible d (pgRstar d) r mu) :
    volume (outputRepresentative d r mu h (pgD0 d r mu)) ≠ ⊤ := by
  obtain ⟨-, -, -, hvol⟩ := cell_transfer d r mu h (fam_isSigmaCompact_D0 h) (fun _ hJ => hJ)
  intro htop
  have hfin : volume (kset d r mu h (pgD0 d r mu) ∩ cylinderCell d.V r) ≠ ⊤ :=
    ne_top_of_le_ne_top (stCell_ne_top d h.1) (measure_mono inter_subset_right)
  rw [hvol, htop, ENNReal.mul_top (by simp; positivity)] at hfin
  exact hfin rfl

instance stMeasure_finite (h : admissible d (pgRstar d) r mu) :
    IsFiniteMeasure (stMeasure d r mu h) := by
  have : IsFiniteMeasure (volume.restrict (outputRepresentative d r mu h (pgD0 d r mu))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (stRep_ne_top h)⟩
  exact Measure.isFiniteMeasure_map _ _

theorem stMeasure_apply {A : Set (Fin (a+b) → ℝ)} (hA : MeasurableSet A) :
    stMeasure d r mu h A = volume (outputRepresentative d r mu h (pgD0 d r mu ∩ A)) := by
  rw [stMeasure, Measure.map_apply stParam_measurable hA, Measure.restrict_apply
    (stParam_measurable hA)]
  unfold outputRepresentative
  rw [← inter_assoc, stParam_preimage]

/-- The mass of a σ-compact set of parameters, in terms of the parameter measure. -/
theorem st_mass {B : Set (Fin (a+b) → ℝ)} (hB : IsSigmaCompact B) (hsub : B ⊆ pgD0 d r mu) :
    volume (kset d r mu h B ∩ cylinderCell d.V r) =
      ENNReal.ofReal ((2*Real.pi)^(a+b)) * stMeasure d r mu h B := by
  rw [stMeasure_apply (measurableSet_of_isSigmaCompact hB), inter_eq_right.2 hsub]
  exact (cell_transfer d r mu h hB hsub).2.2.2

theorem stMeasure_compl_D0 (h : admissible d (pgRstar d) r mu) :
    stMeasure d r mu h (pgD0 d r mu)ᶜ = 0 := by
  have hD := measurableSet_of_isSigmaCompact (fam_isSigmaCompact_D0 h)
  rw [stMeasure_apply hD.compl, inter_compl_self]
  simp [outputRepresentative, rawUnion]

end Param

end KAM.Planetary

end
