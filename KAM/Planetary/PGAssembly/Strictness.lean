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
  rw [stParam, dite_eq_left_of_eq_true (eq_true hex)]
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
        rw [stParam, dite_eq_right_of_eq_false (eq_false (by
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

theorem stMeasure_inter_D0 {A : Set (Fin (a+b) → ℝ)} (hA : MeasurableSet A) :
    stMeasure d r mu h (pgD0 d r mu ∩ A) = stMeasure d r mu h A := by
  have hD := measurableSet_of_isSigmaCompact (fam_isSigmaCompact_D0 h)
  rw [stMeasure_apply (hD.inter hA), stMeasure_apply hA, ← inter_assoc, inter_self]

theorem st_mass_real {B : Set (Fin (a+b) → ℝ)} (hB : IsSigmaCompact B) (hsub : B ⊆ pgD0 d r mu) :
    (volume (kset d r mu h B ∩ cylinderCell d.V r)).toReal =
      (2*Real.pi)^(a+b) * (stMeasure d r mu h B).toReal := by
  rw [st_mass hB hsub, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- `stepP:p5:st-add`: the mass `B ↦ meas (S_B ∩ F)` is countably additive on σ-compact
subsets of `D₀`. -/
theorem st_add {B : ℕ → Set (Fin (a+b) → ℝ)} (hB : ∀ i, IsSigmaCompact (B i))
    (hsub : ∀ i, B i ⊆ pgD0 d r mu) (hdisj : Pairwise (Function.onFun Disjoint B)) :
    volume (kset d r mu h (⋃ i, B i) ∩ cylinderCell d.V r) =
      ∑' i, volume (kset d r mu h (B i) ∩ cylinderCell d.V r) := by
  rw [st_mass (isSigmaCompact_iUnion _ hB) (iUnion_subset hsub),
    measure_iUnion hdisj fun i => measurableSet_of_isSigmaCompact (hB i),
    ← ENNReal.tsum_mul_left]
  exact tsum_congr fun i => (st_mass (hB i) (hsub i)).symm

/-- The coordinate slices of `D₀` carry no mass. -/
theorem st_slice_rep_null (j : Fin (a+b)) (s : ℝ) :
    volume (outputRepresentative d r mu h (pgD0 d r mu ∩ {J | J j = s})) = 0 := by
  set Z := pgD0 d r mu ∩ {J : Fin (a+b) → ℝ | J j = s} with hZdef
  have hZ : volume Z = 0 := by
    refine measure_mono_null inter_subset_right ?_
    simpa [volume_pi] using Measure.pi_hyperplane (fun _ : Fin (a+b) => (volume : Measure ℝ)) j s
  obtain ⟨-, ⟨L, -, hL⟩, -⟩ := ct_spec d r mu h
  refine measure_mono_null inter_subset_left ?_
  rw [ct_rawUnion_eq d r mu h inter_subset_left]
  have : (volume : Measure (Phase (a+b))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  refine measure_iUnion_null fun k => ?_
  rw [Set.image_add_right, measure_preimage_add_right]
  have himg := lip_image_prod (n := a+b) (S := Z ×ˢ torusCube (a+b))
    (F := ctCellMap d r mu h) (Λ := L) fun x hx y hy =>
      hL x ⟨inter_subset_left hx.1, hx.2⟩ y ⟨inter_subset_left hy.1, hy.2⟩
  rw [volume_prod_torusCube, hZ, mul_zero] at himg
  exact le_antisymm himg bot_le

/-- `stepP:p5:st-null`: coordinate slices of `D₀` are null for the mass. -/
theorem st_null (j : Fin (a+b)) (s : ℝ) :
    volume (kset d r mu h (pgD0 d r mu ∩ {J | J j = s}) ∩ cylinderCell d.V r) = 0 := by
  have hD := fam_isSigmaCompact_D0 h
  have hcl : IsClosed {J : Fin (a+b) → ℝ | J j = s} :=
    isClosed_eq (continuous_apply j) continuous_const
  rw [st_mass (stSigma_inter_closed hD hcl) inter_subset_left,
    stMeasure_apply (measurableSet_of_isSigmaCompact (stSigma_inter_closed hD hcl)),
    inter_eq_right.2 inter_subset_left]
  have := st_slice_rep_null (h := h) j s
  rw [this, mul_zero]

theorem stMeasure_slice_null (j : Fin (a+b)) (s : ℝ) :
    stMeasure d r mu h {x | x j = s} = 0 := by
  have hm : MeasurableSet {x : Fin (a+b) → ℝ | x j = s} :=
    measurableSet_eq_fun (measurable_pi_apply j) measurable_const
  rw [← stMeasure_inter_D0 hm, stMeasure_apply (measurableSet_of_isSigmaCompact
    (stSigma_inter_closed (fam_isSigmaCompact_D0 h) (isClosed_eq (continuous_apply j)
      continuous_const))), inter_eq_right.2 inter_subset_left]
  exact st_slice_rep_null j s

end Param

/-- Every value strictly between `0` and the total mass is a cut mass of a coordinate
half-space (the intermediate value step of `stepP:p5:st-ivt`). -/
theorem st_cut_value {N : ℕ} (j : Fin N) (nu : Measure (Fin N → ℝ)) [IsFiniteMeasure nu]
    (hnull : ∀ s : ℝ, nu {x | x j = s} = 0) {m : ℝ} (hm0 : 0 < m)
    (hm : m < (nu univ).toReal) : ∃ s : ℝ, (nu {x | x j ≤ s}).toReal = m := by
  have hc := finite_measure_coordinate_cut j nu hnull
  have hmeas : ∀ s : ℝ, MeasurableSet {x : Fin N → ℝ | x j ≤ s} := fun s =>
    measurableSet_le (measurable_pi_apply j) measurable_const
  have hup : Tendsto (fun n : ℕ => (nu {x | x j ≤ (n:ℝ)}).toReal) atTop
      (𝓝 (nu univ).toReal) := by
    have h1 := tendsto_measure_iUnion_atTop (μ := nu)
      (s := fun n : ℕ => {x : Fin N → ℝ | x j ≤ (n:ℝ)})
      (fun m n hmn x (hx : x j ≤ (m:ℝ)) => le_trans hx (by exact_mod_cast hmn))
    have hU : (⋃ n : ℕ, {x : Fin N → ℝ | x j ≤ (n:ℝ)}) = univ := by
      ext x
      simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
      exact exists_nat_ge _
    rw [hU] at h1
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h1
  have hdown : Tendsto (fun n : ℕ => (nu {x | x j ≤ -(n:ℝ)}).toReal) atTop (𝓝 0) := by
    have h1 := tendsto_measure_iInter_atTop (μ := nu)
      (s := fun n : ℕ => {x : Fin N → ℝ | x j ≤ -(n:ℝ)})
      (fun n => (hmeas _).nullMeasurableSet)
      (fun m n hmn x (hx : x j ≤ -(n:ℝ)) => le_trans hx (by
        have : (m:ℝ) ≤ n := by exact_mod_cast hmn
        linarith)) ⟨0, measure_ne_top _ _⟩
    have hI : (⋂ n : ℕ, {x : Fin N → ℝ | x j ≤ -(n:ℝ)}) = ∅ := by
      ext x
      simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-x j)
      exact ⟨n, by linarith⟩
    rw [hI, measure_empty] at h1
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
  obtain ⟨n1, hn1⟩ := (hup.eventually (lt_mem_nhds hm)).exists_forall_of_atTop
  obtain ⟨n2, hn2⟩ := (hdown.eventually (gt_mem_nhds hm0)).exists_forall_of_atTop
  have hlo := hn2 (max n1 n2) (le_max_right _ _)
  have hhi := hn1 (max n1 n2) (le_max_left _ _)
  have hab : -((max n1 n2 : ℕ) : ℝ) ≤ ((max n1 n2 : ℕ) : ℝ) := by
    have : (0:ℝ) ≤ ((max n1 n2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc hab hc.continuousOn ⟨hlo.le, hhi.le⟩
  exact ⟨s, hs⟩

section Conclusion

variable (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)

theorem stCell_toReal_pos (hr : 0 < r) : 0 < (volume (cylinderCell (b := b) d.V r)).toReal := by
  rw [(disc_measure (b := b) d.hV.measurableSet hr).1, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  have := volume_V_pos d
  positivity

/-- The half-space cut parameter and the strict bounds on its complement, as real numbers. -/
theorem st_ivt (hr : r < finalRadius d) (j : Fin (a+b)) :
    ∃ s : ℝ, (volume (kset d r mu h (pgD0 d r mu ∩ {J | J j ≤ s}) ∩
        cylinderCell d.V r)).toReal =
      min ((volume (kset d r mu h (pgD0 d r mu) ∩ cylinderCell d.V r)).toReal / 2)
        (Real.sqrt r * (volume (cylinderCell (b := b) d.V r)).toReal / 2) := by
  have hD := fam_isSigmaCompact_D0 h
  have hDm := measurableSet_of_isSigmaCompact hD
  obtain ⟨hC0, hlow⟩ := lower d
  have hlow := hlow r mu h
  have hr0 : 0 < r := h.1
  have hρ : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hρ' : Real.sqrt r < (2 * (pgLoss d + 1))⁻¹ := by
    have h1 : r < ((2 * (pgLoss d + 1))⁻¹) ^ 2 := lt_of_lt_of_le hr (min_le_right _ _)
    calc Real.sqrt r < Real.sqrt (((2 * (pgLoss d + 1))⁻¹) ^ 2) := Real.sqrt_lt_sqrt hr0.le h1
      _ = (2 * (pgLoss d + 1))⁻¹ := Real.sqrt_sq (by positivity)
  have hρ2 : Real.sqrt r * (2 * (pgLoss d + 1)) < 1 := by
    have := mul_lt_mul_of_pos_right hρ' (show 0 < 2 * (pgLoss d + 1) by positivity)
    rwa [inv_mul_cancel₀ (by positivity)] at this
  have hKpos := stCell_toReal_pos d r hr0
  have hKfin := stCell_ne_top d hr0
  set c : ℝ := (2 * Real.pi) ^ (a + b) with hc
  have hcpos : 0 < c := by positivity
  set ν := stMeasure d r mu h with hν
  have hνD : ν (pgD0 d r mu) = ν univ := by
    have := measure_add_measure_compl (μ := ν) hDm
    rw [stMeasure_compl_D0 h, add_zero] at this
    exact this
  have hT : (volume (kset d r mu h (pgD0 d r mu) ∩ cylinderCell d.V r)).toReal =
      c * (ν univ).toReal := by
    rw [st_mass_real hD le_rfl, hνD]
  have hTK : (volume (kset d r mu h (pgD0 d r mu) ∩ cylinderCell d.V r)).toReal ≤
      (volume (cylinderCell (b := b) d.V r)).toReal :=
    ENNReal.toReal_mono hKfin (measure_mono inter_subset_right)
  have hlow' : (1 - pgLoss d * Real.sqrt r) *
      (volume (cylinderCell (b := b) d.V r)).toReal ≤
      (volume (kset d r mu h (pgD0 d r mu) ∩ cylinderCell d.V r)).toReal := by
    have hx : 0 ≤ 1 - pgLoss d * Real.sqrt r := by nlinarith
    have := ENNReal.toReal_mono (ne_top_of_le_ne_top hKfin
      (measure_mono inter_subset_right)) hlow
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hx] at this
  have hTpos : 0 < (volume (kset d r mu h (pgD0 d r mu) ∩ cylinderCell d.V r)).toReal := by
    have : 0 < (1 - pgLoss d * Real.sqrt r) * (volume (cylinderCell (b := b) d.V r)).toReal :=
      mul_pos (by nlinarith) hKpos
    linarith
  have htpos : 0 < (ν univ).toReal := by
    rw [hT] at hTpos
    exact pos_of_mul_pos_right hTpos hcpos.le
  set m := min ((ν univ).toReal / 2) (Real.sqrt r * (volume (cylinderCell (b := b) d.V r)).toReal /
    (2 * c)) with hm
  have hm0 : 0 < m := lt_min (by positivity) (by positivity)
  have hm1 : m < (ν univ).toReal := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨s, hs⟩ := st_cut_value j ν (fun s => stMeasure_slice_null j s) hm0 hm1
  refine ⟨s, ?_⟩
  have hcl : IsClosed {J : Fin (a+b) → ℝ | J j ≤ s} := isClosed_le (continuous_apply j)
    continuous_const
  have hBs := stSigma_inter_closed hD hcl
  rw [st_mass_real hBs inter_subset_left, stMeasure_inter_D0 (hcl.measurableSet), hs, hT, hm,
    mul_min_of_nonneg _ _ hcpos.le]
  congr 1
  · ring
  · field_simp

/-- `stepP:p5:st-conc` (with `st-ivt`): deleting the half-space cut. -/
theorem strictness_aux (hr : r < finalRadius d) (j : Fin (a+b)) :
    ∃ B : Set (Fin (a+b) → ℝ),
      B ⊆ pgD0 d r mu ∧ IsSigmaCompact B ∧ IsSigmaCompact (pgD0 d r mu \ B) ∧
      (volume (kset d r mu h B ∩ cylinderCell d.V r)).toReal =
        min ((volume (kset d r mu h (pgD0 d r mu) ∩ cylinderCell d.V r)).toReal / 2)
          (Real.sqrt r * (volume (cylinderCell (b := b) d.V r)).toReal / 2) := by
  obtain ⟨s, hs⟩ := st_ivt d r mu h hr j
  have hD := fam_isSigmaCompact_D0 h
  refine ⟨pgD0 d r mu ∩ {J | J j ≤ s}, inter_subset_left,
    stSigma_inter_closed hD (isClosed_le (continuous_apply j) continuous_const), ?_, hs⟩
  have : pgD0 d r mu \ (pgD0 d r mu ∩ {J | J j ≤ s}) =
      ⋃ n : ℕ, pgD0 d r mu ∩ {J | s + 1 / ((n:ℝ) + 1) ≤ J j} := by
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hx, hxs⟩
      have hlt : s < x j := by
        by_contra hc
        exact hxs ⟨hx, not_lt.1 hc⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
      exact ⟨n, hx, by linarith⟩
    · rintro ⟨n, hx, hn⟩
      refine ⟨hx, fun hx' => ?_⟩
      have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith [hx'.2]
  rw [this]
  exact isSigmaCompact_iUnion _ fun n => stSigma_inter_closed hD
    (isClosed_le continuous_const (continuous_apply j))

end Conclusion

/-- Deletes whole tori via an action-coordinate half-space; both sides remain sigma compact. -/
theorem strictness (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (hr : r < finalRadius d) : ∃ B : Set (Fin (a+b) → ℝ),
      B ⊆ pgD0 d r mu ∧ IsSigmaCompact B ∧ IsSigmaCompact (pgD0 d r mu \ B) ∧
      0 < volume (kset d r mu h (pgD0 d r mu \ B) ∩ cylinderCell d.V r) ∧
      ENNReal.ofReal (1-(pgLoss d+1/2)*Real.sqrt r)*volume (cylinderCell (b:=b) d.V r) ≤
        volume (kset d r mu h (pgD0 d r mu \ B) ∩ cylinderCell d.V r) ∧
      volume (kset d r mu h (pgD0 d r mu \ B) ∩ cylinderCell d.V r) <
        volume (cylinderCell (b:=b) d.V r) := by
  have hj : 0 < a + b := lt_of_lt_of_le d.hb (Nat.le_add_left _ _)
  obtain ⟨B, hBD, hBσ, hDBσ, hBm⟩ := strictness_aux d r mu h hr ⟨0, hj⟩
  have hD := fam_isSigmaCompact_D0 h
  have hr0 : 0 < r := h.1
  have hρ : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  obtain ⟨hC0, hlow⟩ := lower d
  have hlow := hlow r mu h
  have hKpos := stCell_toReal_pos d r hr0
  have hKfin := stCell_ne_top d hr0
  have hρ' : Real.sqrt r < (2 * (pgLoss d + 1))⁻¹ := by
    have h1 : r < ((2 * (pgLoss d + 1))⁻¹) ^ 2 := lt_of_lt_of_le hr (min_le_right _ _)
    calc Real.sqrt r < Real.sqrt (((2 * (pgLoss d + 1))⁻¹) ^ 2) := Real.sqrt_lt_sqrt hr0.le h1
      _ = (2 * (pgLoss d + 1))⁻¹ := Real.sqrt_sq (by positivity)
  have hρ2 : Real.sqrt r * (2 * (pgLoss d + 1)) < 1 := by
    have := mul_lt_mul_of_pos_right hρ' (show 0 < 2 * (pgLoss d + 1) by positivity)
    rwa [inv_mul_cancel₀ (by positivity)] at this
  set K := (volume (cylinderCell (b := b) d.V r)).toReal with hK
  set T := (volume (kset d r mu h (pgD0 d r mu) ∩ cylinderCell d.V r)).toReal with hTdef
  set W := volume (kset d r mu h (pgD0 d r mu \ B) ∩ cylinderCell d.V r) with hW
  have hWfin : W ≠ ⊤ := ne_top_of_le_ne_top hKfin (measure_mono inter_subset_right)
  have hTfin : volume (kset d r mu h (pgD0 d r mu) ∩ cylinderCell d.V r) ≠ ⊤ :=
    ne_top_of_le_ne_top hKfin (measure_mono inter_subset_right)
  have hTK : T ≤ K := ENNReal.toReal_mono hKfin (measure_mono inter_subset_right)
  have hlow' : (1 - pgLoss d * Real.sqrt r) * K ≤ T := by
    have hx : 0 ≤ 1 - pgLoss d * Real.sqrt r := by nlinarith
    have := ENNReal.toReal_mono hTfin hlow
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hx] at this
  have hTpos : 0 < T := by
    have : 0 < (1 - pgLoss d * Real.sqrt r) * K := mul_pos (by nlinarith) hKpos
    linarith
  -- the mass splits
  have hsplit : T = (volume (kset d r mu h B ∩ cylinderCell d.V r)).toReal + W.toReal := by
    have hν := measure_inter_add_sdiff (μ := stMeasure d r mu h) (pgD0 d r mu)
      (measurableSet_of_isSigmaCompact hBσ)
    rw [inter_eq_right.2 hBD] at hν
    have hf1 : stMeasure d r mu h B ≠ ⊤ := measure_ne_top _ _
    have hf2 : stMeasure d r mu h (pgD0 d r mu \ B) ≠ ⊤ := measure_ne_top _ _
    rw [hTdef, hW, st_mass_real hD le_rfl, st_mass_real hBσ hBD,
      st_mass_real hDBσ sdiff_subset, ← mul_add, ← ENNReal.toReal_add hf1 hf2, hν]
  set q := (volume (kset d r mu h B ∩ cylinderCell d.V r)).toReal with hq
  have hq1 : q ≤ T / 2 := hBm ▸ min_le_left _ _
  have hq2 : q ≤ Real.sqrt r * K / 2 := hBm ▸ min_le_right _ _
  have hq0 : 0 < q := by
    rw [hBm]; exact lt_min (by linarith) (by positivity)
  have hW' : W.toReal = T - q := by linarith
  have hKr : ENNReal.ofReal K = volume (cylinderCell (b := b) d.V r) :=
    ENNReal.ofReal_toReal hKfin
  refine ⟨B, hBD, hBσ, hDBσ, ?_, ?_, ?_⟩
  · exact (ENNReal.toReal_pos_iff.1 (by rw [hW']; linarith)).1
  · have hx : 0 ≤ 1 - (pgLoss d + 1/2) * Real.sqrt r := by nlinarith
    rw [← hKr, ← ENNReal.ofReal_mul hx]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (le_of_eq (ENNReal.ofReal_toReal hWfin))
    rw [hW']
    nlinarith
  · exact (ENNReal.toReal_lt_toReal hWfin hKfin).1 (by rw [hW']; linarith)

end KAM.Planetary

end
