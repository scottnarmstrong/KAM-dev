/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.ParameterLipschitz
public import KAM.Measure.McShane
public import KAM.Measure.Lipeo
public import KAM.Measure.Lipschitz

/-! # P11B evaluation map: `evaluation_bilipschitz`

The evaluation `z ↦ (θ, b) + defect b θ` on `Kinf`-fibres is extended (McShane, `mcshane_prod`) to a
globally `lam`-Lipschitz perturbation of the identity, `lam = 2⁻¹⁰`. Then `lipeo_onto` gives the
bijective extension with inverse bound, and `lip_image_prod` the two volume estimates (the LOWER
one through the inverse Lipschitz map, factor `(1 - lam)^(2n)`). The half-open cube is a countable
union of compact inner boxes, so its evaluation image is a countable union of compacts; the closed
cell image is compact, integer lattice saturation (using periodicity of the defect) gives the real
covering image, and its image in the `AddCircle` quotient is compact.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function Metric
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

def selectionHalfCell (H : Set (SelectionR n)) : Set (Phase n) :=
  {z | z.2 ∈ H ∧ ∀ i, z.1 i ∈ Ico (0 : ℝ) 1}
def selectionClosedCell (H : Set (SelectionR n)) : Set (Phase n) :=
  {z | z.2 ∈ H ∧ ∀ i, z.1 i ∈ Icc (0 : ℝ) 1}
def selectionQuotient (z : Phase n) : (Fin n → AddCircle (1 : ℝ)) × SelectionR n :=
  (fun i => (z.1 i : AddCircle (1 : ℝ)), z.2)

/-! ### Extension data -/

/-- A global Lipschitz perturbation `Φ` of the identity that agrees with the evaluation `ev` on the
fibres over `Kinf`, with `ev` periodic there. -/
structure EvalExtData (Kinf : Set (SelectionR n)) (ev : Phase n → Phase n) (lam : ℝ) where
  Φ : Phase n → Phase n
  lam_nonneg : 0 ≤ lam
  lam_lt : lam < 1
  lip : ∀ x y, ‖Φ x - Φ y‖ ≤ lam * ‖x - y‖
  ev_eq : ∀ z : Phase n, z.2 ∈ Kinf → ev z = z + Φ z
  periodic : ∀ z : Phase n, z.2 ∈ Kinf → ∀ k : Fin n → ℤ,
    ev (z + ((fun i => (k i : ℝ)), 0)) = ev z + ((fun i => (k i : ℝ)), 0)

namespace EvalExtData
variable {Kinf : Set (SelectionR n)} {ev : Phase n → Phase n} {lam : ℝ}
  (D : EvalExtData Kinf ev lam)
include D

/-- The global extension `z ↦ z + Φ z`. -/
def E (z : Phase n) : Phase n := z + D.Φ z

theorem continuous_E : Continuous D.E := by
  have : Continuous D.Φ :=
    (LipschitzWith.of_dist_le_mul (K := ⟨lam, D.lam_nonneg⟩) fun x y => by
      rw [dist_eq_norm, dist_eq_norm]; exact D.lip x y).continuous
  exact continuous_id.add this

theorem bounds (x y : Phase n) :
    (1 - lam) * ‖x - y‖ ≤ ‖D.E x - D.E y‖ ∧ ‖D.E x - D.E y‖ ≤ (1 + lam) * ‖x - y‖ :=
  (lipeo_bounds D.lam_lt D.lip).1 x y

theorem bij_inv : Bijective D.E ∧ ∀ x y, ‖x - y‖ ≤ (1 - lam)⁻¹ * ‖D.E x - D.E y‖ :=
  lipeo_onto D.lam_lt D.lip

theorem ev_image {Hs : Set (SelectionR n)} (hH : Hs ⊆ Kinf) {A : Set (Phase n)}
    (hA : ∀ z ∈ A, z.2 ∈ Hs) : ev '' A = D.E '' A :=
  image_congr fun z hz => D.ev_eq z (hH (hA z hz))

theorem measure_lower_aux (A : Set (Phase n)) :
    ENNReal.ofReal ((1 - lam) ^ (2 * n)) * volume A ≤ volume (D.E '' A) := by
  obtain ⟨hb, hinv⟩ := D.bij_inv
  have hpos : 0 < 1 - lam := sub_pos.2 D.lam_lt
  let e := Equiv.ofBijective D.E hb
  have h := lip_image_prod (S := D.E '' A) (F := e.symm) (Λ := (1 - lam)⁻¹) (by
    intro x _ y _
    have h1 := hinv (e.symm x) (e.symm y)
    have hx : D.E (e.symm x) = x := e.apply_symm_apply x
    have hy : D.E (e.symm y) = y := e.apply_symm_apply y
    rw [hx, hy] at h1
    exact h1)
  have himg : e.symm '' (D.E '' A) = A := Equiv.symm_image_image e A
  rw [himg] at h
  calc ENNReal.ofReal ((1 - lam) ^ (2 * n)) * volume A
      ≤ ENNReal.ofReal ((1 - lam) ^ (2 * n)) *
          (ENNReal.ofReal (((1 - lam)⁻¹) ^ (2 * n)) * volume (D.E '' A)) := by gcongr
    _ = volume (D.E '' A) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hpos.le _), ← mul_pow,
        mul_inv_cancel₀ hpos.ne', one_pow, ENNReal.ofReal_one, one_mul]

theorem measure_upper_aux (A : Set (Phase n)) :
    volume (D.E '' A) ≤ ENNReal.ofReal ((1 + lam) ^ (2 * n)) * volume A :=
  lip_image_prod (S := A) (F := D.E) (Λ := 1 + lam) fun x _ y _ => (D.bounds x y).2

end EvalExtData

/-! ### Cells -/

theorem selectionHalfCell_eq (H : Set (SelectionR n)) :
    selectionHalfCell H = (Set.pi univ fun _ => Ico (0 : ℝ) 1) ×ˢ H := by
  ext z
  simp only [selectionHalfCell, mem_ofPred_eq, mem_prod, Set.mem_pi, mem_univ, true_implies]
  exact and_comm

theorem selectionClosedCell_eq (H : Set (SelectionR n)) :
    selectionClosedCell H = (Set.pi univ fun _ => Icc (0 : ℝ) 1) ×ˢ H := by
  ext z
  simp only [selectionClosedCell, mem_ofPred_eq, mem_prod, Set.mem_pi, mem_univ, true_implies]
  exact and_comm

theorem volume_selectionHalfCell (H : Set (SelectionR n)) :
    volume (selectionHalfCell H) = volume H := by
  rw [selectionHalfCell_eq, Measure.volume_eq_prod, Measure.prod_prod, volume_pi_Ico]
  simp

theorem selectionHalfCell_subset (H : Set (SelectionR n)) :
    ∀ z ∈ selectionHalfCell H, z.2 ∈ H := fun _ hz => hz.1

theorem selectionClosedCell_subset (H : Set (SelectionR n)) :
    ∀ z ∈ selectionClosedCell H, z.2 ∈ H := fun _ hz => hz.1

/-- Compact inner boxes exhausting the half-open cell. -/
def selectionInnerBox (H : Set (SelectionR n)) (j : ℕ) : Set (Phase n) :=
  (Set.pi univ fun _ => Icc (0 : ℝ) (1 - 1 / ((j : ℝ) + 1))) ×ˢ H

theorem selectionInnerBox_compact {H : Set (SelectionR n)} (hH : IsCompact H) (j : ℕ) :
    IsCompact (selectionInnerBox H j) :=
  (isCompact_univ_pi fun _ => isCompact_Icc).prod hH

theorem selectionHalfCell_eq_iUnion (H : Set (SelectionR n)) :
    selectionHalfCell H = ⋃ j : ℕ, selectionInnerBox H j := by
  ext z
  simp only [selectionHalfCell, selectionInnerBox, mem_ofPred_eq, mem_iUnion, mem_prod,
    Set.mem_pi, mem_univ, true_implies, mem_Ico, mem_Icc]
  constructor
  · rintro ⟨hz2, h⟩
    choose j hj using fun i => exists_nat_one_div_lt (sub_pos.2 (h i).2)
    refine ⟨Finset.univ.sup j, fun i => ⟨(h i).1, ?_⟩, hz2⟩
    have hle : (j i : ℝ) + 1 ≤ ((Finset.univ.sup j : ℕ) : ℝ) + 1 := by
      have : (j i : ℝ) ≤ ((Finset.univ.sup j : ℕ) : ℝ) :=
        Nat.cast_le.2 (Finset.le_sup (Finset.mem_univ i))
      linarith
    have := one_div_le_one_div_of_le (by positivity) hle
    linarith [hj i]
  · rintro ⟨j, h, hz2⟩
    refine ⟨hz2, fun i => ⟨(h i).1, ?_⟩⟩
    have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    linarith [(h i).2]

theorem selectionClosedCell_compact {H : Set (SelectionR n)} (hH : IsCompact H) :
    IsCompact (selectionClosedCell H) := by
  rw [selectionClosedCell_eq]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).prod hH

namespace EvalExtData
variable {Kinf : Set (SelectionR n)} {ev : Phase n → Phase n} {lam : ℝ}
  (D : EvalExtData Kinf ev lam)
include D

theorem compact_union {H : Set (SelectionR n)} (hH : IsCompact H) (hHK : H ⊆ Kinf) :
    ∃ C : ℕ → Set (Phase n), (∀ j, IsCompact (C j)) ∧ ev '' selectionHalfCell H = ⋃ j, C j := by
  refine ⟨fun j => D.E '' selectionInnerBox H j, fun j =>
    (selectionInnerBox_compact hH j).image D.continuous_E, ?_⟩
  rw [D.ev_image hHK (selectionHalfCell_subset H), selectionHalfCell_eq_iUnion, image_iUnion]

theorem closed_union {H : Set (SelectionR n)} (hH : IsCompact H) (hHK : H ⊆ Kinf) :
    ∃ C : ℕ → Set (Phase n), (∀ j, IsClosed (C j)) ∧ ev '' selectionHalfCell H = ⋃ j, C j :=
  let ⟨C, hC, e⟩ := D.compact_union hH hHK
  ⟨C, fun j => (hC j).isClosed, e⟩

theorem sigma_compact {H : Set (SelectionR n)} (hH : IsCompact H) (hHK : H ⊆ Kinf) :
    IsSigmaCompact (ev '' selectionHalfCell H) := by
  obtain ⟨C, hC, e⟩ := D.compact_union hH hHK
  rw [e]
  exact isSigmaCompact_iUnion_of_isCompact C hC

theorem measurable {H : Set (SelectionR n)} (hH : IsCompact H) (hHK : H ⊆ Kinf) :
    MeasurableSet (ev '' selectionHalfCell H) := by
  obtain ⟨C, hC, e⟩ := D.closed_union hH hHK
  rw [e]
  exact MeasurableSet.iUnion fun j => (hC j).measurableSet

theorem closed_image_compact {H : Set (SelectionR n)} (hH : IsCompact H) (hHK : H ⊆ Kinf) :
    IsCompact (ev '' selectionClosedCell H) := by
  rw [D.ev_image hHK (selectionClosedCell_subset H)]
  exact (selectionClosedCell_compact hH).image D.continuous_E

theorem lattice_union {H : Set (SelectionR n)} (hHK : H ⊆ Kinf) :
    ev '' {z : Phase n | z.2 ∈ H} =
      ⋃ k : Fin n → ℤ, (fun z : Phase n => z + ((fun i => (k i : ℝ)), 0)) ''
        (ev '' selectionClosedCell H) := by
  ext w
  simp only [mem_image, mem_iUnion]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz : z.2 ∈ H := hz
    let k : Fin n → ℤ := fun i => ⌊z.1 i⌋
    let z' : Phase n := (fun i => z.1 i - k i, z.2)
    have hz'K : z'.2 ∈ Kinf := hHK hz
    have hzz : z' + ((fun i => (k i : ℝ)), 0) = z := by
      ext i <;> simp [z']
    refine ⟨k, ev z', ⟨z', ⟨hz, fun i => ?_⟩, rfl⟩, ?_⟩
    · have h0 : 0 ≤ z.1 i - ⌊z.1 i⌋ := Int.fract_nonneg _
      have h1 : z.1 i - ⌊z.1 i⌋ < 1 := Int.fract_lt_one _
      exact ⟨h0, h1.le⟩
    · have := D.periodic z' hz'K k
      rw [hzz] at this
      exact this.symm
  · rintro ⟨k, w', ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨z + ((fun i => (k i : ℝ)), 0), by simpa using hz.1, ?_⟩
    exact D.periodic z (hHK hz.1) k

end EvalExtData

theorem selectionQuotient_add_lattice (w : Phase n) (k : Fin n → ℤ) :
    selectionQuotient (w + ((fun i => (k i : ℝ)), 0)) = selectionQuotient w := by
  refine Prod.ext (funext fun i => ?_) (by simp [selectionQuotient])
  simp [selectionQuotient]

theorem continuous_selectionQuotient : Continuous (selectionQuotient (n := n)) := by
  unfold selectionQuotient
  refine Continuous.prodMk ?_ continuous_snd
  exact continuous_pi fun i =>
    (AddCircle.continuous_mk' (1 : ℝ)).comp ((continuous_apply i).comp continuous_fst)

namespace EvalExtData
variable {Kinf : Set (SelectionR n)} {ev : Phase n → Phase n} {lam : ℝ}
  (D : EvalExtData Kinf ev lam)
include D

theorem quotient_compact {H : Set (SelectionR n)} (hH : IsCompact H) (hHK : H ⊆ Kinf) :
    IsCompact (selectionQuotient '' (ev '' {z : Phase n | z.2 ∈ H})) := by
  have key : selectionQuotient '' (ev '' {z : Phase n | z.2 ∈ H}) =
      selectionQuotient '' (ev '' selectionClosedCell H) := by
    rw [D.lattice_union hHK, image_iUnion]
    have : ∀ k : Fin n → ℤ, selectionQuotient ''
        ((fun z : Phase n => z + ((fun i => (k i : ℝ)), 0)) '' (ev '' selectionClosedCell H)) =
        selectionQuotient '' (ev '' selectionClosedCell H) := fun k => by
      rw [image_image]
      exact image_congr fun w _ => selectionQuotient_add_lattice w k
    simp_rw [this]
    exact iUnion_const _
  rw [key]
  exact (D.closed_image_compact hH hHK).image continuous_selectionQuotient

end EvalExtData

/-! ### The output record -/

/-- Joint final output: the same chain, frequencies and family satisfy all clauses. -/
structure SelectionEvaluationOutput (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (ε : ℝ) extends SelectionLipschitz d f ε where
  bilipschitz : ∀ b ∈ Kinf, ∀ b' ∈ Kinf, ∀ θ θ',
    (1 - (2 : ℝ)⁻¹ ^ 10) * ‖((θ, b) : Phase n) - (θ', b')‖ ≤
      ‖selectionEvaluation defect b θ - selectionEvaluation defect b' θ'‖ ∧
    ‖selectionEvaluation defect b θ - selectionEvaluation defect b' θ'‖ ≤
      (1 + (2 : ℝ)⁻¹ ^ 10) * ‖((θ, b) : Phase n) - (θ', b')‖
  inverse_bound : ∀ b ∈ Kinf, ∀ b' ∈ Kinf, ∀ θ θ',
    ‖((θ, b) : Phase n) - (θ', b')‖ ≤ (1 - (2 : ℝ)⁻¹ ^ 10)⁻¹ *
      ‖selectionEvaluation defect b θ - selectionEvaluation defect b' θ'‖
  extension : Phase n → Phase n
  extension_eq : ∀ z : Phase n, z.2 ∈ Kinf → extension z = selectionEvaluation defect z.2 z.1
  extension_bijective : Bijective extension
  extension_defect_lip : ∀ z z',
    ‖(extension z - z) - (extension z' - z')‖ ≤ (2 : ℝ)⁻¹ ^ 10 * ‖z - z'‖
  image_closed_union : ∀ H : Set (SelectionR n), IsCompact H → H ⊆ Kinf →
    ∃ C : ℕ → Set (Phase n), (∀ j, IsClosed (C j)) ∧
      (fun z : Phase n => selectionEvaluation defect z.2 z.1) '' selectionHalfCell H = ⋃ j, C j
  image_fsigma : ∀ H : Set (SelectionR n), IsCompact H → H ⊆ Kinf →
    IsSigmaCompact ((fun z : Phase n => selectionEvaluation defect z.2 z.1) '' selectionHalfCell H)
  image_measurable : ∀ H : Set (SelectionR n), IsCompact H → H ⊆ Kinf →
    MeasurableSet ((fun z : Phase n => selectionEvaluation defect z.2 z.1) '' selectionHalfCell H)
  measure_lower : ∀ H : Set (SelectionR n), IsCompact H → H ⊆ Kinf →
    ENNReal.ofReal ((1 - (2 : ℝ)⁻¹ ^ 10) ^ (2 * n)) * volume H ≤
      volume ((fun z : Phase n => selectionEvaluation defect z.2 z.1) '' selectionHalfCell H)
  measure_coarse : ∀ H : Set (SelectionR n), IsCompact H → H ⊆ Kinf →
    ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (2 * n)) * volume H ≤
      volume ((fun z : Phase n => selectionEvaluation defect z.2 z.1) '' selectionHalfCell H)
  measure_upper : ∀ H : Set (SelectionR n), IsCompact H → H ⊆ Kinf →
    volume ((fun z : Phase n => selectionEvaluation defect z.2 z.1) '' selectionHalfCell H) ≤
      ENNReal.ofReal ((1 + (2 : ℝ)⁻¹ ^ 10) ^ (2 * n)) * volume H
  closed_image_compact : ∀ H : Set (SelectionR n), IsCompact H → H ⊆ Kinf →
    IsCompact ((fun z : Phase n => selectionEvaluation defect z.2 z.1) '' selectionClosedCell H)
  lattice_union : ∀ H : Set (SelectionR n), H ⊆ Kinf →
    (fun z : Phase n => selectionEvaluation defect z.2 z.1) '' {z | z.2 ∈ H} =
      ⋃ k : Fin n → ℤ, (fun z : Phase n => z + ((fun i => (k i : ℝ)), 0)) ''
        ((fun z : Phase n => selectionEvaluation defect z.2 z.1) '' selectionClosedCell H)
  quotient_compact : ∀ H : Set (SelectionR n), IsCompact H → H ⊆ Kinf →
    IsCompact (selectionQuotient ''
      ((fun z : Phase n => selectionEvaluation defect z.2 z.1) '' {z | z.2 ∈ H}))

/-! ### The theorem -/

theorem evaluation_bilipschitz (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) : Nonempty (SelectionEvaluationOutput d f ε) := by
  obtain ⟨L⟩ := lipschitz_family d ε he hsmall f hf
  obtain ⟨⟨Φ, hΦl, hΦe⟩, -⟩ := mcshane_prod (X := Phase n)
    (S := {z : Phase n | z.2 ∈ L.Kinf}) (Λ := (2 : ℝ)⁻¹ ^ 10) (by positivity)
    (φ := fun z => L.defect z.2 z.1) (fun x hx y hy => by
      simpa [dist_eq_norm] using L.lipschitz_joint x.2 hx y.2 hy x.1 y.1)
  let ev : Phase n → Phase n := fun z => selectionEvaluation L.defect z.2 z.1
  have hlam : (2 : ℝ)⁻¹ ^ 10 < 1 := by norm_num
  let D : EvalExtData L.Kinf ev ((2 : ℝ)⁻¹ ^ 10) :=
    { Φ := Φ
      lam_nonneg := by positivity
      lam_lt := hlam
      lip := fun x y => by simpa [dist_eq_norm] using hΦl x y
      ev_eq := fun z hz => by
        have h : Φ z = L.defect z.2 z.1 := hΦe z hz
        show (z.1, z.2) + L.defect z.2 z.1 = z + Φ z
        rw [h]
      periodic := fun z hz k => by
        simp only [ev, selectionEvaluation, Prod.fst_add, Prod.snd_add, add_zero]
        rw [L.periodic z.2 hz z.1 k]
        ext i <;> simp; ring }
  have hbil : ∀ b ∈ L.Kinf, ∀ b' ∈ L.Kinf, ∀ θ θ' : SelectionR n,
      D.E (θ, b) - D.E (θ', b') = ev (θ, b) - ev (θ', b') := fun b hb b' hb' θ θ' => by
    have e1 : D.E (θ, b) = ev (θ, b) := (D.ev_eq (θ, b) hb).symm
    have e2 : D.E (θ', b') = ev (θ', b') := (D.ev_eq (θ', b') hb').symm
    rw [e1, e2]
  refine ⟨{ L with
    bilipschitz := fun b hb b' hb' θ θ' => ?_
    inverse_bound := fun b hb b' hb' θ θ' => ?_
    extension := D.E
    extension_eq := fun z hz => (D.ev_eq z hz).symm
    extension_bijective := D.bij_inv.1
    extension_defect_lip := fun z z' => ?_
    image_closed_union := fun H hH hHK => D.closed_union hH hHK
    image_fsigma := fun H hH hHK => D.sigma_compact hH hHK
    image_measurable := fun H hH hHK => D.measurable hH hHK
    measure_lower := fun H hH hHK => ?_
    measure_coarse := fun H hH hHK => ?_
    measure_upper := fun H hH hHK => ?_
    closed_image_compact := fun H hH hHK => D.closed_image_compact hH hHK
    lattice_union := fun H hHK => D.lattice_union hHK
    quotient_compact := fun H hH hHK => D.quotient_compact hH hHK }⟩
  · have h := D.bounds (θ, b) (θ', b')
    have e := hbil b hb b' hb' θ θ'
    rw [e] at h
    exact h
  · have h := D.bij_inv.2 (θ, b) (θ', b')
    have e := hbil b hb b' hb' θ θ'
    rw [e] at h
    exact h
  · have e : (D.E z - z) - (D.E z' - z') = Φ z - Φ z' := by
      show (z + Φ z - z) - (z' + Φ z' - z') = _
      abel
    rw [e]
    simpa [dist_eq_norm] using hΦl z z'
  · rw [D.ev_image hHK (selectionHalfCell_subset H)]
    have h := D.measure_lower_aux (selectionHalfCell H)
    rwa [volume_selectionHalfCell] at h
  · rw [D.ev_image hHK (selectionHalfCell_subset H)]
    have h := D.measure_lower_aux (selectionHalfCell H)
    rw [volume_selectionHalfCell] at h
    refine le_trans ?_ h
    gcongr
    norm_num
  · rw [D.ev_image hHK (selectionHalfCell_subset H)]
    have h := D.measure_upper_aux (selectionHalfCell H)
    rwa [volume_selectionHalfCell] at h

/-- Source situation is output packaging, not a new standing-assumption structure. -/
def situation (d : SelectionData n) (f : SelectionPhaseC n → ℂ) (ε : ℝ) :=
  SelectionEvaluationOutput d f ε

end KAM.Planetary

end
