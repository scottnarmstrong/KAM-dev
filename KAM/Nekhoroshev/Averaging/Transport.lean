/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.Flow
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Part N12: transport of integrals through the flow (`bpN:p12:transport`)

`avgCell ell` is the half-open unit angle cell with free actions. `transport` bounds the integral
over a measurable piece `D` of one initial cell of `g` composed with the action part of the time-`t`
flow by the integral of `g` over `avgG n R`. There is no global assumption on the flow domain:
change of variables is applied on `D ⊆ Ω_t` (the flow is `C¹`, injective, of determinant one), the
image is cut into integer angle cells, every cell is translated to the fundamental cell, and the
translated pieces are disjoint because two flow points in the same half-open initial cell cannot
differ by a nonzero integer angle shift.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace KAM.Nekhoroshev

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

/-- Half-open angle cell with free actions. -/
def avgCell (ell : Fin n → ℤ) : Set (AvgPhase n) :=
  {x | ∀ i, (ell i : ℝ) ≤ x.1 i ∧ x.1 i < (ell i : ℝ) + 1}

/-- Lebesgue measure on the phase space is an additive Haar measure (product instance). -/
instance avgPhase_isAddHaar (n : ℕ) : (volume : Measure (AvgPhase n)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

section Cells

theorem measurableSet_avgCell (ell : Fin n → ℤ) : MeasurableSet (avgCell ell) := by
  have : avgCell ell = ⋂ i, ({x : AvgPhase n | (ell i : ℝ) ≤ x.1 i} ∩
      {x : AvgPhase n | x.1 i < (ell i : ℝ) + 1}) := by
    ext x; simp [avgCell, forall_and]
  rw [this]
  exact MeasurableSet.iInter fun i => (measurableSet_le measurable_const
    ((measurable_pi_apply i).comp measurable_fst)).inter (measurableSet_lt
    ((measurable_pi_apply i).comp measurable_fst) measurable_const)

theorem mem_avgCell_floor (y : AvgPhase n) : y ∈ avgCell (fun i => ⌊y.1 i⌋) :=
  fun _ => ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

theorem avgCell_unique {k k' : Fin n → ℤ} {y : AvgPhase n} (hk : y ∈ avgCell k)
    (hk' : y ∈ avgCell k') : k = k' := by
  funext i
  have h1 := hk i
  have h2 := hk' i
  have a : (k i : ℝ) < k' i + 1 := h1.1.trans_lt h2.2
  have b : (k' i : ℝ) < k i + 1 := h2.1.trans_lt h1.2
  have a' : k i < k' i + 1 := by exact_mod_cast a
  have b' : k' i < k i + 1 := by exact_mod_cast b
  omega

theorem disjoint_avgCell {k k' : Fin n → ℤ} (hne : k ≠ k') : Disjoint (avgCell k) (avgCell k' :
    Set (AvgPhase n)) :=
  Set.disjoint_left.2 fun _ h1 h2 => hne (avgCell_unique h1 h2)

end Cells

section Translates

/-- Translating a piece `S ∩ cell k` back to the fundamental cell. -/
def cellPiece (S : Set (AvgPhase n)) (k : Fin n → ℤ) : Set (AvgPhase n) :=
  (fun y => y + KAM.ODE.angleShift k) ⁻¹' (S ∩ avgCell k)

theorem measurableSet_cellPiece {S : Set (AvgPhase n)} (hS : MeasurableSet S) (k : Fin n → ℤ) :
    MeasurableSet (cellPiece S k) :=
  (hS.inter (measurableSet_avgCell k)).preimage (measurable_id.add_const _)

theorem cellPiece_subset {S : Set (AvgPhase n)} {G : Set (Fin n → ℝ)}
    (hSG : ∀ y ∈ S, y.2 ∈ G) (k : Fin n → ℤ) :
    cellPiece S k ⊆ (pi univ fun _ => Ico (0 : ℝ) 1) ×ˢ G := by
  intro y hy
  obtain ⟨hyS, hyc⟩ := hy
  refine ⟨fun i _ => ?_, by simpa [KAM.ODE.angleShift] using hSG _ hyS⟩
  have := hyc i
  simp only [KAM.ODE.angleShift, Prod.fst_add, Pi.add_apply] at this
  simp only [mem_Ico]
  constructor <;> linarith [this.1, this.2]

theorem lintegral_cellPiece (g : (Fin n → ℝ) → ℝ≥0∞) (S : Set (AvgPhase n)) (k : Fin n → ℤ) :
    ∫⁻ y in cellPiece S k, g y.2 = ∫⁻ y in S ∩ avgCell k, g y.2 := by
  have hme := measurableEmbedding_addRight (KAM.ODE.angleShift k : AvgPhase n)
  have := (measurePreserving_add_right (volume : Measure (AvgPhase n))
    (KAM.ODE.angleShift k)).setLIntegral_comp_preimage_emb hme (fun y => g y.2) (S ∩ avgCell k)
  simpa [cellPiece, KAM.ODE.angleShift] using this

/-- Disjoint translated pieces fit in one fundamental cell times `G`. -/
theorem lintegral_le_of_disjoint_cellPieces {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g)
    {S : Set (AvgPhase n)} (hS : MeasurableSet S) {G : Set (Fin n → ℝ)}
    (hSG : ∀ y ∈ S, y.2 ∈ G)
    (hdisj : ∀ k k', k ≠ k' → Disjoint (cellPiece S k) (cellPiece S k')) :
    ∫⁻ y in S, g y.2 ≤ ∫⁻ I in G, g I := by
  have hS_eq : S = ⋃ k, S ∩ avgCell k := by
    ext y
    simp only [mem_iUnion, mem_inter_iff]
    exact ⟨fun hy => ⟨_, hy, mem_avgCell_floor y⟩, fun ⟨_, hy, _⟩ => hy⟩
  have hcm : ∀ k, MeasurableSet (S ∩ avgCell k) := fun k => hS.inter (measurableSet_avgCell k)
  have hcd : Pairwise (Function.onFun Disjoint fun k => S ∩ avgCell k) := fun k k' hne =>
    (disjoint_avgCell hne).mono inter_subset_right inter_subset_right
  calc ∫⁻ y in S, g y.2 = ∑' k, ∫⁻ y in S ∩ avgCell k, g y.2 := by
        conv_lhs => rw [hS_eq]
        exact lintegral_iUnion hcm hcd _
    _ = ∑' k, ∫⁻ y in cellPiece S k, g y.2 := by simp_rw [lintegral_cellPiece]
    _ = ∫⁻ y in ⋃ k, cellPiece S k, g y.2 :=
        (lintegral_iUnion (measurableSet_cellPiece hS) hdisj _).symm
    _ ≤ ∫⁻ y in (pi univ fun _ => Ico (0 : ℝ) 1) ×ˢ G, g y.2 :=
        lintegral_mono_set (iUnion_subset (cellPiece_subset hSG))
    _ = ∫⁻ I in G, g I := by
        have hm : AEMeasurable (fun y : (Fin n → ℝ) × (Fin n → ℝ) => g y.2)
            ((volume.restrict (pi univ fun _ => Ico (0 : ℝ) 1)).prod (volume.restrict G)) :=
          (hg.comp measurable_snd).aemeasurable
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hm]
        simp [Real.volume_pi_Ico]

end Translates

section Transport

variable (d : AveragingData n R s h f) (ε : ℝ)
include d

theorem transport {t : ℝ} (ht : 0 ≤ t)
    (g : (Fin n → ℝ) → ℝ≥0∞) (hg : Measurable g) (ell : Fin n → ℤ)
    {D : Set (AvgPhase n)} (hD : MeasurableSet D)
    (hDO : D ⊆ avgOmega h f R ε t) (hcell : D ⊆ avgCell ell)
    (hDG : ∀ x ∈ D, (avgFlow h f R ε t x).2 ∈ avgG n R) :
    (∫⁻ x in D, g (avgFlow h f R ε t x).2) ≤ ∫⁻ I in avgG n R, g I := by
  have hΩ := isOpen_avgOmega d ε t
  have hC := contDiffOn_avgFlow d ε t
  have hinjΩ : InjOn (avgFlow h f R ε t) (avgOmega h f R ε t) :=
    LeftInvOn.injOn fun x hx => (avgFlow_inverse d ε hx).2
  have hinj := hinjΩ.mono hDO
  have hder : ∀ x ∈ D, HasFDerivWithinAt (avgFlow h f R ε t)
      (fderiv ℝ (avgFlow h f R ε t) x) D x := fun x hx =>
    (((hC.differentiableOn one_ne_zero x (hDO hx)).differentiableAt
      (hΩ.mem_nhds (hDO hx))).hasFDerivAt).hasFDerivWithinAt
  have hSm : MeasurableSet (avgFlow h f R ε t '' D) :=
    hD.image_of_continuousOn_injOn (hC.continuousOn.mono hDO) hinj
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure (AvgPhase n))
    hD hder hinj (fun y => g y.2)
  have h1 : ∫⁻ x in D, g (avgFlow h f R ε t x).2 = ∫⁻ y in avgFlow h f R ε t '' D, g y.2 := by
    rw [hcov]
    refine setLIntegral_congr_fun hD fun x hx => ?_
    rw [det_fderiv_avgFlow d ε (hDO hx)]
    simp
  rw [h1]
  refine lintegral_le_of_disjoint_cellPieces hg hSm
    (by rintro _ ⟨x, hx, rfl⟩; exact hDG x hx) fun k k' hne => ?_
  rw [Set.disjoint_left]
  rintro y ⟨⟨x, hx, hxy⟩, hyc⟩ ⟨⟨x', hx', hxy'⟩, hyc'⟩
  have hshift : ∀ {x : AvgPhase n} (k : Fin n → ℤ), x ∈ D →
      x + KAM.ODE.angleShift (-k) ∈ avgOmega h f R ε t ∧
        avgFlow h f R ε t (x + KAM.ODE.angleShift (-k)) =
          avgFlow h f R ε t x + KAM.ODE.angleShift (-k) := fun {x} k hx =>
    ⟨(avgFlow_translate d ε (-k) x).1.2 (hDO hx), (avgFlow_translate d ε (-k) x).2 (hDO hx)⟩
  obtain ⟨hax, hΦx⟩ := hshift k hx
  obtain ⟨hax', hΦx'⟩ := hshift k' hx'
  have e1 : avgFlow h f R ε t (x + KAM.ODE.angleShift (-k)) = y := by
    rw [hΦx, hxy, angleShift_neg]; simp
  have e2 : avgFlow h f R ε t (x' + KAM.ODE.angleShift (-k')) = y := by
    rw [hΦx', hxy', angleShift_neg]; simp
  have heq := hinjΩ hax hax' (e1.trans e2.symm)
  have h1' := congrArg Prod.fst heq
  have hxc := hcell hx
  have hxc' := hcell hx'
  refine hne (funext fun i => ?_)
  have hi := congrFun h1' i
  simp only [KAM.ODE.angleShift, Prod.fst_add, Pi.neg_apply, Int.cast_neg, Pi.add_apply] at hi
  have a := hxc i
  have b := hxc' i
  have c : ((k i - k' i : ℤ) : ℝ) < 1 := by push_cast; linarith [a.1, a.2, b.1, b.2, hi]
  have c' : (-1 : ℝ) < ((k i - k' i : ℤ) : ℝ) := by push_cast; linarith [a.1, a.2, b.1, b.2, hi]
  have c1 : k i - k' i < 1 := by exact_mod_cast c
  have c2 : -1 < k i - k' i := by exact_mod_cast c'
  omega

end Transport

end KAM.Nekhoroshev

end
