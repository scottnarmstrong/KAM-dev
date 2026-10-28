/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.Flow
public import KAM.Nekhoroshev.Averaging.CompactMaximum
public import KAM.ODE.Exit
public import KAM.ODE.Continuation

/-!
# Part N12: first exit from the displacement tube (`bpN:p12:exit`)

`avgStay` is the set of times and initial points whose orbit has stayed within action displacement
`< R/8` of its start; `avgTau` is its supremum in `EReal` (infinite exit times are allowed).
`exit` proves the dichotomy: the exit time is positive, at most the maximal endpoint, either
infinite (and then so is the endpoint) or finite, strictly before the endpoint, with displacement
exactly `R/8`; up to the exit time the action stays in the compactum `avgG n R`; and the stay set
is open relative to nonnegative times and initial actions in `B(0, R/2)`.
-/

@[expose] public noncomputable section

open Set Metric Filter
open KAM.ODE (IsSolutionIn IsMaximalSolution eIoo)

namespace KAM.Nekhoroshev

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

/-- Stay-set uses real time; the exit time uses EReal, never real sSup at infinity. -/
def avgStay (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ)
    (R ε : ℝ) : Set (ℝ × AvgPhase n) :=
  {p | 0 ≤ p.1 ∧ p.2.2 ∈ actionBall n (R / 2) ∧ p.2 ∈ avgOmega h f R ε p.1 ∧
    ∀ u ∈ Icc 0 p.1, ‖(avgFlow h f R ε u p.2).2 - p.2.2‖ < R / 8}
def avgTau (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ)
    (R ε : ℝ) (x : AvgPhase n) : EReal :=
  sSup ((fun t : ℝ => (t : EReal)) '' {t | (t, x) ∈ avgStay h f R ε})

section Aux

/-- A supremum of the image of a set of reals with real supremum `a` is `a`. -/
private theorem sSup_coe_image {B : Set ℝ} (hne : B.Nonempty) (hbdd : BddAbove B) :
    sSup ((fun t : ℝ => (t : EReal)) '' B) = ((sSup B : ℝ) : EReal) := by
  apply le_antisymm
  · exact sSup_le (by rintro _ ⟨b, hb, rfl⟩; exact EReal.coe_le_coe_iff.2 (le_csSup hbdd hb))
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have : sSup B ≤ r := csSup_le hne fun b hb => EReal.coe_le_coe_iff.1
      ((le_sSup (mem_image_of_mem _ hb)).trans hr1.le)
    exact absurd (EReal.coe_lt_coe_iff.1 hr2) (not_lt.2 this)

/-- A set of reals unbounded above has top supremum in `EReal`. -/
private theorem sSup_coe_image_top {B : Set ℝ} (hB : ∀ t : ℝ, 0 ≤ t → t ∈ B) :
    sSup ((fun t : ℝ => (t : EReal)) '' B) = ⊤ := by
  by_contra hne
  obtain ⟨r, hr1, -⟩ := EReal.lt_iff_exists_real_btwn.1 (lt_top_iff_ne_top.2 hne)
  have := le_sSup (s := (fun t : ℝ => (t : EReal)) '' B) ⟨max r 0, hB _ (le_max_right _ _), rfl⟩
  have h2 : ((max r 0 : ℝ) : EReal) < r := lt_of_le_of_lt this hr1
  exact absurd (EReal.coe_lt_coe_iff.1 h2) (not_lt.2 (le_max_left _ _))

end Aux

section Openness

variable (d : AveragingData n R s h f) (ε : ℝ)
include d

/-- The stay set is open relative to nonnegative times and initial actions in `B(0, R/2)`. -/
theorem isOpen_avgStay_relative :
    IsOpen {p : Set.Ici (0 : ℝ) × {y : AvgPhase n // y.2 ∈ actionBall n (R / 2)} |
      ((p.1 : ℝ), (p.2 : AvgPhase n)) ∈ avgStay h f R ε} := by
  set D := avgFlowDomain h f R ε with hD
  have hDo : IsOpen D := isOpen_avgFlowDomain d ε
  have hg : ContinuousOn (fun q : ℝ × AvgPhase n => ‖(avgFlow h f R ε q.1 q.2).2 - q.2.2‖) D :=
    (((continuousOn_avgFlow d ε).snd).sub (continuous_snd.snd.continuousOn)).norm
  set A := D ∩ (fun q : ℝ × AvgPhase n => ‖(avgFlow h f R ε q.1 q.2).2 - q.2.2‖) ⁻¹'
    Iio (R / 8) with hA
  have hAo : IsOpen A := hg.isOpen_inter_preimage hDo isOpen_Iio
  rw [isOpen_iff_mem_nhds]
  rintro ⟨⟨t₀, ht₀⟩, ⟨y₀, hy₀⟩⟩ hp
  obtain ⟨-, -, hΩ, hlt⟩ := hp
  have hsub : Icc 0 t₀ ×ˢ ({y₀} : Set (AvgPhase n)) ⊆ A := by
    rintro ⟨u, y⟩ ⟨hu, hy⟩
    rw [mem_singleton_iff] at hy
    subst hy
    refine ⟨?_, hlt u hu⟩
    have hmx := avgMaximal_spec d ε hΩ.1
    have hJ := (KAM.ODE.ordConnected_eIoo (avgTm h f R ε y) (avgTp h f R ε y)).out
      (KAM.ODE.zero_mem_eIoo hmx) hΩ.2 hu
    exact ⟨hΩ.1, hJ⟩
  obtain ⟨U, V, hU, hV, hUs, hVy, hUV⟩ := generalized_tube_lemma isCompact_Icc
    isCompact_singleton hAo hsub
  obtain ⟨η, hη, hηU⟩ : ∃ η > 0, Ioo (t₀ - η) (t₀ + η) ⊆ U := by
    obtain ⟨ε', hε', hb⟩ := Metric.isOpen_iff.1 hU t₀ (hUs ⟨ht₀, le_rfl⟩)
    exact ⟨ε', hε', fun t ht => hb (by rw [Real.ball_eq_Ioo]; exact ht)⟩
  have hnhds : (Iio (t₀ + η) ×ˢ V : Set (ℝ × AvgPhase n)) ∈ nhds (t₀, y₀) :=
    prod_mem_nhds (Iio_mem_nhds (by linarith)) (hV.mem_nhds (hVy rfl))
  have hcont : Continuous (fun p : Set.Ici (0 : ℝ) ×
      {y : AvgPhase n // y.2 ∈ actionBall n (R / 2)} =>
      (((p.1 : ℝ), (p.2 : AvgPhase n)) : ℝ × AvgPhase n)) := by fun_prop
  refine Filter.mem_of_superset (hcont.continuousAt.preimage_mem_nhds hnhds) ?_
  rintro ⟨⟨t, ht⟩, ⟨y, hy⟩⟩ ⟨hlt', hyV⟩
  have hlt'' : t < t₀ + η := hlt'
  have hsubU : Icc 0 t ⊆ U := by
    intro u hu
    by_cases hu0 : u ≤ t₀
    · exact hUs ⟨hu.1, hu0⟩
    · exact hηU ⟨by linarith [not_le.1 hu0], by linarith [hu.2]⟩
  have hmem : ∀ u ∈ Icc 0 t, (u, y) ∈ A := fun u hu => hUV ⟨hsubU hu, hyV⟩
  exact ⟨ht, hy, (hmem t ⟨ht, le_rfl⟩).1, fun u hu => (hmem u hu).2⟩

end Openness

section Dichotomy

variable (d : AveragingData n R s h f) {ε : ℝ}
include d

private theorem avgField_periodic (k : Fin n → ℤ) :
    ∀ x ∈ (univ : Set (Fin n → ℝ)) ×ˢ actionBall n R,
      KAM.hamiltonianVectorField (avgH h f ε) (x + KAM.ODE.angleShift k) =
        KAM.hamiltonianVectorField (avgH h f ε) x :=
  fun _ hx => avgField_shift d ε k hx

/-- `bpN:p12:exit`. -/
theorem exit (hε : 0 < ε)
    {x : AvgPhase n} (hx : x.2 ∈ actionBall n (R / 2)) :
    0 < avgTau h f R ε x ∧ avgTau h f R ε x ≤ avgTp h f R ε x ∧
    (avgTau h f R ε x = ⊤ → avgTp h f R ε x = ⊤) ∧
    (∀ t : ℝ, (t : EReal) = avgTau h f R ε x →
      (t : EReal) < avgTp h f R ε x ∧ ‖(avgFlow h f R ε t x).2 - x.2‖ = R / 8) ∧
    (∀ t : ℝ, 0 ≤ t → (t : EReal) ≤ avgTau h f R ε x →
      (t : EReal) < avgTp h f R ε x ∧ (avgFlow h f R ε t x).2 ∈ avgG n R) ∧
    IsOpen {p : Set.Ici (0 : ℝ) × {y : AvgPhase n // y.2 ∈ actionBall n (R / 2)} |
      ((p.1 : ℝ), (p.2 : AvgPhase n)) ∈ avgStay h f R ε} := by
  have _ := hε
  have hR := d.hR
  have hxD : x ∈ avgDomain n R := ⟨mem_univ _, by
    refine ball_subset_ball (by linarith) hx⟩
  have hmax := avgMaximal_spec d ε hxD
  set Tm := avgTm h f R ε x
  set Tp := avgTp h f R ε x
  set z : ℝ → AvgPhase n := fun t => avgFlow h f R ε t x with hz
  set J := eIoo Tm Tp with hJ
  have hJo : J.OrdConnected := KAM.ODE.ordConnected_eIoo _ _
  have h0J : (0 : ℝ) ∈ J := KAM.ODE.zero_mem_eIoo hmax
  have hzc : ContinuousOn z J := fun t ht =>
    (hmax.isSolution t ht).2.continuousAt.continuousWithinAt
  set V : Set (AvgPhase n) := {y | ‖y.2 - x.2‖ < R / 8} with hV
  have hVo : IsOpen V := isOpen_lt (by fun_prop) continuous_const
  have hz0V : z 0 ∈ V := by
    show ‖(z 0).2 - x.2‖ < R / 8
    have h0 : z 0 = x := hmax.init
    rw [h0, sub_self, norm_zero]; linarith
  -- the stay set at `x` is the set `B`
  set B : Set ℝ := {t | t ∈ J ∧ 0 ≤ t ∧ z '' Icc 0 t ⊆ V} with hB
  have hstay : {t | (t, x) ∈ avgStay h f R ε} = B := by
    ext t
    constructor
    · rintro ⟨ht0, -, ⟨-, htJ⟩, hlt⟩
      exact ⟨htJ, ht0, by rintro _ ⟨u, hu, rfl⟩; exact hlt u hu⟩
    · rintro ⟨htJ, ht0, hsub⟩
      exact ⟨ht0, hx, ⟨hxD, htJ⟩, fun u hu => hsub ⟨u, hu, rfl⟩⟩
  have htau : avgTau h f R ε x = sSup ((fun t : ℝ => (t : EReal)) '' B) := by
    rw [avgTau, hstay]
  have hgV : ∀ y : AvgPhase n, ‖y.2 - x.2‖ ≤ R / 8 → y.2 ∈ avgG n R := by
    intro y hy
    have : ‖y.2‖ ≤ ‖x.2‖ + R / 8 := by
      calc ‖y.2‖ = ‖(y.2 - x.2) + x.2‖ := by rw [sub_add_cancel]
        _ ≤ ‖y.2 - x.2‖ + ‖x.2‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    have hxn : ‖x.2‖ < R / 2 := by simpa [actionBall] using hx
    rw [avgG, mem_closedBall_zero_iff]
    linarith
  have hIcc : ∀ t ∈ J, 0 ≤ t → Icc 0 t ⊆ J := fun t ht ht0 => hJo.out h0J ht
  rcases KAM.ODE.gen_exit hJo h0J hzc hVo hz0V with
      ⟨-, hno⟩ | ⟨-, ts, hleast, hpos, htsJ, hbelow, hfr, hsup⟩
  · -- no exit: the orbit stays in `V`, hence `Tp = ⊤`
    have hBall : ∀ t ∈ J, 0 ≤ t → t ∈ B := fun t ht ht0 =>
      ⟨ht, ht0, by rintro _ ⟨u, hu, rfl⟩; exact hno u (hIcc t ht ht0 hu) hu.1⟩
    have hTp : Tp = ⊤ := by
      have hKc : IsCompact (closedBall (0 : Fin n → ℝ) (5 * R / 8)) := isCompact_closedBall _ _
      have hKU : closedBall (0 : Fin n → ℝ) (5 * R / 8) ⊆ actionBall n R :=
        closedBall_subset_ball (by linarith)
      have hxn : ‖x.2‖ < R / 2 := by simpa [actionBall] using hx
      refine (KAM.ODE.gen_continuation_periodic (isOpen_ball) (avgField_contDiffOn d ε)
        (avgField_periodic d) hmax hKc hKU).1 ⟨0, le_rfl, by simpa using hmax.pos_lt, ?_⟩
      intro t ht0 htT
      have htJ : t ∈ J := ⟨lt_of_lt_of_le hmax.neg_lt (by exact_mod_cast ht0), htT⟩
      have hv := hno t htJ ht0
      rw [mem_closedBall_zero_iff]
      have h1 : ‖(z t).2 - x.2‖ < R / 8 := hv
      calc ‖(z t).2‖ = ‖((z t).2 - x.2) + x.2‖ := by rw [sub_add_cancel]
        _ ≤ ‖(z t).2 - x.2‖ + ‖x.2‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    have hTpt : ∀ t : ℝ, (t : EReal) < Tp := fun t => by simp [hTp]
    have hJall : ∀ t : ℝ, 0 ≤ t → t ∈ J := fun t ht0 =>
      ⟨lt_of_lt_of_le hmax.neg_lt (by exact_mod_cast ht0), hTpt t⟩
    have hτ : avgTau h f R ε x = ⊤ := by
      rw [htau]; exact sSup_coe_image_top fun t ht0 => hBall t (hJall t ht0) ht0
    rw [hτ]
    refine ⟨by simp, by rw [hTp], fun _ => hTp, fun t ht => absurd ht (by simp),
      fun t ht0 _ => ⟨hTpt t, hgV _ (hno t (hJall t ht0) ht0).le⟩,
      isOpen_avgStay_relative d ε⟩
  · -- exit at the finite time `ts`
    have hBne : B.Nonempty := ⟨0, h0J, le_rfl, by
      rintro _ ⟨u, hu, rfl⟩
      rw [le_antisymm hu.2 hu.1]; exact hz0V⟩
    have hBle : ∀ t ∈ B, t < ts := by
      intro t ht
      by_contra hge
      have := ht.2.2 ⟨ts, ⟨hleast.1.2.1, not_lt.1 hge⟩, rfl⟩
      exact hleast.1.2.2 this
    have hτ : avgTau h f R ε x = (ts : EReal) := by
      rw [htau, sSup_coe_image hBne ⟨ts, fun t ht => (hBle t ht).le⟩, ← hsup]
    have hts : ‖(z ts).2 - x.2‖ = R / 8 := by
      have hcl : z ts ∈ closure V := hfr.1
      have hclosed : IsClosed {y : AvgPhase n | ‖y.2 - x.2‖ ≤ R / 8} :=
        isClosed_le (by fun_prop) continuous_const
      have h1 : ‖(z ts).2 - x.2‖ ≤ R / 8 :=
        closure_minimal (fun y hy => (hy : ‖y.2 - x.2‖ < R / 8).le) hclosed hcl
      have h2 : ¬ ‖(z ts).2 - x.2‖ < R / 8 := hleast.1.2.2
      exact le_antisymm h1 (not_lt.1 h2)
    have htsTp : (ts : EReal) < Tp := htsJ.2
    rw [hτ]
    refine ⟨by exact_mod_cast hpos, htsTp.le, fun h => absurd h (by simp),
      fun t ht => ?_, fun t ht0 htt => ?_, ?_⟩
    · have : t = ts := EReal.coe_eq_coe_iff.1 ht
      subst this
      exact ⟨htsTp, hts⟩
    · have htle : t ≤ ts := EReal.coe_le_coe_iff.1 htt
      have htJ : t ∈ J := hJo.out h0J htsJ ⟨ht0, htle⟩
      refine ⟨htJ.2, hgV _ ?_⟩
      rcases htle.lt_or_eq with hl | he
      · exact (hbelow t ⟨ht0, hl⟩).le
      · subst he; exact hts.le
    · exact isOpen_avgStay_relative d ε

end Dichotomy

end KAM.Nekhoroshev

end
