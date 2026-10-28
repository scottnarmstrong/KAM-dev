/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.EnvelopeIntegrals
public import KAM.Nekhoroshev.Averaging.Exit
public import KAM.Nekhoroshev.Averaging.Pointwise
public import KAM.Nekhoroshev.Averaging.Transport

/-!
# Part N12: the stopped maximum majorant (`bpN:p12:s-trans#psi`, `bpN:p12:stopped`)

`avgStopped` is the pointwise majorant of the displacement up to the stopping time: the corrector
term plus `ε` times the envelope integrated along the orbit, with the integrand killed outside the
stay set. `stopped` fixes `M₂` and `A₁` before `ε` and before any size-one perturbation `f₁`, and
proves that on a compact `K` the killed integrand is Borel (`st-meas`), the majorant bounds the
displacement at every time up to the stop (`st-pt`, from `pointwise` and `exit`) and its integral
over `K` is at most `A₁ √ε` (`st-int`): `K` is covered by finitely many half-open angle cells, on
each cell `transport` (also at time zero) converts the integral along the flow into the integral
of the envelope over `avgG n R`, and the time interval has length `1/ε`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

namespace KAM.Nekhoroshev

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

def avgStopped (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ)
    (R s M₂ ε : ℝ) (x : AvgPhase n) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * ε) * avgWenv h s (Real.sqrt ε) x.2 + ENNReal.ofReal ε *
    ∫⁻ t in Icc 0 (1 / ε), (avgStay h f R ε).indicator
      (fun p => avgPhiEnv h s M₂ ε (Real.sqrt ε) (avgFlow h f R ε p.1 p.2).2) (t, x)

section Measurability

variable (d : AveragingData n R s h f) (ε : ℝ)
include d

/-- The stay set is Borel: it is relatively open in `[0,∞) × {y | y.2 ∈ B(0,R/2)}`. -/
theorem measurableSet_avgStay : MeasurableSet (avgStay h f R ε) := by
  have hO := isOpen_avgStay_relative d ε
  set c : Set.Ici (0 : ℝ) × {y : AvgPhase n // y.2 ∈ actionBall n (R / 2)} →
      ℝ × AvgPhase n := fun p => (((p.1 : ℝ), (p.2 : AvgPhase n)) : ℝ × AvgPhase n) with hcdef
  have hc : Topology.IsInducing c :=
    Topology.IsInducing.subtypeVal.prodMap Topology.IsInducing.subtypeVal
  obtain ⟨U, hU, hUe⟩ := hc.isOpen_iff.1 hO
  have hS : MeasurableSet ((Ici (0 : ℝ)) ×ˢ {y : AvgPhase n | y.2 ∈ actionBall n (R / 2)}) :=
    measurableSet_Ici.prod (measurableSet_ball.preimage measurable_snd)
  suffices hEq : avgStay h f R ε =
      U ∩ ((Ici (0 : ℝ)) ×ˢ {y : AvgPhase n | y.2 ∈ actionBall n (R / 2)}) from
    hEq ▸ hU.measurableSet.inter hS
  ext p
  constructor
  · intro hp
    have h1 : (⟨⟨p.1, hp.1⟩, ⟨p.2, hp.2.1⟩⟩ : Set.Ici (0 : ℝ) ×
        {y : AvgPhase n // y.2 ∈ actionBall n (R / 2)}) ∈ c ⁻¹' U := by
      rw [hUe]; exact hp
    exact ⟨h1, hp.1, hp.2.1⟩
  · rintro ⟨hpU, h0, h2⟩
    have : (⟨⟨p.1, h0⟩, ⟨p.2, h2⟩⟩ : Set.Ici (0 : ℝ) ×
        {y : AvgPhase n // y.2 ∈ actionBall n (R / 2)}) ∈ c ⁻¹' U := hpU
    rw [hUe] at this
    exact this

/-- `st-meas`: the killed integrand is jointly Borel. -/
theorem measurable_killed {Φ : (Fin n → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    Measurable ((avgStay h f R ε).indicator
      (fun p => Φ (avgFlow h f R ε p.1 p.2).2)) := by
  have hΩ : MeasurableSet (avgFlowDomain h f R ε) := (isOpen_avgFlowDomain d ε).measurableSet
  have hsub : avgStay h f R ε ⊆ avgFlowDomain h f R ε := fun p hp => hp.2.2.1
  refine measurable_of_restrict_of_restrict_compl hΩ ?_ ?_
  · have hcont : Continuous fun q : avgFlowDomain h f R ε => avgFlow h f R ε q.1.1 q.1.2 :=
      (continuousOn_avgFlow d ε).comp_continuous continuous_subtype_val fun q => q.2
    have hG : Measurable fun q : avgFlowDomain h f R ε =>
        Φ (avgFlow h f R ε q.1.1 q.1.2).2 := hΦ.comp (continuous_snd.comp hcont).measurable
    refine Measurable.ite ?_ hG measurable_const
    exact measurable_subtype_coe (measurableSet_avgStay d ε)
  · have : (avgFlowDomain h f R ε)ᶜ.domRestrict ((avgStay h f R ε).indicator
        (fun p => Φ (avgFlow h f R ε p.1 p.2).2)) = fun _ => (0 : ℝ≥0∞) := by
      funext q
      exact indicator_of_notMem (fun hq => q.2 (hsub hq)) _
    rw [this]; exact measurable_const

end Measurability

section Basic

variable (d : AveragingData n R s h f) (ε : ℝ)
include d

theorem avgFlow_zero {x : AvgPhase n} (hx : x ∈ avgDomain n R) : avgFlow h f R ε 0 x = x :=
  (avgMaximal_spec d ε hx).init

theorem zero_mem_avgOmega {x : AvgPhase n} (hx : x ∈ avgDomain n R) : x ∈ avgOmega h f R ε 0 :=
  ⟨hx, KAM.ODE.zero_mem_eIoo (avgMaximal_spec d ε hx)⟩

theorem mem_avgDomain_of_half {x : AvgPhase n} (hx : x.2 ∈ actionBall n (R / 2)) :
    x ∈ avgDomain n R :=
  ⟨mem_univ _, ball_subset_ball (by linarith [d.hR]) hx⟩

/-- Before the exit time the pair `(v, x)` is still in the stay set. -/
theorem mem_avgStay_of_lt_tau {x : AvgPhase n} (hx : x.2 ∈ actionBall n (R / 2)) {v : ℝ}
    (hv : 0 ≤ v) (hlt : (v : EReal) < avgTau h f R ε x) : (v, x) ∈ avgStay h f R ε := by
  obtain ⟨b, ⟨t', ht', rfl⟩, hb⟩ := lt_sSup_iff.1 hlt
  have hvt : v ≤ t' := EReal.coe_le_coe_iff.1 hb.le
  obtain ⟨-, -, hΩ, hdisp⟩ := ht'
  have hmx := avgMaximal_spec d ε hΩ.1
  have hJ := (KAM.ODE.ordConnected_eIoo (avgTm h f R ε x) (avgTp h f R ε x)).out
    (KAM.ODE.zero_mem_eIoo hmx) hΩ.2 ⟨hv, hvt⟩
  exact ⟨hv, hx, ⟨hΩ.1, hJ⟩, fun u hu => hdisp u ⟨hu.1, hu.2.trans hvt⟩⟩

/-- Along the stay set the flow stays in `avgG n R`, hence in the action ball. -/
theorem flow_mem_of_stay (hε : 0 < ε) {t : ℝ} {x : AvgPhase n} (hp : (t, x) ∈ avgStay h f R ε) :
    (avgFlow h f R ε t x).2 ∈ avgG n R := by
  have ht : (t : EReal) ≤ avgTau h f R ε x := le_sSup ⟨t, hp, rfl⟩
  exact ((exit d hε hp.2.1).2.2.2.2.1 t hp.1 ht).2

theorem avgG_subset_actionBall : avgG n R ⊆ actionBall n R := fun _ hI =>
  closedBall_subset_ball (by linarith [d.hR]) hI

end Basic

section Integrals

variable (d : AveragingData n R s h f) (ε : ℝ)
include d

/-- One time slice of the killed integrand over a piece of one initial cell. -/
theorem lintegral_slice_le (hε : 0 < ε) {Φ : (Fin n → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ)
    (ell : Fin n → ℤ) {D : Set (AvgPhase n)} (hD : MeasurableSet D)
    (hcell : D ⊆ avgCell ell) {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ x in D, (avgStay h f R ε).indicator
      (fun p => Φ (avgFlow h f R ε p.1 p.2).2) (t, x)) ≤ ∫⁻ I in avgG n R, Φ I := by
  have hSt : MeasurableSet {x : AvgPhase n | (t, x) ∈ avgStay h f R ε} :=
    measurable_prodMk_left (measurableSet_avgStay d ε)
  have h1 : (fun x : AvgPhase n => (avgStay h f R ε).indicator
      (fun p => Φ (avgFlow h f R ε p.1 p.2).2) (t, x)) =
      {x : AvgPhase n | (t, x) ∈ avgStay h f R ε}.indicator
        (fun x => Φ (avgFlow h f R ε t x).2) := by
    funext x; simp [Set.indicator]
  rw [h1, lintegral_indicator hSt, Measure.restrict_restrict hSt]
  refine transport d ε ht Φ hΦ ell (hSt.inter hD) (fun x hx => hx.1.2.2.1)
    (fun x hx => hcell hx.2) fun x hx => flow_mem_of_stay d ε hε hx.1

/-- The time integral of the killed integrand over a piece of a cell: `1/ε` times the envelope. -/
theorem lintegral_time_le (hε : 0 < ε) {Φ : (Fin n → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ)
    (ell : Fin n → ℤ) {D : Set (AvgPhase n)} (hD : MeasurableSet D)
    (hcell : D ⊆ avgCell ell) :
    (∫⁻ x in D, ∫⁻ t in Icc 0 (1 / ε), (avgStay h f R ε).indicator
      (fun p => Φ (avgFlow h f R ε p.1 p.2).2) (t, x)) ≤
      ENNReal.ofReal (1 / ε) * ∫⁻ I in avgG n R, Φ I := by
  have hF := measurable_killed d ε hΦ
  have hF' : Measurable (fun q : AvgPhase n × ℝ => (avgStay h f R ε).indicator
      (fun p => Φ (avgFlow h f R ε p.1 p.2).2) (q.2, q.1)) := hF.comp measurable_swap
  rw [lintegral_lintegral_swap hF'.aemeasurable]
  calc (∫⁻ t in Icc 0 (1 / ε), ∫⁻ x in D, (avgStay h f R ε).indicator
        (fun p => Φ (avgFlow h f R ε p.1 p.2).2) (t, x))
      ≤ ∫⁻ t in Icc 0 (1 / ε), ∫⁻ I in avgG n R, Φ I :=
        setLIntegral_mono' measurableSet_Icc fun t ht =>
          lintegral_slice_le d ε hε hΦ ell hD hcell ht.1
    _ = ENNReal.ofReal (1 / ε) * ∫⁻ I in avgG n R, Φ I := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm]

end Integrals

section Cover

/-- A compact set meets only finitely many half-open angle cells. -/
theorem exists_cell_cover {K : Set (AvgPhase n)} (hK : IsCompact K) :
    ∃ S : Finset (Fin n → ℤ), K ⊆ ⋃ ell ∈ S, avgCell ell := by
  obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
  refine ⟨Fintype.piFinset fun _ => Finset.Icc (-⌈B⌉) ⌈B⌉, fun x hx => ?_⟩
  simp only [mem_iUnion, Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨fun i => ⌊x.1 i⌋, fun i => ?_, mem_avgCell_floor x⟩
  have hxi : |x.1 i| ≤ B := by
    have h1 : ‖x.1 i‖ ≤ ‖x.1‖ := norm_le_pi_norm x.1 i
    have h2 : ‖x.1‖ ≤ ‖x‖ := norm_fst_le x
    rw [← Real.norm_eq_abs]; linarith [hB x hx]
  have hc : (B : ℝ) ≤ ⌈B⌉ := Int.le_ceil B
  show -⌈B⌉ ≤ ⌊x.1 i⌋ ∧ ⌊x.1 i⌋ ≤ ⌈B⌉
  constructor
  · have := (abs_le.1 hxi).1
    have h3 := Int.sub_one_lt_floor (x.1 i)
    have h4 : ((-⌈B⌉ - 1 : ℤ) : ℝ) < ⌊x.1 i⌋ := by push_cast; linarith
    have := Int.cast_lt.1 h4
    omega
  · rw [← Int.cast_le (R := ℝ)]
    have := (abs_le.1 hxi).2
    have h3 := Int.floor_le (x.1 i)
    linarith

end Cover

section Extended

/-- `avgStopped` with the envelopes extended by zero off the action ball, so that it is Borel. -/
def avgStoppedExt (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ)
    (R s M₂ ε : ℝ) (x : AvgPhase n) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * ε) * (actionBall n R).indicator (avgWenv h s (Real.sqrt ε)) x.2 +
    ENNReal.ofReal ε * ∫⁻ t in Icc 0 (1 / ε), (avgStay h f R ε).indicator
      (fun p => (actionBall n R).indicator (avgPhiEnv h s M₂ ε (Real.sqrt ε))
        (avgFlow h f R ε p.1 p.2).2) (t, x)

variable (d : AveragingData n R s h f) (ε M₂ : ℝ)
include d

theorem avgStopped_eq_ext (hε : 0 < ε) {x : AvgPhase n} (hx : x.2 ∈ actionBall n (R / 2)) :
    avgStopped h f R s M₂ ε x = avgStoppedExt h f R s M₂ ε x := by
  have hxR : x.2 ∈ actionBall n R := ball_subset_ball (by linarith [d.hR]) hx
  unfold avgStopped avgStoppedExt
  rw [indicator_of_mem hxR]
  congr 2
  refine lintegral_congr fun t => ?_
  by_cases hp : (t, x) ∈ avgStay h f R ε
  · rw [indicator_of_mem hp, indicator_of_mem hp,
      indicator_of_mem (avgG_subset_actionBall d (flow_mem_of_stay d ε hε hp))]
  · rw [indicator_of_notMem hp, indicator_of_notMem hp]

theorem measurable_avgStoppedExt (hε : 0 < ε) (hM0 : 0 ≤ M₂) :
    Measurable (avgStoppedExt h f R s M₂ ε) := by
  obtain ⟨mW, -, -, -, mΦ, -⟩ := envelope_regular d (Real.sqrt_pos.2 hε) hM0
  have hF := measurable_killed d ε (mΦ ε)
  refine (measurable_const.mul (mW.comp measurable_snd)).add (measurable_const.mul ?_)
  exact (hF.comp measurable_swap).lintegral_prod_right' (ν := volume.restrict (Icc 0 (1 / ε)))

/-- The integral of the extended majorant over a piece of one angle cell. -/
theorem lintegral_cell_le (hε : 0 < ε) (hM0 : 0 ≤ M₂) (ell : Fin n → ℤ)
    {D : Set (AvgPhase n)} (hD : MeasurableSet D) (hcell : D ⊆ avgCell ell)
    (hDI : ∀ x ∈ D, x.2 ∈ actionBall n (R / 2)) :
    (∫⁻ x in D, avgStoppedExt h f R s M₂ ε x) ≤
      ENNReal.ofReal (2 * ε) * (∫⁻ I in avgG n R, avgWenv h s (Real.sqrt ε) I) +
      ENNReal.ofReal ε * (ENNReal.ofReal (1 / ε) *
        ∫⁻ I in avgG n R, avgPhiEnv h s M₂ ε (Real.sqrt ε) I) := by
  obtain ⟨mW, -, -, -, mΦ, -⟩ := envelope_regular d (Real.sqrt_pos.2 hε) hM0
  have hG : MeasurableSet (avgG n R) := measurableSet_closedBall
  unfold avgStoppedExt
  have hm1 : Measurable fun x : AvgPhase n => ENNReal.ofReal (2 * ε) *
      (actionBall n R).indicator (avgWenv h s (Real.sqrt ε)) x.2 :=
    measurable_const.mul (mW.comp measurable_snd)
  rw [lintegral_add_left hm1]
  refine add_le_add ?_ ?_
  · have htr := transport d ε le_rfl (fun I => ENNReal.ofReal (2 * ε) *
      (actionBall n R).indicator (avgWenv h s (Real.sqrt ε)) I) (measurable_const.mul mW)
      ell hD (fun x hx => zero_mem_avgOmega d ε (mem_avgDomain_of_half d (hDI x hx))) hcell
      (fun x hx => by
        rw [avgFlow_zero d ε (mem_avgDomain_of_half d (hDI x hx))]
        exact ball_subset_closedBall (ball_subset_ball (by linarith [d.hR]) (hDI x hx)))
    calc (∫⁻ x in D, ENNReal.ofReal (2 * ε) *
          (actionBall n R).indicator (avgWenv h s (Real.sqrt ε)) x.2)
        = ∫⁻ x in D, ENNReal.ofReal (2 * ε) *
          (actionBall n R).indicator (avgWenv h s (Real.sqrt ε)) (avgFlow h f R ε 0 x).2 :=
          setLIntegral_congr_fun hD fun x hx => by
            rw [avgFlow_zero d ε (mem_avgDomain_of_half d (hDI x hx))]
      _ ≤ _ := htr
      _ = ENNReal.ofReal (2 * ε) * ∫⁻ I in avgG n R,
          (actionBall n R).indicator (avgWenv h s (Real.sqrt ε)) I := lintegral_const_mul _ mW
      _ = _ := by
          congr 1
          exact setLIntegral_congr_fun hG fun I hI =>
            indicator_of_mem (avgG_subset_actionBall d hI) _
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul_right ?_ _
    have e : ∫⁻ I in avgG n R, avgPhiEnv h s M₂ ε (Real.sqrt ε) I =
        ∫⁻ I in avgG n R, (actionBall n R).indicator
          (avgPhiEnv h s M₂ ε (Real.sqrt ε)) I :=
      setLIntegral_congr_fun hG fun I hI => (indicator_of_mem (avgG_subset_actionBall d hI) _).symm
    rw [e]
    exact lintegral_time_le d ε hε (mΦ ε) ell hD hcell

end Extended

section Main

/-- Uniform witness chosen before epsilon, eta, or any supplied solution family. -/
theorem stopped (d : AveragingData n R s h f) (K : Set (AvgPhase n))
    (hK : IsCompact K) (hKI : ∀ x ∈ K, x.2 ∈ actionBall n (R / 2)) :
    ∃ M₂ A₁ : ℝ, 0 ≤ M₂ ∧ 0 < A₁ ∧
      (∀ I ∈ closedBall (0 : Fin n → ℝ) R, ∀ i, ∑ j, |avgM h I i j| ≤ M₂) ∧
      ∀ f₁ : AvgComplexPhase n → ℂ, IsAnalyticPerturbation R s 1 f₁ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        Measurable (K.indicator (avgStopped h f₁ R s M₂ ε)) ∧
        (∫⁻ x in K, avgStopped h f₁ R s M₂ ε x) ≤ ENNReal.ofReal (A₁ * Real.sqrt ε) ∧
        ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 / ε → (t : EReal) ≤ avgTau h f₁ R ε x →
          ∀ u ∈ Icc 0 t, ENNReal.ofReal ‖(avgFlow h f₁ R ε u x).2 - x.2‖ ≤
            avgStopped h f₁ R s M₂ ε x := by
  obtain ⟨C₁, Ω₀, M₂, -, -, hM0, -, hM, -, henv⟩ := envelopes d
  obtain ⟨S, hS⟩ := exists_cell_cover hK
  set cW := max 0 (avgCW n s C₁ Ω₀) with hcW
  set cΦ := max 0 (avgCPhi n s C₁ Ω₀ M₂) with hcΦ
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  refine ⟨M₂, max 1 (S.card * (cΦ + 4 * cW)), hM0, lt_of_lt_of_le one_pos (le_max_left _ _),
    hM, fun f₁ hf₁ ε hε hε1 => ?_⟩
  have d₁ : AveragingData n R s h f₁ := { d with hf := hf₁ }
  have hsq : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hsqpos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  refine ⟨?_, ?_, ?_⟩
  · have hEq : K.indicator (avgStopped h f₁ R s M₂ ε) =
        K.indicator (avgStoppedExt h f₁ R s M₂ ε) := by
      funext x
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx, indicator_of_mem hx, avgStopped_eq_ext d₁ ε M₂ hε (hKI x hx)]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx]
    rw [hEq]
    exact (measurable_avgStoppedExt d₁ ε M₂ hε hM0).indicator hKm
  · obtain ⟨hW, hP⟩ := henv ε hε hε1
    have hcongr : (∫⁻ x in K, avgStopped h f₁ R s M₂ ε x) =
        ∫⁻ x in K, avgStoppedExt h f₁ R s M₂ ε x :=
      setLIntegral_congr_fun hKm fun x hx => avgStopped_eq_ext d₁ ε M₂ hε (hKI x hx)
    have hKeq : K = ⋃ ell ∈ S, (K ∩ avgCell ell) := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, exists_prop]
      refine ⟨fun hx => ?_, fun ⟨_, _, hx, _⟩ => hx⟩
      have := hS hx
      simp only [mem_iUnion, exists_prop] at this
      obtain ⟨ell, hell, hxc⟩ := this
      exact ⟨ell, hell, hx, hxc⟩
    have hmeas : ∀ ell ∈ S, MeasurableSet (K ∩ avgCell ell) := fun ell _ =>
      hKm.inter (measurableSet_avgCell ell)
    have hdisj : (S : Set (Fin n → ℤ)).PairwiseDisjoint fun ell => K ∩ avgCell ell :=
      fun a _ b _ hne => (disjoint_avgCell hne).mono inter_subset_right inter_subset_right
    have hcell : ∀ ell ∈ S, (∫⁻ x in K ∩ avgCell ell, avgStoppedExt h f₁ R s M₂ ε x) ≤
        ENNReal.ofReal ((cΦ + 4 * cW) * Real.sqrt ε) := by
      intro ell hell
      refine (lintegral_cell_le d₁ ε M₂ hε hM0 ell (hmeas ell hell) inter_subset_right
        fun x hx => hKI x hx.1).trans ?_
      have e : ENNReal.ofReal ε * (ENNReal.ofReal (1 / ε) *
          ∫⁻ I in avgG n R, avgPhiEnv h s M₂ ε (Real.sqrt ε) I) =
          ∫⁻ I in avgG n R, avgPhiEnv h s M₂ ε (Real.sqrt ε) I := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hε.le, mul_one_div_cancel hε.ne']
        simp
      rw [e]
      calc _ ≤ ENNReal.ofReal (4 * cW * Real.sqrt ε) + ENNReal.ofReal (cΦ * Real.sqrt ε) := by
            refine add_le_add (hW.trans (ENNReal.ofReal_le_ofReal ?_))
              (hP.trans (ENNReal.ofReal_le_ofReal ?_))
            · gcongr; exact le_max_right _ _
            · gcongr; exact le_max_right _ _
        _ = _ := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    calc (∫⁻ x in K, avgStopped h f₁ R s M₂ ε x)
        = ∑ ell ∈ S, ∫⁻ x in K ∩ avgCell ell, avgStoppedExt h f₁ R s M₂ ε x := by
          rw [hcongr]
          conv_lhs => rw [hKeq]
          exact lintegral_biUnion_finset hdisj hmeas _
      _ ≤ ∑ _ell ∈ S, ENNReal.ofReal ((cΦ + 4 * cW) * Real.sqrt ε) := Finset.sum_le_sum hcell
      _ = ENNReal.ofReal (S.card * ((cΦ + 4 * cW) * Real.sqrt ε)) := by
          rw [Finset.sum_const, nsmul_eq_mul,
            ENNReal.ofReal_mul (p := (S.card : ℝ)) (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hsq
  · intro x hxK t ht0 ht1 htau u hu
    have hx := hKI x hxK
    obtain ⟨-, -, -, -, hexit, -⟩ := exit d₁ hε hx
    have hpt := pointwise d₁ hε hε1 hsqpos (Real.sqrt_le_one.2 hε1) hM hx ht0
      (hexit t ht0 htau).1
      (fun v hv => (hexit v hv.1 ((EReal.coe_le_coe_iff.2 hv.2).trans htau)).2) u hu
    refine hpt.trans ?_
    unfold avgStopped
    refine add_le_add le_rfl (mul_le_mul_right ?_ _)
    calc (∫⁻ v in Icc 0 t, avgPhiEnv h s M₂ ε (Real.sqrt ε) (avgFlow h f₁ R ε v x).2)
        = ∫⁻ v in Ico 0 t, avgPhiEnv h s M₂ ε (Real.sqrt ε) (avgFlow h f₁ R ε v x).2 :=
          setLIntegral_congr Ico_ae_eq_Icc.symm
      _ = ∫⁻ v in Ico 0 t, (avgStay h f₁ R ε).indicator
            (fun p => avgPhiEnv h s M₂ ε (Real.sqrt ε) (avgFlow h f₁ R ε p.1 p.2).2) (v, x) :=
          setLIntegral_congr_fun measurableSet_Ico fun v hv => by
            rw [indicator_of_mem (mem_avgStay_of_lt_tau d₁ ε hx hv.1
              (lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hv.2) htau))]
      _ ≤ _ := lintegral_mono_set
          (show Ico 0 t ⊆ Icc 0 (1 / ε) from fun v hv => ⟨hv.1, hv.2.le.trans ht1⟩)

end Main

end KAM.Nekhoroshev

end
