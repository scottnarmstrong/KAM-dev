/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.GoodSet

/-!
# Part N12: the mean estimate (`stepN:p12:me-*`)

`mean_family`: an arbitrary supplied family `Φ` of genuine solutions on `[0, 1/ε]` through the
points of `K` coincides there with the maximal flow `avgFlow` (uniqueness,
`IsMaximalSolution.maximal`), so `averagingError ε Φ` is continuous on `K` (compact maximum),
hence integrable, although `Φ` has no regularity premise.

`averaging_mean_core`: the constant is `13 * A₁` with `A₁` from `bad`. The error is pointwise
`≤ 13 * avgStopped`: on the good set at level `R/8` by `bad`, and elsewhere because the error is
`≤ 3R/2 = 12 * (R/8) ≤ 12 * avgStopped`. The exceptional set is the Markov set.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

namespace KAM.Nekhoroshev

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

private theorem averagingError_eq_flow {ε : ℝ} {Φ : AvgPhase n → ℝ → AvgPhase n} {x : AvgPhase n}
    (hΦ : ∀ t ∈ Icc 0 (1 / ε), Φ x t = avgFlow h f R ε t x) :
    averagingError ε Φ x =
      sSup ((fun t => ‖(avgFlow h f R ε t x).2 - x.2‖) '' Icc 0 (1 / ε)) := by
  unfold averagingError
  congr 1
  ext y
  simp only [mem_image]
  constructor <;> rintro ⟨t, ht, rfl⟩ <;> exact ⟨t, ht, by rw [hΦ t ht]⟩

/-- Uniqueness supplies regularity on K although Phi has no regularity premise. -/
theorem mean_family (d : AveragingData n R s h f) (K : Set (AvgPhase n))
    (hK : IsCompact K) (hKI : ∀ x ∈ K, x.2 ∈ actionBall n (R / 2))
    {ε : ℝ} (hε : 0 < ε) (Φ : AvgPhase n → ℝ → AvgPhase n)
    (hΦ : ∀ x ∈ K, Φ x 0 = x ∧ IsSolutionOn (avgH h f ε)
      (actionBall n R) (Icc 0 (1 / ε)) (Φ x)) :
    (∀ x ∈ K, x ∈ avgOmega h f R ε (1 / ε) ∧
      ∀ t ∈ Icc 0 (1 / ε), Φ x t = avgFlow h f R ε t x) ∧
    ContinuousOn (averagingError ε Φ) K ∧ IntegrableOn (averagingError ε Φ) K ∧
    ∀ x ∈ K, 0 ≤ averagingError ε Φ x ∧ averagingError ε Φ x ≤ 3 * R / 2 ∧
      ∀ t ∈ Icc 0 (1 / ε), ‖(Φ x t).2 - x.2‖ ≤ averagingError ε Φ x := by
  have hT : (0 : ℝ) ≤ 1 / ε := by positivity
  have hR := d.hR
  have hxD : ∀ x ∈ K, x ∈ avgDomain n R := fun x hx =>
    ⟨mem_univ _, ball_subset_ball (by linarith) (hKI x hx)⟩
  have huniq : ∀ x ∈ K, x ∈ avgOmega h f R ε (1 / ε) ∧
      ∀ t ∈ Icc 0 (1 / ε), Φ x t = avgFlow h f R ε t x := by
    intro x hx
    obtain ⟨h0, hsol⟩ := hΦ x hx
    have hsolIn : KAM.ODE.IsSolutionIn (KAM.hamiltonianVectorField (avgH h f ε))
        (avgDomain n R) (Icc 0 (1 / ε)) (Φ x) := by
      intro t ht
      obtain ⟨h1, -, h3⟩ := hsol t ht
      exact ⟨⟨mem_univ _, h1⟩, h3⟩
    obtain ⟨hsub, heq⟩ := (avgMaximal_spec d ε (hxD x hx)).maximal (Icc 0 (1 / ε)) (Φ x)
      ordConnected_Icc ⟨le_rfl, hT⟩ h0 hsolIn
    exact ⟨⟨hxD x hx, hsub ⟨hT, le_rfl⟩⟩, fun t ht => heq ht⟩
  have hb : ∀ x ∈ K, ∀ t ∈ Icc 0 (1 / ε), ‖(Φ x t).2 - x.2‖ ≤ 3 * R / 2 := by
    intro x hx t ht
    have h1 : ‖(Φ x t).2‖ < R := mem_ball_zero_iff.1 ((hΦ x hx).2 t ht).1
    have h2 : ‖x.2‖ < R / 2 := mem_ball_zero_iff.1 (hKI x hx)
    calc _ ≤ ‖(Φ x t).2‖ + ‖x.2‖ := norm_sub_le _ _
      _ ≤ 3 * R / 2 := by linarith
  have hbdd : ∀ x ∈ K, BddAbove ((fun t => ‖(Φ x t).2 - x.2‖) '' Icc 0 (1 / ε)) := fun x hx =>
    ⟨3 * R / 2, by rintro _ ⟨t, ht, rfl⟩; exact hb x hx t ht⟩
  have hcont : ContinuousOn (averagingError ε Φ) K :=
    ((continuousOn_sSup_disp d (1 / ε) hT).mono fun x hx => (huniq x hx).1).congr
      fun x hx => averagingError_eq_flow (huniq x hx).2
  refine ⟨huniq, hcont, hcont.integrableOn_compact hK, fun x hx => ⟨?_, ?_, ?_⟩⟩
  · exact Real.sSup_nonneg (by rintro _ ⟨t, -, rfl⟩; exact norm_nonneg _)
  · exact csSup_le ⟨_, 0, ⟨le_rfl, hT⟩, rfl⟩ (by rintro _ ⟨t, ht, rfl⟩; exact hb x hx t ht)
  · intro t ht
    exact le_csSup (hbdd x hx) ⟨t, ht, rfl⟩

/-- Implementation assembly before provider namespace export. -/
theorem averaging_mean_core (d : AveragingData n R s h f) (K : Set (AvgPhase n))
    (hK : IsCompact K) (hKI : ∀ x ∈ K, x.2 ∈ actionBall n (R / 2)) :
    ∃ A : ℝ, 0 < A ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ Φ : AvgPhase n → ℝ → AvgPhase n,
      (∀ x ∈ K, Φ x 0 = x ∧ IsSolutionOn (avgH h f ε)
        (actionBall n R) (Icc 0 (1 / ε)) (Φ x)) →
      IntegrableOn (averagingError ε Φ) K ∧
      (∫⁻ x in K, ENNReal.ofReal (averagingError ε Φ x)) ≤ ENNReal.ofReal (A * Real.sqrt ε) ∧
      ∀ κ : ℝ, 0 < κ → ∃ E : Set (AvgPhase n), MeasurableSet E ∧ E ⊆ K ∧
        volume E ≤ ENNReal.ofReal κ ∧ ∀ x ∈ K \ E, ∀ t ∈ Icc 0 (1 / ε),
          ‖(Φ x t).2 - x.2‖ ≤ A * Real.sqrt ε / κ := by
  obtain ⟨M₂, A₁, -, hA, hbad⟩ := bad d K hK hKI
  refine ⟨13 * A₁, by positivity, fun ε hε hε1 Φ hΦ => ?_⟩
  obtain ⟨hint, hlow, hgood⟩ := hbad ε hε hε1
  obtain ⟨hflow, hcont, hI, hbd⟩ := mean_family d K hK hKI hε Φ hΦ
  have hR := d.hR
  have hT : (0 : ℝ) ≤ 1 / ε := by positivity
  have hptw : ∀ x ∈ K, ENNReal.ofReal (averagingError ε Φ x) ≤
      13 * avgStopped h f R s M₂ ε x := by
    intro x hx
    have hΨ : avgStopped h f R s M₂ ε x ≤ 13 * avgStopped h f R s M₂ ε x := by
      calc _ = 1 * avgStopped h f R s M₂ ε x := (one_mul _).symm
        _ ≤ _ := by gcongr; norm_num
    by_cases hg : x ∈ avgGood h f R ε (R / 8) K
    · obtain ⟨u, hu, hsup⟩ := exists_max_disp d hT (hflow x hx).1
      rw [averagingError_eq_flow (hflow x hx).2, hsup]
      exact (hgood x hg u hu).trans hΨ
    · have h1 := hlow (R / 8) (by positivity) le_rfl x ⟨hx, hg⟩
      calc ENNReal.ofReal (averagingError ε Φ x) ≤ ENNReal.ofReal (12 * (R / 8)) :=
            ENNReal.ofReal_le_ofReal (by linarith [(hbd x hx).2.1])
        _ = 12 * ENNReal.ofReal (R / 8) := by
            rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
        _ ≤ 12 * avgStopped h f R s M₂ ε x := by gcongr
        _ ≤ 13 * avgStopped h f R s M₂ ε x := by gcongr; norm_num
  have hmean : (∫⁻ x in K, ENNReal.ofReal (averagingError ε Φ x)) ≤
      ENNReal.ofReal (13 * A₁ * Real.sqrt ε) := by
    calc _ ≤ ∫⁻ x in K, 13 * avgStopped h f R s M₂ ε x :=
          setLIntegral_mono' hK.measurableSet hptw
      _ = 13 * ∫⁻ x in K, avgStopped h f R s M₂ ε x := lintegral_const_mul' _ _ (by simp)
      _ ≤ 13 * ENNReal.ofReal (A₁ * Real.sqrt ε) := by gcongr
      _ = _ := by
          rw [mul_assoc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 13), ENNReal.ofReal_ofNat]
  refine ⟨hI, hmean, fun κ hκ => ?_⟩
  set A : ℝ := 13 * A₁ with hAdef
  have hAs : 0 < A * Real.sqrt ε := by positivity
  set lam : ℝ := A * Real.sqrt ε / κ with hlam
  have hlam0 : 0 < lam := by positivity
  set E : Set (AvgPhase n) := {x ∈ K | lam < averagingError ε Φ x} with hE
  have hEK : E ⊆ K := fun x hx => hx.1
  have hEm : MeasurableSet E := by
    have hc : Continuous (K.domRestrict (averagingError ε Φ)) :=
      continuousOn_iff_continuous_domRestrict.1 hcont
    have ho : IsOpen {y : K | lam < averagingError ε Φ y} :=
      isOpen_lt continuous_const hc
    have := MeasurableSet.subtype_image hK.measurableSet ho.measurableSet
    convert this using 1
    ext x
    constructor
    · rintro ⟨hxK, hl⟩
      exact ⟨⟨x, hxK⟩, hl, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
  refine ⟨E, hEm, hEK, ?_, fun x hx t ht => ?_⟩
  · have h1 : ENNReal.ofReal lam * volume E ≤ ENNReal.ofReal (A * Real.sqrt ε) := by
      calc ENNReal.ofReal lam * volume E = ∫⁻ _ in E, ENNReal.ofReal lam := by
            rw [setLIntegral_const]
        _ ≤ ∫⁻ x in E, ENNReal.ofReal (averagingError ε Φ x) :=
            setLIntegral_mono' hEm fun x hx => ENNReal.ofReal_le_ofReal hx.2.le
        _ ≤ ∫⁻ x in K, ENNReal.ofReal (averagingError ε Φ x) :=
            lintegral_mono_set hEK
        _ ≤ _ := hmean
    have h2 : ENNReal.ofReal (A * Real.sqrt ε) = ENNReal.ofReal lam * ENNReal.ofReal κ := by
      rw [← ENNReal.ofReal_mul hlam0.le, hlam, div_mul_cancel₀ _ hκ.ne']
    rw [h2] at h1
    exact (ENNReal.mul_le_mul_iff_right (by simpa using hlam0) ENNReal.ofReal_ne_top).1 h1
  · have hxK : x ∈ K := hx.1
    have : ¬ lam < averagingError ε Φ x := fun hlt => hx.2 ⟨hxK, hlt⟩
    exact ((hbd x hxK).2.2 t ht).trans (not_lt.1 this)

end KAM.Nekhoroshev

end
