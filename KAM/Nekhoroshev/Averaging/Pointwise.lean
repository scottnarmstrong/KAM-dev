/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.PointwiseModes

/-!
# Part N12: the pointwise stopped estimate (`bpN:p12:pointwise`)

For `x` with `|I₀| < R/2` and an orbit segment `[0, t]` inside `G`, the corrector identity gives
`|I(u) - I₀| ≤ ε(|Λ(u)| + |Λ(0)|) + ε² |∫Q| + ε |∫r|`, and

* `pw-lambda`: `ofReal |Λ(u)| ≤ Ŵ(I₀) + (2ε/s) ∫ B̂(I(v)) dv`, by the modewise variation
  `PointwiseModes.mode_bound` summed over `k` (Tonelli, `lintegral_tsum`);
* `pw-q`: `ofReal |Q| ≤ (2/s)(Ŵ₁ + B̂)` and `ofReal |r| ≤ R̂` from `wreg`;
* `pw-sum`: add up (`le_lintegral_add` for the final regrouping into `Φ̂`).

All envelope integrals are `ℝ≥0∞`-valued lower/upper integrals, so no measurability of the
envelopes along the orbit is used except termwise for `lintegral_tsum`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal ContDiff

namespace KAM.Nekhoroshev

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

section Lintegral

theorem ofReal_norm_tsum_le {ι E : Type*} [NormedAddCommGroup E] (g : ι → E) :
    ENNReal.ofReal ‖∑' i, g i‖ ≤ ∑' i, ENNReal.ofReal ‖g i‖ := by
  by_cases htop : ∑' i, ENNReal.ofReal ‖g i‖ = ⊤
  · rw [htop]; exact le_top
  · have hsum : Summable (fun i => ‖g i‖₊) := by
      refine ENNReal.tsum_coe_ne_top_iff_summable.1 ?_
      simpa [ofReal_norm, ← ENNReal.ofReal_coe_nnreal] using htop
    have hs : Summable (fun i => ‖g i‖) := by simpa using NNReal.summable_coe.2 hsum
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
    exact ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hs)

theorem ofReal_norm_integral_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ → E} {t u : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (hG : ContinuousOn G (Icc 0 t)) :
    ENNReal.ofReal ‖∫ v in (0 : ℝ)..u, G v‖ ≤ ∫⁻ v in Icc 0 t, ENNReal.ofReal ‖G v‖ := by
  have hint : IntervalIntegrable G volume 0 u := by
    refine (hG.mono ?_).intervalIntegrable
    rw [uIcc_of_le hu]; exact Icc_subset_Icc_right hut
  calc ENNReal.ofReal ‖∫ v in (0 : ℝ)..u, G v‖
      ≤ ENNReal.ofReal (∫ v in (0 : ℝ)..u, ‖G v‖) :=
        ENNReal.ofReal_le_ofReal (intervalIntegral.norm_integral_le_integral_norm hu)
    _ = ENNReal.ofReal (∫ v in Ioc 0 u, ‖G v‖) := by rw [intervalIntegral.integral_of_le hu]
    _ = ∫⁻ v in Ioc 0 u, ENNReal.ofReal ‖G v‖ :=
        ofReal_integral_eq_lintegral_ofReal hint.1.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ ∫⁻ v in Icc 0 t, ENNReal.ofReal ‖G v‖ :=
        lintegral_mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right hut))

end Lintegral

section Main

variable (d : AveragingData n R s h f)
include d

/-- `pw-lambda`: the corrector along the orbit, from the modewise variation. -/
theorem lambda_orbit_le {κ M₂ ε : ℝ} (hκ : 0 < κ)
    (hM : ∀ I ∈ closedBall (0 : Fin n → ℝ) R, ∀ i, ∑ j, |avgM h I i j| ≤ M₂)
    (hε : 0 ≤ ε) {x : AvgPhase n} (hx : x ∈ avgDomain n R) {t : ℝ}
    (htp : (t : EReal) < avgTp h f R ε x)
    (htraj : ∀ u ∈ Icc 0 t, (avgFlow h f R ε u x).2 ∈ avgG n R) {u : ℝ} (hu : u ∈ Icc 0 t) :
    ENNReal.ofReal ‖avgW h f κ (avgFlow h f R ε u x)‖ ≤ avgWenv h s κ x.2 +
      ENNReal.ofReal (ε * (2 / s)) *
        ∫⁻ v in Icc 0 t, avgBenv h s M₂ κ (avgFlow h f R ε v x).2 := by
  have hM0 : 0 ≤ M₂ := (Finset.sum_nonneg fun j _ => abs_nonneg _).trans
    (hM 0 (by simpa using d.hR.le) ⟨0, d.hn⟩)
  have hc0 : 0 ≤ ε * (2 / s) := by have := d.hs; positivity
  have h1 : ENNReal.ofReal ‖avgW h f κ (avgFlow h f R ε u x)‖ ≤
      ∑' k : Fin n → ℤ, ENNReal.ofReal ‖avgU h f κ k (avgFlow h f R ε u x).2‖ := by
    unfold avgW
    rw [norm_neg]
    refine (ofReal_norm_tsum_le _).trans (le_of_eq (tsum_congr fun k => ?_))
    rw [norm_smul, KAM.norm_character]; simp
  have hmeas : ∀ k : Fin n → ℤ, AEMeasurable (fun v => ENNReal.ofReal
      (avgBterm h s M₂ κ k (avgFlow h f R ε v x).2)) (volume.restrict (Icc 0 t)) := fun k =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuousOn_bterm_orbit d hκ hx htp k).aemeasurable measurableSet_Icc)
  have h2 : ∀ k : Fin n → ℤ, ENNReal.ofReal ‖avgU h f κ k (avgFlow h f R ε u x).2‖ ≤
      ENNReal.ofReal ‖avgU h f κ k x.2‖ + ENNReal.ofReal (ε * (2 / s)) *
        ∫⁻ v in Icc 0 t, ENNReal.ofReal (avgBterm h s M₂ κ k (avgFlow h f R ε v x).2) := by
    intro k
    have hb := mode_bound d hκ hM hε hx htp htraj k u hu
    have hnn : ∀ v, 0 ≤ avgBterm h s M₂ κ k (avgFlow h f R ε v x).2 := fun v =>
      avgBterm_nonneg' d hM0 k _
    have hI0 : 0 ≤ ∫ v in (0 : ℝ)..u, avgBterm h s M₂ κ k (avgFlow h f R ε v x).2 :=
      intervalIntegral.integral_nonneg hu.1 fun v _ => hnn v
    have hint := ofReal_norm_integral_le (G := fun v => avgBterm h s M₂ κ k (avgFlow h f R ε v x).2)
      hu.1 hu.2 (continuousOn_bterm_orbit d hκ hx htp k)
    have hint' : ENNReal.ofReal (∫ v in (0 : ℝ)..u,
        avgBterm h s M₂ κ k (avgFlow h f R ε v x).2) ≤
        ∫⁻ v in Icc 0 t, ENNReal.ofReal (avgBterm h s M₂ κ k (avgFlow h f R ε v x).2) := by
      refine (ENNReal.ofReal_le_ofReal (Real.le_norm_self _)).trans (hint.trans ?_)
      exact le_of_eq (lintegral_congr fun v => by rw [Real.norm_of_nonneg (hnn v)])
    calc ENNReal.ofReal ‖avgU h f κ k (avgFlow h f R ε u x).2‖
        ≤ ENNReal.ofReal (‖avgU h f κ k x.2‖ + ε * (2 / s) *
          ∫ v in (0 : ℝ)..u, avgBterm h s M₂ κ k (avgFlow h f R ε v x).2) :=
          ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal ‖avgU h f κ k x.2‖ + ENNReal.ofReal (ε * (2 / s)) *
          ENNReal.ofReal (∫ v in (0 : ℝ)..u,
            avgBterm h s M₂ κ k (avgFlow h f R ε v x).2) := by
          rw [ENNReal.ofReal_add (norm_nonneg _) (mul_nonneg hc0 hI0), ENNReal.ofReal_mul hc0]
      _ ≤ _ := by gcongr
  have hI : x.2 ∈ actionBall n R := hx.2
  calc ENNReal.ofReal ‖avgW h f κ (avgFlow h f R ε u x)‖
      ≤ ∑' k : Fin n → ℤ, (ENNReal.ofReal ‖avgU h f κ k x.2‖ + ENNReal.ofReal (ε * (2 / s)) *
        ∫⁻ v in Icc 0 t, ENNReal.ofReal (avgBterm h s M₂ κ k (avgFlow h f R ε v x).2)) :=
        h1.trans (ENNReal.tsum_le_tsum h2)
    _ = (∑' k : Fin n → ℤ, ENNReal.ofReal ‖avgU h f κ k x.2‖) + ENNReal.ofReal (ε * (2 / s)) *
        ∫⁻ v in Icc 0 t, ∑' k : Fin n → ℤ,
          ENNReal.ofReal (avgBterm h s M₂ κ k (avgFlow h f R ε v x).2) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, lintegral_tsum hmeas]
    _ ≤ _ := by
        gcongr
        all_goals first
          | exact le_rfl
          | exact ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (norm_avgU_le' d κ k hI)

theorem pointwise {ε κ M₂ t : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hM : ∀ I ∈ closedBall (0 : Fin n → ℝ) R, ∀ i, ∑ j, |avgM h I i j| ≤ M₂)
    {x : AvgPhase n} (hx : x.2 ∈ actionBall n (R / 2)) (ht : 0 ≤ t)
    (htp : (t : EReal) < avgTp h f R ε x)
    (htraj : ∀ u ∈ Icc 0 t, (avgFlow h f R ε u x).2 ∈ avgG n R) :
    ∀ u ∈ Icc 0 t, ENNReal.ofReal ‖(avgFlow h f R ε u x).2 - x.2‖ ≤
      ENNReal.ofReal (2 * ε) * avgWenv h s κ x.2 +
      ENNReal.ofReal ε * ∫⁻ v in Icc 0 t, avgPhiEnv h s M₂ ε κ (avgFlow h f R ε v x).2 := by
  have _ := hε1
  have _ := hκ1
  have _ := ht
  have hε0 : 0 ≤ ε := hε.le
  have hxD : x ∈ avgDomain n R := ⟨mem_univ _, ball_subset_ball (by linarith [d.hR]) hx⟩
  have hW := wreg d hκ hM
  have hcont := orbit_continuousOn d ε hxD htp
  have hmem := orbit_mapsTo d ε hxD htp
  have hs2 : 0 ≤ 2 / s := by have := d.hs; positivity
  have hbd := fun v (hv : v ∈ Icc 0 t) => (hW.2.2 _ (hmem hv)).2 (htraj v hv)
  -- `pw-q`: the pointwise envelope bounds on `Q` and `r`
  have hQ : ∀ v ∈ Icc 0 t, ENNReal.ofReal ‖avgCorrectionQ h f κ (avgFlow h f R ε v x)‖ ≤
      ENNReal.ofReal (2 / s) * (avgW1env h s κ (avgFlow h f R ε v x).2 +
        avgBenv h s M₂ κ (avgFlow h f R ε v x).2) := by
    intro v hv
    obtain ⟨-, -, -, hW1, hB, -⟩ := hbd v hv
    have hfb := fbounds d _ (hmem hv)
    calc ENNReal.ofReal ‖avgCorrectionQ h f κ (avgFlow h f R ε v x)‖
        ≤ ENNReal.ofReal (‖fderiv ℝ (avgW h f κ) (avgFlow h f R ε v x)
            (avgB f (avgFlow h f R ε v x), 0)‖ + ‖fderiv ℝ (avgW h f κ) (avgFlow h f R ε v x)
              (0, avgA f (avgFlow h f R ε v x))‖) :=
          ENNReal.ofReal_le_ofReal (norm_add_le _ _)
      _ = ENNReal.ofReal ‖fderiv ℝ (avgW h f κ) (avgFlow h f R ε v x)
            (avgB f (avgFlow h f R ε v x), 0)‖ + ENNReal.ofReal ‖fderiv ℝ (avgW h f κ)
              (avgFlow h f R ε v x) (0, avgA f (avgFlow h f R ε v x))‖ :=
          ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
      _ ≤ avgW1env h s κ (avgFlow h f R ε v x).2 * ENNReal.ofReal ‖avgB f (avgFlow h f R ε v x)‖ +
          avgBenv h s M₂ κ (avgFlow h f R ε v x).2 *
            ENNReal.ofReal ‖avgA f (avgFlow h f R ε v x)‖ := add_le_add (hW1 _) (hB _)
      _ ≤ avgW1env h s κ (avgFlow h f R ε v x).2 * ENNReal.ofReal (2 / s) +
          avgBenv h s M₂ κ (avgFlow h f R ε v x).2 * ENNReal.ofReal (2 / s) := by
          gcongr
          · exact hfb.2.1
          · exact hfb.1
      _ = _ := by ring
  have hRv : ∀ v ∈ Icc 0 t, ENNReal.ofReal ‖avgResidual h f κ (avgFlow h f R ε v x)‖ ≤
      avgRenv h s κ (avgFlow h f R ε v x).2 := fun v hv => (hbd v hv).2.1
  -- the corrector along the orbit
  have hΛu := fun u (hu : u ∈ Icc 0 t) => lambda_orbit_le d hκ hM hε0 hxD htp htraj hu
  have hΛ0 : ENNReal.ofReal ‖avgW h f κ x‖ ≤ avgWenv h s κ x.2 := by
    have := (hW.2.2 x hxD).2 (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith [d.hR])) hx)
    exact this.1
  -- the regrouping of the integrals into `Φ̂`
  set c : ℝ := ε * (2 / s) with hc
  have hc0 : 0 ≤ c := by positivity
  set A2 : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal c * (avgW1env h s κ (avgFlow h f R ε v x).2 +
    avgBenv h s M₂ κ (avgFlow h f R ε v x).2) with hA2
  have hΦ : ENNReal.ofReal c * (∫⁻ v in Icc 0 t, avgBenv h s M₂ κ (avgFlow h f R ε v x).2) +
      (∫⁻ v in Icc 0 t, A2 v) + ∫⁻ v in Icc 0 t, avgRenv h s κ (avgFlow h f R ε v x).2 ≤
      ∫⁻ v in Icc 0 t, avgPhiEnv h s M₂ ε κ (avgFlow h f R ε v x).2 := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (add_le_add (le_lintegral_add _ _) le_rfl).trans ((le_lintegral_add _ _).trans
      (le_of_eq (lintegral_congr fun v => ?_)))
    have e1 : ENNReal.ofReal (ε * 4 / s) = ENNReal.ofReal c + ENNReal.ofReal c := by
      rw [← ENNReal.ofReal_add hc0 hc0, hc]; congr 1; ring
    have e2 : ENNReal.ofReal (ε * 2 / s) = ENNReal.ofReal c := by rw [hc]; congr 1; ring
    simp only [hA2, avgPhiEnv, e1, e2]
    ring
  intro u hu
  have hup : (u : EReal) < avgTp h f R ε x :=
    lt_of_le_of_lt (EReal.coe_le_coe_iff.2 hu.2) htp
  have hid := identity d hε hκ hxD hu.1 hup
  have hIc : ContinuousOn (fun v => avgCorrectionQ h f κ (avgFlow h f R ε v x)) (Icc 0 t) :=
    (continuousOn_avgCorrectionQ d hκ).comp hcont hmem
  have hIr : ContinuousOn (fun v => avgResidual h f κ (avgFlow h f R ε v x)) (Icc 0 t) :=
    (continuousOn_avgResidual d hκ).comp hcont hmem
  set Iq := ∫ v in (0 : ℝ)..u, avgCorrectionQ h f κ (avgFlow h f R ε v x) with hIqdef
  set Ir := ∫ v in (0 : ℝ)..u, avgResidual h f κ (avgFlow h f R ε v x) with hIrdef
  have hQi : ENNReal.ofReal ‖Iq‖ ≤ ∫⁻ v in Icc 0 t,
      ENNReal.ofReal ‖avgCorrectionQ h f κ (avgFlow h f R ε v x)‖ :=
    ofReal_norm_integral_le hu.1 hu.2 hIc
  have hRi : ENNReal.ofReal ‖Ir‖ ≤ ∫⁻ v in Icc 0 t,
      ENNReal.ofReal ‖avgResidual h f κ (avgFlow h f R ε v x)‖ :=
    ofReal_norm_integral_le hu.1 hu.2 hIr
  have hQi' : ENNReal.ofReal ε * ENNReal.ofReal ‖Iq‖ ≤ ∫⁻ v in Icc 0 t, A2 v := by
    calc ENNReal.ofReal ε * ENNReal.ofReal ‖Iq‖
        ≤ ENNReal.ofReal ε * ∫⁻ v in Icc 0 t,
            ENNReal.ofReal ‖avgCorrectionQ h f κ (avgFlow h f R ε v x)‖ := by gcongr
      _ = ∫⁻ v in Icc 0 t, ENNReal.ofReal ε *
            ENNReal.ofReal ‖avgCorrectionQ h f κ (avgFlow h f R ε v x)‖ :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ v in Icc 0 t, A2 v := by
          refine setLIntegral_mono' measurableSet_Icc fun v hv => ?_
          calc ENNReal.ofReal ε * ENNReal.ofReal ‖avgCorrectionQ h f κ (avgFlow h f R ε v x)‖
              ≤ ENNReal.ofReal ε * (ENNReal.ofReal (2 / s) * (avgW1env h s κ
                (avgFlow h f R ε v x).2 + avgBenv h s M₂ κ (avgFlow h f R ε v x).2)) := by
                gcongr; exact hQ v hv
            _ = A2 v := by
                simp only [hA2, hc]
                rw [ENNReal.ofReal_mul hε0, mul_assoc]
  have hRi' : ∫⁻ v in Icc 0 t, ENNReal.ofReal ‖avgResidual h f κ (avgFlow h f R ε v x)‖ ≤
      ∫⁻ v in Icc 0 t, avgRenv h s κ (avgFlow h f R ε v x).2 :=
    setLIntegral_mono' measurableSet_Icc hRv
  -- `pw-sum`: add up
  have hΔ : ‖(avgFlow h f R ε u x).2 - x.2‖ ≤ ε * (‖avgW h f κ (avgFlow h f R ε u x)‖ +
      ‖avgW h f κ x‖) + ε * (ε * ‖Iq‖) + ε * ‖Ir‖ := by
    rw [← KAM.norm_realInclusion, hid]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [norm_smul, Real.norm_of_nonneg hε0]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hε0
    · rw [norm_smul, norm_pow, Real.norm_of_nonneg hε0]; exact le_of_eq (by ring)
    · rw [norm_smul, Real.norm_of_nonneg hε0]
  have hT : ENNReal.ofReal (ε * (‖avgW h f κ (avgFlow h f R ε u x)‖ + ‖avgW h f κ x‖) +
      ε * (ε * ‖Iq‖) + ε * ‖Ir‖) = ENNReal.ofReal ε * (ENNReal.ofReal
        ‖avgW h f κ (avgFlow h f R ε u x)‖ + ENNReal.ofReal ‖avgW h f κ x‖) +
        ENNReal.ofReal ε * (ENNReal.ofReal ε * ENNReal.ofReal ‖Iq‖) +
        ENNReal.ofReal ε * ENNReal.ofReal ‖Ir‖ := by
    have p1 : 0 ≤ ε * (‖avgW h f κ (avgFlow h f R ε u x)‖ + ‖avgW h f κ x‖) := by positivity
    have p2 : 0 ≤ ε * (ε * ‖Iq‖) := by positivity
    have p3 : 0 ≤ ε * ‖Ir‖ := by positivity
    rw [ENNReal.ofReal_add (add_nonneg p1 p2) p3, ENNReal.ofReal_add p1 p2,
      ENNReal.ofReal_mul hε0, ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
      ENNReal.ofReal_mul hε0, ENNReal.ofReal_mul hε0, ENNReal.ofReal_mul hε0]
  have h2ε : ENNReal.ofReal (2 * ε) = ENNReal.ofReal ε + ENNReal.ofReal ε := by
    rw [two_mul, ENNReal.ofReal_add hε0 hε0]
  calc ENNReal.ofReal ‖(avgFlow h f R ε u x).2 - x.2‖
      ≤ ENNReal.ofReal (ε * (‖avgW h f κ (avgFlow h f R ε u x)‖ + ‖avgW h f κ x‖) +
          ε * (ε * ‖Iq‖) + ε * ‖Ir‖) := ENNReal.ofReal_le_ofReal hΔ
    _ = _ := hT
    _ ≤ ENNReal.ofReal ε * ((avgWenv h s κ x.2 + ENNReal.ofReal c *
          ∫⁻ v in Icc 0 t, avgBenv h s M₂ κ (avgFlow h f R ε v x).2) + avgWenv h s κ x.2) +
        ENNReal.ofReal ε * (∫⁻ v in Icc 0 t, A2 v) +
        ENNReal.ofReal ε * ∫⁻ v in Icc 0 t, avgRenv h s κ (avgFlow h f R ε v x).2 := by
        gcongr
        all_goals first
          | exact hΛu u hu
          | exact hRi.trans hRi'
    _ = ENNReal.ofReal (2 * ε) * avgWenv h s κ x.2 + ENNReal.ofReal ε *
        (ENNReal.ofReal c * (∫⁻ v in Icc 0 t, avgBenv h s M₂ κ (avgFlow h f R ε v x).2) +
          (∫⁻ v in Icc 0 t, A2 v) + ∫⁻ v in Icc 0 t,
            avgRenv h s κ (avgFlow h f R ε v x).2) := by
        rw [h2ε]; ring
    _ ≤ _ := by gcongr

end Main

end KAM.Nekhoroshev

end
