/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.Flow
public import KAM.Canonical.FlowRegularIntegral

/-!
# Picard iterates of the canonical flow

Helper module of `KAM.Canonical.FlowRegular` (blueprint-N Part 5, node `bpN:p5:flow`
(b)). For a small field `F` (`SmallField W Ω F ε`) the Picard iterates

  `y₀(t, z) = z`,   `y_{k+1}(t, z) = z + ∫₀ᵗ F(y_k(τ, z)) dτ`

are defined on `[-1, 1] × Ω^{1/2}` (the displacement bound `ν(y_k(t, z) - z) ≤ |t| ε ≤ 1/2` keeps
them in `Ω`), are holomorphic in `z`, and have jointly continuous `z`-derivative
(`KAM.Canonical.picard_regular`). The estimate used for their convergence is the elementary bound
`KAM.Canonical.norm_intervalIntegral_le_pow`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped Interval

namespace KAM.Canonical

section Picard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-! ### An integral estimate -/

/-- `‖∫₀ᵗ f‖ ≤ C |t|^{m+1} / (m+1)` if `‖f τ‖ ≤ C |τ|^m`. -/
theorem norm_intervalIntegral_le_pow {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℝ → G} {C : ℝ} {m : ℕ} {t : ℝ} (h : ∀ τ ∈ Ι (0 : ℝ) t, ‖f τ‖ ≤ C * |τ| ^ m) :
    ‖∫ τ in (0 : ℝ)..t, f τ‖ ≤ C * |t| ^ (m + 1) / (m + 1) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun τ : ℝ => C * |τ| ^ m) volume a b :=
    fun a b => (continuous_const.mul (continuous_abs.pow m)).intervalIntegrable a b
  rcases le_total 0 t with ht | ht
  · have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) ht
      (Filter.Eventually.of_forall fun τ hτ => h τ (by rwa [uIoc_of_le ht])) (hint 0 t)
    have hcongr : ∫ τ in (0 : ℝ)..t, C * |τ| ^ m = ∫ τ in (0 : ℝ)..t, C * τ ^ m :=
      intervalIntegral.integral_congr fun τ hτ => by
        rw [uIcc_of_le ht] at hτ
        simp [abs_of_nonneg hτ.1]
    rw [hcongr, intervalIntegral.integral_const_mul, integral_pow] at hle
    calc _ ≤ C * ((t ^ (m + 1) - 0 ^ (m + 1)) / (m + 1)) := hle
      _ = C * |t| ^ (m + 1) / (m + 1) := by
        rw [abs_of_nonneg ht]
        simp
        ring
  · have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := f) ht
      (Filter.Eventually.of_forall fun τ hτ => h τ (by rwa [uIoc_of_ge ht])) (hint t 0)
    have hcongr : ∫ τ in t..(0 : ℝ), C * |τ| ^ m = ∫ τ in t..(0 : ℝ), C * (-τ) ^ m :=
      intervalIntegral.integral_congr fun τ hτ => by
        rw [uIcc_of_le ht] at hτ
        simp [abs_of_nonpos hτ.2]
    have hneg : ∫ τ in t..(0 : ℝ), (-τ) ^ m = (-t) ^ (m + 1) / (m + 1) := by
      have := intervalIntegral.integral_comp_neg (a := t) (b := 0) (fun x : ℝ => x ^ m)
      rw [this, integral_pow]
      simp
    rw [hcongr, intervalIntegral.integral_const_mul, hneg] at hle
    rw [intervalIntegral.integral_symm, norm_neg]
    calc _ ≤ C * ((-t) ^ (m + 1) / (m + 1)) := hle
      _ = C * |t| ^ (m + 1) / (m + 1) := by
        rw [abs_of_nonpos ht]
        ring

/-- The gauge norm of an integral: `ν(∫₀ᵗ f) ≤ C |t|^{m+1}/(m+1)` if `ν(f τ) ≤ C |τ|^m`. -/
theorem norm_gauge_intervalIntegral_le {W : E ≃L[ℂ] E} {f : ℝ → E} {C : ℝ} {m : ℕ} {t : ℝ}
    (hf : IntervalIntegrable f volume 0 t)
    (h : ∀ τ ∈ Ι (0 : ℝ) t, ‖W (f τ)‖ ≤ C * |τ| ^ m) :
    ‖W (∫ τ in (0 : ℝ)..t, f τ)‖ ≤ C * |t| ^ (m + 1) / (m + 1) := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hcomm := ((W : E →L[ℂ] E).restrictScalars ℝ).intervalIntegral_comp_comm hf
  have : W (∫ τ in (0 : ℝ)..t, f τ) = ∫ τ in (0 : ℝ)..t, W (f τ) := hcomm.symm
  rw [this]
  exact norm_intervalIntegral_le_pow h

/-! ### Gauge balls -/

/-- Closed gauge balls are compact. -/
theorem isCompact_gaugeBall' (W : E ≃L[ℂ] E) (z : E) (c : ℝ) :
    IsCompact {w : E | ‖W (w - z)‖ ≤ c} := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have h : {w : E | ‖W (w - z)‖ ≤ c} = (fun y => W.symm y + z) '' closedBall (0 : E) c := by
    ext w
    simp only [mem_ofPred_eq, mem_image, mem_closedBall, dist_zero_right]
    constructor
    · intro hw
      exact ⟨W (w - z), hw, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [h]
  exact (isCompact_closedBall 0 c).image (W.symm.continuous.add continuous_const)

/-- A gauge interior has a little room: `Ω^c ⊆ ⋃_{η>0} Ω^{c+η}` pointwise. -/
theorem exists_gaugeInterior_gt' {Ω : Set E} (hΩ : IsOpen Ω) (W : E ≃L[ℂ] E) {c : ℝ} {z : E}
    (hz : z ∈ gaugeInterior W Ω c) : ∃ η > 0, z ∈ gaugeInterior W Ω (c + η) := by
  by_cases hS : ({w : E | ‖W (w - z)‖ ≤ c + 1} ∩ Ωᶜ).Nonempty
  · have hcomp : IsCompact ({w : E | ‖W (w - z)‖ ≤ c + 1} ∩ Ωᶜ) :=
      (isCompact_gaugeBall' W z (c + 1)).inter_right hΩ.isClosed_compl
    have hcont : ContinuousOn (fun w : E => ‖W (w - z)‖) ({w : E | ‖W (w - z)‖ ≤ c + 1} ∩ Ωᶜ) :=
      (continuous_norm.comp (W.continuous.comp (continuous_id.sub continuous_const))).continuousOn
    obtain ⟨w₀, hw₀, hmin⟩ := hcomp.exists_isMinOn hS hcont
    have hm : c < ‖W (w₀ - z)‖ := by
      by_contra hle
      exact hw₀.2 (hz w₀ (not_lt.1 hle))
    refine ⟨min 1 ((‖W (w₀ - z)‖ - c) / 2), lt_min one_pos (by linarith), fun w hw => ?_⟩
    by_contra hwΩ
    have hwS : w ∈ {w : E | ‖W (w - z)‖ ≤ c + 1} ∩ Ωᶜ :=
      ⟨(hw.trans (by linarith [min_le_left 1 ((‖W (w₀ - z)‖ - c) / 2)])), hwΩ⟩
    have h1 := isMinOn_iff.1 hmin w hwS
    have h2 := min_le_right 1 ((‖W (w₀ - z)‖ - c) / 2)
    linarith
  · refine ⟨1, one_pos, fun w hw => ?_⟩
    by_contra hwΩ
    exact hS ⟨w, hw, hwΩ⟩

/-! ### Regularity of the field -/

/-- `DF` is continuous on `Ω`. -/
theorem continuousOn_fderiv_field {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ}
    (h : SmallField W Ω F ε) : ContinuousOn (fun x => fderiv ℂ F x) Ω := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  exact ((KAM.contDiffOn_infty_of_differentiableOn h.isOpen h.differentiableOn).of_le
    (by exact_mod_cast le_top)).continuousOn_fderiv_of_isOpen h.isOpen le_rfl

/-- Composing a `ParamHyp` family with the holomorphic field `F` (with values in `Ω`). -/
theorem ParamHyp.comp_field {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ}
    (h : SmallField W Ω F ε) {U : Set E} (hU : IsOpen U) {y : ℝ → E → E} (hy : ParamHyp U y)
    (hmap : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ z ∈ U, y t z ∈ Ω) :
    ParamHyp U (fun t z => F (y t z)) ∧ ∀ t ∈ Icc (-1 : ℝ) 1, ∀ z ∈ U,
      fderiv ℂ (fun w => F (y t w)) z = (fderiv ℂ F (y t z)).comp (fderiv ℂ (y t) z) := by
  have hder : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ z ∈ U,
      fderiv ℂ (fun w => F (y t w)) z = (fderiv ℂ F (y t z)).comp (fderiv ℂ (y t) z) := by
    intro t ht z hz
    exact fderiv_comp z
      (h.differentiableOn.differentiableAt (h.isOpen.mem_nhds (hmap t ht z hz)))
      ((hy.diff t ht).differentiableAt (hU.mem_nhds hz))
  refine ⟨⟨?_, ?_, ?_⟩, hder⟩
  · exact h.differentiableOn.continuousOn.comp hy.cont fun p hp => hmap p.1 hp.1 p.2 hp.2
  · exact fun t ht => h.differentiableOn.comp (hy.diff t ht) fun z hz => hmap t ht z hz
  · have hc : ContinuousOn (fun p : ℝ × E => (fderiv ℂ F (y p.1 p.2)).comp
        (fderiv ℂ (y p.1) p.2)) (Icc (-1 : ℝ) 1 ×ˢ U) :=
      ((continuousOn_fderiv_field h).comp hy.cont fun p hp => hmap p.1 hp.1 p.2 hp.2).clm_comp
        hy.contD
    exact hc.congr fun p hp => hder p.1 hp.1 p.2 hp.2

omit [FiniteDimensional ℂ E] in
/-- The time slice `τ ↦ y τ z` of a `ParamHyp` family is continuous on `[-1, 1]`. -/
theorem ParamHyp.continuousOn_time {U : Set E} {y : ℝ → E → E} (hy : ParamHyp U y) {z : E}
    (hz : z ∈ U) : ContinuousOn (fun τ => y τ z) (Icc (-1 : ℝ) 1) := by
  have h1 : Continuous (fun τ : ℝ => (τ, z)) := continuous_id.prodMk continuous_const
  exact hy.cont.comp h1.continuousOn fun τ hτ => ⟨hτ, hz⟩

/-! ### The Picard iterates -/

/-- The Picard iterates `y₀ = z`, `y_{k+1}(t, z) = z + ∫₀ᵗ F(y_k(τ, z)) dτ`. -/
def picard (F : E → E) : ℕ → ℝ → E → E
  | 0 => fun _ z => z
  | k + 1 => fun t z => z + ∫ τ in (0 : ℝ)..t, F (picard F k τ z)

omit [FiniteDimensional ℂ E] in
theorem picard_zero (F : E → E) (t : ℝ) (z : E) : picard F 0 t z = z := rfl

omit [FiniteDimensional ℂ E] in
theorem picard_succ (F : E → E) (k : ℕ) (t : ℝ) (z : E) :
    picard F (k + 1) t z = z + ∫ τ in (0 : ℝ)..t, F (picard F k τ z) := rfl

omit [FiniteDimensional ℂ E] in
/-- `|t| ε ≤ 1/2` for `|t| ≤ 1`. -/
theorem abs_mul_le_half {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ} (h : SmallField W Ω F ε)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : |t| * ε ≤ 1 / 2 := by
  have h1 : |t| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  have h2 := h.eps_nonneg
  have h3 := h.eps_le
  nlinarith [abs_nonneg t]

omit [FiniteDimensional ℂ E] in
/-- A point at gauge distance `≤ |t| ε` from `z ∈ Ω^{1/2}` lies in `Ω`. -/
theorem mem_of_displacement {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ}
    (h : SmallField W Ω F ε) {z x : E} (hz : z ∈ gaugeInterior W Ω (1 / 2)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (hx : ‖W (x - z)‖ ≤ |t| * ε) : x ∈ Ω :=
  hz x (hx.trans (abs_mul_le_half h ht))

/-- Regularity of the Picard iterates on `[-1, 1] × Ω^{1/2}`, and their displacement bound. -/
theorem picard_regular {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ} (h : SmallField W Ω F ε)
    (k : ℕ) :
    ParamHyp (gaugeInterior W Ω (1 / 2)) (picard F k) ∧
    ∀ t ∈ Icc (-1 : ℝ) 1, ∀ z ∈ gaugeInterior W Ω (1 / 2), ‖W (picard F k t z - z)‖ ≤ |t| * ε := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hU := isOpen_gaugeInterior h.isOpen W (1 / 2)
  induction k with
  | zero =>
    refine ⟨⟨continuousOn_snd, fun t _ => differentiableOn_id, ?_⟩, fun t ht z _ => ?_⟩
    · have hc : ContinuousOn (fun _ : ℝ × E => ContinuousLinearMap.id ℂ E)
          (Icc (-1 : ℝ) 1 ×ˢ gaugeInterior W Ω (1 / 2)) := continuousOn_const
      exact hc.congr fun p _ => fderiv_fun_id
    · simp [picard_zero]
      exact mul_nonneg (abs_nonneg t) h.eps_nonneg
  | succ k ih =>
    obtain ⟨hy, hd⟩ := ih
    have hmap : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ z ∈ gaugeInterior W Ω (1 / 2), picard F k t z ∈ Ω :=
      fun t ht z hz => mem_of_displacement h hz ht (by simpa using hd t ht z hz)
    obtain ⟨hg, -⟩ := ParamHyp.comp_field h hU hy hmap
    obtain ⟨hy', -⟩ := hg.id_add hU
    refine ⟨hy', fun t ht z hz => ?_⟩
    have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have hsub : uIcc (0 : ℝ) t ⊆ Icc (-1 : ℝ) 1 := uIcc_subset_Icc h0 ht
    have hint : IntervalIntegrable (fun τ => F (picard F k τ z)) volume 0 t :=
      ((hg.continuousOn_time hz).mono hsub).intervalIntegrable
    have hb : ∀ τ ∈ Ι (0 : ℝ) t, ‖W (F (picard F k τ z))‖ ≤ ε * |τ| ^ 0 := fun τ hτ => by
      simpa using h.bound _ (hmap τ (hsub (uIoc_subset_uIcc hτ)) z hz)
    have := norm_gauge_intervalIntegral_le hint hb
    rw [picard_succ, add_sub_cancel_left]
    simpa [mul_comm] using this

/-- The integrand `τ ↦ F (y_k(τ, z))` of the Picard step is interval integrable on `[0, t]`. -/
theorem intervalIntegrable_picard_field {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ}
    (h : SmallField W Ω F ε) (k : ℕ) {z : E} (hz : z ∈ gaugeInterior W Ω (1 / 2)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) : IntervalIntegrable (fun τ => F (picard F k τ z)) volume 0 t := by
  have hU := isOpen_gaugeInterior h.isOpen W (1 / 2)
  obtain ⟨hy, hd⟩ := picard_regular h k
  have hmap : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ z ∈ gaugeInterior W Ω (1 / 2), picard F k t z ∈ Ω :=
    fun t ht z hz => mem_of_displacement h hz ht (by simpa using hd t ht z hz)
  obtain ⟨hg, -⟩ := ParamHyp.comp_field h hU hy hmap
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  exact ((hg.continuousOn_time hz).mono (uIcc_subset_Icc h0 ht)).intervalIntegrable

end Picard

end KAM.Canonical
