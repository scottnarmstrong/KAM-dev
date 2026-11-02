/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.Homological

/-!
# HD 11964: `χ*` on the bridge's open set, and the explicit small divisors (HD11964-CHI)

* `openHD`: actions within `1/250` of the box (open), chart AMD below `1/50`, every angle.
  `isOpen_openHD`, `isAngleSaturated_openHD`; `openHD_subset_chartSafe` (LP-LIFT: every point,
  at every angle, is collision-free, by `mem_chartSafe_of_liftQ` for the initial state at the
  nearest box point); `region_subset_openHD` (`R(d) ⊆ openHD` for `d ≤ 1/500`);
  `chartRot_mem_openHD` (`openHD` is invariant under the chart rotation).
* `modesHD`: the mode set `0 < |k|`, `|k_c| ≤ 80`, `|k_b| ≤ 20`. `smallDivisor_HD`: on `openHD`,
  `|k·ω(Λ)| ≥ ω_b(Λ) ≥ 1/(Λhi_b + 1/250)³` for every `k ∈ modesHD` (`ω_c ≥ 21 ω_b` there, while
  `|k_b| ≤ 20`; the smallest divisor is at `k = (0, ±1)`). `isModeSet_HD`.
* `contDiffOn_chi_HD`: `χ₁ = χ*(P)`, `G₂ = {P - ½ Π_S P, χ₁}`, `χ₂ = χ*(G₂)` are `C^∞` on `openHD`,
  and `approxIntegral₂` is differentiable there (the bridge's `hF`).
* `residual_tails_HD`: `r₁ = P - Π_S P` and `r₂ = G₂ - Π_S G₂` on `openHD`, pure tails outside
  `modesHD`.
-/

@[expose] public noncomputable section

open Set Filter Topology KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Application.LambdaDrift
open scoped Real ContDiff

namespace HD11964.Cover

/-- **The mode set of HD 11964**: `0 < |k|`, `|k_c| ≤ 80`, `|k_b| ≤ 20` (planet `c` is index 0).
Irreducible: membership is used through `mem_modesHD` only (the finset has 6600 modes). -/
@[irreducible] def modesHD : Finset (Fin 2 → ℤ) :=
  ((Finset.Icc (-80 : ℤ) 80 ×ˢ Finset.Icc (-20 : ℤ) 20).image fun p => ![p.1, p.2]).erase 0

/-- **The open set of the bridge** for HD 11964: actions within `1/250` of the box (open), chart
AMD below `1/50`, every angle. -/
def openHD : Set (Phase (2 + 2)) :=
  {w | (∀ i, lamLo i - 1 / 250 < fast w.2 i ∧ fast w.2 i < lamHi i + 1 / 250) ∧
    chartAMD w < 1 / 50}

/-! ### The open set -/

theorem continuous_fast_snd' (i : Fin 2) : Continuous fun w : Phase (2 + 2) => fast w.2 i :=
  ((contDiff_coord (Fin.castAdd 2 i)).comp contDiff_snd).continuous

theorem continuous_chartAMD' : Continuous fun w : Phase (2 + 2) => chartAMD w := by
  unfold chartAMD
  refine continuous_finsetSum _ fun i _ => ?_
  have h1 : Continuous fun w : Phase (2 + 2) => slow w.1 i :=
    (continuous_apply (Fin.natAdd 2 i)).comp continuous_fst
  have h2 : Continuous fun w : Phase (2 + 2) => slow w.2 i :=
    (continuous_apply (Fin.natAdd 2 i)).comp continuous_snd
  exact ((h1.pow 2).add (h2.pow 2)).div_const 2

theorem isOpen_openHD : IsOpen openHD := by
  have e : openHD = (⋂ i : Fin 2, ({w : Phase (2 + 2) | lamLo i - 1 / 250 < fast w.2 i} ∩
      {w | fast w.2 i < lamHi i + 1 / 250})) ∩ {w | chartAMD w < 1 / 50} := by
    ext w
    simp [openHD, forall_and]
  rw [e]
  exact (isOpen_iInter_of_finite fun i =>
    (isOpen_lt continuous_const (continuous_fast_snd' i)).inter
      (isOpen_lt (continuous_fast_snd' i) continuous_const)).inter
    (isOpen_lt continuous_chartAMD' continuous_const)

theorem isAngleSaturated_openHD : IsAngleSaturated openHD := by
  intro w hw lam
  refine ⟨fun i => ?_, ?_⟩
  · rw [withAngles_snd]
    exact hw.1 i
  · rw [chartAMD_withAngles]
    exact hw.2

theorem lamLo_le_lamHi (i : Fin 2) : lamLo i ≤ lamHi i := by
  fin_cases i <;> norm_num [lamLo, lamHi]

/-- **The HD open set is collision-free at every angle** (LP-LIFT). -/
theorem openHD_subset_chartSafe : openHD ⊆ chartSafe nu := by
  intro w hw
  -- the nearest box point and its circular chart state
  set Λ0 : Fin 2 → ℝ := fun i => max (lamLo i) (min (fast w.2 i) (lamHi i)) with hΛ0
  have hbox0 : ∀ i, lamLo i ≤ Λ0 i ∧ Λ0 i ≤ lamHi i := fun i =>
    ⟨le_max_left _ _, max_le (lamLo_le_lamHi i) (min_le_right _ _)⟩
  have hclose : ∀ i, |fast w.2 i - Λ0 i| ≤ 1 / 250 := by
    intro i
    have h1 := (hw.1 i).1
    have h2 := (hw.1 i).2
    have h3 := lamLo_le_lamHi i
    simp only [hΛ0, max_def, min_def]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  set w0 : Phase (2 + 2) := assemble Λ0 0 0 0 with hw0
  have hfast0 : fast w0.2 = Λ0 := by simp only [hw0, assemble, fast_append']
  have hslow1 : slow w0.1 = 0 := by simp only [hw0, assemble, slow_append']
  have hslow2 : slow w0.2 = 0 := by simp only [hw0, assemble, slow_append']
  have hamd0 : chartAMD w0 = 0 := by simp [chartAMD, hslow1, hslow2]
  have hΛw0 : ∀ i, lamLo i ≤ fast w0.2 i ∧ fast w0.2 i ≤ lamHi i := by
    rw [hfast0]
    exact hbox0
  obtain ⟨hphys, hbox, hC, hL⟩ := initial_of_chart hΛw0 (by rw [hamd0]; norm_num [cBar])
  have hd := liftData hphys hbox hC hL
  -- the chart domain at `w0`, for its actions
  have hdom : w0 ∈ poincareProdDom 2 := by
    intro i
    have hΓ : poincareGamma (planetBlock w0 i) = lpGamma w0 i := by
      simp [poincareGamma, lpGamma, planetBlock, slow]
    have h0 : (planetBlock w0 i).2 0 = fast w0.2 i := by simp [planetBlock]
    have hl : lpGamma w0 i = 0 := by simp [lpGamma, hslow1, hslow2]
    have hpos : 0 < fast w0.2 i := by
      rw [hfast0]
      refine lt_of_lt_of_le ?_ (hbox0 i).1
      fin_cases i <;> norm_num [lamLo]
    refine ⟨by rw [h0]; exact hpos, ?_⟩
    rw [hΓ, h0, hl]
    exact hpos
  have hact : actionVector nu (poincareProd nu 1 w0) = Λ0 := by
    funext i
    show keplerAction nu (poincareProd nu 1 w0) i = Λ0 i
    rw [lpChart_action nu_pos hdom i, hfast0]
  have hboxA : Λ0 ∈ actionBox := by
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := (hbox0 i).1
      show lamLo i - rTube ≤ Λ0 i
      norm_num [rTube]
      linarith
    · have := (hbox0 i).2
      show Λ0 i ≤ lamHi i + rTube
      norm_num [rTube]
      linarith
  have hnorm : ‖fast w.2 - actionVector nu (poincareProd nu 1 w0)‖ ≤ rTube := by
    rw [hact]
    refine (pi_norm_le_iff_of_nonneg (by norm_num [rTube])).2 fun i => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs]
    norm_num [rTube]
    exact hclose i
  have hamd : chartAMD w ≤ strongThreshold nu (actionVector nu (poincareProd nu 1 w0)) -
      delta / 4 := by
    rw [hact, strongThreshold_eq_on_box hboxA]
    have h1 := hw.2
    have h2 := (hbox0 0).1
    have h3 : (1 : ℝ) / 50 ≤ lamLo 0 - delta / 4 := by norm_num [lamLo, delta]
    linarith
  exact hd.mem_chartSafe_of_liftQ (LiftData.zeroAngle_mem_liftQ hnorm hamd)

/-- **`R(d)` lies in the HD open set** for `d ≤ 1/500`. -/
theorem region_subset_openHD {d : ℝ} (hd : d ≤ 1 / 500) : region d ⊆ openHD := by
  intro w hw
  obtain ⟨-, hΛ, hA⟩ := hw
  refine ⟨fun i => ⟨by linarith [(hΛ i).1], by linarith [(hΛ i).2]⟩, ?_⟩
  have : cBar + 2 * d < 1 / 50 := by norm_num [cBar]; linarith
  linarith

theorem openHD_subset_dom : openHD ⊆ poincareProdDom 2 := fun _ hw =>
  chartSafe_subset_dom nu (openHD_subset_chartSafe hw)

/-- **`openHD` is invariant under the chart rotation** (the `O` half of the bridge's `hFrot`;
AUDIT-HD11964-CHI-1, R1): rotations fix `Λ` and `chartAMD`. -/
theorem chartRot_mem_openHD (θ : ℝ) {w : Phase (2 + 2)} (hw : w ∈ openHD) :
    chartRot θ w ∈ openHD :=
  ⟨fun i => by rw [fast_chartRot]; exact hw.1 i, by rw [chartAMD_chartRot]; exact hw.2⟩

/-! ### The small divisors -/

theorem mem_modesHD {k : Fin 2 → ℤ} : k ∈ modesHD ↔ k ≠ 0 ∧ |k 0| ≤ 80 ∧ |k 1| ≤ 20 := by
  unfold modesHD
  simp only [Finset.mem_erase, Finset.mem_image, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨hk, ⟨a, b⟩, ⟨⟨ha1, ha2⟩, hb1, hb2⟩, rfl⟩
    exact ⟨hk, abs_le.mpr ⟨ha1, ha2⟩, abs_le.mpr ⟨hb1, hb2⟩⟩
  · rintro ⟨hk, h0, h1⟩
    refine ⟨hk, (k 0, k 1), ⟨abs_le.mp h0, abs_le.mp h1⟩, ?_⟩
    funext i
    fin_cases i <;> rfl

theorem neg_mem_modesHD {k : Fin 2 → ℤ} (hk : k ∈ modesHD) : -k ∈ modesHD := by
  obtain ⟨h0, h1, h2⟩ := mem_modesHD.mp hk
  exact mem_modesHD.mpr ⟨neg_ne_zero.mpr h0, by simpa using h1, by simpa using h2⟩

theorem zero_not_mem_modesHD : (0 : Fin 2 → ℤ) ∉ modesHD := fun h =>
  (mem_modesHD.mp h).1 rfl

/-- **The small divisors of HD 11964, explicit**: on `openHD`, every divisor satisfies
`|k·ω(Λ)| ≥ ω_b(Λ) ≥ 1/(Λhi_b + 1/250)³` (for `k_c = 0`, `|k_b| ≥ 1`; for `k_c ≠ 0`,
`ω_c ≥ 21 ω_b` and `|k_b| ≤ 20`). -/
theorem smallDivisor_HD {k : Fin 2 → ℤ} (hk : k ∈ modesHD) {w : Phase (2 + 2)} (hw : w ∈ openHD) :
    1 / (lamHi 1 + 1 / 250) ^ 3 ≤ |∑ i, (k i : ℝ) * keplerFreq nu (fast w.2) i| := by
  obtain ⟨hk0, hkc, hkb⟩ := mem_modesHD.mp hk
  have hx := hw.1 0
  have hy := hw.1 1
  set x := fast w.2 0
  set y := fast w.2 1
  have hxpos : 0 < x := by
    have := hx.1
    norm_num [lamLo] at this
    linarith
  have hypos : 0 < y := by
    have := hy.1
    norm_num [lamLo] at this
    linarith
  have hnu0 : nu 0 = 1217282799 / 10027486241 := by simp [nu]
  have hnu1 : nu 1 = 1 := by simp [nu]
  simp only [Fin.sum_univ_two, keplerFreq]
  set ωc := nu 0 ^ 3 / x ^ 3 with hωc_def
  set ωb := nu 1 ^ 3 / y ^ 3 with hωb_def
  have hωbpos : 0 < ωb := by rw [hωb_def, hnu1]; positivity
  have hωcpos : 0 < ωc := by rw [hωc_def, hnu0]; positivity
  have hωb : 1 / (lamHi 1 + 1 / 250) ^ 3 ≤ ωb := by
    rw [hωb_def, hnu1, one_pow]
    exact one_div_le_one_div_of_le (pow_pos hypos 3) (pow_le_pow_left₀ hypos.le hy.2.le 3)
  have hωc : 21 * ωb ≤ ωc := by
    rw [hωb_def, hωc_def, hnu1, one_pow, mul_one_div, div_le_div_iff₀ (pow_pos hypos 3)
      (pow_pos hxpos 3)]
    have hX : x ^ 3 ≤ (lamHi 0 + 1 / 250) ^ 3 := pow_le_pow_left₀ hxpos.le hx.2.le 3
    have hYpos : (0 : ℝ) < lamLo 1 - 1 / 250 := by norm_num [lamLo]
    have hY : (lamLo 1 - 1 / 250) ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hYpos.le hy.1.le 3
    have hnum : 21 * (lamHi 0 + 1 / 250) ^ 3 ≤ nu 0 ^ 3 * (lamLo 1 - 1 / 250) ^ 3 := by
      rw [hnu0]
      norm_num [lamHi, lamLo]
    have hnu3 : 0 ≤ nu 0 ^ 3 := by rw [hnu0]; positivity
    nlinarith [mul_le_mul_of_nonneg_left hY hnu3]
  refine hωb.trans ?_
  by_cases hc0 : k 0 = 0
  · have hb : k 1 ≠ 0 := fun h => hk0 (by funext i; fin_cases i <;> simp [hc0, h])
    have h1 : (1 : ℝ) ≤ |(k 1 : ℝ)| := by exact_mod_cast Int.one_le_abs hb
    rw [hc0, Int.cast_zero, zero_mul, zero_add, abs_mul, abs_of_pos hωbpos]
    nlinarith
  · have h1 : (1 : ℝ) ≤ |(k 0 : ℝ)| := by exact_mod_cast Int.one_le_abs hc0
    have h2 : |(k 1 : ℝ)| ≤ 20 := by exact_mod_cast hkb
    have htri := abs_add_le ((k 0 : ℝ) * ωc + (k 1 : ℝ) * ωb) (-((k 1 : ℝ) * ωb))
    rw [add_neg_cancel_right, abs_neg, abs_mul, abs_mul, abs_of_pos hωcpos,
      abs_of_pos hωbpos] at htri
    nlinarith [mul_le_mul_of_nonneg_right h1 hωcpos.le, mul_le_mul_of_nonneg_right h2 hωbpos.le]

/-- `modesHD` is a mode set on `openHD` (AUDIT-HD11964-LEMMAS-1, L1). -/
theorem isModeSet_HD : IsModeSet modesHD (keplerFreq nu) openHD :=
  ⟨fun _ hk => neg_mem_modesHD hk, zero_not_mem_modesHD, fun _ hk _ hw =>
    abs_pos.mp (lt_of_lt_of_le (by norm_num [lamHi]) (smallDivisor_HD hk hw))⟩

/-! ### The bridge's `hF`, and the tails -/

theorem contDiffOn_chartPert_HD : ContDiffOn ℝ ∞ (chartPert nu mu) openHD :=
  (((contDiffOn_liftChartHam nu_pos mu).mono openHD_subset_chartSafe).sub
    ((contDiffOn_hProd nu).mono openHD_subset_dom))

/-- **Smoothness of `χ₁`, `χ₂` and the bridge's `hF` for HD 11964** on `openHD`. -/
theorem contDiffOn_chi_HD :
    let P := chartPert nu mu
    let χ₁ := chiStar modesHD (keplerFreq nu) P
    let G₂ := pb (fun y => P y - projS modesHD P y / 2) χ₁
    let χ₂ := chiStar modesHD (keplerFreq nu) G₂
    ContDiffOn ℝ ∞ χ₁ openHD ∧ ContDiffOn ℝ ∞ χ₂ openHD ∧
      ∀ i : Fin 2, DifferentiableOn ℝ (approxIntegral₂ (Fin.castAdd 2 i) χ₁ χ₂) openHD := by
  intro P χ₁ G₂ χ₂
  have hfrq : ∀ w ∈ openHD, ContDiffAt ℝ ∞ (keplerFreq nu) (fast w.2) := fun w hw =>
    contDiffAt_keplerFreq nu (fast_ne_zero_of_mem_dom (openHD_subset_dom hw))
  have hP := contDiffOn_chartPert_HD
  have hχ₁ : ContDiffOn ℝ ∞ χ₁ openHD :=
    contDiffOn_chiStar isOpen_openHD isAngleSaturated_openHD hP hfrq isModeSet_HD
  have hA : ContDiffOn ℝ ∞ (fun y => P y - projS modesHD P y / 2) openHD :=
    hP.sub ((contDiffOn_projS isOpen_openHD isAngleSaturated_openHD modesHD hP).div_const 2)
  have hG₂ : ContDiffOn ℝ ∞ G₂ openHD := fun y hy =>
    (contDiffAt_pb (hA.contDiffAt (isOpen_openHD.mem_nhds hy))
      (hχ₁.contDiffAt (isOpen_openHD.mem_nhds hy))).contDiffWithinAt
  have hχ₂ : ContDiffOn ℝ ∞ χ₂ openHD :=
    contDiffOn_chiStar isOpen_openHD isAngleSaturated_openHD hG₂ hfrq isModeSet_HD
  exact ⟨hχ₁, hχ₂, fun i => differentiableOn_approxIntegral₂ _ isOpen_openHD hχ₁ hχ₂⟩

/-- **The residuals of HD 11964 are pure tails** outside `modesHD`, on `openHD`. -/
theorem residual_tails_HD :
    let P := chartPert nu mu
    let χ₁ := chiStar modesHD (keplerFreq nu) P
    let G₂ := pb (fun y => P y - projS modesHD P y / 2) χ₁
    let χ₂ := chiStar modesHD (keplerFreq nu) G₂
    ((∀ w ∈ openHD, residual₁ (hProd 1 nu) P χ₁ w = P w - projS modesHD P w) ∧
      ∀ k ∈ modesHD, ∀ w ∈ openHD, chartCoeff (residual₁ (hProd 1 nu) P χ₁) k w = 0) ∧
    ((∀ w ∈ openHD, residual₂ (hProd 1 nu) P χ₁ χ₂ w = G₂ w - projS modesHD G₂ w) ∧
      ∀ k ∈ modesHD, ∀ w ∈ openHD, chartCoeff (residual₂ (hProd 1 nu) P χ₁ χ₂) k w = 0) :=
  ⟨residual₁_tail isOpen_openHD isAngleSaturated_openHD openHD_subset_dom
      contDiffOn_chartPert_HD isModeSet_HD,
    residual₂_tail isOpen_openHD isAngleSaturated_openHD openHD_subset_dom
      contDiffOn_chartPert_HD isModeSet_HD⟩

end HD11964.Cover

end
