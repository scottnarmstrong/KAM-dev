/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Recon2.Force
public import KAM.Wave.Recon2.Orbit
public import KAM.Frozen.Wave.Defs.IsClassicalSolution

/-!
# Classical solutions from analytic coefficient solutions (blueprint `bpW:w2:curve`)

Infrastructure used by several nodes; the dependency graph is still being built. Blueprint label
`bpW:w2:curve` (milestone W2): P96-W Lemma 1 in frozen form.

For an analytic coefficient solution `Y` (`KAM.Wave.IsAnalyticCoeffSolution`) and
`u(t, x) = reconU (Y t).1 x`:

* (i) `KAM.Wave.analyticAt_reconWave_u` and siblings: joint real analyticity of
  `u, u_t, u_x, u_xx, u_tt`;
* (ii) `KAM.Wave.hasDerivAt_reconWave_ut`: `u_t = V_m(Y₂)`;
* (iii) `KAM.Wave.hasDerivAt_reconWave_utt`: `u_tt = u_xx - m u - u³` for `x ∈ [0, π]`;
* (iv) `KAM.Wave.hasDerivAt_reconWave_ux`: the `x`-derivatives;
* (v) `KAM.Wave.isClassicalSolution_reconWave`: the frozen `IsClassicalSolution`;
* (vi) `KAM.Wave.reconWave_bound`: the `derivWithin` identification and the bound `M_m ‖Y t‖`.
The bundled statement is `KAM.Wave.reconWave_curve`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

section Curve

variable {m : ℝ} {hm : 0 < m} {Y : ℝ → WaveSpace}

lemma analyticAt_coeffSol_fst (hY : IsAnalyticCoeffSolution m hm Y) (t : ℝ) :
    AnalyticAt ℝ (fun s => (Y s).1) t :=
  ((ContinuousLinearMap.fst ℝ (lp (fun _ : ℕ+ => ℝ) 2)
    (lp (fun _ : ℕ+ => ℝ) 2)).analyticAt (Y t)).comp (hY.1 t)

lemma analyticAt_coeffSol_snd (hY : IsAnalyticCoeffSolution m hm Y) (t : ℝ) :
    AnalyticAt ℝ (fun s => (Y s).2) t :=
  ((ContinuousLinearMap.snd ℝ (lp (fun _ : ℕ+ => ℝ) 2)
    (lp (fun _ : ℕ+ => ℝ) 2)).analyticAt (Y t)).comp (hY.1 t)

/-! ### (i) Joint analyticity -/

theorem analyticAt_reconWave_u (hY : IsAnalyticCoeffSolution m hm Y) (z : ℝ × ℝ) :
    AnalyticAt ℝ (fun z : ℝ × ℝ => reconU m hm (Y z.1).1 z.2) z := by
  obtain ⟨t, x⟩ := z
  have := analyticAt_reconUIter m hm 0 (analyticAt_coeffSol_fst hY t) x
  simpa only [reconUIter_zero] using this

theorem analyticAt_reconWave_ux (hY : IsAnalyticCoeffSolution m hm Y) (z : ℝ × ℝ) :
    AnalyticAt ℝ (fun z : ℝ × ℝ => reconUx m hm (Y z.1).1 z.2) z := by
  obtain ⟨t, x⟩ := z
  have := analyticAt_reconUIter m hm 1 (analyticAt_coeffSol_fst hY t) x
  simpa only [← reconUx_eq_iter] using this

theorem analyticAt_reconWave_uxx (hY : IsAnalyticCoeffSolution m hm Y) (z : ℝ × ℝ) :
    AnalyticAt ℝ (fun z : ℝ × ℝ => reconUxx m hm (Y z.1).1 z.2) z := by
  obtain ⟨t, x⟩ := z
  have := analyticAt_reconUIter m hm 2 (analyticAt_coeffSol_fst hY t) x
  simpa only [← reconUxx_eq_iter] using this

theorem analyticAt_reconWave_ut (hY : IsAnalyticCoeffSolution m hm Y) (z : ℝ × ℝ) :
    AnalyticAt ℝ (fun z : ℝ × ℝ => reconV m hm (Y z.1).2 z.2) z := by
  obtain ⟨t, x⟩ := z
  have := analyticAt_reconVIter m hm 0 (analyticAt_coeffSol_snd hY t) x
  simpa only [reconVIter_zero] using this

theorem analyticAt_reconWave_utt (hY : IsAnalyticCoeffSolution m hm Y) (z : ℝ × ℝ) :
    AnalyticAt ℝ (fun z : ℝ × ℝ => reconUxx m hm (Y z.1).1 z.2 - m * reconU m hm (Y z.1).1 z.2 -
      reconU m hm (Y z.1).1 z.2 ^ 3) z :=
  ((analyticAt_reconWave_uxx hY z).sub (analyticAt_const.mul (analyticAt_reconWave_u hY z))).sub
    ((analyticAt_reconWave_u hY z).pow 3)

/-! ### (ii), (iii) Time derivatives -/

lemma lam_mul_div_sqrt_lam (m : ℝ) (hm : 0 < m) (j : ℕ+) (c : ℝ) :
    lam m hm j * c / Real.sqrt (lam m hm j) = Real.sqrt (lam m hm j) * c := by
  calc lam m hm j * c / Real.sqrt (lam m hm j)
      = ((Real.sqrt (lam m hm j))⁻¹ * lam m hm j) * c := by rw [div_eq_inv_mul]; ring
    _ = _ := by rw [wave_sqrt_lam_inv_mul_lam]

/-- `U_m(Y₁') = V_m(Y₂)` when `κ(Y₁')_j = λ_j κ(Y₂)_j`. -/
lemma reconU_eq_reconV_of_coeff {y' y : lp (fun _ : ℕ+ => ℝ) 2}
    (h : ∀ j, coeff y' j = lam m hm j * coeff y j) (x : ℝ) :
    reconU m hm y' x = reconV m hm y x := by
  unfold reconU reconV
  refine tsum_congr fun j => ?_
  rw [h, lam_mul_div_sqrt_lam]

/-- (ii) of `bpW:w2:curve`: `s ↦ u(s, x)` has derivative `V_m(Y₂(t))(x)` at `t`, for every
`x ∈ ℝ`. -/
theorem hasDerivAt_reconWave_ut (hY : IsAnalyticCoeffSolution m hm Y) (t x : ℝ) :
    HasDerivAt (fun s => reconU m hm (Y s).1 x) (reconV m hm (Y t).2 x) t := by
  have h := (innerSL ℝ (reconFeatureU m hm 0 x)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_coeffSol_fst hY t)
  have e : reconV m hm (Y t).2 x =
      innerSL ℝ (reconFeatureU m hm 0 x) (deriv (fun s => (Y s).1) t) := by
    rw [innerSL_apply_apply, ← reconU_eq_inner]
    exact (reconU_eq_reconV_of_coeff (coeff_deriv_coeffSol_fst hY t) x).symm
  rw [e]
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp [reconU_eq_inner]

/-- (iii) of `bpW:w2:curve`: `s ↦ u_t(s, x)` has derivative `u_xx - m u - u³` at `t`, for
`x ∈ [0, π]`. -/
theorem hasDerivAt_reconWave_utt (hY : IsAnalyticCoeffSolution m hm Y) (t : ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc 0 π) :
    HasDerivAt (fun s => reconV m hm (Y s).2 x)
      (reconUxx m hm (Y t).1 x - m * reconU m hm (Y t).1 x - reconU m hm (Y t).1 x ^ 3) t := by
  have h := (innerSL ℝ (reconFeatureV m hm 0 x)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_coeffSol_snd hY t)
  obtain ⟨hs1, hs2, hl, hc⟩ := reconWave_force m hm (Y t).1
  have e : reconUxx m hm (Y t).1 x - m * reconU m hm (Y t).1 x - reconU m hm (Y t).1 x ^ 3 =
      innerSL ℝ (reconFeatureV m hm 0 x) (deriv (fun s => (Y s).2) t) := by
    rw [innerSL_apply_apply, ← reconV_eq_inner]
    unfold reconV
    have : ∀ j : ℕ+, Real.sqrt (lam m hm j) * coeff (deriv (fun s => (Y s).2) t) j * sineMode j x =
        -(Real.sqrt (lam m hm j) * (lam m hm j * coeff (Y t).1 j) * sineMode j x) -
          Real.sqrt (lam m hm j) * cubicGrad m hm (Y t).1 j * sineMode j x := fun j => by
      rw [coeff_deriv_coeffSol_snd hY t j]; ring
    simp_rw [this]
    rw [Summable.tsum_sub (hs1 x).of_abs.neg (hs2 x).of_abs, tsum_neg, hl x, hc x hx]
    ring
  rw [e]
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp [reconV_eq_inner]

/-! ### (iv), (v), (vi) -/

/-- (iv) of `bpW:w2:curve`. -/
theorem hasDerivAt_reconWave_ux (Y₁ : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    HasDerivAt (reconU m hm Y₁) (reconUx m hm Y₁ x) x ∧
      HasDerivAt (reconUx m hm Y₁) (reconUxx m hm Y₁ x) x :=
  ⟨hasDerivAt_reconU_reconUx m hm Y₁ x, hasDerivAt_reconUx_reconUxx m hm Y₁ x⟩

/-- (v) of `bpW:w2:curve`: `u(t, x) = reconU (Y t).1 x` is a classical solution in the sense of
the frozen definition. -/
theorem isClassicalSolution_reconWave (hY : IsAnalyticCoeffSolution m hm Y) :
    IsClassicalSolution m hm (fun t x => reconU m hm (Y t).1 x) := by
  refine ⟨fun t x => reconV m hm (Y t).2 x, fun t x => reconUx m hm (Y t).1 x,
    fun t x => reconUxx m hm (Y t).1 x - m * reconU m hm (Y t).1 x - reconU m hm (Y t).1 x ^ 3,
    fun t x => reconUxx m hm (Y t).1 x, ?_, ?_, ?_⟩
  · intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    have key : ∀ {f : ℝ × ℝ → ℝ}, (∀ z, AnalyticAt ℝ f z) →
        ContinuousOn f (Set.univ ×ˢ Set.Icc 0 π) :=
      fun h z _ => (h z).continuousAt.continuousWithinAt
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact key (analyticAt_reconWave_u hY)
    · exact key (analyticAt_reconWave_ut hY)
    · exact key (analyticAt_reconWave_ux hY)
    · exact key (analyticAt_reconWave_utt hY)
    · exact key (analyticAt_reconWave_uxx hY)
  · intro t x hx
    exact ⟨hasDerivAt_reconWave_ut hY t x, hasDerivAt_reconWave_utt hY t hx,
      (hasDerivAt_reconWave_ux (Y t).1 x).1.hasDerivWithinAt,
      (hasDerivAt_reconWave_ux (Y t).1 x).2.hasDerivWithinAt, rfl⟩
  · intro t
    exact ⟨reconU_apply_zero m hm _, reconU_apply_pi m hm _⟩

/-- (vi) of `bpW:w2:curve`: `derivWithin` is `u_x`, and the bound `M_m ‖Y t‖`. -/
theorem reconWave_bound (Y : ℝ → WaveSpace) (t : ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc 0 π) :
    derivWithin (reconU m hm (Y t).1) (Set.Icc 0 π) x = reconUx m hm (Y t).1 x ∧
      |reconU m hm (Y t).1 x| + |derivWithin (reconU m hm (Y t).1) (Set.Icc 0 π) x| +
        |reconV m hm (Y t).2 x| ≤ reconWaveBound m * ‖Y t‖ := by
  have hd : derivWithin (reconU m hm (Y t).1) (Set.Icc 0 π) x = reconUx m hm (Y t).1 x :=
    (hasDerivAt_reconU_reconUx m hm (Y t).1 x).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc Real.pi_pos x hx)
  refine ⟨hd, ?_⟩
  rw [hd]
  have h1 := abs_reconU_le m hm (Y t).1 x
  have h2 := abs_reconUx_le m hm (Y t).1 x
  have h3 := abs_reconV_le m hm (Y t).2 x
  have n1 : ‖(Y t).1‖ ≤ ‖Y t‖ := norm_fst_le _
  have n2 : ‖(Y t).2‖ ≤ ‖Y t‖ := norm_snd_le _
  have c0 := reconWaveC0_nonneg
  have s0 := Real.sqrt_nonneg (Real.sqrt (1 + m))
  unfold reconWaveBound
  nlinarith [mul_le_mul_of_nonneg_left n1 c0, mul_le_mul_of_nonneg_left n2 (mul_nonneg s0 c0)]

/-- **P96-W Lemma 1 in frozen form** (blueprint `bpW:w2:curve`). -/
theorem reconWave_curve (hY : IsAnalyticCoeffSolution m hm Y) :
    (∀ z : ℝ × ℝ,
      AnalyticAt ℝ (fun z : ℝ × ℝ => reconU m hm (Y z.1).1 z.2) z ∧
      AnalyticAt ℝ (fun z : ℝ × ℝ => reconUx m hm (Y z.1).1 z.2) z ∧
      AnalyticAt ℝ (fun z : ℝ × ℝ => reconUxx m hm (Y z.1).1 z.2) z ∧
      AnalyticAt ℝ (fun z : ℝ × ℝ => reconV m hm (Y z.1).2 z.2) z ∧
      AnalyticAt ℝ (fun z : ℝ × ℝ => reconUxx m hm (Y z.1).1 z.2 -
        m * reconU m hm (Y z.1).1 z.2 - reconU m hm (Y z.1).1 z.2 ^ 3) z) ∧
    (∀ t x : ℝ, HasDerivAt (fun s => reconU m hm (Y s).1 x) (reconV m hm (Y t).2 x) t) ∧
    (∀ t : ℝ, ∀ x ∈ Set.Icc 0 π, HasDerivAt (fun s => reconV m hm (Y s).2 x)
      (reconUxx m hm (Y t).1 x - m * reconU m hm (Y t).1 x - reconU m hm (Y t).1 x ^ 3) t) ∧
    (∀ (t x : ℝ), HasDerivAt (reconU m hm (Y t).1) (reconUx m hm (Y t).1 x) x ∧
      HasDerivAt (reconUx m hm (Y t).1) (reconUxx m hm (Y t).1 x) x) ∧
    IsClassicalSolution m hm (fun t x => reconU m hm (Y t).1 x) ∧
    ∀ t : ℝ, ∀ x ∈ Set.Icc 0 π,
      derivWithin (reconU m hm (Y t).1) (Set.Icc 0 π) x = reconUx m hm (Y t).1 x ∧
      |reconU m hm (Y t).1 x| + |derivWithin (reconU m hm (Y t).1) (Set.Icc 0 π) x| +
        |reconV m hm (Y t).2 x| ≤ reconWaveBound m * ‖Y t‖ :=
  ⟨fun z => ⟨analyticAt_reconWave_u hY z, analyticAt_reconWave_ux hY z,
      analyticAt_reconWave_uxx hY z, analyticAt_reconWave_ut hY z, analyticAt_reconWave_utt hY z⟩,
    hasDerivAt_reconWave_ut hY, fun t _ hx => hasDerivAt_reconWave_utt hY t hx,
    fun t x => hasDerivAt_reconWave_ux (Y t).1 x, isClassicalSolution_reconWave hY,
    fun t _ hx => reconWave_bound Y t hx⟩

end Curve

end KAM.Wave

end
