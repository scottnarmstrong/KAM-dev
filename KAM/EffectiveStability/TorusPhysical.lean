/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusStep

/-!
# Physical (original-coordinate) action box and action drift for the torus step (track B, B4-TORIG)

* `torusFlow_coord_sub_le`: coordinatewise displacement of the real torus flow in the gauge
  `scaleCLE ρ' σ'`: angles `≤ |t| ε σ'`, actions `≤ |t| ε ρ'`;
* `torusChart_sub_le`, `torusChartInv_sub_le`: the same for `Ψ` and `Ψinv` on the real cylinder;
* `torusChart_torusChartInv`: `Ψ (Ψinv z) = z` on the closed real cylinder;
* `torusStep_physical`: the physical-coordinate version of `torusStep_confinement`. The physical
  actions are the observable `A = snd` with `L = id` and `d = ε ρ'`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set KAM.Canonical

variable {n : ℕ}

/-- The finite majorant checks give the small-field hypothesis for the torus generator. -/
private theorem torus_smallField {χ : FTPoly} (hχ : FTFits n χ) {σ ρ σ' ρ' ε : ℝ}
    (hσ' : 0 < σ') (hρ' : 0 < ρ') (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) {πub lam : ℚ}
    (hπ : Real.pi ≤ ((πub : ℚ) : ℝ)) (hσ0 : 0 ≤ σ) (hx : 2 * ((πub : ℚ) : ℝ) * σ < 1)
    (hlam : 1 / (1 - 2 * ((πub : ℚ) : ℝ) * σ) ≤ ((lam : ℚ) : ℝ))
    (ρl : List ℚ) (hρl : ∀ i : Fin n, ((ρl.getD i 0 : ℚ) : ℝ) = ρ)
    (hJ : ∀ i : Fin n, ((ftSupBound (ftDJ i χ) πub lam ρl : ℚ) : ℝ) ≤ ε * σ')
    (hφ : ∀ i : Fin n, ((ftSupBound (ftDφ i χ) πub lam ρl : ℚ) : ℝ) ≤ ε * ρ') :
    SmallField (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ)
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w)) ε := by
  have hlam0 : 0 < lam := by
    have h1 : 0 < 1 - 2 * ((πub : ℚ) : ℝ) * σ := by linarith
    have : (0 : ℝ) < ((lam : ℚ) : ℝ) := lt_of_lt_of_le (by positivity) hlam
    exact_mod_cast this
  exact smallField_of_ftBounds hχ hσ' hρ' hπ hlam0 (strip_le_log_lam hπ hσ0 hx hlam) ρl hρl
    hε0 hε hJ hφ

/-- Coordinatewise real displacement of the time-`t` real torus flow, `|t| ≤ 1`: angles move by
at most `|t| ε σ'`, actions by at most `|t| ε ρ'`. -/
theorem torusFlow_coord_sub_le {χ : FTPoly} {σ ρ σ' ρ' ε : ℝ} (hσ' : 0 < σ') (hρ' : 0 < ρ')
    (hS : SmallField (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ)
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w)) ε)
    {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    ∀ i, |(realFlow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w) (cstripOpen σ ρ) t x).1 i
        - x.1 i| ≤ |t| * ε * σ' ∧
      |(realFlow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w) (cstripOpen σ ρ) t x).2 i
        - x.2 i| ≤ |t| * ε * ρ' := by
  have hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ cstripOpen σ ρ →
      (ftEvalC χ (KAM.realInclusion₂ n x)).im = 0 := fun x _ => ftEvalC_realInclusion₂_im χ x
  have hφd := (ftEvalC_differentiable (n := n) χ).differentiableOn (s := cstripOpen σ ρ)
  have h := norm_realFlow_sub_le (isOpen_cstripOpen σ ρ) hφd hS hreal hx ht
  set y := realFlow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w) (cstripOpen σ ρ) t x
  rw [norm_scaleCLE, scaledNorm, max_le_iff, div_le_iff₀ hσ', div_le_iff₀ hρ'] at h
  intro i
  have h1 : ‖(KAM.realInclusion₂ n y - KAM.realInclusion₂ n x).1 i‖ ≤ |t| * ε * σ' :=
    (norm_le_pi_norm _ i).trans h.1
  have h2 : ‖(KAM.realInclusion₂ n y - KAM.realInclusion₂ n x).2 i‖ ≤ |t| * ε * ρ' :=
    (norm_le_pi_norm _ i).trans h.2
  simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, KAM.realInclusion₂_apply,
    KAM.realInclusion_apply, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h1 h2
  exact ⟨h1, h2⟩

/-- Displacement of the torus chart `Ψ` on the half real interior. -/
theorem torusChart_sub_le {χ : FTPoly} {σ ρ σ' ρ' ε : ℝ} (hσ' : 0 < σ') (hρ' : 0 < ρ')
    (hS : SmallField (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ)
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w)) ε)
    {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2)) :
    ∀ i, |(torusChart χ σ ρ x).1 i - x.1 i| ≤ ε * σ' ∧
      |(torusChart χ σ ρ x).2 i - x.2 i| ≤ ε * ρ' := by
  intro i
  have := torusFlow_coord_sub_le hσ' hρ' hS hx (t := 1) ⟨by norm_num, le_rfl⟩ i
  simpa [torusChart] using this

/-- Displacement of the inverse torus chart `Ψinv` on the half real interior. -/
theorem torusChartInv_sub_le {χ : FTPoly} {σ ρ σ' ρ' ε : ℝ} (hσ' : 0 < σ') (hρ' : 0 < ρ')
    (hS : SmallField (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ)
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w)) ε)
    {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2)) :
    ∀ i, |(torusChartInv χ σ ρ x).1 i - x.1 i| ≤ ε * σ' ∧
      |(torusChartInv χ σ ρ x).2 i - x.2 i| ≤ ε * ρ' := by
  intro i
  have := torusFlow_coord_sub_le hσ' hρ' hS hx (t := -1) ⟨le_rfl, by norm_num⟩ i
  simpa [torusChartInv] using this

/-- `Ψ (Ψinv z) = z` for real `z` in `realInterior W Ω 1`. -/
theorem torusChart_torusChartInv {χ : FTPoly} {σ ρ σ' ρ' ε : ℝ} (hσ' : 0 < σ') (hρ' : 0 < ρ')
    (hS : SmallField (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ)
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w)) ε)
    {z : (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : z ∈ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) 1) :
    torusChart χ σ ρ (torusChartInv χ σ ρ z) = z :=
  realFlow_one_realFlow_neg (isOpen_cstripOpen σ ρ)
    ((ftEvalC_differentiable (n := n) χ).differentiableOn (s := cstripOpen σ ρ)) hS
    (fun x _ => ftEvalC_realInclusion₂_im χ x) hz

/-- **Physical one-step torus confinement** (track B, B4-TORIG): the premises of
`torusStep_confinement`, plus a physical action box `a'` with `a' i + ε ρ' ≤ a i` and
`a' i + ρ' < ρ`. For every physical `z₀` with `|z₀.2 j| ≤ a' j`, the physical flow exists, is
unique, and the PHYSICAL actions drift by at most `2 ε ρ' + η |t|` on `|t| ≤ T`. -/
theorem torusStep_physical {H χ Nact P : FTPoly}
    (hH : FTFits n H) (hχ : FTFits n χ) (hP : FTFits n P)
    (hA : ftActOnly Nact = true) {L : ℕ} (hL : 1 ≤ L)
    (hid : ftEqCheck (ftLieSum χ H L) (ftAdd Nact P) = true)
    {σ ρ σ' ρ' δc ε : ℝ} (hσ' : 0 < σ') (hρ' : 0 < ρ') (hδc : 0 < δc) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) {πub lam : ℚ} (hπ : Real.pi ≤ ((πub : ℚ) : ℝ))
    (hx : 2 * ((πub : ℚ) : ℝ) * σ < 1)
    (hlam : 1 / (1 - 2 * ((πub : ℚ) : ℝ) * σ) ≤ ((lam : ℚ) : ℝ))
    (ρl : List ℚ) (hρl : ∀ i : Fin n, ((ρl.getD i 0 : ℚ) : ℝ) = ρ)
    (hJ : ∀ i : Fin n, ((ftSupBound (ftDJ i χ) πub lam ρl : ℚ) : ℝ) ≤ ε * σ')
    (hφ : ∀ i : Fin n, ((ftSupBound (ftDφ i χ) πub lam ρl : ℚ) : ℝ) ≤ ε * ρ')
    (a b η : Fin n → ℝ) (εb T : ℝ) (hεb : 0 < εb) (hT : 0 ≤ T)
    (bl : List ℚ) (hbl : ∀ i : Fin n, ((bl.getD i 0 : ℚ) : ℝ) = b i)
    (r : Fin n → ℝ) (hbr : ∀ i, b i ≤ r i)
    (hσσ' : σ' < σ) (hdom1 : ∀ i, b i + εb + ρ' ≤ ρ) (hσc : δc + σ' / 2 < σ)
    (hr3 : ∀ i, r i + δc + ρ' / 2 < ρ) (hη : ∀ j, 0 ≤ η j)
    (hdrift : ∀ j : Fin n, ((ftAngleDriftBound P j πub bl : ℚ) : ℝ) +
      ((ftSupBound (ftAdPow χ L H) πub lam ρl : ℚ) : ℝ) / ((L.factorial : ℝ) * δc) ≤ η j)
    (hmargin : ∀ j, a j + T * η j < b j)
    (a' : Fin n → ℝ) (hpa : ∀ i, a' i + ε * ρ' ≤ a i) (hpρ : ∀ i, a' i + ρ' < ρ)
    (z₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hz₀ : ∀ j, |z₀.2 j| ≤ a' j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = z₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
        HasDerivAt z (KAM.hamiltonianVectorField
          (fun w : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR H w) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = z₀ →
        (∀ t ∈ I, y t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
          HasDerivAt y (KAM.hamiltonianVectorField
            (fun w : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR H w) (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → ∀ j,
        |(z t).2 j - z₀.2 j| ≤ 2 * (ε * ρ') + η j * |t| ∧
          |(z t).2 j| ≤ a j + η j * T + ε * ρ' := by
  have hσ0 : 0 ≤ σ := by linarith
  have hS := torus_smallField hχ hσ' hρ' hε0 hε hπ hσ0 hx hlam ρl hρl hJ hφ
  have hab : ∀ j, a j ≤ b j := fun j => by
    have := mul_nonneg hT (hη j)
    linarith [hmargin j]
  have hdomc : ∀ i, b i + ρ' < ρ := fun i => by linarith [hdom1 i]
  have hz₀I : z₀ ∈ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) 1 :=
    cylClosed_subset_realInterior_cstrip hρ' hσ' hσσ' hpρ hz₀
  have hz₀I2 : z₀ ∈ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2) :=
    realInterior_mono (by norm_num) hz₀I
  set w₀ := torusChartInv χ σ ρ z₀ with hw₀def
  have hdisp0 := torusChartInv_sub_le hσ' hρ' hS hz₀I2
  have hΨw₀ : torusChart χ σ ρ w₀ = z₀ := torusChart_torusChartInv hσ' hρ' hS hz₀I
  have hw₀a : ∀ j, |w₀.2 j| ≤ a j := fun j => by
    have h1 := (hdisp0 j).2
    have e : |w₀.2 j| ≤ |z₀.2 j| + |w₀.2 j - z₀.2 j| := by
      simpa using abs_add_le (z₀.2 j) (w₀.2 j - z₀.2 j)
    linarith [hz₀ j, hpa j]
  obtain ⟨T₁, hT₁, z, hz0, hode, huniq, hb⟩ := torusStep_confinement hH hχ hP hA hL hid hσ' hρ'
    hδc hε0 hε hπ hx hlam ρl hρl hJ hφ a b η εb T hεb hT bl hbl r hbr hσσ' hdom1 hσc hr3 hη
    hdrift hmargin w₀ hw₀a
  rw [hΨw₀] at hz0
  refine ⟨T₁, hT₁, z, hz0, hode, fun I y hI h0 hy0 hyd t htI htT => huniq I y hI h0
    (by rw [hΨw₀]; exact hy0) hyd t htI htT, fun t ht j => ?_⟩
  obtain ⟨hinv, hbd⟩ := hb t ht
  set u := torusChartInv χ σ ρ (z t) with hu
  have hbj : ∀ k, |u.2 k| ≤ b k := fun k => by
    have h2 := mul_le_mul_of_nonneg_left ht (hη k)
    have h3 := hmargin k
    have := (hbd k).2
    nlinarith [mul_comm T (η k)]
  have huI : u ∈ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2) :=
    realInterior_mono (by norm_num) (cylClosed_subset_realInterior_cstrip hρ' hσ' hσσ' hdomc hbj)
  have hdispu := torusChart_sub_le hσ' hρ' hS huI
  rw [show torusChart χ σ ρ u = z t from hinv] at hdispu
  have p1 := (hdispu j).2
  have p2 := (hdisp0 j).2
  have c1 := abs_le.1 (hbd j).1
  have c2 := (hbd j).2
  have q1 := abs_le.1 p1
  have q2 := abs_le.1 p2
  have ub : |(z t).2 j| ≤ |u.2 j| + |(z t).2 j - u.2 j| := by
    simpa using abs_add_le (u.2 j) ((z t).2 j - u.2 j)
  constructor
  · rw [abs_le]; constructor <;> nlinarith [c1.1, c1.2, q1.1, q1.2, q2.1, q2.2]
  · linarith

end KAM.EffectiveStability

end
