/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.SepLarge

/-!
# W7: the exceptional zones (blueprint `bpW:w7:Xzones`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

For `(k, l) ∈ X` the function `g_{kl} = ⟨k, ω⁰⟩ + ⟨l, Ω⁰⟩` is affine and not identically zero
(condition (A₃), `KAM.Wave.A3_holds`): the zone is empty if `p_{kl} = 0`, and of measure
`≤ 4 ρ_ζ a K_* / (ϑ σ_X D_A)` otherwise.
-/

@[expose] public noncomputable section

open Real Finsupp MeasureTheory

namespace KAM.Wave

section

variable (m : ℝ) (hm : 0 < m)
variable {Pi : Set (Fin 2 → ℝ)} {α : ℝ} {D : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ → ℝ} {εω ε1 ε2 θ : ℝ}

theorem theta_mul_LA_X {θ : ℝ} (hθ : θ ≤ measTheta0 m hm) :
    θ * measLA m hm * (measKstar m hm + 2) ≤ measSigmaX m hm / 2 := by
  have hLA := measLA_pos m hm
  have hK : 0 < measKstar m hm + 2 := by linarith [measKstar_pos m hm]
  unfold measTheta0 at hθ
  have h1 : θ * measLA m hm ≤ min (1 / 8) (measSigmaX m hm / (2 * (measKstar m hm + 2))) := by
    have := mul_le_mul_of_nonneg_right hθ hLA.le
    have h2 : (measLA m hm)⁻¹ * min (1 / 8) (measSigmaX m hm / (2 * (measKstar m hm + 2))) *
        measLA m hm = min (1 / 8) (measSigmaX m hm / (2 * (measKstar m hm + 2))) := by
      field_simp
    rwa [h2] at this
  have h3 := h1.trans (min_le_right _ _)
  calc θ * measLA m hm * (measKstar m hm + 2) ≤
        measSigmaX m hm / (2 * (measKstar m hm + 2)) * (measKstar m hm + 2) :=
        mul_le_mul_of_nonneg_right h3 hK.le
    _ = measSigmaX m hm / 2 := by field_simp

/-- Drift Lipschitz bound. -/
theorem IsFreqPair.drift_lip (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {ξ ξ' : Fin 2 → ℝ}
    (hξ : ξ ∈ D) (hξ' : ξ' ∈ D) (l : ℕ →₀ ℤ) :
    |(linF l (Ω ξ) - linF l (omegaNor m hm ξ)) - (linF l (Ω ξ') - linF l (omegaNor m hm ξ'))| ≤
      θ * absWt l (-(1 / 2 : ℝ)) * ‖ξ - ξ'‖ := by
  have e : (linF l (Ω ξ) - linF l (omegaNor m hm ξ)) - (linF l (Ω ξ') - linF l (omegaNor m hm ξ')) =
      l.sum fun ν v => (v : ℝ) * ((Ω ξ ν - omegaNor m hm ξ ν) - (Ω ξ' ν - omegaNor m hm ξ' ν)) := by
    rw [← linF_sub l (fun ν => (Ω ξ ν - omegaNor m hm ξ ν))
      (fun ν => (Ω ξ' ν - omegaNor m hm ξ' ν))]
    simp only [linF_sub']
  rw [e]
  have := abs_linF_le_absWt l (fun ν => (Ω ξ ν - omegaNor m hm ξ ν) - (Ω ξ' ν - omegaNor m hm ξ' ν))
    (fun ν => θ * normLab ν ^ (-(1 / 2 : ℝ)) * ‖ξ - ξ'‖) (fun ν => by
      simpa using hP.h2_lip ξ hξ ξ' hξ' ν)
  refine this.trans (le_of_eq ?_)
  unfold absWt Finsupp.sum
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun ν _ => by ring

theorem IsFreqPair.continuousOn_zoneFun (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ)
    (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) :
    ContinuousOn (fun ξ => ∑ i, (k i : ℝ) * ω ξ i + linF l (Ω ξ)) D := by
  have h1 : ContinuousOn (fun ξ => ∑ i, (k i : ℝ) * ω ξ i) D := by
    set C := kAbs k * measNA m hm + θ * kAbs k + kAbs k / 8 * measNA m hm with hC
    have hlip := LipschitzOnWith.of_dist_le' (K := C) (f := fun ξ => ∑ i, (k i : ℝ) * ω ξ i)
      (s := D) (fun x hx y hy => by
      rw [Real.dist_eq, dist_eq_norm]
      have := (hP.zone_diff_bounds m hm (fun _ => (0 : ℝ)) (fun ξ _ ξ' _ => by
        simp only [sub_self, abs_zero]
        have := kAbs_nonneg k
        positivity) hx hy).1
      simpa using this)
    exact hlip.continuousOn
  have h2 : ContinuousOn (fun ξ => linF l (Ω ξ)) D := by
    set C := measCLam m hm * absWt l (-(1 / 2 : ℝ)) * measNA m hm with hC
    have hlip := LipschitzOnWith.of_dist_le' (K := C) (f := fun ξ => linF l (Ω ξ)) (s := D)
      (fun x hx y hy => by
      rw [Real.dist_eq, dist_eq_norm]
      have h := hP.linF_lip m hm hx hy l
      have h' := norm_omegaTan_sub_le m hm x y
      have hc := measCLam_pos m hm
      have hw := absWt_nonneg l (-(1 / 2 : ℝ))
      calc _ ≤ _ := h
        _ ≤ measCLam m hm * absWt l (-(1 / 2 : ℝ)) * (measNA m hm * ‖x - y‖) :=
            mul_le_mul_of_nonneg_left h' (by positivity)
        _ = _ := by rw [hC]; ring)
    exact hlip.continuousOn
  exact h1.add h2

/-- `(k, l) ∈ X` with `p_{kl} = 0`: the zone is empty (blueprint `bpW:w7:Xzones`). -/
theorem IsFreqPair.Xzone_empty (hS : MeasSetup m hm Pi α)
    (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ alphaHat α)
    {k : Fin 2 → ℤ} {l : ℕ →₀ ℤ} (hx : (k, l) ∈ measXSet m hm) (hp : measPX m hm k l = 0) :
    zoneSet D ω Ω a k l = ∅ := by
  have hx0 := hx
  obtain ⟨hl, hk1, hkK, hjK, -⟩ := hx
  obtain ⟨-, -, hαhat, -, -, hαc⟩ := alpha_facts m hm hS.alpha_pos hS.alpha_le
  have hcX := measCX_le m hm hx0 hp
  have hcX0 := measCX_pos m hm
  have hϑ := measTheta_pos m hm
  have hϑ1 := measTheta_le m hm
  have hK := measKstar_pos m hm
  ext ξ
  simp only [zoneSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
  intro hξ
  -- the affine function is constant
  have hg : affineForm m hm k l ξ = affineForm m hm k l 0 := by
    rw [affineForm_eq]; simp [hp]
  have hg0 : |affineForm m hm k l 0| = measCval m hm k l := (measCval_eq m hm k l).symm
  have hdiff : |(∑ i, (k i : ℝ) * ω ξ i + linF l (Ω ξ)) - affineForm m hm k l ξ| ≤
      (measKstar m hm + 4) * alphaHat α := by
    have e : (∑ i, (k i : ℝ) * ω ξ i + linF l (Ω ξ)) - affineForm m hm k l ξ =
        ∑ i, (k i : ℝ) * (ω ξ - omegaTan m hm ξ) i + (linF l (Ω ξ) - linF l (omegaNor m hm ξ)) := by
      unfold affineForm
      simp only [_root_.Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h1 := abs_sum_k_mul_le k (ω ξ - omegaTan m hm ξ)
    have h2 := hP.drift_le_two m hm hξ hl
    have h3 := hP.h1_sup ξ hξ
    have e1 := hP.ε1_mem.2
    have e2 := hP.ε2_mem.2
    have e3 := hP.εω_mem.2
    have hk0 := kAbs_nonneg k
    have hn : ‖ω ξ - omegaTan m hm ξ‖ * kAbs k ≤ α * measKstar m hm := by
      calc _ ≤ εω * kAbs k := mul_le_mul_of_nonneg_right h3 hk0
        _ ≤ α * kAbs k := mul_le_mul_of_nonneg_right e3 hk0
        _ ≤ α * measKstar m hm := mul_le_mul_of_nonneg_left hkK.le hS.alpha_pos.le
    nlinarith
  have hbound : (measKstar m hm + 4) * alphaHat α ≤ measCX m hm / 2 := by
    have h1 : alphaHat α * (4 * measKstar m hm * (measKstar m hm + 4)) ≤ measTheta m hm * measCX m
        hm := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * measKstar m hm * (measKstar m hm + 4))).1
                                 hαc
      exact this
    nlinarith [mul_pos hϑ hcX0]
  have hzone : a * japL l / kAk k ≤ measCX m hm / 4 := by
    have hk1' := kAk_pos k
    have : a * japL l / kAk k ≤ alphaHat α * (measKstar m hm / measTheta m hm) := by
      calc a * japL l / kAk k ≤ a * japL l := div_le_self (by have := japL_ge_one l; positivity)
                                                                hk1'
        _ ≤ alphaHat α * (measKstar m hm / measTheta m hm) :=
            mul_le_mul ha hjK.le (by linarith [japL_ge_one l]) (by linarith [measAlphaM_pos m hm])
    refine this.trans ?_
    have h1 : alphaHat α * (4 * measKstar m hm * (measKstar m hm + 4)) ≤ measTheta m hm * measCX m
        hm :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * measKstar m hm * (measKstar m hm + 4))).1 hαc
    rw [mul_div_assoc', div_le_iff₀ hϑ]
    nlinarith [mul_pos (by linarith : (0 : ℝ) < measKstar m hm) hcX0]
  have hsum : measCX m hm ≤ |affineForm m hm k l ξ| := by
    rw [hg]; rw [hg0]; exact hcX
  have := abs_sub_abs_le_abs_sub (affineForm m hm k l ξ)
    (affineForm m hm k l ξ - (∑ i, (k i : ℝ) * ω ξ i + linF l (Ω ξ)))
  have h2 : |affineForm m hm k l ξ - (∑ i, (k i : ℝ) * ω ξ i + linF l (Ω ξ))| ≤
      (measKstar m hm + 4) * alphaHat α := by rw [abs_sub_comm]; exact hdiff
  have h3 : |∑ i, (k i : ℝ) * ω ξ i + linF l (Ω ξ)| ≥ measCX m hm / 2 := by
    have := abs_sub_abs_le_abs_sub (affineForm m hm k l ξ)
      (affineForm m hm k l ξ - (∑ i, (k i : ℝ) * ω ξ i + linF l (Ω ξ)))
    simp only [sub_sub_cancel] at this
    linarith
  linarith


/-- `(k, l) ∈ X` with `p_{kl} ≠ 0`: measure of the zone (blueprint `bpW:w7:Xzones`). -/
theorem IsFreqPair.Xzone_measure_le
    (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {a : ℝ} (ha0 : 0 < a)
    {k : Fin 2 → ℤ} {l : ℕ →₀ ℤ} (hx : (k, l) ∈ measXSet m hm) (hp : measPX m hm k l ≠ 0)
    {ρζ : ℝ} (hρ0 : 0 ≤ ρζ)
    (hρζ : ∀ ξ ∈ D, ∀ ξ' ∈ D, ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤ ρζ) :
    MeasurableSet (zoneSet D ω Ω a k l) ∧
      volume (zoneSet D ω Ω a k l) ≤ ENNReal.ofReal
        (4 * ρζ * a * measKstar m hm / (measTheta m hm * measSigmaX m hm * measDA m hm)) := by
  have hx0 := hx
  obtain ⟨hl, hk1, hkK, hjK, -⟩ := hx
  have hσ := measSigmaX_le m hm hx0 hp
  have hσ0 := measSigmaX_pos m hm
  have hϑ := measTheta_pos m hm
  have hDA := measDA_pos m hm
  have hLA := measLA_pos m hm
  have hK := measKstar_pos m hm
  have hθ0 := hP.θ_mem.1
  have hθX := theta_mul_LA_X m hm hP.θ_mem.2
  set p := measPX m hm k l with hpdef
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, ‖p‖ ≤ |p i| := by
    rcases le_total |p 1| |p 0| with h | h
    · refine ⟨0, ?_⟩
      rw [pi_norm_le_iff_of_nonneg (abs_nonneg _)]
      intro j; fin_cases j <;> simp [h]
    · refine ⟨1, ?_⟩
      rw [pi_norm_le_iff_of_nonneg (abs_nonneg _)]
      intro j; fin_cases j <;> simp [h]
  have hpi : measSigmaX m hm ≤ |p i| := hσ.trans hi
  set F : (Fin 2 → ℝ) → ℝ := fun ξ => ∑ j, (k j : ℝ) * ω ξ j + linF l (Ω ξ) with hF
  have hcont : ContinuousOn F D := hP.continuousOn_zoneFun m hm k l
  set η := a * japL l / kAk k with hη
  have hj1 := japL_ge_one l
  have hA1 := kAk_pos k
  have hηpos : 0 < η := by positivity
  have hgrow : ∀ ξ ∈ D, ∀ ξ' ∈ D,
      (∀ j, j ≠ i → omegaTan m hm ξ j = omegaTan m hm ξ' j) →
      measSigmaX m hm / 2 * |omegaTan m hm ξ i - omegaTan m hm ξ' i| ≤ |F ξ - F ξ'| := by
    intro ξ hξ ξ' hξ' hsame
    set d : Fin 2 → ℝ := omegaTan m hm ξ - omegaTan m hm ξ' with hd
    set e : Fin 2 → ℝ := (ω ξ - omegaTan m hm ξ) - (ω ξ' - omegaTan m hm ξ') with he
    have hdi : ∀ j, j ≠ i → d j = 0 := fun j hj => by
      simp only [hd, _root_.Pi.sub_apply]; rw [hsame j hj]; ring
    have hdnorm : ‖d‖ ≤ |d i| := by
      rw [pi_norm_le_iff_of_nonneg (abs_nonneg _)]
      intro j
      by_cases hj : j = i
      · subst hj; simp
      · rw [hdi j hj]; simp
    have hdi' : d i = omegaTan m hm ξ i - omegaTan m hm ξ' i := by simp [hd]
    have hΔ : ‖ξ - ξ'‖ ≤ measLA m hm * |d i| :=
      (norm_sub_le_measLA_mul m hm ξ ξ').trans (mul_le_mul_of_nonneg_left hdnorm hLA.le)
    -- the affine part
    have hsum : ∑ j, p j * d j = p i * d i :=
      Finset.sum_eq_single i (fun j _ hj => by rw [hdi j hj, mul_zero]) (by simp)
    have hg : affineForm m hm k l ξ - affineForm m hm k l ξ' = p i * d i := by
      rw [affineForm_eq m hm k l ξ, affineForm_eq m hm k l ξ', ← hsum]
      simp only [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, hd, _root_.Pi.sub_apply]
      exact Finset.sum_congr rfl fun j _ => by ring
    -- the remainder
    have hrem : |(F ξ - affineForm m hm k l ξ) - (F ξ' - affineForm m hm k l ξ')| ≤
        measSigmaX m hm / 2 * |d i| := by
      have e1 : (F ξ - affineForm m hm k l ξ) - (F ξ' - affineForm m hm k l ξ') =
          ∑ j, (k j : ℝ) * e j +
            ((linF l (Ω ξ) - linF l (omegaNor m hm ξ)) -
              (linF l (Ω ξ') - linF l (omegaNor m hm ξ'))) := by
        simp only [hF, affineForm, he, _root_.Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
        ring
      rw [e1]
      refine (abs_add_le _ _).trans ?_
      have b1 := abs_sum_k_mul_le k e
      have b2 : ‖e‖ ≤ θ * ‖ξ - ξ'‖ := hP.h1_lip ξ hξ ξ' hξ'
      have b3 := hP.drift_lip m hm hξ hξ' l
      have b4 := absWt_le_two hl (δ := -(1 / 2 : ℝ)) (by norm_num)
      have b5 := absWt_nonneg l (-(1 / 2 : ℝ))
      have hk0 := kAbs_nonneg k
      have hΔ0 := norm_nonneg (ξ - ξ')
      have c1 : ‖e‖ * kAbs k ≤ θ * ‖ξ - ξ'‖ * measKstar m hm :=
        mul_le_mul b2 hkK.le hk0 (by positivity)
      have c2 : θ * absWt l (-(1 / 2 : ℝ)) * ‖ξ - ξ'‖ ≤ θ * 2 * ‖ξ - ξ'‖ := by gcongr
      have c3 : θ * ‖ξ - ξ'‖ * (measKstar m hm + 2) ≤ θ * (measLA m hm * |d i|) * (measKstar m hm +
          2) := by
        gcongr
      have c4 : θ * (measLA m hm * |d i|) * (measKstar m hm + 2) =
          θ * measLA m hm * (measKstar m hm + 2) * |d i| := by ring
      have c5 : θ * measLA m hm * (measKstar m hm + 2) * |d i| ≤ measSigmaX m hm / 2 * |d i| :=
        mul_le_mul_of_nonneg_right hθX (abs_nonneg _)
      nlinarith
    have hmain : |affineForm m hm k l ξ - affineForm m hm k l ξ'| ≥ measSigmaX m hm * |d i| := by
      rw [hg, abs_mul]
      exact mul_le_mul_of_nonneg_right hpi (abs_nonneg _)
    have hdecomp : F ξ - F ξ' = (affineForm m hm k l ξ - affineForm m hm k l ξ') +
        ((F ξ - affineForm m hm k l ξ) - (F ξ' - affineForm m hm k l ξ')) := by ring
    rw [← hdi', hdecomp]
    have := abs_sub_abs_le_abs_sub (affineForm m hm k l ξ - affineForm m hm k l ξ')
      (-((F ξ - affineForm m hm k l ξ) - (F ξ' - affineForm m hm k l ξ')))
    rw [abs_neg, sub_neg_eq_add] at this
    nlinarith [abs_nonneg (d i)]
  have hmeas := measure_abs_lt_le_of_growth m hm hP.meas hcont i (σ := measSigmaX m hm / 2)
    (ρζ := ρζ) (η := η) (by positivity) hηpos hρζ hgrow
  refine ⟨hmeas.1, hmeas.2.trans ?_⟩
  refine ENNReal.ofReal_le_ofReal ?_
  have hηle : η ≤ a * measKstar m hm / measTheta m hm := by
    calc η ≤ a * japL l := div_le_self (by positivity) hA1
      _ ≤ a * (measKstar m hm / measTheta m hm) := mul_le_mul_of_nonneg_left hjK.le ha0.le
      _ = _ := by ring
  calc 2 * η * ρζ / (measSigmaX m hm / 2 * measDA m hm)
      = 4 * η * ρζ / (measSigmaX m hm * measDA m hm) := by field_simp; ring
    _ ≤ 4 * (a * measKstar m hm / measTheta m hm) * ρζ / (measSigmaX m hm * measDA m hm) := by
        gcongr
    _ = _ := by field_simp

end

end KAM.Wave

end
