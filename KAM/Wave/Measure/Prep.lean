/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.PrepMinus

/-!
# W7: the preparatory zones (blueprint `bpW:w7:prep`)

`volume Ξ ≤ C_P ρ_ζ D_A⁻¹ α̂^{8/11}`.
-/

@[expose] public noncomputable section

open Real Finsupp MeasureTheory

namespace KAM.Wave

section

variable (m : ℝ) (hm : 0 < m)
variable {Pi : Set (Fin 2 → ℝ)} {α : ℝ}

/-- The per-`k` real bound of the preparatory zones. -/
theorem prep_perk_real {a ρ DA ϑ aκ : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hρ : 0 ≤ ρ) (hDA : 0 < DA)
    (hϑ : 0 < ϑ) (hκ : 0 < aκ) {k : Fin 2 → ℤ} (hk : k ≠ 0) :
    8 * (a / kAk k) * ρ / (kAbs k * DA) + 32 * a * ρ * kAbs k ^ 2 / (ϑ ^ 3 * kAk k * DA) +
      2 * (8 * ρ * (3 + aκ) * (a / kAk k) ^ (8 / 11 : ℝ) / (kAbs k * DA) *
        (kAbs k / ϑ) ^ 2) ≤
      (ρ / DA * a ^ (8 / 11 : ℝ) * (8 + 32 * (ϑ⁻¹) ^ 3 + 16 * (3 + aκ) * (ϑ⁻¹) ^ 2)) /
        kAbs k ^ 3 := by
  have hk1 := one_le_kAbs hk
  have hkpos : 0 < kAbs k := by linarith
  have hA := kAk_pos k
  have hApos : 0 < kAk k := by linarith
  have ha8 : a ≤ a ^ (8 / 11 : ℝ) := by
    calc a = a ^ (1 : ℝ) := (Real.rpow_one a).symm
      _ ≤ a ^ (8 / 11 : ℝ) := Real.rpow_le_rpow_of_exponent_ge ha0 ha1 (by norm_num)
  have ha8pos : 0 < a ^ (8 / 11 : ℝ) := Real.rpow_pos_of_pos ha0 _
  have p2 := pow_le_kAk_rpow hk (e := 2) (s := 1) (by norm_num) (by norm_num)
  have p5 := pow_le_kAk_rpow hk (e := 5) (s := 1) (by norm_num) (by norm_num)
  have p4 := pow_le_kAk_rpow hk (e := 4) (s := 8 / 11) (by norm_num) (by norm_num)
  rw [Real.rpow_one] at p2 p5
  have hA8 : 0 < kAk k ^ (8 / 11 : ℝ) := Real.rpow_pos_of_pos hApos _
  have hdiv : (a / kAk k) ^ (8 / 11 : ℝ) = a ^ (8 / 11 : ℝ) / kAk k ^ (8 / 11 : ℝ) :=
    Real.div_rpow ha0.le hApos.le _
  have hk3 : 0 < kAbs k ^ 3 := by positivity
  set u3 : ℝ := (kAbs k ^ 3)⁻¹ with hu3
  have hu3pos : 0 < u3 := by positivity
  have hu3e : ∀ x : ℝ, x / kAbs k ^ 3 = x * u3 := fun x => by rw [hu3, div_eq_mul_inv]
  have f1 : (kAbs k * kAk k)⁻¹ ≤ u3 := inv_anti₀ hk3 (by nlinarith [pow_pos hkpos 2])
  have f2 : kAbs k ^ 2 / kAk k ≤ u3 := by
    rw [div_le_iff₀ hApos]
    calc kAbs k ^ 2 = u3 * kAbs k ^ 5 := by rw [hu3]; field_simp
      _ ≤ u3 * kAk k := mul_le_mul_of_nonneg_left p5 hu3pos.le
  have f3 : kAbs k / kAk k ^ (8 / 11 : ℝ) ≤ u3 := by
    rw [div_le_iff₀ hA8]
    calc kAbs k = u3 * kAbs k ^ 4 := by rw [hu3]; field_simp
      _ ≤ u3 * kAk k ^ (8 / 11 : ℝ) := mul_le_mul_of_nonneg_left p4 hu3pos.le
  have e1 : 8 * (a / kAk k) * ρ / (kAbs k * DA) = (8 * a * ρ / DA) * (kAbs k * kAk k)⁻¹ := by
    field_simp
  have e2 : 32 * a * ρ * kAbs k ^ 2 / (ϑ ^ 3 * kAk k * DA) =
      (32 * a * ρ / (ϑ ^ 3 * DA)) * (kAbs k ^ 2 / kAk k) := by field_simp
  have e3 : 2 * (8 * ρ * (3 + aκ) * (a / kAk k) ^ (8 / 11 : ℝ) / (kAbs k * DA) *
        (kAbs k / ϑ) ^ 2) = (16 * ρ * (3 + aκ) * a ^ (8 / 11 : ℝ) / (ϑ ^ 2 * DA)) *
        (kAbs k / kAk k ^ (8 / 11 : ℝ)) := by
    rw [hdiv]; field_simp; ring
  rw [e1, e2, e3, hu3e]
  have c1 : 0 ≤ 8 * a * ρ / DA := by positivity
  have c2 : 0 ≤ 32 * a * ρ / (ϑ ^ 3 * DA) := by positivity
  have c3 : 0 ≤ 16 * ρ * (3 + aκ) * a ^ (8 / 11 : ℝ) / (ϑ ^ 2 * DA) := by positivity
  calc (8 * a * ρ / DA) * (kAbs k * kAk k)⁻¹ + (32 * a * ρ / (ϑ ^ 3 * DA)) * (kAbs k ^ 2 / kAk k) +
        (16 * ρ * (3 + aκ) * a ^ (8 / 11 : ℝ) / (ϑ ^ 2 * DA)) * (kAbs k / kAk k ^ (8 / 11 : ℝ))
      ≤ (8 * a * ρ / DA) * u3 + (32 * a * ρ / (ϑ ^ 3 * DA)) * u3 +
        (16 * ρ * (3 + aκ) * a ^ (8 / 11 : ℝ) / (ϑ ^ 2 * DA)) * u3 := by gcongr
    _ ≤ (8 * a ^ (8 / 11 : ℝ) * ρ / DA) * u3 + (32 * a ^ (8 / 11 : ℝ) * ρ / (ϑ ^ 3 * DA)) * u3 +
        (16 * ρ * (3 + aκ) * a ^ (8 / 11 : ℝ) / (ϑ ^ 2 * DA)) * u3 := by gcongr
    _ = _ := by field_simp

/-- The preparatory zones (blueprint `bpW:w7:prep`): `volume Ξ ≤ C_P ρ_ζ D_A⁻¹ α̂^{8/11}`. -/
theorem prepSet_measure_le (hS : MeasSetup m hm Pi α) {ρζ : ℝ} (hρ0 : 0 ≤ ρζ)
    (hρζ : ∀ ξ ∈ Pi, ∀ ξ' ∈ Pi, ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤ ρζ) :
    volume (prepSet m hm Pi α) ≤
      ENNReal.ofReal (measCP m hm * (ρζ / measDA m hm) * alphaHat α ^ (8 / 11 : ℝ)) := by
  classical
  obtain ⟨hc, hcA, hαhat, h27, hβ4, -⟩ := alpha_facts m hm hS.alpha_pos hS.alpha_le
  have hP := isFreqPair_unpert m hm hS.meas hS.alpha_pos.le
  have hα0 : 0 < alphaHat α := lt_of_lt_of_le hS.alpha_pos hαhat
  have ha1 : alphaHat α ≤ 1 := by linarith
  have hDA := measDA_pos m hm
  have hϑ := measTheta_pos m hm
  have hκ := measAKappa_pos hm
  have haβ : alphaHat α ≤ measBetaStar m := by have := measBetaStar_pos hm; linarith
  set a := alphaHat α with ha
  set Cs : ℝ := ρζ / measDA m hm * a ^ (8 / 11 : ℝ) *
    (8 + 32 * (measTheta m hm)⁻¹ ^ 3 + 16 * (3 + measAKappa m) * (measTheta m hm)⁻¹ ^ 2) with hCs
  set XP : Set (Fin 2 → ℝ) := ⋃ (kl : (Fin 2 → ℤ) × (ℕ →₀ ℤ)) (_ : kl ∈ measXSet m hm),
    zoneSet Pi (omegaTan m hm) (omegaNor m hm) a kl.1 kl.2 with hXP
  set Yk : (Fin 2 → ℤ) → Set (Fin 2 → ℝ) := fun k =>
    ((⋃ (_ : k ≠ 0), zoneSet Pi (omegaTan m hm) (omegaNor m hm) a k 0) ∪
      (⋃ (l : ℕ →₀ ℤ) (_ : IsLam l ∧ ¬ IsLamMinus l ∧ (k, l) ∉ measXSet m hm),
        zoneSet Pi (omegaTan m hm) (omegaNor m hm) a k l)) ∪
    minusUnion m hm (fun k l => prepZone m hm Pi a k l) k with hYk
  have hcover : prepSet m hm Pi α ⊆ XP ∪ ⋃ k, Yk k := by
    intro x hx
    simp only [prepSet, Set.mem_iUnion] at hx
    obtain ⟨k, l, ⟨hl0, hkl⟩, hxz⟩ := hx
    have hsubz := prepZone_subset m hm (Pi := Pi) hα0.le k l hxz
    by_cases hX : (k, l) ∈ measXSet m hm
    · left
      simp only [hXP, Set.mem_iUnion]
      exact ⟨(k, l), hX, hsubz⟩
    · right
      simp only [Set.mem_iUnion]
      refine ⟨k, ?_⟩
      rcases hl0 with rfl | hlam
      · rcases hkl with hk | hl
        · left; left
          simp only [Set.mem_iUnion]
          exact ⟨hk, hsubz⟩
        · exact absurd rfl hl
      · by_cases hmn : IsLamMinus l
        · right
          simp only [minusUnion, Set.mem_iUnion]
          exact ⟨l, ⟨hmn, hX⟩, hxz⟩
        · left; right
          simp only [Set.mem_iUnion]
          exact ⟨l, ⟨hlam, hmn, hX⟩, hsubz⟩
  -- the bound for each `k`
  have hZ0 : ∀ k : Fin 2 → ℤ, k = 0 → Yk k = ∅ := by
    intro k hk
    subst hk
    ext x
    simp only [hYk, Set.mem_union, Set.mem_iUnion, minusUnion, Set.mem_empty_iff_false, iff_false]
    rintro ((⟨h, _⟩ | ⟨l, ⟨hlam, _, _⟩, hz⟩) | ⟨l, ⟨hmn, _⟩, hz⟩)
    · exact h rfl
    · rw [zoneSet_zero_empty m hm hS hP (by linarith) hlam] at hz; exact hz
    · have := prepZone_subset m hm (Pi := Pi) hα0.le 0 l hz
      rw [zoneSet_zero_empty m hm hS hP (by linarith) (IsLam_of_minus hmn)] at this; exact this
  have hYbound : ∀ k : Fin 2 → ℤ, volume (Yk k) ≤
      (if k = 0 then 0 else ENNReal.ofReal (Cs / kAbs k ^ 3)) := by
    intro k
    by_cases hk : k = 0
    · rw [hZ0 k hk]; simp
    · simp only [hk, ↓reduceIte]
      have hk1 := one_le_kAbs hk
      have hA := kAk_pos k
      have h0 := hP.zone_bound_zero m hm hk hα0 hρζ
      have h1 := hP.plus_bound m hm hS hα0 le_rfl hρ0 hρζ hk
      have h2 := minus_assembly m hm (fun k l => prepZone m hm Pi a k l)
        (fun k l => prepZone_neg m hm a k l) hk (c1 := 8 * ρζ * (3 + measAKappa m) *
          (a / kAk k) ^ (8 / 11 : ℝ) / (kAbs k * measDA m hm)) (c0 := 0) (by positivity)
        le_rfl
        (fun k' hk' j n hne => by
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · simp only [Nat.cast_zero]; positivity
          · have hl : IsLam (lamMinusPlus j n) :=
              IsLam_of_minus ⟨j + n, j, 1, by omega, Or.inl rfl, rfl⟩
            have hz : (zoneSet Pi (omegaTan m hm) (omegaNor m hm) a k' (lamMinusPlus j n)).Nonempty
                :=
              hne.mono (prepZone_subset m hm (Pi := Pi) hα0.le k' _)
            have := hP.largek m hm hS hα0.le haβ hl hz
            have hj : japL (lamMinusPlus j n) = n := by
              have := japL_minus (i := j + n) (j := j) (σ := 1) (by omega) (Or.inl rfl)
              unfold lamMinusPlus
              rw [show (-1 : ℤ) = -(1 : ℤ) by norm_num, this]; push_cast; ring
            rw [hj, hk'] at this
            rw [le_div_iff₀ hϑ]; linarith)
        (fun k' hk' n hn1 hn2 => by
          have hk'0 : k' ≠ 0 := by
            intro h; rw [h] at hk'
            have : kAbs (0 : Fin 2 → ℤ) = 0 := by simp [kAbs]
            linarith
          have hAk : kAk k' = kAk k := by simp [kAk, hk']
          have := prep_minus_n_bound m hm hS hρ0 hρζ hk'0 hn1
          rw [hAk, hk'] at this
          simpa using this)
      have hu : (⋃ (_ : k ≠ 0), zoneSet Pi (omegaTan m hm) (omegaNor m hm) a k 0) =
          zoneSet Pi (omegaTan m hm) (omegaNor m hm) a k 0 := by
        ext x; simp only [Set.mem_iUnion]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hk, h⟩⟩
      calc volume (Yk k) ≤ volume (⋃ (_ : k ≠ 0), zoneSet Pi (omegaTan m hm) (omegaNor m hm) a k 0)
          +
            volume (⋃ (l : ℕ →₀ ℤ) (_ : IsLam l ∧ ¬ IsLamMinus l ∧ (k, l) ∉ measXSet m hm),
              zoneSet Pi (omegaTan m hm) (omegaNor m hm) a k l) +
            volume (minusUnion m hm (fun k l => prepZone m hm Pi a k l) k) :=
            (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
        _ ≤ ENNReal.ofReal (8 * (a / kAk k) * ρζ / (kAbs k * measDA m hm)) +
            ENNReal.ofReal (32 * a * ρζ * kAbs k ^ 2 /
              (measTheta m hm ^ 3 * kAk k * measDA m hm)) +
            ENNReal.ofReal (2 * (8 * ρζ * (3 + measAKappa m) * (a / kAk k) ^ (8 / 11 : ℝ) /
              (kAbs k * measDA m hm) * (kAbs k / measTheta m hm) ^ 2)) := by
            rw [hu]
            refine add_le_add (add_le_add h0 h1) (h2.trans (le_of_eq ?_))
            congr 1; ring
        _ = ENNReal.ofReal (8 * (a / kAk k) * ρζ / (kAbs k * measDA m hm) +
            32 * a * ρζ * kAbs k ^ 2 / (measTheta m hm ^ 3 * kAk k * measDA m hm) +
            2 * (8 * ρζ * (3 + measAKappa m) * (a / kAk k) ^ (8 / 11 : ℝ) /
              (kAbs k * measDA m hm) * (kAbs k / measTheta m hm) ^ 2)) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ ENNReal.ofReal (Cs / kAbs k ^ 3) := by
            refine ENNReal.ofReal_le_ofReal ?_
            exact prep_perk_real hα0 ha1 hρ0 hDA hϑ hκ hk
  -- assemble
  have hsum : ∑' k : Fin 2 → ℤ, volume (Yk k) ≤ ENNReal.ofReal (Cs * (2 * π ^ 2 / 3)) := by
    refine (ENNReal.tsum_le_tsum hYbound).trans (tsum_lattice_le ?_)
    have h8 : 0 ≤ ρζ / measDA m hm * a ^ (8 / 11 : ℝ) :=
      mul_nonneg (div_nonneg hρ0 hDA.le) (Real.rpow_nonneg hα0.le _)
    have h9 : 0 ≤ 8 + 32 * (measTheta m hm)⁻¹ ^ 3 + 16 * (3 + measAKappa m) * (measTheta m hm)⁻¹ ^
        2 := by
      have := inv_nonneg.2 hϑ.le
      positivity
    exact mul_nonneg h8 h9
  calc volume (prepSet m hm Pi α) ≤ volume (XP ∪ ⋃ k, Yk k) := measure_mono hcover
    _ ≤ volume XP + volume (⋃ k, Yk k) := measure_union_le _ _
    _ ≤ volume XP + ∑' k, volume (Yk k) := add_le_add le_rfl (measure_iUnion_le _)
    _ ≤ ENNReal.ofReal ((measNX m hm : ℝ) * (4 * ρζ * a * measKstar m hm /
          (measTheta m hm * measSigmaX m hm * measDA m hm))) +
        ENNReal.ofReal (Cs * (2 * π ^ 2 / 3)) := by
        refine add_le_add ?_ hsum
        exact hP.X_bound m hm hα0 le_rfl hS hρ0 hρζ
    _ ≤ ENNReal.ofReal (measCP m hm * (ρζ / measDA m hm) * a ^ (8 / 11 : ℝ)) := by
        have hσ := measSigmaX_pos m hm
        have hK : 0 < measKstar m hm := by linarith [measKstar_pos m hm]
        have hCs0 : 0 ≤ Cs := by
          have h8 : 0 ≤ ρζ / measDA m hm * a ^ (8 / 11 : ℝ) :=
            mul_nonneg (div_nonneg hρ0 hDA.le) (Real.rpow_nonneg hα0.le _)
          have h9 : 0 ≤ 8 + 32 * (measTheta m hm)⁻¹ ^ 3 +
              16 * (3 + measAKappa m) * (measTheta m hm)⁻¹ ^ 2 := by
            have := inv_nonneg.2 hϑ.le
            positivity
          exact mul_nonneg h8 h9
        rw [← ENNReal.ofReal_add (by positivity) (mul_nonneg hCs0 (by positivity))]
        refine ENNReal.ofReal_le_ofReal ?_
        have ha8 : a ≤ a ^ (8 / 11 : ℝ) := by
          calc a = a ^ (1 : ℝ) := (Real.rpow_one a).symm
            _ ≤ a ^ (8 / 11 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hα0 ha1 (by norm_num)
        have hXb : (measNX m hm : ℝ) * (4 * ρζ * a * measKstar m hm /
            (measTheta m hm * measSigmaX m hm * measDA m hm)) ≤
            4 * (measNX m hm : ℝ) * measKstar m hm * (measTheta m hm)⁻¹ * (measSigmaX m hm)⁻¹ *
              (ρζ / measDA m hm) * a ^ (8 / 11 : ℝ) := by
          have e : (measNX m hm : ℝ) * (4 * ρζ * a * measKstar m hm /
            (measTheta m hm * measSigmaX m hm * measDA m hm)) =
            4 * (measNX m hm : ℝ) * measKstar m hm * (measTheta m hm)⁻¹ * (measSigmaX m hm)⁻¹ *
              (ρζ / measDA m hm) * a := by field_simp
          rw [e]
          have : 0 ≤ 4 * (measNX m hm : ℝ) * measKstar m hm * (measTheta m hm)⁻¹ *
              (measSigmaX m hm)⁻¹ * (ρζ / measDA m hm) := by positivity
          exact mul_le_mul_of_nonneg_left ha8 this
        have e2 : measCP m hm * (ρζ / measDA m hm) * a ^ (8 / 11 : ℝ) =
            Cs * (2 * π ^ 2 / 3) + 4 * (measNX m hm : ℝ) * measKstar m hm * (measTheta m hm)⁻¹ *
              (measSigmaX m hm)⁻¹ * (ρζ / measDA m hm) * a ^ (8 / 11 : ℝ) := by
          unfold measCP measZ3
          simp only [hCs]; ring
        rw [e2]; linarith

end

end KAM.Wave

end
