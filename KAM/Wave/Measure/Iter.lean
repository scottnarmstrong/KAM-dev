/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.IterMinus
public import KAM.Wave.Measure.Prep

/-!
# W7: the iteration zones (blueprint `bpW:w7:iter`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

`volume ℰ_it ≤ ρ_ζ D_A⁻¹ (Z₃ (8 + 32ϑ⁻³ + 16 (2 + a_κ) ϑ⁻²) α̌^{2/3} + 32 Z₃ ϑ⁻¹ (ε₁ + ε₂) + 4 N_X K_*² ϑ⁻¹ σ_X⁻¹ α̌)`.
-/

@[expose] public noncomputable section

open Real Finsupp MeasureTheory

namespace KAM.Wave

theorem zoneSet_neg (D : Set (Fin 2 → ℝ)) (ω : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (Ω : (Fin 2 → ℝ) → ℕ → ℝ) (a : ℝ) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) :
    zoneSet D ω Ω a k (-l) = zoneSet D ω Ω a (-k) l := by
  ext ξ
  simp only [zoneSet, Set.mem_ofPred_eq, japL_neg, kAk_neg, linF_neg]
  have : ∑ i, (((-k) i : ℤ) : ℝ) * ω ξ i = -∑ i, (k i : ℝ) * ω ξ i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp
  rw [this, ← abs_neg]
  have : -(∑ i, (k i : ℝ) * ω ξ i + -linF l (Ω ξ)) =
      -∑ i, (k i : ℝ) * ω ξ i + linF l (Ω ξ) := by ring
  rw [this]

/-- The per-`k` real bound of the iteration zones. -/
theorem iter_perk_real {a ρ DA ϑ aκ ε : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hρ : 0 ≤ ρ)
    (hDA : 0 < DA) (hϑ : 0 < ϑ) (hκ : 0 < aκ) (hε : 0 ≤ ε) {k : Fin 2 → ℤ} (hk : k ≠ 0) :
    kAbs k * (8 * (a / kAk k) * ρ / (kAbs k * DA) +
      32 * a * ρ * kAbs k ^ 2 / (ϑ ^ 3 * kAk k * DA) +
      2 * ((8 * ρ * (2 + aκ) * (a / kAk k) ^ (2 / 3 : ℝ) / (kAbs k * DA)) * (kAbs k / ϑ) ^ 2 +
        (16 * ρ * ε * kAk k ^ (-(1 / 6 : ℝ)) / (kAbs k * DA)) * (kAbs k / ϑ))) ≤
      (ρ / DA * (a ^ (2 / 3 : ℝ) * (8 + 32 * (ϑ⁻¹) ^ 3 + 16 * (2 + aκ) * (ϑ⁻¹) ^ 2) +
        32 * ϑ⁻¹ * ε)) / kAbs k ^ 3 := by
  have hk1 := one_le_kAbs hk
  have hkpos : 0 < kAbs k := by linarith
  have hA := kAk_pos k
  have hApos : 0 < kAk k := by linarith
  have ha8 : a ≤ a ^ (2 / 3 : ℝ) := by
    calc a = a ^ (1 : ℝ) := (Real.rpow_one a).symm
      _ ≤ a ^ (2 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_ge ha0 ha1 (by norm_num)
  have ha8pos : 0 < a ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos ha0 _
  have p3 := pow_le_kAk_rpow hk (e := 3) (s := 1) (by norm_num) (by norm_num)
  have p6 := pow_le_kAk_rpow hk (e := 6) (s := 1) (by norm_num) (by norm_num)
  have p5 := pow_le_kAk_rpow hk (e := 5) (s := 2 / 3) (by norm_num) (by norm_num)
  have p4 := pow_le_kAk_rpow hk (e := 4) (s := 1 / 6) (by norm_num) (by norm_num)
  rw [Real.rpow_one] at p3 p6
  have hA23 : 0 < kAk k ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hApos _
  have hA16 : 0 < kAk k ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hApos _
  have hdiv : (a / kAk k) ^ (2 / 3 : ℝ) = a ^ (2 / 3 : ℝ) / kAk k ^ (2 / 3 : ℝ) :=
    Real.div_rpow ha0.le hApos.le _
  have hneg : kAk k ^ (-(1 / 6 : ℝ)) = (kAk k ^ (1 / 6 : ℝ))⁻¹ := Real.rpow_neg hApos.le _
  have hk3 : 0 < kAbs k ^ 3 := by positivity
  set u3 : ℝ := (kAbs k ^ 3)⁻¹ with hu3
  have hu3pos : 0 < u3 := by positivity
  have hu3e : ∀ x : ℝ, x / kAbs k ^ 3 = x * u3 := fun x => by rw [hu3, div_eq_mul_inv]
  have f0 : (kAk k)⁻¹ ≤ u3 := inv_anti₀ hk3 p3
  have f1 : kAbs k ^ 3 / kAk k ≤ u3 := by
    rw [div_le_iff₀ hApos]
    calc kAbs k ^ 3 = u3 * kAbs k ^ 6 := by rw [hu3]; field_simp
      _ ≤ u3 * kAk k := mul_le_mul_of_nonneg_left p6 hu3pos.le
  have f2 : kAbs k ^ 2 / kAk k ^ (2 / 3 : ℝ) ≤ u3 := by
    rw [div_le_iff₀ hA23]
    calc kAbs k ^ 2 = u3 * kAbs k ^ 5 := by rw [hu3]; field_simp
      _ ≤ u3 * kAk k ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_left p5 hu3pos.le
  have f3 : kAbs k / kAk k ^ (1 / 6 : ℝ) ≤ u3 := by
    rw [div_le_iff₀ hA16]
    calc kAbs k = u3 * kAbs k ^ 4 := by rw [hu3]; field_simp
      _ ≤ u3 * kAk k ^ (1 / 6 : ℝ) := mul_le_mul_of_nonneg_left p4 hu3pos.le
  have e0 : kAbs k * (8 * (a / kAk k) * ρ / (kAbs k * DA)) = (8 * a * ρ / DA) * (kAk k)⁻¹ := by
    field_simp
  have e1 : kAbs k * (32 * a * ρ * kAbs k ^ 2 / (ϑ ^ 3 * kAk k * DA)) =
      (32 * a * ρ / (ϑ ^ 3 * DA)) * (kAbs k ^ 3 / kAk k) := by field_simp
  have e2 : kAbs k * (2 * ((8 * ρ * (2 + aκ) * (a / kAk k) ^ (2 / 3 : ℝ) / (kAbs k * DA)) *
      (kAbs k / ϑ) ^ 2)) = (16 * ρ * (2 + aκ) * a ^ (2 / 3 : ℝ) / (ϑ ^ 2 * DA)) *
      (kAbs k ^ 2 / kAk k ^ (2 / 3 : ℝ)) := by
    rw [hdiv]; field_simp; ring
  have e3 : kAbs k * (2 * ((16 * ρ * ε * kAk k ^ (-(1 / 6 : ℝ)) / (kAbs k * DA)) *
      (kAbs k / ϑ))) = (32 * ρ * ε / (ϑ * DA)) * (kAbs k / kAk k ^ (1 / 6 : ℝ)) := by
    rw [hneg]; field_simp; ring
  have hsplit : kAbs k * (8 * (a / kAk k) * ρ / (kAbs k * DA) +
      32 * a * ρ * kAbs k ^ 2 / (ϑ ^ 3 * kAk k * DA) +
      2 * ((8 * ρ * (2 + aκ) * (a / kAk k) ^ (2 / 3 : ℝ) / (kAbs k * DA)) * (kAbs k / ϑ) ^ 2 +
        (16 * ρ * ε * kAk k ^ (-(1 / 6 : ℝ)) / (kAbs k * DA)) * (kAbs k / ϑ))) =
      kAbs k * (8 * (a / kAk k) * ρ / (kAbs k * DA)) +
      kAbs k * (32 * a * ρ * kAbs k ^ 2 / (ϑ ^ 3 * kAk k * DA)) +
      kAbs k * (2 * ((8 * ρ * (2 + aκ) * (a / kAk k) ^ (2 / 3 : ℝ) / (kAbs k * DA)) *
        (kAbs k / ϑ) ^ 2)) +
      kAbs k * (2 * ((16 * ρ * ε * kAk k ^ (-(1 / 6 : ℝ)) / (kAbs k * DA)) * (kAbs k / ϑ))) := by
    ring
  rw [hsplit, e0, e1, e2, e3, hu3e]
  have c1 : 0 ≤ 8 * a * ρ / DA := by positivity
  have c2 : 0 ≤ 32 * a * ρ / (ϑ ^ 3 * DA) := by positivity
  have c3 : 0 ≤ 16 * ρ * (2 + aκ) * a ^ (2 / 3 : ℝ) / (ϑ ^ 2 * DA) := by positivity
  have c4 : 0 ≤ 32 * ρ * ε / (ϑ * DA) := by positivity
  calc (8 * a * ρ / DA) * (kAk k)⁻¹ + (32 * a * ρ / (ϑ ^ 3 * DA)) * (kAbs k ^ 3 / kAk k) +
        (16 * ρ * (2 + aκ) * a ^ (2 / 3 : ℝ) / (ϑ ^ 2 * DA)) *
          (kAbs k ^ 2 / kAk k ^ (2 / 3 : ℝ)) +
        (32 * ρ * ε / (ϑ * DA)) * (kAbs k / kAk k ^ (1 / 6 : ℝ))
      ≤ (8 * a * ρ / DA) * u3 + (32 * a * ρ / (ϑ ^ 3 * DA)) * u3 +
        (16 * ρ * (2 + aκ) * a ^ (2 / 3 : ℝ) / (ϑ ^ 2 * DA)) * u3 +
        (32 * ρ * ε / (ϑ * DA)) * u3 := by gcongr
    _ ≤ (8 * a ^ (2 / 3 : ℝ) * ρ / DA) * u3 + (32 * a ^ (2 / 3 : ℝ) * ρ / (ϑ ^ 3 * DA)) * u3 +
        (16 * ρ * (2 + aκ) * a ^ (2 / 3 : ℝ) / (ϑ ^ 2 * DA)) * u3 +
        (32 * ρ * ε / (ϑ * DA)) * u3 := by gcongr
    _ = _ := by field_simp

section

variable (m : ℝ) (hm : 0 < m)
variable {Pi : Set (Fin 2 → ℝ)} {α : ℝ}

/-- The iteration zones (blueprint `bpW:w7:iter`). -/
theorem iterSet_measure_le (hS : MeasSetup m hm Pi α) (F : AdmissibleFamily m hm Pi α) {ρζ : ℝ}
    (hρ0 : 0 ≤ ρζ) (hρζ : ∀ ξ ∈ Pi, ∀ ξ' ∈ Pi, ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤ ρζ) :
    volume (iterSet m hm F) ≤ ENNReal.ofReal (ρζ / measDA m hm *
      (measZ3 * (8 + 32 * (measTheta m hm)⁻¹ ^ 3 + 16 * (2 + measAKappa m) *
          (measTheta m hm)⁻¹ ^ 2) * alphaCheck α ^ (2 / 3 : ℝ) +
        32 * measZ3 * (measTheta m hm)⁻¹ * (F.ε1 + F.ε2) +
        4 * (measNX m hm : ℝ) * measKstar m hm ^ 2 * (measTheta m hm)⁻¹ * (measSigmaX m hm)⁻¹ *
          alphaCheck α)) := by
  classical
  obtain ⟨hc, hcA, hαhat, h27, hβ4, -⟩ := alpha_facts m hm hS.alpha_pos hS.alpha_le
  have hα0 : 0 < alphaHat α := lt_of_lt_of_le hS.alpha_pos hαhat
  have hαc : alphaCheck α ≤ alphaHat α := by linarith
  have hc1 : alphaCheck α ≤ 1 := by linarith
  have hDA := measDA_pos m hm
  have hϑ := measTheta_pos m hm
  have hκ := measAKappa_pos hm
  have hσ := measSigmaX_pos m hm
  have hK : 0 < measKstar m hm := by linarith [measKstar_pos m hm]
  have haβ : alphaCheck α ≤ measBetaStar m := by have := measBetaStar_pos hm; linarith
  have hε : 0 ≤ F.ε1 + F.ε2 := by linarith [(F.pair 0).ε1_mem.1, (F.pair 0).ε2_mem.1]
  set a := alphaCheck α with ha
  set Cs : ℝ := ρζ / measDA m hm * (a ^ (2 / 3 : ℝ) * (8 + 32 * (measTheta m hm)⁻¹ ^ 3 +
    16 * (2 + measAKappa m) * (measTheta m hm)⁻¹ ^ 2) + 32 * (measTheta m hm)⁻¹ * (F.ε1 + F.ε2))
    with hCs
  have hCs0 : 0 ≤ Cs := by
    have := inv_nonneg.2 hϑ.le
    have h1 : 0 ≤ ρζ / measDA m hm := div_nonneg hρ0 hDA.le
    simp only [hCs]; positivity
  -- notation for the zones of the `ν`-th pair
  set Zn : ℕ → (Fin 2 → ℤ) → (ℕ →₀ ℤ) → Set (Fin 2 → ℝ) := fun ν k l =>
    zoneSet (F.D ν) (F.ω ν) (F.Ω ν) a k l with hZn
  set Xν : ℕ → Set (Fin 2 → ℝ) := fun ν => ⋃ (kl : (Fin 2 → ℤ) × (ℕ →₀ ℤ))
    (_ : kl ∈ measXSet m hm) (_ : F.Kprev m hm ν < kAbs kl.1), Zn ν kl.1 kl.2 with hXν
  set Yν : ℕ → (Fin 2 → ℤ) → Set (Fin 2 → ℝ) := fun ν k => ⋃ (_ : F.Kprev m hm ν < kAbs k),
    (((⋃ (_ : k ≠ 0), Zn ν k 0) ∪
      (⋃ (l : ℕ →₀ ℤ) (_ : IsLam l ∧ ¬ IsLamMinus l ∧ (k, l) ∉ measXSet m hm), Zn ν k l)) ∪
      minusUnion m hm (Zn ν) k) with hYν
  have hcover : iterSet m hm F ⊆ (⋃ ν, Xν ν) ∪ ⋃ ν, ⋃ k, Yν ν k := by
    intro x hx
    simp only [iterSet, Set.mem_iUnion] at hx
    obtain ⟨ν, k, l, ⟨⟨hl0, hkl⟩, hKk⟩, hxz⟩ := hx
    by_cases hX : (k, l) ∈ measXSet m hm
    · left
      simp only [hXν, Set.mem_iUnion]
      exact ⟨ν, (k, l), hX, hKk, hxz⟩
    · right
      simp only [Set.mem_iUnion, hYν]
      refine ⟨ν, k, hKk, ?_⟩
      rcases hl0 with rfl | hlam
      · rcases hkl with hk | hl
        · left; left
          simp only [Set.mem_iUnion]
          exact ⟨hk, hxz⟩
        · exact absurd rfl hl
      · by_cases hmn : IsLamMinus l
        · right
          simp only [minusUnion, Set.mem_iUnion]
          exact ⟨l, ⟨hmn, hX⟩, hxz⟩
        · left; right
          simp only [Set.mem_iUnion]
          exact ⟨l, ⟨hlam, hmn, hX⟩, hxz⟩
  have hρν : ∀ ν, ∀ ξ ∈ F.D ν, ∀ ξ' ∈ F.D ν, ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤ ρζ :=
    fun ν ξ hξ ξ' hξ' => hρζ ξ ((F.pair ν).sub hξ) ξ' ((F.pair ν).sub hξ')
  -- the zones at `k = 0` are empty
  have hY0 : ∀ ν, Yν ν 0 = ∅ := by
    intro ν
    ext x
    simp only [hYν, hZn, Set.mem_union, Set.mem_iUnion, minusUnion, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨_, (⟨h, _⟩ | ⟨l, ⟨hlam, _, _⟩, hz⟩) | ⟨l, ⟨hmn, _⟩, hz⟩⟩
    · exact h rfl
    · rw [zoneSet_zero_empty m hm hS (F.pair ν) (by linarith) hlam] at hz; exact hz
    · rw [zoneSet_zero_empty m hm hS (F.pair ν) (by linarith) (IsLam_of_minus hmn)] at hz
      exact hz
  -- the per-`k` bound
  set bk : (Fin 2 → ℤ) → ℝ := fun k =>
    8 * (a / kAk k) * ρζ / (kAbs k * measDA m hm) +
      32 * a * ρζ * kAbs k ^ 2 / (measTheta m hm ^ 3 * kAk k * measDA m hm) +
      2 * ((8 * ρζ * (2 + measAKappa m) * (a / kAk k) ^ (2 / 3 : ℝ) / (kAbs k * measDA m hm)) *
          (kAbs k / measTheta m hm) ^ 2 +
        (16 * ρζ * (F.ε1 + F.ε2) * kAk k ^ (-(1 / 6 : ℝ)) / (kAbs k * measDA m hm)) *
          (kAbs k / measTheta m hm)) with hbk
  have hYb : ∀ ν, ∀ k : Fin 2 → ℤ, k ≠ 0 → F.Kprev m hm ν < kAbs k →
      volume (Yν ν k) ≤ ENNReal.ofReal (bk k) := by
    intro ν k hk hKk
    have hP := F.pair ν
    have hk1 := one_le_kAbs hk
    have hA := kAk_pos k
    have h0 := hP.zone_bound_zero m hm hk hc (hρν ν)
    have h1 := hP.plus_bound m hm hS hc hαc hρ0 (hρν ν) hk
    have h2 := minus_assembly m hm (Zn ν) (fun k l => zoneSet_neg _ _ _ a k l) hk
      (c1 := 8 * ρζ * (2 + measAKappa m) * (a / kAk k) ^ (2 / 3 : ℝ) / (kAbs k * measDA m hm))
      (c0 := 16 * ρζ * (F.ε1 + F.ε2) * kAk k ^ (-(1 / 6 : ℝ)) / (kAbs k * measDA m hm))
      (by positivity) (by have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ kAk k) (-(1 / 6 : ℝ))
                          positivity)
      (fun k' hk' j n hne => by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp only [Nat.cast_zero]; positivity
        · have hz : (Zn ν k' (lamMinusPlus j n)).Nonempty := hne
          have := hP.largek m hm hS hc.le haβ (isLam_lamMinusPlus j n hn) hz
          rw [japL_lamMinusPlus j n hn, hk'] at this
          rw [le_div_iff₀ hϑ]; linarith)
      (fun k' hk' n hn1 hn2 => by
        have hk'0 : k' ≠ 0 := by
          intro h; rw [h] at hk'
          have : kAbs (0 : Fin 2 → ℤ) = 0 := by simp [kAbs]
          linarith
        have hAk : kAk k' = kAk k := by simp [kAk, hk']
        have := iter_minus_n_bound m hm hS hP hρ0 (hρν ν) hk'0 hn1
        rw [hAk, hk'] at this
        exact this)
    have hu : (⋃ (_ : k ≠ 0), Zn ν k 0) = Zn ν k 0 := by
      ext x; simp only [Set.mem_iUnion]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hk, h⟩⟩
    have hYe : Yν ν k = (((⋃ (_ : k ≠ 0), Zn ν k 0) ∪
      (⋃ (l : ℕ →₀ ℤ) (_ : IsLam l ∧ ¬ IsLamMinus l ∧ (k, l) ∉ measXSet m hm), Zn ν k l)) ∪
      minusUnion m hm (Zn ν) k) := by
      ext x; simp only [hYν, Set.mem_iUnion]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hKk, h⟩⟩
    rw [hYe, hu]
    calc volume ((Zn ν k 0 ∪ ⋃ (l : ℕ →₀ ℤ) (_ : IsLam l ∧ ¬ IsLamMinus l ∧ (k, l) ∉ measXSet m hm),
          Zn ν k l) ∪ minusUnion m hm (Zn ν) k)
        ≤ volume (Zn ν k 0) + volume (⋃ (l : ℕ →₀ ℤ)
            (_ : IsLam l ∧ ¬ IsLamMinus l ∧ (k, l) ∉ measXSet m hm), Zn ν k l) +
          volume (minusUnion m hm (Zn ν) k) :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ _ := by
          rw [hbk]
          dsimp only
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity)]
          exact add_le_add (add_le_add h0 h1) h2
  set G : (Fin 2 → ℤ) → ENNReal := fun k => if k = 0 then 0 else ENNReal.ofReal (bk k) with hG
  have hg : ∀ ν k, volume (Yν ν k) ≤ (if F.Kprev m hm ν < kAbs k then G k else 0) := by
    intro ν k
    by_cases hKk : F.Kprev m hm ν < kAbs k
    · simp only [hKk, ↓reduceIte]
      by_cases hk : k = 0
      · subst hk; rw [hY0]; simp
      · simp only [hG, hk, ↓reduceIte]; exact hYb ν k hk hKk
    · simp only [hKk, ↓reduceIte]
      have : Yν ν k = ∅ := by
        ext x; simp only [hYν, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
        exact fun ⟨h, _⟩ => hKk h
      rw [this]; simp
  have hYsum : volume (⋃ ν, ⋃ k, Yν ν k) ≤ ENNReal.ofReal (Cs * (2 * π ^ 2 / 3)) := by
    calc volume (⋃ ν, ⋃ k, Yν ν k) ≤ ∑' ν, volume (⋃ k, Yν ν k) := measure_iUnion_le _
      _ ≤ ∑' ν, ∑' k, volume (Yν ν k) := ENNReal.tsum_le_tsum fun ν => measure_iUnion_le _
      _ ≤ ∑' ν, ∑' k, (if F.Kprev m hm ν < kAbs k then G k else 0) :=
          ENNReal.tsum_le_tsum fun ν => ENNReal.tsum_le_tsum fun k => hg ν k
      _ = ∑' k, ∑' ν, (if F.Kprev m hm ν < kAbs k then G k else 0) := ENNReal.tsum_comm
      _ ≤ ∑' k : Fin 2 → ℤ, (if k = 0 then 0 else ENNReal.ofReal (Cs / kAbs k ^ 3)) := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          by_cases hk : k = 0
          · subst hk; simp [hG]
          · simp only [hk, ↓reduceIte]
            refine (tsum_Kprev_le m hm F hk (G k)).trans ?_
            simp only [hG, hk, ↓reduceIte]
            rw [← ENNReal.ofReal_mul (kAbs_nonneg k)]
            refine ENNReal.ofReal_le_ofReal ?_
            exact iter_perk_real hc hc1 hρ0 hDA hϑ hκ hε hk
      _ ≤ ENNReal.ofReal (Cs * (2 * π ^ 2 / 3)) := tsum_lattice_le hCs0
  -- the exceptional zones
  have hfin := measXSet_finite m hm
  set cX : ℝ := 4 * ρζ * a * measKstar m hm / (measTheta m hm * measSigmaX m hm * measDA m hm)
    with hcX
  have hXsum : volume (⋃ ν, Xν ν) ≤
      ENNReal.ofReal ((measNX m hm : ℝ) * (measKstar m hm * cX)) := by
    have hXe : ∀ ν, Xν ν = ⋃ kl ∈ hfin.toFinset, ⋃ (_ : F.Kprev m hm ν < kAbs kl.1),
        Zn ν kl.1 kl.2 := by
      intro ν; ext x; simp [hXν]
    have hXb : ∀ ν, volume (Xν ν) ≤
        ∑ kl ∈ hfin.toFinset, (if F.Kprev m hm ν < kAbs kl.1 then ENNReal.ofReal cX else 0) := by
      intro ν
      rw [hXe]
      refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun kl hkl => ?_)
      by_cases hKk : F.Kprev m hm ν < kAbs kl.1
      · have ite_e : (if F.Kprev m hm ν < kAbs kl.1 then ENNReal.ofReal cX else 0) =
            ENNReal.ofReal cX := by simp [hKk]
        have e : (⋃ (_ : F.Kprev m hm ν < kAbs kl.1), Zn ν kl.1 kl.2) = Zn ν kl.1 kl.2 := by
          ext x; simp only [Set.mem_iUnion]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hKk, h⟩⟩
        rw [ite_e, e]
        have hx : kl ∈ measXSet m hm := hfin.mem_toFinset.1 hkl
        obtain ⟨k, l⟩ := kl
        by_cases hp : measPX m hm k l = 0
        · simp only [hZn]
          rw [(F.pair ν).Xzone_empty m hm hS hc.le hαc hx hp]; simp
        · exact ((F.pair ν).Xzone_measure_le m hm hc hx hp hρ0 (hρν ν)).2
      · have ite_e : (if F.Kprev m hm ν < kAbs kl.1 then ENNReal.ofReal cX else 0) = 0 := by
          simp [hKk]
        have e : (⋃ (_ : F.Kprev m hm ν < kAbs kl.1), Zn ν kl.1 kl.2) = ∅ := by
          ext x; simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
          exact fun ⟨h, _⟩ => hKk h
        rw [ite_e, e]; simp
    calc volume (⋃ ν, Xν ν) ≤ ∑' ν, volume (Xν ν) := measure_iUnion_le _
      _ ≤ ∑' ν, ∑ kl ∈ hfin.toFinset,
          (if F.Kprev m hm ν < kAbs kl.1 then ENNReal.ofReal cX else 0) :=
          ENNReal.tsum_le_tsum hXb
      _ = ∑ kl ∈ hfin.toFinset, ∑' ν,
          (if F.Kprev m hm ν < kAbs kl.1 then ENNReal.ofReal cX else 0) :=
          Summable.tsum_finsetSum fun _ _ => ENNReal.summable
      _ ≤ ∑ kl ∈ hfin.toFinset, ENNReal.ofReal (measKstar m hm * cX) := by
          refine Finset.sum_le_sum fun kl hkl => ?_
          have hx : kl ∈ measXSet m hm := hfin.mem_toFinset.1 hkl
          have hk0 : kl.1 ≠ 0 := by
            intro h
            have := hx.2.1
            rw [h] at this
            have h0 : kAbs (0 : Fin 2 → ℤ) = 0 := by simp [kAbs]
            linarith
          refine (tsum_Kprev_le m hm F hk0 _).trans ?_
          rw [← ENNReal.ofReal_mul (kAbs_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hcX0 : 0 ≤ cX := by simp only [hcX]; positivity
          exact mul_le_mul_of_nonneg_right hx.2.2.1.le hcX0
      _ = ENNReal.ofReal ((measNX m hm : ℝ) * (measKstar m hm * cX)) := by
          rw [Finset.sum_const, nsmul_eq_mul, measNX, Set.ncard_eq_toFinset_card _ hfin,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  calc volume (iterSet m hm F) ≤ volume ((⋃ ν, Xν ν) ∪ ⋃ ν, ⋃ k, Yν ν k) := measure_mono hcover
    _ ≤ volume (⋃ ν, Xν ν) + volume (⋃ ν, ⋃ k, Yν ν k) := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((measNX m hm : ℝ) * (measKstar m hm * cX)) +
        ENNReal.ofReal (Cs * (2 * π ^ 2 / 3)) := add_le_add hXsum hYsum
    _ = ENNReal.ofReal ((measNX m hm : ℝ) * (measKstar m hm * cX) + Cs * (2 * π ^ 2 / 3)) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = _ := by
        congr 1
        simp only [hCs, hcX, measZ3]
        field_simp
        ring

end

end KAM.Wave

end
