/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.ZoneBound

/-!
# W7: normal separation, large `|k|` and the dichotomy (blueprint `bpW:w7:sep`, `bpW:w7:largek`,
`bpW:w7:dichotomy`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.
-/

@[expose] public noncomputable section

open Real Finsupp MeasureTheory

namespace KAM.Wave

section

variable (m : ℝ) (hm : 0 < m)
variable {Pi : Set (Fin 2 → ℝ)} {α : ℝ} {D : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ → ℝ} {εω ε1 ε2 θ : ℝ}

/-- **Normal separation** (blueprint `bpW:w7:sep`): `|⟨l, Ω'⟩| ≥ 2 β_* ⟨l⟩` on `Λ`. -/
theorem IsFreqPair.normal_sep (hS : MeasSetup m hm Pi α)
    (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ D) {l : ℕ →₀ ℤ}
    (hl : IsLam l) : 2 * measBetaStar m * japL l ≤ |linF l (Ω ξ)| := by
  have h0 := three_betaStar_japL_le m hm (hS.sub ξ (hP.sub hξ)) hl
  have hd := hP.drift_le_two m hm hξ hl
  obtain ⟨-, -, hαhat, -, hαβ, -⟩ := alpha_facts m hm hS.alpha_pos hS.alpha_le
  have e1 := hP.ε1_mem.2
  have e2 := hP.ε2_mem.2
  have hβ := measBetaStar_pos hm
  have hj := japL_ge_one l
  have h1 := abs_sub_abs_le_abs_sub (linF l (omegaNor m hm ξ)) (linF l (Ω ξ))
  have h2 : |linF l (omegaNor m hm ξ) - linF l (Ω ξ)| ≤ 2 * (ε1 + ε2) := by
    rw [abs_sub_comm]; exact hd
  nlinarith

theorem zoneSet_zero_empty (hS : MeasSetup m hm Pi α)
    (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {a : ℝ} (ha : a ≤ 2 * measBetaStar m)
    {l : ℕ →₀ ℤ} (hl : IsLam l) : zoneSet D ω Ω a 0 l = ∅ := by
  ext ξ
  simp only [zoneSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
  intro hξ
  have := hP.normal_sep m hm hS hξ hl
  simp only [_root_.Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, zero_add]
  have hk : kAk (0 : Fin 2 → ℤ) = 1 := by simp [kAk, kAbs]
  rw [hk, div_one]
  have hj := japL_ge_one l
  nlinarith

/-- **Nonempty zones have large `|k|`** (blueprint `bpW:w7:largek`). -/
theorem IsFreqPair.largek (hS : MeasSetup m hm Pi α)
    (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ measBetaStar m)
    {k : Fin 2 → ℤ} {l : ℕ →₀ ℤ} (hl : IsLam l) (hne : (zoneSet D ω Ω a k l).Nonempty) :
    measTheta m hm * japL l ≤ kAbs k := by
  obtain ⟨ξ, hξ, hz⟩ := hne
  have hsep := hP.normal_sep m hm hS hξ hl
  obtain ⟨-, -, hαhat, h27, -, -⟩ := alpha_facts m hm hS.alpha_pos hS.alpha_le
  have hW := hP.norm_omega_le m hm hS.sub (hαhat.trans h27) hξ
  have hsum := abs_sum_k_mul_le k (ω ξ)
  have hk1 := kAk_pos k
  have hj := japL_ge_one l
  have hβ := measBetaStar_pos hm
  have hWpos := measW_pos m hm
  have hk0 := kAbs_nonneg k
  have hzle : a * japL l / kAk k ≤ a * japL l := div_le_self (by positivity) hk1
  have htri : |linF l (Ω ξ)| ≤ |∑ i, (k i : ℝ) * ω ξ i| +
      |∑ i, (k i : ℝ) * ω ξ i + linF l (Ω ξ)| := by
    have : linF l (Ω ξ) = (∑ i, (k i : ℝ) * ω ξ i + linF l (Ω ξ)) - ∑ i, (k i : ℝ) * ω ξ i := by
        ring
    calc |linF l (Ω ξ)| = |(∑ i, (k i : ℝ) * ω ξ i + linF l (Ω ξ)) - ∑ i, (k i : ℝ) * ω ξ i| := by
          rw [← this]
      _ ≤ _ := by
          have := abs_sub (∑ i, (k i : ℝ) * ω ξ i + linF l (Ω ξ)) (∑ i, (k i : ℝ) * ω ξ i)
          linarith
  have h1 : ‖ω ξ‖ * kAbs k ≤ measW m hm * kAbs k := mul_le_mul_of_nonneg_right hW hk0
  have h2 : a * japL l ≤ measBetaStar m * japL l := mul_le_mul_of_nonneg_right ha (by linarith)
  have h3 : measBetaStar m * japL l ≤ measW m hm * kAbs k := by linarith
  unfold measTheta
  rw [div_mul_eq_mul_div, div_le_iff₀ hWpos]
  linarith

theorem prepZone_subset {Pi : Set (Fin 2 → ℝ)} {a : ℝ} (ha : 0 ≤ a) (k : Fin 2 → ℤ)
    (l : ℕ →₀ ℤ) :
    prepZone m hm Pi a k l ⊆ zoneSet Pi (omegaTan m hm) (omegaNor m hm) a k l := by
  intro ξ ⟨hξ, hz⟩
  refine ⟨hξ, hz.trans_le ?_⟩
  have := kAk_pos k
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hatW_le_japL l) ha) (by linarith)

theorem IsFreqPair.zone_dichotomy (hS : MeasSetup m hm Pi α)
    (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ measBetaStar m)
    {k : Fin 2 → ℤ} {l : ℕ →₀ ℤ} (hl : IsLam l) (hX : (k, l) ∉ measXSet m hm)
    (hne : (zoneSet D ω Ω a k l).Nonempty) :
    k ≠ 0 ∧ japL l ≤ kAbs k / measTheta m hm ∧
      8 * measCLam m hm * absWt l (-(1 / 2 : ℝ)) ≤ kAbs k := by
  have hlk := hP.largek m hm hS ha0 ha hl hne
  have hϑ := measTheta_pos m hm
  have hj := japL_ge_one l
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : (0 : ℝ) < measTheta m hm * japL l := by positivity
    have h0 : kAbs (0 : Fin 2 → ℤ) = 0 := by simp [kAbs]
    rw [h0] at hlk; linarith
  have hk1 := one_le_kAbs hk0
  have hjk : japL l ≤ kAbs k / measTheta m hm := by
    rw [le_div_iff₀ hϑ]; linarith
  refine ⟨hk0, hjk, ?_⟩
  have hc := measCLam_pos m hm
  have hw2 := absWt_le_two hl (δ := -(1 / 2 : ℝ)) (by norm_num)
  by_cases hbig : measKstar m hm ≤ kAbs k
  · unfold measKstar at hbig
    nlinarith [absWt_nonneg l (-(1 / 2 : ℝ))]
  · push Not at hbig
    have hjK : japL l < measKstar m hm / measTheta m hm :=
      lt_of_le_of_lt hjk (div_lt_div_of_pos_right hbig hϑ)
    have hmin : IsLamMinus l ∧ normLab (sInf {ν | l ν ≠ 0}) ≥ measJstar m hm := by
      by_contra hcon
      apply hX
      refine ⟨hl, hk1, hbig, hjK, ?_⟩
      by_cases hmn : IsLamMinus l
      · right
        by_contra h
        exact hcon ⟨hmn, not_lt.1 h⟩
      · exact Or.inl hmn
    obtain ⟨hmn, hjs⟩ := hmin
    obtain ⟨i, j, σ, hji, hσ, rfl⟩ := hmn
    rw [sInf_minus hji σ hσ] at hjs
    rw [absWt_minus hji hσ]
    have hl3 := normLab_ge j
    have hij : normLab j ≤ normLab i := by
      unfold normLab
      have : (j : ℝ) ≤ i := by exact_mod_cast hji.le
      linarith
    have hpow : ∀ x : ℝ, measJstar m hm ≤ x → x ^ (-(1 / 2 : ℝ)) ≤ 1 / (16 * measCLam m hm) := by
      intro x hx
      have hJpos : 0 < measJstar m hm := by linarith [measJstar_pos m hm]
      calc x ^ (-(1 / 2 : ℝ)) ≤ (measJstar m hm) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hJpos hx (by norm_num)
        _ = 1 / (16 * measCLam m hm) := by
            unfold measJstar
            have hb : 0 ≤ 16 * measCLam m hm := by positivity
            rw [← Real.rpow_two, ← Real.rpow_mul hb]
            norm_num [Real.rpow_neg_one]
    have p1 := hpow _ hjs
    have p2 := hpow _ (hjs.trans hij)
    have : 8 * measCLam m hm * (normLab i ^ (-(1 / 2 : ℝ)) + normLab j ^ (-(1 / 2 : ℝ))) ≤ 1 := by
      have : 8 * measCLam m hm * (1 / (16 * measCLam m hm) + 1 / (16 * measCLam m hm)) = 1 := by
        field_simp; ring
      nlinarith
    linarith

end

end KAM.Wave

end
