/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.Xzones
public import KAM.Wave.Measure.Count

/-!
# W7: measure of unions of zones at fixed `k` (blueprint `bpW:w7:prep`, `bpW:w7:iter`, first steps)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

For a frequency pair on `D` at level `a ≤ α̂` and `ρ_ζ` bounding `‖ω⁰ ξ - ω⁰ ξ'‖`: the zones `l =
    0`,
the union over `Λ⁺ ∖ X` at fixed `k`, and the exceptional zones.
-/

@[expose] public noncomputable section

open Real Finsupp MeasureTheory

namespace KAM.Wave

section

variable (m : ℝ) (hm : 0 < m)
variable {Pi : Set (Fin 2 → ℝ)} {α : ℝ} {D : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ → ℝ} {εω ε1 ε2 θ : ℝ}

theorem japL_zero : japL 0 = 1 := by
  unfold japL
  have : linF (0 : ℕ →₀ ℤ) normLab = 0 := by unfold linF; simp
  rw [this, abs_zero]; exact max_eq_left zero_le_one

/-- The zone of `l ∈ Λ` with `8 c_Λ |l|_{-1/2} ≤ |k|` (blueprint `bpW:w7:zone`, last sentence). -/
theorem IsFreqPair.zone_bound_lam (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {a : ℝ}
    {k : Fin 2 → ℤ} (hk : k ≠ 0) {l : ℕ →₀ ℤ}
    (h8 : 8 * measCLam m hm * absWt l (-(1 / 2 : ℝ)) ≤ kAbs k) (ha : 0 < a) {ρζ : ℝ}
    (hρζ : ∀ ξ ∈ D, ∀ ξ' ∈ D, ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤ ρζ) :
    MeasurableSet (zoneSet D ω Ω a k l) ∧ volume (zoneSet D ω Ω a k l) ≤
      ENNReal.ofReal (8 * (a * japL l / kAk k) * ρζ / (kAbs k * measDA m hm)) := by
  have hj := japL_ge_one l
  have hA := kAk_pos k
  exact hP.zone_measure_le m hm hk (fun ξ => linF l (Ω ξ)) (fun ξ hξ ξ' hξ' => by
    refine (hP.linF_lip m hm hξ hξ' l).trans ?_
    have hn := norm_nonneg (omegaTan m hm ξ - omegaTan m hm ξ')
    nlinarith) hρζ (by positivity)

/-- The zone of `l = 0`. -/
theorem IsFreqPair.zone_bound_zero (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {a : ℝ}
    {k : Fin 2 → ℤ} (hk : k ≠ 0) (ha : 0 < a) {ρζ : ℝ}
    (hρζ : ∀ ξ ∈ D, ∀ ξ' ∈ D, ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤ ρζ) :
    volume (zoneSet D ω Ω a k 0) ≤
      ENNReal.ofReal (8 * (a / kAk k) * ρζ / (kAbs k * measDA m hm)) := by
  have hA := kAk_pos k
  have := hP.zone_measure_le m hm hk (fun _ => (0 : ℝ)) (fun ξ _ ξ' _ => by
    simp only [sub_self, abs_zero]
    have := kAbs_nonneg k
    positivity) hρζ (η := a / kAk k) (by positivity)
  have e : zoneSet D ω Ω a k 0 = {ξ ∈ D | |∑ i, (k i : ℝ) * ω ξ i + 0| < a / kAk k} := by
    ext ξ
    simp only [zoneSet, Set.mem_ofPred_eq, japL_zero, mul_one]
    have : linF (0 : ℕ →₀ ℤ) (Ω ξ) = 0 := by unfold linF; simp
    rw [this]
  rw [e]; exact this.2

/-- The union over `Λ⁺ ∖ X` at fixed `k` (blueprint `bpW:w7:prep`, step `Λ⁺`). -/
theorem IsFreqPair.plus_bound (hS : MeasSetup m hm Pi α)
    (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {a : ℝ} (ha0 : 0 < a)
    (ha : a ≤ alphaHat α) {ρζ : ℝ} (hρ0 : 0 ≤ ρζ)
    (hρζ : ∀ ξ ∈ D, ∀ ξ' ∈ D, ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤ ρζ) {k : Fin 2 → ℤ}
    (hk : k ≠ 0) :
    volume (⋃ (l : ℕ →₀ ℤ) (_ : IsLam l ∧ ¬ IsLamMinus l ∧ (k, l) ∉ measXSet m hm),
        zoneSet D ω Ω a k l) ≤
      ENNReal.ofReal (32 * a * ρζ * kAbs k ^ 2 /
        (measTheta m hm ^ 3 * kAk k * measDA m hm)) := by
  have hϑ := measTheta_pos m hm
  have hϑ1 := measTheta_le m hm
  have hDA := measDA_pos m hm
  have hk1 := one_le_kAbs hk
  have hA := kAk_pos k
  obtain ⟨-, -, -, -, hαβ, -⟩ := alpha_facts m hm hS.alpha_pos hS.alpha_le
  have haβ : a ≤ measBetaStar m := by
    have := measBetaStar_pos hm; linarith
  set x : ℝ := kAbs k / measTheta m hm with hx
  have hx18 : 18 ≤ x := by
    rw [hx, le_div_iff₀ hϑ]; nlinarith
  set N : ℕ := ⌊x⌋₊ with hN
  have hN2 : 2 ≤ N := by
    have : (18 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx18)
    omega
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  set c : ℝ := 8 * a * ρζ / (measTheta m hm * kAk k * measDA m hm) with hc
  have hsub : (⋃ (l : ℕ →₀ ℤ) (_ : IsLam l ∧ ¬ IsLamMinus l ∧ (k, l) ∉ measXSet m hm),
      zoneSet D ω Ω a k l) ⊆ ⋃ l ∈ lamPlusFin N, ⋃ (_ : IsLam l ∧ ¬ IsLamMinus l ∧
        (k, l) ∉ measXSet m hm), zoneSet D ω Ω a k l := by
    intro ξ hξ
    simp only [Set.mem_iUnion] at hξ ⊢
    obtain ⟨l, hcond, hξl⟩ := hξ
    have hne : (zoneSet D ω Ω a k l).Nonempty := ⟨ξ, hξl⟩
    have hd := hP.zone_dichotomy m hm hS ha0.le haβ hcond.1 hcond.2.2 hne
    exact ⟨l, mem_lamPlusFin hcond.1 hcond.2.1 hd.2.1, hcond, hξl⟩
  have hterm : ∀ l ∈ lamPlusFin N, volume (⋃ (_ : IsLam l ∧ ¬ IsLamMinus l ∧
      (k, l) ∉ measXSet m hm), zoneSet D ω Ω a k l) ≤ ENNReal.ofReal c := by
    intro l _
    by_cases hcond : IsLam l ∧ ¬ IsLamMinus l ∧ (k, l) ∉ measXSet m hm
    · have e : (⋃ (_ : IsLam l ∧ ¬ IsLamMinus l ∧ (k, l) ∉ measXSet m hm),
          zoneSet D ω Ω a k l) = zoneSet D ω Ω a k l := by
        ext x; simp only [Set.mem_iUnion]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hcond, h⟩⟩
      rw [e]
      by_cases hne : (zoneSet D ω Ω a k l).Nonempty
      · have hd := hP.zone_dichotomy m hm hS ha0.le haβ hcond.1 hcond.2.2 hne
        have hz := (hP.zone_bound_lam m hm hk hd.2.2 ha0 hρζ).2
        refine hz.trans (ENNReal.ofReal_le_ofReal ?_)
        have hj := japL_ge_one l
        have hjk : japL l ≤ kAbs k / measTheta m hm := hd.2.1
        rw [hc]
        have e1 : 8 * (a * japL l / kAk k) * ρζ / (kAbs k * measDA m hm) =
            8 * a * ρζ * japL l / (kAbs k * kAk k * measDA m hm) := by
          field_simp
        rw [e1, div_le_div_iff₀ (by positivity) (by positivity)]
        have : japL l * measTheta m hm ≤ kAbs k := by
          rwa [le_div_iff₀ hϑ] at hjk
        have h8 : 0 ≤ 8 * a * ρζ := by positivity
        have hAp : (0 : ℝ) ≤ kAk k := by linarith
        nlinarith [mul_nonneg h8 (mul_nonneg hAp hDA.le), mul_nonneg h8 hDA.le,
          mul_nonneg (mul_nonneg h8 hDA.le) hAp]
      · rw [Set.not_nonempty_iff_eq_empty.1 hne]; simp
    · have e : (⋃ (_ : IsLam l ∧ ¬ IsLamMinus l ∧ (k, l) ∉ measXSet m hm),
          zoneSet D ω Ω a k l) = ∅ := by
        ext x; simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
        exact fun ⟨h, _⟩ => hcond h
      rw [e]; simp
  calc volume (⋃ (l : ℕ →₀ ℤ) (_ : IsLam l ∧ ¬ IsLamMinus l ∧ (k, l) ∉ measXSet m hm),
        zoneSet D ω Ω a k l)
      ≤ volume (⋃ l ∈ lamPlusFin N, ⋃ (_ : IsLam l ∧ ¬ IsLamMinus l ∧
        (k, l) ∉ measXSet m hm), zoneSet D ω Ω a k l) := measure_mono hsub
    _ ≤ ∑ l ∈ lamPlusFin N, volume (⋃ (_ : IsLam l ∧ ¬ IsLamMinus l ∧
        (k, l) ∉ measXSet m hm), zoneSet D ω Ω a k l) := measure_biUnion_finset_le _ _
    _ ≤ ∑ l ∈ lamPlusFin N, ENNReal.ofReal c := Finset.sum_le_sum hterm
    _ = ((lamPlusFin N).card : ENNReal) * ENNReal.ofReal c := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (4 * x ^ 2) * ENNReal.ofReal c := by
        gcongr
        have h1 : ((lamPlusFin N).card : ℝ) ≤ 4 * (N : ℝ) ^ 2 := by
          exact_mod_cast card_lamPlusFin_le hN2
        have h2 : (N : ℝ) ^ 2 ≤ x ^ 2 := by
          have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
          nlinarith
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (32 * a * ρζ * kAbs k ^ 2 / (measTheta m hm ^ 3 * kAk k * measDA m hm)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hx, hc]
        field_simp
        ring

end

end KAM.Wave

end
