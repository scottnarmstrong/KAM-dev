/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.PrepMinus

/-!
# W7: the iteration zones of `Λ⁻` (blueprint `bpW:w7:iter`, steps "`Λ⁻`")

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

With `j₀ = ⌈(A_k/α̌)^{1/3}⌉` and the drift `ε = ε₁ + ε₂`: for fixed `k ≠ 0`, `n ≥ 1` the union over
`j` of the zones of `e_{j+n} - e_j` at level `α̌` has measure
`≤ (8 ρ_ζ / (|k| D_A)) ((2 + a_κ) n (α̌/A_k)^{2/3} + 2 ε A_k^{-1/6})`.
-/

@[expose] public noncomputable section

open Real Finsupp MeasureTheory

namespace KAM.Wave

section

variable (m : ℝ) (hm : 0 < m)
variable {Pi : Set (Fin 2 → ℝ)} {α : ℝ} {D : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ → ℝ} {εω ε1 ε2 θ : ℝ}

theorem japL_lamMinusPlus (j n : ℕ) (hn : 1 ≤ n) : japL (lamMinusPlus j n) = n := by
  have := japL_minus (i := j + n) (j := j) (σ := 1) (by omega) (Or.inl rfl)
  unfold lamMinusPlus
  rw [show (-1 : ℤ) = -(1 : ℤ) by norm_num, this]; push_cast; ring

theorem isLam_lamMinusPlus (j n : ℕ) (hn : 1 ≤ n) : IsLam (lamMinusPlus j n) :=
  IsLam_of_minus ⟨j + n, j, 1, by omega, Or.inl rfl, rfl⟩

/-- Drift of `⟨e_{j+n} - e_j, Ω'⟩ - n`. -/
theorem IsFreqPair.minus_drift (hS : MeasSetup m hm Pi α)
    (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ D) (j n : ℕ)
    (hn : 1 ≤ n) :
    |linF (lamMinusPlus j n) (Ω ξ) - n| ≤
      2 * (ε1 + ε2) * normLab j ^ (-(1 / 2 : ℝ)) + measAKappa m * n / normLab j ^ 2 := by
  have hξ12 := hS.sub ξ (hP.sub hξ)
  have hd := hP.drift_le m hm hξ (lamMinusPlus j n)
  have hlm : lamMinusPlus j n = single (j + n) 1 + single j (-(1 : ℤ)) := by
    unfold lamMinusPlus; rw [show (-1 : ℤ) = -(1 : ℤ) by norm_num]
  rw [hlm, absWt_minus (by omega) (Or.inl rfl), absWt_minus (by omega) (Or.inl rfl)] at hd
  have happ := omegaNor_sub_approx m hm hξ12 (i := j + n) (j := j) (by omega)
  have hdn : normLab (j + n) - normLab j = n := by unfold normLab; push_cast; ring
  rw [hdn] at happ
  have hl : linF (lamMinusPlus j n) (omegaNor m hm ξ) =
      omegaNor m hm ξ (j + n) - omegaNor m hm ξ j := by
    rw [hlm, linF_minus (by omega)]; push_cast; ring
  have hij : normLab j ≤ normLab (j + n) := by unfold normLab; push_cast; linarith
  have h1 : normLab (j + n) ^ (-1 : ℝ) ≤ normLab j ^ (-(1 / 2 : ℝ)) := by
    have := Real.rpow_le_rpow_of_nonpos (normLab_pos j) hij (by norm_num : (-1 : ℝ) ≤ 0)
    refine this.trans ?_
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [normLab_ge j]) (by norm_num)
  have h2 : normLab j ^ (-1 : ℝ) ≤ normLab j ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [normLab_ge j]) (by norm_num)
  have h3 : normLab (j + n) ^ (-(1 / 2 : ℝ)) ≤ normLab j ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (normLab_pos j) hij (by norm_num)
  have e1 := hP.ε1_mem.1
  have e2 := hP.ε2_mem.1
  have hsplit : linF (lamMinusPlus j n) (Ω ξ) - n =
      (linF (lamMinusPlus j n) (Ω ξ) - linF (lamMinusPlus j n) (omegaNor m hm ξ)) +
        (omegaNor m hm ξ (j + n) - omegaNor m hm ξ j - n) := by rw [hl]; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ happ)
  refine hd.trans ?_
  nlinarith [mul_le_mul_of_nonneg_left h1 e1, mul_le_mul_of_nonneg_left h2 e1,
    mul_le_mul_of_nonneg_left h3 e2, mul_le_mul_of_nonneg_left (le_refl (normLab j ^ (-(1 / 2 : ℝ)))) e2]

/-- For fixed `k ≠ 0` and `n ≥ 1`. -/
theorem iter_minus_n_bound (hS : MeasSetup m hm Pi α)
    (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {ρζ : ℝ} (hρ0 : 0 ≤ ρζ)
    (hρζ : ∀ ξ ∈ D, ∀ ξ' ∈ D, ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤ ρζ)
    {k : Fin 2 → ℤ} (hk : k ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    volume (⋃ (j : ℕ) (_ : (k, lamMinusPlus j n) ∉ measXSet m hm),
        zoneSet D ω Ω (alphaCheck α) k (lamMinusPlus j n)) ≤
      ENNReal.ofReal (8 * ρζ * (2 + measAKappa m) * (alphaCheck α / kAk k) ^ (2 / 3 : ℝ) /
          (kAbs k * measDA m hm) * n +
        16 * ρζ * (ε1 + ε2) * kAk k ^ (-(1 / 6 : ℝ)) / (kAbs k * measDA m hm)) := by
  obtain ⟨hc, hcA, hαhat, h27, hβ4, -⟩ := alpha_facts m hm hS.alpha_pos hS.alpha_le
  have hc1 : alphaCheck α ≤ 1 / 27 := by linarith
  have hαc : alphaCheck α ≤ alphaHat α := by linarith
  have hA := kAk_pos k
  have hApos : 0 < kAk k := by linarith
  have hDA := measDA_pos m hm
  have hk1 := one_le_kAbs hk
  have hκ := measAKappa_pos hm
  have e1 := hP.ε1_mem.1
  have e2 := hP.ε2_mem.1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set u : ℝ := alphaCheck α / kAk k with hu
  have hu0 : 0 < u := by positivity
  have hu27 : u ≤ 1 / 27 := (div_le_self hc.le hA).trans hc1
  set J0 : ℕ := ⌈u ^ (-(1 / 3 : ℝ))⌉₊ with hJ0
  obtain ⟨hJ3, hJu, hJ2, hJ12⟩ := iter_real_bound hu0 hu27 J0 hJ0
  have hJpos : (0 : ℝ) < J0 := by
    have : (3 : ℝ) ≤ J0 := by exact_mod_cast hJ3
    linarith
  set ε : ℝ := ε1 + ε2 with hε
  set η : ℕ → ℝ := fun _ => alphaCheck α * n / kAk k with hη
  set θQ : ℝ := alphaCheck α * n / kAk k + 2 * ε * (J0 : ℝ) ^ (-(1 / 2 : ℝ)) +
    measAKappa m * n * (J0 : ℝ) ^ (-(2 : ℝ)) with hθQ
  have hη_pos : ∀ j, 0 < η j := fun j => by simp only [hη]; positivity
  have hθQ_pos : 0 < θQ := by
    have h1 := Real.rpow_pos_of_pos hJpos (-(1 / 2 : ℝ))
    have h2 := Real.rpow_pos_of_pos hJpos (-(2 : ℝ))
    simp only [hθQ]; positivity
  have hmain := hP.minus_n_bound m hm hS hc hαc hk hn (J0 - 3) η hη_pos
    (fun j => by
      simp only [hη]
      exact le_of_eq (by rfl)) hθQ_pos hρ0 hρζ
    (fun j hj ξ ⟨hξ, hz⟩ => by
      refine ⟨hξ, ?_⟩
      have hlab : (J0 : ℝ) ≤ normLab j := by
        unfold normLab
        have : (J0 : ℝ) - 3 ≤ j := by
          have h := (Nat.cast_le (α := ℝ)).2 hj
          rw [Nat.cast_sub hJ3] at h; push_cast at h; linarith
        linarith
      have hdr := hP.minus_drift m hm hS hξ j n hn
      have h1 : normLab j ^ (-(1 / 2 : ℝ)) ≤ (J0 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hJpos hlab (by norm_num)
      have h2 : measAKappa m * n / normLab j ^ 2 ≤ measAKappa m * n * (J0 : ℝ) ^ (-(2 : ℝ)) := by
        rw [rpow_neg_two_eq hJpos.le, ← div_eq_mul_inv]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith
      have e0 : ∑ i, ((k i : ℤ) : ℝ) * ω ξ i + (n : ℝ) =
          (∑ i, ((k i : ℤ) : ℝ) * ω ξ i + linF (lamMinusPlus j n) (Ω ξ)) -
            (linF (lamMinusPlus j n) (Ω ξ) - n) := by ring
      rw [e0]
      refine lt_of_le_of_lt (abs_sub _ _) ?_
      have hz' : |∑ i, ((k i : ℤ) : ℝ) * ω ξ i + linF (lamMinusPlus j n) (Ω ξ)| <
          alphaCheck α * n / kAk k := hz
      have h3 : 2 * ε * normLab j ^ (-(1 / 2 : ℝ)) ≤ 2 * ε * (J0 : ℝ) ^ (-(1 / 2 : ℝ)) := by
        have : 0 ≤ 2 * ε := by simp only [hε]; linarith
        exact mul_le_mul_of_nonneg_left h1 this
      simp only [hθQ]
      linarith)
  have hzeq : (⋃ (j : ℕ) (_ : (k, lamMinusPlus j n) ∉ measXSet m hm),
      zoneSet D ω Ω (alphaCheck α) k (lamMinusPlus j n)) = ⋃ (j : ℕ)
      (_ : (k, lamMinusPlus j n) ∉ measXSet m hm), genZone D ω Ω (η j) k (lamMinusPlus j n) := by
    ext x; simp only [Set.mem_iUnion]
    have hj : ∀ j, zoneSet D ω Ω (alphaCheck α) k (lamMinusPlus j n) =
        genZone D ω Ω (η j) k (lamMinusPlus j n) := fun j => by
      rw [zoneSet_eq_genZone, japL_lamMinusPlus j n hn]
    simp only [hj]
  rw [hzeq]
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hD : 0 < kAbs k * measDA m hm := by positivity
  have hε0 : 0 ≤ ε := by simp only [hε]; linarith
  -- the bound on `A^{-1/6}`: `J0^{-1/2} ≤ u^{1/6}`, `u^{1/6} ≤ A^{-1/6}`
  have hu16 : u ^ (1 / 6 : ℝ) ≤ kAk k ^ (-(1 / 6 : ℝ)) := by
    rw [hu, Real.div_rpow hc.le hApos.le, Real.rpow_neg hApos.le, div_eq_mul_inv]
    have : alphaCheck α ^ (1 / 6 : ℝ) ≤ 1 :=
      Real.rpow_le_one hc.le (by linarith) (by norm_num)
    have hpos : 0 ≤ (kAk k ^ (1 / 6 : ℝ))⁻¹ := by positivity
    nlinarith
  have hsumc : ∑ j ∈ Finset.range (J0 - 3), 8 * η j * ρζ / (kAbs k * measDA m hm) =
      ((J0 - 3 : ℕ) : ℝ) * (8 * (alphaCheck α * n / kAk k) * ρζ / (kAbs k * measDA m hm)) := by
    simp only [hη, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsumc]
  have hJ3r : ((J0 - 3 : ℕ) : ℝ) + 1 ≤ J0 := by
    have : ((J0 - 3 : ℕ) : ℝ) = (J0 : ℝ) - 3 := by rw [Nat.cast_sub hJ3]; norm_num
    rw [this]; linarith
  have hpre : 0 ≤ 8 * (alphaCheck α * n / kAk k) * ρζ / (kAbs k * measDA m hm) := by positivity
  have hQ16 : (J0 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ kAk k ^ (-(1 / 6 : ℝ)) := hJ12.trans hu16
  have hQ1 : ((J0 - 3 : ℕ) : ℝ) * (8 * (alphaCheck α * n / kAk k) * ρζ / (kAbs k * measDA m hm)) +
      8 * θQ * ρζ / (kAbs k * measDA m hm) ≤
      (8 * ρζ / (kAbs k * measDA m hm)) * ((J0 : ℝ) * u * n + measAKappa m * n * u ^ (2 / 3 : ℝ) +
        2 * ε * kAk k ^ (-(1 / 6 : ℝ))) := by
    have e1' : ((J0 - 3 : ℕ) : ℝ) * (8 * (alphaCheck α * n / kAk k) * ρζ / (kAbs k * measDA m hm)) +
        8 * θQ * ρζ / (kAbs k * measDA m hm) =
        (8 * ρζ / (kAbs k * measDA m hm)) * ((((J0 - 3 : ℕ) : ℝ) + 1) * (u * n) +
          2 * ε * (J0 : ℝ) ^ (-(1 / 2 : ℝ)) + measAKappa m * n * (J0 : ℝ) ^ (-(2 : ℝ))) := by
      simp only [hθQ, hu]; ring
    rw [e1']
    have hnn : 0 ≤ 8 * ρζ / (kAbs k * measDA m hm) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hnn
    have a1 : (((J0 - 3 : ℕ) : ℝ) + 1) * (u * n) ≤ (J0 : ℝ) * u * n := by
      have : 0 ≤ u * n := by positivity
      nlinarith
    have a2 : 2 * ε * (J0 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 * ε * kAk k ^ (-(1 / 6 : ℝ)) :=
      mul_le_mul_of_nonneg_left hQ16 (by linarith)
    have a3 : measAKappa m * n * (J0 : ℝ) ^ (-(2 : ℝ)) ≤ measAKappa m * n * u ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hJ2 (by positivity)
    linarith
  refine hQ1.trans ?_
  have h1 : (J0 : ℝ) * u * n ≤ 2 * u ^ (2 / 3 : ℝ) * n := mul_le_mul_of_nonneg_right hJu hnpos.le
  have hnn : 0 ≤ 8 * ρζ / (kAbs k * measDA m hm) := by positivity
  calc (8 * ρζ / (kAbs k * measDA m hm)) * ((J0 : ℝ) * u * n + measAKappa m * n * u ^ (2 / 3 : ℝ) +
        2 * ε * kAk k ^ (-(1 / 6 : ℝ)))
      ≤ (8 * ρζ / (kAbs k * measDA m hm)) * (2 * u ^ (2 / 3 : ℝ) * n +
        measAKappa m * n * u ^ (2 / 3 : ℝ) + 2 * ε * kAk k ^ (-(1 / 6 : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith) hnn
    _ = _ := by simp only [hε]; ring

end

end KAM.Wave

end
