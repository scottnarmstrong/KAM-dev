/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.MinusSum

/-!
# W7: the preparatory zones of `Λ⁻` (blueprint `bpW:w7:prep`, steps "`Λ⁻`")

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

With the weight exponent `β = 1/4` and `j₀ = ⌈(A_k/α̂)^{4/11}⌉`:
for fixed `k ≠ 0` and `n ≥ 1` the union over `j` of the preparatory zones of `e_{j+n} - e_j` has
measure `≤ 8 ρ_ζ n (3 + a_κ) (α̂/A_k)^{8/11} / (|k| D_A)`.
-/

@[expose] public noncomputable section

open Real Finsupp MeasureTheory

namespace KAM.Wave

theorem linF_neg (l : ℕ →₀ ℤ) (f : ℕ → ℝ) : linF (-l) f = - linF l f := by
  unfold linF Finsupp.sum
  rw [Finsupp.support_neg, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun ν _ => by simp

theorem rpow_neg_two_eq {x : ℝ} (hx : 0 ≤ x) : x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_two]

section

variable (m : ℝ) (hm : 0 < m)
variable {Pi : Set (Fin 2 → ℝ)} {α : ℝ}

theorem prepZone_neg (a : ℝ) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) :
    prepZone m hm Pi a k (-l) = prepZone m hm Pi a (-k) l := by
  ext ξ
  simp only [prepZone, Set.mem_ofPred_eq, hatW_neg, kAk_neg, linF_neg]
  have : ∑ i, (((-k) i : ℤ) : ℝ) * omegaTan m hm ξ i = -∑ i, (k i : ℝ) * omegaTan m hm ξ i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp
  rw [this, ← abs_neg]
  have : -(∑ i, (k i : ℝ) * omegaTan m hm ξ i + -linF l (omegaNor m hm ξ)) =
      -∑ i, (k i : ℝ) * omegaTan m hm ξ i + linF l (omegaNor m hm ξ) := by ring
  rw [this]

theorem prepZone_minus (a : ℝ) (k : Fin 2 → ℤ) (j n : ℕ) (hn : 1 ≤ n) :
    prepZone m hm Pi a k (lamMinusPlus j n) =
      genZone Pi (omegaTan m hm) (omegaNor m hm)
        (a * ((n : ℝ) * normLab j ^ (-(1 / 4 : ℝ))) / kAk k) k (lamMinusPlus j n) := by
  have h := hatW_minus (i := j + n) (j := j) (σ := 1) (by omega) (Or.inl rfl)
  have e : hatW (lamMinusPlus j n) = (n : ℝ) * normLab j ^ (-(1 / 4 : ℝ)) := by
    unfold lamMinusPlus
    rw [show (-1 : ℤ) = -(1 : ℤ) by norm_num, h]; push_cast; ring_nf
  ext ξ
  simp only [prepZone, genZone, Set.mem_ofPred_eq, e]

/-- For fixed `k ≠ 0` and `n ≥ 1`. -/
theorem prep_minus_n_bound (hS : MeasSetup m hm Pi α) {ρζ : ℝ} (hρ0 : 0 ≤ ρζ)
    (hρζ : ∀ ξ ∈ Pi, ∀ ξ' ∈ Pi, ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤ ρζ)
    {k : Fin 2 → ℤ} (hk : k ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    volume (⋃ (j : ℕ) (_ : (k, lamMinusPlus j n) ∉ measXSet m hm),
        prepZone m hm Pi (alphaHat α) k (lamMinusPlus j n)) ≤
      ENNReal.ofReal (8 * ρζ * (3 + measAKappa m) *
        (alphaHat α / kAk k) ^ (8 / 11 : ℝ) / (kAbs k * measDA m hm) * n) := by
  obtain ⟨hc, hcA, hαhat, h27, hβ4, -⟩ := alpha_facts m hm hS.alpha_pos hS.alpha_le
  have hP := isFreqPair_unpert m hm hS.meas hS.alpha_pos.le
  have hα0 : 0 < alphaHat α := lt_of_lt_of_le hS.alpha_pos hαhat
  have hA := kAk_pos k
  have hDA := measDA_pos m hm
  have hk1 := one_le_kAbs hk
  have hκ := measAKappa_pos hm
  set u : ℝ := alphaHat α / kAk k with hu
  have hu0 : 0 < u := by positivity
  have hu27 : u ≤ 1 / 27 := by
    refine (div_le_self hα0.le hA).trans h27
  set J0 : ℕ := ⌈u ^ (-(4 / 11 : ℝ))⌉₊ with hJ0
  obtain ⟨hJ3, hreal⟩ := prep_real_bound hu0 hu27 hκ.le J0 hJ0
  have hJpos : (0 : ℝ) < J0 := by
    have : (3 : ℝ) ≤ J0 := by exact_mod_cast hJ3
    linarith
  set η : ℕ → ℝ := fun j => alphaHat α * ((n : ℝ) * normLab j ^ (-(1 / 4 : ℝ))) / kAk k with hη
  set θQ : ℝ := n * (u * (J0 : ℝ) ^ (-(1 / 4 : ℝ)) + measAKappa m * (J0 : ℝ) ^ (-(2 : ℝ))) with hθQ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hη_pos : ∀ j, 0 < η j := fun j => by
    have := Real.rpow_pos_of_pos (normLab_pos j) (-(1 / 4 : ℝ)); simp only [hη]; positivity
  have hη_le : ∀ j, η j ≤ alphaHat α * n / kAk k := fun j => by
    simp only [hη]
    have h1 := normLab_rpow_le_one (ν := j) (δ := -(1 / 4 : ℝ)) (by norm_num)
    have hApos : 0 < kAk k := by linarith
    have h2 : (n : ℝ) * normLab j ^ (-(1 / 4 : ℝ)) ≤ n := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ n)
      linarith
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hα0.le) hApos.le
  have hθQ_pos : 0 < θQ := by
    have h1 := Real.rpow_pos_of_pos hJpos (-(1 / 4 : ℝ))
    have h2 := Real.rpow_pos_of_pos hJpos (-(2 : ℝ))
    simp only [hθQ]; positivity
  have hmain := hP.minus_n_bound m hm hS hα0 le_rfl hk hn (J0 - 3) η hη_pos hη_le hθQ_pos hρ0 hρζ
    (fun j hj ξ ⟨hξ, hz⟩ => by
      refine ⟨hξ, ?_⟩
      have hξ12 := hS.sub ξ hξ
      have hlab : (J0 : ℝ) ≤ normLab j := by
        unfold normLab
        have : (J0 : ℝ) - 3 ≤ j := by
          have h := (Nat.cast_le (α := ℝ)).2 hj
          rw [Nat.cast_sub hJ3] at h; push_cast at h; linarith
        linarith
      have happ := omegaNor_sub_approx m hm hξ12 (i := j + n) (j := j) (by omega)
      have hl : linF (single (j + n) 1 + single j (-1)) (omegaNor m hm ξ) =
          omegaNor m hm ξ (j + n) - omegaNor m hm ξ j := by
        rw [show (-1 : ℤ) = -(1 : ℤ) by norm_num, linF_minus (by omega)]; push_cast; ring
      have hd : normLab (j + n) - normLab j = n := by unfold normLab; push_cast; ring
      rw [hd] at happ
      rw [hl] at hz
      simp only [hη] at hz
      have hz' : |∑ i, ((k i : ℤ) : ℝ) * omegaTan m hm ξ i + (omegaNor m hm ξ (j + n) - omegaNor m
          hm ξ j)| <
          alphaHat α * ((n : ℝ) * normLab j ^ (-(1 / 4 : ℝ))) / kAk k := hz
      have h1 : normLab j ^ (-(1 / 4 : ℝ)) ≤ (J0 : ℝ) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hJpos hlab (by norm_num)
      have h2 : measAKappa m * n / normLab j ^ 2 ≤ measAKappa m * n * (J0 : ℝ) ^ (-(2 : ℝ)) := by
        rw [rpow_neg_two_eq hJpos.le, ← div_eq_mul_inv]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith
      have h3 : alphaHat α * ((n : ℝ) * normLab j ^ (-(1 / 4 : ℝ))) / kAk k ≤
          n * (u * (J0 : ℝ) ^ (-(1 / 4 : ℝ))) := by
        rw [hu]
        have h0 := Real.rpow_nonneg hJpos.le (-(1 / 4 : ℝ))
        calc alphaHat α * ((n : ℝ) * normLab j ^ (-(1 / 4 : ℝ))) / kAk k
            = (n : ℝ) * (alphaHat α / kAk k * normLab j ^ (-(1 / 4 : ℝ))) := by ring
          _ ≤ (n : ℝ) * (alphaHat α / kAk k * (J0 : ℝ) ^ (-(1 / 4 : ℝ))) := by gcongr
      have e0 : ∑ i, ((k i : ℤ) : ℝ) * omegaTan m hm ξ i + (n : ℝ) =
          (∑ i, ((k i : ℤ) : ℝ) * omegaTan m hm ξ i +
            (omegaNor m hm ξ (j + n) - omegaNor m hm ξ j)) -
          (omegaNor m hm ξ (j + n) - omegaNor m hm ξ j - n) := by ring
      rw [e0]
      refine lt_of_le_of_lt (abs_sub _ _) ?_
      have : measAKappa m * (n : ℝ) / normLab j ^ 2 =
          measAKappa m * n / normLab j ^ 2 := rfl
      simp only [hθQ]
      nlinarith [abs_nonneg (omegaNor m hm ξ (j + n) - omegaNor m hm ξ j - n)])
  rw [show (⋃ (j : ℕ) (_ : (k, lamMinusPlus j n) ∉ measXSet m hm),
      prepZone m hm Pi (alphaHat α) k (lamMinusPlus j n)) = ⋃ (j : ℕ)
      (_ : (k, lamMinusPlus j n) ∉ measXSet m hm), genZone Pi (omegaTan m hm) (omegaNor m hm)
      (η j) k (lamMinusPlus j n) from by
    ext x; simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj, hx⟩; exact ⟨j, hj, by rwa [prepZone_minus m hm _ _ _ _ hn] at hx⟩
    · rintro ⟨j, hj, hx⟩; exact ⟨j, hj, by rwa [prepZone_minus m hm _ _ _ _ hn]⟩]
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hD : 0 < kAbs k * measDA m hm := by positivity
  have eS : ∑ j ∈ Finset.range (J0 - 3), 8 * η j * ρζ / (kAbs k * measDA m hm) =
      (8 * ρζ * n / (kAbs k * measDA m hm)) *
        (u * ∑ j ∈ Finset.range (J0 - 3), ((j : ℝ) + 3) ^ (-(1 / 4 : ℝ))) := by
    simp only [hη, hu, normLab]
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have eQ : 8 * θQ * ρζ / (kAbs k * measDA m hm) = (8 * ρζ * n / (kAbs k * measDA m hm)) *
      (u * (J0 : ℝ) ^ (-(1 / 4 : ℝ)) + measAKappa m * (J0 : ℝ) ^ (-(2 : ℝ))) := by
    simp only [hθQ]; ring
  rw [eS, eQ, ← mul_add]
  have hnn : 0 ≤ 8 * ρζ * n / (kAbs k * measDA m hm) := by positivity
  calc (8 * ρζ * n / (kAbs k * measDA m hm)) * (u * ∑ j ∈ Finset.range (J0 - 3),
        ((j : ℝ) + 3) ^ (-(1 / 4 : ℝ)) + (u * (J0 : ℝ) ^ (-(1 / 4 : ℝ)) +
        measAKappa m * (J0 : ℝ) ^ (-(2 : ℝ))))
      ≤ (8 * ρζ * n / (kAbs k * measDA m hm)) * ((3 + measAKappa m) * u ^ (8 / 11 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hnn
        have := hreal
        nlinarith
    _ = _ := by simp only [hu]; ring

end

end KAM.Wave

end
