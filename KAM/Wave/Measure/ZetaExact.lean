/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.ZetaSum

/-!
# W7: exact lattice sums (blueprint `bpW:w7:ext-zeta`, `bpW:w7:count` (iii))

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

The exact statements of `bpW:w7:ext-zeta` and `bpW:w7:count` (iii): `#{k ∈ ℤ² : |k| = N} = 4N`
for `N ≥ 1`, and `Z₃ = ∑_{k ∈ ℤ² ∖ 0} |k|^{-3} = 4 ζ(2) = 2π²/3 < 7`. The upper bounds used by the
measure estimate are in `KAM.Wave.Measure.ZetaSum`.
-/

@[expose] public noncomputable section

open Real Set

namespace KAM.Wave

/-- `#{k ∈ ℤ² : |k₁| + |k₂| = N} = 4N` for `N ≥ 1` (blueprint `bpW:w7:ext-zeta`). -/
theorem encard_l1Sphere_eq {N : ℕ} (hN : 1 ≤ N) : (waveL1Sphere N).encard = 4 * N := by
  refine le_antisymm (encard_l1Sphere_le hN) ?_
  -- four disjoint injective families inside the sphere, one per quadrant
  set f0 : ℕ → (Fin 2 → ℤ) := fun t => ![(t : ℤ), (N : ℤ) - t] with hf0
  set f1 : ℕ → (Fin 2 → ℤ) := fun t => ![-((N : ℤ) - t), (t : ℤ)] with hf1
  set f2 : ℕ → (Fin 2 → ℤ) := fun t => ![-(t : ℤ), -((N : ℤ) - t)] with hf2
  set f3 : ℕ → (Fin 2 → ℤ) := fun t => ![(N : ℤ) - t, -(t : ℤ)] with hf3
  have c0 : ∀ t, f0 t 0 = t ∧ f0 t 1 = N - t := fun t => by simp [hf0]
  have c1 : ∀ t, f1 t 0 = -(N - t) ∧ f1 t 1 = t := fun t => by simp [hf1]
  have c2 : ∀ t, f2 t 0 = -t ∧ f2 t 1 = -(N - t) := fun t => by simp [hf2]
  have c3 : ∀ t, f3 t 0 = N - t ∧ f3 t 1 = -t := fun t => by simp [hf3]
  have i0 : Function.Injective f0 := fun t t' h => by
    have := congrFun h 0; rw [(c0 t).1, (c0 t').1] at this; exact_mod_cast this
  have i1 : Function.Injective f1 := fun t t' h => by
    have := congrFun h 1; rw [(c1 t).2, (c1 t').2] at this; exact_mod_cast this
  have i2 : Function.Injective f2 := fun t t' h => by
    have := congrFun h 0; rw [(c2 t).1, (c2 t').1] at this; omega
  have i3 : Function.Injective f3 := fun t t' h => by
    have := congrFun h 1; rw [(c3 t).2, (c3 t').2] at this; omega
  set S0 := (Finset.range N).image f0
  set S1 := (Finset.range N).image f1
  set S2 := (Finset.range N).image f2
  set S3 := (Finset.range N).image f3
  -- quadrant description of each family
  have q0 : ∀ x ∈ S0, 0 ≤ x 0 ∧ 1 ≤ x 1 ∧ (x 0).natAbs + (x 1).natAbs = N := by
    intro x hx
    simp only [S0, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [(c0 t).1, (c0 t).2]; omega
  have q1 : ∀ x ∈ S1, x 0 ≤ -1 ∧ 0 ≤ x 1 ∧ (x 0).natAbs + (x 1).natAbs = N := by
    intro x hx
    simp only [S1, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [(c1 t).1, (c1 t).2]; omega
  have q2 : ∀ x ∈ S2, x 0 ≤ 0 ∧ x 1 ≤ -1 ∧ (x 0).natAbs + (x 1).natAbs = N := by
    intro x hx
    simp only [S2, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [(c2 t).1, (c2 t).2]; omega
  have q3 : ∀ x ∈ S3, 1 ≤ x 0 ∧ x 1 ≤ 0 ∧ (x 0).natAbs + (x 1).natAbs = N := by
    intro x hx
    simp only [S3, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [(c3 t).1, (c3 t).2]; omega
  have d01 : Disjoint S0 S1 := Finset.disjoint_left.2 fun x hx hx' => by
    have := q0 x hx; have := q1 x hx'; omega
  have d012 : Disjoint (S0 ∪ S1) S2 := by
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_left.2 fun x hx hx' => by have := q0 x hx; have := q2 x hx'; omega,
      Finset.disjoint_left.2 fun x hx hx' => by have := q1 x hx; have := q2 x hx'; omega⟩
  have d0123 : Disjoint (S0 ∪ S1 ∪ S2) S3 := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
    exact ⟨⟨Finset.disjoint_left.2 fun x hx hx' => by have := q0 x hx; have := q3 x hx'; omega,
      Finset.disjoint_left.2 fun x hx hx' => by have := q1 x hx; have := q3 x hx'; omega⟩,
      Finset.disjoint_left.2 fun x hx hx' => by have := q2 x hx; have := q3 x hx'; omega⟩
  have hcard : (S0 ∪ S1 ∪ S2 ∪ S3).card = 4 * N := by
    rw [Finset.card_union_of_disjoint d0123, Finset.card_union_of_disjoint d012,
      Finset.card_union_of_disjoint d01]
    simp only [S0, S1, S2, S3, Finset.card_image_of_injective _ i0,
      Finset.card_image_of_injective _ i1, Finset.card_image_of_injective _ i2,
      Finset.card_image_of_injective _ i3, Finset.card_range]
    ring
  have hsub : ((S0 ∪ S1 ∪ S2 ∪ S3 : Finset (Fin 2 → ℤ)) : Set (Fin 2 → ℤ)) ⊆ waveL1Sphere N := by
    intro x hx
    simp only [waveL1Sphere, mem_ofPred_eq]
    simp only [Finset.coe_union, mem_union, Finset.mem_coe] at hx
    rcases hx with ((h | h) | h) | h
    · exact (q0 x h).2.2
    · exact (q1 x h).2.2
    · exact (q2 x h).2.2
    · exact (q3 x h).2.2
  calc (4 * N : ℕ∞) = ((S0 ∪ S1 ∪ S2 ∪ S3).card : ℕ∞) := by rw [hcard]; push_cast; ring
    _ = ((S0 ∪ S1 ∪ S2 ∪ S3 : Finset (Fin 2 → ℤ)) : Set (Fin 2 → ℤ)).encard :=
        (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ (waveL1Sphere N).encard := Set.encard_le_encard hsub

/-- The lattice sum in extended reals: `∑_{k ≠ 0} |k|^{-3} = 2π²/3`. -/
theorem tsum_lattice_inv_cube_ennreal :
    ∑' k : Fin 2 → ℤ, ENNReal.ofReal (if k = 0 then 0 else (kAbs k ^ 3)⁻¹) =
      ENNReal.ofReal measZ3 := by
  set F : (Fin 2 → ℤ) → ENNReal := fun k => ENNReal.ofReal (if k = 0 then 0 else (kAbs k ^ 3)⁻¹)
    with hF
  let p : (Fin 2 → ℤ) → ℕ := fun k => (k 0).natAbs + (k 1).natAbs
  rw [← (Equiv.sigmaFiberEquiv p).tsum_eq, ENNReal.tsum_sigma']
  have hfib : ∀ n : ℕ, ∑' c : {k // p k = n}, F ((Equiv.sigmaFiberEquiv p) ⟨n, c⟩) =
      if n = 0 then 0 else ENNReal.ofReal (4 / (n : ℝ) ^ 2) := by
    intro n
    have hval : ∀ c : {k // p k = n}, F ((Equiv.sigmaFiberEquiv p) ⟨n, c⟩) =
        if n = 0 then 0 else ENNReal.ofReal ((n : ℝ) ^ 3)⁻¹ := by
      rintro ⟨k, hk⟩
      simp only [Equiv.sigmaFiberEquiv_apply, hF]
      have hkA : kAbs k = n := kAbs_eq_of_mem_l1Sphere (N := n) hk
      by_cases hn : n = 0
      · have hk0 : k = 0 := by
          simp only [p] at hk
          ext i; fin_cases i <;> simp <;> omega
        simp [hn, hk0]
      · have hk0 : k ≠ 0 := by
          rintro rfl; simp [p] at hk; exact hn hk.symm
        simp [hn, hk0, hkA]
    simp_rw [hval]
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      rw [show (∑' _ : {k // p k = n}, ENNReal.ofReal ((n : ℝ) ^ 3)⁻¹) =
          ∑' _ : waveL1Sphere n, ENNReal.ofReal ((n : ℝ) ^ 3)⁻¹ from rfl,
        ENNReal.tsum_set_const, encard_l1Sphere_eq (Nat.one_le_iff_ne_zero.2 hn)]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have e : ((4 * n : ℕ∞) : ENNReal) = ENNReal.ofReal (4 * (n : ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num)]; simp
      rw [e, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
  refine Eq.trans (tsum_congr hfib) ?_
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [↓reduceIte, zero_add, Nat.add_one_ne_zero, Nat.cast_add, Nat.cast_one]
  have hsum : HasSum (fun n : ℕ => 4 / ((n : ℝ) + 1) ^ 2) (4 * (π ^ 2 / 6)) := by
    have h := ((hasSum_nat_add_iff' 1).2 hasSum_zeta_two).mul_left 4
    convert h using 1
    · funext n; simp; ring
    · simp
  have hnn : ∀ n : ℕ, 0 ≤ 4 / ((n : ℝ) + 1) ^ 2 := fun n => by positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable, hsum.tsum_eq, measZ3]
  congr 1; ring

/-- `Z₃ = ∑_{k ∈ ℤ² ∖ 0} |k|^{-3}` with `Z₃ = 2π²/3` (blueprint `bpW:w7:count` (iii),
`bpW:w7:ext-zeta`). -/
theorem hasSum_lattice_inv_cube :
    HasSum (fun k : Fin 2 → ℤ => if k = 0 then 0 else (kAbs k ^ 3)⁻¹) measZ3 := by
  have hnn : ∀ k : Fin 2 → ℤ, 0 ≤ (if k = 0 then 0 else (kAbs k ^ 3)⁻¹ : ℝ) := fun k => by
    split_ifs
    · exact le_rfl
    · have := kAbs_nonneg k; positivity
  have h := tsum_lattice_inv_cube_ennreal
  have hfin : ∑' k : Fin 2 → ℤ, ENNReal.ofReal (if k = 0 then 0 else (kAbs k ^ 3)⁻¹) ≠ ⊤ := by
    rw [h]; exact ENNReal.ofReal_ne_top
  have hs := ENNReal.summable_toReal hfin
  simp only [ENNReal.toReal_ofReal (hnn _)] at hs
  have ht := ENNReal.tsum_toReal_eq (f := fun k : Fin 2 → ℤ =>
    ENNReal.ofReal (if k = 0 then 0 else (kAbs k ^ 3)⁻¹)) fun _ => ENNReal.ofReal_ne_top
  rw [h, ENNReal.toReal_ofReal (by unfold measZ3; positivity)] at ht
  simp only [ENNReal.toReal_ofReal (hnn _)] at ht
  rw [ht]
  exact hs.hasSum

/-- `Z₃ < 7` (blueprint `bpW:w7:count` (iii)). -/
theorem measZ3_lt_seven : measZ3 < 7 := by
  have h1 := Real.pi_lt_d2
  have h0 := Real.pi_pos
  unfold measZ3
  nlinarith

/-- `∑_{k ≠ 0} |k|^{-3} = Z₃ < 7` (blueprint `bpW:w7:count` (iii)). -/
theorem tsum_lattice_inv_cube :
    ∑' k : Fin 2 → ℤ, (if k = 0 then 0 else (kAbs k ^ 3)⁻¹) = measZ3 ∧ measZ3 < 7 :=
  ⟨hasSum_lattice_inv_cube.tsum_eq, measZ3_lt_seven⟩

end KAM.Wave

end
