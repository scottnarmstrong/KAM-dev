/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.ResonanceGeometry.Blocks
public import KAM.Nekhoroshev.ResonanceGeometry.GeomFormula

/-!
# The Geometric Lemma (`bpN:p8:geometric`)

Non-resonance of the blocks: the rank-one case `B_Θ` (a) and the higher-rank case `B_Λ` (b),
following the five explicit steps (setting, volumes, the two projections, the divisor).
-/

@[expose] public noncomputable section
open Set Matrix Module Classical

namespace KAM.Nekhoroshev
open KAM.Stability
variable {n : ℕ}

theorem lattice_addVector_eq (Λ : Lattice n) (k : Fin n → ℤ) :
    lattice (addVector Λ k) = lattice Λ ⊔ Submodule.span ℝ {integerReal k} := by
  apply le_antisymm
  · refine lattice_le_iff.2 fun x hx => ?_
    obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hx
    obtain ⟨m, rfl⟩ := AddSubgroup.mem_closure_singleton.1 hz
    rw [integerReal_add, integerReal_zsmul]
    exact add_mem (Submodule.mem_sup_left (integerReal_mem_lattice hy))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  · refine sup_le (lattice_mono le_sup_left) ?_
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact integerReal_mem_lattice (AddSubgroup.mem_sup_right (AddSubgroup.subset_closure rfl))

theorem latticeDim_eq_zero_of_bot : latticeDim (⊥ : Lattice n) = 0 := latticeDim_bot

theorem ne_bot_of_dim_pos {Λ : Lattice n} (h : 1 ≤ latticeDim Λ) : Λ ≠ ⊥ := by
  rintro rfl; rw [latticeDim_bot] at h; omega

theorem not_mem_zone {lam : ℕ → ℝ} {Λ : Lattice n} (hΛ : Λ ≠ ⊥) {w : Fin n → ℝ}
    (h : w ∉ zone lam Λ) : lam (latticeDim Λ) / volume_def Λ ≤ resonanceDistance Λ w := by
  simp only [zone, hΛ, ↓reduceIte] at h
  exact not_lt.1 h

theorem lt_of_mem_zone {lam : ℕ → ℝ} {Λ : Lattice n} (hΛ : Λ ≠ ⊥) {w : Fin n → ℝ}
    (h : w ∈ zone lam Λ) : resonanceDistance Λ w < lam (latticeDim Λ) / volume_def Λ := by
  simp only [zone, hΛ, ↓reduceIte] at h
  exact h

/-- The span of one nonzero vector is the resonance-side line: its projection has norm
`|k ⬝ w| / ‖k‖`. -/
theorem euclid_proj_line {k : Fin n → ℝ} (hk : k ≠ 0) (w : Fin n → ℝ) :
    euclid (proj (Submodule.span ℝ {k}) w) * euclid k = |k ⬝ᵥ w| := by
  have hkV : k ∉ (⊥ : Submodule ℝ (Fin n → ℝ)) := by simpa using hk
  obtain ⟨-, -, -, h4, -⟩ := geom_formula (⊥ : Submodule ℝ (Fin n → ℝ)) k w hkV
  simp only [bot_sup_eq, projection_zero, LinearMap.zero_apply, sub_zero] at h4
  have hc : compProj (⊥ : Submodule ℝ (Fin n → ℝ)) k = k := by simp [compProj, projection_zero]
  rw [hc] at h4
  rw [h4]; ring

/-- A rank-one maximal lattice containing `k ≠ 0` has `lattice = ℝ k` and volume at most `‖k‖`. -/
theorem rank_one_facts {k : Fin n → ℤ} (hk0 : k ≠ 0) {Λ : Lattice n} (hd : latticeDim Λ = 1)
    (hkΛ : k ∈ Λ) :
    lattice Λ = Submodule.span ℝ {integerReal k} ∧ volume_def Λ ≤ euclid (integerReal k) := by
  have hik : integerReal k ≠ 0 := fun h =>
    hk0 (integerReal_injective (h.trans integerReal_zero.symm))
  have hli : LinearIndependent ℝ (fun _ : Fin 1 => integerReal k) :=
    LinearIndependent.of_subsingleton 0 hik
  have hcl : latticeDim (AddSubgroup.closure {k}) = 1 := by
    have h := latticeDim_closure (fun _ : Fin 1 => k) (integer_independent_of_real _ hli)
    simpa [Set.range_const] using h
  have hle : AddSubgroup.closure {k} ≤ Λ := (AddSubgroup.closure_le _).2 (by simpa using hkΛ)
  refine ⟨?_, ?_⟩
  · refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact integerReal_mem_lattice hkΛ
    · rw [finrank_span_singleton hik]; exact hd.symm
  · have := (lattice_volume Λ).2.2.2.2.2.1 _ hle (hcl.trans hd.symm)
    rw [lattice_volume_cyclic k hk0] at this
    exact this

/-- Part (a): the block `B_Θ` is completely `K`-nonresonant. -/
theorem geometric_theta {K : ℝ} (lam : ℕ → ℝ) (hl : 0 < lam 1) (hK : 0 < K) (hn : 1 ≤ n)
    {w : Fin n → ℝ} (hw : w ∈ blocks K lam (⊥ : Lattice n)) {k : Fin n → ℤ} (hk : k ∈ eBall n K)
    (hk0 : k ≠ 0) : lam 1 ≤ |integerReal k ⬝ᵥ w| := by
  obtain ⟨Λ, hΛ, hd, hkΛ⟩ := (maximal hK.le (⊥ : Lattice n)).2.2.2.2.1 k hk hk0
  have hnot : w ∉ zoneStratum K lam 1 := by
    have := hw.2
    rwa [latticeDim_bot, zero_add] at this
  have hwz : w ∉ zone lam Λ := fun h => hnot ⟨le_rfl, hn, Λ, hΛ, hd, h⟩
  have hdist := not_mem_zone (ne_bot_of_dim_pos hd.ge) hwz
  rw [hd] at hdist
  obtain ⟨hlat, hvol⟩ := rank_one_facts hk0 hd hkΛ
  have hik : integerReal k ≠ 0 := fun h =>
    hk0 (integerReal_injective (h.trans integerReal_zero.symm))
  have hpos : 0 < euclid (integerReal k) := by
    rcases (euclid_nonneg' (integerReal k)).lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.1 (by rw [← euclid_sq_eq_dot, ← h]; ring)) hik
  have hv1 := one_le_volume Λ
  have h1 : euclid (proj (lattice Λ) w) * euclid (integerReal k) = |integerReal k ⬝ᵥ w| := by
    rw [hlat]; exact euclid_proj_line hik w
  have hlam : lam 1 / euclid (integerReal k) ≤ lam 1 / volume_def Λ :=
    div_le_div_of_nonneg_left hl.le (by linarith) hvol
  rw [← h1]
  calc lam 1 = lam 1 / euclid (integerReal k) * euclid (integerReal k) := by field_simp
    _ ≤ _ := mul_le_mul (hlam.trans hdist) le_rfl hpos.le (euclid_nonneg' _)

/-- Part (b): the block `B_Λ` is `K`-nonresonant modulo `Λ`. -/
theorem geometric_lattice {K E A : ℝ} (hK : 0 < K) (hE : 0 < E)
    (hA : E + Real.sqrt 2 ≤ A) (lam : ℕ → ℝ)
    (hlam : ∀ d, 1 ≤ d → d ≤ n → 0 < lam d)
    (hratio : ∀ d, 1 ≤ d → d < n → A * K ≤ lam (d + 1) / lam d)
    {Λ : Lattice n} (hΛ : maximalK K Λ) (hd : 1 ≤ latticeDim Λ) {w : Fin n → ℝ}
    (hw : w ∈ blocks K lam Λ) {k : Fin n → ℤ} (hk : k ∈ eBall n K) (hkΛ : k ∉ Λ) :
    E * K * (lam (latticeDim Λ) / volume_def Λ) ≤ |integerReal k ⬝ᵥ w| := by
  set d := latticeDim Λ with hdd
  obtain ⟨hreal, hdn, hkl, hdim⟩ := (maximal hK.le Λ).2.2.2.2.2.1 hΛ k hk hkΛ
  obtain ⟨Λ', hΛ', hle, hdim'⟩ := exists_maximalK_above hkl
  have hdim2 : latticeDim Λ' = d + 1 := hdim'.trans hdim
  have hlatEq : lattice Λ' = lattice Λ ⊔ Submodule.span ℝ {integerReal k} := by
    rw [← lattice_addVector_eq]; exact (lattice_eq_of_le_dim hle hdim'.symm).symm
  have hkV : integerReal k ∉ lattice Λ := hreal
  obtain ⟨hq0, hform, hsplit, habs, hpyth⟩ := geom_formula (lattice Λ) (integerReal k) w hkV
  rw [← hlatEq] at hform habs hpyth
  set q := compProj (lattice Λ) (integerReal k) with hq
  set P := proj (lattice Λ) w
  set P' := proj (lattice Λ') w
  set s := euclid (P' - P) with hs
  -- volumes
  obtain ⟨-, -, -, -, -, hmono, haddv⟩ := lattice_volume Λ
  have hvadd := (haddv k hkV).2.1
  have hV'le : volume_def Λ' ≤ volume_def Λ * euclid q := by
    rw [← hvadd]; exact (lattice_volume Λ').2.2.2.2.2.1 _ hle hdim'.symm
  have hqK : euclid q ≤ K := by
    refine ((projection (lattice Λ)).2.2.2.2.2.1 _).2.trans hk
  have hV1 := one_le_volume Λ
  have hV'1 := one_le_volume Λ'
  have hV'K : volume_def Λ' ≤ K * volume_def Λ := by
    nlinarith
  -- zones
  have hΛne : Λ ≠ ⊥ := ne_bot_of_dim_pos hd
  have hΛ'ne : Λ' ≠ ⊥ := ne_bot_of_dim_pos (by omega)
  have hlt : euclid P < lam d / volume_def Λ := by
    have := lt_of_mem_zone hΛne hw.1
    exact this
  have hnot : w ∉ zone lam Λ' := fun h => hw.2 ⟨by omega, by omega, Λ', hΛ', hdim2, h⟩
  have hge := not_mem_zone hΛ'ne hnot
  rw [hdim2] at hge
  have hld := hlam d hd (by omega)
  have hrat := hratio d hd (by omega)
  rw [le_div_iff₀ hld] at hrat
  set L := K * lam d / volume_def Λ' with hL
  have hLpos : 0 < L := by positivity
  have hPL : euclid P < L := by
    refine hlt.trans_le ?_
    rw [hL, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hPL' : A * L ≤ euclid P' := by
    refine le_trans ?_ hge
    have : A * L = A * K * lam d / volume_def Λ' := by rw [hL]; ring
    rw [this]
    exact div_le_div_of_nonneg_right hrat (by linarith)
  obtain ⟨hA1, hA2⟩ := sqrt A (by
    have := Real.sqrt_nonneg 2; linarith)
  have hApos : 0 < A := by have := Real.sqrt_nonneg 2; linarith
  have hs0 : 0 ≤ s := euclid_nonneg' _
  have hP0 := euclid_nonneg' P
  have hs2 : (L * Real.sqrt (A ^ 2 - 1)) ^ 2 ≤ s ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    nlinarith [mul_pos hApos hLpos]
  have hsr : L * Real.sqrt (A ^ 2 - 1) ≤ s :=
    (pow_le_pow_iff_left₀ (by positivity) hs0 two_ne_zero).1 hs2
  have hqL : K * (lam d / volume_def Λ) ≤ euclid q * L := by
    have h1 : K * lam d ≤ euclid q * L * volume_def Λ := by
      have : volume_def Λ' * L = K * lam d := by rw [hL]; field_simp
      rw [← this]
      nlinarith [hLpos]
    rw [← div_le_iff₀ (by linarith)] at h1
    calc K * (lam d / volume_def Λ) = K * lam d / volume_def Λ := by ring
      _ ≤ _ := h1
  set δ := lam d / volume_def Λ with hδ
  have hδpos : 0 < δ := div_pos hld (by linarith)
  have hr0 := Real.sqrt_nonneg (A ^ 2 - 1)
  have hqs : K * δ * Real.sqrt (A ^ 2 - 1) ≤ |q ⬝ᵥ w| := by
    rw [habs]
    calc K * δ * Real.sqrt (A ^ 2 - 1) ≤ (euclid q * L) * Real.sqrt (A ^ 2 - 1) :=
          mul_le_mul_of_nonneg_right hqL hr0
      _ = euclid q * (L * Real.sqrt (A ^ 2 - 1)) := by ring
      _ ≤ euclid q * s := mul_le_mul_of_nonneg_left hsr (euclid_nonneg' _)
  have hdot : |proj (lattice Λ) (integerReal k) ⬝ᵥ P| ≤ K * δ := by
    refine (abs_dot_le_euclid _ _).trans ?_
    have h1 := ((projection (lattice Λ)).2.2.2.2.2.1 (integerReal k)).1
    exact mul_le_mul (h1.trans hk) hlt.le hP0 hK.le
  have hfin : |integerReal k ⬝ᵥ w| ≥ |q ⬝ᵥ w| - |proj (lattice Λ) (integerReal k) ⬝ᵥ P| := by
    rw [hsplit]
    have := abs_sub_abs_le_abs_sub (q ⬝ᵥ w) (-(proj (lattice Λ) (integerReal k) ⬝ᵥ P))
    rw [abs_neg, sub_neg_eq_add, add_comm] at this
    exact this
  have hKδ : 0 ≤ K * δ := by positivity
  have hEA : E ≤ A - Real.sqrt 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left (hEA.trans hA2) hKδ]

theorem geometric (hn : 1 ≤ n) {K E A : ℝ} (hK : 0 < K) (hE : 0 < E)
    (hA : E + Real.sqrt 2 ≤ A) (lam : ℕ → ℝ)
    (hlam : ∀ d, 1 ≤ d → d ≤ n → 0 < lam d)
    (hratio : ∀ d, 1 ≤ d → d < n → A * K ≤ lam (d + 1) / lam d) :
    (∀ w ∈ blocks K lam (⊥ : Lattice n), ∀ k ∈ eBall n K, k ≠ 0 → lam 1 ≤ |integerReal k ⬝ᵥ w|) ∧
    (∀ Λ : Lattice n, maximalK K Λ → 1 ≤ latticeDim Λ → ∀ w ∈ blocks K lam Λ,
      resonanceDistance Λ w < lam (latticeDim Λ) / volume_def Λ ∧
      ∀ k ∈ eBall n K, k ∉ Λ → E * K * (lam (latticeDim Λ) / volume_def Λ) ≤
        |integerReal k ⬝ᵥ w|) :=
  ⟨fun _ hw _ hk hk0 => geometric_theta lam (hlam 1 le_rfl hn) hK hn hw hk hk0,
    fun _ hΛ hd _ hw =>
      ⟨lt_of_mem_zone (ne_bot_of_dim_pos hd) hw.1, fun _ hk hkΛ =>
        geometric_lattice hK hE hA lam hlam hratio hΛ hd hw hk hkΛ⟩⟩

end KAM.Nekhoroshev
