/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.UnpertBounds

/-!
# W7: the exceptional set `X` and the constants (blueprint `bpW:w7:Xdef`, `bpW:w7:constdef`)

The constants of `bpW:w7:constdef` in the order (C1)–(C5): `W`, `ϑ`, `c_Λ`, `K_*`, `j_*`; the finite
exceptional set `X` with `N_X`, `σ_X`, `c_X`; `θ₀`, `α₀`; `Z₃`, `C_P`, `C_I`, `C₇`; and
`α̂ = α^{44/47}`, `α̌ = α^{48/47}`. All depend on `m` only.
-/

@[expose] public noncomputable section

open Real Finsupp

namespace KAM.Wave

section

variable (m : ℝ) (hm : 0 < m)

/-- `W = λ₂ + 1`. -/
def measW : ℝ := lamTan m hm 1 + 1

/-- `ϑ = β_* / W`. -/
def measTheta : ℝ := measBetaStar m / measW m hm

/-- `c_Λ = (4/7)(λ₁ + λ₂) + 1`. -/
def measCLam : ℝ := 4 / 7 * (lamTan m hm 0 + lamTan m hm 1) + 1

/-- `K_* = 16 c_Λ`. -/
def measKstar : ℝ := 16 * measCLam m hm

/-- `j_* = (16 c_Λ)²`. -/
def measJstar : ℝ := (16 * measCLam m hm) ^ 2

/-- The exceptional set `X` (blueprint `bpW:w7:Xdef`). -/
def measXSet : Set ((Fin 2 → ℤ) × (ℕ →₀ ℤ)) :=
  {kl | IsLam kl.2 ∧ 1 ≤ kAbs kl.1 ∧ kAbs kl.1 < measKstar m hm ∧
    japL kl.2 < measKstar m hm / measTheta m hm ∧
    (¬ IsLamMinus kl.2 ∨ normLab (sInf {ν | kl.2 ν ≠ 0}) < measJstar m hm)}

/-- The gradient `p_{kl} = k + (4/7)(∑_j l_j/λ_j) λ_J` of the affine function `g_{kl}`. -/
def measPX (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) : Fin 2 → ℝ :=
  fun i => (k i : ℝ) + 4 / 7 * linF l (fun ν => 1 / lamN m hm ν) * lamTan m hm i

/-- `|⟨k, λ_J⟩ + ⟨l, λ⟩|`. -/
def measCval (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) : ℝ :=
  |∑ i, (k i : ℝ) * lamTan m hm i + linF l (lamN m hm)|

theorem measW_pos : 0 < measW m hm := by
  unfold measW; linarith [lamTan_pos m hm 1]

theorem measTheta_pos : 0 < measTheta m hm := by
  unfold measTheta
  exact div_pos (measBetaStar_pos hm) (measW_pos m hm)

theorem measTheta_le : measTheta m hm ≤ 1 / 18 := by
  unfold measTheta
  have h1 := measBetaStar_le hm
  have h2 := (measLam_facts m hm).2.2
  have hW : 3 < measW m hm := by unfold measW; linarith
  rw [div_le_iff₀ (measW_pos m hm)]
  nlinarith [measBetaStar_pos hm]

theorem measCLam_pos : 1 ≤ measCLam m hm := by
  unfold measCLam
  have := lamTan_pos m hm 0
  have := lamTan_pos m hm 1
  linarith

theorem measKstar_pos : 16 ≤ measKstar m hm := by
  unfold measKstar; linarith [measCLam_pos m hm]

theorem measJstar_pos : 256 ≤ measJstar m hm := by
  unfold measJstar; nlinarith [measCLam_pos m hm]

/-- `X` is finite (blueprint `bpW:w7:dichotomy`, step "Finite"). -/
theorem measXSet_finite : (measXSet m hm).Finite := by
  set N := measKstar m hm / measTheta m hm with hN
  set J := measJstar m hm with hJ
  set K := measKstar m hm with hK
  set B : ℕ := ⌈N⌉₊ + ⌈J⌉₊ + 1 with hB
  -- finitely many `l`
  have hl : {l : ℕ →₀ ℤ | IsLam l ∧ japL l < N ∧ (¬ IsLamMinus l ∨ normLab (sInf {ν | l ν ≠ 0}) <
      J)}.Finite := by
    have hfin := Finset.finite_toSet ((Finset.range B ×ˢ Finset.range B ×ˢ Finset.Icc (-2 : ℤ) 2 ×ˢ
        Finset.Icc (-2 : ℤ) 2).image
        (fun x : ℕ × ℕ × ℤ × ℤ => single x.1 x.2.2.1 + single x.2.1 x.2.2.2))
    refine hfin.subset ?_
    have key : ∀ (a b : ℕ) (σ τ : ℤ), a < B → b < B → -2 ≤ σ → σ ≤ 2 → -2 ≤ τ → τ ≤ 2 →
        single a σ + single b τ ∈ (↑((Finset.range B ×ˢ Finset.range B ×ˢ Finset.Icc (-2 : ℤ) 2 ×ˢ
          Finset.Icc (-2 : ℤ) 2).image
          (fun x : ℕ × ℕ × ℤ × ℤ => single x.1 x.2.2.1 + single x.2.1 x.2.2.2)) : Set (ℕ →₀ ℤ)) :=
              by
      intro a b σ τ ha hb h1 h2 h3 h4
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(a, b, σ, τ), ?_, rfl⟩)
      simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
      exact ⟨ha, hb, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have hB0 : 0 < B := by rw [hB]; omega
    have hNB : N ≤ ⌈N⌉₊ := Nat.le_ceil _
    have hJB : J ≤ ⌈J⌉₊ := Nat.le_ceil _
    have hJ0 : (0 : ℝ) ≤ ⌈J⌉₊ := Nat.cast_nonneg _
    have hN0 : (0 : ℝ) ≤ ⌈N⌉₊ := Nat.cast_nonneg _
    have hBr : (B : ℝ) = ⌈N⌉₊ + ⌈J⌉₊ + 1 := by rw [hB]; push_cast; ring
    rintro l ⟨hl, hj, hx⟩
    rcases lam_cases l hl with ⟨a, σ, hσ, rfl⟩ | ⟨a, b, σ, hab, hσ, rfl⟩ | hmn
    · have hja := japL_single a hσ
      have h3 := normLab_ge a
      have h1 : (1 : ℝ) ≤ |(σ : ℝ)| := by rcases hσ with rfl | rfl | rfl | rfl <;> norm_num
      have haN : (a : ℝ) < N := by
        rw [hja] at hj
        have := normLab_pos a
        unfold normLab at hj h3
        nlinarith [abs_nonneg (σ : ℝ)]
      have haB : a < B := by
        have : (a : ℝ) < B := by rw [hBr]; linarith
        exact_mod_cast this
      have := key a 0 σ 0 haB hB0 (by rcases hσ with rfl | rfl | rfl | rfl <;> norm_num)
        (by rcases hσ with rfl | rfl | rfl | rfl <;> norm_num) (by norm_num) (by norm_num)
      simpa using this
    · have hja := japL_pair hab.ne hσ
      have h3 := normLab_ge a
      have h4 := normLab_ge b
      have hbN : (b : ℝ) < N := by rw [hja] at hj; unfold normLab at hj h3 h4; linarith
      have haN : (a : ℝ) < N := by rw [hja] at hj; unfold normLab at hj h3 h4; linarith
      have haB : a < B := by
        have : (a : ℝ) < B := by rw [hBr]; linarith
        exact_mod_cast this
      have hbB : b < B := by
        have : (b : ℝ) < B := by rw [hBr]; linarith
        exact_mod_cast this
      exact key a b σ σ haB hbB (by rcases hσ with rfl | rfl <;> norm_num)
        (by rcases hσ with rfl | rfl <;> norm_num) (by rcases hσ with rfl | rfl <;> norm_num)
        (by rcases hσ with rfl | rfl <;> norm_num)
    · obtain ⟨i, j, σ, hji, hσ, rfl⟩ := hmn
      have hja := japL_minus hji hσ
      have hsj := sInf_minus hji σ hσ
      have hjJ : normLab j < J := by
        rcases hx with hx | hx
        · exact absurd ⟨i, j, σ, hji, hσ, rfl⟩ hx
        · rwa [hsj] at hx
      have h3 := normLab_ge j
      have hjJ' : (j : ℝ) < J := by unfold normLab at hjJ; linarith
      have hiN : (i : ℝ) < N + J := by
        rw [hja] at hj
        linarith
      have hiB : i < B := by
        have : (i : ℝ) < B := by rw [hBr]; linarith
        exact_mod_cast this
      have hjB : j < B := by
        have : (j : ℝ) < B := by rw [hBr]; linarith
        exact_mod_cast this
      exact key i j σ (-σ) hiB hjB (by rcases hσ with rfl | rfl <;> norm_num)
        (by rcases hσ with rfl | rfl <;> norm_num) (by rcases hσ with rfl | rfl <;> norm_num)
        (by rcases hσ with rfl | rfl <;> norm_num)
  -- finitely many `k`
  have hk : {k : Fin 2 → ℤ | kAbs k < K}.Finite := by
    have hpi : (Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-(⌈K⌉ : ℤ)) ⌈K⌉)).Finite :=
      Set.Finite.pi fun _ => Set.finite_Icc _ _
    refine hpi.subset ?_
    intro k hk i _
    have h1 : |(k i : ℝ)| ≤ kAbs k := Finset.single_le_sum (f := fun i => |(k i : ℝ)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : |(k i : ℝ)| ≤ (⌈K⌉ : ℝ) := by
      have := Int.le_ceil K
      simp only [Set.mem_ofPred_eq] at hk
      linarith
    have h3 : |k i| ≤ ⌈K⌉ := by exact_mod_cast h2
    exact abs_le.1 h3
  refine (hk.prod hl).subset ?_
  rintro ⟨k, l⟩ ⟨h1, h2, h3, h4, h5⟩
  exact ⟨h3, h1, h4, h5⟩

/-- `N_X = #X`. -/
def measNX : ℕ := (measXSet m hm).ncard

/-- The set of the nonzero `|p_{kl}|_∞` over `X`. -/
def measSigmaSet : Set ℝ :=
  (fun kl : (Fin 2 → ℤ) × (ℕ →₀ ℤ) => ‖measPX m hm kl.1 kl.2‖) ''
    {kl | kl ∈ measXSet m hm ∧ measPX m hm kl.1 kl.2 ≠ 0}

/-- The set of `|⟨k, λ_J⟩ + ⟨l, λ⟩|` over the `(k, l) ∈ X` with `p_{kl} = 0`. -/
def measCSet : Set ℝ :=
  (fun kl : (Fin 2 → ℤ) × (ℕ →₀ ℤ) => measCval m hm kl.1 kl.2) ''
    {kl | kl ∈ measXSet m hm ∧ measPX m hm kl.1 kl.2 = 0}

/-- `σ_X`: the least `|p_{kl}|_∞ ≠ 0` over `X` (`1` if there is none). -/
def measSigmaX : ℝ :=
  open scoped Classical in
  if (measSigmaSet m hm).Nonempty then sInf (measSigmaSet m hm) else 1

/-- `c_X`: the least `|⟨k, λ_J⟩ + ⟨l, λ⟩|` over the `(k, l) ∈ X` with `p_{kl} = 0` (`1` if none). -/
def measCX : ℝ :=
  open scoped Classical in
  if (measCSet m hm).Nonempty then sInf (measCSet m hm) else 1

theorem measSigmaSet_finite : (measSigmaSet m hm).Finite :=
  ((measXSet_finite m hm).subset (fun _ h => h.1)).image _

theorem measCSet_finite : (measCSet m hm).Finite :=
  ((measXSet_finite m hm).subset (fun _ h => h.1)).image _

/-- `g_{kl}(ξ) = g_{kl}(0) + ⟨p_{kl}, ω⁰(ξ) - λ_J⟩`. -/
theorem affineForm_eq (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) (ξ : Fin 2 → ℝ) :
    affineForm m hm k l ξ =
      affineForm m hm k l 0 + ∑ i, measPX m hm k l i * (omegaTan m hm ξ i - lamTan m hm i) := by
  have hfun : ∀ ζ : Fin 2 → ℝ, omegaNor m hm ζ =
      fun ν => lamN m hm ν + (4 / 7 * measS m hm ζ) * (1 / lamN m hm ν) := by
    intro ζ; funext ν
    have : lamN m hm ν ≠ 0 := by linarith [lt_lamN m hm ν, normLab_ge ν]
    rw [omegaNor_eq]; field_simp
  have h0 : omegaTan m hm 0 = fun i => lamTan m hm i := by funext i; simp [omegaTan]
  have hs0 : measS m hm 0 = 0 := by simp [measS, h0]
  have hP : ∑ i, measPX m hm k l i * (omegaTan m hm ξ i - lamTan m hm i) =
      (∑ i, (k i : ℝ) * omegaTan m hm ξ i - ∑ i, (k i : ℝ) * lamTan m hm i) +
        4 / 7 * linF l (fun ν => 1 / lamN m hm ν) * measS m hm ξ := by
    simp only [measPX, measS, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold affineForm
  rw [hfun ξ, hfun 0, linF_add_mul, linF_add_mul, hs0, h0, hP]
  ring

theorem measCval_eq (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) :
    measCval m hm k l = |affineForm m hm k l 0| := by
  unfold measCval affineForm
  have h0 : omegaTan m hm 0 = fun i => lamTan m hm i := by funext i; simp [omegaTan]
  have hn0 : omegaNor m hm 0 = lamN m hm := by
    funext ν
    have : lamN m hm ν ≠ 0 := by linarith [lt_lamN m hm ν, normLab_ge ν]
    rw [omegaNor_eq]
    have hs0 : measS m hm 0 = 0 := by simp [measS, h0]
    rw [hs0]; ring
  rw [h0, hn0]

/-- `σ_X > 0`, and `σ_X ≤ |p_{kl}|_∞` on `X` when `p_{kl} ≠ 0`. -/
theorem measSigmaX_pos : 0 < measSigmaX m hm := by
  classical
  unfold measSigmaX
  split_ifs with h
  · have hmem := h.csInf_mem (measSigmaSet_finite m hm)
    obtain ⟨kl, ⟨_, hne⟩, heq⟩ := hmem
    rw [← heq]
    exact norm_pos_iff.2 hne
  · exact one_pos

theorem measSigmaX_le {k : Fin 2 → ℤ} {l : ℕ →₀ ℤ} (hx : (k, l) ∈ measXSet m hm)
    (hp : measPX m hm k l ≠ 0) : measSigmaX m hm ≤ ‖measPX m hm k l‖ := by
  classical
  unfold measSigmaX
  have hmem : ‖measPX m hm k l‖ ∈ measSigmaSet m hm := ⟨(k, l), ⟨hx, hp⟩, rfl⟩
  have hne : (measSigmaSet m hm).Nonempty := ⟨_, hmem⟩
  simp only [hne, ↓reduceIte]
  exact csInf_le (measSigmaSet_finite m hm).bddBelow hmem

theorem measCval_pos {k : Fin 2 → ℤ} {l : ℕ →₀ ℤ} (hx : (k, l) ∈ measXSet m hm)
    (hp : measPX m hm k l = 0) : 0 < measCval m hm k l := by
  obtain ⟨hl, -⟩ := hx
  obtain ⟨ξ, hξ⟩ := A3_holds m hm k l hl.1 hl.2
  rw [affineForm_eq] at hξ
  have : ∑ i, measPX m hm k l i * (omegaTan m hm ξ i - lamTan m hm i) = 0 := by
    simp [hp]
  rw [this, add_zero] at hξ
  rw [measCval_eq]
  exact abs_pos.2 hξ

theorem measCX_pos : 0 < measCX m hm := by
  classical
  unfold measCX
  split_ifs with h
  · have hmem := h.csInf_mem (measCSet_finite m hm)
    obtain ⟨kl, ⟨hk, hp⟩, heq⟩ := hmem
    rw [← heq]
    exact measCval_pos m hm hk hp
  · exact one_pos

theorem measCX_le {k : Fin 2 → ℤ} {l : ℕ →₀ ℤ} (hx : (k, l) ∈ measXSet m hm)
    (hp : measPX m hm k l = 0) : measCX m hm ≤ measCval m hm k l := by
  classical
  unfold measCX
  have hmem : measCval m hm k l ∈ measCSet m hm := ⟨(k, l), ⟨hx, hp⟩, rfl⟩
  have hne : (measCSet m hm).Nonempty := ⟨_, hmem⟩
  simp only [hne, ↓reduceIte]
  exact csInf_le (measCSet_finite m hm).bddBelow hmem

/-- `θ₀ = L_A⁻¹ min (1/8, σ_X / (2 (K_* + 2)))` (blueprint `bpW:w7:constdef` (C4)). -/
def measTheta0 : ℝ :=
  (measLA m hm)⁻¹ * min (1 / 8) (measSigmaX m hm / (2 * (measKstar m hm + 2)))

/-- `α₀ = (min {1/27, β_*/4, ϑ c_X / (4 K_* (K_* + 4))})^{47/44}` (blueprint `bpW:w7:constdef`
    (C4)). -/
def measAlpha0 : ℝ :=
  (min (min (1 / 27) (measBetaStar m / 4))
    (measTheta m hm * measCX m hm / (4 * measKstar m hm * (measKstar m hm + 4)))) ^ (47 / 44 : ℝ)

/-- `Z₃ = 2π²/3`. -/
def measZ3 : ℝ := 2 * π ^ 2 / 3

/-- `C_P` (blueprint `bpW:w7:constdef` (C5)). -/
def measCP : ℝ :=
  measZ3 * (8 + 32 * (measTheta m hm)⁻¹ ^ 3 + 16 * (3 + measAKappa m) * (measTheta m hm)⁻¹ ^ 2)
    + 4 * (measNX m hm : ℝ) * measKstar m hm * (measTheta m hm)⁻¹ * (measSigmaX m hm)⁻¹

/-- `C_I` (blueprint `bpW:w7:constdef` (C5)). -/
def measCI : ℝ :=
  measZ3 * (8 + 32 * (measTheta m hm)⁻¹ ^ 3 + 16 * (2 + measAKappa m) * (measTheta m hm)⁻¹ ^ 2
      + 64 * (measTheta m hm)⁻¹)
    + 4 * (measNX m hm : ℝ) * measKstar m hm ^ 2 * (measTheta m hm)⁻¹ * (measSigmaX m hm)⁻¹

/-- `C₇ = L_A (C_P + C_I)` (blueprint `bpW:w7:constdef` (C5)). -/
def measC7 : ℝ := measLA m hm * (measCP m hm + measCI m hm)

end

/-- `α̂ = α^{44/47} = α^{1-3w}`. -/
def alphaHat (α : ℝ) : ℝ := α ^ (44 / 47 : ℝ)

/-- `α̌ = α^{48/47} = α^{1+w}`. -/
def alphaCheck (α : ℝ) : ℝ := α ^ (48 / 47 : ℝ)

end KAM.Wave

end
