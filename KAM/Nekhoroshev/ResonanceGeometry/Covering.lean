/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.ResonanceGeometry.Geometric
public import KAM.Nekhoroshev.Interfaces.CoverParams
public import KAM.Nekhoroshev.Interfaces.Norms
public import KAM.Nekhoroshev.NormalForm.Setting

/-!
# The Covering Lemma and cutoffs (`bpN:p8:covering`, `bpN:p8:cutoffs`)

The geometry-dependent definitions of the covering parameters (`lam`, `radius`, `alpha`, `delta`),
the action blocks `actionBlock`, and the theorems `covering` and `cutoffs`, obtained by
specialising the Geometric Lemma to `λ_d = b m r₀ (A K)^(d-n)` and using the volume bounds
`1 ≤ V(Λ) ≤ K^d` of maximal lattices.
-/

@[expose] public noncomputable section
open Set Matrix Module Classical

namespace KAM.Nekhoroshev
open KAM.Weighted KAM.Canonical KAM.Stability
variable {n : ℕ}

def CoverParams.lam (c : CoverParams n) (d : ℕ) : ℝ :=
  c.b * c.m * c.r0 / (c.A * c.K) ^ n * (c.A * c.K) ^ d

def CoverParams.radius (c : CoverParams n) (Λ : Lattice n) : ℝ :=
  c.r0 / (c.A * c.K) ^ n * (c.A * c.K) ^ latticeDim Λ / volume_def Λ

def CoverParams.alpha (c : CoverParams n) (Λ : Lattice n) : ℝ := c.p * c.M * c.K * c.radius Λ

def CoverParams.delta (c : CoverParams n) (Λ : Lattice n) : ℝ := c.b * c.m * c.radius Λ

def actionBlock {ι : Type*} (c : CoverParams n) (P : Set ι) (freqR : ι → (Fin n → ℝ))
    (Λ : Lattice n) : Set ι := {I | I ∈ P ∧ freqR I ∈ blocks c.K c.lam Λ}

section Aux
variable {c : CoverParams n}

theorem CoverParams.Valid.hE (hc : c.Valid) : 0 < c.p * c.M / (c.b * c.m) :=
  div_pos (mul_pos hc.hp hc.hM) (mul_pos hc.hb hc.hm)

theorem CoverParams.Valid.hA1 (hc : c.Valid) : 1 < c.A := by
  have h2 : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith [hc.hE, hc.hA]

theorem CoverParams.Valid.hq1 (hc : c.Valid) : 1 ≤ c.A * c.K := by
  nlinarith [hc.hA1, hc.hK]

theorem CoverParams.Valid.hqpos (hc : c.Valid) : 0 < c.A * c.K := by linarith [hc.hq1]

theorem CoverParams.Valid.lam_pos (hc : c.Valid) (d : ℕ) : 0 < c.lam d := by
  have := hc.hqpos
  unfold CoverParams.lam
  have := hc.hb; have := hc.hm; have := hc.hr0
  positivity

theorem CoverParams.delta_eq (c : CoverParams n) (Λ : Lattice n) :
    c.delta Λ = c.lam (latticeDim Λ) / volume_def Λ := by
  unfold CoverParams.delta CoverParams.radius CoverParams.lam
  ring

theorem CoverParams.Valid.alpha_eq (hc : c.Valid) (Λ : Lattice n) :
    c.alpha Λ = c.p * c.M / (c.b * c.m) * c.K * (c.lam (latticeDim Λ) / volume_def Λ) := by
  have hb := hc.hb; have hm := hc.hm
  unfold CoverParams.alpha CoverParams.radius CoverParams.lam
  field_simp

theorem CoverParams.Valid.radius_nonneg (hc : c.Valid) (Λ : Lattice n) : 0 ≤ c.radius Λ := by
  have := hc.hqpos; have := hc.hr0
  have := one_le_volume Λ
  unfold CoverParams.radius
  positivity

theorem latticeDim_top : latticeDim (⊤ : Lattice n) = n :=
  (basis_card_eq_latticeDim (topBasis n)).symm

theorem CoverParams.radius_bot (c : CoverParams n) :
    c.radius (⊥ : Lattice n) = c.r0 / (c.A * c.K) ^ n := by
  simp [CoverParams.radius, latticeDim_bot, volume_bot]

theorem CoverParams.radius_top (hc : c.Valid) : c.radius (⊤ : Lattice n) = c.r0 := by
  have := hc.hqpos
  simp only [CoverParams.radius, latticeDim_top, volume_top, div_one]
  field_simp

/-- Bounds on the radius of a maximal lattice. -/
theorem CoverParams.Valid.radius_bounds (hc : c.Valid) {Λ : Lattice n} (hΛ : maximalK c.K Λ) :
    c.radius (⊥ : Lattice n) ≤ c.radius Λ ∧ c.radius Λ ≤ c.r0 ∧
      (Λ ≠ ⊤ → c.radius Λ ≤ c.r0 / (c.A * c.K)) := by
  have hq := hc.hqpos
  have hq1 := hc.hq1
  have hr0 := hc.hr0
  obtain ⟨-, -, -, -, -, -, -, htop, -, hvol⟩ := maximal (n := n) (K := c.K) (by linarith [hc.hK]) Λ
  obtain ⟨hv1, hvK⟩ := hvol hΛ
  have hdn := (lattice_basis Λ).1
  have hvpos : 0 < volume_def Λ := by linarith
  have hqn : 0 < (c.A * c.K) ^ n := by positivity
  have hKq : c.K ^ latticeDim Λ ≤ (c.A * c.K) ^ latticeDim Λ :=
    pow_le_pow_left₀ (by linarith [hc.hK]) (by nlinarith [hc.hA1, hc.hK]) _
  have hd1 : (1 : ℝ) ≤ (c.A * c.K) ^ latticeDim Λ := one_le_pow₀ hq1
  have hqd : (c.A * c.K) ^ latticeDim Λ ≤ (c.A * c.K) ^ n := pow_le_pow_right₀ hq1 hdn
  refine ⟨?_, ?_, fun hne => ?_⟩
  · rw [c.radius_bot]
    unfold CoverParams.radius
    rw [mul_div_assoc]
    calc c.r0 / (c.A * c.K) ^ n = c.r0 / (c.A * c.K) ^ n * 1 := (mul_one _).symm
      _ ≤ _ := by
        gcongr
        rw [le_div_iff₀ hvpos]
        linarith
  · unfold CoverParams.radius
    rw [div_le_iff₀ hvpos, div_mul_eq_mul_div, div_le_iff₀ hqn]
    have h1 : (c.A * c.K) ^ n ≤ volume_def Λ * (c.A * c.K) ^ n :=
      le_mul_of_one_le_left hqn.le hv1
    nlinarith [mul_le_mul_of_nonneg_left (hqd.trans h1) hr0.le]
  · have hlt : latticeDim Λ < n := by
      refine lt_of_le_of_ne hdn fun h => hne ?_
      exact (htop hc.hK).2 hΛ h
    have hqq : (c.A * c.K) ^ latticeDim Λ * (c.A * c.K) ≤ (c.A * c.K) ^ n := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hq1 hlt
    unfold CoverParams.radius
    rw [div_le_div_iff₀ hvpos hq, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hqn]
    nlinarith [mul_nonneg hr0.le (sub_nonneg.2 hqq), mul_nonneg hr0.le (sub_nonneg.2 hv1)]

theorem CoverParams.Valid.alpha_bot_le (hc : c.Valid) : c.alpha (⊥ : Lattice n) ≤ c.lam 1 := by
  have hq := hc.hqpos
  have hl0 := hc.lam_pos 0
  have hl1 : c.lam 1 = c.lam 0 * (c.A * c.K) := by
    unfold CoverParams.lam; rw [pow_one, pow_zero]; ring
  rw [hc.alpha_eq, latticeDim_bot, volume_bot, div_one, hl1]
  have hEA : c.p * c.M / (c.b * c.m) ≤ c.A := by
    have := hc.hA; have := Real.sqrt_nonneg 2; linarith
  have : c.p * c.M / (c.b * c.m) * c.K ≤ c.A * c.K :=
    mul_le_mul_of_nonneg_right hEA (by linarith [hc.hK])
  nlinarith
end Aux

theorem covering {ι : Type*} (c : CoverParams n) (hc : c.Valid)
    (P : Set ι) (freqR : ι → (Fin n → ℝ)) :
    {Λ : Lattice n | maximalK c.K Λ}.Finite ∧
    (∀ I ∈ P, ∃ Λ : Lattice n, maximalK c.K Λ ∧ I ∈ actionBlock c P freqR Λ) ∧
    (∀ Λ : Lattice n, maximalK c.K Λ →
      (1 ≤ latticeDim Λ → c.delta Λ = c.lam (latticeDim Λ) / volume_def Λ) ∧
      (∀ I ∈ actionBlock c P freqR Λ, ∀ k ∈ eBall n c.K, k ∉ Λ →
        c.alpha Λ ≤ |integerReal k ⬝ᵥ freqR I|) ∧
      (Λ = ⊥ → c.alpha Λ ≤ c.lam 1 ∧
        ∀ I ∈ actionBlock c P freqR Λ, ∀ k ∈ eBall n c.K, k ≠ 0 →
          c.lam 1 ≤ |integerReal k ⬝ᵥ freqR I|) ∧
      (Λ ≠ ⊥ → ∀ I ∈ actionBlock c P freqR Λ, resonanceDistance Λ (freqR I) < c.delta Λ) ∧
      c.radius (⊥ : Lattice n) ≤ c.radius Λ ∧ c.radius Λ ≤ c.r0 ∧
      (Λ ≠ ⊤ → c.radius Λ ≤ c.r0 / (c.A * c.K))) ∧
    c.radius (⊥ : Lattice n) = c.r0 / (c.A * c.K) ^ n ∧ c.radius (⊤ : Lattice n) = c.r0 := by
  have hK0 : 0 < c.K := by linarith [hc.hK]
  have hlam : ∀ d, 1 ≤ d → d ≤ n → 0 < c.lam d := fun d _ _ => hc.lam_pos d
  have hratio : ∀ d, 1 ≤ d → d < n → c.A * c.K ≤ c.lam (d + 1) / c.lam d := by
    intro d _ _
    have hl := (hc.lam_pos d).ne'
    have hq := hc.hqpos.ne'
    have : c.lam (d + 1) / c.lam d = c.A * c.K := by
      rw [div_eq_iff hl]
      unfold CoverParams.lam
      rw [pow_succ]
      ring
    rw [this]
  obtain ⟨hfin, hcov⟩ := blocks_cover hK0.le c.lam hlam
  obtain ⟨hgθ, hgΛ⟩ := geometric hc.hn hK0 hc.hE hc.hA c.lam hlam hratio
  refine ⟨hfin, fun I hI => ?_, fun Λ hΛ => ?_, c.radius_bot, CoverParams.radius_top hc⟩
  · obtain ⟨Λ, hΛ, hw⟩ := hcov (freqR I)
    exact ⟨Λ, hΛ, hI, hw⟩
  · have hbot : ∀ I ∈ actionBlock c P freqR Λ, Λ = ⊥ → ∀ k ∈ eBall n c.K, k ≠ 0 →
        c.lam 1 ≤ |integerReal k ⬝ᵥ freqR I| := fun I hI hΛ0 k hk hk0 => by
      subst hΛ0
      exact hgθ _ hI.2 k hk hk0
    refine ⟨fun _ => c.delta_eq Λ, fun I hI k hk hkΛ => ?_,
      fun hΛ0 => ⟨?_, fun I hI => hbot I hI hΛ0⟩, fun hne I hI => ?_,
      (hc.radius_bounds hΛ).1, (hc.radius_bounds hΛ).2.1, (hc.radius_bounds hΛ).2.2⟩
    · by_cases hd : 1 ≤ latticeDim Λ
      · rw [hc.alpha_eq]
        exact (hgΛ Λ hΛ hd _ hI.2).2 k hk hkΛ
      · have hΛ0 : Λ = ⊥ := (lattice_resonance Λ).2.1 (by omega)
        subst hΛ0
        exact hc.alpha_bot_le.trans (hbot I hI rfl k hk fun h => hkΛ (by simp [h]))
    · subst hΛ0; exact hc.alpha_bot_le
    · have hd : 1 ≤ latticeDim Λ := by
        by_contra h
        exact hne ((lattice_resonance Λ).2.1 (by omega))
      rw [c.delta_eq]
      exact (hgΛ Λ hΛ hd _ hI.2).1

theorem cutoffs (c : CoverParams n) (hc : c.Valid) {Ka : ℝ} (hKa : 0 ≤ Ka) :
    (KAM.NormalForm.zBall n Ka ⊆ eBall n Ka) ∧
    (eBall n Ka ⊆ KAM.NormalForm.zBall n (Real.sqrt n * Ka)) ∧
    (Ka ≤ c.K → ∀ Λ : Lattice n, maximalK c.K Λ →
      ∀ w ∈ blocks c.K c.lam Λ, ∀ k ∈ KAM.NormalForm.zBall n Ka,
        k ∉ Λ → c.alpha Λ ≤ |integerReal k ⬝ᵥ w|) ∧
    (∀ Λ : Lattice n, maximalK c.K Λ → ∀ w ∈ blocks c.K c.lam Λ,
      resonanceDistance Λ w < c.delta Λ) ∧
    (0 < Real.sqrt n * Ka → Real.sqrt n * Ka ≤ c.K → ∀ Λ : Lattice n,
      c.radius Λ = c.alpha Λ / (c.p * c.M * c.K) ∧
      c.radius Λ ≤ c.alpha Λ / (c.p * Real.sqrt n * c.M * Ka)) := by
  have hK0 : 0 < c.K := by linarith [hc.hK]
  have hcv := covering c hc (Set.univ : Set (Fin n → ℝ)) id
  have hdist0 : resonanceDistance (⊥ : Lattice n) = fun _ => 0 := by
    have : lattice (⊥ : Lattice n) = ⊥ :=
      Submodule.finrank_eq_zero.1 (by simpa [latticeDim] using latticeDim_bot (n := n))
    funext w
    simp [resonanceDistance, this, projection_zero, euclid]
  have hz : KAM.NormalForm.zBall n Ka ⊆ eBall n Ka := fun k hk =>
    (modeSize_euclid_compare k).1.trans hk
  refine ⟨hz, fun k hk => ?_, fun hKaK Λ hΛ w hw k hk hkΛ => ?_, fun Λ hΛ w hw => ?_,
    fun hpos hle Λ => ?_⟩
  · exact (modeSize_euclid_compare k).2.trans (by gcongr; exact hk)
  · exact (hcv.2.2.1 Λ hΛ).2.1 w ⟨trivial, hw⟩ k (le_trans (hz hk) hKaK) hkΛ
  · by_cases h : Λ = ⊥
    · subst h
      rw [hdist0, c.delta_eq, latticeDim_bot, volume_bot]
      simpa using hc.lam_pos 0
    · exact (hcv.2.2.1 Λ hΛ).2.2.2.1 h w ⟨trivial, hw⟩
  · have hpM : 0 < c.p * c.M * c.K := by
      have := hc.hp; have := hc.hM; positivity
    have hr : c.radius Λ = c.alpha Λ / (c.p * c.M * c.K) := by
      have := hc.hp.ne'; have := hc.hM.ne'; have := hK0.ne'
      unfold CoverParams.alpha; field_simp
    refine ⟨hr, ?_⟩
    have hsn : 0 < Real.sqrt n * Ka := hpos
    have hrad := hc.radius_nonneg Λ
    rw [hr]
    have hKa' : 0 < Ka := by
      by_contra h
      have : Ka = 0 := le_antisymm (not_lt.1 h) hKa
      rw [this, mul_zero] at hsn; exact lt_irrefl _ hsn
    have hsq : 0 < Real.sqrt n := by
      by_contra h
      have : Real.sqrt n = 0 := le_antisymm (not_lt.1 h) (Real.sqrt_nonneg _)
      rw [this, zero_mul] at hsn; exact lt_irrefl _ hsn
    have hp := hc.hp; have hM := hc.hM
    rw [show c.p * Real.sqrt n * c.M * Ka = c.p * c.M * (Real.sqrt n * Ka) by ring]
    have hal : 0 ≤ c.alpha Λ := mul_nonneg hpM.le hrad
    refine div_le_div_of_nonneg_left hal (by positivity) ?_
    have : c.p * c.M * (Real.sqrt n * Ka) ≤ c.p * c.M * c.K := by gcongr
    exact this

end KAM.Nekhoroshev
