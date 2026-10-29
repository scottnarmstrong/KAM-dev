/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedDev
public import KAM.Planetary.Preparation.PreparedNum

/-!
# Rescaled bounds of the partials of `h = h₀ + g₂` (P11A-P8b2, pr-b and pr-d)

`p11_dev_resc`: at a point of the Cauchy region, for every multi-index `β` of order `j + 1`
(`j ≤ μ̄ + 1`), `ε^j |∂^β h| ≤ (L if j = 0 else εL) + K (1 + c) ε ℓ^Q`, with `Q` the exponent of
step
`prepared`. This is the content of steps pr-in and pr-b/pr-d of `bpP:p11:prepared`: the
Cauchy radii `s₂/4`, `ε/4` cancel against the rescaling of `N_ε`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped BigOperators
namespace KAM.Planetary

section Resc

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

theorem p11_resc_prod_le {N : ℕ} (α : Fin N → ℕ) :
    (∏ i, ((α i).factorial : ℝ)) ≤ ((∑ i, α i).factorial : ℝ) := by
  exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum _ _)

theorem p11_resc_prod2_le (α γ : Fin n → ℕ) :
    (∏ i, ((α i).factorial : ℝ)) * (∏ i, ((γ i).factorial : ℝ)) ≤
      ((∑ i, α i + ∑ i, γ i).factorial : ℝ) := by
  have h := p11_resc_prod_le (Fin.append α γ : Fin (n + n) → ℕ)
  rw [Fin.prod_univ_add, Fin.sum_univ_add] at h
  simpa using h

theorem p11_resc_rpow_le {l x y : ℝ} (hl : 1 ≤ l) (hxy : x ≤ y) : l ^ x ≤ l ^ y :=
  Real.rpow_le_rpow_of_exponent_le hl hxy

/-- Pure-`J` deviation from the main term `∂^α C.h` (rescaled). -/
theorem p11_resc_pure_dev (hC : P11SecularSpec D C) {Fast : P11FastData n} {nu eps c : ℝ}
    {A : P11SlowData n} (hnu : 1 ≤ nu) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hFs : P11FastSpec C eps Fast) (hA : P11SlowSpecOf C Fast nu eps c A) (hc0 : 0 ≤ c)
    (hzs : 3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16) (h5 : 5 * eps ≤ p11s2 C nu eps)
    (α : Fin n → ℕ) (j : ℕ) (hα : ∑ i, α i = j + 1)
    (J ρ : P11CVec n) (hJ : ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4)
    (hρ : ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4) {F k1 : ℝ}
    (hP : ((j + 1).factorial : ℝ) ≤ F) (hη : p11eta1 C eps ≤ 1)
    (hs1' : 4 * eps / p11s1 C eps ≤ 4 * k1 * eps * Real.log (1 / eps) ^ (C.tau + 1))
    (hs1small : 4 * eps / p11s1 C eps ≤ 1) (hl : 1 ≤ Real.log (1 / eps)) :
    eps ^ j * ‖p11PartialVec (Fin.append α (0 : Fin n → ℕ)) (p11DevH A) (Fin.append J ρ) -
        p11PartialVec α (fun (J' : P11CVec n) (_ : Fin 1) => C.h J') J‖ ≤
      F * (C.MF + 1) * (4 * k1 * eps * Real.log (1 / eps) ^ (C.tau + 1)) +
        F * (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) := by
  obtain ⟨hK2, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  have hspec := p11s2_spec hC hK2
  have hs1r := p11s1_le C eps
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  have hJball : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) := by
    rw [mem_ball_iff_norm]; linarith
  have hd := p11_dev_J_bound hC hnu heps hεM hFs hA hzs h5 α J ρ hJ hρ
  have hP0 : 0 ≤ ∏ i, ((α i).factorial : ℝ) := Finset.prod_nonneg fun _ _ => by positivity
  have hPα : (∏ i, ((α i).factorial : ℝ)) ≤ F := by
    refine (p11_resc_prod_le α).trans ?_
    rw [hα]; exact hP
  have hη0 : 0 ≤ p11eta1 C eps := by
    obtain ⟨-, -, -, -, hGd, -, -, -, -, -, -, -, -, hGη, -⟩ := hFs
    have hr : 0 < C.rz / 2 := by positivity
    have := hGη (KAM.realInclusion n C.J0) (by simp; positivity) 0 (by simpa using hr)
    exact (norm_nonneg _).trans this
  -- the three terms
  have hF0 : 0 ≤ F := (Nat.cast_nonneg _).trans hP
  have hRη : 0 ≤ C.MF + p11eta1 C eps := by linarith
  have t1 : eps ^ j * (eps * p11DevA C eps α) ≤
      (∏ i, ((α i).factorial : ℝ)) * (C.MF + p11eta1 C eps) * (4 * eps / p11s1 C eps) :=
    p11_num_a heps hs1 hP0 hRη hs1small _ j hα
  have t1' : (∏ i, ((α i).factorial : ℝ)) * (C.MF + p11eta1 C eps) * (4 * eps / p11s1 C eps) ≤
      F * (C.MF + 1) * (4 * k1 * eps * Real.log (1 / eps) ^ (C.tau + 1)) := by
    have h1 : C.MF + p11eta1 C eps ≤ C.MF + 1 := by linarith
    have h0 : 0 ≤ 4 * eps / p11s1 C eps := by positivity
    have hF1 : 0 ≤ F * (C.MF + 1) := by positivity
    calc _ ≤ F * (C.MF + 1) * (4 * eps / p11s1 C eps) := by gcongr
      _ ≤ _ := by gcongr
  have t2 : eps ^ j * p11DevG C nu eps c α 0 ≤
      (∏ i, ((α i).factorial : ℝ)) * (∏ i, (((0 : Fin n → ℕ) i).factorial : ℝ)) *
        4 ^ (∑ i, (0 : Fin n → ℕ) i) *
        (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) :=
    p11_num_g heps h5 hP0 (Finset.prod_nonneg fun _ _ => by positivity) hc0
      (Real.rpow_nonneg (by linarith) _) _ _ j (by simpa using hα)
  have t2' : (∏ i, ((α i).factorial : ℝ)) * (∏ i, (((0 : Fin n → ℕ) i).factorial : ℝ)) *
        4 ^ (∑ i, (0 : Fin n → ℕ) i) *
        (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) ≤
      F * (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) := by
    simp only [Pi.zero_apply, Nat.factorial_zero, Nat.cast_one, Finset.prod_const_one, mul_one,
      Finset.sum_const_zero, pow_zero]
    have : 0 ≤ c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2) := by
      have := Real.rpow_nonneg (show 0 ≤ Real.log (1 / eps) by linarith) (5 * C.tau + 2)
      positivity
    gcongr
  calc eps ^ j * ‖p11PartialVec (Fin.append α (0 : Fin n → ℕ)) (p11DevH A) (Fin.append J ρ) -
        p11PartialVec α (fun (J' : P11CVec n) (_ : Fin 1) => C.h J') J‖
      ≤ eps ^ j * (eps * p11DevA C eps α + p11DevG C nu eps c α 0) := by gcongr
    _ = eps ^ j * (eps * p11DevA C eps α) + eps ^ j * p11DevG C nu eps c α 0 := by ring
    _ ≤ _ := by linarith

/-- Pure-`J` case of the rescaled deviation bound. -/
theorem p11_resc_pure (hC : P11SecularSpec D C) {Fast : P11FastData n} {nu eps c : ℝ}
    {A : P11SlowData n} (hnu : 1 ≤ nu) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hFs : P11FastSpec C eps Fast) (hA : P11SlowSpecOf C Fast nu eps c A) (hc0 : 0 ≤ c)
    (hzs : 3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16) (h5 : 5 * eps ≤ p11s2 C nu eps)
    (α : Fin n → ℕ) (j : ℕ) (hα : ∑ i, α i = j + 1) (hj : j ≤ (p11PatchData D).mu + 1)
    (J ρ : P11CVec n) (hJ : ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4)
    (hρ : ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4) {F k1 : ℝ}
    (hP : ((j + 1).factorial : ℝ) ≤ F) (hη : p11eta1 C eps ≤ 1)
    (hs1' : 4 * eps / p11s1 C eps ≤ 4 * k1 * eps * Real.log (1 / eps) ^ (C.tau + 1))
    (hs1small : 4 * eps / p11s1 C eps ≤ 1) (hl : 1 ≤ Real.log (1 / eps)) :
    eps ^ j * ‖p11PartialVec (Fin.append α (0 : Fin n → ℕ)) (p11DevH A) (Fin.append J ρ)‖ ≤
      eps ^ j * C.L + F * (C.MF + 1) * (4 * k1 * eps * Real.log (1 / eps) ^ (C.tau + 1)) +
        F * (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) := by
  obtain ⟨hK2, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  have hspec := p11s2_spec hC hK2
  have hs1r := p11s1_le C eps
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  have hJball : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) := by
    rw [mem_ball_iff_norm]; linarith
  have hmain := p11_dev_main_h hC hJball α (by omega) (by omega)
  have hd := p11_dev_J_bound hC hnu heps hεM hFs hA hzs h5 α J ρ hJ hρ
  have hXY : ‖p11PartialVec (Fin.append α (0 : Fin n → ℕ)) (p11DevH A) (Fin.append J ρ)‖ ≤
      (eps * p11DevA C eps α + p11DevG C nu eps c α 0) + C.L :=
    calc _ = ‖(p11PartialVec (Fin.append α (0 : Fin n → ℕ)) (p11DevH A) (Fin.append J ρ) -
          p11PartialVec α (fun (J' : P11CVec n) (_ : Fin 1) => C.h J') J) +
          p11PartialVec α (fun (J' : P11CVec n) (_ : Fin 1) => C.h J') J‖ := by
            rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hd hmain)
  have hP0 : 0 ≤ ∏ i, ((α i).factorial : ℝ) := Finset.prod_nonneg fun _ _ => by positivity
  have hPα : (∏ i, ((α i).factorial : ℝ)) ≤ F := by
    refine (p11_resc_prod_le α).trans ?_
    rw [hα]; exact hP
  have hη0 : 0 ≤ p11eta1 C eps := by
    obtain ⟨-, -, -, -, hGd, -, -, -, -, -, -, -, -, hGη, -⟩ := hFs
    have hr : 0 < C.rz / 2 := by positivity
    have := hGη (KAM.realInclusion n C.J0) (by simp; positivity) 0 (by simpa using hr)
    exact (norm_nonneg _).trans this
  -- the three terms
  have hF0 : 0 ≤ F := (Nat.cast_nonneg _).trans hP
  have hRη : 0 ≤ C.MF + p11eta1 C eps := by linarith
  have t1 : eps ^ j * (eps * p11DevA C eps α) ≤
      (∏ i, ((α i).factorial : ℝ)) * (C.MF + p11eta1 C eps) * (4 * eps / p11s1 C eps) :=
    p11_num_a heps hs1 hP0 hRη hs1small _ j hα
  have t1' : (∏ i, ((α i).factorial : ℝ)) * (C.MF + p11eta1 C eps) * (4 * eps / p11s1 C eps) ≤
      F * (C.MF + 1) * (4 * k1 * eps * Real.log (1 / eps) ^ (C.tau + 1)) := by
    have h1 : C.MF + p11eta1 C eps ≤ C.MF + 1 := by linarith
    have h0 : 0 ≤ 4 * eps / p11s1 C eps := by positivity
    have hF1 : 0 ≤ F * (C.MF + 1) := by positivity
    calc _ ≤ F * (C.MF + 1) * (4 * eps / p11s1 C eps) := by gcongr
      _ ≤ _ := by gcongr
  have t2 : eps ^ j * p11DevG C nu eps c α 0 ≤
      (∏ i, ((α i).factorial : ℝ)) * (∏ i, (((0 : Fin n → ℕ) i).factorial : ℝ)) *
        4 ^ (∑ i, (0 : Fin n → ℕ) i) *
        (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) :=
    p11_num_g heps h5 hP0 (Finset.prod_nonneg fun _ _ => by positivity) hc0
      (Real.rpow_nonneg (by linarith) _) _ _ j (by simpa using hα)
  have t2' : (∏ i, ((α i).factorial : ℝ)) * (∏ i, (((0 : Fin n → ℕ) i).factorial : ℝ)) *
        4 ^ (∑ i, (0 : Fin n → ℕ) i) *
        (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) ≤
      F * (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) := by
    simp only [Pi.zero_apply, Nat.factorial_zero, Nat.cast_one, Finset.prod_const_one, mul_one,
      Finset.sum_const_zero, pow_zero]
    have : 0 ≤ c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2) := by
      have := Real.rpow_nonneg (show 0 ≤ Real.log (1 / eps) by linarith) (5 * C.tau + 2)
      positivity
    gcongr
  calc eps ^ j * ‖p11PartialVec (Fin.append α (0 : Fin n → ℕ)) (p11DevH A) (Fin.append J ρ)‖
      ≤ eps ^ j * ((eps * p11DevA C eps α + p11DevG C nu eps c α 0) + C.L) := by gcongr
    _ = eps ^ j * (eps * p11DevA C eps α) + eps ^ j * p11DevG C nu eps c α 0 + eps ^ j * C.L := by
        ring
    _ ≤ _ := by linarith

/-- The main `Ω̃`-term of a partial with a `ρ̃`-index is bounded by `L`. -/
theorem p11_resc_Om (hC : P11SecularSpec D C) {nu eps : ℝ} (hnu : 1 ≤ nu) (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) (i : Fin n) (α γ : Fin n → ℕ) (j : ℕ)
    (hα : ∑ k, α k + ∑ k, γ k = j) (hj : j ≤ (p11PatchData D).mu + 1)
    (J ρ : P11CVec n) (hJ : ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4)
    (hρ : ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4) :
    ‖p11PartialVec (Fin.append α γ) (fun (I : P11CVec (n + n)) (_ : Fin 1) =>
        (2 * Real.pi : ℂ)⁻¹ * C.Omega (fun k : Fin n => I (Fin.castAdd n k)) i)
        (Fin.append J ρ)‖ ≤ C.L := by
  obtain ⟨hK2, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  have hspec := p11s2_spec hC hK2
  have hs1r := p11s1_le C eps
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  have hJball : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) := by
    rw [mem_ball_iff_norm]; linarith
  have hP' : (Fin.append J ρ : P11CVec (n + n)) ∈
      p11Box (p11DevCenter C eps) (p11s2 C nu eps) (Real.pi * eps) :=
    p11_dev_mem_box J ρ (by linarith) (by nlinarith [Real.pi_gt_three]) hJ hρ
  by_cases hγ0' : γ = 0
  · subst hγ0'
    rw [p11_dev_Om_slice hC hs2 (by linarith) i α J ρ hP']
    refine p11_dev_main_Omega hC hJball i α ?_
    simp at hα
    omega
  · rw [p11_dev_Om_zero hC hs2 (by linarith) i α γ hγ0' J ρ hP', norm_zero]
    linarith

/-- `ρ̃`-index deviation from the main term `ε ∂^α Ω̃_i` (rescaled). -/
theorem p11_resc_rho_dev (hC : P11SecularSpec D C) {Fast : P11FastData n} {nu eps c : ℝ}
    {A : P11SlowData n} (hnu : 1 ≤ nu) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hA : P11SlowSpecOf C Fast nu eps c A) (hc0 : 0 ≤ c)
    (hzs : 3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16) (h5 : 5 * eps ≤ p11s2 C nu eps)
    (i : Fin n) (α γ : Fin n → ℕ) (j : ℕ) (hα : ∑ k, α k + ∑ k, γ k = j)
    (hj : j ≤ (p11PatchData D).mu + 1)
    (J ρ : P11CVec n) (hJ : ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4)
    (hρ : ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4) {F k2 : ℝ}
    (hP : ((j + 1).factorial : ℝ) ≤ F) (he1 : eps ≤ 1)
    (hη0 : 0 ≤ p11eta1 C eps)
    (hη : p11eta1 C eps ≤ k2 * eps * Real.log (1 / eps) ^ (2 * C.tau + 1))
    (hl : 1 ≤ Real.log (1 / eps)) :
    eps ^ j * ‖p11PartialVec (Fin.append α γ + Pi.single (Fin.natAdd n i) 1) (p11DevH A)
          (Fin.append J ρ) -
        (eps : ℂ) • p11PartialVec (Fin.append α γ) (fun (I : P11CVec (n + n)) (_ : Fin 1) =>
          (2 * Real.pi : ℂ)⁻¹ * C.Omega (fun k : Fin n => I (Fin.castAdd n k)) i)
          (Fin.append J ρ)‖ ≤
      F * (c * (1 + k2) * eps ^ 2 * Real.log (1 / eps) ^ (2 * C.tau + 1)) +
        F * 4 ^ ((p11PatchData D).mu + 2) *
          (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) := by
  obtain ⟨hK2, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  have hspec := p11s2_spec hC hK2
  have hs1r := p11s1_le C eps
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  have hJball : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) := by
    rw [mem_ball_iff_norm]; linarith
  have hd := p11_dev_rho_bound hC hnu heps hεM hA hzs h5 i α γ J ρ hJ hρ
  have hF0 : 0 ≤ F := (Nat.cast_nonneg _).trans hP
  have hP0 : 0 ≤ ∏ k, ((α k).factorial : ℝ) := Finset.prod_nonneg fun _ _ => by positivity
  have hQ0 : 0 ≤ ∏ k, ((γ k).factorial : ℝ) := Finset.prod_nonneg fun _ _ => by positivity
  have hPQ : (∏ k, ((α k).factorial : ℝ)) * (∏ k, ((γ k).factorial : ℝ)) ≤ F :=
    (p11_resc_prod2_le α γ).trans (by
      rw [hα]
      exact le_trans (by exact_mod_cast Nat.factorial_le (Nat.le_succ j)) hP)
  have hM0 : 0 ≤ c * (eps + p11eta1 C eps) := by positivity
  have hlx : 1 ≤ Real.log (1 / eps) ^ (2 * C.tau + 1) := Real.one_le_rpow hl (by linarith)
  have hl5 : 0 ≤ Real.log (1 / eps) ^ (5 * C.tau + 2) :=
    Real.rpow_nonneg (by linarith) _
  have tz : eps ^ j * (eps * p11DevZ C nu eps c α γ) ≤
      eps * ((∏ k, ((α k).factorial : ℝ)) * (∏ k, ((γ k).factorial : ℝ)) *
        (c * (eps + p11eta1 C eps))) :=
    p11_num_z heps h5 hP0 hQ0 hM0 _ _ j hα
  have tz' : eps * ((∏ k, ((α k).factorial : ℝ)) * (∏ k, ((γ k).factorial : ℝ)) *
        (c * (eps + p11eta1 C eps))) ≤
      F * (c * (1 + k2) * eps ^ 2 * Real.log (1 / eps) ^ (2 * C.tau + 1)) :=
    p11_num_z_final heps hc0 hη0 hlx (mul_nonneg hP0 hQ0) hPQ hη
  have hsum2 : ∑ k, (γ + Pi.single i 1 : Fin n → ℕ) k = ∑ k, γ k + 1 := by
    simp [Finset.sum_add_distrib]
  have tg : eps ^ j * p11DevG C nu eps c α (γ + Pi.single i 1 : Fin n → ℕ) ≤
      (∏ k, ((α k).factorial : ℝ)) * (∏ k, (((γ + Pi.single i 1 : Fin n → ℕ) k).factorial : ℝ)) *
        4 ^ (∑ k, (γ + Pi.single i 1 : Fin n → ℕ) k) *
        (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) :=
    p11_num_g heps h5 hP0 (Finset.prod_nonneg fun _ _ => by positivity) hc0 hl5 _ _ j
      (by rw [hsum2]; omega)
  have tg' : (∏ k, ((α k).factorial : ℝ)) *
        (∏ k, (((γ + Pi.single i 1 : Fin n → ℕ) k).factorial : ℝ)) *
        4 ^ (∑ k, (γ + Pi.single i 1 : Fin n → ℕ) k) *
        (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) ≤
      F * 4 ^ ((p11PatchData D).mu + 2) *
        (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) := by
    have hPQ2 : (∏ k, ((α k).factorial : ℝ)) *
        (∏ k, (((γ + Pi.single i 1 : Fin n → ℕ) k).factorial : ℝ)) ≤ F :=
      (p11_resc_prod2_le α (γ + Pi.single i 1 : Fin n → ℕ)).trans (by
        rw [hsum2]
        refine le_trans ?_ hP
        have : ∑ k, α k + (∑ k, γ k + 1) = j + 1 := by omega
        rw [this])
    have h4 : (4 : ℝ) ^ (∑ k, (γ + Pi.single i 1 : Fin n → ℕ) k) ≤
        4 ^ ((p11PatchData D).mu + 2) := by
      rw [hsum2]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hnn : 0 ≤ c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2) := by positivity
    have hP1 : 0 ≤ (∏ k, ((α k).factorial : ℝ)) *
        (∏ k, (((γ + Pi.single i 1 : Fin n → ℕ) k).factorial : ℝ)) :=
      mul_nonneg hP0 (Finset.prod_nonneg fun _ _ => by positivity)
    calc _ ≤ F * 4 ^ ((p11PatchData D).mu + 2) *
          (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) := by
            refine mul_le_mul_of_nonneg_right ?_ hnn
            exact mul_le_mul hPQ2 h4 (by positivity) hF0
      _ ≤ _ := le_rfl
  have hLe : eps ^ j * (eps * C.L) ≤ eps * C.L := by
    have : 0 ≤ eps * C.L := by positivity
    nlinarith [pow_le_one₀ heps.le he1 (n := j)]
  calc eps ^ j * ‖p11PartialVec (Fin.append α γ + Pi.single (Fin.natAdd n i) 1) (p11DevH A)
          (Fin.append J ρ) -
        (eps : ℂ) • p11PartialVec (Fin.append α γ) (fun (I : P11CVec (n + n)) (_ : Fin 1) =>
          (2 * Real.pi : ℂ)⁻¹ * C.Omega (fun k : Fin n => I (Fin.castAdd n k)) i)
          (Fin.append J ρ)‖
      ≤ eps ^ j * (eps * p11DevZ C nu eps c α γ +
        p11DevG C nu eps c α (γ + Pi.single i 1 : Fin n → ℕ)) := by gcongr
    _ = eps ^ j * (eps * p11DevZ C nu eps c α γ) +
        eps ^ j * p11DevG C nu eps c α (γ + Pi.single i 1 : Fin n → ℕ) := by ring
    _ ≤ _ := by linarith

/-- `ρ̃`-index case of the rescaled deviation bound. -/
theorem p11_resc_rho (hC : P11SecularSpec D C) {Fast : P11FastData n} {nu eps c : ℝ}
    {A : P11SlowData n} (hnu : 1 ≤ nu) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hA : P11SlowSpecOf C Fast nu eps c A) (hc0 : 0 ≤ c)
    (hzs : 3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16) (h5 : 5 * eps ≤ p11s2 C nu eps)
    (i : Fin n) (α γ : Fin n → ℕ) (j : ℕ) (hα : ∑ k, α k + ∑ k, γ k = j)
    (hj : j ≤ (p11PatchData D).mu + 1)
    (J ρ : P11CVec n) (hJ : ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4)
    (hρ : ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4) {F k2 : ℝ}
    (hP : ((j + 1).factorial : ℝ) ≤ F) (he1 : eps ≤ 1)
    (hη0 : 0 ≤ p11eta1 C eps)
    (hη : p11eta1 C eps ≤ k2 * eps * Real.log (1 / eps) ^ (2 * C.tau + 1))
    (hl : 1 ≤ Real.log (1 / eps)) :
    eps ^ j * ‖p11PartialVec (Fin.append α γ + Pi.single (Fin.natAdd n i) 1) (p11DevH A)
        (Fin.append J ρ)‖ ≤
      eps * C.L + F * (c * (1 + k2) * eps ^ 2 * Real.log (1 / eps) ^ (2 * C.tau + 1)) +
        F * 4 ^ ((p11PatchData D).mu + 2) *
          (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) := by
  obtain ⟨hK2, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  have hspec := p11s2_spec hC hK2
  have hs1r := p11s1_le C eps
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  have hJball : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) := by
    rw [mem_ball_iff_norm]; linarith
  have hd := p11_dev_rho_bound hC hnu heps hεM hA hzs h5 i α γ J ρ hJ hρ
  have hOm := p11_resc_Om hC hnu heps hεM i α γ j hα hj J ρ hJ hρ
  have hXY : ‖p11PartialVec (Fin.append α γ + Pi.single (Fin.natAdd n i) 1) (p11DevH A)
      (Fin.append J ρ)‖ ≤ eps * C.L + (eps * p11DevZ C nu eps c α γ +
        p11DevG C nu eps c α (γ + Pi.single i 1 : Fin n → ℕ)) := by
    calc _ = ‖(p11PartialVec (Fin.append α γ + Pi.single (Fin.natAdd n i) 1) (p11DevH A)
          (Fin.append J ρ) - (eps : ℂ) • p11PartialVec (Fin.append α γ)
          (fun (I : P11CVec (n + n)) (_ : Fin 1) =>
            (2 * Real.pi : ℂ)⁻¹ * C.Omega (fun k : Fin n => I (Fin.castAdd n k)) i)
          (Fin.append J ρ)) + (eps : ℂ) • p11PartialVec (Fin.append α γ)
          (fun (I : P11CVec (n + n)) (_ : Fin 1) =>
            (2 * Real.pi : ℂ)⁻¹ * C.Omega (fun k : Fin n => I (Fin.castAdd n k)) i)
          (Fin.append J ρ)‖ := by rw [sub_add_cancel]
      _ ≤ _ := by
        refine (norm_add_le _ _).trans ?_
        rw [add_comm (eps * C.L)]
        refine add_le_add hd ?_
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg heps.le]
        exact mul_le_mul_of_nonneg_left hOm heps.le
  have hF0 : 0 ≤ F := (Nat.cast_nonneg _).trans hP
  have hP0 : 0 ≤ ∏ k, ((α k).factorial : ℝ) := Finset.prod_nonneg fun _ _ => by positivity
  have hQ0 : 0 ≤ ∏ k, ((γ k).factorial : ℝ) := Finset.prod_nonneg fun _ _ => by positivity
  have hPQ : (∏ k, ((α k).factorial : ℝ)) * (∏ k, ((γ k).factorial : ℝ)) ≤ F :=
    (p11_resc_prod2_le α γ).trans (by
      rw [hα]
      exact le_trans (by exact_mod_cast Nat.factorial_le (Nat.le_succ j)) hP)
  have hM0 : 0 ≤ c * (eps + p11eta1 C eps) := by positivity
  have hlx : 1 ≤ Real.log (1 / eps) ^ (2 * C.tau + 1) := Real.one_le_rpow hl (by linarith)
  have hl5 : 0 ≤ Real.log (1 / eps) ^ (5 * C.tau + 2) :=
    Real.rpow_nonneg (by linarith) _
  have tz : eps ^ j * (eps * p11DevZ C nu eps c α γ) ≤
      eps * ((∏ k, ((α k).factorial : ℝ)) * (∏ k, ((γ k).factorial : ℝ)) *
        (c * (eps + p11eta1 C eps))) :=
    p11_num_z heps h5 hP0 hQ0 hM0 _ _ j hα
  have tz' : eps * ((∏ k, ((α k).factorial : ℝ)) * (∏ k, ((γ k).factorial : ℝ)) *
        (c * (eps + p11eta1 C eps))) ≤
      F * (c * (1 + k2) * eps ^ 2 * Real.log (1 / eps) ^ (2 * C.tau + 1)) :=
    p11_num_z_final heps hc0 hη0 hlx (mul_nonneg hP0 hQ0) hPQ hη
  have hsum2 : ∑ k, (γ + Pi.single i 1 : Fin n → ℕ) k = ∑ k, γ k + 1 := by
    simp [Finset.sum_add_distrib]
  have tg : eps ^ j * p11DevG C nu eps c α (γ + Pi.single i 1 : Fin n → ℕ) ≤
      (∏ k, ((α k).factorial : ℝ)) * (∏ k, (((γ + Pi.single i 1 : Fin n → ℕ) k).factorial : ℝ)) *
        4 ^ (∑ k, (γ + Pi.single i 1 : Fin n → ℕ) k) *
        (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) :=
    p11_num_g heps h5 hP0 (Finset.prod_nonneg fun _ _ => by positivity) hc0 hl5 _ _ j
      (by rw [hsum2]; omega)
  have tg' : (∏ k, ((α k).factorial : ℝ)) *
        (∏ k, (((γ + Pi.single i 1 : Fin n → ℕ) k).factorial : ℝ)) *
        4 ^ (∑ k, (γ + Pi.single i 1 : Fin n → ℕ) k) *
        (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) ≤
      F * 4 ^ ((p11PatchData D).mu + 2) *
        (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) := by
    have hPQ2 : (∏ k, ((α k).factorial : ℝ)) *
        (∏ k, (((γ + Pi.single i 1 : Fin n → ℕ) k).factorial : ℝ)) ≤ F :=
      (p11_resc_prod2_le α (γ + Pi.single i 1 : Fin n → ℕ)).trans (by
        rw [hsum2]
        refine le_trans ?_ hP
        have : ∑ k, α k + (∑ k, γ k + 1) = j + 1 := by omega
        rw [this])
    have h4 : (4 : ℝ) ^ (∑ k, (γ + Pi.single i 1 : Fin n → ℕ) k) ≤
        4 ^ ((p11PatchData D).mu + 2) := by
      rw [hsum2]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hnn : 0 ≤ c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2) := by positivity
    have hP1 : 0 ≤ (∏ k, ((α k).factorial : ℝ)) *
        (∏ k, (((γ + Pi.single i 1 : Fin n → ℕ) k).factorial : ℝ)) :=
      mul_nonneg hP0 (Finset.prod_nonneg fun _ _ => by positivity)
    calc _ ≤ F * 4 ^ ((p11PatchData D).mu + 2) *
          (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) := by
            refine mul_le_mul_of_nonneg_right ?_ hnn
            exact mul_le_mul hPQ2 h4 (by positivity) hF0
      _ ≤ _ := le_rfl
  have hLe : eps ^ j * (eps * C.L) ≤ eps * C.L := by
    have : 0 ≤ eps * C.L := by positivity
    nlinarith [pow_le_one₀ heps.le he1 (n := j)]
  calc eps ^ j * ‖p11PartialVec (Fin.append α γ + Pi.single (Fin.natAdd n i) 1) (p11DevH A)
        (Fin.append J ρ)‖
      ≤ eps ^ j * (eps * C.L + (eps * p11DevZ C nu eps c α γ +
        p11DevG C nu eps c α (γ + Pi.single i 1 : Fin n → ℕ))) := by gcongr
    _ = eps ^ j * (eps * C.L) + eps ^ j * (eps * p11DevZ C nu eps c α γ) +
        eps ^ j * p11DevG C nu eps c α (γ + Pi.single i 1 : Fin n → ℕ) := by ring
    _ ≤ _ := by linarith

/-- Rescaled deviation bound. -/
theorem p11_dev_resc (hC : P11SecularSpec D C) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Fast : P11FastData n} {eps c : ℝ} {A : P11SlowData n},
      0 < eps → eps * C.MF ≤ Real.exp (-1) → 0 ≤ c →
      K * (1 + c) * eps * Real.log (1 / eps) ^
        (5 * C.tau + 2 + (C.tau + 1) * ((p11PatchData D).mu + 1)) ≤ 1 →
      3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16 → 5 * eps ≤ p11s2 C nu eps →
      P11FastSpec C eps Fast → P11SlowSpecOf C Fast nu eps c A →
      ∀ j : ℕ, j ≤ (p11PatchData D).mu + 1 → ∀ β : Fin (n + n) → ℕ, ∑ i, β i = j + 1 →
        ∀ J ρ : P11CVec n, ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4 →
        ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4 →
        eps ^ j * ‖p11PartialVec β (p11DevH A) (Fin.append J ρ)‖ ≤
          (if j = 0 then C.L else eps * C.L) + K * (1 + c) * eps * Real.log (1 / eps) ^
            (5 * C.tau + 2 + (C.tau + 1) * ((p11PatchData D).mu + 1)) := by
  obtain ⟨k1, hk1, hs1inv⟩ := p11_prin_s1_inv hC
  obtain ⟨k2, hk2, heta⟩ := p11_prin_eta1_le hC
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  have hMF1 : 0 ≤ C.MF + 1 := by linarith
  have hMF0 : 0 ≤ C.MF := by linarith
  refine ⟨((((p11PatchData D).mu + 2).factorial : ℕ) : ℝ) * ((C.MF + 1) * 4 * k1 +
    4 ^ ((p11PatchData D).mu + 2) + k2 + 1) + k2 + 4 * k1, by positivity, ?_⟩
  intro Fast eps c A heps hεM hc0 hθ
  generalize hF : ((((p11PatchData D).mu + 2).factorial : ℕ) : ℝ) = F at hθ ⊢
  have hF1 : 1 ≤ F := by
    rw [← hF]; exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  generalize hK : F * ((C.MF + 1) * 4 * k1 + 4 ^ ((p11PatchData D).mu + 2) + k2 + 1) + k2 +
    4 * k1 = K at hθ ⊢
  generalize hQe : 5 * C.tau + 2 + (C.tau + 1) * (((p11PatchData D).mu : ℝ) + 1) = Qe at hθ ⊢
  have hl : 1 ≤ Real.log (1 / eps) := slow_log_ge_one hC heps hεM
  have hℓ0 : 0 ≤ Real.log (1 / eps) := by linarith
  have hF0 : 0 < F := by linarith
  have hP4 : (1 : ℝ) ≤ 4 ^ ((p11PatchData D).mu + 2) := one_le_pow₀ (by norm_num)
  have hKa : F * ((C.MF + 1) * 4 * k1) + F * (4 ^ ((p11PatchData D).mu + 2) + k2 + 1) = F *
      ((C.MF + 1) * 4 * k1 + 4 ^ ((p11PatchData D).mu + 2) + k2 + 1) := by ring
  have hKnn : 0 ≤ F * ((C.MF + 1) * 4 * k1 + 4 ^ ((p11PatchData D).mu + 2) + k2 + 1) := by
    positivity
  have hFK : F ≤ K := by
    have h1 : F * 1 ≤ F * ((C.MF + 1) * 4 * k1 + 4 ^ ((p11PatchData D).mu + 2) + k2 + 1) :=
      mul_le_mul_of_nonneg_left (by nlinarith [mul_pos (by linarith : 0 < C.MF + 1) hk1]) hF0.le
    linarith
  have haK : F * ((C.MF + 1) * 4 * k1) ≤ K := by
    have h1 : 0 ≤ F * (4 ^ ((p11PatchData D).mu + 2) + k2 + 1) := by positivity
    linarith
  have hKrho : F * (1 + k2) + F * 4 ^ ((p11PatchData D).mu + 2) ≤ K := by
    have h1 : F * (1 + k2) + F * 4 ^ ((p11PatchData D).mu + 2) ≤ F * (4 ^ ((p11PatchData D).mu + 2)
        + k2 + 1) := by nlinarith
    have h2 : 0 ≤ F * ((C.MF + 1) * 4 * k1) := by positivity
    linarith
  have he1 : eps ≤ 1 := by
    have h1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    nlinarith
  have hmu0 : (0 : ℝ) ≤ (p11PatchData D).mu := Nat.cast_nonneg _
  have hprod : 0 ≤ (C.tau + 1) * (((p11PatchData D).mu : ℝ) + 1) := by positivity
  have hQ1 : C.tau + 1 ≤ Qe := by rw [← hQe]; linarith
  have hQ2 : 2 * C.tau + 1 ≤ Qe := by rw [← hQe]; linarith
  have hQ3 : 5 * C.tau + 2 ≤ Qe := by rw [← hQe]; linarith
  have hlQ1 : Real.log (1 / eps) ^ (C.tau + 1) ≤ Real.log (1 / eps) ^ Qe :=
    p11_resc_rpow_le hl hQ1
  have hlQ2 : Real.log (1 / eps) ^ (2 * C.tau + 1) ≤ Real.log (1 / eps) ^ Qe :=
    p11_resc_rpow_le hl hQ2
  have hlQ3 : Real.log (1 / eps) ^ (5 * C.tau + 2) ≤ Real.log (1 / eps) ^ Qe :=
    p11_resc_rpow_le hl hQ3
  have hlx : 1 ≤ Real.log (1 / eps) ^ (2 * C.tau + 1) := Real.one_le_rpow hl (by linarith)
  have hKk2 : k2 ≤ K := by
    rw [← hK]
    have : 0 ≤ F * ((C.MF + 1) * 4 * k1 + 4 ^ ((p11PatchData D).mu + 2) + k2 + 1) := by positivity
    linarith
  have hKk1 : 4 * k1 ≤ K := by
    rw [← hK]
    have : 0 ≤ F * ((C.MF + 1) * 4 * k1 + 4 ^ ((p11PatchData D).mu + 2) + k2 + 1) := by positivity
    linarith
  have hθ' : ∀ t : ℝ, 0 ≤ t → t ≤ K → ∀ x : ℝ, x ≤ Qe →
      t * eps * Real.log (1 / eps) ^ x ≤ 1 := by
    intro t ht htK x hx
    have h1 : Real.log (1 / eps) ^ x ≤ Real.log (1 / eps) ^ Qe := p11_resc_rpow_le hl hx
    have h3 : t * eps * Real.log (1 / eps) ^ x ≤ t * eps * Real.log (1 / eps) ^ Qe := by gcongr
    have htc : t ≤ K * (1 + c) := by nlinarith
    have h4 : t * eps * Real.log (1 / eps) ^ Qe ≤ K * (1 + c) * eps * Real.log (1 / eps) ^ Qe := by
      gcongr
    exact h3.trans (h4.trans hθ)
  have hη : p11eta1 C eps ≤ k2 * eps * Real.log (1 / eps) ^ (2 * C.tau + 1) := heta heps hεM
  have hη1 : p11eta1 C eps ≤ 1 := hη.trans (hθ' k2 hk2.le hKk2 _ hQ2)
  have hs1' : 4 * eps / p11s1 C eps ≤ 4 * k1 * eps * Real.log (1 / eps) ^ (C.tau + 1) := by
    have h1 := hs1inv heps hεM
    rw [div_eq_mul_inv]
    calc 4 * eps * (p11s1 C eps)⁻¹ ≤ 4 * eps * (k1 * Real.log (1 / eps) ^ (C.tau + 1)) := by
          gcongr
      _ = 4 * k1 * eps * Real.log (1 / eps) ^ (C.tau + 1) := by ring
  have hs1small : 4 * eps / p11s1 C eps ≤ 1 :=
    hs1'.trans (hθ' (4 * k1) (by positivity) hKk1 _ hQ1)
  have hfac : ∀ m : ℕ, m ≤ (p11PatchData D).mu + 2 → ((m.factorial : ℕ) : ℝ) ≤ F := fun m hm => by
    rw [← hF]; exact_mod_cast Nat.factorial_le hm
  intro hzs h5 hFs hA j hj β hβ J ρ hJ hρ
  have hη0 : 0 ≤ p11eta1 C eps := by
    obtain ⟨-, -, -, -, hGd, -, -, -, -, -, -, -, -, hGη, -⟩ := hFs
    have hr : 0 < C.rz / 2 := by positivity
    have hs1 := (slow_pos hC hnu heps hεM).2.1
    have := hGη (KAM.realInclusion n C.J0) (by simp; linarith only [hs1]) 0 (by simpa using hr)
    exact (norm_nonneg _).trans this
  have hLmain : eps ^ j * C.L ≤ (if j = 0 then C.L else eps * C.L) := by
    by_cases hj0 : j = 0
    · simp [hj0]
    · simp only [hj0, ↓reduceIte]
      exact mul_le_mul_of_nonneg_right (pow_le_of_le_one heps.le he1 hj0)
        (by linarith only [hL1])
  have hsum1 : ∀ α γ : Fin n → ℕ, ∑ i, (Fin.append α γ : Fin (n + n) → ℕ) i =
      ∑ i, α i + ∑ i, γ i := fun α γ => by
    rw [Fin.sum_univ_add]; simp
  obtain ⟨α, γ, rfl⟩ : ∃ α γ : Fin n → ℕ, β = Fin.append α γ :=
    ⟨_, _, (Fin.append_castAdd_natAdd (f := β)).symm⟩
  rw [hsum1] at hβ
  by_cases hγ : γ = 0
  · subst hγ
    have hα : ∑ i, α i = j + 1 := by simpa using hβ
    have h := p11_resc_pure hC hnu heps hεM hFs hA hc0 hzs h5 α j hα hj J ρ hJ hρ
      (hfac _ (by omega)) hη1 hs1' hs1small hl
    refine p11_num_collect_pure heps he1 hc0 hF0.le (Real.rpow_nonneg hℓ0 _)
      (Real.rpow_nonneg hℓ0 _) hlQ1 hlQ3 haK hFK ?_
    have e1 : F * (C.MF + 1) * (4 * k1 * eps * Real.log (1 / eps) ^ (C.tau + 1)) =
        F * ((C.MF + 1) * 4 * k1) * (eps * Real.log (1 / eps) ^ (C.tau + 1)) := by ring
    linarith only [h, e1, hLmain]
  · obtain ⟨i, hi⟩ : ∃ i, γ i ≠ 0 := by
      by_contra hcon
      exact hγ (funext fun i => by by_contra hi; exact hcon ⟨i, hi⟩)
    obtain ⟨γ', hγeq, hγs⟩ := p11_dev_split γ i hi
    subst hγeq
    have hα : ∑ k, α k + ∑ k, γ' k = j := by
      simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single'] at hβ
      simp at hβ
      omega
    rw [← p11_dev_append_add]
    have h := p11_resc_rho hC hnu heps hεM hA hc0 hzs h5 i α γ' j hα hj J ρ hJ hρ
      (hfac _ (by omega)) he1 hη0 hη hl
    refine p11_num_collect_rho (m := eps * C.L) heps he1 hc0 hF0.le hk2.le (by positivity)
      (Real.rpow_nonneg hℓ0 _) (Real.rpow_nonneg hℓ0 _) hlQ2 hlQ3 hKrho h ?_
    by_cases hj0 : j = 0
    · simp only [hj0, ite_true]
      exact mul_le_of_le_one_left (by linarith only [hL1]) he1
    · simp [hj0]

end Resc

end KAM.Planetary

end
