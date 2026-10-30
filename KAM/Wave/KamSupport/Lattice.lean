/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamSupport.LatticeCount
public import KAM.Fourier.ExpSums
public import KAM.Fourier.ExponentialDecay
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Weighted lattice sums (blueprint-W `bpW:w1:lattice`)

Off-frontier, source-faithful infrastructure; the dependency graph is still being built.

For `n ≥ 1`, `σ > 0`, `ε = 2πσ`, and `|k|₁ = KAM.Fourier.modeSize k`:

* (i) `kamLattice_hasSum_exp`: `∑ₖ e^{-ε|k|₁} = coth(πσ)ⁿ`;
* (ii) `kamLattice_ncard_fiber_le`, `kamLattice_ncard_fiber_le_pow` (in `LatticeCount.lean`);
* (iii) `kamLattice_tsum_pow_exp_le`: `∑ₖ (1+|k|₁)^c e^{-ε|k|₁} ≤ S_{n,c}(σ)` with
  `kamLatticeConst n c σ = S_{n,c}(σ)`;
* (iv) `kamLattice_tsum_divisor_le`, `kamLattice_BSigma_le`: the small-divisor weights.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open Finset

variable {n : ℕ}

/-- The constant `S_{n,c}(σ) = 2ⁿ (2b/(eε))^b e^{ε/2} (1 + 2/ε)` with `ε = 2πσ`, `b = c + n - 1`
(blueprint `bpW:w1:lattice` (iii)). The power is a real power, `(·)^0 = 1`. -/
def kamLatticeConst (n : ℕ) (c σ : ℝ) : ℝ :=
  2 ^ n * ((2 * (c + (n - 1 : ℕ))) / (Real.exp 1 * (2 * Real.pi * σ))) ^ (c + (n - 1 : ℕ) : ℝ) *
    Real.exp (Real.pi * σ) * (1 + 2 / (2 * Real.pi * σ))

/-- **Lattice sum** (blueprint `bpW:w1:lattice` (i)): `∑_{k∈ℤⁿ} e^{-2πσ|k|₁} = coth(πσ)ⁿ`. -/
theorem kamLattice_hasSum_exp (n : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    HasSum (fun k : Fin n → ℤ => Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k))
      ((Real.cosh (Real.pi * σ) / Real.sinh (Real.pi * σ)) ^ n) := by
  have h := Fourier.hasSum_exp_neg_modeSize n (x := 2 * Real.pi * σ) (by positivity)
  rwa [show 2 * Real.pi * σ / 2 = Real.pi * σ by ring] at h

/-- The geometric tail: `∑_{m<N} e^{-εm/2} ≤ 1 + 2/ε`. -/
theorem kamGeom_sum_le {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∑ m ∈ range N, Real.exp (-(ε / 2) * m) ≤ 1 + 2 / ε := by
  have hq : Real.exp (-(ε / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hq0 : 0 ≤ Real.exp (-(ε / 2)) := (Real.exp_pos _).le
  have hgeo := hasSum_geometric_of_lt_one hq0 hq
  have hterm : ∀ m : ℕ, Real.exp (-(ε / 2) * m) = Real.exp (-(ε / 2)) ^ m := fun m => by
    rw [← Real.exp_nat_mul]; ring_nf
  have h1 : ∑ m ∈ range N, Real.exp (-(ε / 2) * m) ≤ (1 - Real.exp (-(ε / 2)))⁻¹ := by
    simp_rw [hterm]
    exact sum_le_hasSum (range N) (fun _ _ => by positivity) hgeo
  refine h1.trans ?_
  have hpos : 0 < 1 - Real.exp (-(ε / 2)) := by linarith
  rw [inv_le_comm₀ hpos (by positivity)]
  have hx : Real.exp (-(ε / 2)) * (ε / 2 + 1) ≤ 1 := by
    have h := Real.add_one_le_exp (ε / 2)
    have : Real.exp (-(ε / 2)) * Real.exp (ε / 2) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-(ε / 2))]
  have : (1 + 2 / ε)⁻¹ = (ε / 2) / (ε / 2 + 1) := by field_simp
  rw [this, div_le_iff₀ (by positivity)]
  nlinarith

/-- A partial-sum bound for the terms `(m+1)^b e^{-εm}`. -/
theorem kamLattice_partial_sum_le {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε) (N : ℕ) :
    ∑ m ∈ range N, ((m : ℝ) + 1) ^ b * Real.exp (-ε * m) ≤
      (2 * b / (Real.exp 1 * ε)) ^ b * Real.exp (ε / 2) * (1 + 2 / ε) := by
  have hterm : ∀ m ∈ range N, ((m : ℝ) + 1) ^ b * Real.exp (-ε * m) ≤
      ((2 * b / (Real.exp 1 * ε)) ^ b * Real.exp (ε / 2)) * Real.exp (-(ε / 2) * m) := by
    intro m _
    have h := Fourier.rpow_mul_exp_neg_le (x := (m : ℝ) + 1) (τ := b) (δ := ε / 2)
      (by positivity) hb (by positivity)
    have hdiv : b / (Real.exp 1 * (ε / 2)) = 2 * b / (Real.exp 1 * ε) := by field_simp
    rw [hdiv] at h
    have hexp : Real.exp (-ε * m) = Real.exp (-(ε / 2) * ((m : ℝ) + 1)) * Real.exp (ε / 2) *
        Real.exp (-(ε / 2) * m) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [hexp]
    calc ((m : ℝ) + 1) ^ b * (Real.exp (-(ε / 2) * ((m : ℝ) + 1)) * Real.exp (ε / 2) *
          Real.exp (-(ε / 2) * m))
        = (((m : ℝ) + 1) ^ b * Real.exp (-(ε / 2) * ((m : ℝ) + 1))) * Real.exp (ε / 2) *
          Real.exp (-(ε / 2) * m) := by ring
      _ ≤ (2 * b / (Real.exp 1 * ε)) ^ b * Real.exp (ε / 2) * Real.exp (-(ε / 2) * m) := by
        gcongr
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have hg := kamGeom_sum_le hε N
  have hc : 0 ≤ (2 * b / (Real.exp 1 * ε)) ^ b * Real.exp (ε / 2) := by positivity
  calc _ ≤ ((2 * b / (Real.exp 1 * ε)) ^ b * Real.exp (ε / 2)) * (1 + 2 / ε) :=
        mul_le_mul_of_nonneg_left hg hc
    _ = _ := by ring

theorem kamLattice_term_fiber {c ε : ℝ} (hn : 1 ≤ n) (s : Finset (Fin n → ℤ)) :
    ∑ k ∈ s, (1 + Fourier.modeSize k) ^ c * Real.exp (-ε * Fourier.modeSize k) ≤
      2 ^ n * ∑ m ∈ range (s.sup kamL1 + 1),
        ((m : ℝ) + 1) ^ (c + (n - 1 : ℕ) : ℝ) * Real.exp (-ε * m) := by
  classical
  have hmaps : ∀ k ∈ s, kamL1 k ∈ range (s.sup kamL1 + 1) := fun k hk =>
    mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := kamL1) hk))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  have hfib : ∀ k ∈ s.filter (fun k => kamL1 k = m),
      (1 + Fourier.modeSize k) ^ c * Real.exp (-ε * Fourier.modeSize k) =
        ((m : ℝ) + 1) ^ c * Real.exp (-ε * m) := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    rw [← kamL1_cast_eq_modeSize, hk', add_comm]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((s.filter fun k => kamL1 k = m).card : ℝ) ≤ 2 ^ n * ((m : ℝ) + 1) ^ (n - 1) := by
    exact_mod_cast kamLattice_card_filter_le_pow hn s m
  have hpow : ((m : ℝ) + 1) ^ (c + (n - 1 : ℕ) : ℝ) =
      ((m : ℝ) + 1) ^ c * ((m : ℝ) + 1) ^ (n - 1) := by
    rw [Real.rpow_add (by positivity), Real.rpow_natCast]
  rw [hpow]
  have h0 : 0 ≤ ((m : ℝ) + 1) ^ c * Real.exp (-ε * m) := by positivity
  calc ((s.filter fun k => kamL1 k = m).card : ℝ) * (((m : ℝ) + 1) ^ c * Real.exp (-ε * m))
      ≤ (2 ^ n * ((m : ℝ) + 1) ^ (n - 1)) * (((m : ℝ) + 1) ^ c * Real.exp (-ε * m)) :=
        mul_le_mul_of_nonneg_right hcard h0
    _ = 2 ^ n * (((m : ℝ) + 1) ^ c * ((m : ℝ) + 1) ^ (n - 1) * Real.exp (-ε * m)) := by ring

/-- **Weighted lattice sum** (blueprint `bpW:w1:lattice` (iii)): for `n ≥ 1`, `σ > 0`, `c ≥ 0`,
`∑_{k∈ℤⁿ} (1+|k|₁)^c e^{-2πσ|k|₁} ≤ S_{n,c}(σ)`, and the series is summable. -/
theorem kamLattice_tsum_pow_exp_le (hn : 1 ≤ n) {c σ : ℝ} (hc : 0 ≤ c) (hσ : 0 < σ) :
    Summable (fun k : Fin n → ℤ =>
        (1 + Fourier.modeSize k) ^ c * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) ∧
      ∑' k : Fin n → ℤ,
        (1 + Fourier.modeSize k) ^ c * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) ≤
          kamLatticeConst n c σ := by
  have hε : 0 < 2 * Real.pi * σ := by positivity
  have hb : 0 ≤ c + (n - 1 : ℕ) := by positivity
  have hbound : ∀ s : Finset (Fin n → ℤ),
      ∑ k ∈ s, (1 + Fourier.modeSize k) ^ c * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) ≤
        kamLatticeConst n c σ := by
    intro s
    refine (kamLattice_term_fiber hn s).trans ?_
    have h := kamLattice_partial_sum_le hb hε (s.sup kamL1 + 1)
    have hexp : Real.exp (2 * Real.pi * σ / 2) = Real.exp (Real.pi * σ) := by congr 1; ring
    rw [hexp] at h
    unfold kamLatticeConst
    calc 2 ^ n * ∑ m ∈ range (s.sup kamL1 + 1),
          ((m : ℝ) + 1) ^ (c + (n - 1 : ℕ) : ℝ) * Real.exp (-(2 * Real.pi * σ) * m)
        ≤ 2 ^ n * ((2 * (c + (n - 1 : ℕ)) / (Real.exp 1 * (2 * Real.pi * σ))) ^
            (c + (n - 1 : ℕ) : ℝ) * Real.exp (Real.pi * σ) * (1 + 2 / (2 * Real.pi * σ))) := by
          gcongr
      _ = _ := by ring
  have hnn : ∀ k : Fin n → ℤ,
      0 ≤ (1 + Fourier.modeSize k) ^ c * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) :=
    fun k => by have := Fourier.modeSize_nonneg k; positivity
  exact ⟨summable_of_sum_le hnn hbound, Real.tsum_le_of_sum_le hnn hbound⟩

theorem kamLattice_const_nonneg {c σ : ℝ} (hc : 0 ≤ c) (hσ : 0 < σ) :
    0 ≤ kamLatticeConst n c σ := by
  unfold kamLatticeConst
  have : 0 ≤ c + (n - 1 : ℕ) := by positivity
  positivity

/-- `1 + x^τ ≤ (1+x)^τ` for `x ≥ 0`, `τ ≥ 1` (blueprint `bpW:w1:lattice` (iv)). -/
theorem kamDivisor_le {x τ : ℝ} (hx : 0 ≤ x) (hτ : 1 ≤ τ) : 1 + x ^ τ ≤ (1 + x) ^ τ := by
  lift x to NNReal using hx
  have h := NNReal.add_rpow_le_rpow_add 1 x hτ
  rw [NNReal.one_rpow] at h
  exact_mod_cast h

/-- **Small-divisor weights** (blueprint `bpW:w1:lattice` (iv)): for `τ ≥ 1`, `γ, β ≥ 0`,
`∑ₖ A_k^γ (1+|k|₁)^β e^{-2πσ|k|₁} ≤ S_{n,γτ+β}(σ)` with `A_k = 1 + |k|₁^τ`. -/
theorem kamLattice_tsum_divisor_le (hn : 1 ≤ n) {τ γ β σ : ℝ} (hτ : 1 ≤ τ) (hγ : 0 ≤ γ)
    (hβ : 0 ≤ β) (hσ : 0 < σ) :
    Summable (fun k : Fin n → ℤ => (1 + Fourier.modeSize k ^ τ) ^ γ *
        (1 + Fourier.modeSize k) ^ β * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) ∧
      ∑' k : Fin n → ℤ, (1 + Fourier.modeSize k ^ τ) ^ γ * (1 + Fourier.modeSize k) ^ β *
        Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) ≤ kamLatticeConst n (γ * τ + β) σ := by
  have hc : 0 ≤ γ * τ + β := by positivity
  obtain ⟨hs, hle⟩ := kamLattice_tsum_pow_exp_le hn hc hσ
  have hpt : ∀ k : Fin n → ℤ, (1 + Fourier.modeSize k ^ τ) ^ γ * (1 + Fourier.modeSize k) ^ β *
        Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) ≤
      (1 + Fourier.modeSize k) ^ (γ * τ + β) *
        Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) := by
    intro k
    have hk := Fourier.modeSize_nonneg k
    have h1 : (1 + Fourier.modeSize k ^ τ) ^ γ ≤ (1 + Fourier.modeSize k) ^ (γ * τ) := by
      rw [mul_comm, Real.rpow_mul (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (kamDivisor_le hk hτ) hγ
    rw [Real.rpow_add (by positivity)]
    gcongr
  have hnn : ∀ k : Fin n → ℤ, 0 ≤ (1 + Fourier.modeSize k ^ τ) ^ γ * (1 + Fourier.modeSize k) ^ β *
        Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) :=
    fun k => by have := Fourier.modeSize_nonneg k; positivity
  have hsum := Summable.of_nonneg_of_le hnn hpt hs
  exact ⟨hsum, (Summable.tsum_le_tsum hpt hsum hs).trans hle⟩

/-- **P96-K's `B_σ²`** (blueprint `bpW:w1:lattice` (iv)): in period-one units
`2ⁿ ∑ₖ (1+|k|₁)² A_k⁴ e^{-2σ|k|₁} ≤ 2ⁿ S_{n,4τ+2}(σ/π)`. -/
theorem kamLattice_BSigma_le (hn : 1 ≤ n) {τ σ : ℝ} (hτ : 1 ≤ τ) (hσ : 0 < σ) :
    2 ^ n * ∑' k : Fin n → ℤ, (1 + Fourier.modeSize k) ^ (2 : ℝ) *
        (1 + Fourier.modeSize k ^ τ) ^ (4 : ℝ) * Real.exp (-(2 * σ) * Fourier.modeSize k) ≤
      2 ^ n * kamLatticeConst n (4 * τ + 2) (σ / Real.pi) := by
  have hσ' : 0 < σ / Real.pi := by positivity
  have h := (kamLattice_tsum_divisor_le hn hτ (γ := 4) (β := 2) (by norm_num) (by norm_num) hσ').2
  have hε : 2 * Real.pi * (σ / Real.pi) = 2 * σ := by field_simp
  rw [hε] at h
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc _ = ∑' k : Fin n → ℤ, (1 + Fourier.modeSize k ^ τ) ^ (4 : ℝ) *
        (1 + Fourier.modeSize k) ^ (2 : ℝ) * Real.exp (-(2 * σ) * Fourier.modeSize k) :=
        tsum_congr fun k => by ring
    _ ≤ _ := h

end KAM.Wave
