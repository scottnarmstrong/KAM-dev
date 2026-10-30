/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LatticeCount
public import KAM.Wave.KamSupport.Lattice
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Sharp lattice sums in `ℤ²` (blueprint-W `bpW:w4:lattice` (ii), (iii))

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still being built.

With `|k|₁ = KAM.Fourier.modeSize k` and `S_q(σ) = ∑ₖ |k|₁^q e^{-2π|k|₁σ}` (real power, `0^0 = 1`):

* (ii) `waveS_zero_eq`, `waveS_zero_le`: `S_0(σ) = coth(πσ)² ≤ (1 + (πσ)⁻¹)²`;
* (iii) `waveS_le`: for `q > 0`, `S_q(σ) ≤ (4/(πσ)) ((q+1)/(eπσ))^{q+1}` (with summability).
-/

@[expose] public section

namespace KAM.Wave

open Finset

/-- The lattice sum `S_q(σ) = ∑_{k ∈ ℤ²} |k|₁^q e^{-2π|k|₁σ}`
(blueprint `bpW:w4:lattice`). -/
noncomputable def waveS (q σ : ℝ) : ℝ :=
  ∑' k : Fin 2 → ℤ, Fourier.modeSize k ^ q * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)

theorem waveS_zero_eq {σ : ℝ} (hσ : 0 < σ) :
    HasSum (fun k : Fin 2 → ℤ =>
      Fourier.modeSize k ^ (0 : ℝ) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k))
      ((Real.cosh (Real.pi * σ) / Real.sinh (Real.pi * σ)) ^ 2) := by
  simpa only [Real.rpow_zero, one_mul] using kamLattice_hasSum_exp 2 hσ

/-- `S_0(σ) = coth(πσ)²` (blueprint `bpW:w4:lattice` (ii)). -/
theorem waveS_zero_value {σ : ℝ} (hσ : 0 < σ) :
    waveS 0 σ = (Real.cosh (Real.pi * σ) / Real.sinh (Real.pi * σ)) ^ 2 :=
  (waveS_zero_eq hσ).tsum_eq

/-- `coth t ≤ 1 + 1/t` for `t > 0`. -/
theorem coth_le_one_add_inv {t : ℝ} (ht : 0 < t) :
    Real.cosh t / Real.sinh t ≤ 1 + t⁻¹ := by
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.2 ht
  rw [div_le_iff₀ hs, Real.cosh_eq, Real.sinh_eq]
  have h1 := Real.add_one_le_exp (2 * t)
  have h2 : Real.exp (2 * t) = Real.exp t * Real.exp t := by rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have h4 := Real.exp_pos t
  have h5 := Real.exp_pos (-t)
  have : (1 + t⁻¹) * ((Real.exp t - Real.exp (-t)) / 2) -
      (Real.exp t + Real.exp (-t)) / 2 = (Real.exp t - (2 * t + 1) * Real.exp (-t)) / (2 * t) := by
    field_simp
    ring
  have h6 : 0 ≤ Real.exp t - (2 * t + 1) * Real.exp (-t) := by
    have : Real.exp t - (2 * t + 1) * Real.exp (-t) = Real.exp (-t) * (Real.exp (2 * t) - (2 * t + 1)) := by
      rw [h2]
      nlinarith [h3]
    rw [this]
    exact mul_nonneg h5.le (by linarith)
  have : 0 ≤ (Real.exp t - (2 * t + 1) * Real.exp (-t)) / (2 * t) := by positivity
  linarith

/-- `S_0(σ) ≤ (1 + (πσ)⁻¹)²` (blueprint `bpW:w4:lattice` (ii)). -/
theorem waveS_zero_le {σ : ℝ} (hσ : 0 < σ) : waveS 0 σ ≤ (1 + (Real.pi * σ)⁻¹) ^ 2 := by
  rw [waveS_zero_value hσ]
  have hs : 0 < Real.sinh (Real.pi * σ) := Real.sinh_pos_iff.2 (by positivity)
  have hc : 0 ≤ Real.cosh (Real.pi * σ) / Real.sinh (Real.pi * σ) := by
    have := Real.cosh_pos (Real.pi * σ); positivity
  exact pow_le_pow_left₀ hc (coth_le_one_add_inv (by positivity)) 2

/-- Partial geometric sums: `∑_{N<M} e^{-(ε/2)(N+1)} ≤ 2/ε`. -/
theorem waveGeom_partial_le {ε : ℝ} (hε : 0 < ε) (M : ℕ) :
    ∑ N ∈ range M, Real.exp (-(ε / 2) * ((N : ℝ) + 1)) ≤ 2 / ε := by
  set r := Real.exp (-(ε / 2)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hterm : ∀ N : ℕ, Real.exp (-(ε / 2) * ((N : ℝ) + 1)) = r * r ^ N := by
    intro N
    rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  simp_rw [hterm]
  rw [← mul_sum]
  have hgeo := hasSum_geometric_of_lt_one hr0.le hr1
  have h1 : ∑ N ∈ range M, r ^ N ≤ (1 - r)⁻¹ := sum_le_hasSum (range M) (fun _ _ => by positivity) hgeo
  have hpos : 0 < 1 - r := by linarith
  have hx : r * (ε / 2 + 1) ≤ 1 := by
    have h := Real.add_one_le_exp (ε / 2)
    have : r * Real.exp (ε / 2) = 1 := by rw [hr, ← Real.exp_add]; simp
    nlinarith
  calc r * ∑ N ∈ range M, r ^ N ≤ r * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left h1 hr0.le
    _ ≤ 2 / ε := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ hpos hε]
      nlinarith

theorem waveSphere_card_le_of_kamL1 (s : Finset (Fin 2 → ℤ)) (N : ℕ) :
    (s.filter fun k => kamL1 k = N).card ≤ 4 * N ∨ N = 0 := by
  classical
  rcases Nat.eq_zero_or_pos N with h | h
  · exact Or.inr h
  refine Or.inl ?_
  rw [← waveSphere_card N h]
  refine card_le_card_of_injOn (fun k => (k 0, k 1)) ?_ ?_
  · intro k hk
    have hk' := (mem_filter.mp hk).2
    simp only [kamL1, Fin.sum_univ_two] at hk'
    simp only [waveSphere, mem_filter, mem_product, mem_Icc, Finset.mem_coe]
    omega
  · intro k _ l _ hkl
    simp only [Prod.mk.injEq] at hkl
    funext i
    fin_cases i
    · exact hkl.1
    · exact hkl.2

/-- A finset partial sum of `S_q`, `q > 0`, is at most `4 ∑_{N≤M} N^{q+1} e^{-2πσN}`. -/
theorem waveS_finset_le {q σ : ℝ} (hq : 0 < q) (s : Finset (Fin 2 → ℤ)) :
    ∑ k ∈ s, Fourier.modeSize k ^ q * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) ≤
      4 * ∑ N ∈ range (s.sup kamL1 + 1),
        ((N : ℝ) ^ (q + 1) * Real.exp (-(2 * Real.pi * σ) * N)) := by
  classical
  have hmaps : ∀ k ∈ s, kamL1 k ∈ range (s.sup kamL1 + 1) := fun k hk =>
    mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := kamL1) hk))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_le_sum fun N _ => ?_
  have hfib : ∀ k ∈ s.filter (fun k => kamL1 k = N),
      Fourier.modeSize k ^ q * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) =
        (N : ℝ) ^ q * Real.exp (-(2 * Real.pi * σ) * N) := by
    intro k hk
    have hk' := (mem_filter.mp hk).2
    rw [← kamL1_cast_eq_modeSize, hk']
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  have hrp : (N : ℝ) ^ (q + 1) = (N : ℝ) ^ q * N := by
    rw [Real.rpow_add' (by positivity) (by linarith), Real.rpow_one]
  rcases waveSphere_card_le_of_kamL1 s N with hc | h0
  · have hc' : ((s.filter fun k => kamL1 k = N).card : ℝ) ≤ 4 * N := by exact_mod_cast hc
    have h0 : 0 ≤ (N : ℝ) ^ q * Real.exp (-(2 * Real.pi * σ) * N) := by positivity
    calc _ ≤ (4 * (N : ℝ)) * ((N : ℝ) ^ q * Real.exp (-(2 * Real.pi * σ) * N)) :=
          mul_le_mul_of_nonneg_right hc' h0
      _ = _ := by rw [hrp]; ring
  · subst h0
    simp [Real.zero_rpow hq.ne', Real.zero_rpow (by linarith : q + 1 ≠ 0)]

/-- **Weighted lattice sums** (blueprint `bpW:w4:lattice` (iii)): for `q > 0`, `σ > 0`,
`S_q(σ) ≤ (4/(πσ)) ((q+1)/(eπσ))^{q+1}`, and the series is summable. -/
theorem waveS_le {q σ : ℝ} (hq : 0 < q) (hσ : 0 < σ) :
    Summable (fun k : Fin 2 → ℤ =>
        Fourier.modeSize k ^ q * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) ∧
      waveS q σ ≤ 4 / (Real.pi * σ) * ((q + 1) / (Real.exp 1 * (Real.pi * σ))) ^ (q + 1) := by
  have hx : 0 < 2 * Real.pi * σ := by positivity
  set x := 2 * Real.pi * σ with hxdef
  have hbound : ∀ s : Finset (Fin 2 → ℤ),
      ∑ k ∈ s, Fourier.modeSize k ^ q * Real.exp (-x * Fourier.modeSize k) ≤
        4 / (Real.pi * σ) * ((q + 1) / (Real.exp 1 * (Real.pi * σ))) ^ (q + 1) := by
    intro s
    refine (waveS_finset_le (σ := σ) hq s).trans ?_
    set c := (2 * (q + 1) / (Real.exp 1 * x)) ^ (q + 1) with hc
    have hc0 : 0 ≤ c := by positivity
    have hsplit := Finset.sum_range_succ' (fun N : ℕ => (N : ℝ) ^ (q + 1) * Real.exp (-x * N))
      (s.sup kamL1)
    have hterm : ∀ N ∈ range (s.sup kamL1), (((N + 1 : ℕ) : ℝ)) ^ (q + 1) *
        Real.exp (-x * ((N + 1 : ℕ) : ℝ)) ≤ c * Real.exp (-(x / 2) * ((N : ℝ) + 1)) := by
      intro N _
      have h := Fourier.rpow_mul_exp_neg_le (x := ((N : ℝ) + 1)) (τ := q + 1) (δ := x / 2)
        (by positivity) (by linarith) (by positivity)
      have hdiv : (q + 1) / (Real.exp 1 * (x / 2)) = 2 * (q + 1) / (Real.exp 1 * x) := by
        field_simp
      rw [hdiv] at h
      have hexp : Real.exp (-x * ((N : ℝ) + 1)) =
          Real.exp (-(x / 2) * ((N : ℝ) + 1)) * Real.exp (-(x / 2) * ((N : ℝ) + 1)) := by
        rw [← Real.exp_add]; congr 1; ring
      push_cast
      rw [hexp, ← mul_assoc]
      calc _ ≤ c * Real.exp (-(x / 2) * ((N : ℝ) + 1)) := by gcongr
        _ = _ := rfl
    have hsum : ∑ N ∈ range (s.sup kamL1 + 1), (N : ℝ) ^ (q + 1) * Real.exp (-x * N) ≤
        c * (2 / x) := by
      rw [hsplit]
      simp only [Nat.cast_zero, Real.zero_rpow (by linarith : q + 1 ≠ 0), zero_mul, add_zero]
      calc _ ≤ ∑ N ∈ range (s.sup kamL1), c * Real.exp (-(x / 2) * ((N : ℝ) + 1)) :=
            sum_le_sum hterm
        _ = c * ∑ N ∈ range (s.sup kamL1), Real.exp (-(x / 2) * ((N : ℝ) + 1)) := by
            rw [mul_sum]
        _ ≤ c * (2 / x) := mul_le_mul_of_nonneg_left (waveGeom_partial_le hx _) hc0
    have hbase : 2 * (q + 1) / (Real.exp 1 * x) = (q + 1) / (Real.exp 1 * (Real.pi * σ)) := by
      rw [hxdef]; field_simp
    calc 4 * ∑ N ∈ range (s.sup kamL1 + 1), (N : ℝ) ^ (q + 1) * Real.exp (-x * N)
        ≤ 4 * (c * (2 / x)) := by gcongr
      _ = _ := by
        rw [hc, hbase, hxdef]; field_simp
  have hnn : ∀ k : Fin 2 → ℤ, 0 ≤ Fourier.modeSize k ^ q * Real.exp (-x * Fourier.modeSize k) :=
    fun k => by have := Fourier.modeSize_nonneg k; positivity
  exact ⟨summable_of_sum_le hnn hbound, Real.tsum_le_of_sum_le hnn hbound⟩

end KAM.Wave
