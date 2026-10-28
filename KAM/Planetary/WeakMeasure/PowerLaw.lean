/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakMeasure.Diophantine
public import KAM.Measure.Lattice

/-!
# The power-law Diophantine set (blueprint `bpP:p11a:power-law`, P11A-W8)

For the profile `Ψ(k) = γ |k|₁^(-τ)`: the per-mode ratio `Ψ(k)/|k|₂ ≤ √m γ |k|₁^(-τ-1) ≤ √m γ`
(`stepP:p11a:pl-profile`, `p11_pl_profile`), the lattice-sum bound
(`stepP:p11a:pl-sum`, `p11_pl_sum`) and the concentration estimate (`stepP:p11a:pl-conc`, inlined
in `power_law`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff ENNReal
namespace KAM.Planetary

def p11CDio (n m rho mu : ℕ) (d v beta M tau : ℝ) : ℝ :=
  p11Csub n mu d v (M/beta) * beta^(-((mu : ℝ)⁻¹)) *
    (m : ℝ)^((rho : ℝ)/(2*mu)) * 2*3^(m-1) *
      (1+(((rho : ℝ)*(tau+1)/mu-m)⁻¹))
def p11GammaStar (m rho mu : ℕ) (beta C eps : ℝ) : ℝ :=
  min ((1/2 : ℝ)*(m : ℝ)^(-(1/2 : ℝ))*(beta/4)^((rho : ℝ)⁻¹))
    ((eps/C)^((mu : ℝ)/rho))

section PowerLaw

variable {m : ℕ}

theorem p11_modeSize_pos {k : Fin m → ℤ} (hk : k ≠ 0) : 0 < KAM.Fourier.modeSize k := by
  refine lt_of_le_of_ne (KAM.Fourier.modeSize_nonneg k) fun h => hk ?_
  funext i
  have := KAM.Fourier.abs_coord_le_modeSize k i
  rw [← h] at this
  simpa using abs_nonpos_iff.1 this

theorem p11_modeSize_ge_one {k : Fin m → ℤ} (hk : k ≠ 0) : 1 ≤ KAM.Fourier.modeSize k := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h; push Not at h; exact hk (funext h)
  have h1 : (1 : ℝ) ≤ |(k i : ℝ)| := by
    have : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
    exact_mod_cast this
  exact h1.trans (KAM.Fourier.abs_coord_le_modeSize k i)

/-- `stepP:p11a:pl-profile`. -/
theorem p11_pl_profile {gamma tau : ℝ} (hg : 0 < gamma) (htau : 0 ≤ tau + 1)
    {k : Fin m → ℤ} (hk : k ≠ 0) :
    gamma * KAM.Fourier.modeSize k ^ (-tau) / p11euclid (fun i => (k i : ℝ)) ≤
        Real.sqrt m * gamma * KAM.Fourier.modeSize k ^ (-tau - 1) ∧
      Real.sqrt m * gamma * KAM.Fourier.modeSize k ^ (-tau - 1) ≤ Real.sqrt m * gamma := by
  have hs := p11_modeSize_pos hk
  have he := p11euclid_int_pos hk
  have hcmp := (KAM.Nekhoroshev.modeSize_euclid_compare k).2
  set s := KAM.Fourier.modeSize k
  set e := p11euclid (fun i => (k i : ℝ))
  have hpow : s ^ (-tau - 1) = s ^ (-tau) / s := Real.rpow_sub_one hs.ne' _
  have hpos : 0 < s ^ (-tau) := Real.rpow_pos_of_pos hs _
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ he, hpow]
    have : s ^ (-tau) / s * s = s ^ (-tau) := div_mul_cancel₀ _ hs.ne'
    calc gamma * s ^ (-tau) = gamma * (s ^ (-tau) / s * s) := by rw [this]
      _ ≤ gamma * (s ^ (-tau) / s * (Real.sqrt m * e)) := by gcongr
      _ = Real.sqrt m * gamma * (s ^ (-tau) / s) * e := by ring
  · have : s ^ (-tau - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (p11_modeSize_ge_one hk) (by linarith)
    have h0 : 0 ≤ Real.sqrt m * gamma := by positivity
    simpa using mul_le_mul_of_nonneg_left this h0

end PowerLaw

section Main

variable {n m rho mu : ℕ}

theorem p11_pl_sum {tau : ℝ} (hm : 1 ≤ m) (hrho : 1 ≤ rho) (hmu : 1 ≤ mu)
    (ht : (m : ℝ)*mu/rho-1 < tau) :
    Summable (fun k : {k : Fin m → ℤ // k ≠ 0} =>
      (KAM.Fourier.modeSize k.val) ^ (-((tau+1)*((rho : ℝ)/mu)))) ∧
    ∑' k : {k : Fin m → ℤ // k ≠ 0},
      (KAM.Fourier.modeSize k.val) ^ (-((tau+1)*((rho : ℝ)/mu))) ≤
        2*3^(m-1)*(1+(((rho : ℝ)*(tau+1)/mu-m)⁻¹)) := by
  have hr : (0 : ℝ) < rho := by exact_mod_cast hrho
  have hu : (0 : ℝ) < mu := by exact_mod_cast hmu
  set q : ℝ := (rho : ℝ)/mu with hq
  have hqpos : 0 < q := div_pos hr hu
  have hlt : (m : ℝ) < (tau + 1) * q := by
    have h1 : (m : ℝ) * mu / rho < tau + 1 := by linarith
    have h2 := mul_lt_mul_of_pos_right h1 hqpos
    have h3 : (m : ℝ) * mu / rho * q = m := by rw [hq]; field_simp
    rw [h3] at h2; exact h2
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨hs, hb⟩ := KAM.Measure.lattice_sum hm (τ := (tau + 1) * q - 1) (by linarith)
  have heq : ∀ k : {k : Fin m → ℤ // k ≠ 0},
      (∑ i, |((k.val : Fin m → ℤ) i : ℝ)|) ^ (-((tau + 1) * q - 1) - 1) =
        (KAM.Fourier.modeSize k.val) ^ (-((tau+1)*q)) := fun k => by
    unfold KAM.Fourier.modeSize; congr 1; ring
  simp only [heq] at hs hb
  refine ⟨hs, hb.trans (le_of_eq ?_)⟩
  have hne : (tau + 1) * q - 1 + 1 - m ≠ 0 := by intro h; linarith
  have : (rho : ℝ) * (tau + 1) / mu = (tau + 1) * q := by rw [hq]; ring
  rw [this]
  have h2 : (tau + 1) * q - m ≠ 0 := by intro h; linarith
  have h3 : (tau + 1) * q - 1 + 2 - m = ((tau + 1) * q - m) + 1 := by ring
  have h4 : (tau + 1) * q - 1 + 1 - m = (tau + 1) * q - m := by ring
  rw [h3, h4]
  field_simp

theorem p11_C_nonneg {P : P11Patch n} {M beta tau : ℝ} (hm : 1 ≤ m) (hrho : 1 ≤ rho)
    (hmu : 1 ≤ mu) (hb : 0 < beta) (hM : 0 ≤ M) (ht : (m : ℝ)*mu/rho-1 < tau) :
    0 ≤ p11CDio n m rho mu (Metric.diam P.K) P.v beta M tau := by
  have hr : (0 : ℝ) < rho := by exact_mod_cast hrho
  have hu : (0 : ℝ) < mu := by exact_mod_cast hmu
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlt : (m : ℝ) < (rho : ℝ) * (tau + 1) / mu := by
    have h1 : (m : ℝ) * mu / rho < tau + 1 := by linarith
    rw [lt_div_iff₀ hu]
    have := mul_lt_mul_of_pos_right h1 hr
    have h3 : (m : ℝ) * mu / rho * rho = m * mu := by field_simp
    nlinarith
  have hpos : 0 < (rho : ℝ) * (tau + 1) / mu - m := by linarith
  have hA := p11Csub_nonneg (P := P) (mu := mu) hb hM
  unfold p11CDio
  have : 0 < (1 : ℝ) + ((rho : ℝ) * (tau + 1) / mu - m)⁻¹ := by positivity
  positivity

/-- `bpP:p11a:power-law`; `stepP:p11a:pl-conc` is inlined. -/
theorem power_law {n m rho mu : ℕ} {P : P11Patch n}
    {w : P11Vec n → P11Vec m} {wt : (Fin m → ℤ) → P11Vec n → P11Vec m}
    {beta M tau gamma : ℝ} (H : P11DioHyp P rho mu w wt beta M)
    (ht : (m : ℝ)*mu/rho-1 < tau) (hg : 0 < gamma)
    (hsmall : (Real.sqrt m*gamma)^rho < beta/4) :
    let G := p11Good P.K wt (fun k => gamma * KAM.Fourier.modeSize k ^ (-tau))
    let C := p11CDio n m rho mu (Metric.diam P.K) P.v beta M tau
    IsCompact G ∧ volume (P.K \ G) ≤ ENNReal.ofReal (C*gamma^((rho : ℝ)/mu)) ∧
    ∀ eps, 0 < eps → ENNReal.ofReal eps < volume P.K →
      gamma ≤ p11GammaStar m rho mu beta C eps →
      volume P.K - ENNReal.ofReal eps ≤ volume G := by
  intro G C
  have hm := H.m_pos
  have hmu := H.mu_pos
  have hrho : 1 ≤ rho := by rcases H.convention with h | h <;> omega
  have hβ := H.beta_pos
  have hM : 0 ≤ M := hβ.le.trans H.size_ge
  have hr : (0 : ℝ) < rho := by exact_mod_cast hrho
  have hu : (0 : ℝ) < mu := by exact_mod_cast hmu
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 0 < (rho : ℝ) / mu := div_pos hr hu
  have htau1 : 0 ≤ tau + 1 := by
    have : (0 : ℝ) < (m : ℝ) * mu / rho := by positivity
    linarith
  have hC : 0 ≤ C := p11_C_nonneg (P := P) hm hrho hmu hβ hM ht
  have hsm : 0 ≤ Real.sqrt m * gamma := by positivity
  have hpsi : ∀ k : Fin m → ℤ, k ≠ 0 →
      0 < gamma * KAM.Fourier.modeSize k ^ (-tau) := fun k hk =>
    mul_pos hg (Real.rpow_pos_of_pos (p11_modeSize_pos hk) _)
  have hprof := fun (k : Fin m → ℤ) (hk : k ≠ 0) => p11_pl_profile hg htau1 hk
  have hsm' : ∀ k : Fin m → ℤ, k ≠ 0 →
      (gamma * KAM.Fourier.modeSize k ^ (-tau) / p11euclid (fun i => (k i : ℝ)))^rho
        < beta/4 := fun k hk =>
    lt_of_le_of_lt (pow_le_pow_left₀
      (div_nonneg (hpsi k hk).le (p11euclid_int_pos hk).le)
      ((hprof k hk).1.trans (hprof k hk).2) rho) hsmall
  obtain ⟨hcomp, hvol⟩ := diophantine_measure H _ hpsi hsm'
  set q : ℝ := (rho : ℝ) / mu with hqdef
  have hmeas : volume (P.K \ G) ≤ ENNReal.ofReal (C * gamma ^ q) := by
    obtain ⟨hsum, hS⟩ := p11_pl_sum (tau := tau) hm hrho hmu ht
    set A := p11Csub n mu (Metric.diam P.K) P.v (M/beta) * beta^(-((mu : ℝ)⁻¹)) with hA
    have hA0 : 0 ≤ A :=
      mul_nonneg (p11Csub_nonneg (P := P) hβ hM) (Real.rpow_nonneg hβ.le _)
    set c := (Real.sqrt m * gamma) ^ q with hcdef
    have hc0 : 0 ≤ c := Real.rpow_nonneg hsm _
    have hterm : ∀ k : {k : Fin m → ℤ // k ≠ 0},
        ENNReal.ofReal ((gamma * KAM.Fourier.modeSize k.val ^ (-tau) /
            p11euclid (fun i => ((k.val i : ℤ) : ℝ))) ^ q) ≤
          ENNReal.ofReal (c * KAM.Fourier.modeSize k.val ^ (-((tau+1)*q))) := by
      intro k
      apply ENNReal.ofReal_le_ofReal
      have hs := p11_modeSize_pos k.2
      have hnn : 0 ≤ gamma * KAM.Fourier.modeSize k.val ^ (-tau) /
          p11euclid (fun i => ((k.val i : ℤ) : ℝ)) :=
        div_nonneg (hpsi k.1 k.2).le (p11euclid_int_pos k.2).le
      calc _ ≤ (Real.sqrt m * gamma * KAM.Fourier.modeSize k.val ^ (-tau - 1)) ^ q :=
            Real.rpow_le_rpow hnn (hprof k.1 k.2).1 hq.le
        _ = c * KAM.Fourier.modeSize k.val ^ (-((tau+1)*q)) := by
          rw [Real.mul_rpow hsm (Real.rpow_nonneg hs.le _), ← Real.rpow_mul hs.le]
          congr 2; ring
    have hnonneg : ∀ k : {k : Fin m → ℤ // k ≠ 0},
        0 ≤ c * KAM.Fourier.modeSize k.val ^ (-((tau+1)*q)) := fun k =>
      mul_nonneg hc0 (Real.rpow_nonneg (p11_modeSize_pos k.2).le _)
    have htsum : ∑' k : {k : Fin m → ℤ // k ≠ 0},
        ENNReal.ofReal (c * KAM.Fourier.modeSize k.val ^ (-((tau+1)*q))) =
        ENNReal.ofReal (c * ∑' k : {k : Fin m → ℤ // k ≠ 0},
          KAM.Fourier.modeSize k.val ^ (-((tau+1)*q))) := by
      rw [← tsum_mul_left]
      exact (ENNReal.ofReal_tsum_of_nonneg hnonneg (hsum.mul_left c)).symm
    have hcC : c = (m : ℝ) ^ ((rho : ℝ) / (2 * mu)) * gamma ^ q := by
      rw [hcdef, Real.mul_rpow (Real.sqrt_nonneg _) hg.le, Real.sqrt_eq_rpow,
        ← Real.rpow_mul (Nat.cast_nonneg m)]
      congr 2; rw [hqdef]; field_simp
    calc volume (P.K \ G) ≤ _ := hvol
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (c * ∑' k : {k : Fin m → ℤ // k ≠ 0},
          KAM.Fourier.modeSize k.val ^ (-((tau+1)*q))) := by
        rw [← htsum]; exact mul_le_mul_right (ENNReal.tsum_le_tsum hterm) _
      _ = ENNReal.ofReal (A * (c * ∑' k : {k : Fin m → ℤ // k ≠ 0},
          KAM.Fourier.modeSize k.val ^ (-((tau+1)*q)))) := (ENNReal.ofReal_mul hA0).symm
      _ ≤ ENNReal.ofReal (C * gamma ^ q) := by
        apply ENNReal.ofReal_le_ofReal
        have hT : A * (c * ∑' k : {k : Fin m → ℤ // k ≠ 0},
            KAM.Fourier.modeSize k.val ^ (-((tau+1)*q))) ≤
            A * (c * (2*3^(m-1)*(1+(((rho : ℝ)*(tau+1)/mu-m)⁻¹)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS hc0) hA0
        refine hT.trans (le_of_eq ?_)
        simp only [C, p11CDio, hcC, hA]
        ring
  refine ⟨hcomp, hmeas, ?_⟩
  intro eps heps hlt hγ
  have hGK : G ⊆ P.K := fun y hy => hy.1
  have hcle : C * gamma ^ q ≤ eps := by
    rcases hC.eq_or_lt with h0 | hpos
    · rw [← h0]; simpa using heps.le
    · have h := hγ.trans (min_le_right _ _)
      have h2 : gamma ^ q ≤ eps / C := by
        calc gamma ^ q ≤ ((eps / C) ^ ((mu : ℝ) / rho)) ^ q :=
              Real.rpow_le_rpow hg.le h hq.le
          _ = eps / C := by
            rw [← Real.rpow_mul (by positivity)]
            have : (mu : ℝ) / rho * q = 1 := by rw [hqdef]; field_simp
            rw [this, Real.rpow_one]
      rw [le_div_iff₀ hpos] at h2
      linarith
  rw [tsub_le_iff_right]
  calc volume P.K = volume (P.K ∩ G) + volume (P.K \ G) :=
        (measure_inter_add_sdiff _ hcomp.measurableSet).symm
    _ ≤ volume G + ENNReal.ofReal eps :=
        add_le_add (measure_mono inter_subset_right) (hmeas.trans (ENNReal.ofReal_le_ofReal hcle))

end Main

end KAM.Planetary
