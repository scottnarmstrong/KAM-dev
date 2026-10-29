/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowAverage
public import KAM.Planetary.Preparation.SlowConclude
public import KAM.Planetary.Preparation.SlowSmall
public import KAM.Planetary.Preparation.SlowCoeff
public import KAM.Planetary.Preparation.SlowMW

/-!
# Slow averaging: assembly of `avg_slow_of_spec` (P11A-P7d)

`avg_slow_of_spec`: for `C` with `P11SecularSpec D C`, `1 ≤ ν` and fast data satisfying
`P11FastSpec` for all small `ε`, there are `ε₂`, `c₂` such that `P11SlowSpecOf` holds for every
`ε ≤ ε₂`. P7b supplies `Ẑ, h₀, f₂` (`p11_slow_osc`), P7c the divisor clause and the
averaging step (`p11_slow_divisor`, `p11_slow_conclude`); the constant `c₂` dominates all the
explicit constants and `ε₂` is chosen by the eventual lemmas of `SlowSmall`/`SlowRates`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric Filter
open scoped BigOperators Topology
namespace KAM.Planetary

section Assembly

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- The eventual smallness conditions on `ε` used by the assembly. -/
theorem p11_slow_eventually (hC : P11SecularSpec D C) {nu c : ℝ} (hnu : 1 ≤ nu) (hc : 0 ≤ c) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), (0 < eps ∧ eps * C.MF ≤ Real.exp (-1) ∧
      eps ≤ Real.exp (-1) ∧ 3 * eps ≤ C.rz ^ 2 / 32) ∧ p11eta1 C eps ≤ 1 ∧
      (0 < eps → eps * C.MF ≤ Real.exp (-1) → Real.pi * eps ≤ p11s2 C nu eps) ∧
      (0 < eps → eps * C.MF ≤ Real.exp (-1) →
        p11K2 C nu eps * (c * (eps + p11eta1 C eps)) ≤
          C.gamma * p11K2 C nu eps ^ (-C.tau) / 8) ∧
      (0 < eps → eps * C.MF ≤ Real.exp (-1) →
        eps * p11K2 C nu eps * p11SlowMW C ≤ C.gamma * p11K2 C nu eps ^ (-C.tau) / 4 *
          min (p11s1 C eps / 4) (Real.pi * C.rz ^ 2 / 32)) ∧
      c * eps ^ (5 / 2 : ℝ) * Real.log (1 / eps) ^ (2 * C.tau + 1) ≤
        (eps * (C.gamma / 4 * (3 * nu / (Real.pi * (C.sigma / 12)) * Real.log (1 / eps)) ^
          (-C.tau))) * Real.pi * eps / (128 * (3 * nu / (Real.pi * (C.sigma / 12)) *
          Real.log (1 / eps))) := by
  obtain ⟨hγ0, hτ0, -, -, -, hσ0, -, -, -, -⟩ := fast_consts hC
  obtain ⟨cη, eps1, heps1, hη⟩ := p11eta1_source_rate hC
  have hπ := Real.pi_pos
  have hnu0 : 0 < nu := by linarith
  have ha : 0 < 3 * nu / (Real.pi * (C.sigma / 12)) := by positivity
  have hη1 : ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), p11eta1 C eps ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT heps1, Ioo_mem_nhdsGT (Real.exp_pos (-1)),
      eventually_eps_log_le (m := 2 * C.tau + 1) (by linarith) (show 0 < 1 / (|cη| + 1) by
        positivity)] with eps h0 h0' h2
    have hl1 := log_inv_ge_one h0.1 h0'.2.le
    have hl : 0 ≤ eps * Real.log (1 / eps) ^ (2 * C.tau + 1) :=
      mul_nonneg h0.1.le (Real.rpow_nonneg (by linarith) _)
    have h3 : cη * eps * Real.log (1 / eps) ^ (2 * C.tau + 1) ≤ |cη| *
        (eps * Real.log (1 / eps) ^ (2 * C.tau + 1)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self cη) hl
    refine (hη eps h0.1 h0.2.le).trans (h3.trans ?_)
    calc |cη| * (eps * Real.log (1 / eps) ^ (2 * C.tau + 1)) ≤ |cη| * (1 / (|cη| + 1)) :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith
  filter_upwards [slow_base_eventually hC, hη1, slow_pe_eventually hC hnu,
    slow_cz_eventually hC hnu hc, slow_R4_eventually hC hnu (p11SlowMW_nonneg hC),
    slow_b2_eventually c ha hγ0 hτ0.le] with eps h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The constant `c₂` of the assembly: dominates the constants of `p11_slow_conclude`. -/
def p11SlowAsmC (C : P11SecularData n) (nu c0 : ℝ) : ℝ :=
  max c0 (max (C.MF ^ 3 + 260 * c0 ^ 2 * (3 * nu / (Real.pi * (C.sigma / 12))) ^ C.tau /
      (Real.pi ^ 2 * C.gamma * (C.sigma / 12)))
    (max (6 * c0 * (3 * nu / (Real.pi * (C.sigma / 12))) ^ C.tau /
      (Real.pi * C.gamma * (C.sigma / 12)))
      (18 * c0 * (3 * nu / (Real.pi * (C.sigma / 12))) ^ C.tau / (Real.pi ^ 2 * C.gamma))))

/-- The assembly at one `ε`: all smallness conditions in hand. -/
theorem p11_slow_at (hC : P11SecularSpec D C) {nu eps c0 : ℝ} (hnu : 1 ≤ nu) (hc0 : 1 ≤ c0)
    {Fast : P11FastData n} (hF : P11FastSpec C eps Fast)
    (hosc : ∃ Z h0 : P11CVec (n + n) → ℂ, ∃ f2 : P11Phase (n + n) → ℂ,
      P11SlowOscSpec C Fast eps c0 Z h0 f2)
    (hs : (0 < eps ∧ eps * C.MF ≤ Real.exp (-1) ∧
      eps ≤ Real.exp (-1) ∧ 3 * eps ≤ C.rz ^ 2 / 32) ∧ p11eta1 C eps ≤ 1 ∧
      (0 < eps → eps * C.MF ≤ Real.exp (-1) → Real.pi * eps ≤ p11s2 C nu eps) ∧
      (0 < eps → eps * C.MF ≤ Real.exp (-1) →
        p11K2 C nu eps * (p11SlowAsmC C nu c0 * (eps + p11eta1 C eps)) ≤
          C.gamma * p11K2 C nu eps ^ (-C.tau) / 8) ∧
      (0 < eps → eps * C.MF ≤ Real.exp (-1) →
        eps * p11K2 C nu eps * p11SlowMW C ≤ C.gamma * p11K2 C nu eps ^ (-C.tau) / 4 *
          min (p11s1 C eps / 4) (Real.pi * C.rz ^ 2 / 32)) ∧
      p11SlowAsmC C nu c0 * eps ^ (5 / 2 : ℝ) * Real.log (1 / eps) ^ (2 * C.tau + 1) ≤
        (eps * (C.gamma / 4 * (3 * nu / (Real.pi * (C.sigma / 12)) * Real.log (1 / eps)) ^
          (-C.tau))) * Real.pi * eps / (128 * (3 * nu / (Real.pi * (C.sigma / 12)) *
          Real.log (1 / eps)))) :
    ∃ A, P11SlowSpecOf C Fast nu eps (p11SlowAsmC C nu c0) A := by
  obtain ⟨⟨heps, hεM, hεE, hrz⟩, hη1, hpe, hcz, hR, hb2⟩ := hs
  obtain ⟨Z, h0, f2, hosc⟩ := hosc
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12⟩ := hosc
  obtain ⟨hγ0, hτ0, hL1, hrC0, hrC1, hσ0, hσ1, hrz0, hrz1, hMF⟩ := fast_consts hC
  obtain ⟨hK, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  have hsm : 64 * eps < C.rz ^ 2 := by linarith
  have hη0 := p11eta1_pos hC heps hεM
  set c := p11SlowAsmC C nu c0 with hcdef
  have hcc0 : c0 ≤ c := le_max_left _ _
  have hcg : C.MF ^ 3 + 260 * c0 ^ 2 * (3 * nu / (Real.pi * (C.sigma / 12))) ^ C.tau /
      (Real.pi ^ 2 * C.gamma * (C.sigma / 12)) ≤ c :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hcd1 : 6 * c0 * (3 * nu / (Real.pi * (C.sigma / 12))) ^ C.tau /
      (Real.pi * C.gamma * (C.sigma / 12)) ≤ c :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hcd3 : 18 * c0 * (3 * nu / (Real.pi * (C.sigma / 12))) ^ C.tau /
      (Real.pi ^ 2 * C.gamma) ≤ c :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hsub : p11SlowBox C nu eps ⊆ p11SlowAvgBox C eps := p11SlowBox_subset_avg hC hK
  have hsubS : KAM.complexStrip (n + n) (C.sigma / 12) ×ˢ p11SlowBox C nu eps ⊆
      KAM.complexStrip (n + n) (C.sigma / 12) ×ˢ p11SlowAvgBox C eps :=
    prod_mono subset_rfl hsub
  have hpe' := hpe heps hεM
  have hhalf : p11Box (p11SlowCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2) ⊆
      p11SlowAvgBox C eps := fun I hI =>
    hsub (p11Box_half_subset _ hs2.le (by positivity) hI)
  have h3 : ∀ I ∈ p11SlowBox C nu eps,
      h0 I = C.h (fun i : Fin n => I (Fin.castAdd n i)) + eps * p11SlowW C Z I :=
    fun I hI => o3 I (hsub hI)
  have hdZ0 := p11_drho_of_clause6 o6
  have hdZ : ∀ J : P11CVec n, ‖J - KAM.realInclusion n C.J0‖ < p11s1 C eps / 4 →
      ∀ rho : P11CVec n, ‖rho - (fun _ => (2 * Real.pi * eps : ℂ))‖ < Real.pi * eps →
        ∀ i : Fin n, ‖fderiv ℂ (fun rho : P11CVec n => Z (Fin.append J rho)) rho
          (Pi.single i 1)‖ ≤ c * (eps + p11eta1 C eps) := fun J hJ rho hρ i =>
    (hdZ0 J hJ rho hρ i).trans (mul_le_mul_of_nonneg_right hcc0 (by linarith))
  have hdiv0 := p11_slow_divisor hC (h0 := h0) (Z := Z) (cZ := c * (eps + p11eta1 C eps))
    (MW := p11SlowMW C) heps hK hs1 hs2 hrz
    (mul_nonneg (by linarith [le_max_left (1 : ℝ) c0]) (by linarith)) h3 o4
    (p11_slow_MW hC hη1 (p11s1_le C eps) o5) hdZ (hcz heps hεM) (hR heps hεM)
  have hδ : 0 ≤ C.gamma * p11K2 C nu eps ^ (-C.tau) :=
    mul_nonneg hγ0.le (Real.rpow_pos_of_pos hK _).le
  have hα := p11_slow_alpha1_le_half (τ := C.tau) hγ0.le hK
  have hdiv : ∀ I ∈ p11SlowBox C nu eps, ∀ k : Fin (n + n) → ℤ, k ≠ 0 →
      KAM.Fourier.modeSize k ≤ p11K2 C nu eps →
      (if (fun i : Fin n => k (Fin.castAdd n i)) = 0 then eps else 1) *
        C.gamma / 4 * p11K2 C nu eps ^ (-C.tau) ≤
        ‖p11dotC k (fun i => fderiv ℂ h0 I (Pi.single i 1))‖ := by
    intro I hI k hk hkK
    refine le_trans ?_ (hdiv0 I hI k hk hkK)
    split_ifs
    · nlinarith [mul_nonneg heps.le hδ]
    · linarith
  have hf0 : ∀ I ∈ p11Box (p11SlowCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2),
      ‖KAM.Weighted.coeff f2 I 0‖ ≤ C.MF ^ 3 * eps ^ 3 := fun I hI => by
    have := p11_slow_coeff_zero hC Fast hF heps hεM hsm o1 o2 (hhalf hI)
    rwa [mul_pow, mul_comm] at this
  have hb2' : c * eps ^ (5 / 2 : ℝ) * Real.log (1 / eps) ^ (2 * C.tau + 1) ≤
      (eps * C.gamma / 4 * p11K2 C nu eps ^ (-C.tau)) * Real.pi * eps /
        (128 * p11K2 C nu eps) := by
    refine hb2.trans (le_of_eq ?_)
    unfold p11K2
    ring
  obtain ⟨Psi, g2, f3, hU⟩ := p11_slow_conclude hC (cf0 := C.MF ^ 3) (c := c) hnu
    (by positivity) heps hεE hpe' (by linarith) (o7.mono hsub) (o8.mono hsubS)
    (fun z hz i => o11 z (hsubS hz) i) (fun I hI => o10 I (hsub hI))
    (fun x hx => o9 x (hsubS hx)) (fun I hI => o12 I (hsub hI)) hf0 hdiv hb2' hcc0 hcg hcd1 hcd3
  refine ⟨⟨Psi, h0, g2, Z, f2, f3⟩, ?_⟩
  unfold P11SlowSpecOf
  dsimp only
  refine ⟨fun z hz => o1 z (hsubS hz), fun I hI => o2 I (hsub hI), fun I hI => o3 I (hsub hI),
    o4, ?_, hdiv, hU⟩
  intro alpha J hJ rho hρ
  refine (o6 alpha J hJ rho hρ).trans ?_
  have hX : 0 ≤ eps + p11eta1 C eps := by linarith
  have hY : 0 ≤ ∏ i, ((alpha i).factorial : ℝ) := Finset.prod_nonneg fun i _ => by positivity
  have hZ : 0 ≤ (4 / p11s1 C eps) ^ (∑ i, alpha i) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcc0 hX) hY) hZ

/-- **P11A-P7d core**: the conclusion of `avg_slow` for an arbitrary `C` with
`P11SecularSpec D C` and fast data satisfying `P11FastSpec` for all `ε ≤ ε₁`. -/
theorem avg_slow_of_spec (hC : P11SecularSpec D C) {nu : ℝ} (hnu : 1 ≤ nu) {eps1 : ℝ}
    (heps1 : 0 < eps1) (Fast : ℝ → P11FastData n)
    (hF : ∀ eps, 0 < eps → eps ≤ eps1 → P11FastSpec C eps (Fast eps)) :
    ∃ eps2 c2 : ℝ, 0 < eps2 ∧ eps2 < 1 ∧ 1 ≤ c2 ∧ ∀ eps, 0 < eps → eps ≤ eps2 →
      ∃ A, P11SlowSpecOf C (Fast eps) nu eps c2 A := by
  obtain ⟨c0, epsO, hc0, hepsO, hO⟩ := p11_slow_osc hC
  have hc : 1 ≤ p11SlowAsmC C nu c0 := hc0.trans (le_max_left _ _)
  obtain ⟨u, hu0, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (p11_slow_eventually hC (c := p11SlowAsmC C nu c0) hnu (by linarith))
  refine ⟨min (min (u / 2) (min epsO eps1)) (1 / 2), p11SlowAsmC C nu c0, ?_, ?_, hc, ?_⟩
  · exact lt_min (lt_min (half_pos hu0) (lt_min hepsO heps1)) (by norm_num)
  · exact (min_le_right _ _).trans_lt (by norm_num)
  · intro eps heps hle
    have h1 : eps ≤ u / 2 := hle.trans ((min_le_left _ _).trans (min_le_left _ _))
    have h2 : eps ≤ epsO := hle.trans ((min_le_left _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
    have h3 : eps ≤ eps1 := hle.trans ((min_le_left _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
    exact p11_slow_at hC hnu hc0 (hF eps heps h3) (hO eps heps h2 _ (hF eps heps h3))
      (hu ⟨heps, by linarith⟩)

end Assembly

end KAM.Planetary

end
