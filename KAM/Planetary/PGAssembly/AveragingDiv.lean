/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.AveragingBound
public import KAM.Planetary.PGAssembly.FastComplex

/-!
# P Part 5: the divisor bound of the averaging adapter (`stepP:p5:av-R1`)

At a core point the frozen Diophantine hypothesis gives the divisor `gammaBar/|k|₁^τ`; throughout
the complex `rhoBar`-neighbourhood this loses at most half, because `‖∂²H̃₀‖ ≤ M0` and
`rhoBar = gammaBar/(2 M0 Kbar^(τ+1))`; dividing `H̃₀` by `2π` gives `pgOscAlpha`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-AV (F7).
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b n : ℕ} {d : PGData a b} {r mu : ℝ}

theorem pgAnalytic_dfast (d : PGData a b) :
    ∀ z ∈ KAM.actionNbhd (closure d.V) (2*(pgAnalytic d).rho),
      ‖fderiv ℂ (complexFast d) z‖ ≤ (pgAnalytic d).M0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    pgAnalytic_spec d
  exact h

theorem modeSize_ge_one {k : Fin n → ℤ} (hk : k ≠ 0) : 1 ≤ KAM.Fourier.modeSize k := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h; push Not at h; exact hk (funext h)
  have h1 : (1:ℝ) ≤ |(k i : ℝ)| := by
    have : (1:ℤ) ≤ |k i| := Int.one_le_abs hi
    exact_mod_cast this
  exact h1.trans (KAM.Fourier.abs_coord_le_modeSize k i)

theorem norm_dotC_le (k : Fin n → ℤ) (v : Fin n → ℂ) :
    ‖KAM.NormalForm.dotC k v‖ ≤ KAM.Fourier.modeSize k * ‖v‖ := by
  unfold KAM.NormalForm.dotC KAM.Fourier.modeSize
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul]
  have : ‖(k i : ℂ)‖ = |(k i : ℝ)| := by simp
  rw [this]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (abs_nonneg _)

theorem dotC_sub (k : Fin n → ℤ) (v w : Fin n → ℂ) :
    KAM.NormalForm.dotC k v - KAM.NormalForm.dotC k w = KAM.NormalForm.dotC k (v - w) := by
  simp [KAM.NormalForm.dotC, mul_sub, Finset.sum_sub_distrib]

theorem freq_pgOscH {I : Fin a → ℂ}
    (hI : I ∈ KAM.actionNbhd (closure d.V) (pgExtension d).delta) :
    KAM.NormalForm.freq (pgOscH d) I = fun i => complexFast d I i / (2*Real.pi:ℂ) := by
  have hdiff : DifferentiableAt ℂ (pgExtension d).H0 I :=
    (pgExtension d).h0holo.differentiableAt ((isOpen_actionNbhd _ _).mem_nhds hI)
  funext i
  have : pgOscH d = (1/(2*(Real.pi:ℂ))) • (pgExtension d).H0 := by
    funext J; simp [pgOscH, div_eq_inv_mul]
  have h2 := (hdiff.hasFDerivAt.const_smul (1/(2*(Real.pi:ℂ)))).fderiv
  rw [KAM.NormalForm.freq, this, h2]
  simp [complexFast, div_eq_inv_mul]

/-- The divisor bound at the real points of the core. -/
theorem core_divisor {J : Fin a → ℝ} (hJ : J ∈ checkedCore d r mu) (hr : 0 < r)
    {k : Fin a → ℤ} (hk : k ≠ 0) :
    (params d r mu).gammaBar / (KAM.Fourier.modeSize k) ^ pgTau a b ≤
      ‖KAM.NormalForm.dotC k (complexFast d (KAM.realInclusion a J))‖ := by
  have hJV : J ∈ d.V := hJ.1.1
  have hmem : KAM.realInclusion a J ∈ KAM.actionNbhd (closure d.V) (pgExtension d).delta :=
    mem_actionNbhd_real (pgExtension d).delta_pos (subset_closure hJV)
  obtain ⟨-, hreal⟩ := real_relation d hmem
  have hdio := hJ.2 k hk
  rw [hreal]
  have : KAM.NormalForm.dotC k (KAM.realInclusion a (fastFrequency d.H0 J)) =
      ((∑ i, (k i : ℝ) * fastFrequency d.H0 J i : ℝ) : ℂ) := by
    simp [KAM.NormalForm.dotC]
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact hdio

theorem dotC_div_const (k : Fin n → ℤ) (v : Fin n → ℂ) (c : ℂ) :
    KAM.NormalForm.dotC k (fun i => v i / c) = KAM.NormalForm.dotC k v / c := by
  simp [KAM.NormalForm.dotC, mul_div_assoc, Finset.sum_div]

theorem pgOsc_K_eq (d : PGData a b) (r : ℝ) :
    15/(Real.pi*pgOscWidth d)*Real.log (1/r) = 30/pgWidth d*Real.log (1/r) := by
  unfold pgOscWidth
  have := Real.pi_pos
  have := pgWidth_pos d
  congr 1
  field_simp
  ring

theorem pg_osc_divisor (h : admissible d (pgRstar d) r mu) :
    KAM.NormalForm.DivisorBound (KAM.actionNbhd (checkedCore d r mu) (params d r mu).rhoBar)
      (15/(Real.pi*pgOscWidth d)*Real.log (1/r)) {0} (pgOscH d) (pgOscAlpha d r mu) := by
  rw [pgOsc_K_eq, ← params_Kbar]
  intro I hI k hk
  obtain ⟨hkK, hk0⟩ := hk
  have hk0' : k ≠ 0 := fun h0 => hk0 (by simp [h0])
  have hkK' : KAM.Fourier.modeSize k ≤ (params d r mu).Kbar := hkK
  have hK1 := av_Kbar_ge_one h
  have hγ0 := av_gamma_pos h
  have hM0 := pgAnalytic_M0_ge_one d
  have hτ := pgTau_pos a b
  have hm1 := modeSize_ge_one hk0'
  have hρδ := av_rhoBar_lt_delta h
  have hρρ := av_rhoBar_le_rho h
  have hρ0 := av_rhoBar_pos h
  have hρ' := pgAnalytic_rho_lt d
  have hδ0 := (pgExtension d).delta_pos
  have hrho0 := pgAnalytic_rho_pos d
  have hI' : I ∈ KAM.actionNbhd (closure d.V) (pgExtension d).delta :=
    actionNbhd_checkedCore_le h (by linarith) hI
  set K := (params d r mu).Kbar with hK
  set γ := (params d r mu).gammaBar with hγ
  set ρ := (params d r mu).rhoBar with hρ
  obtain ⟨J, hJ, hIJ⟩ := hI
  have hJmem : KAM.realInclusion a J ∈ KAM.actionNbhd (closure d.V) (pgExtension d).delta :=
    mem_actionNbhd_real hδ0 (subset_closure (checkedCore_subset_V d r mu hJ))
  -- mean value estimate for the complex fast frequency
  have hball : ∀ y ∈ ball (KAM.realInclusion a J) ρ,
      y ∈ KAM.actionNbhd (closure d.V) (2*(pgAnalytic d).rho) := fun y hy =>
    ⟨J, subset_closure (checkedCore_subset_V d r mu hJ), by
      rw [mem_ball, dist_eq_norm] at hy
      have hy' : ‖y - fun i => ((J i : ℝ) : ℂ)‖ < ρ := hy
      linarith⟩
  have hdiff : ∀ y ∈ ball (KAM.realInclusion a J) ρ, DifferentiableAt ℂ (complexFast d) y :=
    fun y hy => (differentiableOn_complexFast d).differentiableAt
      ((isOpen_actionNbhd _ _).mem_nhds (mem_actionNbhd_mono (by linarith) (hball y hy)))
  have hmv := (convex_ball (KAM.realInclusion a J) ρ).norm_image_sub_le_of_norm_fderiv_le hdiff
    (fun y hy => pgAnalytic_dfast d y (hball y hy)) (mem_ball_self hρ0)
    (show I ∈ ball (KAM.realInclusion a J) ρ by rw [mem_ball, dist_eq_norm]; exact hIJ)
  have h2 : ‖complexFast d I - complexFast d (KAM.realInclusion a J)‖ ≤ (pgAnalytic d).M0 * ρ :=
    hmv.trans (mul_le_mul_of_nonneg_left hIJ.le (by linarith))
  have hdiv := core_divisor hJ h.1 hk0'
  have hdot : ‖KAM.NormalForm.dotC k (complexFast d I)‖ ≥
      ‖KAM.NormalForm.dotC k (complexFast d (KAM.realInclusion a J))‖ -
        KAM.Fourier.modeSize k * ((pgAnalytic d).M0 * ρ) := by
    have h1 := norm_dotC_le k (complexFast d (KAM.realInclusion a J) - complexFast d I)
    have h2' : ‖complexFast d (KAM.realInclusion a J) - complexFast d I‖ ≤ (pgAnalytic d).M0 * ρ := by
      rw [norm_sub_rev]; exact h2
    have h3 := mul_le_mul_of_nonneg_left h2' (by linarith : 0 ≤ KAM.Fourier.modeSize k)
    have h4 := norm_sub_norm_le (KAM.NormalForm.dotC k (complexFast d (KAM.realInclusion a J)))
      (KAM.NormalForm.dotC k (complexFast d I))
    rw [dotC_sub] at h4
    linarith
  have hKτ : 0 < K^(pgTau a b) := Real.rpow_pos_of_pos (by linarith) _
  have hmτ : 0 < (KAM.Fourier.modeSize k)^(pgTau a b) := Real.rpow_pos_of_pos (by linarith) _
  have hKM : K*((pgAnalytic d).M0*ρ) = γ/(2*K^(pgTau a b)) := by
    rw [hρ, params_rhoBar, ← hK, ← hγ, Real.rpow_add_one (by linarith)]
    field_simp
  have hmτK : (KAM.Fourier.modeSize k)^(pgTau a b) ≤ K^(pgTau a b) :=
    Real.rpow_le_rpow (by linarith) hkK' hτ.le
  have h5 : γ/K^(pgTau a b) ≤ γ/(KAM.Fourier.modeSize k)^(pgTau a b) :=
    div_le_div_of_nonneg_left hγ0.le hmτ hmτK
  have h6 : KAM.Fourier.modeSize k * ((pgAnalytic d).M0 * ρ) ≤ K*((pgAnalytic d).M0 * ρ) :=
    mul_le_mul_of_nonneg_right hkK' (by positivity)
  have hD : γ/(2*K^(pgTau a b)) ≤ ‖KAM.NormalForm.dotC k (complexFast d I)‖ := by
    have : γ/(2*K^(pgTau a b)) = γ/K^(pgTau a b) - γ/(2*K^(pgTau a b)) := by
      field_simp; norm_num
    linarith
  rw [freq_pgOscH hI', dotC_div_const, norm_div]
  have h2pi : ‖(2*Real.pi:ℂ)‖ = 2*Real.pi := by
    have := Real.pi_pos
    simpa [abs_of_pos this] using (Complex.norm_real (2*Real.pi))
  rw [h2pi]
  have hpi := Real.pi_pos
  unfold pgOscAlpha
  rw [← hγ, ← hK, le_div_iff₀ (by positivity)]
  calc γ / (4 * Real.pi * K ^ pgTau a b) * (2 * Real.pi) = γ/(2*K^(pgTau a b)) := by
        field_simp; ring
    _ ≤ _ := hD

end KAM.Planetary

end
