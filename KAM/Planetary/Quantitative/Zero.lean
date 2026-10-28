/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.Interface
public import KAM.Planetary.WeakMeasure.PowerLaw
public import KAM.Strip.Regularity

/-!
# Quantitative weak KAM: the zero perturbation (P11C-Q5)

`bpP:p11a:zero-case`: for `f = 0` the unperturbed tori `θ ↦ (θ, b)` over the good set
`p11c_zeroGood` (the `2γ`-Diophantine frequencies in `K`) form a `QuantitativeFamily`.
The good set is handled by `power_law` (`stepP:p11a:zc-set`), the tori by direct verification
(`stepP:p11a:zc-tori`).
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology
namespace KAM.Planetary
open KAM KAM.Kepler KAM.ODE

section Smooth

variable {N : ℕ}

theorem p11c_zero_isOpen_nbhd (B : Set (Fin N → ℝ)) (r : ℝ) : IsOpen (actionNbhd B r) := by
  have e : actionNbhd B r = ⋃ J ∈ B, ball (realInclusion N J) r := by
    ext I
    simp only [actionNbhd, mem_ofPred_eq, mem_iUnion, mem_ball, dist_eq_norm, exists_prop]
    rfl
  rw [e]
  exact isOpen_biUnion fun _ _ => isOpen_ball

theorem p11c_zero_contDiffOn_freq {U : Set (Fin N → ℂ)} (hU : IsOpen U)
    {h : (Fin N → ℂ) → ℂ} (hh : DifferentiableOn ℂ h U) :
    ContDiffOn ℝ ∞ (frequencyMap h) (realInclusion N ⁻¹' U) := by
  have h2 : ContDiffOn ℝ ∞ h U :=
    (contDiffOn_infty_of_differentiableOn hU hh).restrict_scalars ℝ
  have h3 : ContDiffOn ℝ ∞ (fun J => (h (realInclusion N J)).re) (realInclusion N ⁻¹' U) :=
    Complex.reCLM.contDiff.comp_contDiffOn
      (h2.comp (realInclusion N).contDiff.contDiffOn fun _ hx => hx)
  have h4 := h3.fderiv_of_isOpen (hU.preimage (realInclusion N).continuous) (m := ∞)
    (by simp)
  exact contDiffOn_pi.2 fun i => h4.clm_apply contDiffOn_const

theorem p11c_zero_contDiffAt_scalar {W : Set (Fin N → ℝ)} (hW : IsOpen W)
    {w : (Fin N → ℝ) → Fin N → ℝ} (hw : ContDiffOn ℝ ∞ w W) (rho : ℕ) (c : Fin N → ℝ)
    {y : Fin N → ℝ} (hy : y ∈ W) : ContDiffAt ℝ ∞ (p11c_scalar rho w c) y := by
  have hw' : ContDiffAt ℝ ∞ w y := hw.contDiffAt (hW.mem_nhds hy)
  have : ContDiffAt ℝ ∞ (fun x => ∑ i, c i * w x i) y :=
    ContDiffAt.sum fun i _ => contDiffAt_const.mul
      ((contDiffAt_pi.1 hw') i)
  exact this.pow rho

theorem p11c_zero_euclid_iter {g : P11Vec N → ℝ} {y : P11Vec N} (hg : ContDiffAt ℝ ∞ g y)
    (j : ℕ) (a : Fin j → P11Vec N) :
    p11euclid (iteratedFDeriv ℝ j (fun x (_ : Fin 1) => g x) y a) =
      |iteratedFDeriv ℝ j g y a| := by
  let L : ℝ →L[ℝ] (Fin 1 → ℝ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ
  have e : (fun x (_ : Fin 1) => g x) = L ∘ g := by
    ext x i; simp [L]
  rw [e, L.iteratedFDeriv_comp_left hg (by exact_mod_cast le_top)]
  simp [L, p11euclid, KAM.Nekhoroshev.euclid, Real.sqrt_sq_eq_abs]

end Smooth

section Hypotheses

variable {N : ℕ}

theorem p11c_zero_diam_pos (d : QuantitativeData N) (hd : d.NumericalValid) :
    0 < d.diameter := by
  obtain ⟨hN, -, -, -, -, -, -, -, -, -, -, -, -, hK, -, hvol⟩ := hd
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  refine Metric.diam_pos ?_ hK.isBounded
  by_contra hns
  have hs : d.K.Subsingleton := Set.not_nontrivial_iff.1 hns
  have h0 := hs.measure_zero volume
  rw [h0] at hvol
  exact ENNReal.not_lt_zero hvol

theorem p11c_zero_patch (d : QuantitativeData N) (hd : d.NumericalValid) :
    ∃ P : P11Patch N, P.K = d.K ∧
      P.V = realInclusion N ⁻¹' actionNbhd d.K (2 * d.vartheta) ∧ P.v = d.vartheta := by
  have hd' := hd
  obtain ⟨hN, -, -, -, -, hv, -, -, -, -, -, -, -, hK, hl, hvol⟩ := hd'
  refine ⟨P11Patch.mk d.K (realInclusion N ⁻¹' actionNbhd d.K (2 * d.vartheta)) d.vartheta hN
    ?_ hK ((p11c_zero_isOpen_nbhd _ _).preimage (realInclusion N).continuous)
    (p11c_zero_diam_pos d hd) hv ?_, rfl, rfl, rfl⟩
  · exact nonempty_of_measure_ne_zero
      ((bot_le.trans_lt hvol).ne')
  · rintro y ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    show ‖realInclusion N y - realInclusion N x‖ < 2 * d.vartheta
    rw [← map_sub, norm_realInclusion]
    exact lt_of_le_of_lt ((KAM.Nekhoroshev.norm_le_euclid _).1.trans hxy) (by linarith)

theorem p11c_zero_dioHyp (d : QuantitativeData N) (hd : d.NumericalValid)
    (h : (Fin N → ℂ) → ℂ) (hh : QuantitativeInput d h 0) {P : P11Patch N} (hK : P.K = d.K)
    (hV : P.V = realInclusion N ⁻¹' actionNbhd d.K (2 * d.vartheta)) (hv : P.v = d.vartheta) :
    P11DioHyp P d.rho d.mu (frequencyMap h) (fun _ => frequencyMap h) d.beta d.M := by
  have hd' := hd
  obtain ⟨hN, hmu, hrho, -, -, hv0, -, -, -, -, -, hb0, hbM, -, -, hvol⟩ := hd'
  obtain ⟨hhol, -, -, -, -, hfin, hsize, -, -⟩ := hh
  have hW : IsOpen (realInclusion N ⁻¹' actionNbhd d.K (2 * d.vartheta)) :=
    (p11c_zero_isOpen_nbhd _ _).preimage (realInclusion N).continuous
  have hw := p11c_zero_contDiffOn_freq (p11c_zero_isOpen_nbhd d.K (2 * d.vartheta)) hhol
  have hthick : p11thick P.K P.v ⊆ realInclusion N ⁻¹' actionNbhd d.K (2 * d.vartheta) := by
    rw [← hV]; exact P.thick_sub
  have hsc : ∀ (rho : ℕ) (c : Fin N → ℝ) (y : Fin N → ℝ),
      y ∈ realInclusion N ⁻¹' actionNbhd d.K (2 * d.vartheta) →
      ContDiffAt ℝ ∞ (p11c_scalar rho (frequencyMap h) c) y :=
    fun rho c y hy => p11c_zero_contDiffAt_scalar hW hw rho c hy
  have hK' : P.K.Nonempty := hK ▸ nonempty_of_measure_ne_zero ((bot_le.trans_lt hvol).ne')
  refine ⟨hN, hmu, hrho, hb0, hbM, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hV]; exact hw.of_le (by exact_mod_cast le_top)
  · intro k _; rw [hV]; exact hw.of_le (by exact_mod_cast le_top)
  · refine le_index_def hN _ _ _ hK' fun c hc y hy => ?_
    obtain ⟨j, hj, a, ha, hle⟩ := hfin c hc y (hK ▸ hy)
    have hy' : y ∈ realInclusion N ⁻¹' actionNbhd d.K (2 * d.vartheta) := by
      refine hthick ⟨y, hy, ?_⟩
      simp [p11euclid_zero, hv0.le, hv]
    refine hle.trans ((le_of_eq ?_).trans ((le_p11dg _ j y a ha).trans
      (le_p11maxJet _ y _ hj)))
    exact (p11c_zero_euclid_iter (hsc d.rho c y hy') j _).symm
  · intro c hc j hj1 hj2 y hy
    have hy' := hthick hy
    refine Real.sSup_le ?_ (hb0.le.trans hbM)
    rintro _ ⟨a, ha, rfl⟩
    have he := p11c_zero_euclid_iter (hsc d.rho c y hy') j a
    change p11euclid (iteratedFDeriv ℝ j (fun x (_ : Fin 1) => p11c_scalar d.rho (frequencyMap h) c x)
      y a) ≤ d.M
    rw [he]
    exact hsize c hc j hj1 hj2 y (by rw [hK, hv] at hy; exact hy) a ha
  · intro k _ c _ j _ y _
    simp only [sub_self, ite_true]
    refine Real.sSup_le ?_ (by linarith)
    rintro _ ⟨a, _, rfl⟩
    simp [p11euclid_zero]
    linarith

end Hypotheses

section Good

variable {N : ℕ}

def p11c_zeroGood {N : ℕ} (d : QuantitativeData N) (h : (Fin N → ℂ) → ℂ) : Set (Fin N → ℝ) :=
  {b ∈ d.K | IsDiophantine (2 * d.gamma) d.tau (frequencyMap h b)}

theorem p11c_zero_cDio_pos (d : QuantitativeData N) (hd : d.NumericalValid) :
    0 < d.cDio := by
  have hdiam := p11c_zero_diam_pos d hd
  obtain ⟨hN, hmu, hrho, htau, -, hv0, -, -, -, -, -, hb0, hbM, -, -, -⟩ := hd
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hmu' : (0 : ℝ) < d.mu := by exact_mod_cast hmu
  have hr : (0 : ℝ) < d.rho := by rcases hrho with h | h <;> simp [h]
  have hM : 0 < d.M := hb0.trans_le hbM
  have hden : 0 < (d.rho : ℝ) * (d.tau + 1) / d.mu - N := by
    rw [sub_pos, lt_div_iff₀ hmu']
    have h1 : (N : ℝ) * d.mu / d.rho < d.tau + 1 := by linarith
    rw [div_lt_iff₀ hr] at h1
    linarith
  have hlast : 0 < 1 + 1 / ((d.rho : ℝ) * (d.tau + 1) / d.mu - N) := by
    have := one_div_pos.2 hden
    linarith
  unfold QuantitativeData.cDio
  generalize 1 + 1 / ((d.rho : ℝ) * (d.tau + 1) / d.mu - N) = L at hlast ⊢
  positivity

theorem p11c_zero_gamma_pos (d : QuantitativeData N) (hd : d.NumericalValid) :
    0 < d.gamma := by
  have hc := p11c_zero_cDio_pos d hd
  obtain ⟨hN, hmu, hrho, htau, -, hv0, -, -, -, -, -, hb0, hbM, -, hl, -⟩ := hd
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : (0 : ℝ) < d.rho := by rcases hrho with h | h <;> simp [h]
  unfold QuantitativeData.gamma
  refine half_pos (lt_min ?_ ?_)
  · positivity
  · exact Real.rpow_pos_of_pos (div_pos hl hc) _

theorem p11c_zero_two_gamma (d : QuantitativeData N) :
    2 * d.gamma = p11GammaStar N d.rho d.mu d.beta d.cDio d.epsLoss := by
  unfold QuantitativeData.gamma p11GammaStar
  simp only [one_div]
  ring

theorem p11c_zero_cDio_eq (d : QuantitativeData N) :
    p11CDio N N d.rho d.mu (Metric.diam d.K) d.vartheta d.beta d.M d.tau = d.cDio := by
  unfold p11CDio p11Csub QuantitativeData.cDio QuantitativeData.diameter
  simp only [one_div]

theorem p11c_zero_small (d : QuantitativeData N) (hd : d.NumericalValid) :
    (Real.sqrt N * (2 * d.gamma)) ^ d.rho < d.beta / 4 := by
  have hgp := p11c_zero_gamma_pos d hd
  obtain ⟨hN, hmu, hrho, htau, -, hv0, -, -, -, -, -, hb0, hbM, -, hl, -⟩ := hd
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : (0 : ℝ) < d.rho := by rcases hrho with h | h <;> simp [h]
  have hr1 : 1 ≤ d.rho := by rcases hrho with h | h <;> omega
  rw [p11c_zero_two_gamma]
  set A : ℝ := (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) * (d.beta / 4) ^ ((d.rho : ℝ)⁻¹) with hA
  have hbq : 0 < d.beta / 4 := by linarith
  have hle : p11GammaStar N d.rho d.mu d.beta d.cDio d.epsLoss ≤ A := min_le_left _ _
  have hsq : Real.sqrt N * A = (1 / 2) * (d.beta / 4) ^ ((d.rho : ℝ)⁻¹) := by
    have : Real.sqrt N * (N : ℝ) ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN']
      norm_num
    rw [hA]
    calc Real.sqrt N * ((1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) * (d.beta / 4) ^ ((d.rho : ℝ)⁻¹))
        = (Real.sqrt N * (N : ℝ) ^ (-(1 / 2 : ℝ))) * (1 / 2) * (d.beta / 4) ^ ((d.rho : ℝ)⁻¹) := by
          ring
      _ = _ := by rw [this]; ring
  have hg0 : 0 ≤ p11GammaStar N d.rho d.mu d.beta d.cDio d.epsLoss := by
    rw [← p11c_zero_two_gamma]; linarith
  calc (Real.sqrt N * p11GammaStar N d.rho d.mu d.beta d.cDio d.epsLoss) ^ d.rho
      ≤ (Real.sqrt N * A) ^ d.rho :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)) _
    _ = (1 / 2) ^ d.rho * d.beta / 4 := by
        rw [hsq, mul_pow, ← Real.rpow_natCast ((d.beta / 4) ^ ((d.rho : ℝ)⁻¹)), ← Real.rpow_mul hbq.le,
          inv_mul_cancel₀ hr.ne', Real.rpow_one]
        ring
    _ < d.beta / 4 := by
        have : (1 / 2 : ℝ) ^ d.rho < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
        nlinarith

end Good

end KAM.Planetary

end
