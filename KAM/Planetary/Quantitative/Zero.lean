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

end Hypotheses

end KAM.Planetary

end
