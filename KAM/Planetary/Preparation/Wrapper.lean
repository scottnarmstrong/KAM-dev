/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.WrapperEps
public import KAM.Planetary.Preparation.WrapperAsym
public import KAM.Planetary.Preparation.WrapperSmall

/-!
# The local wrapper for P-FIXED, parametric in `data_star` (P11A-P10, `bpP:p11:wrapper`)

`wrapper_of_data_star D hDS` is the signed `wrapper D` with the signed `data_star D` as hypothesis
(its literal conclusion).  The final theorem `wrapper D := wrapper_of_data_star D (data_star D)` is
added when `data_star` is imported.

Local steps (graph nodes): `wr-nu` is `p11_wr_small`, `p11_ev_thr`, `p11_ev_slowDisp`,
`p11_ev_tube` and the choice of `ν₂` below; `wr-kam` is `p11_wr_qi` with
`weak_kam_quantitative_full`; `wr-chain` is `p11_wr_chain`; `wr-tor` is `p11_wr_torus`; `wr-meas` is
`p11_wr_set`; `wr-tube` is `p11_wr_tube`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace KAM.Planetary

section Wrapper

variable {n : ℕ}

theorem p11SlowConstant_nonneg (D : P11Physical n) {nu : ℝ} (hnu : 1 ≤ nu) :
    0 ≤ p11SlowConstant D nu := by
  unfold p11SlowConstant
  rw [dif_pos hnu]
  have := ((avg_slow D hnu).choose_spec).choose_spec.2.2.1
  linarith

theorem p11_patch_beta_pos (D : P11Physical n) : 0 < (p11PatchData D).beta := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hb, -⟩ := (p11_patch D).choose_spec
  exact hb

/-- `bpP:p11:wrapper` with the conclusion of `data_star` as hypothesis. -/
theorem wrapper_of_data_star {n : ℕ} (D : P11Physical n)
    (hDS : IsCompact (p11PreparedBox n) ∧ volume (p11PreparedBox n)=1 ∧
    Metric.diam (p11PreparedBox n)=1 ∧
    0 < (1/4 : ℝ) ∧ 0 < (1/2 : ℝ) ∧
    max ((n : ℝ)*(p11PatchData D).mu) (2*n) >
      max (((n+n : ℕ) : ℝ)*(p11PatchData D).mu/2-1)
        (((n+n : ℕ) : ℝ)-1) ∧
    ∀ nu : ℝ, 1 ≤ nu →
      ∃ epsA c : ℝ, 0 < epsA ∧ epsA < 1 ∧ 1 ≤ c ∧
      ∀ eps, 0 < eps → eps ≤ epsA →
        let C := p11SecularData D
        let A := p11PatchData D
        let beta := (1/2 : ℝ)*eps^(A.mu+2)*A.beta
        let M := (2 : ℝ)^(A.mu+1)*(2*C.L+1)^2
        0 < beta ∧ beta ≤ min 1 M ∧
        1 ≤ p11M0 n A.mu C.L ∧
        let Q := p11PreparedData D nu eps c
        P11PreparedFullSpec D nu eps c Q ∧
          beta ≤ index_def 2 A.mu (p11PreparedFreqR Q) (p11PreparedBox n)) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ eps, 0 < eps → eps < eps0 →
      ∃ S : Set (Phase (n*2)), MeasurableSet S ∧ 0 < volume S ∧ volume S < ⊤ ∧
        S ⊆ circularTube D.G D.m0 D.m D.a (p11Zeta D) ∧
        ∀ z ∈ S, ∃ w : P11Vec (n*2), ∃ K : P11Vec (n*2) → Phase (n*2),
          ∃ theta0, z=K theta0 ∧ Set.range K ⊆ S ∧
            IsPhysicalTorus (fixedHamiltonian D.G D.m0 D.m eps) w K := by
  obtain ⟨hK, hvol, -, -, -, -, hmain⟩ := hDS
  have hC : P11SecularSpec D (p11SecularData D) := (holo_chart D).choose_spec.1
  obtain ⟨-, hτ0, hL1, -, -, -, -, -, -, -⟩ := fast_consts hC
  set μ := (p11PatchData D).mu with hμ
  set M : ℝ := (2 : ℝ)^(μ+1)*(2*(p11SecularData D).L+1)^2 with hM
  have hM1 : 1 ≤ M := by
    refine one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) ?_
    nlinarith
  have hd0 : (p11WrDatum D (min 1 M)).Valid :=
    p11WrDatum_valid hC hK hvol (lt_min one_pos (by linarith)) (le_refl _)
  obtain ⟨cDelta, hcΔ, hQ⟩ := weak_kam_quantitative_full (n+n) μ (p11WrDatum D (min 1 M)).tau
    (p11WrDatum D (min 1 M)).s (p11WrDatum D (min 1 M)).C1
  obtain ⟨cD, hcD, ⟨cs, hcs, hthr⟩, hfam⟩ := hQ _ hd0 rfl rfl rfl rfl
  set d0 := p11WrDatum D (min 1 M) with hd0def
  set B0 := p11c_B0 d0 with hB0
  set G0 := p11c_G0 d0 with hG0def
  have hG0 : 0 ≤ G0 := by rw [hG0def]; unfold p11c_G0; positivity
  set m : ℝ := ((μ + 2 : ℕ) : ℝ) with hmdef
  have hm0 : 0 ≤ m := by positivity
  set nu : ℝ := max (m*B0 + 2) (2*m*G0 + 4) with hnu
  have hν4 : 2*m*G0 + 4 ≤ nu := le_max_right _ _
  have hν1 : 1 ≤ nu := by
    have : 0 ≤ 2*m*G0 := by positivity
    linarith
  obtain ⟨epsA, c, hepsA0, hepsA1, hc1, hA⟩ := hmain nu hν1
  obtain ⟨eps3, h3, hsmall⟩ := p11_wr_small D hν1
  have hβJ := p11_patch_beta_pos D
  have hτ : 0 ≤ (p11SecularData D).tau := hτ0.le
  have hev := p11_ev_thr (c := c) (q := 2*(p11SecularData D).tau+1) (βJ := (p11PatchData D).beta)
    (cstar := cs) (cD := cD) (B0 := B0) (G0 := G0) (nu := nu) (mu := μ) (by linarith)
    (by linarith) hβJ hcs hcD hG0 (le_max_left _ _) hν4
  have hev2 := p11_ev_slowDisp (p11SlowConstant D nu) (p11SecularData D).tau
    (p11SlowConstant_nonneg D hν1) hτ
  have hev3 := p11_ev_tube hC
  have hev4 := p11_ev_lt (r := min epsA eps3) (lt_min hepsA0 h3)
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 ((hev.and (hev2.and
    (hev3.and hev4))))
  refine ⟨u, hu, fun eps heps hlt => ?_⟩
  obtain ⟨hthr', hdisp', hR', hlt4⟩ := hsub ⟨heps, hlt⟩
  obtain ⟨hthr1, hthr2⟩ := hthr' heps
  obtain ⟨hP1, hP2⟩ := hdisp' heps
  have hleA : eps ≤ epsA := (hlt4.trans_le (min_le_left _ _)).le
  have hle3 : eps ≤ eps3 := (hlt4.trans_le (min_le_right _ _)).le
  obtain ⟨hF, hS, hεM, hpe, hsm256⟩ := hsmall eps heps hle3
  obtain ⟨hR1, hR2⟩ := hR' heps hεM
  obtain ⟨hb0, hbM, -, hFS, hidx⟩ := hA eps heps hleA
  have hQI := p11_wr_qi hFS hidx
  have hbmem : (1/2 : ℝ)*eps^(μ+2)*(p11PatchData D).beta ∈ Ioc 0 (min 1 d0.M) := ⟨hb0, hbM⟩
  have hPb : p11Bound (KAM.complexStrip (n+n) ((p11SecularData D).sigma/72) ×ˢ
      KAM.actionNbhd (p11PreparedBox n) 1) (p11PreparedData D nu eps c).P
      (c*eps^(nu+3/2)*Real.log (1/eps)^(2*(p11SecularData D).tau+1)) := by
    obtain ⟨-, -, -, -, -, -, -, hPb, -⟩ := hFS.1
    exact hPb
  have hsup : ∀ z ∈ KAM.complexStrip (n+n) d0.s ×ˢ KAM.actionNbhd d0.K (2*d0.vartheta),
      ‖(p11PreparedData D nu eps c).P z‖ ≤
        c*eps^(nu+3/2)*Real.log (1/eps)^(2*(p11SecularData D).tau+1) := fun z hz =>
    hPb z ⟨hz.1, p11_actionNbhd_mono _ (by norm_num : (2*(1/4) : ℝ) ≤ 1) hz.2⟩
  have hℓ : 1 ≤ Real.log (1/eps) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hMF⟩ := fast_consts hC
    exact log_inv_ge_one heps (le_trans (by nlinarith) hεM)
  have hεf0 : 0 ≤ c*eps^(nu+3/2)*Real.log (1/eps)^(2*(p11SecularData D).tau+1) := by
    have : 0 ≤ Real.log (1/eps)^(2*(p11SecularData D).tau+1) :=
      Real.rpow_nonneg (by linarith) _
    positivity
  obtain ⟨Q', -, -, hdispQ⟩ := hfam _ hbmem _ _ hQI _ hεf0 (hthr1.trans (hthr _ hbmem)) hsup
  have hdβ : (p11WrDatum D ((1/2 : ℝ)*eps^(μ+2)*(p11PatchData D).beta)).Valid :=
    p11WrDatum_valid hC hK hvol hb0 hbM
  have hγ : 0 < (p11WrDatum D ((1/2 : ℝ)*eps^(μ+2)*(p11PatchData D).beta)).gamma :=
    (qt_order _ hdβ).1
  have hgood : 0 < volume Q'.good := by
    have hm : volume (p11PreparedBox n) ≤ volume Q'.good + ENNReal.ofReal (1/2) := Q'.measure
    rw [hvol] at hm
    by_contra hz
    have : volume Q'.good = 0 := by simpa using hz
    rw [this, zero_add] at hm
    have : (1 : ENNReal) ≤ ENNReal.ofReal (1/2) := hm
    have h2 : ENNReal.ofReal (1/2) < 1 := ENNReal.ofReal_lt_one.2 (by norm_num)
    exact absurd this (not_le.2 h2)
  have hdisp : ∀ b ∈ Q'.good, ∀ θ, ‖Q'.torus b θ - (θ, b)‖ ≤ 1/2 := fun b hb θ =>
    ((hdispQ b hb θ).trans hthr2)
  exact p11_wr_set hC hF hS heps hεM hpe hsm256 hP1 hP2 hR1 hR2 hFS hgood Q'.subset
    Q'.lattice hγ hdβ.2.1 Q'.dio hdisp Q'.borel Q'.cell_lower

end Wrapper

end KAM.Planetary

end
