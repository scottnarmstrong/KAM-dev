/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.WrapperTube

/-!
# `stepP:p11:wr-tube` (P11A-P10)

Real points of `Ξ_ε` with actions in `[-1,1]` lie in the circular tube of radius `ζ_*`.
-/

@[expose] public noncomputable section
open Set
namespace KAM.Planetary

section TubeMain

variable {n : ℕ}

theorem p11_sq_aux {a u d : ℝ} (h : |a - u| ≤ d) : a ^ 2 ≤ 2*u ^ 2 + 2*d ^ 2 := by
  have h1 : (a - u) ^ 2 ≤ d ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith [sq_nonneg (a - 2*u)]

theorem p11_tube_sq {a b a' b' u1 u2 ε d : ℝ} (hu : u1 ^ 2 + u2 ^ 2 ≤ 3*ε)
    (h1 : |a - u1| ≤ d) (h2 : |b - u2| ≤ d) (ha : a = a') (hb : b = b') :
    a' ^ 2 + b' ^ 2 ≤ 6*ε + 4*d^2 := by
  subst ha hb
  have := p11_sq_aux h1
  have := p11_sq_aux h2
  linarith

theorem p11_tube_lambda {vJ uJ wJ yJ J0 zc ε dJ δ Lam : ℝ} (hz : |zc| ≤ 1) (hε : 0 ≤ ε)
    (h1 : |vJ - uJ| ≤ dJ) (h2 : uJ = wJ) (h3 : |wJ - (J0 + ε*zc)| ≤ ε) (h4 : yJ = J0 + ε*zc)
    (hR : 2*ε + dJ ≤ 7*Real.pi*δ/4) (hn : |J0/(2*Real.pi) - Lam| < δ/8) (hδ : 0 ≤ δ) :
    |vJ/(2*Real.pi) - Lam| ≤ δ := by
  subst h2 h4
  have hz' := abs_le.1 hz
  have hε' : |ε*zc| ≤ ε := by rw [abs_mul, abs_of_nonneg hε]; nlinarith [abs_nonneg zc]
  have he : |vJ - J0| ≤ 7*Real.pi*δ/4 := by
    calc |vJ - J0| = |(vJ - uJ) + (uJ - (J0 + ε*zc)) + ε*zc| := by ring_nf
      _ ≤ |vJ - uJ| + |uJ - (J0 + ε*zc)| + |ε*zc| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
      _ ≤ _ := by linarith
  have e : vJ/(2*Real.pi) - Lam = (J0/(2*Real.pi) - Lam) + (vJ - J0)/(2*Real.pi) := by ring
  rw [e]
  have : |(vJ - J0)/(2*Real.pi)| ≤ 7*δ/8 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi), div_le_iff₀ (by positivity)]
    nlinarith
  exact (abs_add_le _ _).trans (by linarith)

theorem p11_delta_nonneg (D : P11Physical n) : 0 ≤ p11PhysicalDelta D :=
  (forward_tube D (p11_zeta_pos D)).choose_spec.1.le

/-- `stepP:p11:wr-tube`: for small `ε`, the real points of `Ξ_ε` with actions in `[-1,1]` lie in the
circular tube of radius `ζ_*`. The smallness hypotheses are discharged in `wr-nu`. -/
theorem p11_wr_tube {D : P11Physical n} {nu eps : ℝ}
    (hC : P11SecularSpec D (p11SecularData D))
    (hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps))
    (hS : P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps))
    (heps : 0 < eps) (hεM : eps*(p11SecularData D).MF ≤ Real.exp (-1))
    (hpe : Real.pi*eps ≤ p11s2 (p11SecularData D) nu eps)
    (hsm : 256*eps < (p11SecularData D).rz^2)
    (hP1 : p11SlowConstant D nu*eps^(3/2 : ℝ)*Real.log (1/eps)^(3*(p11SecularData D).tau+1) ≤ eps)
    (hP2 : p11SlowConstant D nu*eps^(5/2 : ℝ)*Real.log (1/eps)^(3*(p11SecularData D).tau+1) ≤ eps)
    (hR1 : 2*eps + 3*eps*(p11SecularData D).MF/(2*Real.pi*p11Alpha1 (p11SecularData D) eps*
      (p11SecularData D).sigma) ≤ 7*Real.pi*p11PhysicalDelta D/4)
    (hR2 : 3*n*eps + 2*n*(9*eps*(p11SecularData D).MF/(2*Real.pi*
      p11Alpha1 (p11SecularData D) eps*(p11SecularData D).rz))^2 ≤ p11PhysicalDelta D)
    {z : Phase (n+n)} (hz : z ∈ p11WrO D) (hI : ∀ j, |z.2 j| ≤ 1) :
    p11WrChain D nu eps z ∈ circularTube D.G D.m0 D.m D.a (p11Zeta D) := by
  obtain ⟨hy, hw, hu, hv, -⟩ := p11_wr_dom hC hF hS heps hpe hsm hz
  obtain ⟨hγ0, -, -, hrC0, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  have hα : 0 < p11Alpha1 (p11SecularData D) eps := by
    have hK := p11K1_ge_one hC heps hεM
    unfold p11Alpha1
    have : 0 < p11K1 (p11SecularData D) eps ^ (-(p11SecularData D).tau) :=
      Real.rpow_pos_of_pos (by linarith) _
    positivity
  obtain ⟨hbn, hbc⟩ := p11_wr_psi_disp hS hy
  obtain ⟨hdJ, hdx, hdy⟩ := p11_wr_fast_disp hF hα hσ0 hrz0 hu
  set C := p11SecularData D with hCd
  set y := p11RescaleReal C.J0 eps z with hy_def
  set w := p11WrPsiR D nu eps y with hw_def
  set u := p11PolarR w with hu_def
  set v := p11WrFastR D eps u with hv_def
  have hy2n : ∀ i : Fin n, y.2 (Fin.natAdd n i) = eps*(2*Real.pi + z.2 (Fin.natAdd n i)) :=
    fun i => by simp [hy_def, p11RescaleReal]
  have hy2c : ∀ i : Fin n, y.2 (Fin.castAdd n i) = C.J0 i + eps*z.2 (Fin.castAdd n i) :=
    fun i => by simp [hy_def, p11RescaleReal]
  have hsq : ∀ i : Fin n, u.1 (Fin.natAdd n i) ^ 2 + u.2 (Fin.natAdd n i) ^ 2 ≤ 3*eps := fun i => by
    rw [hu_def, p11PolarR_sq hw i, div_le_iff₀ Real.pi_pos]
    have h1 := (abs_le.1 ((hbn i).trans hP1)).2
    rw [hy2n i] at h1
    have := (abs_le.1 (hI (Fin.natAdd n i))).2
    have hpi := Real.pi_gt_three
    nlinarith
  have hvsq : ∀ i : Fin n, v.1 (Fin.natAdd n i) ^ 2 + v.2 (Fin.natAdd n i) ^ 2 ≤
      6*eps + 4*(9*eps*C.MF/(2*Real.pi*p11Alpha1 C eps*C.rz))^2 := fun i =>
    p11_tube_sq (hsq i) (hdx i) (hdy i) rfl rfl
  have hvn : ‖(fun i : Fin n => v.2 (Fin.castAdd n i)) - C.J0‖ < 2*C.rC := by
    have h := hv.2.1
    have e : (fun i : Fin n => (KAM.realInclusion₂ (n+n) v).2 (Fin.castAdd n i)) -
      KAM.realInclusion n C.J0 = KAM.realInclusion n ((fun i : Fin n => v.2 (Fin.castAdd n i)) -
        C.J0) := by funext i; simp
    rw [e, KAM.norm_realInclusion] at h
    exact h
  have hΓ : ∀ i, poincareGamma (planetBlock (p11ChartInput C v) i) ≤
      p11PhysicalDelta D := fun i => by
    refine (p11_chartInput_gamma hC hvn i).trans ?_
    have hs : ∑ j : Fin n, (v.1 (Fin.natAdd n j) ^ 2 + v.2 (Fin.natAdd n j) ^ 2) ≤
        n * (6*eps + 4*(9*eps*C.MF/(2*Real.pi*p11Alpha1 C eps*C.rz))^2) := by
      refine (Finset.sum_le_sum fun j _ => hvsq j).trans (le_of_eq ?_)
      simp
      ring
    linarith
  have hC' := hC
  obtain ⟨-, -, -, -, -, -, -, hJ0, -⟩ := hC'
  have hJ0K : C.J0 ∈ (p11PatchData D).K := interior_subset hJ0
  have hΛ : ∀ i : Fin n, |(p11ChartInput C v).2 (Fin.castAdd n i) -
      D.m i * Real.sqrt (D.G*D.m0*D.a i)| ≤ p11PhysicalDelta D := fun i => by
    have hform : (p11ChartInput C v).2 (Fin.castAdd n i) = v.2 (Fin.castAdd n i)/(2*Real.pi) := by
      simp [p11ChartInput, assemble, fast]
    rw [hform]
    have h3 := (hbc i).trans hP2
    rw [hy2c i] at h3
    exact p11_tube_lambda (hI _) heps.le (hdJ i) (p11PolarR_cast hw i) h3 (hy2c i) hR1
      (p11_patch_near D hJ0K i) (p11_delta_nonneg D)
  have hδ := (forward_tube D (p11_zeta_pos D)).choose_spec
  obtain ⟨-, hlt⟩ := hδ.2.2 _ hΛ hΓ
  obtain ⟨-, -, hin, -⟩ := hC.chart_part
  refine ⟨fun i => (p11ChartInput C v).1 (Fin.castAdd n i)/(2*Real.pi), ?_⟩
  show ‖C.chart v - _‖ < _
  rw [(hin v hv).2.1]
  exact hlt

end TubeMain

end KAM.Planetary

end
