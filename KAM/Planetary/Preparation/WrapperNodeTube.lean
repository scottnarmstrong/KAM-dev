/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.WrapperAsym
public import KAM.Planetary.Preparation.WrapperTubeMain

/-!
# Literal export of `stepP:p11:wr-tube` (GAP-WR)

The source asserts, for real points with actions in `[-1,1]` and `ε` small, that
`∑ (ξ_i² + η_i²) ≤ 4 n ε`, `Γ_i ≤ 2 n ε`, and that `Ξ_ε` lies in the circular tube. The earlier
export `p11_wr_tube` proves the coarser `Γ_i ≤ 3 n ε + 2 n d²`. Here the fast-map displacement `d`
is absorbed into the constant (`28 d² ≤ ε`, which holds eventually since `d = O(ε ℓ^τ)`), giving
the literal constants.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace KAM.Planetary

section TubeNode

variable {n : ℕ}

theorem p11_tube_sq4 {a b a' b' u1 u2 ε d : ℝ} (hu : u1 ^ 2 + u2 ^ 2 ≤ 3*ε)
    (h1 : |a - u1| ≤ d) (h2 : |b - u2| ≤ d) (ha : a = a') (hb : b = b') (hd : 28*d^2 ≤ ε) :
    a' ^ 2 + b' ^ 2 ≤ 4*ε := by
  subst ha hb
  have e1 : (a - u1) ^ 2 ≤ d ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e2 : (b - u2) ^ 2 ≤ d ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  nlinarith [sq_nonneg (u1 - 6*(a - u1)), sq_nonneg (u2 - 6*(b - u2))]

/-- `stepP:p11:wr-tube` with the literal constants of the source: for every real point with
actions in `[-1,1]`, the oscillator point `(x, y)` after the fast map satisfies
`∑ (x_j² + y_j²) ≤ 4 n ε`, every `Γ_i ≤ 2 n ε`, and `Ξ_ε` lies in the circular tube. The smallness
hypotheses are eventual in `ε` (`p11_ev_tube_node`, `p11_ev_tube`, `p11_ev_slowDisp`). -/
theorem p11_wr_tube_node {D : P11Physical n} {nu eps : ℝ}
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
    (hd : 28*(9*eps*(p11SecularData D).MF/(2*Real.pi*
      p11Alpha1 (p11SecularData D) eps*(p11SecularData D).rz))^2 ≤ eps)
    (hΓε : 2*n*eps ≤ p11PhysicalDelta D)
    {z : Phase (n+n)} (hI : ∀ j, |z.2 j| ≤ 1) :
    ∑ j : Fin n, ((p11WrFastR D eps (p11PolarR (p11WrPsiR D nu eps
        (p11RescaleReal (p11SecularData D).J0 eps z)))).1 (Fin.natAdd n j) ^ 2 +
      (p11WrFastR D eps (p11PolarR (p11WrPsiR D nu eps
        (p11RescaleReal (p11SecularData D).J0 eps z)))).2 (Fin.natAdd n j) ^ 2) ≤ 4*n*eps ∧
    (∀ i, poincareGamma (planetBlock (p11ChartInput (p11SecularData D)
      (p11WrFastR D eps (p11PolarR (p11WrPsiR D nu eps
        (p11RescaleReal (p11SecularData D).J0 eps z))))) i) ≤ 2*n*eps) ∧
    p11WrChain D nu eps z ∈ circularTube D.G D.m0 D.m D.a (p11Zeta D) := by
  have hz : z ∈ p11WrO D := by
    obtain ⟨-, -, -, -, -, hσ0, -, -, -, -⟩ := fast_consts hC
    refine ⟨fun i => by simpa using (by positivity : 0 < (p11SecularData D).sigma/72),
      fun j => z.2 j/2, fun j _ => ?_, ?_⟩
    · have := abs_le.1 (hI j)
      exact ⟨by linarith, by linarith⟩
    · refine (pi_norm_lt_iff one_pos).2 fun j => ?_
      show ‖(KAM.realInclusion₂ (n+n) z).2 j - ((z.2 j/2 : ℝ) : ℂ)‖ < 1
      have : (KAM.realInclusion₂ (n+n) z).2 j - ((z.2 j/2 : ℝ) : ℂ) = ((z.2 j/2 : ℝ) : ℂ) := by
        simp; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
      have := hI j
      linarith
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
  have hvsq : ∀ i : Fin n, v.1 (Fin.natAdd n i) ^ 2 + v.2 (Fin.natAdd n i) ^ 2 ≤ 4*eps :=
    fun i => p11_tube_sq4 (hsq i) (hdx i) (hdy i) rfl rfl hd
  have hvn : ‖(fun i : Fin n => v.2 (Fin.castAdd n i)) - C.J0‖ < 2*C.rC := by
    have h := hv.2.1
    have e : (fun i : Fin n => (KAM.realInclusion₂ (n+n) v).2 (Fin.castAdd n i)) -
      KAM.realInclusion n C.J0 = KAM.realInclusion n ((fun i : Fin n => v.2 (Fin.castAdd n i)) -
        C.J0) := by funext i; simp
    rw [e, KAM.norm_realInclusion] at h
    exact h
  have hsum : ∑ j : Fin n, (v.1 (Fin.natAdd n j) ^ 2 + v.2 (Fin.natAdd n j) ^ 2) ≤ 4*n*eps := by
    refine (Finset.sum_le_sum fun j _ => hvsq j).trans (le_of_eq ?_)
    simp
    ring
  have hΓ : ∀ i, poincareGamma (planetBlock (p11ChartInput C v) i) ≤ 2*n*eps := fun i => by
    refine (p11_chartInput_gamma hC hvn i).trans ?_
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
  obtain ⟨-, hlt⟩ := hδ.2.2 _ hΛ (fun i => (hΓ i).trans hΓε)
  obtain ⟨-, -, hin, -⟩ := hC.chart_part
  refine ⟨hsum, hΓ, fun i => (p11ChartInput C v).1 (Fin.castAdd n i)/(2*Real.pi), ?_⟩
  show ‖C.chart v - _‖ < _
  rw [(hin v hv).2.1]
  exact hlt


/-- The two new smallness conditions of `p11_wr_tube_node` hold for small `ε`. -/
theorem p11_ev_tube_node {D : P11Physical n} (hC : P11SecularSpec D (p11SecularData D)) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), 0 < eps →
      eps*(p11SecularData D).MF ≤ Real.exp (-1) →
      28*(9*eps*(p11SecularData D).MF/(2*Real.pi*p11Alpha1 (p11SecularData D) eps*
        (p11SecularData D).rz))^2 ≤ eps ∧ 2*n*eps ≤ p11PhysicalDelta D := by
  set C := p11SecularData D with hCd
  obtain ⟨hγ0, hτ0, -, -, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  have hδ0 : 0 < p11PhysicalDelta D := (forward_tube D (p11_zeta_pos D)).choose_spec.1
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast D.n_ge
  have hn0 : (0 : ℝ) < n := by linarith
  have hpi := Real.pi_gt_three
  set c3 := 6/(Real.pi*C.sigma) with hc3
  have hc30 : 0 < c3 := by positivity
  set Xz := 9*C.MF*c3^C.tau/(Real.pi*C.rz*C.gamma) with hXz
  have hXz0 : 0 < Xz := by positivity
  have hη0 : 0 < 1/(6*Xz) := by positivity
  filter_upwards [p11_ev_pow_log (a := 1/2) (b := C.tau) (δ := 1/(6*Xz)) (by norm_num) hτ0.le hη0,
    p11_ev_lt (r := p11PhysicalDelta D/(2*n)) (by positivity)] with eps hB hε1 heps hεM
  have hia := p11_inv_alpha_le hC heps hεM
  have hd2 : 9*eps*C.MF/(2*Real.pi*p11Alpha1 C eps*C.rz) ≤ Xz*(eps*Real.log (1/eps)^C.tau) := by
    have e : 9*eps*C.MF/(2*Real.pi*p11Alpha1 C eps*C.rz) =
        9*C.MF*eps/(2*Real.pi*C.rz) * (p11Alpha1 C eps)⁻¹ := by field_simp
    rw [e]
    calc _ ≤ 9*C.MF*eps/(2*Real.pi*C.rz) * (2/C.gamma*(c3^C.tau*Real.log (1/eps)^C.tau)) :=
          mul_le_mul_of_nonneg_left hia (by positivity)
      _ = _ := by rw [hXz]; field_simp
  set d := 9*eps*C.MF/(2*Real.pi*p11Alpha1 C eps*C.rz) with hd
  have hd0 : 0 ≤ d := by
    have hα : 0 < p11Alpha1 C eps := by
      have hK := p11K1_ge_one hC heps hεM
      unfold p11Alpha1
      have : 0 < p11K1 C eps ^ (-C.tau) := Real.rpow_pos_of_pos (by linarith) _
      positivity
    positivity
  have hs : eps^(1/2 : ℝ) * eps^(1/2 : ℝ) = eps := by
    rw [← Real.rpow_add heps]; norm_num
  have hs0 : 0 < eps^(1/2 : ℝ) := Real.rpow_pos_of_pos heps _
  have hdd : d ≤ eps^(1/2 : ℝ)/6 := by
    refine hd2.trans ?_
    have : Xz*(eps*Real.log (1/eps)^C.tau) =
        Xz*eps^(1/2 : ℝ)*(eps^(1/2 : ℝ)*Real.log (1/eps)^C.tau) := by
      calc Xz*(eps*Real.log (1/eps)^C.tau) =
          Xz*(eps^(1/2 : ℝ)*eps^(1/2 : ℝ))*Real.log (1/eps)^C.tau := by rw [hs]; ring
        _ = _ := by ring
    rw [this]
    calc Xz*eps^(1/2 : ℝ)*(eps^(1/2 : ℝ)*Real.log (1/eps)^C.tau)
        ≤ Xz*eps^(1/2 : ℝ)*(1/(6*Xz)) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = eps^(1/2 : ℝ)/6 := by field_simp
  refine ⟨?_, ?_⟩
  · have : d^2 ≤ (eps^(1/2 : ℝ)/6)^2 := pow_le_pow_left₀ hd0 hdd 2
    have h2 : (eps^(1/2 : ℝ)/6)^2 = eps/36 := by rw [div_pow, sq, hs]; norm_num
    linarith
  · have := (lt_div_iff₀ (by positivity : (0:ℝ) < 2*n)).1 hε1
    linarith

end TubeNode

end KAM.Planetary

end
