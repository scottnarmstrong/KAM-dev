/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.WrapperChain

/-!
# Tube helper lemmas (P11A-P10, `stepP:p11:wr-tube`)

Real polar formulas and the orthogonality estimate for the rotation chart input.
-/

@[expose] public noncomputable section
open Set
namespace KAM.Planetary

section Tube

variable {n : ℕ}

theorem p11PolarR_cast {w : Phase (n+n)} (hw : ∀ i : Fin n, 0 < w.2 (Fin.natAdd n i))
    (i : Fin n) : (p11PolarR w).2 (Fin.castAdd n i) = w.2 (Fin.castAdd n i) := by
  rw [p11PolarR_eq hw]
  simp [polarMap, p11PolarScale_apply, assemble, fast]

theorem p11PolarR_sq {w : Phase (n+n)} (hw : ∀ i : Fin n, 0 < w.2 (Fin.natAdd n i))
    (i : Fin n) : (p11PolarR w).1 (Fin.natAdd n i) ^ 2 + (p11PolarR w).2 (Fin.natAdd n i) ^ 2 =
      w.2 (Fin.natAdd n i) / Real.pi := by
  rw [p11PolarR_eq hw]
  have hR : 0 ≤ 2 * ((2 * Real.pi)⁻¹ * w.2 (Fin.natAdd n i)) :=
    by have := hw i; positivity
  simp only [polarMap, p11PolarScale_apply, assemble, slow, fast, Fin.append_right,
    Pi.smul_apply, smul_eq_mul]
  rw [mul_pow, mul_pow, Real.sq_sqrt hR, ← mul_add, Real.sin_sq_add_cos_sq, mul_one]
  field_simp

/-- A complex matrix with real entries and `Rᵀ R = 1` preserves the Euclidean norm of real
vectors (read through the real part). -/
theorem p11_orth_sq {R : Matrix (Fin n) (Fin n) ℂ} (hre : ∀ i j, (R i j).im = 0)
    (horth : R.transpose * R = 1) (a : Fin n → ℝ) :
    ∑ i, ((R.mulVec (KAM.realInclusion n a)) i).re ^ 2 = ∑ j, a j ^ 2 := by
  set Rr : Matrix (Fin n) (Fin n) ℝ := fun i j => (R i j).re with hRr
  have h1 : ∀ i, ((R.mulVec (KAM.realInclusion n a)) i).re = (Rr.mulVec a) i := fun i => by
    simp only [Matrix.mulVec, dotProduct, Complex.re_sum, KAM.realInclusion_apply, hRr]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_re, hre i j]
  have h2 : Rr.transpose * Rr = 1 := by
    ext i j
    have := congrFun (congrFun horth i) j
    have h3 := congrArg Complex.re this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Complex.re_sum, Complex.mul_re,
      hre, mul_zero, sub_zero] at h3
    show ∑ x, (R x i).re * (R x j).re = (1 : Matrix (Fin n) (Fin n) ℝ) i j
    rw [h3]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  simp only [h1, sq]
  have := Matrix.dotProduct_mulVec (Rr.mulVec a) Rr a
  calc ∑ i, (Rr.mulVec a) i * (Rr.mulVec a) i = (Rr.mulVec a) ⬝ᵥ (Rr.mulVec a) := rfl
    _ = ∑ j, a j * a j := by
      rw [this, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]; rfl

/-- The `Γ_i` of the chart input is bounded by half the Euclidean norm of the oscillator point. -/
theorem p11_chartInput_gamma {D : P11Physical n} (hC : P11SecularSpec D (p11SecularData D))
    {v : Phase (n+n)}
    (hv : ‖(fun i : Fin n => v.2 (Fin.castAdd n i)) - (p11SecularData D).J0‖ <
      2*(p11SecularData D).rC) (i : Fin n) :
    poincareGamma (planetBlock (p11ChartInput (p11SecularData D) v) i) ≤
      (1/2) * ∑ j : Fin n, (v.1 (Fin.natAdd n j) ^ 2 + v.2 (Fin.natAdd n j) ^ 2) := by
  set C := p11SecularData D with hCd
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hrc, hrb, -⟩ := hC
  set L : P11Vec n := fun i => fast v.2 i / (2*Real.pi) with hL
  have hLn : ‖L - (2*Real.pi)⁻¹ • C.J0‖ < C.rC/Real.pi := by
    have : L - (2*Real.pi)⁻¹ • C.J0 = (2*Real.pi)⁻¹ • ((fun i : Fin n => v.2 (Fin.castAdd n i)) -
        C.J0) := by
      funext i; simp [hL, fast, div_eq_inv_mul, mul_sub]
    rw [this, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc (2*Real.pi)⁻¹ * ‖(fun i : Fin n => v.2 (Fin.castAdd n i)) - C.J0‖
        < (2*Real.pi)⁻¹ * (2*C.rC) := mul_lt_mul_of_pos_left hv (by positivity)
      _ = C.rC/Real.pi := by field_simp
  have hre := (hrc L hLn).1
  have hball : KAM.realInclusion n L ∈ Metric.ball ((2*Real.pi)⁻¹ • KAM.realInclusion n C.J0)
      (C.rC/Real.pi) := by
    rw [Metric.mem_ball, dist_eq_norm, ← map_smul, ← map_sub, KAM.norm_realInclusion]
    exact hLn
  have horth := (hrb.2 _ hball).1
  have hsq := fun a => p11_orth_sq (R := C.rho (KAM.realInclusion n L)) hre horth a
  have hpt : poincareGamma (planetBlock (p11ChartInput C v) i) =
      (((C.rho (KAM.realInclusion n L)).mulVec (KAM.realInclusion n (slow v.1)) i).re ^ 2 +
        ((C.rho (KAM.realInclusion n L)).mulVec (KAM.realInclusion n (slow v.2)) i).re ^ 2)/2 := by
    simp [poincareGamma, planetBlock, p11ChartInput, assemble, slow, fast, hL]
  rw [hpt]
  have h1 := Finset.single_le_sum (f := fun i => ((C.rho (KAM.realInclusion n L)).mulVec
    (KAM.realInclusion n (slow v.1)) i).re ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 := Finset.single_le_sum (f := fun i => ((C.rho (KAM.realInclusion n L)).mulVec
    (KAM.realInclusion n (slow v.2)) i).re ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
  rw [hsq] at h1 h2
  have : ∑ j : Fin n, (v.1 (Fin.natAdd n j) ^ 2 + v.2 (Fin.natAdd n j) ^ 2) =
      ∑ j, slow v.1 j ^ 2 + ∑ j, slow v.2 j ^ 2 := by
    rw [← Finset.sum_add_distrib]; rfl
  rw [this]
  linarith

theorem p11_patch_near (D : P11Physical n) {J : P11Vec n} (hJ : J ∈ (p11PatchData D).K)
    (i : Fin n) : |J i/(2*Real.pi) - D.m i*Real.sqrt (D.G*D.m0*D.a i)| < p11PhysicalDelta D/8 := by
  have h := (p11_patch D).choose_spec
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hnear⟩ := h
  exact hnear J hJ i

theorem p11_abs_le_of_pi_norm {a b : ℝ} {f : Fin n → ℂ} {i : Fin n} {M : ℝ}
    (hf : f i = (a : ℂ) - (b : ℂ)) (h : ‖f‖ ≤ M) : |a - b| ≤ M := by
  have := (norm_le_pi_norm f i).trans h
  rwa [hf, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this

/-- Displacement of the slow stage on real points. -/
theorem p11_wr_psi_disp {D : P11Physical n} {nu eps : ℝ}
    (hS : P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps))
    {y : Phase (n+n)} (hy : KAM.realInclusion₂ (n+n) y ∈ p11WrSlowDom D nu eps) :
    (∀ i : Fin n, |(p11WrPsiR D nu eps y).2 (Fin.natAdd n i) - y.2 (Fin.natAdd n i)| ≤
      p11SlowConstant D nu*eps^(3/2 : ℝ)*Real.log (1/eps)^(3*(p11SecularData D).tau+1)) ∧
    ∀ i : Fin n, |(p11WrPsiR D nu eps y).2 (Fin.castAdd n i) - y.2 (Fin.castAdd n i)| ≤
      p11SlowConstant D nu*eps^(5/2 : ℝ)*Real.log (1/eps)^(3*(p11SecularData D).tau+1) := by
  obtain ⟨-, -, hPsiReal, -⟩ := p11WrPsiR_facts hS
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hS26⟩ := hS
  obtain ⟨hb1, hb2, -⟩ := hS26 _ hy
  rw [← hPsiReal y hy] at hb1 hb2
  exact ⟨fun i => p11_abs_le_of_pi_norm (f := fun i : Fin n =>
      (KAM.realInclusion₂ (n+n) (p11WrPsiR D nu eps y)).2 (Fin.natAdd n i) -
      (KAM.realInclusion₂ (n+n) y).2 (Fin.natAdd n i)) (i := i) rfl hb1,
    fun i => p11_abs_le_of_pi_norm (f := fun i : Fin n =>
      (KAM.realInclusion₂ (n+n) (p11WrPsiR D nu eps y)).2 (Fin.castAdd n i) -
      (KAM.realInclusion₂ (n+n) y).2 (Fin.castAdd n i)) (i := i) rfl hb2⟩

/-- Displacement of the fast stage on real points. -/
theorem p11_wr_fast_disp {D : P11Physical n} {eps : ℝ}
    (hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps))
    (hα : 0 < p11Alpha1 (p11SecularData D) eps) (hσ : 0 < (p11SecularData D).sigma)
    (hrz : 0 < (p11SecularData D).rz) {u : Phase (n+n)}
    (hu : KAM.realInclusion₂ (n+n) u ∈ p11WrFastDom D eps) :
    (∀ i : Fin n, |(p11WrFastR D eps u).2 (Fin.castAdd n i) - u.2 (Fin.castAdd n i)| ≤
      3*eps*(p11SecularData D).MF/(2*Real.pi*p11Alpha1 (p11SecularData D) eps*
        (p11SecularData D).sigma)) ∧
    (∀ i : Fin n, |(p11WrFastR D eps u).1 (Fin.natAdd n i) - u.1 (Fin.natAdd n i)| ≤
      9*eps*(p11SecularData D).MF/(2*Real.pi*p11Alpha1 (p11SecularData D) eps*
        (p11SecularData D).rz)) ∧
    ∀ i : Fin n, |(p11WrFastR D eps u).2 (Fin.natAdd n i) - u.2 (Fin.natAdd n i)| ≤
      9*eps*(p11SecularData D).MF/(2*Real.pi*p11Alpha1 (p11SecularData D) eps*
        (p11SecularData D).rz) := by
  obtain ⟨-, -, hFReal, -⟩ := p11WrFastR_facts hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hFb⟩ := hF
  obtain ⟨hFJ, -, hFxy⟩ := hFb _ hu
  rw [← hFReal u hu] at hFJ hFxy
  have hpi := Real.pi_pos
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · refine p11_abs_le_of_pi_norm (f := fun i : Fin n => (KAM.realInclusion₂ (n+n)
      (p11WrFastR D eps u)).2 (Fin.castAdd n i) - (KAM.realInclusion₂ (n+n) u).2
      (Fin.castAdd n i)) (i := i) rfl ?_
    rw [le_div_iff₀ (by positivity)]
    linarith
  · refine p11_abs_le_of_pi_norm (f := fun i : Fin n => (KAM.realInclusion₂ (n+n)
      (p11WrFastR D eps u)).1 (Fin.natAdd n i) - (KAM.realInclusion₂ (n+n) u).1
      (Fin.natAdd n i)) (i := i) rfl ?_
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact (mul_le_mul_of_nonneg_left (le_max_left _ _)
      (by positivity : (0:ℝ) ≤ 2*Real.pi*p11Alpha1 (p11SecularData D) eps*
        (p11SecularData D).rz)).trans hFxy
  · refine p11_abs_le_of_pi_norm (f := fun i : Fin n => (KAM.realInclusion₂ (n+n)
      (p11WrFastR D eps u)).2 (Fin.natAdd n i) - (KAM.realInclusion₂ (n+n) u).2
      (Fin.natAdd n i)) (i := i) rfl ?_
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact (mul_le_mul_of_nonneg_left (le_max_right _ _)
      (by positivity : (0:ℝ) ≤ 2*Real.pi*p11Alpha1 (p11SecularData D) eps*
        (p11SecularData D).rz)).trans hFxy

end Tube

end KAM.Planetary

end
