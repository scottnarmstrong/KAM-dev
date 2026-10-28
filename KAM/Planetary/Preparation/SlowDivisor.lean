/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowDerivative
public import KAM.Planetary.Preparation.FastDivisor

/-!
# Slow averaging: the divisor clause (P11A-P7c, `stepP:p11:as-nr`)

The pure-slow and mixed divisor bounds `(B1)` for `h₀ = C.h ∘ J + ε W` on the box `V₂`:
the mixed case via `fast_divisor`, the pure-slow case via the Diophantine bound on the secular
frequency `Ω/(2π)` and the `ρ`-derivative bound of `Z`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped BigOperators
namespace KAM.Planetary

section SlowDivisor

variable {n : ℕ}

open KAM.NormalForm

/-- The center of the slow box `V₂` (verbatim from `P11SlowSpecOf`). -/
def p11SlowCenter (C : P11SecularData n) (eps : ℝ) : P11CVec (n+n) :=
  Fin.append (KAM.realInclusion n C.J0) (fun _ => 2*Real.pi*eps)

/-- The slow box `V₂` (verbatim from `P11SlowSpecOf`). -/
def p11SlowBox (C : P11SecularData n) (nu eps : ℝ) : Set (P11CVec (n+n)) :=
  p11Box (p11SlowCenter C eps) (p11s2 C nu eps) (Real.pi*eps)

/-- The domain of `Z` in `P11SlowSpecOf`. -/
def p11SlowZDom (C : P11SecularData n) (eps : ℝ) : Set (P11CVec (n+n)) :=
  {I : P11CVec (n+n) |
    ‖(fun i : Fin n => I (Fin.castAdd n i))-KAM.realInclusion n C.J0‖ < p11s1 C eps/2 ∧
    ‖(fun i : Fin n => I (Fin.natAdd n i))‖ < Real.pi*C.rz^2/16}

theorem p11SlowBox_isOpen (C : P11SecularData n) (nu eps : ℝ) : IsOpen (p11SlowBox C nu eps) := by
  unfold p11SlowBox p11Box
  rw [Set.ofPred_and]
  simp only [Set.ofPred_forall]
  refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_lt ?_ continuous_const)
    (isOpen_iInter_of_finite fun i => isOpen_lt ?_ continuous_const) <;> fun_prop

theorem p11SlowZDom_isOpen (C : P11SecularData n) (eps : ℝ) : IsOpen (p11SlowZDom C eps) := by
  unfold p11SlowZDom
  rw [Set.ofPred_and]
  refine IsOpen.inter (isOpen_lt ?_ continuous_const) (isOpen_lt ?_ continuous_const) <;>
    fun_prop

theorem p11SlowBox_mem {C : P11SecularData n} {nu eps : ℝ} (hs2 : 0 < p11s2 C nu eps)
    (heps : 0 < eps) {I : P11CVec (n+n)} (hI : I ∈ p11SlowBox C nu eps) :
    ‖(fun i : Fin n => I (Fin.castAdd n i))-KAM.realInclusion n C.J0‖ < p11s2 C nu eps ∧
    ‖(fun i : Fin n => I (Fin.natAdd n i))-(fun _ => (2*Real.pi*eps : ℂ))‖ < Real.pi*eps := by
  obtain ⟨h1, h2⟩ := hI
  refine ⟨(pi_norm_lt_iff hs2).2 fun i => ?_, (pi_norm_lt_iff (by positivity)).2 fun i => ?_⟩
  · simpa [p11SlowCenter, Fin.append_left] using h1 i
  · simpa [p11SlowCenter, Fin.append_right] using h2 i

theorem norm_Jf_sub_le (y I : P11CVec (n+n)) :
    ‖(fun i : Fin n => y (Fin.castAdd n i)) - (fun i : Fin n => I (Fin.castAdd n i))‖ ≤ ‖y - I‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
    simpa using norm_le_pi_norm (y - I) (Fin.castAdd n i)

theorem norm_Rf_sub_le (y I : P11CVec (n+n)) :
    ‖(fun i : Fin n => y (Fin.natAdd n i)) - (fun i : Fin n => I (Fin.natAdd n i))‖ ≤ ‖y - I‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
    simpa using norm_le_pi_norm (y - I) (Fin.natAdd n i)

theorem modeSize_split (k : Fin (n+n) → ℤ) :
    KAM.Fourier.modeSize k = KAM.Fourier.modeSize (fun i : Fin n => k (Fin.castAdd n i)) +
      KAM.Fourier.modeSize (fun i : Fin n => k (Fin.natAdd n i)) := by
  unfold KAM.Fourier.modeSize
  rw [Fin.sum_univ_add]

/-- The two constants of `p11s2`: `s₂ ≤ s₁/4` and `K L s₂ ≤ γ K^{-τ}/8`. -/
theorem p11s2_spec {D : P11Physical n} {C : P11SecularData n} (hC : P11SecularSpec D C)
    {nu eps : ℝ} (hK : 0 < p11K2 C nu eps) :
    p11s2 C nu eps ≤ p11s1 C eps / 4 ∧
      p11K2 C nu eps * C.L * p11s2 C nu eps ≤ C.gamma * p11K2 C nu eps ^ (-C.tau) / 8 := by
  obtain ⟨hγ0, hτ0, hL1, -⟩ := fast_consts hC
  refine ⟨min_le_left _ _, ?_⟩
  have hL0 : 0 < C.L := by linarith
  have h2 : p11s2 C nu eps ≤ C.gamma / (8 * C.L * p11K2 C nu eps ^ (C.tau + 1)) :=
    min_le_right _ _
  have hKp : 0 < p11K2 C nu eps ^ (C.tau + 1) := Real.rpow_pos_of_pos hK _
  calc p11K2 C nu eps * C.L * p11s2 C nu eps
      ≤ p11K2 C nu eps * C.L * (C.gamma / (8 * C.L * p11K2 C nu eps ^ (C.tau + 1))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = C.gamma * p11K2 C nu eps ^ (-C.tau) / 8 := by
        rw [Real.rpow_neg hK.le, Real.rpow_add_one hK.ne']
        field_simp

theorem slowZDom_J_mem {C : P11SecularData n} {eps : ℝ} (hrC : 0 < C.rC)
    {x : P11CVec (n+n)} (hx : x ∈ p11SlowZDom C eps) :
    (fun i : Fin n => x (Fin.castAdd n i)) ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) := by
  have h1 : p11s1 C eps ≤ C.rC := min_le_left _ _
  have := hx.1
  rw [mem_ball_iff_norm]
  linarith

/-- The bracket `W` is holomorphic where `Z` is. -/
theorem slowW_differentiableOn {D : P11Physical n} {C : P11SecularData n}
    (hC : P11SecularSpec D C) {eps : ℝ} {Z : P11CVec (n+n) → ℂ}
    (hZd : DifferentiableOn ℂ Z (p11SlowZDom C eps)) :
    DifferentiableOn ℂ (p11SlowW C Z) (p11SlowZDom C eps) := by
  obtain ⟨-, -, -, hrC, -⟩ := fast_consts hC
  obtain ⟨hOm, -⟩ := secular_extract hC
  have hJf : Differentiable ℂ (fun x : P11CVec (n+n) => fun i : Fin n => x (Fin.castAdd n i)) := by
    fun_prop
  have hmaps : MapsTo (fun x : P11CVec (n+n) => fun i : Fin n => x (Fin.castAdd n i))
      (p11SlowZDom C eps) (ball (KAM.realInclusion n C.J0) (2 * C.rC)) :=
    fun x hx => slowZDom_J_mem hrC hx
  have hC1 := (p11C_differentiableOn hC).comp hJf.differentiableOn hmaps
  have hO1 := hOm.comp hJf.differentiableOn hmaps
  have hsum : DifferentiableOn ℂ (fun x : P11CVec (n+n) =>
      ∑ i : Fin n, C.Omega (fun j : Fin n => x (Fin.castAdd n j)) i/(2*Real.pi)*
        x (Fin.natAdd n i)) (p11SlowZDom C eps) := by
    refine DifferentiableOn.fun_sum fun i _ => ?_
    have hd : DifferentiableOn ℂ (fun x : P11CVec (n+n) =>
        C.Omega (fun j : Fin n => x (Fin.castAdd n j)) i) (p11SlowZDom C eps) :=
      differentiableOn_pi.1 hO1 i
    have hd' : DifferentiableOn ℂ (fun x : P11CVec (n+n) =>
        C.Omega (fun j : Fin n => x (Fin.castAdd n j)) i/(2*Real.pi)) (p11SlowZDom C eps) :=
      (hd.const_smul ((2*Real.pi : ℂ)⁻¹)).congr (fun x _ => by
        simp [div_eq_inv_mul])
    refine hd'.mul ?_
    exact (differentiable_pi.1 (differentiable_id) (Fin.natAdd n i)).differentiableOn
  exact (hC1.add hsum).add hZd

/-- The secular frequency `Ω/(2π)` is `L`-Lipschitz on the ball `2 r_C`. -/
theorem Omega_lipschitz {D : P11Physical n} {C : P11SecularData n} (hC : P11SecularSpec D C)
    {J : P11CVec n} (hJ : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC)) :
    ‖(2 * Real.pi : ℂ)⁻¹ • C.Omega J - (2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0)‖ ≤
      C.L * ‖J - KAM.realInclusion n C.J0‖ := by
  obtain ⟨-, -, ⟨hωd, hΩd⟩, -, -, -, hL, -, -, -, -, hrC0, -⟩ := hC
  have hopen : IsOpen (ball (KAM.realInclusion n C.J0) (2 * C.rC)) := isOpen_ball
  have hd : ∀ x ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC),
      DifferentiableAt ℂ (fun J => (Fin.append (C.omega J) ((2 * Real.pi : ℂ)⁻¹ • C.Omega J) :
        Fin (n + n) → ℂ)) x := fun x hx =>
    differentiableAt_append (hωd.differentiableAt (hopen.mem_nhds hx))
      (DifferentiableAt.const_smul (hΩd.differentiableAt (hopen.mem_nhds hx)) ((2 * Real.pi : ℂ)⁻¹))
  have hb : ∀ x ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC),
      ‖fderiv ℂ (fun J => (Fin.append (C.omega J) ((2 * Real.pi : ℂ)⁻¹ • C.Omega J) :
        Fin (n + n) → ℂ)) x‖ ≤ C.L := fun x hx => by
    have := hL x hx 1 (Nat.le_add_left 1 _)
    simpa using this
  have hmvt := (convex_ball (KAM.realInclusion n C.J0)
    (2 * C.rC)).norm_image_sub_le_of_norm_fderiv_le
    hd hb (mem_ball_self (by linarith)) hJ
  refine le_trans ?_ hmvt
  refine pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun i => ?_
  have := norm_le_pi_norm (Fin.append (C.omega J) ((2 * Real.pi : ℂ)⁻¹ • C.Omega J) -
    Fin.append (C.omega (KAM.realInclusion n C.J0))
      ((2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0))) (Fin.natAdd n i)
  simpa using this

/-- The real part of `k₂ · Ω(J₀)/(2π)` is `k₂ · ϖ`'s slow block, so it is Diophantine. -/
theorem re_dotC_Omega {D : P11Physical n} {C : P11SecularData n} (hC : P11SecularSpec D C)
    {k : Fin n → ℤ} (hk : k ≠ 0) :
    C.gamma / (KAM.Fourier.modeSize k) ^ C.tau ≤
      |(dotC k ((2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0))).re| := by
  obtain ⟨hA, -, -, -, -, -, -, -, -, -, hdio, hrC0, -⟩ := hC
  have hmem : KAM.realInclusion n C.J0 ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) :=
    mem_ball_self (by linarith)
  obtain ⟨-, -, hre⟩ := hA C.J0 hmem
  have hk' : (Fin.append (0 : Fin n → ℤ) k : Fin (n + n) → ℤ) ≠ 0 := by
    intro h
    apply hk
    funext i
    have := congrFun h (Fin.natAdd n i)
    simpa using this
  have h := hdio _ hk'
  have e1 : ∑ i : Fin (n + n), |((Fin.append (0 : Fin n → ℤ) k i : ℤ) : ℝ)| =
      KAM.Fourier.modeSize k := by
    rw [Fin.sum_univ_add]
    simp [KAM.Fourier.modeSize]
  have e2 : ∑ i : Fin (n + n), ((Fin.append (0 : Fin n → ℤ) k i : ℤ) : ℝ) *
      (p11PatchData D).varpi C.J0 i =
        (dotC k ((2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0))).re := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, Int.cast_zero, zero_mul,
      Finset.sum_const_zero, zero_add, dotC, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hr := hre i
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have : ((2 * Real.pi : ℂ)⁻¹ * C.Omega (KAM.realInclusion n C.J0) i).re =
        (p11PatchData D).varpi C.J0 (Fin.natAdd n i) := by
      have h1 : ((2 * Real.pi : ℂ)⁻¹) = ((2 * Real.pi)⁻¹ : ℝ) := by push_cast; rfl
      rw [h1, Complex.re_ofReal_mul, hr]
      field_simp
    rw [Pi.smul_apply, smul_eq_mul, ← Complex.ofReal_intCast, Complex.re_ofReal_mul, this]
  rw [e1, e2] at h
  exact h

/-- Lower bound of the slow-block pairing `k₂ · Ω(J)/(2π)` near `J₀`. -/
theorem dotC_Omega_lower {D : P11Physical n} {C : P11SecularData n} (hC : P11SecularSpec D C)
    {J : P11CVec n} (hJ : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC)) {K sV : ℝ} (hK : 0 < K)
    (hJs : ‖J - KAM.realInclusion n C.J0‖ ≤ sV)
    (hsK : K * C.L * sV ≤ C.gamma * K ^ (-C.tau) / 8)
    {k : Fin n → ℤ} (hk0 : k ≠ 0) (hkK : KAM.Fourier.modeSize k ≤ K) :
    7 / 8 * (C.gamma * K ^ (-C.tau)) ≤ ‖dotC k ((2 * Real.pi : ℂ)⁻¹ • C.Omega J)‖ := by
  have hC' := hC
  obtain ⟨-, -, -, hτ, -, -, -, -, hγ0, -, -, hrC0, -⟩ := hC
  have hpos : 0 < KAM.Fourier.modeSize k := by
    unfold KAM.Fourier.modeSize
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hk0
    exact lt_of_lt_of_le (abs_pos.2 (by exact_mod_cast hi))
      (Finset.single_le_sum (f := fun j => |(k j : ℝ)|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i))
  have hτ0 : 0 < C.tau := by
    rw [hτ]
    exact lt_max_of_lt_right (by have := (show (2 : ℕ) ≤ n from D.n_ge); positivity)
  have hdiv1 : C.gamma * K ^ (-C.tau) ≤ C.gamma / (KAM.Fourier.modeSize k) ^ C.tau := by
    rw [Real.rpow_neg hK.le, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hγ0.le (Real.rpow_pos_of_pos hpos _)
      (Real.rpow_le_rpow hpos.le hkK hτ0.le)
  have hdio := re_dotC_Omega hC' hk0
  have hre : |(dotC k ((2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0))).re| ≤
      ‖dotC k ((2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0))‖ :=
    Complex.abs_re_le_norm _
  have hlip := Omega_lipschitz hC' hJ
  have hms := p11fd_norm_dotC_le k ((2 * Real.pi : ℂ)⁻¹ • C.Omega J -
    (2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0))
  have hL0 : 0 ≤ C.L := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hL1, -⟩ := hC'
    linarith
  have hKL : KAM.Fourier.modeSize k * (C.L * ‖J - KAM.realInclusion n C.J0‖) ≤
      K * C.L * sV := by
    calc _ ≤ K * (C.L * sV) :=
          mul_le_mul hkK (mul_le_mul_of_nonneg_left hJs hL0) (by positivity) hK.le
      _ = _ := by ring
  have hmul : KAM.Fourier.modeSize k * ‖(2 * Real.pi : ℂ)⁻¹ • C.Omega J -
      (2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0)‖ ≤
      KAM.Fourier.modeSize k * (C.L * ‖J - KAM.realInclusion n C.J0‖) :=
    mul_le_mul_of_nonneg_left hlip hpos.le
  have hsub : dotC k ((2 * Real.pi : ℂ)⁻¹ • C.Omega J) =
      dotC k ((2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0)) +
      dotC k ((2 * Real.pi : ℂ)⁻¹ • C.Omega J -
        (2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0)) := by
    unfold dotC
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply]; ring
  have htri : ‖dotC k ((2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0))‖ -
      ‖dotC k ((2 * Real.pi : ℂ)⁻¹ • C.Omega J -
        (2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0))‖ ≤
      ‖dotC k ((2 * Real.pi : ℂ)⁻¹ • C.Omega J)‖ := by
    rw [hsub]
    have := norm_sub_norm_le (dotC k ((2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0)))
      (-(dotC k ((2 * Real.pi : ℂ)⁻¹ • C.Omega J -
        (2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0))))
    rw [norm_neg] at this
    simpa using this
  linarith

/-- `stepP:p11:as-nr` (B1): the divisor clause of `P11SlowSpecOf`, pure-slow and mixed.

`h₀ = C.h ∘ J + ε W` on `V₂`, `Z` holomorphic on its domain with `‖W‖ ≤ MW` there and the
`ρ`-slice derivative bound `cZ` (clause 6 of the spec for `α = 0`); the smallness hypotheses
are `K cZ ≤ δ₀/8` and `ε K MW ≤ (δ₀/2) R` with `δ₀ = γ K^{-τ}`, `R = min (s₁/4) (π r_z²/32)`. -/
theorem p11_slow_divisor {D : P11Physical n} {C : P11SecularData n} (hC : P11SecularSpec D C)
    {nu eps : ℝ} {h0 Z : P11CVec (n+n) → ℂ} {cZ MW : ℝ}
    (heps : 0 < eps) (hK : 0 < p11K2 C nu eps) (hs1 : 0 < p11s1 C eps)
    (hs2 : 0 < p11s2 C nu eps) (hepsrz : 3*eps ≤ C.rz^2/32) (hcZ0 : 0 ≤ cZ)
    (h3 : ∀ I ∈ p11SlowBox C nu eps,
      h0 I = C.h (fun i : Fin n => I (Fin.castAdd n i)) + eps*p11SlowW C Z I)
    (hZd : DifferentiableOn ℂ Z (p11SlowZDom C eps))
    (hMW : ∀ I ∈ p11SlowZDom C eps, ‖p11SlowW C Z I‖ ≤ MW)
    (hdZ : ∀ J : P11CVec n, ‖J-KAM.realInclusion n C.J0‖ < p11s1 C eps/4 →
      ∀ rho : P11CVec n, ‖rho-(fun _ => (2*Real.pi*eps : ℂ))‖ < Real.pi*eps → ∀ i : Fin n,
        ‖fderiv ℂ (fun rho : P11CVec n => Z (Fin.append J rho)) rho (Pi.single i 1)‖ ≤ cZ)
    (hcZ : p11K2 C nu eps*cZ ≤ C.gamma*p11K2 C nu eps^(-C.tau)/8)
    (hMWs : eps*p11K2 C nu eps*MW ≤
      C.gamma*p11K2 C nu eps^(-C.tau)/2*min (p11s1 C eps/4) (Real.pi*C.rz^2/32)) :
    ∀ I ∈ p11SlowBox C nu eps, ∀ k : Fin (n+n) → ℤ, k ≠ 0 →
      KAM.Fourier.modeSize k ≤ p11K2 C nu eps →
      (if (fun i : Fin n => k (Fin.castAdd n i))=0 then eps else 1)*
        C.gamma/4*p11K2 C nu eps^(-C.tau) ≤
        ‖p11dotC k (fun i => fderiv ℂ h0 I (Pi.single i 1))‖ := by
  intro I hI k hk0 hkK
  have hC' := hC
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, -, -, hrz0, -, -⟩ := fast_consts hC
  obtain ⟨-, -, ⟨-, hΩd⟩, -, hhd, hωh, -⟩ := hC'
  set K := p11K2 C nu eps with hKdef
  set s1 := p11s1 C eps with hs1def
  set s2 := p11s2 C nu eps with hs2def
  obtain ⟨hs2le, hKs⟩ := p11s2_spec hC hK
  obtain ⟨hJs, hρ⟩ := p11SlowBox_mem hs2 heps hI
  have hs1rC : s1 ≤ C.rC := min_le_left _ _
  have hπ : 0 < Real.pi := Real.pi_pos
  have hrz2 : 0 < C.rz ^ 2 := by positivity
  have hprz : 0 < Real.pi * C.rz ^ 2 := by positivity
  set J : P11CVec n := fun i => I (Fin.castAdd n i) with hJdef
  set Rr : P11CVec n := fun i => I (Fin.natAdd n i) with hRrdef
  have hJball : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) := by
    rw [mem_ball_iff_norm]; linarith
  have hρ0 : ‖(fun _ : Fin n => (2*Real.pi*eps : ℂ))‖ ≤ 2*Real.pi*eps := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Complex.norm_mul, Complex.norm_mul]
    simp [abs_of_pos heps, abs_of_pos hπ]
  have hRn : ‖Rr‖ < Real.pi * C.rz ^ 2 / 32 := by
    have h2 : ‖Rr‖ ≤ ‖(fun _ : Fin n => (2*Real.pi*eps : ℂ))‖ + ‖Rr - (fun _ : Fin n =>
        (2*Real.pi*eps : ℂ))‖ := by
      have := norm_le_insert' Rr (fun _ : Fin n => (2*Real.pi*eps : ℂ))
      linarith
    nlinarith
  set Rrad := min (s1/4) (Real.pi * C.rz ^ 2 / 32) with hRrad
  have hRpos : 0 < Rrad := lt_min (by linarith) (by positivity)
  have hIZ : I ∈ p11SlowZDom C eps := ⟨by show ‖J - _‖ < _; linarith, by
    show ‖Rr‖ < _; linarith⟩
  have hcl : closedBall I Rrad ⊆ p11SlowZDom C eps := by
    intro y hy
    rw [mem_closedBall_iff_norm] at hy
    have h1 := norm_Jf_sub_le y I
    have h2 := norm_Rf_sub_le y I
    have hr1 : Rrad ≤ s1/4 := min_le_left _ _
    have hr2 : Rrad ≤ Real.pi * C.rz ^ 2 / 32 := min_le_right _ _
    refine ⟨?_, ?_⟩
    · have := norm_sub_le_norm_sub_add_norm_sub
        (fun i : Fin n => y (Fin.castAdd n i)) J (KAM.realInclusion n C.J0)
      show _ < _
      linarith
    · have := norm_sub_le_norm_sub_add_norm_sub
        (fun i : Fin n => y (Fin.natAdd n i)) Rr 0
      simp only [sub_zero] at this
      show _ < _
      linarith
  have hWd := slowW_differentiableOn hC hZd
  have hWat : DifferentiableAt ℂ (p11SlowW C Z) I :=
    hWd.differentiableAt ((p11SlowZDom_isOpen C eps).mem_nhds hIZ)
  have hZat : DifferentiableAt ℂ Z I := hZd.differentiableAt ((p11SlowZDom_isOpen C eps).mem_nhds hIZ)
  have hhat : DifferentiableAt ℂ C.h J := hhd.differentiableAt (isOpen_ball.mem_nhds hJball)
  have hCat : DifferentiableAt ℂ C.C J :=
    (p11C_differentiableOn hC).differentiableAt (isOpen_ball.mem_nhds hJball)
  have hOat : DifferentiableAt ℂ C.Omega J := hΩd.differentiableAt (isOpen_ball.mem_nhds hJball)
  have hEv : h0 =ᶠ[nhds I] fun x : P11CVec (n+n) =>
      C.h (fun i : Fin n => x (Fin.castAdd n i)) + eps*p11SlowW C Z x :=
    Filter.eventuallyEq_of_mem ((p11SlowBox_isOpen C nu eps).mem_nhds hI) h3
  have hsplit := p11_slow_dotC_split (eps := eps) (Z := Z) hEv hhat hWat (hωh J hJball) k
  have hCau : ∀ j : Fin (n+n), ‖fderiv ℂ (p11SlowW C Z) I (Pi.single j 1)‖ ≤ MW / Rrad :=
    fun j => p11_scalar_step_bound (p11SlowZDom_isOpen C eps) hWd hRpos hcl
      (fun y hy => hMW y (hcl hy)) j
  have hepsC : ‖(eps : ℂ)‖ = eps := by simp [abs_of_pos heps]
  set δ0 := C.gamma * K ^ (-C.tau) with hδ0
  have hKt : 0 < K ^ (-C.tau) := Real.rpow_pos_of_pos hK _
  have hδpos : 0 < δ0 := mul_pos hγ0 hKt
  have hrhs : ∀ c : ℝ, c * C.gamma / 4 * K ^ (-C.tau) = c * (δ0 / 4) := fun c => by
    rw [hδ0]; ring
  have hmk1 : KAM.Fourier.modeSize (fun i : Fin n => k (Fin.castAdd n i)) ≤ K := by
    have := modeSize_split k
    have h2 := KAM.Fourier.modeSize_nonneg (fun i : Fin n => k (Fin.natAdd n i))
    linarith
  by_cases hk1 : (fun i : Fin n => k (Fin.castAdd n i)) = 0
  · rw [if_pos hk1, hrhs]
    have hk2 : (fun i : Fin n => k (Fin.natAdd n i)) ≠ 0 := by
      intro h; apply hk0; funext j
      refine Fin.addCases (fun a => ?_) (fun a => ?_) j
      · exact congrFun hk1 a
      · exact congrFun h a
    have hmk2 : KAM.Fourier.modeSize (fun i : Fin n => k (Fin.natAdd n i)) ≤ K := by
      have := modeSize_split k
      have h2 := KAM.Fourier.modeSize_nonneg (fun i : Fin n => k (Fin.castAdd n i))
      linarith
    have hΩ := dotC_Omega_lower hC hJball (K := K) (sV := s2) hK hJs.le hKs hk2 hmk2
    set zz : P11CVec n := fun a => fderiv ℂ Z I (Pi.single (Fin.natAdd n a) 1) with hzz
    have hdW : p11dotC k (fun i => fderiv ℂ (p11SlowW C Z) I (Pi.single i 1)) =
        dotC (fun i : Fin n => k (Fin.natAdd n i)) ((2 * Real.pi : ℂ)⁻¹ • C.Omega J) +
        dotC (fun i : Fin n => k (Fin.natAdd n i)) zz := by
      rw [p11dotC_split]
      have h0' : p11dotC (fun i : Fin n => k (Fin.castAdd n i)) (fun i : Fin n =>
          fderiv ℂ (p11SlowW C Z) I (Pi.single (Fin.castAdd n i) 1)) = 0 := by
        rw [hk1]; simp [p11dotC]
      rw [h0', zero_add]
      unfold p11dotC dotC
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      beta_reduce
      rw [fderiv_slowW_nat hCat hOat hZat a]
      simp only [Pi.smul_apply, smul_eq_mul, hzz, div_eq_inv_mul]
      ring
    have hzzn : ‖zz‖ ≤ cZ := by
      refine (pi_norm_le_iff_of_nonneg hcZ0).2 fun a => ?_
      have hI' : (Fin.append J Rr : P11CVec (n+n)) = I := Fin.append_castAdd_natAdd (f := I)
      have h1 := fderiv_append_slice (Z := Z) (J := J) (ρ := Rr) (by rw [hI']; exact hZat) a
      rw [hI'] at h1
      show ‖fderiv ℂ Z I (Pi.single (Fin.natAdd n a) 1)‖ ≤ cZ
      rw [← h1]
      exact hdZ J (by linarith) Rr hρ a
    have hB : ‖dotC (fun i : Fin n => k (Fin.natAdd n i)) zz‖ ≤ δ0 / 8 := by
      refine (p11fd_norm_dotC_le _ zz).trans ?_
      calc _ ≤ K * cZ := mul_le_mul hmk2 hzzn (norm_nonneg _) hK.le
        _ ≤ δ0 / 8 := hcZ
    have hdot0 : dotC (fun i : Fin n => k (Fin.castAdd n i)) (C.omega J) = 0 := by
      rw [hk1]; simp [dotC]
    have hsp : p11dotC k (fun i => fderiv ℂ h0 I (Pi.single i 1)) =
        (eps : ℂ) * (dotC (fun i : Fin n => k (Fin.natAdd n i)) ((2 * Real.pi : ℂ)⁻¹ • C.Omega J) +
        dotC (fun i : Fin n => k (Fin.natAdd n i)) zz) := by
      rw [hsplit, hdW]
      show dotC _ _ + _ = _
      rw [hdot0, zero_add]
    rw [hsp, norm_mul, hepsC]
    have hA := norm_sub_le (dotC (fun i : Fin n => k (Fin.natAdd n i))
      ((2 * Real.pi : ℂ)⁻¹ • C.Omega J) + dotC (fun i : Fin n => k (Fin.natAdd n i)) zz)
      (dotC (fun i : Fin n => k (Fin.natAdd n i)) zz)
    rw [add_sub_cancel_right] at hA
    have hge : δ0 / 4 ≤ ‖dotC (fun i : Fin n => k (Fin.natAdd n i))
        ((2 * Real.pi : ℂ)⁻¹ • C.Omega J) + dotC (fun i : Fin n => k (Fin.natAdd n i)) zz‖ := by
      linarith
    exact mul_le_mul_of_nonneg_left hge heps.le
  · rw [if_neg hk1, hrhs]
    have hKs' : K * C.L * s2 ≤ C.gamma * K ^ (-C.tau) / 4 := by linarith
    have hdb := fast_divisor hC (s1 := s2) (K := K) (α := 3 / 4 * C.gamma * K ^ (-C.tau))
      (hs1 := hs2le.trans (by linarith)) hK hKs' le_rfl
    have hJm : J ∈ KAM.actionNbhd {C.J0} s2 := by
      refine ⟨C.J0, rfl, ?_⟩
      have : KAM.realInclusion n C.J0 = fun i => (C.J0 i : ℂ) := by funext i; simp
      rw [← this]; exact hJs
    have hkz : (fun i : Fin n => k (Fin.castAdd n i)) ∈ KAM.NormalForm.zBall n K \ {0} :=
      ⟨hmk1, fun h => hk1 (by simpa using h)⟩
    have hfd := hdb J hJm _ hkz
    have hfr : KAM.NormalForm.freq C.h J = C.omega J := by
      rw [hωh J hJball]; rfl
    rw [hfr] at hfd
    have hCW : ‖p11dotC k (fun i => fderiv ℂ (p11SlowW C Z) I (Pi.single i 1))‖ ≤
        K * (MW / Rrad) := by
      have h0MW : 0 ≤ MW / Rrad := div_nonneg ((norm_nonneg _).trans (hMW I hIZ)) hRpos.le
      have hv : ‖fun j : Fin (n+n) => fderiv ℂ (p11SlowW C Z) I (Pi.single j 1)‖ ≤ MW / Rrad :=
        (pi_norm_le_iff_of_nonneg h0MW).2 hCau
      refine (p11fd_norm_dotC_le k _).trans ?_
      exact mul_le_mul hkK hv (norm_nonneg _) hK.le
    have hsm : eps * (K * (MW / Rrad)) ≤ δ0 / 2 := by
      have : eps * (K * (MW / Rrad)) = eps * K * MW / Rrad := by ring
      rw [this, div_le_iff₀ hRpos]
      exact hMWs
    have hA := norm_sub_le (p11dotC k (fun i => fderiv ℂ h0 I (Pi.single i 1)))
      ((eps : ℂ) * p11dotC k (fun i => fderiv ℂ (p11SlowW C Z) I (Pi.single i 1)))
    have hsub : p11dotC k (fun i => fderiv ℂ h0 I (Pi.single i 1)) -
        (eps : ℂ) * p11dotC k (fun i => fderiv ℂ (p11SlowW C Z) I (Pi.single i 1)) =
        dotC (fun i : Fin n => k (Fin.castAdd n i)) (C.omega J) := by
      have hdd : p11dotC (fun i : Fin n => k (Fin.castAdd n i)) (C.omega J) =
          dotC (fun i : Fin n => k (Fin.castAdd n i)) (C.omega J) := rfl
      rw [hsplit, hdd]; ring
    rw [hsub] at hA
    have hε : ‖(eps : ℂ) * p11dotC k (fun i => fderiv ℂ (p11SlowW C Z) I (Pi.single i 1))‖ ≤
        eps * (K * (MW / Rrad)) := by
      rw [norm_mul, hepsC]
      exact mul_le_mul_of_nonneg_left hCW heps.le
    have hfd2 : 3 / 4 * δ0 ≤ ‖dotC (fun i : Fin n => k (Fin.castAdd n i)) (C.omega J)‖ := by
      have : 3 / 4 * C.gamma * K ^ (-C.tau) = 3 / 4 * δ0 := by rw [hδ0, mul_assoc]
      rw [← this]; exact hfd
    linarith

end SlowDivisor

end KAM.Planetary

end
