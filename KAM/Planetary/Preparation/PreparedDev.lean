/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedJets
public import KAM.Planetary.Preparation.PreparedOps

/-!
# Deviation of the partials of `h = h₀ + g₂` from the main terms (P11A-P8b2, pr-b, pr-c, pr-d)

Identities (no estimates) for the coordinate partials of `h = A.h₀ + A.g₂` at a point
`P = (J, ρ̃)` of the Cauchy region (`‖J - J₀‖ < s₂/4`, `‖ρ̃ - 2πε‖ < 5ε/4`):

* `p11_dev_J`: pure `J` partials, `∂^{(α,0)} h₀ = ∂^α C.h + ε ∂^α Ĝ₀` (formula 1 of the spec);
* `p11_dev_rho`: partials with a `ρ̃`-index, via formula 2 of the spec.
-/

@[expose] public noncomputable section
open Set Metric
open scoped BigOperators
namespace KAM.Planetary

section Dev

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- Centre of the slow polydisc. -/
abbrev p11DevCenter (C : P11SecularData n) (eps : ℝ) : P11CVec (n + n) :=
  Fin.append (KAM.realInclusion n C.J0) (fun _ => (2 * Real.pi * eps : ℂ))

theorem p11_dev_mem_box {C : P11SecularData n} {eps r1 r2 r1' r2' : ℝ} (J ρ : P11CVec n)
    (hr1 : r1' ≤ r1) (hr2 : r2' ≤ r2)
    (hJ : ‖J - KAM.realInclusion n C.J0‖ < r1')
    (hρ : ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < r2') :
    (Fin.append J ρ : P11CVec (n + n)) ∈ p11Box (p11DevCenter C eps) r1 r2 := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := norm_le_pi_norm (J - KAM.realInclusion n C.J0) i
    simp only [Fin.append_left, Pi.sub_apply] at this ⊢
    linarith
  · have := norm_le_pi_norm (ρ - (fun _ => (2 * Real.pi * eps : ℂ))) i
    simp only [Fin.append_right, Pi.sub_apply] at this ⊢
    linarith

theorem p11_dev_box_isOpen {a b : ℕ} (c : P11CVec (a + b)) (r1 r2 : ℝ) :
    IsOpen (p11Box c r1 r2) := by
  rw [p11Box_eq]
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const

theorem p11_dev_rho_norm {eps : ℝ} (heps : 0 < eps) (hrz0 : 0 < C.rz)
    (hzs : 3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16) {ρ : P11CVec n}
    (hρ : ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4) :
    ‖ρ‖ < Real.pi * (C.rz / 2) ^ 2 := by
  have hπ := Real.pi_gt_three
  have hc : ‖(fun _ : Fin n => (2 * Real.pi * eps : ℂ))‖ ≤ 2 * Real.pi * eps := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [show (2 * Real.pi * eps : ℂ) = ((2 * Real.pi * eps : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h1 := norm_le_norm_add_norm_sub' ρ (fun _ : Fin n => (2 * Real.pi * eps : ℂ))
  have h2 : Real.pi * C.rz ^ 2 / 16 > 0 := by positivity
  have h3 : Real.pi * (C.rz / 2) ^ 2 = Real.pi * C.rz ^ 2 / 4 := by ring
  rw [h3]
  nlinarith

/-- The slice `J ↦ Ĝ₀(J, ρ̃)` of the polar average is holomorphic on `D(J₀, s₁/2)`. -/
theorem p11_dev_G0_diff {Fast : P11FastData n} {eps : ℝ} (hF : P11FastSpec C eps Fast)
    (hrz0 : 0 < C.rz) (ρ : P11CVec n) (hρ : ‖ρ‖ < Real.pi * (C.rz / 2) ^ 2) :
    DifferentiableOn ℂ (fun (J : P11CVec n) (_ : Fin 1) => p11PolarAverage Fast.G (J, ρ))
      (ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2)) := by
  obtain ⟨-, -, -, -, hGd, -⟩ := hF
  have hr : 0 < C.rz / 2 := by positivity
  have hdiff := p11PolarAverage_differentiableOn (isOpen_ball (x := KAM.realInclusion n C.J0)
    (ε := p11s1 C eps / 2)) hr hGd
  refine differentiableOn_pi.2 fun _ => ?_
  exact hdiff.comp (by fun_prop : DifferentiableOn ℂ (fun J : P11CVec n => (J, ρ)) _)
    (fun J' hJ' => ⟨hJ', mem_ball_zero_iff.2 hρ⟩)

/-- Pure `J` partials of `h₀` at a point of the Cauchy region (formula 1 of the spec):
`∂^{(α,0)} h₀ = ∂^α C.h + ε ∂^α Ĝ₀`. -/
theorem p11_dev_J (hC : P11SecularSpec D C) {Fast : P11FastData n} {nu eps c : ℝ}
    {A : P11SlowData n} (hnu : 1 ≤ nu) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hF : P11FastSpec C eps Fast) (hA : P11SlowSpecOf C Fast nu eps c A)
    (hzs : 3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16)
    (h5 : 5 * eps ≤ p11s2 C nu eps) (α : Fin n → ℕ) (J ρ : P11CVec n)
    (hJ : ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4)
    (hρ : ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4) :
    p11PartialVec (Fin.append α (0 : Fin n → ℕ)) (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.h0 I)
        (Fin.append J ρ) =
      p11PartialVec α (fun (J : P11CVec n) (_ : Fin 1) => C.h J) J +
        (eps : ℂ) • p11PartialVec α
          (fun (J : P11CVec n) (_ : Fin 1) => p11PolarAverage Fast.G (J, ρ)) J := by
  obtain ⟨hK, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  obtain ⟨-, hf1, -, -, -, -, hh0d, -⟩ := hA
  obtain ⟨-, -, -, -, hhd, -⟩ := id hC
  have hspec := p11s2_spec hC hK
  have hs1r := p11s1_le C eps
  have hπ := Real.pi_gt_three
  set V := p11Box (p11DevCenter C eps) (p11s2 C nu eps) (Real.pi * eps) with hV
  have hVo : IsOpen V := p11_dev_box_isOpen _ _ _
  have hP : (Fin.append J ρ : P11CVec (n + n)) ∈ V :=
    p11_dev_mem_box J ρ (by linarith) (by nlinarith) hJ hρ
  have hh0v : DifferentiableOn ℂ (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.h0 I) V :=
    differentiableOn_pi.2 fun _ => hh0d
  have key := p11_partial_slice hVo hh0v ρ α hP
  beta_reduce at key
  rw [← key]
  -- the open set on which the slice is the sum
  set U1 : Set (P11CVec n) := {J' | (Fin.append J' ρ : P11CVec (n + n)) ∈ V} ∩
    ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) with hU1
  have hcont : Continuous fun J' : P11CVec n => (Fin.append J' ρ : P11CVec (n + n)) := by
    refine continuous_pi fun i => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp <;> fun_prop
  have hU1o : IsOpen U1 := (hVo.preimage hcont).inter isOpen_ball
  have hJ1 : J ∈ U1 := by
    refine ⟨hP, ?_⟩
    rw [mem_ball_iff_norm]; linarith
  have hρs := p11_dev_rho_norm heps hrz0 hzs hρ
  have hG := p11_dev_G0_diff hF hrz0 ρ hρs
  have hcont' : Continuous fun J' : P11CVec n => (Fin.append J' ρ : P11CVec (n + n)) := hcont
  have hEq : EqOn (fun (J' : P11CVec n) (_ : Fin 1) => A.h0 (Fin.append J' ρ))
      ((fun (J' : P11CVec n) (_ : Fin 1) => C.h J') + fun (J' : P11CVec n) (_ : Fin 1) =>
        (eps : ℂ) * p11PolarAverage Fast.G (J', ρ)) U1 := by
    intro J' hJ'
    have := hf1 _ hJ'.1
    funext x
    simpa using this
  have hCh : DifferentiableOn ℂ (fun (J' : P11CVec n) (_ : Fin 1) => C.h J') U1 :=
    (differentiableOn_pi.2 fun _ => hhd).mono fun J' hJ' => by
      have := hJ'.2
      rw [mem_ball_iff_norm] at this ⊢
      linarith
  have hGU : DifferentiableOn ℂ (fun (J' : P11CVec n) (_ : Fin 1) => p11PolarAverage Fast.G (J', ρ))
      U1 := hG.mono fun J' hJ' => hJ'.2
  have hGe : DifferentiableOn ℂ (fun (J' : P11CVec n) (_ : Fin 1) =>
      (eps : ℂ) * p11PolarAverage Fast.G (J', ρ)) U1 :=
    differentiableOn_pi.2 fun _ => (differentiableOn_const _).mul (differentiableOn_pi.1 hGU 0)
  rw [p11_partial_congr hU1o hEq α hJ1, p11_partial_add hU1o hCh hGe α hJ1]
  have hcl := p11_partial_clm hU1o hGU ((eps : ℂ) • ContinuousLinearMap.id ℂ (P11CVec 1)) α hJ1
  simp only [Pi.add_apply]
  congr 1

/-- The slow box `V` lies in the domain of `Z`. -/
theorem p11_dev_V_sub_Z {nu eps : ℝ}
    (hC : P11SecularSpec D C) (hnu : 1 ≤ nu) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hzs : 3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16) :
    p11Box (p11DevCenter C eps) (p11s2 C nu eps) (Real.pi * eps) ⊆
      {I : P11CVec (n + n) |
        ‖(fun i : Fin n => I (Fin.castAdd n i)) - KAM.realInclusion n C.J0‖ < p11s1 C eps / 2 ∧
        ‖(fun i : Fin n => I (Fin.natAdd n i))‖ < Real.pi * C.rz ^ 2 / 16} := by
  obtain ⟨hK, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  obtain ⟨-, -, -, -, -, -, -, hrz0, -, -⟩ := fast_consts hC
  have hspec := p11s2_spec hC hK
  have hπ := Real.pi_gt_three
  intro I hI
  obtain ⟨hI1, hI2⟩ := hI
  refine ⟨?_, ?_⟩
  · refine (pi_norm_lt_iff (by linarith)).2 fun i => ?_
    have := hI1 i
    simp only [Fin.append_left, Pi.sub_apply] at this ⊢
    linarith
  · refine (pi_norm_lt_iff (by positivity)).2 fun i => ?_
    have := hI2 i
    have h2 := norm_le_norm_add_norm_sub' (I (Fin.natAdd n i)) (2 * Real.pi * eps : ℂ)
    have h3 : ‖(2 * Real.pi * eps : ℂ)‖ = 2 * Real.pi * eps := by
      rw [show (2 * Real.pi * eps : ℂ) = ((2 * Real.pi * eps : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    simp only [Fin.append_right] at this h2
    linarith

theorem p11_dev_Z_open (C : P11SecularData n) (r1 r2 : ℝ) :
    IsOpen {I : P11CVec (n + n) |
      ‖(fun i : Fin n => I (Fin.castAdd n i)) - KAM.realInclusion n C.J0‖ < r1 ∧
        ‖(fun i : Fin n => I (Fin.natAdd n i))‖ < r2} := by
  have c1 : Continuous fun I : P11CVec (n + n) => (fun i : Fin n => I (Fin.castAdd n i)) :=
    continuous_pi fun i => continuous_apply _
  have c2 : Continuous fun I : P11CVec (n + n) => (fun i : Fin n => I (Fin.natAdd n i)) :=
    continuous_pi fun i => continuous_apply _
  exact (isOpen_lt (c1.sub continuous_const).norm continuous_const).inter
    (isOpen_lt c2.norm continuous_const)

/-- The `ρ̃_k`-derivative of `h₀` on `V` (formula 2 of the spec). -/
theorem p11_dev_h0_rho {Fast : P11FastData n} {nu eps c : ℝ} {A : P11SlowData n}
    (hC : P11SecularSpec D C) (hnu : 1 ≤ nu) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hA : P11SlowSpecOf C Fast nu eps c A)
    (hzs : 3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16) (k : Fin n)
    {I : P11CVec (n + n)}
    (hI : I ∈ p11Box (p11DevCenter C eps) (p11s2 C nu eps) (Real.pi * eps)) :
    fderiv ℂ A.h0 I (Pi.single (Fin.natAdd n k) 1) =
      (eps : ℂ) * ((2 * Real.pi : ℂ)⁻¹ * C.Omega (fun i : Fin n => I (Fin.castAdd n i)) k +
        fderiv ℂ A.Z I (Pi.single (Fin.natAdd n k) 1)) := by
  obtain ⟨-, -, hf2, hZd, -, -, hh0d, -⟩ := hA
  have hVo := p11_dev_box_isOpen (p11DevCenter C eps) (p11s2 C nu eps) (Real.pi * eps)
  have hIZ := p11_dev_V_sub_Z (nu := nu) (eps := eps) hC hnu heps hεM hzs hI
  have hZo := p11_dev_Z_open C (p11s1 C eps / 2) (Real.pi * C.rz ^ 2 / 16)
  have hZI : DifferentiableAt ℂ A.Z I := hZd.differentiableAt (hZo.mem_nhds hIZ)
  have hh0I : DifferentiableAt ℂ A.h0 I := hh0d.differentiableAt (hVo.mem_nhds hI)
  set e : P11CVec (n + n) := Pi.single (Fin.natAdd n k) 1 with he
  set φ : ℂ → P11CVec (n + n) := fun t => I + t • e with hφdef
  have hφ : HasDerivAt φ e 0 :=
    (((hasDerivAt_id (0 : ℂ)).smul_const e).const_add I).congr_deriv (by simp)
  have hφ0 : φ 0 = I := by simp [hφdef]
  have h1 : HasDerivAt (fun t => A.h0 (φ t)) (fderiv ℂ A.h0 I e) 0 := by
    have hd : HasFDerivAt A.h0 (fderiv ℂ A.h0 I) (φ 0) := by rw [hφ0]; exact hh0I.hasFDerivAt
    exact hd.comp_hasDerivAt (0 : ℂ) hφ
  have h2 : HasDerivAt (fun t => A.Z (φ t)) (fderiv ℂ A.Z I e) 0 := by
    have hd : HasFDerivAt A.Z (fderiv ℂ A.Z I) (φ 0) := by rw [hφ0]; exact hZI.hasFDerivAt
    exact hd.comp_hasDerivAt (0 : ℂ) hφ
  set w : ℂ := (2 * Real.pi : ℂ)⁻¹ * C.Omega (fun i : Fin n => I (Fin.castAdd n i)) k with hw
  set S : ℂ := C.C (fun i : Fin n => I (Fin.castAdd n i)) +
    ∑ i : Fin n, C.Omega (fun j : Fin n => I (Fin.castAdd n j)) i / (2 * Real.pi) *
      I (Fin.natAdd n i) with hS
  set K0 : ℂ := C.h (fun i : Fin n => I (Fin.castAdd n i)) with hK0
  have hg : HasDerivAt (fun t : ℂ => K0 + (eps : ℂ) * (S + t * w + A.Z (φ t)))
      ((eps : ℂ) * (w + fderiv ℂ A.Z I e)) 0 := by
    have h3 : HasDerivAt (fun t : ℂ => S + t * w + A.Z (φ t)) (w + fderiv ℂ A.Z I e) 0 :=
      ((((hasDerivAt_id (0 : ℂ)).mul_const w).const_add S).add h2).congr_deriv (by simp)
    simpa using (h3.const_mul (eps : ℂ)).const_add K0
  have hφc : Continuous φ := by simp only [hφdef]; fun_prop
  have hev : ∀ᶠ t in nhds (0 : ℂ), A.h0 (φ t) = K0 + (eps : ℂ) * (S + t * w + A.Z (φ t)) := by
    have hmem : ∀ᶠ t in nhds (0 : ℂ), φ t ∈ p11Box (p11DevCenter C eps) (p11s2 C nu eps)
        (Real.pi * eps) :=
      hφc.continuousAt.preimage_mem_nhds (by rw [hφ0]; exact hVo.mem_nhds hI)
    filter_upwards [hmem] with t ht
    rw [hf2 _ ht]
    have hJ : (fun i : Fin n => φ t (Fin.castAdd n i)) = fun i : Fin n => I (Fin.castAdd n i) := by
      funext i
      have hne : (Fin.castAdd n i : Fin (n + n)) ≠ Fin.natAdd n k := fun h => by
        have := congrArg Fin.val h
        simp at this
        have := i.isLt
        omega
      show I (Fin.castAdd n i) + t * (Pi.single (Fin.natAdd n k) 1 : P11CVec (n + n))
        (Fin.castAdd n i) = _
      rw [Pi.single_eq_of_ne hne]; simp
    have hρ : ∀ i : Fin n, φ t (Fin.natAdd n i) =
        I (Fin.natAdd n i) + t * (if i = k then 1 else 0) := by
      intro i
      simp [hφdef, he, Pi.single_apply, eq_comm]
    rw [hJ]
    simp only [hρ, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [hS, hK0, hw]
    ring
  have := h1.unique (hg.congr_of_eventuallyEq hev)
  rw [this]

theorem p11_dev_step_const {N : ℕ} {φ : P11CVec N → ℂ} {I : P11CVec N} (c' : Fin N)
    (h : DifferentiableAt ℂ φ I) :
    p11Step c' (fun (I : P11CVec N) (_ : Fin 1) => φ I) I =
      fun _ => fderiv ℂ φ I (Pi.single c' 1) := by
  unfold p11Step
  rw [fderiv_pi (fun _ => h)]
  rfl

/-- Partials of `h₀` with a `ρ̃`-index, at a point of the Cauchy region (formula 2 of the spec). -/
theorem p11_dev_rho (hC : P11SecularSpec D C) {Fast : P11FastData n} {nu eps c : ℝ}
    {A : P11SlowData n} (hnu : 1 ≤ nu) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hA : P11SlowSpecOf C Fast nu eps c A)
    (hzs : 3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16)
    (h5 : 5 * eps ≤ p11s2 C nu eps) (k : Fin n) (β : Fin (n + n) → ℕ) (J ρ : P11CVec n)
    (hJ : ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4)
    (hρ : ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4) :
    p11PartialVec (β + Pi.single (Fin.natAdd n k) 1)
        (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.h0 I) (Fin.append J ρ) =
      (eps : ℂ) • (p11PartialVec β (fun (I : P11CVec (n + n)) (_ : Fin 1) =>
          (2 * Real.pi : ℂ)⁻¹ * C.Omega (fun i : Fin n => I (Fin.castAdd n i)) k) (Fin.append J ρ) +
        p11PartialVec β (p11Step (Fin.natAdd n k) (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.Z I))
          (Fin.append J ρ)) := by
  obtain ⟨hK, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  obtain ⟨-, -, -, hrC0, -, -, -, hrz0, -, -⟩ := fast_consts hC
  have hspec := p11s2_spec hC hK
  have hs1r := p11s1_le C eps
  have hπ := Real.pi_gt_three
  obtain ⟨-, -, -, hZd, -, -, hh0d, -⟩ := id hA
  obtain ⟨-, -, ⟨-, hΩd⟩, -, -, -⟩ := id hC
  have hVo := p11_dev_box_isOpen (p11DevCenter C eps) (p11s2 C nu eps) (Real.pi * eps)
  have hP : (Fin.append J ρ : P11CVec (n + n)) ∈
      p11Box (p11DevCenter C eps) (p11s2 C nu eps) (Real.pi * eps) :=
    p11_dev_mem_box J ρ (by linarith) (by nlinarith) hJ hρ
  have hsub := p11_dev_V_sub_Z (nu := nu) (eps := eps) hC hnu heps hεM hzs
  have hZo := p11_dev_Z_open C (p11s1 C eps / 2) (Real.pi * C.rz ^ 2 / 16)
  have hHv : DifferentiableOn ℂ (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.h0 I)
      (p11Box (p11DevCenter C eps) (p11s2 C nu eps) (Real.pi * eps)) :=
    differentiableOn_pi.2 fun _ => hh0d
  have hZv : DifferentiableOn ℂ (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.Z I)
      {I : P11CVec (n + n) |
        ‖(fun i : Fin n => I (Fin.castAdd n i)) - KAM.realInclusion n C.J0‖ < p11s1 C eps / 2 ∧
          ‖(fun i : Fin n => I (Fin.natAdd n i))‖ < Real.pi * C.rz ^ 2 / 16} :=
    differentiableOn_pi.2 fun _ => hZd
  have hstZ := p11Step_differentiableOn hZo hZv (Fin.natAdd n k)
  have hOm : DifferentiableOn ℂ (fun (I : P11CVec (n + n)) (_ : Fin 1) =>
      (2 * Real.pi : ℂ)⁻¹ * C.Omega (fun i : Fin n => I (Fin.castAdd n i)) k)
      (p11Box (p11DevCenter C eps) (p11s2 C nu eps) (Real.pi * eps)) := by
    refine differentiableOn_pi.2 fun _ => (differentiableOn_const _).mul ?_
    have h1 : DifferentiableOn ℂ (fun I : P11CVec (n + n) => C.Omega (fun i : Fin n =>
        I (Fin.castAdd n i)) k) {I | (fun i : Fin n => I (Fin.castAdd n i)) ∈
          ball (KAM.realInclusion n C.J0) (2 * C.rC)} := by
      refine (differentiableOn_pi.1 hΩd k).comp (by fun_prop) fun I hI => hI
    refine h1.mono fun I hI => ?_
    have := (hsub hI).1
    show (fun i : Fin n => I (Fin.castAdd n i)) ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC)
    rw [mem_ball_iff_norm]
    linarith
  have hEq : EqOn (p11Step (Fin.natAdd n k) (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.h0 I))
      ((eps : ℂ) • ((fun (I : P11CVec (n + n)) (_ : Fin 1) =>
          (2 * Real.pi : ℂ)⁻¹ * C.Omega (fun i : Fin n => I (Fin.castAdd n i)) k) +
        p11Step (Fin.natAdd n k) (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.Z I)))
      (p11Box (p11DevCenter C eps) (p11s2 C nu eps) (Real.pi * eps)) := by
    intro I hI
    have hh0I : DifferentiableAt ℂ A.h0 I := hh0d.differentiableAt (hVo.mem_nhds hI)
    have hZI : DifferentiableAt ℂ A.Z I := hZd.differentiableAt (hZo.mem_nhds (hsub hI))
    rw [p11_dev_step_const _ hh0I, p11_dev_h0_rho hC hnu heps hεM hA hzs k hI]
    funext x
    rw [Pi.smul_apply, Pi.add_apply, p11_dev_step_const _ hZI]
    simp
  have hsum : DifferentiableOn ℂ ((fun (I : P11CVec (n + n)) (_ : Fin 1) =>
      (2 * Real.pi : ℂ)⁻¹ * C.Omega (fun i : Fin n => I (Fin.castAdd n i)) k) +
        p11Step (Fin.natAdd n k) (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.Z I))
      (p11Box (p11DevCenter C eps) (p11s2 C nu eps) (Real.pi * eps)) :=
    hOm.add (hstZ.mono hsub)
  rw [← p11_partial_step hVo hHv β (Fin.natAdd n k) hP, p11_partial_congr hVo hEq β hP]
  have h1 := p11_partial_clm hVo hsum ((eps : ℂ) • ContinuousLinearMap.id ℂ (P11CVec 1)) β hP
  have h2 := p11_partial_add hVo hOm (hstZ.mono hsub) β hP
  change p11PartialVec β (fun x => ((eps : ℂ) • ContinuousLinearMap.id ℂ (P11CVec 1))
    (((fun (I : P11CVec (n + n)) (_ : Fin 1) =>
      (2 * Real.pi : ℂ)⁻¹ * C.Omega (fun i : Fin n => I (Fin.castAdd n i)) k) +
        p11Step (Fin.natAdd n k) (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.Z I)) x)) _ = _
  rw [h1]
  simp only [smul_apply, ContinuousLinearMap.id_apply]
  rw [h2]
  rfl

/-- Projection of `(J, ρ̃)` to `J`. -/
def p11DevProj (n : ℕ) : P11CVec (n + n) →L[ℂ] P11CVec n :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castAdd n i)

theorem p11DevProj_apply (I : P11CVec (n + n)) : p11DevProj n I = fun i => I (Fin.castAdd n i) :=
  rfl

private theorem p11DevProj_natAdd (i : Fin n) : p11DevProj n (Pi.single (Fin.natAdd n i) 1) = 0 := by
  funext j
  have hne : (Fin.castAdd n j : Fin (n + n)) ≠ Fin.natAdd n i := fun h => by
    have := congrArg Fin.val h
    simp at this
    have := j.isLt
    omega
  show (Pi.single (Fin.natAdd n i) 1 : P11CVec (n + n)) (Fin.castAdd n j) = 0
  rw [Pi.single_eq_of_ne hne]

private theorem devPartial_zero_foldl {N m : ℕ} :
    ∀ L : List (Fin N), L.foldl (fun g i => p11Step i g) (fun _ : P11CVec N => (0 : P11CVec m)) =
      fun _ => 0 := by
  intro L
  induction L with
  | nil => rfl
  | cons a L ih =>
    have : p11Step a (fun _ : P11CVec N => (0 : P11CVec m)) = fun _ => 0 := by
      funext x; simp [p11Step]
    simp only [List.foldl_cons, this]
    exact ih

/-- A function of `J` only has no partial derivative with a `ρ̃`-index. -/
theorem p11_partial_proj_rho {U : Set (P11CVec n)} {f : P11CVec n → P11CVec m}
    (hf : DifferentiableOn ℂ f U) (β : Fin (n + n) → ℕ) (i : Fin n) {P : P11CVec (n + n)}
    (hP : p11DevProj n P ∈ U) (hU : IsOpen U) :
    p11PartialVec (β + Pi.single (Fin.natAdd n i) 1) (fun I => f (p11DevProj n I)) P = 0 := by
  have hUo : IsOpen (p11DevProj n ⁻¹' U) := hU.preimage (p11DevProj n).continuous
  have hF : DifferentiableOn ℂ (fun I => f (p11DevProj n I)) (p11DevProj n ⁻¹' U) :=
    hf.comp (p11DevProj n).differentiableOn fun x hx => hx
  rw [← p11_partial_step hUo hF β (Fin.natAdd n i) hP]
  have h0 : EqOn (p11Step (Fin.natAdd n i) (fun I => f (p11DevProj n I))) (fun _ => 0)
      (p11DevProj n ⁻¹' U) := by
    intro x hx
    have hfx := hf.differentiableAt (hU.mem_nhds hx)
    have := (hfx.hasFDerivAt.comp x (p11DevProj n).hasFDerivAt).fderiv
    simp only [p11Step]
    rw [show (fun I => f (p11DevProj n I)) = f ∘ (p11DevProj n) from rfl, this,
      ContinuousLinearMap.comp_apply, p11DevProj_natAdd, map_zero]
  rw [p11_partial_congr hUo h0 β hP]
  exact congrFun (devPartial_zero_foldl _) P

private theorem dev_prod_append (α γ : Fin n → ℕ) (f : ℕ → ℝ) :
    ∏ j : Fin (n + n), f (Fin.append α γ j) = (∏ i, f (α i)) * ∏ i, f (γ i) := by
  rw [Fin.prod_univ_add]; simp [Fin.append_left]

private theorem dev_poly_prod (α γ : Fin n → ℕ) (r1 r2 : ℝ) :
    ∏ j : Fin (n + n), p11BoxRad n n r1 r2 j ^ (Fin.append α γ j) =
      r1 ^ (∑ i, α i) * r2 ^ (∑ i, γ i) := by
  rw [Fin.prod_univ_add]
  simp [p11BoxRad, Fin.append_left, Finset.prod_pow_eq_pow_sum]

/-- The linear part of the slice `ρ ↦ (J, ρ)`: extension by zero in the `J` block. -/
private def opsExtR (n : ℕ) : P11CVec n →L[ℂ] P11CVec (n + n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Fin.append (0 : P11CVec n) v
      map_add' := fun v w => by
        funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
      map_smul' := fun a v => by
        funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp }

private theorem opsExtR_single (a : Fin n) :
    opsExtR n (Pi.single a 1) = Pi.single (Fin.natAdd n a) 1 := by
  show Fin.append (0 : P11CVec n) (Pi.single a 1) = _
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have hne : (Fin.castAdd n j : Fin (n + n)) ≠ Fin.natAdd n a := fun h => by
      have := congrArg Fin.val h
      simp at this
      have := j.isLt
      omega
    simp only [Fin.append_left]
    rw [Pi.single_eq_of_ne hne]; rfl
  · simp [Pi.single_apply, Fin.ext_iff]

/-- The `ρ̃_k`-derivative of `Z` is the derivative of the slice `ρ ↦ Z (J, ρ)`. -/
theorem p11_dev_Z_slice {Z : P11CVec (n + n) → ℂ} (J ρ : P11CVec n) (k : Fin n)
    (hZ : DifferentiableAt ℂ Z (Fin.append J ρ)) :
    fderiv ℂ (fun ρ' : P11CVec n => Z (Fin.append J ρ')) ρ (Pi.single k 1) =
      fderiv ℂ Z (Fin.append J ρ) (Pi.single (Fin.natAdd n k) 1) := by
  have hκ : HasFDerivAt (fun ρ' : P11CVec n => (Fin.append J ρ' : P11CVec (n + n))) (opsExtR n) ρ := by
    have h : (fun ρ' : P11CVec n => (Fin.append J ρ' : P11CVec (n + n))) =
        fun ρ' => opsExtR n ρ' + Fin.append J (0 : P11CVec n) := by
      funext ρ' i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [opsExtR]
    rw [h]
    exact (opsExtR n).hasFDerivAt.add_const _
  have := (hZ.hasFDerivAt.comp ρ hκ).fderiv
  rw [show (fun ρ' : P11CVec n => Z (Fin.append J ρ')) =
    Z ∘ (fun ρ' : P11CVec n => (Fin.append J ρ' : P11CVec (n + n))) from rfl, this]
  simp [opsExtR_single]

/-- Mixed Cauchy estimate for the `ρ̃_k`-derivative `∂_{ρ̃_k} Z` on the polydisc of radii `s₂/2`
(in `J`) and `ε` (in `ρ̃`) around a point of the Cauchy region; the supremum is the `α = 0` case of
the spec bound on `∂_ρ Z`. -/
theorem p11_dev_Z_jet (hC : P11SecularSpec D C) {Fast : P11FastData n} {nu eps c : ℝ}
    {A : P11SlowData n} (hnu : 1 ≤ nu) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hA : P11SlowSpecOf C Fast nu eps c A)
    (hzs : 3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16) (k : Fin n) (α γ : Fin n → ℕ)
    (J ρ : P11CVec n) (hJ : ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4)
    (hρ : ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4) :
    ‖p11PartialVec (Fin.append α γ)
        (p11Step (Fin.natAdd n k) (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.Z I))
        (Fin.append J ρ)‖ ≤
      (∏ i, ((α i).factorial : ℝ)) * (∏ i, ((γ i).factorial : ℝ)) *
        (c * (eps + p11eta1 C eps)) / ((p11s2 C nu eps / 2) ^ (∑ i, α i) * eps ^ (∑ i, γ i)) := by
  obtain ⟨hK, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  have hspec := p11s2_spec hC hK
  have hπ := Real.pi_gt_three
  obtain ⟨-, -, -, hZd, hZj, -⟩ := id hA
  have hVo := p11_dev_box_isOpen (p11DevCenter C eps) (p11s2 C nu eps) (Real.pi * eps)
  have hsub := p11_dev_V_sub_Z (nu := nu) (eps := eps) hC hnu heps hεM hzs
  have hZo := p11_dev_Z_open C (p11s1 C eps / 2) (Real.pi * C.rz ^ 2 / 16)
  have hZv : DifferentiableOn ℂ (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.Z I)
      {I : P11CVec (n + n) |
        ‖(fun i : Fin n => I (Fin.castAdd n i)) - KAM.realInclusion n C.J0‖ < p11s1 C eps / 2 ∧
          ‖(fun i : Fin n => I (Fin.natAdd n i))‖ < Real.pi * C.rz ^ 2 / 16} :=
    differentiableOn_pi.2 fun _ => hZd
  have hg := (p11Step_differentiableOn hZo hZv (Fin.natAdd n k)).mono hsub
  have hR : ∀ j, 0 < p11BoxRad n n (p11s2 C nu eps / 2) eps j := fun j => by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [p11BoxRad] <;> positivity
  have hcl : {y : P11CVec (n + n) | ∀ j, ‖y j - Fin.append J ρ j‖ ≤
      p11BoxRad n n (p11s2 C nu eps / 2) eps j} ⊆
      p11Box (p11DevCenter C eps) (p11s2 C nu eps) (Real.pi * eps) := by
    intro y hy
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have h1 := hy (Fin.castAdd n i)
      simp only [p11BoxRad, Fin.append_left] at h1 ⊢
      have h2 : ‖J i - KAM.realInclusion n C.J0 i‖ < p11s2 C nu eps / 4 :=
        lt_of_le_of_lt (by simpa using norm_le_pi_norm (J - KAM.realInclusion n C.J0) i) hJ
      have := norm_sub_le_norm_sub_add_norm_sub (y (Fin.castAdd n i)) (J i)
        (KAM.realInclusion n C.J0 i)
      linarith
    · have h1 := hy (Fin.natAdd n i)
      simp only [p11BoxRad, Fin.append_right] at h1 ⊢
      have h2 : ‖ρ i - (2 * Real.pi * eps : ℂ)‖ < 5 * eps / 4 :=
        lt_of_le_of_lt (norm_le_pi_norm (ρ - fun _ : Fin n => (2 * Real.pi * eps : ℂ)) i) hρ
      have := norm_sub_le_norm_sub_add_norm_sub (y (Fin.natAdd n i)) (ρ i) (2 * Real.pi * eps : ℂ)
      nlinarith
  have hM : ∀ w ∈ p11Box (p11DevCenter C eps) (p11s2 C nu eps) (Real.pi * eps),
      ‖p11Step (Fin.natAdd n k) (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.Z I) w‖ ≤
        c * (eps + p11eta1 C eps) := by
    intro w hw
    have hwZ : DifferentiableAt ℂ A.Z w := hZd.differentiableAt (hZo.mem_nhds (hsub hw))
    rw [p11_dev_step_const _ hwZ, pi_norm_const]
    obtain ⟨hw1, hw2⟩ := hw
    set J' : P11CVec n := fun i => w (Fin.castAdd n i) with hJ'
    set ρ' : P11CVec n := fun i => w (Fin.natAdd n i) with hρ'
    have hwe : (Fin.append J' ρ' : P11CVec (n + n)) = w := Fin.append_castAdd_natAdd (f := w)
    have hJn : ‖J' - KAM.realInclusion n C.J0‖ < p11s1 C eps / 4 := by
      refine (pi_norm_lt_iff (by linarith)).2 fun i => ?_
      have := hw1 i
      simp only [Fin.append_left, Pi.sub_apply] at this ⊢
      linarith
    have hρn : ‖ρ' - (fun _ => (2 * Real.pi * eps : ℂ))‖ < Real.pi * eps := by
      refine (pi_norm_lt_iff (by positivity)).2 fun i => ?_
      have := hw2 i
      simp only [Fin.append_right] at this
      exact this
    have h1 := hZj 0 J' hJn ρ' hρn
    rw [p11PartialVec_zero] at h1
    have h2 := (norm_le_pi_norm _ k).trans h1
    have h3 := p11_dev_Z_slice (Z := A.Z) J' ρ' k (by rw [hwe]; exact hwZ)
    rw [hwe] at h3
    rw [← h3]
    simpa using h2
  have h := p11PartialVec_norm_le_poly hVo hg hR hcl hM (Fin.append α γ)
  rw [dev_prod_append α γ (fun k => (k.factorial : ℝ)), dev_poly_prod] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- `h = h₀ + g₂` as a one-component vector function. -/
def p11DevH (A : P11SlowData n) : P11CVec (n + n) → P11CVec 1 := fun I _ => A.h0 I + A.g2 I

theorem p11DevH_eq (A : P11SlowData n) :
    p11DevH A = (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.h0 I) +
      fun (I : P11CVec (n + n)) (_ : Fin 1) => A.g2 I := rfl

/-- Cauchy bound of `∂^α Ĝ₀` (step pr-in (i)). -/
def p11DevA (C : P11SecularData n) (eps : ℝ) (α : Fin n → ℕ) : ℝ :=
  (∏ i, ((α i).factorial : ℝ)) * (C.MF + p11eta1 C eps) / (p11s1 C eps / 4) ^ (∑ i, α i)

/-- Cauchy bound of `∂_J^α ∂_ρ̃^γ g₂` (step pr-in (iii)). -/
def p11DevG (C : P11SecularData n) (nu eps c : ℝ) (α γ : Fin n → ℕ) : ℝ :=
  (∏ i, ((α i).factorial : ℝ)) * (∏ i, ((γ i).factorial : ℝ)) *
    (c * eps ^ 3 * Real.log (1 / eps) ^ (5 * C.tau + 2)) /
    ((p11s2 C nu eps / 4) ^ (∑ i, α i) * (eps / 4) ^ (∑ i, γ i))

/-- Cauchy bound of `∂_J^α ∂_ρ̃^γ ∂_ρ̃ Z` (spec bound on `∂_ρ Z`, polydisc `s₂/2`, `ε`). -/
def p11DevZ (C : P11SecularData n) (nu eps c : ℝ) (α γ : Fin n → ℕ) : ℝ :=
  (∏ i, ((α i).factorial : ℝ)) * (∏ i, ((γ i).factorial : ℝ)) * (c * (eps + p11eta1 C eps)) /
    ((p11s2 C nu eps / 2) ^ (∑ i, α i) * eps ^ (∑ i, γ i))

theorem p11_dev_Vh_sub {C : P11SecularData n} {nu eps : ℝ} (hs2 : 0 ≤ p11s2 C nu eps)
    (heps : 0 ≤ eps) :
    p11Box (p11DevCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2) ⊆
      p11Box (p11DevCenter C eps) (p11s2 C nu eps) (Real.pi * eps) := by
  have hπ := Real.pi_pos
  intro I ⟨h1, h2⟩
  exact ⟨fun i => lt_of_lt_of_le (h1 i) (by linarith), fun i => lt_of_lt_of_le (h2 i)
    (by nlinarith)⟩

/-- Pure `J` deviation: `∂^{(α,0)} h = ∂^α C.h + ε ∂^α Ĝ₀ + ∂^{(α,0)} g₂`. -/
theorem p11_dev_J_bound (hC : P11SecularSpec D C) {Fast : P11FastData n} {nu eps c : ℝ}
    {A : P11SlowData n} (hnu : 1 ≤ nu) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hF : P11FastSpec C eps Fast) (hA : P11SlowSpecOf C Fast nu eps c A)
    (hzs : 3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16)
    (h5 : 5 * eps ≤ p11s2 C nu eps) (α : Fin n → ℕ) (J ρ : P11CVec n)
    (hJ : ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4)
    (hρ : ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4) :
    ‖p11PartialVec (Fin.append α (0 : Fin n → ℕ)) (p11DevH A) (Fin.append J ρ) -
        p11PartialVec α (fun (J : P11CVec n) (_ : Fin 1) => C.h J) J‖ ≤
      eps * p11DevA C eps α + p11DevG C nu eps c α 0 := by
  obtain ⟨hK, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  obtain ⟨-, -, -, hrC0, -, -, -, hrz0, -, -⟩ := fast_consts hC
  have hspec := p11s2_spec hC hK
  have hπ := Real.pi_gt_three
  obtain ⟨-, -, -, -, -, -, hh0d, hdg, -⟩ := id hA
  set Vh := p11Box (p11DevCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2) with hVh
  have hVho : IsOpen Vh := p11_dev_box_isOpen _ _ _
  have hP : (Fin.append J ρ : P11CVec (n + n)) ∈ Vh :=
    p11_dev_mem_box J ρ (by linarith) (by nlinarith) hJ hρ
  have hsub := p11_dev_Vh_sub (C := C) (nu := nu) hs2.le heps.le
  have hh0 : DifferentiableOn ℂ (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.h0 I) Vh :=
    (differentiableOn_pi.2 fun _ => hh0d).mono hsub
  have hg2 : DifferentiableOn ℂ (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.g2 I) Vh :=
    differentiableOn_pi.2 fun _ => hdg
  rw [p11DevH_eq, p11_partial_add hVho hh0 hg2 _ hP]
  have hid := p11_dev_J hC hnu heps hεM hF hA hzs h5 α J ρ hJ hρ
  have hhh : p11PartialVec (Fin.append α (0 : Fin n → ℕ))
      (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.h0 I) (Fin.append J ρ) =
      p11PartialVec α (fun (J : P11CVec n) (_ : Fin 1) => C.h J) J +
        (eps : ℂ) • p11PartialVec α
          (fun (J : P11CVec n) (_ : Fin 1) => p11PolarAverage Fast.G (J, ρ)) J := hid
  simp only [Pi.add_apply, hhh]
  have hG0 := p11_prin_G0_jet hC heps hεM hF α J ρ
    (by linarith) (p11_dev_rho_norm heps hrz0 hzs hρ)
  have hg := p11_prin_g2_jet hs2 heps hA α (0 : Fin n → ℕ) J ρ hJ hρ
  calc ‖p11PartialVec α (fun (J : P11CVec n) (_ : Fin 1) => C.h J) J +
          (eps : ℂ) • p11PartialVec α
            (fun (J : P11CVec n) (_ : Fin 1) => p11PolarAverage Fast.G (J, ρ)) J +
          p11PartialVec (Fin.append α (0 : Fin n → ℕ))
            (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.g2 I) (Fin.append J ρ) -
        p11PartialVec α (fun (J : P11CVec n) (_ : Fin 1) => C.h J) J‖
      = ‖(eps : ℂ) • p11PartialVec α
            (fun (J : P11CVec n) (_ : Fin 1) => p11PolarAverage Fast.G (J, ρ)) J +
          p11PartialVec (Fin.append α (0 : Fin n → ℕ))
            (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.g2 I) (Fin.append J ρ)‖ := by
        congr 1; abel
    _ ≤ eps * p11DevA C eps α + p11DevG C nu eps c α 0 := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg heps.le]
          exact mul_le_mul_of_nonneg_left hG0 heps.le
        · refine hg.trans (le_of_eq ?_)
          simp [p11DevG]

theorem p11_dev_append_add (α γ : Fin n → ℕ) (k : Fin n) :
    (Fin.append α γ : Fin (n + n) → ℕ) + Pi.single (Fin.natAdd n k) 1 =
      Fin.append α (γ + Pi.single k 1) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have hne : (Fin.castAdd n j : Fin (n + n)) ≠ Fin.natAdd n k := fun h => by
      have := congrArg Fin.val h
      simp at this
      have := j.isLt
      omega
    simp only [Pi.add_apply, Fin.append_left]
    rw [Pi.single_eq_of_ne hne, add_zero]
  · by_cases h : j = k
    · subst h
      simp only [Pi.add_apply, Fin.append_right, Pi.single_eq_same]
    · have hne : (Fin.natAdd n j : Fin (n + n)) ≠ Fin.natAdd n k := fun h' => h (by
        have := congrArg Fin.val h'
        simp at this
        exact Fin.ext this)
      simp only [Pi.add_apply, Fin.append_right]
      rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne h]

/-- Deviation of a partial with a `ρ̃`-index:
`∂^{β'+e_k} h = ε ∂^{β'} Ω̃_k + ε ∂^{β'} ∂_{ρ̃_k} Z + ∂^{β'+e_k} g₂`. -/
theorem p11_dev_rho_bound (hC : P11SecularSpec D C) {Fast : P11FastData n} {nu eps c : ℝ}
    {A : P11SlowData n} (hnu : 1 ≤ nu) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hA : P11SlowSpecOf C Fast nu eps c A)
    (hzs : 3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16)
    (h5 : 5 * eps ≤ p11s2 C nu eps) (k : Fin n) (α γ : Fin n → ℕ) (J ρ : P11CVec n)
    (hJ : ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4)
    (hρ : ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4) :
    ‖p11PartialVec (Fin.append α γ + Pi.single (Fin.natAdd n k) 1) (p11DevH A)
          (Fin.append J ρ) -
        (eps : ℂ) • p11PartialVec (Fin.append α γ) (fun (I : P11CVec (n + n)) (_ : Fin 1) =>
          (2 * Real.pi : ℂ)⁻¹ * C.Omega (fun i : Fin n => I (Fin.castAdd n i)) k)
          (Fin.append J ρ)‖ ≤
      eps * p11DevZ C nu eps c α γ + p11DevG C nu eps c α (γ + Pi.single k 1) := by
  obtain ⟨hK, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  have hspec := p11s2_spec hC hK
  have hπ := Real.pi_gt_three
  obtain ⟨-, -, -, -, -, -, hh0d, hdg, -⟩ := id hA
  set Vh := p11Box (p11DevCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2) with hVh
  have hVho : IsOpen Vh := p11_dev_box_isOpen _ _ _
  have hP : (Fin.append J ρ : P11CVec (n + n)) ∈ Vh :=
    p11_dev_mem_box J ρ (by linarith) (by nlinarith) hJ hρ
  have hsub := p11_dev_Vh_sub (C := C) (nu := nu) hs2.le heps.le
  have hh0 : DifferentiableOn ℂ (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.h0 I) Vh :=
    (differentiableOn_pi.2 fun _ => hh0d).mono hsub
  have hg2 : DifferentiableOn ℂ (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.g2 I) Vh :=
    differentiableOn_pi.2 fun _ => hdg
  rw [p11DevH_eq, p11_partial_add hVho hh0 hg2 _ hP]
  have hid := p11_dev_rho hC hnu heps hεM hA hzs h5 k (Fin.append α γ) J ρ hJ hρ
  simp only [Pi.add_apply, hid]
  have hz := p11_dev_Z_jet hC hnu heps hεM hA hzs k α γ J ρ hJ hρ
  have hg := p11_prin_g2_jet hs2 heps hA α (γ + Pi.single k 1) J ρ hJ hρ
  rw [← p11_dev_append_add] at hg
  calc ‖(eps : ℂ) • (p11PartialVec (Fin.append α γ) (fun (I : P11CVec (n + n)) (_ : Fin 1) =>
            (2 * Real.pi : ℂ)⁻¹ * C.Omega (fun i : Fin n => I (Fin.castAdd n i)) k)
            (Fin.append J ρ) +
          p11PartialVec (Fin.append α γ) (p11Step (Fin.natAdd n k)
            (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.Z I)) (Fin.append J ρ)) +
        p11PartialVec (Fin.append α γ + Pi.single (Fin.natAdd n k) 1)
          (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.g2 I) (Fin.append J ρ) -
        (eps : ℂ) • p11PartialVec (Fin.append α γ) (fun (I : P11CVec (n + n)) (_ : Fin 1) =>
          (2 * Real.pi : ℂ)⁻¹ * C.Omega (fun i : Fin n => I (Fin.castAdd n i)) k)
          (Fin.append J ρ)‖
      = ‖(eps : ℂ) • p11PartialVec (Fin.append α γ) (p11Step (Fin.natAdd n k)
            (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.Z I)) (Fin.append J ρ) +
        p11PartialVec (Fin.append α γ + Pi.single (Fin.natAdd n k) 1)
          (fun (I : P11CVec (n + n)) (_ : Fin 1) => A.g2 I) (Fin.append J ρ)‖ := by
        congr 1; rw [smul_add]; abel
    _ ≤ eps * p11DevZ C nu eps c α γ + p11DevG C nu eps c α (γ + Pi.single k 1) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg heps.le]
          exact mul_le_mul_of_nonneg_left hz heps.le
        · exact hg

end Dev

end KAM.Planetary

end
