/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedFreq
public import KAM.Planetary.Preparation.PreparedData

/-!
# Closeness of the normalised frequency (P11A-P8b2, `stepP:p11:pr-c`)

`p11CloseFun C A ε ρ̃` is the complex `J`-holomorphic vector `(∂_J h - ω, ∂_ρ̃ h / ε - Ω/(2π))`
at fixed `ρ̃`, `h = h₀ + g₂`; its real part on real `J` is `ψ - ϖ`.  The partials of order
`≤ μ̄` are `≤ K (1+c) ε ℓ^Q` (the four contributions of step pr-c).
-/

@[expose] public noncomputable section
open Set Metric
open scoped BigOperators
namespace KAM.Planetary

section Close

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- `(∂_J h - ω, ∂_ρ̃ h / ε - Ω/(2π))` at fixed `ρ̃`. -/
def p11CloseFun (C : P11SecularData n) (A : P11SlowData n) (eps : ℝ) (ρt : P11CVec n) :
    P11CVec n → P11CVec (n + n) := fun J =>
  Fin.append
    (fun k => fderiv ℂ (fun I => A.h0 I + A.g2 I) (Fin.append J ρt) (Pi.single (Fin.castAdd n k) 1)
      - C.omega J k)
    (fun k => fderiv ℂ (fun I => A.h0 I + A.g2 I) (Fin.append J ρt)
      (Pi.single (Fin.natAdd n k) 1) / (eps : ℂ) - (2 * Real.pi : ℂ)⁻¹ * C.Omega J k)

theorem p11_partial_sub {N m : ℕ} {U : Set (P11CVec N)} (hU : IsOpen U) {F G : P11CVec N → P11CVec m}
    (hF : DifferentiableOn ℂ F U) (hG : DifferentiableOn ℂ G U) (α : Fin N → ℕ) {x : P11CVec N}
    (hx : x ∈ U) :
    p11PartialVec α (fun y => F y - G y) x = p11PartialVec α F x - p11PartialVec α G x := by
  set T : P11CVec m →L[ℂ] P11CVec m := (-1 : ℂ) • ContinuousLinearMap.id ℂ (P11CVec m) with hT
  have hGn : DifferentiableOn ℂ (fun y => T (G y)) U := by
    have : DifferentiableOn ℂ ((-1 : ℂ) • G) U := hG.const_smul (-1 : ℂ)
    exact this
  have h1 : (fun y => F y - G y) = F + fun y => T (G y) := by
    funext y; simp [hT, sub_eq_add_neg]
  have h2 := p11_partial_clm hU hG T α hx
  rw [h1, p11_partial_add hU hF hGn α hx]
  show p11PartialVec α F x + p11PartialVec α (fun y => T (G y)) x = _
  rw [h2]
  simp [hT, sub_eq_add_neg]

/-- The open set on which the slice at `ρ̃` of the slow box and the ball of `C` are available. -/
def p11CloseDom (C : P11SecularData n) (eps r1 : ℝ) (ρt : P11CVec n) : Set (P11CVec n) :=
  {J | (Fin.append J ρt : P11CVec (n + n)) ∈
    p11Box (p11DevCenter C eps) r1 (Real.pi * eps / 2)} ∩ ball (KAM.realInclusion n C.J0) (2 * C.rC)

theorem p11_close_dom_open (C : P11SecularData n) (eps r1 : ℝ) (ρt : P11CVec n) :
    IsOpen (p11CloseDom C eps r1 ρt) := by
  have hcont : Continuous fun J' : P11CVec n => (Fin.append J' ρt : P11CVec (n + n)) := by
    refine continuous_pi fun i => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp <;> fun_prop
  exact ((p11_dev_box_isOpen _ _ _).preimage hcont).inter isOpen_ball

theorem p11_close_append_cast (α : Fin n → ℕ) (k : Fin n) :
    (Fin.append α (0 : Fin n → ℕ) : Fin (n + n) → ℕ) + Pi.single (Fin.castAdd n k) 1 =
      Fin.append (α + Pi.single k 1) (0 : Fin n → ℕ) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · by_cases h : j = k
    · subst h; simp
    · have hne : (Fin.castAdd n j : Fin (n + n)) ≠ Fin.castAdd n k := fun h' => h (by
        have := congrArg Fin.val h'
        simp at this
        exact Fin.ext this)
      simp only [Pi.add_apply, Fin.append_left]
      rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne h]
  · have hne : (Fin.natAdd n j : Fin (n + n)) ≠ Fin.castAdd n k := fun h' => by
      have := congrArg Fin.val h'
      simp at this
      have := k.isLt
      omega
    simp only [Pi.add_apply, Fin.append_right, Pi.zero_apply]
    rw [Pi.single_eq_of_ne hne]
    rfl

theorem p11_close_Phi_diff {Fast : P11FastData n} {nu eps c : ℝ} {A : P11SlowData n}
    (hC : P11SecularSpec D C) (hs2 : 0 ≤ p11s2 C nu eps) (heps : 0 ≤ eps)
    (hA : P11SlowSpecOf C Fast nu eps c A) (ρt : P11CVec n) :
    DifferentiableOn ℂ (p11CloseFun C A eps ρt) (p11CloseDom C eps (p11s2 C nu eps / 2) ρt) := by
  obtain ⟨-, -, ⟨hωd, hΩd⟩, -⟩ := id hC
  have hHd := p11_freq_H_diff (C := C) hs2 heps hA
  have hVho := p11_dev_box_isOpen (p11DevCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2)
  have hκ : DifferentiableOn ℂ (fun J' : P11CVec n => (Fin.append J' ρt : P11CVec (n + n)))
      (p11CloseDom C eps (p11s2 C nu eps / 2) ρt) := by
    refine (differentiable_pi.2 fun i => ?_).differentiableOn
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp <;> fun_prop
  have hS : ∀ c' : Fin (n + n), DifferentiableOn ℂ
      (fun J' : P11CVec n => p11Step c' (p11DevH A) (Fin.append J' ρt))
      (p11CloseDom C eps (p11s2 C nu eps / 2) ρt) := fun c' =>
    (p11Step_differentiableOn hVho hHd c').comp hκ fun J' hJ' => hJ'.1
  have hmain : ∀ c', DifferentiableOn ℂ (fun J' : P11CVec n => fderiv ℂ (fun I => A.h0 I + A.g2 I)
      (Fin.append J' ρt) (Pi.single c' 1)) (p11CloseDom C eps (p11s2 C nu eps / 2) ρt) := by
    intro c'
    refine (differentiableOn_pi.1 (hS c') 0).congr fun J' hJ' => ?_
    have hd : DifferentiableAt ℂ (fun I => A.h0 I + A.g2 I) (Fin.append J' ρt) :=
      ((differentiableOn_pi.1 hHd 0).differentiableAt
        ((p11_dev_box_isOpen _ _ _).mem_nhds hJ'.1))
    exact (congrFun (p11_dev_step_const (φ := fun I => A.h0 I + A.g2 I) c' hd) 0).symm
  refine differentiableOn_pi.2 fun i => ?_
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp only [p11CloseFun, Fin.append_left]
    exact (hmain _).sub ((differentiableOn_pi.1 hωd k).mono fun J' hJ' => hJ'.2)
  · simp only [p11CloseFun, Fin.append_right]
    refine DifferentiableOn.sub ?_ ?_
    · exact ((hmain (Fin.natAdd n k)).mul (differentiableOn_const ((eps : ℂ)⁻¹))).congr
        fun x _ => by simp [div_eq_mul_inv]
    · exact (differentiableOn_const _).mul ((differentiableOn_pi.1 hΩd k).mono fun J' hJ' => hJ'.2)

theorem p11_close_omega_partial (hC : P11SecularSpec D C) {J : P11CVec n}
    (hJ : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC)) (k : Fin n) (α : Fin n → ℕ) :
    p11PartialVec α (fun (J' : P11CVec n) (_ : Fin 1) => C.omega J' k) J =
      p11PartialVec (α + Pi.single k 1) (fun (J' : P11CVec n) (_ : Fin 1) => C.h J') J := by
  obtain ⟨-, -, -, -, hhd, hωh, -⟩ := id hC
  have hCh : DifferentiableOn ℂ (fun (J' : P11CVec n) (_ : Fin 1) => C.h J')
      (ball (KAM.realInclusion n C.J0) (2 * C.rC)) := differentiableOn_pi.2 fun _ => hhd
  have hEq : EqOn (p11Step k (fun (J' : P11CVec n) (_ : Fin 1) => C.h J'))
      (fun (J' : P11CVec n) (_ : Fin 1) => C.omega J' k)
      (ball (KAM.realInclusion n C.J0) (2 * C.rC)) := by
    intro J' hJ'
    rw [p11_dev_step_const _ (hhd.differentiableAt (isOpen_ball.mem_nhds hJ'))]
    funext x
    simp [hωh J' hJ']
  rw [← p11_partial_step isOpen_ball hCh α k hJ, p11_partial_congr isOpen_ball hEq α hJ]

/-- A coordinate of the partials of `p11CloseFun`. -/
theorem p11_close_comp {Fast : P11FastData n} {nu eps c : ℝ} {A : P11SlowData n}
    (hC : P11SecularSpec D C) (hs2 : 0 ≤ p11s2 C nu eps) (heps : 0 ≤ eps)
    (hA : P11SlowSpecOf C Fast nu eps c A) (ρt : P11CVec n) (c' : Fin (n + n)) (α : Fin n → ℕ)
    {J : P11CVec n} (hJ : J ∈ p11CloseDom C eps (p11s2 C nu eps / 2) ρt) :
    (p11PartialVec α (p11CloseFun C A eps ρt) J) c' =
      (p11PartialVec α (fun J' (_ : Fin 1) => p11CloseFun C A eps ρt J' c') J) 0 := by
  have hΦ := p11_close_Phi_diff hC hs2 heps hA ρt
  have := p11_partial_clm (p11_close_dom_open C eps _ ρt) hΦ
    (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.proj c') α hJ
  exact (congrFun this 0).symm

theorem p11_close_block1 (hC : P11SecularSpec D C) {Fast : P11FastData n} {nu eps c : ℝ}
    {A : P11SlowData n} (hnu : 1 ≤ nu) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hF : P11FastSpec C eps Fast) (hA : P11SlowSpecOf C Fast nu eps c A)
    (hzs : 3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16) (h5 : 5 * eps ≤ p11s2 C nu eps)
    (k : Fin n) (α : Fin n → ℕ) (J ρ : P11CVec n)
    (hJ : ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4)
    (hρ : ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4) :
    ‖(p11PartialVec α (p11CloseFun C A eps ρ) J) (Fin.castAdd n k)‖ ≤
      eps * p11DevA C eps (α + Pi.single k 1) + p11DevG C nu eps c (α + Pi.single k 1) 0 := by
  obtain ⟨hK, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  obtain ⟨-, -, -, hrC0, -, -, -, hrz0, -, -⟩ := fast_consts hC
  have hspec := p11s2_spec hC hK
  have hs1r := p11s1_le C eps
  have hπ := Real.pi_gt_three
  have hVho := p11_dev_box_isOpen (p11DevCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2)
  have hP : (Fin.append J ρ : P11CVec (n + n)) ∈
      p11Box (p11DevCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2) :=
    p11_dev_mem_box J ρ (by linarith) (by nlinarith) hJ hρ
  have hJU : J ∈ p11CloseDom C eps (p11s2 C nu eps / 2) ρ := by
    refine ⟨hP, ?_⟩
    rw [mem_ball_iff_norm]; linarith
  have hUo := p11_close_dom_open C eps (p11s2 C nu eps / 2) ρ
  have hHd := p11_freq_H_diff (C := C) hs2.le heps.le hA
  have hΩ1 : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) := hJU.2
  rw [p11_close_comp hC hs2.le heps.le hA ρ _ α hJU]
  -- the scalar function
  have hκ : DifferentiableOn ℂ (fun J' : P11CVec n => (Fin.append J' ρ : P11CVec (n + n)))
      (p11CloseDom C eps (p11s2 C nu eps / 2) ρ) := by
    refine (differentiable_pi.2 fun i => ?_).differentiableOn
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp <;> fun_prop
  have hSd : DifferentiableOn ℂ (fun J' : P11CVec n =>
      p11Step (Fin.castAdd n k) (p11DevH A) (Fin.append J' ρ))
      (p11CloseDom C eps (p11s2 C nu eps / 2) ρ) :=
    (p11Step_differentiableOn hVho hHd _).comp hκ fun J' hJ' => hJ'.1
  obtain ⟨-, -, ⟨hωd, -⟩, -⟩ := id hC
  have hOmd : DifferentiableOn ℂ (fun (J' : P11CVec n) (_ : Fin 1) => C.omega J' k)
      (p11CloseDom C eps (p11s2 C nu eps / 2) ρ) :=
    (differentiableOn_pi.2 fun _ => differentiableOn_pi.1 hωd k).mono fun J' hJ' => hJ'.2
  have hEq : EqOn (fun J' (_ : Fin 1) => p11CloseFun C A eps ρ J' (Fin.castAdd n k))
      (fun J' => p11Step (Fin.castAdd n k) (p11DevH A) (Fin.append J' ρ) -
        fun _ => C.omega J' k) (p11CloseDom C eps (p11s2 C nu eps / 2) ρ) := by
    intro J' hJ'
    have hd : DifferentiableAt ℂ (fun I => A.h0 I + A.g2 I) (Fin.append J' ρ) :=
      (differentiableOn_pi.1 hHd 0).differentiableAt (hVho.mem_nhds hJ'.1)
    have h1 := congrFun (p11_dev_step_const (φ := fun I => A.h0 I + A.g2 I) (Fin.castAdd n k) hd)
    funext x
    simp only [p11CloseFun, Fin.append_left, Pi.sub_apply]
    exact congrArg (fun z => z - C.omega J' k) (h1 x).symm
  have hsub := p11_partial_sub hUo hSd hOmd α hJU
  have hcg := p11_partial_congr hUo (fun J' hJ' => hEq hJ') α hJU
  have hslice := p11_partial_slice hVho (p11Step_differentiableOn hVho hHd (Fin.castAdd n k)) ρ α hP
  have hstep := p11_partial_step hVho hHd (Fin.append α (0 : Fin n → ℕ)) (Fin.castAdd n k) hP
  rw [p11_close_append_cast] at hstep
  have hom := p11_close_omega_partial hC hΩ1 k α
  have hbd := p11_dev_J_bound hC hnu heps hεM hF hA hzs h5 (α + Pi.single k 1) J ρ hJ hρ
  have hval : p11PartialVec α (fun J' (_ : Fin 1) => p11CloseFun C A eps ρ J' (Fin.castAdd n k)) J =
      p11PartialVec (Fin.append (α + Pi.single k 1) (0 : Fin n → ℕ)) (p11DevH A)
        (Fin.append J ρ) -
      p11PartialVec (α + Pi.single k 1) (fun (J' : P11CVec n) (_ : Fin 1) => C.h J') J := by
    rw [hcg, hsub, hom, ← hstep, ← hslice]
  rw [hval]
  exact (norm_le_pi_norm _ 0).trans hbd

theorem p11_close_block2 (hC : P11SecularSpec D C) {Fast : P11FastData n} {nu eps c : ℝ}
    {A : P11SlowData n} (hnu : 1 ≤ nu) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hA : P11SlowSpecOf C Fast nu eps c A)
    (hzs : 3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16) (h5 : 5 * eps ≤ p11s2 C nu eps)
    (k : Fin n) (α : Fin n → ℕ) (J ρ : P11CVec n)
    (hJ : ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4)
    (hρ : ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4) :
    ‖(p11PartialVec α (p11CloseFun C A eps ρ) J) (Fin.natAdd n k)‖ ≤
      p11DevZ C nu eps c α 0 + p11DevG C nu eps c α (0 + Pi.single k 1) / eps := by
  obtain ⟨hK, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  obtain ⟨-, -, -, hrC0, -, -, -, hrz0, -, -⟩ := fast_consts hC
  have hspec := p11s2_spec hC hK
  have hs1r := p11s1_le C eps
  have hπ := Real.pi_gt_three
  have hVho := p11_dev_box_isOpen (p11DevCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2)
  have hP : (Fin.append J ρ : P11CVec (n + n)) ∈
      p11Box (p11DevCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2) :=
    p11_dev_mem_box J ρ (by linarith) (by nlinarith) hJ hρ
  have hJU : J ∈ p11CloseDom C eps (p11s2 C nu eps / 2) ρ := by
    refine ⟨hP, ?_⟩
    rw [mem_ball_iff_norm]; linarith
  have hUo := p11_close_dom_open C eps (p11s2 C nu eps / 2) ρ
  have hHd := p11_freq_H_diff (C := C) hs2.le heps.le hA
  rw [p11_close_comp hC hs2.le heps.le hA ρ _ α hJU]
  have hκ : DifferentiableOn ℂ (fun J' : P11CVec n => (Fin.append J' ρ : P11CVec (n + n)))
      (p11CloseDom C eps (p11s2 C nu eps / 2) ρ) := by
    refine (differentiable_pi.2 fun i => ?_).differentiableOn
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp <;> fun_prop
  have hSd : DifferentiableOn ℂ (fun J' : P11CVec n =>
      p11Step (Fin.natAdd n k) (p11DevH A) (Fin.append J' ρ))
      (p11CloseDom C eps (p11s2 C nu eps / 2) ρ) :=
    (p11Step_differentiableOn hVho hHd _).comp hκ fun J' hJ' => hJ'.1
  obtain ⟨-, -, ⟨-, hΩd⟩, -⟩ := id hC
  have hOmd : DifferentiableOn ℂ (fun (J' : P11CVec n) (_ : Fin 1) =>
      (2 * Real.pi : ℂ)⁻¹ * C.Omega J' k) (p11CloseDom C eps (p11s2 C nu eps / 2) ρ) :=
    (differentiableOn_pi.2 fun _ => (differentiableOn_const _).mul
      (differentiableOn_pi.1 hΩd k)).mono fun J' hJ' => hJ'.2
  have hS' : DifferentiableOn ℂ (fun J' : P11CVec n => ((eps : ℂ)⁻¹ • ContinuousLinearMap.id ℂ
      (P11CVec 1)) (p11Step (Fin.natAdd n k) (p11DevH A) (Fin.append J' ρ)))
      (p11CloseDom C eps (p11s2 C nu eps / 2) ρ) := hSd.const_smul ((eps : ℂ)⁻¹)
  have hEq : EqOn (fun J' (_ : Fin 1) => p11CloseFun C A eps ρ J' (Fin.natAdd n k))
      (fun J' => ((eps : ℂ)⁻¹ • ContinuousLinearMap.id ℂ (P11CVec 1))
        (p11Step (Fin.natAdd n k) (p11DevH A) (Fin.append J' ρ)) -
        fun _ => (2 * Real.pi : ℂ)⁻¹ * C.Omega J' k)
      (p11CloseDom C eps (p11s2 C nu eps / 2) ρ) := by
    intro J' hJ'
    have hd : DifferentiableAt ℂ (fun I => A.h0 I + A.g2 I) (Fin.append J' ρ) :=
      (differentiableOn_pi.1 hHd 0).differentiableAt (hVho.mem_nhds hJ'.1)
    have h1 := congrFun (p11_dev_step_const (φ := fun I => A.h0 I + A.g2 I) (Fin.natAdd n k) hd)
    funext x
    simp only [p11CloseFun, Fin.append_right, Pi.sub_apply]
    have h2 : p11Step (Fin.natAdd n k) (p11DevH A) (Fin.append J' ρ) x =
        fderiv ℂ (fun I => A.h0 I + A.g2 I) (Fin.append J' ρ) (Pi.single (Fin.natAdd n k) 1) :=
      h1 x
    simp only [smul_apply, ContinuousLinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [h2]
    ring
  have hsub := p11_partial_sub hUo hS' hOmd α hJU
  have hcg := p11_partial_congr hUo (fun J' hJ' => hEq hJ') α hJU
  have hclm := p11_partial_clm hUo hSd ((eps : ℂ)⁻¹ • ContinuousLinearMap.id ℂ (P11CVec 1)) α hJU
  have hslice := p11_partial_slice hVho (p11Step_differentiableOn hVho hHd (Fin.natAdd n k)) ρ α hP
  have hstep := p11_partial_step hVho hHd (Fin.append α (0 : Fin n → ℕ)) (Fin.natAdd n k) hP
  rw [p11_dev_append_add] at hstep
  have hOm := p11_dev_Om_slice hC (r2 := Real.pi * eps / 2) (eps := eps) (by linarith) (by linarith) k α J ρ hP
  have hbd := p11_dev_rho_bound hC hnu heps hεM hA hzs h5 k α 0 J ρ hJ hρ
  have hX : p11PartialVec α (fun J' : P11CVec n =>
        p11Step (Fin.natAdd n k) (p11DevH A) (Fin.append J' ρ)) J =
      p11PartialVec (Fin.append α (0 + Pi.single k 1 : Fin n → ℕ)) (p11DevH A) (Fin.append J ρ) := by
    rw [← hstep]
    exact hslice
  have hval : p11PartialVec α (fun J' (_ : Fin 1) => p11CloseFun C A eps ρ J' (Fin.natAdd n k)) J =
      (eps : ℂ)⁻¹ • (p11PartialVec (Fin.append α (0 + Pi.single k 1 : Fin n → ℕ)) (p11DevH A)
          (Fin.append J ρ) - (eps : ℂ) • p11PartialVec (Fin.append α (0 : Fin n → ℕ))
          (fun (I : P11CVec (n + n)) (_ : Fin 1) =>
            (2 * Real.pi : ℂ)⁻¹ * C.Omega (fun i : Fin n => I (Fin.castAdd n i)) k)
          (Fin.append J ρ)) := by
    rw [hcg, hsub, hclm, hOm]
    beta_reduce
    rw [hX]
    have hc0 : (eps : ℂ) ≠ 0 := by exact_mod_cast heps.ne'
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_sub, smul_smul, inv_mul_cancel₀ hc0,
      one_smul]
  rw [hval]
  refine (norm_le_pi_norm _ 0).trans ?_
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg heps.le]
  have hb2 : ‖p11PartialVec (Fin.append α (0 : Fin n → ℕ) + Pi.single (Fin.natAdd n k) 1)
      (p11DevH A) (Fin.append J ρ) - (eps : ℂ) • p11PartialVec (Fin.append α (0 : Fin n → ℕ))
      (fun (I : P11CVec (n + n)) (_ : Fin 1) =>
        (2 * Real.pi : ℂ)⁻¹ * C.Omega (fun i : Fin n => I (Fin.castAdd n i)) k)
      (Fin.append J ρ)‖ ≤ eps * p11DevZ C nu eps c α 0 + p11DevG C nu eps c α (0 + Pi.single k 1) :=
    hbd
  rw [p11_dev_append_add α 0 k] at hb2
  calc eps⁻¹ * ‖_‖ ≤ eps⁻¹ * (eps * p11DevZ C nu eps c α 0 +
        p11DevG C nu eps c α (0 + Pi.single k 1)) := by gcongr
    _ = _ := by field_simp

theorem p11_close_Reta {C : P11SecularData n} {eps l k2 : ℝ} (hl : 1 ≤ l)
    {lx : ℝ} (hlx : 1 ≤ lx) (he1 : eps ≤ 1) (heps : 0 < eps) (hk2 : 0 ≤ k2) {η : ℝ}
    (hηb : η ≤ k2 * eps * lx) (hMF : 1 ≤ C.MF) : C.MF + η ≤ (C.MF + k2) * lx := by
  have h1 : k2 * eps * lx ≤ k2 * lx := by
    have : 0 ≤ k2 * lx := by positivity
    nlinarith
  nlinarith

theorem p11_close_fin1 {nu eps c k2 Rc Λ F l : ℝ} {mu : ℕ} {C : P11SecularData n}
    (heps : 0 < eps) (he1 : eps ≤ 1) (hl : 1 ≤ l) (hc : 0 ≤ c) (hΛ : 1 ≤ Λ)
    (hτ : 0 ≤ C.tau) {α' : Fin n → ℕ} (hs : ∑ i, α' i ≤ mu + 1) (hs1 : 0 < p11s1 C eps)
    (hs2 : 0 < p11s2 C nu eps) (h41 : 4 / p11s1 C eps ≤ Λ * l ^ (C.tau + 1))
    (h42 : 4 / p11s2 C nu eps ≤ Λ * l ^ (C.tau + 1))
    (hR : C.MF + p11eta1 C eps ≤ Rc * l ^ (2 * C.tau + 1)) (hF0 : 0 ≤ F)
    (hPF : ((∑ i, α' i).factorial : ℝ) ≤ F) (hk2 : 0 ≤ k2) (hRc : Rc = C.MF + k2)
    (hMF : 1 ≤ C.MF) (hη0 : 0 ≤ p11eta1 C eps) (hlE : l = Real.log (1 / eps)) :
    eps * p11DevA C eps α' + p11DevG C nu eps c α' 0 ≤
      F * Λ ^ (mu + 1) * (Rc + k2 + 5) * (1 + c) *
        (eps * l ^ (5 * C.tau + 2 + (C.tau + 1) * (((mu + 1 : ℕ) : ℝ)))) := by
  have hP : (∏ i, ((α' i).factorial : ℝ)) ≤ F := (p11_resc_prod_le α').trans hPF
  have hP0 : 0 ≤ ∏ i, ((α' i).factorial : ℝ) := Finset.prod_nonneg fun _ _ => by positivity
  have hnum := p11_num_cl1 (e := eps) (c := c) (l := l) (F := F) (Rc := Rc) (Λ := Λ)
    (τ := C.tau) (P := ∏ i, ((α' i).factorial : ℝ)) (R := C.MF + p11eta1 C eps)
    (s1 := p11s1 C eps) (s2 := p11s2 C nu eps) (s := ∑ i, α' i) (M := mu + 1) heps he1 hl hc hΛ
    hτ hP0 hP (by linarith) hR hs1 hs2 h41 h42 hs
  have e1 : eps * p11DevA C eps α' + p11DevG C nu eps c α' 0 =
      eps * ((∏ i, ((α' i).factorial : ℝ)) * (C.MF + p11eta1 C eps) /
        (p11s1 C eps / 4) ^ (∑ i, α' i)) +
      (∏ i, ((α' i).factorial : ℝ)) * (c * eps ^ 3 * l ^ (5 * C.tau + 2)) /
        (p11s2 C nu eps / 4) ^ (∑ i, α' i) := by
    simp [p11DevA, p11DevG, mul_assoc, hlE]
  rw [e1]
  refine hnum.trans ?_
  have hRc0 : 0 ≤ Rc := by rw [hRc]; linarith
  have hFΛ : 0 ≤ F * Λ ^ (mu + 1) := by positivity
  have hLQ : 0 ≤ eps * l ^ (5 * C.tau + 2 + (C.tau + 1) * (((mu + 1 : ℕ) : ℝ))) := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ l) (5 * C.tau + 2 + (C.tau + 1) *
      (((mu + 1 : ℕ) : ℝ)))
    positivity
  have h2 : Rc + c ≤ (Rc + k2 + 5) * (1 + c) := by nlinarith [mul_nonneg hk2 hc]
  calc F * Λ ^ (mu + 1) * (Rc + c) * (eps * l ^ (5 * C.tau + 2 + (C.tau + 1) *
        (((mu + 1 : ℕ) : ℝ)))) ≤ F * Λ ^ (mu + 1) * ((Rc + k2 + 5) * (1 + c)) *
        (eps * l ^ (5 * C.tau + 2 + (C.tau + 1) * (((mu + 1 : ℕ) : ℝ)))) := by
        gcongr
    _ = _ := by ring

theorem p11_close_fin2 {nu eps c k2 Rc Λ F l : ℝ} {mu : ℕ} {C : P11SecularData n}
    (heps : 0 < eps) (he1 : eps ≤ 1) (hl : 1 ≤ l) (hc : 0 ≤ c) (hΛ : 1 ≤ Λ)
    (hτ : 0 ≤ C.tau) {α : Fin n → ℕ} (hs : ∑ i, α i ≤ mu + 1) (hs2 : 0 < p11s2 C nu eps)
    (h42 : 4 / p11s2 C nu eps ≤ Λ * l ^ (C.tau + 1)) (hη0 : 0 ≤ p11eta1 C eps)
    (hηb : p11eta1 C eps ≤ k2 * eps * l ^ (2 * C.tau + 1)) (hF0 : 0 ≤ F)
    (hPF : ((∑ i, α i).factorial : ℝ) ≤ F) (hk2 : 0 ≤ k2) {k : Fin n} (hRc : Rc = C.MF + k2)
    (hMF : 1 ≤ C.MF) (hlE : l = Real.log (1 / eps)) :
    p11DevZ C nu eps c α 0 + p11DevG C nu eps c α (0 + Pi.single k 1) / eps ≤
      F * Λ ^ (mu + 1) * (Rc + k2 + 5) * (1 + c) *
        (eps * l ^ (5 * C.tau + 2 + (C.tau + 1) * (((mu + 1 : ℕ) : ℝ)))) := by
  have hP : (∏ i, ((α i).factorial : ℝ)) ≤ F := (p11_resc_prod_le α).trans hPF
  have hP0 : 0 ≤ ∏ i, ((α i).factorial : ℝ) := Finset.prod_nonneg fun _ _ => by positivity
  have hnum := p11_num_cl2 (e := eps) (c := c) (l := l) (F := F) (k2 := k2) (Λ := Λ)
    (τ := C.tau) (P := ∏ i, ((α i).factorial : ℝ)) (η := p11eta1 C eps) (s2 := p11s2 C nu eps)
    (j := ∑ i, α i) (M := mu + 1) heps he1 hl hc hΛ hτ hP0 hP hη0 hηb hs2 h42 hs
  have e1 : p11DevZ C nu eps c α 0 + p11DevG C nu eps c α (0 + Pi.single k 1) / eps =
      (∏ i, ((α i).factorial : ℝ)) * (c * (eps + p11eta1 C eps)) / (p11s2 C nu eps / 2) ^ (∑ i, α i) +
      (∏ i, ((α i).factorial : ℝ)) * (c * eps ^ 3 * l ^ (5 * C.tau + 2)) /
        ((p11s2 C nu eps / 4) ^ (∑ i, α i) * (eps / 4) ^ 1) / eps := by
    have hq : (∏ x : Fin n, (((if x = k then 1 else 0 : ℕ)).factorial : ℝ)) = 1 :=
      Finset.prod_eq_one fun x _ => by split_ifs <;> simp
    simp [p11DevZ, p11DevG, Pi.single_apply, mul_assoc, hlE]
    rw [hq, one_mul]
  rw [e1]
  refine hnum.trans ?_
  have hFΛ : 0 ≤ F * Λ ^ (mu + 1) := by positivity
  have hRc0 : 0 ≤ Rc := by rw [hRc]; linarith
  have h2 : c * (1 + k2) + 4 * c ≤ (Rc + k2 + 5) * (1 + c) := by
    nlinarith [mul_nonneg hk2 hc]
  calc F * Λ ^ (mu + 1) * (c * (1 + k2) + 4 * c) * (eps * l ^ (5 * C.tau + 2 + (C.tau + 1) *
        (((mu + 1 : ℕ) : ℝ)))) ≤ F * Λ ^ (mu + 1) * ((Rc + k2 + 5) * (1 + c)) *
        (eps * l ^ (5 * C.tau + 2 + (C.tau + 1) * (((mu + 1 : ℕ) : ℝ)))) := by
        gcongr
    _ = _ := by ring

theorem p11_close_partial (hC : P11SecularSpec D C) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ Kb : ℝ, 0 < Kb ∧ ∀ {Fast : P11FastData n} {eps c : ℝ} {A : P11SlowData n},
      0 < eps → eps * C.MF ≤ Real.exp (-1) → 0 ≤ c → P11FastSpec C eps Fast →
      P11SlowSpecOf C Fast nu eps c A →
      3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16 → 5 * eps ≤ p11s2 C nu eps →
      ∀ ρ J : P11CVec n, ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4 →
      ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4 →
      ∀ α : Fin n → ℕ, ∑ i, α i ≤ (p11PatchData D).mu →
      ‖p11PartialVec α (p11CloseFun C A eps ρ) J‖ ≤ Kb * (1 + c) * (eps * Real.log (1 / eps) ^
        (5 * C.tau + 2 + (C.tau + 1) * (((p11PatchData D).mu + 1 : ℕ) : ℝ))) := by
  obtain ⟨k1, hk1, hs1inv⟩ := p11_prin_s1_inv hC
  obtain ⟨k2, hk2, heta⟩ := p11_prin_eta1_le hC
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  set m0 : ℝ := min (min C.rC (C.gamma / (4 * C.L)) / (4 * (6 / (Real.pi * C.sigma)) ^ (C.tau + 1)))
      (C.gamma / (8 * C.L * (3 * nu / (Real.pi * (C.sigma / 12))) ^ (C.tau + 1))) with hm0
  have hnu0 : 0 < nu := by linarith
  have hm0pos : 0 < m0 := by
    have hπ := Real.pi_pos
    have hL0 : 0 < C.L := by linarith
    have hr1 : 0 < (6 / (Real.pi * C.sigma)) ^ (C.tau + 1) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hr2 : 0 < (3 * nu / (Real.pi * (C.sigma / 12))) ^ (C.tau + 1) :=
      Real.rpow_pos_of_pos (by positivity) _
    have h1 : 0 < min C.rC (C.gamma / (4 * C.L)) := lt_min hrC0 (by positivity)
    exact lt_min (by positivity) (by positivity)
  set mu := (p11PatchData D).mu with hmu
  set F : ℝ := ((mu + 1).factorial : ℝ) with hF
  set Λ : ℝ := 1 + 4 * k1 + 4 / m0 with hΛ
  have hΛ1 : 1 ≤ Λ := by
    have : 0 ≤ 4 / m0 := by positivity
    rw [hΛ]; linarith
  set Rc : ℝ := C.MF + k2 with hRc
  refine ⟨F * Λ ^ (mu + 1) * (Rc + k2 + 5) , by positivity, ?_⟩
  intro Fast eps c A heps hεM hc0 hFs hA hzs h5 ρ J hJ hρ α hα
  obtain ⟨hK2, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  have hl : 1 ≤ Real.log (1 / eps) := slow_log_ge_one hC heps hεM
  have he1 : eps ≤ 1 := by
    have h1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    nlinarith
  have hs1' : 4 / p11s1 C eps ≤ Λ * Real.log (1 / eps) ^ (C.tau + 1) := by
    have h1 := hs1inv heps hεM
    have : 4 / p11s1 C eps = 4 * (p11s1 C eps)⁻¹ := by rw [div_eq_mul_inv]
    rw [this]
    have hl1 : 0 ≤ Real.log (1 / eps) ^ (C.tau + 1) := Real.rpow_nonneg (by linarith) _
    calc 4 * (p11s1 C eps)⁻¹ ≤ 4 * (k1 * Real.log (1 / eps) ^ (C.tau + 1)) := by gcongr
      _ ≤ Λ * Real.log (1 / eps) ^ (C.tau + 1) := by
          have : 4 * k1 ≤ Λ := by
            have : 0 ≤ 4 / m0 := by positivity
            rw [hΛ]; linarith
          nlinarith
  have hs2' : 4 / p11s2 C nu eps ≤ Λ * Real.log (1 / eps) ^ (C.tau + 1) := by
    have h1 := p11s2_log_lower hC hnu0 heps hεM
    have hlp : 0 < Real.log (1 / eps) ^ (C.tau + 1) := Real.rpow_pos_of_pos (by linarith) _
    rw [← hm0] at h1
    have h2 : m0 / Real.log (1 / eps) ^ (C.tau + 1) ≤ p11s2 C nu eps := h1
    have h3 : 4 / p11s2 C nu eps ≤ 4 / (m0 / Real.log (1 / eps) ^ (C.tau + 1)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) h2
    refine h3.trans ?_
    have : 4 / (m0 / Real.log (1 / eps) ^ (C.tau + 1)) =
        (4 / m0) * Real.log (1 / eps) ^ (C.tau + 1) := by field_simp
    rw [this]
    have : 4 / m0 ≤ Λ := by
      have : 0 ≤ 4 * k1 := by positivity
      rw [hΛ]; linarith
    exact mul_le_mul_of_nonneg_right this hlp.le
  have hη0 : 0 ≤ p11eta1 C eps := by
    obtain ⟨-, -, -, -, hGd, -, -, -, -, -, -, -, -, hGη, -⟩ := hFs
    have hr : 0 < C.rz / 2 := by positivity
    have := hGη (KAM.realInclusion n C.J0) (by simp; linarith only [hs1]) 0 (by simpa using hr)
    exact (norm_nonneg _).trans this
  have hηb : p11eta1 C eps ≤ k2 * eps * Real.log (1 / eps) ^ (2 * C.tau + 1) := heta heps hεM
  have hl0 : 0 < Real.log (1 / eps) := by linarith
  have hlx : 1 ≤ Real.log (1 / eps) ^ (2 * C.tau + 1) := Real.one_le_rpow hl (by linarith)
  have hF0 : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos _
  have hΛM : 0 < Λ ^ (mu + 1) := by positivity
  have hRη : C.MF + p11eta1 C eps ≤ Rc * Real.log (1 / eps) ^ (2 * C.tau + 1) :=
    p11_close_Reta hl hlx he1 heps hk2.le hηb hMF
  have hfac : ∀ s : ℕ, s ≤ mu + 1 → ((s.factorial : ℕ) : ℝ) ≤ F := fun s hs => by
    rw [hF]; exact_mod_cast Nat.factorial_le hs
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun c' => ?_
  refine Fin.addCases (fun k => ?_) (fun k => ?_) c'
  · have hb := p11_close_block1 hC hnu heps hεM hFs hA hzs h5 k α J ρ hJ hρ
    have hs : ∑ i, (α + Pi.single k 1 : Fin n → ℕ) i ≤ mu + 1 := by
      simp [Finset.sum_add_distrib]; omega
    exact hb.trans (p11_close_fin1 (C := C) (nu := nu) heps he1 hl hc0 hΛ1 hτ0.le hs hs1 hs2 hs1'
      hs2' hRη hF0.le (hfac _ hs) hk2.le rfl hMF hη0 rfl)
  · have hb := p11_close_block2 hC hnu heps hεM hA hzs h5 k α J ρ hJ hρ
    have hs : ∑ i, α i ≤ mu + 1 := by omega
    exact hb.trans (p11_close_fin2 (C := C) (nu := nu) (c := c) heps he1 hl hc0 hΛ1 hτ0.le hs hs2
      hs2' hη0 hηb hF0.le (hfac _ (by omega)) hk2.le (k := k) (α := α) (Rc := Rc) rfl hMF rfl)

end Close

end KAM.Planetary

end
