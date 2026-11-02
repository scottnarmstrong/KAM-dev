/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Analytic.Cauchy
public import KAM.Wave.Analytic.HoloAnalytic
public import KAM.Wave.KamStep.TaylorOneVar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The derivative of a holomorphic map on a Banach space is holomorphic (infrastructure for W5)

Used for: `D²P`, `DX` differentiable (symmetry of the Hessian of a smoothing Hamiltonian),
operator-norm holomorphy of the Hessian blocks `H(θ)` of the Taylor polynomial, and holomorphy of
`w ↦ Dφ^t(w)` for the flow (`bpW:w5:taylor`, `bpW:w5:flow-calc`).
-/

@[expose] public section

open Metric Set Filter Topology

namespace KAM.Wave

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The function `p ↦ f(x + p₀ k + p₁ d)` on `ℂ²` is holomorphic near `0` when `f` is holomorphic
near `x`. -/
theorem differentiableAt_slice2 {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {x : E} (k d : E) {p : Fin 2 → ℂ}
    (hp : x + p 0 • k + p 1 • d ∈ U) :
    DifferentiableAt ℂ (fun q : Fin 2 → ℂ => f (x + q 0 • k + q 1 • d)) p := by
  have h1 : DifferentiableAt ℂ f (x + p 0 • k + p 1 • d) := hf.differentiableAt (hU.mem_nhds hp)
  have h2 : DifferentiableAt ℂ (fun q : Fin 2 → ℂ => x + q 0 • k + q 1 • d) p := by fun_prop
  exact h1.comp p h2

/-- The linear map `q ↦ q₀ k + q₁ d`. -/
noncomputable def slice2L (k d : E) : (Fin 2 → ℂ) →L[ℂ] E :=
  (ContinuousLinearMap.proj 0 : (Fin 2 → ℂ) →L[ℂ] ℂ).smulRight k +
    (ContinuousLinearMap.proj 1 : (Fin 2 → ℂ) →L[ℂ] ℂ).smulRight d

theorem slice2L_apply (k d : E) (q : Fin 2 → ℂ) : slice2L k d q = q 0 • k + q 1 • d := by
  simp [slice2L]

/-- **`μ ↦ Df(x + μ k) d` is holomorphic** (existence of the second derivative along slices). -/
theorem differentiableAt_fderiv_line {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {x : E} (hx : x ∈ U) (k d : E) :
    DifferentiableAt ℂ (fun μ : ℂ => fderiv ℂ f (x + μ • k) d) 0 := by
  set S : Set (Fin 2 → ℂ) := {q | x + q 0 • k + q 1 • d ∈ U} with hS
  set g : (Fin 2 → ℂ) → F := fun q => f (x + q 0 • k + q 1 • d) with hgdef
  have hSo : IsOpen S := hU.preimage (by fun_prop)
  have h0 : (0 : Fin 2 → ℂ) ∈ S := by simpa [hS] using hx
  have hg : DifferentiableOn ℂ g S :=
    fun q hq => (differentiableAt_slice2 hU hf k d hq).differentiableWithinAt
  have han := analyticOnNhd_of_differentiableOn_banach hSo hg
  have hfd := han.fderiv_of_isOpen hSo
  set ℓ : ℂ → (Fin 2 → ℂ) := fun μ => μ • (Pi.single 0 (1 : ℂ) : Fin 2 → ℂ) with hℓ
  have hℓd : DifferentiableAt ℂ ℓ 0 := by
    have : Differentiable ℂ ℓ := fun μ => ((differentiableAt_id).smul_const _)
    exact this 0
  have hℓ0 : ℓ 0 = 0 := by simp [hℓ]
  have hev : ∀ᶠ μ in 𝓝 (0 : ℂ), ℓ μ ∈ S := by
    have : ContinuousAt ℓ 0 := hℓd.continuousAt
    rw [← hℓ0] at h0
    exact this.eventually (hSo.mem_nhds h0)
  have hcomp : DifferentiableAt ℂ (fun μ : ℂ => fderiv ℂ g (ℓ μ) (Pi.single 1 1)) 0 := by
    have h1 : DifferentiableAt ℂ (fderiv ℂ g) (ℓ 0) := by
      rw [hℓ0]; exact (hfd 0 h0).differentiableAt
    have h2 := h1.comp (0 : ℂ) hℓd
    exact (ContinuousLinearMap.apply ℂ F (Pi.single 1 1 : Fin 2 → ℂ)).differentiableAt.comp 0 h2
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hev] with μ hμ
  have hz : x + ℓ μ 0 • k + ℓ μ 1 • d ∈ U := hμ
  have hd := (hf.differentiableAt (hU.mem_nhds hz))
  have hL : HasFDerivAt (fun q : Fin 2 → ℂ => x + q 0 • k + q 1 • d) (slice2L k d) (ℓ μ) := by
    have := ((slice2L k d).hasFDerivAt (x := ℓ μ)).const_add x
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
    simp [slice2L_apply, add_assoc]
  have hch : HasFDerivAt g ((fderiv ℂ f (x + ℓ μ 0 • k + ℓ μ 1 • d)).comp (slice2L k d)) (ℓ μ) :=
    hd.hasFDerivAt.comp (ℓ μ) hL
  rw [hch.fderiv]
  simp [slice2L_apply, hℓ]

/-- The map `(μ₁,μ₂) ↦ Df(x + μ₁k₁ + μ₂k₂) d` is complex Fréchet differentiable at `0`. -/
theorem exists_hasFDerivAt_fderiv_plane {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {x : E} (hx : x ∈ U) (k₁ k₂ d : E) :
    ∃ L : (Fin 2 → ℂ) →L[ℂ] F,
      HasFDerivAt (fun p : Fin 2 → ℂ => fderiv ℂ f (x + p 0 • k₁ + p 1 • k₂) d) L 0 := by
  set g : (Fin 3 → ℂ) → F := fun q => f (x + q 0 • k₁ + q 1 • k₂ + q 2 • d) with hgdef
  set S : Set (Fin 3 → ℂ) := {q | x + q 0 • k₁ + q 1 • k₂ + q 2 • d ∈ U} with hS
  have hSo : IsOpen S := hU.preimage (by fun_prop)
  have h0 : (0 : Fin 3 → ℂ) ∈ S := by simpa [hS] using hx
  have hg : DifferentiableOn ℂ g S := fun q hq =>
    ((hf.differentiableAt (hU.mem_nhds hq)).comp q (by fun_prop :
      DifferentiableAt ℂ (fun q : Fin 3 → ℂ => x + q 0 • k₁ + q 1 • k₂ + q 2 • d) q)
      ).differentiableWithinAt
  have han := analyticOnNhd_of_differentiableOn_banach hSo hg
  have hfd := han.fderiv_of_isOpen hSo
  set ι : (Fin 2 → ℂ) →L[ℂ] (Fin 3 → ℂ) :=
    (ContinuousLinearMap.proj 0 : (Fin 2 → ℂ) →L[ℂ] ℂ).smulRight (Pi.single 0 (1 : ℂ)) +
      (ContinuousLinearMap.proj 1 : (Fin 2 → ℂ) →L[ℂ] ℂ).smulRight (Pi.single 1 (1 : ℂ)) with hι
  have hιapp : ∀ p, ι p = p 0 • (Pi.single 0 (1 : ℂ) : Fin 3 → ℂ) + p 1 • Pi.single 1 1 := by
    intro p; simp [hι]
  have hι0 : ι 0 = 0 := map_zero ι
  have hev : ∀ᶠ p in 𝓝 (0 : Fin 2 → ℂ), ι p ∈ S := by
    have : ContinuousAt ι 0 := ι.continuous.continuousAt
    rw [← hι0] at h0
    exact this.eventually (hSo.mem_nhds h0)
  set Φ : (Fin 2 → ℂ) → F := fun p => fderiv ℂ g (ι p) (Pi.single 2 1) with hΦ
  have hΦd : DifferentiableAt ℂ Φ 0 := by
    have h1 : DifferentiableAt ℂ (fderiv ℂ g) (ι 0) := by
      rw [hι0]; exact (hfd 0 h0).differentiableAt
    have h2 := h1.comp (0 : Fin 2 → ℂ) ι.differentiableAt
    exact (ContinuousLinearMap.apply ℂ F (Pi.single 2 1 : Fin 3 → ℂ)).differentiableAt.comp 0 h2
  refine ⟨fderiv ℂ Φ 0, ?_⟩
  refine hΦd.hasFDerivAt.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  have hz : x + (ι p) 0 • k₁ + (ι p) 1 • k₂ + (ι p) 2 • d ∈ U := hp
  have hd := hf.differentiableAt (hU.mem_nhds hz)
  set L3 : (Fin 3 → ℂ) →L[ℂ] E :=
    (ContinuousLinearMap.proj 0 : (Fin 3 → ℂ) →L[ℂ] ℂ).smulRight k₁ +
      (ContinuousLinearMap.proj 1 : (Fin 3 → ℂ) →L[ℂ] ℂ).smulRight k₂ +
      (ContinuousLinearMap.proj 2 : (Fin 3 → ℂ) →L[ℂ] ℂ).smulRight d with hL3
  have hL3app : ∀ q, L3 q = q 0 • k₁ + q 1 • k₂ + q 2 • d := by intro q; simp [hL3]
  have hL : HasFDerivAt (fun q : Fin 3 → ℂ => x + q 0 • k₁ + q 1 • k₂ + q 2 • d) L3 (ι p) := by
    have := (L3.hasFDerivAt (x := ι p)).const_add x
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
    simp [hL3app, add_assoc]
  have hch : HasFDerivAt g ((fderiv ℂ f (x + (ι p) 0 • k₁ + (ι p) 1 • k₂ + (ι p) 2 • d)).comp L3)
      (ι p) := hd.hasFDerivAt.comp (ι p) hL
  simp only [hΦ]
  rw [hch.fderiv]
  simp [hL3app, hιapp]

/-- The second derivative along slices, `D²f(x)[k, d] := d/dμ Df(x + μ k) d |_{μ=0}`. -/
noncomputable def holoD2 (f : E → F) (x k d : E) : F :=
  deriv (fun μ : ℂ => fderiv ℂ f (x + μ • k) d) 0

section D2

variable {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : E} (hx : x ∈ U)
include hU hf hx

theorem hasDerivAt_holoD2 (k d : E) :
    HasDerivAt (fun μ : ℂ => fderiv ℂ f (x + μ • k) d) (holoD2 f x k d) 0 :=
  (differentiableAt_fderiv_line hU hf hx k d).hasDerivAt

theorem holoD2_add_right (k d d' : E) :
    holoD2 f x k (d + d') = holoD2 f x k d + holoD2 f x k d' := by
  have h := (hasDerivAt_holoD2 hU hf hx k d).add (hasDerivAt_holoD2 hU hf hx k d')
  have h2 : HasDerivAt (fun μ : ℂ => fderiv ℂ f (x + μ • k) (d + d'))
      (holoD2 f x k d + holoD2 f x k d') 0 := by
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun μ => ?_)
    simp
  exact h2.deriv

theorem holoD2_smul_right (k : E) (c : ℂ) (d : E) :
    holoD2 f x k (c • d) = c • holoD2 f x k d := by
  have h := (hasDerivAt_holoD2 hU hf hx k d).const_smul c
  have h2 : HasDerivAt (fun μ : ℂ => fderiv ℂ f (x + μ • k) (c • d)) (c • holoD2 f x k d) 0 := by
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun μ => ?_)
    simp
  exact h2.deriv

theorem holoD2_plane (k₁ k₂ d : E) :
    ∃ L : (Fin 2 → ℂ) →L[ℂ] F, ∀ v : Fin 2 → ℂ,
      holoD2 f x (v 0 • k₁ + v 1 • k₂) d = L v := by
  obtain ⟨L, hL⟩ := exists_hasFDerivAt_fderiv_plane hU hf hx k₁ k₂ d
  refine ⟨L, fun v => ?_⟩
  have hc : HasDerivAt (fun μ : ℂ => μ • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const v
  have hL' : HasFDerivAt (fun p : Fin 2 → ℂ => fderiv ℂ f (x + p 0 • k₁ + p 1 • k₂) d) L
      ((fun μ : ℂ => μ • v) 0) := by simpa using hL
  have h := hL'.comp_hasDerivAt (0 : ℂ) hc
  have h2 : HasDerivAt (fun μ : ℂ => fderiv ℂ f (x + μ • (v 0 • k₁ + v 1 • k₂)) d) (L v) 0 := by
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun μ => ?_)
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, smul_add, smul_smul, add_assoc]
  exact h2.deriv

theorem holoD2_add_left (k₁ k₂ d : E) :
    holoD2 f x (k₁ + k₂) d = holoD2 f x k₁ d + holoD2 f x k₂ d := by
  obtain ⟨L, hL⟩ := holoD2_plane hU hf hx k₁ k₂ d
  have e1 : holoD2 f x k₁ d = L (Pi.single 0 1) := by simpa using hL (Pi.single 0 1)
  have e2 : holoD2 f x k₂ d = L (Pi.single 1 1) := by simpa using hL (Pi.single 1 1)
  have e3 : holoD2 f x (k₁ + k₂) d = L (fun _ => 1) := by simpa using hL (fun _ => 1)
  rw [e1, e2, e3, ← map_add]
  congr 1
  ext i; fin_cases i <;> simp

theorem holoD2_smul_left (c : ℂ) (k d : E) :
    holoD2 f x (c • k) d = c • holoD2 f x k d := by
  obtain ⟨L, hL⟩ := holoD2_plane hU hf hx k 0 d
  have e1 : holoD2 f x k d = L (Pi.single 0 1) := by simpa using hL (Pi.single 0 1)
  have e2 : holoD2 f x (c • k) d = L (Pi.single 0 c) := by simpa using hL (Pi.single 0 c)
  rw [e1, e2, ← map_smul]
  congr 1
  ext i; fin_cases i <;> simp

end D2

section Bounds

variable {f : E → F} {U : Set E} {x : E} {ρ B : ℝ}

omit [CompleteSpace F] in
/-- Local boundedness data: a ball `B(x, 3ρ) ⊆ U` on which `f` is bounded. -/
theorem holo_local_bound (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hx : x ∈ U) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧ ball x (3 * ρ) ⊆ U ∧ ∀ z ∈ ball x (3 * ρ), ‖f z‖ ≤ B := by
  have hc : ContinuousAt f x := (hf.differentiableAt (hU.mem_nhds hx)).continuousAt
  have h1 : ∀ᶠ z in 𝓝 x, z ∈ U := hU.mem_nhds hx
  have hev : ∀ᶠ z in 𝓝 x, z ∈ U ∧ ‖f z‖ ≤ ‖f x‖ + 1 :=
    h1.and (hc.norm.eventually (eventually_le_nhds (lt_add_one ‖f x‖)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨ε / 3, ‖f x‖ + 1, by positivity, by positivity, ?_, ?_⟩
  · intro z hz; exact (hball (by simpa [mul_div_cancel₀] using hz)).1
  · intro z hz; exact (hball (by simpa [mul_div_cancel₀] using hz)).2

omit [CompleteSpace F] in
theorem norm_fderiv_le_local (hf : DifferentiableOn ℂ f U) (hρ : 0 < ρ) (hB : 0 ≤ B) (hsub : ball x
    (3 * ρ) ⊆ U)
    (hbd : ∀ z ∈ ball x (3 * ρ), ‖f z‖ ≤ B) {z : E} (hz : z ∈ ball x (2 * ρ)) :
    ‖fderiv ℂ f z‖ ≤ B / ρ := by
  refine norm_fderiv_le_div_of_ball hρ hB (hf.mono ?_) ?_
  · intro y hy
    refine hsub ?_
    rw [mem_ball] at hy hz ⊢
    have := dist_triangle y z x
    linarith
  · intro y hy
    refine hbd y ?_
    rw [mem_ball] at hy hz ⊢
    have := dist_triangle y z x
    linarith

theorem differentiableAt_fderiv_line_at (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {k d : E}
    {μ : ℂ} (hμ : x + μ • k ∈ U) :
    DifferentiableAt ℂ (fun ν : ℂ => fderiv ℂ f (x + ν • k) d) μ := by
  have h := differentiableAt_fderiv_line hU hf hμ k d
  have h' : DifferentiableAt ℂ (fun ν : ℂ => fderiv ℂ f ((x + μ • k) + ν • k) d)
      ((fun ν : ℂ => ν - μ) μ) := by simpa using h
  have hin : DifferentiableAt ℂ (fun ν : ℂ => ν - μ) μ := differentiableAt_id.sub_const μ
  have h2 : DifferentiableAt ℂ ((fun ν : ℂ => fderiv ℂ f ((x + μ • k) + ν • k) d) ∘
      (fun ν : ℂ => ν - μ)) μ :=
    DifferentiableAt.comp (x := μ) (f := fun ν : ℂ => ν - μ)
      (g := fun ν : ℂ => fderiv ℂ f ((x + μ • k) + ν • k) d) h' hin
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun ν => ?_)
  have e : x + ν • k = (x + μ • k) + (ν - μ) • k := by rw [sub_smul]; abel
  simp only [Function.comp_apply]
  rw [← e]

omit [CompleteSpace F] in
theorem taylorCoeff_one {g : ℂ → F} : taylorCoeff g 1 = deriv g 0 := by
  simp [taylorCoeff, iteratedDeriv_one]

theorem norm_holoD2_le (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hρ : 0 < ρ) (hB : 0 ≤ B)
    (hsub : ball x (3 * ρ) ⊆ U)
    (hbd : ∀ z ∈ ball x (3 * ρ), ‖f z‖ ≤ B) (k d : E) :
    ‖holoD2 f x k d‖ ≤ B / (2 * ρ ^ 2) * ‖k‖ * ‖d‖ := by
  have hx : x ∈ U := hsub (mem_ball_self (by positivity))
  by_cases hk : k = 0
  · subst hk; simp [holoD2]
  have hk0 : 0 < ‖k‖ := norm_pos_iff.mpr hk
  set R : ℝ := 2 * ρ / ‖k‖ with hR
  have hR0 : 0 < R := by positivity
  set g : ℂ → F := fun μ => fderiv ℂ f (x + μ • k) d with hg
  have hmem : ∀ μ ∈ ball (0 : ℂ) R, x + μ • k ∈ ball x (2 * ρ) := by
    intro μ hμ
    rw [mem_ball_zero_iff] at hμ
    rw [mem_ball_iff_norm]
    simp only [add_sub_cancel_left, norm_smul]
    calc ‖μ‖ * ‖k‖ < R * ‖k‖ := mul_lt_mul_of_pos_right hμ hk0
      _ = 2 * ρ := by rw [hR]; field_simp
  have hgd : DifferentiableOn ℂ g (ball 0 R) := fun μ hμ =>
    (differentiableAt_fderiv_line_at hU hf (d := d) (k := k)
      (hsub (ball_subset_ball (by linarith) (hmem μ hμ)))).differentiableWithinAt
  have hgb : ∀ μ ∈ ball (0 : ℂ) R, ‖g μ‖ ≤ B / ρ * ‖d‖ := fun μ hμ =>
    ((fderiv ℂ f (x + μ • k)).le_opNorm d).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_local hf hρ hB hsub hbd (hmem μ hμ))
        (norm_nonneg d))
  have := norm_taylorCoeff_le hR0 hgd hgb 1
  rw [taylorCoeff_one] at this
  have e : holoD2 f x k d = deriv g 0 := rfl
  rw [e]
  refine this.trans (le_of_eq ?_)
  rw [hR]; field_simp

theorem norm_fderiv_remainder_le (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hρ : 0 < ρ) (hB : 0
    ≤ B) (hsub : ball x (3 * ρ) ⊆ U)
    (hbd : ∀ z ∈ ball x (3 * ρ), ‖f z‖ ≤ B) {k : E} (hk : ‖k‖ < ρ) (d : E) :
    ‖fderiv ℂ f (x + k) d - fderiv ℂ f x d - holoD2 f x k d‖ ≤ B / (2 * ρ ^ 3) * ‖k‖ ^ 2 * ‖d‖ := by
  have hx : x ∈ U := hsub (mem_ball_self (by positivity))
  by_cases hk0' : k = 0
  · subst hk0'; simp [holoD2]
  have hk0 : 0 < ‖k‖ := norm_pos_iff.mpr hk0'
  set R : ℝ := 2 * ρ / ‖k‖ with hR
  have hR0 : 0 < R := by positivity
  have hR2 : 2 < R := by
    rw [hR, lt_div_iff₀ hk0]; linarith
  set g : ℂ → F := fun μ => fderiv ℂ f (x + μ • k) d with hg
  have hmem : ∀ μ ∈ ball (0 : ℂ) R, x + μ • k ∈ ball x (2 * ρ) := by
    intro μ hμ
    rw [mem_ball_zero_iff] at hμ
    rw [mem_ball_iff_norm]
    simp only [add_sub_cancel_left, norm_smul]
    calc ‖μ‖ * ‖k‖ < R * ‖k‖ := mul_lt_mul_of_pos_right hμ hk0
      _ = 2 * ρ := by rw [hR]; field_simp
  have hgd : DifferentiableOn ℂ g (ball 0 R) := fun μ hμ =>
    (differentiableAt_fderiv_line_at hU hf (d := d) (k := k)
      (hsub (ball_subset_ball (by linarith) (hmem μ hμ)))).differentiableWithinAt
  have hgb : ∀ μ ∈ ball (0 : ℂ) R, ‖g μ‖ ≤ B / ρ * ‖d‖ := fun μ hμ =>
    ((fderiv ℂ f (x + μ • k)).le_opNorm d).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_local hf hρ hB hsub hbd (hmem μ hμ))
        (norm_nonneg d))
  set M : ℝ := B / ρ * ‖d‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have hrem := norm_taylor_remainder_le (by linarith : 1 < R) hgd hgb (t := (1 : ℂ)) (by simp)
  have hc2 := norm_taylorCoeff_le hR0 hgd hgb 2
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, one_pow,
    one_smul] at hrem
  have h0 : taylorCoeff g 0 = g 0 := by simp [taylorCoeff]
  rw [h0, taylorCoeff_one] at hrem
  have hg1 : g 1 = fderiv ℂ f (x + k) d := by simp [hg]
  have hg0 : g 0 = fderiv ℂ f x d := by simp [hg]
  have hd1 : deriv g 0 = holoD2 f x k d := rfl
  have hid : fderiv ℂ f (x + k) d - fderiv ℂ f x d - holoD2 f x k d =
      (g 1 - (g 0 + deriv g 0 + taylorCoeff g 2)) + taylorCoeff g 2 := by
    rw [hg1, hg0, hd1]; abel
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  have hR3 : M / R ^ 3 / (1 - 1 / R) ≤ M / R ^ 2 := by
    have hne : R - 1 ≠ 0 := by linarith
    have e : M / R ^ 3 / (1 - 1 / R) = M / (R ^ 2 * (R - 1)) := by
      field_simp
    rw [e]
    refine div_le_div_of_nonneg_left hM0 (by positivity) ?_
    nlinarith [sq_nonneg R]
  have hsum : ‖g 1 - (g 0 + deriv g 0 + taylorCoeff g 2)‖ + ‖taylorCoeff g 2‖ ≤ 2 * (M / R ^ 2) :=
      by
    have := hrem.trans hR3
    have h2 : ‖taylorCoeff g 2‖ ≤ M / R ^ 2 := hc2
    linarith
  refine hsum.trans (le_of_eq ?_)
  rw [hM, hR]; field_simp

/-- **The derivative of a holomorphic map is complex differentiable** at every point of the open
domain (`f` holomorphic on `U` between complex Banach spaces). -/
theorem hasFDerivAt_fderiv_of_holomorphic (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hx : x ∈ U) : ∃ A : E →L[ℂ] (E →L[ℂ] F), HasFDerivAt (fderiv ℂ f) A x := by
  obtain ⟨ρ, B, hρ, hB, hsub, hbd⟩ := holo_local_bound hU hf hx
  have hx0 : x ∈ U := hx
  set C : ℝ := B / (2 * ρ ^ 2) with hC
  have hC0 : 0 ≤ C := by positivity
  let Dk : E → (E →L[ℂ] F) := fun k =>
    LinearMap.mkContinuous
      { toFun := fun d => holoD2 f x k d
        map_add' := fun d d' => holoD2_add_right hU hf hx k d d'
        map_smul' := fun c d => holoD2_smul_right hU hf hx k c d }
      (C * ‖k‖) (fun d => by
        have := norm_holoD2_le hU hf hρ hB hsub hbd k d
        simpa [hC, mul_assoc] using this)
  have hDk : ∀ k d, Dk k d = holoD2 f x k d := fun k d => rfl
  let A : E →L[ℂ] (E →L[ℂ] F) :=
    LinearMap.mkContinuous
      { toFun := Dk
        map_add' := fun k₁ k₂ => ContinuousLinearMap.ext fun d => by
          simp only [hDk, add_apply]; exact holoD2_add_left hU hf hx k₁ k₂ d
        map_smul' := fun c k => ContinuousLinearMap.ext fun d => by
          simp only [hDk, smul_apply, RingHom.id_apply]; exact holoD2_smul_left hU hf hx c k d }
      C (fun k => by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun d => ?_
        show ‖Dk k d‖ ≤ C * ‖k‖ * ‖d‖
        rw [hDk]
        have := norm_holoD2_le hU hf hρ hB hsub hbd k d
        simpa [hC, mul_assoc] using this)
  refine ⟨A, ?_⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set K : ℝ := B / (2 * ρ ^ 3) with hK
  have hK0 : 0 ≤ K := by positivity
  have hev : ∀ᶠ h : E in 𝓝 0, ‖h‖ < min ρ (c / (K + 1)) := by
    have : ContinuousAt (fun h : E => ‖h‖) 0 := continuous_norm.continuousAt
    exact this.eventually (eventually_lt_nhds (by simp; exact ⟨hρ, by positivity⟩))
  filter_upwards [hev] with h hh
  have hhρ : ‖h‖ < ρ := hh.trans_le (min_le_left _ _)
  have hhc : ‖h‖ < c / (K + 1) := hh.trans_le (min_le_right _ _)
  have key : ‖fderiv ℂ f (x + h) - fderiv ℂ f x - A h‖ ≤ K * ‖h‖ ^ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun d => ?_
    have := norm_fderiv_remainder_le hU hf hρ hB hsub hbd hhρ d
    simp only [sub_apply]
    have e : A h d = holoD2 f x h d := rfl
    rw [e]
    simpa [hK, mul_assoc, mul_comm, mul_left_comm] using this
  refine key.trans ?_
  have h1 : K * ‖h‖ ≤ c := by
    have := mul_lt_mul_of_pos_left hhc (by positivity : 0 < K + 1)
    rw [mul_div_cancel₀ _ (by positivity)] at this
    nlinarith [norm_nonneg h]
  nlinarith [norm_nonneg h]

end Bounds

/-- **`Df` is holomorphic**: the derivative of a holomorphic map on an open subset of a complex
normed space with values in a complex Banach space is again holomorphic (into the operator
space). -/
theorem differentiableOn_fderiv_of_holomorphic {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : DifferentiableOn ℂ (fderiv ℂ f) U := fun x hx => by
  obtain ⟨A, hA⟩ := hasFDerivAt_fderiv_of_holomorphic hU hf hx
  exact hA.differentiableAt.differentiableWithinAt

end KAM.Wave
