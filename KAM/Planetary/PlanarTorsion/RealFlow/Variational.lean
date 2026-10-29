/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Defs.SymplecticForm
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Kepler.Basic
public import KAM.ODE.Basic
public import KAM.Planetary.PlanarTorsion.RealFlow.Analytic

/-!
# Planar quartic torsion: variational equation and symplecticity (package R3)

Blueprint P, Part 11b (`bpP:p11b:e-ode`, package R3).  For the jointly analytic local Hamiltonian
flow `Φ` of `p11c_analytic_hamiltonian_flow` we prove

* `p11cVar_variational`: the variational equation `∂ₜ DΦₜ(y) u = D X_H (Φₜ y) (DΦₜ(y) u)`,
  obtained by differentiating `∂ₜ Φ = X_H ∘ Φ` in the data and using symmetry of the second
  derivative of the (analytic) flow;
* `p11cVar_form_add_form_eq_zero`: `Ω (DX_H w, v) + Ω (w, DX_H v) = 0`, i.e. Hessian symmetry
  of the real analytic `H`;
* `p11cVar_form_const`: `t ↦ Ω (DΦₜ u, DΦₜ v)` is constant (frozen form conservation);
* `real_analytic_hamiltonian_local_flow`: the signed real bridge of the design.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

variable {d : ℕ}

/-! ### Algebra of the standard form -/

/-- A linear functional on `Phase d` is determined by its values on the coordinate vectors. -/
theorem p11cVar_clm_eq_sum (L : Phase d →L[ℝ] ℝ) (w : Phase d) :
    L w = ∑ i, (w.1 i * L (Pi.single i 1, 0) + w.2 i * L (0, Pi.single i 1)) := by
  have h1 : ((w.1, 0) : Phase d) = ∑ i, w.1 i • ((Pi.single i 1 : Fin d → ℝ), (0 : Fin d → ℝ)) := by
    ext j
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  have h2 : ((0, w.2) : Phase d) = ∑ i, w.2 i • ((0 : Fin d → ℝ), (Pi.single i 1 : Fin d → ℝ)) := by
    ext j
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hw : w = (w.1, 0) + (0, w.2) := by simp
  conv_lhs => rw [hw, map_add, h1, h2]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.sum_add_distrib]

/-- The linearisation `M B` of a Hamiltonian field at a point with Hessian `B`. -/
def p11cVarLin (B : Phase d →L[ℝ] Phase d →L[ℝ] ℝ) (w : Phase d) : Phase d :=
  (fun i => B w (0, Pi.single i 1), fun i => -B w (Pi.single i 1, 0))

theorem p11cVar_form_lin_left (B : Phase d →L[ℝ] Phase d →L[ℝ] ℝ) (w v : Phase d) :
    symplecticForm (p11cVarLin B w) v = - B w v := by
  rw [p11cVar_clm_eq_sum (B w) v]
  simp only [symplecticForm, p11cVarLin, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem p11cVar_form_lin_right (B : Phase d →L[ℝ] Phase d →L[ℝ] ℝ) (w v : Phase d) :
    symplecticForm w (p11cVarLin B v) = B v w := by
  rw [p11cVar_clm_eq_sum (B v) w]
  simp only [symplecticForm, p11cVarLin]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Hessian symmetry gives `Ω (M w, v) + Ω (w, M v) = 0`. -/
theorem p11cVar_form_add_form_eq_zero (B : Phase d →L[ℝ] Phase d →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (w v : Phase d) :
    symplecticForm (p11cVarLin B w) v + symplecticForm w (p11cVarLin B v) = 0 := by
  rw [p11cVar_form_lin_left, p11cVar_form_lin_right, hB v w]
  ring

/-- Derivative of the standard form along two differentiable curves. -/
theorem p11cVar_hasDerivAt_form {a b : ℝ → Phase d} {a' b' : Phase d} {t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => symplecticForm (a s) (b s))
      (symplecticForm a' (b t) + symplecticForm (a t) b') t := by
  have h1 : ∀ i, HasDerivAt (fun s => (a s).1 i) (a'.1 i) t := fun i =>
    hasDerivAt_pi.1 (hasFDerivAt_fst.comp_hasDerivAt t ha) i
  have h2 : ∀ i, HasDerivAt (fun s => (a s).2 i) (a'.2 i) t := fun i =>
    hasDerivAt_pi.1 (hasFDerivAt_snd.comp_hasDerivAt t ha) i
  have h3 : ∀ i, HasDerivAt (fun s => (b s).1 i) (b'.1 i) t := fun i =>
    hasDerivAt_pi.1 (hasFDerivAt_fst.comp_hasDerivAt t hb) i
  have h4 : ∀ i, HasDerivAt (fun s => (b s).2 i) (b'.2 i) t := fun i =>
    hasDerivAt_pi.1 (hasFDerivAt_snd.comp_hasDerivAt t hb) i
  have := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin d)))
    (A := fun i s => (a s).2 i * (b s).1 i - (a s).1 i * (b s).2 i)
    (A' := fun i => a'.2 i * (b t).1 i + (a t).2 i * b'.1 i -
      (a'.1 i * (b t).2 i + (a t).1 i * b'.2 i))
    (fun i _ => ((h2 i).mul (h3 i)).sub ((h1 i).mul (h4 i)))
  refine this.congr_deriv ?_
  simp only [symplecticForm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### Linearisation of the Hamiltonian field -/

/-- `fderiv (hamiltonianVectorField H)` is the linearisation of the Hessian of `H`. -/
theorem p11cVar_hasFDerivAt_field {H : Phase d → ℝ} {z : Phase d} (hH : AnalyticAt ℝ H z) :
    HasFDerivAt (hamiltonianVectorField H)
      (ContinuousLinearMap.prod
        (ContinuousLinearMap.pi fun i => (ContinuousLinearMap.apply ℝ ℝ
          ((0 : Fin d → ℝ), (Pi.single i 1 : Fin d → ℝ))).comp (fderiv ℝ (fderiv ℝ H) z))
        (ContinuousLinearMap.pi fun i => -((ContinuousLinearMap.apply ℝ ℝ
          ((Pi.single i 1 : Fin d → ℝ), (0 : Fin d → ℝ))).comp (fderiv ℝ (fderiv ℝ H) z)))) z := by
  have hD : HasFDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) z) z :=
    (hH.fderiv.differentiableAt).hasFDerivAt
  have hc : ∀ v : Phase d, HasFDerivAt (fun z => fderiv ℝ H z v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ H) z)) z := fun v =>
    (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp z hD
  refine HasFDerivAt.prodMk ?_ ?_
  · exact hasFDerivAt_pi'.2 fun i => hc _
  · exact hasFDerivAt_pi'.2 fun i => (hc _).neg

/-- The derivative of the Hamiltonian field at an analytic point is `p11cVarLin` of the Hessian. -/
theorem p11cVar_fderiv_field {H : Phase d → ℝ} {z : Phase d} (hH : AnalyticAt ℝ H z)
    (w : Phase d) :
    fderiv ℝ (hamiltonianVectorField H) z w = p11cVarLin (fderiv ℝ (fderiv ℝ H) z) w := by
  rw [(p11cVar_hasFDerivAt_field hH).fderiv]
  rfl

/-- Hessian symmetry of an analytic function. -/
theorem p11cVar_hessian_symm {H : Phase d → ℝ} {z : Phase d} (hH : AnalyticAt ℝ H z)
    (v w : Phase d) : fderiv ℝ (fderiv ℝ H) z v w = fderiv ℝ (fderiv ℝ H) z w v :=
  hH.contDiffAt.isSymmSndFDerivAt_of_omega v w

/-- `Ω (DX_H w, v) + Ω (w, DX_H v) = 0` at an analytic point of `H`. -/
theorem p11cVar_field_form {H : Phase d → ℝ} {z : Phase d} (hH : AnalyticAt ℝ H z)
    (w v : Phase d) :
    symplecticForm (fderiv ℝ (hamiltonianVectorField H) z w) v +
      symplecticForm w (fderiv ℝ (hamiltonianVectorField H) z v) = 0 := by
  rw [p11cVar_fderiv_field hH, p11cVar_fderiv_field hH]
  exact p11cVar_form_add_form_eq_zero _ (p11cVar_hessian_symm hH) w v

/-! ### The variational equation -/

section Flow

variable {H : Phase d → ℝ} {W : Set (Phase d)} {x : Phase d} {r T : ℝ}
  {Φ : ℝ → Phase d → Phase d}

/-- Jacobian of the time-`s` map in direction `u` equals the joint derivative on `(s, y)`. -/
theorem p11cVar_fderiv_slice
    (hΦ : AnalyticOnNhd ℝ (fun u : ℝ × Phase d => Φ u.1 u.2) (Ioo (-T) T ×ˢ ball x r))
    {s : ℝ} {y : Phase d} (hs : s ∈ Ioo (-T) T) (hy : y ∈ ball x r) (u : Phase d) :
    fderiv ℝ (Φ s) y u = fderiv ℝ (fun p : ℝ × Phase d => Φ p.1 p.2) (s, y) (0, u) := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × Phase d => Φ p.1 p.2) (s, y) :=
    (hΦ (s, y) ⟨hs, hy⟩).differentiableAt
  have := hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)
  have h2 : fderiv ℝ (Φ s) y = _ := this.fderiv
  rw [h2]
  simp

/-- The variational equation `∂ₜ DΦₜ(y) u = DX_H(Φₜ y) (DΦₜ(y) u)`. -/
theorem p11cVar_variational
    (hH : AnalyticOnNhd ℝ H W)
    (hΦ : AnalyticOnNhd ℝ (fun u : ℝ × Phase d => Φ u.1 u.2) (Ioo (-T) T ×ˢ ball x r))
    (hsol : ∀ y ∈ ball x r,
      IsSolutionIn (hamiltonianVectorField H) W (Ioo (-T) T) (fun t => Φ t y))
    {y : Phase d} (hy : y ∈ ball x r) {t : ℝ} (ht : t ∈ Ioo (-T) T) (u : Phase d) :
    HasDerivAt (fun s => fderiv ℝ (Φ s) y u)
      (fderiv ℝ (hamiltonianVectorField H) (Φ t y) (fderiv ℝ (Φ t) y u)) t := by
  set Ψ : ℝ × Phase d → Phase d := fun p => Φ p.1 p.2 with hΨ
  have hUo : IsOpen (Ioo (-T) T ×ˢ ball x r) := isOpen_Ioo.prod isOpen_ball
  have hp : (t, y) ∈ Ioo (-T) T ×ˢ ball x r := ⟨ht, hy⟩
  have hΨa : AnalyticAt ℝ Ψ (t, y) := hΦ _ hp
  have hHa : AnalyticAt ℝ H (Φ t y) := hH _ ((hsol y hy t ht).1)
  -- Step 1: `fderiv Ψ q (1,0) = X (Ψ q)` on the open set.
  have hstep1 : ∀ q ∈ Ioo (-T) T ×ˢ ball x r,
      fderiv ℝ Ψ q (1, 0) = hamiltonianVectorField H (Ψ q) := by
    intro q hq
    obtain ⟨s, z⟩ := q
    have hd : DifferentiableAt ℝ Ψ (s, z) := (hΦ (s, z) hq).differentiableAt
    have hg : HasDerivAt (fun s : ℝ => ((s, z) : ℝ × Phase d)) ((1 : ℝ), (0 : Phase d)) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s z)
    have h1 := hd.hasFDerivAt.comp_hasDerivAt s hg
    have h2 := (hsol z hq.2 s hq.1).2
    exact h1.unique h2
  -- Step 2: differentiate in the data direction `(0,u)`.
  have hD2 : HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) (t, y)) (t, y) :=
    hΨa.fderiv.differentiableAt.hasFDerivAt
  have hL : HasFDerivAt (fun q => fderiv ℝ Ψ q (1, 0))
      ((ContinuousLinearMap.apply ℝ (Phase d) ((1 : ℝ), (0 : Phase d))).comp
        (fderiv ℝ (fderiv ℝ Ψ) (t, y))) (t, y) :=
    (ContinuousLinearMap.apply ℝ (Phase d) ((1 : ℝ), (0 : Phase d))).hasFDerivAt.comp _ hD2
  have hXd : HasFDerivAt (hamiltonianVectorField H) (fderiv ℝ (hamiltonianVectorField H) (Φ t y))
      (Φ t y) := (p11c_hamField_analyticAt hHa).differentiableAt.hasFDerivAt
  have hR : HasFDerivAt (fun q => hamiltonianVectorField H (Ψ q))
      ((fderiv ℝ (hamiltonianVectorField H) (Φ t y)).comp (fderiv ℝ Ψ (t, y))) (t, y) :=
    HasFDerivAt.comp (g := hamiltonianVectorField H) (f := Ψ) (t, y) hXd
      hΨa.differentiableAt.hasFDerivAt
  have hev : (fun q => fderiv ℝ Ψ q (1, 0)) =ᶠ[𝓝 (t, y)]
      fun q => hamiltonianVectorField H (Ψ q) :=
    Filter.eventually_of_mem (hUo.mem_nhds hp) hstep1
  have hLR := hL.unique (hR.congr_of_eventuallyEq hev)
  have h3 := congrArg (fun L => L ((0 : ℝ), u)) hLR
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at h3
  -- Step 3: symmetry of the second derivative.
  have hsym : fderiv ℝ (fderiv ℝ Ψ) (t, y) (0, u) (1, 0) =
      fderiv ℝ (fderiv ℝ Ψ) (t, y) (1, 0) (0, u) :=
    hΨa.contDiffAt.isSymmSndFDerivAt_of_omega _ _
  -- Step 4: `s ↦ fderiv Ψ (s, y) (0,u)` has the derivative `D²Ψ (1,0) (0,u)`.
  have hg : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × Phase d)) ((1 : ℝ), (0 : Phase d)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  have hC : HasDerivAt (fun s : ℝ => fderiv ℝ Ψ (s, y) (0, u))
      (fderiv ℝ (fderiv ℝ Ψ) (t, y) (1, 0) (0, u)) t := by
    have h4 := hD2.comp_hasDerivAt t hg
    exact (ContinuousLinearMap.apply ℝ (Phase d) ((0 : ℝ), u)).hasFDerivAt.comp_hasDerivAt
      t h4
  have hfin : fderiv ℝ (fderiv ℝ Ψ) (t, y) (1, 0) (0, u) =
      fderiv ℝ (hamiltonianVectorField H) (Φ t y) (fderiv ℝ (Φ t) y u) := by
    rw [← hsym, h3, p11cVar_fderiv_slice hΦ ht hy]
  rw [hfin] at hC
  refine hC.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact p11cVar_fderiv_slice hΦ hs hy u

/-- Frozen-form conservation: `t ↦ Ω (DΦₜ(y) u, DΦₜ(y) v)` has derivative zero. -/
theorem p11cVar_form_hasDerivAt
    (hH : AnalyticOnNhd ℝ H W)
    (hΦ : AnalyticOnNhd ℝ (fun u : ℝ × Phase d => Φ u.1 u.2) (Ioo (-T) T ×ˢ ball x r))
    (hsol : ∀ y ∈ ball x r,
      IsSolutionIn (hamiltonianVectorField H) W (Ioo (-T) T) (fun t => Φ t y))
    {y : Phase d} (hy : y ∈ ball x r) {t : ℝ} (ht : t ∈ Ioo (-T) T) (u v : Phase d) :
    HasDerivAt (fun s => symplecticForm (fderiv ℝ (Φ s) y u) (fderiv ℝ (Φ s) y v)) 0 t := by
  have h := p11cVar_hasDerivAt_form (p11cVar_variational hH hΦ hsol hy ht u)
    (p11cVar_variational hH hΦ hsol hy ht v)
  rwa [p11cVar_field_form (hH _ ((hsol y hy t ht).1))] at h

/-- Frozen-form conservation: the form `Ω (DΦₜ(y) u, DΦₜ(y) v)` is independent of `t`. -/
theorem p11cVar_form_const
    (hH : AnalyticOnNhd ℝ H W)
    (hΦ : AnalyticOnNhd ℝ (fun u : ℝ × Phase d => Φ u.1 u.2) (Ioo (-T) T ×ˢ ball x r))
    (hsol : ∀ y ∈ ball x r,
      IsSolutionIn (hamiltonianVectorField H) W (Ioo (-T) T) (fun t => Φ t y))
    (hT : 0 < T) {y : Phase d} (hy : y ∈ ball x r) {t : ℝ} (ht : t ∈ Ioo (-T) T)
    (u v : Phase d) :
    symplecticForm (fderiv ℝ (Φ t) y u) (fderiv ℝ (Φ t) y v) =
      symplecticForm (fderiv ℝ (Φ 0) y u) (fderiv ℝ (Φ 0) y v) := by
  have hd : ∀ s ∈ Ioo (-T) T,
      HasDerivAt (fun s => symplecticForm (fderiv ℝ (Φ s) y u) (fderiv ℝ (Φ s) y v)) 0 s :=
    fun s hs => p11cVar_form_hasDerivAt hH hΦ hsol hy hs u v
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (isPreconnected_Ioo)
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => by simp [(hd s hs).deriv]) ht ⟨by linarith, hT⟩

/-- Symplecticity of each time-`t` map of the flow on the data ball. -/
theorem p11cVar_isSymplecticOn
    (hH : AnalyticOnNhd ℝ H W)
    (hΦ : AnalyticOnNhd ℝ (fun u : ℝ × Phase d => Φ u.1 u.2) (Ioo (-T) T ×ˢ ball x r))
    (hsol : ∀ y ∈ ball x r,
      IsSolutionIn (hamiltonianVectorField H) W (Ioo (-T) T) (fun t => Φ t y))
    (hT : 0 < T) (h0 : ∀ y ∈ ball x r, Φ 0 y = y) {t : ℝ} (ht : t ∈ Ioo (-T) T) :
    IsSymplecticOn 1 (Φ t) (ball x r) := by
  intro y hy u v
  rw [p11cVar_form_const hH hΦ hsol hT hy ht u v]
  have hev : Φ 0 =ᶠ[𝓝 y] id :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hy) fun z hz => h0 z hz
  rw [hev.fderiv_eq, fderiv_id]
  simp

end Flow

/-- New real parametric ODE bridge: local solution/existence, analytic dependence,
variational equation and symplecticity are to be proved, not assumed. -/
theorem real_analytic_hamiltonian_local_flow {d : ℕ} {W : Set (Phase d)} (hW : IsOpen W)
    (H : Phase d → ℝ) (hH : AnalyticOnNhd ℝ H W) (x : Phase d) (hx : x ∈ W) :
    ∃ r T : ℝ, 0 < r ∧ 0 < T ∧ ∃ Phi : ℝ → Phase d → Phase d,
      AnalyticOnNhd ℝ (fun u : ℝ × Phase d => Phi u.1 u.2) (Ioo (-T) T ×ˢ ball x r) ∧
      (∀ y ∈ ball x r, Phi 0 y = y ∧
        IsSolutionIn (hamiltonianVectorField H) W (Ioo (-T) T) (fun t => Phi t y)) ∧
      (∀ t ∈ Ioo (-T) T, IsSymplecticOn 1 (Phi t) (ball x r)) := by
  obtain ⟨r, T, hr, hT, Phi, han, hs⟩ := p11c_analytic_hamiltonian_flow hW hH hx
  exact ⟨r, T, hr, hT, Phi, han, hs, fun t ht =>
    p11cVar_isSymplecticOn hH han (fun y hy => (hs y hy).2) hT (fun y hy => (hs y hy).1) ht⟩

end KAM.Planetary
