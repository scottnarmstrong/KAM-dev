/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.SpectralAdapter
public import KAM.Planetary.SecularForm.Coefficients
public import KAM.Planetary.SecularSpectrum.Lift
public import KAM.Planetary.SecularSpectrum.Transport
public import KAM.Planetary.Hamiltonian.Chart

/-!
# Planar quartic torsion: the global eigenframe and the rotation lift (P11C, package T14)

Blueprint P, Part 11b (`bpP:p11b:bt-rot`, `bt-rot#lift`): the explicit oriented eigenframe
`p11c_frame` built from the nonzero vector `(-Q₁₂, Q₁₁ - σ₁)`, and `global_planar_frame`, which
proves that it is analytic on the axis cone, special orthogonal and sorts the diagonalisation of
`p11c_Q`.  Positivity of `Q₁₂` gives non-vanishing on the whole cone, so no covering-space or
angle-lifting argument is needed.  `p11c_rotationLift` is the concrete inverse rotation lift of
Part 9 in the frozen assembled coordinates; `p11c_rotationLift_eq_liftInv` identifies it with the
upstream `SecularSpectrum.liftInv` of the frame family, and `p11c_rotationLift_chart` transports the
Part-9 lift theorem (chart, injectivity, action preservation, translation covariance).
-/

@[expose] public noncomputable section
open Set Metric Real Function Filter
open scoped Topology
namespace KAM.Planetary
open KAM KAM.Kepler

def p11c_rotateSlow (U : Matrix (Fin 2) (Fin 2) ℝ) (z : Phase 2) : Phase 2 :=
  (U.mulVec z.1, U.mulVec z.2)

/-- Exact explicit global SO(2) eigenframe avoids the unpaid covering-space argument. -/
def p11c_frame (p : PlanarData) (a : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let Q := p11c_Q p a
  let s := p11c_sigma p a 0
  let v : Fin 2 → ℝ := ![-Q 0 1, Q 0 0 - s]
  let e := (sqrt (∑ i, v i ^ 2))⁻¹ • v
  !![e 0, -e 1; e 1, e 0]

/-! ### Positivity and the eigenvector -/

theorem p11c_Q_off_pos (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes) :
    0 < p11c_Q p a 0 1 := by
  rw [← p11c_Q_symm, p11c_Q_eq_coeffs p hp ha]
  have hax := p11c_axes_mem ha
  set D := p11cSecularData p hp
  rw [SecularSpectrum.coeffs_two_off10]
  have := SecularSpectrum.pairB_pos D hax (j := 0) (k := 1) (by decide)
  have := SecularSpectrum.action_pos D hax 0
  have := SecularSpectrum.action_pos D hax 1
  positivity

theorem p11c_frame_norm_pos (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ}
    (ha : a ∈ p11c_axes) :
    0 < (-p11c_Q p a 0 1) ^ 2 + (p11c_Q p a 0 0 - p11c_sigma p a 0) ^ 2 := by
  have h := p11c_Q_off_pos p hp ha
  nlinarith [mul_pos h h, sq_nonneg (p11c_Q p a 0 0 - p11c_sigma p a 0)]

/-- The unnormalised eigenvector `(-Q₁₂, Q₁₁ - σ₁)` is a `σ₁`-eigenvector. -/
theorem p11c_frame_eigen (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes) :
    (p11c_Q p a).mulVec ![-p11c_Q p a 0 1, p11c_Q p a 0 0 - p11c_sigma p a 0] =
      p11c_sigma p a 0 • ![-p11c_Q p a 0 1, p11c_Q p a 0 0 - p11c_sigma p a 0] := by
  obtain ⟨hs, hd⟩ := p11c_sigma_sum_prod p hp ha
  have hq := p11c_Q_symm p a
  funext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hq]
    linear_combination p11c_sigma p a 0 * hs - hd

/-! ### Analyticity on the axis cone -/

theorem p11c_axes_isOpen : IsOpen p11c_axes := by
  have h0 : IsOpen {a : Fin 2 → ℝ | 0 < a 0} := isOpen_lt continuous_const (by fun_prop)
  have h1 : IsOpen {a : Fin 2 → ℝ | a 0 < a 1} := isOpen_lt (by fun_prop) (by fun_prop)
  exact h0.inter h1

theorem p11c_Q_analyticAt (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes)
    (i j : Fin 2) : AnalyticAt ℝ (fun b => p11c_Q p b i j) a := by
  have h := SecularForm.coeffs_analytic (p11cSecularData p hp) a (p11c_axes_mem ha)
  have h' := analyticAt_pi_iff.1 (analyticAt_pi_iff.1 h i) j
  refine h'.congr ?_
  filter_upwards [p11c_axes_isOpen.mem_nhds ha] with b hb
  exact (congrFun (congrFun (p11c_Q_eq_coeffs p hp hb) i) j).symm

theorem p11c_sigma0_analyticAt (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ}
    (ha : a ∈ p11c_axes) : AnalyticAt ℝ (fun b => p11c_sigma p b 0) a := by
  have h00 := p11c_Q_analyticAt p hp ha 0 0
  have h11 := p11c_Q_analyticAt p hp ha 1 1
  have h01 := p11c_Q_analyticAt p hp ha 0 1
  have hpos : 0 < (p11c_Q p a 0 0 - p11c_Q p a 1 1) ^ 2 + 4 * p11c_Q p a 0 1 ^ 2 := by
    have := p11c_Q_off_pos p hp ha
    nlinarith [sq_nonneg (p11c_Q p a 0 0 - p11c_Q p a 1 1), mul_pos this this]
  have hin : AnalyticAt ℝ (fun b => (p11c_Q p b 0 0 - p11c_Q p b 1 1) ^ 2 +
      4 * p11c_Q p b 0 1 ^ 2) a := ((h00.sub h11).pow 2).add (analyticAt_const.mul (h01.pow 2))
  have hsq := (hin.contDiffAt.sqrt hpos.ne').analyticAt
  exact (((h00.add h11).sub hsq).div analyticAt_const two_ne_zero).congr
    (Eventually.of_forall fun b => by simp [p11c_sigma])

theorem p11c_frame_analyticAt (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ}
    (ha : a ∈ p11c_axes) (i j : Fin 2) :
    AnalyticAt ℝ (fun b => p11c_frame p b i j) a := by
  have h01 := p11c_Q_analyticAt p hp ha 0 1
  have h00 := p11c_Q_analyticAt p hp ha 0 0
  have hs := p11c_sigma0_analyticAt p hp ha
  have hv1 : AnalyticAt ℝ (fun b => -p11c_Q p b 0 1) a := h01.neg
  have hv2 : AnalyticAt ℝ (fun b => p11c_Q p b 0 0 - p11c_sigma p b 0) a := h00.sub hs
  have hN : AnalyticAt ℝ (fun b => (-p11c_Q p b 0 1) ^ 2 +
      (p11c_Q p b 0 0 - p11c_sigma p b 0) ^ 2) a := (hv1.pow 2).add (hv2.pow 2)
  have hc : AnalyticAt ℝ (fun b => (sqrt ((-p11c_Q p b 0 1) ^ 2 +
      (p11c_Q p b 0 0 - p11c_sigma p b 0) ^ 2))⁻¹) a := by
    have hNp := p11c_frame_norm_pos p hp ha
    exact (hN.contDiffAt.sqrt hNp.ne').analyticAt.inv (Real.sqrt_pos.2 hNp).ne'
  have e0 := hc.mul hv1
  have e1 := hc.mul hv2
  fin_cases i <;> fin_cases j
  · exact e0.congr (Eventually.of_forall fun b => by simp [p11c_frame, Fin.sum_univ_two])
  · exact e1.neg.congr (Eventually.of_forall fun b => by simp [p11c_frame, Fin.sum_univ_two])
  · exact e1.congr (Eventually.of_forall fun b => by simp [p11c_frame, Fin.sum_univ_two])
  · exact e0.congr (Eventually.of_forall fun b => by simp [p11c_frame, Fin.sum_univ_two])

/-! ### The frame theorem and the rotation lift -/

theorem global_planar_frame (p : PlanarData) (hp : p.Valid) :
    (∀ i j, AnalyticOnNhd ℝ (fun a => p11c_frame p a i j) p11c_axes) ∧ ∀ a ∈ p11c_axes,
      (p11c_frame p a).transpose * p11c_frame p a = 1 ∧ (p11c_frame p a).det = 1 ∧
      (p11c_frame p a).transpose * p11c_Q p a * p11c_frame p a =
        Matrix.diagonal (p11c_sigma p a) := by
  refine ⟨fun i j a ha => p11c_frame_analyticAt p hp ha i j, fun a ha => ?_⟩
  have hN := p11c_frame_norm_pos p hp ha
  have heig := p11c_frame_eigen p hp ha
  obtain ⟨hs, -⟩ := p11c_sigma_sum_prod p hp ha
  have hq := p11c_Q_symm p a
  obtain ⟨c, hc⟩ : ∃ c : ℝ,
      c = (sqrt ((-p11c_Q p a 0 1) ^ 2 + (p11c_Q p a 0 0 - p11c_sigma p a 0) ^ 2))⁻¹ := ⟨_, rfl⟩
  have hc2 : c ^ 2 * ((-p11c_Q p a 0 1) ^ 2 + (p11c_Q p a 0 0 - p11c_sigma p a 0) ^ 2) = 1 := by
    rw [hc, inv_pow, Real.sq_sqrt hN.le]
    exact inv_mul_cancel₀ hN.ne'
  have hf : p11c_frame p a = !![c * -p11c_Q p a 0 1, -(c * (p11c_Q p a 0 0 - p11c_sigma p a 0));
      c * (p11c_Q p a 0 0 - p11c_sigma p a 0), c * -p11c_Q p a 0 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [p11c_frame, Fin.sum_univ_two, hc]
  have h1 := congrFun heig 0
  have h2 := congrFun heig 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hq] at h1 h2
  obtain ⟨e0, he0⟩ : ∃ e : ℝ, e = c * -p11c_Q p a 0 1 := ⟨_, rfl⟩
  obtain ⟨e1, he1⟩ : ∃ e : ℝ, e = c * (p11c_Q p a 0 0 - p11c_sigma p a 0) := ⟨_, rfl⟩
  rw [← he0, ← he1] at hf
  have hn : e0 ^ 2 + e1 ^ 2 = 1 := by rw [he0, he1]; linear_combination hc2
  have g1 : p11c_Q p a 0 0 * e0 + p11c_Q p a 0 1 * e1 = p11c_sigma p a 0 * e0 := by
    rw [he0, he1]; linear_combination c * h1
  have g2 : p11c_Q p a 0 1 * e0 + p11c_Q p a 1 1 * e1 = p11c_sigma p a 0 * e1 := by
    rw [he0, he1]; linear_combination c * h2
  rw [hf]
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | ring1 | linear_combination hn
  · rw [Matrix.det_fin_two_of]; linear_combination hn
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hq]
    · linear_combination e0 * g1 + e1 * g2 + p11c_sigma p a 0 * hn
    · linear_combination (-e1) * g1 + e0 * g2
    · linear_combination (-e1) * g1 + e0 * g2
    · linear_combination (p11c_Q p a 0 0 + p11c_Q p a 1 1) * hn - e0 * g1 - e1 * g2 -
        p11c_sigma p a 0 * hn - hs

/-- The inverse rotation lift of Part 9, in the existing frozen assembled coordinates. -/
def p11c_rotationLift (p : PlanarData) (w : Phase (2 + 2)) : Phase (2 + 2) :=
  let I : Fin 2 → ℝ := fun i => w.2 (Fin.castAdd 2 i)
  let lam : Fin 2 → ℝ := fun i => w.1 (Fin.castAdd 2 i)
  let z : Phase 2 := (fun i => w.1 (Fin.natAdd 2 i), fun i => w.2 (Fin.natAdd 2 i))
  let U := p11c_frame p (p.axes I)
  let H : Fin 2 → ℝ := fun l => ∑ i, ∑ j, ∑ k,
    z.2 i * U k i * fderiv ℝ (fun J => p11c_frame p (p.axes J) k j) I (Pi.single l 1) * z.1 j
  let Z := p11c_rotateSlow U z
  assemble I (lam + H) Z.2 Z.1

/-! ### Identification with the Part-9 inverse lift -/

open scoped Matrix.Norms.Elementwise

/-- The open set of actions whose axes lie in the cone `p11c_axes` (domain of the frame family). -/
def p11c_frameActionDomain (p : PlanarData) : Set (Fin 2 → ℝ) := {I | p.axes I ∈ p11c_axes}

/-- `p11c_frameActionDomain p` is open: `p.axes` is continuous and `p11c_axes` is open. -/
theorem p11c_frameActionDomain_isOpen (p : PlanarData) : IsOpen (p11c_frameActionDomain p) := by
  refine p11c_axes_isOpen.preimage ?_
  refine continuous_pi fun i => ?_
  unfold PlanarData.axes
  fun_prop

/-- The axis map `I ↦ p.axes I` is analytic (on valid data). -/
theorem p11c_axes_map_analyticAt (p : PlanarData) (hp : p.Valid) (I : Fin 2 → ℝ) :
    AnalyticAt ℝ p.axes I := by
  refine analyticAt_pi_iff.2 fun i => ?_
  have hk : p.m i ^ 2 * p.kappa ≠ 0 := by
    have := hp.2.2 i
    have h2 : 0 < p.kappa := mul_pos hp.1 hp.2.1
    positivity
  exact (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).analyticAt I).pow
    2).div analyticAt_const hk

/-- Frame family regularity: `I ↦ p11c_frame p (p.axes I)` is analytic on the frame domain. -/
theorem p11c_frameFamily_analyticOnNhd (p : PlanarData) (hp : p.Valid) :
    AnalyticOnNhd ℝ (fun I => p11c_frame p (p.axes I)) (p11c_frameActionDomain p) := by
  intro I hI
  refine analyticAt_pi_iff.2 fun i => analyticAt_pi_iff.2 fun j => ?_
  exact AnalyticAt.comp (g := fun b => p11c_frame p b i j) (f := p.axes)
    (p11c_frame_analyticAt p hp hI i j) (p11c_axes_map_analyticAt p hp I)

/-- The frame family is special orthogonal on the frame domain (from `global_planar_frame`). -/
theorem p11c_frameFamily_isSO (p : PlanarData) (hp : p.Valid) :
    ∀ I ∈ p11c_frameActionDomain p, SecularSpectrum.isSO (p11c_frame p (p.axes I)) := fun _ hI =>
  let h := (global_planar_frame p hp).2 _ hI
  ⟨h.1, h.2.1⟩

/-- Part 9 identification (`bpP:p9:lift`, design U9): on valid data and actions whose axes lie
in `p11c_axes`, the concrete `p11c_rotationLift` is the upstream `SecularSpectrum.liftInv` of
the frame family.  Differentiability of the family comes from `global_planar_frame`'s analytic
frame and the analytic axis map; the scalar entry derivatives of the signed formula are the entries
of the matrix derivative via `SecularSpectrum.fderiv_entry`. -/
theorem p11c_rotationLift_eq_liftInv (p : PlanarData) (hp : p.Valid) (w : Phase (2 + 2))
    (hw : fast w.2 ∈ p11c_frameActionDomain p) :
    p11c_rotationLift p w = SecularSpectrum.liftInv (fun I => p11c_frame p (p.axes I)) w := by
  have hd := (p11c_frameFamily_analyticOnNhd p hp _ hw).differentiableAt
  have hf : (fun i => w.2 (Fin.castAdd 2 i)) = fast w.2 := rfl
  unfold p11c_rotationLift SecularSpectrum.liftInv
  simp only [p11c_rotateSlow]
  congr 1
  funext l
  simp only [hf, Pi.add_apply, SecularSpectrum.fderiv_entry hd, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply, Fin.sum_univ_two]
  simp only [fast, slow]
  ring

/-- Part 9 transported to `p11c_rotationLift` on the lift domain of the frame domain:
chart (analytic and symplectic for `c = 1`), injectivity, action preservation and translation
covariance, for the consumer `PlanarBirkhoffResult` (design U9). -/
theorem p11c_rotationLift_chart (p : PlanarData) (hp : p.Valid) :
    IsChart 1 (p11c_rotationLift p) (SecularSpectrum.liftDomain (p11c_frameActionDomain p)) ∧
    InjOn (p11c_rotationLift p) (SecularSpectrum.liftDomain (p11c_frameActionDomain p)) ∧
    (∀ w ∈ SecularSpectrum.liftDomain (p11c_frameActionDomain p),
      (fun i => (p11c_rotationLift p w).2 (Fin.castAdd 2 i)) =
        fun i => w.2 (Fin.castAdd 2 i)) ∧
    (∀ w ∈ SecularSpectrum.liftDomain (p11c_frameActionDomain p), ∀ c : Fin 2 → ℝ,
      p11c_rotationLift p (w + (Fin.append c 0, 0)) =
        p11c_rotationLift p w + (Fin.append c 0, 0)) := by
  have hW := p11c_frameActionDomain_isOpen p
  have hAn := p11c_frameFamily_analyticOnNhd p hp
  have hR := p11c_frameFamily_isSO p hp
  have hL := SecularSpectrum.lift hW hAn hR
  have heq : ∀ w ∈ SecularSpectrum.liftDomain (p11c_frameActionDomain p),
      p11c_rotationLift p w = SecularSpectrum.liftInv (fun I => p11c_frame p (p.axes I)) w :=
    fun w hw => p11c_rotationLift_eq_liftInv p hp w hw
  have hev : ∀ w ∈ SecularSpectrum.liftDomain (p11c_frameActionDomain p),
      p11c_rotationLift p =ᶠ[𝓝 w]
        SecularSpectrum.liftInv (fun I => p11c_frame p (p.axes I)) := fun w hw => by
    filter_upwards [(SecularSpectrum.isOpen_liftDomain hW).mem_nhds hw] with y hy using heq y hy
  refine ⟨⟨fun w hw => (hL.2.1 w hw).congr (hev w hw).symm, fun w hw u v => ?_⟩, ?_, ?_, ?_⟩
  · rw [(hev w hw).fderiv_eq]
    exact hL.2.2.2.1 w hw u v
  · intro u hu v hv h
    rw [heq u hu, heq v hv] at h
    exact SecularSpectrum.liftInv_injOn hR hu hv h
  · intro w hw
    rw [heq w hw]
    show fast (SecularSpectrum.liftInv _ w).2 = fast w.2
    simp only [SecularSpectrum.liftInv, SecularSpectrum.fast_snd_assemble]
  · intro w hw c
    have hw' : w + (Fin.append c 0, 0) ∈
        SecularSpectrum.liftDomain (p11c_frameActionDomain p) := by
      simpa [SecularSpectrum.liftDomain, fast] using hw
    rw [heq _ hw', heq w hw]
    exact SecularSpectrum.liftInv_add_append _ w c

end KAM.Planetary

end
