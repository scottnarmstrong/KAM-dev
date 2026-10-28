/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.HoloStripBound
public import KAM.Planetary.Preparation.Holomorphic
public import KAM.Strip.AnalyticTaylor

/-!
# The complexified chart input `Φ_ρ⁻¹ ∘ T₁` (P11A-P2c, `stepP:p11:hc-lift`, `hc-F`)

For a rotation family `ρ` (parametric: holomorphic on a complex ball, with the row-sum bounds
`B`, `B'` of `p11_rotation_bounds`) `p11hsInput ρ z` is the complexified chart input of
`p11ChartInput` (the same formula without the real part), and `p11hsF D ρ = f̂_fix ∘ p11hsInput ρ`.
Here: the elementary bounds `|ρ x| ≤ B |x|`, `|H_ρ| ≤ n B' |x||y|`, holomorphy of the input, and
its realness at real points.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler SecularForm

section Input

variable {n : ℕ}

/-- The complexified lift `(λ̃ + H_ρ, ρ x; Λ, ρ y)` of a working point `((θ, x), (J, y))`:
`λ̃_l = 2π θ_l + Σ y_i (ρᵀ ∂_l ρ)_{ij} x_j` with `ρ` and `∂_l ρ` at `Λ = J/(2π)`. -/
def p11hsInput (ρ : P11CVec n → Matrix (Fin n) (Fin n) ℂ) (z : P11Phase (n + n)) :
    P11Phase (n + n) :=
  let L : P11CVec n := fun i => z.2 (Fin.castAdd n i) / (2 * π)
  let x : P11CVec n := fun i => z.1 (Fin.natAdd n i)
  let y : P11CVec n := fun i => z.2 (Fin.natAdd n i)
  let R := ρ L
  (Fin.append (fun l => 2 * π * z.1 (Fin.castAdd n l) +
      ∑ i, ∑ j, y i * ((R.transpose * fderiv ℂ ρ L (Pi.single l 1)) i j) * x j) (R.mulVec x),
   Fin.append L (R.mulVec y))

/-- `F := f̂_fix ∘ Φ_ρ⁻¹ ∘ T₁` (`hc-F`). -/
def p11hsF (D : Data n) (ρ : P11CVec n → Matrix (Fin n) (Fin n) ℂ) (z : P11Phase (n + n)) : ℂ :=
  p11hsFHat D (p11hsInput ρ z)

theorem norm_mulVec_le {R : Matrix (Fin n) (Fin n) ℂ} {B : ℝ} (hB : ∀ i, ∑ j, ‖R i j‖ ≤ B)
    (x : P11CVec n) (i : Fin n) : ‖R.mulVec x i‖ ≤ B * ‖x‖ := by
  calc ‖R.mulVec x i‖ = ‖∑ j, R i j * x j‖ := rfl
    _ ≤ ∑ j, ‖R i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖R i j‖ * ‖x‖ :=
        Finset.sum_le_sum fun j _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (norm_nonneg _)
    _ = (∑ j, ‖R i j‖) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ B * ‖x‖ := mul_le_mul_of_nonneg_right (hB i) (norm_nonneg _)

theorem norm_hRho_le {T : Matrix (Fin n) (Fin n) ℂ} {B' : ℝ} (hB : ∀ i, ∑ j, ‖T i j‖ ≤ B')
    (x y : P11CVec n) : ‖∑ i, ∑ j, y i * T i j * x j‖ ≤ n * B' * (‖x‖ * ‖y‖) := by
  calc ‖∑ i, ∑ j, y i * T i j * x j‖ ≤ ∑ i, ‖∑ j, y i * T i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖y i * T i j * x j‖ :=
        Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ∑ j, ‖T i j‖ * (‖x‖ * ‖y‖) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          rw [norm_mul, norm_mul]
          have h1 := norm_le_pi_norm x j
          have h2 := norm_le_pi_norm y i
          calc ‖y i‖ * ‖T i j‖ * ‖x j‖ = ‖T i j‖ * (‖x j‖ * ‖y i‖) := by ring
            _ ≤ ‖T i j‖ * (‖x‖ * ‖y‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _))
                (norm_nonneg _)
    _ = ∑ i : Fin n, (∑ j, ‖T i j‖) * (‖x‖ * ‖y‖) := by
        simp only [Finset.sum_mul]
    _ ≤ ∑ i : Fin n, B' * (‖x‖ * ‖y‖) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hB i) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = n * B' * (‖x‖ * ‖y‖) := by simp [mul_assoc]

/-- The derivative of a holomorphic matrix family is holomorphic in each direction. -/
theorem p11hs_differentiableOn_fderiv {U : Set (P11CVec n)} (hU : IsOpen U)
    {ρ : P11CVec n → Matrix (Fin n) (Fin n) ℂ}
    (hρ : ∀ i j, DifferentiableOn ℂ (fun z => ρ z i j) U) (v : P11CVec n) (i j : Fin n) :
    DifferentiableOn ℂ (fun J => (fderiv ℂ ρ J v : Matrix (Fin n) (Fin n) ℂ) i j) U := by
  have hρd : DifferentiableOn ℂ ρ U :=
    differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j => hρ i j
  have hentry : ∀ J ∈ U, (fderiv ℂ ρ J v : Matrix (Fin n) (Fin n) ℂ) i j =
      fderiv ℂ (fun z => ρ z i j) J v := by
    intro J hJ
    have hdA : DifferentiableAt ℂ (fun z => (ρ z : Fin n → Fin n → ℂ)) J :=
      hρd.differentiableAt (hU.mem_nhds hJ)
    have hproj : HasFDerivAt (fun M : Fin n → Fin n → ℂ => M i j)
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).comp
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Fin n → ℂ) i)) (ρ J : Fin n → Fin n → ℂ) :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).comp
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Fin n → ℂ) i)).hasFDerivAt
    have h3 := congrArg (fun L => L v) (hproj.comp J hdA.hasFDerivAt).fderiv
    exact h3.symm
  have hA : AnalyticOnNhd ℂ (fun z => ρ z i j) U :=
    analyticOnNhd_of_differentiableOn hU (hρ i j)
  have h2 : AnalyticOnNhd ℂ (fun J => fderiv ℂ (fun z => ρ z i j) J v) U := fun J hJ =>
    ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp (hA.fderiv J hJ)
  exact (h2.differentiableOn).congr fun J hJ => hentry J hJ

/-- The parametric hypotheses of `hc-F`: the rotation family `ρ` (holomorphic, real on reals, with
the bounds `B`, `B'` of `p11_rotation_bounds`) on the ball of radius `rC/π` about `J₀/(2π)`, the
strip data `(r', σ')` of `p11hs_strip`, and the smallness of `r_z` (source: `stepP:p11:hc-lift`,
`r_z ≤ min {1, ρ_*/(8 B_ρ), (π σ'/(2 n B'_ρ))^{1/2}}`) and of the working strip `σ ≤ σ'/4`. -/
structure P11HsHyp (D : Data n) (a : Vec n) (ρ : P11CVec n → Matrix (Fin n) (Fin n) ℂ)
    (J0 : P11Vec n) (rC σ rz B B' r' σ' : ℝ) : Prop where
  rot_diff : ∀ i j, DifferentiableOn ℂ (fun z => ρ z i j)
    (Metric.ball ((2 * π)⁻¹ • KAM.realInclusion n J0) (rC / π))
  rot_bound : ∀ J ∈ Metric.ball ((2 * π)⁻¹ • KAM.realInclusion n J0) (rC / π),
    (∀ i, ∑ j, ‖ρ J i j‖ ≤ B) ∧
    ∀ l i, ∑ j, ‖((ρ J).transpose * fderiv ℂ ρ J (Pi.single l 1)) i j‖ ≤ B'
  rot_real : ∀ L : P11Vec n, ‖L - (2 * π)⁻¹ • J0‖ < rC / π →
    ∀ i j, (ρ (KAM.realInclusion n L) i j).im = 0
  B_nonneg : 0 ≤ B
  rC_pos : 0 < rC
  sigma_pos : 0 < σ
  rz_pos : 0 < rz
  center : ∀ L ∈ Metric.ball ((2 * π)⁻¹ • KAM.realInclusion n J0) (rC / π), ∀ i,
    ‖L i - (action D a i : ℂ)‖ < r'
  hB_rz : B * rz < r'
  hB'_rz : n * B' * rz ^ 2 ≤ π * σ' / 2
  sigma_le : σ ≤ σ' / 4
  r'_lt : r' < rho D a
  sigma'_pos : 0 < σ'
  sigma'_small : 2 * π * σ' ≤ 1 / 8
  strip : ∀ lam : CVec n, (∀ l, |(lam l).im| ≤ 2 * π * σ') → ∀ x ∈ polydisc D a r',
    ∀ i j : Fin n, i < j → (a j - a i) ^ 2 / 4 ≤ (p11hsSep D lam x i j).re

variable {D : Data n} {a : Vec n} {ρ : P11CVec n → Matrix (Fin n) (Fin n) ℂ} {J0 : P11Vec n}
  {rC σ rz B B' r' σ' : ℝ}

theorem P11HsHyp.B'_nonneg (hn : 0 < n) (h : P11HsHyp D a ρ J0 rC σ rz B B' r' σ') : 0 ≤ B' := by
  have hmem : (2 * π)⁻¹ • KAM.realInclusion n J0 ∈
      Metric.ball ((2 * π)⁻¹ • KAM.realInclusion n J0) (rC / π) :=
    Metric.mem_ball_self (div_pos h.rC_pos Real.pi_pos)
  have := (h.rot_bound _ hmem).2 ⟨0, hn⟩ ⟨0, hn⟩
  exact (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans this

/-- The `Λ = J/(2π)` coordinates of a working point lie in the rotation ball. -/
theorem p11hs_L_mem {z : P11Phase (n + n)}
    (hz : z ∈ p11WorkingDom n J0 (2 * σ) (2 * rC) rz) :
    (fun i : Fin n => z.2 (Fin.castAdd n i) / (2 * π)) ∈
      Metric.ball ((2 * π)⁻¹ • KAM.realInclusion n J0) (rC / π) := by
  have h := hz.2.1
  rw [Metric.mem_ball, dist_eq_norm]
  have h2 : (fun i : Fin n => z.2 (Fin.castAdd n i) / (2 * π)) -
      (2 * π)⁻¹ • KAM.realInclusion n J0 =
      (2 * π : ℂ)⁻¹ • ((fun i : Fin n => z.2 (Fin.castAdd n i)) - KAM.realInclusion n J0) := by
    funext i
    simp [div_eq_inv_mul, mul_sub]
  rw [h2, norm_smul]
  have : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv]; simp [abs_of_pos Real.pi_pos]
  rw [this]
  calc (2 * π)⁻¹ * ‖(fun i : Fin n => z.2 (Fin.castAdd n i)) - KAM.realInclusion n J0‖
      < (2 * π)⁻¹ * (2 * rC) := mul_lt_mul_of_pos_left h (by positivity)
    _ = rC / π := by field_simp

theorem p11hsAngle_input (z : P11Phase (n + n)) (l : Fin n) :
    p11hsAngle (p11hsInput ρ z) l = 2 * π * z.1 (Fin.castAdd n l) +
      ∑ i, ∑ j, z.2 (Fin.natAdd n i) *
        (((ρ fun i => z.2 (Fin.castAdd n i) / (2 * π)).transpose *
          fderiv ℂ ρ (fun i => z.2 (Fin.castAdd n i) / (2 * π)) (Pi.single l 1)) i j) *
        z.1 (Fin.natAdd n j) := by
  simp [p11hsAngle, p11hsInput]

theorem p11hsSlow_input (z : P11Phase (n + n)) :
    p11hsSlow (p11hsInput ρ z) =
      ((ρ fun i => z.2 (Fin.castAdd n i) / (2 * π)).mulVec (fun i => z.1 (Fin.natAdd n i)),
       (fun i => z.2 (Fin.castAdd n i) / (2 * π)),
       (ρ fun i => z.2 (Fin.castAdd n i) / (2 * π)).mulVec (fun i => z.2 (Fin.natAdd n i))) := by
  simp [p11hsSlow, p11hsInput]

theorem norm_H_le (hn : 0 < n) (h : P11HsHyp D a ρ J0 rC σ rz B B' r' σ')
    {z : P11Phase (n + n)} (hz : z ∈ p11WorkingDom n J0 (2 * σ) (2 * rC) rz) (l : Fin n) :
    ‖p11hsAngle (p11hsInput ρ z) l - 2 * π * z.1 (Fin.castAdd n l)‖ ≤ π * σ' / 2 := by
  rw [p11hsAngle_input, add_sub_cancel_left]
  have hT := (h.rot_bound _ (p11hs_L_mem hz)).2 l
  refine (norm_hRho_le hT _ _).trans ?_
  have hx := hz.2.2.1
  have hy := hz.2.2.2
  have hB' := h.B'_nonneg hn
  calc (n : ℝ) * B' * (‖fun i : Fin n => z.1 (Fin.natAdd n i)‖ *
        ‖fun i : Fin n => z.2 (Fin.natAdd n i)‖) ≤ n * B' * (rz * rz) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hx.le hy.le (norm_nonneg _) h.rz_pos.le)
          (by positivity)
    _ = n * B' * rz ^ 2 := by ring
    _ ≤ π * σ' / 2 := h.hB'_rz

/-- `hc-lift` (membership): the complexified lift of a working point lies in the good set. -/
theorem p11hsInput_mem_good (hn : 0 < n) (h : P11HsHyp D a ρ J0 rC σ rz B B' r' σ')
    {z : P11Phase (n + n)} (hz : z ∈ p11WorkingDom n J0 (2 * σ) (2 * rC) rz) :
    p11hsInput ρ z ∈ p11hsGood D a r' := by
  have hL := p11hs_L_mem hz
  have hRB := (h.rot_bound _ hL).1
  have hx := hz.2.2.1
  have hy := hz.2.2.2
  have hslow : p11hsSlow (p11hsInput ρ z) ∈ polydisc D a r' := by
    rw [p11hsSlow_input]
    intro i
    refine ⟨?_, h.center _ hL i, ?_⟩
    · refine lt_of_le_of_lt (norm_mulVec_le hRB _ i) ?_
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hx.le h.B_nonneg) h.hB_rz
    · refine lt_of_le_of_lt (norm_mulVec_le hRB _ i) ?_
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hy.le h.B_nonneg) h.hB_rz
  have him : ∀ l, |(p11hsAngle (p11hsInput ρ z) l).im| ≤ 2 * π * σ' := by
    intro l
    have h1 := norm_H_le hn h hz l
    have h2 : |(p11hsAngle (p11hsInput ρ z) l - 2 * π * z.1 (Fin.castAdd n l)).im| ≤ π * σ' / 2 :=
      (Complex.abs_im_le_norm _).trans h1
    have h3 : |(z.1 (Fin.castAdd n l)).im| < 2 * σ := hz.1 l
    have h4 : (p11hsAngle (p11hsInput ρ z) l).im =
        (p11hsAngle (p11hsInput ρ z) l - 2 * π * z.1 (Fin.castAdd n l)).im +
          2 * π * (z.1 (Fin.castAdd n l)).im := by
      simp
    rw [h4]
    refine (abs_add_le _ _).trans ?_
    have h5 : |2 * π * (z.1 (Fin.castAdd n l)).im| ≤ 2 * π * (2 * σ) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      exact mul_le_mul_of_nonneg_left h3.le (by positivity)
    have hmul : π * σ ≤ π * (σ' / 4) := mul_le_mul_of_nonneg_left h.sigma_le Real.pi_pos.le
    have hpos : 0 < π * σ' := mul_pos Real.pi_pos h.sigma'_pos
    linarith
  refine ⟨fun l => ?_, hslow, fun i j hij => h.strip _ him _ hslow i j hij⟩
  exact lt_of_le_of_lt (him l) (by linarith [h.sigma'_small])

end Input

end KAM.Planetary

end
