/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.NormalOps
public import KAM.Wave.Homological.SolveDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Taylor Hamiltonians and their field norm (blueprint-W `bpW:w4:taylor`)

Representative model (`NormalOps.lean`): the normal variables `z, \bar z ∈ ℓ^N_{a,p}` are given by
their representatives in `ℓ²` (`HomL2`), the gradients `c^±` by representatives in `ℓ²` of
`ℓ^N_{a,p+1}`, and the operator components `P, P', Q, Q^T` by weighted matrices (`HomOp`).

* `HomTaylor_gen a p pb s`: the class `𝒯_s`; components `a, b, c^±, P, P', Q, Q^T` (here `a0, b,
    cp, cm,
  P, P', Q, Qt`) complex differentiable, `1`-periodic and bounded on `T_s`, `P, P'` symmetric and
  `Q^T` the entrywise transpose of `Q` (entries `homNormalEntry_gen`);
* `homRz_gen`, `homRzb_gen`, `homRu_gen`, `homRv_gen`, `homRy_gen`, `homRtheta_gen`: the gradients
    `R_z, R_{\bar z}, R_u,
  R_v, R_y, R_θ` of the polynomial (`bpW:w4:R`);
* `homXnorm_gen r`: `|X_R|_r = (1/2π)|R_y| + (1/(2π r²))|R_θ| + (1/r)(‖R_u‖+‖R_v‖)`;
* `HomDomain s r`: the domain `D(s,r)` (`‖u‖ + ‖v‖ < r`), and the relations
  `z = (u + iv)/√2` (`bpW:w4:zu`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- A component of a Taylor Hamiltonian: complex differentiable, `1`-periodic and bounded on
`T_s`. -/
def IsHomComp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℝ)
    (f : (Fin 2 → ℂ) → E) : Prop :=
  DifferentiableOn ℂ f (complexStrip 2 s) ∧
    (∀ (i : Fin 2) z, z ∈ complexStrip 2 s → f (z + Pi.single i 1) = f z) ∧
    ∃ C : ℝ, ∀ z ∈ complexStrip 2 s, ‖f z‖ ≤ C

/-- **The class `𝒯_s`** (blueprint `bpW:w4:taylor`). -/
structure HomTaylor_gen (a p pb s : ℝ) where
  a0 : (Fin 2 → ℂ) → ℂ
  b : (Fin 2 → ℂ) → (Fin 2 → ℂ)
  cp : (Fin 2 → ℂ) → HomL2
  cm : (Fin 2 → ℂ) → HomL2
  P : (Fin 2 → ℂ) → HomOp
  P' : (Fin 2 → ℂ) → HomOp
  Q : (Fin 2 → ℂ) → HomOp
  Qt : (Fin 2 → ℂ) → HomOp
  comp_a0 : IsHomComp s a0
  comp_b : IsHomComp s b
  comp_cp : IsHomComp s cp
  comp_cm : IsHomComp s cm
  comp_P : IsHomComp s P
  comp_P' : IsHomComp s P'
  comp_Q : IsHomComp s Q
  comp_Qt : IsHomComp s Qt
  symP : ∀ θ ∈ complexStrip 2 s, ∀ i j,
    homNormalEntry_gen a p pb (P θ) i j = homNormalEntry_gen a p pb (P θ) j i
  symP' : ∀ θ ∈ complexStrip 2 s, ∀ i j,
    homNormalEntry_gen a p pb (P' θ) i j = homNormalEntry_gen a p pb (P' θ) j i
  transQ : ∀ θ ∈ complexStrip 2 s, ∀ i j,
    homNormalEntry_gen a p pb (Qt θ) i j = homNormalEntry_gen a p pb (Q θ) j i

variable {a p pb s : ℝ}

/-- `√2` as a complex number. -/
def homSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

theorem homSqrt2_ne : homSqrt2 ≠ 0 := by
  unfold homSqrt2
  exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'

theorem norm_homSqrt2 : ‖homSqrt2‖ = Real.sqrt 2 := by
  unfold homSqrt2
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by norm_num))]

theorem homSqrt2_sq : homSqrt2 * homSqrt2 = 2 := by
  unfold homSqrt2
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  simp

/-- `R_y = b`. -/
def homRy_gen (T : HomTaylor_gen a p pb s) (θ : Fin 2 → ℂ) : Fin 2 → ℂ := T.b θ

/-- `R_z = c^+ + 2Pz + Q^T \bar z`. -/
def homRz_gen (T : HomTaylor_gen a p pb s) (θ : Fin 2 → ℂ) (z zb : HomL2) : HomL2 :=
  T.cp θ + (2 : ℂ) • T.P θ z + T.Qt θ zb

/-- `R_{\bar z} = c^- + Qz + 2P'\bar z`. -/
def homRzb_gen (T : HomTaylor_gen a p pb s) (θ : Fin 2 → ℂ) (z zb : HomL2) : HomL2 :=
  T.cm θ + T.Q θ z + (2 : ℂ) • T.P' θ zb

/-- `R_u = (R_z + R_{\bar z})/√2`. -/
def homRu_gen (T : HomTaylor_gen a p pb s) (θ : Fin 2 → ℂ) (z zb : HomL2) : HomL2 :=
  (homSqrt2⁻¹) • (homRz_gen T θ z zb + homRzb_gen T θ z zb)

/-- `R_v = i (R_z - R_{\bar z})/√2`. -/
def homRv_gen (T : HomTaylor_gen a p pb s) (θ : Fin 2 → ℂ) (z zb : HomL2) : HomL2 :=
  (Complex.I * homSqrt2⁻¹) • (homRz_gen T θ z zb - homRzb_gen T θ z zb)

theorem homSqrt2_inv : homSqrt2⁻¹ = homSqrt2 / 2 := by
  have h := homSqrt2_ne
  field_simp
  rw [sq]
  exact homSqrt2_sq.symm

/-- `R_z = (R_u - i R_v)/√2` and `R_{\bar z} = (R_u + i R_v)/√2`. -/
theorem homRz_eq_gen (T : HomTaylor_gen a p pb s) (θ : Fin 2 → ℂ) (z zb : HomL2) :
    homRz_gen T θ z zb = (homSqrt2⁻¹) • (homRu_gen T θ z zb - Complex.I • homRv_gen T θ z zb) := by
  unfold homRu_gen homRv_gen
  have h2' : homSqrt2 ^ 2 = 2 := by rw [sq]; exact homSqrt2_sq
  rw [homSqrt2_inv]
  ext j
  simp only [lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sub, Pi.smul_apply, Pi.add_apply,
    Pi.sub_apply, smul_eq_mul]
  ring_nf
  simp only [h2', Complex.I_sq]
  ring

theorem homRzb_eq_gen (T : HomTaylor_gen a p pb s) (θ : Fin 2 → ℂ) (z zb : HomL2) :
    homRzb_gen T θ z zb = (homSqrt2⁻¹) • (homRu_gen T θ z zb + Complex.I • homRv_gen T θ z zb) := by
  unfold homRu_gen homRv_gen
  have h2' : homSqrt2 ^ 2 = 2 := by rw [sq]; exact homSqrt2_sq
  rw [homSqrt2_inv]
  ext j
  simp only [lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sub, Pi.smul_apply, Pi.add_apply,
    Pi.sub_apply, smul_eq_mul]
  ring_nf
  simp only [h2', Complex.I_sq]
  ring

/-- `∂_{θ_i} R` for the Taylor polynomial, in terms of the derivatives of the components
(`bpW:w4:taylor`). -/
def homRtheta_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb
    s) (i :
    Fin 2)
    (θ y : Fin 2 → ℂ) (z zb : HomL2) : ℂ :=
  homPartial i T.a0 θ + ∑ k, homPartial i T.b θ k * y k
    + homPairRep_gen ha (homPP hp hpb) (homPartial i T.cp θ) z + homPairRep_gen ha (homPP hp hpb)
        (homPartial i T.cm θ) zb
    + homPairRep_gen ha (homPP hp hpb) (homPartial i T.P θ z) z + homPairRep_gen ha (homPP hp hpb)
        (homPartial i T.Q θ z) zb
    + homPairRep_gen ha (homPP hp hpb) (homPartial i T.P' θ zb) zb

/-- The coordinates `u = (z + \bar z)/√2`. -/
def homU (z zb : HomL2) : HomL2 := (homSqrt2⁻¹) • (z + zb)

/-- The coordinates `v = (z - \bar z)/(i√2)`. -/
def homV (z zb : HomL2) : HomL2 := (-Complex.I * homSqrt2⁻¹) • (z - zb)

/-- The domain `D(s,r)`: `θ ∈ T_s`, `|y| < r²`, `‖u‖ + ‖v‖ < r`. -/
def HomDomain (s r : ℝ) (θ y : Fin 2 → ℂ) (z zb : HomL2) : Prop :=
  θ ∈ complexStrip 2 s ∧ ‖y‖ < r ^ 2 ∧ ‖homU z zb‖ + ‖homV z zb‖ < r

/-- **The field norm** `|X_R|_r` (blueprint `bpW:w4:taylor`), at a point. -/
def homXnorm_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (r : ℝ) (T : HomTaylor_gen a
    p pb s)
    (θ y : Fin 2 → ℂ) (z zb : HomL2) : ℝ :=
  (2 * Real.pi)⁻¹ * ‖homRy_gen T θ‖
    + (2 * Real.pi * r ^ 2)⁻¹ * ‖fun i => homRtheta_gen ha hp hpb T i θ y z zb‖
    + r⁻¹ * (‖homRu_gen T θ z zb‖ + ‖homRv_gen T θ z zb‖)

theorem homXnorm_nonneg_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r : ℝ} (hr : 0 <
    r)
    (T : HomTaylor_gen a p pb s) (θ y : Fin 2 → ℂ) (z zb : HomL2) :
    0 ≤ homXnorm_gen ha hp hpb r T θ y z zb := by
  unfold homXnorm_gen
  positivity

/-- `‖z‖ ≤ (‖u‖ + ‖v‖)/√2` and `‖\bar z‖ ≤ (‖u‖+‖v‖)/√2` for the coordinates of a domain
point (`bpW:w4:zu`). -/
theorem homNorm_le_uv (z zb : HomL2) :
    ‖z‖ ≤ (‖homU z zb‖ + ‖homV z zb‖) / Real.sqrt 2 ∧
      ‖zb‖ ≤ (‖homU z zb‖ + ‖homV z zb‖) / Real.sqrt 2 := by
  have h2' : homSqrt2 ^ 2 = 2 := by rw [sq]; exact homSqrt2_sq
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have e1 : z = (homSqrt2⁻¹) • (homU z zb + Complex.I • homV z zb) := by
    unfold homU homV
    rw [homSqrt2_inv]
    ext j
    simp only [lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sub, Pi.smul_apply, Pi.add_apply,
      Pi.sub_apply, smul_eq_mul]
    ring_nf
    simp only [h2', Complex.I_sq]
    ring
  have e2 : zb = (homSqrt2⁻¹) • (homU z zb - Complex.I • homV z zb) := by
    unfold homU homV
    rw [homSqrt2_inv]
    ext j
    simp only [lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sub, Pi.smul_apply, Pi.add_apply,
      Pi.sub_apply, smul_eq_mul]
    ring_nf
    simp only [h2', Complex.I_sq]
    ring
  have hn : ‖homSqrt2⁻¹‖ = (Real.sqrt 2)⁻¹ := by rw [norm_inv, norm_homSqrt2]
  constructor
  · conv_lhs => rw [e1]
    rw [norm_smul, hn]
    refine le_trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)) ?_
    rw [norm_smul, Complex.norm_I, one_mul, div_eq_inv_mul]
  · conv_lhs => rw [e2]
    rw [norm_smul, hn]
    refine le_trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)) ?_
    rw [norm_smul, Complex.norm_I, one_mul, div_eq_inv_mul]

end KAM.Wave
