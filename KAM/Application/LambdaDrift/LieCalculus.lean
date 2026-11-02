/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Application.LambdaDrift.LieRemainder

/-!
# Public calculus for the Lie remainder identities

Follow-ups of AUDIT-HD11964-P2B-1 (R1, R4), additive.

* `differentiableOn_approxIntegral₂`, `contDiffOn_approxIntegral₂`: the bridge's `hF` for
  `F = approxIntegral₂ k χ₁ χ₂` (R1).
* `pb_eq_sum`: the coordinate formula
  `{a, b} = Σ_k (∂_{θ_k} a ∂_{I_k} b − ∂_{I_k} a ∂_{θ_k} b)` (R4).
* The pointwise linearity rules of `pb` (left slot) and `dirDeriv`, and `{D_v a, h} = D_v {a, h}`
  for an angle-independent `h`, as public API for the order-3 identity (R4). They restate, under
  `fun_` names, the private helpers of `LieRemainder.lean`.
-/

@[expose] public noncomputable section

open Set Filter Topology KAM KAM.Planetary
open scoped ContDiff

namespace KAM.Application.LambdaDrift

variable {d : ℕ}

/-- **The coordinate formula** of the bracket (angles first). -/
theorem pb_eq_sum (a b : Phase d → ℝ) (w : Phase d) :
    pb a b w = ∑ k, (fderiv ℝ a w (Pi.single k 1, 0) * fderiv ℝ b w (0, Pi.single k 1) -
      fderiv ℝ a w (0, Pi.single k 1) * fderiv ℝ b w (Pi.single k 1, 0)) := by
  unfold pb
  rw [← symplecticForm_hamiltonianVectorField a w (hamiltonianVectorField b w)]
  unfold symplecticForm hamiltonianVectorField
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `approxIntegral₂ k χ₁ χ₂` is smooth at every point of an open set where `χ₁, χ₂` are. -/
theorem contDiffOn_approxIntegral₂ (k : Fin d) {χ₁ χ₂ : Phase d → ℝ} {O : Set (Phase d)}
    (hO : IsOpen O) (h₁ : ContDiffOn ℝ ∞ χ₁ O) (h₂ : ContDiffOn ℝ ∞ χ₂ O) :
    ContDiffOn ℝ ∞ (approxIntegral₂ k χ₁ χ₂) O := fun y hy => by
  have s1 := h₁.contDiffAt (hO.mem_nhds hy)
  have s2 := h₂.contDiffAt (hO.mem_nhds hy)
  have hI : ContDiff ℝ ∞ (fun z : Phase d => z.2 k) := by fun_prop
  have hs : ContDiffAt ℝ ∞ (approxIntegral₂ k χ₁ χ₂) y :=
    ((hI.contDiffAt.add (contDiffAt_dirDeriv _ s1)).add (contDiffAt_dirDeriv _ s2)).sub
      ((contDiffAt_pb (contDiffAt_dirDeriv _ s1) s1).div_const 2)
  exact hs.contDiffWithinAt

/-- **The bridge's `hF`** for `F = approxIntegral₂ k χ₁ χ₂` (R1). -/
theorem differentiableOn_approxIntegral₂ (k : Fin d) {χ₁ χ₂ : Phase d → ℝ} {O : Set (Phase d)}
    (hO : IsOpen O) (h₁ : ContDiffOn ℝ ∞ χ₁ O) (h₂ : ContDiffOn ℝ ∞ χ₂ O) :
    DifferentiableOn ℝ (approxIntegral₂ k χ₁ χ₂) O := fun _ hy =>
  (differentiableAt_of_contDiffAt
    ((contDiffOn_approxIntegral₂ k hO h₁ h₂).contDiffAt (hO.mem_nhds hy))).differentiableWithinAt

/-- `D_v (f + g) = D_v f + D_v g` at a point of differentiability. -/
theorem dirDeriv_fun_add {f g : Phase d → ℝ} {y : Phase d} (v : Phase d)
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    dirDeriv v (fun z => f z + g z) y = dirDeriv v f y + dirDeriv v g y := by
  show fderiv ℝ (f + g) y v = _
  rw [(hf.hasFDerivAt.add hg.hasFDerivAt).fderiv]
  rfl

/-- `D_v (f − g) = D_v f − D_v g` at a point of differentiability. -/
theorem dirDeriv_fun_sub {f g : Phase d → ℝ} {y : Phase d} (v : Phase d)
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    dirDeriv v (fun z => f z - g z) y = dirDeriv v f y - dirDeriv v g y := by
  show fderiv ℝ (f - g) y v = _
  rw [(hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv]
  rfl

/-- `D_v (c f) = c D_v f` at a point of differentiability. -/
theorem dirDeriv_fun_const_mul {f : Phase d → ℝ} {y : Phase d} (v : Phase d) (c : ℝ)
    (hf : DifferentiableAt ℝ f y) : dirDeriv v (fun z => c * f z) y = c * dirDeriv v f y := by
  show fderiv ℝ (fun z => c * f z) y v = _
  rw [(hf.hasFDerivAt.const_mul c).fderiv]
  rfl

/-- `{f + g, b} = {f, b} + {g, b}` at a point of differentiability. -/
theorem pb_fun_add_left {f g b : Phase d → ℝ} {y : Phase d} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) : pb (fun z => f z + g z) b y = pb f b y + pb g b y := by
  show pb (f + g) b y = _
  rw [pb_of_hasFDerivAt (hf.hasFDerivAt.add hg.hasFDerivAt)]
  rfl

/-- `{f − g, b} = {f, b} − {g, b}` at a point of differentiability. -/
theorem pb_fun_sub_left {f g b : Phase d → ℝ} {y : Phase d} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) : pb (fun z => f z - g z) b y = pb f b y - pb g b y := by
  show pb (f - g) b y = _
  rw [pb_of_hasFDerivAt (hf.hasFDerivAt.sub hg.hasFDerivAt)]
  rfl

/-- `{c f, b} = c {f, b}` at a point of differentiability. -/
theorem pb_fun_const_mul_left {f b : Phase d → ℝ} {y : Phase d} (c : ℝ)
    (hf : DifferentiableAt ℝ f y) : pb (fun z => c * f z) b y = c * pb f b y := by
  rw [pb_of_hasFDerivAt (hf.hasFDerivAt.const_mul c)]
  rfl

/-- `{a, c G} = c {a, G}` at a point of differentiability of `G`. -/
theorem pb_fun_const_mul_right {a G : Phase d → ℝ} {y : Phase d} (c : ℝ)
    (hG : DifferentiableAt ℝ G y) : pb a (fun z => c * G z) y = c * pb a G y := by
  rw [pb_antisymm, pb_fun_const_mul_left c hG, pb_antisymm a G y]
  ring

/-- For an angle-independent `h` (`D_v h ≡ 0`): `{D_v a, h} = D_v {a, h}` at a point where `a`,
`h` are smooth. -/
theorem pb_dirDeriv_left_of_invariant {h a : Phase d → ℝ} {v : Phase d}
    (hh : ∀ y, fderiv ℝ h y v = 0) {y : Phase d} (ha : ContDiffAt ℝ ∞ a y)
    (hhs : ContDiffAt ℝ ∞ h y) : pb (dirDeriv v a) h y = dirDeriv v (pb a h) y := by
  have h0 : dirDeriv v h = fun _ => (0 : ℝ) := funext hh
  have hz : pb a (dirDeriv v h) y = 0 := by
    refine pb_eq_zero_of_fderiv_eq_zero ?_
    rw [h0]
    exact fderiv_const_apply 0
  rw [dirDeriv_pb ha hhs, hz, add_zero]

end KAM.Application.LambdaDrift

end
