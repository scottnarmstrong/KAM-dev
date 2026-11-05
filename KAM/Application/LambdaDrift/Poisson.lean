/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Hamiltonian.Algebra

/-!
# The canonical Poisson bracket on `Phase d` (real)

Design `docs/campaign/design/HD11964-PILOT.md` §6.2. The bracket of the Λ-drift bridge: for
`a b : Phase d → ℝ`, `{a, b}(w) = Da(w) X_b(w)`, with LP's `hamiltonianVectorField`
`X_b = (∂_I b, -∂_θ b)` (angles first). The bridge's rate `fderiv ℝ (F i) w (X_H w)` is
`pb (F i) H w`.

All statements are pointwise, with smoothness at the point (`ContDiffAt ℝ ∞`).

## Main results

* `pb_antisymm`: `{a, b} = -{b, a}` (no hypothesis).
* `pb_mom`: `{I_k, G} = -D_k G`, for the action coordinate `I_k = w.2 k` and the angle derivative
  `D_k = dirDeriv (angleDir k)`; `pb_angle_mom`: `{θ_k, I_k} = 1`.
* `fderiv_pb_apply`: `D{a, b}(w) v = D²a(w)(v)(X_b) - D²b(w)(v)(X_a)`.
* `dirDeriv_pb`: a constant direction `v` differentiates the bracket as a derivation.
* `pb_jacobi`: the Jacobi identity `{{a, b}, c} = {{a, c}, b} + {a, {b, c}}`.
* `contDiffAt_pb`, `contDiffAt_dirDeriv`: smoothness is preserved.
-/

@[expose] public noncomputable section

open Set Filter Topology KAM KAM.Planetary
open scoped ContDiff

namespace KAM.Application.LambdaDrift

variable {d : ℕ}

/-- The canonical bracket `{a, b}(w) = Da(w) X_b(w)` (angles first, LP's sign convention). -/
def pb (a b : Phase d → ℝ) (w : Phase d) : ℝ := fderiv ℝ a w (hamiltonianVectorField b w)

/-- The derivative along a constant vector `v`. -/
def dirDeriv (v : Phase d) (a : Phase d → ℝ) (w : Phase d) : ℝ := fderiv ℝ a w v

/-- The direction of the angle conjugate to the action `w.2 k`. -/
def angleDir (k : Fin d) : Phase d := (Pi.single k 1, 0)

/-- `ℓ ↦ X_ℓ` as a continuous linear map. -/
def linearFieldCLM : (Phase d →L[ℝ] ℝ) →L[ℝ] Phase d :=
  LinearMap.toContinuousLinearMap
    { toFun := linearField
      map_add' := fun ℓ ℓ' => by
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
        · simp [linearField]
        · simp [linearField]
          ring
      map_smul' := fun c ℓ => by
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
          simp [linearField] }

theorem linearFieldCLM_apply (ℓ : Phase d →L[ℝ] ℝ) : linearFieldCLM ℓ = linearField ℓ := rfl

theorem hamiltonianVectorField_eq_clm (b : Phase d → ℝ) (w : Phase d) :
    hamiltonianVectorField b w = linearFieldCLM (fderiv ℝ b w) := rfl

/-- `Da(w) X_ℓ = -ℓ (X_a(w))`. -/
theorem fderiv_apply_linearField (a : Phase d → ℝ) (w : Phase d) (ℓ : Phase d →L[ℝ] ℝ) :
    fderiv ℝ a w (linearField ℓ) = -ℓ (hamiltonianVectorField a w) := by
  rw [← symplecticForm_hamiltonianVectorField a w (linearField ℓ), symplecticForm_antisymm,
    symplecticForm_linearField]

/-- **Antisymmetry** of the bracket (no smoothness needed). -/
theorem pb_antisymm (a b : Phase d → ℝ) (w : Phase d) : pb a b w = -pb b a w := by
  show fderiv ℝ a w (linearField (fderiv ℝ b w)) = -fderiv ℝ b w (hamiltonianVectorField a w)
  exact fderiv_apply_linearField a w _

/-- The bracket through any derivative of the left function. -/
theorem pb_of_hasFDerivAt {a b : Phase d → ℝ} {w : Phase d} {L : Phase d →L[ℝ] ℝ}
    (h : HasFDerivAt a L w) : pb a b w = L (hamiltonianVectorField b w) := by
  unfold pb
  rw [h.fderiv]

/-- The bracket depends on the left function only near the point. -/
theorem pb_congr_left {a a' b : Phase d → ℝ} {w : Phase d} (h : a =ᶠ[𝓝 w] a') :
    pb a b w = pb a' b w := by
  unfold pb
  rw [h.fderiv_eq]

/-- The directional derivative depends on the function only near the point. -/
theorem dirDeriv_congr {a a' : Phase d → ℝ} {w : Phase d} (v : Phase d) (h : a =ᶠ[𝓝 w] a') :
    dirDeriv v a w = dirDeriv v a' w := by
  unfold dirDeriv
  rw [h.fderiv_eq]

/-- A function with zero derivative has zero bracket from the right. -/
theorem pb_eq_zero_of_fderiv_eq_zero {a b : Phase d → ℝ} {w : Phase d}
    (hb : fderiv ℝ b w = 0) : pb a b w = 0 := by
  unfold pb
  rw [hamiltonianVectorField_eq_clm, hb, map_zero, map_zero]

/-- Additivity in the right function. -/
theorem pb_add_right {a b c : Phase d → ℝ} {w : Phase d} (hb : DifferentiableAt ℝ b w)
    (hc : DifferentiableAt ℝ c w) : pb a (fun y => b y + c y) w = pb a b w + pb a c w := by
  show fderiv ℝ a w (linearFieldCLM (fderiv ℝ (b + c) w)) =
    fderiv ℝ a w (linearFieldCLM (fderiv ℝ b w)) + fderiv ℝ a w (linearFieldCLM (fderiv ℝ c w))
  rw [(hb.hasFDerivAt.add hc.hasFDerivAt).fderiv, map_add, map_add]

/-- `X_b`'s `k`-th action component is `-D_k b`. -/
theorem hamiltonianVectorField_snd (b : Phase d → ℝ) (w : Phase d) (k : Fin d) :
    (hamiltonianVectorField b w).2 k = -dirDeriv (angleDir k) b w := rfl

/-- **The action coordinate**: `{I_k, G} = -D_k G`. -/
theorem pb_mom (k : Fin d) (G : Phase d → ℝ) (w : Phase d) :
    pb (fun y : Phase d => y.2 k) G w = -dirDeriv (angleDir k) G w := by
  have hd : HasFDerivAt (fun y : Phase d => y.2 k)
      ((ContinuousLinearMap.proj (R := ℝ) k).comp
        (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin d → ℝ))) w :=
    ((ContinuousLinearMap.proj (R := ℝ) k).comp
      (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin d → ℝ))).hasFDerivAt
  rw [pb_of_hasFDerivAt hd]
  rfl

/-- **The canonical pair** (a non-degeneracy check of the convention): `{θ_k, I_k} = 1`. -/
theorem pb_angle_mom (k : Fin d) (w : Phase d) :
    pb (fun y : Phase d => y.1 k) (fun y : Phase d => y.2 k) w = 1 := by
  have hθ : HasFDerivAt (fun y : Phase d => y.1 k)
      ((ContinuousLinearMap.proj (R := ℝ) k).comp
        (ContinuousLinearMap.fst ℝ (Fin d → ℝ) (Fin d → ℝ))) w :=
    ((ContinuousLinearMap.proj (R := ℝ) k).comp
      (ContinuousLinearMap.fst ℝ (Fin d → ℝ) (Fin d → ℝ))).hasFDerivAt
  have hI : fderiv ℝ (fun y : Phase d => y.2 k) w =
      (ContinuousLinearMap.proj (R := ℝ) k).comp
        (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin d → ℝ)) :=
    ((ContinuousLinearMap.proj (R := ℝ) k).comp
      (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin d → ℝ))).fderiv
  rw [pb_of_hasFDerivAt hθ]
  show fderiv ℝ (fun y : Phase d => y.2 k) w (0, Pi.single k 1) = 1
  rw [hI]
  simp

/-! ### Smoothness -/

theorem contDiffAt_dirDeriv {a : Phase d → ℝ} {w : Phase d} (v : Phase d)
    (ha : ContDiffAt ℝ ∞ a w) : ContDiffAt ℝ ∞ (dirDeriv v a) w :=
  (ha.fderiv_right (m := ∞) le_rfl).clm_apply contDiffAt_const

theorem contDiffAt_pb {a b : Phase d → ℝ} {w : Phase d} (ha : ContDiffAt ℝ ∞ a w)
    (hb : ContDiffAt ℝ ∞ b w) : ContDiffAt ℝ ∞ (pb a b) w :=
  (ha.fderiv_right (m := ∞) le_rfl).clm_apply
    ((linearFieldCLM (d := d)).contDiff.contDiffAt.comp w (hb.fderiv_right (m := ∞) le_rfl))

theorem differentiableAt_of_contDiffAt {a : Phase d → ℝ} {w : Phase d}
    (ha : ContDiffAt ℝ ∞ a w) : DifferentiableAt ℝ a w :=
  ha.differentiableAt (by simp)

private theorem hasFDerivAt_fderiv {a : Phase d → ℝ} {w : Phase d} (ha : ContDiffAt ℝ ∞ a w) :
    HasFDerivAt (fderiv ℝ a) (fderiv ℝ (fderiv ℝ a) w) w :=
  ((ha.fderiv_right (m := ∞) le_rfl).differentiableAt (by simp)).hasFDerivAt

private theorem symm_snd {a : Phase d → ℝ} {w : Phase d} (ha : ContDiffAt ℝ ∞ a w)
    (u v : Phase d) : fderiv ℝ (fderiv ℝ a) w u v = fderiv ℝ (fderiv ℝ a) w v u :=
  ha.isSymmSndFDerivAt (by simp) u v

/-! ### Second-order calculus -/

/-- The derivative of the bracket: `D{a, b}(w) v = D²a(w)(v)(X_b(w)) - D²b(w)(v)(X_a(w))`. -/
theorem fderiv_pb_apply {a b : Phase d → ℝ} {w : Phase d} (ha : ContDiffAt ℝ ∞ a w)
    (hb : ContDiffAt ℝ ∞ b w) (v : Phase d) :
    fderiv ℝ (pb a b) w v = fderiv ℝ (fderiv ℝ a) w v (hamiltonianVectorField b w) -
      fderiv ℝ (fderiv ℝ b) w v (hamiltonianVectorField a w) := by
  have hX : HasFDerivAt (fun y => linearFieldCLM (fderiv ℝ b y))
      ((linearFieldCLM (d := d)).comp (fderiv ℝ (fderiv ℝ b) w)) w :=
    (linearFieldCLM (d := d)).hasFDerivAt.comp w (hasFDerivAt_fderiv hb)
  have h := (hasFDerivAt_fderiv ha).clm_apply hX
  have hpb : pb a b = fun y => fderiv ℝ a y (linearFieldCLM (fderiv ℝ b y)) := rfl
  have e1 : fderiv ℝ a w (linearFieldCLM (fderiv ℝ (fderiv ℝ b) w v)) =
      -fderiv ℝ (fderiv ℝ b) w v (hamiltonianVectorField a w) :=
    fderiv_apply_linearField a w _
  have e2 : linearFieldCLM (fderiv ℝ b w) = hamiltonianVectorField b w := rfl
  rw [hpb, h.fderiv]
  show fderiv ℝ a w (linearFieldCLM (fderiv ℝ (fderiv ℝ b) w v)) +
      fderiv ℝ (fderiv ℝ a) w v (linearFieldCLM (fderiv ℝ b w)) = _
  rw [e1, e2]
  ring

/-- The derivative of a directional derivative: `D(D_v a)(w) u = D²a(w)(u)(v)`. -/
theorem fderiv_dirDeriv_apply {a : Phase d → ℝ} {w : Phase d} (ha : ContDiffAt ℝ ∞ a w)
    (v u : Phase d) : fderiv ℝ (dirDeriv v a) w u = fderiv ℝ (fderiv ℝ a) w u v := by
  have h := (hasFDerivAt_fderiv ha).clm_apply (hasFDerivAt_const v w)
  have hD : dirDeriv v a = fun y => fderiv ℝ a y v := rfl
  rw [hD, h.fderiv]
  simp

/-- **The derivation rule**: a constant direction `v` differentiates the bracket,
`D_v {a, b} = {D_v a, b} + {a, D_v b}`. -/
theorem dirDeriv_pb {a b : Phase d → ℝ} {w : Phase d} (ha : ContDiffAt ℝ ∞ a w)
    (hb : ContDiffAt ℝ ∞ b w) (v : Phase d) :
    dirDeriv v (pb a b) w = pb (dirDeriv v a) b w + pb a (dirDeriv v b) w := by
  have h1 : dirDeriv v (pb a b) w = fderiv ℝ (pb a b) w v := rfl
  have h2 : pb (dirDeriv v a) b w = fderiv ℝ (dirDeriv v a) w (hamiltonianVectorField b w) := rfl
  have h3 : pb a (dirDeriv v b) w =
      -fderiv ℝ (dirDeriv v b) w (hamiltonianVectorField a w) := pb_antisymm _ _ _
  rw [h1, h2, h3, fderiv_pb_apply ha hb, fderiv_dirDeriv_apply ha, fderiv_dirDeriv_apply hb,
    symm_snd ha (hamiltonianVectorField b w) v, symm_snd hb (hamiltonianVectorField a w) v]
  ring

/-- **The Jacobi identity** `{{a, b}, c} = {{a, c}, b} + {a, {b, c}}` at a point where `a, b, c`
are smooth. -/
theorem pb_jacobi {a b c : Phase d → ℝ} {w : Phase d} (ha : ContDiffAt ℝ ∞ a w)
    (hb : ContDiffAt ℝ ∞ b w) (hc : ContDiffAt ℝ ∞ c w) :
    pb (pb a b) c w = pb (pb a c) b w + pb a (pb b c) w := by
  have h1 : pb (pb a b) c w = fderiv ℝ (pb a b) w (hamiltonianVectorField c w) := rfl
  have h2 : pb (pb a c) b w = fderiv ℝ (pb a c) w (hamiltonianVectorField b w) := rfl
  have h3 : pb a (pb b c) w = -fderiv ℝ (pb b c) w (hamiltonianVectorField a w) :=
    pb_antisymm _ _ _
  rw [h1, h2, h3, fderiv_pb_apply ha hb, fderiv_pb_apply ha hc, fderiv_pb_apply hb hc]
  have sa := symm_snd ha (hamiltonianVectorField b w) (hamiltonianVectorField c w)
  have sb := symm_snd hb (hamiltonianVectorField a w) (hamiltonianVectorField c w)
  have sc := symm_snd hc (hamiltonianVectorField a w) (hamiltonianVectorField b w)
  linarith

end KAM.Application.LambdaDrift

end
