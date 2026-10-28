/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.ODE.Hamiltonian
public import KAM.Planetary.SecularBox.Covariance
public import KAM.Planetary.SecularBox.Region
public import KAM.Planetary.SecularBox.Smooth
public import KAM.Planetary.SecularBox.Rotation
public import KAM.Frozen.Planetary.Defs.ExactSecularHamiltonian
public import KAM.Frozen.Planetary.Defs.JupiterSaturnWeights

/-!
# The secular Hamiltonian vector field on the box

Blueprint `bpP:p14:sb-flow#omega`, `sb-pred` (steps `sb-pr-1`, `sb-pr-2`) and `sb-field`
(steps `sb-fd-1`, `sb-fd-2`).

* `sb_omega`: the fast-action gradient `∂_Λ H_sec`; `reducedSecularH`: the affine reduction at
  fast angle `0`.
* `sb_pred`: on `S` the frozen Hamiltonian-solution predicate is `IsSolutionIn` for `X_H`.
* `sb_field`: `X_H` has zero fast-action component and the slow angular-momentum cancellation.
* `secular_field_components`: the fast-angle component is `sb_omega`, and the slow components are
  the Hamiltonian field of `reducedSecularH`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff
open KAM.Kepler

namespace KAM.Planetary

def sb_omega (m : Fin 2 → ℝ) (mu : ℝ) (w : Phase (2+2)) : Fin 2 → ℝ :=
  fun i => fderiv ℝ (exactSecularHamiltonian m mu) w (0, Fin.append (Pi.single i 1) 0)
def reducedSecularH (m : Fin 2 → ℝ) (mu : ℝ) (I : Fin 2 → ℝ) (y : Phase 2) : ℝ :=
  exactSecularHamiltonian m mu (assemble I 0 y.2 y.1)

private theorem sbField_diffAt (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    {w : Phase (2+2)} (hw : w ∈ sb_sdef saturn) :
    DifferentiableAt ℝ (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) w :=
  ((sb_smooth_prop saturn mu hs).1.differentiableOn (by simp)).differentiableAt
    ((sb_s saturn hs).1.mem_nhds hw)

theorem sb_pred (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    (J : Set ℝ) (z : ℝ → Phase (2+2)) (hz : ∀ t ∈ J, z t ∈ sb_sdef saturn) :
    KAM.Iso.IsHamiltonianSolutionOn (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu)
      univ J z ↔ KAM.ODE.IsSolutionIn
        (KAM.hamiltonianVectorField (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu))
        (sb_sdef saturn) J z := by
  constructor
  · intro h t ht
    exact ⟨hz t ht, (h t ht).2.2⟩
  · intro h t ht
    exact ⟨mem_univ _, sbField_diffAt saturn mu hs (hz t ht), (h t ht).2⟩

private theorem sbField_eta {a b : ℕ} (w : Phase (a+b)) :
    assemble (fast w.2) (fast w.1) (slow w.2) (slow w.1) = w := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
    simp [assemble, fast, slow]

private theorem sbField_shift {a b : ℕ} (w : Phase (a+b)) (i : Fin a) (s : ℝ) :
    w + s • ((Pi.single (Fin.castAdd b i) 1, 0) : Phase (a+b)) =
      assemble (fast w.2) (fast w.1 + s • Pi.single i 1) (slow w.2) (slow w.1) := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;>
    simp [assemble, fast, slow, Pi.single_apply, (Fin.castAdd_injective a b).eq_iff,
      Fin.ext_iff]
  all_goals (intro h; exact absurd h (by have := i.2; omega))

private theorem sbField_rot_deriv {a b : ℕ} (w : Phase (a+b)) :
    HasDerivAt (fun θ => (assemble (fast w.2) (fast w.1)
      (fun i => (rot θ ![slow w.1 i, slow w.2 i]) 1)
      (fun i => (rot θ ![slow w.1 i, slow w.2 i]) 0) : Phase (a+b)))
      ((Fin.append 0 (fun i => -slow w.2 i), Fin.append 0 (slow w.1)) : Phase (a+b)) 0 := by
  refine HasDerivAt.prodMk (hasDerivAt_pi.2 fun k => ?_) (hasDerivAt_pi.2 fun k => ?_) <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simpa [assemble] using hasDerivAt_const (0 : ℝ) (fast w.1 j)
  · simpa [assemble, rot, Pi.sub_def, Pi.add_def] using
      ((Real.hasDerivAt_cos 0).mul_const (slow w.1 j)).sub
        ((Real.hasDerivAt_sin 0).mul_const (slow w.2 j))
  · simpa [assemble] using hasDerivAt_const (0 : ℝ) (fast w.2 j)
  · simpa [assemble, rot, Pi.sub_def, Pi.add_def] using
      ((Real.hasDerivAt_sin 0).mul_const (slow w.1 j)).add
        ((Real.hasDerivAt_cos 0).mul_const (slow w.2 j))

private theorem sbField_rot_zero {a b : ℕ} (w : Phase (a+b)) :
    (assemble (fast w.2) (fast w.1)
      (fun i => (rot 0 ![slow w.1 i, slow w.2 i]) 1)
      (fun i => (rot 0 ![slow w.1 i, slow w.2 i]) 0) : Phase (a+b)) = w := by
  conv_rhs => rw [← sbField_eta w]
  simp [assemble, rot]

/-- A function constant along a differentiable path has vanishing derivative along its tangent. -/
private theorem sbField_fderiv_zero {d : ℕ} {H : Phase d → ℝ} {w : Phase d} {v : Phase d}
    (hH : DifferentiableAt ℝ H w) (γ : ℝ → Phase d) (hγ : HasDerivAt γ v 0) (h0 : γ 0 = w)
    (hc : ∀ s, H (γ s) = H w) : fderiv ℝ H w v = 0 := by
  have h1 := (h0 ▸ hH : DifferentiableAt ℝ H (γ 0)).hasFDerivAt.comp_hasDerivAt 0 hγ
  have h2 : (H ∘ γ) = fun _ => H w := funext hc
  rw [h2, h0] at h1
  exact (hasDerivAt_const (0 : ℝ) (H w)).unique h1 |>.symm

private theorem sbField_clm {d : ℕ} (ℓ : Phase d →L[ℝ] ℝ) (x y : Fin d → ℝ) :
    ℓ (x, y) = ∑ k, x k * ℓ (Pi.single k 1, 0) + ∑ k, y k * ℓ (0, Pi.single k 1) := by
  have hx : ((x, y) : Phase d) = ∑ k, x k • ((Pi.single k 1, 0) : Phase d) +
      ∑ k, y k • ((0, Pi.single k 1) : Phase d) := by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [hx, map_add, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

private theorem sbField_clm_slow {a b : ℕ} (ℓ : Phase (a+b) →L[ℝ] ℝ) (p q : Fin b → ℝ) :
    ℓ (Fin.append (0 : Fin a → ℝ) p, Fin.append (0 : Fin a → ℝ) q) =
      ∑ i, p i * ℓ (Pi.single (Fin.natAdd a i) 1, 0) +
        ∑ i, q i * ℓ (0, Pi.single (Fin.natAdd a i) 1) := by
  rw [sbField_clm, Fin.sum_univ_add, Fin.sum_univ_add]
  simp

theorem sb_field (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    {w : Phase (2+2)} (hw : w ∈ sb_sdef saturn) :
    fast (KAM.hamiltonianVectorField
      (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) w).2 = 0 ∧
    ∑ i, (slow w.1 i * slow
      (KAM.hamiltonianVectorField
        (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) w).1 i +
      slow w.2 i * slow
      (KAM.hamiltonianVectorField
        (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) w).2 i) = 0 := by
  set H := exactSecularHamiltonian (jupiterSaturnWeights saturn) mu with hHdef
  have hd : DifferentiableAt ℝ H w := sbField_diffAt saturn mu hs hw
  have hinv := (sb_smooth_prop saturn mu hs).2.2
  refine ⟨?_, ?_⟩
  · -- `sb-fd-1`: `∂_{λ_i} H = 0`
    funext i
    simp only [fast, KAM.hamiltonianVectorField, Pi.zero_apply]
    rw [neg_eq_zero]
    set d : Phase (2+2) := (Pi.single (Fin.castAdd 2 i) 1, 0) with hd'
    refine sbField_fderiv_zero hd (fun s => w + s • d) ?_ (by simp) fun s => ?_
    · simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add w
    · have := sbField_shift w i s
      rw [this]
      exact hinv w _
  · -- `sb-fd-2`: the rotation identity
    set ℓ := fderiv ℝ H w with hℓ
    have hz : ℓ ((Fin.append 0 (fun i => -slow w.2 i), Fin.append 0 (slow w.1)) :
        Phase (2+2)) = 0 :=
      sbField_fderiv_zero hd _ (sbField_rot_deriv w) (sbField_rot_zero w) fun θ =>
        (sb_rot saturn mu hs hw θ).2
    rw [sbField_clm_slow] at hz
    simp only [KAM.hamiltonianVectorField, slow, Finset.sum_add_distrib]
    simp only [slow, mul_neg, neg_mul, Finset.sum_neg_distrib] at hz ⊢
    linarith

end KAM.Planetary

end
