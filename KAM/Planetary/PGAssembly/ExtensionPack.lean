/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.ExtensionDefs

/-!
# P Part 5: packing `(mu, w)` into one vector (helper for `ext`)

`packVec mu z = (mu, z.1, z.2) ∈ R^(n+n+1)`, the continuous linear unpacking `unpackL`, and the
elementary algebra (sub, real inclusion, norms, differentiability) used to complexify in the
parameter `mu` together with the phase point.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-EX.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology Function

namespace KAM.Planetary

variable {n : ℕ}

/-- The parameter and a phase point packed into one vector. -/
def packVec {R : Type*} (mu : R) (z : (Fin n → R) × (Fin n → R)) : Fin (n + n + 1) → R :=
  Fin.cons (α := fun _ => R) mu (Fin.append z.1 z.2)

@[simp] theorem packVec_zero {R : Type*} (mu : R) (z : (Fin n → R) × (Fin n → R)) :
    packVec mu z 0 = mu := rfl

@[simp] theorem packVec_fst {R : Type*} (mu : R) (z : (Fin n → R) × (Fin n → R)) (i : Fin n) :
    packVec mu z (Fin.succ (Fin.castAdd n i)) = z.1 i := by
  simp only [packVec, Fin.cons_succ, Fin.append_left]

@[simp] theorem packVec_snd {R : Type*} (mu : R) (z : (Fin n → R) × (Fin n → R)) (i : Fin n) :
    packVec mu z (Fin.succ (Fin.natAdd n i)) = z.2 i := by
  simp only [packVec, Fin.cons_succ, Fin.append_right]

/-- The continuous linear unpacking, inverse to `packVec`. -/
def unpackL (n : ℕ) : (Fin (n + n + 1) → ℝ) →L[ℝ] ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (ContinuousLinearMap.proj 0).prod
    ((ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.succ (Fin.castAdd n i))).prod
      (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.succ (Fin.natAdd n i))))

theorem unpackL_packVec (mu : ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    unpackL n (packVec mu z) = (mu, z) := by
  show (packVec mu z 0, (fun i => packVec mu z (Fin.succ (Fin.castAdd n i)),
    fun i => packVec mu z (Fin.succ (Fin.natAdd n i)))) = (mu, z)
  simp only [packVec_zero, packVec_fst, packVec_snd]

theorem packVec_unpackL (y : Fin (n + n + 1) → ℝ) :
    packVec (unpackL n y).1 (unpackL n y).2 = y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [unpackL]
  · refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
    · simp only [unpackL, ContinuousLinearMap.prod_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.pi_apply, packVec_fst]
    · simp only [unpackL, ContinuousLinearMap.prod_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.pi_apply, packVec_snd]

theorem packVec_sub {R : Type*} [AddGroup R] (mu mu' : R) (z z' : (Fin n → R) × (Fin n → R)) :
    packVec mu z - packVec mu' z' = packVec (mu - mu') (z - z') := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j <;>
      simp only [packVec_fst, packVec_snd, Pi.sub_apply, Prod.fst_sub, Prod.snd_sub]

theorem realInclusion_packVec (mu : ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    KAM.realInclusion (n + n + 1) (packVec mu z) =
      packVec (mu : ℂ) (KAM.realInclusion₂ n z) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j <;>
      simp only [packVec_fst, packVec_snd, KAM.realInclusion_apply, KAM.realInclusion₂_apply]

theorem norm_packVec_zero_le (u : (Fin n → ℂ) × (Fin n → ℂ)) :
    ‖packVec (0 : ℂ) u‖ ≤ ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
    · simp only [packVec_fst]
      exact (norm_le_pi_norm u.1 j').trans (le_max_left _ _)
    · simp only [packVec_snd]
      exact (norm_le_pi_norm u.2 j').trans (le_max_right _ _)

theorem differentiable_packVec_sub (mu : ℂ) (c : (Fin n → ℂ) × (Fin n → ℂ)) :
    Differentiable ℂ fun z : (Fin n → ℂ) × (Fin n → ℂ) => packVec mu (z - c) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [packVec_zero]; exact differentiable_const _
  · refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
    · simp only [packVec_fst]
      simp only [Prod.fst_sub, Pi.sub_apply]; fun_prop
    · simp only [packVec_snd]
      simp only [Prod.snd_sub, Pi.sub_apply]; fun_prop

theorem continuous_packVec_sub (c : (Fin n → ℂ) × (Fin n → ℂ)) :
    Continuous fun p : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) => packVec (p.1 : ℂ) (p.2 - c) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [packVec_zero]; exact Complex.continuous_ofReal.comp continuous_fst
  · refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
    · simp only [packVec_fst]
      simp only [Prod.fst_sub, Pi.sub_apply]; fun_prop
    · simp only [packVec_snd]
      simp only [Prod.snd_sub, Pi.sub_apply]; fun_prop

theorem continuous_packVec_real :
    Continuous fun p : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => packVec p.1 p.2 := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [packVec_zero]; exact continuous_fst
  · refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
    · simp only [packVec_fst]; fun_prop
    · simp only [packVec_snd]; fun_prop

end KAM.Planetary

end
