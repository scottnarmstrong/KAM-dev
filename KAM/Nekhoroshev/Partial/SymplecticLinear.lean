/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Nekhoroshev.Partial.Coordinates
public import KAM.Canonical.SymplecticForm
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Linear algebra of the weighted symplectic structure (Part 11, package N11-E1)

Helper module of `KAM.Nekhoroshev.Partial.Symplectic`. The weighted structure on
`EC n k = ℂⁿ × ℂ^{n+(k+k)}` (angles; fast actions, slow `q`, slow `p`) is the standard one on
`ℂ^{n+k} × ℂ^{n+k}` after the regrouping `(θ, (I, q, p)) ↦ ((θ, q), (I, p/c))`:

* `regroup c hc : EC n k ≃L[ℂ] (ℂ^{n+k} × ℂ^{n+k})` (for `c ≠ 0`);
* `wfieldOf_eq`: the weighted field is `L⁻¹ J (ℓ ∘ L⁻¹)`, with `J = KAM.hamiltonianJ`;
* `extForm_eq`: the weighted form `extForm c` is the pull-back of `symplFormC`;
* `canonical_at_iff`: pointwise `ExtCanonical` is `Y J (η ∘ Y) = J η` for `Y = L DΨ L⁻¹`;
* `form_of_bracket`: that identity forces `Y` to preserve `symplFormC`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Nekhoroshev

variable {n k : ℕ}

/-! ### The regrouping -/

/-- `(θ, (I, q, p)) ↦ ((θ, q), (I, p/c))`. -/
def regroupFwd (c : ℝ) (z : EC n k) : (Fin (n+k) → ℂ) × (Fin (n+k) → ℂ) :=
  (Fin.append z.1 (slowPair z).1,
   Fin.append (fastAction z) (fun i => (c:ℂ)⁻¹ * (slowPair z).2 i))

/-- The inverse regrouping `((θ, q), (I, p)) ↦ (θ, (I, q, c p))`. -/
def regroupBwd (c : ℝ) (y : (Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) : EC n k :=
  (fun i => y.1 (Fin.castAdd k i),
   Fin.append (fun i => y.2 (Fin.castAdd k i))
     (Fin.append (fun i => y.1 (Fin.natAdd n i)) (fun i => (c:ℂ) * y.2 (Fin.natAdd n i))))

theorem regroupBwd_fst (c : ℝ) (y : (Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) (i : Fin n) :
    (regroupBwd c y).1 i = y.1 (Fin.castAdd k i) := rfl

theorem regroupBwd_fast (c : ℝ) (y : (Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) (i : Fin n) :
    (regroupBwd c y).2 (Fin.castAdd (k+k) i) = y.2 (Fin.castAdd k i) := by
  simp only [regroupBwd, Fin.append_left]

theorem regroupBwd_q (c : ℝ) (y : (Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) (i : Fin k) :
    (regroupBwd c y).2 (Fin.natAdd n (Fin.castAdd k i)) = y.1 (Fin.natAdd n i) := by
  simp only [regroupBwd, Fin.append_left, Fin.append_right]

theorem regroupBwd_p (c : ℝ) (y : (Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) (i : Fin k) :
    (regroupBwd c y).2 (Fin.natAdd n (Fin.natAdd k i)) = (c:ℂ) * y.2 (Fin.natAdd n i) := by
  simp only [regroupBwd, Fin.append_right]

theorem regroupFwd_fst_left (c : ℝ) (z : EC n k) (i : Fin n) :
    (regroupFwd c z).1 (Fin.castAdd k i) = z.1 i := by
  simp [regroupFwd, Fin.append_left]

theorem regroupFwd_fst_right (c : ℝ) (z : EC n k) (i : Fin k) :
    (regroupFwd c z).1 (Fin.natAdd n i) = z.2 (Fin.natAdd n (Fin.castAdd k i)) := by
  simp [regroupFwd, Fin.append_right, slowPair]

theorem regroupFwd_snd_left (c : ℝ) (z : EC n k) (i : Fin n) :
    (regroupFwd c z).2 (Fin.castAdd k i) = z.2 (Fin.castAdd (k+k) i) := by
  simp [regroupFwd, Fin.append_left, fastAction]

theorem regroupFwd_snd_right (c : ℝ) (z : EC n k) (i : Fin k) :
    (regroupFwd c z).2 (Fin.natAdd n i) = (c:ℂ)⁻¹ * z.2 (Fin.natAdd n (Fin.natAdd k i)) := by
  simp [regroupFwd, Fin.append_right, slowPair]

theorem regroupBwd_fwd (c : ℝ) (hc : c ≠ 0) (z : EC n k) : regroupBwd c (regroupFwd c z) = z := by
  have hc' : (c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · rw [regroupBwd_fst, regroupFwd_fst_left]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [regroupBwd_fast, regroupFwd_snd_left]
    · refine Fin.addCases (fun a => ?_) (fun a => ?_) i
      · rw [regroupBwd_q, regroupFwd_fst_right]
      · rw [regroupBwd_p, regroupFwd_snd_right]; field_simp

theorem regroupFwd_bwd (c : ℝ) (hc : c ≠ 0) (y : (Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) :
    regroupFwd c (regroupBwd c y) = y := by
  have hc' : (c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [regroupFwd_fst_left, regroupBwd_fst]
    · rw [regroupFwd_fst_right, regroupBwd_q]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [regroupFwd_snd_left, regroupBwd_fast]
    · rw [regroupFwd_snd_right, regroupBwd_p]; field_simp

/-- The regrouping as a `ℂ`-linear equivalence. -/
def regroupEquiv (c : ℝ) (hc : c ≠ 0) :
    EC n k ≃ₗ[ℂ] (Fin (n+k) → ℂ) × (Fin (n+k) → ℂ) where
  toFun := regroupFwd c
  invFun := regroupBwd c
  map_add' x y := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [regroupFwd_fst_left, Prod.fst_add, Pi.add_apply]
      · simp only [regroupFwd_fst_right, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [regroupFwd_snd_left, Prod.snd_add, Pi.add_apply]
      · simp only [regroupFwd_snd_right, Prod.snd_add, Pi.add_apply, mul_add]
  map_smul' a x := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [regroupFwd_fst_left, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply]
      · simp only [regroupFwd_fst_right, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
          RingHom.id_apply]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [regroupFwd_snd_left, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
      · simp only [regroupFwd_snd_right, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply,
          smul_eq_mul]
        ring
  left_inv := regroupBwd_fwd c hc
  right_inv := regroupFwd_bwd c hc

/-- The regrouping as a continuous linear equivalence. -/
def regroup (c : ℝ) (hc : c ≠ 0) : EC n k ≃L[ℂ] (Fin (n+k) → ℂ) × (Fin (n+k) → ℂ) :=
  (regroupEquiv c hc).toContinuousLinearEquiv

theorem regroup_apply (c : ℝ) (hc : c ≠ 0) (z : EC n k) : regroup c hc z = regroupFwd c z := rfl

theorem regroup_symm_apply (c : ℝ) (hc : c ≠ 0) (y : (Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) :
    (regroup c hc).symm y = regroupBwd c y := rfl

/-! ### The weighted form -/

/-- The weighted symplectic form. -/
def extForm (c : ℝ) (v w : EC n k) : ℂ :=
  (∑ i, (fastAction v i*w.1 i-v.1 i*fastAction w i)) +
    (c:ℂ)⁻¹*(∑ i, ((slowPair v).2 i*(slowPair w).1 i-(slowPair v).1 i*(slowPair w).2 i))

theorem extForm_eq (c : ℝ) (v w : EC n k) :
    extForm c v w = KAM.Canonical.symplFormC (regroupFwd c v) (regroupFwd c w) := by
  unfold extForm KAM.Canonical.symplFormC
  rw [Fin.sum_univ_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [regroupFwd_snd_left, regroupFwd_fst_left, regroupFwd_fst_left, regroupFwd_snd_left]
    rfl
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [regroupFwd_snd_right, regroupFwd_fst_right, regroupFwd_fst_right, regroupFwd_snd_right]
    simp only [slowPair]
    ring

theorem extForm_eq_regroup (c : ℝ) (hc : c ≠ 0) (v w : EC n k) :
    extForm c v w = KAM.Canonical.symplFormC (regroup c hc v) (regroup c hc w) :=
  extForm_eq c v w

/-! ### The weighted field of a functional -/

/-- The weighted field in terms of the derivative functional `ℓ`. -/
def wfieldOf (c : ℝ) (ℓ : EC n k →L[ℂ] ℂ) : EC n k :=
  (fun i => ℓ (0, Pi.single (Fin.castAdd (k+k) i) 1),
   Fin.append (fun i => -ℓ (Pi.single i 1, 0))
    (Fin.append
      (fun i => (c : ℂ) * ℓ (0, Pi.single (Fin.natAdd n (Fin.natAdd k i)) 1))
      (fun i => -(c : ℂ) * ℓ (0, Pi.single (Fin.natAdd n (Fin.castAdd k i)) 1))))

theorem wfield_eq_wfieldOf (c : ℝ) (H : EC n k → ℂ) (z : EC n k) :
    wfield c H z = wfieldOf c (fderiv ℂ H z) := rfl

section basis

variable (c : ℝ) (i : Fin n) (j : Fin k)

/-- Pointwise tail for the index case analyses below. -/
local macro "idx_tail" a:ident : tactic =>
  `(tactic| (simp [Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;>
    (have := $a.2; first | rfl | omega | (exfalso; omega))))

theorem regroupBwd_single_b1 :
    regroupBwd c ((0 : Fin (n+k) → ℂ), (Pi.single (Fin.castAdd k i) 1 : Fin (n+k) → ℂ)) =
      ((0 : Fin n → ℂ), (Pi.single (Fin.castAdd (k+k) i) 1 : Fin (n+(k+k)) → ℂ)) := by
  refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
  · simp [regroupBwd]
  · refine ext_cases (P := fun a => _ = _) (fun a => ?_) (fun a => ?_) (fun a => ?_) a
    · rw [regroupBwd_fast]; idx_tail a
    · rw [regroupBwd_q]; idx_tail a
    · rw [regroupBwd_p]; idx_tail a

theorem regroupBwd_single_b2 :
    regroupBwd c ((0 : Fin (n+k) → ℂ), (Pi.single (Fin.natAdd n j) 1 : Fin (n+k) → ℂ)) =
      (c:ℂ) • ((0 : Fin n → ℂ),
        (Pi.single (Fin.natAdd n (Fin.natAdd k j)) 1 : Fin (n+(k+k)) → ℂ)) := by
  refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
  · simp [regroupBwd]
  · refine ext_cases (P := fun a => _ = _) (fun a => ?_) (fun a => ?_) (fun a => ?_) a
    · rw [regroupBwd_fast]; idx_tail a
    · rw [regroupBwd_q]; idx_tail a
    · rw [regroupBwd_p]; idx_tail a

theorem regroupBwd_single_b3 :
    regroupBwd c ((Pi.single (Fin.castAdd k i) 1 : Fin (n+k) → ℂ), (0 : Fin (n+k) → ℂ)) =
      ((Pi.single i 1 : Fin n → ℂ), (0 : Fin (n+(k+k)) → ℂ)) := by
  refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
  · rw [regroupBwd_fst]; idx_tail a
  · refine ext_cases (P := fun a => _ = _) (fun a => ?_) (fun a => ?_) (fun a => ?_) a
    · rw [regroupBwd_fast]; idx_tail a
    · rw [regroupBwd_q]; idx_tail a
    · rw [regroupBwd_p]; idx_tail a

theorem regroupBwd_single_b4 :
    regroupBwd c ((Pi.single (Fin.natAdd n j) 1 : Fin (n+k) → ℂ), (0 : Fin (n+k) → ℂ)) =
      ((0 : Fin n → ℂ),
        (Pi.single (Fin.natAdd n (Fin.castAdd k j)) 1 : Fin (n+(k+k)) → ℂ)) := by
  refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
  · rw [regroupBwd_fst]; idx_tail a
  · refine ext_cases (P := fun a => _ = _) (fun a => ?_) (fun a => ?_) (fun a => ?_) a
    · rw [regroupBwd_fast]; idx_tail a
    · rw [regroupBwd_q]; idx_tail a
    · rw [regroupBwd_p]; idx_tail a

end basis

/-- `wfieldOf c ℓ = L⁻¹ J (ℓ ∘ L⁻¹)`. -/
theorem wfieldOf_eq (c : ℝ) (hc : c ≠ 0) (ℓ : EC n k →L[ℂ] ℂ) :
    wfieldOf c ℓ =
      regroupBwd c (KAM.hamiltonianJ (ℓ.comp (regroup c hc).symm.toContinuousLinearMap)) := by
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · rw [regroupBwd_fst]
    show ℓ (0, Pi.single (Fin.castAdd (k+k) i) 1) =
      ℓ (regroupBwd c (0, Pi.single (Fin.castAdd k i) 1))
    rw [regroupBwd_single_b1]
  · refine ext_cases (P := fun j => _ = _) (fun i => ?_) (fun i => ?_) (fun i => ?_) j
    · rw [regroupBwd_fast]
      simp only [wfieldOf, Fin.append_left]
      show -ℓ (Pi.single i 1, 0) = -ℓ (regroupBwd c (Pi.single (Fin.castAdd k i) 1, 0))
      rw [regroupBwd_single_b3]
    · rw [regroupBwd_q]
      simp only [wfieldOf, Fin.append_right, Fin.append_left]
      show (c:ℂ) * ℓ (0, Pi.single (Fin.natAdd n (Fin.natAdd k i)) 1) =
        ℓ (regroupBwd c (0, Pi.single (Fin.natAdd n i) 1))
      rw [regroupBwd_single_b2, map_smul, smul_eq_mul]
    · rw [regroupBwd_p]
      simp only [wfieldOf, Fin.append_right]
      show -(c:ℂ) * ℓ (0, Pi.single (Fin.natAdd n (Fin.castAdd k i)) 1) =
        (c:ℂ) * -ℓ (regroupBwd c (Pi.single (Fin.natAdd n i) 1, 0))
      rw [regroupBwd_single_b4]
      ring

/-! ### Pointwise canonicity as a bracket identity -/

/-- The conjugate `L A L⁻¹` of a linear map `A` of `EC n k` to the regrouped space. -/
def conjLin (c : ℝ) (hc : c ≠ 0) (A : EC n k →L[ℂ] EC n k) :
    ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) →L[ℂ] ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) :=
  (regroup c hc).toContinuousLinearMap.comp (A.comp (regroup c hc).symm.toContinuousLinearMap)

theorem conjLin_apply (c : ℝ) (hc : c ≠ 0) (A : EC n k →L[ℂ] EC n k) (y) :
    conjLin c hc A y = regroup c hc (A ((regroup c hc).symm y)) := rfl

theorem bracket_pair (c : ℝ) (hc : c ≠ 0) {Ψ : EC n k → EC n k} {z : EC n k}
    (hΨ : DifferentiableAt ℂ Ψ z) (u v : EC n k →L[ℂ] ℂ) :
    extBracket c (fun x => u (Ψ x)) (fun x => v (Ψ x)) z =
      (u.comp (regroup c hc).symm.toContinuousLinearMap)
        (conjLin c hc (fderiv ℂ Ψ z) (KAM.hamiltonianJ
          ((v.comp (regroup c hc).symm.toContinuousLinearMap).comp
            (conjLin c hc (fderiv ℂ Ψ z))))) ∧
    extBracket c (fun x => u x) (fun x => v x) (Ψ z) =
      (u.comp (regroup c hc).symm.toContinuousLinearMap)
        (KAM.hamiltonianJ (v.comp (regroup c hc).symm.toContinuousLinearMap)) := by
  set L := regroup c hc with hLdef
  have hdu : fderiv ℂ (fun x => u (Ψ x)) z = u.comp (fderiv ℂ Ψ z) :=
    (u.hasFDerivAt.comp z hΨ.hasFDerivAt).fderiv
  have hdv : fderiv ℂ (fun x => v (Ψ x)) z = v.comp (fderiv ℂ Ψ z) :=
    (v.hasFDerivAt.comp z hΨ.hasFDerivAt).fderiv
  constructor
  · unfold extBracket
    rw [hdu, wfield_eq_wfieldOf, hdv, wfieldOf_eq c hc]
    have : (v.comp (fderiv ℂ Ψ z)).comp L.symm.toContinuousLinearMap =
        (v.comp L.symm.toContinuousLinearMap).comp (conjLin c hc (fderiv ℂ Ψ z)) := by
      refine ContinuousLinearMap.ext fun w => ?_
      simp [conjLin_apply, hLdef]
    rw [this]
    simp [conjLin_apply, hLdef, regroup_symm_apply]
  · unfold extBracket
    rw [u.fderiv, wfield_eq_wfieldOf, v.fderiv, wfieldOf_eq c hc]
    rfl

theorem sep_dual {a b : (Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)}
    (h : ∀ ξ : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) →L[ℂ] ℂ, ξ a = ξ b) : a = b :=
  (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 h

theorem canonical_at_iff (c : ℝ) (hc : c ≠ 0) {Ψ : EC n k → EC n k} {z : EC n k}
    (hΨ : DifferentiableAt ℂ Ψ z) :
    (∀ u v : EC n k →L[ℂ] ℂ,
      extBracket c (fun x => u (Ψ x)) (fun x => v (Ψ x)) z =
        extBracket c (fun x => u x) (fun x => v x) (Ψ z)) ↔
    ∀ η : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) →L[ℂ] ℂ,
      conjLin c hc (fderiv ℂ Ψ z) (KAM.hamiltonianJ (η.comp (conjLin c hc (fderiv ℂ Ψ z)))) =
        KAM.hamiltonianJ η := by
  set L := regroup c hc with hLdef
  have hcomp : ∀ ξ : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) →L[ℂ] ℂ,
      (ξ.comp L.toContinuousLinearMap).comp L.symm.toContinuousLinearMap = ξ := fun ξ => by
    refine ContinuousLinearMap.ext fun w => ?_; simp [hLdef]
  constructor
  · intro h η
    refine sep_dual fun ξ => ?_
    have := h (ξ.comp L.toContinuousLinearMap) (η.comp L.toContinuousLinearMap)
    rw [(bracket_pair c hc hΨ _ _).1, (bracket_pair c hc hΨ _ _).2, hcomp, hcomp] at this
    exact this
  · intro h u v
    rw [(bracket_pair c hc hΨ _ _).1, (bracket_pair c hc hΨ _ _).2, h]

/-! ### The form is invariant when the bracket is -/

/-- The functional `w ↦ -ω(a, w)`. -/
def dualOfVec (a : (Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) :
    ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => -KAM.Canonical.symplFormC a w
      map_add' := fun x y => by rw [KAM.Canonical.symplFormC_add_right]; ring
      map_smul' := fun r x => by
        rw [KAM.Canonical.symplFormC_smul_right]; simp }

theorem hamiltonianJ_dualOfVec (a : (Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) :
    KAM.hamiltonianJ (dualOfVec a) = a := by
  refine KAM.Canonical.symplFormC_eq_of_left fun w => ?_
  rw [KAM.Canonical.symplFormC_hamiltonianJ]
  simp [dualOfVec]

/-- `Y J (η ∘ Y) = J η` for all `η` forces `Y` to preserve `symplFormC`. -/
theorem form_of_bracket
    (Y : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) →L[ℂ] ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)))
    (hY : ∀ η : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) →L[ℂ] ℂ,
      Y (KAM.hamiltonianJ (η.comp Y)) = KAM.hamiltonianJ η) :
    ∀ v w, KAM.Canonical.symplFormC (Y v) (Y w) = KAM.Canonical.symplFormC v w := by
  have hsurj : Function.Surjective
      ((Y : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) →L[ℂ] ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ))) :
        ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) →ₗ[ℂ] ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ))) :=
    fun b => ⟨KAM.hamiltonianJ ((dualOfVec b).comp Y), by
      show Y _ = b
      rw [hY, hamiltonianJ_dualOfVec]⟩
  have hinj := LinearMap.injective_iff_surjective.2 hsurj
  intro v w
  set η := dualOfVec (Y v) with hη
  have h1 : Y (KAM.hamiltonianJ (η.comp Y)) = Y v := by rw [hY, hη, hamiltonianJ_dualOfVec]
  have h2 : KAM.hamiltonianJ (η.comp Y) = v := hinj h1
  have h3 := KAM.Canonical.symplFormC_hamiltonianJ (η.comp Y) w
  rw [h2] at h3
  rw [h3]
  simp [hη, dualOfVec]

end KAM.Nekhoroshev

end
