/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Planetary.Defs.Fast
public import KAM.Frozen.Planetary.Defs.Slow

/-!
# The period-one rescaling and the field conversion (package LP-DICT, Part B, items 5–6)

Package LP-DICT, MAIN Lemma 13 (`LP:MAIN L13 (435–441)`), track LP, non-frozen; the statement
surface
is proposed in `docs/tracks/LP/FREEZE-PROPOSAL.md`.

`lpRescale ℓ : Phase (n + n) →L[ℝ] ER n n` sends a chart point `((λ, ξ), (Λ, η))` to the engine
point
`(θ, (I, q, p)) = (λ/(2π), (Λ, ξ/ℓ, η/ℓ))` with the engine's slot order (angles; fast actions; slow
`q`; slow `p`).  `lpUnrescale ℓ` is its inverse.  `lpRescale_hasDerivAt` is the field conversion at
unchanged physical time: a solution of the chart Hamiltonian field of `G` maps to a solution of
`realWfield (2π/ℓ²)` of `Ĝ = (1/(2π)) • (G ∘ lpUnrescale ℓ)`.  The conventions match exactly (no
sign
or factor mismatch): `θ̇ = Ĝ_I`, `İ = −Ĝ_θ`, `q̇ = c Ĝ_p`, `ṗ = −c Ĝ_q` with `c = 2π/ℓ²`.
-/

@[expose] public noncomputable section

open KAM KAM.Planetary KAM.Nekhoroshev Set

namespace KAM.Planetary.StrongAMD

variable {n : ℕ}

/-- `simp` normalises `Fin.natAdd n i` to `i.addNat n` when both blocks have length `n`. -/
@[simp] theorem lp_append_addNat {α : Type*} (u v : Fin n → α) (i : Fin n) :
    Fin.append u v (i.addNat n) = v i := by
  have : i.addNat n = Fin.natAdd n i := Fin.ext (Nat.add_comm _ _)
  rw [this]; exact Fin.append_right u v i

/-- The rescaling as a bare function (period-one angles, fast action unchanged, slow pair over
`ℓ`). -/
def lpRescaleFun (ℓ : ℝ) (w : Phase (n + n)) : ER n n :=
  (fun i => fast w.1 i / (2 * Real.pi),
   Fin.append (fast w.2) (Fin.append (fun i => slow w.1 i / ℓ) (fun i => slow w.2 i / ℓ)))

/-- The inverse rescaling as a bare function. -/
def lpUnrescaleFun (ℓ : ℝ) (y : ER n n) : Phase (n + n) :=
  (Fin.append (fun i => 2 * Real.pi * y.1 i)
      (fun i => ℓ * y.2 (Fin.natAdd n (Fin.castAdd n i))),
   Fin.append (fun i => y.2 (Fin.castAdd (n + n) i))
      (fun i => ℓ * y.2 (Fin.natAdd n (Fin.natAdd n i))))

/-- `lpRescaleFun` as a linear map. -/
def lpRescaleLin (ℓ : ℝ) : Phase (n + n) →ₗ[ℝ] ER n n where
  toFun := lpRescaleFun ℓ
  map_add' u v := by
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · simp [lpRescaleFun, fast, add_div]
    · refine Fin.addCases (fun i => ?_) (fun j => ?_) j
      · simp [lpRescaleFun, fast]
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [lpRescaleFun, slow, add_div]
  map_smul' c v := by
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · simp [lpRescaleFun, fast]; ring
    · refine Fin.addCases (fun i => ?_) (fun j => ?_) j
      · simp [lpRescaleFun, fast]
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [lpRescaleFun, slow] <;> ring

/-- `lpUnrescaleFun` as a linear map. -/
def lpUnrescaleLin (ℓ : ℝ) : ER n n →ₗ[ℝ] Phase (n + n) where
  toFun := lpUnrescaleFun ℓ
  map_add' u v := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [lpUnrescaleFun] <;> ring
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [lpUnrescaleFun]; ring
  map_smul' c v := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [lpUnrescaleFun] <;> ring
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [lpUnrescaleFun]; ring

/-- The period-one rescaling `lpRescale ℓ : Phase (n + n) →L[ℝ] ER n n`
(`θ = λ/(2π)`, fast action `Λ`, slow pair `(ξ, η)/ℓ`; `LP:MAIN L13 (435–441)`). -/
def lpRescale (ℓ : ℝ) : Phase (n + n) →L[ℝ] ER n n :=
  LinearMap.toContinuousLinearMap (lpRescaleLin ℓ)

/-- The inverse of `lpRescale ℓ` (for `ℓ ≠ 0`). -/
def lpUnrescale (ℓ : ℝ) : ER n n →L[ℝ] Phase (n + n) :=
  LinearMap.toContinuousLinearMap (lpUnrescaleLin ℓ)

theorem lpRescale_apply (ℓ : ℝ) (w : Phase (n + n)) : lpRescale ℓ w = lpRescaleFun ℓ w := rfl

theorem lpUnrescale_apply (ℓ : ℝ) (y : ER n n) : lpUnrescale ℓ y = lpUnrescaleFun ℓ y := rfl

theorem lpUnrescale_lpRescale {ℓ : ℝ} (hℓ : ℓ ≠ 0) (w : Phase (n + n)) :
    lpUnrescale ℓ (lpRescale ℓ w) = w := by
  rw [lpRescale_apply, lpUnrescale_apply]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [lpUnrescaleFun, lpRescaleFun, fast]; field_simp
    · simp [lpUnrescaleFun, lpRescaleFun, slow]; field_simp
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [lpUnrescaleFun, lpRescaleFun, fast]
    · simp [lpUnrescaleFun, lpRescaleFun, slow]; field_simp

theorem lpRescale_lpUnrescale {ℓ : ℝ} (hℓ : ℓ ≠ 0) (y : ER n n) :
    lpRescale ℓ (lpUnrescale ℓ y) = y := by
  rw [lpRescale_apply, lpUnrescale_apply]
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp [lpUnrescaleFun, lpRescaleFun, fast]
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp [lpUnrescaleFun, lpRescaleFun, fast]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
        simp [lpUnrescaleFun, lpRescaleFun, slow] <;> field_simp

/-- `lpRescale ℓ` as a continuous linear equivalence. -/
def lpRescaleEquiv {ℓ : ℝ} (hℓ : ℓ ≠ 0) : Phase (n + n) ≃L[ℝ] ER n n :=
  ContinuousLinearEquiv.equivOfInverse (lpRescale ℓ) (lpUnrescale ℓ)
    (lpUnrescale_lpRescale hℓ) (lpRescale_lpUnrescale hℓ)

/-! ### Reading the engine coordinates -/

theorem fastAction_lpRescale (ℓ : ℝ) (w : Phase (n + n)) :
    fastAction (lpRescale ℓ w) = fast w.2 := by
  funext i; simp [lpRescale_apply, lpRescaleFun, fastAction]

theorem slowPair_lpRescale (ℓ : ℝ) (w : Phase (n + n)) :
    slowPair (lpRescale ℓ w) = (fun i => slow w.1 i / ℓ, fun i => slow w.2 i / ℓ) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    simp [lpRescale_apply, lpRescaleFun, slowPair]

/-- `ℓ • slowPair (lpRescale ℓ w)` is the chart slow pair `((ξ_i), (η_i))`. -/
theorem smul_slowPair_lpRescale {ℓ : ℝ} (hℓ : ℓ ≠ 0) (w : Phase (n + n)) :
    ℓ • slowPair (lpRescale ℓ w) = (slow w.1, slow w.2) := by
  rw [slowPair_lpRescale]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [mul_div_cancel₀ _ hℓ]

/-- Closing tactic for the basis-vector computations. -/
local macro "lp_basis" : tactic =>
  `(tactic| (simp [lpUnrescale_apply, lpUnrescaleFun, Pi.single_apply, Fin.ext_iff] <;>
    first | omega | (intro h; exfalso; omega) | (split_ifs <;> first | omega | simp_all) | skip))

/-! ### Basis vectors under the inverse rescaling -/

theorem lpUnrescale_theta (ℓ : ℝ) (i : Fin n) :
    lpUnrescale ℓ ((Pi.single i 1 : Fin n → ℝ), (0 : Fin (n + (n + n)) → ℝ)) =
      (2 * Real.pi) • ((Pi.single (Fin.castAdd n i) 1 : Fin (n + n) → ℝ),
        (0 : Fin (n + n) → ℝ)) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      lp_basis
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      lp_basis

theorem lpUnrescale_fast (ℓ : ℝ) (i : Fin n) :
    lpUnrescale ℓ ((0 : Fin n → ℝ), (Pi.single (Fin.castAdd (n + n) i) 1 : Fin (n + (n + n)) → ℝ)) =
      ((0 : Fin (n + n) → ℝ), (Pi.single (Fin.castAdd n i) 1 : Fin (n + n) → ℝ)) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      lp_basis
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      lp_basis

theorem lpUnrescale_q (ℓ : ℝ) (i : Fin n) :
    lpUnrescale ℓ ((0 : Fin n → ℝ),
        (Pi.single (Fin.natAdd n (Fin.castAdd n i)) 1 : Fin (n + (n + n)) → ℝ)) =
      ℓ • ((Pi.single (Fin.natAdd n i) 1 : Fin (n + n) → ℝ), (0 : Fin (n + n) → ℝ)) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      lp_basis
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      lp_basis

theorem lpUnrescale_p (ℓ : ℝ) (i : Fin n) :
    lpUnrescale ℓ ((0 : Fin n → ℝ),
        (Pi.single (Fin.natAdd n (Fin.natAdd n i)) 1 : Fin (n + (n + n)) → ℝ)) =
      ℓ • ((0 : Fin (n + n) → ℝ), (Pi.single (Fin.natAdd n i) 1 : Fin (n + n) → ℝ)) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      lp_basis
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      lp_basis

/-! ### The field conversion -/

/-- The rescaled Hamiltonian `Ĝ = (1/(2π)) • (G ∘ lpUnrescale ℓ)`. -/
def lpRescaleHam (ℓ : ℝ) (G : Phase (n + n) → ℝ) : ER n n → ℝ :=
  fun y => (1 / (2 * Real.pi)) * G (lpUnrescale ℓ y)

theorem lpRescaleHam_hasFDerivAt {ℓ : ℝ} (hℓ : ℓ ≠ 0) {G : Phase (n + n) → ℝ}
    {w : Phase (n + n)} (hd : DifferentiableAt ℝ G w) :
    HasFDerivAt (lpRescaleHam ℓ G)
      ((1 / (2 * Real.pi)) • (fderiv ℝ G w).comp (lpUnrescale ℓ)) (lpRescale ℓ w) := by
  have hG : HasFDerivAt G (fderiv ℝ G w) (lpUnrescale ℓ (lpRescale ℓ w)) := by
    rw [lpUnrescale_lpRescale hℓ]; exact hd.hasFDerivAt
  exact (hG.comp (lpRescale ℓ w) (lpUnrescale ℓ).hasFDerivAt).const_mul _

/-- Pointwise field conversion: the rescaling carries the chart Hamiltonian field of `G` to the
engine's weighted field `realWfield (2π/ℓ²)` of `Ĝ`. -/
theorem lpRescale_field {ℓ : ℝ} (hℓ : ℓ ≠ 0) {G : Phase (n + n) → ℝ} {w : Phase (n + n)}
    (hd : DifferentiableAt ℝ G w) :
    lpRescale ℓ (hamiltonianVectorField G w) =
      realWfield (2 * Real.pi / ℓ ^ 2) (lpRescaleHam ℓ G) (lpRescale ℓ w) := by
  have hfd := (lpRescaleHam_hasFDerivAt hℓ hd).fderiv
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  unfold realWfield
  rw [hfd]
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp only [lpRescale_apply, lpRescaleFun, hamiltonianVectorField, fast,
      smul_apply, ContinuousLinearMap.comp_apply, lpUnrescale_fast,
      smul_eq_mul]
    ring
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp only [lpRescale_apply, lpRescaleFun, hamiltonianVectorField, fast, Fin.append_left,
        smul_apply, ContinuousLinearMap.comp_apply, lpUnrescale_theta,
        map_smul, smul_eq_mul, neg_mul]
      field_simp
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [lpRescale_apply, lpRescaleFun, hamiltonianVectorField, slow, Fin.append_right,
        Fin.append_left,
          smul_apply, ContinuousLinearMap.comp_apply, lpUnrescale_p,
          map_smul, smul_eq_mul]
        field_simp
      · simp only [lpRescale_apply, lpRescaleFun, hamiltonianVectorField, slow, Fin.append_right,
          smul_apply, ContinuousLinearMap.comp_apply, lpUnrescale_q,
          map_smul, smul_eq_mul, neg_mul]
        field_simp

/-- Solutions of the chart Hamiltonian field of `G` map to solutions of the engine's weighted field
of `Ĝ = lpRescaleHam ℓ G`, in unchanged physical time. -/
theorem lpRescale_hasDerivAt {ℓ : ℝ} (hℓ : ℓ ≠ 0) {G : Phase (n + n) → ℝ}
    {w : ℝ → Phase (n + n)} {t : ℝ} (hd : DifferentiableAt ℝ G (w t))
    (hw : HasDerivAt w (hamiltonianVectorField G (w t)) t) :
    HasDerivAt (lpRescale ℓ ∘ w)
      (realWfield (2 * Real.pi / ℓ ^ 2) (lpRescaleHam ℓ G) (lpRescale ℓ (w t))) t := by
  rw [← lpRescale_field hℓ hd]
  exact (lpRescale ℓ).hasFDerivAt.comp_hasDerivAt t hw

end KAM.Planetary.StrongAMD

end
