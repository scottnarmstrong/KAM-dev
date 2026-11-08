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
public import KAM.Planetary.StrongAMD.NonresonantAdapterRescale

/-!
# The period-one rescaling for unequal fast and slow blocks

Source: re-typing of the planar chart-dictionary Part B adapter (`LP:MAIN L13 (435–441)`),
track LP, non-frozen.

`lpRescaleNM ℓ : Phase (n + m) →L[ℝ] ER n m` sends a chart point `((λ, ξ), (Λ, η))`, with `n` fast
pairs and `m` slow pairs (slow positions in `w.1`, slow momenta in `w.2`), to the engine point
`(θ, (I, q, p)) = (λ/(2π), (Λ, ξ/ℓ, η/ℓ))`.  `lpUnrescaleNM ℓ` is its inverse for `ℓ ≠ 0`.
`lpRescaleNM_hasDerivAt` is the field conversion at unchanged physical time: a solution of the
chart Hamiltonian field of `G` maps to a solution of `realWfield (2π/ℓ²)` of
`Ĝ = (1/(2π)) • (G ∘ lpUnrescaleNM ℓ)`.  The slot and sign conventions match for every `m`
(`θ̇ = Ĝ_I`, `İ = −Ĝ_θ`, `q̇ = c Ĝ_p`, `ṗ = −c Ĝ_q`, `c = 2π/ℓ²`).
The spatial chart is `m = n + n`.
-/

@[expose] public noncomputable section

open KAM KAM.Planetary KAM.Nekhoroshev Set

namespace KAM.Planetary.Spatial

variable {n m : ℕ}

/-- The rescaling as a bare function (period-one angles, fast action unchanged, slow pair over
`ℓ`). -/
def lpRescaleNMFun (ℓ : ℝ) (w : Phase (n + m)) : ER n m :=
  (fun i => fast w.1 i / (2 * Real.pi),
   Fin.append (fast w.2) (Fin.append (fun i => slow w.1 i / ℓ) (fun i => slow w.2 i / ℓ)))

/-- The inverse rescaling as a bare function. -/
def lpUnrescaleNMFun (ℓ : ℝ) (y : ER n m) : Phase (n + m) :=
  (Fin.append (fun i => 2 * Real.pi * y.1 i)
      (fun i => ℓ * y.2 (Fin.natAdd n (Fin.castAdd m i))),
   Fin.append (fun i => y.2 (Fin.castAdd (m + m) i))
      (fun i => ℓ * y.2 (Fin.natAdd n (Fin.natAdd m i))))

/-- `lpRescaleNMFun` as a linear map. -/
def lpRescaleNMLin (ℓ : ℝ) : Phase (n + m) →ₗ[ℝ] ER n m where
  toFun := lpRescaleNMFun ℓ
  map_add' u v := by
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · simp [lpRescaleNMFun, fast, add_div]
    · refine Fin.addCases (fun i => ?_) (fun j => ?_) j
      · simp [lpRescaleNMFun, fast]
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [lpRescaleNMFun, slow, add_div]
  map_smul' c v := by
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · simp [lpRescaleNMFun, fast]; ring
    · refine Fin.addCases (fun i => ?_) (fun j => ?_) j
      · simp [lpRescaleNMFun, fast]
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [lpRescaleNMFun, slow] <;> ring

/-- `lpUnrescaleNMFun` as a linear map. -/
def lpUnrescaleNMLin (ℓ : ℝ) : ER n m →ₗ[ℝ] Phase (n + m) where
  toFun := lpUnrescaleNMFun ℓ
  map_add' u v := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [lpUnrescaleNMFun] <;> ring
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [lpUnrescaleNMFun]; ring
  map_smul' c v := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [lpUnrescaleNMFun] <;> ring
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [lpUnrescaleNMFun]; ring

/-- The period-one rescaling `lpRescaleNM ℓ : Phase (n + m) →L[ℝ] ER n m`
(`θ = λ/(2π)`, fast action `Λ`, slow pair `(ξ, η)/ℓ`; `LP:MAIN L13 (435–441)`). -/
def lpRescaleNM (ℓ : ℝ) : Phase (n + m) →L[ℝ] ER n m :=
  LinearMap.toContinuousLinearMap (lpRescaleNMLin ℓ)

/-- The inverse of `lpRescaleNM ℓ` (for `ℓ ≠ 0`). -/
def lpUnrescaleNM (ℓ : ℝ) : ER n m →L[ℝ] Phase (n + m) :=
  LinearMap.toContinuousLinearMap (lpUnrescaleNMLin ℓ)

theorem lpRescaleNM_apply (ℓ : ℝ) (w : Phase (n + m)) : lpRescaleNM ℓ w = lpRescaleNMFun ℓ w := rfl

theorem lpUnrescaleNM_apply (ℓ : ℝ) (y : ER n m) : lpUnrescaleNM ℓ y = lpUnrescaleNMFun ℓ y := rfl

theorem lpUnrescaleNM_lpRescaleNM {ℓ : ℝ} (hℓ : ℓ ≠ 0) (w : Phase (n + m)) :
    lpUnrescaleNM ℓ (lpRescaleNM ℓ w) = w := by
  rw [lpRescaleNM_apply, lpUnrescaleNM_apply]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [lpUnrescaleNMFun, lpRescaleNMFun, fast]; field_simp
    · simp [lpUnrescaleNMFun, lpRescaleNMFun, slow]; field_simp
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [lpUnrescaleNMFun, lpRescaleNMFun, fast]
    · simp [lpUnrescaleNMFun, lpRescaleNMFun, slow]; field_simp

theorem lpRescaleNM_lpUnrescaleNM {ℓ : ℝ} (hℓ : ℓ ≠ 0) (y : ER n m) :
    lpRescaleNM ℓ (lpUnrescaleNM ℓ y) = y := by
  rw [lpRescaleNM_apply, lpUnrescaleNM_apply]
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp [lpUnrescaleNMFun, lpRescaleNMFun, fast]
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp [lpUnrescaleNMFun, lpRescaleNMFun, fast]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
        simp [lpUnrescaleNMFun, lpRescaleNMFun, slow] <;> field_simp

/-! ### Reading the engine coordinates -/

theorem fastAction_lpRescaleNM (ℓ : ℝ) (w : Phase (n + m)) :
    fastAction (lpRescaleNM ℓ w) = fast w.2 := by
  funext i; simp [lpRescaleNM_apply, lpRescaleNMFun, fastAction]

theorem slowPair_lpRescaleNM (ℓ : ℝ) (w : Phase (n + m)) :
    slowPair (lpRescaleNM ℓ w) = (fun i => slow w.1 i / ℓ, fun i => slow w.2 i / ℓ) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    simp [lpRescaleNM_apply, lpRescaleNMFun, slowPair]

/-- `ℓ • slowPair (lpRescaleNM ℓ w)` is the chart slow pair `((ξ_i), (η_i))`. -/
theorem smul_slowPair_lpRescaleNM {ℓ : ℝ} (hℓ : ℓ ≠ 0) (w : Phase (n + m)) :
    ℓ • slowPair (lpRescaleNM ℓ w) = (slow w.1, slow w.2) := by
  rw [slowPair_lpRescaleNM]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [mul_div_cancel₀ _ hℓ]

/-- Closing tactic for the basis-vector computations. -/
local macro "lp_basis" : tactic =>
  `(tactic| (simp [lpUnrescaleNM_apply, lpUnrescaleNMFun, Pi.single_apply, Fin.ext_iff] <;>
    first | omega | (intro h; exfalso; omega) | (split_ifs <;> first | omega | simp_all) | skip))

/-! ### Basis vectors under the inverse rescaling -/

theorem lpUnrescaleNM_theta (ℓ : ℝ) (i : Fin n) :
    lpUnrescaleNM ℓ ((Pi.single i 1 : Fin n → ℝ), (0 : Fin (n + (m + m)) → ℝ)) =
      (2 * Real.pi) • ((Pi.single (Fin.castAdd m i) 1 : Fin (n + m) → ℝ),
        (0 : Fin (n + m) → ℝ)) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      lp_basis
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      lp_basis

theorem lpUnrescaleNM_fast (ℓ : ℝ) (i : Fin n) :
    lpUnrescaleNM ℓ ((0 : Fin n → ℝ),
      (Pi.single (Fin.castAdd (m + m) i) 1 : Fin (n + (m + m)) → ℝ)) =
      ((0 : Fin (n + m) → ℝ), (Pi.single (Fin.castAdd m i) 1 : Fin (n + m) → ℝ)) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      lp_basis
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      lp_basis

theorem lpUnrescaleNM_q (ℓ : ℝ) (i : Fin m) :
    lpUnrescaleNM ℓ ((0 : Fin n → ℝ),
        (Pi.single (Fin.natAdd n (Fin.castAdd m i)) 1 : Fin (n + (m + m)) → ℝ)) =
      ℓ • ((Pi.single (Fin.natAdd n i) 1 : Fin (n + m) → ℝ), (0 : Fin (n + m) → ℝ)) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      lp_basis
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      lp_basis

theorem lpUnrescaleNM_p (ℓ : ℝ) (i : Fin m) :
    lpUnrescaleNM ℓ ((0 : Fin n → ℝ),
        (Pi.single (Fin.natAdd n (Fin.natAdd m i)) 1 : Fin (n + (m + m)) → ℝ)) =
      ℓ • ((0 : Fin (n + m) → ℝ), (Pi.single (Fin.natAdd n i) 1 : Fin (n + m) → ℝ)) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      lp_basis
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      lp_basis

/-! ### The field conversion -/

/-- The rescaled Hamiltonian `Ĝ = (1/(2π)) • (G ∘ lpUnrescaleNM ℓ)`. -/
def lpRescaleHamNM (ℓ : ℝ) (G : Phase (n + m) → ℝ) : ER n m → ℝ :=
  fun y => (1 / (2 * Real.pi)) * G (lpUnrescaleNM ℓ y)

theorem lpRescaleHamNM_hasFDerivAt {ℓ : ℝ} (hℓ : ℓ ≠ 0) {G : Phase (n + m) → ℝ}
    {w : Phase (n + m)} (hd : DifferentiableAt ℝ G w) :
    HasFDerivAt (lpRescaleHamNM ℓ G)
      ((1 / (2 * Real.pi)) • (fderiv ℝ G w).comp (lpUnrescaleNM ℓ)) (lpRescaleNM ℓ w) := by
  have hG : HasFDerivAt G (fderiv ℝ G w) (lpUnrescaleNM ℓ (lpRescaleNM ℓ w)) := by
    rw [lpUnrescaleNM_lpRescaleNM hℓ]; exact hd.hasFDerivAt
  exact (hG.comp (lpRescaleNM ℓ w) (lpUnrescaleNM ℓ).hasFDerivAt).const_mul _

/-- Pointwise field conversion: the rescaling carries the chart Hamiltonian field of `G` to the
engine's weighted field `realWfield (2π/ℓ²)` of `Ĝ`. -/
theorem lpRescaleNM_field {ℓ : ℝ} (hℓ : ℓ ≠ 0) {G : Phase (n + m) → ℝ} {w : Phase (n + m)}
    (hd : DifferentiableAt ℝ G w) :
    lpRescaleNM ℓ (hamiltonianVectorField G w) =
      realWfield (2 * Real.pi / ℓ ^ 2) (lpRescaleHamNM ℓ G) (lpRescaleNM ℓ w) := by
  have hfd := (lpRescaleHamNM_hasFDerivAt hℓ hd).fderiv
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  unfold realWfield
  rw [hfd]
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp only [lpRescaleNM_apply, lpRescaleNMFun, hamiltonianVectorField, fast,
      smul_apply, ContinuousLinearMap.comp_apply, lpUnrescaleNM_fast,
      smul_eq_mul]
    ring
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp only [lpRescaleNM_apply, lpRescaleNMFun, hamiltonianVectorField, fast, Fin.append_left,
        smul_apply, ContinuousLinearMap.comp_apply, lpUnrescaleNM_theta,
        map_smul, smul_eq_mul, neg_mul]
      field_simp
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [lpRescaleNM_apply, lpRescaleNMFun, hamiltonianVectorField, slow,
          Fin.append_right,
        Fin.append_left,
          smul_apply, ContinuousLinearMap.comp_apply, lpUnrescaleNM_p,
          map_smul, smul_eq_mul]
        field_simp
      · simp only [lpRescaleNM_apply, lpRescaleNMFun, hamiltonianVectorField, slow,
          Fin.append_right,
          smul_apply, ContinuousLinearMap.comp_apply, lpUnrescaleNM_q,
          map_smul, smul_eq_mul, neg_mul]
        field_simp

/-- Solutions of the chart Hamiltonian field of `G` map to solutions of the engine's weighted field
of `Ĝ = lpRescaleHamNM ℓ G`, in unchanged physical time. -/
theorem lpRescaleNM_hasDerivAt {ℓ : ℝ} (hℓ : ℓ ≠ 0) {G : Phase (n + m) → ℝ}
    {w : ℝ → Phase (n + m)} {t : ℝ} (hd : DifferentiableAt ℝ G (w t))
    (hw : HasDerivAt w (hamiltonianVectorField G (w t)) t) :
    HasDerivAt (lpRescaleNM ℓ ∘ w)
      (realWfield (2 * Real.pi / ℓ ^ 2) (lpRescaleHamNM ℓ G) (lpRescaleNM ℓ (w t))) t := by
  rw [← lpRescaleNM_field hℓ hd]
  exact (lpRescaleNM ℓ).hasFDerivAt.comp_hasDerivAt t hw

end KAM.Planetary.Spatial

end
