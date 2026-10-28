/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Product
public import KAM.Planetary.Hamiltonian.Chart

/-!
# The oscillator polar chart and the full lattice

Blueprint P, Part 7 (`bpP:p7:lattice`): the polar chart `Θ_n` with `(ξ, η) = √(2R) (sin ψ, cos ψ)`
on the slow block, and the composite `Φ_n = Ψ^{(n)} ∘ Θ_n`.  Everything is blockwise: `polarMap`
is the one-planet polar map `polar1` on each `planetBlock`, so analyticity and symplecticity are
inherited from the explicit one-planet derivative.  The full lattice is `fullShift k = (2π k, 0)`,
`k : Fin (n + n) → ℤ`; `fullShift` and `angleScale` (`S_c`) are owned by Part 1
(`KAM.Planetary.Hamiltonian.Chart`).
-/

@[expose] public noncomputable section

open Set Metric Real
open scoped ContDiff

namespace KAM.Planetary

open KAM KAM.Kepler

section PolarChart

variable {n : ℕ}

/-- `bpP:p7:lattice`: the oscillator polar chart `Θ_n` and `Φ_n = Ψ^{(n)} ∘ Θ_n`
(coordinates `z = ((φ, ψ), (I, R))`). -/
def polarDom (n : ℕ) : Set (Phase (n + n)) :=
  {z | ∀ i, 0 < fast z.2 i ∧ 0 < slow z.2 i ∧ slow z.2 i < fast z.2 i}

def polarMap (z : Phase (n + n)) : Phase (n + n) :=
  assemble (fast z.2) (fast z.1) (fun i => √(2 * slow z.2 i) * Real.cos (slow z.1 i))
    (fun i => √(2 * slow z.2 i) * Real.sin (slow z.1 i))

/-! ### Block calculus -/

/-- The one-planet polar map `(ψ, R) ↦ √(2R) (sin ψ, cos ψ)` (with `(λ, Λ)` untouched). -/
def polar1 (w : Phase 2) : Phase 2 :=
  (![w.1 0, √(2 * w.2 1) * Real.sin (w.1 1)], ![w.2 0, √(2 * w.2 1) * Real.cos (w.1 1)])

/-- The one-planet polar domain. -/
def polarDom1 : Set (Phase 2) := {w | 0 < w.2 0 ∧ 0 < w.2 1 ∧ w.2 1 < w.2 0}

theorem planetBlock_polarMap (z : Phase (n + n)) (i : Fin n) :
    planetBlock (polarMap z) i = polar1 (planetBlock z i) := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;>
    simp [planetBlock, polarMap, polar1, assemble, fast, slow, Fin.append_left]

theorem mem_polarDom_iff {z : Phase (n + n)} : z ∈ polarDom n ↔ ∀ i, planetBlock z i ∈ polarDom1 := by
  simp [polarDom, polarDom1, planetBlock, fast, slow]

/-- Reassembling the blocks of a point gives the point back. -/
theorem unblock_planetBlock (z : Phase (n + n)) : unblock (fun i => planetBlock z i) = z := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [unblock, planetBlock, fast, slow, Fin.append_left]

theorem polarMap_eq_unblock (z : Phase (n + n)) :
    polarMap z = unblock fun i => polar1 (planetBlock z i) := by
  conv_lhs => rw [← unblock_planetBlock (polarMap z)]
  congr 1
  funext i
  exact planetBlock_polarMap z i

/-- `unblock` as a linear map. -/
def unblockLin : (Fin n → Phase 2) →ₗ[ℝ] Phase (n + n) where
  toFun := unblock
  map_add' P Q := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [unblock, Fin.append_left]
  map_smul' c P := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [unblock, Fin.append_left]

/-- `unblock` as a continuous linear map. -/
def unblockCLM : (Fin n → Phase 2) →L[ℝ] Phase (n + n) :=
  LinearMap.toContinuousLinearMap unblockLin

theorem unblockCLM_apply (P : Fin n → Phase 2) : unblockCLM P = unblock P := rfl

/-! ### The one-planet polar map -/

private theorem hasFDerivAt_polar1 {w : Phase 2} (hR : 0 < w.2 1) :
    ∃ L : Phase 2 →L[ℝ] Phase 2, HasFDerivAt polar1 L w ∧ ∀ u : Phase 2,
      L u = (![u.1 0, (√(2 * w.2 1))⁻¹ * Real.sin (w.1 1) * u.2 1 +
                √(2 * w.2 1) * Real.cos (w.1 1) * u.1 1],
             ![u.2 0, (√(2 * w.2 1))⁻¹ * Real.cos (w.1 1) * u.2 1 -
                √(2 * w.2 1) * Real.sin (w.1 1) * u.1 1]) := by
  let c : Phase 2 →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).comp (ContinuousLinearMap.fst ℝ _ _)
  let r : Phase 2 →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).comp (ContinuousLinearMap.snd ℝ _ _)
  let a : Phase 2 →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp (ContinuousLinearMap.fst ℝ _ _)
  let b : Phase 2 →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp (ContinuousLinearMap.snd ℝ _ _)
  have h2R : (2 * w.2 1) ≠ 0 := by positivity
  have hs : HasFDerivAt (fun w : Phase 2 => √(2 * w.2 1))
      ((1 / (2 * √(2 * w.2 1))) • ((2 : ℝ) • r)) w :=
    HasFDerivAt.sqrt (f := fun w : Phase 2 => 2 * w.2 1) (r.hasFDerivAt.const_mul 2) h2R
  have hsin : HasFDerivAt (fun w : Phase 2 => Real.sin (w.1 1)) (Real.cos (w.1 1) • c) w :=
    c.hasFDerivAt.sin
  have hcos : HasFDerivAt (fun w : Phase 2 => Real.cos (w.1 1)) (-Real.sin (w.1 1) • c) w :=
    c.hasFDerivAt.cos
  have hg1 := hs.mul hsin
  have hg2 := hs.mul hcos
  let X1 : Phase 2 →L[ℝ] ℝ :=
    (√(2 * w.2 1) * Real.cos (w.1 1)) • c + (Real.sin (w.1 1) * (1 / (2 * √(2 * w.2 1)) * 2)) • r
  let X2 : Phase 2 →L[ℝ] ℝ :=
    (-(√(2 * w.2 1) * Real.sin (w.1 1))) • c + (Real.cos (w.1 1) * (1 / (2 * √(2 * w.2 1)) * 2)) • r
  let L : Phase 2 →L[ℝ] Phase 2 :=
    (ContinuousLinearMap.pi (![a, X1] : Fin 2 → Phase 2 →L[ℝ] ℝ)).prod
      (ContinuousLinearMap.pi (![b, X2] : Fin 2 → Phase 2 →L[ℝ] ℝ))
  refine ⟨L, ?_, fun u => ?_⟩
  · refine HasFDerivAt.prodMk ?_ ?_
    · refine hasFDerivAt_pi'.2 fun k => ?_
      fin_cases k
      · exact a.hasFDerivAt
      · refine hg1.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
        simp [X1, c, r]
        ring
    · refine hasFDerivAt_pi'.2 fun k => ?_
      fin_cases k
      · exact b.hasFDerivAt
      · refine hg2.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
        simp [X2, c, r]
        ring
  · refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;>
      simp [L, X1, X2, a, b, c, r] <;> field_simp <;> ring

end PolarChart

end KAM.Planetary

end
