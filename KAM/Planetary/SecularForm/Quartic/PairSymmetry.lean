/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.PairAnalytic
public import KAM.Planetary.SecularForm.Quartic.Invariant
public import KAM.Planetary.SecularForm.Quartic.Orthogonal
public import KAM.Planetary.SecularForm.Symmetry

/-!
# Secular form: the quartic jet of the pair average

Blueprint P, Part 8, `stepP:p8:q4-str`: the pair average is invariant under simultaneous
orthogonal transformations of the two eccentricity-type vectors (by `evenness` of the two-planet
secular function), so its fourth derivative at `0` has the six-monomial form.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

variable {n : ℕ}

/-- Pairs of planar vectors, as a product. -/
abbrev PairW := (Fin 2 → ℝ) × (Fin 2 → ℝ)

/-- The simultaneous action of a `2 × 2` matrix on both planar vectors. -/
def matW (R : Matrix (Fin 2) (Fin 2) ℝ) : PairW →L[ℝ] PairW :=
  (LinearMap.toContinuousLinearMap (Matrix.mulVecLin R)).prodMap
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin R))

theorem matW_apply (R : Matrix (Fin 2) (Fin 2) ℝ) (w : PairW) :
    matW R w = (R.mulVec w.1, R.mulVec w.2) := rfl

def rotW (θ : ℝ) (w : PairW) : PairW := (rot θ w.1, rot θ w.2)

def reflW (w : PairW) : PairW := (![w.1 0, -w.1 1], ![w.2 0, -w.2 1])

private theorem continuous_rot (θ : ℝ) : Continuous (rot θ) := by
  refine continuous_pi fun k => ?_
  fin_cases k <;> simp [rot] <;> fun_prop

theorem continuous_rotW (θ : ℝ) : Continuous (rotW θ) :=
  ((continuous_rot θ).comp continuous_fst).prodMk ((continuous_rot θ).comp continuous_snd)

theorem continuous_reflW : Continuous reflW := by
  refine Continuous.prodMk (continuous_pi fun k => ?_) (continuous_pi fun k => ?_) <;>
    fin_cases k <;> simp <;> fun_prop

theorem pairEmb_rotW (q : ℝ × ℝ) (θ : ℝ) (w : PairW) :
    pairEmb (q, rotW θ w) = rotateSlow θ (pairEmb (q, w)) := by
  refine Prod.ext (funext fun k => ?_) (Prod.ext rfl (funext fun k => ?_)) <;>
    fin_cases k <;> simp [pairEmb_apply, rotateSlow, rotW, vec2_eta]

theorem pairEmb_reflW (q : ℝ × ℝ) (w : PairW) :
    pairEmb (q, reflW w) = ((pairEmb (q, w)).1, (pairEmb (q, w)).2.1, -(pairEmb (q, w)).2.2) := by
  refine Prod.ext (funext fun k => ?_) (Prod.ext rfl (funext fun k => ?_)) <;>
    fin_cases k <;> simp [pairEmb_apply, reflW]

theorem eventually_pair_mem {N : Set ((ℝ × ℝ) × PairW)} (hN : IsOpen N) {q : ℝ × ℝ}
    (h0 : (q, (0 : PairW)) ∈ N) {f : PairW → PairW} (hf : Continuous f) (hf0 : f 0 = 0) :
    ∀ᶠ w in 𝓝 (0 : PairW), (q, w) ∈ N ∧ (q, f w) ∈ N := by
  have h1 : Continuous fun w : PairW => (q, w) := continuous_const.prodMk continuous_id
  have h2 : Continuous fun w : PairW => (q, f w) := continuous_const.prodMk hf
  have a : ∀ᶠ w in 𝓝 (0 : PairW), (q, w) ∈ N := (hN.preimage h1).mem_nhds h0
  have b : ∀ᶠ w in 𝓝 (0 : PairW), (q, f w) ∈ N :=
    (hN.preimage h2).mem_nhds (by show (q, f 0) ∈ N; rw [hf0]; exact h0)
  exact a.and b

variable (D : Data n) (i j : Fin n) {I0 J0 : ℝ} (hI : 0 < I0) (hJ : 0 < J0)
  (hab : I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) < J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0)))

include hI hJ hab in
theorem pair_rot_invariant (θ : ℝ) :
    ∀ᶠ w in 𝓝 (0 : PairW), pairSlowSecular D i j I0 J0 (rotW θ w) =
      pairSlowSecular D i j I0 J0 w := by
  obtain ⟨N, hN, h0, hmem, hF, -⟩ := pair_secular_nbhd D i j hI hJ hab
  filter_upwards [eventually_pair_mem hN h0 (continuous_rotW θ) (by simp [rotW, rot])] with w hw
  have e1 := hF _ hw.2
  have e2 := hF _ hw.1
  simp only at e1 e2
  rw [e1, e2, pairEmb_rotW]
  exact (evenness (pairData D i j) (hmem _ hw.1) false θ).2.2.2

include hI hJ hab in
theorem pair_refl_invariant :
    ∀ᶠ w in 𝓝 (0 : PairW), pairSlowSecular D i j I0 J0 (reflW w) =
      pairSlowSecular D i j I0 J0 w := by
  obtain ⟨N, hN, h0, hmem, hF, -⟩ := pair_secular_nbhd D i j hI hJ hab
  filter_upwards [eventually_pair_mem hN h0 continuous_reflW (by simp [reflW])] with w hw
  have e1 := hF _ hw.2
  have e2 := hF _ hw.1
  simp only at e1 e2
  rw [e1, e2, pairEmb_reflW]
  exact (evenness (pairData D i j) (hmem _ hw.1) false 0).2.1

end SecularForm
end KAM.Planetary
end
