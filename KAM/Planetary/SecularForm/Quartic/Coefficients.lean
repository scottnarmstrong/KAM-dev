/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.PairJet

/-!
# Secular form: the six quartic coefficients of a pair

Blueprint P, Part 8, `stepP:p8:q4-str`: the six invariant coefficients `quarticCoeff` of the pair
jet are explicit linear combinations of the fourth derivative at six test vectors; they are real
analytic in the two actions and represent the whole fourth derivative.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

variable {n : ℕ}

/-- The quartic part `(1/24) d⁴ S_ij (0)[w⁴]` of the pair average. -/
def pairQuartic (D : Data n) (i j : Fin n) (I J : ℝ) (w : PairW) : ℝ :=
  iteratedFDeriv ℝ 4 (fun w' : PairW => pairSlowSecular D i j I J w') 0 (fun _ => w) / 24

/-- Six test vectors on which the monomial matrix is invertible. -/
def testPt : Fin 6 → PairW :=
  ![(![1, 0], ![0, 0]), (![0, 0], ![1, 0]), (![1, 0], ![0, 1]), (![1, 0], ![1, 0]),
    (![1, 0], ![-1, 0]), (![1, 0], ![2, 0])]

/-- The six coefficients, read off from the quartic part at the six test vectors. -/
def quarticCoeff (D : Data n) (i j : Fin n) (IJ : ℝ × ℝ) : Fin 6 → ℝ :=
  let F : Fin 6 → ℝ := fun m => pairQuartic D i j IJ.1 IJ.2 (testPt m)
  let c5 : ℝ := (F 5 - F 0 - 16 * F 1 - 4 * (F 2 - F 0 - F 1) -
    4 * ((F 3 + F 4) / 2 - F 2) - 2 * ((F 3 - F 4) / 2)) / 6
  ![F 0, F 1, F 2 - F 0 - F 1, (F 3 + F 4) / 2 - F 2, (F 3 - F 4) / 2 - c5, c5]

variable (D : Data n) (i j : Fin n) {I0 J0 : ℝ} (hI : 0 < I0) (hJ : 0 < J0)
  (hab : I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) < J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0)))

include hI hJ hab in
theorem pairQuartic_eq (w : PairW) :
    pairQuartic D i j I0 J0 w =
      ∑ k, quarticCoeff D i j (I0, J0) k * quarticMonomials w.1 w.2 k := by
  obtain ⟨c, hc⟩ := pair_quartic_structure D i j hI hJ hab
  have E : ∀ w : PairW, pairQuartic D i j I0 J0 w =
      ∑ k, (c k / 24) * quarticMonomials w.1 w.2 k := fun w => by
    unfold pairQuartic
    rw [hc w, Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h0 := E (testPt 0)
  have h1 := E (testPt 1)
  have h2 := E (testPt 2)
  have h3 := E (testPt 3)
  have h4 := E (testPt 4)
  have h5 := E (testPt 5)
  simp [Fin.sum_univ_succ, quarticMonomials, planeSq, planeDot, testPt] at h0 h1 h2 h3 h4 h5
  have hq : quarticCoeff D i j (I0, J0) = fun k => c k / 24 := by
    funext k
    fin_cases k <;> simp [quarticCoeff, testPt] <;> linarith
  rw [E w, hq]

end SecularForm
end KAM.Planetary
end
