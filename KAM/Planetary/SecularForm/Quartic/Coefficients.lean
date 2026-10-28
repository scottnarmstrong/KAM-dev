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

include hI hJ hab in
theorem analyticAt_pairQuartic (w : PairW) :
    AnalyticAt ℝ (fun IJ : ℝ × ℝ => pairQuartic D i j IJ.1 IJ.2 w) (I0, J0) := by
  obtain ⟨N, hN, h0, -, hF, hA⟩ := pair_secular_nbhd D i j hI hJ hab
  set Gs : (ℝ × ℝ) × PairW → ℝ := fun p => secular (pairData D i j) false (pairEmb p) with hGs
  let v : Fin 4 → (ℝ × ℝ) × PairW := fun _ => ((0 : ℝ × ℝ), w)
  have hJ4 : AnalyticOnNhd ℝ (fun x => iteratedFDeriv ℝ 4 Gs x v) N := fun x hx =>
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 4 => (ℝ × ℝ) × PairW) ℝ v).analyticAt _).comp
      ((hA.iteratedFDeriv_of_isOpen hN 4) x hx)
  have hEq : ∀ IJ : ℝ × ℝ, (IJ, (0 : PairW)) ∈ N →
      pairQuartic D i j IJ.1 IJ.2 w = iteratedFDeriv ℝ 4 Gs (IJ, 0) v / 24 := by
    intro IJ hIJ
    unfold pairQuartic
    congr 1
    set a : (ℝ × ℝ) × PairW := (IJ, 0) with ha
    have h1 : Continuous fun w' : PairW => (IJ, w') := continuous_const.prodMk continuous_id
    have hev : (fun w' : PairW => pairSlowSecular D i j IJ.1 IJ.2 w') =ᶠ[𝓝 (0 : PairW)]
        fun w' => Gs (IJ, w') := by
      filter_upwards [(hN.preimage h1).mem_nhds hIJ] with w' hw'
      exact hF (IJ, w') hw'
    rw [(hev.iteratedFDeriv ℝ 4).self_of_nhds]
    let inr : PairW →L[ℝ] (ℝ × ℝ) × PairW := ContinuousLinearMap.inr ℝ (ℝ × ℝ) PairW
    have hcomp : (fun w' : PairW => Gs (IJ, w')) = (fun z => Gs (z + a)) ∘ inr := by
      funext w'; simp [inr, ha]
    have hadd : Continuous fun z : (ℝ × ℝ) × PairW => z + a := continuous_id.add continuous_const
    have hU : IsOpen ((fun z : (ℝ × ℝ) × PairW => z + a) ⁻¹' N) := hN.preimage hadd
    have hcd : ContDiffOn ℝ 4 (fun z => Gs (z + a)) ((fun z : (ℝ × ℝ) × PairW => z + a) ⁻¹' N) :=
      (hA.contDiffOn hN.uniqueDiffOn).comp (contDiff_id.add contDiff_const).contDiffOn
        fun z hz => hz
    have key := iteratedFDeriv_comp_clm_of_isOpen hU hcd inr (x := 0)
      (by simpa [inr, ha] using hIJ) (le_refl 4)
    rw [hcomp, key, iteratedFDeriv_comp_add_right]
    simp [inr, ha, v]
  have hV : IsOpen {IJ : ℝ × ℝ | (IJ, (0 : PairW)) ∈ N} :=
    hN.preimage (continuous_id.prodMk continuous_const)
  have hmap : AnalyticAt ℝ (fun IJ : ℝ × ℝ => (IJ, (0 : PairW))) (I0, J0) :=
    analyticAt_id.prod analyticAt_const
  have hfin : AnalyticAt ℝ (fun IJ : ℝ × ℝ => iteratedFDeriv ℝ 4 Gs (IJ, 0) v / 24) (I0, J0) :=
    (AnalyticAt.comp_of_eq (hJ4 _ h0) hmap rfl).div_const
  refine hfin.congr ?_
  filter_upwards [hV.mem_nhds h0] with IJ hIJ
  exact (hEq IJ hIJ).symm

include hI hJ hab in
theorem analyticAt_quarticCoeff :
    AnalyticAt ℝ (fun IJ : ℝ × ℝ => quarticCoeff D i j IJ) (I0, J0) := by
  have hF : ∀ m : Fin 6, AnalyticAt ℝ
      (fun IJ : ℝ × ℝ => pairQuartic D i j IJ.1 IJ.2 (testPt m)) (I0, J0) := fun m =>
    analyticAt_pairQuartic D i j hI hJ hab (testPt m)
  refine analyticAt_pi_iff.2 fun k => ?_
  fin_cases k <;> simp only [quarticCoeff] <;> simp <;> fun_prop

end SecularForm
end KAM.Planetary
end
