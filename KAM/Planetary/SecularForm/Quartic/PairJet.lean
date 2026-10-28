/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.PairSymmetry

/-!
# Secular form: the six-monomial form of the pair jet

Blueprint P, Part 8, `stepP:p8:q4-str`: the fourth derivative of the pair average at `u = 0` is a
combination of the six quartic monomials.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

variable {n : ℕ}

/-- Iterated derivative of a composition with a continuous linear map, on an open set. -/
theorem iteratedFDeriv_comp_clm_of_isOpen {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 4 f U)
    (g : G →L[ℝ] E) {x : G} (hx : g x ∈ U) {k : ℕ} (hk : k ≤ 4) :
    iteratedFDeriv ℝ k (f ∘ g) x =
      (iteratedFDeriv ℝ k f (g x)).compContinuousLinearMap fun _ => g := by
  have hU' : IsOpen (g ⁻¹' U) := hU.preimage g.continuous
  have h := g.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hU'.uniqueDiffOn hx
    (by exact_mod_cast hk)
  rwa [iteratedFDerivWithin_of_isOpen k hU' (show x ∈ g ⁻¹' U from hx),
    iteratedFDerivWithin_of_isOpen k hU hx] at h

variable (D : Data n) (i j : Fin n) {I0 J0 : ℝ} (hI : 0 < I0) (hJ : 0 < J0)
  (hab : I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) < J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0)))

include hI hJ hab in
theorem pair_matW_invariant {R : Matrix (Fin 2) (Fin 2) ℝ} (hR : R.transpose * R = 1) :
    ∀ᶠ w in 𝓝 (0 : PairW), pairSlowSecular D i j I0 J0 (matW R w) =
      pairSlowSecular D i j I0 J0 w := by
  obtain ⟨θ, h | h⟩ := orth_cases R hR
  · have : ∀ w, matW R w = rotW θ w := fun w => Prod.ext (h _) (h _)
    simp_rw [this]
    exact pair_rot_invariant D i j hI hJ hab θ
  · have : ∀ w, matW R w = rotW θ (reflW w) := fun w => Prod.ext (h _) (h _)
    simp_rw [this]
    have hr : Tendsto reflW (𝓝 (0 : PairW)) (𝓝 0) := by
      have := continuous_reflW.tendsto (0 : PairW)
      have e : reflW 0 = 0 := by
        refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;> simp [reflW]
      rwa [e] at this
    filter_upwards [hr.eventually (pair_rot_invariant D i j hI hJ hab θ),
      pair_refl_invariant D i j hI hJ hab] with w h1 h2
    exact h1.trans h2

include hI hJ hab in
theorem pair_contDiffOn :
    ∃ U : Set PairW, IsOpen U ∧ (0 : PairW) ∈ U ∧
      ContDiffOn ℝ 4 (fun w : PairW => pairSlowSecular D i j I0 J0 w) U := by
  obtain ⟨N, hN, h0, -, hF, hA, -⟩ := pair_secular_nbhd D i j hI hJ hab
  have h1 : Continuous fun w : PairW => ((I0, J0), w) := continuous_const.prodMk continuous_id
  refine ⟨_, hN.preimage h1, h0, ?_⟩
  have hAn : AnalyticOnNhd ℝ
      (fun w : PairW => secular (pairData D i j) false (pairEmb ((I0, J0), w)))
      ((fun w : PairW => ((I0, J0), w)) ⁻¹' N) := fun w hw =>
    (hA _ hw).comp (AnalyticAt.prod (analyticAt_const (v := (I0, J0))) analyticAt_id)
  have hAn' : AnalyticOnNhd ℝ (fun w : PairW => pairSlowSecular D i j I0 J0 w)
      ((fun w : PairW => ((I0, J0), w)) ⁻¹' N) :=
    hAn.congr (hN.preimage h1) fun w hw => (hF _ hw).symm
  exact hAn'.contDiffOn (hN.preimage h1).uniqueDiffOn

include hI hJ hab in
theorem pair_quartic_structure :
    ∃ c : Fin 6 → ℝ, ∀ w : PairW,
      iteratedFDeriv ℝ 4 (fun w' : PairW => pairSlowSecular D i j I0 J0 w') 0 (fun _ => w) =
        ∑ k, c k * quarticMonomials w.1 w.2 k := by
  obtain ⟨U, hU, h0, hcd⟩ := pair_contDiffOn D i j hI hJ hab
  set Fp : PairW → ℝ := fun w' => pairSlowSecular D i j I0 J0 w' with hFp
  let sendPair : PairVec →L[ℝ] PairW :=
    (ContinuousLinearMap.proj 0).prod (ContinuousLinearMap.proj 1)
  let M : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => PairVec) ℝ :=
    (iteratedFDeriv ℝ 4 Fp 0).compContinuousLinearMap fun _ => sendPair
  have hinv : ∀ R : Matrix (Fin 2) (Fin 2) ℝ, R.transpose * R = 1 → ∀ u : PairVec,
      M (fun _ => fun p => R.mulVec (u p)) = M (fun _ => u) := by
    intro R hR u
    have hev : Fp ∘ matW R =ᶠ[𝓝 (0 : PairW)] Fp := pair_matW_invariant D i j hI hJ hab hR
    have h1 := (hev.iteratedFDeriv ℝ 4).self_of_nhds
    have h2 := iteratedFDeriv_comp_clm_of_isOpen hU hcd (matW R) (x := 0)
      (by rw [map_zero]; exact h0) (le_refl 4)
    rw [h1] at h2
    have h3 := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => PairW) ℝ =>
      T (fun _ => (u 0, u 1))) h2
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at h3
    have e0 : matW R 0 = 0 := map_zero _
    rw [e0] at h3
    have e1 : sendPair (fun p => R.mulVec (u p)) = matW R (u 0, u 1) := rfl
    have e2 : sendPair u = (u 0, u 1) := rfl
    simp only [M, ContinuousMultilinearMap.compContinuousLinearMap_apply, e1, e2]
    exact h3.symm
  obtain ⟨c, hc⟩ := quartic_form_of_invariant M hinv
  refine ⟨c, fun w => ?_⟩
  have := hc ![w.1, w.2]
  simp only [M, ContinuousMultilinearMap.compContinuousLinearMap_apply] at this
  simpa [sendPair] using this

end SecularForm
end KAM.Planetary
end
