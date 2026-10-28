/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.Invariant
public import KAM.Planetary.SecularForm.Quartic.PairSymmetry
public import KAM.Planetary.PGAssembly.JetsPolar

/-!
# Secular form: the quadratic and quartic Taylor parts of an `O(2)`-invariant analytic function

Blueprint P, Part 8, `stepP:p8:q4-a`: an analytic function of two planar vectors that is invariant
under simultaneous orthogonal transformations near `0` has the Taylor expansion
`F(0) + (A |w₁|² + A' |w₂|² + B w₁·w₂) + ∑ c_m (quarticMonomials w₁ w₂) m + O(‖w‖⁵)`; the odd
parts vanish (use `-1`), the quadratic part is an invariant quadratic form (`quadratic_invariant`)
and the quartic part is an invariant quartic form (`quartic_form_of_invariant`).
-/

@[expose] public noncomputable section
open Set Filter Asymptotics
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

/-- The second derivative of any function is a homogeneous quadratic polynomial in the
coordinates. -/
theorem exists_poly_of_multilinear_two
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => PairVec) ℝ) :
    ∃ P : MvPolynomial (Fin 2 × Fin 2) ℝ, P.IsHomogeneous 2 ∧
      ∀ u : PairVec, M (fun _ => u) = MvPolynomial.eval (fun ic => u ic.1 ic.2) P := by
  classical
  let e : Fin 2 × Fin 2 → PairVec := fun ic => Pi.single ic.1 (Pi.single ic.2 1)
  refine ⟨∑ r : Fin 2 → Fin 2 × Fin 2,
    MvPolynomial.C (M fun k => e (r k)) * ∏ k, MvPolynomial.X (r k), ?_, fun u => ?_⟩
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun r _ => ?_
    have h1 : (∏ k : Fin 2, (MvPolynomial.X (r k) : MvPolynomial (Fin 2 × Fin 2) ℝ)).IsHomogeneous
        (∑ _k : Fin 2, 1) :=
      MvPolynomial.IsHomogeneous.prod _ _ _ fun k _ => MvPolynomial.isHomogeneous_X _ _
    have := (MvPolynomial.isHomogeneous_C (Fin 2 × Fin 2) (M fun k => e (r k))).mul h1
    simpa using this
  · have hu : u = ∑ ic : Fin 2 × Fin 2, u ic.1 ic.2 • e ic := by
      ext p q
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e, Fintype.sum_prod_type]
      fin_cases p <;> fin_cases q <;> simp
    have hu' : (fun _ : Fin 2 => u) = fun _ => ∑ ic : Fin 2 × Fin 2, u ic.1 ic.2 • e ic := by
      rw [← hu]
    rw [hu', ContinuousMultilinearMap.map_sum
      (g := fun (_ : Fin 2) (ic : Fin 2 × Fin 2) => u ic.1 ic.2 • e ic)]
    simp only [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, map_sum, map_mul,
      MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring

/-- If the diagonal of a continuous bilinear map is invariant under simultaneous orthogonal
transformations, it is a combination of `|u|²`, `|v|²`, `u·v`. -/
theorem quadratic_form_of_invariant
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => PairVec) ℝ)
    (hinv : ∀ R : Matrix (Fin 2) (Fin 2) ℝ, R.transpose * R = 1 → ∀ u : PairVec,
      M (fun _ => fun p => R.mulVec (u p)) = M (fun _ => u)) :
    ∃ c : Fin 3 → ℝ, ∀ u : PairVec,
      M (fun _ => u) = ∑ k, c k * Weyl.quadraticTerms (u 0) (u 1) k := by
  obtain ⟨P, hP, hPM⟩ := exists_poly_of_multilinear_two M
  obtain ⟨c, hc⟩ := Weyl.quadratic_invariant P hP fun R hR u => by
    have h1 := hPM (fun p => R.mulVec (u p))
    have h2 := hPM u
    rw [← h1, ← h2]
    exact hinv R hR u
  exact ⟨c, fun u => by rw [hPM u, hc u]⟩

/-- The projection of a pair of planar vectors to its two coordinate vectors. -/
private def qexSend : PairVec →L[ℝ] PairW :=
  (ContinuousLinearMap.proj 0).prod (ContinuousLinearMap.proj 1)

private theorem qex_jet_invariant {F : PairW → ℝ} {U : Set PairW} (hU : IsOpen U)
    (h0 : (0 : PairW) ∈ U) (hcd : ContDiffOn ℝ (4 : ℕ) F U)
    (hinv : ∀ R : Matrix (Fin 2) (Fin 2) ℝ, R.transpose * R = 1 →
      ∀ᶠ w in 𝓝 (0 : PairW), F (matW R w) = F w) {k : ℕ} (hk : k ≤ 4)
    {R : Matrix (Fin 2) (Fin 2) ℝ} (hR : R.transpose * R = 1) (w : PairW) :
    iteratedFDeriv ℝ k F 0 (fun _ => matW R w) = iteratedFDeriv ℝ k F 0 (fun _ => w) := by
  have hev : F ∘ matW R =ᶠ[𝓝 (0 : PairW)] F := hinv R hR
  have h1 := (hev.iteratedFDeriv ℝ k).self_of_nhds
  have h2 := iteratedFDeriv_comp_clm_of_isOpen hU hcd (matW R) (x := 0)
    (by rw [map_zero]; exact h0) hk
  rw [h1] at h2
  have h3 := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin k => PairW) ℝ =>
    T (fun _ => w)) h2
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at h3
  rw [map_zero] at h3
  exact h3.symm

private theorem qex_odd {F : PairW → ℝ} {U : Set PairW} (hU : IsOpen U)
    (h0 : (0 : PairW) ∈ U) (hcd : ContDiffOn ℝ (4 : ℕ) F U)
    (hinv : ∀ R : Matrix (Fin 2) (Fin 2) ℝ, R.transpose * R = 1 →
      ∀ᶠ w in 𝓝 (0 : PairW), F (matW R w) = F w) {k : ℕ} (hk : k ≤ 4) (hodd : Odd k) (w : PairW) :
    iteratedFDeriv ℝ k F 0 (fun _ => w) = 0 := by
  have hR : ((-1 : Matrix (Fin 2) (Fin 2) ℝ)).transpose * (-1) = 1 := by simp
  have h := qex_jet_invariant hU h0 hcd hinv hk hR w
  have e : matW (-1) w = (-1 : ℝ) • w := by
    refine Prod.ext ?_ ?_ <;> simp [matW_apply, Matrix.neg_mulVec]
  rw [e] at h
  have h2 := (iteratedFDeriv ℝ k F 0).map_smul_univ (fun _ => (-1 : ℝ)) (fun _ => w)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hodd.neg_one_pow] at h2
  simp only [neg_smul, one_smul] at h2 h ⊢
  have : iteratedFDeriv ℝ k F 0 (fun _ => -w) = -iteratedFDeriv ℝ k F 0 (fun _ => w) := by
    simpa using h2
  rw [this] at h
  linarith

private theorem qex_hinv {F : PairW → ℝ} {U : Set PairW} (hU : IsOpen U)
    (h0 : (0 : PairW) ∈ U) (hcd : ContDiffOn ℝ (4 : ℕ) F U)
    (hinv : ∀ R : Matrix (Fin 2) (Fin 2) ℝ, R.transpose * R = 1 →
      ∀ᶠ w in 𝓝 (0 : PairW), F (matW R w) = F w) {k : ℕ} (hk : k ≤ 4)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : R.transpose * R = 1) (u : PairVec) :
    ((iteratedFDeriv ℝ k F 0).compContinuousLinearMap fun _ => qexSend)
        (fun _ => fun p => R.mulVec (u p)) =
      ((iteratedFDeriv ℝ k F 0).compContinuousLinearMap fun _ => qexSend) (fun _ => u) := by
  have h3 := qex_jet_invariant hU h0 hcd hinv hk hR (u 0, u 1)
  have e1 : qexSend (fun p => R.mulVec (u p)) = matW R (u 0, u 1) := rfl
  have e2 : qexSend u = (u 0, u 1) := rfl
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, e1, e2]
  exact h3

/-- **Taylor parts of an invariant analytic function** (`stepP:p8:q4-a`). An analytic function of
a pair of planar vectors that is invariant under simultaneous orthogonal transformations near `0`
equals `F(0) + W₂ + W₄ + O(‖w‖⁵)`, where `W₂ = A |w₁|² + A' |w₂|² + B w₁·w₂` is its quadratic Taylor
part and `W₄ = ∑ c_m (quarticMonomials w₁ w₂) m` its quartic Taylor part. -/
theorem taylor_parts_of_invariant (F : PairW → ℝ) (hF : AnalyticAt ℝ F 0)
    (hinv : ∀ R : Matrix (Fin 2) (Fin 2) ℝ, R.transpose * R = 1 →
      ∀ᶠ w in 𝓝 (0 : PairW), F (matW R w) = F w) :
    ∃ (A A' B : ℝ) (c : Fin 6 → ℝ),
      (∀ w : PairW, A * planeSq w.1 + A' * planeSq w.2 + B * planeDot w.1 w.2 =
        iteratedFDeriv ℝ 2 F 0 (fun _ => w) / 2) ∧
      (∀ w : PairW, ∑ k, c k * quarticMonomials w.1 w.2 k =
        iteratedFDeriv ℝ 4 F 0 (fun _ => w) / 24) ∧
      (fun w : PairW => F w - F 0 - (A * planeSq w.1 + A' * planeSq w.2 + B * planeDot w.1 w.2) -
        ∑ k, c k * quarticMonomials w.1 w.2 k) =O[𝓝 0] fun w => ‖w‖ ^ 5 := by
  obtain ⟨U, hUa, hU, h0⟩ := eventually_nhds_iff.1 hF.eventually_analyticAt
  have hcd : ContDiffOn ℝ (4 : ℕ) F U := (show AnalyticOnNhd ℝ F U from hUa).contDiffOn
    hU.uniqueDiffOn
  obtain ⟨c2, hc2⟩ := quadratic_form_of_invariant
    ((iteratedFDeriv ℝ 2 F 0).compContinuousLinearMap fun _ => qexSend)
    (qex_hinv hU h0 hcd hinv (by norm_num))
  obtain ⟨c4, hc4⟩ := quartic_form_of_invariant
    ((iteratedFDeriv ℝ 4 F 0).compContinuousLinearMap fun _ => qexSend)
    (qex_hinv hU h0 hcd hinv (by norm_num))
  have hq2 : ∀ w : PairW, iteratedFDeriv ℝ 2 F 0 (fun _ => w) =
      c2 0 * planeSq w.1 + c2 1 * planeSq w.2 + c2 2 * planeDot w.1 w.2 := fun w => by
    have := hc2 ![w.1, w.2]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at this
    simpa [qexSend, Fin.sum_univ_three, Weyl.quadraticTerms] using this
  have hq4 : ∀ w : PairW, iteratedFDeriv ℝ 4 F 0 (fun _ => w) =
      ∑ k, c4 k * quarticMonomials w.1 w.2 k := fun w => by
    have := hc4 ![w.1, w.2]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at this
    simpa [qexSend] using this
  refine ⟨c2 0 / 2, c2 1 / 2, c2 2 / 2, fun k => c4 k / 24, fun w => ?_, fun w => ?_, ?_⟩
  · rw [hq2 w]; ring
  · rw [hq4 w, Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  · obtain ⟨p, r, hr⟩ := hF
    have hp : HasFPowerSeriesAt F p 0 := ⟨r, hr⟩
    have hpk : ∀ (k : ℕ) (y : PairW), p k (fun _ => y) =
        iteratedFDeriv ℝ k F 0 (fun _ => y) / (k.factorial : ℝ) := fun k y => by
      have := hr.factorial_smul y k
      rw [← this, nsmul_eq_mul]
      field_simp
    refine (hp.isBigO_sub_partialSum_pow 5).congr_left (fun y => ?_)
    simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_range_zero,
      hpk, zero_add]
    have h0' : iteratedFDeriv ℝ 0 F 0 (fun _ => y) = F 0 := by
      simp [iteratedFDeriv_zero_apply]
    rw [h0', qex_odd hU h0 hcd hinv (k := 1) (by norm_num) (by decide) y,
      qex_odd hU h0 hcd hinv (k := 3) (by norm_num) (by decide) y, hq2 y, hq4 y]
    have e : ∑ k, c4 k / 24 * quarticMonomials y.1 y.2 k =
        (∑ k, c4 k * quarticMonomials y.1 y.2 k) / 24 := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    push_cast
    ring

end SecularForm
end KAM.Planetary
end
