/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.LocalAnalytic.Eigenvalues
public import KAM.Planetary.SecularSpectrum.LocalAnalytic.Sorted

/-!
# Secular spectrum: local analytic spectral decomposition

Blueprint P, Part 9 (`bpP:p9:local-analytic`, `stepP:p9:la-ev`, `stepP:p9:la-adj`,
`stepP:p9:la-vec`, `stepP:p9:la-so`): near a point with simple spectrum an analytic symmetric
family has analytic ordered eigenvalues and an analytic `SO(n)` eigenframe.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Polynomial
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

lemma exists_signs {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (h0 : n = 0 → ε = 1) :
    ∃ e : Fin n → ℝ, (∀ i, e i = 1 ∨ e i = -1) ∧ ∏ i, e i = ε := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun _ => 1, fun _ => Or.inl rfl, by simp [h0 rfl]⟩
  · refine ⟨fun i => if i = ⟨0, hn⟩ then ε else 1, fun i => ?_, ?_⟩
    · show (if i = ⟨0, hn⟩ then ε else 1) = 1 ∨ (if i = ⟨0, hn⟩ then ε else 1) = -1
      split_ifs
      · exact hε
      · exact Or.inl rfl
    · simp [Finset.prod_ite_eq']

lemma isSO_mul_diagonal_signs {F : Mat n} (hF : F.transpose * F = 1) {e : Fin n → ℝ}
    (he : ∀ i, e i = 1 ∨ e i = -1) (hdet : F.det * ∏ i, e i = 1) :
    isSO (F * Matrix.diagonal e) := by
  have hee : Matrix.diagonal e * Matrix.diagonal e = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rcases he i with h | h <;> simp [h]
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc F.transpose, hF, Matrix.one_mul, hee]
  · rw [Matrix.det_mul, Matrix.det_diagonal, hdet]

lemma diagonal_signs_conj {e : Fin n → ℝ} (he : ∀ i, e i = 1 ∨ e i = -1) (σ : Vec n) :
    Matrix.diagonal e * Matrix.diagonal σ * Matrix.diagonal e = Matrix.diagonal σ := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rcases he i with h | h <;> simp [h]

/-- Generic local spectral theorem. Sorted branches avoid witness-choice ambiguity. -/
theorem local_analytic {d : ℕ} {W : Set (Vec d)} (hW : IsOpen W)
    {M : Vec d → Mat n} (hM : ∀ x ∈ W, (M x).IsHermitian)
    (hAn : AnalyticOnNhd ℝ M W) {x0 : Vec d} (hx0 : x0 ∈ W)
    (hSimple : Function.Injective ((hM x0 hx0).eigenvalues)) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x0 r ⊆ W ∧
    ∃ s : Vec d → Vec n, ∃ R : Vec d → Mat n,
      AnalyticOnNhd ℝ s (Metric.ball x0 r) ∧ AnalyticOnNhd ℝ R (Metric.ball x0 r) ∧
      ∀ x ∈ Metric.ball x0 r, isSO (R x) ∧ StrictMono (s x) ∧
        M x = R x * Matrix.diagonal (s x) * (R x).transpose := by
  have hsym : ∀ x ∈ W, (M x).transpose = M x := fun x hx => by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using (hM x hx).eq
  have hM0 := hM x0 hx0
  have hσ0s : StrictMono (sorted (M x0) hM0) := sorted_strictMono hM0 hSimple
  have hch0 := charpoly_eq_prod_sorted hM0
  choose s hsan hs0 hsev using
    fun j => exists_eigenvalue_branch (hAn x0 hx0) hσ0s.injective hch0 j
  set σ : Vec d → Vec n := fun x j => s j x with hσdef
  have hσ0eq : σ x0 = sorted (M x0) hM0 := funext hs0
  have hinj0 : Function.Injective (σ x0) := by rw [hσ0eq]; exact hσ0s.injective
  choose k hk using
    fun j => exists_eigProj_diag_pos hσ0s.injective hch0 (hsym x0 hx0) j
  have hcont : ∀ j, ContinuousAt (fun x => eigProj (M x) (σ x) j (k j) (k j)) x0 := fun j =>
    (analyticAt_mat_entry (analyticAt_eigProj (hAn x0 hx0) (fun i => hsan i) hinj0 j)
      (k j) (k j)).continuousAt
  have e1 : ∀ᶠ x in 𝓝 x0, x ∈ W := hW.mem_nhds hx0
  have e2 : ∀ᶠ x in 𝓝 x0, ∀ j, AnalyticAt ℝ (s j) x :=
    Filter.eventually_all.2 fun j => (hsan j).eventually_analyticAt
  have e3 : ∀ᶠ x in 𝓝 x0, ∀ j, (M x).charpoly.eval (σ x j) = 0 := Filter.eventually_all.2 hsev
  have e4 : ∀ᶠ x in 𝓝 x0, StrictMono (σ x) := by
    have : ∀ᶠ x in 𝓝 x0, ∀ i j, i < j → s i x < s j x :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => by
        by_cases hij : i < j
        · refine ((hsan i).continuousAt.eventually_lt (hsan j).continuousAt ?_).mono
            fun x hx _ => hx
          rw [hs0, hs0]; exact hσ0s hij
        · exact Filter.Eventually.of_forall fun x h => absurd h hij
    exact this.mono fun x hx i j hij => hx i j hij
  have e5 : ∀ᶠ x in 𝓝 x0, ∀ j, 0 < eigProj (M x) (σ x) j (k j) (k j) :=
    Filter.eventually_all.2 fun j =>
      (continuousAt_const.eventually_lt (hcont j) (by rw [hσ0eq]; exact hk j)).mono fun x hx => hx
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (e1.and (e2.and (e3.and (e4.and e5))))
  have hb : ∀ x ∈ Metric.ball x0 r, x ∈ W ∧ (∀ j, AnalyticAt ℝ (s j) x) ∧
      (∀ j, (M x).charpoly.eval (σ x j) = 0) ∧ StrictMono (σ x) ∧
      ∀ j, 0 < eigProj (M x) (σ x) j (k j) (k j) := hball
  have hchx : ∀ x ∈ Metric.ball x0 r, (M x).charpoly = ∏ j, (X - C (σ x j)) := fun x hx =>
    charpoly_eq_prod_of_roots (M x) (hb x hx).2.2.2.1.injective (hb x hx).2.2.1
  set F : Vec d → Mat n := fun x => eigFrame (M x) (σ x) k with hFdef
  have hFt : ∀ x ∈ Metric.ball x0 r, (F x).transpose * F x = 1 := fun x hx =>
    eigFrame_transpose_mul (hsym x (hb x hx).1) (hb x hx).2.2.2.1.injective (hchx x hx)
      (hb x hx).2.2.2.2
  have hFan : ∀ x ∈ Metric.ball x0 r, AnalyticAt ℝ F x := fun x hx =>
    analyticAt_eigFrame (hAn x (hb x hx).1) (fun i => (hb x hx).2.1 i)
      (hb x hx).2.2.2.1.injective (hb x hx).2.2.2.2
  have hdetsq : ∀ x ∈ Metric.ball x0 r, (F x).det ^ 2 = 1 := fun x hx => by
    have := congrArg Matrix.det (hFt x hx)
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← sq] at this
  have hdetc : ContinuousOn (fun x => (F x).det) (Metric.ball x0 r) := fun x hx =>
    (analyticAt_det (hFan x hx)).continuousAt.continuousWithinAt
  have hsign := (convex_ball x0 r).isPreconnected.eq_one_or_eq_neg_one_of_sq_eq hdetc
    (fun x hx => by simp only [Pi.pow_apply, Pi.one_apply]; exact hdetsq x hx)
  have hx0b : x0 ∈ Metric.ball x0 r := Metric.mem_ball_self hr
  have hε : (F x0).det = 1 ∨ (F x0).det = -1 := by
    rcases hsign with h | h
    · exact Or.inl (by simpa using h hx0b)
    · exact Or.inr (by simpa using h hx0b)
  have hconst : ∀ x ∈ Metric.ball x0 r, (F x).det = (F x0).det := fun x hx => by
    rcases hsign with h | h
    · rw [show (F x).det = 1 by simpa using h hx, show (F x0).det = 1 by simpa using h hx0b]
    · rw [show (F x).det = -1 by simpa using h hx, show (F x0).det = -1 by simpa using h hx0b]
  obtain ⟨e, he, hprod⟩ := exists_signs (ε := (F x0).det) hε (fun (hn0 : n = 0) => by
    have : IsEmpty (Fin n) := by rw [hn0]; infer_instance
    exact Matrix.det_isEmpty)
  refine ⟨r, hr, fun x hx => (hb x hx).1, σ, fun x => F x * Matrix.diagonal e, ?_, ?_, ?_⟩
  · exact fun x hx => analyticAt_pi_iff.2 fun j => (hb x hx).2.1 j
  · exact fun x hx => analyticAt_mat_mul (hFan x hx) analyticAt_const
  · intro x hx
    refine ⟨isSO_mul_diagonal_signs (hFt x hx) he ?_, (hb x hx).2.2.2.1, ?_⟩
    · rw [hprod, hconst x hx, ← sq]; exact hdetsq x0 hx0b
    · have hdiag := eigFrame_diagonalises (hsym x (hb x hx).1) (hb x hx).2.2.2.1.injective
        (hchx x hx) (hb x hx).2.2.2.2
      rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
      calc M x = F x * Matrix.diagonal (σ x) * (F x).transpose := hdiag
        _ = F x * (Matrix.diagonal e * Matrix.diagonal (σ x) * Matrix.diagonal e) *
              (F x).transpose := by rw [diagonal_signs_conj he]
        _ = _ := by simp only [Matrix.mul_assoc]