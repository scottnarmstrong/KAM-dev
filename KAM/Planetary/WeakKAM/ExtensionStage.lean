/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.ExtensionNorm
public import KAM.Planetary.MaximalStep.Parameter
public import KAM.Planetary.PGAssembly.JetsPolar
public import KAM.Strip.AnalyticTaylor

/-! # P11B finite extension: one cut-off increment

The real trace of a complex increment `Δω` on a collar `E + t` is smooth on the real collar, and its
iterated derivatives at real points within `t / 2` of `E` are bounded by the parameter Cauchy
estimate (`fe-cauchy`). Multiplying by a cutoff `χ` supported in that region gives a globally smooth
function whose derivatives obey the Leibniz bound (`fe-leib`), in operator norms for the max norms.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

/-- The real trace of a complex increment. -/
def selectionIncrement (Δ : SelectionC n → SelectionC n) (y : SelectionR n) : SelectionR n :=
  selectionRe (Δ (selectionReal y))

/-- The real points of the complex collar `E + t`. -/
def selectionRealCollar (E : Set (SelectionR n)) (t : ℝ) : Set (SelectionR n) :=
  {y | selectionReal y ∈ actionNbhd E t}

theorem isOpen_selectionRealCollar (E : Set (SelectionR n)) (t : ℝ) :
    IsOpen (selectionRealCollar E t) :=
  (p11_isOpen_actionNbhd E t).preimage (selectionRealLI n).continuous

theorem selectionIteratedFDeriv_congr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : SelectionR n → F} {x : SelectionR n} (h : f =ᶠ[𝓝 x] g) (k : ℕ) :
    iteratedFDeriv ℝ k f x = iteratedFDeriv ℝ k g x := by
  have := Filter.EventuallyEq.iteratedFDerivWithin_eq (𝕜 := ℝ) (s := univ) (n := k)
    (by rwa [nhdsWithin_univ]) h.self_of_nhds
  simpa [iteratedFDerivWithin_univ] using this

theorem mem_selectionRealCollar_of_infDist {E : Set (SelectionR n)} (hE : IsCompact E)
    (hne : E.Nonempty) {s r : ℝ} (hsr : s < r) {y : SelectionR n}
    (hy : Metric.infDist y E ≤ s) : y ∈ selectionRealCollar E r := by
  obtain ⟨J, hJ, hd⟩ := hE.exists_infDist_eq_dist hne y
  refine ⟨J, hJ, ?_⟩
  have : (selectionReal y - fun i => (J i : ℂ)) = selectionReal (y - J) := by
    funext i; simp [selectionReal]
  rw [this, norm_selectionReal, ← dist_eq_norm, ← hd]
  exact lt_of_le_of_lt hy hsr

theorem selectionIncrement_contDiffOn {E : Set (SelectionR n)} {Δ : SelectionC n → SelectionC n}
    (hΔ : DifferentiableOn ℂ Δ (actionNbhd E t)) (m : ℕ) :
    ContDiffOn ℝ m (selectionIncrement Δ) (selectionRealCollar E t) := by
  have hA : AnalyticOnNhd ℂ Δ (actionNbhd E t) :=
    analyticOnNhd_of_differentiableOn (p11_isOpen_actionNbhd E t) hΔ
  have hC : ContDiffOn ℝ m Δ (actionNbhd E t) :=
    hA.restrictScalars.contDiffOn_of_completeSpace
  have hcomp : ContDiffOn ℝ m (fun y => Δ (selectionReal y)) (selectionRealCollar E t) :=
    hC.comp (selectionRealLI n).toContinuousLinearMap.contDiff.contDiffOn fun y hy => hy
  refine contDiffOn_pi.2 fun i => ?_
  exact Complex.reCLM.contDiff.comp_contDiffOn
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).contDiff.comp_contDiffOn
      hcomp)

theorem selectionIncrement_norm_iteratedFDeriv_le {E : Set (SelectionR n)} (hE : IsCompact E)
    (hne : E.Nonempty) (ht : 0 < t) {Δ : SelectionC n → SelectionC n} {ℓ : ℝ}
    (hΔ : DifferentiableOn ℂ Δ (actionNbhd E t))
    (hreal : ∀ b : SelectionR n, selectionReal b ∈ actionNbhd E t →
      Δ (selectionReal b) = selectionReal (selectionRe (Δ (selectionReal b))))
    (hbd : ∀ b ∈ actionNbhd E t, ‖Δ b‖ ≤ ℓ) (u : ℕ) {y : SelectionR n}
    (hy : Metric.infDist y E ≤ t / 2) :
    ‖iteratedFDeriv ℝ u (selectionIncrement Δ) y‖ ≤ (u : ℝ) ^ u * ℓ / (t / 4) ^ u := by
  have hyt : y ∈ selectionRealCollar E t :=
    mem_selectionRealCollar_of_infDist hE hne (by linarith) hy
  have hy3 : selectionReal y ∈ actionNbhd E (3 * t / 4) :=
    mem_selectionRealCollar_of_infDist hE hne (by linarith) hy
  have hℓ : 0 ≤ ℓ := (norm_nonneg _).trans (hbd _ hyt)
  have hreal' : (selectionRealLI n) ∘ selectionIncrement Δ =ᶠ[𝓝 y]
      fun y => Δ (selectionReal y) := by
    filter_upwards [(isOpen_selectionRealCollar E t).mem_nhds hyt] with z hz
    exact (hreal z hz).symm
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · rw [norm_iteratedFDeriv_zero]
    simp only [selectionIncrement, pow_zero, Nat.cast_zero, one_mul, div_one]
    calc ‖selectionRe (Δ (selectionReal y))‖ ≤ ‖Δ (selectionReal y)‖ := by
          refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
          exact (Complex.abs_re_le_norm _).trans (norm_le_pi_norm _ i)
      _ ≤ ℓ := hbd _ hyt
  · have hg : ContDiffAt ℝ u (selectionIncrement Δ) y :=
      (selectionIncrement_contDiffOn hΔ u).contDiffAt
        ((isOpen_selectionRealCollar E t).mem_nhds hyt)
    set L := (selectionRealLI n).toContinuousLinearMap with hL
    have hLy : L y ∈ actionNbhd E t := hyt
    have hAC : AnalyticOnNhd ℂ Δ (actionNbhd E t) :=
      analyticOnNhd_of_differentiableOn (p11_isOpen_actionNbhd E t) hΔ
    have hCR : ContDiffOn ℝ u Δ (actionNbhd E t) :=
      hAC.restrictScalars.contDiffOn_of_completeSpace
    have h1 : ‖iteratedFDeriv ℝ u (selectionIncrement Δ) y‖ =
        ‖iteratedFDeriv ℝ u ((selectionRealLI n) ∘ selectionIncrement Δ) y‖ :=
      ((selectionRealLI n).norm_iteratedFDeriv_comp_left hg le_rfl).symm
    have h2 : iteratedFDeriv ℝ u ((selectionRealLI n) ∘ selectionIncrement Δ) y =
        iteratedFDeriv ℝ u (Δ ∘ L) y := selectionIteratedFDeriv_congr hreal' u
    have h3 := iteratedFDeriv_comp_clm_of_isOpen (p11_isOpen_actionNbhd E t) hCR L hLy
      (i := u) le_rfl
    have h4 : iteratedFDeriv ℝ u Δ (L y) =
        (iteratedFDeriv ℂ u Δ (L y)).restrictScalars ℝ := by
      have := (hAC (L y) hLy).contDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ) (n := u)
      simpa using this.symm
    have h5 : ‖iteratedFDeriv ℝ u (Δ ∘ L) y‖ ≤ ‖iteratedFDeriv ℂ u Δ (L y)‖ := by
      rw [h3, h4]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      have hprod : ∏ _i : Fin u, ‖L‖ ≤ 1 :=
        Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => norm_selectionRealLI_clm_le n
      calc _ ≤ ‖(iteratedFDeriv ℂ u Δ (L y)).restrictScalars ℝ‖ * 1 :=
            mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
        _ = _ := by rw [mul_one, ContinuousMultilinearMap.norm_restrictScalars]
    have h6 := param_cauchy (E := E) (q := n) (M := ℓ) (by linarith : 0 < 3 * t / 4)
      (by linarith : 3 * t / 4 < t) hℓ hΔ hbd hu (L y) hy3
    have h7 : t - 3 * t / 4 = t / 4 := by ring
    rw [h7] at h6
    rw [h1, h2]
    exact h5.trans h6

end KAM.Planetary
