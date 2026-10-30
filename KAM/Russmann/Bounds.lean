/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakMeasure.Basic
public import KAM.Planetary.Quantitative.Interface
public import KAM.Russmann.Frequency

/-!
# Track R: the derivative bounds `M`, `M₀`, `C₁` of `QuantitativeInput`

Track P's hypotheses `QuantitativeInput` ask for finite bounds on derivatives of `ω = ∇h` on the
compact real thickening `V = {y : ∃ x ∈ K, |y - x|₂ ≤ ϑ}` and on the complex Hessian on
`actionNbhd K (2ϑ)`. Only their existence matters for R-HEAD (whose `ε₀` is existential), so they
come from continuity on compact sets, with no Cauchy estimate:

* `exists_bound_iteratedFDeriv`: an analytic map has bounded derivatives of orders `≤ m` on every
  compact subset of its open domain;
* `abs_iteratedFDeriv_scalar_le`, `euclid_iteratedFDeriv_le`: the shapes of the bounds `M`
  (derivatives of `c · ω`) and `M₀` (derivatives of `ω`, Euclidean length) in terms of
  `‖D^j ω(y)‖`;
* `isCompact_euclidThick`, `euclidThick_subset_realNbhd`: the thickening `V` is compact and lies in
  the domain of analyticity of `ω`;
* `exists_hessian_bound`: the complex Hessian `D(∇_ℂ h)` is bounded on `actionNbhd K t`, `t < r₀`.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology

namespace KAM.Russmann

open KAM KAM.Planetary

variable {n : ℕ}

/-- Derivatives of orders `≤ m` of an analytic map are bounded on a compact subset of its open
domain. -/
theorem exists_bound_iteratedFDeriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {W V : Set E}
    (hV : IsCompact V) (hVW : V ⊆ W) {g : E → F} (hg : AnalyticOnNhd ℝ g W) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j ≤ m, ∀ y ∈ V, ‖iteratedFDeriv ℝ j g y‖ ≤ A := by
  have hb : ∀ j : ℕ, ∃ C : ℝ, ∀ y ∈ V, ‖iteratedFDeriv ℝ j g y‖ ≤ C := fun j =>
    hV.exists_bound_of_continuousOn ((hg.iteratedFDeriv j).continuousOn.mono hVW)
  choose C hC using hb
  refine ⟨∑ j ∈ Finset.range (m + 1), max (C j) 0, Finset.sum_nonneg fun j _ => le_max_right _ _,
    fun j hj y hy => (hC j y hy).trans ((le_max_left (C j) 0).trans ?_)⟩
  exact Finset.single_le_sum (f := fun j => max (C j) 0) (fun j _ => le_max_right _ _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

theorem prod_norm_le_one_of_euclid {j : ℕ} {v : Fin j → (Fin n → ℝ)}
    (hv : ∀ i, KAM.Nekhoroshev.euclid (v i) ≤ 1) : ∏ i, ‖v i‖ ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    fun i _ => (KAM.Nekhoroshev.norm_le_euclid (v i)).1.trans (hv i)

/-- The shape of the bound `M`: derivatives of the scalar family `c · ω` (`|c|₂ = 1`) applied to
vectors of Euclidean length `≤ 1` are at most `n ‖D^j ω(y)‖`. -/
theorem abs_iteratedFDeriv_scalar_le {ω : (Fin n → ℝ) → Fin n → ℝ} {y : Fin n → ℝ}
    (hω : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω y) {c : Fin n → ℝ}
    (hc : KAM.Nekhoroshev.euclid c = 1) (j : ℕ) {v : Fin j → (Fin n → ℝ)}
    (hv : ∀ i, KAM.Nekhoroshev.euclid (v i) ≤ 1) :
    |iteratedFDeriv ℝ j (p11c_scalar 1 ω c) y v| ≤ n * ‖iteratedFDeriv ℝ j ω y‖ := by
  set L : (Fin n → ℝ) →L[ℝ] ℝ := ∑ i, c i • ContinuousLinearMap.proj i with hL
  have hLapp : ∀ w : Fin n → ℝ, L w = ∑ i, c i * w i := fun w => by
    simp [hL]
  have e : p11c_scalar 1 ω c = L ∘ ω := by
    funext x; simp [p11c_scalar, hLapp]
  rw [e, L.iteratedFDeriv_comp_left hω (by exact_mod_cast le_top)]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  rw [hLapp]
  set w := iteratedFDeriv ℝ j ω y v
  have hw : ‖w‖ ≤ ‖iteratedFDeriv ℝ j ω y‖ :=
    ((iteratedFDeriv ℝ j ω y).le_opNorm v).trans
      (mul_le_of_le_one_right (norm_nonneg _) (prod_norm_le_one_of_euclid hv))
  have hci : ∀ i, |c i| ≤ 1 := fun i =>
    ((norm_le_pi_norm c i).trans (KAM.Nekhoroshev.norm_le_euclid c).1).trans hc.le
  calc |∑ i, c i * w i| ≤ ∑ i, |c i * w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖iteratedFDeriv ℝ j ω y‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact (mul_le_of_le_one_left (abs_nonneg _) (hci i)).trans
          ((norm_le_pi_norm w i).trans hw)
    _ = n * ‖iteratedFDeriv ℝ j ω y‖ := by simp

/-- The shape of the bound `M₀`: the Euclidean length of `D^j ω(y)(v, …, v)` for a Euclidean-unit
`v` is at most `√n ‖D^j ω(y)‖`. -/
theorem euclid_iteratedFDeriv_le {ω : (Fin n → ℝ) → Fin n → ℝ} (y : Fin n → ℝ) (j : ℕ)
    {v : Fin n → ℝ} (hv : KAM.Nekhoroshev.euclid v = 1) :
    KAM.Nekhoroshev.euclid (iteratedFDeriv ℝ j ω y (fun _ => v)) ≤
      Real.sqrt n * ‖iteratedFDeriv ℝ j ω y‖ := by
  refine (KAM.Nekhoroshev.norm_le_euclid _).2.1.trans ?_
  gcongr
  exact ((iteratedFDeriv ℝ j ω y).le_opNorm _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (prod_norm_le_one_of_euclid fun _ => hv.le))

/-- The closed Euclidean thickening of a compact set is compact. -/
theorem isCompact_euclidThick {K : Set (Fin n → ℝ)} (hK : IsCompact K) (t : ℝ) :
    IsCompact {y : Fin n → ℝ | ∃ x ∈ K, KAM.Nekhoroshev.euclid (y - x) ≤ t} := by
  have hball : IsCompact {v : Fin n → ℝ | KAM.Nekhoroshev.euclid v ≤ t} := by
    refine (isCompact_closedBall (0 : Fin n → ℝ) t).of_isClosed_subset
      (isClosed_le p11euclid_continuous continuous_const) fun v hv => ?_
    rw [mem_closedBall, dist_zero_right]
    exact (KAM.Nekhoroshev.norm_le_euclid v).1.trans hv
  have : {y : Fin n → ℝ | ∃ x ∈ K, KAM.Nekhoroshev.euclid (y - x) ≤ t} =
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 + p.2) ''
        (K ×ˢ {v | KAM.Nekhoroshev.euclid v ≤ t}) := by
    ext y
    constructor
    · rintro ⟨x, hx, hy⟩
      exact ⟨(x, y - x), ⟨hx, hy⟩, by simp⟩
    · rintro ⟨⟨x, v⟩, ⟨hx, hv⟩, rfl⟩
      exact ⟨x, hx, by simpa using hv⟩
  rw [this]
  exact (hK.prod hball).image (continuous_fst.add continuous_snd)

/-- The closed Euclidean `t`-thickening of `K ⊆ B` lies in the real `r`-neighbourhood of `B`
for `t < r`. -/
theorem euclidThick_subset_realNbhd {K B : Set (Fin n → ℝ)} (hKB : K ⊆ B) {t r : ℝ}
    (htr : t < r) :
    {y : Fin n → ℝ | ∃ x ∈ K, KAM.Nekhoroshev.euclid (y - x) ≤ t} ⊆ realNbhd B r := by
  rintro y ⟨x, hx, hy⟩
  exact ⟨x, hKB hx, by
    rw [dist_eq_norm]
    exact ((KAM.Nekhoroshev.norm_le_euclid _).1.trans hy).trans_lt htr⟩

/-- The complex Hessian `D(∇_ℂ h)` of a function holomorphic on `actionNbhd B r₀` is bounded on
`actionNbhd K t` for every compact `K ⊆ B` and `t < r₀`. -/
theorem exists_hessian_bound {B : Set (Fin n → ℝ)} {r₀ : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (actionNbhd B r₀)) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKB : K ⊆ B) {t : ℝ} (ht : t < r₀) :
    ∃ C : ℝ, ∀ y ∈ actionNbhd K t,
      ‖fderiv ℂ (fun x : Fin n → ℂ => fun i => fderiv ℂ h x (Pi.single i 1)) y‖ ≤ C := by
  set Kc : Set (Fin n → ℂ) := (fun p : (Fin n → ℝ) × (Fin n → ℂ) => realInclusion n p.1 + p.2) ''
    (K ×ˢ closedBall 0 t) with hKc
  have hKcc : IsCompact Kc :=
    (hK.prod (isCompact_closedBall _ _)).image
      (((realInclusion n).continuous.comp continuous_fst).add continuous_snd)
  have hsub : actionNbhd K t ⊆ Kc := by
    rintro y ⟨J, hJ, hy⟩
    refine ⟨(J, y - realInclusion n J), ⟨hJ, ?_⟩, by simp⟩
    rw [mem_closedBall, dist_zero_right]
    exact hy.le
  have hKcU : Kc ⊆ actionNbhd B r₀ := by
    rintro _ ⟨⟨J, w⟩, ⟨hJ, hw⟩, rfl⟩
    refine ⟨J, hKB hJ, ?_⟩
    rw [mem_closedBall, dist_zero_right] at hw
    show ‖realInclusion n J + w - (fun i => (J i : ℂ))‖ < r₀
    have : realInclusion n J + w - (fun i => (J i : ℂ)) = w := by
      rw [show (fun i => (J i : ℂ)) = realInclusion n J from rfl]
      abel
    rw [this]
    exact hw.trans_lt ht
  obtain ⟨C, hC⟩ := hKcc.exists_bound_of_continuousOn
    (((analyticOnNhd_gradC hh).fderiv).continuousOn.mono hKcU)
  exact ⟨C, fun y hy => hC y (hsub hy)⟩

end KAM.Russmann

end
