/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.HoloSlab
public import HD11964.CoverPlan

/-!
# HD 11964: the fully complexified perturbation — analyticity and periodicity (HD11964-HOLO)

* `CVar`, `qpCC`, `distSqCC`, `pertCC`: LP's chart and `P_C = μ((p_c + p_b)·(p_c + p_b)/2 −
  ν_c ν_b (d²)^{−1/2})` at complex angles `θ` (`λ = 2πθ`) **and** complex slow variables
  `(Λ, ξ, η)`; `realVar w θ` is the real state `w` with complex angles, `chartPertC y w θ =
  pertCC y (realVar w θ)`.
* `PlanetOk`, `ChartOkAt`: the chart conditions at a point (all strict): `Λ ≠ 0`, the radicand in
  the slit plane, `1 + k ≠ 0`, the Kepler invariance and contraction.
* `keplerSol_analyticAt`: the strip solution of Kepler's equation is analytic at every point where
  the invariance and contraction hold strictly (generic coefficients).
* `pertCC_analyticAt` (1c-i): `P_C` is analytic at every point with `ChartOkAt` and `Re d² > 0`
  (the form DESIGN A's hypotheses `hR` consume: analyticity at each point of a compact set gives
  it on a neighbourhood).
* `pertCC_add_single` (1c-ii): `P_C` is `1`-periodic in each angle.
-/

@[expose] public noncomputable section

open Set Filter KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Application.LambdaDrift
open scoped Real Topology

namespace HD11964.Cover

/-! ### Definitions -/

/-- The complex chart variables `x = (θ, Λ, ξ, η)` (`λ = 2πθ`, planet `c` = index `0`). -/
abbrev CVar : Type := (Fin 2 → ℂ) × (Fin 2 → ℂ) × (Fin 2 → ℂ) × (Fin 2 → ℂ)

/-- Planet `j`'s complexified chart at the complex point `x`. -/
def qpCC (y : Fin 2 → ℝ) (x : CVar) (j : Fin 2) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  planetChartC (y j) (nu j) (2 * π * x.1 j) (x.2.1 j) (x.2.2.1 j) (x.2.2.2 j)

/-- The complexified mutual distance squared at `x` (bilinear). -/
def distSqCC (y : Fin 2 → ℝ) (x : CVar) : ℂ :=
  ((qpCC y x 0).1 0 - (qpCC y x 1).1 0) ^ 2 + ((qpCC y x 0).1 1 - (qpCC y x 1).1 1) ^ 2

/-- **The fully complexified perturbation** `P_C(θ, Λ, ξ, η)`. -/
def pertCC (y : Fin 2 → ℝ) (x : CVar) : ℂ :=
  (mu : ℂ) * ((((qpCC y x 0).2 0 + (qpCC y x 1).2 0) ^ 2 +
    ((qpCC y x 0).2 1 + (qpCC y x 1).2 1) ^ 2) / 2 -
    (nu 0 : ℂ) * (nu 1 : ℂ) * distSqCC y x ^ (-(1 / 2 : ℂ)))

/-- The real chart state `w` with complex angles `θ`. -/
def realVar (w : Phase (2 + 2)) (θ : Fin 2 → ℂ) : CVar :=
  (θ, fun j => (fast w.2 j : ℂ), fun j => (slow w.1 j : ℂ), fun j => (slow w.2 j : ℂ))

theorem chartPertC_eq_pertCC (y : Fin 2 → ℝ) (w : Phase (2 + 2)) (θ : Fin 2 → ℂ) :
    chartPertC y w θ = pertCC y (realVar w θ) := rfl

theorem distSqC_eq_distSqCC (y : Fin 2 → ℝ) (w : Phase (2 + 2)) (θ : Fin 2 → ℂ) :
    distSqC y w θ = distSqCC y (realVar w θ) := rfl

/-- The radicand `(1 - Γ/(2Λ))/Λ`. -/
def radC (Λ ξ η : ℂ) : ℂ := (1 - (ξ ^ 2 + η ^ 2) / 2 / (2 * Λ)) / Λ

/-- The eccentricity vector `v = radC^{1/2} (ξ, η)` (principal branch). -/
def eccC (Λ ξ η : ℂ) : Fin 2 → ℂ := radC Λ ξ η ^ (1 / 2 : ℂ) • ![ξ, η]

/-- `k = 1 - Γ/Λ`. -/
def kC (Λ ξ η : ℂ) : ℂ := 1 - (ξ ^ 2 + η ^ 2) / 2 / Λ

/-- The eccentric longitude on the Kepler strip `y₀`. -/
def eccLongC (y₀ : ℝ) (lam Λ ξ η : ℂ) : ℂ :=
  KAM.Kepler.keplerSol y₀ (eccC Λ ξ η 0) (eccC Λ ξ η 1) lam

/-- `v·c`, `c = (cos F, sin F)`. -/
def vcC (y₀ : ℝ) (lam Λ ξ η : ℂ) : ℂ :=
  eccC Λ ξ η 0 * Complex.cos (eccLongC y₀ lam Λ ξ η) +
    eccC Λ ξ η 1 * Complex.sin (eccLongC y₀ lam Λ ξ η)

/-- `planetChartC` in terms of the named pieces. -/
theorem planetChartC_eq (y₀ m : ℝ) (lam Λ ξ η : ℂ) :
    planetChartC y₀ m lam Λ ξ η =
      ((Λ ^ 2 / ((m ^ 2 : ℝ) : ℂ)) • (kC Λ ξ η • ![Complex.cos (eccLongC y₀ lam Λ ξ η),
          Complex.sin (eccLongC y₀ lam Λ ξ η)] - eccC Λ ξ η +
          (vcC y₀ lam Λ ξ η / (1 + kC Λ ξ η)) • eccC Λ ξ η),
        (((m ^ 2 : ℝ) : ℂ) / (Λ * (1 - vcC y₀ lam Λ ξ η))) •
          (![-Complex.sin (eccLongC y₀ lam Λ ξ η), Complex.cos (eccLongC y₀ lam Λ ξ η)] -
            (vcC y₀ lam Λ ξ η / (1 + kC Λ ξ η)) • ![-eccC Λ ξ η 1, eccC Λ ξ η 0])) := rfl

/-- **One planet's chart conditions at a complex point** (all strict, hence open). -/
structure PlanetOk (y₀ : ℝ) (lam Λ ξ η : ℂ) : Prop where
  ne_zero : Λ ≠ 0
  rad_mem : radC Λ ξ η ∈ Complex.slitPlane
  one_add_k : 1 + kC Λ ξ η ≠ 0
  y_pos : 0 < y₀
  invariant : |lam.im| + (|(eccC Λ ξ η 0).re| + |(eccC Λ ξ η 1).re|) * Real.sinh y₀ +
      (|(eccC Λ ξ η 0).im| + |(eccC Λ ξ η 1).im|) * Real.cosh y₀ < y₀
  contraction : (‖eccC Λ ξ η 0‖ + ‖eccC Λ ξ η 1‖) * Real.cosh y₀ < 1

/-- Both planets' chart conditions at `x`. -/
def ChartOkAt (y : Fin 2 → ℝ) (x : CVar) : Prop :=
  ∀ j, PlanetOk (y j) (2 * π * x.1 j) (x.2.1 j) (x.2.2.1 j) (x.2.2.2 j)

/-! ### The Kepler solution at a point -/

/-- **The strip solution is analytic at a point** where the invariance and contraction hold
strictly (the coefficients analytic there). -/
theorem keplerSol_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {a b c : E → ℂ} {y₀ : ℝ} {x₀ : E} (ha : AnalyticAt ℂ a x₀)
    (hb : AnalyticAt ℂ b x₀) (hc : AnalyticAt ℂ c x₀) (hy : 0 < y₀)
    (hinv : |(c x₀).im| + (|(a x₀).re| + |(b x₀).re|) * Real.sinh y₀ +
      (|(a x₀).im| + |(b x₀).im|) * Real.cosh y₀ < y₀)
    (hcon : (‖a x₀‖ + ‖b x₀‖) * Real.cosh y₀ < 1) :
    AnalyticAt ℂ (fun x => KAM.Kepler.keplerSol y₀ (a x) (b x) (c x)) x₀ := by
  set κ := ((‖a x₀‖ + ‖b x₀‖) * Real.cosh y₀ + 1) / 2 with hκ
  have hκ1 : κ < 1 := by rw [hκ]; linarith
  have hlt : (‖a x₀‖ + ‖b x₀‖) * Real.cosh y₀ < κ := by rw [hκ]; linarith
  have hac := ha.continuousAt
  have hbc := hb.continuousAt
  have hcc := hc.continuousAt
  have hI : ContinuousAt (fun x => |(c x).im| + (|(a x).re| + |(b x).re|) * Real.sinh y₀ +
      (|(a x).im| + |(b x).im|) * Real.cosh y₀) x₀ := by fun_prop
  have hC : ContinuousAt (fun x => (‖a x‖ + ‖b x‖) * Real.cosh y₀) x₀ := by fun_prop
  have hev : ∀ᶠ x in 𝓝 x₀, AnalyticAt ℂ a x ∧ AnalyticAt ℂ b x ∧ AnalyticAt ℂ c x ∧
      |(c x).im| + (|(a x).re| + |(b x).re|) * Real.sinh y₀ +
        (|(a x).im| + |(b x).im|) * Real.cosh y₀ < y₀ ∧
      (‖a x‖ + ‖b x‖) * Real.cosh y₀ < κ :=
    ha.eventually_analyticAt.and (hb.eventually_analyticAt.and (hc.eventually_analyticAt.and
      ((hI.eventually (gt_mem_nhds hinv)).and (hC.eventually (gt_mem_nhds hlt)))))
  obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.1 hev
  have hK : KAM.Kepler.KeplerData U a b c y₀ κ :=
    ⟨hUo, fun x hx => (hU x hx).1, fun x hx => (hU x hx).2.1, fun x hx => (hU x hx).2.2.1, hy,
      hκ1, fun x hx => (hU x hx).2.2.2.1, fun x hx => (hU x hx).2.2.2.2.le⟩
  exact KAM.Kepler.keplerSol_analyticOnNhd hK x₀ hxU

/-- The solution at a point with the chart conditions: in the strip, it solves the equation, and
it is the unique such. -/
theorem eccLongC_spec {y₀ : ℝ} {lam Λ ξ η : ℂ} (h : PlanetOk y₀ lam Λ ξ η) :
    |(eccLongC y₀ lam Λ ξ η).im| ≤ y₀ ∧
      KAM.Kepler.keplerOp (eccC Λ ξ η 0) (eccC Λ ξ η 1) (eccLongC y₀ lam Λ ξ η) = lam ∧
      ∀ G : ℂ, |G.im| ≤ y₀ → KAM.Kepler.keplerOp (eccC Λ ξ η 0) (eccC Λ ξ η 1) G = lam →
        G = eccLongC y₀ lam Λ ξ η :=
  KAM.Kepler.EqC.keplerSol_props (KAM.Kepler.EqC.existsUnique_keplerOp h.y_pos
    (by linarith [h.contraction] : (‖eccC Λ ξ η 0‖ + ‖eccC Λ ξ η 1‖) * Real.cosh y₀ / 2 + 1 / 2 < 1)
    h.invariant (by linarith [h.contraction]))

/-- `|v·c| < 1`, hence `1 - v·c ≠ 0`. -/
theorem one_sub_vcC_ne_zero {y₀ : ℝ} {lam Λ ξ η : ℂ} (h : PlanetOk y₀ lam Λ ξ η) :
    1 - vcC y₀ lam Λ ξ η ≠ 0 := by
  have hs := (eccLongC_spec h).1
  have hc := KAM.Kepler.EqC.norm_cos_le hs
  have hsn := KAM.Kepler.EqC.norm_sin_le hs
  have hb : ‖vcC y₀ lam Λ ξ η‖ < 1 := by
    unfold vcC
    calc ‖eccC Λ ξ η 0 * Complex.cos (eccLongC y₀ lam Λ ξ η) +
          eccC Λ ξ η 1 * Complex.sin (eccLongC y₀ lam Λ ξ η)‖
        ≤ ‖eccC Λ ξ η 0‖ * Real.cosh y₀ + ‖eccC Λ ξ η 1‖ * Real.cosh y₀ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul] <;>
            exact mul_le_mul_of_nonneg_left (by assumption) (norm_nonneg _)
      _ < 1 := by linarith [h.contraction]
  intro h0
  have : vcC y₀ lam Λ ξ η = 1 := by linear_combination -h0
  rw [this, norm_one] at hb
  exact lt_irrefl _ hb

/-! ### (1c-i) Analyticity at a point -/

theorem analyticAt_vec2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ}
    {x₀ : E} (hf : AnalyticAt ℂ f x₀) (hg : AnalyticAt ℂ g x₀) :
    AnalyticAt ℂ (fun x => ![f x, g x]) x₀ := by
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · simpa using hf
  · simpa using hg

/-- **One planet's chart is analytic at a point with the chart conditions**, for analytic inputs. -/
theorem planetChartC_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {y₀ m : ℝ} {lam Λ ξ η : E → ℂ} {x₀ : E} (hlam : AnalyticAt ℂ lam x₀)
    (hΛ : AnalyticAt ℂ Λ x₀) (hξ : AnalyticAt ℂ ξ x₀) (hη : AnalyticAt ℂ η x₀)
    (h : PlanetOk y₀ (lam x₀) (Λ x₀) (ξ x₀) (η x₀)) :
    AnalyticAt ℂ (fun x => planetChartC y₀ m (lam x) (Λ x) (ξ x) (η x)) x₀ := by
  have hΛ0 := h.ne_zero
  have hslit := h.rad_mem
  have hR : AnalyticAt ℂ (fun x => radC (Λ x) (ξ x) (η x)) x₀ := by
    unfold radC; fun_prop (disch := simp [hΛ0])
  have hv0 : AnalyticAt ℂ (fun x => eccC (Λ x) (ξ x) (η x) 0) x₀ := by
    simp only [eccC, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
    fun_prop (disch := assumption)
  have hv1 : AnalyticAt ℂ (fun x => eccC (Λ x) (ξ x) (η x) 1) x₀ := by
    simp only [eccC, Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
      smul_eq_mul]
    fun_prop (disch := assumption)
  have hv : AnalyticAt ℂ (fun x => eccC (Λ x) (ξ x) (η x)) x₀ := by
    have := analyticAt_vec2 hv0 hv1
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    funext i; fin_cases i <;> rfl
  have hF : AnalyticAt ℂ (fun x => eccLongC y₀ (lam x) (Λ x) (ξ x) (η x)) x₀ :=
    keplerSol_analyticAt hv0 hv1 hlam h.y_pos h.invariant h.contraction
  have hcos : AnalyticAt ℂ (fun x => Complex.cos (eccLongC y₀ (lam x) (Λ x) (ξ x) (η x))) x₀ :=
    Complex.analyticAt_cos.comp hF
  have hsin : AnalyticAt ℂ (fun x => Complex.sin (eccLongC y₀ (lam x) (Λ x) (ξ x) (η x))) x₀ :=
    Complex.analyticAt_sin.comp hF
  have hk : AnalyticAt ℂ (fun x => kC (Λ x) (ξ x) (η x)) x₀ := by
    unfold kC; fun_prop (disch := simp [hΛ0])
  have hvc : AnalyticAt ℂ (fun x => vcC y₀ (lam x) (Λ x) (ξ x) (η x)) x₀ := by
    unfold vcC; fun_prop
  have h1k := h.one_add_k
  have hf : AnalyticAt ℂ (fun x => vcC y₀ (lam x) (Λ x) (ξ x) (η x) /
      (1 + kC (Λ x) (ξ x) (η x))) x₀ := by fun_prop (disch := assumption)
  have hcs := analyticAt_vec2 hcos hsin
  have hsc := analyticAt_vec2 (by fun_prop : AnalyticAt ℂ (fun x =>
    -Complex.sin (eccLongC y₀ (lam x) (Λ x) (ξ x) (η x))) x₀) hcos
  have hvv := analyticAt_vec2 (by fun_prop : AnalyticAt ℂ (fun x =>
    -eccC (Λ x) (ξ x) (η x) 1) x₀) hv0
  have hm : (((m ^ 2 : ℝ) : ℂ)) = (((m ^ 2 : ℝ) : ℂ)) := rfl
  have hq : AnalyticAt ℂ (fun x => (Λ x ^ 2 / ((m ^ 2 : ℝ) : ℂ)) •
      (kC (Λ x) (ξ x) (η x) • ![Complex.cos (eccLongC y₀ (lam x) (Λ x) (ξ x) (η x)),
        Complex.sin (eccLongC y₀ (lam x) (Λ x) (ξ x) (η x))] - eccC (Λ x) (ξ x) (η x) +
        (vcC y₀ (lam x) (Λ x) (ξ x) (η x) / (1 + kC (Λ x) (ξ x) (η x))) •
          eccC (Λ x) (ξ x) (η x))) x₀ := by
    have hl : AnalyticAt ℂ (fun x => Λ x ^ 2 / ((m ^ 2 : ℝ) : ℂ)) x₀ := by
      simp only [div_eq_mul_inv]; fun_prop
    exact hl.smul (((hk.smul hcs).sub hv).add (hf.smul hv))
  have hden : Λ x₀ * (1 - vcC y₀ (lam x₀) (Λ x₀) (ξ x₀) (η x₀)) ≠ 0 :=
    mul_ne_zero hΛ0 (one_sub_vcC_ne_zero h)
  have hp : AnalyticAt ℂ (fun x => (((m ^ 2 : ℝ) : ℂ) /
      (Λ x * (1 - vcC y₀ (lam x) (Λ x) (ξ x) (η x)))) •
      (![-Complex.sin (eccLongC y₀ (lam x) (Λ x) (ξ x) (η x)),
          Complex.cos (eccLongC y₀ (lam x) (Λ x) (ξ x) (η x))] -
        (vcC y₀ (lam x) (Λ x) (ξ x) (η x) / (1 + kC (Λ x) (ξ x) (η x))) •
          ![-eccC (Λ x) (ξ x) (η x) 1, eccC (Λ x) (ξ x) (η x) 0])) x₀ := by
    have hs : AnalyticAt ℂ (fun x => ((m ^ 2 : ℝ) : ℂ) /
        (Λ x * (1 - vcC y₀ (lam x) (Λ x) (ξ x) (η x)))) x₀ := by
      fun_prop (disch := assumption)
    exact hs.smul (hsc.sub (hf.smul hvv))
  simp only [planetChartC_eq]
  exact hq.prod hp

theorem analyticAt_proj_fst (j : Fin 2) {x : CVar} : AnalyticAt ℂ (fun x : CVar => x.1 j) x :=
  (analyticAt_pi_iff.1 analyticAt_fst) j

theorem analyticAt_proj_Λ (j : Fin 2) {x : CVar} : AnalyticAt ℂ (fun x : CVar => x.2.1 j) x :=
  (analyticAt_pi_iff.1 (analyticAt_fst.comp analyticAt_snd)) j

theorem analyticAt_proj_ξ (j : Fin 2) {x : CVar} : AnalyticAt ℂ (fun x : CVar => x.2.2.1 j) x :=
  (analyticAt_pi_iff.1 (analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd))) j

theorem analyticAt_proj_η (j : Fin 2) {x : CVar} : AnalyticAt ℂ (fun x : CVar => x.2.2.2 j) x :=
  (analyticAt_pi_iff.1 (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd))) j

theorem qpCC_analyticAt {y : Fin 2 → ℝ} {x₀ : CVar} (h : ChartOkAt y x₀) (j : Fin 2) :
    AnalyticAt ℂ (fun x => qpCC y x j) x₀ :=
  planetChartC_analyticAt (analyticAt_const.mul (analyticAt_proj_fst j)) (analyticAt_proj_Λ j)
    (analyticAt_proj_ξ j) (analyticAt_proj_η j) (h j)

theorem qpCC_coord_analyticAt {y : Fin 2 → ℝ} {x₀ : CVar} (h : ChartOkAt y x₀) (j i : Fin 2) :
    AnalyticAt ℂ (fun x => (qpCC y x j).1 i) x₀ ∧ AnalyticAt ℂ (fun x => (qpCC y x j).2 i) x₀ :=
  ⟨(analyticAt_pi_iff.1 (analyticAt_fst.comp (qpCC_analyticAt h j))) i,
    (analyticAt_pi_iff.1 (analyticAt_snd.comp (qpCC_analyticAt h j))) i⟩

theorem distSqCC_analyticAt {y : Fin 2 → ℝ} {x₀ : CVar} (h : ChartOkAt y x₀) :
    AnalyticAt ℂ (distSqCC y) x₀ := by
  have q := qpCC_coord_analyticAt h
  unfold distSqCC
  exact ((q 0 0).1.sub (q 1 0).1).pow 2 |>.add (((q 0 1).1.sub (q 1 1).1).pow 2)

/-- **(1c-i) `P_C` is analytic at every point with the chart conditions and `Re d² > 0`.** -/
theorem pertCC_analyticAt {y : Fin 2 → ℝ} {x₀ : CVar} (h : ChartOkAt y x₀)
    (hd : 0 < (distSqCC y x₀).re) : AnalyticAt ℂ (pertCC y) x₀ := by
  have q := qpCC_coord_analyticAt h
  have hD : AnalyticAt ℂ (fun x => distSqCC y x ^ (-(1 / 2 : ℂ))) x₀ :=
    (distSqCC_analyticAt h).cpow analyticAt_const (Complex.mem_slitPlane_iff.2 (Or.inl hd))
  unfold pertCC
  have a00 := (q 0 0).2
  have a10 := (q 1 0).2
  have a01 := (q 0 1).2
  have a11 := (q 1 1).2
  fun_prop

/-! ### (1c-ii) Periodicity -/

/-- A shift of `λ` by `2π` does not change one planet's chart (uniqueness in the strip). -/
theorem planetChartC_add_two_pi {y₀ m : ℝ} {lam Λ ξ η : ℂ} (h : PlanetOk y₀ lam Λ ξ η) :
    planetChartC y₀ m (lam + 2 * π) Λ ξ η = planetChartC y₀ m lam Λ ξ η := by
  have hu : ∃! G : ℂ, |G.im| ≤ y₀ ∧ KAM.Kepler.keplerOp (eccC Λ ξ η 0) (eccC Λ ξ η 1) G = lam := by
    obtain ⟨h1, h2, h3⟩ := eccLongC_spec h
    exact ⟨_, ⟨h1, h2⟩, fun G hG => h3 G hG.1 hG.2⟩
  have hs : eccLongC y₀ (lam + 2 * π) Λ ξ η = eccLongC y₀ lam Λ ξ η + 2 * π :=
    KAM.Kepler.keplerSol_shift hu
  simp only [planetChartC_eq, vcC, hs, Complex.cos_add_two_pi, Complex.sin_add_two_pi]

/-- **(1c-ii) `P_C` is `1`-periodic in each angle.** -/
theorem pertCC_add_single {y : Fin 2 → ℝ} {x : CVar} (h : ChartOkAt y x) (j : Fin 2) :
    pertCC y (x.1 + Pi.single j 1, x.2) = pertCC y x := by
  have hx1 : ∀ i, ((x.1 + Pi.single j (1 : ℂ) : Fin 2 → ℂ)) i =
      x.1 i + if i = j then 1 else 0 := by
    intro i; simp [Pi.single_apply]
  have hq : ∀ i, qpCC y (x.1 + Pi.single j 1, x.2) i = qpCC y x i := by
    intro i
    unfold qpCC
    dsimp only
    by_cases hij : i = j
    · subst hij
      have e : 2 * (π : ℂ) * ((x.1 + Pi.single i (1 : ℂ) : Fin 2 → ℂ)) i =
          2 * π * x.1 i + 2 * π := by
        rw [hx1]; simp only [ite_true]; ring
      rw [e]
      exact planetChartC_add_two_pi (h i)
    · have e : ((x.1 + Pi.single j (1 : ℂ) : Fin 2 → ℂ)) i = x.1 i := by rw [hx1]; simp [hij]
      rw [e]
  simp only [pertCC, distSqCC, hq]

/-! ### (1c-iii) Agreement at real points -/

theorem ofReal_cpow_half {r : ℝ} (hr : 0 ≤ r) : (r : ℂ) ^ (1 / 2 : ℂ) = ((√r : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr]; norm_num

theorem ofReal_cpow_neg_half {r : ℝ} (hr : 0 ≤ r) :
    (r : ℂ) ^ (-(1 / 2 : ℂ)) = (((√r)⁻¹ : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hr, Complex.ofReal_cpow hr]; norm_num

/-- **One planet's complexified chart at a real point is LP's real chart** (`κ = 1`). -/
theorem planetChartC_ofReal {y₀ m lam Λ ξ η : ℝ} (hΛ : 0 < Λ) (hΓ : (ξ ^ 2 + η ^ 2) / 2 < Λ)
    (h : PlanetOk y₀ (lam : ℂ) (Λ : ℂ) (ξ : ℂ) (η : ℂ)) :
    planetChartC y₀ m lam Λ ξ η =
      (fun i => ((poincare m 1 (![lam, ξ], ![Λ, η])).1 i : ℂ),
        fun i => ((poincare m 1 (![lam, ξ], ![Λ, η])).2 i : ℂ)) := by
  set b : Phase 2 := (![lam, ξ], ![Λ, η]) with hbdef
  have hG : poincareGamma b = (ξ ^ 2 + η ^ 2) / 2 := by simp [poincareGamma, hbdef]
  have hr : 0 ≤ (1 - poincareGamma b / (2 * Λ)) / Λ := by
    apply div_nonneg _ hΛ.le
    rw [sub_nonneg, div_le_one (by linarith), hG]
    have : 0 ≤ (ξ ^ 2 + η ^ 2) / 2 := by positivity
    linarith
  have hrad : radC Λ ξ η = (((1 - poincareGamma b / (2 * Λ)) / Λ : ℝ) : ℂ) := by
    rw [hG]; simp only [radC]; push_cast; ring
  have hV : ∀ i, poincareV b i = √((1 - poincareGamma b / (2 * Λ)) / Λ) * ![ξ, η] i := by
    intro i; simp [poincareV, hbdef]
  have hv : eccC Λ ξ η = fun i => ((poincareV b i : ℝ) : ℂ) := by
    funext i
    rw [eccC, hrad, ofReal_cpow_half hr, hV]
    fin_cases i <;> simp
  have hpl : planeLength (poincareV b) < 1 := by
    have hc := h.contraction
    rw [hv] at hc
    simp only [Complex.norm_real, Real.norm_eq_abs] at hc
    have h1 : 1 ≤ Real.cosh y₀ := Real.one_le_cosh y₀
    have h2 : |poincareV b 0| + |poincareV b 1| < 1 := by
      nlinarith [abs_nonneg (poincareV b 0), abs_nonneg (poincareV b 1)]
    have hsq : planeSq (poincareV b) ≤ (|poincareV b 0| + |poincareV b 1|) ^ 2 := by
      simp only [planeSq, Fin.sum_univ_two, add_sq, sq_abs]
      nlinarith [abs_nonneg (poincareV b 0), abs_nonneg (poincareV b 1)]
    unfold planeLength
    rw [Real.sqrt_lt' one_pos]
    nlinarith [abs_nonneg (poincareV b 0), abs_nonneg (poincareV b 1)]
  have hF : eccLongC y₀ lam Λ ξ η = ((poincareF b : ℝ) : ℂ) := by
    symm
    refine (eccLongC_spec h).2.2 _ (by simpa using h.y_pos.le) ?_
    have h1 := KAM.Kepler.keplerPhi_keplerLong hpl (b.1 0)
    unfold KAM.Kepler.keplerPhi at h1
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) h1
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sin,
      Complex.ofReal_cos] at h2
    rw [hv]
    unfold KAM.Kepler.keplerOp poincareF
    simpa [hbdef] using h2
  have hk : kC Λ ξ η = ((poincareK b : ℝ) : ℂ) := by
    simp only [kC, poincareK, hG]; push_cast
    simp [hbdef]
  have hvc : vcC y₀ lam Λ ξ η = ((planeDot (poincareV b) (orbitalUnit (poincareF b)) : ℝ) : ℂ) := by
    unfold vcC
    rw [hv, hF]
    simp [planeDot, Fin.sum_univ_two, orbitalUnit]
  have hΛb : b.2 0 = Λ := by simp [hbdef]
  rw [planetChartC_eq, hvc, hk, hF, hv]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · fin_cases i <;>
      simp only [poincare, orbitalUnit, hΛb, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
        smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta,
        Fin.mk_one, Fin.isValue, mul_one] <;> push_cast <;> ring
  · fin_cases i <;>
      simp only [poincare, orbitalUnit, quarterTurn, KAM.Kepler.keplerJac, hΛb, Pi.smul_apply,
        Pi.sub_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fin.zero_eta, Fin.mk_one, Fin.isValue, mul_one] <;> push_cast <;> ring

/-- `P = μ fMov(Ψ)` on the chart domain. -/
theorem chartPert_eq_fMov {w : Phase (2 + 2)} (hw : w ∈ poincareProdDom 2) :
    chartPert nu mu w = mu * fMov 1 1 nu (poincareProd nu 1 w) := by
  unfold chartPert liftChartHam
  rw [lpChart_hamiltonian nu_pos mu hw]; ring

/-- `fMov` for two planets. -/
theorem fMov_two (z : Phase (2 * 2)) :
    fMov 1 1 nu z = planeSq (bodyVector z.2 0 + bodyVector z.2 1) / 2 -
      nu 0 * nu 1 / planeLength (bodyVector z.1 0 - bodyVector z.1 1) := by
  have e0 : Finset.univ.filter (fun j : Fin 2 => (0 : Fin 2) < j) = {1} := by decide
  have e1 : Finset.univ.filter (fun j : Fin 2 => (1 : Fin 2) < j) = ∅ := by decide
  simp only [fMov, pairPotential, Fin.sum_univ_two, e0, e1, Finset.sum_singleton,
    Finset.sum_empty]
  ring

theorem withAngles_mem_dom {w : Phase (2 + 2)} (hw : w ∈ poincareProdDom 2) (lam : Fin 2 → ℝ) :
    withAngles w lam ∈ poincareProdDom 2 := by
  intro i
  have h := hw i
  simpa [poincareDom, poincareGamma, planetBlock, withAngles_fst_slow, withAngles_snd] using h

/-- **(1c-iii) At real points `P_C` is `P`.** -/
theorem pertCC_realVar_ofReal {y : Fin 2 → ℝ} {w : Phase (2 + 2)}
    (hw : w ∈ poincareProdDom 2) (t : Fin 2 → ℝ) (h : ChartOkAt y (realVar w fun j => (t j : ℂ))) :
    pertCC y (realVar w fun j => (t j : ℂ)) =
      (chartPert nu mu (withAngles w fun j => 2 * π * t j) : ℂ) := by
  set w' := withAngles w fun j => 2 * π * t j with hw'def
  have hw' : w' ∈ poincareProdDom 2 := withAngles_mem_dom hw _
  have hblk : ∀ j, qpCC y (realVar w fun j => (t j : ℂ)) j =
      (fun i => ((poincare (nu j) 1 (planetBlock w' j)).1 i : ℂ),
        fun i => ((poincare (nu j) 1 (planetBlock w' j)).2 i : ℂ)) := by
    intro j
    have hb := hw' j
    have hpb : planetBlock w' j = (![2 * π * t j, slow w.1 j], ![fast w.2 j, slow w.2 j]) := by
      simp [planetBlock, hw'def, withAngles_fst_fast, withAngles_fst_slow, withAngles_snd]
    rw [hpb] at hb ⊢
    obtain ⟨hΛ, hΓ⟩ := hb
    simp only [poincareGamma] at hΓ
    have hlam : ((2 * π * t j : ℝ) : ℂ) = 2 * π * (t j : ℂ) := by push_cast; ring
    have hj := h j
    simp only [realVar] at hj
    rw [← hlam] at hj
    have := planetChartC_ofReal (m := nu j) (by simpa using hΛ) (by simpa using hΓ) hj
    simp only [qpCC, realVar, ← hlam]
    simpa using this
  have hq := fun j => poincareProd_block nu 1 w' j
  rw [chartPert_eq_fMov hw', fMov_two]
  have hQ : ∀ j, bodyVector (poincareProd nu 1 w').1 j = (poincare (nu j) 1 (planetBlock w' j)).1 :=
    fun j => congrArg Prod.fst (hq j)
  have hP : ∀ j, bodyVector (poincareProd nu 1 w').2 j = (poincare (nu j) 1 (planetBlock w' j)).2 :=
    fun j => congrArg Prod.snd (hq j)
  rw [hQ, hQ, hP, hP]
  have hD : distSqCC y (realVar w fun j => (t j : ℂ)) = ((planeSq
      ((poincare (nu 0) 1 (planetBlock w' 0)).1 - (poincare (nu 1) 1 (planetBlock w' 1)).1) :
        ℝ) : ℂ) := by
    simp only [distSqCC, hblk]
    simp [planeSq, Fin.sum_univ_two]
  have hD0 : 0 ≤ planeSq ((poincare (nu 0) 1 (planetBlock w' 0)).1 -
      (poincare (nu 1) 1 (planetBlock w' 1)).1) := Finset.sum_nonneg fun k _ => sq_nonneg _
  simp only [pertCC, hD, ofReal_cpow_neg_half hD0, hblk]
  push_cast
  simp only [planeSq, planeLength, Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply]
  push_cast
  ring

/-! ### (1c) on the per-slab strips, with (1b) as a named premise -/

/-- **(1b) as a named premise**: no complex collision on the strip `ρ` at the real state `w`
(to be discharged by the layer's certified enclosure of `d²`, e.g. `noCollision_of_enclosure`). -/
def NoCollisionOn (y ρ : Fin 2 → ℝ) (w : Phase (2 + 2)) : Prop :=
  ∀ θ ∈ stripA ρ, 0 < (distSqC y w θ).re

/-- (1c) in the drafted form: holomorphic and `1`-periodic on the strip, `P` at real angles. -/
def ChartPertExt (y ρ : Fin 2 → ℝ) (w : Phase (2 + 2)) : Prop :=
  DifferentiableOn ℂ (chartPertC y w) (stripA ρ) ∧
    (∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ stripA ρ →
      chartPertC y w (θ + Pi.single j 1) = chartPertC y w θ) ∧
    ∀ t : Fin 2 → ℝ, chartPertC y w (fun j => (t j : ℂ)) =
      (chartPert nu mu (withAngles w fun j => 2 * π * t j) : ℂ)

theorem holoDomHD_subset_dom : holoDomHD ⊆ poincareProdDom 2 := fun _ hw =>
  openHD_subset_dom (region_subset_openHD (by norm_num) hw.1)

/-- The eccentricity vector at a real point is LP's `β (ξ, η)`. -/
theorem eccC_ofReal {Λ ξ η : ℝ} (hΛ : 0 < Λ) (hΓ : (ξ ^ 2 + η ^ 2) / 2 < Λ) :
    eccC Λ ξ η = ![((lpEccScale Λ ((ξ ^ 2 + η ^ 2) / 2) * ξ : ℝ) : ℂ),
      ((lpEccScale Λ ((ξ ^ 2 + η ^ 2) / 2) * η : ℝ) : ℂ)] := by
  have hr : 0 ≤ (1 - (ξ ^ 2 + η ^ 2) / 2 / (2 * Λ)) / Λ := by
    apply div_nonneg _ hΛ.le
    rw [sub_nonneg, div_le_one (by linarith)]
    have : 0 ≤ (ξ ^ 2 + η ^ 2) / 2 := by positivity
    linarith
  have hrad : radC Λ ξ η = (((1 - (ξ ^ 2 + η ^ 2) / 2 / (2 * Λ)) / Λ : ℝ) : ℂ) := by
    simp only [radC]; push_cast; ring
  funext i
  rw [eccC, hrad, ofReal_cpow_half hr]
  fin_cases i <;> simp [lpEccScale]

/-- **The chart conditions on the strip from (1a)** at a real state of the chart domain. -/
theorem chartOkAt_of_keplerData {y ρ κ : Fin 2 → ℝ} {w : Phase (2 + 2)}
    (hw : w ∈ poincareProdDom 2)
    (hK : ∀ j, KAM.Kepler.KeplerData {lam : ℂ | |lam.im| < 2 * π * ρ j}
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.1 j : ℝ) : ℂ))
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.2 j : ℝ) : ℂ))
      (fun lam => lam) (y j) (κ j))
    {θ : Fin 2 → ℂ} (hθ : θ ∈ stripA ρ) : ChartOkAt y (realVar w θ) := by
  intro j
  obtain ⟨hΛ, hΓ⟩ := hw j
  have hΛ' : 0 < fast w.2 j := by simpa [planetBlock] using hΛ
  have hΓ' : ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2 < fast w.2 j := by
    simpa [poincareGamma, planetBlock] using hΓ
  have hv := eccC_ofReal hΛ' hΓ'
  have hG : lpGamma w j = ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2 := rfl
  have hmem : 2 * π * θ j ∈ {lam : ℂ | |lam.im| < 2 * π * ρ j} := by
    have h1 := hθ j
    have hpi : (0 : ℝ) < 2 * π := by positivity
    simp only [Set.mem_ofPred_eq]
    have e : (2 * (π : ℂ) * θ j).im = 2 * π * (θ j).im := by simp
    rw [e, abs_mul, abs_of_pos hpi]
    exact mul_lt_mul_of_pos_left h1 hpi
  have hinv := (hK j).invariant _ hmem
  have hcon := (hK j).contraction _ hmem
  rw [hG] at hinv hcon
  simp only [realVar]
  refine ⟨by exact_mod_cast hΛ'.ne', ?_, ?_, (hK j).y₀_pos, ?_, ?_⟩
  · have hpos : 0 < (1 - ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2 / (2 * fast w.2 j)) /
        fast w.2 j := by
      apply div_pos _ hΛ'
      rw [sub_pos, div_lt_one (by linarith)]
      have : 0 ≤ ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2 := by positivity
      linarith
    have e : radC (fast w.2 j) (slow w.1 j) (slow w.2 j) = (((1 - ((slow w.1 j) ^ 2 +
        (slow w.2 j) ^ 2) / 2 / (2 * fast w.2 j)) / fast w.2 j : ℝ) : ℂ) := by
      simp only [radC]; push_cast; ring
    rw [e]
    exact Complex.ofReal_mem_slitPlane.2 hpos
  · have e : 1 + kC (fast w.2 j) (slow w.1 j) (slow w.2 j) = ((2 - ((slow w.1 j) ^ 2 +
        (slow w.2 j) ^ 2) / 2 / fast w.2 j : ℝ) : ℂ) := by
      simp only [kC]; push_cast; ring
    rw [e]
    have : ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2 / fast w.2 j < 1 := by
      rw [div_lt_one hΛ']; exact hΓ'
    exact_mod_cast (by linarith : (0 : ℝ) < 2 - ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2 /
      fast w.2 j).ne'
  · rw [hv]
    simpa using hinv
  · rw [hv]
    have := (hK j).κ_lt
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hcon ⊢
    linarith

/-- **(1c) on a strip from (1a) and (1b)**: holomorphic, periodic, `P` at real angles. -/
theorem chartPertExt_of {y ρ κ : Fin 2 → ℝ} {w : Phase (2 + 2)} (hw : w ∈ poincareProdDom 2)
    (hρ : ∀ j, 0 < ρ j)
    (hK : ∀ j, KAM.Kepler.KeplerData {lam : ℂ | |lam.im| < 2 * π * ρ j}
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.1 j : ℝ) : ℂ))
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.2 j : ℝ) : ℂ))
      (fun lam => lam) (y j) (κ j))
    (hcol : NoCollisionOn y ρ w) : ChartPertExt y ρ w := by
  have e : chartPertC y w = pertCC y ∘ fun θ => realVar w θ :=
    funext fun θ => chartPertC_eq_pertCC y w θ
  refine ⟨fun θ hθ => ?_, fun j θ hθ => ?_, fun t => ?_⟩
  · have ha := pertCC_analyticAt (chartOkAt_of_keplerData hw hK hθ) (hcol θ hθ)
    have hr : AnalyticAt ℂ (fun θ : Fin 2 → ℂ => realVar w θ) θ :=
      analyticAt_id.prod analyticAt_const
    rw [e]
    exact (ha.comp hr).differentiableAt.differentiableWithinAt
  · rw [chartPertC_eq_pertCC, chartPertC_eq_pertCC]
    exact pertCC_add_single (chartOkAt_of_keplerData hw hK hθ) j
  · rw [chartPertC_eq_pertCC]
    exact pertCC_realVar_ofReal hw t (chartOkAt_of_keplerData hw hK (ofReal_mem_stripA hρ t))

/-- **(1c), uniform strip** `ρ = (1/40, 3/20)` (slab 6, and all of `holoDomHD`). -/
theorem chartPertExt_HD {w : Phase (2 + 2)} (hw : w ∈ holoDomHD)
    (hcol : NoCollisionOn yHolo rhoHolo w) : ChartPertExt yHolo rhoHolo w :=
  chartPertExt_of (holoDomHD_subset_dom hw) (fun j => by fin_cases j <;> norm_num [rhoHolo])
    (fun j => keplerData_HD j hw) hcol

/-- **(1c), slabs 0–4** (`|ξ_c| ≤ 0.1431`): `ρ = (7/200, 3/20)`. -/
theorem chartPertExt_HD_A {w : Phase (2 + 2)} (hw : w ∈ holoDomHD)
    (hξ : |slow w.1 0| ≤ 1431 / 10000) (hcol : NoCollisionOn yHoloA rhoHoloA w) :
    ChartPertExt yHoloA rhoHoloA w :=
  chartPertExt_of (holoDomHD_subset_dom hw) (fun j => by fin_cases j <;> norm_num [rhoHoloA])
    (fun j => keplerData_HD_A j hw hξ) hcol

/-- **(1c), slab 5** (`|ξ_c| ≤ 0.1612`): `ρ = (3/100, 3/20)`. -/
theorem chartPertExt_HD_B {w : Phase (2 + 2)} (hw : w ∈ holoDomHD)
    (hξ : |slow w.1 0| ≤ 1612 / 10000) (hcol : NoCollisionOn yHoloB rhoHoloB w) :
    ChartPertExt yHoloB rhoHoloB w :=
  chartPertExt_of (holoDomHD_subset_dom hw) (fun j => by fin_cases j <;> norm_num [rhoHoloB])
    (fun j => keplerData_HD_B j hw hξ) hcol

/-! ### The cell-to-slab check -/

/-- The cells of one slab (in `CoverPlan.cells` order). -/
def Slab.cells (s : Slab) : List AffineCell := s.disc.toList ++ (s.upper ++ s.lower).map (·.cell)

/-- Decidable: every cell of the slab has `|c₂| + |h₂| ≤ X` (the `ξ_c` axis). -/
def Slab.xiOk (s : Slab) (X : ℚ) : Bool := s.cells.all fun k => decide (|k.c 2| + |k.h 2| ≤ X)

theorem abs_xi_le_of_mem_toSet {k : AffineCell} {w : Phase (2 + 2)} (hw : w ∈ k.toSet) :
    |slow w.1 0| ≤ |((k.c 2 : ℚ) : ℝ)| + |((k.h 2 : ℚ) : ℝ)| := by
  obtain ⟨u, hu, he⟩ := hw
  have h2 := congrFun he 2
  simp only [cellCoord, AffineCell.map] at h2
  simp only [Matrix.cons_val, Fin.isValue] at h2
  rw [h2]
  calc |((k.c 2 : ℚ) : ℝ) + ((k.h 2 : ℚ) : ℝ) * u 2| ≤
        |((k.c 2 : ℚ) : ℝ)| + |((k.h 2 : ℚ) : ℝ)| * |u 2| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ |((k.c 2 : ℚ) : ℝ)| + |((k.h 2 : ℚ) : ℝ)| * 1 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (hu 2) (abs_nonneg _))
    _ = _ := by ring

theorem abs_xi_le_of_xiOk {s : Slab} {X : ℚ} (hs : s.xiOk X = true) {k : AffineCell}
    (hk : k ∈ s.cells) {w : Phase (2 + 2)} (hw : w ∈ k.toSet) : |slow w.1 0| ≤ (X : ℝ) := by
  have h := List.all_eq_true.1 hs k hk
  have hq : |k.c 2| + |k.h 2| ≤ X := of_decide_eq_true h
  have hq' : ((|k.c 2| + |k.h 2| : ℚ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hq
  push_cast at hq'
  exact (abs_xi_le_of_mem_toSet hw).trans hq'

/-- The decided check on `fitPlan`: slabs 0–4 within `0.1431`, slab 5 within `0.1612`. -/
theorem fitPlan_xiOk : ((fitPlan.slabs.take 5).all fun s => s.xiOk (1431 / 10000)) = true ∧
    (((fitPlan.slabs.drop 5).take 1).all fun s => s.xiOk (1612 / 10000)) = true :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- **The cell-to-slab statement**: every cell of slabs 0–4 of `fitPlan` lies in
`|ξ_c| ≤ 0.1431`, every cell of slab 5 in `|ξ_c| ≤ 0.1612`. -/
theorem fitPlan_slabs_xi :
    (∀ s ∈ fitPlan.slabs.take 5, ∀ k ∈ s.cells, ∀ w ∈ k.toSet, |slow w.1 0| ≤ 1431 / 10000) ∧
    (∀ s ∈ (fitPlan.slabs.drop 5).take 1, ∀ k ∈ s.cells, ∀ w ∈ k.toSet,
      |slow w.1 0| ≤ 1612 / 10000) := by
  refine ⟨fun s hs k hk w hw => ?_, fun s hs k hk w hw => ?_⟩
  · exact (abs_xi_le_of_xiOk (List.all_eq_true.1 fitPlan_xiOk.1 s hs) hk hw).trans
      (by norm_num)
  · exact (abs_xi_le_of_xiOk (List.all_eq_true.1 fitPlan_xiOk.2 s hs) hk hw).trans
      (by norm_num)

end HD11964.Cover

end
