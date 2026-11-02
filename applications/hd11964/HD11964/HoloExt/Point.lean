/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.HoloSlab

/-!
# HD 11964: the fully complexified perturbation — analyticity and periodicity (HD11964-HOLO)

Part 1 of `HD11964.HoloExt` (the facade keeps the public names).

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

end HD11964.Cover

end
