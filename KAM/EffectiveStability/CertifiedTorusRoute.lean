/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.CertifiedTorusRoute.Glue
public import KAM.EffectiveStability.TorusNormalForm

/-!
# Certified exact torus ⇒ certified effective stability near it (track B, package B5-ROUTE)

`certifiedTorus_confinement`: for the exact torus `K∞` of a certificate (`CertifiedTorusAt`,
under `G1Hyps` and the Diophantine condition), the real Hamiltonian `realHam c.H`, the chart
`Ψ = torusChartMap (torusRealU K∞) (torusRealV K∞)` and the frequency `ω' = s∞ ω*`, the conclusion
of B1-T `torus_confinement` holds for every chart point `w₀` with `|w₀.2 j| ≤ a j`, provided the
finite checks of `RouteChecks` hold, the Cauchy radius `r` satisfies `r ≤ δφ` and
`b j + ε + r ≤ ρJ`, and the drift margins `a j + T η j < b j`, `η j ≥ C₃ B²/2` hold with the
explicit Cauchy constant `C₃ = routeC3 c r = 64 (M μ/2) / r³`.

Items: 1 `RouteChecks.chartData`, 2 `certifiedTorus_nfTorus`, 3 `hG` by complexification
(`RouteChecks.realHam_comp_chart_eq`, `contDiffOn_realPart_of_holo`) and `hD3` by the
third-derivative Cauchy estimate `abs_fderiv3_realPart_le` with the sup bound
`RouteChecks.ham_sub_le`, 4 periodicity from `G1Hyps.hper`, 5 `torusNormalForm_confinement`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.EffectiveStability

open KAM KAM.Torus KAM.Certificate KAM.Application CertArith Metric Set

variable {n : ℕ} {α : Type} [CertArith α] {c : TorusCertificate n α} {ωstar : Fin n → ℝ}
  {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {sinf : ℝ} {κc δ δφ ρJ : ℝ}

/-- The explicit third-derivative Cauchy constant `C₃ = 64 (M μ / 2) / r³`. -/
def routeC3 (c : TorusCertificate n α) (r : ℝ) : ℝ :=
  64 * ((c.params.M : ℝ) * ((c.params.μ : ℝ) / 2)) / r ^ 3

theorem routeC3_nonneg (hG : G1Hyps c ωstar) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ routeC3 c r := by
  have := hG.hM; have := hG.hμ
  unfold routeC3
  positivity

/-- **Certified exact torus ⇒ certified effective stability near it.** -/
theorem certifiedTorus_confinement (hG : G1Hyps c ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar)
    (hT : CertifiedTorusAt c ωstar Kinf sinf) (h : RouteChecks c κc δ δφ ρJ)
    {r : ℝ} (hr : 0 < r) (hrφ : r ≤ δφ)
    (a b η : Fin n → ℝ) (ε Tt : ℝ) (hε : 0 < ε) (hTt : 0 ≤ Tt)
    (hmargin : ∀ j, a j + Tt * η j < b j) (hrJ : ∀ j, b j + ε + r ≤ ρJ)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ j, b j ≤ B) (hηB : ∀ j, routeC3 c r * B ^ 2 / 2 ≤ η j)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hw₀ : ∀ j, |w₀.2 j| ≤ a j) :
    ∃ T₁ : ℝ, Tt < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ),
      z 0 = torusChartMap (torusRealU Kinf) (torusRealV Kinf) w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ {y | realInclusion₂ n y ∈ c.D} ∧
        HasDerivAt z (hamiltonianVectorField (realHam c.H) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = torusChartMap (torusRealU Kinf) (torusRealV Kinf) w₀ →
        (∀ t ∈ I, y t ∈ {y | realInclusion₂ n y ∈ c.D} ∧
          HasDerivAt y (hamiltonianVectorField (realHam c.H) (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ Tt →
        torusChartMap (torusRealU Kinf) (torusRealV Kinf)
          (torusChartInvMap (torusRealU Kinf) (torusRealV Kinf) (z t)) = z t ∧
        ∀ j, |(torusChartInvMap (torusRealU Kinf) (torusRealV Kinf) (z t)).2 j - w₀.2 j| ≤
            η j * |t| ∧
          |(torusChartInvMap (torusRealU Kinf) (torusRealV Kinf) (z t)).2 j| ≤ a j + η j * Tt := by
  have hchart := h.chartData hG hdio hT
  have hnf := certifiedTorus_nfTorus hG hT
  have hDom := isOpen_routeDomain (n := n) δφ ρJ
  have hHd := h.ham_differentiableOn hG hT
  -- the chart cylinder lies in the pulled-back domain
  have hcylD : ∀ y : (Fin n → ℝ) × (Fin n → ℝ), (∀ j, |y.2 j| < b j + ε) →
      realInclusion₂ n y ∈ routeDomain n δφ ρJ := fun y hy =>
    ball_subset_routeDomain hrφ hrJ h.hρJ0 hy (mem_ball_self hr)
  have hmapD : ∀ w : (Fin n → ℝ) × (Fin n → ℝ), (∀ j, |w.2 j| < b j + ε) →
      realInclusion₂ n (torusChartMap (torusRealU Kinf) (torusRealV Kinf) w) ∈ c.D := by
    intro w hw
    rw [← torusCxChart_realInclusion hG.hρinf hT.2.2.1 hT.2.2.2.2.1 (h.chart_det_ne hG hdio hT) w]
    exact h.chart_mem_D hG hT (hcylD w hw)
  refine torusNormalForm_confinement hchart a b η ε Tt hε hTt hmargin
    {y | realInclusion₂ n y ∈ c.D} (hG.hopen.preimage (realInclusion₂ n).continuous)
    (realHam c.H) (contDiffOn_realPart_of_holo hG.hopen hG.hholo 2) (c.params.E0 : ℝ)
    (sinf • ωstar) hmapD ?_ hnf ?_ (routeC3 c r) B (routeC3_nonneg hG hr.le) hB0 hB ?_ hηB w₀ hw₀
  · -- periodicity along the chart image
    intro k w hw
    have hz := hmapD w hw
    unfold realHam
    have : realInclusion₂ n (torusChartMap (torusRealU Kinf) (torusRealV Kinf) w +
        KAM.ODE.angleShift k) = ((realInclusion₂ n (torusChartMap (torusRealU Kinf)
          (torusRealV Kinf) w)).1 + (fun i => (k i : ℂ)),
          (realInclusion₂ n (torusChartMap (torusRealU Kinf) (torusRealV Kinf) w)).2) := by
      ext i <;> simp [KAM.ODE.angleShift]
    rw [this, hG.hper _ hz k]
  · -- hG : C³
    have hfun : realHam c.H ∘ torusChartMap (torusRealU Kinf) (torusRealV Kinf) =
        fun w => (c.H (torusCxChart Kinf (realInclusion₂ n w))).re :=
      funext fun w => h.realHam_comp_chart_eq hG hdio hT w
    rw [hfun]
    exact (contDiffOn_realPart_of_holo hDom hHd 3).mono fun y hy => hcylD y hy
  · -- hD3 : third derivative bound
    intro y hy x₁ x₂ x₃
    have hfun : realHam c.H ∘ torusChartMap (torusRealU Kinf) (torusRealV Kinf) =
        fun w => (c.H (torusCxChart Kinf (realInclusion₂ n w))).re :=
      funext fun w => h.realHam_comp_chart_eq hG hdio hT w
    rw [hfun]
    have hball := ball_subset_routeDomain (δφ := δφ) (ρJ := ρJ) hrφ hrJ h.hρJ0 hy
    have := abs_fderiv3_realPart_le hDom hHd (y := y) ((c.params.E0 : ℝ) : ℂ) hr hball
      (fun w hw => h.ham_sub_le hG hT (hball hw)) x₁ x₂ x₃
    refine this.trans (le_of_eq ?_)
    unfold routeC3
    ring

end KAM.EffectiveStability

end
