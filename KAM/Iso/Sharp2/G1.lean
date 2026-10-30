/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.RouteB
public import KAM.Iso.Sharp2.RouteA.Frozen

/-!
# The combined isoenergetic theorem (`bpI:p2s2:frozen`, hybrid of the routes)

`KAM.Iso.Sharp2.iso_g1_v2`: the literal frozen `KAM.Iso.Charts.IG1Body` with
`C₁ = min {C₁♯, C₁ᴬ, C₁ᴮ}`, `C₂ = max {C₂♯, C₂ᴬ, C₂ᴮ}`, `C₃ = max {C₃♯, C₃ᴬ, C₃ᴮ}`, uniform over
the three branches: v1 (`KAM.Iso.Sharp.g1_sharp`), route A
(`KAM.Iso.Sharp2.RouteA.iso_g1_v2A_frozen`, SHARP2-B9) and route B
(`KAM.Iso.Sharp2.RouteB.iso_g1_v2B_frozen`), as `KAM.Sharp2.g1_v2` at fixed frequency: by cases on
the minimum, with the monotonicity `IsoG1V2.ig1Body_mono`.
-/

@[expose] public noncomputable section

namespace KAM.Iso.Sharp2

open KAM KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA KAM.Sharp2.RouteB KAM.Iso.Sharp2.RouteA
  KAM.Iso.Charts KAM.Iso.Sharp

namespace IsoG1V2

/-- The frozen body is monotone: a larger smallness constant and larger closeness constants. -/
theorem ig1Body_mono {n : ℕ} {τ ρ ρinf M σK σB σT μ γbar σω ν C₁ C₂ C₃ C₁' C₂' C₃' : ℝ}
    {ωstar : Fin n → ℝ} (hρ : 0 < ρ)
    (hB : IG1Body n τ ρ ρinf M σK σB σT μ γbar σω ν ωstar C₁ C₂ C₃) (h1 : C₁ ≤ C₁') (h2 : C₂ ≤ C₂')
    (h3 : C₃ ≤ C₃') : IG1Body n τ ρ ρinf M σK σB σT μ γbar σω ν ωstar C₁' C₂' C₃' := by
  intro D H K s γ e E₀ hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hs1 hsσ
    hν1 hν2 hγ hγγbar hdio he0 hE hEn hsm
  have hd4 : 0 < γ ^ 4 * ρ ^ (4 * τ) := mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos hρ _)
  have hd2 : 0 < γ ^ 2 * ρ ^ (2 * τ) := mul_pos (pow_pos hγ 2) (Real.rpow_pos_of_pos hρ _)
  have hsm' : C₁ * e / (γ ^ 4 * ρ ^ (4 * τ)) < 1 := lt_of_le_of_lt
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 he0) hd4.le) hsm
  obtain ⟨Kinf, sinf, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := hB D H K s γ e E₀ hopen
    htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hs1 hsσ hν1 hν2 hγ hγγbar hdio he0
    hE hEn hsm'
  exact ⟨Kinf, sinf, k1, k2, k3, k4, k5, k6, k7, k8, k9, fun θ hθ => (k10 θ hθ).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 he0) hd2.le), k11.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h3 he0) hd2.le)⟩

end IsoG1V2

/-- The v2 isoenergetic theorem, literal frozen `IG1Body`: `C₁ = min {C₁♯, C₁ᴬ, C₁ᴮ}`,
`C₂ = max {C₂♯, C₂ᴬ, C₂ᴮ}`, `C₃ = max {C₃♯, C₃ᴬ, C₃ᴮ}` (uniform over the three branches; B9's route
A with its hypotheses, route B). -/
theorem iso_g1_v2 {NA : NumA} {NB : NumB NA.n} (hNA : NA.Wf) (hNB : NB.Wf) (hisoA : NA.iso = true)
    (hisoB : NB.iso = true) (hτ : (NA.n : ℝ) - 1 ≤ NA.τ) (hτB : NB.τ = NA.τ) (hρB : NB.ρ = NA.ρ)
    (hρinfB : NB.ρinf = NA.ρinf) {M σK σB σT μ γbar σω ν Xa Xb : ℝ} (hM : 0 < M) (hσK : μ < σK)
    (hσB : μ < σB) (hσT : 0 < σT) (hμ : 0 < μ) (hσω : 1 < σω) (hν : 0 < ν)
    (ωstar : Fin NA.n → ℝ) (hωstar : ωstar ≠ 0) (hγA : γbar = NA.γb) (hγB : γbar = NB.γb)
    (hsKA : NA.sK = σK - μ / 2) (hsKB : NB.sK = σK - μ / 2) (hsBB : σB - μ < NB.sB)
    (hΘA : NA.Θ = σω * ‖ωstar‖) (hΘB : NB.Θ = σω * ‖ωstar‖) (hHY : NA.HY = M * NA.sN)
    (hy0 : NB.y0 = M * NB.sN) (hM1A : NA.M1 = M) (hM2A : NA.M2 = M) (hMh2A : NA.Mh2 = M)
    (hM1B : NB.M1 = M) (hM2B : NB.M2 = M) (hMh2B : NB.Mh2 = M) (hcTh : 2 * M ≤ NB.cTh)
    (hcDTh : 2 * M ≤ NB.cDTh) (hI : (defaultInitB NA.n σK σB μ).Wf NB σT μ)
    (hfit : NB.Fits (defaultInitB NA.n σK σB μ))
    (hOkA : routeAOkI NA (capI NA (μ / 2) (ν / 2)) (initI (defaultInit NA.n M σK σB μ) σK σB σT μ)
      Xa) (hTs : TorsionOk NA M σK σB Xa)
    (hOkB : routeBOk NB (capB NB σT μ ν) (initB (defaultInitB NA.n σK σB μ) σK σB μ) (μ / 2) Xb)
    (hXa : 0 < Xa) (hXb : 0 < Xb)
    (hcertA : ∀ γ, 0 < γ → γ ≤ γbar → NA.Cert γ {ω | IsDiophantine γ NA.τ ω})
    (hcertB : ∀ γ, 0 < γ → γ ≤ γbar → NB.Cert γ {ω | IsDiophantine γ NA.τ ω}) :
    0 < min (min (sharpIsoC1 NA.n NA.τ (cohConstR NA.n NA.τ) M σK σB σT γbar μ ν NA.τ NA.ρ NA.ρinf)
          (c1A NA Xa))
        (c1B NB (defaultInitB NA.n σK σB μ) Xb) ∧
      0 < max (max (sharpIsoC2 NA.n NA.τ (cohConstR NA.n NA.τ) M σK σB σT γbar NA.τ NA.ρ NA.ρinf)
          (c2I NA Xa))
        (c2B NB (defaultInitB NA.n σK σB μ) Xb) ∧
      0 < max (max (sharpIsoC3 NA.n NA.τ (cohConstR NA.n NA.τ) M σK σB σT γbar NA.τ NA.ρ NA.ρinf)
          (c3I NA Xa))
        (c3B NB (defaultInitB NA.n σK σB μ) Xb) ∧
      IG1Body NA.n NA.τ NA.ρ NA.ρinf M σK σB σT μ γbar σω ν ωstar
        (min (min (sharpIsoC1 NA.n NA.τ (cohConstR NA.n NA.τ) M σK σB σT γbar μ ν NA.τ NA.ρ NA.ρinf)
            (c1A NA Xa))
          (c1B NB (defaultInitB NA.n σK σB μ) Xb))
        (max (max (sharpIsoC2 NA.n NA.τ (cohConstR NA.n NA.τ) M σK σB σT γbar NA.τ NA.ρ NA.ρinf)
            (c2I NA Xa))
          (c2B NB (defaultInitB NA.n σK σB μ) Xb))
        (max (max (sharpIsoC3 NA.n NA.τ (cohConstR NA.n NA.τ) M σK σB σT γbar NA.τ NA.ρ NA.ρinf)
            (c3I NA Xa))
          (c3B NB (defaultInitB NA.n σK σB μ) Xb)) := by
  have hσK0 : 0 < σK := hμ.trans hσK
  have hσB0 : 0 < σB := hμ.trans hσB
  obtain ⟨hA1, hA2, hA3, hA⟩ := iso_g1_v2A_frozen hNA hisoA hτ hM hσK0 hσB0 hσT hμ hσω hν ωstar
    hωstar hγA hsKA hΘA hHY hM1A hM2A hMh2A hOkA hXa hTs hcertA
  have hτ' : (NA.n : ℝ) - 1 ≤ NB.τ := hτB ▸ hτ
  have hcertB' : ∀ γ, 0 < γ → γ ≤ γbar → NB.Cert γ {ω | IsDiophantine γ NB.τ ω} := by
    rw [hτB]; exact hcertB
  obtain ⟨hB1, hB2, hB3, hB⟩ := KAM.Iso.Sharp2.RouteB.iso_g1_v2B_frozen hNB hisoB hτ' hM hσK hσB
    hσT hμ hσω hν ωstar hωstar hγB hsKB hsBB hΘB hy0 hM1B hM2B hMh2B hcTh hcDTh hI hfit hOkB hXb
    hcertB'
  rw [hτB, hρB, hρinfB] at hB1 hB2 hB3 hB
  have hc1B : 0 < c1B NB (defaultInitB NA.n σK σB μ) Xb := (lt_min_iff.1 hB1).2
  have hρ : 0 < NA.ρ := hρB ▸ hNB.ρ_pos
  refine ⟨lt_min hA1 hc1B, lt_max_of_lt_left hA2, lt_max_of_lt_left hA3, ?_⟩
  by_cases hcase : min (sharpIsoC1 NA.n NA.τ (cohConstR NA.n NA.τ) M σK σB σT γbar μ ν NA.τ NA.ρ
      NA.ρinf) (c1A NA Xa) ≤ c1B NB (defaultInitB NA.n σK σB μ) Xb
  · rw [min_eq_left hcase]
    exact IsoG1V2.ig1Body_mono hρ hA le_rfl (le_max_left _ _) (le_max_left _ _)
  · rw [min_eq_right (not_le.1 hcase).le]
    exact IsoG1V2.ig1Body_mono hρ hB (min_le_right _ _) (max_le_max_right _ (le_max_left _ _))
      (max_le_max_right _ (le_max_left _ _))

end KAM.Iso.Sharp2

end
