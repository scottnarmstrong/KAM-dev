/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteB.Frozen
public import KAM.Sharp2.RouteA.Frozen

/-!
# The v2 a-posteriori theorem (blueprint `bp:p2s2:g1`, `bp:p2s2:frozen-form`)

`KAM.Sharp2.g1_v2` (verbatim): the literal frozen `KAM.Sharp.G1Body` with
`C₁ = min {C₁♯, C₁ᴬ, C₁ᴮ}` and `C₂ = max {C₂♯, C₂ᴬ, C₂ᴮ}`, uniform over the three branches: v1
(`KAM.Sharp.g1_sharp`), route A (`KAM.Sharp2.RouteA.g1_v2A_frozen`, SHARP2-B9) and route B
(`KAM.Sharp2.RouteB.g1_v2B_frozen`). By cases on the minimum: in the branch where route A or v1 is
smallest the body of `g1_v2A_frozen` applies verbatim; otherwise the body of `g1_v2B_frozen`,
with the smallness constant `min {C₁♯, C₁ᴮ} ≤ C₁ᴮ` (`G1V2.g1Body_mono`).
-/

@[expose] public noncomputable section

namespace KAM.Sharp2

open KAM KAM.Sharp KAM.Sharp2.RouteA KAM.Sharp2.RouteB

namespace G1V2

/-- The frozen body is monotone: a larger smallness constant and a larger closeness constant. -/
theorem g1Body_mono {n : ℕ} {τ ρ ρinf M σK σB σT μ γbar C₁ C₂ C₁' C₂' : ℝ} (hρ : 0 < ρ)
    (hB : G1Body n τ ρ ρinf M σK σB σT μ γbar C₁ C₂) (h1 : C₁ ≤ C₁') (h2 : C₂ ≤ C₂') :
    G1Body n τ ρ ρinf M σK σB σT μ γbar C₁' C₂' := by
  intro 𝔅 h K ω γ e hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hγ hγγbar
    hdio hE hsm
  have h00 : (0 : Fin n → ℂ) ∈ complexStrip n ρ := fun i => by simpa using hρ
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hE 0 h00)
  have hd4 : 0 < γ ^ 4 * ρ ^ (4 * τ) := mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos hρ _)
  have hd2 : 0 < γ ^ 2 * ρ ^ (2 * τ) := mul_pos (pow_pos hγ 2) (Real.rpow_pos_of_pos hρ _)
  have hsm' : C₁ * e / (γ ^ 4 * ρ ^ (4 * τ)) < 1 := lt_of_le_of_lt
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 he0) hd4.le) hsm
  obtain ⟨Kinf, k1, k2, k3, k4, k5, k6, k7⟩ := hB 𝔅 h K ω γ e hopen htransl hholo hper hreal hbd
    hK hKp hKr hball hDK hG hTu hTb hγ hγγbar hdio hE hsm'
  exact ⟨Kinf, k1, k2, k3, k4, k5, k6, fun θ hθ => (k7 θ hθ).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 he0) hd2.le)⟩

end G1V2

/-- The v2 theorem, literal frozen `KAM.Sharp.G1Body`: `C₁ = min {C₁♯, C₁ᴬ, C₁ᴮ}`,
`C₂ = max {C₂♯, C₂ᴬ, C₂ᴮ}` (uniform over the three branches; B9's route A with its hypotheses,
route B above). -/
theorem g1_v2 {NA : NumA} {NB : NumB NA.n} (hNA : NA.Wf) (hNB : NB.Wf) (hfixA : NA.iso = false)
    (hΘA : NA.Θ = 0) (hfixB : NB.iso = false) (hτ : (NA.n : ℝ) - 1 ≤ NA.τ) (hτB : NB.τ = NA.τ)
    (hρB : NB.ρ = NA.ρ) (hρinfB : NB.ρinf = NA.ρinf) {M σK σB σT μ γbar Xa Xb : ℝ} (hM : 0 < M)
    (hσK : μ < σK) (hσB : μ < σB) (hσT : 0 < σT) (hμ : 0 < μ) (hγA : γbar = NA.γb)
    (hγB : γbar = NB.γb) (hsKA : NA.sK = σK - μ / 2) (hsKB : NB.sK = σK - μ / 2)
    (hsBB : σB - μ < NB.sB) (hM1A : NA.M1 = M) (hM2A : NA.M2 = M) (hM1B : NB.M1 = M)
    (hM2B : NB.M2 = M) (hcTh : 2 * M ≤ NB.cTh) (hcDTh : 2 * M ≤ NB.cDTh)
    (hI : (defaultInitB NA.n σK σB μ).Wf NB σT μ) (hfit : NB.Fits (defaultInitB NA.n σK σB μ))
    (hOkA : routeAOk NA (NA.capV (μ / 2)) (initV (defaultInit NA.n M σK σB μ) σK σB σT μ) Xa)
    (hTs : TorsionOk NA M σK σB Xa)
    (hOkB : routeBOk NB (capB NB σT μ 0) (initB (defaultInitB NA.n σK σB μ) σK σB μ) (μ / 2)
      Xb)
    (hXa : 0 < Xa) (hXb : 0 < Xb)
    (hcertA : ∀ γ, 0 < γ → γ ≤ γbar → NA.Cert γ {ω | IsDiophantine γ NA.τ ω})
    (hcertB : ∀ γ, 0 < γ → γ ≤ γbar → NB.Cert γ {ω | IsDiophantine γ NA.τ ω}) :
    0 < min (min (sharpC1 NA.n NA.τ (cohConstR NA.n NA.τ) M σK σB σT γbar μ NA.τ NA.ρ NA.ρinf)
          (c1A NA Xa))
        (c1B NB (defaultInitB NA.n σK σB μ) Xb) ∧
      0 < max (max (sharpC2 NA.n NA.τ (cohConstR NA.n NA.τ) M σK σB σT γbar NA.τ NA.ρ NA.ρinf)
          (c2A NA Xa))
        (c2B NB (defaultInitB NA.n σK σB μ) Xb) ∧
      G1Body NA.n NA.τ NA.ρ NA.ρinf M σK σB σT μ γbar
        (min (min (sharpC1 NA.n NA.τ (cohConstR NA.n NA.τ) M σK σB σT γbar μ NA.τ NA.ρ NA.ρinf)
            (c1A NA Xa))
          (c1B NB (defaultInitB NA.n σK σB μ) Xb))
        (max (max (sharpC2 NA.n NA.τ (cohConstR NA.n NA.τ) M σK σB σT γbar NA.τ NA.ρ NA.ρinf)
            (c2A NA Xa))
          (c2B NB (defaultInitB NA.n σK σB μ) Xb)) := by
  have hσK0 : 0 < σK := hμ.trans hσK
  have hσB0 : 0 < σB := hμ.trans hσB
  obtain ⟨hA1, hA2, hA⟩ := g1_v2A_frozen hNA hfixA hΘA hτ hM hσK0 hσB0 hσT hμ hγA hsKA hM1A hM2A
    hOkA hXa hTs hcertA
  have hτ' : (NA.n : ℝ) - 1 ≤ NB.τ := hτB ▸ hτ
  have hcertB' : ∀ γ, 0 < γ → γ ≤ γbar → NB.Cert γ {ω | IsDiophantine γ NB.τ ω} := by
    rw [hτB]; exact hcertB
  obtain ⟨hB1, hB2, hB⟩ := g1_v2B_frozen hNB hfixB hτ' hM hσK hσB hσT hμ hγB hsKB hsBB hM1B
    hM2B hcTh hcDTh hI hfit hOkB hXb hcertB'
  rw [hτB, hρB, hρinfB] at hB1 hB2 hB
  have hc1B : 0 < c1B NB (defaultInitB NA.n σK σB μ) Xb := (lt_min_iff.1 hB1).2
  have hρ : 0 < NA.ρ := hρB ▸ hNB.ρ_pos
  refine ⟨lt_min hA1 hc1B, lt_max_of_lt_left hA2, ?_⟩
  by_cases hcase : min (sharpC1 NA.n NA.τ (cohConstR NA.n NA.τ) M σK σB σT γbar μ NA.τ NA.ρ NA.ρinf)
      (c1A NA Xa) ≤ c1B NB (defaultInitB NA.n σK σB μ) Xb
  · rw [min_eq_left hcase]
    exact G1V2.g1Body_mono hρ hA le_rfl (le_max_left _ _)
  · rw [min_eq_right (not_le.1 hcase).le]
    exact G1V2.g1Body_mono hρ hB (min_le_right _ _) (max_le_max_right _ (le_max_left _ _))

end KAM.Sharp2

end
