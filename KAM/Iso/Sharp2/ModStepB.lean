/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.ModStepB.Energy

/-!
# The bordered modified Newton step (`bpI:p2s2:step`, route B)

`KAM.Iso.Sharp2.modified_stepIB`: the isoenergetic form of `KAM.Sharp2.modified_stepB`, with the
frequency correction `ω̄ = (1 - ξ^ω) ω` of HL19 §6 and the constants `stepConstsB` at `p.iso = true`
(`bpI:p2s2:constants`). The objects `xiNI`, `tilK`, `gLI`, `xiLI`, `newK`, `newOmega` are in
`ModStepB.Defs`; the proof is in the parts `ModStepB.Geo` (the current torus), `.Normal` (the
bordered system, `ξᴺ`, `ξ^ω`, `K̃`, `L̃`), `.Inter` (`Ẽ`, `η̃ᴺ`, `Ω_K̃`), `.Comp` (`ξᴸ`, `K̄`),
`.Frames` (`L̄`, `B̄`, `N̄`, `𝒯_ab`), `.NewErr` (`η̄ᴺ`, `η̄ᴸ`), `.SelfCons` (L10) and `.Energy`
(`Ē^ω`).

The parts are parallel to `KAM/Sharp2/ModStepB`, and not a reuse of it, by necessity: every lemma of
`ModStepB.Hyp` there depends on a bundle containing `⟨T⟩` invertible and `p.iso = false`, while
here only the bordered average `⟨𝖳⟩` is invertible (`⟨T⟩` may be singular). The lemmas independent
of the bundle are reused.

The weighted error is `muI`, with `λ_ω`; the bundle `ModStepB.Hyp` is applied with
`ε_L = λ μ`, `ε_N = γ δ^κ μ`, for which its two-term `μ` is this one.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Sharp2

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Iso.Linear KAM.Iso.Apost

variable {n : ℕ}

namespace ModStepB

/-- The weighted error `μ = max {|ηᴸ|/λ, |ηᴺ|/(γ δ^κ), |E^ω|/λ_ω}`. -/
def muI (p : StepInB) (γ εL εN εω δ : ℝ) : ℝ :=
  max (max (εL / p.lam) (εN / (γ * δ ^ p.κ))) (εω / p.lamW)

/-- The normalized error `X = μ/(γ δ^{κ+1})`. -/
def xI (p : StepInB) (γ εL εN εω δ : ℝ) : ℝ := muI p γ εL εN εω δ / (γ * δ ^ (p.κ + 1))

/-- The bordered average of `isoBordData` is the frozen extended torsion average. -/
theorem bordAvg_eq_extended {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ω : Fin n → ℝ} {E₀ r β τ M σK σB σT γ₀ : ℝ} (hS : Standing n τ M σK σB σT 𝔅 h ω γ₀)
    (hdH : ∃ A : ℝ, ∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ A) (hr : 0 < r) (hβ : 0 < β)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hKr : IsRealOnReals K) (hball : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ 𝔅)
    (hdK : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ σK)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB) :
    bordAvg ω (isoBordData h K ω E₀) = KAM.Iso.extendedTorsionAverage h K ω := by
  obtain ⟨A, hA⟩ := hdH
  have hle : M ≤ max M A := le_max_left _ _
  have hSet : Setting n τ (max M A) σK σB σT 𝔅 h ω γ₀ :=
    { hS with
      M_pos := hS.M_pos.trans_le hle
      bounds := fun z hz => ⟨(hS.bounds z hz).1.trans hle, (hS.bounds z hz).2.1.trans hle,
        (hS.bounds z hz).2.2.trans hle⟩
      dH_le := fun z hz => (hA z hz).trans (le_max_right _ _) }
  have hKD : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅 := fun θ hθ =>
    hball θ hθ (Metric.mem_ball_self hβ)
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hTc⟩, -, -, -⟩ :=
    frame_basic hS hr hβ hK hball hdK hG
  obtain ⟨⟨-, -, -, -, -, -, -, havg, -⟩, -⟩ :=
    extended_basic hSet hr hK hKp hKr hKD fun θ hθ => (hG θ hθ).1
  rw [havg, torsionAverage_eq_avg h K ω hTc]
  rfl

namespace Hyp

variable {p : StepInB} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)}
  {E₀ γ β εL εN δ r s c' b cb : ℝ} {m : Fin 5 → ℝ}
  (H : Hyp p 𝔅 h K ω E₀ Ω γ β εL εN δ r s c' b cb m)
  {τ M γ₀ : ℝ} (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ₀)
include H hS

/-- `|ω̄ - ω| ≤ Θ C_0 μ`. -/
theorem newOmega_sub_le :
    ‖newOmega h K ω E₀ - ω‖ ≤ sCnu p * KAM.Sharp2.ModStepB.mu p γ εL εN δ := by
  have e : newOmega h K ω E₀ - ω = (-xw h K ω E₀) • ω := by
    rw [newOmega, sub_smul, one_smul, neg_smul]
    abel
  rw [e, norm_smul, sCnu]
  simp only [H.iso, ↓reduceIte, Real.norm_eq_abs, abs_neg]
  calc _ ≤ sC0 p * KAM.Sharp2.ModStepB.mu p γ εL εN δ * p.Θ :=
        mul_le_mul (H.abs_xw_le hS) H.Θ (norm_nonneg _)
          (mul_nonneg (nn_sC0 H.ok) H.mu_nonneg)
    _ = _ := by ring

end Hyp

end ModStepB

open ModStepB in
/-- Blueprint `bpI:p2s2:step`: the hypotheses of `KAM.Sharp2.modified_stepB` with the iso fields
(`p.iso = true`): the frozen bordered torsion `⟨𝖳⟩` instead of `⟨T⟩`, the bound of `Y`, of `|ω|`, of
`DH` and of `D²H`, and the energy error `|⟨H ∘ K⟩ - E₀| ≤ ε_ω` with its weight `λ_ω`. Conclusions:
the new torus at the new frequency `ω̄ = (1 - ξ^ω) ω`, the frequency increment, its errors (with the
new energy error `Q_ω μ²/(γ δ^{κ+1})`) at `T_{r-3δ}`, the frames and the frame part `𝒯_ab` of the
torsion. -/
theorem modified_stepIB (p : StepInB) {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)}
    {E₀ γ β εL εN εω δ r s c' b cb : ℝ} {m : Fin 5 → ℝ} {τ M σK σB σT γ₀ : ℝ}
    (hp : p.Ok) (hpn : p.n = n) (hiso : p.iso = true) (hγ : 0 < γ) (hγb : γ ≤ p.γb)
    (hδ : 0 < δ) (hδp : δ ≤ p.δ)
    (hr : 3 * δ < r) (hω : ω ∈ Ω)
    (hc : SDConst n p.κ γ δ p.c Ω)
    (hs : 0 < s ∧ s < 1) (hc' : SDConst n p.κ γ (s * δ) c' Ω)
    (hc1 : c' / (s ^ p.κ * (1 - s)) ≤ p.c1)
    (hb : δ ≤ b ∧ b ≤ r) (hcb : SDConst n p.κ γ b cb Ω) (hcavg : cb * (δ / b) ^ p.κ ≤ p.cavg)
    (hS : Standing n τ M σK σB σT 𝔅 h ω γ₀)
    (hdX : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ p.M1)
    (hd2X : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ p.M2)
    (hcomm : ∀ z ∈ 𝔅, ‖hamComm h z‖ ≤ p.cTh)
    (hlip : ∀ z ∈ 𝔅, ∀ z' ∈ 𝔅, segment ℝ z z' ⊆ 𝔅 →
      ‖hamComm h z - hamComm h z'‖ ≤ p.cDTh * ‖z - z'‖)
    (hdH : ∃ A : ℝ, ∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ A)
    (hd2H : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 h z‖ ≤ p.Mh2)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hKr : IsRealOnReals K)
    (hball : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ 𝔅)
    (hL : ∀ θ ∈ complexStrip n r, ‖tangentMat K θ‖ ≤ m 0)
    (hLt : ∀ θ ∈ complexStrip n r, ‖(tangentMat K θ)ᵀ‖ ≤ m 1)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ m 2)
    (hN : ∀ θ ∈ complexStrip n r, ‖normalMat K θ‖ ≤ m 3)
    (hNt : ∀ θ ∈ complexStrip n r, ‖(normalMat K θ)ᵀ‖ ≤ m 4)
    (hT : ∀ θ ∈ complexStrip n (r - δ), ‖torsion h K ω θ‖ ≤ p.cTh * p.sNt * p.sN + p.ts)
    (hTa : IsUnit (KAM.Iso.extendedTorsionAverage h K ω).det ∧
      ‖(KAM.Iso.extendedTorsionAverage h K ω)⁻¹‖ ≤ p.sT)
    (hY : ∀ θ ∈ complexStrip n (r - δ), ∑ b, ‖energyRow h K θ b‖ ≤ p.y0)
    (hΘ : ‖ω‖ ≤ p.Θ)
    (hηL : ∀ θ ∈ complexStrip n r, ‖etaL h K ω θ‖ ≤ εL)
    (hηN : ∀ θ ∈ complexStrip n r, ‖etaN h K ω θ‖ ≤ εN)
    (hηω : ‖KAM.Iso.energyAverage h K - (E₀ : ℂ)‖ ≤ εω)
    (hE0 : p.stage0 = true → ∀ θ ∈ complexStrip n r,
      ‖invarianceError h K ω θ‖ ≤ p.ePer * muI p γ εL εN εω δ)
    (hcond : stepCondB p (xI p γ εL εN εω δ))
    (hβ : (stepConstsB p).CDK * muI p γ εL εN εω δ / (γ * δ ^ p.κ) < β)
    (hroom : m 0 + p.n * (stepConstsB p).CDK * xI p γ εL εN εω δ ≤ p.sK ∧
      m 1 + 2 * p.n * (stepConstsB p).CDK * xI p γ εL εN εω δ ≤ p.sLt ∧
      m 2 + (stepConstsB p).CBb * xI p γ εL εN εω δ ≤ p.sB ∧
      m 3 + (stepConstsB p).CNb * xI p γ εL εN εω δ ≤ p.sN ∧
      m 4 + (stepConstsB p).CNbT * xI p γ εL εN εω δ ≤ p.sNt) :
    let μ := muI p γ εL εN εω δ
    let X := xI p γ εL εN εω δ
    let Kb := newK h K ω E₀ (r - 2 * δ)
    let ωb := newOmega h K ω E₀
    DifferentiableOn ℂ Kb (complexStrip n (r - 2 * δ)) ∧ IsPrimaryOnStrip Kb (r - 2 * δ) ∧
      IsRealOnReals Kb ∧
      (∀ θ ∈ complexStrip n (r - 2 * δ), ‖Kb θ - K θ‖ ≤ (stepConstsB p).CDK * μ / (γ * δ ^ p.κ)) ∧
      ‖ωb - ω‖ ≤ (stepConstsB p).Cnu * μ ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ), ‖etaN h Kb ωb θ‖ ≤ (stepConstsB p).QbN * μ ^ 2 / δ) ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ),
        ‖etaL h Kb ωb θ‖ ≤ (stepConstsB p).QL * μ ^ 2 / (γ * δ ^ (p.κ + 1))) ∧
      ‖KAM.Iso.energyAverage h Kb - (E₀ : ℂ)‖ ≤ sQw p * μ ^ 2 / (γ * δ ^ (p.κ + 1)) ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ),
        ‖tangentMat Kb θ - tangentMat K θ‖ ≤ p.n * (stepConstsB p).CDK * X ∧
        ‖(tangentMat Kb θ)ᵀ - (tangentMat K θ)ᵀ‖ ≤ 2 * p.n * (stepConstsB p).CDK * X) ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ), IsUnit (gramMatrix Kb θ).det ∧
        ‖(gramMatrix Kb θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤ (stepConstsB p).CBb * X) ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ), ‖normalMat Kb θ - normalMat K θ‖ ≤
          (stepConstsB p).CNb * X ∧
        ‖(normalMat Kb θ)ᵀ - (normalMat K θ)ᵀ‖ ≤ (stepConstsB p).CNbT * X) ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ),
        ‖torsionAB h Kb θ - torsionAB h K θ‖ ≤ sCab0 p * X) ∧
      (∀ θ ∈ complexStrip n (r - δ),
        ‖torsion h K ω θ - torsionAB h K θ‖ ≤ (stepConstsB p).Bsup * X) := by
  have hS' : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ₀ :=
    { hS with σK_pos := hp.caps.1, σB_pos := hp.caps.2.2.1, σT_pos := hp.caps.2.2.2.2.2 }
  have hgd : 0 < γ * δ ^ p.κ := mul_pos hγ (Real.rpow_pos_of_pos hδ _)
  have hgd1 : 0 < γ * δ ^ (p.κ + 1) := mul_pos hγ (Real.rpow_pos_of_pos hδ _)
  have hlam := hp.lam.1
  have hlamW := hp.lam.2.2.1
  have hr0 : 0 < r := by linarith
  have h0 : (0 : Fin n → ℂ) ∈ complexStrip n r := fun i => by simpa using hr0
  set μ := muI p γ εL εN εω δ with hμd
  have hμL : εL / p.lam ≤ μ := (le_max_left _ _).trans (le_max_left _ _)
  have hμN : εN / (γ * δ ^ p.κ) ≤ μ := (le_max_right _ _).trans (le_max_left _ _)
  have hμω : εω / p.lamW ≤ μ := le_max_right _ _
  have hμ0 : 0 ≤ μ := (div_nonneg ((norm_nonneg _).trans (hηL 0 h0)) hlam.le).trans hμL
  have hmu : KAM.Sharp2.ModStepB.mu p γ (p.lam * μ) (γ * δ ^ p.κ * μ) δ = μ := by
    rw [KAM.Sharp2.ModStepB.mu, mul_div_cancel_left₀ _ hlam.ne',
      mul_div_cancel_left₀ _ hgd.ne', max_self]
  have hX : KAM.Sharp2.ModStepB.xX p γ (p.lam * μ) (γ * δ ^ p.κ * μ) δ =
      xI p γ εL εN εω δ := by
    rw [KAM.Sharp2.ModStepB.xX, hmu, xI]
  have hX0 : 0 ≤ xI p γ εL εN εω δ := div_nonneg hμ0 hgd1.le
  have hβ0 : 0 < β := lt_of_le_of_lt
    (div_nonneg (mul_nonneg (stepConstsB_nonneg hp).2.1 hμ0) hgd.le) hβ
  have hm0 : m 0 ≤ p.sK := by
    have : 0 ≤ (p.n : ℝ) * (stepConstsB p).CDK * xI p γ εL εN εω δ :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (stepConstsB_nonneg hp).2.1) hX0
    linarith [hroom.1]
  have hm2 : m 2 ≤ p.sB := by
    have : 0 ≤ (stepConstsB p).CBb * xI p γ εL εN εω δ :=
      mul_nonneg (stepConstsB_nonneg hp).2.2.1 hX0
    linarith [hroom.2.2.1]
  have hbord : bordAvg ω (isoBordData h K ω E₀) = KAM.Iso.extendedTorsionAverage h K ω :=
    bordAvg_eq_extended hS' hdH hr0 hβ0 hK hKp hKr hball
      (fun θ hθ => by rw [← norm_colMat]; exact (hL θ hθ).trans hm0)
      fun θ hθ => ⟨(hG θ hθ).1, (hG θ hθ).2.trans hm2⟩
  have H : ModStepB.Hyp p 𝔅 h K ω E₀ Ω γ β (p.lam * μ) (γ * δ ^ p.κ * μ) δ r s c' b cb m :=
    { ok := hp, pn := hpn, iso := hiso, γ_pos := hγ, γ_le := hγb, δ_pos := hδ, δ_le := hδp,
      three := hr, mem := hω, cert := hc, s_pos := hs.1, s_lt := hs.2, cert' := hc',
      c1_le := hc1, b_ge := hb.1, b_le := hb.2, certb := hcb, cavg_le := hcavg,
      std := ⟨τ, M, γ₀, hS'⟩, dX := hdX, d2X := hd2X, comm := hcomm, lip := hlip, holo := hK,
      primary := hKp, real := hKr, ball := hball, L := hL, Lt := hLt, G := hG, N := hN,
      Nt := hNt, T := hT, Ta := by rw [hbord]; exact hTa, Y := hY, Θ := hΘ, dH := hdH,
      d2H := hd2H
      ηω := by
        rw [hmu]
        calc _ ≤ εω := hηω
          _ = p.lamW * (εω / p.lamW) := (mul_div_cancel₀ _ hlamW.ne').symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hμω hlamW.le
      ηL := fun θ hθ => by
        calc _ ≤ εL := hηL θ hθ
          _ = p.lam * (εL / p.lam) := (mul_div_cancel₀ _ hlam.ne').symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hμL hlam.le
      ηN := fun θ hθ => by
        calc _ ≤ εN := hηN θ hθ
          _ = (γ * δ ^ p.κ) * (εN / (γ * δ ^ p.κ)) := (mul_div_cancel₀ _ hgd.ne').symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hμN hgd.le
      E0 := by rw [hmu]; exact hE0
      cond := by rw [hX]; exact hcond
      β_gt := by rw [hmu]; exact hβ
      room := by rw [hX]; exact hroom }
  intro X Kb ωb
  have hpn' : (p.n : ℝ) = n := by rw [hpn]
  have c_Kb := H.Kb_sub_le hS'
  have c_ω := H.newOmega_sub_le hS'
  have c_N := H.etaNb_le hS'
  have c_L := H.etaLb_le hS'
  have c_E := H.energyAverage_Kb_sub_le hS'
  have c_F := H.Lb_sub_le hS'
  have c_G := H.Gb hS'
  have c_Nb := H.Nb_sub_le hS'
  have c_ab := H.torsionAB_sub_le hS'
  have c_T := H.torsion_sub_le hS'
  rw [hmu] at c_Kb c_ω c_N c_L c_E
  rw [hX] at c_F c_G c_Nb c_ab c_T
  refine ⟨H.Kb_holo hS', H.Kb_primary hS', H.Kb_real hS', fun θ hθ => ?_, c_ω, c_N, c_L, c_E,
    fun θ hθ => ?_, fun θ hθ => ⟨(c_G θ hθ).1, (c_G θ hθ).2.1⟩, fun θ hθ => (c_Nb θ hθ).1, c_ab,
    c_T⟩
  · exact (c_Kb θ hθ).trans_eq (mul_div_assoc _ _ _).symm
  · obtain ⟨h1, h2⟩ := c_F θ hθ
    rw [← Matrix.transpose_sub]
    refine ⟨h1.trans_eq ?_, h2.trans_eq ?_⟩
    · rw [hpn']; exact (mul_assoc _ _ _).symm
    · rw [hpn']; exact (mul_assoc _ _ _).symm

end KAM.Iso.Sharp2

end
