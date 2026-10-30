/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.ModStepB.SelfCons

/-!
# The repaired modified Newton step (`bp:p2s2:step`, route B)

`KAM.Sharp2.modified_stepB`: FH24's modified (composition) step `K̄ = (K + N ξᴺ) ∘ (id + ξᴸ)`
with the constants `stepConstsB` (SHARP2-B3B), the torsion against the initial torus
(`KAM.Sharp2.TorsionRef`) and option L10. The objects `modXiN0`, `modXiN`, `modKtilde`,
`modXiL`, `modNewton` are in `KAM.Sharp2.ModStepB.Defs`; the proof is in the parts
`ModStepB.Geo` (the current torus), `.Normal` (`ξᴺ`, `K̃`, `L̃`), `.Inter` (`Ẽ`, `η̃ᴺ`, `Ω_K̃`),
`.Comp` (`ξᴸ`, `K̄`), `.Frames` (`L̄`, `B̄`, `N̄`, `𝒯_ab`), `.NewErr` (`η̄ᴺ`, `η̄ᴸ`) and
`.SelfCons` (L10).

Two changes against `APOST-SHARP-V2-SIGNATURES.lean.txt` (SHARP2-B4B handoff, design signals):

* **Stage `0`** (audit AUDIT-SHARP2-FIX-iso-1, F1; orchestrator ruling): the constants use
  `C_E = min {C_E⁰, e/μ₀}` and `C_DE = min {C_DE⁰, n e/μ₀}` when `p.stage0`, which needs the
  frozen bound of `E` itself; the hypothesis `hE0 : p.stage0 = true → |E| ≤ p.ePer · μ on T_r`
  is added (vacuous for `stage0 = false`).
* **Standing data**: the five hypotheses `hopen`, `htransl`, `hholo`, `hper`, `hreal` are replaced
  by `hS : KAM.Apost.Standing n τ M σK σB σT 𝔅 h ω γ₀` (which contains them verbatim, plus
  `n ≥ 2`, `‖X_h‖ ≤ M` and `ω ∈ Dio_{γ₀,τ}`), as SHARP2-B2 did for
  `norm_lagrangeMat_le_etaN_of_standing`. The blueprint step assumes `ω ∈ Dio_{γ,τ}`; the
  regularity, periodicity, reality and the cohomological equation `∂_ω 𝓡g = g` of the solution
  operator `𝓡 = cohR` are proved in the library only for Diophantine `ω` (`SDConst` gives
  bounds only), and every frame identity used is stated under `Standing`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2

open KAM KAM.Torus KAM.Apost

variable {n : ℕ}

/-- Blueprint `bp:p2s2:step` (repaired, audit F4/F8): the actual bite `δ ≤ p.δ`; the standing
data of `h` (`Standing`: open translation-invariant domain, holomorphy, periodicity, reality,
`ω` Diophantine); `1 ≤ κ`; certificates at the actual bite, at a split bite and at a full bite
`b ≤ r`; current frame values `m ≤` caps with room for the increments; at stage `0` the frozen
bound of `E`. Conclusions: the new torus, its errors at `T_{r-3δ}`, the frames and the frame part
`𝒯_ab` of the torsion. -/
theorem modified_stepB (p : StepInB) {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)}
    {γ β εL εN δ r s c' b cb : ℝ} {m : Fin 5 → ℝ} {τ M σK σB σT γ₀ : ℝ}
    (hp : p.Ok) (hpn : p.n = n) (hfix : p.iso = false) (hγ : 0 < γ) (hγb : γ ≤ p.γb)
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
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hKr : IsRealOnReals K)
    (hball : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ 𝔅)
    (hL : ∀ θ ∈ complexStrip n r, ‖tangentMat K θ‖ ≤ m 0)
    (hLt : ∀ θ ∈ complexStrip n r, ‖(tangentMat K θ)ᵀ‖ ≤ m 1)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ m 2)
    (hN : ∀ θ ∈ complexStrip n r, ‖normalMat K θ‖ ≤ m 3)
    (hNt : ∀ θ ∈ complexStrip n r, ‖(normalMat K θ)ᵀ‖ ≤ m 4)
    (hT : ∀ θ ∈ complexStrip n (r - δ), ‖torsion h K ω θ‖ ≤ p.cTh * p.sNt * p.sN + p.ts)
    (hTa : IsUnit (torsionAverage h K ω).det ∧ ‖(torsionAverage h K ω)⁻¹‖ ≤ p.sT)
    (hηL : ∀ θ ∈ complexStrip n r, ‖etaL h K ω θ‖ ≤ εL)
    (hηN : ∀ θ ∈ complexStrip n r, ‖etaN h K ω θ‖ ≤ εN)
    (hE0 : p.stage0 = true → ∀ θ ∈ complexStrip n r,
      ‖invarianceError h K ω θ‖ ≤ p.ePer * max (εL / p.lam) (εN / (γ * δ ^ p.κ)))
    (hcond : stepCondB p (max (εL / p.lam) (εN / (γ * δ ^ p.κ)) / (γ * δ ^ (p.κ + 1))))
    (hβ : (stepConstsB p).CDK * max (εL / p.lam) (εN / (γ * δ ^ p.κ)) / (γ * δ ^ p.κ) < β)
    (hroom : let X := max (εL / p.lam) (εN / (γ * δ ^ p.κ)) / (γ * δ ^ (p.κ + 1))
      m 0 + p.n * (stepConstsB p).CDK * X ≤ p.sK ∧
      m 1 + 2 * p.n * (stepConstsB p).CDK * X ≤ p.sLt ∧
      m 2 + (stepConstsB p).CBb * X ≤ p.sB ∧ m 3 + (stepConstsB p).CNb * X ≤ p.sN ∧
      m 4 + (stepConstsB p).CNbT * X ≤ p.sNt) :
    let μ := max (εL / p.lam) (εN / (γ * δ ^ p.κ))
    let X := μ / (γ * δ ^ (p.κ + 1))
    let Kb := modNewton h K ω (r - 2 * δ)
    DifferentiableOn ℂ Kb (complexStrip n (r - 2 * δ)) ∧ IsPrimaryOnStrip Kb (r - 2 * δ) ∧
      IsRealOnReals Kb ∧
      (∀ θ ∈ complexStrip n (r - 2 * δ), ‖Kb θ - K θ‖ ≤ (stepConstsB p).CDK * μ / (γ * δ ^ p.κ)) ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ), ‖etaN h Kb ω θ‖ ≤ (stepConstsB p).QbN * μ ^ 2 / δ) ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ),
        ‖etaL h Kb ω θ‖ ≤ (stepConstsB p).QL * μ ^ 2 / (γ * δ ^ (p.κ + 1))) ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ),
        ‖tangentMat Kb θ - tangentMat K θ‖ ≤ p.n * (stepConstsB p).CDK * X ∧
        ‖(tangentMat Kb θ)ᵀ - (tangentMat K θ)ᵀ‖ ≤ 2 * p.n * (stepConstsB p).CDK * X) ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ), IsUnit (gramMatrix Kb θ).det ∧
        ‖(gramMatrix Kb θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤ (stepConstsB p).CBb * X) ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ), ‖normalMat Kb θ - normalMat K θ‖ ≤
          (stepConstsB p).CNb * X ∧
        ‖(normalMat Kb θ)ᵀ - (normalMat K θ)ᵀ‖ ≤ (stepConstsB p).CNbT * X) ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ),
        ‖torsionAB h Kb θ - torsionAB h K θ‖ ≤ (stepConstsB p).Cab * X) ∧
      (∀ θ ∈ complexStrip n (r - δ),
        ‖torsion h K ω θ - torsionAB h K θ‖ ≤ (stepConstsB p).Bsup * X) := by
  have hS' : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ₀ :=
    { hS with σK_pos := hp.caps.1, σB_pos := hp.caps.2.2.1, σT_pos := hp.caps.2.2.2.2.2 }
  have H : ModStepB.Hyp p 𝔅 h K ω Ω γ β εL εN δ r s c' b cb m :=
    { ok := hp, pn := hpn, fix := hfix, γ_pos := hγ, γ_le := hγb, δ_pos := hδ, δ_le := hδp,
      three := hr, mem := hω, cert := hc, s_pos := hs.1, s_lt := hs.2, cert' := hc',
      c1_le := hc1, b_ge := hb.1, b_le := hb.2, certb := hcb, cavg_le := hcavg,
      std := ⟨τ, M, γ₀, hS'⟩, dX := hdX, d2X := hd2X, comm := hcomm, lip := hlip, holo := hK,
      primary := hKp, real := hKr, ball := hball, L := hL, Lt := hLt, G := hG, N := hN,
      Nt := hNt, T := hT, Ta := hTa, ηL := hηL, ηN := hηN, E0 := hE0, cond := hcond,
      β_gt := hβ, room := hroom }
  intro μ X Kb
  have hpn' : (p.n : ℝ) = n := by rw [hpn]
  refine ⟨H.Kb_holo hS', H.Kb_primary hS', H.Kb_real hS', fun θ hθ => ?_, H.etaNb_le hS',
    H.etaLb_le hS', fun θ hθ => ?_, fun θ hθ => ⟨(H.Gb hS' θ hθ).1, (H.Gb hS' θ hθ).2.1⟩,
    fun θ hθ => (H.Nb_sub_le hS' θ hθ).1, H.torsionAB_sub_le hS', H.torsion_sub_le hS'⟩
  · exact (H.Kb_sub_le hS' θ hθ).trans_eq (mul_div_assoc _ _ _).symm
  · obtain ⟨h1, h2⟩ := H.Lb_sub_le hS' θ hθ
    rw [← Matrix.transpose_sub]
    refine ⟨h1.trans_eq ?_, h2.trans_eq ?_⟩
    · rw [hpn']; exact (mul_assoc _ _ _).symm
    · rw [hpn']; exact (mul_assoc _ _ _).symm

end KAM.Sharp2

end
