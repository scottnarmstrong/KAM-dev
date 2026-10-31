/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.Ref.Local
public import KAM.Sharp2.RouteA.Step
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Lever L8′ of route A: the step

`Ref.step_core` is the additive step `KAM.Sharp2.RouteA.step_A` without its two conclusions on the
torsion of the new torus: no Neumann condition for `⟨T̄⟩` and no cap of `|⟨T⟩⁻¹|` or `|T|`. Its
torsion output is the change of `𝒯_ab` alone. The bounds of `T` and `⟨T⟩⁻¹` are hypotheses, and
at the next stage they come from `Ref.AdmR.entry`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2.RouteA

open KAM KAM.Torus KAM.Apost KAM.Sharp

/-- `Cond.facts` without the Neumann condition of `⟨T̄⟩`. -/
theorem StepInA.Cond0.facts {p : StepInA} {γ : ℝ} (hp : p.Pos) {δ ε : ℝ} (hγ : 0 < γ)
    (hγb : γ ≤ p.γb) (hδ : 0 < δ) (hδD : δ ≤ p.δ) (hε : 0 ≤ ε)
    (hC : p.Cond0 (ε / (γ ^ 4 * δ ^ (2 * (2 * p.κ))))) :
    ε ≤ δ ∧ p.CSym * (ε / (γ * δ ^ (p.κ + 1))) ≤ 1 / 2 ∧
      p.CE * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) ≤ ε ∧
      p.sB * (p.CGr * (p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))) ≤ p.th := by
  obtain ⟨-, -, -, -, s5, s6, s7, -⟩ := scales (ε := ε) (κ := p.κ) hγ hδ
  have hκ := hp.κ_ge
  set x := ε / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) with hx
  have hx0 : 0 ≤ x := div_nonneg hε (by positivity)
  have b4 := mul_le_mul_of_nonneg_right
    (pow_mul_rpow_le (j := 2 * (2 * p.κ) - 1) 4 hγ hγb hδ hδD (by linarith)) hx0
  have b3 := mul_le_mul_of_nonneg_right
    (pow_mul_rpow_le (j := 3 * p.κ - 1) 3 hγ hγb hδ hδD (by linarith)) hx0
  have b2 := mul_le_mul_of_nonneg_right
    (pow_mul_rpow_le (j := 2 * p.κ - 1) 2 hγ hγb hδ hδD (by linarith)) hx0
  have hE : p.CE * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) = ε * (p.CE * x) := by
    rw [hx]; ring
  have hX : ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)) ≤ p.γb ^ 2 * p.δ ^ (2 * p.κ - 1) * x := by
    rw [s5]; exact b2
  have hB0 := hp.sB
  have hG0 := hp.CGr
  have hDK0 := hp.CDK
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : ε / δ ≤ 1 := by
      rw [s6]
      refine b4.trans ?_
      have := hC.err
      linarith
    exact (div_le_one hδ).1 this
  · rw [s7]
    calc p.CSym * ((γ ^ 3 * δ ^ (3 * p.κ - 1)) * x) ≤
          p.CSym * (p.γb ^ 3 * p.δ ^ (3 * p.κ - 1) * x) :=
          mul_le_mul_of_nonneg_left b3 hp.CSym
      _ = p.CSym * (p.γb ^ 3 * p.δ ^ (3 * p.κ - 1)) * x := by ring
      _ ≤ 1 / 2 := hC.sym
  · rw [hE]
    exact mul_le_of_le_one_right hε hC.quad
  · calc p.sB * (p.CGr * (p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))) ≤
        p.sB * (p.CGr * (p.CDK * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1) * x))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hX hDK0) hG0) hB0
      _ = p.sB * p.CGr * p.CDK * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x := by ring
      _ ≤ p.th := hC.gram

namespace Ref

variable {n : ℕ} {τ M : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

/-- The additive step, with the change of `𝒯_ab` in place of the bounds of the new torsion. -/
theorem step_core {p : StepInA} (hp : p.Pos) (hfix : p.iso = false) (hΘ : p.Θ = 0) (hpn : p.n = n)
    (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ)
    (hd1 : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ p.M1)
    (hd2 : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ p.M2)
    (hγb : γ ≤ p.γb) {Ω : Set (Fin n → ℝ)} (hω : ω ∈ Ω)
    {r β ε δ b cb mK mB mLt mN mNt : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : AdmA 𝔅 h ω r (r - δ) β ε mK mB p.sT mLt mN mNt p.t K)
    (hδ : 0 < δ) (hδD : δ ≤ p.δ) (h3δ : 3 * δ < r)
    (hc : SDConst n p.κ γ δ p.c Ω) (hcb : SDConst n p.κ γ b cb Ω) (hbr : b ≤ r)
    (hca : cb * b ^ (-p.κ) ≤ p.ca * δ ^ (-p.κ))
    (hcond : p.Cond0 (ε / (γ ^ 4 * δ ^ (2 * (2 * p.κ)))))
    (hβ : p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) < β)
    (hcK : mK + n * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sK)
    (hcB : mB + p.CB * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sB)
    (hcLt : mLt + 2 * n * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sLt)
    (hcN : mN + p.CNd * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sN)
    (hcNt : mNt + p.CNtd * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sNt) :
    Adm0 𝔅 h ω (r - 3 * δ) (β - p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ))))
        (p.CE * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))))
        (mK + n * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mB + p.CB * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mLt + 2 * n * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mN + p.CNd * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mNt + p.CNtd * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (newtonMap h K ω (r - 2 * δ)) ∧
      p.CE * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) ≤ ε ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ),
        ‖newtonMap h K ω (r - 2 * δ) θ - K θ‖ ≤ p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
        ‖fderiv ℂ (newtonMap h K ω (r - 2 * δ)) θ - fderiv ℂ K θ‖ ≤
          n * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)))) ∧
      ∀ θ ∈ complexStrip n (r - 3 * δ),
        ‖torsionAB h (newtonMap h K ω (r - 2 * δ)) θ - torsionAB h K θ‖ ≤
          p.CDab * (p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)))) := by
  have hr := hK.r_pos
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hδ1 : δ ≤ 1 := hδD.trans hp.δ1
  obtain ⟨hεδ, hsym, hE, hgr⟩ := hcond.facts hp hγ hγb hδ hδD hε0
  have hε1 : ε ≤ 1 := hεδ.trans hδ1
  obtain ⟨-, -, -, s4, -, -, -, s8⟩ := scales (ε := ε) (κ := p.κ) hγ hδ
  obtain ⟨-, -, s3, -, -, -, -, -⟩ := scales (ε := ε) (κ := p.κ) hγ hδ
  set E := ε / (γ ^ 2 * δ ^ (2 * p.κ)) with hEd
  set X := ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)) with hXd
  have hX0 : 0 ≤ X := div_nonneg hε0 (by positivity)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hDK0 := hp.CDK
  -- the budgets: `m ≤ cap`
  have hr1 : 0 ≤ (n : ℝ) * p.CDK * X := by positivity
  have hr2 : 0 ≤ p.CB * p.CDK * X := mul_nonneg (mul_nonneg hp.CB hDK0) hX0
  have hr4 : 0 ≤ 2 * (n : ℝ) * p.CDK * X := by positivity
  have hr5 : 0 ≤ p.CNd * p.CDK * X := mul_nonneg (mul_nonneg hp.CNd hDK0) hX0
  have hr6 : 0 ≤ p.CNtd * p.CDK * X := mul_nonneg (mul_nonneg hp.CNtd hDK0) hX0
  have hK0 : AdmA 𝔅 h ω r (r - δ) β ε p.sK p.sB p.sT p.sLt p.sN p.sNt p.t K :=
    hK.mono (by linarith) (by linarith) le_rfl (by linarith) (by linarith) (by linarith) le_rfl
  have h2δ : 2 * δ < r := by linarith
  have hr3 : 0 < r - 3 * δ := by linarith
  have hsub : complexStrip n (r - 2 * δ) ⊆ complexStrip n r :=
    Triangular.strip_mono (by linarith)
  have hsub32 : complexStrip n (r - 3 * δ) ⊆ complexStrip n (r - 2 * δ) :=
    Triangular.strip_mono (by linarith)
  have hsub3r : complexStrip n (r - 3 * δ) ⊆ complexStrip n r := hsub32.trans hsub
  have hsub31 : complexStrip n (r - 3 * δ) ⊆ complexStrip n (r - δ) :=
    Triangular.strip_mono (by linarith)
  have hAd := hK0.toAdmissible hε1
  obtain ⟨⟨-, -, -, hcd, hcp, hcr⟩, -⟩ := correction_spec hS hAd hδ hδ1 h2δ
  obtain ⟨hdist', hΩ, herr⟩ := newton_error_boundsA hp hfix hΘ hpn hS hd2 hγb hω hK0 hδ hδD h2δ hε1
    hc hcb hbr hca hβ hsym
  set K' := newtonMap h K ω (r - 2 * δ) with hK'def
  have hdiff : DifferentiableOn ℂ K' (complexStrip n (r - 2 * δ)) :=
    KAM.Apost.Step.newtonMap_differentiableOn (hK.holo.mono hsub) hcd
  have hdist : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖K' θ - K θ‖ ≤ p.CDK * E := fun θ hθ => by
    rw [hK'def, NewtonError.newtonMap_of_mem hθ, add_sub_cancel_left]
    exact hdist' θ hθ
  have hD : p.CDK * E / δ = p.CDK * X := by
    rw [s3]; field_simp
  have hball : ∀ θ ∈ complexStrip n (r - 2 * δ), Metric.ball (K' θ) (β - p.CDK * E) ⊆ 𝔅 :=
    fun θ hθ => PerturbationAux.ball_subset_of_close (hK.ball_sub θ (hsub hθ)) (hdist θ hθ)
  have hβ' : 0 < β - p.CDK * E := by linarith
  have hK'𝔅 : ∀ θ ∈ complexStrip n (r - 2 * δ), K' θ ∈ 𝔅 := fun θ hθ =>
    hball θ hθ (Metric.mem_ball_self hβ')
  -- the frames
  have hLθ : ∀ θ ∈ complexStrip n r, ‖tangentMat K θ‖ ≤ p.sK := fun θ hθ => hK0.tangent_le hθ
  have hfr := frames_bar hp hpn hK.holo hLθ hK.gram hK.tangentT (by linarith) (by linarith) hδ hdiff
    hdist (by rw [hD]; exact hgr) (by rw [hD]; linarith) (by rw [hD]; linarith)
  rw [hD] at hfr
  have hL'θ : ∀ θ ∈ complexStrip n (r - 3 * δ), ‖fderiv ℂ K' θ‖ ≤ mK + n * p.CDK * X := fun θ hθ =>
      by
    have := norm_le_add_sub (hK.deriv_le θ (hsub3r hθ)) (hfr θ hθ).dDK
    rwa [← mul_assoc] at this
  have hLt'θ : ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖(tangentMat K' θ)ᵀ‖ ≤ mLt + 2 * n * p.CDK * X := fun θ hθ => by
    have e : (tangentMat K' θ)ᵀ = (tangentMat K θ)ᵀ + (tangentMat K' θ - tangentMat K θ)ᵀ := by
      rw [Matrix.transpose_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add (hK.tangentT θ (hsub3r hθ)) ?_)
    exact (hfr θ hθ).dLt.trans_eq (by ring)
  have hB'θ : ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖(gramMatrix K' θ)⁻¹‖ ≤ mB + p.CB * p.CDK * X := fun θ hθ => by
    have := norm_le_add_sub (hK.gram θ (hsub3r hθ)).2 (hfr θ hθ).dB
    rwa [← mul_assoc] at this
  have hN'θ : ∀ θ ∈ complexStrip n (r - 3 * δ), ‖normalMat K' θ‖ ≤ mN + p.CNd * p.CDK * X :=
    fun θ hθ => by
      have := norm_le_add_sub (hK.normal θ (hsub3r hθ)) (hfr θ hθ).dN
      rwa [← mul_assoc] at this
  have hNt'θ : ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖(normalMat K' θ)ᵀ‖ ≤ mNt + p.CNtd * p.CDK * X := fun θ hθ => by
    have := norm_le_add_sub (hK.normalT θ (hsub3r hθ)) (hfr θ hθ).dNt
    rwa [← mul_assoc] at this
  -- the torsion
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  have hG'3 : ∀ θ ∈ complexStrip n (r - 3 * δ), IsUnit (gramMatrix K' θ).det :=
    fun θ hθ => (hfr θ hθ).unit
  have hab : ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖torsionAB h K' θ - torsionAB h K θ‖ ≤ p.CDab * (p.CDK * X) := fun θ hθ => by
    have := torsionAB_sub_le hp hpn hS hd1 hd2 (K := K) (K' := K') (β := β) (d := p.CDK * E)
      (δ := δ) hδ hδD (hK.mem θ (hsub3r hθ)) (hK'𝔅 θ (hsub32 hθ)) (hK.ball_sub θ (hsub3r hθ))
      (hdist θ (hsub32 hθ)) hβ (hK0.normalT θ (hsub3r hθ)) ((hN'θ θ hθ).trans hcN)
      (by rw [hD]; exact hfr θ hθ)
    rwa [hD] at this
  refine ⟨?_, hE, fun θ hθ => ⟨hdist θ (hsub32 hθ), ?_⟩, hab⟩
  · exact
      { r_pos := hr3
        β_pos := hβ'
        ε_nonneg := by
          have h1 : 0 ≤ p.CE * ε ^ 2 := mul_nonneg hp.CE (sq_nonneg _)
          positivity
        holo := hdiff.mono hsub32
        primary := fun θ hθ k =>
          (KAM.Apost.Step.newtonMap_isPrimaryOnStrip (by linarith) hK.primary hcp) θ (hsub32 hθ) k
        real := KAM.Apost.Step.newtonMap_isRealOnReals (by linarith) hK.real hcr
        ball_sub := fun θ hθ => hball θ (hsub32 hθ)
        deriv_le := hL'θ
        gram := fun θ hθ => ⟨hG'3 θ hθ, hB'θ θ hθ⟩
        tangentT := hLt'θ
        normal := hN'θ
        normalT := hNt'θ
        error_le := fun θ hθ => herr θ (hsub32 hθ) }
  · have := (hfr θ hθ).dDK
    rwa [← mul_assoc] at this

end Ref

end KAM.Sharp2.RouteA

end
