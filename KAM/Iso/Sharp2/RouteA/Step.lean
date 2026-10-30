/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.RouteA.NewtonError
public import KAM.Sharp2.RouteA.Step
public import KAM.Iso.Sharp.Twist
public import KAM.Iso.Apost.Torsion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The additive step of the isoenergetic route A

`step_IA`: one step `(K, s) ↦ (K̄, s̄)` from an admissible pair, each cap increased by its rate, with the
ray margin decreased by `C_Δω E`. The torsion of the new pair is bounded by `torsion_sub_le` for the two
frequencies `s ω*`, `s̄ ω*`; the bordered torsion adds the blocks `Δω` and `ΔY`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Sharp2.RouteA

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp

variable {n : ℕ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {ωstar : Fin n → ℝ} {τ M σω ν γ : ℝ}

/-- The additive step of the isoenergetic route A. -/
theorem step_IA {p : StepInA} (hp : p.Pos) (hiso : p.iso = true) (hpn : p.n = n)
    (hS : IsoStanding n τ M p.sK p.sB p.sT σω ν ωstar D H γ)
    (hd1 : ∀ z ∈ D, ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ p.M1)
    (hd2 : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ p.M2)
    (hd2H : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ p.Mh2) {Mh1 : ℝ}
    (hdH : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ Mh1) (hHYv : p.HY = Mh1 * p.sN) (hγb : γ ≤ p.γb)
    {Ω : Set (Fin n → ℝ)} {E₀ r β ε δ b cb s ν' mK mB mT mLt mN mNt mH : ℝ} (hω : s • ωstar ∈ Ω)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : AdmIA D H ωstar E₀ r (r - δ) β ε s mK mB mT mLt mN mNt mH K)
    (hδ : 0 < δ) (hδD : δ ≤ p.δ) (h3δ : 3 * δ < r) (hΘ : ‖s • ωstar‖ ≤ p.Θ)
    (hc : SDConst n p.κ γ δ p.c Ω) (hcb : SDConst n p.κ γ b cb Ω) (hbr : b ≤ r)
    (hca : cb * b ^ (-p.κ) ≤ p.ca * δ ^ (-p.κ))
    (hcond : p.Cond (ε / (γ ^ 4 * δ ^ (2 * (2 * p.κ)))))
    (hβ : p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) < β)
    (hray : ν' ≤ rayMargin σω ωstar s)
    (hνd : p.CDw * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) < ν')
    (hcK : mK + n * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sK)
    (hcB : mB + p.CB * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sB)
    (hcT : mT + p.rT * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sT)
    (hcLt : mLt + 2 * n * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sLt)
    (hcN : mN + p.CNd * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sN)
    (hcNt : mNt + p.CNtd * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sNt)
    (hcH : mH + p.CDT * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.t) :
    AdmIA D H ωstar E₀ (r - 3 * δ) (r - 3 * δ - δ / 2) (β - p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ))))
        (p.CE * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ)))) (isoNewS H K ωstar E₀ s)
        (mK + n * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mB + p.CB * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mT + p.rT * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mLt + 2 * n * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mN + p.CNd * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mNt + p.CNtd * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mH + p.CDT * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) ∧
      p.CE * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) ≤ ε ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ),
        ‖isoNewtonMap H K ωstar E₀ s (r - 2 * δ) θ - K θ‖ ≤
          p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
        ‖fderiv ℂ (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ - fderiv ℂ K θ‖ ≤
          n * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)))) ∧
      |isoNewS H K ωstar E₀ s - s| * ‖ωstar‖ ≤ p.CDw * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
      ν' - p.CDw * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ≤ rayMargin σω ωstar (isoNewS H K ωstar E₀ s) := by
  have hSet := hS.setting hK.s_gt.le
  have hSt := hSet.toStanding
  have hr := hK.r_pos
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hδ1 : δ ≤ 1 := hδD.trans hp.δ1
  obtain ⟨hεδ, hsym, hE, htw, hgr⟩ := hcond.facts hp hγ hγb hδ hδD hε0
  have hε1 : ε ≤ 1 := hεδ.trans hδ1
  obtain ⟨-, -, s3, s4, -, -, -, s8⟩ := scales (ε := ε) (κ := p.κ) hγ hδ
  set E := ε / (γ ^ 2 * δ ^ (2 * p.κ)) with hEd
  set X := ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)) with hXd
  have hX0 : 0 ≤ X := div_nonneg hε0 (by positivity)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hDK0 := hp.CDK
  have hr1 : 0 ≤ (n : ℝ) * p.CDK * X := by positivity
  have hr2 : 0 ≤ p.CB * p.CDK * X := mul_nonneg (mul_nonneg hp.CB hDK0) hX0
  have hr3' : 0 ≤ p.rT * X := mul_nonneg hp.rT hX0
  have hr4 : 0 ≤ 2 * (n : ℝ) * p.CDK * X := by positivity
  have hr5 : 0 ≤ p.CNd * p.CDK * X := mul_nonneg (mul_nonneg hp.CNd hDK0) hX0
  have hr6 : 0 ≤ p.CNtd * p.CDK * X := mul_nonneg (mul_nonneg hp.CNtd hDK0) hX0
  have hr7 : 0 ≤ p.CDT * X := mul_nonneg hp.CDT hX0
  have hK0 : AdmIA D H ωstar E₀ r (r - δ) β ε s p.sK p.sB p.sT p.sLt p.sN p.sNt p.t K :=
    hK.mono (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith)
  have h2δ : 2 * δ < r := by linarith
  have hr3 : 0 < r - 3 * δ := by linarith
  have hsub : complexStrip n (r - 2 * δ) ⊆ complexStrip n r :=
    Triangular.strip_mono (by linarith)
  have hsub32 : complexStrip n (r - 3 * δ) ⊆ complexStrip n (r - 2 * δ) :=
    Triangular.strip_mono (by linarith)
  have hsub3r : complexStrip n (r - 3 * δ) ⊆ complexStrip n r := hsub32.trans hsub
  have hsub31 : complexStrip n (r - 3 * δ) ⊆ complexStrip n (r - δ) :=
    Triangular.strip_mono (by linarith)
  have hK𝔅 := hK.mem
  have hAd := hK0.toIso hε1
  have hHY : ∀ θ ∈ complexStrip n r, ∑ b, ‖energyRow H K θ b‖ ≤ p.HY := fun θ hθ => by
    rw [hHYv]
    exact sum_norm_energyRow_le_ref (hdH _ (hK𝔅 θ hθ)) (hK0.normal θ hθ)
  obtain ⟨⟨-, -, -, hcd, hcp, hcr, -⟩, -⟩ := KAM.Iso.Apost.correction hS hAd hδ hδ1 h2δ
  obtain ⟨-, -, hsd⟩ := iso_correction_boundsA hp hiso hpn hS hd1 hγb hω hK0 hδ hδD h2δ hεδ hΘ hHY
    hc hcb hbr hca
  obtain ⟨hdist', hΩ, herr, hen⟩ := iso_newton_error_boundsA hp hiso hpn hS hd1 hd2 hd2H hγb hω hK0
    hδ hδD h2δ hεδ hΘ hHY hc hcb hbr hca hβ hsym
  obtain ⟨hs1', -, hray'⟩ := (KAM.Iso.Apost.ray (σω := σω) hS.dio).2.2.2.2.2 s
    (isoNewS H K ωstar E₀ s) ν' _ hray hsd hνd
  set s' := isoNewS H K ωstar E₀ s with hs'
  set K' := isoNewtonMap H K ωstar E₀ s (r - 2 * δ) with hK'def
  have hdiff : DifferentiableOn ℂ K' (complexStrip n (r - 2 * δ)) :=
    TorsionAux.isoNewtonMap_differentiableOn (hK.holo.mono hsub) hcd
  have hdist : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖K' θ - K θ‖ ≤ p.CDK * E := fun θ hθ => by
    rw [hK'def, TorsionAux.isoNewtonMap_of_mem hθ, add_sub_cancel_left]
    exact hdist' θ hθ
  have hD : p.CDK * E / δ = p.CDK * X := by
    rw [s3]; field_simp
  have hball : ∀ θ ∈ complexStrip n (r - 2 * δ), Metric.ball (K' θ) (β - p.CDK * E) ⊆ D :=
    fun θ hθ => PerturbationAux.ball_subset_of_close (hK.ball_sub θ (hsub hθ)) (hdist θ hθ)
  have hβ' : 0 < β - p.CDK * E := by linarith
  have hK'𝔅 : ∀ θ ∈ complexStrip n (r - 2 * δ), K' θ ∈ D := fun θ hθ =>
    hball θ hθ (Metric.mem_ball_self hβ')
  have hLθ : ∀ θ ∈ complexStrip n r, ‖tangentMat K θ‖ ≤ p.sK := fun θ hθ => hK0.tangent_le hθ
  have hfr := frames_bar hp hpn hK.holo hLθ hK.gram hK.tangentT (by linarith) (by linarith) hδ hdiff
    hdist (by rw [hD]; exact hgr) (by rw [hD]; linarith) (by rw [hD]; linarith)
  rw [hD] at hfr
  have hL'θ : ∀ θ ∈ complexStrip n (r - 3 * δ), ‖fderiv ℂ K' θ‖ ≤ mK + n * p.CDK * X := fun θ hθ => by
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
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  have hG'3 : ∀ θ ∈ complexStrip n (r - 3 * δ), IsUnit (gramMatrix K' θ).det :=
    fun θ hθ => (hfr θ hθ).unit
  have hYg : ε / (γ * δ ^ (p.κ + 1)) ≤ p.g * X := by
    rw [s8]
    exact mul_le_mul_of_nonneg_right (StepInA.gd_le hp hγ hγb hδ hδD) hX0
  have hεg : ε / δ ≤ p.γb ^ 2 * p.δ ^ (2 * p.κ) * X := by
    rw [s4]
    exact mul_le_mul_of_nonneg_right
      (pow_mul_rpow_le 2 hγ hγb hδ hδD (by linarith [hp.κ_ge])) hX0
  have hω' : ‖s' • ωstar - s • ωstar‖ ≤ p.CDw * E := hsd
  have hT' : ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖torsion H K' (s' • ωstar) θ - torsion H K (s • ωstar) θ‖ ≤ p.CDT0 * X := by
    intro θ hθ
    have hθr := hsub3r hθ
    have hθ2 := hsub32 hθ
    have hL' : ‖tangentMat K' θ‖ ≤ p.sK :=
      (FrameAux.norm_tangentMat K' θ).le.trans ((hL'θ θ hθ).trans hcK)
    have hmain := torsion_sub_le hp hpn hSt hd1 hd2 (K := K) (K' := K') (ω₁ := s • ωstar)
      (ω₂ := s' • ωstar) (β := β) (d := p.CDK * E) (δ := δ) (ε := ε)
      (ε' := p.CE * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))))
      (Wb := p.COm * (ε / (γ * δ ^ (p.κ + 1)))) hr hδ hδD h3δ hθ hK.holo hK.mem hGu hK.error_le hdiff
      hK'𝔅 hG'3 herr (hK.ball_sub θ hθr) (hdist θ hθ2) hβ hε0 hE hεδ (hLθ θ hθr) (hK0.tangentT θ hθr)
      (hK0.normalT θ hθr) (hK0.gram θ hθr).2 hL' ((hLt'θ θ hθ).trans hcLt) ((hN'θ θ hθ).trans hcN)
      ((hNt'θ θ hθ).trans hcNt) ((hB'θ θ hθ).trans hcB) (hΩ θ hθ2)
      (by rw [hD]; exact hfr θ hθ)
    rw [hD] at hmain
    have hw0 := hp.w
    have hsB0 := hp.sB
    have hNt0 := hp.sNt
    have hOm0 := hp.COm
    refine hmain.trans ?_
    calc (p.CDab + p.CDc) * (p.CDK * X) + 2 * n * p.sNt * p.sB * (ε / δ) +
          2 * p.sB ^ 3 * p.w * (p.COm * (ε / (γ * δ ^ (p.κ + 1))))
        ≤ (p.CDab + p.CDc) * (p.CDK * X) + 2 * n * p.sNt * p.sB * (p.γb ^ 2 * p.δ ^ (2 * p.κ) * X) +
          2 * p.sB ^ 3 * p.w * (p.COm * (p.g * X)) :=
          add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hεg (by positivity)))
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hYg hOm0) (by positivity))
      _ = p.CDT0 * X := by
          unfold StepInA.CDT0; rw [hpn]; ring
  have hCDT : p.CDT = max (p.CDT0 + p.CDw * p.δ)
      (p.n * p.CDw * p.δ + 2 * p.n * p.sNt * (p.γb ^ 2 * p.δ ^ (2 * p.κ))) := by
    simp [StepInA.CDT, hiso]
  have hEX : E ≤ p.δ * X := by
    rw [s3]; exact mul_le_mul_of_nonneg_right hδD hX0
  have hε_le : ε ≤ p.γb ^ 2 * p.δ ^ (2 * p.κ) * X := by
    refine le_trans ?_ hεg
    rw [le_div_iff₀ hδ]
    exact mul_le_of_le_one_right hε0 hδ1
  have hDw0 := hp.CDw
  have hEdw : p.CDw * E ≤ p.CDw * p.δ * X := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hEX hDw0
  have hT'' : ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖torsion H K' (s' • ωstar) θ - torsion H K (s • ωstar) θ‖ ≤ p.CDT * X := by
    intro θ hθ
    refine (hT' θ hθ).trans (mul_le_mul_of_nonneg_right ?_ hX0)
    rw [hCDT]
    exact le_max_of_le_left (le_add_of_nonneg_right (mul_nonneg hDw0 hp.δ.le))
  -- the bordered torsion
  have hc0 := (extended_regular hSt hr hK.holo hK.mem hGu (s • ωstar)).2.2
  have hc' := (extended_regular hSt hr3 (hdiff.mono hsub32) (fun θ hθ => hK'𝔅 θ (hsub32 hθ)) hG'3
    (s' • ωstar)).2.2
  have hpt : ∀ x : Fin n → ℝ,
      ‖KAM.Iso.extendedTorsion H K' (s' • ωstar) (fun i => (x i : ℂ)) -
        KAM.Iso.extendedTorsion H K (s • ωstar) (fun i => (x i : ℂ))‖ ≤ p.CDT * X := by
    intro x
    have hθ := ofReal_mem_complexStrip hr3 x (n := n)
    have hθr := hsub3r hθ
    have hη := norm_etaL_le (hK0.normalT _ hθr) (hK.error_le _ hθr)
    have hη' := norm_etaL_le ((hNt'θ _ hθ).trans hcNt) (herr _ (hsub32 hθ))
    have hY : ∑ j, ‖energyRow H K' (fun i => (x i : ℂ)) j -
        energyRow H K (fun i => (x i : ℂ)) j‖ ≤
        n * (p.CDw * E) + 2 * n * p.sNt * ε := by
      refine (IsoTwistSharp.sum_norm_energyRow_sub_le_eta (ω := s • ωstar) (ω' := s' • ωstar)
        (hGu _ hθr) (hG'3 _ hθ)).trans ?_
      have h2 : p.sNt * (p.CE * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ)))) ≤ p.sNt * ε :=
        mul_le_mul_of_nonneg_left hE hp.sNt
      calc _ ≤ n * (p.CDw * E) + n * (p.sNt * ε) + n * (p.sNt * ε) :=
            add_le_add (add_le_add (mul_le_mul_of_nonneg_left hω' hn0)
              (mul_le_mul_of_nonneg_left (hη'.trans h2) hn0))
              (mul_le_mul_of_nonneg_left hη hn0)
        _ = _ := by ring
    refine (TorsionDiff.norm_extendedTorsion_sub_le _ (hT' _ hθ) hω' hY).trans ?_
    rw [hCDT, max_mul_of_nonneg _ _ hX0]
    refine max_le_max ?_ ?_
    · calc p.CDT0 * X + p.CDw * E ≤ p.CDT0 * X + p.CDw * p.δ * X := add_le_add le_rfl hEdw
        _ = _ := by ring
    · have hpn' : ((p.n : ℕ) : ℝ) = n := by rw [hpn]
      rw [hpn']
      have h1 : (n : ℝ) * (p.CDw * E) ≤ n * (p.CDw * p.δ * X) :=
        mul_le_mul_of_nonneg_left hEdw hn0
      have h2 : 2 * (n : ℝ) * p.sNt * ε ≤ 2 * n * p.sNt * (p.γb ^ 2 * p.δ ^ (2 * p.κ) * X) :=
        mul_le_mul_of_nonneg_left hε_le (mul_nonneg (by positivity) hp.sNt)
      calc _ ≤ _ := add_le_add h1 h2
        _ = _ := by ring
  have havg := TorsionDiff.norm_extendedTorsionAverage_sub_le hc0 hc' hpt
  have hTu : IsUnit (KAM.Iso.extendedTorsionAverage H K (s • ωstar)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 hK.twist.1
  have hTσ : ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ≤ p.sT :=
    hK.twist.2.trans (by linarith)
  have hsmall : ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ *
      ‖KAM.Iso.extendedTorsionAverage H K' (s' • ωstar) -
        KAM.Iso.extendedTorsionAverage H K (s • ωstar)‖ ≤ p.th :=
    (mul_le_mul hTσ havg (norm_nonneg _) hp.sT).trans htw
  obtain ⟨hU, -, hBdiff⟩ := neumann_ratio hTu hp.th1 hsmall
  rw [add_sub_cancel] at hU hBdiff
  have hth := hp.one_sub_th
  have hTdd : ‖(KAM.Iso.extendedTorsionAverage H K' (s' • ωstar))⁻¹ -
      (KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ≤ p.rT * X := by
    have hTT : ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ^ 2 ≤ p.sT ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hTσ 2
    calc _ ≤ ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ^ 2 *
          ‖KAM.Iso.extendedTorsionAverage H K' (s' • ωstar) -
            KAM.Iso.extendedTorsionAverage H K (s • ωstar)‖ / (1 - p.th) := hBdiff
      _ ≤ p.sT ^ 2 * (p.CDT * X) / (1 - p.th) :=
          div_le_div_of_nonneg_right (mul_le_mul hTT havg (norm_nonneg _) (by positivity)) hth.le
      _ = p.rT * X := by unfold StepInA.rT; ring
  have hsubT : complexStrip n (r - 3 * δ - δ / 2) ⊆ complexStrip n (r - 3 * δ) :=
    Triangular.strip_mono (by linarith)
  refine ⟨?_, hE, fun θ hθ => ⟨hdist θ (hsub32 hθ), ?_⟩, ?_, hray'⟩
  · exact
      { r_pos := hr3
        β_pos := hβ'
        ε_nonneg := by
          have h1 : 0 ≤ p.CE * ε ^ 2 := mul_nonneg hp.CE (sq_nonneg _)
          positivity
        holo := hdiff.mono hsub32
        primary := fun θ hθ k =>
          (TorsionAux.isoNewtonMap_isPrimaryOnStrip (by linarith) hK.primary hcp) θ (hsub32 hθ) k
        real := TorsionAux.isoNewtonMap_isRealOnReals (by linarith) hK.real hcr
        ball_sub := fun θ hθ => hball θ (hsub32 hθ)
        deriv_le := hL'θ
        gram := fun θ hθ => ⟨hG'3 θ hθ, hB'θ θ hθ⟩
        tangentT := hLt'θ
        normal := hN'θ
        normalT := hNt'θ
        tors := fun θ hθ => norm_le_add_sub (hK.tors θ (hsub31 (hsubT hθ))) (hT'' θ (hsubT hθ))
        error_le := fun θ hθ => herr θ (hsub32 hθ)
        s_gt := hs1'
        twist := ⟨(Matrix.isUnit_iff_isUnit_det _).1 hU, norm_le_add_sub hK.twist.2 hTdd⟩
        energy_le := hen }
  · have := (hfr θ hθ).dDK
    rwa [← mul_assoc] at this
  · have e : ‖s' • ωstar - s • ωstar‖ = |s' - s| * ‖ωstar‖ :=
      (KAM.Iso.Apost.ray (σω := σω) hS.dio).2.2.2.1 s s'
    rw [← e]
    exact hω'

end KAM.Iso.Sharp2.RouteA

end
