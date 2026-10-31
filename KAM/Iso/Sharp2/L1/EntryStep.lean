/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.L1.EntryError
public import KAM.Sharp2.L1.EntryStep
public import KAM.Iso.Sharp2.RouteA.Step
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The isoenergetic ℓ¹ entry step of route A (package B10c)

`iso_entry_step`: B9's `KAM.Iso.Sharp2.RouteA.step_IA` from the ℓ¹ entry data at `s ω*`, with
every cap increased by its entry rate and the ray margin decreased by `C_Δω E`. The frame increments
are those of `KAM.Sharp2.L1.entry_frame_rates_of` (the ℓ¹ one through
`KAM.Sharp2.L1.l1_frame_increment_of` for the isoenergetic correction), the torsion is bounded by
`KAM.Sharp2.L1.torsion_sub_leG` for the two frequencies `s ω*`, `s̄ ω*`, and the bordered torsion
adds the blocks `Δω`, `ΔY` as in B9.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Sharp2.L1

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp KAM.Iso.Sharp2.RouteA KAM.Sharp2.L1

variable {n : ℕ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {ωstar : Fin n → ℝ} {τ M σω ν γ : ℝ}

/-- The isoenergetic ℓ¹ entry step of route A. -/
theorem iso_entry_step {p : StepInA} {Ed : EntryA} (hp : p.Pos) (hE : Ed.Wf) (hiso : p.iso = true)
    (hpn : p.n = n) (hS : IsoStanding n τ M p.sK p.sB p.sT σω ν ωstar D H γ)
    (hd1 : ∀ z ∈ D, ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ p.M1)
    (hd2 : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ p.M2)
    (hd2H : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ p.Mh2) {Mh1 : ℝ}
    (hdH : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ Mh1) (hHYv : p.HY = Mh1 * p.sN) (hγb : γ ≤ p.γb)
    {Ω : Set (Fin n → ℝ)} {E₀ r β ε δ b cb s ν' mK mB mT mLt mN mNt mH : ℝ} (hω : s • ωstar ∈ Ω)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : AdmIA D H ωstar E₀ r (r - δ) β ε s mK mB mT mLt mN mNt mH K)
    (hδ : 0 < δ) (hδD : δ ≤ p.δ) (h3δ : 3 * δ < r) (hΘ : ‖s • ωstar‖ ≤ p.Θ)
    (hc : SDConst n p.κ γ δ p.c Ω) (hcb : SDConst n p.κ γ b cb Ω) (hbr : b ≤ r)
    (hca : cb * b ^ (-p.κ) ≤ p.ca * δ ^ (-p.κ)) (hD : EntryData Ed H K (s • ωstar) r δ ε)
    (hcond : EntryCond p Ed (ε / (γ ^ 4 * δ ^ (2 * (2 * p.κ)))))
    (hβ : Ent.CDK p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) < β)
    (hray : ν' ≤ rayMargin σω ωstar s)
    (hνd : Ent.CDw p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) < ν')
    (hcK : mK + Ent.dL p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sK)
    (hcB : mB + Ent.rB p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sB)
    (hcT : mT + Ent.rT p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sT)
    (hcLt : mLt + Ent.dLt p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sLt)
    (hcN : mN + Ent.rN p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sN)
    (hcNt : mNt + Ent.rNt p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sNt)
    (hcH : mH + Ent.CDT p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.t) :
    AdmIA D H ωstar E₀ (r - 3 * δ) (r - 3 * δ - δ / 2)
        (β - Ent.CDK p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ))))
        (Ent.CE p Ed * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ)))) (isoNewS H K ωstar E₀ s)
        (mK + Ent.dL p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mB + Ent.rB p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mT + Ent.rT p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mLt + Ent.dLt p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mN + Ent.rN p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mNt + Ent.rNt p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mH + Ent.CDT p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) ∧
      Ent.CE p Ed * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) ≤ ε ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ),
        ‖isoNewtonMap H K ωstar E₀ s (r - 2 * δ) θ - K θ‖ ≤
          Ent.CDK p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
        ‖fderiv ℂ (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ - fderiv ℂ K θ‖ ≤
          n * Ent.CDK p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)))) ∧
      |isoNewS H K ωstar E₀ s - s| * ‖ωstar‖ ≤ Ent.CDw p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
      ν' - Ent.CDw p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ≤
        rayMargin σω ωstar (isoNewS H K ωstar E₀ s) := by
  have hk := Ent.nonneg hp hE
  have hSet := hS.setting hK.s_gt.le
  have hSt := hSet.toStanding
  have hr := hK.r_pos
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hδ1 : δ ≤ 1 := hδD.trans hp.δ1
  obtain ⟨hεδ, hsym, hE2, htw, hgr⟩ := hcond.facts hp hE hγ hγb hδ hδD hε0
  have hε1 : ε ≤ 1 := hεδ.trans hδ1
  obtain ⟨-, -, s3, s4, -, -, -, -⟩ := scales (ε := ε) (κ := p.κ) hγ hδ
  set E := ε / (γ ^ 2 * δ ^ (2 * p.κ)) with hEd
  set X := ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)) with hXd
  have hX0 : 0 ≤ X := div_nonneg hε0 (by positivity)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr1 : 0 ≤ Ent.dL p Ed * X := mul_nonneg hk.dL hX0
  have hr2 : 0 ≤ Ent.rB p Ed * X := mul_nonneg hk.rB hX0
  have hr3' : 0 ≤ Ent.rT p Ed * X := mul_nonneg hk.rT hX0
  have hr4 : 0 ≤ Ent.dLt p Ed * X := mul_nonneg hk.dLt hX0
  have hr5 : 0 ≤ Ent.rN p Ed * X := mul_nonneg hk.rN hX0
  have hr6 : 0 ≤ Ent.rNt p Ed * X := mul_nonneg hk.rNt hX0
  have hr7 : 0 ≤ Ent.CDT p Ed * X := mul_nonneg hk.CDT hX0
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
  obtain ⟨-, -, hsd, hXN1, hXL1, hXNd, hXNp, hXLd, hXLp⟩ := iso_entry_correction_bounds hp hE hiso
    hpn hS hd1 hγb hω hK0 hδ hδD h2δ hεδ hΘ hHY hc hcb hbr hca hD
  obtain ⟨hdist', hΩ, herr, hen⟩ := iso_entry_newton_error hp hE hiso hpn hS hd1 hd2 hd2H hγb hω
    hK0 hδ hδD h2δ hεδ hΘ hHY hc hcb hbr hca hD hβ hsym
  obtain ⟨hs1', -, hray'⟩ := (KAM.Iso.Apost.ray (σω := σω) hS.dio).2.2.2.2.2 s
    (isoNewS H K ωstar E₀ s) ν' _ hray hsd hνd
  set s' := isoNewS H K ωstar E₀ s with hs'
  set K' := isoNewtonMap H K ωstar E₀ s (r - 2 * δ) with hK'def
  have hdiff : DifferentiableOn ℂ K' (complexStrip n (r - 2 * δ)) :=
    TorsionAux.isoNewtonMap_differentiableOn (hK.holo.mono hsub) hcd
  have hdist : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖K' θ - K θ‖ ≤ Ent.CDK p Ed * E := fun θ hθ => by
    rw [hK'def, TorsionAux.isoNewtonMap_of_mem hθ, add_sub_cancel_left]
    exact hdist' θ hθ
  have hD' : Ent.CDK p Ed * E / δ = Ent.CDK p Ed * X := by
    rw [s3]; field_simp
  have hball : ∀ θ ∈ complexStrip n (r - 2 * δ),
      Metric.ball (K' θ) (β - Ent.CDK p Ed * E) ⊆ D :=
    fun θ hθ => PerturbationAux.ball_subset_of_close (hK.ball_sub θ (hsub hθ)) (hdist θ hθ)
  have hβ' : 0 < β - Ent.CDK p Ed * E := by linarith
  have hK'𝔅 : ∀ θ ∈ complexStrip n (r - 2 * δ), K' θ ∈ D := fun θ hθ =>
    hball θ hθ (Metric.mem_ball_self hβ')
  -- the frame increments
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  obtain ⟨⟨hLd, -, -, -, -, -, hNd, -, -, -, -, -, -, -, -⟩, -, -, -⟩ :=
    frame_basic hSt hr hK.β_pos hK.holo hK.ball_sub hK0.deriv_le hK0.gram
  obtain ⟨⟨hLp, -⟩, hperiod, -⟩ := periodicity hSt hr hK.holo hK.primary hK𝔅
  obtain ⟨-, hNp, -⟩ := hperiod hGu
  have hrates := entry_frame_rates_of hp hE hpn hγ hγb hε0 hδ hδD hK.holo hdist hdiff
    fun F hF => l1_frame_increment_of hδ h3δ hK.holo hcd hcp
      (fun θ hθ => TorsionAux.isoNewtonMap_of_mem hθ)
      (fun θ => by
        rw [CorrectionAux.sumVec_isoCorrection]
        unfold frameMat
        rw [show isoXi H K (s • ωstar) E₀ θ =
          Sum.elim (bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0 θ)
            (bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ) from rfl,
          Matrix.fromCols_mulVec_sumElim])
      hLd hLp hNd hNp hXLd hXLp hXNd hXNp (hD.frame F hF).1 (hD.frame F hF).2 hXL1 hXN1
  have hLθ : ∀ θ ∈ complexStrip n r, ‖tangentMat K θ‖ ≤ p.sK := fun θ hθ => hK0.tangent_le hθ
  have hfr : ∀ θ ∈ complexStrip n (r - 3 * δ), BarBdG K K' θ (Ent.dL p Ed * X) (Ent.dLt p Ed * X)
      (Ent.rB p Ed * X) (Ent.rN p Ed * X) (Ent.rNt p Ed * X) := by
    intro θ hθ
    have hθr := hsub3r hθ
    have e1 : rBOf p (Ent.dL p Ed * X) (Ent.dLt p Ed * X) = Ent.rB p Ed * X := by
      unfold rBOf Ent.rB; ring
    have hb := frames_barG hp (hLθ θ hθr) (hK.gram θ hθr).1 (hK.gram θ hθr).2 (hK.tangentT θ hθr)
      (by linarith) (by linarith) (hrates θ hθ).1 (hrates θ hθ).2
      (by have : p.sLt * (Ent.dL p Ed * X) + p.sK * (Ent.dLt p Ed * X) = Ent.GrK p Ed * X := by
            unfold Ent.GrK; ring
          rw [this]; exact hgr)
      hcLt (by rw [e1]; exact hcB)
    rw [e1] at hb
    have e2 : p.sB * (Ent.dL p Ed * X) + p.sK * (Ent.rB p Ed * X) = Ent.rN p Ed * X := by
      unfold Ent.rN; ring
    have e3 : Ent.rB p Ed * X * p.sLt + p.sB * (Ent.dLt p Ed * X) = Ent.rNt p Ed * X := by
      unfold Ent.rNt; ring
    rw [e2, e3] at hb
    exact hb
  have hL'θ : ∀ θ ∈ complexStrip n (r - 3 * δ), ‖fderiv ℂ K' θ‖ ≤ mK + Ent.dL p Ed * X :=
    fun θ hθ => norm_le_add_sub (hK.deriv_le θ (hsub3r hθ)) (hfr θ hθ).dDK
  have hLt'θ : ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖(tangentMat K' θ)ᵀ‖ ≤ mLt + Ent.dLt p Ed * X := fun θ hθ => by
    have e : (tangentMat K' θ)ᵀ = (tangentMat K θ)ᵀ + (tangentMat K' θ - tangentMat K θ)ᵀ := by
      rw [Matrix.transpose_sub]; abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add (hK.tangentT θ (hsub3r hθ)) (hfr θ hθ).dLt)
  have hB'θ : ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖(gramMatrix K' θ)⁻¹‖ ≤ mB + Ent.rB p Ed * X := fun θ hθ =>
    norm_le_add_sub (hK.gram θ (hsub3r hθ)).2 (hfr θ hθ).dB
  have hN'θ : ∀ θ ∈ complexStrip n (r - 3 * δ), ‖normalMat K' θ‖ ≤ mN + Ent.rN p Ed * X :=
    fun θ hθ => norm_le_add_sub (hK.normal θ (hsub3r hθ)) (hfr θ hθ).dN
  have hNt'θ : ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖(normalMat K' θ)ᵀ‖ ≤ mNt + Ent.rNt p Ed * X := fun θ hθ =>
    norm_le_add_sub (hK.normalT θ (hsub3r hθ)) (hfr θ hθ).dNt
  have hG'3 : ∀ θ ∈ complexStrip n (r - 3 * δ), IsUnit (gramMatrix K' θ).det :=
    fun θ hθ => (hfr θ hθ).unit
  have hεg : ε / δ ≤ p.γb ^ 2 * p.δ ^ (2 * p.κ) * X := by
    rw [s4]
    exact mul_le_mul_of_nonneg_right
      (pow_mul_rpow_le 2 hγ hγb hδ hδD (by linarith [hp.κ_ge])) hX0
  have hω' : ‖s' • ωstar - s • ωstar‖ ≤ Ent.CDw p Ed * E := hsd
  -- the torsion at the two frequencies
  have hT' : ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖torsion H K' (s' • ωstar) θ - torsion H K (s • ωstar) θ‖ ≤ Ent.CDT0 p Ed * X := by
    intro θ hθ
    have hθr := hsub3r hθ
    have hθ2 := hsub32 hθ
    have hL' : ‖tangentMat K' θ‖ ≤ p.sK :=
      (FrameAux.norm_tangentMat K' θ).le.trans ((hL'θ θ hθ).trans hcK)
    have hmain := torsion_sub_leG hp hpn hSt hd1 hd2 (K := K) (K' := K') (ω₁ := s • ωstar)
      (ω₂ := s' • ωstar) (β := β) (d := Ent.CDK p Ed * E) (δ := δ) (ε := ε)
      (ε' := Ent.CE p Ed * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))))
      (Wb := Ent.COmK p Ed * (ε / (γ * δ ^ (p.κ + 1)))) hr hδ h3δ hθ hK.holo hK.mem hGu
      hK.error_le hdiff hK'𝔅 hG'3 herr (hK.ball_sub θ hθr) (hdist θ hθ2) hβ hE2 hεδ (hLθ θ hθr)
      (hK0.tangentT θ hθr) (hK0.normalT θ hθr) (hK0.gram θ hθr).2 hL' ((hLt'θ θ hθ).trans hcLt)
      ((hN'θ θ hθ).trans hcN) ((hNt'θ θ hθ).trans hcNt) ((hB'θ θ hθ).trans hcB) (hΩ θ hθ2)
      (hfr θ hθ)
    exact hmain.trans (entry_torsion_arith hp hE hpn hγ hγb hδ hδD hX0 rfl rfl)
  have hCDT : Ent.CDT p Ed = max (Ent.CDT0 p Ed + Ent.CDw p Ed * p.δ)
      (p.n * Ent.CDw p Ed * p.δ + 2 * p.n * p.sNt * (p.γb ^ 2 * p.δ ^ (2 * p.κ))) := by
    simp [Ent.CDT, hiso]
  have hEX : E ≤ p.δ * X := by
    rw [s3]; exact mul_le_mul_of_nonneg_right hδD hX0
  have hε_le : ε ≤ p.γb ^ 2 * p.δ ^ (2 * p.κ) * X := by
    refine le_trans ?_ hεg
    rw [le_div_iff₀ hδ]
    exact mul_le_of_le_one_right hε0 hδ1
  have hDw0 := hk.CDw
  have hEdw : Ent.CDw p Ed * E ≤ Ent.CDw p Ed * p.δ * X := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hEX hDw0
  have hT'' : ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖torsion H K' (s' • ωstar) θ - torsion H K (s • ωstar) θ‖ ≤ Ent.CDT p Ed * X := by
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
        KAM.Iso.extendedTorsion H K (s • ωstar) (fun i => (x i : ℂ))‖ ≤ Ent.CDT p Ed * X := by
    intro x
    have hθ := ofReal_mem_complexStrip hr3 x (n := n)
    have hθr := hsub3r hθ
    have hη := norm_etaL_le (hK0.normalT _ hθr) (hK.error_le _ hθr)
    have hη' := norm_etaL_le ((hNt'θ _ hθ).trans hcNt) (herr _ (hsub32 hθ))
    have hY : ∑ j, ‖energyRow H K' (fun i => (x i : ℂ)) j -
        energyRow H K (fun i => (x i : ℂ)) j‖ ≤
        n * (Ent.CDw p Ed * E) + 2 * n * p.sNt * ε := by
      refine (IsoTwistSharp.sum_norm_energyRow_sub_le_eta (ω := s • ωstar) (ω' := s' • ωstar)
        (hGu _ hθr) (hG'3 _ hθ)).trans ?_
      have h2 : p.sNt * (Ent.CE p Ed * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ)))) ≤ p.sNt * ε :=
        mul_le_mul_of_nonneg_left hE2 hp.sNt
      calc _ ≤ n * (Ent.CDw p Ed * E) + n * (p.sNt * ε) + n * (p.sNt * ε) :=
            add_le_add (add_le_add (mul_le_mul_of_nonneg_left hω' hn0)
              (mul_le_mul_of_nonneg_left (hη'.trans h2) hn0))
              (mul_le_mul_of_nonneg_left hη hn0)
        _ = _ := by ring
    refine (TorsionDiff.norm_extendedTorsion_sub_le _ (hT' _ hθ) hω' hY).trans ?_
    rw [hCDT, max_mul_of_nonneg _ _ hX0]
    refine max_le_max ?_ ?_
    · calc Ent.CDT0 p Ed * X + Ent.CDw p Ed * E ≤ Ent.CDT0 p Ed * X + Ent.CDw p Ed * p.δ * X :=
            add_le_add le_rfl hEdw
        _ = _ := by ring
    · have hpn' : ((p.n : ℕ) : ℝ) = n := by rw [hpn]
      rw [hpn']
      have h1 : (n : ℝ) * (Ent.CDw p Ed * E) ≤ n * (Ent.CDw p Ed * p.δ * X) :=
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
      (KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ≤ Ent.rT p Ed * X := by
    have hTT : ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ^ 2 ≤ p.sT ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hTσ 2
    calc _ ≤ ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ^ 2 *
          ‖KAM.Iso.extendedTorsionAverage H K' (s' • ωstar) -
            KAM.Iso.extendedTorsionAverage H K (s • ωstar)‖ / (1 - p.th) := hBdiff
      _ ≤ p.sT ^ 2 * (Ent.CDT p Ed * X) / (1 - p.th) :=
          div_le_div_of_nonneg_right (mul_le_mul hTT havg (norm_nonneg _) (by positivity)) hth.le
      _ = Ent.rT p Ed * X := by unfold Ent.rT; ring
  have hsubT : complexStrip n (r - 3 * δ - δ / 2) ⊆ complexStrip n (r - 3 * δ) :=
    Triangular.strip_mono (by linarith)
  refine ⟨?_, hE2, fun θ hθ => ⟨hdist θ (hsub32 hθ), ?_⟩, ?_, hray'⟩
  · exact
      { r_pos := hr3
        β_pos := hβ'
        ε_nonneg := by
          have h1 : 0 ≤ Ent.CE p Ed * ε ^ 2 := mul_nonneg hk.CE (sq_nonneg _)
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
  · have := PerturbationAux.norm_fderiv_sub_le (hK.holo.mono hsub) hdiff hdist hδ θ
      (by rwa [show r - 2 * δ - δ = r - 3 * δ by ring])
    rw [mul_div_assoc, hD'] at this
    rw [mul_assoc]
    exact this
  · have e : ‖s' • ωstar - s • ωstar‖ = |s' - s| * ‖ωstar‖ :=
      (KAM.Iso.Apost.ray (σω := σω) hS.dio).2.2.2.1 s s'
    rw [← e]
    exact hω'

end KAM.Iso.Sharp2.L1

end
