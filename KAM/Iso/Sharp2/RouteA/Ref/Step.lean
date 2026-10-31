/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.RouteA.Step
public import KAM.Sharp2.RouteA.Ref.Step
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Lever L8′ of the isoenergetic route A: the step

* `Ref.inv_le_of_ref_fintype`: Neumann against the initial average, for any index type (the
  bordered torsion is indexed by `Fin n ⊕ Unit`);
* `Ref.RefTI`, `Ref.AdmRI`: the reference data of the initial pair `(K₀, s₀)` and the admissibility
  of a stage. `mAb` bounds `|𝒯_ab(K) - 𝒯_ab(K₀)| + |ω - ω₀|` and `n |ω - ω₀|`;
* `Ref.AdmRI.entry`: at the entry to a stage the bounds of `T` and of the bordered `⟨T⟩⁻¹` follow
  from the reference data, since `T̃ - T̃₀` is `T - T₀` with the column `ω - ω₀` and the row
  `Y - Y₀`, and `Y = ω - ηᴸ`;
* `Ref.step_coreI`: `step_IA` without its two conclusions on the torsion of the new pair.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Sharp2.RouteA.Ref

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp KAM.Sharp2.RouteA.Ref

variable {n : ℕ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {ωstar : Fin n → ℝ} {τ M σω ν γ : ℝ}

/-- `KAM.Sharp2.inv_le_of_ref` for any index type. -/
theorem inv_le_of_ref_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] {A A0 : Matrix ι ι ℂ}
    {m σ : ℝ} (hA0 : IsUnit A0.det) (hm : ‖A0⁻¹‖ ≤ m) (hm0 : 0 < m) (hmσ : m < σ)
    (hd : ‖A - A0‖ ≤ (σ - m) / (σ * m)) : IsUnit A.det ∧ ‖A⁻¹‖ ≤ σ := by
  have hσ : 0 < σ := hm0.trans hmσ
  have hq : (σ - m) / σ < 1 := by rw [div_lt_one hσ]; linarith
  have hsmall : ‖A0⁻¹‖ * ‖A - A0‖ ≤ (σ - m) / σ := by
    calc ‖A0⁻¹‖ * ‖A - A0‖ ≤ m * ((σ - m) / (σ * m)) :=
          mul_le_mul hm hd (norm_nonneg _) hm0.le
      _ = (σ - m) / σ := by field_simp
  obtain ⟨hu, hb, -⟩ := neumann_ratio ((Matrix.isUnit_iff_isUnit_det A0).2 hA0) hq hsmall
  rw [add_sub_cancel] at hu hb
  refine ⟨(Matrix.isUnit_iff_isUnit_det A).1 hu, hb.trans ?_⟩
  have h1 : 1 - (σ - m) / σ = m / σ := by field_simp; ring
  rw [h1, div_le_iff₀ (div_pos hm0 hσ)]
  calc ‖A0⁻¹‖ ≤ m := hm
    _ = σ * (m / σ) := by field_simp

/-- The data of the initial pair, at the frequency `ω₀`, on the strip `T_R`. -/
structure RefTI {n : ℕ} (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K₀ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω₀ : Fin n → ℝ) (R bF iH mT : ℝ) : Prop where
  cont : Continuous (fun x : Fin n → ℝ => KAM.Iso.extendedTorsion H K₀ ω₀ (fun i => (x i : ℂ)))
  unit : IsUnit (KAM.Iso.extendedTorsionAverage H K₀ ω₀).det
  inv : ‖(KAM.Iso.extendedTorsionAverage H K₀ ω₀)⁻¹‖ ≤ mT
  tors : ∀ θ ∈ complexStrip n R, ‖torsion H K₀ ω₀ θ‖ ≤ iH
  loc : ∀ θ ∈ complexStrip n R, ‖torsion H K₀ ω₀ θ - torsionAB H K₀ θ‖ ≤ bF
  row : ∀ θ ∈ complexStrip n R, (n : ℝ) * ‖etaL H K₀ ω₀ θ‖ ≤ bF
  gram : ∀ θ ∈ complexStrip n R, IsUnit (gramMatrix K₀ θ).det

/-- Admissibility of a stage of the isoenergetic route A with the torsion against `(K₀, s₀)`. -/
structure AdmRI {n : ℕ} (D : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ωstar : Fin n → ℝ) (E₀ : ℝ)
    (K₀ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (s₀ r rT β ε s mK mB mAb mLt mN mNt : ℝ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) : Prop extends
    Adm0 D H (s • ωstar) r β ε mK mB mLt mN mNt K where
  s_gt : 1 < s
  energy_le : ‖KAM.Iso.energyAverage H K - (E₀ : ℂ)‖ ≤ ε
  tab : ∀ θ ∈ complexStrip n rT, ‖torsionAB H K θ - torsionAB H K₀ θ‖ +
    ‖s • ωstar - s₀ • ωstar‖ ≤ mAb
  freq : (n : ℝ) * ‖s • ωstar - s₀ • ωstar‖ ≤ mAb

/-- Lemma `bp:p2s2:torsion-ref` for the bordered torsion, at the entry to a stage. -/
theorem AdmRI.entry {K₀ K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {E₀ s₀ r rT β ε s mK mB mAb mLt mN mNt R bF iH mT σ t : ℝ}
    (hK : AdmRI D H ωstar E₀ K₀ s₀ r rT β ε s mK mB mAb mLt mN mNt K)
    (hR : RefTI H K₀ (s₀ • ωstar) R bF iH mT) (hsub : complexStrip n rT ⊆ complexStrip n R)
    (hcont : Continuous (fun x : Fin n → ℝ =>
      KAM.Iso.extendedTorsion H K (s • ωstar) (fun i => (x i : ℂ))))
    (hrT : 0 < rT) (hrr : rT ≤ r)
    (hloc : ∀ θ ∈ complexStrip n rT, ‖torsion H K (s • ωstar) θ - torsionAB H K θ‖ ≤ bF)
    (hrow : ∀ θ ∈ complexStrip n rT, (n : ℝ) * ‖etaL H K (s • ωstar) θ‖ ≤ bF)
    (hm0 : 0 < mT) (hmσ : mT < σ) (hβ : mAb + 2 * bF ≤ (σ - mT) / (σ * mT))
    (ht : iH + mAb + 2 * bF ≤ t) : AdmIA D H ωstar E₀ r rT β ε s mK mB σ mLt mN mNt t K := by
  have hd : ∀ θ ∈ complexStrip n rT, ‖torsion H K (s • ωstar) θ - torsion H K₀ (s₀ • ωstar) θ‖ ≤
      ‖torsionAB H K θ - torsionAB H K₀ θ‖ + 2 * bF := by
    intro θ hθ
    have e : torsion H K (s • ωstar) θ - torsion H K₀ (s₀ • ωstar) θ =
        (torsion H K (s • ωstar) θ - torsionAB H K θ) + (torsionAB H K θ - torsionAB H K₀ θ) -
          (torsion H K₀ (s₀ • ωstar) θ - torsionAB H K₀ θ) := by abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_add_le (torsion H K (s • ωstar) θ - torsionAB H K θ)
      (torsionAB H K θ - torsionAB H K₀ θ)
    have h2 := hloc θ hθ
    have h4 := hR.loc θ (hsub hθ)
    linarith
  have hpt : ∀ x : Fin n → ℝ, ‖KAM.Iso.extendedTorsion H K (s • ωstar) (fun i => (x i : ℂ)) -
      KAM.Iso.extendedTorsion H K₀ (s₀ • ωstar) (fun i => (x i : ℂ))‖ ≤ mAb + 2 * bF := by
    intro x
    have hθ := ofReal_mem_complexStrip hrT x (n := n)
    have hθr : (fun i => (x i : ℂ)) ∈ complexStrip n r :=
      Triangular.strip_mono hrr hθ
    have hY := IsoTwistSharp.sum_norm_energyRow_sub_le_eta (H := H) (ω := s₀ • ωstar)
      (ω' := s • ωstar) (hR.gram _ (hsub hθ)) (hK.gram _ hθr).1
    have h1 := hK.tab _ hθ
    have h2 := hK.freq
    have h3 := hrow _ hθ
    have h4 := hR.row _ (hsub hθ)
    refine (TorsionDiff.norm_extendedTorsion_sub_le _ (hd _ hθ) le_rfl hY).trans (max_le ?_ ?_)
    · linarith
    · linarith
  have havg := TorsionDiff.norm_extendedTorsionAverage_sub_le hR.cont hcont hpt
  have htw := inv_le_of_ref_fintype hR.unit hR.inv hm0 hmσ (havg.trans hβ)
  exact
    { r_pos := hK.r_pos
      β_pos := hK.β_pos
      ε_nonneg := hK.ε_nonneg
      holo := hK.holo
      primary := hK.primary
      real := hK.real
      ball_sub := hK.ball_sub
      deriv_le := hK.deriv_le
      gram := hK.gram
      tangentT := hK.tangentT
      normal := hK.normal
      normalT := hK.normalT
      tors := fun θ hθ => by
        have e : torsion H K (s • ωstar) θ = torsion H K₀ (s₀ • ωstar) θ +
            (torsion H K (s • ωstar) θ - torsion H K₀ (s₀ • ωstar) θ) := by abel
        rw [e]
        refine (norm_add_le _ _).trans ?_
        have h1 := hR.tors θ (hsub hθ)
        have h2 := hd θ hθ
        have h3 := hK.tab θ hθ
        have h4 : 0 ≤ ‖s • ωstar - s₀ • ωstar‖ := norm_nonneg _
        linarith
      error_le := hK.error_le
      s_gt := hK.s_gt
      twist := htw
      energy_le := hK.energy_le }

/-- The additive step of the isoenergetic route A, with the change of `𝒯_ab` in place of the
bounds of the new torsion. -/
theorem step_coreI {p : StepInA} (hp : p.Pos) (hiso : p.iso = true) (hpn : p.n = n)
    (hS : IsoStanding n τ M p.sK p.sB p.sT σω ν ωstar D H γ)
    (hd1 : ∀ z ∈ D, ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ p.M1)
    (hd2 : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ p.M2)
    (hd2H : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ p.Mh2) {Mh1 : ℝ}
    (hdH : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ Mh1) (hHYv : p.HY = Mh1 * p.sN) (hγb : γ ≤ p.γb)
    {Ω : Set (Fin n → ℝ)} {E₀ r β ε δ b cb s ν' mK mB mLt mN mNt : ℝ} (hω : s • ωstar ∈ Ω)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : AdmIA D H ωstar E₀ r (r - δ) β ε s mK mB p.sT mLt mN mNt p.t K)
    (hδ : 0 < δ) (hδD : δ ≤ p.δ) (h3δ : 3 * δ < r) (hΘ : ‖s • ωstar‖ ≤ p.Θ)
    (hc : SDConst n p.κ γ δ p.c Ω) (hcb : SDConst n p.κ γ b cb Ω) (hbr : b ≤ r)
    (hca : cb * b ^ (-p.κ) ≤ p.ca * δ ^ (-p.κ))
    (hcond : p.Cond0 (ε / (γ ^ 4 * δ ^ (2 * (2 * p.κ)))))
    (hβ : p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) < β)
    (hray : ν' ≤ rayMargin σω ωstar s)
    (hνd : p.CDw * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) < ν')
    (hcK : mK + n * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sK)
    (hcB : mB + p.CB * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sB)
    (hcLt : mLt + 2 * n * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sLt)
    (hcN : mN + p.CNd * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sN)
    (hcNt : mNt + p.CNtd * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sNt) :
    Adm0 D H (isoNewS H K ωstar E₀ s • ωstar) (r - 3 * δ)
        (β - p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ))))
        (p.CE * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))))
        (mK + n * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mB + p.CB * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mLt + 2 * n * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mN + p.CNd * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mNt + p.CNtd * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) ∧
      1 < isoNewS H K ωstar E₀ s ∧
      ‖KAM.Iso.energyAverage H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) - (E₀ : ℂ)‖ ≤
        p.CE * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) ∧
      p.CE * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) ≤ ε ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ),
        ‖isoNewtonMap H K ωstar E₀ s (r - 2 * δ) θ - K θ‖ ≤
          p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
        ‖fderiv ℂ (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ - fderiv ℂ K θ‖ ≤
          n * p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)))) ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ),
        ‖torsionAB H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ - torsionAB H K θ‖ ≤
          p.CDab * (p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))) ∧
      |isoNewS H K ωstar E₀ s - s| * ‖ωstar‖ ≤ p.CDw * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
      ν' - p.CDw * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ≤ rayMargin σω ωstar (isoNewS H K ωstar E₀ s) := by
  have hSet := hS.setting hK.s_gt.le
  have hSt := hSet.toStanding
  have hr := hK.r_pos
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hδ1 : δ ≤ 1 := hδD.trans hp.δ1
  obtain ⟨hεδ, hsym, hE, hgr⟩ := hcond.facts hp hγ hγb hδ hδD hε0
  have hε1 : ε ≤ 1 := hεδ.trans hδ1
  obtain ⟨-, -, s3, s4, -, -, -, s8⟩ := scales (ε := ε) (κ := p.κ) hγ hδ
  set E := ε / (γ ^ 2 * δ ^ (2 * p.κ)) with hEd
  set X := ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)) with hXd
  have hX0 : 0 ≤ X := div_nonneg hε0 (by positivity)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hDK0 := hp.CDK
  have hr1 : 0 ≤ (n : ℝ) * p.CDK * X := by positivity
  have hr2 : 0 ≤ p.CB * p.CDK * X := mul_nonneg (mul_nonneg hp.CB hDK0) hX0
  have hr4 : 0 ≤ 2 * (n : ℝ) * p.CDK * X := by positivity
  have hr5 : 0 ≤ p.CNd * p.CDK * X := mul_nonneg (mul_nonneg hp.CNd hDK0) hX0
  have hr6 : 0 ≤ p.CNtd * p.CDK * X := mul_nonneg (mul_nonneg hp.CNtd hDK0) hX0
  have hK0 : AdmIA D H ωstar E₀ r (r - δ) β ε s p.sK p.sB p.sT p.sLt p.sN p.sNt p.t K :=
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
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  have hG'3 : ∀ θ ∈ complexStrip n (r - 3 * δ), IsUnit (gramMatrix K' θ).det :=
    fun θ hθ => (hfr θ hθ).unit
  have hω' : ‖s' • ωstar - s • ωstar‖ ≤ p.CDw * E := hsd
  have hab : ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖torsionAB H K' θ - torsionAB H K θ‖ ≤ p.CDab * (p.CDK * X) := fun θ hθ => by
    have := torsionAB_sub_le hp hpn hSt hd1 hd2 (K := K) (K' := K') (β := β) (d := p.CDK * E)
      (δ := δ) hδ hδD (hK.mem θ (hsub3r hθ)) (hK'𝔅 θ (hsub32 hθ)) (hK.ball_sub θ (hsub3r hθ))
      (hdist θ (hsub32 hθ)) hβ (hK0.normalT θ (hsub3r hθ)) ((hN'θ θ hθ).trans hcN)
      (by rw [hD]; exact hfr θ hθ)
    rwa [hD] at this
  refine ⟨?_, hs1', hen, hE, fun θ hθ => ⟨hdist θ (hsub32 hθ), ?_⟩, hab, ?_, hray'⟩
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
        error_le := fun θ hθ => herr θ (hsub32 hθ) }
  · have := (hfr θ hθ).dDK
    rwa [← mul_assoc] at this
  · have e : ‖s' • ωstar - s • ωstar‖ = |s' - s| * ‖ωstar‖ :=
      (KAM.Iso.Apost.ray (σω := σω) hS.dio).2.2.2.1 s s'
    rw [← e]
    exact hω'

end KAM.Iso.Sharp2.RouteA.Ref

end
