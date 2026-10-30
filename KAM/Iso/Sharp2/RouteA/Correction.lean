/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.Correction
public import KAM.Iso.Sharp.Correction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The isoenergetic correction of route A

The route-A deltas (`bp:p2s2:constantsA`, `bpI:p2s2:g1`) of `bpI:p2s:correction`:

* `AdmIA`: the admissibility of the isoenergetic route A: every cap of `(R1)–(R3)`, the bordered
  twist,
  the energy error;
* `sum_norm_energyRow_le_ref`: `∑_b |Y_b| ≤ M_{h1} |N|`;
* `norm_bordSol_le_avg`: the bordered solution with the averages `⟨T 𝓡ηᴺ⟩`, `⟨Y 𝓡ηᴺ⟩` at real
  points;
* `norm_fderiv_frameMat_le`: `|∂_ω P| ≤ C_P`, refined;
* `iso_correction_boundsA`: the bounds of `ξ^ω, ξᴺ, gᴸ, ξ, ΔK, ∂_ω ξ, ∂_ω ΔK, ξᴸ, Δω`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Sharp2.RouteA

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA

variable {n : ℕ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {ωstar : Fin n → ℝ}

/-- Admissibility of the isoenergetic route A at the strip `r`, at the point `s` of the ray. -/
structure AdmIA {n : ℕ} (D : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ωstar : Fin n → ℝ) (E₀ r rT β ε s mK mB mT mLt mN mNt mH :
        ℝ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) : Prop where
  r_pos : 0 < r
  β_pos : 0 < β
  ε_nonneg : 0 ≤ ε
  holo : DifferentiableOn ℂ K (complexStrip n r)
  primary : IsPrimaryOnStrip K r
  real : IsRealOnReals K
  ball_sub : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ D
  deriv_le : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ mK
  gram : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ mB
  tangentT : ∀ θ ∈ complexStrip n r, ‖(tangentMat K θ)ᵀ‖ ≤ mLt
  normal : ∀ θ ∈ complexStrip n r, ‖normalMat K θ‖ ≤ mN
  normalT : ∀ θ ∈ complexStrip n r, ‖(normalMat K θ)ᵀ‖ ≤ mNt
  tors : ∀ θ ∈ complexStrip n rT, ‖torsion H K (s • ωstar) θ‖ ≤ mH
  error_le : ∀ θ ∈ complexStrip n r, ‖invarianceError H K (s • ωstar) θ‖ ≤ ε
  s_gt : 1 < s
  twist : IsUnit (KAM.Iso.extendedTorsionAverage H K (s • ωstar)).det ∧
    ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ≤ mT
  energy_le : ‖KAM.Iso.energyAverage H K - (E₀ : ℂ)‖ ≤ ε

namespace AdmIA

variable {E₀ r rT β ε s mK mB mT mLt mN mNt mH : ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- Raising the values of the caps. -/
theorem mono {mK' mB' mT' mLt' mN' mNt' mH' : ℝ}
    (hA : AdmIA D H ωstar E₀ r rT β ε s mK mB mT mLt mN mNt mH K) (h1 : mK ≤ mK') (h2 : mB ≤ mB')
    (h3 : mT ≤ mT') (h4 : mLt ≤ mLt') (h5 : mN ≤ mN') (h6 : mNt ≤ mNt') (h7 : mH ≤ mH') :
    AdmIA D H ωstar E₀ r rT β ε s mK' mB' mT' mLt' mN' mNt' mH' K :=
  { hA with
    deriv_le := fun θ hθ => (hA.deriv_le θ hθ).trans h1
    gram := fun θ hθ => ⟨(hA.gram θ hθ).1, (hA.gram θ hθ).2.trans h2⟩
    tangentT := fun θ hθ => (hA.tangentT θ hθ).trans h4
    normal := fun θ hθ => (hA.normal θ hθ).trans h5
    normalT := fun θ hθ => (hA.normalT θ hθ).trans h6
    tors := fun θ hθ => (hA.tors θ hθ).trans h7
    twist := ⟨hA.twist.1, hA.twist.2.trans h3⟩ }

/-- The admissibility of `KAM.Iso.Apost` (the qualitative lemmas of v1 apply). -/
theorem toIso (hA : AdmIA D H ωstar E₀ r rT β ε s mK mB mT mLt mN mNt mH K) (hε : ε ≤ 1) :
    IsoAdmissible mK mB mT D H ωstar E₀ r β ε s K :=
  { r_pos := hA.r_pos
    β_pos := hA.β_pos
    ε_nonneg := hA.ε_nonneg
    ε_le_one := hε
    holo := hA.holo
    primary := hA.primary
    real := hA.real
    ball_sub := hA.ball_sub
    deriv_le := hA.deriv_le
    gram := hA.gram
    error_le := hA.error_le
    s_gt := hA.s_gt
    twist := hA.twist
    energy_le := hA.energy_le }

theorem mem (hA : AdmIA D H ωstar E₀ r rT β ε s mK mB mT mLt mN mNt mH K) :
    ∀ θ ∈ complexStrip n r, K θ ∈ D := fun θ hθ =>
  hA.ball_sub θ hθ (Metric.mem_ball_self hA.β_pos)

theorem tangent_le (hA : AdmIA D H ωstar E₀ r rT β ε s mK mB mT mLt mN mNt mH K) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n r) : ‖tangentMat K θ‖ ≤ mK :=
  (FrameAux.norm_tangentMat K θ).le.trans (hA.deriv_le θ hθ)

end AdmIA

/-- `∑_b |Y_b| ≤ M_{h1} a` at a point with `|DH(K θ)| ≤ M_{h1}`, `|N| ≤ a`. -/
theorem sum_norm_energyRow_le_ref {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    {Mh1 a : ℝ} (hd : ‖fderiv ℂ H (K θ)‖ ≤ Mh1) (hN : ‖normalMat K θ‖ ≤ a) :
    ∑ b, ‖energyRow H K θ b‖ ≤ Mh1 * a := by
  have hg : ∑ s, ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖ ≤ Mh1 :=
    (ExtendedAux.sum_norm_apply_le_opNorm (fderiv ℂ H (K θ))).trans hd
  calc ∑ b, ‖energyRow H K θ b‖
      = ∑ b, ‖∑ s, normalMat K θ s b *
          fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖ := by
        simp only [ExtendedAux.energyRow_apply]
    _ ≤ ∑ b, ∑ s, ‖normalMat K θ s b‖ *
          ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖ :=
        Finset.sum_le_sum fun b _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => (norm_mul _ _).le)
    _ = ∑ s, (∑ b, ‖normalMat K θ s b‖) *
          ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun s _ => (Finset.sum_mul _ _ _).symm
    _ ≤ ∑ s, a * ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖ :=
        Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_right ((rowSum_le_norm _ s).trans hN) (norm_nonneg _)
    _ = a * ∑ s, ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖ :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ a * Mh1 := mul_le_mul_of_nonneg_left hg ((norm_nonneg _).trans hN)
    _ = Mh1 * a := mul_comm _ _

/-- The bordered solution with the averages bounded at real points by `Z ≥ |uᴺ|` on `ℝⁿ`. -/
theorem norm_bordSol_le_avg {ω : Fin n → ℝ} (d : BordData n) {r HL HT HY Z σ : ℝ} (hr : 0 < r)
    (hHL : ∀ θ ∈ complexStrip n r, ‖d.ηL θ‖ ≤ HL)
    (hHT : ∀ x : Fin n → ℝ, ‖d.T (fun i => (x i : ℂ))‖ ≤ HT)
    (hHY : ∀ x : Fin n → ℝ, ∑ b, ‖d.Y (fun i => (x i : ℂ)) b‖ ≤ HY)
    (hU : ∀ x : Fin n → ℝ, ‖triU ω d.ηN (fun i => (x i : ℂ))‖ ≤ Z)
    (hσ : ‖(bordAvg ω d)⁻¹‖ ≤ σ) :
    ‖bordSol ω d‖ ≤ σ * max (HL + HT * Z) (‖d.ηω‖ + HY * Z) := by
  have hHT0 : 0 ≤ HT := (norm_nonneg _).trans (hHT 0)
  have hHY0 : 0 ≤ HY := (Finset.sum_nonneg fun b _ => norm_nonneg _).trans (hHY 0)
  have hσ0 : 0 ≤ σ := (norm_nonneg _).trans hσ
  have h1 : ‖avg d.ηL‖ ≤ HL := norm_torusAverage_le_of_strip_bound hr hHL
  have h2 : ‖avg (fun θ => d.T θ *ᵥ triU ω d.ηN θ)‖ ≤ HT * Z := by
    refine norm_torusAverage_le (f := fun x : Fin n → ℝ => d.T (fun i => (x i : ℂ)) *ᵥ
      triU ω d.ηN (fun i => (x i : ℂ))) fun x _ => ?_
    exact (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul (hHT x) (hU x) (norm_nonneg _) hHT0)
  have h3 : ‖avg (fun θ => d.Y θ ⬝ᵥ triU ω d.ηN θ)‖ ≤ HY * Z := by
    refine norm_torusAverage_le (f := fun x : Fin n → ℝ => d.Y (fun i => (x i : ℂ)) ⬝ᵥ
      triU ω d.ηN (fun i => (x i : ℂ))) fun x _ => ?_
    exact (BorderSolve.norm_dotProduct_le _ _).trans
      (mul_le_mul (hHY x) (hU x) (norm_nonneg _) hHY0)
  have hw : ‖(Sum.elim (avg d.ηL + avg (fun θ => d.T θ *ᵥ triU ω d.ηN θ))
      (fun _ => d.ηω + avg (fun θ => d.Y θ ⬝ᵥ triU ω d.ηN θ)) : Fin n ⊕ Unit → ℂ)‖ ≤
        max (HL + HT * Z) (‖d.ηω‖ + HY * Z) :=
    BorderSolve.norm_sumElim_le ((norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_max_left _
        _)))
      ((norm_add_le _ _).trans ((add_le_add le_rfl h3).trans (le_max_right _ _)))
  calc ‖bordSol ω d‖ ≤ ‖(bordAvg ω d)⁻¹‖ * ‖(Sum.elim (avg d.ηL +
        avg (fun θ => d.T θ *ᵥ triU ω d.ηN θ))
        (fun _ => d.ηω + avg (fun θ => d.Y θ ⬝ᵥ triU ω d.ηN θ)) : Fin n ⊕ Unit → ℂ)‖ :=
        Matrix.linfty_opNorm_mulVec _ _
    _ ≤ σ * max (HL + HT * Z) (‖d.ηω‖ + HY * Z) := mul_le_mul hσ hw (norm_nonneg _) hσ0

/-- `|∂_ω P| ≤ C_P`, from `|L| ≤ σ_K`, `|Lᵀ| ≤ σ_{Lᵀ}`, `|N| ≤ σ_N`, `|B| ≤ σ_B`, `|A|, |Aᵀ| ≤ M₁`,
`|DE| ≤ n`, `|(DE)ᵀ| ≤ 2n`. -/
theorem norm_fderiv_frameMat_le {p : StepInA} (hp : p.Pos) (hpn : p.n = n) {τ M σK σB σT γ : ℝ}
    {ω : Fin n → ℝ} (hS : Standing n τ M σK σB σT D H ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n r) (hL : ‖tangentMat K θ‖ ≤ p.sK)
    (hLt : ‖(tangentMat K θ)ᵀ‖ ≤ p.sLt) (hN : ‖normalMat K θ‖ ≤ p.sN)
    (hB : ‖(gramMatrix K θ)⁻¹‖ ≤ p.sB) (hA : ‖linMat H K θ‖ ≤ p.M1) (hAt : ‖(linMat H K θ)ᵀ‖ ≤ p.M1)
    (hF : ‖errDerivMat H K ω θ‖ ≤ n) (hFt : ‖(errDerivMat H K ω θ)ᵀ‖ ≤ 2 * n) :
    ‖fderiv ℂ (frameMat K) θ (fun l => (ω l : ℂ))‖ ≤ p.CFr := by
  subst hpn
  have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hsK := hp.sK
  have hsB := hp.sB
  have hsN := hp.sN
  have hsLt := hp.sLt
  have hM := hp.M1
  set X := linMat H K θ * tangentMat K θ - errDerivMat H K ω θ with hXdef
  have hX : ‖X‖ ≤ p.M1 * p.sK + p.n :=
    (norm_sub_le _ _).trans (add_le_add ((Matrix.linfty_opNorm_mul _ _).trans
      (mul_le_mul hA hL (norm_nonneg _) hM)) hF)
  have hXt : ‖Xᵀ‖ ≤ p.sLt * p.M1 + 2 * p.n := by
    rw [hXdef, Matrix.transpose_sub, Matrix.transpose_mul]
    exact (norm_sub_le _ _).trans (add_le_add ((Matrix.linfty_opNorm_mul _ _).trans
      (mul_le_mul hLt hAt (norm_nonneg _) hsLt)) hFt)
  have hdL : fderiv ℂ (tangentMat K) θ (fun l => (ω l : ℂ)) = X :=
    TorsionPoly.fderiv_tangentMat_eq hS hK hKD hθ ω
  have hdN := (torsion_identity hS hr hK hKD hG ω θ hθ).2.1
  rw [← hXdef] at hdN
  rw [Identities.fderiv_frameMat hK hG hθ]
  refine (Tools.norm_fromCols_le_add _ _).trans ?_
  rw [hdL, hdN]
  have hW : ‖Xᵀ * tangentMat K θ + (tangentMat K θ)ᵀ * X‖ ≤
      (p.sLt * p.M1 + 2 * p.n) * p.sK + p.sLt * (p.M1 * p.sK + p.n) :=
    (norm_add_le _ _).trans (add_le_add
      ((Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul hXt hL (norm_nonneg _) (by positivity)))
      ((Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul hLt hX (norm_nonneg _) hsLt)))
  have h1 : ‖omegaZeroMatrix p.n * X * (gramMatrix K θ)⁻¹‖ ≤ (p.M1 * p.sK + p.n) * p.sB := by
    refine (Matrix.linfty_opNorm_mul _ _).trans ?_
    rw [norm_omegaZeroMatrix_mul]
    exact mul_le_mul hX hB (norm_nonneg _) (by positivity)
  have h2 : ‖normalMat K θ * (Xᵀ * tangentMat K θ + (tangentMat K θ)ᵀ * X) *
      (gramMatrix K θ)⁻¹‖ ≤
      p.sN * ((p.sLt * p.M1 + 2 * p.n) * p.sK + p.sLt * (p.M1 * p.sK + p.n)) * p.sB := by
    refine (Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul ?_ hB (norm_nonneg _) (by positivity))
    exact (Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul hN hW (norm_nonneg _) hsN)
  calc ‖X‖ + ‖omegaZeroMatrix p.n * X * (gramMatrix K θ)⁻¹ - normalMat K θ *
        (Xᵀ * tangentMat K θ + (tangentMat K θ)ᵀ * X) * (gramMatrix K θ)⁻¹‖
      ≤ (p.M1 * p.sK + p.n) + ((p.M1 * p.sK + p.n) * p.sB +
          p.sN * ((p.sLt * p.M1 + 2 * p.n) * p.sK + p.sLt * (p.M1 * p.sK + p.n)) * p.sB) :=
        add_le_add hX ((norm_sub_le _ _).trans (add_le_add h1 h2))
    _ = p.CFr := by unfold StepInA.CFr; ring

variable {τ M σω ν γ : ℝ}

/-- The route-A bounds of the isoenergetic correction, for a bite `δ ≤ p.δ`. -/
theorem iso_correction_boundsA {p : StepInA} (hp : p.Pos) (hiso : p.iso = true) (hpn : p.n = n)
    (hS : IsoStanding n τ M p.sK p.sB p.sT σω ν ωstar D H γ)
    (hd1 : ∀ z ∈ D, ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ p.M1) (hγb : γ ≤ p.γb)
    {Ω : Set (Fin n → ℝ)} {E₀ r β ε δ b cb s : ℝ} (hω : s • ωstar ∈ Ω)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : AdmIA D H ωstar E₀ r (r - δ) β ε s p.sK p.sB p.sT p.sLt p.sN p.sNt p.t K)
    (hδ : 0 < δ) (hδD : δ ≤ p.δ) (h2δ : 2 * δ < r) (hεδ : ε ≤ δ) (hΘ : ‖s • ωstar‖ ≤ p.Θ)
    (hHY : ∀ θ ∈ complexStrip n r, ∑ b, ‖energyRow H K θ b‖ ≤ p.HY)
    (hc : SDConst n p.κ γ δ p.c Ω) (hcb : SDConst n p.κ γ b cb Ω) (hbr : b ≤ r)
    (hca : cb * b ^ (-p.κ) ≤ p.ca * δ ^ (-p.κ)) :
    ((‖isoXiOmega H K (s • ωstar) E₀‖ ≤ p.CS * (ε / (γ * δ ^ p.κ))) ∧
      ∀ θ ∈ complexStrip n (r - δ),
        ‖bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ ≤ p.CXiN * (ε / (γ * δ ^ p.κ)) ∧
        ‖bordGL (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ ≤ p.CG * (ε / (γ * δ ^ p.κ))) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖isoXi H K (s • ωstar) E₀ θ‖ ≤ p.CXi * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
      ‖isoCorrection H K (s • ωstar) E₀ θ‖ ≤ p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
      ‖fderiv ℂ (isoXi H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ))‖ ≤
        p.CDXi * (ε / (γ * δ ^ p.κ)) ∧
      ‖fderiv ℂ (isoCorrection H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ))‖ ≤
        p.CdK * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
      ‖bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0 θ‖ ≤
        p.c * p.CG * (ε / (γ ^ 2 * δ ^ (2 * p.κ)))) ∧
    ‖isoNewS H K ωstar E₀ s • ωstar - s • ωstar‖ ≤ p.CDw * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) := by
  have hSet := hS.setting hK.s_gt.le
  have hSt := hSet.toStanding
  have hr := hK.r_pos
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hr1 : 0 < r - δ := by linarith
  have hδr : δ < r := by linarith
  have hδ1 : δ ≤ 1 := hδD.trans hp.δ1
  have hτ0 : 0 ≤ τ := by
    have := hS.two_le
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast this
    linarith [hS.tau_ge]
  have hsub : complexStrip n (r - 2 * δ) ⊆ complexStrip n (r - δ) :=
    Triangular.strip_mono (by linarith)
  have hsubr : complexStrip n (r - δ) ⊆ complexStrip n r := Triangular.strip_mono (by linarith)
  have hK𝔅 := hK.mem
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  obtain ⟨⟨-, -, -, -, -, -, -, hPd, -, hTd, -, -, hηd, -, hTc⟩, -, -, -⟩ :=
    frame_basic hSt hr hK.β_pos hK.holo hK.ball_sub hK.deriv_le hK.gram
  obtain ⟨-, hperiod, -⟩ := periodicity hSt hr hK.holo hK.primary hK𝔅
  obtain ⟨-, -, -, -, hTp, -, hηp⟩ := hperiod hGu
  obtain ⟨⟨hYd, hYp, -, -, -, -, -, havg, -⟩, -⟩ :=
    extended_basic hSet hr hK.holo hK.primary hK.real hK𝔅 hGu
  have hηN0 : avg (etaN H K (s • ωstar)) = 0 := (exactness hSt hr hK.holo hK.primary hK𝔅).2
  have hbord : bordAvg (s • ωstar) (isoBordData H K (s • ωstar) E₀) =
      KAM.Iso.extendedTorsionAverage H K (s • ωstar) := by
    rw [havg, torsionAverage_eq_avg H K (s • ωstar) hTc]
    rfl
  have hinv : IsUnit (bordAvg (s • ωstar) (isoBordData H K (s • ωstar) E₀)).det := by
    rw [hbord]
    exact hK.twist.1
  have hσ : ‖(bordAvg (s • ωstar) (isoBordData H K (s • ωstar) E₀))⁻¹‖ ≤ p.sT := by
    rw [hbord]
    exact hK.twist.2
  have hHL : ∀ θ ∈ complexStrip n r, ‖etaL H K (s • ωstar) θ‖ ≤ p.sNt * ε := fun θ hθ =>
    norm_etaL_le (hK.normalT θ hθ) (hK.error_le θ hθ)
  have hHN : ∀ θ ∈ complexStrip n r, ‖etaN H K (s • ωstar) θ‖ ≤ p.sLt * ε := fun θ hθ =>
    norm_etaN_le (hK.tangentT θ hθ) (hK.error_le θ hθ)
  have hHY' : ∀ θ ∈ complexStrip n (r - δ), ∑ b, ‖energyRow H K θ b‖ ≤ p.HY :=
    fun θ hθ => hHY θ (hsubr hθ)
  have hηωe : ‖(isoBordData H K (s • ωstar) E₀).ηω‖ ≤ ε := by
    show ‖-(KAM.Iso.energyAverage H K - (E₀ : ℂ))‖ ≤ ε
    rw [norm_neg]
    exact hK.energy_le
  have hηLd := KAM.Apost.Correction.diffOn_etaL hηd
  have hηNd := KAM.Apost.Correction.diffOn_etaN hηd
  have hηLp := KAM.Apost.Correction.periodic_etaL hηp
  have hηNp := KAM.Apost.Correction.periodic_etaN hηp
  obtain ⟨⟨hXNd, -, hgd, hgp, hg0, hXLd, -⟩, ⟨hb1, hb2, -⟩, -, -, -⟩ :=
    border_solve hγ hτ0 hSt.dio hr hδ h2δ (isoBordData H K (s • ωstar) E₀)
      (HL := p.sNt * ε) (HN := p.sLt * ε) (HT := p.t) (HY := p.HY) (σ := p.sT)
      hηLd hηLp hηNd hηNp hHL hHN hηN0 hTd hTp hYd hYp hK.tors hHY' hinv hσ 0
  -- the scales
  obtain ⟨sU, sE, -, -, -, -, -, -⟩ := scales (ε := ε) (κ := p.κ) hγ hδ
  set u := ε / (γ * δ ^ p.κ) with hu
  set E := ε / (γ ^ 2 * δ ^ (2 * p.κ)) with hE
  have hgd0 := StepInA.gd_le hp hγ hγb hδ hδD
  have hpd : 0 < γ * δ ^ p.κ := mul_pos hγ (Real.rpow_pos_of_pos hδ _)
  have hu0 : 0 ≤ u := div_nonneg hε0 hpd.le
  have hE0 : 0 ≤ E := div_nonneg hε0 (by positivity)
  have hεu : ε ≤ p.g * u := by
    rw [sU]; exact mul_le_mul_of_nonneg_right hgd0 hu0
  have huE : u ≤ p.g * E := by
    rw [sE]; exact mul_le_mul_of_nonneg_right hgd0 hE0
  have hCS : p.CS = p.sT * max (p.sNt * p.g + p.t * p.ca * p.sLt) (p.g + p.ca * p.HY * p.sLt) := by
    simp [StepInA.CS, hiso]
  have hNt0 := hp.sNt
  have hLt0 := hp.sLt
  have ht0 := hp.t
  have hT0 := hp.sT
  have hg0' := hp.g
  have hc0 := hp.c
  have hca0 := hp.ca
  have hY0 := hp.HY
  have hΘ0 := hp.Θ
  have hε' : p.sNt * ε ≤ p.sNt * p.g * u := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hεu hNt0
  -- `uᴺ` on `T_{r-δ}` and at real points
  have hU : ∀ θ ∈ complexStrip n (r - δ), ‖triU (s • ωstar) (etaN H K (s • ωstar)) θ‖ ≤
      p.c * p.sLt * u := by
    intro θ hθ
    have := hc.sol _ hω hδr (etaN H K (s • ωstar)) (p.sLt * ε) hηNd hηNp hHN hηN0 θ hθ
    rw [CorrectionSharp.gamma_mul_eq hγ hδ] at this
    exact this.trans_eq (by ring)
  have hUr : ∀ x : Fin n → ℝ, ‖triU (s • ωstar) (etaN H K (s • ωstar)) (fun i => (x i : ℂ))‖ ≤
      p.ca * p.sLt * u := by
    intro x
    have h1 := hcb.real _ hω hbr (etaN H K (s • ωstar)) (p.sLt * ε) hηNd hηNp hHN hηN0 x
    have hi : 0 ≤ γ⁻¹ := (inv_pos.2 hγ).le
    have h2 : cb * γ⁻¹ * b ^ (-p.κ) * (p.sLt * ε) ≤ p.ca * γ⁻¹ * δ ^ (-p.κ) * (p.sLt * ε) := by
      calc _ = (cb * b ^ (-p.κ)) * (γ⁻¹ * (p.sLt * ε)) := by ring
        _ ≤ (p.ca * δ ^ (-p.κ)) * (γ⁻¹ * (p.sLt * ε)) :=
            mul_le_mul_of_nonneg_right hca (by positivity)
        _ = _ := by ring
    have h3 := h1.trans h2
    rw [CorrectionSharp.gamma_mul_eq hγ hδ] at h3
    exact h3.trans_eq (by ring)
  -- the bordered solution
  have hS0 : ‖bordSol (s • ωstar) (isoBordData H K (s • ωstar) E₀)‖ ≤ p.CS * u := by
    refine (norm_bordSol_le_avg (ω := s • ωstar) (isoBordData H K (s • ωstar) E₀) hr hHL
      (HT := p.t) (HY := p.HY) (Z := p.ca * p.sLt * u)
      (fun x => hK.tors _ (ofReal_mem_complexStrip hr1 x))
      (fun x => hHY' _ (ofReal_mem_complexStrip hr1 x)) hUr hσ).trans ?_
    rw [hCS, mul_assoc p.sT]
    refine mul_le_mul_of_nonneg_left ?_ hT0
    rw [max_mul_of_nonneg _ _ hu0]
    refine max_le_max ?_ ?_
    · calc p.sNt * ε + p.t * (p.ca * p.sLt * u) ≤ p.sNt * p.g * u + p.t * (p.ca * p.sLt * u) :=
            add_le_add hε' le_rfl
        _ = _ := by ring
    · calc ‖(isoBordData H K (s • ωstar) E₀).ηω‖ + p.HY * (p.ca * p.sLt * u) ≤
            p.g * u + p.HY * (p.ca * p.sLt * u) := add_le_add (hηωe.trans hεu) le_rfl
        _ = _ := by ring
  have hXω : ‖isoXiOmega H K (s • ωstar) E₀‖ ≤ p.CS * u :=
    (BorderSolve.norm_bordXiOmega_le _ _).trans hS0
  have e1 : p.CS * u + p.c * p.sLt * u = p.CXiN * u := by unfold StepInA.CXiN; ring
  have hNG : ∀ θ ∈ complexStrip n (r - δ),
      ‖bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ ≤ p.CXiN * u ∧
      ‖bordGL (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ ≤ p.CG * u := by
    intro θ hθ
    obtain ⟨h1, h2⟩ := BorderSolve.norm_bordXiN_bordGL_le (s • ωstar) (isoBordData H K (s • ωstar)
        E₀) hS0 hU
      (fun θ hθ => hHL θ (hsubr hθ)) hK.tors hθ
    rw [e1] at h1 h2
    refine ⟨h1, h2.trans ?_⟩
    calc p.t * (p.CXiN * u) + ‖s • ωstar‖ * (p.CS * u) + p.sNt * ε ≤
        p.t * (p.CXiN * u) + p.Θ * (p.CS * u) + p.sNt * p.g * u :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hΘ
          (mul_nonneg hp.CS hu0))) hε'
      _ = p.CG * u := by unfold StepInA.CG; ring
  have hXL : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0 θ‖ ≤ p.c * p.CG * E := by
    intro θ hθ
    have hδr1 : δ < r - δ := by linarith
    have h2 := hc.sol _ hω hδr1 (bordGL (s • ωstar) (isoBordData H K (s • ωstar) E₀)) (p.CG * u)
      hgd hgp (fun θ hθ => (hNG θ hθ).2) hg0
    have e : r - δ - δ = r - 2 * δ := by ring
    rw [e] at h2
    have h3 := h2 θ hθ
    rw [CorrectionSharp.gamma_mul_u_eq hγ hδ, mul_div_assoc] at h3
    simpa [bordXiL] using h3
  have hXNE : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ ≤ p.g * p.CXiN * E := by
    intro θ hθ
    calc _ ≤ p.CXiN * u := (hNG θ (hsub hθ)).1
      _ ≤ p.CXiN * (p.g * E) := mul_le_mul_of_nonneg_left huE hp.CXiN
      _ = p.g * p.CXiN * E := by ring
  have hXi : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖isoXi H K (s • ωstar) E₀ θ‖ ≤ p.CXi * E :=
    fun θ hθ => KAM.Apost.Correction.norm_sumElim_le
      ((hXL θ hθ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE0))
      ((hXNE θ hθ).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hE0))
  have hξd : DifferentiableOn ℂ (isoXi H K (s • ωstar) E₀) (complexStrip n (r - 2 * δ)) :=
    KAM.Apost.Correction.diffOn_sumElim hXLd (hXNd.mono hsub)
  have hdξ : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖fderiv ℂ (isoXi H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ))‖ ≤ p.CDXi * u := by
    intro θ hθ
    have hopen : complexStrip n (r - 2 * δ) ∈ 𝓝 θ := (isOpen_complexStrip n _).mem_nhds hθ
    have hdL : fderiv ℂ (bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0) θ
        (fun l => ((s • ωstar) l : ℂ)) = bordGL (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ := by
      have h1 := hb1 θ hθ
      simp only [bordGL]
      rw [← h1]
      abel
    have hdN : fderiv ℂ (bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀)) θ
        (fun l => ((s • ωstar) l : ℂ)) = -(etaN H K (s • ωstar) θ) :=
      neg_eq_iff_eq_neg.mp (hb2 θ (hsub hθ))
    rw [show isoXi H K (s • ωstar) E₀ = fun θ =>
      (Sum.elim (bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0 θ)
        (bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ) : Fin n ⊕ Fin n → ℂ) from rfl,
      KAM.Apost.Correction.fderiv_sumElim_apply (hXLd.differentiableAt hopen)
        ((hXNd.mono hsub).differentiableAt hopen), hdL, hdN]
    refine KAM.Apost.Correction.norm_sumElim_le
      (((hNG θ (hsub hθ)).2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hu0)) ?_
    rw [norm_neg]
    calc ‖etaN H K (s • ωstar) θ‖ ≤ p.sLt * ε := hHN θ (hsubr (hsub hθ))
      _ ≤ p.sLt * (p.g * u) := mul_le_mul_of_nonneg_left hεu hLt0
      _ = p.sLt * p.g * u := by ring
      _ ≤ p.CDXi * u := mul_le_mul_of_nonneg_right (le_max_right _ _) hu0
  refine ⟨⟨hXω, hNG⟩, fun θ hθ => ⟨hXi θ hθ, ?_, hdξ θ hθ, ?_, hXL θ hθ⟩, ?_⟩
  · -- `ΔK = L ξᴸ + N ξᴺ`
    have hθr : θ ∈ complexStrip n r := hsubr (hsub hθ)
    rw [← norm_sumVec, CorrectionAux.sumVec_isoCorrection]
    unfold frameMat
    rw [show isoXi H K (s • ωstar) E₀ θ =
      Sum.elim (bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0 θ)
        (bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ) from rfl,
      Matrix.fromCols_mulVec_sumElim]
    calc _ ≤ ‖tangentMat K θ‖ * ‖bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0 θ‖ +
          ‖normalMat K θ‖ * ‖bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ :=
          (norm_add_le _ _).trans (add_le_add (Matrix.linfty_opNorm_mulVec _ _)
            (Matrix.linfty_opNorm_mulVec _ _))
      _ ≤ p.sK * (p.c * p.CG * E) + p.sN * (p.g * p.CXiN * E) :=
          add_le_add (mul_le_mul (hK.tangent_le hθr) (hXL θ hθ) (norm_nonneg _) hp.sK)
            (mul_le_mul (hK.normal θ hθr) (hXNE θ hθ) (norm_nonneg _) hp.sN)
      _ = p.CDK * E := by unfold StepInA.CDK; ring
  · -- `∂_ω ΔK = (∂_ω P) ξ + P ∂_ω ξ`
    have hθ1 : θ ∈ complexStrip n (r - δ) := hsub hθ
    have hθr : θ ∈ complexStrip n r := hsubr hθ1
    have hopen : complexStrip n (r - 2 * δ) ∈ 𝓝 θ := (isOpen_complexStrip n _).mem_nhds hθ
    have hL := hK.tangent_le hθr
    have hA : ‖linMat H K θ‖ ≤ p.M1 := by
      rw [FrameAux.norm_linMat]; exact hd1 _ (hK𝔅 θ hθr)
    have hAt : ‖(linMat H K θ)ᵀ‖ ≤ p.M1 := by
      rw [FrameSharp.linMat_transpose hSt (hK𝔅 θ hθr), norm_mul_omegaZeroMatrix,
        norm_omegaZeroMatrix_mul]
      exact hA
    obtain ⟨hF, hFt⟩ := Geometry.geo_de hSt hK.holo hK𝔅 hK.error_le hδ θ hθ1
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hεδ1 : ε / δ ≤ 1 := (div_le_one hδ).2 hεδ
    have hF' : ‖errDerivMat H K (s • ωstar) θ‖ ≤ n := by
      refine hF.trans (le_of_eq_of_le (mul_div_assoc _ _ _) ?_)
      exact mul_le_of_le_one_right hn hεδ1
    have hFt' : ‖(errDerivMat H K (s • ωstar) θ)ᵀ‖ ≤ 2 * n := by
      refine hFt.trans (le_of_eq_of_le (mul_div_assoc _ _ _) ?_)
      exact mul_le_of_le_one_right (by positivity) hεδ1
    have hdP := norm_fderiv_frameMat_le hp hpn hSt hr hK.holo hK𝔅 hGu hθr hL (hK.tangentT θ hθr)
      (hK.normal θ hθr) (hK.gram θ hθr).2 hA hAt hF' hFt'
    have hPdiff : DifferentiableAt ℂ (frameMat K) θ :=
      hPd.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθr)
    have hPn : ‖frameMat K θ‖ ≤ p.P :=
      (Tools.norm_fromCols_le_add _ _).trans (add_le_add hL (hK.normal θ hθr))
    rw [← norm_sumVec, CorrectionAux.sumVec_fderiv_isoCorrection hPdiff
      (hξd.differentiableAt hopen)]
    calc _ ≤ ‖fderiv ℂ (frameMat K) θ (fun l => ((s • ωstar) l : ℂ)) *ᵥ
            isoXi H K (s • ωstar) E₀ θ‖ +
          ‖frameMat K θ *ᵥ fderiv ℂ (isoXi H K (s • ωstar) E₀) θ
            (fun l => ((s • ωstar) l : ℂ))‖ := norm_add_le _ _
      _ ≤ p.CFr * (p.CXi * E) + p.P * (p.CDXi * u) :=
          add_le_add ((Matrix.linfty_opNorm_mulVec _ _).trans
              (mul_le_mul hdP (hXi θ hθ) (norm_nonneg _) hp.CFr))
            ((Matrix.linfty_opNorm_mulVec _ _).trans
              (mul_le_mul hPn (hdξ θ hθ) (norm_nonneg _) hp.P))
      _ ≤ p.CFr * (p.CXi * E) + p.P * (p.CDXi * (p.g * E)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left huE hp.CDXi) hp.P)
      _ = p.CdK * E := by unfold StepInA.CdK; ring
  · -- `|Δω| = |ξ^ω| |ω|`
    rw [isoNewS_smul_sub, norm_smul, norm_neg, Real.norm_eq_abs]
    calc |(isoXiOmega H K (s • ωstar) E₀).re| * ‖s • ωstar‖
        ≤ ‖isoXiOmega H K (s • ωstar) E₀‖ * ‖s • ωstar‖ :=
          mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (norm_nonneg _)
      _ ≤ p.CS * u * p.Θ := mul_le_mul hXω hΘ (norm_nonneg _) (mul_nonneg hp.CS hu0)
      _ ≤ p.CS * (p.g * E) * p.Θ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huE hp.CS) hΘ0
      _ = p.CDw * E := by unfold StepInA.CDw; ring

end KAM.Iso.Sharp2.RouteA

end
