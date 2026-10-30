/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.Arith
public import KAM.Sharp2.RouteA.Geometry
public import KAM.Sharp.Correction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The size of the correction of route A

* `AdmA`: the admissibility of route A: every cap of `(R1)–(R3)` with its current value;
* `correction_boundsA`: the bounds of `ξᴺ, gᴸ, ξ, ΔK, ∂_ω ξ` with the constants of
  `bp:p2s2:constantsA` (levers L1, L2 and L3). The proof is that of `KAM.Sharp.correction_bounds`,
  with `|ηᴸ| ≤ σ_{Nᵀ} ε`, `|ηᴺ| ≤ σ_{Lᵀ} ε`, `|T| ≤ t`, a small-divisor constant at the bite, and
  the average `⟨T 𝓡ηᴺ⟩` taken at real points (`bp:p2s2sd:avg`).

The bite `δ` is any bite with `δ ≤ p.δ`, so that one record of constants serves the whole tail.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2.RouteA

open KAM KAM.Torus KAM.Apost KAM.Sharp

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

/-- Admissibility of route A at the strip `r`: `β` the ball margin, `ε` the error, and the current
values of the caps of `|DK|, |B|, |⟨T⟩⁻¹|, |Lᵀ|, |N|, |Nᵀ|`; the torsion bound holds on `T_{rT}`. -/
structure AdmA {n : ℕ} (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ω : Fin n → ℝ) (r rT β ε mK mB mT mLt mN mNt mH : ℝ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) : Prop where
  r_pos : 0 < r
  β_pos : 0 < β
  ε_nonneg : 0 ≤ ε
  holo : DifferentiableOn ℂ K (complexStrip n r)
  primary : IsPrimaryOnStrip K r
  real : IsRealOnReals K
  ball_sub : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ 𝔅
  deriv_le : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ mK
  gram : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ mB
  tangentT : ∀ θ ∈ complexStrip n r, ‖(tangentMat K θ)ᵀ‖ ≤ mLt
  normal : ∀ θ ∈ complexStrip n r, ‖normalMat K θ‖ ≤ mN
  normalT : ∀ θ ∈ complexStrip n r, ‖(normalMat K θ)ᵀ‖ ≤ mNt
  tors : ∀ θ ∈ complexStrip n rT, ‖torsion h K ω θ‖ ≤ mH
  twist : IsUnit (torsionAverage h K ω).det ∧ ‖(torsionAverage h K ω)⁻¹‖ ≤ mT
  error_le : ∀ θ ∈ complexStrip n r, ‖invarianceError h K ω θ‖ ≤ ε

namespace AdmA

variable {r rT β ε mK mB mT mLt mN mNt mH : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- Raising the values of the caps. -/
theorem mono {mK' mB' mT' mLt' mN' mNt' mH' : ℝ}
    (hA : AdmA 𝔅 h ω r rT β ε mK mB mT mLt mN mNt mH K) (h1 : mK ≤ mK') (h2 : mB ≤ mB')
    (h3 : mT ≤ mT') (h4 : mLt ≤ mLt') (h5 : mN ≤ mN') (h6 : mNt ≤ mNt') (h7 : mH ≤ mH') :
    AdmA 𝔅 h ω r rT β ε mK' mB' mT' mLt' mN' mNt' mH' K :=
  { hA with
    deriv_le := fun θ hθ => (hA.deriv_le θ hθ).trans h1
    gram := fun θ hθ => ⟨(hA.gram θ hθ).1, (hA.gram θ hθ).2.trans h2⟩
    tangentT := fun θ hθ => (hA.tangentT θ hθ).trans h4
    normal := fun θ hθ => (hA.normal θ hθ).trans h5
    normalT := fun θ hθ => (hA.normalT θ hθ).trans h6
    tors := fun θ hθ => (hA.tors θ hθ).trans h7
    twist := ⟨hA.twist.1, hA.twist.2.trans h3⟩ }

/-- The admissibility of `KAM.Apost` (the qualitative lemmas of v1 apply). -/
theorem toAdmissible (hA : AdmA 𝔅 h ω r rT β ε mK mB mT mLt mN mNt mH K) (hε : ε ≤ 1) :
    Admissible mK mB mT 𝔅 h ω r β ε K :=
  ⟨hA.r_pos, hA.β_pos, hA.ε_nonneg, hε, hA.holo, hA.primary, hA.real, hA.ball_sub, hA.deriv_le,
    hA.gram, hA.twist, hA.error_le⟩

theorem mem (hA : AdmA 𝔅 h ω r rT β ε mK mB mT mLt mN mNt mH K) :
    ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅 := fun θ hθ =>
  hA.ball_sub θ hθ (Metric.mem_ball_self hA.β_pos)

/-- `|L| ≤ m_K`. -/
theorem tangent_le (hA : AdmA 𝔅 h ω r rT β ε mK mB mT mLt mN mNt mH K) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n r) : ‖tangentMat K θ‖ ≤ mK :=
  (FrameAux.norm_tangentMat K θ).le.trans (hA.deriv_le θ hθ)

end AdmA

/-- `|ηᴸ| ≤ |Nᵀ| |E|`. -/
theorem norm_etaL_le {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ} {a ε : ℝ}
    (hN : ‖(normalMat K θ)ᵀ‖ ≤ a) (hE : ‖invarianceError h K ω θ‖ ≤ ε) :
    ‖etaL h K ω θ‖ ≤ a * ε := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hN
  unfold etaL
  rw [norm_neg]
  refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
  rw [norm_mul_omegaZeroMatrix, norm_sumVec]
  exact mul_le_mul hN hE (norm_nonneg _) ha

/-- `|ηᴺ| ≤ |Lᵀ| |E|`. -/
theorem norm_etaN_le {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ} {a ε : ℝ}
    (hL : ‖(tangentMat K θ)ᵀ‖ ≤ a) (hE : ‖invarianceError h K ω θ‖ ≤ ε) :
    ‖etaN h K ω θ‖ ≤ a * ε := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hL
  unfold etaN
  refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
  rw [norm_mul_omegaZeroMatrix, norm_sumVec]
  exact mul_le_mul hL hE (norm_nonneg _) ha

/-- `γ δ^κ ≤ g` for `γ ≤ γ̄`, `δ ≤ D`. -/
theorem StepInA.gd_le {p : StepInA} (hp : p.Pos) {γ δ : ℝ} (hγ : 0 < γ) (hγb : γ ≤ p.γb)
    (hδ : 0 < δ) (hδD : δ ≤ p.δ) : γ * δ ^ p.κ ≤ p.g := by
  have := pow_mul_rpow_le (j := p.κ) 1 hγ hγb hδ hδD (by linarith [hp.κ_ge])
  simpa [StepInA.g] using this

/-- `⟨Y 𝓡 g⟩` at real points from a small-divisor constant at any bite `b ≤ r` (`bp:p2s2sd:avg`
in the form used by the additive step): `|⟨Y 𝓡g⟩| ≤ y ca H/(γδ^κ)`, where `cb b^{-κ} ≤ ca δ^{-κ}`.
    -/
theorem norm_avg_mulVec_cohR_le {κ b cb ca δ r y H : ℝ} {Ω : Set (Fin n → ℝ)} {q : ℕ}
    (hγ : 0 < γ) (hω : ω ∈ Ω) (hcb : SDConst n κ γ b cb Ω) (hbr : b ≤ r)
    (hca : cb * b ^ (-κ) ≤ ca * δ ^ (-κ)) {g : (Fin n → ℂ) → Fin n → ℂ}
    (hg : DifferentiableOn ℂ g (complexStrip n r)) (hgp : IsPeriodicOn g r)
    (hgH : ∀ θ ∈ complexStrip n r, ‖g θ‖ ≤ H) (hg0 : avg g = 0)
    {Y : (Fin n → ℂ) → Matrix (Fin q) (Fin n) ℂ}
    (hY : ∀ x : Fin n → ℝ, ‖Y (fun i => (x i : ℂ))‖ ≤ y) (hy : 0 ≤ y) (hH : 0 ≤ H) :
    ‖avg (fun θ => Y θ *ᵥ cohR ω g θ)‖ ≤ y * (ca * γ⁻¹ * δ ^ (-κ) * H) := by
  refine norm_torusAverage_le (f := fun x : Fin n → ℝ => Y (fun i => (x i : ℂ)) *ᵥ
    cohR ω g (fun i => (x i : ℂ))) fun x _ => ?_
  have h1 := hcb.real ω hω hbr g H hg hgp hgH hg0 x
  have h2 : cb * γ⁻¹ * b ^ (-κ) * H ≤ ca * γ⁻¹ * δ ^ (-κ) * H := by
    have hi : 0 ≤ γ⁻¹ := (inv_pos.2 hγ).le
    calc cb * γ⁻¹ * b ^ (-κ) * H = (cb * b ^ (-κ)) * (γ⁻¹ * H) := by ring
      _ ≤ (ca * δ ^ (-κ)) * (γ⁻¹ * H) := mul_le_mul_of_nonneg_right hca (by positivity)
      _ = _ := by ring
  exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul (hY x) (h1.trans h2) (norm_nonneg _) hy)

/-- Definition `bp:p2s2:constantsA`, the correction: the bounds of `ξᴺ, gᴸ` on `T_{r-δ}` and of
`ξ, ΔK, ∂_ω ξ` on `T_{r-2δ}` for an actual bite `δ ≤ p.δ`. -/
theorem correction_boundsA {p : StepInA} (hp : p.Pos) (hfix : p.iso = false) (hΘ : p.Θ = 0)
    (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ) (hγb : γ ≤ p.γb) {Ω : Set (Fin n → ℝ)}
    (hω : ω ∈ Ω) {r β ε δ b cb : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : AdmA 𝔅 h ω r (r - δ) β ε p.sK p.sB p.sT p.sLt p.sN p.sNt p.t K)
    (hδ : 0 < δ) (hδD : δ ≤ p.δ) (h2δ : 2 * δ < r)
    (hc : SDConst n p.κ γ δ p.c Ω) (hcb : SDConst n p.κ γ b cb Ω) (hbr : b ≤ r)
    (hca : cb * b ^ (-p.κ) ≤ p.ca * δ ^ (-p.κ)) :
    (∀ θ ∈ complexStrip n (r - δ),
      ‖triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤ p.CXiN * (ε / (γ * δ ^ p.κ)) ∧
      ‖triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤ p.CG * (ε / (γ * δ ^ p.κ))) ∧
    ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖xi h K ω θ‖ ≤ p.CXi * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
      ‖correction h K ω θ‖ ≤ p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
      ‖fderiv ℂ (xi h K ω) θ (fun l => (ω l : ℂ))‖ ≤ p.CDXi * (ε / (γ * δ ^ p.κ)) := by
  have hr := hK.r_pos
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hr1 : 0 < r - δ := by linarith
  have hδr : δ < r := by linarith
  have hsub : complexStrip n (r - 2 * δ) ⊆ complexStrip n (r - δ) :=
    Triangular.strip_mono (by linarith)
  have hsub1 : complexStrip n (r - δ) ⊆ complexStrip n r := Triangular.strip_mono (by linarith)
  have hK𝔅 := hK.mem
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, hTd, -, -, hηd, -, hTc⟩, -, -, -⟩ :=
    frame_basic hS hr hK.β_pos hK.holo hK.ball_sub hK.deriv_le hK.gram
  obtain ⟨-, hperiod, -⟩ := periodicity hS hr hK.holo hK.primary hK𝔅
  obtain ⟨-, -, -, -, hTp, -, hηp⟩ := hperiod hGu
  have hTavg : torsionAverage h K ω = avg (torsion h K ω) := torsionAverage_eq_avg h K ω hTc
  have hTinv : IsUnit (avg (torsion h K ω)).det := by
    rw [← hTavg]
    exact hK.twist.1
  have hσ : ‖(avg (torsion h K ω))⁻¹‖ ≤ p.sT := by
    rw [← hTavg]
    exact hK.twist.2
  have hηN0 : avg (etaN h K ω) = 0 := (exactness hS hr hK.holo hK.primary hK𝔅).2
  have hHL : ∀ θ ∈ complexStrip n r, ‖etaL h K ω θ‖ ≤ p.sNt * ε := fun θ hθ =>
    norm_etaL_le (hK.normalT θ hθ) (hK.error_le θ hθ)
  have hHN : ∀ θ ∈ complexStrip n r, ‖etaN h K ω θ‖ ≤ p.sLt * ε := fun θ hθ =>
    norm_etaN_le (hK.tangentT θ hθ) (hK.error_le θ hθ)
  have hηLd := Correction.diffOn_etaL hηd
  have hηNd := Correction.diffOn_etaN hηd
  have hηLp := Correction.periodic_etaL hηp
  have hηNp := Correction.periodic_etaN hηp
  obtain ⟨⟨hg0, hXNd, -, hgd', hgp', hXLd, -⟩, ⟨hdXN, hdXL⟩, -, -⟩ :=
    triangular hS hr hδ h2δ (ηL := etaL h K ω) (ηN := etaN h K ω) (T := torsion h K ω)
      (HL := p.sNt * ε) (HN := p.sLt * ε) (HT := p.t) (σ := p.sT)
      hηLd hηLp hηNd hηNp hHL hHN hηN0 hTd hTp hK.tors hTinv hσ
  -- the scales
  obtain ⟨sU, sE, -, -, -, -, -, -⟩ := scales (ε := ε) (κ := p.κ) hγ hδ
  set u := ε / (γ * δ ^ p.κ) with hu
  set E := ε / (γ ^ 2 * δ ^ (2 * p.κ)) with hE
  have hgd0 := StepInA.gd_le hp hγ hγb hδ hδD
  have hpd : 0 < γ * δ ^ p.κ := mul_pos hγ (Real.rpow_pos_of_pos hδ _)
  have hu0 : 0 ≤ u := div_nonneg hε0 hpd.le
  have hE0 : 0 ≤ E := div_nonneg hε0 (by positivity)
  have hεu : ε ≤ p.g * u := by
    rw [sU]
    exact mul_le_mul_of_nonneg_right hgd0 hu0
  have huE : u ≤ p.g * E := by
    rw [sE]
    exact mul_le_mul_of_nonneg_right hgd0 hE0
  have hCS : p.CS = p.sT * (p.sNt * p.g + p.t * p.ca * p.sLt) := by simp [StepInA.CS, hfix]
  have hCG : p.CG = p.t * p.CXiN + p.sNt * p.g := by simp [StepInA.CG, hΘ]
  have hNt0 := hp.sNt
  have hLt0 := hp.sLt
  have ht0 := hp.t
  have hT0 := hp.sT
  have hc0 := hp.c
  have hg0' := hp.g
  have hε' : p.sNt * ε ≤ p.sNt * p.g * u := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hεu hNt0
  -- `ξᴺ₀`
  have hU : ∀ θ ∈ complexStrip n (r - δ), ‖triU ω (etaN h K ω) θ‖ ≤ p.c * p.sLt * u := by
    intro θ hθ
    have := hc.sol ω hω hδr (etaN h K ω) (p.sLt * ε) hηNd hηNp hHN hηN0 θ hθ
    rw [CorrectionSharp.gamma_mul_eq hγ hδ] at this
    calc _ ≤ _ := this
      _ = p.c * p.sLt * u := by ring
  have hav : ‖avg (fun θ => torsion h K ω θ *ᵥ triU ω (etaN h K ω) θ)‖ ≤
      p.t * (p.ca * p.sLt * u) := by
    have := norm_avg_mulVec_cohR_le (y := p.t) hγ hω hcb hbr hca hηNd hηNp hHN hηN0
      (Y := torsion h K ω) (fun x => hK.tors _ (ofReal_mem_complexStrip hr1 x)) ht0
      (mul_nonneg hLt0 hε0)
    rw [CorrectionSharp.gamma_mul_eq hγ hδ] at this
    calc _ ≤ _ := this
      _ = p.t * (p.ca * p.sLt * u) := by ring
  have hX0 : ‖triXi0 ω (etaL h K ω) (etaN h K ω) (torsion h K ω)‖ ≤ p.CS * u := by
    have h1 : ‖avg (etaL h K ω)‖ ≤ p.sNt * ε := norm_torusAverage_le_of_strip_bound hr hHL
    unfold triXi0
    calc _ ≤ ‖(avg (torsion h K ω))⁻¹‖ *
          ‖avg (etaL h K ω) + avg (fun θ => torsion h K ω θ *ᵥ triU ω (etaN h K ω) θ)‖ :=
          Matrix.linfty_opNorm_mulVec _ _
      _ ≤ p.sT * (p.sNt * p.g * u + p.t * (p.ca * p.sLt * u)) :=
          mul_le_mul hσ ((norm_add_le _ _).trans (add_le_add (h1.trans hε') hav)) (norm_nonneg _)
            hT0
      _ = p.CS * u := by rw [hCS]; ring
  -- `ξᴺ`, `gᴸ`
  have hXN : ∀ θ ∈ complexStrip n (r - δ),
      ‖triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤ p.CXiN * u := by
    intro θ hθ
    calc _ ≤ ‖triXi0 ω (etaL h K ω) (etaN h K ω) (torsion h K ω)‖ + p.c * p.sLt * u :=
          Triangular.norm_triXiN_le (Γ := 1) (HN := p.c * p.sLt * u)
            (fun θ hθ => by rw [one_mul]; exact hU θ hθ) hθ |>.trans (by rw [one_mul])
      _ ≤ p.CS * u + p.c * p.sLt * u := add_le_add hX0 le_rfl
      _ = p.CXiN * u := by unfold StepInA.CXiN; ring
  have hGL : ∀ θ ∈ complexStrip n (r - δ),
      ‖triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤ p.CG * u := by
    intro θ hθ
    calc _ ≤ p.t * (p.CXiN * u) + p.sNt * ε :=
          Triangular.norm_triGL_le (fun θ hθ => hHL θ (hsub1 hθ)) hK.tors hXN hθ
      _ ≤ p.t * (p.CXiN * u) + p.sNt * p.g * u := add_le_add le_rfl hε'
      _ = p.CG * u := by rw [hCG]; ring
  -- `ξᴸ`
  have hXLE : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤ p.c * p.CG * E := by
    intro θ hθ
    have hδr1 : δ < r - δ := by linarith
    have h2 := hc.sol ω hω hδr1 (triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω)) (p.CG * u)
      hgd' hgp' hGL hg0
    have e : r - δ - δ = r - 2 * δ := by ring
    rw [e] at h2
    have := h2 θ hθ
    rw [CorrectionSharp.gamma_mul_u_eq hγ hδ, mul_div_assoc] at this
    exact this
  have hXNE : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤ p.g * p.CXiN * E := by
    intro θ hθ
    calc _ ≤ p.CXiN * u := hXN θ (hsub hθ)
      _ ≤ p.CXiN * (p.g * E) := mul_le_mul_of_nonneg_left huE hp.CXiN
      _ = p.g * p.CXiN * E := by ring
  have hXi : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖xi h K ω θ‖ ≤ p.CXi * E := fun θ hθ =>
    Correction.norm_sumElim_le
      ((hXLE θ hθ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE0))
      ((hXNE θ hθ).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hE0))
  refine ⟨fun θ hθ => ⟨hXN θ hθ, hGL θ hθ⟩, fun θ hθ => ⟨hXi θ hθ, ?_, ?_⟩⟩
  · -- `ΔK = L ξᴸ + N ξᴺ`
    have hθr : θ ∈ complexStrip n r := hsub1 (hsub hθ)
    rw [← norm_sumVec, Correction.sumVec_correction]
    unfold frameMat
    have hx : xi h K ω θ = Sum.elim (triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ)
        (triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ) := rfl
    rw [hx, Matrix.fromCols_mulVec_sumElim]
    calc _ ≤ ‖tangentMat K θ‖ * ‖triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ +
          ‖normalMat K θ‖ * ‖triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ :=
          (norm_add_le _ _).trans (add_le_add (Matrix.linfty_opNorm_mulVec _ _)
            (Matrix.linfty_opNorm_mulVec _ _))
      _ ≤ p.sK * (p.c * p.CG * E) + p.sN * (p.g * p.CXiN * E) :=
          add_le_add (mul_le_mul (hK.tangent_le hθr) (hXLE θ hθ) (norm_nonneg _) hp.sK)
            (mul_le_mul (hK.normal θ hθr) (hXNE θ hθ) (norm_nonneg _) hp.sN)
      _ = p.CDK * E := by unfold StepInA.CDK; ring
  · -- `∂_ω ξ = (gᴸ, -ηᴺ)`
    have hθ1 : θ ∈ complexStrip n (r - δ) := hsub hθ
    have hopen : (complexStrip n (r - 2 * δ)) ∈ 𝓝 θ := (isOpen_complexStrip n _).mem_nhds hθ
    rw [show xi h K ω = fun θ => (Sum.elim
      (triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ)
      (triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ) : Fin n ⊕ Fin n → ℂ) from rfl,
      Correction.fderiv_sumElim_apply (hXLd.differentiableAt hopen)
        ((hXNd.mono hsub).differentiableAt hopen), hdXL θ hθ, hdXN θ hθ1]
    refine Correction.norm_sumElim_le ((hGL θ hθ1).trans ?_) ?_
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hu0
    · rw [norm_neg]
      calc ‖etaN h K ω θ‖ ≤ p.sLt * ε := hHN θ (hsub1 hθ1)
        _ ≤ p.sLt * (p.g * u) := mul_le_mul_of_nonneg_left hεu hLt0
        _ = p.sLt * p.g * u := by ring
        _ ≤ p.CDXi * u := mul_le_mul_of_nonneg_right (le_max_right _ _) hu0

end KAM.Sharp2.RouteA

end
