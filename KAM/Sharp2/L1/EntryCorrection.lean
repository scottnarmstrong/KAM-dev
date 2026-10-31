/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.L1.EntryA
public import KAM.Sharp2.L1.NormsOps
public import KAM.Sharp2.L1.NormsProduct
public import KAM.Sharp2.L1.Solve
public import KAM.Sharp2.RouteA.Correction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The correction of the ℓ¹ entry step (package B10c)

Blueprint `bp:p2s2l1:entryA` of `blueprint/parts/p2s2-l1hybrid.tex`, the correction: B9's
`KAM.Sharp2.RouteA.correction_boundsA` with every solve bounded by the smaller of its sup bound and
its ℓ¹ bound (`KAM.Sharp2.L1.l1_cohR`, `KAM.Sharp2.L1.l1_cohR_real`):

* `𝓡ηᴺ`: `min {c σ_{Lᵀ}, G₀ a_N g} u` on `T_{r-δ}` (the ℓ¹ solve at the bite `δ`);
* `⟨T 𝓡ηᴺ⟩`: `min {t, t_ℝ} min {c_a σ_{Lᵀ}, G_ρ a_N g} u` (real points, the full bite `r`);
* `ξᴸ = 𝓡 gᴸ`: `min {c C_g, C¹_ξᴸ} E` on `T_{r-2δ}`, where `gᴸ = T ξᴺ - ηᴸ` is bounded in ℓ¹ by the
  Wiener product (`L1Mat.mulVec`).

`EntryData` is the ℓ¹ data at a strip `r` and a bite `δ`; `EntryHypA` is `EntryData` at `(ρ, δ₀)`.
The conclusion also carries the ℓ¹ bounds of `ξᴺ` on `T_{r-δ}` and of `ξᴸ` on `T_{r-2δ}` used by the
ℓ¹ frame increment.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology KAM.Sharp.Engine

namespace KAM.Sharp2.L1

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2.RouteA

variable {n : ℕ} {τ M : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

/-- The ℓ¹ entry data at the strip `r` and the bite `δ`, with the current error `ε`. -/
structure EntryData (E : EntryA) (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (r δ ε : ℝ) : Prop where
  l1EtaN : L1Vec r (etaN h K ω) (E.aN * ε)
  l1EtaL : L1Vec r (etaL h K ω) (E.aL * ε)
  l1Torsion : L1Mat (r - δ) (torsion h K ω) E.t1
  realTorsion : ∀ x : Fin n → ℝ, ‖torsion h K ω (fun i => (x i : ℂ))‖ ≤ E.tR
  gam0 : smallDivisorSup ω δ ≤ E.G0
  gamρ : smallDivisorSup ω r ≤ E.Gρ
  frame : ∀ F, E.frame = some F → L1Mat r (tangentMat K) F.nuK ∧ L1Mat r (normalMat K) F.nuN

/-- `EntryHypA` is the entry data at `(ρ, δ₀)`. -/
theorem EntryHypA.toData {N : NumA} {E : EntryA} {h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ}
    {K : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)} {ω : Fin N.n → ℝ} {e : ℝ}
    (hE : EntryHypA N E h K ω e) : EntryData E h K ω (N.r 0) (N.δ 0) e := by
  have hr : N.r 0 = N.ρ := rSeq_zero
  rw [hr]
  exact ⟨hE.l1EtaN, hE.l1EtaL, hE.l1Torsion, hE.realTorsion, hE.gam0, hE.gamρ, hE.frame⟩

/-- The solve bounds of the entry step with the constants of `bp:p2s2l1:constA`: on `T_{r-δ}` the
bounds of `ξᴺ`, `gᴸ`; on `T_{r-2δ}` those of `ξ`, `ΔK`, `∂_ω ξ`; and the ℓ¹ bounds of `ξᴺ` on
`T_{r-δ}`, of `ξᴸ` on `T_{r-2δ}`. -/
theorem entry_correction_bounds {p : StepInA} {E : EntryA} (hp : p.Pos) (hE : E.Wf)
    (hfix : p.iso = false) (hΘ : p.Θ = 0)
    (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ) (hγb : γ ≤ p.γb) {Ω : Set (Fin n → ℝ)}
    (hω : ω ∈ Ω) {r β ε δ b cb : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : AdmA 𝔅 h ω r (r - δ) β ε p.sK p.sB p.sT p.sLt p.sN p.sNt p.t K)
    (hδ : 0 < δ) (hδD : δ ≤ p.δ) (h2δ : 2 * δ < r)
    (hc : SDConst n p.κ γ δ p.c Ω) (hcb : SDConst n p.κ γ b cb Ω) (hbr : b ≤ r)
    (hca : cb * b ^ (-p.κ) ≤ p.ca * δ ^ (-p.κ)) (hD : EntryData E h K ω r δ ε) :
    (∀ θ ∈ complexStrip n (r - δ),
      ‖triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤
        Ent.CXiN p E * (ε / (γ * δ ^ p.κ)) ∧
      ‖triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤
        Ent.CG p E * (ε / (γ * δ ^ p.κ))) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖xi h K ω θ‖ ≤ Ent.CXi p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
      ‖correction h K ω θ‖ ≤ Ent.CDK p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
      ‖fderiv ℂ (xi h K ω) θ (fun l => (ω l : ℂ))‖ ≤ Ent.CDXi p E * (ε / (γ * δ ^ p.κ))) ∧
    L1Vec (r - δ) (triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω))
      (Ent.CXiN1 p E * (ε / (γ * δ ^ p.κ))) ∧
    L1Vec (r - 2 * δ) (triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω))
      (Ent.CXiL1 p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ)))) := by
  have hk := Ent.nonneg hp hE
  have hr := hK.r_pos
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hτ0 : 0 ≤ τ := by
    have h1 := hS.tau_ge
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hS.two_le
    linarith
  have hr1 : 0 < r - δ := by linarith
  have hδr : δ < r := by linarith
  have hδr1 : δ < r - δ := by linarith
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
  have hTinv : IsUnit (avg (torsion h K ω)).det := by rw [← hTavg]; exact hK.twist.1
  have hσ : ‖(avg (torsion h K ω))⁻¹‖ ≤ p.sT := by rw [← hTavg]; exact hK.twist.2
  have hηN0 : avg (etaN h K ω) = 0 := (exactness hS hr hK.holo hK.primary hK𝔅).2
  have hHL : ∀ θ ∈ complexStrip n r, ‖etaL h K ω θ‖ ≤ p.sNt * ε := fun θ hθ =>
    norm_etaL_le (hK.normalT θ hθ) (hK.error_le θ hθ)
  have hHN : ∀ θ ∈ complexStrip n r, ‖etaN h K ω θ‖ ≤ p.sLt * ε := fun θ hθ =>
    norm_etaN_le (hK.tangentT θ hθ) (hK.error_le θ hθ)
  have hηLd := Correction.diffOn_etaL hηd
  have hηNd := Correction.diffOn_etaN hηd
  have hηLp := Correction.periodic_etaL hηp
  have hηNp := Correction.periodic_etaN hηp
  obtain ⟨⟨hg0, hXNd, hXNp, hgd', hgp', hXLd, -⟩, ⟨hdXN, hdXL⟩, -, -⟩ :=
    triangular hS hr hδ h2δ (ηL := etaL h K ω) (ηN := etaN h K ω) (T := torsion h K ω)
      (HL := p.sNt * ε) (HN := p.sLt * ε) (HT := p.t) (σ := p.sT)
      hηLd hηLp hηNd hηNp hHL hHN hηN0 hTd hTp hK.tors hTinv hσ
  -- the scales
  obtain ⟨sU, sE, -, -, -, -, -, -⟩ := scales (ε := ε) (κ := p.κ) hγ hδ
  set u := ε / (γ * δ ^ p.κ) with hu
  set E' := ε / (γ ^ 2 * δ ^ (2 * p.κ)) with hE'
  have hgd0 := StepInA.gd_le hp hγ hγb hδ hδD
  have hpd : 0 < γ * δ ^ p.κ := mul_pos hγ (Real.rpow_pos_of_pos hδ _)
  have hu0 : 0 ≤ u := div_nonneg hε0 hpd.le
  have hE0 : 0 ≤ E' := div_nonneg hε0 (by positivity)
  have hεu : ε ≤ p.g * u := by rw [sU]; exact mul_le_mul_of_nonneg_right hgd0 hu0
  have huE : u ≤ p.g * E' := by rw [sE]; exact mul_le_mul_of_nonneg_right hgd0 hE0
  have hNt0 := hp.sNt
  have hLt0 := hp.sLt
  have ht0 := hp.t
  have hT0 := hp.sT
  have hc0 := hp.c
  have hg0' := hp.g
  have haN := hE.aN
  have haL := hE.aL
  have hG0 := hE.G0
  have hGρ := hE.Gρ
  have hΓ0 : 0 ≤ smallDivisorSup ω δ := smallDivisorSup_nonneg ω δ
  have hε' : p.sNt * ε ≤ p.sNt * p.g * u := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hεu hNt0
  -- the ℓ¹ solve of `ηᴺ` at the bite `δ`
  obtain ⟨hU1, hU1s⟩ := l1_cohR hS.dio hγ hτ0 hδ hδr hηNd hηNp hηN0 hD.l1EtaN
  have hUl1 : smallDivisorSup ω δ * (E.aN * ε) ≤ Ent.cN1 p E * u := by
    calc smallDivisorSup ω δ * (E.aN * ε) ≤ E.G0 * (E.aN * (p.g * u)) :=
          mul_le_mul hD.gam0 (mul_le_mul_of_nonneg_left hεu haN) (by positivity) hG0
      _ = Ent.cN1 p E * u := by unfold Ent.cN1; ring
  -- `uᴺ = 𝓡ηᴺ`
  have hU : ∀ θ ∈ complexStrip n (r - δ), ‖triU ω (etaN h K ω) θ‖ ≤
      min (p.c * p.sLt) (Ent.cN1 p E) * u := by
    intro θ hθ
    rw [min_mul_of_nonneg _ _ hu0]
    refine le_min ?_ ((hU1s θ hθ).trans hUl1)
    have := hc.sol ω hω hδr (etaN h K ω) (p.sLt * ε) hηNd hηNp hHN hηN0 θ hθ
    rw [CorrectionSharp.gamma_mul_eq hγ hδ] at this
    calc _ ≤ _ := this
      _ = p.c * p.sLt * u := by ring
  -- the average `⟨T 𝓡ηᴺ⟩` at real points
  have hav : ‖avg (fun θ => torsion h K ω θ *ᵥ triU ω (etaN h K ω) θ)‖ ≤
      Ent.tavg p E * (Ent.cavg p E * u) := by
    refine norm_torusAverage_le fun x _ => ?_
    have hT : ‖torsion h K ω (fun i => (x i : ℂ))‖ ≤ Ent.tavg p E :=
      le_min (hK.tors _ (ofReal_mem_complexStrip hr1 x)) (hD.realTorsion x)
    have hUs : ‖triU ω (etaN h K ω) (fun i => (x i : ℂ))‖ ≤ p.ca * p.sLt * u := by
      have h1 := hcb.real ω hω hbr (etaN h K ω) (p.sLt * ε) hηNd hηNp hHN hηN0 x
      have h2 : cb * γ⁻¹ * b ^ (-p.κ) * (p.sLt * ε) ≤ p.ca * γ⁻¹ * δ ^ (-p.κ) * (p.sLt * ε) := by
        have hi : 0 ≤ γ⁻¹ := (inv_pos.2 hγ).le
        calc cb * γ⁻¹ * b ^ (-p.κ) * (p.sLt * ε) = (cb * b ^ (-p.κ)) * (γ⁻¹ * (p.sLt * ε)) := by
              ring
          _ ≤ (p.ca * δ ^ (-p.κ)) * (γ⁻¹ * (p.sLt * ε)) :=
              mul_le_mul_of_nonneg_right hca (by positivity)
          _ = _ := by ring
      have h3 := h1.trans h2
      rw [CorrectionSharp.gamma_mul_eq hγ hδ] at h3
      calc _ ≤ _ := h3
        _ = p.ca * p.sLt * u := by ring
    have hUl : ‖triU ω (etaN h K ω) (fun i => (x i : ℂ))‖ ≤ E.Gρ * E.aN * p.g * u := by
      have h1 := l1_cohR_real hS.dio hγ hτ0 hr hηNd hηNp hηN0 hD.l1EtaN x
      calc _ ≤ _ := h1
        _ ≤ E.Gρ * (E.aN * (p.g * u)) :=
            mul_le_mul hD.gamρ (mul_le_mul_of_nonneg_left hεu haN) (by positivity) hGρ
        _ = E.Gρ * E.aN * p.g * u := by ring
    have hUm : ‖triU ω (etaN h K ω) (fun i => (x i : ℂ))‖ ≤ Ent.cavg p E * u := by
      unfold Ent.cavg
      rw [min_mul_of_nonneg _ _ hu0]
      exact le_min hUs hUl
    exact (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul hT hUm (norm_nonneg _) hk.tavg)
  have hCS : Ent.CS p E = p.sT * (p.sNt * p.g + Ent.tavg p E * Ent.cavg p E) := by
    simp [Ent.CS, hfix]
  have hX0 : ‖triXi0 ω (etaL h K ω) (etaN h K ω) (torsion h K ω)‖ ≤ Ent.CS p E * u := by
    have h1 : ‖avg (etaL h K ω)‖ ≤ p.sNt * ε := norm_torusAverage_le_of_strip_bound hr hHL
    unfold triXi0
    calc _ ≤ ‖(avg (torsion h K ω))⁻¹‖ *
          ‖avg (etaL h K ω) + avg (fun θ => torsion h K ω θ *ᵥ triU ω (etaN h K ω) θ)‖ :=
          Matrix.linfty_opNorm_mulVec _ _
      _ ≤ p.sT * (p.sNt * p.g * u + Ent.tavg p E * (Ent.cavg p E * u)) :=
          mul_le_mul hσ ((norm_add_le _ _).trans (add_le_add (h1.trans hε') hav)) (norm_nonneg _)
            hT0
      _ = Ent.CS p E * u := by rw [hCS]; ring
  -- `ξᴺ`, `gᴸ` in sup
  have hXN : ∀ θ ∈ complexStrip n (r - δ),
      ‖triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤ Ent.CXiN p E * u := by
    intro θ hθ
    calc _ ≤ ‖triXi0 ω (etaL h K ω) (etaN h K ω) (torsion h K ω)‖ +
          ‖triU ω (etaN h K ω) θ‖ := norm_sub_le _ _
      _ ≤ Ent.CS p E * u + min (p.c * p.sLt) (Ent.cN1 p E) * u := add_le_add hX0 (hU θ hθ)
      _ = Ent.CXiN p E * u := by unfold Ent.CXiN; ring
  have hCG : Ent.CG p E = p.t * Ent.CXiN p E + p.sNt * p.g := by simp [Ent.CG, hΘ]
  have hGL : ∀ θ ∈ complexStrip n (r - δ),
      ‖triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤ Ent.CG p E * u := by
    intro θ hθ
    calc _ ≤ p.t * (Ent.CXiN p E * u) + p.sNt * ε :=
          Triangular.norm_triGL_le (fun θ hθ => hHL θ (hsub1 hθ)) hK.tors hXN hθ
      _ ≤ p.t * (Ent.CXiN p E * u) + p.sNt * p.g * u := add_le_add le_rfl hε'
      _ = Ent.CG p E * u := by rw [hCG]; ring
  -- `ξᴺ` and `gᴸ` in ℓ¹ on `T_{r-δ}`
  have hUd : DifferentiableOn ℂ (triU ω (etaN h K ω)) (complexStrip n (r - δ)) :=
    differentiableOn_cohR_l1 hS.dio hγ hτ0 hδ hδr hD.l1EtaN
  have hXN1 : L1Vec (r - δ) (triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω))
      (Ent.CXiN1 p E * u) := by
    have h1 := L1Vec.sub hr1 (differentiableOn_const _) hUd
      (L1Vec.const hr1.le (triXi0 ω (etaL h K ω) (etaN h K ω) (torsion h K ω))) hU1
    refine L1Vec.le (L1Vec.congr_real (fun x => rfl) h1) ?_
    calc ‖triXi0 ω (etaL h K ω) (etaN h K ω) (torsion h K ω)‖ + smallDivisorSup ω δ * (E.aN * ε)
        ≤ Ent.CS p E * u + Ent.cN1 p E * u := add_le_add hX0 hUl1
      _ = Ent.CXiN1 p E * u := by unfold Ent.CXiN1; ring
  have hTd1 : DifferentiableOn ℂ (torsion h K ω) (complexStrip n (r - δ)) := hTd.mono hsub1
  have hTp1 : IsPeriodicOn (torsion h K ω) (r - δ) := fun j z hz => hTp j z (hsub1 hz)
  have hTX := L1Mat.mulVec hr1 hTd1 hTp1 hXNd hXNp hD.l1Torsion hXN1
  have hTXd : DifferentiableOn ℂ
      (fun θ => torsion h K ω θ *ᵥ triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ)
      (complexStrip n (r - δ)) := hTd1.matrix_mulVec hXNd
  have hGL1 : L1Vec (r - δ) (triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω))
      ((E.t1 * Ent.CXiN1 p E + p.Θ * Ent.CS p E + E.aL * p.g) * u) := by
    have h1 := L1Vec.sub hr1 hTXd (hηLd.mono hsub1) hTX (L1Vec.mono hr1.le (by linarith) hD.l1EtaL)
    refine L1Vec.le (L1Vec.congr_real (fun x => rfl) h1) ?_
    have hΘ0 : 0 ≤ p.Θ * Ent.CS p E := mul_nonneg hp.Θ hk.CS
    calc E.t1 * (Ent.CXiN1 p E * u) + E.aL * ε ≤ E.t1 * (Ent.CXiN1 p E * u) + E.aL * (p.g * u) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hεu haL)
      _ ≤ (E.t1 * Ent.CXiN1 p E + p.Θ * Ent.CS p E + E.aL * p.g) * u := by
          nlinarith [mul_nonneg hΘ0 hu0]
  -- `ξᴸ = 𝓡 gᴸ`
  obtain ⟨hXL1', hXL1s⟩ := l1_cohR hS.dio hγ hτ0 hδ hδr1 hgd' hgp' hg0 hGL1
  have e2 : r - δ - δ = r - 2 * δ := by ring
  rw [e2] at hXL1' hXL1s
  have hl1L : smallDivisorSup ω δ * ((E.t1 * Ent.CXiN1 p E + p.Θ * Ent.CS p E + E.aL * p.g) * u) ≤
      Ent.CXiL1 p E * E' := by
    have hA0 : 0 ≤ E.t1 * Ent.CXiN1 p E + p.Θ * Ent.CS p E + E.aL * p.g := by
      have := hE.t1; have := hk.CXiN1; have := hp.Θ; have := hk.CS; positivity
    calc smallDivisorSup ω δ * ((E.t1 * Ent.CXiN1 p E + p.Θ * Ent.CS p E + E.aL * p.g) * u)
        ≤ E.G0 * ((E.t1 * Ent.CXiN1 p E + p.Θ * Ent.CS p E + E.aL * p.g) * (p.g * E')) :=
          mul_le_mul hD.gam0 (mul_le_mul_of_nonneg_left huE hA0) (by positivity) hG0
      _ = Ent.CXiL1 p E * E' := by unfold Ent.CXiL1; ring
  have hXLE : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤ Ent.CXiL p E * E' := by
    intro θ hθ
    unfold Ent.CXiL
    rw [min_mul_of_nonneg _ _ hE0]
    refine le_min ?_ ((hXL1s θ hθ).trans hl1L)
    have h2 := hc.sol ω hω hδr1 (triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω))
      (Ent.CG p E * u) hgd' hgp' hGL hg0
    rw [e2] at h2
    have := h2 θ hθ
    rw [CorrectionSharp.gamma_mul_u_eq hγ hδ, mul_div_assoc] at this
    exact this
  have hXNE : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤ p.g * Ent.CXiN p E * E' := by
    intro θ hθ
    calc _ ≤ Ent.CXiN p E * u := hXN θ (hsub hθ)
      _ ≤ Ent.CXiN p E * (p.g * E') := mul_le_mul_of_nonneg_left huE hk.CXiN
      _ = p.g * Ent.CXiN p E * E' := by ring
  have hXi : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖xi h K ω θ‖ ≤ Ent.CXi p E * E' := fun θ hθ =>
    Correction.norm_sumElim_le
      ((hXLE θ hθ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE0))
      ((hXNE θ hθ).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hE0))
  refine ⟨fun θ hθ => ⟨hXN θ hθ, hGL θ hθ⟩, fun θ hθ => ⟨hXi θ hθ, ?_, ?_⟩, hXN1,
    L1Vec.le hXL1' hl1L⟩
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
      _ ≤ p.sK * (Ent.CXiL p E * E') + p.sN * (p.g * Ent.CXiN p E * E') :=
          add_le_add (mul_le_mul (hK.tangent_le hθr) (hXLE θ hθ) (norm_nonneg _) hp.sK)
            (mul_le_mul (hK.normal θ hθr) (hXNE θ hθ) (norm_nonneg _) hp.sN)
      _ = Ent.CDK p E * E' := by unfold Ent.CDK; ring
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
        _ ≤ Ent.CDXi p E * u := mul_le_mul_of_nonneg_right (le_max_right _ _) hu0

end KAM.Sharp2.L1

end
