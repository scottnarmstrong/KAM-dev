/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.L1.EntryCorrection
public import KAM.Iso.Sharp2.RouteA.Correction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The isoenergetic correction of the ℓ¹ entry step (package B10c)

Blueprint `bpI:p2s2l1:entry` of `blueprint-I/parts/p2s2-iso-l1hybrid.tex`: B9's
`KAM.Iso.Sharp2.RouteA.iso_correction_boundsA` with every solve bounded by the smaller of its sup
and ℓ¹ bounds, at the frequency `s ω*`:

* `uᴺ = 𝓡ηᴺ`: `min {c σ_{Lᵀ}, G₀ a_N g} u` on `T_{r-δ}`, and `min {c_a σ_{Lᵀ}, G_ρ a_N g} u` at real
  points (the bordered averages use `min {t, t_ℝ}`);
* `gᴸ = T ξᴺ + ω ξ^ω - ηᴸ` in ℓ¹ (Wiener product and the constant `ω ξ^ω`, `|ω| ≤ Θ`), and
  `ξᴸ = 𝓡 gᴸ` bounded by `min {c C_g, C¹_ξᴸ} E` on `T_{r-2δ}`.

The conclusion carries the ℓ¹ bounds of `ξᴺ`, `ξᴸ` and their regularity, used by the frame
increment.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Sharp2.L1

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp2.RouteA KAM.Sharp2.L1

variable {n : ℕ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {ωstar : Fin n → ℝ} {τ M σω ν γ : ℝ}

/-- The bounds of the isoenergetic entry step, for a bite `δ ≤ p.δ`, with the ℓ¹ data at `s ω*`. -/
theorem iso_entry_correction_bounds {p : StepInA} {E : EntryA} (hp : p.Pos) (hE : E.Wf)
    (hiso : p.iso = true) (hpn : p.n = n)
    (hS : IsoStanding n τ M p.sK p.sB p.sT σω ν ωstar D H γ)
    (hd1 : ∀ z ∈ D, ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ p.M1) (hγb : γ ≤ p.γb)
    {Ω : Set (Fin n → ℝ)} {E₀ r β ε δ b cb s : ℝ} (hω : s • ωstar ∈ Ω)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : AdmIA D H ωstar E₀ r (r - δ) β ε s p.sK p.sB p.sT p.sLt p.sN p.sNt p.t K)
    (hδ : 0 < δ) (hδD : δ ≤ p.δ) (h2δ : 2 * δ < r) (hεδ : ε ≤ δ) (hΘ : ‖s • ωstar‖ ≤ p.Θ)
    (hHY : ∀ θ ∈ complexStrip n r, ∑ b, ‖energyRow H K θ b‖ ≤ p.HY)
    (hc : SDConst n p.κ γ δ p.c Ω) (hcb : SDConst n p.κ γ b cb Ω) (hbr : b ≤ r)
    (hca : cb * b ^ (-p.κ) ≤ p.ca * δ ^ (-p.κ)) (hD : EntryData E H K (s • ωstar) r δ ε) :
    ((‖isoXiOmega H K (s • ωstar) E₀‖ ≤ Ent.CS p E * (ε / (γ * δ ^ p.κ))) ∧
      ∀ θ ∈ complexStrip n (r - δ),
        ‖bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ ≤
          Ent.CXiN p E * (ε / (γ * δ ^ p.κ)) ∧
        ‖bordGL (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ ≤
          Ent.CG p E * (ε / (γ * δ ^ p.κ))) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖isoXi H K (s • ωstar) E₀ θ‖ ≤ Ent.CXi p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
      ‖isoCorrection H K (s • ωstar) E₀ θ‖ ≤ Ent.CDK p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
      ‖fderiv ℂ (isoXi H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ))‖ ≤
        Ent.CDXi p E * (ε / (γ * δ ^ p.κ)) ∧
      ‖fderiv ℂ (isoCorrection H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ))‖ ≤
        Ent.CdK p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
      ‖bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0 θ‖ ≤
        Ent.CXiL p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ)))) ∧
    ‖isoNewS H K ωstar E₀ s • ωstar - s • ωstar‖ ≤
      Ent.CDw p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
    L1Vec (r - δ) (bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀))
      (Ent.CXiN1 p E * (ε / (γ * δ ^ p.κ))) ∧
    L1Vec (r - 2 * δ) (bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0)
      (Ent.CXiL1 p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ)))) ∧
    DifferentiableOn ℂ (bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀))
      (complexStrip n (r - δ)) ∧
    IsPeriodicOn (bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀)) (r - δ) ∧
    DifferentiableOn ℂ (bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0)
      (complexStrip n (r - 2 * δ)) ∧
    IsPeriodicOn (bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0) (r - 2 * δ) := by
  have hk := Ent.nonneg hp hE
  have hSet := hS.setting hK.s_gt.le
  have hSt := hSet.toStanding
  have hr := hK.r_pos
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hr1 : 0 < r - δ := by linarith
  have hδr : δ < r := by linarith
  have hδr1 : δ < r - δ := by linarith
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
    rw [hbord]; exact hK.twist.1
  have hσ : ‖(bordAvg (s • ωstar) (isoBordData H K (s • ωstar) E₀))⁻¹‖ ≤ p.sT := by
    rw [hbord]; exact hK.twist.2
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
  obtain ⟨⟨hXNd, hXNp, hgd, hgp, hg0, hXLd, hXLp⟩, ⟨hb1, hb2, -⟩, -, -, -⟩ :=
    border_solve hγ hτ0 hSt.dio hr hδ h2δ (isoBordData H K (s • ωstar) E₀)
      (HL := p.sNt * ε) (HN := p.sLt * ε) (HT := p.t) (HY := p.HY) (σ := p.sT)
      hηLd hηLp hηNd hηNp hHL hHN hηN0 hTd hTp hYd hYp hK.tors hHY' hinv hσ 0
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
  have hT0 := hp.sT
  have hY0 := hp.HY
  have hΘ0 := hp.Θ
  have haN := hE.aN
  have haL := hE.aL
  have hG0 := hE.G0
  have hGρ := hE.Gρ
  have hε' : p.sNt * ε ≤ p.sNt * p.g * u := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hεu hNt0
  -- `uᴺ`: the ℓ¹ solve, on `T_{r-δ}` and at real points
  obtain ⟨hU1, hU1s⟩ := l1_cohR hSt.dio hγ hτ0 hδ hδr hηNd hηNp hηN0 hD.l1EtaN
  have hUl1 : smallDivisorSup (s • ωstar) δ * (E.aN * ε) ≤ Ent.cN1 p E * u := by
    calc smallDivisorSup (s • ωstar) δ * (E.aN * ε) ≤ E.G0 * (E.aN * (p.g * u)) :=
          mul_le_mul hD.gam0 (mul_le_mul_of_nonneg_left hεu haN) (by positivity) hG0
      _ = Ent.cN1 p E * u := by unfold Ent.cN1; ring
  have hU : ∀ θ ∈ complexStrip n (r - δ), ‖triU (s • ωstar) (etaN H K (s • ωstar)) θ‖ ≤
      min (p.c * p.sLt) (Ent.cN1 p E) * u := by
    intro θ hθ
    rw [min_mul_of_nonneg _ _ hu0]
    refine le_min ?_ ((hU1s θ hθ).trans hUl1)
    have := hc.sol _ hω hδr (etaN H K (s • ωstar)) (p.sLt * ε) hηNd hηNp hHN hηN0 θ hθ
    rw [CorrectionSharp.gamma_mul_eq hγ hδ] at this
    exact this.trans_eq (by ring)
  have hUr : ∀ x : Fin n → ℝ, ‖triU (s • ωstar) (etaN H K (s • ωstar)) (fun i => (x i : ℂ))‖ ≤
      Ent.cavg p E * u := by
    intro x
    unfold Ent.cavg
    rw [min_mul_of_nonneg _ _ hu0]
    refine le_min ?_ ?_
    · have h1 := hcb.real _ hω hbr (etaN H K (s • ωstar)) (p.sLt * ε) hηNd hηNp hHN hηN0 x
      have hi : 0 ≤ γ⁻¹ := (inv_pos.2 hγ).le
      have h2 : cb * γ⁻¹ * b ^ (-p.κ) * (p.sLt * ε) ≤ p.ca * γ⁻¹ * δ ^ (-p.κ) * (p.sLt * ε) := by
        calc _ = (cb * b ^ (-p.κ)) * (γ⁻¹ * (p.sLt * ε)) := by ring
          _ ≤ (p.ca * δ ^ (-p.κ)) * (γ⁻¹ * (p.sLt * ε)) :=
              mul_le_mul_of_nonneg_right hca (by positivity)
          _ = _ := by ring
      have h3 := h1.trans h2
      rw [CorrectionSharp.gamma_mul_eq hγ hδ] at h3
      exact h3.trans_eq (by ring)
    · have h1 := l1_cohR_real hSt.dio hγ hτ0 hr hηNd hηNp hηN0 hD.l1EtaN x
      calc _ ≤ _ := h1
        _ ≤ E.Gρ * (E.aN * (p.g * u)) :=
            mul_le_mul hD.gamρ (mul_le_mul_of_nonneg_left hεu haN) (by positivity) hGρ
        _ = E.Gρ * E.aN * p.g * u := by ring
  -- the bordered solution
  have hCS : Ent.CS p E = p.sT * max (p.sNt * p.g + Ent.tavg p E * Ent.cavg p E)
      (p.g + Ent.cavg p E * p.HY) := by simp [Ent.CS, hiso]
  have hS0 : ‖bordSol (s • ωstar) (isoBordData H K (s • ωstar) E₀)‖ ≤ Ent.CS p E * u := by
    refine (norm_bordSol_le_avg (ω := s • ωstar) (isoBordData H K (s • ωstar) E₀) hr hHL
      (HT := Ent.tavg p E) (HY := p.HY) (Z := Ent.cavg p E * u)
      (fun x => le_min (hK.tors _ (ofReal_mem_complexStrip hr1 x)) (hD.realTorsion x))
      (fun x => hHY' _ (ofReal_mem_complexStrip hr1 x)) hUr hσ).trans ?_
    rw [hCS, mul_assoc p.sT]
    refine mul_le_mul_of_nonneg_left ?_ hT0
    rw [max_mul_of_nonneg _ _ hu0]
    refine max_le_max ?_ ?_
    · calc p.sNt * ε + Ent.tavg p E * (Ent.cavg p E * u) ≤
            p.sNt * p.g * u + Ent.tavg p E * (Ent.cavg p E * u) := add_le_add hε' le_rfl
        _ = _ := by ring
    · calc ‖(isoBordData H K (s • ωstar) E₀).ηω‖ + p.HY * (Ent.cavg p E * u) ≤
            p.g * u + p.HY * (Ent.cavg p E * u) := add_le_add (hηωe.trans hεu) le_rfl
        _ = _ := by ring
  have hXω : ‖isoXiOmega H K (s • ωstar) E₀‖ ≤ Ent.CS p E * u :=
    (BorderSolve.norm_bordXiOmega_le _ _).trans hS0
  have e1 : Ent.CS p E * u + min (p.c * p.sLt) (Ent.cN1 p E) * u = Ent.CXiN p E * u := by
    unfold Ent.CXiN; ring
  have hNG : ∀ θ ∈ complexStrip n (r - δ),
      ‖bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ ≤ Ent.CXiN p E * u ∧
      ‖bordGL (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ ≤ Ent.CG p E * u := by
    intro θ hθ
    obtain ⟨h1, h2⟩ := BorderSolve.norm_bordXiN_bordGL_le (s • ωstar)
      (isoBordData H K (s • ωstar) E₀) hS0 hU (fun θ hθ => hHL θ (hsubr hθ)) hK.tors hθ
    rw [e1] at h1 h2
    refine ⟨h1, h2.trans ?_⟩
    calc p.t * (Ent.CXiN p E * u) + ‖s • ωstar‖ * (Ent.CS p E * u) + p.sNt * ε ≤
        p.t * (Ent.CXiN p E * u) + p.Θ * (Ent.CS p E * u) + p.sNt * p.g * u :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hΘ
          (mul_nonneg hk.CS hu0))) hε'
      _ = Ent.CG p E * u := by unfold Ent.CG; ring
  -- `ξᴺ`, `gᴸ` in ℓ¹ on `T_{r-δ}`
  have hUd : DifferentiableOn ℂ (triU (s • ωstar) (etaN H K (s • ωstar)))
      (complexStrip n (r - δ)) :=
    differentiableOn_cohR_l1 hSt.dio hγ hτ0 hδ hδr hD.l1EtaN
  have hXN1 : L1Vec (r - δ) (bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀))
      (Ent.CXiN1 p E * u) := by
    have h1 := L1Vec.sub hr1 (differentiableOn_const _) hUd
      (L1Vec.const hr1.le (bordXi0 (s • ωstar) (isoBordData H K (s • ωstar) E₀))) hU1
    refine L1Vec.le (L1Vec.congr_real (fun x => rfl) h1) ?_
    calc ‖bordXi0 (s • ωstar) (isoBordData H K (s • ωstar) E₀)‖ +
          smallDivisorSup (s • ωstar) δ * (E.aN * ε)
        ≤ Ent.CS p E * u + Ent.cN1 p E * u :=
          add_le_add ((BorderSolve.norm_bordXi0_le _ _).trans hS0) hUl1
      _ = Ent.CXiN1 p E * u := by unfold Ent.CXiN1; ring
  have hTd1 : DifferentiableOn ℂ (torsion H K (s • ωstar)) (complexStrip n (r - δ)) :=
    hTd.mono hsubr
  have hTp1 : IsPeriodicOn (torsion H K (s • ωstar)) (r - δ) := fun j z hz => hTp j z (hsubr hz)
  have hTX := L1Mat.mulVec hr1 hTd1 hTp1 hXNd hXNp hD.l1Torsion hXN1
  set cω : Fin n → ℂ := isoXiOmega H K (s • ωstar) E₀ • (fun a => ((s • ωstar) a : ℂ)) with hcω
  have hcω' : ‖cω‖ ≤ p.Θ * Ent.CS p E * u := by
    rw [hcω, norm_smul]
    have hω1 : ‖(fun a => ((s • ωstar) a : ℂ))‖ ≤ ‖s • ωstar‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
      rw [Complex.norm_real]
      exact norm_le_pi_norm (s • ωstar) a
    calc _ ≤ Ent.CS p E * u * ‖s • ωstar‖ :=
          mul_le_mul hXω hω1 (norm_nonneg _) (mul_nonneg hk.CS hu0)
      _ ≤ Ent.CS p E * u * p.Θ := mul_le_mul_of_nonneg_left hΘ (mul_nonneg hk.CS hu0)
      _ = p.Θ * Ent.CS p E * u := by ring
  have hTXd : DifferentiableOn ℂ
      (fun θ => torsion H K (s • ωstar) θ *ᵥ
        bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ) (complexStrip n (r - δ)) :=
    hTd1.matrix_mulVec hXNd
  have hA1 := L1Vec.add hr1 hTXd (differentiableOn_const cω) hTX (L1Vec.const hr1.le cω)
  have hGL1 : L1Vec (r - δ) (bordGL (s • ωstar) (isoBordData H K (s • ωstar) E₀))
      ((E.t1 * Ent.CXiN1 p E + p.Θ * Ent.CS p E + E.aL * p.g) * u) := by
    have h1 := L1Vec.sub hr1 (hTXd.add (differentiableOn_const cω)) (hηLd.mono hsubr) hA1
      (L1Vec.mono hr1.le (by linarith) hD.l1EtaL)
    refine L1Vec.le (L1Vec.congr_real (fun x => rfl) h1) ?_
    calc E.t1 * (Ent.CXiN1 p E * u) + ‖cω‖ + E.aL * ε ≤
        E.t1 * (Ent.CXiN1 p E * u) + p.Θ * Ent.CS p E * u + E.aL * (p.g * u) :=
          add_le_add (add_le_add le_rfl hcω') (mul_le_mul_of_nonneg_left hεu haL)
      _ = _ := by ring
  -- `ξᴸ = 𝓡 gᴸ`
  obtain ⟨hXL1', hXL1s⟩ := l1_cohR hSt.dio hγ hτ0 hδ hδr1 hgd hgp hg0 hGL1
  have e2 : r - δ - δ = r - 2 * δ := by ring
  rw [e2] at hXL1' hXL1s
  have hl1L : smallDivisorSup (s • ωstar) δ *
      ((E.t1 * Ent.CXiN1 p E + p.Θ * Ent.CS p E + E.aL * p.g) * u) ≤ Ent.CXiL1 p E * E' := by
    have hA0 : 0 ≤ E.t1 * Ent.CXiN1 p E + p.Θ * Ent.CS p E + E.aL * p.g := by
      have := hE.t1; have := hk.CXiN1; have := hk.CS; have := hp.g; positivity
    calc smallDivisorSup (s • ωstar) δ *
          ((E.t1 * Ent.CXiN1 p E + p.Θ * Ent.CS p E + E.aL * p.g) * u)
        ≤ E.G0 * ((E.t1 * Ent.CXiN1 p E + p.Θ * Ent.CS p E + E.aL * p.g) * (p.g * E')) :=
          mul_le_mul hD.gam0 (mul_le_mul_of_nonneg_left huE hA0) (by positivity) hG0
      _ = Ent.CXiL1 p E * E' := by unfold Ent.CXiL1; ring
  have hXLeq : ∀ θ, bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0 θ =
      cohR (s • ωstar) (bordGL (s • ωstar) (isoBordData H K (s • ωstar) E₀)) θ := fun θ => by
    simp [bordXiL]
  have hXL : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0 θ‖ ≤ Ent.CXiL p E * E' := by
    intro θ hθ
    rw [hXLeq]
    unfold Ent.CXiL
    rw [min_mul_of_nonneg _ _ hE0]
    refine le_min ?_ ((hXL1s θ hθ).trans hl1L)
    have h2 := hc.sol _ hω hδr1 (bordGL (s • ωstar) (isoBordData H K (s • ωstar) E₀))
      (Ent.CG p E * u) hgd hgp (fun θ hθ => (hNG θ hθ).2) hg0
    rw [e2] at h2
    have h3 := h2 θ hθ
    rw [CorrectionSharp.gamma_mul_u_eq hγ hδ, mul_div_assoc] at h3
    exact h3
  have hXL1 : L1Vec (r - 2 * δ) (bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0)
      (Ent.CXiL1 p E * E') :=
    L1Vec.congr_real (fun x => (hXLeq _).symm) (L1Vec.le hXL1' hl1L)
  have hXNE : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ ≤ p.g * Ent.CXiN p E * E' := by
    intro θ hθ
    calc _ ≤ Ent.CXiN p E * u := (hNG θ (hsub hθ)).1
      _ ≤ Ent.CXiN p E * (p.g * E') := mul_le_mul_of_nonneg_left huE hk.CXiN
      _ = p.g * Ent.CXiN p E * E' := by ring
  have hXi : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖isoXi H K (s • ωstar) E₀ θ‖ ≤ Ent.CXi p E * E' :=
    fun θ hθ => KAM.Apost.Correction.norm_sumElim_le
      ((hXL θ hθ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE0))
      ((hXNE θ hθ).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hE0))
  have hξd : DifferentiableOn ℂ (isoXi H K (s • ωstar) E₀) (complexStrip n (r - 2 * δ)) :=
    KAM.Apost.Correction.diffOn_sumElim hXLd (hXNd.mono hsub)
  have hdξ : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖fderiv ℂ (isoXi H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ))‖ ≤
        Ent.CDXi p E * u := by
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
      _ ≤ Ent.CDXi p E * u := mul_le_mul_of_nonneg_right (le_max_right _ _) hu0
  refine ⟨⟨hXω, hNG⟩, fun θ hθ => ⟨hXi θ hθ, ?_, hdξ θ hθ, ?_, hXL θ hθ⟩, ?_, hXN1, hXL1, hXNd,
    hXNp, hXLd, hXLp⟩
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
      _ ≤ p.sK * (Ent.CXiL p E * E') + p.sN * (p.g * Ent.CXiN p E * E') :=
          add_le_add (mul_le_mul (hK.tangent_le hθr) (hXL θ hθ) (norm_nonneg _) hp.sK)
            (mul_le_mul (hK.normal θ hθr) (hXNE θ hθ) (norm_nonneg _) hp.sN)
      _ = Ent.CDK p E * E' := by unfold Ent.CDK; ring
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
      _ ≤ p.CFr * (Ent.CXi p E * E') + p.P * (Ent.CDXi p E * u) :=
          add_le_add ((Matrix.linfty_opNorm_mulVec _ _).trans
              (mul_le_mul hdP (hXi θ hθ) (norm_nonneg _) hp.CFr))
            ((Matrix.linfty_opNorm_mulVec _ _).trans
              (mul_le_mul hPn (hdξ θ hθ) (norm_nonneg _) hp.P))
      _ ≤ p.CFr * (Ent.CXi p E * E') + p.P * (Ent.CDXi p E * (p.g * E')) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left huE hk.CDXi) hp.P)
      _ = Ent.CdK p E * E' := by unfold Ent.CdK; ring
  · -- `|Δω| = |ξ^ω| |ω|`
    rw [isoNewS_smul_sub, norm_smul, norm_neg, Real.norm_eq_abs]
    calc |(isoXiOmega H K (s • ωstar) E₀).re| * ‖s • ωstar‖
        ≤ ‖isoXiOmega H K (s • ωstar) E₀‖ * ‖s • ωstar‖ :=
          mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (norm_nonneg _)
      _ ≤ Ent.CS p E * u * p.Θ := mul_le_mul hXω hΘ (norm_nonneg _) (mul_nonneg hk.CS hu0)
      _ ≤ Ent.CS p E * (p.g * E') * p.Θ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huE hk.CS) hΘ0
      _ = Ent.CDw p E * E' := by unfold Ent.CDw; ring

end KAM.Iso.Sharp2.L1

end
