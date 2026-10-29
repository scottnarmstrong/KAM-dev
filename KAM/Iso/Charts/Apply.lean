/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Charts.Points
public import KAM.Iso.Charts.Torus
import KAM.Head.Parameters
import KAM.Matrix.Norms

/-!
# Part 3 (local charts): one application of I-G1

Blueprint nodes `bpI:p3:apply` and
`bpI:p3:apply#constants`. `n = 2`, `τ = 2`.

* `apply_local`: the hypotheses (I1)-(I13) of the frozen I-G1 body `IG1Body` hold for the flat
  torus `K⁰(θ) = (θ, I)` of `h + f` (`hypothesis_d`, `torus`), one hypothesis at a time; the
  output (O1)-(O6) is read back with the Part 3 constants.
* `apply` (`bpI:p3:apply`): the constants `C₁ C₂ C₃` are chosen per patch and ray
  before `f, ε, E` by the premise `IG1Statement`, together with the full frozen conditional body
  `IG1Body` at the chosen tuple; then the local application at `I = Ψ(E, m)` and
  `s = ‖∇h(I)‖/‖ω*‖` (`points`).

Part 3 applies I-G1 only through the premise `IG1Statement` of `KAM.Iso.Charts.Inputs`.
-/

public section

open scoped Matrix.Norms.Operator
open Matrix Set Metric Topology

namespace KAM.Iso.Charts

open KAM KAM.Torus KAM.Iso.Confinement
open KAM.Head (unperturbedTorus muParam Fconst Mconst)

variable {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ} {B' : Set (Fin 2 → ℝ)} {η : ℝ}

namespace ApplyAux

/-- `F₁ ≥ 1` (`F₁ = c̄/δ_* = 32/δ_*` and `δ_* ≤ 1/4`). -/
theorem one_le_Fconst (hs : 0 < s₀) (hr : 0 < r₀) : 1 ≤ Fconst 2 s₀ r₀ 1 := by
  have hδ := KAM.Head.deltaStar_pos hs hr
  have hδ1 := KAM.Head.deltaStar_le_quarter s₀ r₀
  unfold KAM.Head.Fconst
  rw [KAM.Head.cbar_eq, pow_one, le_div_iff₀ hδ]
  linarith

/-- `0 < ρ = s/4`. -/
theorem rhoIso_pos (hs : 0 < s₀) : 0 < rhoIso s₀ := by
  unfold rhoIso
  have : 0 < min s₀ 1 := lt_min hs one_pos
  positivity

/-- `0 < ρ_∞ = s/8`. -/
theorem rhoInf_pos (hs : 0 < s₀) : 0 < rhoInf s₀ := by
  unfold rhoInf
  have : 0 < min s₀ 1 := lt_min hs one_pos
  positivity

/-- `ρ_∞ < ρ`. -/
theorem rhoInf_lt_rhoIso (hs : 0 < s₀) : rhoInf s₀ < rhoIso s₀ := by
  unfold rhoInf rhoIso
  have : 0 < min s₀ 1 := lt_min hs one_pos
  linarith

/-- `T_ρ ⊆ T_{s/2}`. -/
theorem strip_rhoIso_subset (hs : 0 < s₀) :
    complexStrip 2 (rhoIso s₀) ⊆ complexStrip 2 (min s₀ 1 / 2) :=
  KAM.Head.complexStrip_mono (by
    unfold rhoIso
    have : 0 < min s₀ 1 := lt_min hs one_pos
    linarith)

/-- The Gram matrix `1` has inverse row sums `1`. -/
theorem rowSum_one_inv (i : Fin 2) : ∑ j, ‖((1 : Matrix (Fin 2) (Fin 2) ℂ)⁻¹) i j‖ = 1 := by
  fin_cases i <;> simp [Matrix.one_apply]

/-- `‖Kinf θ - K⁰ θ‖ ≤ A` rewrites the exponent `ρ ^ (2 * 2)` of the frozen body. -/
theorem rpow_two_two (x : ℝ) : x ^ (2 * (2 : ℝ)) = x ^ 4 := by
  rw [show (2 * (2 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The exponent `ρ ^ (4 * 2)` of the frozen body. -/
theorem rpow_four_two (x : ℝ) : x ^ (4 * (2 : ℝ)) = x ^ 8 := by
  rw [show (4 * (2 : ℝ)) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The constant `σ_ω = 4 M_g/m_h + 2` exceeds `1` (as `M_g ≥ m_h > 0`). -/
theorem one_lt_sigmaOmega (hd : HeadData B s₀ r₀ h B' η) (hne : B'.Nonempty) :
    1 < sigmaOmegaConst h B B' := by
  obtain ⟨-, -, -, -, hmh, hmhMg, -, -⟩ := compact hd hne
  unfold sigmaOmegaConst
  have : 0 ≤ 4 * MgConst h B B' / mhConst h B B' := by
    have := hmh.le.trans hmhMg
    positivity
  linarith

end ApplyAux

open ApplyAux in
/-- The local application of I-G1 at the flat torus `K⁰(θ) = (θ, I)` of `h + f`: the hypotheses
(I1)-(I13) of `IG1Body` hold (`hypothesis_d`, `torus`), and its output is read back with the Part 3
constants. `I ∈ 𝒮 ∩ B` is on the ray `∇h(I) = s ω*` with `2 < s < 4 M_g/m_h`, `h(I) = E`. -/
theorem apply_local (hd : HeadData B s₀ r₀ h B' η) (hne : B'.Nonempty)
    {f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {ε : ℝ} (hf : PerturbData B s₀ r₀ f ε) (hε1 : ε ≤ 1)
    (hεT : ε ≤ epsT h B B' s₀ r₀) {γ : ℝ} {ωs : Fin 2 → ℝ} {C₁ C₂ C₃ : ℝ} (hC₁ : 0 < C₁)
    (hbody : IG1Body 2 2 (rhoIso s₀) (rhoInf s₀) (Mconst s₀ r₀ B h) (sigmaKConst s₀ r₀)
      (sigmaKConst s₀ r₀) (sigmaTConst h B B' s₀ r₀) (muParam s₀ r₀) γ (sigmaOmegaConst h B B')
      (nuConst h B B') ωs C₁ C₂ C₃)
    (hγ : 0 < γ) (hdio : IsDiophantine γ 2 ωs) (hωlow : mhConst h B B' / 4 < ‖ωs‖)
    {I : Fin 2 → ℝ} (hI : I ∈ B) (hIS : I ∈ sSet B B') {E s : ℝ} (hIE : realPart h I = E)
    (hpar : frequencyMap h I = s • ωs) (hs2 : 2 < s)
    (hs4 : s < 4 * MgConst h B B' / mhConst h B B')
    (hε : ε < γ ^ 4 * rhoIso s₀ ^ 8 / (C₁ * Fconst 2 s₀ r₀ 1)) :
    ∃ (Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (sinf : ℝ),
      1 < sinf ∧ sinf < sigmaOmegaConst h B B' ∧
      DifferentiableOn ℂ Kinf (complexStrip 2 (rhoInf s₀)) ∧
      IsPrimaryOnStrip Kinf (rhoInf s₀) ∧ IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip 2 (rhoInf s₀), invarianceError (totalH h f) Kinf (sinf • ωs) θ = 0) ∧
      (∀ θ ∈ complexStrip 2 (rhoInf s₀), totalH h f (Kinf θ) = (E : ℂ)) ∧
      (∀ θ ∈ complexStrip 2 (rhoInf s₀),
        Metric.ball (Kinf θ) (muParam s₀ r₀ / 2) ⊆ fractD B s₀ r₀ ∧
        ‖fderiv ℂ Kinf θ‖ ≤ sigmaKConst s₀ r₀ - muParam s₀ r₀ / 2 ∧
        ‖Kinf θ - unperturbedTorus I θ‖ ≤
          C₂ * (Fconst 2 s₀ r₀ 1 * ε) / (γ ^ 2 * rhoIso s₀ ^ 4)) ∧
      ‖sinf • ωs - s • ωs‖ ≤ C₃ * (Fconst 2 s₀ r₀ 1 * ε) / (γ ^ 2 * rhoIso s₀ ^ 4) := by
  have hs := hd.hs
  have hr := hd.hr
  obtain ⟨-, -, -, -, hmh, hmhMg, hSh, -⟩ := compact hd hne
  have hF1 : 1 ≤ Fconst 2 s₀ r₀ 1 := one_le_Fconst hs hr
  have hρ : 0 < rhoIso s₀ := rhoIso_pos hs
  have hμ : 0 < muParam s₀ r₀ := KAM.Head.muParam_pos hs hr
  -- (I1)–(I4)
  obtain ⟨hD1, hD2, hD3, hD4, hD5, hD6, -⟩ := hypothesis_d hd hf hε1
  -- the flat torus
  obtain ⟨⟨hKd, -, -, -, hKfr, hKball⟩, hKerr, -, -, hKinv, hKen⟩ :=
    torus hd hf hε1 hI hpar
  have hIB : toC I ∈ actionNbhd B r₀ := subset_realAct_charts hr hI
  -- the energy of the torus
  have hhI : h (toC I) = (E : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; exact hIE
    · simp [hd.real I hIB]
  rw [hhI] at hKen
  have hσT : sigmaTConst h B B' s₀ r₀ - muParam s₀ r₀ = 2 * ShConst h B B' := by
    unfold sigmaTConst; ring
  have hnu : nuConst h B B' ≤ (s - 1) * ‖ωs‖ := by
    unfold nuConst
    nlinarith [norm_nonneg ωs]
  have hnu2 : nuConst h B B' ≤ (sigmaOmegaConst h B B' - s) * ‖ωs‖ := by
    unfold nuConst sigmaOmegaConst
    nlinarith [norm_nonneg ωs]
  have hsmall : C₁ * (Fconst 2 s₀ r₀ 1 * ε) / (γ ^ 4 * rhoIso s₀ ^ (4 * (2 : ℝ))) < 1 := by
    rw [rpow_four_two, div_lt_one (by positivity)]
    have hFpos : 0 < Fconst 2 s₀ r₀ 1 := by linarith
    rw [lt_div_iff₀ (mul_pos hC₁ hFpos)] at hε
    nlinarith
  obtain ⟨Kinf, sinf, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ :=
    hbody (fractD B s₀ r₀) (totalH h f) (unperturbedTorus I) s γ (Fconst 2 s₀ r₀ 1 * ε) E
      hD1 hD2 hD3 hD4 hD5 hD6 hKd.differentiableOn
      (KAM.Head.isPrimaryOnStrip_unperturbedTorus I _) (KAM.Head.isRealOnReals_unperturbedTorus I)
      hKball
      (fun θ _ => by
        rw [(hKfr θ).1]
        simp [sigmaKConst])
      (fun θ _ => by
        rw [(hKfr θ).2.1]
        refine ⟨by simp, fun i => ?_⟩
        rw [rowSum_one_inv]
        simp [sigmaKConst])
      (hKinv hIS hεT).1
      ((norm_le_iff_forall_rowSum (by linarith)).1
        (by rw [hσT]; exact (hKinv hIS hεT).2))
      (by linarith) (by unfold sigmaOmegaConst; linarith) hnu hnu2 hγ le_rfl hdio
      (mul_nonneg (by linarith) hf.nonneg)
      (fun θ hθ => (hKerr θ (strip_rhoIso_subset hs hθ)).2)
      (hKen.trans (le_mul_of_one_le_left hf.nonneg hF1)) hsmall
  refine ⟨Kinf, sinf, k1, k2, k3, k4, k5, k6, k7, fun θ hθ => ⟨k8 θ hθ, k9 θ hθ, ?_⟩, ?_⟩
  · rw [rpow_two_two] at k10
    exact k10 θ hθ
  · rw [rpow_two_two] at k11
    exact k11

open ApplyAux in
/-- `bpI:p3:apply` with `#constants`: constants `C_i`, chosen per patch and ray before
`f, ε, E`, together with the FULL frozen I-G1 body at that tuple (`IG1Body`, the `GValid`
precedent), then (O1)–(O6) for `K = K⁰(I)`, `I = Ψ(E, m)`, `s = |∇h(I)|/|ω*|`, `e = F₁ε`,
`E₀ = E`. -/
theorem apply (hd : HeadData B s₀ r₀ h B' η) (hne : B'.Nonempty) (hG1 : IG1Statement)
    {δE δm ρc : ℝ} {c : Fin 2 → ℝ} {W : Set (Fin 2 → ℝ)} {Ψ : ℝ × ℝ → Fin 2 → ℝ}
    (hp : IsPatch h B r₀ B' (eta1 η B B') c W Ψ δE δm ρc) {γ m : ℝ} {ωs : Fin 2 → ℝ}
    (hray : IsRay h B B' c γ ωs m) (hm : |m| < δm) :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      IG1Body 2 2 (rhoIso s₀) (rhoInf s₀) (Mconst s₀ r₀ B h) (sigmaKConst s₀ r₀) (sigmaKConst s₀ r₀)
        (sigmaTConst h B B' s₀ r₀) (muParam s₀ r₀) γ (sigmaOmegaConst h B B') (nuConst h B B')
        ωs C₁ C₂ C₃ ∧
      ∀ (f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ) (ε : ℝ), PerturbData B s₀ r₀ f ε → ε ≤ 1 →
        ε ≤ epsT h B B' s₀ r₀ → ε < γ ^ 4 * rhoIso s₀ ^ 8 / (C₁ * Fconst 2 s₀ r₀ 1) →
        ∀ E : ℝ, |E - realPart h c| ≤ δE →
        ∃ (Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (sinf : ℝ),
          1 < sinf ∧ sinf < sigmaOmegaConst h B B' ∧
          DifferentiableOn ℂ Kinf (complexStrip 2 (rhoInf s₀)) ∧
          IsPrimaryOnStrip Kinf (rhoInf s₀) ∧ IsRealOnReals Kinf ∧
          (∀ θ ∈ complexStrip 2 (rhoInf s₀), invarianceError (totalH h f) Kinf (sinf • ωs) θ = 0) ∧
          (∀ θ ∈ complexStrip 2 (rhoInf s₀), totalH h f (Kinf θ) = (E : ℂ)) ∧
          (∀ θ ∈ complexStrip 2 (rhoInf s₀),
            Metric.ball (Kinf θ) (muParam s₀ r₀ / 2) ⊆ fractD B s₀ r₀ ∧
            ‖fderiv ℂ Kinf θ‖ ≤ sigmaKConst s₀ r₀ - muParam s₀ r₀ / 2 ∧
            ‖Kinf θ - unperturbedTorus (Ψ (E, m)) θ‖ ≤
              C₂ * (Fconst 2 s₀ r₀ 1 * ε) / (γ ^ 2 * rhoIso s₀ ^ 4)) ∧
          ‖sinf • ωs - (‖frequencyMap h (Ψ (E, m))‖ / ‖ωs‖) • ωs‖ ≤
            C₃ * (Fconst 2 s₀ r₀ 1 * ε) / (γ ^ 2 * rhoIso s₀ ^ 4) := by
  have hs := hd.hs
  have hr := hd.hr
  obtain ⟨-, -, -, -, hmh, hmhMg, hSh, -⟩ := compact hd hne
  have hμ : 0 < muParam s₀ r₀ := KAM.Head.muParam_pos hs hr
  have hωlow : mhConst h B B' / 4 < ‖ωs‖ := hray.2.2.2.2.1
  have hγ : 0 < γ := hray.1
  have hωs : ωs ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hωlow
    linarith
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, hbody⟩ :=
    @hG1 2 (by norm_num) 2 (by norm_num) (rhoIso s₀) (rhoInf s₀) (rhoInf_pos hs)
      (rhoInf_lt_rhoIso hs) (Mconst s₀ r₀ B h) (sigmaKConst s₀ r₀) (sigmaKConst s₀ r₀)
      (sigmaTConst h B B' s₀ r₀) (muParam s₀ r₀) γ (sigmaOmegaConst h B B') (nuConst h B B')
      (KAM.Head.Parameters.Mconst_pos hs hr) (by unfold sigmaKConst; linarith)
      (by unfold sigmaKConst; linarith) (by unfold sigmaTConst; linarith) hμ hγ
      (one_lt_sigmaOmega hd hne) (by unfold nuConst; linarith) ωs hωs
  refine ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, hbody, ?_⟩
  intro f ε hf hε1 hεT hε E hE
  obtain ⟨-, -, hIE, -, hpar, hs2, hs4, -, hIS, hIB, -, -⟩ := points hd hne hp hray hm hE
  exact apply_local hd hne hf hε1 hεT hC₁ hbody hγ hray.2.1 hωlow hIB hIS hIE hpar hs2 hs4 hε

end KAM.Iso.Charts
