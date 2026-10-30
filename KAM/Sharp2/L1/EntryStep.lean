/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.L1.EntryError
public import KAM.Sharp2.L1.EntryTorsion
public import KAM.Sharp2.RouteA.Step
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The ℓ¹ entry step of route A (package B10c)

Blueprint `bp:p2s2l1:entryA` of `blueprint/parts/p2s2-l1hybrid.tex`:

* `EntryCond.facts`: the entry conditions in the actual `ε, γ, δ`;
* `entry_frame_rates`: the increments `|DK̄ - DK| ≤ d_L X`, `|(L̄ - L)ᵀ| ≤ d_{Lᵀ} X` (the sup Cauchy
  estimate, and with the frame certificate the ℓ¹ one, `l1_frame_increment`);
* `entry_step_A`: B9's additive step `KAM.Sharp2.RouteA.step_A` from the ℓ¹ entry data, with
  every cap of `AdmA` increased by its entry rate at `X = ε/(γ²δ^{a+1})`: `ball C_ΔK E`,
  `|DK| d_L X`, `|B| r_B X`, `|⟨T⟩⁻¹| ϱ_T X`, `|Lᵀ| d_{Lᵀ} X`, `|N| r_N X`, `|Nᵀ| r_{Nᵀ} X`,
  `|T| C_ΔT X`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2.L1

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2.RouteA

variable {n : ℕ} {τ M : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

/-- The entry conditions in the actual variables, for `δ ≤ p.δ`. -/
theorem EntryCond.facts {p : StepInA} {E : EntryA} (hp : p.Pos) (hE : E.Wf) {δ ε : ℝ}
    (hγ : 0 < γ) (hγb : γ ≤ p.γb) (hδ : 0 < δ) (hδD : δ ≤ p.δ) (hε : 0 ≤ ε)
    (hC : EntryCond p E (ε / (γ ^ 4 * δ ^ (2 * (2 * p.κ))))) :
    ε ≤ δ ∧ Ent.CSym p E * (ε / (γ * δ ^ (p.κ + 1))) ≤ 1 / 2 ∧
      Ent.CE p E * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) ≤ ε ∧
      p.sT * (Ent.CDT p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)))) ≤ p.th ∧
      p.sB * (Ent.GrK p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)))) ≤ p.th := by
  have hk := Ent.nonneg hp hE
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
  have hE' : Ent.CE p E * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) = ε * (Ent.CE p E * x) := by
    rw [hx]; ring
  have hX : ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)) ≤ p.γb ^ 2 * p.δ ^ (2 * p.κ - 1) * x := by
    rw [s5]; exact b2
  have hT0 := hp.sT
  have hB0 := hp.sB
  have hsym := hC.sym
  have htw := hC.twist
  have hgr := hC.gram
  have hq := hC.quad
  rw [Ent.COmK_eq] at hsym
  rw [Ent.CDT_eq] at htw
  rw [Ent.gram_eq] at hgr
  rw [Ent.CE_eq] at hq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : ε / δ ≤ 1 := by
      rw [s6]
      refine b4.trans ?_
      have := hC.err
      linarith
    exact (div_le_one hδ).1 this
  · rw [s7]
    calc Ent.CSym p E * ((γ ^ 3 * δ ^ (3 * p.κ - 1)) * x) ≤
          Ent.CSym p E * (p.γb ^ 3 * p.δ ^ (3 * p.κ - 1) * x) :=
          mul_le_mul_of_nonneg_left b3 hk.CSym
      _ = max 1 (p.sB ^ 2) * Ent.COmK p E * (p.γb ^ 3 * p.δ ^ (3 * p.κ - 1)) * x := by
          unfold Ent.CSym; ring
      _ ≤ 1 / 2 := hsym
  · rw [hE']
    exact mul_le_of_le_one_right hε hq
  · calc p.sT * (Ent.CDT p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)))) ≤
        p.sT * (Ent.CDT p E * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1) * x)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX hk.CDT) hT0
      _ = p.sT * Ent.CDT p E * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x := by ring
      _ ≤ p.th := htw
  · calc p.sB * (Ent.GrK p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)))) ≤
        p.sB * (Ent.GrK p E * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1) * x)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX hk.GrK) hB0
      _ = p.sB * Ent.GrK p E * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x := by ring
      _ ≤ p.th := hgr

/-- The `|DK|` and `|Lᵀ|` increments of the entry step on `T_{r-3δ}`: the sup Cauchy estimate
(`n C_ΔK X`, `2n C_ΔK X`), and with the frame certificate also the ℓ¹ one. -/
theorem entry_frame_rates {p : StepInA} {E : EntryA} (hp : p.Pos) (hE : E.Wf) (hpn : p.n = n)
    (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ) (hγb : γ ≤ p.γb) {r β ε δ : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : Admissible p.sK p.sB p.sT 𝔅 h ω r β ε K) (hδ : 0 < δ) (hδD : δ ≤ p.δ) (h3δ : 3 * δ < r)
    (hD : EntryData E h K ω r δ ε)
    (hdist : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖newtonMap h K ω (r - 2 * δ) θ - K θ‖ ≤ Ent.CDK p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ))))
    (hdiff : DifferentiableOn ℂ (newtonMap h K ω (r - 2 * δ)) (complexStrip n (r - 2 * δ)))
    (hXLd : DifferentiableOn ℂ (triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω))
      (complexStrip n (r - 2 * δ)))
    (hXLp : IsPeriodicOn (triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω)) (r - 2 * δ))
    (hXNd : DifferentiableOn ℂ (triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω))
      (complexStrip n (r - δ)))
    (hXNp : IsPeriodicOn (triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω)) (r - δ))
    (hXN1 : L1Vec (r - δ) (triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω))
      (Ent.CXiN1 p E * (ε / (γ * δ ^ p.κ))))
    (hXL1 : L1Vec (r - 2 * δ) (triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω))
      (Ent.CXiL1 p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ))))) :
    ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖fderiv ℂ (newtonMap h K ω (r - 2 * δ)) θ - fderiv ℂ K θ‖ ≤
        Ent.dL p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ∧
      ‖(tangentMat (newtonMap h K ω (r - 2 * δ)) θ - tangentMat K θ)ᵀ‖ ≤
        Ent.dLt p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) := by
  subst hpn
  have hk := Ent.nonneg hp hE
  have hr := hK.r_pos
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hδ1 : δ ≤ 1 := hδD.trans hp.δ1
  obtain ⟨-, sE, s3, -, -, -, -, -⟩ := scales (ε := ε) (κ := p.κ) hγ hδ
  set u := ε / (γ * δ ^ p.κ) with hu
  set E' := ε / (γ ^ 2 * δ ^ (2 * p.κ)) with hE'
  set X := ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)) with hX
  have hX0 : 0 ≤ X := div_nonneg hε0 (by positivity)
  have hE0 : 0 ≤ E' := div_nonneg hε0 (by positivity)
  have hgd0 := StepInA.gd_le hp hγ hγb hδ hδD
  have huE : u ≤ p.g * E' := by rw [sE]; exact mul_le_mul_of_nonneg_right hgd0 hE0
  have hsub2r : complexStrip p.n (r - 2 * δ) ⊆ complexStrip p.n r :=
    Triangular.strip_mono (by linarith)
  have hθ' : ∀ θ ∈ complexStrip p.n (r - 3 * δ), θ ∈ complexStrip p.n (r - 2 * δ - δ) :=
    fun θ hθ => by rwa [show r - 2 * δ - δ = r - 3 * δ by ring]
  have hDE : Ent.CDK p E * E' / δ = Ent.CDK p E * X := by rw [s3]; field_simp
  -- the sup Cauchy estimates
  have hsup1 : ∀ θ ∈ complexStrip p.n (r - 3 * δ),
      ‖fderiv ℂ (newtonMap h K ω (r - 2 * δ)) θ - fderiv ℂ K θ‖ ≤ p.n * Ent.CDK p E * X :=
    fun θ hθ => by
      have := PerturbationAux.norm_fderiv_sub_le (hK.holo.mono hsub2r) hdiff hdist hδ θ (hθ' θ hθ)
      rwa [mul_div_assoc, hDE, ← mul_assoc] at this
  have hsup2 : ∀ θ ∈ complexStrip p.n (r - 3 * δ),
      ‖(tangentMat (newtonMap h K ω (r - 2 * δ)) θ - tangentMat K θ)ᵀ‖ ≤
        2 * p.n * Ent.CDK p E * X := fun θ hθ => by
    have := PerturbationAux.norm_transpose_tangentMat_sub_le (hK.holo.mono hsub2r) hdiff hdist hδ θ
      (hθ' θ hθ)
    rwa [mul_div_assoc, hDE, ← mul_assoc] at this
  intro θ hθ
  unfold Ent.dL Ent.dLt
  rcases hF : E.frame with _ | F
  · exact ⟨hsup1 θ hθ, hsup2 θ hθ⟩
  · obtain ⟨hLK, hNK⟩ := hD.frame F hF
    obtain ⟨hν1, hν2⟩ := hE.frame F hF
    obtain ⟨h1, h2⟩ := l1_frame_increment hS hK hδ hδ1 h3δ hLK hNK hXLd hXLp hXNd hXNp hXL1 hXN1
      θ hθ
    have hcmp : F.nuK * (Ent.CXiL1 p E * E') + F.nuN * (Ent.CXiN1 p E * u) ≤
        (F.nuK * Ent.CXiL1 p E + F.nuN * p.g * Ent.CXiN1 p E) * E' := by
      have : F.nuN * (Ent.CXiN1 p E * u) ≤ F.nuN * (Ent.CXiN1 p E * (p.g * E')) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left huE hk.CXiN1) hν2.le
      nlinarith
    have hl1 : (F.nuK * (Ent.CXiL1 p E * E') + F.nuN * (Ent.CXiN1 p E * u)) /
        (Real.exp 1 * δ) ≤
          Ent.einv * (F.nuK * Ent.CXiL1 p E + F.nuN * p.g * Ent.CXiN1 p E) * X := by
      have he : 0 < Real.exp 1 * δ := mul_pos (Real.exp_pos 1) hδ
      calc _ ≤ (F.nuK * Ent.CXiL1 p E + F.nuN * p.g * Ent.CXiN1 p E) * E' / (Real.exp 1 * δ) :=
            div_le_div_of_nonneg_right hcmp he.le
        _ = Ent.einv * (F.nuK * Ent.CXiL1 p E + F.nuN * p.g * Ent.CXiN1 p E) * X := by
            rw [s3]; unfold Ent.einv; field_simp
    refine ⟨?_, ?_⟩
    · rw [min_mul_of_nonneg _ _ hX0]
      exact le_min (hsup1 θ hθ) (h1.trans hl1)
    · rw [min_mul_of_nonneg _ _ hX0]
      refine le_min (hsup2 θ hθ) (h2.trans ?_)
      have := mul_le_mul_of_nonneg_left hl1 (show (0 : ℝ) ≤ 2 * p.n by positivity)
      calc 2 * (p.n : ℝ) * (F.nuK * (Ent.CXiL1 p E * E') + F.nuN * (Ent.CXiN1 p E * u)) /
            (Real.exp 1 * δ) =
            2 * p.n * ((F.nuK * (Ent.CXiL1 p E * E') + F.nuN * (Ent.CXiN1 p E * u)) /
              (Real.exp 1 * δ)) := by ring
        _ ≤ _ := this
        _ = _ := by ring

/-- The arithmetic of the torsion rate of the entry step: the bound of `torsion_sub_leG` at the
entry increments is `≤ C_ΔT X`. -/
theorem entry_torsion_arith {p : StepInA} {E : EntryA} (hp : p.Pos) (hE : E.Wf)
    (hfix : p.iso = false) (hpn : p.n = n) {δ ε X E' : ℝ} (hγ : 0 < γ) (hγb : γ ≤ p.γb)
    (hδ : 0 < δ) (hδD : δ ≤ p.δ) (hX0 : 0 ≤ X)
    (hX : X = ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) (hE' : E' = ε / (γ ^ 2 * δ ^ (2 * p.κ))) :
    2 * p.M1 * (Ent.rNt p E * X * p.sN + p.sNt * (Ent.rN p E * X)) +
        2 * p.M2 * p.sNt * p.sN * (Ent.CDK p E * E') +
        p.sB ^ 3 * p.w * (p.sK * (Ent.dLt p E * X) + p.sLt * (Ent.dL p E * X)) +
        2 * n * p.sNt * p.sB * (ε / δ) +
        2 * p.sB ^ 3 * p.w * (Ent.COmK p E * (ε / (γ * δ ^ (p.κ + 1)))) ≤
      Ent.CDT p E * X := by
  have hk := Ent.nonneg hp hE
  obtain ⟨-, -, s3, s4, -, -, -, s8⟩ := scales (ε := ε) (κ := p.κ) hγ hδ
  have hYg : ε / (γ * δ ^ (p.κ + 1)) ≤ p.g * X := by
    rw [s8, ← hX]
    exact mul_le_mul_of_nonneg_right (StepInA.gd_le hp hγ hγb hδ hδD) hX0
  have hεg : ε / δ ≤ p.γb ^ 2 * p.δ ^ (2 * p.κ) * X := by
    rw [s4, ← hX]
    exact mul_le_mul_of_nonneg_right
      (pow_mul_rpow_le 2 hγ hγb hδ hδD (by linarith [hp.κ_ge])) hX0
  have hCDT : Ent.CDT p E = Ent.CDT0 p E := by simp [Ent.CDT, hfix]
  have hw0 := hp.w
  have hsB0 := hp.sB
  have hNt0 := hp.sNt
  have hN0 := hp.sN
  have hM20 := hp.M2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hOmle : Ent.COmK p E ≤ p.COm := min_le_left _ _
  have hdE : Ent.CDK p E * E' ≤ Ent.CDK p E * p.δ * X := by
    rw [hE', s3, ← hX, mul_comm δ X, ← mul_assoc, mul_assoc (Ent.CDK p E) p.δ X,
      mul_comm p.δ X, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hδD (mul_nonneg hk.CDK hX0)
  have hA : 2 * p.sB ^ 3 * p.w * (Ent.COmK p E * (ε / (γ * δ ^ (p.κ + 1)))) ≤
      p.sB ^ 3 * p.w * ((p.COm + Ent.COmK p E) * (p.g * X)) := by
    have h1 : Ent.COmK p E * (ε / (γ * δ ^ (p.κ + 1))) ≤ Ent.COmK p E * (p.g * X) :=
      mul_le_mul_of_nonneg_left hYg hk.COmK
    have h3 : 2 * (Ent.COmK p E * (p.g * X)) ≤ (p.COm + Ent.COmK p E) * (p.g * X) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hp.g hX0)
    have h4 : 0 ≤ p.sB ^ 3 * p.w := by positivity
    calc 2 * p.sB ^ 3 * p.w * (Ent.COmK p E * (ε / (γ * δ ^ (p.κ + 1))))
        = p.sB ^ 3 * p.w * (2 * (Ent.COmK p E * (ε / (γ * δ ^ (p.κ + 1))))) := by ring
      _ ≤ p.sB ^ 3 * p.w * (2 * (Ent.COmK p E * (p.g * X))) :=
          mul_le_mul_of_nonneg_left (by linarith) h4
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 h4
  have hB2 : 2 * p.M2 * p.sNt * p.sN * (Ent.CDK p E * E') ≤
      2 * p.M2 * p.sNt * p.sN * (Ent.CDK p E * p.δ * X) :=
    mul_le_mul_of_nonneg_left hdE (by positivity)
  have hC2 : 2 * n * p.sNt * p.sB * (ε / δ) ≤
      2 * n * p.sNt * p.sB * (p.γb ^ 2 * p.δ ^ (2 * p.κ) * X) :=
    mul_le_mul_of_nonneg_left hεg (by positivity)
  refine (add_le_add (add_le_add (add_le_add (add_le_add le_rfl hB2) le_rfl) hC2) hA).trans
    (le_of_eq ?_)
  rw [hCDT]; unfold Ent.CDT0; rw [hpn]; ring

/-- The ℓ¹ entry step of route A at fixed frequency. -/
theorem entry_step_A {p : StepInA} {E : EntryA} (hp : p.Pos) (hE : E.Wf) (hfix : p.iso = false)
    (hΘ : p.Θ = 0) (hpn : p.n = n)
    (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ)
    (hd1 : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ p.M1)
    (hd2 : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ p.M2)
    (hγb : γ ≤ p.γb) {Ω : Set (Fin n → ℝ)} (hω : ω ∈ Ω)
    {r β ε δ b cb mK mB mT mLt mN mNt mH : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : AdmA 𝔅 h ω r (r - δ) β ε mK mB mT mLt mN mNt mH K)
    (hδ : 0 < δ) (hδD : δ ≤ p.δ) (h3δ : 3 * δ < r)
    (hc : SDConst n p.κ γ δ p.c Ω) (hcb : SDConst n p.κ γ b cb Ω) (hbr : b ≤ r)
    (hca : cb * b ^ (-p.κ) ≤ p.ca * δ ^ (-p.κ)) (hD : EntryData E h K ω r δ ε)
    (hcond : EntryCond p E (ε / (γ ^ 4 * δ ^ (2 * (2 * p.κ)))))
    (hβ : Ent.CDK p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) < β)
    (hcK : mK + Ent.dL p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sK)
    (hcB : mB + Ent.rB p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sB)
    (hcT : mT + Ent.rT p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sT)
    (hcLt : mLt + Ent.dLt p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sLt)
    (hcN : mN + Ent.rN p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sN)
    (hcNt : mNt + Ent.rNt p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.sNt)
    (hcH : mH + Ent.CDT p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) ≤ p.t) :
    AdmA 𝔅 h ω (r - 3 * δ) (r - 3 * δ - δ / 2) (β - Ent.CDK p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ))))
        (Ent.CE p E * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))))
        (mK + Ent.dL p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mB + Ent.rB p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mT + Ent.rT p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mLt + Ent.dLt p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mN + Ent.rN p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mNt + Ent.rNt p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (mH + Ent.CDT p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))))
        (newtonMap h K ω (r - 2 * δ)) ∧
      Ent.CE p E * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) ≤ ε ∧
      ∀ θ ∈ complexStrip n (r - 3 * δ),
        ‖newtonMap h K ω (r - 2 * δ) θ - K θ‖ ≤ Ent.CDK p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) ∧
        ‖fderiv ℂ (newtonMap h K ω (r - 2 * δ)) θ - fderiv ℂ K θ‖ ≤
          n * Ent.CDK p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ + 1))) := by
  have hk := Ent.nonneg hp hE
  have hr := hK.r_pos
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hδ1 : δ ≤ 1 := hδD.trans hp.δ1
  obtain ⟨hεδ, hsym, hE2, htw, hgr⟩ := hcond.facts hp hE hγ hγb hδ hδD hε0
  have hε1 : ε ≤ 1 := hεδ.trans hδ1
  obtain ⟨-, -, s3, -, -, -, -, -⟩ := scales (ε := ε) (κ := p.κ) hγ hδ
  set u := ε / (γ * δ ^ p.κ) with hud
  set E' := ε / (γ ^ 2 * δ ^ (2 * p.κ)) with hEd
  set X := ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)) with hXd
  have hX0 : 0 ≤ X := div_nonneg hε0 (by positivity)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- the budgets: `m ≤ cap`
  have hr1 : 0 ≤ Ent.dL p E * X := mul_nonneg hk.dL hX0
  have hr2 : 0 ≤ Ent.rB p E * X := mul_nonneg hk.rB hX0
  have hr3' : 0 ≤ Ent.rT p E * X := mul_nonneg hk.rT hX0
  have hr4 : 0 ≤ Ent.dLt p E * X := mul_nonneg hk.dLt hX0
  have hr5 : 0 ≤ Ent.rN p E * X := mul_nonneg hk.rN hX0
  have hr6 : 0 ≤ Ent.rNt p E * X := mul_nonneg hk.rNt hX0
  have hr7 : 0 ≤ Ent.CDT p E * X := mul_nonneg hk.CDT hX0
  have hK0 : AdmA 𝔅 h ω r (r - δ) β ε p.sK p.sB p.sT p.sLt p.sN p.sNt p.t K :=
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
  have hAd := hK0.toAdmissible hε1
  obtain ⟨⟨-, -, -, hcd, hcp, hcr⟩, -⟩ := correction_spec hS hAd hδ hδ1 h2δ
  obtain ⟨hdist', hΩ, herr⟩ := entry_newton_error hp hE hfix hΘ hpn hS hd2 hγb hω hK0 hδ hδD h2δ
    hε1 hc hcb hbr hca hD hβ hsym
  obtain ⟨-, -, hXN1, hXL1⟩ :=
    entry_correction_bounds hp hE hfix hΘ hS hγb hω hK0 hδ hδD h2δ hc hcb hbr hca hD
  -- the solutions (as in `correction_boundsA`)
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  have hK𝔅 := hK.mem
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, hTd0, -, -, hηd, -, hTc⟩, -, -, -⟩ :=
    frame_basic hS hr hK0.β_pos hK0.holo hK0.ball_sub hK0.deriv_le hK0.gram
  obtain ⟨-, hperiod, -⟩ := periodicity hS hr hK.holo hK.primary hK𝔅
  obtain ⟨-, -, -, -, hTp, -, hηp⟩ := hperiod hGu
  have hTavg0 : torsionAverage h K ω = avg (torsion h K ω) := torsionAverage_eq_avg h K ω hTc
  obtain ⟨⟨-, hXNd, hXNp, -, -, hXLd, hXLp⟩, -, -, -⟩ :=
    triangular hS hr hδ h2δ (ηL := etaL h K ω) (ηN := etaN h K ω) (T := torsion h K ω)
      (HL := p.sNt * ε) (HN := p.sLt * ε) (HT := p.t) (σ := p.sT)
      (Correction.diffOn_etaL hηd) (Correction.periodic_etaL hηp)
      (Correction.diffOn_etaN hηd) (Correction.periodic_etaN hηp)
      (fun θ hθ => norm_etaL_le (hK0.normalT θ hθ) (hK0.error_le θ hθ))
      (fun θ hθ => norm_etaN_le (hK0.tangentT θ hθ) (hK0.error_le θ hθ))
      (exactness hS hr hK.holo hK.primary hK𝔅).2 hTd0 hTp hK0.tors
      (by rw [← hTavg0]; exact hK0.twist.1) (by rw [← hTavg0]; exact hK0.twist.2)
  set K' := newtonMap h K ω (r - 2 * δ) with hK'def
  have hdiff : DifferentiableOn ℂ K' (complexStrip n (r - 2 * δ)) :=
    KAM.Apost.Step.newtonMap_differentiableOn (hK.holo.mono hsub) hcd
  have hdist : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖K' θ - K θ‖ ≤ Ent.CDK p E * E' := fun θ hθ => by
    rw [hK'def, NewtonError.newtonMap_of_mem hθ, add_sub_cancel_left]
    exact hdist' θ hθ
  have hD' : Ent.CDK p E * E' / δ = Ent.CDK p E * X := by
    rw [s3]; field_simp
  have hball : ∀ θ ∈ complexStrip n (r - 2 * δ), Metric.ball (K' θ) (β - Ent.CDK p E * E') ⊆ 𝔅 :=
    fun θ hθ => PerturbationAux.ball_subset_of_close (hK.ball_sub θ (hsub hθ)) (hdist θ hθ)
  have hβ' : 0 < β - Ent.CDK p E * E' := by linarith
  have hK'𝔅 : ∀ θ ∈ complexStrip n (r - 2 * δ), K' θ ∈ 𝔅 := fun θ hθ =>
    hball θ hθ (Metric.mem_ball_self hβ')
  -- the frames
  have hrates := entry_frame_rates hp hE hpn hS hγb hAd hδ hδD h3δ hD hdist hdiff hXLd hXLp hXNd
    hXNp hXN1 hXL1
  have hLθ : ∀ θ ∈ complexStrip n r, ‖tangentMat K θ‖ ≤ p.sK := fun θ hθ => hK0.tangent_le hθ
  have hfr : ∀ θ ∈ complexStrip n (r - 3 * δ), BarBdG K K' θ (Ent.dL p E * X) (Ent.dLt p E * X)
      (Ent.rB p E * X) (Ent.rN p E * X) (Ent.rNt p E * X) := by
    intro θ hθ
    have hθr := hsub3r hθ
    have e1 : rBOf p (Ent.dL p E * X) (Ent.dLt p E * X) = Ent.rB p E * X := by
      unfold rBOf Ent.rB; ring
    have hb := frames_barG hp (hLθ θ hθr) (hK.gram θ hθr).1 (hK.gram θ hθr).2 (hK.tangentT θ hθr)
      (by linarith) (by linarith) (hrates θ hθ).1 (hrates θ hθ).2
      (by have : p.sLt * (Ent.dL p E * X) + p.sK * (Ent.dLt p E * X) = Ent.GrK p E * X := by
            unfold Ent.GrK; ring
          rw [this]; exact hgr)
      hcLt (by rw [e1]; exact hcB)
    rw [e1] at hb
    have e2 : p.sB * (Ent.dL p E * X) + p.sK * (Ent.rB p E * X) = Ent.rN p E * X := by
      unfold Ent.rN; ring
    have e3 : Ent.rB p E * X * p.sLt + p.sB * (Ent.dLt p E * X) = Ent.rNt p E * X := by
      unfold Ent.rNt; ring
    rw [e2, e3] at hb
    exact hb
  have hL'θ : ∀ θ ∈ complexStrip n (r - 3 * δ), ‖fderiv ℂ K' θ‖ ≤ mK + Ent.dL p E * X :=
    fun θ hθ => norm_le_add_sub (hK.deriv_le θ (hsub3r hθ)) (hfr θ hθ).dDK
  have hLt'θ : ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖(tangentMat K' θ)ᵀ‖ ≤ mLt + Ent.dLt p E * X := fun θ hθ => by
    have e : (tangentMat K' θ)ᵀ = (tangentMat K θ)ᵀ + (tangentMat K' θ - tangentMat K θ)ᵀ := by
      rw [Matrix.transpose_sub]; abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add (hK.tangentT θ (hsub3r hθ)) (hfr θ hθ).dLt)
  have hB'θ : ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖(gramMatrix K' θ)⁻¹‖ ≤ mB + Ent.rB p E * X := fun θ hθ =>
    norm_le_add_sub (hK.gram θ (hsub3r hθ)).2 (hfr θ hθ).dB
  have hN'θ : ∀ θ ∈ complexStrip n (r - 3 * δ), ‖normalMat K' θ‖ ≤ mN + Ent.rN p E * X :=
    fun θ hθ => norm_le_add_sub (hK.normal θ (hsub3r hθ)) (hfr θ hθ).dN
  have hNt'θ : ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖(normalMat K' θ)ᵀ‖ ≤ mNt + Ent.rNt p E * X := fun θ hθ =>
    norm_le_add_sub (hK.normalT θ (hsub3r hθ)) (hfr θ hθ).dNt
  -- the torsion
  have hG'3 : ∀ θ ∈ complexStrip n (r - 3 * δ), IsUnit (gramMatrix K' θ).det :=
    fun θ hθ => (hfr θ hθ).unit
  have hT' : ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖torsion h K' ω θ - torsion h K ω θ‖ ≤ Ent.CDT p E * X := by
    intro θ hθ
    have hθr := hsub3r hθ
    have hθ2 := hsub32 hθ
    have hL' : ‖tangentMat K' θ‖ ≤ p.sK :=
      (FrameAux.norm_tangentMat K' θ).le.trans ((hL'θ θ hθ).trans hcK)
    have hmain := torsion_sub_leG hp hpn hS hd1 hd2 (K := K) (K' := K') (ω₁ := ω) (ω₂ := ω)
      (β := β) (d := Ent.CDK p E * E') (δ := δ) (ε := ε)
      (ε' := Ent.CE p E * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))))
      (Wb := Ent.COmK p E * (ε / (γ * δ ^ (p.κ + 1)))) hr hδ h3δ hθ hK.holo hK.mem hGu
      hK.error_le hdiff hK'𝔅 hG'3 herr (hK.ball_sub θ hθr) (hdist θ hθ2) hβ hE2 hεδ (hLθ θ hθr)
      (hK0.tangentT θ hθr) (hK0.normalT θ hθr) (hK0.gram θ hθr).2 hL' ((hLt'θ θ hθ).trans hcLt)
      ((hN'θ θ hθ).trans hcN) ((hNt'θ θ hθ).trans hcNt) ((hB'θ θ hθ).trans hcB) (hΩ θ hθ2)
      (hfr θ hθ)
    exact hmain.trans (entry_torsion_arith hp hE hfix hpn hγ hγb hδ hδD hX0 rfl rfl)
  -- the averaged torsion
  have hTd' : DifferentiableOn ℂ (torsion h K' ω) (complexStrip n (r - 3 * δ)) := by
    have hNd := differentiableOn_normalMat (hdiff.mono hsub32) hG'3
    exact FrameAux.differentiableOn_torsion hNd (FrameAux.differentiableOn_normalFieldMat
      (FrameAux.differentiableOn_linMat hS (hdiff.mono hsub32) fun θ hθ => hK'𝔅 θ (hsub32 hθ)) hNd)
  have hc' := FrameAux.continuous_torsion_real hr3 hTd'
  have hTd : DifferentiableOn ℂ (torsion h K ω) (complexStrip n r) :=
    PerturbationAux.differentiableOn_torsion_of hS hK.holo hK.mem hGu
  have hc0 := FrameAux.continuous_torsion_real hr hTd
  have havg := norm_torsionAverage_sub_le_any hc0 hc'
    (fun x => hT' _ (ofReal_mem_complexStrip hr3 x))
  have hTu : IsUnit (torsionAverage h K ω) := (Matrix.isUnit_iff_isUnit_det _).2 hK.twist.1
  have hTσ : ‖(torsionAverage h K ω)⁻¹‖ ≤ p.sT := hK.twist.2.trans (by linarith)
  have hsmall : ‖(torsionAverage h K ω)⁻¹‖ * ‖torsionAverage h K' ω - torsionAverage h K ω‖ ≤
      p.th := (mul_le_mul hTσ havg (norm_nonneg _) hp.sT).trans htw
  obtain ⟨hU, -, hBdiff⟩ := neumann_ratio hTu hp.th1 hsmall
  rw [add_sub_cancel] at hU hBdiff
  have hth := hp.one_sub_th
  have hTdd : ‖(torsionAverage h K' ω)⁻¹ - (torsionAverage h K ω)⁻¹‖ ≤ Ent.rT p E * X := by
    have hTT : ‖(torsionAverage h K ω)⁻¹‖ ^ 2 ≤ p.sT ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hTσ 2
    calc _ ≤ ‖(torsionAverage h K ω)⁻¹‖ ^ 2 * ‖torsionAverage h K' ω - torsionAverage h K ω‖ /
          (1 - p.th) := hBdiff
      _ ≤ p.sT ^ 2 * (Ent.CDT p E * X) / (1 - p.th) :=
          div_le_div_of_nonneg_right (mul_le_mul hTT havg (norm_nonneg _) (by positivity)) hth.le
      _ = Ent.rT p E * X := by unfold Ent.rT; ring
  have hsubT : complexStrip n (r - 3 * δ - δ / 2) ⊆ complexStrip n (r - 3 * δ) :=
    Triangular.strip_mono (by linarith)
  refine ⟨?_, hE2, fun θ hθ => ⟨hdist θ (hsub32 hθ), ?_⟩⟩
  · exact
      { r_pos := hr3
        β_pos := hβ'
        ε_nonneg := by
          have h1 : 0 ≤ Ent.CE p E * ε ^ 2 := mul_nonneg hk.CE (sq_nonneg _)
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
        tors := fun θ hθ => norm_le_add_sub (hK.tors θ (hsub31 (hsubT hθ))) (hT' θ (hsubT hθ))
        twist := ⟨(Matrix.isUnit_iff_isUnit_det _).1 hU, norm_le_add_sub hK.twist.2 hTdd⟩
        error_le := fun θ hθ => herr θ (hsub32 hθ) }
  · have hθr := hsub3r hθ
    have := PerturbationAux.norm_fderiv_sub_le (hK.holo.mono hsub) hdiff hdist hδ θ
      (by rwa [show r - 2 * δ - δ = r - 3 * δ by ring])
    rw [mul_div_assoc, hD'] at this
    rw [mul_assoc]
    exact this

end KAM.Sharp2.L1

end
