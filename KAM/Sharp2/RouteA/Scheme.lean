/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.Data
public import KAM.Sharp2.RouteA.Step
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The fixed-frequency scheme of route A

`schemeA` is the additive scheme whose states are tori; the eight cap values are the used ball budget
and the current bounds of `|DK|, |B|, |⟨T⟩⁻¹|, |Lᵀ|, |N|, |Nᵀ|, |T|`. `schemeA_isNewton` proves (N1),
(N2) from `KAM.Sharp2.RouteA.step_A`, stage by stage, with the certificates of `NumA.Cert`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix KAM.Sharp.Engine

namespace KAM.Sharp2.RouteA

open KAM KAM.Torus KAM.Apost KAM.Sharp

/-- The fixed-frequency scheme of route A. -/
def schemeA (N : NumA) (𝔅 : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ)))
    (h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ) (ω : Fin N.n → ℝ) (μ : ℝ) :
    SchemeA N.n 8 ((Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)) where
  tor := fun K => K
  par := fun _ => 0
  Adm := fun s ε m K => AdmA 𝔅 h ω (N.r s) (N.r s - N.δ s) (μ - m 0) ε (m 1) (m 2) (m 3) (m 4)
    (m 5) (m 6) (m 7) K
  step := fun s K => newtonMap h K ω (N.r s - 2 * N.δ s)

/-- The caps of the eight bounds; `b` is the ball budget. -/
def NumA.capV (N : NumA) (b : ℝ) : Fin 8 → ℝ := ![b, N.sK, N.sB, N.sT, N.sLt, N.sN, N.sNt, N.t]

variable {N : NumA} {τ M : ℝ} {𝔅 : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))}
  {h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ} {ω : Fin N.n → ℝ} {γ : ℝ}
  {Ω : Set (Fin N.n → ℝ)}

/-- The small-divisor inputs of `step_A` at stage `s`: in the prefix the full bite `r_s`, in the tail
the bite `δ_s` itself. -/
theorem NumA.Cert.at (hN : N.Wf) (hC : N.Cert γ Ω) (s : ℕ) :
    SDConst N.n N.τ γ (N.δ s) (N.cS s) Ω ∧ ∃ b cb, SDConst N.n N.τ γ b cb Ω ∧ b ≤ N.r s ∧
      cb * b ^ (-N.τ) ≤ N.caS s * N.δ s ^ (-N.τ) := by
  have hδ := hN.δ_pos s
  have hr := hN.r_pos s
  by_cases hs : s < N.kp
  · refine ⟨by simpa [NumA.cS, hs] using hC.stage s hs, N.r s, N.cbar s, hC.bar s hs, le_rfl, ?_⟩
    have h1 : (N.δ s / N.r s) ^ N.τ * N.δ s ^ (-N.τ) = N.r s ^ (-N.τ) := by
      rw [Real.div_rpow hδ.le hr.le, Real.rpow_neg hδ.le, Real.rpow_neg hr.le]
      have := Real.rpow_pos_of_pos hδ N.τ
      have := Real.rpow_pos_of_pos hr N.τ
      field_simp
    simp only [NumA.caS, hs, ite_true]
    rw [mul_assoc, h1]
  · have hle : N.δ s ≤ N.δ N.kp := hN.δ_anti (not_lt.1 hs)
    have hc : SDConst N.n N.τ γ (N.δ s) N.ctail Ω := hC.tail _ hδ hle
    have e1 : N.cS s = N.ctail := by simp [NumA.cS, hs]
    have e2 : N.caS s = N.ctail := by simp [NumA.caS, hs]
    rw [e1, e2]
    refine ⟨hc, N.δ s, N.ctail, hc, ?_, le_rfl⟩
    have := hN.lam_δ_lt s
    linarith

/-- (N1), (N2) of the fixed-frequency scheme of route A. -/
theorem schemeA_isNewton (hN : N.Wf) (hfix : N.iso = false) (hΘ : N.Θ = 0)
    (hS : Standing N.n τ M N.sK N.sB N.sT 𝔅 h ω γ)
    (hd1 : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ N.M1)
    (hd2 : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ N.M2)
    (hγb : γ ≤ N.γb) (hω : ω ∈ Ω) (hC : N.Cert γ Ω) {μ b : ℝ} (hb : b < μ) :
    (schemeA N 𝔅 h ω μ).IsNewton (2 * N.τ) 3 N.ρ N.ρinf γ N.stage jA
      (fun s x => (N.inp s).Cond x) (N.capV b) where
  adm := fun {s ε m x} hx => ⟨AdmA.ε_nonneg hx, AdmA.holo hx, AdmA.primary hx, AdmA.real hx⟩
  step := by
    intro s ε m K hx hcond hcap
    have hA : AdmA 𝔅 h ω (N.r s) (N.r s - N.δ s) (μ - m 0) ε (m 1) (m 2) (m 3) (m 4) (m 5) (m 6)
        (m 7) K := hx
    set p := N.inp s with hp
    have hpos : p.Pos := hN.pos s
    have hδ := hN.δ_pos s
    obtain ⟨hc, b', cb, hcb, hbr, hca⟩ := hC.at hN s
    set X := ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + 1)) with hX
    set E := ε / (γ ^ 2 * N.δ s ^ (2 * N.τ)) with hE
    have e1 : ∀ c : ℝ, c * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((1 : ℕ) : ℝ))) = c * X := fun c => by
      rw [Nat.cast_one, mul_div_assoc]
    have e0 : ∀ c : ℝ, c * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((0 : ℕ) : ℝ))) = c * E := fun c => by
      rw [Nat.cast_zero, add_zero, mul_div_assoc]
    have c0 : m 0 + p.CDK * E ≤ b := by
      have := hcap 0
      rwa [show (N.stage s).rate 0 = p.CDK from rfl, show ((jA 0 : ℕ) : ℝ) = ((0 : ℕ) : ℝ) from rfl,
        show deltaSeq 3 N.ρ N.ρinf s = N.δ s from rfl, e0] at this
    have cj : ∀ (i : Fin 8) (c : ℝ), (N.stage s).rate i = c → jA i = 1 →
        m i + c * X ≤ N.capV b i := by
      intro i c hc1 hj
      have := hcap i
      rwa [hc1, hj, show deltaSeq 3 N.ρ N.ρinf s = N.δ s from rfl, e1] at this
    have c1 : m 1 + (N.n : ℝ) * p.CDK * X ≤ N.sK := cj 1 _ rfl rfl
    have c2 : m 2 + p.CB * p.CDK * X ≤ N.sB := cj 2 _ rfl rfl
    have c3 : m 3 + p.rT * X ≤ N.sT := cj 3 _ rfl rfl
    have c4 : m 4 + 2 * (N.n : ℝ) * p.CDK * X ≤ N.sLt := cj 4 _ rfl rfl
    have c5 : m 5 + p.CNd * p.CDK * X ≤ N.sN := cj 5 _ rfl rfl
    have c6 : m 6 + p.CNtd * p.CDK * X ≤ N.sNt := cj 6 _ rfl rfl
    have c7 : m 7 + p.CDT * X ≤ N.t := cj 7 _ rfl rfl
    have hβ : p.CDK * E < μ - m 0 := by linarith
    obtain ⟨hA', -, hclose⟩ := step_A (p := p) (n := N.n) (ω := ω) hpos hfix hΘ rfl hS hd1 hd2 hγb
      hω hA hδ (hN.δ_le_dS s) (hN.lam_δ_lt s) hc hcb hbr hca hcond hβ c1 c2 c3 c4 c5 c6 c7
    refine ⟨?_, fun θ hθ => ?_, ?_⟩
    · show AdmA 𝔅 h ω (N.r (s + 1)) (N.r (s + 1) - N.δ (s + 1))
        (μ - (m 0 + (N.stage s).rate 0 * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((0 : ℕ) : ℝ)))))
        (p.CE * ε ^ 2 / (γ ^ 4 * N.δ s ^ (2 * (2 * N.τ))))
        (m 1 + (N.n : ℝ) * p.CDK * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 2 + p.CB * p.CDK * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 3 + p.rT * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 4 + 2 * (N.n : ℝ) * p.CDK * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 5 + p.CNd * p.CDK * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 6 + p.CNtd * p.CDK * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 7 + p.CDT * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (newtonMap h K ω (N.r s - 2 * N.δ s))
      rw [e0 ((N.stage s).rate 0), e1, e1, e1, e1, e1, e1, e1, NumA.r_succ, NumA.δ_succ,
        show μ - (m 0 + (N.stage s).rate 0 * E) = μ - m 0 - p.CDK * E by
          rw [show (N.stage s).rate 0 = p.CDK from rfl]; ring]
      exact hA'
    · have hθ' : θ ∈ complexStrip N.n (N.r s - 3 * N.δ s) := by
        rw [← NumA.r_succ]; exact hθ
      obtain ⟨h1, h2⟩ := hclose θ hθ'
      refine ⟨?_, ?_⟩
      · show ‖newtonMap h K ω (N.r s - 2 * N.δ s) θ - K θ‖ ≤
          p.CDK * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ))
        rw [mul_div_assoc]
        exact h1
      · show ‖fderiv ℂ (newtonMap h K ω (N.r s - 2 * N.δ s)) θ - fderiv ℂ K θ‖ ≤
          (N.n : ℝ) * p.CDK * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + 1))
        rw [mul_div_assoc]
        exact h2
    · show |(0 : ℝ) - 0| ≤ 0 * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ))
      simp

end KAM.Sharp2.RouteA

end
