/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.RouteA.Step
public import KAM.Sharp2.RouteA.Scheme
public import KAM.Iso.Sharp.Scheme
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-!
# The isoenergetic scheme of route A

`schemeIA`: the additive scheme on pairs `(K, s)`, with nine cap values: the eight of the
fixed-frequency
scheme and the used part of the ray margin `ν`. `schemeIA_isNewton` proves (N1), (N2) from
`step_IA`, and
`routeAOkI` is (J1)–(J3) with the frequency budget.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix KAM.Sharp.Engine

namespace KAM.Iso.Sharp2.RouteA

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp

/-- The nine rates of the isoenergetic step. -/
def rateI (p : StepInA) : Fin 9 → ℝ :=
  ![p.CDK, p.n * p.CDK, p.CB * p.CDK, p.rT, 2 * p.n * p.CDK, p.CNd * p.CDK, p.CNtd * p.CDK, p.CDT,
    p.CDw]

/-- The weight exponents: `0` for the ball and the frequency, `1` for the frames. -/
def jI : Fin 9 → ℕ := ![0, 1, 1, 1, 1, 1, 1, 1, 0]

/-- The constants of stage `s` of the isoenergetic scheme. -/
def stageI (N : NumA) (s : ℕ) : StageA 9 where
  CE := (N.inp s).CE
  CD := (N.inp s).CDK
  Cp := (N.inp s).CDw
  rate := rateI (N.inp s)

/-- The recursion of the normalised error from `Xs`. -/
def xI (N : NumA) (Xs : ℝ) : ℕ → ℝ := xA (2 * N.τ) (fun s => (stageI N s).CE) Xs

/-- The caps; `b` is the ball budget, `bν` the frequency budget. -/
def capI (N : NumA) (b bν : ℝ) : Fin 9 → ℝ :=
  ![b, N.sK, N.sB, N.sT, N.sLt, N.sN, N.sNt, N.t, bν]

/-- (J1)–(J3) for the isoenergetic route A at `X⋆`. -/
structure routeAOkI (N : NumA) (σ m₀ : Fin 9 → ℝ) (Xs : ℝ) : Prop where
  Xs_nonneg : 0 ≤ Xs
  J1 : ∀ s < N.kp, (N.inp s).Cond (xI N Xs s)
  J1t : (N.inp N.kp).Cond (xI N Xs N.kp)
  J2 : 2 ^ (2 * (2 * N.τ)) * (stageI N N.kp).CE * xI N Xs N.kp ≤ 1
  J3 : ∀ i, m₀ i + sumA (2 * N.τ) 3 N.ρ N.ρinf N.γb (xI N Xs) (fun s => (stageI N s).rate i)
    (2 * N.τ + (jI i : ℝ)) N.kp ≤ σ i

theorem rateI_nonneg {p : StepInA} (hp : p.Pos) (i : Fin 9) : 0 ≤ rateI p i := by
  have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hDK := hp.CDK
  fin_cases i
  · exact hDK
  · exact mul_nonneg hn hDK
  · exact mul_nonneg hp.CB hDK
  · exact hp.rT
  · exact mul_nonneg (mul_nonneg two_pos.le hn) hDK
  · exact mul_nonneg hp.CNd hDK
  · exact mul_nonneg hp.CNtd hDK
  · exact hp.CDT
  · exact hp.CDw

theorem stageI_tail {N : NumA} {s : ℕ} (hs : N.kp ≤ s) : stageI N s = stageI N N.kp := by
  simp only [stageI, NumA.inp_tail hs]

/-- `routeAOkI` is the engine's `RunData`. -/
theorem routeAOkI.runData {N : NumA} (hN : N.Wf) {σ m₀ : Fin 9 → ℝ} {Xs : ℝ}
    (h : routeAOkI N σ m₀ Xs) :
    RunData (2 * N.τ) 3 N.ρ N.ρinf N.γb (stageI N) jI (fun s x => (N.inp s).Cond x) σ m₀ N.kp Xs
        where
  two_le_a := by linarith [hN.τ_ge]
  j_le := by intro i; fin_cases i <;> simp [jI]
  CE_nonneg := fun s => (hN.pos s).CE
  CD_nonneg := fun s => (hN.pos s).CDK
  Cp_nonneg := fun s => (hN.pos s).CDw
  rate_nonneg := fun s i => rateI_nonneg (hN.pos s) i
  tail := fun _ hs => stageI_tail hs
  Xs_nonneg := h.Xs_nonneg
  down := fun s _ _ _ hxy hc => hc.down (hN.pos s) hxy
  J1 := h.J1
  J1t := fun s hs => by rw [NumA.inp_tail hs]; exact h.J1t
  J2 := h.J2
  J3 := h.J3

/-- The isoenergetic scheme of route A. -/
def schemeIA (N : NumA) (D : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ)))
    (H : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ) (ωstar : Fin N.n → ℝ) (E₀ σω ν μ : ℝ) :
    SchemeA N.n 9 (IsoState N.n) where
  tor := fun x => x.1
  par := fun x => x.2 * ‖ωstar‖
  Adm := fun s ε m x => AdmIA D H ωstar E₀ (N.r s) (N.r s - N.δ s) (μ - m 0) ε x.2 (m 1) (m 2) (m 3)
      (m 4) (m 5) (m 6) (m 7) x.1 ∧ ν - m 8 ≤ rayMargin σω ωstar x.2
  step := fun s x => (isoNewtonMap H x.1 ωstar E₀ x.2 (N.r s - 2 * N.δ s),
    isoNewS H x.1 ωstar E₀ x.2)

variable {N : NumA} {τ M σω ν γ E₀ : ℝ} {D : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))}
  {H : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ} {ωstar : Fin N.n → ℝ} {Ω : Set (Fin N.n → ℝ)}

/-- A positive ray margin bounds the frequency by `σ_ω |ω*|`. -/
theorem norm_smul_le_of_margin {s ν' : ℝ} (hs : 1 < s) (hν' : 0 < ν')
    (h : ν' ≤ rayMargin σω ωstar s) : ‖s • ωstar‖ ≤ σω * ‖ωstar‖ := by
  have hpos : 0 < rayMargin σω ωstar s := hν'.trans_le h
  have hmin : 0 < min (s - 1) (σω - s) := by
    by_contra hneg
    exact absurd (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) (norm_nonneg ωstar))
      (not_le.2 hpos)
  have h2 : s < σω := by linarith [(lt_min_iff.1 hmin).2]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
  exact mul_le_mul_of_nonneg_right h2.le (norm_nonneg _)

/-- (N1), (N2) of the isoenergetic scheme of route A. -/
theorem schemeIA_isNewton (hN : N.Wf) (hiso : N.iso = true) (hΘ : N.Θ = σω * ‖ωstar‖)
    (hS : IsoStanding N.n τ M N.sK N.sB N.sT σω ν ωstar D H γ)
    (hd1 : ∀ z ∈ D, ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ N.M1)
    (hd2 : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ N.M2)
    (hd2H : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ N.Mh2) {Mh1 : ℝ}
    (hdH : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ Mh1) (hHY : N.HY = Mh1 * N.sN)
    (hγb : γ ≤ N.γb) (hΩ : ∀ s : ℝ, 1 ≤ s → s • ωstar ∈ Ω) (hC : N.Cert γ Ω) {μ b bν : ℝ}
    (hb : b < μ) (hbν : bν < ν) :
    (schemeIA N D H ωstar E₀ σω ν μ).IsNewton (2 * N.τ) 3 N.ρ N.ρinf γ (stageI N) jI
      (fun s x => (N.inp s).Cond x) (capI N b bν) where
  adm := fun {s ε m x} hx => ⟨AdmIA.ε_nonneg hx.1, AdmIA.holo hx.1, AdmIA.primary hx.1,
    AdmIA.real hx.1⟩
  step := by
    intro j ε m x hx hcond hcap
    obtain ⟨hA, hray⟩ := hx
    obtain ⟨K, s⟩ := x
    have hA' : AdmIA D H ωstar E₀ (N.r j) (N.r j - N.δ j) (μ - m 0) ε s (m 1) (m 2) (m 3) (m 4)
        (m 5) (m 6) (m 7) K := hA
    have hray' : ν - m 8 ≤ rayMargin σω ωstar s := hray
    set p := N.inp j with hp
    have hpos : p.Pos := hN.pos j
    have hδ := hN.δ_pos j
    obtain ⟨hc, b', cb, hcb, hbr, hca⟩ := hC.at hN j
    set X := ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + 1)) with hX
    set E := ε / (γ ^ 2 * N.δ j ^ (2 * N.τ)) with hE
    have e1 : ∀ c : ℝ, c * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((1 : ℕ) : ℝ))) = c * X := fun c => by
      rw [Nat.cast_one, mul_div_assoc]
    have e0 : ∀ c : ℝ, c * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((0 : ℕ) : ℝ))) = c * E := fun c => by
      rw [Nat.cast_zero, add_zero, mul_div_assoc]
    have c0 : m 0 + p.CDK * E ≤ b := by
      have := hcap 0
      rwa [show (stageI N j).rate 0 = p.CDK from rfl, show ((jI 0 : ℕ) : ℝ) = ((0 : ℕ) : ℝ) from
          rfl,
        show deltaSeq 3 N.ρ N.ρinf j = N.δ j from rfl, e0] at this
    have c8 : m 8 + p.CDw * E ≤ bν := by
      have := hcap 8
      rwa [show (stageI N j).rate 8 = p.CDw from rfl, show ((jI 8 : ℕ) : ℝ) = ((0 : ℕ) : ℝ) from
          rfl,
        show deltaSeq 3 N.ρ N.ρinf j = N.δ j from rfl, e0] at this
    have cj : ∀ (i : Fin 9) (c : ℝ), (stageI N j).rate i = c → jI i = 1 →
        m i + c * X ≤ capI N b bν i := by
      intro i c hc1 hj
      have := hcap i
      rwa [hc1, hj, show deltaSeq 3 N.ρ N.ρinf j = N.δ j from rfl, e1] at this
    have c1 : m 1 + (N.n : ℝ) * p.CDK * X ≤ N.sK := cj 1 _ rfl rfl
    have c2 : m 2 + p.CB * p.CDK * X ≤ N.sB := cj 2 _ rfl rfl
    have c3 : m 3 + p.rT * X ≤ N.sT := cj 3 _ rfl rfl
    have c4 : m 4 + 2 * (N.n : ℝ) * p.CDK * X ≤ N.sLt := cj 4 _ rfl rfl
    have c5 : m 5 + p.CNd * p.CDK * X ≤ N.sN := cj 5 _ rfl rfl
    have c6 : m 6 + p.CNtd * p.CDK * X ≤ N.sNt := cj 6 _ rfl rfl
    have c7 : m 7 + p.CDT * X ≤ N.t := cj 7 _ rfl rfl
    have hβ : p.CDK * E < μ - m 0 := by linarith
    have hDw0 : 0 ≤ p.CDw * E := by
      have h0 := hA'.ε_nonneg
      exact mul_nonneg hpos.CDw (div_nonneg h0 (by positivity))
    have hνd : p.CDw * E < ν - m 8 := by linarith
    have hν' : 0 < ν - m 8 := by linarith
    have hω : ‖s • ωstar‖ ≤ p.Θ := by
      have := norm_smul_le_of_margin hA'.s_gt hν' hray'
      show ‖s • ωstar‖ ≤ N.Θ
      rw [hΘ]
      exact this
    obtain ⟨hA'', -, hclose, hsd, hray''⟩ := step_IA (p := p) (n := N.n) (ωstar := ωstar) hpos hiso
      rfl hS hd1 hd2 hd2H hdH hHY hγb (hΩ s hA'.s_gt.le) hA' hδ (hN.δ_le_dS j) (hN.lam_δ_lt j)
      hω hc hcb hbr hca hcond hβ hray' hνd c1 c2 c3 c4 c5 c6 c7
    refine ⟨⟨?_, ?_⟩, fun θ hθ => ?_, ?_⟩
    · show AdmIA D H ωstar E₀ (N.r (j + 1)) (N.r (j + 1) - N.δ (j + 1))
        (μ - (m 0 + (stageI N j).rate 0 * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((0 : ℕ) : ℝ)))))
        (p.CE * ε ^ 2 / (γ ^ 4 * N.δ j ^ (2 * (2 * N.τ)))) (isoNewS H K ωstar E₀ s)
        (m 1 + (N.n : ℝ) * p.CDK * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 2 + p.CB * p.CDK * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 3 + p.rT * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 4 + 2 * (N.n : ℝ) * p.CDK * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 5 + p.CNd * p.CDK * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 6 + p.CNtd * p.CDK * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 7 + p.CDT * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (isoNewtonMap H K ωstar E₀ s (N.r j - 2 * N.δ j))
      rw [e0 ((stageI N j).rate 0), e1, e1, e1, e1, e1, e1, e1, NumA.r_succ, NumA.δ_succ,
        show μ - (m 0 + (stageI N j).rate 0 * E) = μ - m 0 - p.CDK * E by
          rw [show (stageI N j).rate 0 = p.CDK from rfl]; ring]
      exact hA''
    · show ν - (m 8 + (stageI N j).rate 8 * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((0 : ℕ) : ℝ)))) ≤
        rayMargin σω ωstar (isoNewS H K ωstar E₀ s)
      rw [e0, show (stageI N j).rate 8 = p.CDw from rfl]
      have h9 : ν - m 8 - p.CDw * E ≤ rayMargin σω ωstar (isoNewS H K ωstar E₀ s) := hray''
      linarith
    · have hθ' : θ ∈ complexStrip N.n (N.r j - 3 * N.δ j) := by
        rw [← NumA.r_succ]; exact hθ
      obtain ⟨h1, h2⟩ := hclose θ hθ'
      refine ⟨?_, ?_⟩
      · show ‖isoNewtonMap H K ωstar E₀ s (N.r j - 2 * N.δ j) θ - K θ‖ ≤
          p.CDK * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ))
        rw [mul_div_assoc]
        exact h1
      · show ‖fderiv ℂ (isoNewtonMap H K ωstar E₀ s (N.r j - 2 * N.δ j)) θ - fderiv ℂ K θ‖ ≤
          (N.n : ℝ) * p.CDK * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + 1))
        rw [mul_div_assoc]
        exact h2
    · show |isoNewS H K ωstar E₀ s * ‖ωstar‖ - s * ‖ωstar‖| ≤
        p.CDw * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ))
      rw [← sub_mul, abs_mul, abs_of_nonneg (norm_nonneg _), mul_div_assoc]
      exact hsd

end KAM.Iso.Sharp2.RouteA

end
