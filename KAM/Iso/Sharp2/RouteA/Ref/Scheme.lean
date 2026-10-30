/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.RouteA.Ref.Step
public import KAM.Iso.Sharp2.RouteA.Scheme
public import KAM.Sharp2.RouteA.Ref.Scheme
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lever L8′ of the isoenergetic route A: the scheme

`schemeRI`: the scheme on pairs `(K, s)` with the torsion against the initial pair `(K₀, s₀)`, and
eight cap values: the seven of `schemeR` and the used part of the ray margin `ν`.
`schemeRI_isNewton` proves (N1), (N2): at the entry to a stage `AdmRI.entry` gives the bounds of `T`
and of the bordered `⟨T⟩⁻¹`, and `step_coreI` is the step. `routeAOkRI` is (J1)–(J3).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix KAM.Sharp.Engine

namespace KAM.Iso.Sharp2.RouteA.Ref

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp KAM.Sharp2.RouteA.Ref

/-- The eight rates. -/
def rateRI (p : StepInA) : Fin 8 → ℝ :=
  ![p.CDK, p.n * p.CDK, p.CB * p.CDK, p.rAb, 2 * p.n * p.CDK, p.CNd * p.CDK, p.CNtd * p.CDK, p.CDw]

/-- The weight exponents: `0` for the ball and the frequency, `1` for the others. -/
def jRI : Fin 8 → ℕ := ![0, 1, 1, 1, 1, 1, 1, 0]

/-- The constants of stage `s`. -/
def stageRI (N : NumA) (s : ℕ) : StageA 8 where
  CE := (N.inp s).CE
  CD := (N.inp s).CDK
  Cp := (N.inp s).CDw
  rate := rateRI (N.inp s)

/-- The caps; `b` is the ball budget, `bT` the budget of `𝒯_ab`, `bν` the frequency budget. -/
def capRI (N : NumA) (b bT bν : ℝ) : Fin 8 → ℝ :=
  ![b, N.sK, N.sB, bT, N.sLt, N.sN, N.sNt, bν]

/-- (J1)–(J3) with the torsion against the initial pair, at `X⋆`. -/
structure routeAOkRI (N : NumA) (bF : ℝ) (σ m₀ : Fin 8 → ℝ) (Xs : ℝ) : Prop where
  Xs_nonneg : 0 ≤ Xs
  J1 : ∀ s < N.kp, N.CondR bF s (xI N Xs s)
  J1t : N.CondR bF N.kp (xI N Xs N.kp)
  J2 : 2 ^ (2 * (2 * N.τ)) * (stageRI N N.kp).CE * xI N Xs N.kp ≤ 1
  J3 : ∀ i, m₀ i + sumA (2 * N.τ) 3 N.ρ N.ρinf N.γb (xI N Xs) (fun s => (stageRI N s).rate i)
    (2 * N.τ + (jRI i : ℝ)) N.kp ≤ σ i

theorem rateRI_nonneg {p : StepInA} (hp : p.Pos) (i : Fin 8) : 0 ≤ rateRI p i := by
  have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hDK := hp.CDK
  fin_cases i
  · exact hDK
  · exact mul_nonneg hn hDK
  · exact mul_nonneg hp.CB hDK
  · exact hp.rAb
  · exact mul_nonneg (mul_nonneg two_pos.le hn) hDK
  · exact mul_nonneg hp.CNd hDK
  · exact mul_nonneg hp.CNtd hDK
  · exact hp.CDw

theorem stageRI_tail {N : NumA} {s : ℕ} (hs : N.kp ≤ s) : stageRI N s = stageRI N N.kp := by
  simp only [stageRI, NumA.inp_tail hs]

/-- `routeAOkRI` is the engine's `RunData`. -/
theorem routeAOkRI.runData {N : NumA} (hN : N.Wf) {bF : ℝ} {σ m₀ : Fin 8 → ℝ} {Xs : ℝ}
    (h : routeAOkRI N bF σ m₀ Xs) :
    RunData (2 * N.τ) 3 N.ρ N.ρinf N.γb (stageRI N) jRI (fun s x => N.CondR bF s x) σ m₀ N.kp Xs
        where
  two_le_a := by linarith [hN.τ_ge]
  j_le := by intro i; fin_cases i <;> simp [jRI]
  CE_nonneg := fun s => (hN.pos s).CE
  CD_nonneg := fun s => (hN.pos s).CDK
  Cp_nonneg := fun s => (hN.pos s).CDw
  rate_nonneg := fun s i => rateRI_nonneg (hN.pos s) i
  tail := fun _ hs => stageRI_tail hs
  Xs_nonneg := h.Xs_nonneg
  down := fun _ _ _ _ hxy hc => hc.down hN hxy
  J1 := h.J1
  J1t := fun s hs => ⟨by rw [NumA.inp_tail hs]; exact h.J1t.base, by
    rw [NumA.bLocS_tail hs]; exact h.J1t.loc⟩
  J2 := h.J2
  J3 := h.J3

/-- The isoenergetic scheme with the torsion against the initial pair `(K₀, s₀)`. -/
def schemeRI (N : NumA) (D : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ)))
    (H : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ) (ωstar : Fin N.n → ℝ) (E₀ σω ν μ : ℝ)
    (K₀ : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)) (s₀ : ℝ) :
    SchemeA N.n 8 (IsoState N.n) where
  tor := fun x => x.1
  par := fun x => x.2 * ‖ωstar‖
  Adm := fun s ε m x => AdmRI D H ωstar E₀ K₀ s₀ (N.r s) (N.r s - N.δ s) (μ - m 0) ε x.2 (m 1) (m 2)
      (m 3) (m 4) (m 5) (m 6) x.1 ∧ ν - m 7 ≤ rayMargin σω ωstar x.2
  step := fun s x => (isoNewtonMap H x.1 ωstar E₀ x.2 (N.r s - 2 * N.δ s),
    isoNewS H x.1 ωstar E₀ x.2)

variable {N : NumA} {τ M σω ν γ E₀ : ℝ} {D : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))}
  {H : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ} {ωstar : Fin N.n → ℝ} {Ω : Set (Fin N.n → ℝ)}

/-- The row of the bordered torsion in the local bound: `n |ηᴸ| ≤ n σ_{Nᵀ} γ̄⁴ δ^{2a} x`. -/
theorem row_le {p : StepInA} (hp : p.Pos) (hpn : p.n = N.n) {γ' δ ε η : ℝ} (hγ : 0 < γ')
    (hγb : γ' ≤ p.γb) (hδ : 0 < δ) (hδD : δ ≤ p.δ) (hε : 0 ≤ ε) (hη : η ≤ p.sNt * ε) :
    (N.n : ℝ) * η ≤ p.n * p.sNt * (p.γb ^ 4 * p.δ ^ (2 * (2 * p.κ))) *
      (ε / (γ' ^ 4 * δ ^ (2 * (2 * p.κ)))) := by
  have hκ := hp.κ_ge
  have hδp : 0 < δ ^ (2 * (2 * p.κ)) := Real.rpow_pos_of_pos hδ _
  have hn0 : (0 : ℝ) ≤ N.n := Nat.cast_nonneg _
  have hx0 : 0 ≤ ε / (γ' ^ 4 * δ ^ (2 * (2 * p.κ))) := div_nonneg hε (by positivity)
  have e : ε = γ' ^ 4 * δ ^ (2 * (2 * p.κ)) * (ε / (γ' ^ 4 * δ ^ (2 * (2 * p.κ)))) := by
    field_simp
  have b4 := mul_le_mul_of_nonneg_right
    (pow_mul_rpow_le (j := 2 * (2 * p.κ)) 4 hγ hγb hδ hδD (by linarith)) hx0
  have h1 : p.sNt * ε ≤ p.sNt * (p.γb ^ 4 * p.δ ^ (2 * (2 * p.κ)) *
      (ε / (γ' ^ 4 * δ ^ (2 * (2 * p.κ))))) :=
    mul_le_mul_of_nonneg_left (e.le.trans b4) hp.sNt
  have h2 := mul_le_mul_of_nonneg_left (hη.trans h1) hn0
  rw [hpn]
  refine h2.trans (le_of_eq ?_)
  ring

/-- (N1), (N2) of the isoenergetic scheme with the torsion against the initial pair. -/
theorem schemeRI_isNewton (hN : N.Wf) (hiso : N.iso = true) (hΘ : N.Θ = σω * ‖ωstar‖)
    (hS : IsoStanding N.n τ M N.sK N.sB N.sT σω ν ωstar D H γ)
    (hd1 : ∀ z ∈ D, ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ N.M1)
    (hd2 : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ N.M2)
    (hd2H : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ N.Mh2) {Mh1 : ℝ}
    (hdH : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ Mh1) (hHY : N.HY = Mh1 * N.sN)
    (hγb : γ ≤ N.γb) (hΩ : ∀ s : ℝ, 1 ≤ s → s • ωstar ∈ Ω) (hC : N.Cert γ Ω) {μ b bT bν bF iH mT s₀ : ℝ}
    (hb : b < μ) (hbν : bν < ν) {K₀ : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)}
    (hR : RefTI H K₀ (s₀ • ωstar) (N.r 0 - N.δ 0) bF iH mT) (hB : Budget N mT iH bF bT) :
    (schemeRI N D H ωstar E₀ σω ν μ K₀ s₀).IsNewton (2 * N.τ) 3 N.ρ N.ρinf γ (stageRI N) jRI
      (fun s x => N.CondR bF s x) (capRI N b bT bν) where
  adm := fun {s ε m x} hx => ⟨Adm0.ε_nonneg (AdmRI.toAdm0 hx.1), Adm0.holo (AdmRI.toAdm0 hx.1),
    Adm0.primary (AdmRI.toAdm0 hx.1), Adm0.real (AdmRI.toAdm0 hx.1)⟩
  step := by
    intro j ε m x hx hcond hcap
    obtain ⟨hA, hray⟩ := hx
    obtain ⟨K, s⟩ := x
    have hA' : AdmRI D H ωstar E₀ K₀ s₀ (N.r j) (N.r j - N.δ j) (μ - m 0) ε s (m 1) (m 2) (m 3)
        (m 4) (m 5) (m 6) K := hA
    have hray' : ν - m 7 ≤ rayMargin σω ωstar s := hray
    set p := N.inp j with hp
    have hpos : p.Pos := hN.pos j
    have hδ := hN.δ_pos j
    have hisop : p.iso = true := hiso
    have hγ := hS.gamma_pos
    have hSt := (hS.setting hA'.s_gt.le).toStanding
    obtain ⟨hc, b', cb, hcb, hbr, hca⟩ := hC.at hN j
    set X := ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + 1)) with hX
    set E := ε / (γ ^ 2 * N.δ j ^ (2 * N.τ)) with hE
    have hX0 : 0 ≤ X := div_nonneg hA'.ε_nonneg (by positivity)
    have e1 : ∀ c : ℝ, c * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((1 : ℕ) : ℝ))) = c * X := fun c => by
      rw [Nat.cast_one, mul_div_assoc]
    have e0 : ∀ c : ℝ, c * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((0 : ℕ) : ℝ))) = c * E := fun c => by
      rw [Nat.cast_zero, add_zero, mul_div_assoc]
    have c0 : m 0 + p.CDK * E ≤ b := by
      have := hcap 0
      rwa [show (stageRI N j).rate 0 = p.CDK from rfl, show ((jRI 0 : ℕ) : ℝ) = ((0 : ℕ) : ℝ) from
          rfl,
        show deltaSeq 3 N.ρ N.ρinf j = N.δ j from rfl, e0] at this
    have c8 : m 7 + p.CDw * E ≤ bν := by
      have := hcap 7
      rwa [show (stageRI N j).rate 7 = p.CDw from rfl, show ((jRI 7 : ℕ) : ℝ) = ((0 : ℕ) : ℝ) from
          rfl,
        show deltaSeq 3 N.ρ N.ρinf j = N.δ j from rfl, e0] at this
    have cj : ∀ (i : Fin 8) (c : ℝ), (stageRI N j).rate i = c → jRI i = 1 →
        m i + c * X ≤ capRI N b bT bν i := by
      intro i c hc1 hj
      have := hcap i
      rwa [hc1, hj, show deltaSeq 3 N.ρ N.ρinf j = N.δ j from rfl, e1] at this
    have c1 : m 1 + (N.n : ℝ) * p.CDK * X ≤ N.sK := cj 1 _ rfl rfl
    have c2 : m 2 + p.CB * p.CDK * X ≤ N.sB := cj 2 _ rfl rfl
    have c3 : m 3 + p.rAb * X ≤ bT := cj 3 _ rfl rfl
    have c4 : m 4 + 2 * (N.n : ℝ) * p.CDK * X ≤ N.sLt := cj 4 _ rfl rfl
    have c5 : m 5 + p.CNd * p.CDK * X ≤ N.sN := cj 5 _ rfl rfl
    have c6 : m 6 + p.CNtd * p.CDK * X ≤ N.sNt := cj 6 _ rfl rfl
    have hβ : p.CDK * E < μ - m 0 := by linarith
    have hDw0 : 0 ≤ p.CDw * E := by
      have h0 := hA'.ε_nonneg
      exact mul_nonneg hpos.CDw (div_nonneg h0 (by positivity))
    have hνd : p.CDw * E < ν - m 7 := by linarith
    have hν' : 0 < ν - m 7 := by linarith
    have hω : ‖s • ωstar‖ ≤ p.Θ := by
      have := norm_smul_le_of_margin hA'.s_gt hν' hray'
      show ‖s • ωstar‖ ≤ N.Θ
      rw [hΘ]
      exact this
    have hn0 : (0 : ℝ) ≤ N.n := Nat.cast_nonneg _
    have hDK0 := hpos.CDK
    have hm1 : m 1 ≤ N.sK := le_of_add_le_of_nonneg_left c1 (by positivity)
    have hm2 : m 2 ≤ N.sB :=
      le_of_add_le_of_nonneg_left c2 (mul_nonneg (mul_nonneg hpos.CB hDK0) hX0)
    have hm3 : m 3 ≤ bT := le_of_add_le_of_nonneg_left c3 (mul_nonneg hpos.rAb hX0)
    have hm4 : m 4 ≤ N.sLt := le_of_add_le_of_nonneg_left c4 (by positivity)
    have hm5 : m 5 ≤ N.sN :=
      le_of_add_le_of_nonneg_left c5 (mul_nonneg (mul_nonneg hpos.CNd hDK0) hX0)
    have hm6 : m 6 ≤ N.sNt :=
      le_of_add_le_of_nonneg_left c6 (mul_nonneg (mul_nonneg hpos.CNtd hDK0) hX0)
    have h3δ := hN.lam_δ_lt j
    have hδD := hN.δ_le_dS j
    obtain ⟨hεδ, -, -, -⟩ := hcond.base.facts hpos hγ hγb hδ hδD hA'.ε_nonneg
    have hc2 : SDConst N.n N.τ γ (N.δ j / 2) (N.cS (j + 1)) Ω := by
      have := (hC.at hN (j + 1)).1
      rwa [NumA.δ_succ] at this
    have hx0 : 0 ≤ ε / (γ ^ 4 * N.δ j ^ (2 * (2 * N.τ))) :=
      div_nonneg hA'.ε_nonneg (by positivity)
    have hbL : N.bLocS j = max (p.bLoc0 (N.cS (j + 1)))
        (p.n * p.sNt * (p.γb ^ 4 * p.δ ^ (2 * (2 * p.κ)))) := by
      simp [NumA.bLocS, StepInA.bLoc, hisop, ← hp]
    have hl2 := hcond.loc
    rw [hbL] at hl2
    have hcaps := hA'.toAdm0.mono hm1 hm2 hm4 hm5 hm6
    have hloc : ∀ θ ∈ complexStrip N.n (N.r j - N.δ j),
        ‖torsion H K (s • ωstar) θ - torsionAB H K θ‖ ≤ bF := fun θ hθ => by
      have h1 := local_bound hpos rfl hSt hd1 hγb (hΩ s hA'.s_gt.le) hcaps hδ hδD
        (by linarith) hεδ hc2 θ hθ
      exact h1.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hx0).trans hl2)
    have hrow : ∀ θ ∈ complexStrip N.n (N.r j - N.δ j),
        (N.n : ℝ) * ‖etaL H K (s • ωstar) θ‖ ≤ bF := fun θ hθ => by
      have hθr : θ ∈ complexStrip N.n (N.r j) := Triangular.strip_mono (by linarith) hθ
      have h1 := norm_etaL_le (hcaps.normalT θ hθr) (hcaps.error_le θ hθr)
      have h2 := row_le (N := N) hpos rfl hγ hγb hδ hδD hA'.ε_nonneg h1
      exact h2.trans ((mul_le_mul_of_nonneg_right (le_max_right _ _) hx0).trans hl2)
    have hrT : 0 < N.r j - N.δ j := by linarith
    have hGu := fun θ hθ => (hcaps.gram θ hθ).1
    have hcont := (extended_regular hSt hcaps.r_pos hcaps.holo hcaps.mem hGu (s • ωstar)).2.2
    have hAd : AdmIA D H ωstar E₀ (N.r j) (N.r j - N.δ j) (μ - m 0) ε s (m 1) (m 2) N.sT (m 4) (m 5)
        (m 6) N.t K := hA'.entry hR (strip_sub hN j) hcont hrT (by linarith) hloc hrow hB.mT_pos
      hB.mT_lt (by have := hB.beta; linarith) (by have := hB.sup; linarith)
    obtain ⟨hA'', hs', hen, -, hclose, hab, hsd, hray''⟩ := step_coreI (p := p) (n := N.n)
      (ωstar := ωstar) hpos hiso rfl hS hd1 hd2 hd2H hdH hHY hγb (hΩ s hA'.s_gt.le) hAd hδ hδD h3δ
      hω hc hcb hbr hca hcond.base hβ hray' hνd c1 c2 c4 c5 c6
    have hrAb : p.rAb = max (p.CDab * p.CDK + p.CDw * p.δ) (p.n * p.CDw * p.δ) := by
      simp [StepInA.rAb, hisop]
    have hEX : E ≤ p.δ * X := by
      obtain ⟨-, -, s3, -, -, -, -, -⟩ := scales (ε := ε) (κ := N.τ) hγ hδ
      have hD : E = N.δ j * X := s3
      rw [hD]
      exact mul_le_mul_of_nonneg_right hδD hX0
    have hDw0' := hpos.CDw
    have hEdw : p.CDw * E ≤ p.CDw * p.δ * X := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hEX hDw0'
    have hdω : ‖isoNewS H K ωstar E₀ s • ωstar - s • ωstar‖ ≤ p.CDw * E := by
      have e : ‖isoNewS H K ωstar E₀ s • ωstar - s • ωstar‖ =
          |isoNewS H K ωstar E₀ s - s| * ‖ωstar‖ :=
        (KAM.Iso.Apost.ray (σω := σω) hS.dio).2.2.2.1 s _
      rw [e]
      exact hsd
    have hnN : ((p.n : ℕ) : ℝ) = N.n := rfl
    refine ⟨⟨?_, ?_⟩, fun θ hθ => ?_, ?_⟩
    · show AdmRI D H ωstar E₀ K₀ s₀ (N.r (j + 1)) (N.r (j + 1) - N.δ (j + 1))
        (μ - (m 0 + (stageRI N j).rate 0 * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((0 : ℕ) : ℝ)))))
        (p.CE * ε ^ 2 / (γ ^ 4 * N.δ j ^ (2 * (2 * N.τ)))) (isoNewS H K ωstar E₀ s)
        (m 1 + (N.n : ℝ) * p.CDK * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 2 + p.CB * p.CDK * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 3 + p.rAb * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 4 + 2 * (N.n : ℝ) * p.CDK * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 5 + p.CNd * p.CDK * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 6 + p.CNtd * p.CDK * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (isoNewtonMap H K ωstar E₀ s (N.r j - 2 * N.δ j))
      rw [e0 ((stageRI N j).rate 0), e1, e1, e1, e1, e1, e1, NumA.r_succ, NumA.δ_succ,
        show μ - (m 0 + (stageRI N j).rate 0 * E) = μ - m 0 - p.CDK * E by
          rw [show (stageRI N j).rate 0 = p.CDK from rfl]; ring]
      have hr1 : p.CDab * p.CDK * X + p.CDw * E ≤ p.rAb * X := by
        rw [hrAb, max_mul_of_nonneg _ _ hX0]
        refine le_max_of_le_left ?_
        calc _ ≤ p.CDab * p.CDK * X + p.CDw * p.δ * X := add_le_add le_rfl hEdw
          _ = _ := by ring
      have hr2 : (N.n : ℝ) * (p.CDw * E) ≤ p.rAb * X := by
        rw [hrAb, max_mul_of_nonneg _ _ hX0, ← hnN]
        refine le_max_of_le_right ?_
        calc _ ≤ (p.n : ℝ) * (p.CDw * p.δ * X) := mul_le_mul_of_nonneg_left hEdw (Nat.cast_nonneg _)
          _ = _ := by ring
      refine ⟨hA'', hs', hen, fun θ hθ => ?_, ?_⟩
      · have hθ3 : θ ∈ complexStrip N.n (N.r j - 3 * N.δ j) :=
          Triangular.strip_mono (by linarith) hθ
        have hθ1 : θ ∈ complexStrip N.n (N.r j - N.δ j) :=
          Triangular.strip_mono (by linarith) hθ3
        have h1 := hA'.tab θ hθ1
        have h2 : ‖torsionAB H (isoNewtonMap H K ωstar E₀ s (N.r j - 2 * N.δ j)) θ -
            torsionAB H K θ‖ ≤ p.CDab * (p.CDK * X) := hab θ hθ3
        have h3 := norm_add_le (torsionAB H K θ - torsionAB H K₀ θ)
          (torsionAB H (isoNewtonMap H K ωstar E₀ s (N.r j - 2 * N.δ j)) θ - torsionAB H K θ)
        have h4 := norm_add_le (s • ωstar - s₀ • ωstar) (isoNewS H K ωstar E₀ s • ωstar - s • ωstar)
        have e1' : torsionAB H (isoNewtonMap H K ωstar E₀ s (N.r j - 2 * N.δ j)) θ -
            torsionAB H K₀ θ = (torsionAB H K θ - torsionAB H K₀ θ) +
            (torsionAB H (isoNewtonMap H K ωstar E₀ s (N.r j - 2 * N.δ j)) θ -
              torsionAB H K θ) := by abel
        have e2' : isoNewS H K ωstar E₀ s • ωstar - s₀ • ωstar = (s • ωstar - s₀ • ωstar) +
            (isoNewS H K ωstar E₀ s • ωstar - s • ωstar) := by abel
        rw [e1', e2']
        have h5 : p.CDab * (p.CDK * X) = p.CDab * p.CDK * X := by ring
        linarith
      · have h1 := hA'.freq
        have h2 := norm_add_le (s • ωstar - s₀ • ωstar)
          (isoNewS H K ωstar E₀ s • ωstar - s • ωstar)
        have e2' : isoNewS H K ωstar E₀ s • ωstar - s₀ • ωstar = (s • ωstar - s₀ • ωstar) +
            (isoNewS H K ωstar E₀ s • ωstar - s • ωstar) := by abel
        rw [e2']
        have h3 := mul_le_mul_of_nonneg_left (h2.trans (add_le_add le_rfl hdω)) hn0
        rw [mul_add] at h3
        linarith
    · show ν - (m 7 + (stageRI N j).rate 7 * ε / (γ ^ 2 * N.δ j ^ (2 * N.τ + ((0 : ℕ) : ℝ)))) ≤
        rayMargin σω ωstar (isoNewS H K ωstar E₀ s)
      rw [e0, show (stageRI N j).rate 7 = p.CDw from rfl]
      have h9 : ν - m 7 - p.CDw * E ≤ rayMargin σω ωstar (isoNewS H K ωstar E₀ s) := hray''
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

end KAM.Iso.Sharp2.RouteA.Ref

end
