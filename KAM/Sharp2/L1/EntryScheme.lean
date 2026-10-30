/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.L1.EntryStep
public import KAM.Sharp2.RouteA.Scheme
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-!
# The scheme of route A with the ℓ¹ entry (package B10c)

Blueprint `bp:p2s2l1:engine` of `blueprint/parts/p2s2-l1hybrid.tex`, on B9's stage-indexed engine:

* `schemeAL1`: B9's `schemeA` whose stage-`0` admissibility also carries the entry hypotheses
  (no restart: the schedule is B9's, AUDIT-B10D-1 F5);
* `schemeAL1_isNewton`: (N1), (N2); stage `0` is `KAM.Sharp2.L1.entry_step_A`, every later stage is
  `KAM.Sharp2.RouteA.schemeA_isNewton`;
* `routeAOkL1`, `routeAOkL1.runData`: (J1)–(J3) with the entry at stage `0`, as the engine's
  `RunData` (nonnegativity of the entry constants, downward closure of `EntryCond`, the tail).

`schemeAL1`, `schemeAL1_isNewton`, `routeAOkL1`, `routeAOkL1.runData` are the repaired signatures,
verbatim.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix KAM.Sharp.Engine

namespace KAM.Sharp2.L1

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2.RouteA

/-- The route-A scheme with the ℓ¹ entry: B9's `schemeA`, whose stage-`0` admissibility also carries
the entry hypotheses at the current error. The schedule is B9's (`deltaSeq 3`), unchanged (F5). -/
def schemeAL1 (N : NumA) (E : EntryA) (𝔅 : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ)))
    (h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ) (ω : Fin N.n → ℝ) (μ : ℝ) :
    SchemeA N.n 8 ((Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)) where
  tor := fun K => K
  par := fun _ => 0
  Adm := fun s ε m K => (schemeA N 𝔅 h ω μ).Adm s ε m K ∧ (s = 0 → EntryHypA N E h K ω ε)
  step := (schemeA N 𝔅 h ω μ).step

/-- Blueprint `bp:p2s2l1:entryA` in the engine: (N1), (N2) of the scheme with the ℓ¹ entry. Stage
`0` is the entry step (the B9 step with the ℓ¹ ingredients of B10a/B10b), every later stage is
`KAM.Sharp2.RouteA.schemeA_isNewton`. -/
theorem schemeAL1_isNewton {N : NumA} {E : EntryA} (hN : N.Wf) (hE : E.Wf) (hfix : N.iso = false)
    (hΘ : N.Θ = 0) {τ M γ : ℝ} {𝔅 : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))}
    {h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ} {ω : Fin N.n → ℝ} {Ω : Set (Fin N.n → ℝ)}
    (hS : Standing N.n τ M N.sK N.sB N.sT 𝔅 h ω γ)
    (hd1 : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ N.M1)
    (hd2 : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ N.M2)
    (hγb : γ ≤ N.γb) (hω : ω ∈ Ω) (hC : N.Cert γ Ω) {μ b : ℝ} (hb : b < μ) :
    (schemeAL1 N E 𝔅 h ω μ).IsNewton (2 * N.τ) 3 N.ρ N.ρinf γ (stageL1 N E) jA (condL1 N E)
      (N.capV b) where
  adm := fun {s ε m x} hx =>
    ⟨AdmA.ε_nonneg hx.1, AdmA.holo hx.1, AdmA.primary hx.1, AdmA.real hx.1⟩
  step := by
    intro s ε m K hx hcond hcap
    have hB9 := schemeA_isNewton hN hfix hΘ hS hd1 hd2 hγb hω hC hb
    rcases Nat.eq_zero_or_pos s with hs | hs
    · -- the entry stage
      subst hs
      have hEH : EntryHypA N E h K ω ε := hx.2 rfl
      have hA : AdmA 𝔅 h ω (N.r 0) (N.r 0 - N.δ 0) (μ - m 0) ε (m 1) (m 2) (m 3) (m 4) (m 5)
          (m 6) (m 7) K := hx.1
      have hcond' : EntryCond (N.inp 0) E (ε / (γ ^ 4 * N.δ 0 ^ (2 * (2 * N.τ)))) := by
        have := hcond
        simp only [condL1, ↓reduceIte] at this
        exact this
      set p := N.inp 0 with hp
      have hpos : p.Pos := hN.pos 0
      have hδ := hN.δ_pos 0
      obtain ⟨hc, b', cb, hcb, hbr, hca⟩ := hC.at hN 0
      set X := ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + 1)) with hX
      set E' := ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ)) with hE'
      have e1 : ∀ c : ℝ, c * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((1 : ℕ) : ℝ))) = c * X :=
        fun c => by rw [Nat.cast_one, mul_div_assoc]
      have e0 : ∀ c : ℝ, c * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((0 : ℕ) : ℝ))) = c * E' :=
        fun c => by rw [Nat.cast_zero, add_zero, mul_div_assoc]
      have hst : stageL1 N E 0 = entryStageA p E := by simp [stageL1, hp]
      have c0 : m 0 + Ent.CDK p E * E' ≤ b := by
        have := hcap 0
        rwa [hst, show (entryStageA p E).rate 0 = Ent.CDK p E by simp [entryStageA],
          show ((jA 0 : ℕ) : ℝ) = ((0 : ℕ) : ℝ) from rfl,
          show deltaSeq 3 N.ρ N.ρinf 0 = N.δ 0 from rfl, e0] at this
      have cj : ∀ (i : Fin 8) (c : ℝ), (entryStageA p E).rate i = c → jA i = 1 →
          m i + c * X ≤ N.capV b i := by
        intro i c hc1 hj
        have := hcap i
        rwa [hst, hc1, hj, show deltaSeq 3 N.ρ N.ρinf 0 = N.δ 0 from rfl, e1] at this
      have c1 : m 1 + Ent.dL p E * X ≤ N.sK := cj 1 _ (by simp [entryStageA]) rfl
      have c2 : m 2 + Ent.rB p E * X ≤ N.sB := cj 2 _ (by simp [entryStageA]) rfl
      have c3 : m 3 + Ent.rT p E * X ≤ N.sT := cj 3 _ (by simp [entryStageA]) rfl
      have c4 : m 4 + Ent.dLt p E * X ≤ N.sLt := cj 4 _ (by simp [entryStageA]) rfl
      have c5 : m 5 + Ent.rN p E * X ≤ N.sN := cj 5 _ (by simp [entryStageA]) rfl
      have c6 : m 6 + Ent.rNt p E * X ≤ N.sNt := cj 6 _ (by simp [entryStageA]) rfl
      have c7 : m 7 + Ent.CDT p E * X ≤ N.t := cj 7 _ (by simp [entryStageA]) rfl
      have hβ : Ent.CDK p E * E' < μ - m 0 := by linarith
      have hδD : N.δ 0 ≤ p.δ := hN.δ_le_dS 0
      obtain ⟨hA', -, hclose⟩ := entry_step_A (p := p) (n := N.n) (ω := ω) hpos hE hfix hΘ rfl hS
        hd1 hd2 hγb hω hA hδ hδD (hN.lam_δ_lt 0) hc hcb hbr hca hEH.toData hcond' hβ c1 c2 c3 c4
        c5 c6 c7
      refine ⟨⟨?_, fun h1 => absurd h1 (Nat.succ_ne_zero 0)⟩, fun θ hθ => ?_, ?_⟩
      · show AdmA 𝔅 h ω (N.r (0 + 1)) (N.r (0 + 1) - N.δ (0 + 1))
          (μ - (m 0 + (stageL1 N E 0).rate 0 * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((0 : ℕ) : ℝ)))))
          ((stageL1 N E 0).CE * ε ^ 2 / (γ ^ 4 * N.δ 0 ^ (2 * (2 * N.τ))))
          (m 1 + (stageL1 N E 0).rate 1 * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
          (m 2 + (stageL1 N E 0).rate 2 * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
          (m 3 + (stageL1 N E 0).rate 3 * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
          (m 4 + (stageL1 N E 0).rate 4 * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
          (m 5 + (stageL1 N E 0).rate 5 * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
          (m 6 + (stageL1 N E 0).rate 6 * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
          (m 7 + (stageL1 N E 0).rate 7 * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
          (newtonMap h K ω (N.r 0 - 2 * N.δ 0))
        rw [e0, e1, e1, e1, e1, e1, e1, e1, NumA.r_succ, NumA.δ_succ, hst]
        simp only [entryStageA, Ent.CDK_eq, Ent.dL_eq, Ent.rB_eq, Ent.rT_eq, Ent.dLt_eq,
          Ent.rN_eq, Ent.rNt_eq, Ent.CDT_eq, Ent.CE_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val]
        rw [show μ - (m 0 + Ent.CDK p E * E') = μ - m 0 - Ent.CDK p E * E' by ring]
        exact hA'
      · have hθ' : θ ∈ complexStrip N.n (N.r 0 - 3 * N.δ 0) := by
          rw [← NumA.r_succ]; exact hθ
        obtain ⟨h1, h2⟩ := hclose θ hθ'
        refine ⟨?_, ?_⟩
        · show ‖newtonMap h K ω (N.r 0 - 2 * N.δ 0) θ - K θ‖ ≤
            (stageL1 N E 0).CD * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ))
          rw [hst, show (entryStageA p E).CD = Ent.CDK p E by simp [entryStageA], mul_div_assoc]
          exact h1
        · show ‖fderiv ℂ (newtonMap h K ω (N.r 0 - 2 * N.δ 0)) θ - fderiv ℂ K θ‖ ≤
            (N.n : ℝ) * (stageL1 N E 0).CD * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + 1))
          rw [hst, show (entryStageA p E).CD = Ent.CDK p E by simp [entryStageA], mul_div_assoc]
          exact h2
      · show |(0 : ℝ) - 0| ≤ (stageL1 N E 0).Cp * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ))
        rw [hst]
        simp [entryStageA]
    · -- the later stages are B9's
      have hs0 : s ≠ 0 := Nat.pos_iff_ne_zero.1 hs
      have hst : stageL1 N E s = N.stage s := by simp [stageL1, hs0]
      have hcond' : (N.inp s).Cond (ε / (γ ^ 4 * deltaSeq 3 N.ρ N.ρinf s ^ (2 * (2 * N.τ)))) := by
        have := hcond
        simp only [condL1, hs0, ↓reduceIte] at this
        exact this
      have hcap' : ∀ i, m i + (N.stage s).rate i * ε /
          (γ ^ 2 * deltaSeq 3 N.ρ N.ρinf s ^ (2 * N.τ + (jA i : ℝ))) ≤ N.capV b i := by
        intro i; have := hcap i; rwa [hst] at this
      obtain ⟨h1, h2, h3⟩ := hB9.step hx.1 hcond' hcap'
      rw [hst]
      exact ⟨⟨h1, fun h0 => absurd h0 (Nat.succ_ne_zero s)⟩, h2, h3⟩

/-- (J1)–(J3) for route A with the ℓ¹ entry at `X⋆`: the entry conditions at `X⋆`, B9's conditions
from stage `1`, the tail, and every cap sum with initial values `m₀` and caps `σ` (F2). -/
structure routeAOkL1 (N : NumA) (E : EntryA) (σ m₀ : Fin 8 → ℝ) (Xs : ℝ) : Prop where
  kp_pos : 1 ≤ N.kp
  Xs_nonneg : 0 ≤ Xs
  J0 : EntryCond (N.inp 0) E Xs
  J1 : ∀ s, 1 ≤ s → s < N.kp → (N.inp s).Cond (xSL1 N E Xs s)
  J1t : (N.inp N.kp).Cond (xSL1 N E Xs N.kp)
  J2 : 2 ^ (2 * (2 * N.τ)) * (N.stage N.kp).CE * xSL1 N E Xs N.kp ≤ 1
  J3 : ∀ i, m₀ i + sumA (2 * N.τ) 3 N.ρ N.ρinf N.γb (xSL1 N E Xs)
    (fun s => (stageL1 N E s).rate i) (2 * N.τ + (jA i : ℝ)) N.kp ≤ σ i

/-- `routeAOkL1` is the engine's `RunData` (nonnegativity of the entry constants from `NumA.Wf`,
`EntryA.Wf`; downward closure of `EntryCond`; the tail is B9's since `1 ≤ kp`). -/
theorem routeAOkL1.runData {N : NumA} {E : EntryA} (hN : N.Wf) (hE : E.Wf) {σ m₀ : Fin 8 → ℝ}
    {Xs : ℝ} (h : routeAOkL1 N E σ m₀ Xs) :
    RunData (2 * N.τ) 3 N.ρ N.ρinf N.γb (stageL1 N E) jA (condL1 N E) σ m₀ N.kp Xs := by
  have hk := Ent.nonneg (hN.pos 0) hE
  have hst0 : stageL1 N E 0 = entryStageA (N.inp 0) E := by simp [stageL1]
  have hstS : ∀ s, s ≠ 0 → stageL1 N E s = N.stage s := fun s hs => by simp [stageL1, hs]
  have hkp0 : N.kp ≠ 0 := by have := h.kp_pos; omega
  have hx0 : xSL1 N E Xs 0 = Xs := rfl
  exact
    { two_le_a := by linarith [hN.τ_ge]
      j_le := by intro i; fin_cases i <;> simp [jA]
      CE_nonneg := fun s => by
        rcases Nat.eq_zero_or_pos s with hs | hs
        · subst hs; rw [hst0]; simp only [entryStageA, Ent.CE_eq]; exact hk.CE
        · rw [hstS s hs.ne']; exact (hN.pos s).CE
      CD_nonneg := fun s => by
        rcases Nat.eq_zero_or_pos s with hs | hs
        · subst hs; rw [hst0]; simp only [entryStageA, Ent.CDK_eq]; exact hk.CDK
        · rw [hstS s hs.ne']; exact (hN.pos s).CDK
      Cp_nonneg := fun s => by
        rcases Nat.eq_zero_or_pos s with hs | hs
        · subst hs; rw [hst0]; exact le_rfl
        · rw [hstS s hs.ne']; exact le_rfl
      rate_nonneg := fun s i => by
        rcases Nat.eq_zero_or_pos s with hs | hs
        · subst hs; rw [hst0]; exact entryStageA_rate_nonneg (hN.pos 0) hE i
        · rw [hstS s hs.ne']; exact NumA.rateV_nonneg (hN.pos s) i
      tail := fun s hs => by
        rw [hstS s (by omega), hstS N.kp hkp0]
        exact NumA.stage_tail hs
      Xs_nonneg := h.Xs_nonneg
      down := fun s x y hx hxy hc => by
        rcases Nat.eq_zero_or_pos s with hs | hs
        · subst hs
          simp only [condL1, ↓reduceIte] at hc ⊢
          exact hc.down (hN.pos 0) hE hxy
        · simp only [condL1, hs.ne', ↓reduceIte] at hc ⊢
          exact hc.down (hN.pos s) hxy
      J1 := fun s hs => by
        rcases Nat.eq_zero_or_pos s with h0 | h0
        · subst h0
          simp only [condL1, ↓reduceIte]
          exact h.J0
        · simp only [condL1, h0.ne', ↓reduceIte]
          exact h.J1 s h0 hs
      J1t := fun s hs => by
        simp only [condL1, (show s ≠ 0 by omega), ↓reduceIte]
        rw [NumA.inp_tail hs]
        exact h.J1t
      J2 := by rw [hstS N.kp hkp0]; exact h.J2
      J3 := h.J3 }

end KAM.Sharp2.L1

end
