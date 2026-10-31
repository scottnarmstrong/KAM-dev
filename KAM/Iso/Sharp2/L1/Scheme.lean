/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.L1.EntryStep
public import KAM.Iso.Sharp2.RouteA.Scheme
public import KAM.Sharp2.L1.EntryScheme
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-!
# The isoenergetic scheme of route A with the ℓ¹ entry (package B10c)

* `entryStageIA`, `stageIL1`, `xIL1`: the entry stage (B9's nine rates, `Cp = C_Δω`) at stage `0`,
  B9's `stageI` from stage `1`;
* `routeAOkIL1`, `routeAOkIL1.runData`: (J1)–(J3) with the entry, as the engine's `RunData`;
* `schemeIAL1`, `schemeIAL1_isNewton`: B9's `schemeIA` with the entry hypotheses at stage `0`, and
  (N1), (N2): stage `0` is `KAM.Iso.Sharp2.L1.iso_entry_step`, every later stage is B9's
  `schemeIA_isNewton`.

These are the repaired signatures (AUDIT-B10D-1, F3), verbatim.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix KAM.Sharp.Engine

namespace KAM.Iso.Sharp2.L1

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2.RouteA KAM.Iso.Sharp2.RouteA
  KAM.Iso.Apost KAM.Iso.Sharp KAM.Sharp2.L1

/-- The isoenergetic entry stage: B9's nine rates (the last one the frequency rate `C_Δω`) with the
entry constants; `Cp = C_Δω`. -/
def entryStageIA (p : StepInA) (E : EntryA) : StageA 9 where
  CE := (entryConsts p E).CE
  CD := (entryConsts p E).CDK
  Cp := (entryConsts p E).CDw
  rate := ![(entryConsts p E).CDK, (entryConsts p E).dL, (entryConsts p E).rB, (entryConsts p E).rT,
    (entryConsts p E).dLt, (entryConsts p E).rN, (entryConsts p E).rNt, (entryConsts p E).CDT,
    (entryConsts p E).CDw]

/-- The stages of an isoenergetic run with the ℓ¹ entry. -/
def stageIL1 (N : NumA) (E : EntryA) (s : ℕ) : StageA 9 :=
  if s = 0 then entryStageIA (N.inp 0) E else stageI N s

/-- The normalised errors of an isoenergetic run with the ℓ¹ entry. -/
def xIL1 (N : NumA) (E : EntryA) (Xs : ℝ) : ℕ → ℝ := xA (2 * N.τ) (fun s => (stageIL1 N E s).CE) Xs

/-- (J1)–(J3) of the isoenergetic route A with the ℓ¹ entry (caps `capI`, initial values
`initI`). -/
structure routeAOkIL1 (N : NumA) (E : EntryA) (σ m₀ : Fin 9 → ℝ) (Xs : ℝ) : Prop where
  kp_pos : 1 ≤ N.kp
  Xs_nonneg : 0 ≤ Xs
  J0 : EntryCond (N.inp 0) E Xs
  J1 : ∀ s, 1 ≤ s → s < N.kp → (N.inp s).Cond (xIL1 N E Xs s)
  J1t : (N.inp N.kp).Cond (xIL1 N E Xs N.kp)
  J2 : 2 ^ (2 * (2 * N.τ)) * (stageI N N.kp).CE * xIL1 N E Xs N.kp ≤ 1
  J3 : ∀ i, m₀ i + sumA (2 * N.τ) 3 N.ρ N.ρinf N.γb (xIL1 N E Xs)
    (fun s => (stageIL1 N E s).rate i) (2 * N.τ + (jI i : ℝ)) N.kp ≤ σ i

/-- The rates of the isoenergetic entry stage are nonnegative. -/
theorem entryStageIA_rate_nonneg {p : StepInA} {E : EntryA} (hp : p.Pos) (hE : E.Wf)
    (i : Fin 9) : 0 ≤ (entryStageIA p E).rate i := by
  have hk := Ent.nonneg hp hE
  simp only [entryStageIA, Ent.CDK_eq, Ent.dL_eq, Ent.rB_eq, Ent.rT_eq, Ent.dLt_eq, Ent.rN_eq,
    Ent.rNt_eq, Ent.CDT_eq, Ent.CDw_eq]
  fin_cases i
  · exact hk.CDK
  · exact hk.dL
  · exact hk.rB
  · exact hk.rT
  · exact hk.dLt
  · exact hk.rN
  · exact hk.rNt
  · exact hk.CDT
  · exact hk.CDw

/-- `routeAOkIL1` is the engine's `RunData` (as `routeAOkL1.runData`, with B9's `routeAOkI.runData`
from stage `1`). -/
theorem routeAOkIL1.runData {N : NumA} {E : EntryA} (hN : N.Wf) (hE : E.Wf) {σ m₀ : Fin 9 → ℝ}
    {Xs : ℝ} (h : routeAOkIL1 N E σ m₀ Xs) :
    RunData (2 * N.τ) 3 N.ρ N.ρinf N.γb (stageIL1 N E) jI (condL1 N E) σ m₀ N.kp Xs := by
  have hk := Ent.nonneg (hN.pos 0) hE
  have hst0 : stageIL1 N E 0 = entryStageIA (N.inp 0) E := by simp [stageIL1]
  have hstS : ∀ s, s ≠ 0 → stageIL1 N E s = stageI N s := fun s hs => by simp [stageIL1, hs]
  have hkp0 : N.kp ≠ 0 := by have := h.kp_pos; omega
  exact
    { two_le_a := by linarith [hN.τ_ge]
      j_le := by intro i; fin_cases i <;> simp [jI]
      CE_nonneg := fun s => by
        rcases Nat.eq_zero_or_pos s with hs | hs
        · subst hs; rw [hst0]; simp only [entryStageIA, Ent.CE_eq]; exact hk.CE
        · rw [hstS s hs.ne']; exact (hN.pos s).CE
      CD_nonneg := fun s => by
        rcases Nat.eq_zero_or_pos s with hs | hs
        · subst hs; rw [hst0]; simp only [entryStageIA, Ent.CDK_eq]; exact hk.CDK
        · rw [hstS s hs.ne']; exact (hN.pos s).CDK
      Cp_nonneg := fun s => by
        rcases Nat.eq_zero_or_pos s with hs | hs
        · subst hs; rw [hst0]; simp only [entryStageIA, Ent.CDw_eq]; exact hk.CDw
        · rw [hstS s hs.ne']; exact (hN.pos s).CDw
      rate_nonneg := fun s i => by
        rcases Nat.eq_zero_or_pos s with hs | hs
        · subst hs; rw [hst0]; exact entryStageIA_rate_nonneg (hN.pos 0) hE i
        · rw [hstS s hs.ne']; exact rateI_nonneg (hN.pos s) i
      tail := fun s hs => by
        rw [hstS s (by omega), hstS N.kp hkp0]
        exact stageI_tail hs
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

/-- B9's isoenergetic scheme whose stage-`0` admissibility carries the entry hypotheses at the
initial frequency `s ω*`. -/
def schemeIAL1 (N : NumA) (E : EntryA) (D : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ)))
    (H : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ) (ωstar : Fin N.n → ℝ) (E₀ σω ν μ : ℝ) :
    SchemeA N.n 9 (IsoState N.n) where
  tor := fun x => x.1
  par := fun x => x.2 * ‖ωstar‖
  Adm := fun s ε m x => (schemeIA N D H ωstar E₀ σω ν μ).Adm s ε m x ∧
    (s = 0 → EntryHypA N E H x.1 (x.2 • ωstar) ε)
  step := (schemeIA N D H ωstar E₀ σω ν μ).step

/-- (N1), (N2) of the isoenergetic scheme with the ℓ¹ entry; the iso inputs are B9's: `iso = true`,
`Θ = σ_ω ‖ω*‖`, `HY = Mh1 σ_N` with the certified `‖DH‖ ≤ Mh1`, `‖D²H‖ ≤ Mh2` (F3). -/
theorem schemeIAL1_isNewton {N : NumA} {E : EntryA} (hN : N.Wf) (hE : E.Wf) (hiso : N.iso = true)
    {τ M σω ν γ E₀ : ℝ} {D : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))}
    {H : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ} {ωstar : Fin N.n → ℝ} {Ω : Set (Fin N.n → ℝ)}
    (hΘ : N.Θ = σω * ‖ωstar‖) (hS : IsoStanding N.n τ M N.sK N.sB N.sT σω ν ωstar D H γ)
    (hd1 : ∀ z ∈ D, ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ N.M1)
    (hd2 : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ N.M2)
    (hd2H : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ N.Mh2) {Mh1 : ℝ}
    (hdH : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ Mh1) (hHY : N.HY = Mh1 * N.sN)
    (hγb : γ ≤ N.γb) (hΩ : ∀ s : ℝ, 1 ≤ s → s • ωstar ∈ Ω) (hC : N.Cert γ Ω) {μ b bν : ℝ}
    (hb : b < μ) (hbν : bν < ν) :
    (schemeIAL1 N E D H ωstar E₀ σω ν μ).IsNewton (2 * N.τ) 3 N.ρ N.ρinf γ (stageIL1 N E) jI
      (condL1 N E) (capI N b bν) where
  adm := fun {s ε m x} hx => ⟨AdmIA.ε_nonneg hx.1.1, AdmIA.holo hx.1.1, AdmIA.primary hx.1.1,
    AdmIA.real hx.1.1⟩
  step := by
    intro j ε m x hx hcond hcap
    have hB9 := schemeIA_isNewton (E₀ := E₀) hN hiso hΘ hS hd1 hd2 hd2H hdH hHY hγb hΩ hC hb hbν
    rcases Nat.eq_zero_or_pos j with hj | hj
    · -- the entry stage
      subst hj
      obtain ⟨⟨hA, hray⟩, hEH⟩ := hx
      have hEH' := hEH rfl
      obtain ⟨K, s⟩ := x
      have hA' : AdmIA D H ωstar E₀ (N.r 0) (N.r 0 - N.δ 0) (μ - m 0) ε s (m 1) (m 2) (m 3) (m 4)
          (m 5) (m 6) (m 7) K := hA
      have hray' : ν - m 8 ≤ rayMargin σω ωstar s := hray
      have hcond' : EntryCond (N.inp 0) E (ε / (γ ^ 4 * N.δ 0 ^ (2 * (2 * N.τ)))) := by
        have := hcond
        simp only [condL1, ↓reduceIte] at this
        exact this
      set p := N.inp 0 with hp
      have hpos : p.Pos := hN.pos 0
      have hk := Ent.nonneg hpos hE
      have hδ := hN.δ_pos 0
      obtain ⟨hc, b', cb, hcb, hbr, hca⟩ := hC.at hN 0
      set X := ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + 1)) with hX
      set E' := ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ)) with hE'
      have e1 : ∀ c : ℝ, c * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((1 : ℕ) : ℝ))) = c * X :=
        fun c => by rw [Nat.cast_one, mul_div_assoc]
      have e0 : ∀ c : ℝ, c * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((0 : ℕ) : ℝ))) = c * E' :=
        fun c => by rw [Nat.cast_zero, add_zero, mul_div_assoc]
      have hst : stageIL1 N E 0 = entryStageIA p E := by simp [stageIL1, hp]
      have c0 : m 0 + Ent.CDK p E * E' ≤ b := by
        have := hcap 0
        rwa [hst, show (entryStageIA p E).rate 0 = Ent.CDK p E by simp [entryStageIA],
          show ((jI 0 : ℕ) : ℝ) = ((0 : ℕ) : ℝ) from rfl,
          show deltaSeq 3 N.ρ N.ρinf 0 = N.δ 0 from rfl, e0] at this
      have c8 : m 8 + Ent.CDw p E * E' ≤ bν := by
        have := hcap 8
        rwa [hst, show (entryStageIA p E).rate 8 = Ent.CDw p E by simp [entryStageIA],
          show ((jI 8 : ℕ) : ℝ) = ((0 : ℕ) : ℝ) from rfl,
          show deltaSeq 3 N.ρ N.ρinf 0 = N.δ 0 from rfl, e0] at this
      have cj : ∀ (i : Fin 9) (c : ℝ), (entryStageIA p E).rate i = c → jI i = 1 →
          m i + c * X ≤ capI N b bν i := by
        intro i c hc1 hj
        have := hcap i
        rwa [hst, hc1, hj, show deltaSeq 3 N.ρ N.ρinf 0 = N.δ 0 from rfl, e1] at this
      have c1 : m 1 + Ent.dL p E * X ≤ N.sK := cj 1 _ (by simp [entryStageIA]) rfl
      have c2 : m 2 + Ent.rB p E * X ≤ N.sB := cj 2 _ (by simp [entryStageIA]) rfl
      have c3 : m 3 + Ent.rT p E * X ≤ N.sT := cj 3 _ (by simp [entryStageIA]) rfl
      have c4 : m 4 + Ent.dLt p E * X ≤ N.sLt := cj 4 _ (by simp [entryStageIA]) rfl
      have c5 : m 5 + Ent.rN p E * X ≤ N.sN := cj 5 _ (by simp [entryStageIA]) rfl
      have c6 : m 6 + Ent.rNt p E * X ≤ N.sNt := cj 6 _ (by simp [entryStageIA]) rfl
      have c7 : m 7 + Ent.CDT p E * X ≤ N.t := cj 7 _ (by simp [entryStageIA]) rfl
      have hβ : Ent.CDK p E * E' < μ - m 0 := by linarith
      have hDw0 : 0 ≤ Ent.CDw p E * E' :=
        mul_nonneg hk.CDw (div_nonneg hA'.ε_nonneg (by positivity))
      have hνd : Ent.CDw p E * E' < ν - m 8 := by linarith
      have hν' : 0 < ν - m 8 := by linarith
      have hω : ‖s • ωstar‖ ≤ p.Θ := by
        have := norm_smul_le_of_margin hA'.s_gt hν' hray'
        show ‖s • ωstar‖ ≤ N.Θ
        rw [hΘ]
        exact this
      have hδD : N.δ 0 ≤ p.δ := hN.δ_le_dS 0
      obtain ⟨hA'', -, hclose, hsd, hray''⟩ := iso_entry_step (p := p) (n := N.n) (ωstar := ωstar)
        hpos hE hiso rfl hS hd1 hd2 hd2H hdH hHY hγb (hΩ s hA'.s_gt.le) hA' hδ hδD
        (hN.lam_δ_lt 0) hω hc hcb hbr hca hEH'.toData hcond' hβ hray' hνd c1 c2 c3 c4 c5 c6 c7
      refine ⟨⟨⟨?_, ?_⟩, fun h1 => absurd h1 (Nat.succ_ne_zero 0)⟩, fun θ hθ => ?_, ?_⟩
      · show AdmIA D H ωstar E₀ (N.r (0 + 1)) (N.r (0 + 1) - N.δ (0 + 1))
          (μ - (m 0 + (stageIL1 N E 0).rate 0 * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((0 : ℕ) : ℝ)))))
          ((stageIL1 N E 0).CE * ε ^ 2 / (γ ^ 4 * N.δ 0 ^ (2 * (2 * N.τ))))
          (isoNewS H K ωstar E₀ s)
          (m 1 + (stageIL1 N E 0).rate 1 * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
          (m 2 + (stageIL1 N E 0).rate 2 * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
          (m 3 + (stageIL1 N E 0).rate 3 * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
          (m 4 + (stageIL1 N E 0).rate 4 * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
          (m 5 + (stageIL1 N E 0).rate 5 * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
          (m 6 + (stageIL1 N E 0).rate 6 * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
          (m 7 + (stageIL1 N E 0).rate 7 * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
          (isoNewtonMap H K ωstar E₀ s (N.r 0 - 2 * N.δ 0))
        rw [e0, e1, e1, e1, e1, e1, e1, e1, NumA.r_succ, NumA.δ_succ, hst]
        simp only [entryStageIA, Ent.CDK_eq, Ent.dL_eq, Ent.rB_eq, Ent.rT_eq, Ent.dLt_eq,
          Ent.rN_eq, Ent.rNt_eq, Ent.CDT_eq, Ent.CE_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val]
        rw [show μ - (m 0 + Ent.CDK p E * E') = μ - m 0 - Ent.CDK p E * E' by ring]
        exact hA''
      · show ν - (m 8 + (stageIL1 N E 0).rate 8 * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + ((0 : ℕ) : ℝ))))
          ≤ rayMargin σω ωstar (isoNewS H K ωstar E₀ s)
        rw [e0, hst, show (entryStageIA p E).rate 8 = Ent.CDw p E by simp [entryStageIA]]
        have h9 : ν - m 8 - Ent.CDw p E * E' ≤ rayMargin σω ωstar (isoNewS H K ωstar E₀ s) := hray''
        linarith
      · have hθ' : θ ∈ complexStrip N.n (N.r 0 - 3 * N.δ 0) := by
          rw [← NumA.r_succ]; exact hθ
        obtain ⟨h1, h2⟩ := hclose θ hθ'
        refine ⟨?_, ?_⟩
        · show ‖isoNewtonMap H K ωstar E₀ s (N.r 0 - 2 * N.δ 0) θ - K θ‖ ≤
            (stageIL1 N E 0).CD * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ))
          rw [hst, show (entryStageIA p E).CD = Ent.CDK p E by simp [entryStageIA],
            mul_div_assoc]
          exact h1
        · show ‖fderiv ℂ (isoNewtonMap H K ωstar E₀ s (N.r 0 - 2 * N.δ 0)) θ - fderiv ℂ K θ‖ ≤
            (N.n : ℝ) * (stageIL1 N E 0).CD * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ + 1))
          rw [hst, show (entryStageIA p E).CD = Ent.CDK p E by simp [entryStageIA],
            mul_div_assoc]
          exact h2
      · show |isoNewS H K ωstar E₀ s * ‖ωstar‖ - s * ‖ωstar‖| ≤
          (stageIL1 N E 0).Cp * ε / (γ ^ 2 * N.δ 0 ^ (2 * N.τ))
        rw [← sub_mul, abs_mul, abs_of_nonneg (norm_nonneg _), mul_div_assoc, hst,
          show (entryStageIA p E).Cp = Ent.CDw p E by simp [entryStageIA]]
        exact hsd
    · -- the later stages are B9's
      have hj0 : j ≠ 0 := hj.ne'
      have hst : stageIL1 N E j = stageI N j := by simp [stageIL1, hj0]
      have hcond' : (N.inp j).Cond (ε / (γ ^ 4 * deltaSeq 3 N.ρ N.ρinf j ^ (2 * (2 * N.τ)))) := by
        have := hcond
        simp only [condL1, hj0, ↓reduceIte] at this
        exact this
      have hcap' : ∀ i, m i + (stageI N j).rate i * ε /
          (γ ^ 2 * deltaSeq 3 N.ρ N.ρinf j ^ (2 * N.τ + (jI i : ℝ))) ≤ capI N b bν i := by
        intro i; have := hcap i; rwa [hst] at this
      obtain ⟨h1, h2, h3⟩ := hB9.step hx.1 hcond' hcap'
      rw [hst]
      exact ⟨⟨h1, fun h0 => absurd h0 (Nat.succ_ne_zero j)⟩, h2, h3⟩

end KAM.Iso.Sharp2.L1

end
