/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteBQ

/-!
# The rest of the rational mirror of route B: well-formedness, weights, caps and constants

* `NumBQ.wfOk`, `fitsOk`, `initOk`: the Boolean forms of `NumB.Wf`, `NumB.Fits`, `InitB.Wf`
  (`*_sound`);
* `NumBQ.capBQ`, `NumBQ.initBQ`: the caps and initial values of `capB`, `initB` (`cast_capB`,
  `cast_initB`);
* `NumBQ.c1Q`, `c2Q`, `c3Q`: the mirrors of `c1B`, `c2B`, `c3B` (`cast_c1B`, …).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Sharp2 KAM.Sharp2.RouteB

namespace NumBQ

variable (Q : NumBQ) (n : ℕ)

/-- `NumB.Wf` over `ℚ`. -/
def wfOk : Bool :=
  decide (2 ≤ n) && decide (1 ≤ Q.τ) && decide (0 < Q.ρinf) && decide (Q.ρinf < Q.ρ) &&
    decide (Q.ρ ≤ 1) &&
    decide (0 ≤ Q.M1 ∧ 0 ≤ Q.M2 ∧ 0 ≤ Q.cTh ∧ 0 ≤ Q.cDTh ∧ 0 ≤ Q.Θ ∧ 0 ≤ Q.y0 ∧ 0 ≤ Q.Mh2 ∧
      0 ≤ Q.ePer0) &&
    decide (0 < Q.sK ∧ 0 < Q.sLt ∧ 0 < Q.sB ∧ 0 < Q.sN ∧ 0 < Q.sNt ∧ 0 < Q.sT) &&
    decide (0 < Q.ts ∧ 0 < Q.bF) &&
    decide (0 < Q.θ ∧ Q.θ < 1 ∧ 0 < Q.θξ ∧ Q.θξ < 1 ∧ 0 < Q.θΩ ∧ Q.θΩ < 1 ∧ 0 < Q.q ∧ Q.q < 1 ∧
      0 < Q.θN ∧ Q.θN < 1 ∧ 0 < Q.θω ∧ Q.θω < 1) &&
    decide (1 < Q.a) && decide (0 < Q.ybar ∧ Q.ybar < 1) && decide (1 ≤ Q.kp) &&
    decide (0 < Q.lam0 ∧ Q.lam0 ≤ 1 ∧ 0 < Q.lamW0 ∧ Q.lamW0 ≤ 1) && decide (0 < Q.γb) &&
    Q.c.all (fun a => decide (0 < a)) && Q.c'.all (fun a => decide (0 < a)) &&
    Q.cbar.all (fun a => decide (0 < a)) && decide (0 < Q.ctail ∧ 0 < Q.cbtail)

/-- The stage-0 coefficient `p̄` of `NumB.Fits`, at the bound `iso`. -/
def pbar (iLt iNt b : ℚ) : ℚ := max (max iNt (iLt / (Q.γb * Q.δ0 ^ Q.τ))) b

/-- `NumB.Fits` over `ℚ`. -/
def fitsOk (iLt iNt : ℚ) : Bool :=
  decide (iNt / Q.pbar iLt iNt (if Q.iso then 1 else 0) ≤ Q.lam0) &&
    (!Q.iso || decide (1 / Q.pbar iLt iNt 1 ≤ Q.lamW0)) &&
    decide (1 / Q.pbar iLt iNt (if Q.iso then 1 else 0) ≤ Q.ePer0)

/-- `InitB.Wf` over `ℚ`. -/
def initOk (iLt iN iNt σT μ : ℚ) : Bool :=
  decide (0 < iLt ∧ 0 < iN ∧ 0 < iNt) && decide (iLt < Q.sLt ∧ iN < Q.sN ∧ iNt < Q.sNt) &&
    decide (0 < σT - μ ∧ σT - μ < Q.sT)

/-- The caps of `capB`. -/
def capBQ (σT μ ν : ℚ) : Fin 7 → ℚ :=
  ![Q.sK, Q.sLt, Q.sB, Q.sN, Q.sNt, (Q.sT - (σT - μ)) / (Q.sT * (σT - μ)) - 2 * Q.bF, ν / 2]

/-- The initial values of `initB`. -/
def initBQ (iLt iN iNt σK σB μ : ℚ) : Fin 7 → ℚ := ![σK - μ, iLt, σB - μ, iN, iNt, 0, 0]

/-- `pN`. -/
def pNQ (iNt : ℚ) : ℚ := if Q.iso then max iNt 1 else iNt

/-- `c1B`. -/
def c1Q (iLt iNt Xs : ℚ) : ℚ :=
  Q.ρ ^ (4 * Q.τ) * max (iLt * Q.γb ^ 2) (Q.pNQ iNt * Q.γb ^ 3 * Q.δ0 ^ Q.τ) /
    (Xs * Q.δ0 ^ (2 * Q.τ + 1))

/-- `c2B`. -/
def c2Q (iLt iNt Xs : ℚ) : ℚ :=
  Q.ρ ^ (2 * Q.τ) * max iLt (Q.pNQ iNt * Q.γb * Q.δ0 ^ Q.τ) * Q.ballSum n Xs /
    (Xs * Q.δ0 ^ (2 * Q.τ + 1))

/-- `c3B`. -/
def c3Q (iLt iNt Xs : ℚ) : ℚ :=
  Q.ρ ^ (2 * Q.τ) * max iLt (Q.pNQ iNt * Q.γb * Q.δ0 ^ Q.τ) * Q.freqSum n Xs /
    (Xs * Q.δ0 ^ (2 * Q.τ + 1))

/-! ### Soundness and casts -/

variable {Q n}

theorem getD_pos {l : List ℚ} {d : ℚ} (hl : l.all (fun a => decide (0 < a)) = true) (hd : 0 < d)
    (s : ℕ) : (0 : ℝ) < (l.getD s d : ℚ) := by
  have : 0 < l.getD s d := by
    rw [List.getD_eq_getElem?_getD]
    cases hh : l[s]? with
    | none => simpa using hd
    | some a =>
      simp only [List.all_eq_true, decide_eq_true_eq] at hl
      simpa using hl a (List.mem_of_getElem? hh)
  exact_mod_cast this

/-- **`wfOk` gives `NumB.Wf`.** -/
theorem wfOk_sound (h : Q.wfOk n = true) : (Q.toNum n).Wf := by
  simp only [wfOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩, h16⟩, h17⟩, h18⟩ := h
  exact
    { two_le := h1
      τ_ge := by show (1 : ℝ) ≤ (Q.τ : ℝ); exact_mod_cast h2
      ρinf_pos := by show (0 : ℝ) < Q.ρinf; exact_mod_cast h3
      ρinf_lt := by show (Q.ρinf : ℝ) < Q.ρ; exact_mod_cast h4
      ρ_le := by show (Q.ρ : ℝ) ≤ 1; exact_mod_cast h5
      nonneg := by simp only [toNum]; exact_mod_cast h6
      caps := by simp only [toNum]; exact_mod_cast h7
      budgets := by simp only [toNum]; exact_mod_cast h8
      ratios := by simp only [toNum]; exact_mod_cast h9
      a_gt := by show (1 : ℝ) < Q.a; exact_mod_cast h10
      ybar := by simp only [toNum]; exact_mod_cast h11
      kp_pos := h12
      lam := by simp only [toNum]; exact_mod_cast h13
      γb := by show (0 : ℝ) < Q.γb; exact_mod_cast h14
      sd := ⟨fun s => getD_pos h15 h18.1 s, fun s => getD_pos h16 h18.1 s,
        fun s => getD_pos h17 h18.2 s, by show (0 : ℝ) < Q.ctail; exact_mod_cast h18.1,
        by show (0 : ℝ) < Q.cbtail; exact_mod_cast h18.2⟩ }

theorem cast_δ0τ : (Q.toNum n).δ0 ^ (Q.toNum n).τ = ((Q.δ0 ^ Q.τ : ℚ) : ℝ) := by
  rw [cast_δ0, cast_τ, Real.rpow_natCast]; push_cast; rfl

theorem cast_pbar (iLt iNt b : ℚ) :
    max (max (iNt : ℝ) (iLt / ((Q.toNum n).γb * (Q.toNum n).δ0 ^ (Q.toNum n).τ))) (b : ℝ) =
      (Q.pbar iLt iNt b : ℝ) := by
  rw [cast_δ0τ]; simp only [pbar, toNum]; push_cast; rfl

/-- **`fitsOk` gives `NumB.Fits`.** -/
theorem fitsOk_sound {iLt iN iNt : ℚ} (h : Q.fitsOk iLt iNt = true) :
    (Q.toNum n).Fits ⟨iLt, iN, iNt⟩ := by
  simp only [fitsOk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true']
    at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have ei : ((if Q.iso then 1 else 0 : ℚ) : ℝ) = if (Q.toNum n).iso then 1 else 0 := by
    simp only [toNum]; push_cast [apply_ite (Rat.cast : ℚ → ℝ)]; rfl
  refine ⟨?_, fun hi => ?_, ?_⟩
  · show (iNt : ℝ) / max (max (iNt : ℝ) (iLt / ((Q.toNum n).γb * (Q.toNum n).δ0 ^
      (Q.toNum n).τ))) (if (Q.toNum n).iso then 1 else 0) ≤ (Q.lam0 : ℝ)
    rw [← ei, cast_pbar]; exact_mod_cast h1
  · rcases h2 with h2 | h2
    · exact absurd (hi.symm.trans h2) (by decide)
    · show (1 : ℝ) / max (max (iNt : ℝ) (iLt / ((Q.toNum n).γb * (Q.toNum n).δ0 ^
        (Q.toNum n).τ))) 1 ≤ (Q.lamW0 : ℝ)
      rw [← Rat.cast_one (α := ℝ), cast_pbar]; exact_mod_cast h2
  · show (1 : ℝ) / max (max (iNt : ℝ) (iLt / ((Q.toNum n).γb * (Q.toNum n).δ0 ^
      (Q.toNum n).τ))) (if (Q.toNum n).iso then 1 else 0) ≤ (Q.ePer0 : ℝ)
    rw [← ei, cast_pbar]; exact_mod_cast h3

/-- **`initOk` gives `InitB.Wf`.** -/
theorem initOk_sound {iLt iN iNt σT μ : ℚ} (h : Q.initOk iLt iN iNt σT μ = true) :
    (⟨iLt, iN, iNt⟩ : InitB).Wf (Q.toNum n) σT μ := by
  simp only [initOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨by show (0 : ℝ) < iLt ∧ (0 : ℝ) < iN ∧ (0 : ℝ) < iNt; exact_mod_cast h1,
    by simp only [toNum]; exact_mod_cast h2, ?_⟩
  simp only [toNum]
  exact_mod_cast h3

theorem cast_capB (σT μ ν : ℚ) :
    capB (Q.toNum n) σT μ ν = fun i => (Q.capBQ σT μ ν i : ℝ) := by
  funext i
  fin_cases i <;> simp [capB, capBQ, toNum]

theorem cast_initB (iLt iN iNt σK σB μ : ℚ) :
    initB ⟨iLt, iN, iNt⟩ σK σB μ = fun i => (initBQ iLt iN iNt σK σB μ i : ℝ) := by
  funext i
  fin_cases i <;> simp [initB, initBQ]

theorem cast_pN (iLt iN iNt : ℚ) : pN (Q.toNum n) ⟨iLt, iN, iNt⟩ = (Q.pNQ iNt : ℝ) := by
  simp only [pN, pNQ, toNum]; push_cast [apply_ite (Rat.cast : ℚ → ℝ)]; rfl

theorem cast_c1B (iLt iN iNt Xs : ℚ) :
    c1B (Q.toNum n) ⟨iLt, iN, iNt⟩ Xs = (Q.c1Q iLt iNt Xs : ℝ) := by
  have e4 : (4 * ((Q.τ : ℕ) : ℝ)) = ((4 * Q.τ : ℕ) : ℝ) := by push_cast; ring
  have e2 : (2 * ((Q.τ : ℕ) : ℝ) + 1) = ((2 * Q.τ + 1 : ℕ) : ℝ) := by push_cast; ring
  simp only [c1B, cast_pN, cast_δ0, cast_τ, e4, e2, Real.rpow_natCast, c1Q]
  simp only [toNum]; push_cast; rfl

theorem cast_c2B (iLt iN iNt Xs : ℚ) :
    c2B (Q.toNum n) ⟨iLt, iN, iNt⟩ Xs = (Q.c2Q n iLt iNt Xs : ℝ) := by
  have e2 : (2 * ((Q.τ : ℕ) : ℝ)) = ((2 * Q.τ : ℕ) : ℝ) := by push_cast; ring
  have e2' : (2 * ((Q.τ : ℕ) : ℝ) + 1) = ((2 * Q.τ + 1 : ℕ) : ℝ) := by push_cast; ring
  simp only [c2B, cast_pN, cast_δ0, cast_τ, cast_ballSum, c2Q]
  rw [e2', e2]
  simp only [toNum, Real.rpow_natCast]; push_cast; rfl

theorem cast_c3B (iLt iN iNt Xs : ℚ) :
    c3B (Q.toNum n) ⟨iLt, iN, iNt⟩ Xs = (Q.c3Q n iLt iNt Xs : ℝ) := by
  have e2 : (2 * ((Q.τ : ℕ) : ℝ)) = ((2 * Q.τ : ℕ) : ℝ) := by push_cast; ring
  have e2' : (2 * ((Q.τ : ℕ) : ℝ) + 1) = ((2 * Q.τ + 1 : ℕ) : ℝ) := by push_cast; ring
  simp only [c3B, cast_pN, cast_δ0, cast_τ, cast_freqSum, c3Q]
  rw [e2', e2]
  simp only [toNum, Real.rpow_natCast]; push_cast; rfl

end NumBQ

end KAM.CertificateSharp.V2

end
