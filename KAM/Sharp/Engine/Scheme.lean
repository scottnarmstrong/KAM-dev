/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.Engine.Decay
public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Frozen.Defs.IsPrimaryOnStrip
public import KAM.Frozen.Defs.IsRealOnReals
public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The abstract Newton scheme and its induction

Blueprint `bp:p2s:scheme` and `bp:p2s:engine-iteration`.

`Scheme` is the data of an abstract Newton scheme, `Consts` its constants and `Scheme.IsNewton` the
hypotheses (N1), (N2). `Scheme.iterate` is the induction (i)–(iv) of Proposition
`bp:p2s:engine-iteration` under the arithmetic hypotheses (I1)–(I4). The engine is abstract: it
mentions no Hamiltonian.
-/

@[expose] public noncomputable section

namespace KAM.Sharp.Engine

/-- An abstract Newton scheme (`bp:p2s:scheme`): states `α`, the torus `tor x`, a scalar parameter
`par x`, the admissibility predicate `Adm r β ε m x` (strip `T_r`, ball margin `β`, error `ε`,
current bounds `m`) and the step `step r δ x` (strip `T_r`, loss `δ`). -/
structure Scheme (n k : ℕ) (α : Type*) where
  tor : α → (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)
  par : α → ℝ
  Adm : ℝ → ℝ → ℝ → (Fin k → ℝ) → α → Prop
  step : ℝ → ℝ → α → α

/-- The constants of a scheme: loss factor `λ`, exponent `a`, `C_E`, `C_Δ`, `C_p`, `𝔠_step`,
caps `σ`, rates `ϱ` and exponents `j` of the bounds. -/
structure Consts (k : ℕ) where
  lam : ℝ
  a : ℝ
  CE : ℝ
  CD : ℝ
  Cp : ℝ
  cstep : ℝ
  cap : Fin k → ℝ
  rate : Fin k → ℝ
  j : Fin k → ℕ

variable {n k : ℕ} {α : Type*}

/-- Hypotheses (N1), (N2) of `bp:p2s:scheme` at the Diophantine constant `γ`. Not a hypothesis of a
source theorem: each instance proves it (`KAM.Sharp.fixedScheme_isNewton`,
`KAM.Iso.Sharp.isoScheme_isNewton`). -/
structure Scheme.IsNewton (S : Scheme n k α) (c : Consts k) (γ : ℝ) : Prop where
  lam_pos : 0 < c.lam
  two_le_a : 2 ≤ c.a
  CE_nonneg : 0 ≤ c.CE
  CD_nonneg : 0 ≤ c.CD
  Cp_nonneg : 0 ≤ c.Cp
  rate_nonneg : ∀ i, 0 ≤ c.rate i
  j_le_one : ∀ i, c.j i ≤ 1
  adm : ∀ {r β ε : ℝ} {m : Fin k → ℝ} {x : α}, S.Adm r β ε m x →
    0 ≤ ε ∧ DifferentiableOn ℂ (S.tor x) (complexStrip n r) ∧ IsPrimaryOnStrip (S.tor x) r ∧
      IsRealOnReals (S.tor x)
  step : ∀ {r β ε δ : ℝ} {m : Fin k → ℝ} {x : α}, S.Adm r β ε m x → 0 < δ → δ ≤ 1 →
    c.lam * δ < r → c.cstep * ε / (γ ^ 4 * δ ^ (2 * c.a)) ≤ 1 →
    2 * (c.CD * ε / (γ ^ 2 * δ ^ c.a)) ≤ β →
    (∀ i, m i + c.rate i * ε / (γ ^ 2 * δ ^ (c.a + c.j i)) ≤ c.cap i) →
    S.Adm (r - c.lam * δ) (β - c.CD * ε / (γ ^ 2 * δ ^ c.a))
        (c.CE * ε ^ 2 / (γ ^ 4 * δ ^ (2 * c.a)))
        (fun i => m i + c.rate i * ε / (γ ^ 2 * δ ^ (c.a + c.j i))) (S.step r δ x) ∧
      (∀ θ ∈ complexStrip n (r - c.lam * δ),
        ‖S.tor (S.step r δ x) θ - S.tor x θ‖ ≤ c.CD * ε / (γ ^ 2 * δ ^ c.a) ∧
        ‖fderiv ℂ (S.tor (S.step r δ x)) θ - fderiv ℂ (S.tor x) θ‖ ≤
          n * (c.CD * ε / (γ ^ 2 * δ ^ c.a)) / δ) ∧
      |S.par (S.step r δ x) - S.par x| ≤ c.Cp * ε / (γ ^ 2 * δ ^ c.a)

/-- The iterates `x_{s+1} = Φ(r_s, δ_s; x_s)`. -/
def Scheme.iter (S : Scheme n k α) (lam ρ ρinf : ℝ) (x₀ : α) : ℕ → α
  | 0 => x₀
  | s + 1 => S.step (rSeq lam ρ ρinf s) (deltaSeq lam ρ ρinf s) (S.iter lam ρ ρinf x₀ s)

/-- `ε_s` of the scheme. -/
def Consts.eps (c : Consts k) (ρ ρinf γ e : ℝ) (s : ℕ) : ℝ := epsSeq c.CE c.a c.lam ρ ρinf γ e s

/-- `d_s = C_Δ ε_s/(γ² δ_s^a)`. -/
def Consts.d (c : Consts k) (ρ ρinf γ e : ℝ) (s : ℕ) : ℝ :=
  c.CD * c.eps ρ ρinf γ e s / (γ ^ 2 * deltaSeq c.lam ρ ρinf s ^ c.a)

/-- `D_s = ∑_{t<s} d_t`. -/
def Consts.sumD (c : Consts k) (ρ ρinf γ e : ℝ) (s : ℕ) : ℝ :=
  ∑ t ∈ Finset.range s, c.d ρ ρinf γ e t

/-- `m^{(s)}_i = m^{(0)}_i + ∑_{t<s} ϱ_i ε_t/(γ² δ_t^{a+j_i})`. -/
def Consts.mSeq (c : Consts k) (m₀ : Fin k → ℝ) (ρ ρinf γ e : ℝ) (s : ℕ) : Fin k → ℝ :=
  fun i => m₀ i + ∑ t ∈ Finset.range s,
    c.rate i * c.eps ρ ρinf γ e t / (γ ^ 2 * deltaSeq c.lam ρ ρinf t ^ (c.a + c.j i))

section Sums

variable {CE a lam ρ ρinf γ e : ℝ}

/-- The terms `c ε_s/(γ² δ_s^i)` are nonnegative and summable, with sum at most
`2 c e/(γ² δ₀^i)`, for `0 ≤ i ≤ 2a - 1`. -/
theorem term_sum (hCE : 0 ≤ CE) (hlam : 0 < lam) (hρ : ρinf < ρ) (hγ : 0 < γ) (he : 0 ≤ e)
    (hq : (2 : ℝ) ^ (2 * a) * CE * e / (γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a)) ≤ 1) {c i : ℝ}
    (hc : 0 ≤ c) (hi : 0 ≤ i) (hi2 : i ≤ 2 * a - 1) :
    (∀ s, 0 ≤ c * epsSeq CE a lam ρ ρinf γ e s / (γ ^ 2 * deltaSeq lam ρ ρinf s ^ i)) ∧
      Summable (fun s => c * epsSeq CE a lam ρ ρinf γ e s /
        (γ ^ 2 * deltaSeq lam ρ ρinf s ^ i)) ∧
      ∑' s, c * epsSeq CE a lam ρ ρinf γ e s / (γ ^ 2 * deltaSeq lam ρ ρinf s ^ i) ≤
        2 * c * e / (γ ^ 2 * delta0 lam ρ ρinf ^ i) := by
  obtain ⟨hs, ht⟩ := epsSeq_sum hCE hlam hρ hγ he hq hi hi2
  have hfun : (fun s => c * epsSeq CE a lam ρ ρinf γ e s / (γ ^ 2 * deltaSeq lam ρ ρinf s ^ i)) =
      fun s => c / γ ^ 2 * (epsSeq CE a lam ρ ρinf γ e s / deltaSeq lam ρ ρinf s ^ i) :=
    funext fun s => by ring
  have hd0 := delta0_pos hlam hρ
  have hDi : 0 < delta0 lam ρ ρinf ^ i := Real.rpow_pos_of_pos hd0 _
  have hX : 0 ≤ c / γ ^ 2 := by positivity
  refine ⟨fun s => ?_, ?_⟩
  · have := epsSeq_nonneg hCE hlam hρ he (a := a) (γ := γ) s
    have := Real.rpow_pos_of_pos (deltaSeq_pos hlam hρ s) i
    positivity
  rw [hfun]
  refine ⟨hs.mul_left _, ?_⟩
  rw [tsum_mul_left]
  calc c / γ ^ 2 * ∑' s, epsSeq CE a lam ρ ρinf γ e s / deltaSeq lam ρ ρinf s ^ i
      ≤ c / γ ^ 2 * (2 * e / delta0 lam ρ ρinf ^ i) := mul_le_mul_of_nonneg_left ht hX
    _ = 2 * c * e / (γ ^ 2 * delta0 lam ρ ρinf ^ i) := by field_simp

end Sums

section Iterate

variable {S : Scheme n k α} {c : Consts k} {γ : ℝ} {ρ ρinf β₀ e : ℝ} {m₀ : Fin k → ℝ} {x₀ : α}

/-- The partial sums `D_s`, `m^{(s)}` stay below their limits. -/
theorem Scheme.IsNewton.sums_le (hS : S.IsNewton c γ) (hρ : ρinf < ρ) (hγ : 0 < γ) (he : 0 ≤ e)
    (hE : (2 : ℝ) ^ (2 * c.a) * c.CE * e / (γ ^ 4 * delta0 c.lam ρ ρinf ^ (2 * c.a)) ≤ 1) :
    (∀ s, c.sumD ρ ρinf γ e s ≤ 2 * c.CD * e / (γ ^ 2 * delta0 c.lam ρ ρinf ^ c.a)) ∧
    (∀ s, 0 ≤ c.d ρ ρinf γ e s) ∧
    ∀ s i, c.mSeq m₀ ρ ρinf γ e s i ≤
      m₀ i + 2 * c.rate i * e / (γ ^ 2 * delta0 c.lam ρ ρinf ^ (c.a + c.j i)) := by
  have ha := hS.two_le_a
  refine ⟨fun s => ?_, fun s => ?_, fun s i => ?_⟩
  · obtain ⟨hn, hsm, ht⟩ := term_sum hS.CE_nonneg hS.lam_pos hρ hγ he hE hS.CD_nonneg
      (i := c.a) (by linarith) (by linarith)
    exact (Summable.sum_le_tsum _ (fun t _ => hn t) hsm).trans ht
  · exact (term_sum hS.CE_nonneg hS.lam_pos hρ hγ he hE hS.CD_nonneg
      (i := c.a) (by linarith) (by linarith)).1 s
  · have hj : (c.j i : ℝ) ≤ 1 := by exact_mod_cast hS.j_le_one i
    obtain ⟨hn, hsm, ht⟩ := term_sum hS.CE_nonneg hS.lam_pos hρ hγ he hE (hS.rate_nonneg i)
      (i := c.a + c.j i) (by positivity) (by linarith)
    exact add_le_add_right ((Summable.sum_le_tsum _ (fun t _ => hn t) hsm).trans ht) _

/-- Blueprint `bp:p2s:engine-iteration`. -/
theorem Scheme.iterate (hS : S.IsNewton c γ)
    (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hγ : 0 < γ)
    (h0 : S.Adm ρ β₀ e m₀ x₀)
    (hE : (2 : ℝ) ^ (2 * c.a) * c.CE * e / (γ ^ 4 * delta0 c.lam ρ ρinf ^ (2 * c.a)) ≤ 1)
    (hst : c.cstep * e / (γ ^ 4 * delta0 c.lam ρ ρinf ^ (2 * c.a)) ≤ 1)
    (hball : 2 * c.CD * e / (γ ^ 2 * delta0 c.lam ρ ρinf ^ c.a) ≤ β₀ / 4)
    (hcap : ∀ i, m₀ i + 2 * c.rate i * e / (γ ^ 2 * delta0 c.lam ρ ρinf ^ (c.a + c.j i)) ≤
      c.cap i) :
    ∀ s : ℕ,
      S.Adm (rSeq c.lam ρ ρinf s) (β₀ - c.sumD ρ ρinf γ e s) (c.eps ρ ρinf γ e s)
          (c.mSeq m₀ ρ ρinf γ e s) (S.iter c.lam ρ ρinf x₀ s) ∧
        c.sumD ρ ρinf γ e s ≤ 2 * c.CD * e / (γ ^ 2 * delta0 c.lam ρ ρinf ^ c.a) ∧
        (∀ i, c.mSeq m₀ ρ ρinf γ e s i ≤ c.cap i) ∧
        (∀ θ ∈ complexStrip n (rSeq c.lam ρ ρinf (s + 1)),
          ‖S.tor (S.iter c.lam ρ ρinf x₀ (s + 1)) θ - S.tor (S.iter c.lam ρ ρinf x₀ s) θ‖ ≤
            c.d ρ ρinf γ e s ∧
          ‖fderiv ℂ (S.tor (S.iter c.lam ρ ρinf x₀ (s + 1))) θ -
              fderiv ℂ (S.tor (S.iter c.lam ρ ρinf x₀ s)) θ‖ ≤
            n * c.d ρ ρinf γ e s / deltaSeq c.lam ρ ρinf s) ∧
        |S.par (S.iter c.lam ρ ρinf x₀ (s + 1)) - S.par (S.iter c.lam ρ ρinf x₀ s)| ≤
          c.Cp * c.eps ρ ρinf γ e s / (γ ^ 2 * deltaSeq c.lam ρ ρinf s ^ c.a) ∧
        c.eps ρ ρinf γ e s ≤ (2 : ℝ) ^ (-(2 * c.a * s)) * e := by
  have hlam := hS.lam_pos
  have ha := hS.two_le_a
  have he : 0 ≤ e := (hS.adm h0).1
  have hd0 := delta0_pos hlam hρ
  have hsch := schedule hlam hρinf hρ
  obtain ⟨hsumD, hdnn, hmS⟩ := hS.sums_le (m₀ := m₀) hρ hγ he hE
  have hdec := error_decay hS.CE_nonneg ha hlam hρinf hρ hγ he hE
  have hβ0 : 0 ≤ β₀ := by
    have : 0 ≤ 2 * c.CD * e / (γ ^ 2 * delta0 c.lam ρ ρinf ^ c.a) := by
      have := Real.rpow_pos_of_pos hd0 c.a
      have := hS.CD_nonneg
      positivity
    linarith
  have hsucc : ∀ s, c.sumD ρ ρinf γ e (s + 1) = c.sumD ρ ρinf γ e s + c.d ρ ρinf γ e s :=
    fun s => Finset.sum_range_succ _ _
  have hmsucc : ∀ s, c.mSeq m₀ ρ ρinf γ e (s + 1) = fun i => c.mSeq m₀ ρ ρinf γ e s i +
      c.rate i * c.eps ρ ρinf γ e s / (γ ^ 2 * deltaSeq c.lam ρ ρinf s ^ (c.a + c.j i)) :=
    fun s => by
      funext i
      simp only [Consts.mSeq, Finset.sum_range_succ]
      ring
  have hstS : ∀ s, c.cstep * c.eps ρ ρinf γ e s /
      (γ ^ 4 * deltaSeq c.lam ρ ρinf s ^ (2 * c.a)) ≤ 1 := by
    intro s
    have hw := hdec.2.1 (2 * c.a) s (by linarith) le_rfl
    have hDa : 0 < delta0 c.lam ρ ρinf ^ (2 * c.a) := Real.rpow_pos_of_pos hd0 _
    have hδa : 0 < deltaSeq c.lam ρ ρinf s ^ (2 * c.a) :=
      Real.rpow_pos_of_pos (deltaSeq_pos hlam hρ s) _
    rcases le_total 0 c.cstep with hc | hc
    · calc c.cstep * c.eps ρ ρinf γ e s / (γ ^ 4 * deltaSeq c.lam ρ ρinf s ^ (2 * c.a))
          = c.cstep / γ ^ 4 * (c.eps ρ ρinf γ e s / deltaSeq c.lam ρ ρinf s ^ (2 * c.a)) := by
            field_simp
        _ ≤ c.cstep / γ ^ 4 * (e / delta0 c.lam ρ ρinf ^ (2 * c.a)) :=
            mul_le_mul_of_nonneg_left hw (by positivity)
        _ = c.cstep * e / (γ ^ 4 * delta0 c.lam ρ ρinf ^ (2 * c.a)) := by field_simp
        _ ≤ 1 := hst
    · have : 0 ≤ c.eps ρ ρinf γ e s := (hdec.1 s).1
      have : c.cstep * c.eps ρ ρinf γ e s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc this
      exact (div_nonpos_of_nonpos_of_nonneg this (by positivity)).trans zero_le_one
  have hβS : ∀ s, 2 * (c.CD * c.eps ρ ρinf γ e s /
      (γ ^ 2 * deltaSeq c.lam ρ ρinf s ^ c.a)) ≤ β₀ - c.sumD ρ ρinf γ e s := by
    intro s
    have h1 := hsumD s
    have h2 := hsumD (s + 1)
    rw [hsucc] at h2
    have := hdnn s
    have hD0 : 0 ≤ c.sumD ρ ρinf γ e s := Finset.sum_nonneg fun t _ => hdnn t
    have hd : c.d ρ ρinf γ e s = c.CD * c.eps ρ ρinf γ e s /
      (γ ^ 2 * deltaSeq c.lam ρ ρinf s ^ c.a) := rfl
    rw [← hd]
    linarith
  have hcapS : ∀ s i, c.mSeq m₀ ρ ρinf γ e s i +
      c.rate i * c.eps ρ ρinf γ e s / (γ ^ 2 * deltaSeq c.lam ρ ρinf s ^ (c.a + c.j i)) ≤
        c.cap i := by
    intro s i
    have := hmS (s + 1) i
    rw [hmsucc] at this
    exact this.trans (hcap i)
  have hN : ∀ s, S.Adm (rSeq c.lam ρ ρinf s) (β₀ - c.sumD ρ ρinf γ e s) (c.eps ρ ρinf γ e s)
      (c.mSeq m₀ ρ ρinf γ e s) (S.iter c.lam ρ ρinf x₀ s) →
      S.Adm (rSeq c.lam ρ ρinf (s + 1)) (β₀ - c.sumD ρ ρinf γ e (s + 1))
        (c.eps ρ ρinf γ e (s + 1)) (c.mSeq m₀ ρ ρinf γ e (s + 1))
        (S.iter c.lam ρ ρinf x₀ (s + 1)) ∧
      (∀ θ ∈ complexStrip n (rSeq c.lam ρ ρinf (s + 1)),
        ‖S.tor (S.iter c.lam ρ ρinf x₀ (s + 1)) θ - S.tor (S.iter c.lam ρ ρinf x₀ s) θ‖ ≤
          c.d ρ ρinf γ e s ∧
        ‖fderiv ℂ (S.tor (S.iter c.lam ρ ρinf x₀ (s + 1))) θ -
            fderiv ℂ (S.tor (S.iter c.lam ρ ρinf x₀ s)) θ‖ ≤
          n * c.d ρ ρinf γ e s / deltaSeq c.lam ρ ρinf s) ∧
      |S.par (S.iter c.lam ρ ρinf x₀ (s + 1)) - S.par (S.iter c.lam ρ ρinf x₀ s)| ≤
        c.Cp * c.eps ρ ρinf γ e s / (γ ^ 2 * deltaSeq c.lam ρ ρinf s ^ c.a) := by
    intro s hs
    obtain ⟨hA, hdiff, hpar⟩ := hS.step hs (hsch.2.2.2.2.2.1 s).1 (hsch.2.2.2.2.2.1 s).2
      (hsch.2.2.2.2.2.2 s) (hstS s) (hβS s) (hcapS s)
    have e1 := hsch.2.2.2.1 s
    have e2 : β₀ - c.sumD ρ ρinf γ e (s + 1) =
        β₀ - c.sumD ρ ρinf γ e s - c.CD * c.eps ρ ρinf γ e s /
          (γ ^ 2 * deltaSeq c.lam ρ ρinf s ^ c.a) := by
      rw [hsucc]; unfold Consts.d; ring
    refine ⟨?_, ?_, hpar⟩
    · rw [e1, e2, hmsucc]; exact hA
    · rw [e1]; exact hdiff
  have key : ∀ s, S.Adm (rSeq c.lam ρ ρinf s) (β₀ - c.sumD ρ ρinf γ e s) (c.eps ρ ρinf γ e s)
      (c.mSeq m₀ ρ ρinf γ e s) (S.iter c.lam ρ ρinf x₀ s) := by
    intro s
    induction s with
    | zero =>
      have hm : c.mSeq m₀ ρ ρinf γ e 0 = m₀ := by funext i; simp [Consts.mSeq]
      have hD : c.sumD ρ ρinf γ e 0 = 0 := by simp [Consts.sumD]
      rw [rSeq_zero, hm, hD, sub_zero]
      exact h0
    | succ s ih => exact (hN s ih).1
  intro s
  have hs := key s
  obtain ⟨-, hdiff, hpar⟩ := hN s hs
  refine ⟨hs, hsumD s, fun i => (hmS s i).trans (hcap i), hdiff, ?_, (hdec.1 s).2⟩
  have := hpar
  exact this

end Iterate

end KAM.Sharp.Engine

end
