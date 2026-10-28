/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.OscillatorFiniteGen
public import KAM.Planetary.Averaging.OscillatorHyp
public import KAM.Planetary.Averaging.OscillatorFiniteNumerics

/-!
# P Part 2: the loss budget of the oscillator finite averaging iteration, single-step case
(`stepP:p2:oa-first`, Case B)

`OscGood` packages a schedule, remainder bounds `ε` and a number of stages for which the oscillator
iteration is admissible (`OIter`) and the final domain, remainder, correction and displacement
bounds of `osc_averaging` hold. `oiter_of_hyp` builds `OIter` from `OscHyp`, and `oscGood_single` is
the single doubled-loss step, used when `e^{-κ/6} > 2 b y₀`.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, Revision 3, package P23-15.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- Reality of `h ∘ firstBlock ∘ snd` from reality of `h` on real actions. -/
theorem realOn_h_of_real {n m : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S : ℝ}
    {h : (Fin n → ℂ) → ℂ}
    (hreal : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd D r →
      (h (KAM.realInclusion n I)).im = 0) :
    RealOn (oscDom (m := m) D r rp rq S) (fun z => h (firstBlock (b := m) z.2)) := by
  intro x hx
  have hmem := (mem_oscDom_iff.1 hx).2.1
  have e : firstBlock (b := m) (KAM.realInclusion₂ (n + m) x).2 =
      KAM.realInclusion n (firstBlock (b := m) x.2) := by
    funext i; simp [firstBlock]
  rw [e] at hmem
  show (h (firstBlock (b := m) (KAM.realInclusion₂ (n + m) x).2)).im = 0
  rw [e]
  exact hreal _ hmem

/-- A schedule meeting the `osc_averaging` budget: admissible, with the final bounds. -/
def OscGood {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq sbar s K α E : ℝ)
    (h : (Fin n → ℂ) → ℂ) (f : CHam (n + m)) : Prop :=
  ∃ (c : OSched) (ε : ℕ → ℝ) (M : ℕ),
    OIter D c K α h f ε M ∧ c.x.r = r ∧ c.p.r = rp ∧ c.q.r = rq ∧ c.x.s = sbar + s ∧
    r / 2 ≤ c.x.R (M + 1) ∧ rp / 2 ≤ c.p.R (M + 1) ∧ rq / 2 ≤ c.q.R (M + 1) ∧
    sbar + s / 6 ≤ c.x.S (M + 1) ∧
    ε (M + 1) ≤ Real.exp (-(2 * π * K * s) / 6) * E ∧
    ∑ j ∈ Finset.range M, ε (j + 1) ≤
      400 * (1 + (m : ℝ)) * E ^ 2 / (2 * π * α * min (r * s) (rp * rq)) ∧
    (2 * π * α) * s * ∑ i ∈ Finset.range (M + 1),
      ε i / (Real.exp 1 * (2 * π * α) * c.x.σ i) ≤ 3 * E ∧
    (2 * π * α) * r * ∑ i ∈ Finset.range (M + 1), ε i / (2 * π * α * c.x.ρ i) ≤ 9 * E ∧
    (2 * π * α) * rq * ∑ i ∈ Finset.range (M + 1), ε i / (2 * π * α * c.q.ρ i) ≤ 9 * E ∧
    (2 * π * α) * rp * ∑ i ∈ Finset.range (M + 1), ε i / (2 * π * α * c.p.ρ i) ≤ 9 * E

section Common

variable {n m : ℕ} {D : Set (Fin n → ℝ)} {r rp rq sbar s K α E : ℝ} {h : (Fin n → ℂ) → ℂ}
  {f : CHam (n + m)}

theorem oiter_of_hyp (H : OscHyp D r rp rq sbar s K α E h f) (c : OSched) (hr : c.x.r = r)
    (hrp : c.p.r = rp) (hrq : c.q.r = rq) (hs : c.x.s = sbar + s) (ε : ℕ → ℝ) (hε0 : E ≤ ε 0)
    (M : ℕ)
    (hw : ∀ i ≤ M, 0 < c.x.ρ i ∧ 2 * c.x.ρ i < c.x.R i ∧ 0 < c.p.ρ i ∧ 2 * c.p.ρ i < c.p.R i ∧
      0 < c.q.ρ i ∧ 2 * c.q.ρ i < c.q.R i ∧ 0 < c.x.σ i ∧ 2 * c.x.σ i < c.x.S i)
    (hε : ∀ i ≤ M + 1, 0 ≤ ε i)
    (hsmall : ∀ i ≤ M, ε i ≤ (2 * π * α) * min (c.x.ρ i * c.x.σ i) (c.p.ρ i * c.q.ρ i) /
      (16 * (1 + (m : ℝ))))
    (hstep : ∀ i ≤ M,
      (1 - 2 * exp 1 * (1 + (m : ℝ)) * ε i /
          (2 * π * α * min (c.x.ρ i * c.x.σ i) (c.p.ρ i * c.q.ρ i)))⁻¹ *
        (2 * (1 + (m : ℝ)) / (2 * π * α * min (c.x.ρ i * c.x.σ i) (c.p.ρ i * c.q.ρ i)) *
          (∑ j : Fin i, max (max (c.x.ρ i / (c.x.R j - c.x.R i + c.x.ρ i))
              (c.x.σ i / (c.x.S j - c.x.S i + c.x.σ i)))
            (max (c.p.ρ i / (c.p.R j - c.p.R i + c.p.ρ i))
              (c.q.ρ i / (c.q.R j - c.q.R i + c.q.ρ i))) * ε j + ε i) +
          exp (-(2 * π * K * c.x.σ i))) * ε i ≤ ε (i + 1)) :
    OIter D c K α h f ε M := by
  obtain ⟨hr0, hrp0, hrq0, hs0, hK, hα⟩ := H.positive
  have hrr : KAM.actionNbhd D c.x.r = KAM.actionNbhd D r := by rw [hr]
  refine ⟨H.n_pos, H.m_pos, hK.le, hα, ?_, ?_, ?_, ?_, ?_, ?_, hw, hε, hsmall, hstep⟩
  · rw [hrr]; exact H.holo
  · rw [hrr]; exact H.divisor
  · rw [hr, hrp, hrq, hs]; exact realOn_h_of_real H.real_h
  · rw [hr, hrp, hrq, hs]; exact H.real_f
  · rw [hr, hrp, hrq, hs]; exact H.cls
  · rw [hr, hrp, hrq, hs]; exact H.bound.mono_gen le_rfl le_rfl le_rfl le_rfl hε0

/-- The smallness hypothesis in the form `4096 b E κ ≤ P`. -/
theorem osc_E_le (H : OscHyp D r rp rq sbar s K α E h f) :
    4096 * (1 + (m : ℝ)) * E * (2 * π * K * s) ≤ 2 * π * α * min (r * s) (rp * rq) := by
  have := mul_le_mul_of_nonneg_left H.small (by positivity : (0 : ℝ) ≤ 2 * π)
  linarith

end Common

end KAM.Planetary

end
