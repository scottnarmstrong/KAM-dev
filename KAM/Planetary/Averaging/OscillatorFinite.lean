/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.OscillatorFiniteCaseA

/-!
# P Parts 2-3: averaging with oscillators, one scale (`bpP:p2:osc-averaging`,
`bpP:p2:averaged-remainder`)

`osc_averaging` is the finite iteration of the complete oscillator step `osc_iter` with the loss
schedule of the source (a single doubled-loss step when `e^{-κ/6} > 2 b y₀`, otherwise the first
step with losses `(r/8, rp/8, rq/8, s/6)` and `N = ⌊κ/(12 ln 2)⌋` steps with losses
`(r/(8N), rp/(8N), rq/(8N), s/(4N))`), the telescope of N6-4 and the zero-mode normal form
`∑ f̂ᵢ,₀`; the average correction `g - f̂₀` and the exponentially small tail `fs` stay separate.
`averaged_remainder` is the specialization `E = μ`, `f = μ • P`, `s = s₀`. The modules
`OscillatorFiniteSched`, `OscillatorFiniteStep`, `OscillatorFiniteChain`, `OscillatorFiniteGen`,
`OscillatorFiniteNumerics`, `OscillatorFiniteSetup`, `OscillatorFiniteSingle`,
`OscillatorFiniteMulti`, `OscillatorFiniteCaseA` hold the proof.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, Revision 3, package P23-15.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

section Core

variable {n m : ℕ} {D : Set (Fin n → ℝ)} {r rp rq sbar s K α E : ℝ} {h : (Fin n → ℂ) → ℂ}
  {f : CHam (n + m)}

/-- A schedule meeting the budget exists. -/
theorem oscGood_of_hyp (H : OscHyp D r rp rq sbar s K α E h f) :
    OscGood D r rp rq sbar s K α E h f := by
  by_cases hA : Real.exp (-(2 * π * K * s) / 6) ≤ 2 * ((1 + (m : ℝ)) * E /
      (2 * π * α * min (r / 8 * (s / 6)) (rp / 8 * (rq / 8))))
  · exact oscGood_multi H hA
  · exact oscGood_single H (not_le.1 hA)

/-- The zero mode of `f` is a real function of the class on the final domain. -/
theorem osc_zero_mode (H : OscHyp D r rp rq sbar s K α E h f) :
    oscClass D (r / 2) (rp / 2) (rq / 2) (sbar + s / 6)
      (fun z => coeff (oscFunction f) (oscPack z).2 0) ∧
    RealOn (oscDom (m := m) D (r / 2) (rp / 2) (rq / 2) (sbar + s / 6))
      (fun z => coeff (oscFunction f) (oscPack z).2 0) := by
  obtain ⟨c, ε, M, hS, hx, hp, hq, hs, hR, hRp, hRq, hS', -⟩ := oscGood_of_hyp H
  have hVsub : oscDom (m := m) D (r / 2) (rp / 2) (rq / 2) (sbar + s / 6) ⊆ c.U D (M + 1) :=
    oscDom_mono hR hRp hRq hS'
  have hsc := hS.stage (i := 0) (Nat.zero_le M)
  obtain ⟨a, b, d, e⟩ := hS.R_anti (i := 1) (j := M + 1) (by omega) le_rfl
  refine ⟨?_, ?_⟩
  · have h0 : oscClass D (c.x.R 0) (c.p.R 0) (c.q.R 0) (c.x.S 0) (c.inc D K h f 0) := hsc.inc_cls
    have hx0 : c.x.R 0 = r := hx
    have hp0 : c.p.R 0 = rp := hp
    have hq0 : c.q.R 0 = rq := hq
    have hs0 : c.x.S 0 = sbar + s := hs
    rw [hx0, hp0, hq0, hs0] at h0
    refine h0.mono ?_ ?_ ?_ ?_ <;> linarith [H.positive.1, H.positive.2.1,
      H.positive.2.2.1, H.sbar_nonneg, H.positive.2.2.2.1]
  · intro x hx'
    have := hsc.real_G x (oscDom_mono a b d e (hVsub hx'))
    simpa [OSched.G_succ, OSched.G_zero, OSched.inc, OSched.F_zero] using this

end Core

theorem osc_averaging {n m : ℕ} {D : Set (Fin n → ℝ)} {r rp rq sbar s K α E : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : CHam (n + m)} (H : OscHyp D r rp rq sbar s K α E h f) :
    ∃ (Ψ : CPhase (n + m) → CPhase (n + m)) (g fs : CHam (n + m)),
      let V := oscDom D (r / 2) (rp / 2) (rq / 2) (sbar + s / 6)
      DifferentiableOn ℂ Ψ V ∧ Set.InjOn Ψ V ∧ MapsTo Ψ V (oscDom D r rp rq (sbar + s)) ∧
      (∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v) ∧
      (∀ z ∈ V, ∀ k : Fin n → ℤ,
        Ψ (z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) = Ψ z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) ∧
      (∀ x : Phase (n + m), KAM.realInclusion₂ (n + m) x ∈ V →
        Ψ (KAM.realInclusion₂ (n + m) x) ∈ range (KAM.realInclusion₂ (n + m))) ∧
      oscClass D (r / 2) (rp / 2) (rq / 2) (sbar + s / 6) g ∧ RealOn V g ∧
      (∀ x ∈ oscParams (m := m) D (r / 2) (rp / 2) (rq / 2),
        ∀ θ θ', oscUnpack (θ, x) ∈ V → oscUnpack (θ', x) ∈ V → g (oscUnpack (θ, x)) = g (oscUnpack (θ', x))) ∧
      (∀ z ∈ V, h (firstBlock (b := m) (Ψ z).2) + f (Ψ z) = h (firstBlock (b := m) z.2) + g z + fs z) ∧
      oscBound D (r / 2) (rp / 2) (rq / 2) (sbar + s / 6)
        (fun z => g z - coeff (oscFunction f) (oscPack z).2 0)
        (400 * (1 + (m : ℝ)) * E ^ 2 / (2 * π * α * min (r * s) (rp * rq))) ∧
      oscClass D (r / 2) (rp / 2) (rq / 2) (sbar + s / 6) fs ∧ RealOn V fs ∧
      oscBound D (r / 2) (rp / 2) (rq / 2) (sbar + s / 6) fs (exp (-(2 * π * K * s) / 6) * E) ∧
      ∀ z ∈ V,
        2 * π * α * s * ‖firstBlock (b := m) ((Ψ z).2 - z.2)‖ ≤ 3 * E ∧
        2 * π * α * r * ‖firstBlock (b := m) ((Ψ z).1 - z.1)‖ ≤ 9 * E ∧
        2 * π * α * rq * ‖lastBlock (a := n) ((Ψ z).2 - z.2)‖ ≤ 9 * E ∧
        2 * π * α * rp * ‖lastBlock (a := n) ((Ψ z).1 - z.1)‖ ≤ 9 * E := by
  obtain ⟨c, ε, M, hS, hx, hp, hq, hs, hR, hRp, hRq, hS', hεf, hsum, hσ, hρ, hρq, hρp⟩ :=
    oscGood_of_hyp H
  obtain ⟨hr0, hrp0, hrq0, hs0, hK0, hα0⟩ := H.positive
  have hVsub : oscDom (m := m) D (r / 2) (rp / 2) (rq / 2) (sbar + s / 6) ⊆ c.U D (M + 1) :=
    oscDom_mono hR hRp hRq hS'
  have hinv := (oinv_all hS (M + 1) le_rfl).1
  have hstruct := hS.struct
  have hdisp := hS.disp
  have hα2 : 0 ≤ 2 * π * α := by positivity
  refine ⟨c.Ψ D K h f M, c.G D K h f (M + 1), c.F D K h f (M + 1), ?_⟩
  intro V
  refine ⟨hstruct.1.mono hVsub, hstruct.2.1.mono hVsub, ?_,
    fun z hz => hstruct.2.2.2.1 z (hVsub hz),
    fun z hz k => hstruct.2.2.2.2.1 k z (hVsub hz),
    fun x hx' => hstruct.2.2.2.2.2 x (hVsub hx'), ?_,
    fun x hx' => hinv.2.2.2.2 x (hVsub hx'), ?_, fun z hz => hS.ident z (hVsub hz), ?_,
    hinv.1.mono hR hRp hRq hS', fun x hx' => hinv.2.2.1 x (hVsub hx'), ?_, ?_⟩
  · have := hstruct.2.2.1.mono_left hVsub
    rw [hx, hp, hq, hs] at this
    exact this
  · exact hinv.2.2.2.1.mono hR hRp hRq hS'
  · intro x _ θ θ' _ _
    refine OSched.G_indep c D K h f (M + 1) ?_
    rw [oscPack_oscUnpack, oscPack_oscUnpack]
  · obtain ⟨-, t2⟩ := hS.gen_tail
    exact t2.mono_gen hR hRp hRq hS' hsum
  · exact hinv.2.1.mono_gen hR hRp hRq hS' hεf
  · intro z hz
    obtain ⟨d1, d2, d3, d4⟩ := hdisp z (hVsub hz)
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (mul_le_mul_of_nonneg_left d2 (by positivity)).trans hσ
    · exact (mul_le_mul_of_nonneg_left d1 (by positivity)).trans hρ
    · exact (mul_le_mul_of_nonneg_left d4 (by positivity)).trans hρq
    · exact (mul_le_mul_of_nonneg_left d3 (by positivity)).trans hρp

end KAM.Planetary

end
