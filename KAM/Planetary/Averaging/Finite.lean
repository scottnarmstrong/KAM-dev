/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.FiniteCaseA

/-!
# P Part 2: averaging with a loss budget and two scales (`bpP:p2:nfb`, `bpP:p2:avg`)

`nfb` is the finite iteration of the N Iterative Lemma with the first-block splitting of `split`,
the loss schedule of the source (a single doubled-loss step when `y₀ < e^{-κ/6}`, otherwise the
first step with losses `(r/8, s/6)` and `N = ⌊κ/(12 ln 2)⌋` steps with losses `(r/(8N), s/(4N))`),
the telescope of N6-4 and the zero-mode normal form `∑ f̂ᵢ,₀`. `avg` is the Part 3 reading of
the same construction with geometric widths. The integer-translation law of the composition comes
from the N `iterative_direct_a` on the same flow. Design
`docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-12; modules `FiniteSchedule`, `FiniteStep`,
`FiniteChain`, `FiniteGen`, `FiniteNumerics`, `FiniteSetup`, `FiniteMulti`, `FiniteCaseA`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ}

/-- The conclusion of `nfb`, as a definition shared by the proof and the pointwise sup bound. -/
def NfbConcl {D : Set (Fin (a + b) → ℝ)} {r sbar s K α₁ α₂ E : ℝ} {f : CHam (a + b)}
    (h : (Fin (a + b) → ℂ) → ℂ) (Ψ : CPhase (a + b) → CPhase (a + b))
    (g : (Fin (a + b) → ℂ) → ℂ) (fs : CHam (a + b)) : Prop :=
  let V := Dom (a + b) (realBase D) (r / 2) (sbar + s / 6)
  DifferentiableOn ℂ Ψ V ∧ Set.InjOn Ψ V ∧
  MapsTo Ψ V (Dom (a + b) (realBase D) r (sbar + s)) ∧
  (∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v) ∧
  (∀ z ∈ V, ∀ k : Fin (a + b) → ℤ,
    Ψ (z + ((fun i => (k i : ℂ)), 0)) = Ψ z + ((fun i => (k i : ℂ)), 0)) ∧
  (∀ x : Phase (a + b), KAM.realInclusion₂ (a + b) x ∈ V →
    Ψ (KAM.realInclusion₂ (a + b) x) ∈ range (KAM.realInclusion₂ (a + b))) ∧
  DifferentiableOn ℂ g (KAM.actionNbhd D (r / 2)) ∧
  RealOn V (fun z => g z.2) ∧ RealOn V fs ∧
  (∀ z ∈ V, h (Ψ z).2 + f (Ψ z) = h z.2 + g z.2 + fs z) ∧
  WBound (realBase D) (r / 2) (sbar + s / 6) (fun z : CPhase (a + b) => g z.2 - coeff f z.2 0)
    (E / (2 * π * K * s)) ∧
  WBound (realBase D) (r / 2) (sbar + s / 6) (fun z : CPhase (a + b) => g z.2 - coeff f z.2 0)
    (E / 4) ∧
  InClass (realBase D) (r / 2) (sbar + s / 6) fs ∧
  WBound (realBase D) (r / 2) (sbar + s / 6) fs (exp (-(2 * π * K * s) / 6) * E) ∧
  ∀ z ∈ V,
    (2 * π * α₁) * s * ‖firstBlock (b := b) ((Ψ z).2 - z.2)‖ ≤ 3 * E ∧
    (2 * π * α₂) * s * ‖lastBlock (a := a) ((Ψ z).2 - z.2)‖ ≤ 3 * E ∧
    (2 * π * α₂) * r * ‖(Ψ z).1 - z.1‖ ≤ 9 * E

/-- A schedule for the hypotheses of `nfb` exists. -/
theorem goodSched_of_avg {D : Set (Fin (a + b) → ℝ)} {r sbar s K α₁ α₂ E : ℝ}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)} (H : AvgHyp D r sbar s K α₁ α₂ E h f) :
    GoodSched D r sbar s K α₁ α₂ E h f := by
  by_cases hcase : Real.exp (-(2 * π * K * s) / 6) ≤ E / (2 * π * α₂ * (r / 8) * (s / 6))
  · exact goodSched_multi H hcase
  · exact goodSched_single H (not_le.1 hcase)

/-- `nfb` together with the pointwise bound of `g - f̂₀`. -/
theorem nfb_core {D : Set (Fin (a + b) → ℝ)} {r sbar s K α₁ α₂ E : ℝ}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}
    (H : AvgHyp D r sbar s K α₁ α₂ E h f) :
    ∃ (Ψ : CPhase (a + b) → CPhase (a + b)) (g : (Fin (a + b) → ℂ) → ℂ) (fs : CHam (a + b)),
      NfbConcl (D := D) (r := r) (sbar := sbar) (s := s) (K := K) (α₁ := α₁) (α₂ := α₂) (E := E)
        (f := f) h Ψ g fs ∧
      ∀ I ∈ KAM.actionNbhd D (r / 2), ‖g I - coeff f I 0‖ ≤ E / (2 * π * K * s) := by
  obtain ⟨c, ε, m, hS, hr, hs, hR, hSS, hε, hsum, hd1, hd2, hd3⟩ := goodSched_of_avg H
  have hπ := Real.pi_pos
  have hK := H.K_pos
  have hs0 := H.s_pos
  have hE := H.E_nonneg
  have hbud := H.budget
  have hα₂ := H.α₂_pos
  have hr0 := H.r_pos
  have hsc : ∀ i ≤ m, StepConc (realBase D) c K α₁ α₂ h f ε i := fun i hi =>
    step_conc hS hi fun j hj => inv_all hS (m + 1) le_rfl j (by omega)
  have hVsub : Dom (a + b) (realBase D) (r / 2) (sbar + s / 6) ⊆
      Sched.U (realBase D) c (m + 1) := Dom_mono hR hSS
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := finite_struct hS hsc
  have hid := finite_ident hS hsc
  have hdisp := finite_disp hS hsc
  obtain ⟨t1, t2⟩ := gen_tail hS
  have hcls := (hsc m le_rfl).cls
  have hact : KAM.actionNbhd D (r / 2) = polyNbhd (realBase D) (r / 2) :=
    (conv_data D (r / 2) 0).1.symm
  have hkap : E / (2 * π * K * s) ≤ E / 4 := by
    refine div_le_div_of_nonneg_left hE (by norm_num) ?_
    linarith
  refine ⟨c.Ψ (realBase D) K h f m, c.gI (realBase D) K h f m, c.F (realBase D) K h f (m + 1),
    ?_, ?_⟩
  · show DifferentiableOn ℂ _ _ ∧ _
    refine ⟨s1.mono hVsub, s2.mono hVsub, ?_, fun z hz => s4 z (hVsub hz), fun z hz k =>
      s5 k z (hVsub hz), fun x hx => s6 x (hVsub hx), ?_, fun x hx => gI_real hS hsc x (hVsub hx),
      fun x hx => (hsc m le_rfl).real_F x (hVsub hx), fun z hz => ?_, ?_, ?_, ?_, ?_,
      fun z hz => ?_⟩
    · rw [hr, hs] at s3; exact s3.mono_left hVsub
    · rw [hact]
      exact (gI_differentiable hS).mono (polyNbhd_mono hR)
    · rw [hid z (hVsub hz), G_eq_gI hS z (hVsub hz)]
    · exact t2.mono hR hSS hsum
    · exact t2.mono hR hSS (hsum.trans hkap)
    · exact ⟨hcls.differentiableOn.mono (Dom_mono hR hSS),
        fun j z hz => hcls.periodic j z (Dom_mono hR hSS hz)⟩
    · exact (hsc m le_rfl).bound.mono hR hSS hε
    · obtain ⟨d1, d2, d3⟩ := hdisp z (hVsub hz)
      have hα₁ : 0 < α₁ := lt_of_lt_of_le H.α₂_pos H.α_order
      refine ⟨?_, ?_, ?_⟩
      · exact (mul_le_mul_of_nonneg_left d1 (by positivity)).trans hd1
      · exact (mul_le_mul_of_nonneg_left d2 (by positivity)).trans hd2
      · exact (mul_le_mul_of_nonneg_left d3 (by positivity)).trans hd3
  · intro I hI
    rw [hact] at hI
    have hI' : I ∈ polyNbhd (realBase D) (c.R (m + 1)) := polyNbhd_mono hR hI
    have hz : ((0 : Fin (a + b) → ℂ), I) ∈ Sched.U (realBase D) c (m + 1) :=
      ⟨fun i => by simpa using S_pos_succ hS, hI'⟩
    have := sup_le_wbound t1 t2 _ hz
    exact this.trans (hsum)

/-- Joint witnesses, all clauses of P2 nfb; no conclusion bundle becomes a premise. -/
theorem nfb {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {r sbar s K α₁ α₂ E : ℝ}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}
    (H : AvgHyp D r sbar s K α₁ α₂ E h f) :
    ∃ (Ψ : CPhase (a + b) → CPhase (a + b)) (g : (Fin (a + b) → ℂ) → ℂ) (fs : CHam (a + b)),
      let V := Dom (a + b) (realBase D) (r / 2) (sbar + s / 6)
      DifferentiableOn ℂ Ψ V ∧ Set.InjOn Ψ V ∧
      MapsTo Ψ V (Dom (a + b) (realBase D) r (sbar + s)) ∧
      (∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v) ∧
      (∀ z ∈ V, ∀ k : Fin (a + b) → ℤ,
        Ψ (z + ((fun i => (k i : ℂ)), 0)) = Ψ z + ((fun i => (k i : ℂ)), 0)) ∧
      (∀ x : Phase (a + b), KAM.realInclusion₂ (a + b) x ∈ V →
        Ψ (KAM.realInclusion₂ (a + b) x) ∈ range (KAM.realInclusion₂ (a + b))) ∧
      DifferentiableOn ℂ g (KAM.actionNbhd D (r / 2)) ∧
      RealOn V (fun z => g z.2) ∧ RealOn V fs ∧
      (∀ z ∈ V, h (Ψ z).2 + f (Ψ z) = h z.2 + g z.2 + fs z) ∧
      WBound (realBase D) (r / 2) (sbar + s / 6)
        (fun z : CPhase (a + b) => g z.2 - coeff f z.2 0) (E / (2 * π * K * s)) ∧
      WBound (realBase D) (r / 2) (sbar + s / 6)
        (fun z : CPhase (a + b) => g z.2 - coeff f z.2 0) (E / 4) ∧
      InClass (realBase D) (r / 2) (sbar + s / 6) fs ∧
      WBound (realBase D) (r / 2) (sbar + s / 6) fs (exp (-(2 * π * K * s) / 6) * E) ∧
      ∀ z ∈ V,
        (2 * π * α₁) * s * ‖firstBlock (b := b) ((Ψ z).2 - z.2)‖ ≤ 3 * E ∧
        (2 * π * α₂) * s * ‖lastBlock (a := a) ((Ψ z).2 - z.2)‖ ≤ 3 * E ∧
        (2 * π * α₂) * r * ‖(Ψ z).1 - z.1‖ ≤ 9 * E := by
  obtain ⟨Ψ, g, fs, h1, -⟩ := nfb_core H
  exact ⟨Ψ, g, fs, h1⟩

/-- P2 avg and P3 avg share one export; coefficient-radius conversion is explicit in input. -/
theorem avg {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {r sbar s K α₁ α₂ E : ℝ}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}
    (H : AvgHyp D r (geometricWidth sbar) (geometricWidth s) K α₁ α₂ E h f)
    (hstrict : 64 * exp 1 * K * E < α₂ * r) :
    ∃ (Ψ : CPhase (a + b) → CPhase (a + b)) (g : (Fin (a + b) → ℂ) → ℂ) (fs : CHam (a + b)),
      let V := coefficientDom D (r / 2) (sbar + s / 6)
      DifferentiableOn ℂ Ψ V ∧ Set.InjOn Ψ V ∧ MapsTo Ψ V (coefficientDom D r (sbar + s)) ∧
      (∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v) ∧
      (∀ z ∈ V, ∀ k : Fin (a + b) → ℤ,
        Ψ (z + ((fun i => (k i : ℂ)), 0)) = Ψ z + ((fun i => (k i : ℂ)), 0)) ∧
      (∀ x : Phase (a + b), KAM.realInclusion₂ (a + b) x ∈ V →
        Ψ (KAM.realInclusion₂ (a + b) x) ∈ range (KAM.realInclusion₂ (a + b))) ∧
      DifferentiableOn ℂ g (KAM.actionNbhd D (r / 2)) ∧ RealOn V (fun z => g z.2) ∧ RealOn V fs ∧
      (∀ z ∈ V, h (Ψ z).2 + f (Ψ z) = h z.2 + g z.2 + fs z) ∧
      (∀ I ∈ KAM.actionNbhd D (r / 2),
        ‖g I - coeff f I 0‖ ≤ E / 4 ∧ ‖g I - coeff f I 0‖ ≤ E / (K * s)) ∧
      InClass (realBase D) (r / 2) (geometricWidth (sbar + s / 6)) fs ∧
      WBound (realBase D) (r / 2) (geometricWidth (sbar + s / 6)) fs (exp (-K * s / 6) * E) ∧
      ∀ z ∈ V, α₁ * s * ‖firstBlock (b := b) ((Ψ z).2 - z.2)‖ ≤ 3 * E ∧
        α₂ * s * ‖lastBlock (a := a) ((Ψ z).2 - z.2)‖ ≤ 3 * E ∧
        2 * π * α₂ * r * ‖(Ψ z).1 - z.1‖ ≤ 9 * E := by
  obtain ⟨Ψ, g, fs, h1, hpt⟩ := nfb_core H
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, -, -, c13, c14, c15⟩ := h1
  have hπ := Real.pi_pos
  have hK := H.K_pos
  have hs : 0 < s := by
    have := H.s_pos
    unfold geometricWidth at this
    have h2 : 0 < 2 * π := by positivity
    exact (div_pos_iff_of_pos_right h2).1 this
  have hw : geometricWidth sbar + geometricWidth s / 6 = geometricWidth (sbar + s / 6) := by
    unfold geometricWidth; ring
  have hw2 : geometricWidth sbar + geometricWidth s = geometricWidth (sbar + s) := by
    unfold geometricWidth; ring
  have hk : 2 * π * K * geometricWidth s = K * s := by
    unfold geometricWidth; field_simp
  have hVeq : coefficientDom D (r / 2) (sbar + s / 6) =
      Dom (a + b) (realBase D) (r / 2) (geometricWidth sbar + geometricWidth s / 6) := by
    unfold coefficientDom; rw [hw]
  have hVeq2 : coefficientDom D r (sbar + s) =
      Dom (a + b) (realBase D) r (geometricWidth sbar + geometricWidth s) := by
    unfold coefficientDom; rw [hw2]
  refine ⟨Ψ, g, fs, ?_⟩
  intro V
  have hV : V = Dom (a + b) (realBase D) (r / 2) (geometricWidth sbar + geometricWidth s / 6) :=
    hVeq
  rw [hV, hVeq2]
  have hbud := H.budget
  rw [hk] at hbud hpt
  refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, fun I hI => ?_, ?_, ?_, fun z hz => ?_⟩
  · have := hpt I hI
    refine ⟨this.trans ?_, this⟩
    refine div_le_div_of_nonneg_left H.E_nonneg (by norm_num) ?_
    linarith
  · rw [← hw]; exact c13
  · rw [← hw, show -K * s / 6 = -(K * s) / 6 by ring]
    rw [hk] at c14
    exact c14
  · obtain ⟨d1, d2, d3⟩ := c15 z hz
    have e1 : (2 * π * α₁) * geometricWidth s = α₁ * s := by
      unfold geometricWidth; field_simp
    have e2 : (2 * π * α₂) * geometricWidth s = α₂ * s := by
      unfold geometricWidth; field_simp
    rw [e1] at d1
    rw [e2] at d2
    exact ⟨d1, d2, d3⟩

end KAM.Planetary

end
