/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.NormalFormCaseA
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The Normal Form Lemma (`bpN:p6:normal-form`, `bpN:p6:normal-form#data`, `bpN:p6:nonresonant-case`)

`nfSteps` (the number of steps `N = ⌊κ/(12 ln 2)⌋`), the Case B assembly (a single step with the
losses `(r/4, s/3)`), `normal_form` (Case A of `NormalFormCaseA` or Case B by the test
`exp(-κ/6) ≤ iterU α p ε (r/8) (s/6)`) and `nonresonant_case`. Design
`docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-8 (session 2).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.NormalForm

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

section CaseB

variable {D : Set (Fin n → ℂ)} {r s K α L p ε : ℝ} {Λ : Set (Fin n → ℤ)}
  {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- `bpN:p6:normal-form` in Case B: `iterU α p ε (r/8) (s/6) < exp(-κ/6)`; one step with the
losses `(r/4, s/3)`, `g = P_Λ T_K f`. -/
theorem nfConcl_caseB (H : NFHyp D r s K α L p ε Λ h f)
    (hB : iterU α p ε (r / 8) (s / 6) < Real.exp (-(2 * Real.pi * K * s) / 6)) :
    NFConcl D r s K α p ε Λ h f := by
  have hr := H.hr
  have hs := H.hs
  have hq := IterHyp.conjExp_pos H.hp
  have IH := nfCaseB_hyp H
  have hsub : Dom n D (r / 2) (s / 6) ⊆ Dom n D (r - 3 * (r / 4) / 2) (s - 3 * (s / 3) / 2) :=
    Dom_mono (by linarith) (by linarith)
  have hsub2 : Dom n D (r / 2) (s / 6) ⊆ Dom n D (r - 2 * (r / 4)) (s - 2 * (s / 3)) :=
    Dom_mono (by linarith) (by linarith)
  obtain ⟨a1, a2, a3, a4, a5, -⟩ := iterative_direct_a IH
  obtain ⟨c1, c2, c3, c4⟩ := iterative_direct_c IH
  have hg : ∀ z, iterG K Λ (fun _ => (0 : ℂ)) f z = homRes K Λ f z := fun z =>
    congrFun nfCaseB_g z
  refine ⟨iterMap D r s (r / 4) (s / 3) K Λ h f, homRes K Λ f,
    iterF D r s (r / 4) (s / 3) K Λ h (fun _ => (0 : ℂ)) f, a1.mono hsub, a5.mono hsub2,
    fun z hz => Dom_mono (by linarith) (by linarith) (a2 (hsub hz)),
    fun z hz => a3 z (hsub hz), fun k z hz => a4 k z (hsub hz),
    inClass_mono_nf c2 (by linarith) (by linarith),
    inClass_mono_nf c4 (by linarith) (by linarith), ?_, ?_, ?_, ?_,
    nfCaseB_bound H hB, ?_, ?_⟩
  · intro I hI k hk
    rw [coeff_homRes H.hs H.hf H.hfb I (polyNbhd_mono (by linarith) hI) k]
    exact Set.indicator_of_notMem hk _
  · intro z hz
    have e := c1 z (hsub2 hz)
    have e1 := hg z
    simp only [add_zero] at e
    rw [e1] at e
    simpa using e
  · have e : (fun z => homRes K Λ f z - homRes K Λ f z) =
        fun _ => (0 : ℂ) := by funext z; simp
    rw [e]
    exact wbound_zero_nf (by have := H.hα; have := H.hK; have := hq; positivity)
  · intro _ z _
    rfl
  · intro z hz
    obtain ⟨d1, d2⟩ := nfCaseB_disp H z hz
    exact ⟨d2, d1⟩
  · intro hΛ hhr hfr
    have hg0 : RealOn (Dom n D r s) (fun _ : (Fin n → ℂ) × (Fin n → ℂ) => (0 : ℂ)) :=
      fun x _ => by simp
    obtain ⟨-, e2, e3, e4⟩ := iterative_direct_e IH hΛ hhr hg0 hfr
    have e2' : RealOn (Dom n D r s) (homRes K Λ f) := fun x hx => by
      have := e2 x hx
      rwa [hg] at this
    exact ⟨realOn_mono' e2' (Dom_mono (by linarith) (by linarith)),
      realOn_mono' e3 hsub2, fun x hx => e4 x (hsub hx)⟩

end CaseB

section Main

variable {D : Set (Fin n → ℂ)} {r s K α p ε : ℝ} {Λ : Set (Fin n → ℤ)}
  {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- `bpN:p6:normal-form`. -/
theorem normal_form {D : Set (Fin n → ℂ)} {r s K α L p ε : ℝ} {Λ : Set (Fin n → ℤ)}
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hp : 1 < p) (hα : 0 < α)
    (hK : 0 < K) (hL : 0 ≤ L) (hr : 0 < r) (hs : 0 < s) (hh : DifferentiableOn ℂ h (polyNbhd D r))
    (hnr : IsNonresonant D K α Λ h) (hlip : FreqLipschitz D r L h) (hrad : K * L * r ≤ α / p)
    (hf : InClass D r s f) (hfb : WBound D r s f ε) (hε0 : 0 ≤ ε)
    (hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K)) (hii : 6 ≤ 2 * Real.pi * K * s) :
    ∃ (Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
      (g fs : (Fin n → ℂ) × (Fin n → ℂ) → ℂ),
      -- the map
      DifferentiableOn ℂ Ψ (Dom n D (r / 2) (s / 6)) ∧ InjOn Ψ (Dom n D (r / 2) (s / 6)) ∧
      MapsTo Ψ (Dom n D (r / 2) (s / 6)) (Dom n D r s) ∧
      (∀ z ∈ Dom n D (r / 2) (s / 6), ∀ v w,
        symplFormC (fderiv ℂ Ψ z v) (fderiv ℂ Ψ z w) = symplFormC v w) ∧
      (∀ k : Fin n → ℤ, ∀ z ∈ Dom n D (r / 2) (s / 6),
        Ψ (z.1 + (fun i => (k i : ℂ)), z.2) = Ψ z + ((fun i => (k i : ℂ)), 0)) ∧
      -- the normal form
      InClass D (r / 2) (s / 6) g ∧ InClass D (r / 2) (s / 6) fs ∧
      (∀ I ∈ polyNbhd D (r / 2), ∀ k, k ∉ Λ ∩ zBall n K → coeff g I k = 0) ∧
      (∀ z ∈ Dom n D (r / 2) (s / 6), (fun w => h w.2 + f w) (Ψ z) = h z.2 + g z + fs z) ∧
      -- (a)
      WBound D (r / 2) (s / 6) (fun z => g z - homRes K Λ f z)
        (16 * (2 * conjExp p * K / (α * r)) * ε ^ 2) ∧
      -- exact correction `g = g₀` in the zero-step case and in Case B
      ((nfSteps K s = 0 ∨
          iterU α p ε (r / 8) (s / 6) < Real.exp (-(2 * Real.pi * K * s) / 6)) →
        EqOn g (homRes K Λ f) (Dom n D (r / 2) (s / 6))) ∧
      -- (b)
      WBound D (r / 2) (s / 6) fs (Real.exp (-(2 * Real.pi * K * s) / 6) * ε) ∧
      -- (c)
      (∀ z ∈ Dom n D (r / 2) (s / 6), ‖(Ψ z).2 - z.2‖ ≤ conjExp p * K * ε / α ∧
        ‖(Ψ z).1 - z.1‖ ≤ 10 * conjExp p * ε / (2 * Real.pi * α * r)) ∧
      -- (d)
      ((∀ k ∈ Λ, -k ∈ Λ) → RealOn (Dom n D r s) (fun w => h w.2) → RealOn (Dom n D r s) f →
        RealOn (Dom n D (r / 2) (s / 6)) g ∧ RealOn (Dom n D (r / 2) (s / 6)) fs ∧
        ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Dom n D (r / 2) (s / 6) →
          Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n)) := by
  have H : NFHyp D r s K α L p ε Λ h f :=
    ⟨hp, hα, hK, hL, hr, hs, hh, hnr, hlip, hrad, hf, hfb, hε0, hi, hii⟩
  by_cases hA : Real.exp (-(2 * Real.pi * K * s) / 6) ≤ iterU α p ε (r / 8) (s / 6)
  · exact nfConcl_caseA H hA
  · exact nfConcl_caseB H (not_le.1 hA)

/-- `bpN:p6:nonresonant-case`: `Ψ = id`, `g = 0`, `f_* = f` for `κ < 6`, `|f_*| ≤ e·e^{-κ/6} ε`. -/
theorem nonresonant_case {D : Set (Fin n → ℂ)} {r s K ε : ℝ} {h : (Fin n → ℂ) → ℂ}
    {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hfb : WBound D r s f ε) (hκ : 2 * Real.pi * K * s < 6) :
    (∀ z, (fun w => h w.2 + f w) (id z) = h z.2 + 0 + f z) ∧
    WBound D r s f (Real.exp 1 * Real.exp (-(2 * Real.pi * K * s) / 6) * ε) := by
  refine ⟨fun z => by simp, fun I hI => ?_⟩
  obtain ⟨h1, h2⟩ := hfb I hI
  have hε : 0 ≤ ε := le_trans (tsum_nonneg fun k => by unfold modeWeight; positivity) h2
  have hge : 1 ≤ Real.exp 1 * Real.exp (-(2 * Real.pi * K * s) / 6) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  exact ⟨h1, h2.trans (le_mul_of_one_le_left hε hge)⟩

end Main

end KAM.NormalForm

end
