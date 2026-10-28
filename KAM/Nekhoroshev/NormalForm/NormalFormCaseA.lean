/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.NormalFormAux
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The Normal Form Lemma: the assembly in Case A

The number of steps `nfSteps K s = ⌊κ/(12 ln 2)⌋`, the conclusion `NFConcl` of
`bpN:p6:normal-form` (the statement of `normal_form` after its hypotheses) and its proof in Case A
(`exp(-κ/6) ≤ iterU …`, any `N ≥ 0`): `Ψ = Φ₀ ∘ ⋯ ∘ Φ_N`, `g = g_N`, `f_* = f_{N+1}`. Design
`docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-8 (session 2).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.NormalForm

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

/-- `bpN:p6:normal-form#data`: the number of steps `N = ⌊κ/(12 ln 2)⌋`, `κ = 2πKs`. -/
def nfSteps (K s : ℝ) : ℕ := ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊

/-- The conclusion of `bpN:p6:normal-form`. -/
def NFConcl (D : Set (Fin n → ℂ)) (r s K α p ε : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : Prop :=
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
          Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n))

section CaseA

variable {D : Set (Fin n → ℂ)} {r s K α L p ε : ℝ} {Λ : Set (Fin n → ℤ)}
  {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- The seminorm `‖z.1‖` on `ℂⁿ × ℂⁿ`. -/
def fstSeminorm : Seminorm ℂ ((Fin n → ℂ) × (Fin n → ℂ)) :=
  (normSeminorm ℂ (Fin n → ℂ)).comp (LinearMap.fst ℂ _ _)

/-- The seminorm `‖z.2‖` on `ℂⁿ × ℂⁿ`. -/
def sndSeminorm : Seminorm ℂ ((Fin n → ℂ) × (Fin n → ℂ)) :=
  (normSeminorm ℂ (Fin n → ℂ)).comp (LinearMap.snd ℂ _ _)

theorem fstSeminorm_apply (z : (Fin n → ℂ) × (Fin n → ℂ)) : fstSeminorm z = ‖z.1‖ := rfl

theorem sndSeminorm_apply (z : (Fin n → ℂ) × (Fin n → ℂ)) : sndSeminorm z = ‖z.2‖ := rfl

/-- `bpN:p6:normal-form` in Case A: `exp(-κ/6) ≤ iterU α p ε (r/8) (s/6)`. -/
theorem nfConcl_caseA (H : NFHyp D r s K α L p ε Λ h f)
    (hA : Real.exp (-(2 * Real.pi * K * s) / 6) ≤ iterU α p ε (r / 8) (s / 6)) :
    NFConcl D r s K α p ε Λ h f := by
  set N := nfSteps K s with hNdef
  have hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊ := rfl
  have hr := H.hr
  have hs := H.hs
  have hinv := nf_inv_all H hN hA
  have hU : ∀ i ≤ N, Dom n D (nfR r N (i + 1)) (nfS s N (i + 1)) ⊆
      Dom n D (nfR r N i) (nfS s N i) := fun i _ =>
    Dom_mono (nfR_anti hr.le N (Nat.le_succ i)) (nfS_anti hs.le N (Nat.le_succ i))
  have props := fun i (hi : i ≤ N) => nf_step_props H hN hi (hinv i (by omega))
  have hmap : ∀ i ≤ N, MapsTo (nfPhi D r s K Λ h f N i)
      (Dom n D (nfR r N (i + 1)) (nfS s N (i + 1))) (Dom n D (nfR r N i) (nfS s N i)) :=
    fun i hi => (props i hi).2.1
  have hsub : Dom n D (r / 2) (s / 6) ⊆ Dom n D (nfR r N (N + 1)) (nfS s N (N + 1)) :=
    Dom_mono (nfR_half_le hr N) (nfS_sixth_le hs N)
  obtain ⟨t1, t2, t3, t4⟩ := telescope (U := fun i => Dom n D (nfR r N i) (nfS s N i)) hU hmap
  obtain ⟨hdiff, hsymp⟩ := t3 (fun i _ => isOpen_Dom D _ _) (fun i hi => (props i hi).1)
    (fun i hi => (props i hi).2.2.1)
  have hfin := nf_final_f H hN (hinv (N + 1) le_rfl)
  have hdisp := nf_disp_sums H hN
  have hI := t2 sndSeminorm
    (fun i => conjExp p * nfB (nfEps1 α p r s ε) ε i /
      (Real.exp 1 * (2 * Real.pi * α) * nfSig s N i))
    (fun i hi z hz => (props i hi).2.2.2.2.2.1 z hz |>.2)
  have hθ := t2 fstSeminorm
    (fun i => conjExp p * nfB (nfEps1 α p r s ε) ε i / (2 * Real.pi * α * nfRho r N i))
    (fun i hi z hz => (props i hi).2.2.2.2.2.1 z hz |>.1)
  refine ⟨chain (nfPhi D r s K Λ h f N) N, nfG D r s K Λ h f N (N + 1),
    nfF D r s K Λ h f N (N + 1), hdiff.mono hsub,
    (t4 (fun i hi => (props i hi).2.2.2.2.1)).mono hsub,
    fun z hz => t1 (hsub hz), fun z hz => hsymp z (hsub hz), ?_,
    nf_final_g H (hinv (N + 1) le_rfl), hfin.1, nf_coeff_g H hinv, ?_,
    nf_final_g_diff H hN (hinv (N + 1) le_rfl), ?_, hfin.2, ?_, ?_⟩
  · intro k z hz
    exact chain_translate (U := fun i => Dom n D (nfR r N i) (nfS s N i)) hmap
      (fun i hi k z hz => (props i hi).2.2.2.1 k z hz) k z (hsub hz)
  · intro z hz
    exact nf_chain_identity H hN (fun i hi => hinv i (by omega)) N le_rfl z (hsub hz)
  · rintro (h0 | hB)
    · intro z _
      exact congrFun (nf_final_g_zero (D := D) (r := r) (s := s) (h := h) (f := f) h0) z
    · exact absurd hB (not_lt.2 hA)
  · intro z hz
    exact ⟨((sndSeminorm_apply _) ▸ hI z (hsub hz)).trans hdisp.1,
      ((fstSeminorm_apply _) ▸ hθ z (hsub hz)).trans hdisp.2⟩
  · intro hΛ hhr hfr
    have hreal := nf_real H hN (fun i hi => hinv i (by omega)) hΛ hhr hfr
    refine ⟨realOn_mono' (hreal (N + 1) le_rfl).1 hsub, realOn_mono' (hreal (N + 1) le_rfl).2 hsub,
      fun x hx => ?_⟩
    refine chain_real (U := fun i => Dom n D (nfR r N i) (nfS s N i)) hmap
      (fun i hi x hx => ?_) x (hsub hx)
    exact nf_phi_real H hN hi (hinv i (by omega)) hΛ
      (realOn_mono' hhr (Dom_mono (nfR_anti hr.le N (Nat.zero_le i))
        (nfS_anti hs.le N (Nat.zero_le i)))) (hreal i (by omega)).1 (hreal i (by omega)).2 x hx

end CaseA

end KAM.NormalForm

end
