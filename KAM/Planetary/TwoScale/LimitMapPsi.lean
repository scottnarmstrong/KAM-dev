/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.LimitActions
public import KAM.Planetary.TwoScale.LimitMapScale

/-!
# Two-scale KAM: the symplectic stage maps `Ψ_k` (`bpP:p3:psi-lip`, domains and displacement)

The private conditional interface of the local obligation `psi_lip` (design package P23-18).
`PsiSteps` collects exactly the outputs of `iterative` (P23-16) about the stage maps `Ψ_{j+1}`,
`Φ_j = Ψ_1 ∘ ⋯ ∘ Ψ_j` and the domains `D_j`, on the shared witnesses; `iterative_psiSteps` shows
they are projections of the output of `iterative` (together with `ActionSteps`, on the same
witnesses). Here: the real restriction `psiR` of `Ψ_{j+1}` maps the real half-radius domain
`𝒟_{j+1} × ℝⁿ` into `𝒟_j × ℝⁿ` (`stepP:p3:pl-dom`) and the scaled displacement is
`(3/4) Ê_j 12^{-j}` (`stepP:p3:pl-disp`).
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- The real restriction `Re ∘ Ψ ∘ ι` of a stage map. -/
def psiR {n : ℕ} (Ψ : CPhase n → CPhase n) (x : Phase n) : Phase n :=
  KAM.realPartCLM₂ n (Ψ (KAM.realInclusion₂ n x))

/-- The real half-radius stage domain `𝒟 × ℝⁿ`, angles first. -/
def phaseTube {n : ℕ} (D : Set (Fin n → ℝ)) (r : ℝ) : Set (Phase n) := univ ×ˢ realTube D r

/-- The outputs of `iterative` concerning the stage maps `Ψ_{j+1}` and `Φ_j`, on the shared
witnesses. -/
structure PsiSteps {a b : ℕ} (sbar : ℝ) (p : ScaleData)
    (Ds : ℕ → Set (Fin (a + b) → ℝ)) (hs : ℕ → (Fin (a + b) → ℂ) → ℂ)
    (fs : ℕ → CHam (a + b)) (Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)) : Prop where
  hyp : ∀ j, KamHyp (Ds j) sbar (seq p j) (hs j) (fs j)
  Phi_zero : Φ 0 = id
  Phi_succ : ∀ j, Φ (j + 1) = Φ j ∘ Ψ (j + 1)
  phi_diff : ∀ j, DifferentiableOn ℂ (Φ j)
    (coefficientDom (Ds j) (seq p j).ρ (sbar + (seq p j).s))
  phi_real : ∀ j, ∀ x : Phase (a + b),
    KAM.realInclusion₂ (a + b) x ∈ coefficientDom (Ds j) (seq p j).ρ (sbar + (seq p j).s) →
    Φ j (KAM.realInclusion₂ (a + b) x) ∈ range (KAM.realInclusion₂ (a + b))
  phi_per : ∀ j, ∀ z ∈ coefficientDom (Ds j) (seq p j).ρ (sbar + (seq p j).s),
    ∀ k : Fin (a + b) → ℤ,
      Φ j (z + ((fun i => (k i : ℂ)), 0)) = Φ j z + ((fun i => (k i : ℂ)), 0)
  psi_diff : ∀ j, DifferentiableOn ℂ (Ψ (j + 1))
    (coefficientDom (Ds (j + 1)) (rhoHat (seq p j) / 16) (sbar + (seq p j).s / 12))
  psi_real : ∀ j, ∀ x : Phase (a + b),
    KAM.realInclusion₂ (a + b) x ∈
      coefficientDom (Ds (j + 1)) (rhoHat (seq p j) / 16) (sbar + (seq p j).s / 12) →
    Ψ (j + 1) (KAM.realInclusion₂ (a + b) x) ∈ range (KAM.realInclusion₂ (a + b))
  psi_per : ∀ j, ∀ z ∈ coefficientDom (Ds (j + 1)) (rhoHat (seq p j) / 16)
      (sbar + (seq p j).s / 12), ∀ k : Fin (a + b) → ℤ,
    Ψ (j + 1) (z + ((fun i => (k i : ℂ)), 0)) = Ψ (j + 1) z + ((fun i => (k i : ℂ)), 0)
  psi_bd : ∀ j, ∀ z ∈ coefficientDom (Ds (j + 1)) (rhoHat (seq p j) / 16)
      (sbar + (seq p j).s / 12),
    ‖firstBlock (b := b) ((Ψ (j + 1) z).2 - z.2)‖ ≤
      3 / 4 * (p.Mhat / p.M) * eHat (seq p j) * rhoHat (seq p j) ∧
    ‖lastBlock (a := a) ((Ψ (j + 1) z).2 - z.2)‖ ≤ 3 / 4 * eHat (seq p j) * rhoHat (seq p j) ∧
    2 * π * ‖(Ψ (j + 1) z).1 - z.1‖ ≤ 3 / 4 * eHat (seq p j) * (seq p j).s
  tube : ∀ j, Ds (j + 1) ⊆ realTube (Ds j) (rhoHat (seq p j) / 16)
  eHat_sq : ∀ j, eHat (seq p (j + 1)) < eHat (seq p j) ^ 2
  rho_lo : ∀ j, rhoHat (seq p j) / (2 * (24 : ℝ) ^ (p.τ + 1)) ≤ rhoHat (seq p (j + 1))
  rho_hi : ∀ j, rhoHat (seq p (j + 1)) ≤ rhoHat (seq p j) / 16

/-- Applicability check: `ActionSteps` and `PsiSteps` are projections of the output of
`iterative`, on the same witnesses `(Ds, hs, fs, is, Ψ, Φ)`. -/
theorem iterative_steps {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)} (H : KamHyp D sbar p h f) :
    ∃ (Ds : ℕ → Set (Fin (a + b) → ℝ)) (hs : ℕ → (Fin (a + b) → ℂ) → ℂ)
      (fs : ℕ → CHam (a + b)) (Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b))
      (is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)),
      Ds 0 = dioBase D h p ∧ ActionSteps sbar p h Ds hs fs is ∧ PsiSteps sbar p Ds hs fs Ψ Φ := by
  obtain ⟨Ds, hs, fs, Ψ, Φ, is, h0, h1, -, h3, h4, hK, hP, hI, hPh, ht, hΨ, hr⟩ := iterative H
  refine ⟨Ds, hs, fs, Ψ, Φ, is, h0, ⟨h1, hK, fun j => (hI j).2.1, fun j => (hI j).2.2.1,
    fun j => (hI j).2.2.2, fun j => (ht j).2.2, fun j => (hr j).1, fun j => (hr j).2.2.1⟩,
    ⟨hK, h3, hP, fun j => (hPh j).1, fun j => (hPh j).2.2.1, fun j => (hPh j).2.2.2.1,
      fun j => (hΨ j).1, fun j => (hΨ j).2.1, fun j => (hΨ j).2.2.1, fun j => (hΨ j).2.2.2.2.2,
      fun j => (ht j).1, fun j => (hr j).1, fun j => (hr j).2.1, fun j => (hr j).2.2.1⟩⟩

end KAM.Planetary

end
