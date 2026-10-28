/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.LimitMap
public import KAM.Planetary.TwoScale.RealDynamics

/-!
# Two-scale KAM: the limit data of the tori (`bpP:p3:tori`), shared interface

`ToriLimit` bundles the proved outputs of the P23-17/P23-18 helpers
(`limit_actions_of_steps`, `limit_phi_real_of_steps`, `limit_phi_strip_of_steps`) on one family of
witnesses `(Ds, hs, fs, Ψ, Φ, is)` of `iterative` with one limit action map `i` and one limit phase
map `Φinf`. It is a Prop of proved outputs only (design finding N2); `tori_limit_of_iterative`
discharges it on the witnesses of `iterative`. The packages `estimates`, `lagr`, `invariance` of
`Tori.lean` take it as their only limit hypothesis. Design package P23-20.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- The proved outputs of `limit_actions_of_steps` and `limit_phi_{real,strip}_of_steps` on the
shared witnesses, for the limit maps `i` and `Φinf` (`D_* = i '' D₀`). -/
structure ToriLimit {a b : ℕ} (sbar : ℝ) (p : ScaleData)
    (h : (Fin (a + b) → ℂ) → ℂ)
    (Ds : ℕ → Set (Fin (a + b) → ℝ)) (hs : ℕ → (Fin (a + b) → ℂ) → ℂ)
    (Φ : ℕ → CPhase (a + b) → CPhase (a + b))
    (is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ))
    (i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)) (Φinf : Phase (a + b) → Phase (a + b)) :
    Prop where
  i_conv : TendstoUniformlyOn (actionChain is) i atTop (Ds 0)
  i_mem : ∀ I ∈ Ds 0, ∀ j, actionChain is j I ∈ Ds j
  i_block : ∀ I ∈ Ds 0,
    ‖firstBlock (b := b) (i I - I)‖ ≤
      20 * (p.Mbar₁ / p.Mbar) * eHat (seq p 0) * rhoHat (seq p 0) ∧
    ‖lastBlock (a := a) (i I - I)‖ ≤
      20 * (p.Mbar₂ / p.Mbar) * eHat (seq p 0) * rhoHat (seq p 0) ∧
    ‖i I - I‖ ≤ 20 * eHat (seq p 0) * rhoHat (seq p 0)
  i_tail : ∀ I ∈ Ds 0, ∀ j, ‖i I - actionChain is j I‖ ≤ 20 * rhoHat (seq p j) * eHat (seq p j)
  i_tube : ∀ I ∈ Ds 0, ∀ j, i I ∈ realTube (Ds j) ((seq p j).ρ / 2)
  i_freq : ∀ I ∈ Ds 0, ∀ j, realFreq (hs j) (actionChain is j I) = realFreq h I
  phi_conv : TendstoUniformlyOn (fun j => psiR (Φ j)) Φinf atTop (univ ×ˢ (i '' Ds 0))
  phi_lip : ∀ x ∈ (univ ×ˢ (i '' Ds 0) : Set (Phase (a + b))),
    ∀ y ∈ (univ ×ˢ (i '' Ds 0) : Set (Phase (a + b))),
    limitmap_data (rhoHat p) p.s ((Φinf x - x) - (Φinf y - y)) ≤
      768 * ((a + b : ℕ) : ℝ) * eHat p * limitmap_data (rhoHat p) p.s (x - y)
  phi_block : ∀ x ∈ (univ ×ˢ (i '' Ds 0) : Set (Phase (a + b))),
    ‖firstBlock (b := b) ((Φinf x - x).2)‖ ≤ 3 / 2 * (p.Mhat / p.M) * eHat p * rhoHat p ∧
    ‖lastBlock (a := a) ((Φinf x - x).2)‖ ≤ 3 / 2 * eHat p * rhoHat p ∧
    2 * π * ‖(Φinf x - x).1‖ ≤ 3 / 2 * eHat p * p.s
  phi_per : ∀ x ∈ (univ ×ˢ (i '' Ds 0) : Set (Phase (a + b))), ∀ k : Fin (a + b) → ℤ,
    Φinf (x + KAM.ODE.angleShift k) = Φinf x + KAM.ODE.angleShift k
  phi_strip : ∀ I ∈ i '' Ds 0,
    (∀ c : Fin (a + b), ∃ G, StripLimit (a + b) (geometricWidth sbar)
      (3 / 2 * eHat p * p.s / (2 * π))
      (PsiSteps.stripSeq Φ ((ContinuousLinearMap.proj c).comp
        (ContinuousLinearMap.fst ℂ _ _)) I)
      (fun x => (((Φinf (x, I) - (x, I)).1 c : ℝ) : ℂ)) G) ∧
    (∀ i : Fin a, ∃ G, StripLimit (a + b) (geometricWidth sbar)
      (3 / 2 * (p.Mhat / p.M) * eHat p * rhoHat p)
      (PsiSteps.stripSeq Φ ((ContinuousLinearMap.proj (Fin.castAdd b i)).comp
        (ContinuousLinearMap.snd ℂ _ _)) I)
      (fun x => (((Φinf (x, I) - (x, I)).2 (Fin.castAdd b i) : ℝ) : ℂ)) G) ∧
    (∀ i : Fin b, ∃ G, StripLimit (a + b) (geometricWidth sbar)
      (3 / 2 * eHat p * rhoHat p)
      (PsiSteps.stripSeq Φ ((ContinuousLinearMap.proj (Fin.natAdd a i)).comp
        (ContinuousLinearMap.snd ℂ _ _)) I)
      (fun x => (((Φinf (x, I) - (x, I)).2 (Fin.natAdd a i) : ℝ) : ℂ)) G)

/-- Applicability: on the witnesses of one application of `iterative`, the helpers
`limit_actions_of_steps`, `limit_phi_real_of_steps` and `limit_phi_strip_of_steps` apply in
sequence and their outputs form a `ToriLimit` for one `(i, Φinf)`. -/
theorem tori_limit_of_iterative {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)} (H : KamHyp D sbar p h f) :
    ∃ (Ds : ℕ → Set (Fin (a + b) → ℝ)) (hs : ℕ → (Fin (a + b) → ℂ) → ℂ)
      (fs : ℕ → CHam (a + b)) (Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b))
      (is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ))
      (i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)) (Φinf : Phase (a + b) → Phase (a + b)),
      Ds 0 = dioBase D h p ∧ ActionSteps sbar p h Ds hs fs is ∧ PsiSteps sbar p Ds hs fs Ψ Φ ∧
      ToriLimit sbar p h Ds hs Φ is i Φinf := by
  obtain ⟨Ds, hs, fs, Ψ, Φ, is, h0, S, P⟩ := iterative_steps H
  obtain ⟨i, hconv, hmem, hblk, htail, hloc, -, -, -, -, hfreq⟩ := limit_actions_of_steps S
  have hD : ∀ j, i '' Ds 0 ⊆ realTube (Ds j) ((seq p j).ρ / 2) := by
    rintro j _ ⟨I, hI, rfl⟩
    exact hloc I hI j
  obtain ⟨Φinf, hU, hL, -, -, -, hper, hbk⟩ := P.limit_phi_real_of_steps hD
  exact ⟨Ds, hs, fs, Ψ, Φ, is, i, Φinf, h0, S, P,
    ⟨hconv, hmem, hblk, htail, hloc, hfreq, hU, hL, hbk, hper,
      fun I hI => P.limit_phi_strip_of_steps hD hU I hI⟩⟩

end KAM.Planetary

end
