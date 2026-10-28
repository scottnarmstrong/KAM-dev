/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.LimitMapReal
public import KAM.Planetary.TwoScale.FourierCompact

/-!
# Two-scale KAM: complex angle extension of the limit map (`stepP:p3:lp-an`)

For `I ∈ D_*`, each real coordinate of `θ ↦ Φ(θ, I) − (θ, I)` extends holomorphically to the whole
strip `|Im θ| < s̄/2π`, periodic, with the uniform bound of the finite-stage maps, and the
finite-stage coordinate functions converge to it with all derivatives
(`fourier_compact`, applied coordinatewise). Design package P23-18.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {sbar : ℝ} {p : ScaleData}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)}

/-- The conclusion of `fourier_compact`: `G` is the holomorphic periodic extension of `f` to the
strip of width `w`, bounded by `B`, and `F j → G` with all derivatives on closed substrips. -/
def StripLimit (n : ℕ) (w B : ℝ) (F : ℕ → (Fin n → ℂ) → ℂ) (f : (Fin n → ℝ) → ℂ)
    (G : (Fin n → ℂ) → ℂ) : Prop :=
  DifferentiableOn ℂ G (KAM.complexStrip n w) ∧
  (∀ x, G (KAM.realInclusion n x) = f x) ∧
  (∀ z ∈ KAM.complexStrip n w, ‖G z‖ ≤ B) ∧
  (∀ θ ∈ KAM.complexStrip n w, ∀ k : Fin n → ℤ, G (θ + fun i => (k i : ℂ)) = G θ) ∧
  ∀ v : ℝ, 0 < v → v < w → ∀ m : ℕ,
    TendstoUniformlyOn (fun j => iteratedFDeriv ℂ m (F j)) (iteratedFDeriv ℂ m G)
      atTop {z | ∀ i, |(z i).im| ≤ v}

namespace PsiSteps

/-- The finite-stage coordinate function `θ ↦ π (Φ_j(θ, I) − (θ, I))`. -/
def stripSeq (Φ : ℕ → CPhase (a + b) → CPhase (a + b)) (πC : CPhase (a + b) →L[ℂ] ℂ)
    (I : Fin (a + b) → ℝ) (j : ℕ) (θ : Fin (a + b) → ℂ) : ℂ :=
  πC (Φ j (θ, KAM.realInclusion (a + b) I) - (θ, KAM.realInclusion (a + b) I))

theorem strip_comp (P : PsiSteps sbar p Ds hs fs Ψ Φ)
    {Dstar : Set (Fin (a + b) → ℝ)} (hD : ∀ j, Dstar ⊆ realTube (Ds j) ((seq p j).ρ / 2))
    {Φinf : Phase (a + b) → Phase (a + b)}
    (hU : TendstoUniformlyOn (fun j => psiR (Φ j)) Φinf atTop (univ ×ˢ Dstar))
    (πC : CPhase (a + b) →L[ℂ] ℂ) (πR : Phase (a + b) →L[ℝ] ℝ)
    (hπ : ∀ v, πC (KAM.realInclusion₂ (a + b) v) = ((πR v : ℝ) : ℂ))
    {B : ℝ} (hB : 0 ≤ B) {I : Fin (a + b) → ℝ} (hI : I ∈ Dstar)
    (hbd : ∀ j, ∀ θ ∈ KAM.complexStrip (a + b) (geometricWidth sbar),
      ‖stripSeq Φ πC I j θ‖ ≤ B) :
    ∃ G, StripLimit (a + b) (geometricWidth sbar) B (stripSeq Φ πC I)
      (fun x => ((πR (Φinf (x, I) - (x, I)) : ℝ) : ℂ)) G := by
  have hs0 : 0 < sbar := by
    have := (P.hyp 0).widths.1; have := (P.hyp 0).positive.2.1; linarith
  have hw : 0 < geometricWidth sbar := by unfold geometricWidth; positivity
  have hmem : ∀ j, ∀ θ ∈ KAM.complexStrip (a + b) (geometricWidth sbar),
      (θ, KAM.realInclusion (a + b) I) ∈
        coefficientDom (Ds j) (seq p j).ρ (sbar + (seq p j).s) := by
    intro j θ hθ
    rw [(conv_data _ _ _).2]
    have hsj : 0 < (seq p j).s := (P.hyp j).positive.2.1
    refine ⟨fun i => (hθ i).trans_le ?_, ?_⟩
    · unfold geometricWidth; gcongr; linarith
    · have := realTube_mono (D := Ds j) (by have := P.rho_stage_pos j; linarith :
        (seq p j).ρ / 2 ≤ (seq p j).ρ) (hD j hI)
      exact this
  have hshift : ∀ θ : Fin (a + b) → ℂ, ∀ k : Fin (a + b) → ℤ,
      (θ + (fun i => (k i : ℂ)), KAM.realInclusion (a + b) I) =
        (θ, KAM.realInclusion (a + b) I) + ((fun i => (k i : ℂ)), 0) := by
    intro θ k; ext i <;> simp
  refine fourier_compact (F := stripSeq Φ πC I) hw hB ?_ ?_ hbd ?_
  · intro j
    unfold stripSeq
    have h1 : DifferentiableOn ℂ (fun θ : Fin (a + b) → ℂ => (θ, KAM.realInclusion (a + b) I))
        (KAM.complexStrip (a + b) (geometricWidth sbar)) :=
      (differentiable_id.prodMk (differentiable_const _)).differentiableOn
    have h2 := ((P.phi_diff j).comp h1 (fun θ hθ => hmem j θ hθ)).sub h1
    exact πC.differentiable.comp_differentiableOn h2
  · intro j θ hθ k
    unfold stripSeq
    rw [hshift θ k, P.phi_per j _ (hmem j θ hθ) k]
    simp only [map_sub, map_add]
    abel
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hc : 0 < ‖πR‖ + 1 := by positivity
    have hU' := (Metric.tendstoUniformlyOn_iff.1 hU) (ε / (‖πR‖ + 1)) (by positivity)
    filter_upwards [hU'] with j hj x
    have hy : (x, I) ∈ (univ ×ˢ Dstar : Set (Phase (a + b))) := ⟨trivial, hI⟩
    have hyj : (x, I) ∈ phaseTube (Ds j) ((seq p j).ρ / 2) := ⟨trivial, hD j hI⟩
    have e : stripSeq Φ πC I j (KAM.realInclusion (a + b) x) =
        ((πR (psiR (Φ j) (x, I) - (x, I)) : ℝ) : ℂ) := by
      unfold stripSeq
      have : (KAM.realInclusion (a + b) x, KAM.realInclusion (a + b) I) =
          KAM.realInclusion₂ (a + b) (x, I) := rfl
      rw [this, ← P.phi_real_pt j hyj, ← map_sub, hπ]
    rw [e, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, ← map_sub, Real.norm_eq_abs]
    have h1 := hj (x, I) hy
    rw [dist_eq_norm] at h1
    have e2 : (Φinf (x, I) - (x, I)) - (psiR (Φ j) (x, I) - (x, I)) =
        Φinf (x, I) - psiR (Φ j) (x, I) := by abel
    rw [e2]
    calc |πR (Φinf (x, I) - psiR (Φ j) (x, I))| ≤ ‖πR‖ * ‖Φinf (x, I) - psiR (Φ j) (x, I)‖ :=
          πR.le_opNorm _
      _ ≤ ‖πR‖ * (ε / (‖πR‖ + 1)) := by gcongr
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ hc]; nlinarith [norm_nonneg πR]

end PsiSteps

end KAM.Planetary

end
