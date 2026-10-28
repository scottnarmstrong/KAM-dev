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

theorem strip_mem (P : PsiSteps sbar p Ds hs fs Ψ Φ)
    {Dstar : Set (Fin (a + b) → ℝ)} (hD : ∀ j, Dstar ⊆ realTube (Ds j) ((seq p j).ρ / 2))
    {I : Fin (a + b) → ℝ} (hI : I ∈ Dstar) (j : ℕ) :
    ∀ θ ∈ KAM.complexStrip (a + b) (geometricWidth sbar),
      (θ, KAM.realInclusion (a + b) I) ∈
        coefficientDom (Ds j) (seq p j).ρ (sbar + (seq p j).s) := by
  intro θ hθ
  rw [(conv_data _ _ _).2]
  have hsj : 0 < (seq p j).s := (P.hyp j).positive.2.1
  refine ⟨fun i => (hθ i).trans_le ?_, ?_⟩
  · unfold geometricWidth; gcongr; linarith
  · exact realTube_mono (D := Ds j) (by have := P.rho_stage_pos j; linarith :
      (seq p j).ρ / 2 ≤ (seq p j).ρ) (hD j hI)

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
  have hmem := P.strip_mem hD hI
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

/-- `bpP:p3:limit-phi`, complex angle extension and the three block sup bounds on the strip: for
`I ∈ D_*`, every angle coordinate and every action coordinate of `θ ↦ Φ(θ, I) − (θ, I)` extends
holomorphically and periodically to `|Im θ| < s̄/2π`, bounded by `(3/2) Ê₀ s₀/2π` (angles),
`(3/2)(M̂/M) Ê₀ ρ̂₀` (first block) and `(3/2) Ê₀ ρ̂₀` (last block); the finite-stage coordinate
functions converge to it with all derivatives on closed substrips. -/
theorem limit_phi_strip_of_steps (P : PsiSteps sbar p Ds hs fs Ψ Φ)
    {Dstar : Set (Fin (a + b) → ℝ)} (hD : ∀ j, Dstar ⊆ realTube (Ds j) ((seq p j).ρ / 2))
    {Φinf : Phase (a + b) → Phase (a + b)}
    (hU : TendstoUniformlyOn (fun j => psiR (Φ j)) Φinf atTop (univ ×ˢ Dstar)) :
    ∀ I ∈ Dstar,
      (∀ c : Fin (a + b), ∃ G, StripLimit (a + b) (geometricWidth sbar)
        (3 / 2 * eHat p * p.s / (2 * π))
        (stripSeq Φ ((ContinuousLinearMap.proj c).comp (ContinuousLinearMap.fst ℂ _ _)) I)
        (fun x => (((Φinf (x, I) - (x, I)).1 c : ℝ) : ℂ)) G) ∧
      (∀ i : Fin a, ∃ G, StripLimit (a + b) (geometricWidth sbar)
        (3 / 2 * (p.Mhat / p.M) * eHat p * rhoHat p)
        (stripSeq Φ ((ContinuousLinearMap.proj (Fin.castAdd b i)).comp
          (ContinuousLinearMap.snd ℂ _ _)) I)
        (fun x => (((Φinf (x, I) - (x, I)).2 (Fin.castAdd b i) : ℝ) : ℂ)) G) ∧
      (∀ i : Fin b, ∃ G, StripLimit (a + b) (geometricWidth sbar)
        (3 / 2 * eHat p * rhoHat p)
        (stripSeq Φ ((ContinuousLinearMap.proj (Fin.natAdd a i)).comp
          (ContinuousLinearMap.snd ℂ _ _)) I)
        (fun x => (((Φinf (x, I) - (x, I)).2 (Fin.natAdd a i) : ℝ) : ℂ)) G) := by
  intro I hI
  have h0 : 0 < rhoHat p := (P.hyp 0).R_pos
  have hs0 : 0 < p.s := (P.hyp 0).positive.2.1
  have he0 : 0 ≤ eHat p := (P.hyp 0).eHat_nonneg
  have hr : 0 ≤ p.Mhat / p.M :=
    div_nonneg (P.hyp 0).positive.2.2.2.2.2.1.le (P.hyp 0).positive.2.2.2.2.1.le
  have hdisp : ∀ j, ∀ θ ∈ KAM.complexStrip (a + b) (geometricWidth sbar),
      ‖firstBlock (b := b) ((Φ j (θ, KAM.realInclusion (a + b) I)).2 - KAM.realInclusion (a + b) I)‖ ≤
        3 / 2 * (p.Mhat / p.M) * eHat p * rhoHat p ∧
      ‖lastBlock (a := a) ((Φ j (θ, KAM.realInclusion (a + b) I)).2 - KAM.realInclusion (a + b) I)‖ ≤
        3 / 2 * eHat p * rhoHat p ∧
      ‖(Φ j (θ, KAM.realInclusion (a + b) I)).1 - θ‖ ≤ 3 / 2 * eHat p * p.s / (2 * π) := by
    intro j θ hθ
    obtain ⟨b1, b2, b3⟩ := P.phi_disp_complex j _ (P.strip_mem hD hI j θ hθ)
    have hpart := P.partial_sum_le j
    have hp := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) hr) h0.le
    refine ⟨b1.trans (by nlinarith), b2.trans (by nlinarith), ?_⟩
    rw [le_div_iff₀ (by positivity), mul_comm]
    refine b3.trans (by nlinarith)
  refine ⟨fun c => ?_, fun i => ?_, fun i => ?_⟩
  · refine P.strip_comp hD hU _ (ContinuousLinearMap.proj c |>.comp (ContinuousLinearMap.fst ℝ _ _))
      (fun v => by simp) (by positivity) hI fun j θ hθ => ?_
    unfold stripSeq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.coe_fst', Prod.fst_sub, Pi.sub_apply]
    exact (norm_le_pi_norm (((Φ j (θ, KAM.realInclusion (a + b) I)).1 - θ)) c).trans
      (hdisp j θ hθ).2.2
  · refine P.strip_comp hD hU _ (ContinuousLinearMap.proj (Fin.castAdd b i) |>.comp
      (ContinuousLinearMap.snd ℝ _ _)) (fun v => by simp)
      (by have := mul_nonneg hr h0.le; positivity) hI fun j θ hθ => ?_
    unfold stripSeq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.coe_snd', Prod.snd_sub, Pi.sub_apply]
    exact (norm_le_pi_norm (firstBlock (b := b) ((Φ j (θ, KAM.realInclusion (a + b) I)).2 -
      KAM.realInclusion (a + b) I)) i).trans (hdisp j θ hθ).1
  · refine P.strip_comp hD hU _ (ContinuousLinearMap.proj (Fin.natAdd a i) |>.comp
      (ContinuousLinearMap.snd ℝ _ _)) (fun v => by simp) (by positivity) hI fun j θ hθ => ?_
    unfold stripSeq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.coe_snd', Prod.snd_sub, Pi.sub_apply]
    exact (norm_le_pi_norm (lastBlock (a := a) ((Φ j (θ, KAM.realInclusion (a + b) I)).2 -
      KAM.realInclusion (a + b) I)) i).trans (hdisp j θ hθ).2.1

end PsiSteps

end KAM.Planetary

end
