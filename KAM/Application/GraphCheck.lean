/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.GraphCert
public import KAM.Certificate.Sound.Embedding

/-!
# The graph check

A `Bool` check of the graph condition `AngleNearId c δ` and of the margin `δ + disp/ρ∞ < 1`, from
the strip models of the certificate's own embedding (no new numerical claim: the same
`compDerivModel` sup bounds that `checkEmbedding` uses for `|Im U_i|`).

* `angleRowUp n K W pe i`: the upward-rounded row sum `Σ_j sup_{T_ρ} |∂_j U_i|` of the angle
  displacement `U_i` (`K_θ(θ) = θ + U(θ)`).
* `checkAngleGraph c δ`: `0 ≤ δ`, `δ ρ∞ + disp < ρ∞` (exact rationals) and `angleRowUp ≤ δ` for
  every row `i < n`.
* `checkAngleGraph_sound`: a passing check gives `AngleNearId c δ` and `δ + disp/ρ∞ < 1`.
* `CertifiedTorus.exists_realGraph_of_checks`: the graph adapter with every certificate-side input
  a passing `Bool` check (`checkStatic`, `checkHamBounds`, `checkAngleGraph`).
-/

@[expose] public noncomputable section

open Set

namespace KAM.Application

open KAM KAM.Certificate CertArith

variable {n : ℕ} {α : Type} [CertArith α]

/-- The upward-rounded row sum `Σ_j sup_{T_ρ} |∂_j U_i|` of the angle displacement `U_i`. -/
def angleRowUp (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (pe : PiEnclosure α) (i : ℕ) : α :=
  sumUp (fun j : Fin n =>
    (compDerivModel n W pe (K.angleDeg.getD i 0) K.angle[i]? j.val).supBound W) (List.finRange n)

/-- **The graph check**: `0 ≤ δ`, the margin `δ ρ∞ + disp < ρ∞`, and every angle row sum
`Σ_j sup_{T_ρ} |∂_j U_i| ≤ δ`. -/
def checkAngleGraph (c : TorusCertificate n α) (δ : ℚ) : Bool :=
  decide (0 ≤ δ) && decide (δ * c.params.rhoInf + c.params.disp < c.params.rhoInf) &&
    (List.range n).all fun i => ble (angleRowUp n c.emb c.weight c.piEnc i) (ofRatDown δ)

/-- The `i`-th angle coordinate of `K` is `θ_i + U_i(θ)`, so its derivative is `e_i* + DU_i`. -/
theorem fderiv_eval_fst_apply (K : CertEmbedding α) (z w : Fin n → ℂ) (i : Fin n) :
    (fderiv ℂ (K.eval n) z w).1 i = w i + fderiv ℂ (K.angleAt n i.val) z w := by
  have hd := (CertEmbedding.differentiable_eval n K z).hasFDerivAt
  have h1 : HasFDerivAt (fun θ => (K.eval n θ).1 i)
      (((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (Fin n → ℂ))).comp (fderiv ℂ (K.eval n) z)) z :=
    (((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (Fin n → ℂ))).hasFDerivAt).comp z hd
  have h2 : HasFDerivAt (fun θ => (K.eval n θ).1 i)
      ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ) +
        fderiv ℂ (K.angleAt n i.val) z) z := by
    have e : (fun θ => (K.eval n θ).1 i) = fun θ => θ i + K.angleAt n i.val θ :=
      funext fun θ => CertEmbedding.eval_fst n K θ i
    rw [e]
    exact (ContinuousLinearMap.proj i).hasFDerivAt.add
      (differentiable_angleAt n K i.val z).hasFDerivAt
  have := congrArg (fun L => L w) (h1.unique h2)
  simpa using this

variable [LawfulCertArith α]

/-- A passing row gives `‖DU_i‖ ≤ δ` on the strip `T_ρ`. -/
theorem norm_fderiv_angleAt_le {c : TorusCertificate n α} (hs : checkStatic c = true)
    {δ : ℚ} {i : Fin n}
    (hrow : ble (angleRowUp n c.emb c.weight c.piEnc i.val) (ofRatDown δ) = true)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n c.params.rho) :
    ‖fderiv ℂ (c.emb.angleAt n i.val) θ‖ ≤ δ := by
  have S := checkStatic_sound hs
  have hθ' : θ ∈ complexStrip n c.weight.rho := by rw [S.hrho]; exact hθ
  have hj (j : Fin n) : ‖fderiv ℂ (c.emb.angleAt n i.val) θ (Pi.single j 1)‖ ≤
      val ((compDerivModel n c.weight c.piEnc (c.emb.angleDeg.getD i.val 0) c.emb.angle[i.val]?
        j.val).supBound c.weight) :=
    CertModel.norm_le_supBound S.hW (compDerivModel_encloses S.hW S.hpe _ _ j) hθ'
  have hS : ∑ j : Fin n, val ((compDerivModel n c.weight c.piEnc (c.emb.angleDeg.getD i.val 0)
      c.emb.angle[i.val]? j.val).supBound c.weight) ≤
        val (angleRowUp n c.emb c.weight c.piEnc i.val) := by
    rw [← sum_finRange_map_eq]; exact sumUp_ge _ _
  exact (norm_clm_le_sum_single _).trans ((Finset.sum_le_sum fun j _ => hj j).trans
    (hS.trans ((LawfulCertArith.ble_sound _ _ hrow).trans (LawfulCertArith.ofRatDown_le δ))))

/-- **Soundness of the graph check**: the graph condition and the strict margin. -/
theorem checkAngleGraph_sound {c : TorusCertificate n α} (hs : checkStatic c = true) {δ : ℚ}
    (hg : checkAngleGraph c δ = true) :
    AngleNearId c δ ∧ (δ : ℝ) + (c.params.disp : ℝ) / c.params.rhoInf < 1 := by
  have S := checkStatic_sound hs
  simp only [checkAngleGraph, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hg
  obtain ⟨⟨hδ0, hm⟩, hrows⟩ := hg
  have hδ0' : (0 : ℝ) ≤ δ := by exact_mod_cast hδ0
  refine ⟨⟨hδ0', fun x v => ?_⟩, ?_⟩
  · have hx : realInclusion n x ∈ complexStrip n c.params.rho :=
      realInclusion_mem_complexStrip (S.hρinf.trans S.hρinfρ) x
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hδ0' (norm_nonneg v))).2 fun i => ?_
    have e : ((fderiv ℂ c.K (realInclusion n x) (realInclusion n v)).1 -
        realInclusion n v) i = fderiv ℂ (c.emb.angleAt n i.val) (realInclusion n x)
          (realInclusion n v) := by
      rw [Pi.sub_apply, TorusCertificate.K, fderiv_eval_fst_apply]
      ring
    rw [e]
    refine ((fderiv ℂ (c.emb.angleAt n i.val) (realInclusion n x)).le_opNorm _).trans ?_
    rw [norm_realInclusion]
    exact mul_le_mul_of_nonneg_right (norm_fderiv_angleAt_le hs (hrows i i.isLt) hx)
      (norm_nonneg v)
  · have hρ : (0 : ℝ) < c.params.rhoInf := S.hρinf
    have hm' : (δ : ℝ) * c.params.rhoInf + c.params.disp < c.params.rhoInf := by exact_mod_cast hm
    have h1 : (c.params.disp : ℝ) / c.params.rhoInf < 1 - δ := by
      rw [div_lt_iff₀ hρ]; linarith
    linarith

omit [LawfulCertArith α] in
/-- The static and Hamiltonian-bound sub-checks of the landed checker. -/
theorem checkStatic_checkHamBounds_of_checkTorusCertificate {c : TorusCertificate n α}
    (hc : checkTorusCertificate c = true) :
    checkStatic c = true ∧ checkHamBounds c = true := by
  simp only [checkTorusCertificate, Bool.and_eq_true] at hc
  exact ⟨hc.1.1.1.1.1.1.1, hc.1.1.1.1.1.1.2⟩

/-- **The graph adapter, fully checked**: a certified torus (any certifier) with passing
`checkStatic`, `checkHamBounds` and `checkAngleGraph c δ` is, in real model coordinates, a real
model torus of `realHam c.H` and an analytic graph over the angles with constant
`δ + disp/ρ∞ < 1`. -/
theorem CertifiedTorus.exists_realGraph_of_checks {c : TorusCertificate n α}
    {ωstar : Fin n → ℝ} (hT : CertifiedTorus c ωstar) (hs : checkStatic c = true)
    (hh : checkHamBounds c = true) {δ : ℚ} (hg : checkAngleGraph c δ = true) :
    ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ),
      CertifiedTorusAt c ωstar Kinf sinf ∧
      IsRealModelTorus (realHam c.H) (sinf • ωstar) c.params.E0 (realRestriction Kinf) ∧
      IsAngleGraph (realRestriction Kinf) ((δ : ℝ) + (c.params.disp : ℝ) / c.params.rhoInf) :=
  have hg' := checkAngleGraph_sound hs hg
  CertifiedTorus.exists_realGraph hT hs (isRealHolo_of_checkHamBounds hs hh) hg'.1 hg'.2

end KAM.Application
