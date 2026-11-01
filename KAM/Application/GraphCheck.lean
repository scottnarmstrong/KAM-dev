/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.GraphCert
public import KAM.Certificate.Sound.Embedding
public import KAM.CertificateSharp.Hybrid.ModelMul

/-!
# The graph checks

`Bool` checks of the graph condition `AngleNearId c δ` and of the margin `δ + disp/ρ∞ < 1`, from
the models `compDerivModel` of `∂_j U_i` (`K_θ(θ) = θ + U(θ)`) that `checkEmbedding` already
builds; no new numerical claim. Two versions:

* **real torus (recommended)**: `angleDerivModel`, `angleRowUpReal`, `checkAngleGraphReal`. The sup
  of `|∂_j U_i|` over the **real** angles, by the weight `w = 1`
  (`KAM.CertificateSharp.Hybrid.realWeight`, `CertModel.norm_le_supBound_real`) applied to the
  derivative model **before** its conversion to degree `0` (`CertModel.ofDeriv`; the conversion
  `toDeg` adds a radius measured in the strip weight): for `U_i = (2π)^d Σ_k c_k e^{2πi k·θ}` the
  bound is `(2π)^{d+1} Σ_k |k_j| |c_k|` (rounded up), with no exponential weight. This is what
  `AngleNearId` needs.
* **strip**: `angleRowUp`, `checkAngleGraph`. The sup over the whole strip `T_ρ` (weight `W`):
  each mode is weighted by about `e^{2π|k|ρ}`, so this is very conservative for large `ρ` (on T2,
  `ρ = 9`, one mode of amplitude `10⁻²⁰` fails `δ = 0.99`; see `Tests/Probes.lean`). Kept for
  compatibility.

`checkAngleGraphReal_sound`, `checkAngleGraph_sound`: either passing check gives `AngleNearId c δ`
and `δ + disp/ρ∞ < 1`. `CertifiedTorus.exists_realGraph_of_checks`: the graph adapter with every
certificate-side input a passing `Bool` check (`checkStatic`, `checkHamBounds`, and either graph
check).
-/

@[expose] public noncomputable section

open Set

namespace KAM.Application

open KAM KAM.Certificate CertArith

variable {n : ℕ} {α : Type} [CertArith α]

/-- The upward-rounded row sum `Σ_j sup_{T_ρ} |∂_j U_i|` of the angle displacement `U_i` over the
strip `T_ρ`. -/
def angleRowUp (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (pe : PiEnclosure α) (i : ℕ) : α :=
  sumUp (fun j : Fin n =>
    (compDerivModel n W pe (K.angleDeg.getD i 0) K.angle[i]? j.val).supBound W) (List.finRange n)

/-- The model of `∂_j U_i` before the conversion to degree `0`: `(2π)^{dU_i + 1}` times the
polynomial `Σ_k i k_j c_k e^{2πi k·θ}` (radius: coefficient rounding only, `0` on `ℚ`). -/
def angleDerivModel (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (i j : ℕ) : CertModel α :=
  CertModel.ofDeriv W j (K.angleDeg.getD i 0) (realCompPoly n K.angle[i]?)

/-- The upward-rounded row sum `Σ_j sup_{x ∈ ℝⁿ} |∂_j U_i(x)|` over the **real** torus: the
unconverted derivative models summed with the weight `w = 1`, i.e. `(2π)^{dU_i + 1}` (rounded up)
times `Σ_j Σ_k |k_j| |c_k|`. -/
def angleRowUpReal (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (i : ℕ) : α :=
  sumUp (fun j : Fin n => (angleDerivModel n K W i j.val).supBound
    KAM.CertificateSharp.Hybrid.realWeight) (List.finRange n)

/-- **The strip graph check**: `0 ≤ δ`, the margin `δ ρ∞ + disp < ρ∞`, and every angle row sum
`Σ_j sup_{T_ρ} |∂_j U_i| ≤ δ`. -/
def checkAngleGraph (c : TorusCertificate n α) (δ : ℚ) : Bool :=
  decide (0 ≤ δ) && decide (δ * c.params.rhoInf + c.params.disp < c.params.rhoInf) &&
    (List.range n).all fun i => ble (angleRowUp n c.emb c.weight c.piEnc i) (ofRatDown δ)

/-- **The real-torus graph check**: `0 ≤ δ`, the margin `δ ρ∞ + disp < ρ∞`, and every angle row
sum `Σ_j sup_{ℝⁿ} |∂_j U_i| ≤ δ`. -/
def checkAngleGraphReal (c : TorusCertificate n α) (δ : ℚ) : Bool :=
  decide (0 ≤ δ) && decide (δ * c.params.rhoInf + c.params.disp < c.params.rhoInf) &&
    (List.range n).all fun i => ble (angleRowUpReal n c.emb c.weight i) (ofRatDown δ)

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

/-- `AngleNearId c δ` from a bound `‖DU_i(ι x)‖ ≤ δ` of every row at every real point. -/
theorem angleNearId_of_rows {c : TorusCertificate n α} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hrow : ∀ (i : Fin n) (x : Fin n → ℝ),
      ‖fderiv ℂ (c.emb.angleAt n i.val) (realInclusion n x)‖ ≤ δ) : AngleNearId c δ := by
  refine ⟨hδ0, fun x v => ?_⟩
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hδ0 (norm_nonneg v))).2 fun i => ?_
  have e : ((fderiv ℂ c.K (realInclusion n x) (realInclusion n v)).1 -
      realInclusion n v) i = fderiv ℂ (c.emb.angleAt n i.val) (realInclusion n x)
        (realInclusion n v) := by
    rw [Pi.sub_apply, TorusCertificate.K, fderiv_eval_fst_apply]
    ring
  rw [e]
  refine ((fderiv ℂ (c.emb.angleAt n i.val) (realInclusion n x)).le_opNorm _).trans ?_
  rw [norm_realInclusion]
  exact mul_le_mul_of_nonneg_right (hrow i x) (norm_nonneg v)

variable [LawfulCertArith α]

/-- The margin `δ + disp/ρ∞ < 1` from its exact rational form. -/
theorem margin_of_rat {c : TorusCertificate n α} (hs : checkStatic c = true) {δ : ℚ}
    (hm : δ * c.params.rhoInf + c.params.disp < c.params.rhoInf) :
    (δ : ℝ) + (c.params.disp : ℝ) / c.params.rhoInf < 1 := by
  have hρ : (0 : ℝ) < c.params.rhoInf := (checkStatic_sound hs).hρinf
  have hm' : (δ : ℝ) * c.params.rhoInf + c.params.disp < c.params.rhoInf := by exact_mod_cast hm
  have h1 : (c.params.disp : ℝ) / c.params.rhoInf < 1 - δ := by
    rw [div_lt_iff₀ hρ]; linarith
  linarith

/-- The row sum bound `Σ_j ‖∂_j U_i‖ ≤ δ` of a linear map from row bounds of its columns. -/
theorem norm_fderiv_angleAt_le_of_sum {c : TorusCertificate n α} {i : Fin n} {z : Fin n → ℂ}
    {b : Fin n → ℝ} {S : α} {δ : ℚ}
    (hj : ∀ j : Fin n, ‖fderiv ℂ (c.emb.angleAt n i.val) z (Pi.single j 1)‖ ≤ b j)
    (hS : ∑ j, b j ≤ val S) (hrow : ble S (ofRatDown δ) = true) :
    ‖fderiv ℂ (c.emb.angleAt n i.val) z‖ ≤ δ :=
  (norm_clm_le_sum_single _).trans ((Finset.sum_le_sum fun j _ => hj j).trans
    (hS.trans ((LawfulCertArith.ble_sound _ _ hrow).trans (LawfulCertArith.ofRatDown_le δ))))

/-- A passing strip row gives `‖DU_i‖ ≤ δ` on the strip `T_ρ`. -/
theorem norm_fderiv_angleAt_le {c : TorusCertificate n α} (hs : checkStatic c = true)
    {δ : ℚ} {i : Fin n}
    (hrow : ble (angleRowUp n c.emb c.weight c.piEnc i.val) (ofRatDown δ) = true)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n c.params.rho) :
    ‖fderiv ℂ (c.emb.angleAt n i.val) θ‖ ≤ δ := by
  have S := checkStatic_sound hs
  have hθ' : θ ∈ complexStrip n c.weight.rho := by rw [S.hrho]; exact hθ
  refine norm_fderiv_angleAt_le_of_sum (fun j => CertModel.norm_le_supBound S.hW
    (compDerivModel_encloses S.hW S.hpe _ _ j) hθ') ?_ hrow
  rw [← sum_finRange_map_eq]; exact sumUp_ge _ _

/-- A passing real-torus row gives `‖DU_i(ι x)‖ ≤ δ` at every real point. -/
theorem norm_fderiv_angleAt_le_real {c : TorusCertificate n α} (hs : checkStatic c = true)
    {δ : ℚ} {i : Fin n}
    (hrow : ble (angleRowUpReal n c.emb c.weight i.val) (ofRatDown δ) = true)
    (x : Fin n → ℝ) : ‖fderiv ℂ (c.emb.angleAt n i.val) (realInclusion n x)‖ ≤ δ := by
  have S := checkStatic_sound hs
  have hm (j : Fin n) : (angleDerivModel n c.emb c.weight i.val j.val).Encloses n c.weight.rho
      fun θ => fderiv ℂ (c.emb.angleAt n i.val) θ (Pi.single j 1) :=
    (CertModel.Encloses.ofDeriv S.hW j _ (realCompPoly n c.emb.angle[i.val]?)).of_eq_fun
      fun θ => (fderiv_realComp_apply n _ _ θ _).symm
  refine norm_fderiv_angleAt_le_of_sum (fun j =>
    KAM.CertificateSharp.Hybrid.CertModel.norm_le_supBound_real (CertWeight.rho_pos S.hW)
      (hm j) x) ?_ hrow
  rw [← sum_finRange_map_eq]; exact sumUp_ge _ _

/-- **Soundness of the real-torus graph check**: the graph condition and the strict margin. -/
theorem checkAngleGraphReal_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    {δ : ℚ} (hg : checkAngleGraphReal c δ = true) :
    AngleNearId c δ ∧ (δ : ℝ) + (c.params.disp : ℝ) / c.params.rhoInf < 1 := by
  simp only [checkAngleGraphReal, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hg
  obtain ⟨⟨hδ0, hm⟩, hrows⟩ := hg
  exact ⟨angleNearId_of_rows (by exact_mod_cast hδ0) fun i x =>
    norm_fderiv_angleAt_le_real hs (hrows i i.isLt) x, margin_of_rat hs hm⟩

/-- **Soundness of the strip graph check**: the graph condition and the strict margin. -/
theorem checkAngleGraph_sound {c : TorusCertificate n α} (hs : checkStatic c = true) {δ : ℚ}
    (hg : checkAngleGraph c δ = true) :
    AngleNearId c δ ∧ (δ : ℝ) + (c.params.disp : ℝ) / c.params.rhoInf < 1 := by
  have S := checkStatic_sound hs
  simp only [checkAngleGraph, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hg
  obtain ⟨⟨hδ0, hm⟩, hrows⟩ := hg
  exact ⟨angleNearId_of_rows (by exact_mod_cast hδ0) fun i x =>
    norm_fderiv_angleAt_le hs (hrows i i.isLt)
      (realInclusion_mem_complexStrip (S.hρinf.trans S.hρinfρ) x), margin_of_rat hs hm⟩

omit [LawfulCertArith α] in
/-- The static and Hamiltonian-bound sub-checks of the landed checker. -/
theorem checkStatic_checkHamBounds_of_checkTorusCertificate {c : TorusCertificate n α}
    (hc : checkTorusCertificate c = true) :
    checkStatic c = true ∧ checkHamBounds c = true := by
  simp only [checkTorusCertificate, Bool.and_eq_true] at hc
  exact ⟨hc.1.1.1.1.1.1.1, hc.1.1.1.1.1.1.2⟩

/-- **The graph adapter, fully checked**: a certified torus (any certifier) with passing
`checkStatic`, `checkHamBounds` and one of the graph checks (`checkAngleGraphReal c δ`, or the
strip `checkAngleGraph c δ`) is, in real model coordinates, a real model torus of `realHam c.H` and
an analytic graph over the angles with constant `δ + disp/ρ∞ < 1`. -/
theorem _root_.KAM.Certificate.CertifiedTorus.exists_realGraph_of_checks
    {c : TorusCertificate n α} {ωstar : Fin n → ℝ} (hT : CertifiedTorus c ωstar)
    (hs : checkStatic c = true) (hh : checkHamBounds c = true) {δ : ℚ}
    (hg : checkAngleGraphReal c δ = true ∨ checkAngleGraph c δ = true) :
    ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ),
      CertifiedTorusAt c ωstar Kinf sinf ∧
      IsRealModelTorus (realHam c.H) (sinf • ωstar) c.params.E0 (realRestriction Kinf) ∧
      IsAngleGraph (realRestriction Kinf) ((δ : ℝ) + (c.params.disp : ℝ) / c.params.rhoInf) :=
  have hg' := hg.elim (checkAngleGraphReal_sound hs) (checkAngleGraph_sound hs)
  hT.exists_realGraph hs (isRealHolo_of_checkHamBounds hs hh) hg'.1 hg'.2

/-- Alias in the adapter namespace (the name announced with `V2-ADAPT GRAPH READY`). -/
alias CertifiedTorus.exists_realGraph_of_checks :=
  KAM.Certificate.CertifiedTorus.exists_realGraph_of_checks

end KAM.Application
