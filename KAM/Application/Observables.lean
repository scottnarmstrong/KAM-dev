/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.GraphCheck
public import KAM.Application.Transport

/-!
# Observables along the certified torus

The observables adapter (improvement #7): bounds on observables of the exact torus `K∞`, in model or
original coordinates, from enclosures of the certificate's own embedding `K` (numerical data) and
the displacement `‖K∞ - K‖ ≤ disp` on `T_{ρ∞}`. Since the orbits of the torus stay on it, every
bound holds along every orbit on the torus for all times (`forall_orbit`).

* `abs_sub_le_of_convex`: mean value inequality for an observable with `‖Df‖ ≤ Λ` on a convex set.
* `CertifiedTorusAt.observable_bounds`: an enclosure `f ∘ Re K ∘ ι ∈ [lo, hi]` of an observable
  `f` of the model phase space (e.g. `f = g ∘ Ψ` for a physical observable `g` and the chart `Ψ`)
  gives `f ∘ k ∈ [lo - Λ disp, hi + Λ disp]` on the exact real torus `k = Re K∞ ∘ ι`.
* `CertifiedTorusAt.abs_angle_sub_le`, `abs_action_sub_le`: coordinates move by at most `disp`.
* `CertifiedTorusAt.norm_fderiv_realRestriction_sub_le`: derivatives move by at most `disp/ρ∞`
  (Cauchy at real points).
* `CertifiedTorusAt.norm_physFreq_sub_le`: the physical frequency `κ⁻¹ s∞ ω*` is within
  `disp/|κ|` of `κ⁻¹ s ω*`.
* `checkActionRange c i ctr r` (checkable, the strip model of `A_i - ctr`) and
  `CertifiedTorusAt.abs_action_sub_ctr_le`: `|k_I(θ)_i - ctr| ≤ r + disp` for every real `θ`.
* `realInclusion₂_realRestriction_K_mem_D`: the certificate's own real torus lies in `c.D` (from
  `checkEmbedding`), for choosing the convex set of `observable_bounds`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Application

open KAM KAM.Certificate KAM.Torus CertArith

variable {n : ℕ}

/-- Mean value inequality for an observable on a convex set. -/
theorem abs_sub_le_of_convex {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℝ}
    {S : Set F} (hS : Convex ℝ S) {Λ : ℝ} (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hΛ : ∀ z ∈ S, ‖fderiv ℝ f z‖ ≤ Λ) {z z' : F} (hz : z ∈ S) (hz' : z' ∈ S) :
    |f z - f z'| ≤ Λ * ‖z - z'‖ := by
  have h := hS.norm_image_sub_le_of_norm_fderiv_le hf hΛ hz' hz
  rwa [Real.norm_eq_abs] at h

/-- Every orbit on a torus stays on it: a property of all torus points holds along every line. -/
theorem forall_orbit {X : Type*} {L : (Fin n → ℝ) → X} {P : X → Prop} (h : ∀ θ, P (L θ))
    (ν : Fin n → ℝ) (θ : Fin n → ℝ) (τ : ℝ) : P (L (θ + τ • ν)) :=
  h _

section At

variable {α : Type} [CertArith α] [LawfulCertArith α] {c : TorusCertificate n α}
  {ωstar : Fin n → ℝ} {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {sinf : ℝ}

/-- **Observable bounds on the certified torus**: if `‖Df‖ ≤ Λ` on a convex set `S` containing the
real points of `c.D` and the certificate's real torus, an enclosure `lo ≤ f(Re K(ι θ)) ≤ hi`
transfers to `lo - Λ disp ≤ f(k θ) ≤ hi + Λ disp` on the exact real torus `k`. -/
theorem CertifiedTorusAt.observable_bounds (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (hs : checkStatic c = true) {f : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {S : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hS : Convex ℝ S)
    (hDS : ∀ p, realInclusion₂ n p ∈ c.D → p ∈ S) (hKS : ∀ θ, realRestriction c.K θ ∈ S)
    {Λ : ℝ} (hf : ∀ z ∈ S, DifferentiableAt ℝ f z) (hΛ : ∀ z ∈ S, ‖fderiv ℝ f z‖ ≤ Λ)
    {lo hi : ℝ} (hlo : ∀ θ, lo ≤ f (realRestriction c.K θ))
    (hhi : ∀ θ, f (realRestriction c.K θ) ≤ hi) (θ : Fin n → ℝ) :
    lo - Λ * c.params.disp ≤ f (realRestriction Kinf θ) ∧
      f (realRestriction Kinf θ) ≤ hi + Λ * c.params.disp := by
  have hk : realRestriction Kinf θ ∈ S := by
    apply hDS
    rw [← isRealOnReals_iff.mp hT.2.2.2.2.1]
    exact hT.realInclusion_mem_D hs θ
  have h1 := abs_sub_le_of_convex hS hf hΛ hk (hKS θ)
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ _ hk)
  have h2 := mul_le_mul_of_nonneg_left (hT.norm_realRestriction_sub_le hs θ) hΛ0
  have h3 := abs_le.1 (h1.trans h2)
  exact ⟨by linarith [hlo θ, h3.1], by linarith [hhi θ, h3.2]⟩

/-- Angle coordinates of the exact real torus are within `disp` of the certificate's. -/
theorem CertifiedTorusAt.abs_angle_sub_le (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (hs : checkStatic c = true) (θ : Fin n → ℝ) (i : Fin n) :
    |(realRestriction Kinf θ).1 i - (realRestriction c.K θ).1 i| ≤ c.params.disp := by
  refine le_trans ?_ (hT.norm_realRestriction_sub_le hs θ)
  rw [← Real.norm_eq_abs, ← Pi.sub_apply, ← Prod.fst_sub]
  exact (norm_le_pi_norm _ i).trans (norm_fst_le _)

/-- Action coordinates of the exact real torus are within `disp` of the certificate's. -/
theorem CertifiedTorusAt.abs_action_sub_le (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (hs : checkStatic c = true) (θ : Fin n → ℝ) (i : Fin n) :
    |(realRestriction Kinf θ).2 i - (realRestriction c.K θ).2 i| ≤ c.params.disp := by
  refine le_trans ?_ (hT.norm_realRestriction_sub_le hs θ)
  rw [← Real.norm_eq_abs, ← Pi.sub_apply, ← Prod.snd_sub]
  exact (norm_le_pi_norm _ i).trans (norm_snd_le _)

/-- **Derivatives of the exact real torus** are within `disp/ρ∞` of the certificate's (Cauchy at
real points; operator norms of the max norms). -/
theorem CertifiedTorusAt.norm_fderiv_realRestriction_sub_le
    (hT : CertifiedTorusAt c ωstar Kinf sinf) (hs : checkStatic c = true) (θ : Fin n → ℝ) :
    ‖fderiv ℝ (realRestriction Kinf) θ - fderiv ℝ (realRestriction c.K) θ‖ ≤
      (c.params.disp : ℝ) / c.params.rhoInf := by
  have S := checkStatic_sound hs
  obtain ⟨-, -, hd, -, hr, -, -, -, -, hdisp, -⟩ := hT
  have hK : DifferentiableOn ℂ c.K (complexStrip n c.params.rhoInf) :=
    (CertEmbedding.differentiable_eval n c.emb).differentiableOn
  have hKr : IsRealOnReals c.K := c.emb_structural.2.2
  have h1 := realRestriction_fderiv S.hρinf hd hr θ
  have h2 := realRestriction_fderiv S.hρinf hK hKr θ
  refine le_trans ?_ (norm_fderiv_sub_le_of_real S.hρinf hd hK hdisp θ)
  refine norm_le_of_isometric_restriction norm_realInclusion norm_realInclusion₂ _ _ fun v => ?_
  simp only [sub_apply, map_sub, h1.2, h2.2]

omit [LawfulCertArith α] in
/-- **The physical frequency** `κ⁻¹ s∞ ω*` is within `disp/|κ|` of `κ⁻¹ s ω*`. -/
theorem CertifiedTorusAt.norm_physFreq_sub_le (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (κ : ℝ) :
    ‖κ⁻¹ • (sinf • ωstar) - κ⁻¹ • ((c.params.s : ℝ) • ωstar)‖ ≤ c.params.disp / |κ| := by
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right hT.2.2.2.2.2.2.2.2.2.2 (abs_nonneg κ)

/-- The certificate's real torus lies in `c.D` (from the embedding check, `μ > 0`). -/
theorem realInclusion₂_realRestriction_K_mem_D (hs : checkStatic c = true)
    (he : checkEmbedding c = true) (θ : Fin n → ℝ) :
    realInclusion₂ n (realRestriction c.K θ) ∈ c.D := by
  have S := checkStatic_sound hs
  rw [← isRealOnReals_iff.mp c.emb_structural.2.2]
  exact (checkEmbedding_sound hs he).1 _ (realInclusion_mem_complexStrip
    (S.hρinf.trans S.hρinfρ) θ) (Metric.mem_ball_self S.hμ)

end At

/-! ### A checkable action range -/

section Action

variable {α : Type} [CertArith α]

/-- **The action-range check** for the action coordinate `i`: the strip model of `A_i - ctr` has sup
bound `≤ r` (the model `checkEmbedding` uses for its action room). -/
def checkActionRange {n : ℕ} (c : TorusCertificate n α) (i : ℕ) (ctr r : ℚ) : Bool :=
  ble ((actionShiftModel n c.emb c.weight c.piEnc ctr i).supBound c.weight) (ofRatDown r)

variable [LawfulCertArith α] {c : TorusCertificate n α}

/-- A passing action-range check: `|A_i(θ) - ctr| ≤ r` on the strip `T_ρ`. -/
theorem checkActionRange_sound (hs : checkStatic c = true) {i : Fin n} {ctr r : ℚ}
    (h : checkActionRange c i.val ctr r = true) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n c.params.rho) : ‖(c.K θ).2 i - ((ctr : ℝ) : ℂ)‖ ≤ r := by
  have S := checkStatic_sound hs
  have hθ' : θ ∈ complexStrip n c.weight.rho := by rw [S.hrho]; exact hθ
  have hA := CertModel.norm_le_supBound S.hW
    ((realCompModel_encloses (α := α) n c.weight.rho (c.emb.actionDeg.getD i 0)
      c.emb.action[i.val]?).addMixed S.hW S.hpe (constModel_encloses n c.weight.rho
        (-ctr) 0 0)) hθ'
  have h1 := LawfulCertArith.ble_sound _ _ h
  have h2 := LawfulCertArith.ofRatDown_le (α := α) r
  refine le_trans (le_of_eq ?_) (hA.trans (h1.trans h2))
  rw [TorusCertificate.K, CertEmbedding.eval_snd]
  simp [slpConstVal, CertEmbedding.actionAt, sub_eq_add_neg]

/-- **Checked action bounds on the exact real torus**: `|k_I(θ)_i - ctr| ≤ r + disp` for every real
angle, hence along every orbit on the torus for all times. -/
theorem CertifiedTorusAt.abs_action_sub_ctr_le {ωstar : Fin n → ℝ}
    {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {sinf : ℝ}
    (hT : CertifiedTorusAt c ωstar Kinf sinf) (hs : checkStatic c = true) {i : Fin n}
    {ctr r : ℚ} (h : checkActionRange c i.val ctr r = true) (θ : Fin n → ℝ) :
    |(realRestriction Kinf θ).2 i - ctr| ≤ r + c.params.disp := by
  have S := checkStatic_sound hs
  have hc := checkActionRange_sound hs h
    (realInclusion_mem_complexStrip (S.hρinf.trans S.hρinfρ) θ)
  rw [isRealOnReals_iff.mp c.emb_structural.2.2] at hc
  have hc' : |(realRestriction c.K θ).2 i - ctr| ≤ r := by
    have e : (realInclusion₂ n (realRestriction c.K θ)).2 i - ((ctr : ℝ) : ℂ) =
        (((realRestriction c.K θ).2 i - ctr : ℝ) : ℂ) := by simp
    rw [e, Complex.norm_real, Real.norm_eq_abs] at hc
    exact hc
  have hd := hT.abs_action_sub_le hs θ i
  calc |(realRestriction Kinf θ).2 i - ctr|
      = |((realRestriction Kinf θ).2 i - (realRestriction c.K θ).2 i) +
          ((realRestriction c.K θ).2 i - ctr)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ c.params.disp + r := add_le_add hd hc'
    _ = r + c.params.disp := add_comm _ _

end Action

end KAM.Application
