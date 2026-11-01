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
the displacement `‖K∞ - K‖ ≤ disp` on `T_{ρ∞}`. A bound valid at every torus point holds along
every torus line `τ ↦ L(θ + τ ν)` (`forall_orbit`, a restatement), and along **every solution that
meets the torus**, for all times of its interval, when the field is `C¹` near the torus
(`IsPhysicalFlowTorus.forall_solution`, `KAM/Application/Invariance.lean`, by ODE uniqueness).

* `abs_sub_le_of_convex`: mean value inequality for an observable with `‖Df‖ ≤ Λ` on a convex set.
* `CertifiedTorusAt.observable_bounds`: an enclosure `f ∘ Re K ∘ ι ∈ [lo, hi]` of an observable
  `f` of the model phase space (e.g. `f = g ∘ Ψ` for a physical observable `g` and the chart `Ψ`)
  gives `f ∘ k ∈ [lo - Λ disp, hi + Λ disp]` on the exact real torus `k = Re K∞ ∘ ι`.
* `CertifiedTorusAt.abs_angle_sub_le`, `abs_action_sub_le`: coordinates move by at most `disp`.
* `CertifiedTorusAt.norm_fderiv_realRestriction_sub_le`: derivatives move by at most `disp/ρ∞`
  (Cauchy at real points).
* `CertifiedTorusAt.norm_physFreq_sub_le`: the physical frequency `κ⁻¹ s∞ ω*` is within
  `disp/|κ|` of `κ⁻¹ s ω*`.
* `checkActionRangeReal c i ctr r` (checkable: the model of `A_i - ctr` summed at the real points,
  weight `w = 1`) and `CertifiedTorusAt.abs_action_sub_ctr_le_real`, or the strip version
  `checkActionRange` (weight `W`, about `e^{2π|k|ρ}` per mode, conservative) and
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

/-- A property of all torus points holds along every torus line `τ ↦ L(θ + τ ν)` (a restatement;
for arbitrary solutions meeting the torus see `IsPhysicalFlowTorus.forall_solution`). -/
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

/-- **The strip action-range check** for the action coordinate `i`: the model of `A_i - ctr` has
sup bound `≤ r` over the strip `T_ρ` (the model `checkEmbedding` uses for its action room). -/
def checkActionRange {n : ℕ} (c : TorusCertificate n α) (i : ℕ) (ctr r : ℚ) : Bool :=
  ble ((actionShiftModel n c.emb c.weight c.piEnc ctr i).supBound c.weight) (ofRatDown r)

/-- **The real-torus action-range check**: the same model summed at the real points (weight
`w = 1`, no `e^{2π|k|ρ}`) has sup bound `≤ r`. -/
def checkActionRangeReal {n : ℕ} (c : TorusCertificate n α) (i : ℕ) (ctr r : ℚ) : Bool :=
  ble ((actionShiftModel n c.emb c.weight c.piEnc ctr i).supBound
    KAM.CertificateSharp.Hybrid.realWeight) (ofRatDown r)

variable [LawfulCertArith α] {c : TorusCertificate n α}

/-- The enclosure of `A_i - ctr` (the model of `checkEmbedding`'s action room). -/
theorem actionShiftModel_encloses (hs : checkStatic c = true) (i : Fin n) (ctr : ℚ) :
    (actionShiftModel n c.emb c.weight c.piEnc ctr i.val).Encloses n c.weight.rho
      fun θ => (c.K θ).2 i - ((ctr : ℝ) : ℂ) := by
  have S := checkStatic_sound hs
  refine ((realCompModel_encloses (α := α) n c.weight.rho (c.emb.actionDeg.getD i 0)
    c.emb.action[i.val]?).addMixed S.hW S.hpe (constModel_encloses n c.weight.rho
      (-ctr) 0 0)).of_eq_fun fun θ => ?_
  rw [TorusCertificate.K, CertEmbedding.eval_snd]
  simp [slpConstVal, CertEmbedding.actionAt, sub_eq_add_neg]

/-- A passing strip action-range check: `|A_i(θ) - ctr| ≤ r` on the strip `T_ρ`. -/
theorem checkActionRange_sound (hs : checkStatic c = true) {i : Fin n} {ctr r : ℚ}
    (h : checkActionRange c i.val ctr r = true) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n c.params.rho) : ‖(c.K θ).2 i - ((ctr : ℝ) : ℂ)‖ ≤ r := by
  have S := checkStatic_sound hs
  have hθ' : θ ∈ complexStrip n c.weight.rho := by rw [S.hrho]; exact hθ
  exact (CertModel.norm_le_supBound S.hW (actionShiftModel_encloses hs i ctr) hθ').trans
    ((LawfulCertArith.ble_sound _ _ h).trans (LawfulCertArith.ofRatDown_le r))

/-- A passing real-torus action-range check: `|A_i(ι x) - ctr| ≤ r` at every real point. -/
theorem checkActionRangeReal_sound (hs : checkStatic c = true) {i : Fin n} {ctr r : ℚ}
    (h : checkActionRangeReal c i.val ctr r = true) (x : Fin n → ℝ) :
    ‖(c.K (realInclusion n x)).2 i - ((ctr : ℝ) : ℂ)‖ ≤ r := by
  have S := checkStatic_sound hs
  exact (KAM.CertificateSharp.Hybrid.CertModel.norm_le_supBound_real (CertWeight.rho_pos S.hW)
    (actionShiftModel_encloses hs i ctr) x).trans
    ((LawfulCertArith.ble_sound _ _ h).trans (LawfulCertArith.ofRatDown_le r))

/-- A bound of an action of the certificate's torus at the real points, in real form. -/
theorem abs_realRestriction_K_snd_sub_le {i : Fin n} {ctr r : ℚ}
    (hc : ∀ x : Fin n → ℝ, ‖(c.K (realInclusion n x)).2 i - ((ctr : ℝ) : ℂ)‖ ≤ r)
    (θ : Fin n → ℝ) : |(realRestriction c.K θ).2 i - ctr| ≤ r := by
  have hc0 := hc θ
  rw [isRealOnReals_iff.mp c.emb_structural.2.2] at hc0
  have e : (realInclusion₂ n (realRestriction c.K θ)).2 i - ((ctr : ℝ) : ℂ) =
      (((realRestriction c.K θ).2 i - ctr : ℝ) : ℂ) := by simp
  rw [e, Complex.norm_real, Real.norm_eq_abs] at hc0
  exact hc0

/-- Action bounds on the exact real torus from a bound on the certificate's real torus. -/
theorem CertifiedTorusAt.abs_action_sub_ctr_le_of {ωstar : Fin n → ℝ}
    {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {sinf : ℝ}
    (hT : CertifiedTorusAt c ωstar Kinf sinf) (hs : checkStatic c = true) {i : Fin n}
    {ctr r : ℚ} (hc : ∀ x : Fin n → ℝ, ‖(c.K (realInclusion n x)).2 i - ((ctr : ℝ) : ℂ)‖ ≤ r)
    (θ : Fin n → ℝ) : |(realRestriction Kinf θ).2 i - ctr| ≤ r + c.params.disp := by
  have hc' := abs_realRestriction_K_snd_sub_le hc θ
  have hd := hT.abs_action_sub_le hs θ i
  calc |(realRestriction Kinf θ).2 i - ctr|
      = |((realRestriction Kinf θ).2 i - (realRestriction c.K θ).2 i) +
          ((realRestriction c.K θ).2 i - ctr)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ c.params.disp + r := add_le_add hd hc'
    _ = r + c.params.disp := add_comm _ _

/-- **Checked action bounds on the exact real torus** (strip check): `|k_I(θ)_i - ctr| ≤ r + disp`
for every real angle `θ`. -/
theorem CertifiedTorusAt.abs_action_sub_ctr_le {ωstar : Fin n → ℝ}
    {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {sinf : ℝ}
    (hT : CertifiedTorusAt c ωstar Kinf sinf) (hs : checkStatic c = true) {i : Fin n}
    {ctr r : ℚ} (h : checkActionRange c i.val ctr r = true) (θ : Fin n → ℝ) :
    |(realRestriction Kinf θ).2 i - ctr| ≤ r + c.params.disp := by
  have S := checkStatic_sound hs
  exact hT.abs_action_sub_ctr_le_of hs (fun x => checkActionRange_sound hs h
    (realInclusion_mem_complexStrip (S.hρinf.trans S.hρinfρ) x)) θ

/-- **Checked action bounds on the exact real torus** (real-torus check): `|k_I(θ)_i - ctr| ≤
r + disp` for every real angle `θ`. -/
theorem CertifiedTorusAt.abs_action_sub_ctr_le_real {ωstar : Fin n → ℝ}
    {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {sinf : ℝ}
    (hT : CertifiedTorusAt c ωstar Kinf sinf) (hs : checkStatic c = true) {i : Fin n}
    {ctr r : ℚ} (h : checkActionRangeReal c i.val ctr r = true) (θ : Fin n → ℝ) :
    |(realRestriction Kinf θ).2 i - ctr| ≤ r + c.params.disp :=
  hT.abs_action_sub_ctr_le_of hs (checkActionRangeReal_sound hs h) θ

end Action

end KAM.Application
