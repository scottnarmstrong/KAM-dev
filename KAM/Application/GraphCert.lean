/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.Certified
public import KAM.Application.Graph
public import KAM.Strip.Cauchy

/-!
# The certified torus is a graph over the angles

The graph/embedding adapter at the certificate level (improvement #7).

* `norm_fderiv_sub_le_of_real` (Cauchy at real points): if `‖K₁ - K₂‖ ≤ d` on `T_ρ`, then
  `‖DK₁(ι x) - DK₂(ι x)‖ ≤ d/ρ` at every real `x` (operator norm of the max norms; the polydisc of
  every radius `δ < ρ` around a real point lies in `T_ρ`).
* `AngleNearId c δ`: **the checkable numerical condition on the certificate's own embedding** `K`:
  `0 ≤ δ` and, at every real angle `x` and real direction `v`,
  `‖(DK(ι x) (ι v))_θ - ι v‖ ≤ δ ‖v‖`; equivalently, for every row `i`,
  `Σ_j |∂_j U_i(x)| ≤ δ` where `K_θ(θ) = θ + U(θ)` (`KAM/Application/GraphCheck.lean` checks it:
  `checkAngleGraphReal` at the real points, or the conservative strip `checkAngleGraph`).
* `derivNearId_torusAngle_realRestriction`: then the angle map `A = (Re K∞ ∘ ι)_θ` of the exact
  torus satisfies `‖DA - 1‖ ≤ δ + d/ρ`.
* `CertifiedTorusAt.isAngleGraph`, `KAM.Certificate.CertifiedTorus.exists_realGraph` (dot
  notation `hT.exists_realGraph`; alias `KAM.Application.CertifiedTorus.exists_realGraph`): with
  the strict margin **`δ + disp/ρ∞ < 1`**, the real certified torus is an analytic graph over the
  angles (`IsAngleGraph`), on top of being a real model torus (`IsRealModelTorus`).
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace KAM.Application

open KAM KAM.Certificate CertArith

variable {n : ℕ}

/-- **Cauchy at real points**: if `‖K₁ - K₂‖ ≤ d` on `T_ρ`, the derivatives differ by at most `d/ρ`
at every real point. -/
theorem norm_fderiv_sub_le_of_real {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {K₁ K₂ : (Fin n → ℂ) → F} {ρ d : ℝ} (hρ : 0 < ρ)
    (h₁ : DifferentiableOn ℂ K₁ (complexStrip n ρ)) (h₂ : DifferentiableOn ℂ K₂ (complexStrip n ρ))
    (hd : ∀ θ ∈ complexStrip n ρ, ‖K₁ θ - K₂ θ‖ ≤ d) (x : Fin n → ℝ) :
    ‖fderiv ℂ K₁ (realInclusion n x) - fderiv ℂ K₂ (realInclusion n x)‖ ≤ d / ρ := by
  have hf : DifferentiableOn ℂ (fun θ => K₁ θ - K₂ θ) (complexStrip n ρ) := h₁.sub h₂
  have hx : realInclusion n x ∈ complexStrip n ρ := realInclusion_mem_complexStrip hρ x
  have hsub : fderiv ℂ (fun θ => K₁ θ - K₂ θ) (realInclusion n x) =
      fderiv ℂ K₁ (realInclusion n x) - fderiv ℂ K₂ (realInclusion n x) :=
    fderiv_fun_sub (h₁.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hx))
      (h₂.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hx))
  rw [← hsub]
  have hev : ∀ᶠ δ in 𝓝[<] ρ,
      ‖fderiv ℂ (fun θ => K₁ θ - K₂ θ) (realInclusion n x)‖ ≤ d / δ := by
    filter_upwards [Ioo_mem_nhdsLT hρ] with δ hδ
    exact norm_fderiv_le_of_mem_complexStrip hf hd hδ.1
      (realInclusion_mem_complexStrip (sub_pos.2 hδ.2) x)
  have ht : Tendsto (fun δ : ℝ => d / δ) (𝓝[<] ρ) (𝓝 (d / ρ)) :=
    ((continuousAt_const.div continuousAt_id hρ.ne').tendsto).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht hev

/-- **The angle map of the exact real torus is near the identity**: from the reference `K`'s
angle-block bound `δ` at real points and `‖K∞ - K‖ ≤ d` on `T_ρ`, `‖DA - 1‖ ≤ δ + d/ρ` for
`A = torusAngle (realRestriction K∞)`. -/
theorem derivNearId_torusAngle_realRestriction
    {Kinf K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ρ d δ : ℝ} (hρ : 0 < ρ)
    (hKinf : DifferentiableOn ℂ Kinf (complexStrip n ρ)) (hr : IsRealOnReals Kinf)
    (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hd : ∀ θ ∈ complexStrip n ρ, ‖Kinf θ - K θ‖ ≤ d) (hδ0 : 0 ≤ δ)
    (hδ : ∀ x v : Fin n → ℝ,
      ‖(fderiv ℂ K (realInclusion n x) (realInclusion n v)).1 - realInclusion n v‖ ≤ δ * ‖v‖) :
    DerivNearId (torusAngle (realRestriction Kinf)) (δ + d / ρ) := by
  have hR := realRestriction_fderiv hρ hKinf hr
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd _ (realInclusion_mem_complexStrip hρ 0))
  intro x
  have hdx : DifferentiableAt ℝ (realRestriction Kinf) x := (hR x).1
  refine ⟨(ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)).differentiableAt.comp x hdx, ?_⟩
  rw [fderiv_torusAngle hdx]
  refine ContinuousLinearMap.opNorm_le_bound _ (add_nonneg hδ0 (div_nonneg hd0 hρ.le))
    fun v => ?_
  set ι := realInclusion n
  set DKi := fderiv ℂ Kinf (ι x)
  set DK := fderiv ℂ K (ι x)
  have e : ι ((((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)).comp
      (fderiv ℝ (realRestriction Kinf) x)) - ContinuousLinearMap.id ℝ (Fin n → ℝ)) v) =
      ((DKi - DK) (ι v)).1 + ((DK (ι v)).1 - ι v) := by
    have h1 := congrArg Prod.fst ((hR x).2 v)
    simp only [realInclusion₂_apply] at h1
    have h1' : ι ((fderiv ℝ (realRestriction Kinf) x) v).1 = (DKi (ι v)).1 := h1
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.id_apply, map_sub, Prod.fst_sub, h1']
    abel
  have hC := norm_fderiv_sub_le_of_real hρ hKinf hK hd x
  have h2 : ‖((DKi - DK) (ι v)).1‖ ≤ d / ρ * ‖v‖ :=
    (norm_fst_le _).trans (((DKi - DK).le_opNorm _).trans (by
      rw [norm_realInclusion]; exact mul_le_mul_of_nonneg_right hC (norm_nonneg v)))
  rw [← norm_realInclusion, e]
  calc ‖((DKi - DK) (ι v)).1 + ((DK (ι v)).1 - ι v)‖
      ≤ ‖((DKi - DK) (ι v)).1‖ + ‖(DK (ι v)).1 - ι v‖ := norm_add_le _ _
    _ ≤ d / ρ * ‖v‖ + δ * ‖v‖ := add_le_add h2 (hδ x v)
    _ = (δ + d / ρ) * ‖v‖ := by ring

/-! ### The certificate level -/

variable {α : Type} [CertArith α]

/-- **The graph condition on the certificate's embedding** `K` (checkable, `GraphCheck.lean`):
`0 ≤ δ` and `‖(DK(ι x)(ι v))_θ - ι v‖ ≤ δ ‖v‖` at real `x, v`; for `K_θ = θ + U(θ)` this is the
row-sum bound `Σ_j |∂_j U_i(x)| ≤ δ` for every `i`. -/
def AngleNearId (c : TorusCertificate n α) (δ : ℝ) : Prop :=
  0 ≤ δ ∧ ∀ x v : Fin n → ℝ,
    ‖(fderiv ℂ c.K (realInclusion n x) (realInclusion n v)).1 - realInclusion n v‖ ≤ δ * ‖v‖

variable [LawfulCertArith α] {c : TorusCertificate n α} {ωstar : Fin n → ℝ}

/-- **The certified real torus is an analytic graph over the angles** (named witnesses): with the
graph condition `AngleNearId c δ` and the strict margin `δ + disp/ρ∞ < 1`. -/
theorem CertifiedTorusAt.isAngleGraph {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {sinf : ℝ} (hT : CertifiedTorusAt c ωstar Kinf sinf) (hs : checkStatic c = true) {δ : ℝ}
    (hδ : AngleNearId c δ) (hsmall : δ + (c.params.disp : ℝ) / c.params.rhoInf < 1) :
    IsAngleGraph (realRestriction Kinf) (δ + (c.params.disp : ℝ) / c.params.rhoInf) := by
  have S := checkStatic_sound hs
  obtain ⟨-, -, hd, hp, hr, -, -, -, -, hdisp, -⟩ := hT
  obtain ⟨han, -, -, hper⟩ := real_restriction S.hρinf hd hr
  exact isAngleGraph_of_derivNearId han (hper hp)
    (derivNearId_torusAngle_realRestriction S.hρinf hd hr
      (CertEmbedding.differentiable_eval n c.emb).differentiableOn hdisp hδ.1 hδ.2) hsmall

/-- **The graph adapter** (`V2-ADAPT GRAPH READY`). A certified torus (from any certifier), the
static check, the certified Hamiltonian facts (`IsRealHolo c.D c.H`, e.g.
`isRealHolo_of_checkHamBounds`), the graph condition `AngleNearId c δ` and the margin
`δ + disp/ρ∞ < 1` give an exact torus `K∞` at `s∞` (all clauses of `CertifiedTorus`) whose real
restriction `k = Re ∘ K∞ ∘ ι` is

* a real model torus of `realHam c.H` at `s∞ ω*` on the level `E₀` (analytic,
  `k(θ + m) = k(θ) + (m, 0)`, its lines solve Hamilton's equations, `realHam c.H ∘ k = E₀`), and
* an analytic graph over the angles: `k(θ) = (A θ, G (A θ))` with `A = torusAngle k` an analytic
  diffeomorphism of `ℝⁿ` commuting with `ℤⁿ`, `‖DA - 1‖ ≤ δ + disp/ρ∞ < 1`,
  `G = torusGraph k` analytic and `ℤⁿ`-periodic, `range k = {z | z.2 = G z.1}`, `k` injective
  modulo `ℤⁿ` and an immersion. -/
theorem _root_.KAM.Certificate.CertifiedTorus.exists_realGraph (hT : CertifiedTorus c ωstar)
    (hs : checkStatic c = true) (hH : IsRealHolo c.D c.H) {δ : ℝ} (hδ : AngleNearId c δ)
    (hsmall : δ + (c.params.disp : ℝ) / c.params.rhoInf < 1) :
    ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ),
      CertifiedTorusAt c ωstar Kinf sinf ∧
      IsRealModelTorus (realHam c.H) (sinf • ωstar) c.params.E0 (realRestriction Kinf) ∧
      IsAngleGraph (realRestriction Kinf) (δ + (c.params.disp : ℝ) / c.params.rhoInf) := by
  obtain ⟨Kinf, sinf, hT⟩ := (certifiedTorus_iff c ωstar).1 hT
  exact ⟨Kinf, sinf, hT, hT.isRealModelTorus hs hH, hT.isAngleGraph hs hδ hsmall⟩

/-- Alias in the adapter namespace (the name announced with `V2-ADAPT GRAPH READY`). -/
alias CertifiedTorus.exists_realGraph := KAM.Certificate.CertifiedTorus.exists_realGraph

end KAM.Application
