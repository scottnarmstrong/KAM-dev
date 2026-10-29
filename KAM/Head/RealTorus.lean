/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Normalize
public import KAM.Frozen.Defs.KamCover
public import KAM.Torus.Objects
import KAM.Head.Frequency
import KAM.Head.H1
import KAM.Head.InverseFrequency
import KAM.Head.Lagrangian
import KAM.Head.MatrixNorms
import KAM.Head.Parameters
import KAM.Head.UnperturbedFrame
import KAM.Strip.Bridges

/-!
# The real tori are KAM tori

Blueprint Part 4, `bp:p4:real-torus`. Under `(SA)` and for `ω ∈ Ω_γ`, the
real restriction `k_ω = KAM.realRestriction K_ω` of the normalized torus `K_ω` is an invariant
Lagrangian torus of `H = realHamiltonian h f` with frequency `ω` (the frozen
`KAM.IsInvariantLagrangianTorus`), it lies within `η₀` of `x ↦ (x, I_ω)`, with `I_ω ∈ B` and
`∇h(I_ω) = ω`, and its range lies in the cover `𝒦(η₀)` (`KAM.kamCover`).

The proof steps of the blueprint are the following helper lemmas, all stated for an abstract torus
`K` with the properties given by `KAM.Head.normalize`; `KAM.Head.real_torus` instantiates them at
`K = normTorus … ω`.

* `step:p4:rt-analytic`: `KAM.Head.rt_analytic`, analyticity and primarity of `k`.
* `step:p4:rt-small`: `KAM.Head.rt_small`, `|DW| ≤ 16 n η₀ / s ≤ 1/2` on `T_{s/16}` and
  `|D ũ| ≤ 1/2` on `ℝⁿ` for the angle displacement `ũ(x) = k(x)₁ - x`, which is `ℤⁿ`-periodic.
* `step:p4:rt-immersion`: `KAM.Head.rt_immersion`, `Dk(x)` is injective.
* `step:p4:rt-embedding`: `KAM.Head.rt_embedding`, `k(x') = k(x) + (m, 0)` forces `x' = x + m`,
  by the mean value inequality on the convex set `ℝⁿ`.
* `step:p4:rt-lagrangian`: `KAM.Head.rt_lagrangian`, from `Λ = 0` on `T_{s/8}`
  (`KAM.Head.lagrangian`) and `bp:p4:matrix-norms` (iv).
* `step:p4:rt-ode`: `KAM.Head.rt_ode`, Hamilton's equations along `t ↦ k(x + tω)`, from
  `KAM.hamiltonian_real` and the invariance of `K` on `T_{s/8}`.
* `step:p4:rt-cover`: `KAM.Head.rt_cover`, the cover clauses (ii), (iv) and the membership in
  `kamCover`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology KAM.Torus

namespace KAM.Head

section Geometry

variable {n : ℕ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ρ : ℝ}

/-- The angle displacement `ũ(x) = k(x)₁ - x` of the real restriction `k = realRestriction K`. -/
def angleReal (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (x : Fin n → ℝ) : Fin n → ℝ :=
  (realRestriction K x).1 - x

/-! ### Step `step:p4:rt-analytic` -/

/-- Blueprint `step:p4:rt-analytic`: the real restriction of a holomorphic, primary torus that is
real on reals is real-analytic and satisfies `k(x + m) = k(x) + (m, 0)`. -/
theorem rt_analytic (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hKp : IsPrimaryOnStrip K ρ) (hKr : IsRealOnReals K) :
    AnalyticOnNhd ℝ (realRestriction K) Set.univ ∧
      ∀ (x : Fin n → ℝ) (m : Fin n → ℤ),
        realRestriction K (x + fun i => (m i : ℝ)) =
          realRestriction K x + (fun i => (m i : ℝ), 0) :=
  ⟨analyticOnNhd_realRestriction hρ hK, fun x m => realRestriction_add_int hρ hKp hKr x m⟩

/-! ### Step `step:p4:rt-small` -/

/-- Blueprint `step:p4:rt-small`, the full Cauchy bound. For `K` holomorphic on `T_ρ` with
`‖K - K⁰_I‖ ≤ η` there, the displacement `W = K - K⁰_I` satisfies `‖DW‖ ≤ n (ρ/2)⁻¹ η` on
`T_{ρ/2}` (`bp:p1:cauchy-strip` with loss `ρ/2`). -/
theorem rt_small_full (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    {I : Fin n → ℝ} {η : ℝ}
    (hη : ∀ θ ∈ complexStrip n ρ, ‖K θ - unperturbedTorus I θ‖ ≤ η)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ / 2)) :
    ‖fderiv ℂ (fun θ => K θ - unperturbedTorus I θ) θ‖ ≤ (n : ℝ) * (ρ / 2)⁻¹ * η := by
  have hW : DifferentiableOn ℂ (fun θ => K θ - unperturbedTorus I θ) (complexStrip n ρ) :=
    hK.sub (differentiable_unperturbedTorus I).differentiableOn
  have hθ' : θ ∈ complexStrip n (ρ - ρ / 2) := by rwa [show ρ - ρ / 2 = ρ / 2 by ring]
  exact (cauchy_strip hW hη (half_pos hρ)).2 θ hθ'

/-- The angle component of the displacement derivative on the half strip: if `‖W‖ ≤ η` on `T_ρ`
and `n (ρ/2)⁻¹ η ≤ 1/2`, then `‖(DK(θ) v)₁ - v‖ ≤ ½ ‖v‖` on `T_{ρ/2}`
(a consequence of `KAM.Head.rt_small_full`). -/
theorem rt_small_complex (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    {I : Fin n → ℝ} {η : ℝ}
    (hη : ∀ θ ∈ complexStrip n ρ, ‖K θ - unperturbedTorus I θ‖ ≤ η)
    (hsm : (n : ℝ) * (ρ / 2)⁻¹ * η ≤ 1 / 2) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ / 2))
    (v : Fin n → ℂ) : ‖(fderiv ℂ K θ v).1 - v‖ ≤ 1 / 2 * ‖v‖ := by
  have hc := rt_small_full hρ hK hη hθ
  have hKθ : DifferentiableAt ℂ K θ :=
    hK.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds (complexStrip_mono (by linarith) hθ))
  have hder : fderiv ℂ (fun θ => K θ - unperturbedTorus I θ) θ =
      fderiv ℂ K θ - ContinuousLinearMap.inl ℂ (Fin n → ℂ) (Fin n → ℂ) := by
    exact (hKθ.hasFDerivAt.sub (unperturbedTorus_hasFDerivAt I θ)).fderiv
  have h1 : (fderiv ℂ K θ v).1 - v =
      (fderiv ℂ (fun θ => K θ - unperturbedTorus I θ) θ v).1 := by
    rw [hder]; simp
  rw [h1]
  calc ‖(fderiv ℂ (fun θ => K θ - unperturbedTorus I θ) θ v).1‖
      ≤ ‖fderiv ℂ (fun θ => K θ - unperturbedTorus I θ) θ v‖ := norm_fst_le _
    _ ≤ ‖fderiv ℂ (fun θ => K θ - unperturbedTorus I θ) θ‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 / 2 * ‖v‖ := by
        gcongr
        exact hc.trans hsm

/-- Blueprint `step:p4:rt-small`. For `K` holomorphic on `T_ρ` and real on reals, with
`‖K - K⁰_I‖ ≤ η` there and `n (ρ/2)⁻¹ η ≤ 1/2`: the angle displacement `ũ(x) = k(x)₁ - x` of
the real restriction is differentiable with `Dũ(x) v = (Dk(x) v)₁ - v` and `‖Dũ(x)‖ ≤ 1/2` at
every real `x`. -/
theorem rt_small (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hKr : IsRealOnReals K) {I : Fin n → ℝ} {η : ℝ}
    (hη : ∀ θ ∈ complexStrip n ρ, ‖K θ - unperturbedTorus I θ‖ ≤ η)
    (hsm : (n : ℝ) * (ρ / 2)⁻¹ * η ≤ 1 / 2) (x : Fin n → ℝ) :
    HasFDerivAt (angleReal K)
      ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)).comp (fderiv ℝ (realRestriction K) x) -
        ContinuousLinearMap.id ℝ (Fin n → ℝ)) x ∧
    ‖(ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)).comp (fderiv ℝ (realRestriction K) x) -
        ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤ 1 / 2 := by
  obtain ⟨hdk, hv⟩ := realRestriction_fderiv hρ hK hKr x
  refine ⟨(hdk.hasFDerivAt.fst).sub (hasFDerivAt_id x), ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
  have h1 := congrArg (fun w => w.1) (hv v)
  simp only [realInclusion₂_apply] at h1
  have h2 := rt_small_complex hρ hK hη hsm (realInclusion_mem_complexStrip (half_pos hρ) x)
    (realInclusion n v)
  rw [← h1, ← map_sub, norm_realInclusion, norm_realInclusion] at h2
  simpa using h2

/-- The angle displacement is `ℤⁿ`-periodic: `ũ(x + m) = ũ(x)`. -/
theorem angleReal_add_int (hρ : 0 < ρ) (hKp : IsPrimaryOnStrip K ρ) (hKr : IsRealOnReals K)
    (x : Fin n → ℝ) (m : Fin n → ℤ) :
    angleReal K (x + fun i => (m i : ℝ)) = angleReal K x := by
  unfold angleReal
  rw [realRestriction_add_int hρ hKp hKr x m]
  simp only [Prod.fst_add]
  abel

/-! ### Steps `step:p4:rt-immersion` and `step:p4:rt-embedding` -/

/-- Blueprint `step:p4:rt-immersion`: if `‖(Dk(x) v)₁ - v‖ ≤ ½ ‖v‖` then `Dk(x)` is injective. -/
theorem rt_immersion {k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} {x : Fin n → ℝ}
    (h : ‖(ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)).comp (fderiv ℝ k x) -
        ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤ 1 / 2) :
    Function.Injective (fderiv ℝ k x) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have h1 := (ContinuousLinearMap.le_opNorm _ v).trans
    (mul_le_mul_of_nonneg_right h (norm_nonneg v))
  simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply, hv,
    ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.coe_fst', Prod.fst_zero, zero_sub,
    norm_neg] at h1
  have : ‖v‖ ≤ 0 := by linarith
  exact norm_le_zero_iff.1 this

/-- Blueprint `step:p4:rt-embedding`: if `k(x') = k(x) + (m, 0)` with `m ∈ ℤⁿ`, and the angle
displacement `ũ = k₁ - id` is `ℤⁿ`-periodic, differentiable, with `‖Dũ‖ ≤ 1/2`, then
`x' = x + m` (mean value inequality on the convex set `ℝⁿ`). -/
theorem rt_embedding {k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    {u : (Fin n → ℝ) → Fin n → ℝ} (hu : ∀ x, u x = (k x).1 - x)
    (hper : ∀ (x : Fin n → ℝ) (m : Fin n → ℤ), u (x + fun i => (m i : ℝ)) = u x)
    (hd : ∀ x, DifferentiableAt ℝ u x) (hb : ∀ x, ‖fderiv ℝ u x‖ ≤ 1 / 2)
    (θ θ' : Fin n → ℝ) (m : Fin n → ℤ) (h : k θ' = k θ + (fun i => (m i : ℝ), 0)) :
    θ' = θ + fun i => (m i : ℝ) := by
  have h1 : (k θ').1 = (k θ).1 + fun i => (m i : ℝ) := by rw [h]; rfl
  have h2 : θ' - (θ + fun i => (m i : ℝ)) =
      u (θ + fun i => (m i : ℝ)) - u θ' := by
    rw [hper θ m, hu θ, hu θ', h1]
    abel
  have h3 : ‖u (θ + fun i => (m i : ℝ)) - u θ'‖ ≤ 1 / 2 * ‖(θ + fun i => (m i : ℝ)) - θ'‖ :=
    (convex_univ (𝕜 := ℝ) (E := Fin n → ℝ)).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hd x) (fun x _ => hb x) (Set.mem_univ θ') (Set.mem_univ _)
  have h4 : ‖θ' - (θ + fun i => (m i : ℝ))‖ ≤ 1 / 2 * ‖θ' - (θ + fun i => (m i : ℝ))‖ := by
    calc ‖θ' - (θ + fun i => (m i : ℝ))‖ = ‖u (θ + fun i => (m i : ℝ)) - u θ'‖ := by rw [h2]
      _ ≤ 1 / 2 * ‖(θ + fun i => (m i : ℝ)) - θ'‖ := h3
      _ = 1 / 2 * ‖θ' - (θ + fun i => (m i : ℝ))‖ := by rw [norm_sub_rev]
  have h5 : ‖θ' - (θ + fun i => (m i : ℝ))‖ = 0 := by
    linarith [norm_nonneg (θ' - (θ + fun i => (m i : ℝ)))]
  exact sub_eq_zero.1 (norm_eq_zero.1 h5)

/-! ### Step `step:p4:rt-lagrangian` -/

/-- The bilinear form `(L u)ᵀ Ω₀ (L v)` is `uᵀ (Lᵀ Ω₀ L) v`. -/
theorem dotProduct_mulVec_lagrange (L : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    (L *ᵥ u) ⬝ᵥ (omegaZeroMatrix n *ᵥ (L *ᵥ v)) = u ⬝ᵥ ((Lᵀ * omegaZeroMatrix n * L) *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Lᵀ,
    Matrix.vecMul_transpose]

/-- Blueprint `step:p4:rt-lagrangian`: if `Λ = DKᵀ Ω₀ DK` vanishes on `T_ρ`, the real restriction
`k` of a holomorphic `K` that is real on reals is isotropic for the frozen `symplecticForm`:
`ω(Dk(x) u, Dk(x) v) = (ι u)ᵀ Λ(ι x) (ι v) = 0`, by `bp:p4:matrix-norms` (iv) and the relation
`ι (Dk(x) u) = DK(ι x)(ι u)` of `bp:p1:real-restriction`. -/
theorem rt_lagrangian (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hKr : IsRealOnReals K) (hΛ : ∀ θ ∈ complexStrip n ρ, lagrangeMat K θ = 0)
    (x u v : Fin n → ℝ) :
    symplecticForm (fderiv ℝ (realRestriction K) x u) (fderiv ℝ (realRestriction K) x v) = 0 := by
  obtain ⟨-, hd⟩ := realRestriction_fderiv hρ hK hKr x
  apply Complex.ofReal_injective
  rw [ofReal_symplecticForm]
  have hu : ((fun i => ((fderiv ℝ (realRestriction K) x u).1 i : ℂ)),
      fun i => ((fderiv ℝ (realRestriction K) x u).2 i : ℂ)) =
      fderiv ℂ K (realInclusion n x) (realInclusion n u) := hd u
  have hv : ((fun i => ((fderiv ℝ (realRestriction K) x v).1 i : ℂ)),
      fun i => ((fderiv ℝ (realRestriction K) x v).2 i : ℂ)) =
      fderiv ℂ K (realInclusion n x) (realInclusion n v) := hd v
  rw [hu, hv]
  have e : ∀ w : (Fin n → ℂ) × (Fin n → ℂ),
      (Equiv.sumArrowEquivProdArrow _ _ _).symm w = sumVec n w := fun w => rfl
  rw [e, e, ← colMat_mulVec, ← colMat_mulVec]
  have hΛx := hΛ (realInclusion n x) (realInclusion_mem_complexStrip hρ x)
  rw [show colMat (fderiv ℂ K (realInclusion n x)) = tangentMat K (realInclusion n x) from rfl,
    dotProduct_mulVec_lagrange]
  have : (tangentMat K (realInclusion n x))ᵀ * omegaZeroMatrix n * tangentMat K (realInclusion n x)
      = 0 := hΛx
  rw [this]
  simp

/-! ### Step `step:p4:rt-ode` -/

/-- Blueprint `step:p4:rt-ode`: Hamilton's equations along the linear flow. Let `φ` be holomorphic
on the open set `𝔅`, real at the real points of `𝔅`, and `H = Re φ ∘ ι`. If `K` is holomorphic on
`T_ρ` and real on reals with `K(T_ρ) ⊆ 𝔅` and `X_φ(K) = DK ω` there, then
`t' ↦ k(x + t' ω)` has derivative `X_H(k(x + t ω))` at `t' = t`, where `k = realRestriction K`
(`bp:p1:hamiltonian-real` and `bp:p1:real-restriction`). -/
theorem rt_ode {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} (h𝔅 : IsOpen 𝔅)
    {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hφ : DifferentiableOn ℂ φ 𝔅)
    (hreal : ∀ y : (Fin n → ℝ) × (Fin n → ℝ), realInclusion₂ n y ∈ 𝔅 →
      (φ (realInclusion₂ n y)).im = 0)
    {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} (hH : ∀ y, H y = (φ (realInclusion₂ n y)).re)
    (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ)) (hKr : IsRealOnReals K)
    (hK𝔅 : ∀ θ ∈ complexStrip n ρ, K θ ∈ 𝔅) {ω : Fin n → ℝ}
    (hE : ∀ θ ∈ complexStrip n ρ, invarianceError φ K ω θ = 0) (x : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => realRestriction K (x + s • ω))
      (hamiltonianVectorField H (realRestriction K (x + t • ω))) t := by
  obtain ⟨hdk, hv⟩ := realRestriction_fderiv hρ hK hKr (x + t • ω)
  have hlin : HasDerivAt (fun s : ℝ => x + s • ω) ω t := by
    simpa using ((hasDerivAt_id t).smul_const ω).const_add x
  have hcomp := hdk.hasFDerivAt.comp_hasDerivAt t hlin
  have hX : hamiltonianVectorField H (realRestriction K (x + t • ω)) =
      fderiv ℝ (realRestriction K) (x + t • ω) ω := by
    refine realInclusion₂_injective n ?_
    have hmem : realInclusion n (x + t • ω) ∈ complexStrip n ρ :=
      realInclusion_mem_complexStrip hρ _
    have hKy := isRealOnReals_iff.mp hKr (x + t • ω)
    have hz : realInclusion₂ n (realRestriction K (x + t • ω)) ∈ 𝔅 := by
      rw [← hKy]; exact hK𝔅 _ hmem
    rw [hamiltonianVectorField_eq_of_real h𝔅 hφ hreal hz (Filter.Eventually.of_forall hH),
      hv ω, ← hKy]
    have := hE _ hmem
    rw [invarianceError, sub_eq_zero] at this
    exact this
  rw [hX]
  exact hcomp

/-! ### Step `step:p4:rt-cover` -/

/-- Blueprint `step:p4:rt-cover`: the cover clauses. If `‖K - K⁰_I‖ ≤ η < r₀` on `T_ρ`, `K` is real
on reals, `I ∈ B` with `∇h(I) = ω`, `γ > 0`, `ω ∈ Dio_{γ,τ}` and `k = realRestriction K` is an
invariant Lagrangian torus of `H = realHamiltonian h f`, then (ii) `‖k(x)₂ - I‖ < r₀`,
(iv) `‖k(x) - (x, I)‖ ≤ η`, and `k(ℝⁿ) ⊆ 𝒦(η)` with witnesses `k`, `ω`, `γ`, `I`. -/
theorem rt_cover {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
    {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {r₀ τ γ η : ℝ} {ω I : Fin n → ℝ} (hρ : 0 < ρ)
    (hKr : IsRealOnReals K) (hγ : 0 < γ) (hdio : IsDiophantine γ τ ω)
    (hinv : IsInvariantLagrangianTorus (realHamiltonian h f) ω (realRestriction K))
    (hIB : I ∈ B) (hfreq : frequencyMap h I = ω)
    (hη : ∀ θ ∈ complexStrip n ρ, ‖K θ - unperturbedTorus I θ‖ ≤ η) (hηr : η < r₀) :
    (∀ x : Fin n → ℝ, ‖(realRestriction K x).2 - I‖ < r₀) ∧
    (∀ x : Fin n → ℝ, ‖realRestriction K x - (x, I)‖ ≤ η) ∧
    Set.range (realRestriction K) ⊆ kamCover h f B r₀ τ η := by
  have hiv : ∀ x : Fin n → ℝ, ‖realRestriction K x - (x, I)‖ ≤ η := by
    intro x
    have h1 := hη _ (realInclusion_mem_complexStrip hρ x)
    have h2 : K (realInclusion n x) - unperturbedTorus I (realInclusion n x) =
        realInclusion₂ n (realRestriction K x - (x, I)) := by
      rw [map_sub, ← isRealOnReals_iff.mp hKr x]
      rfl
    rwa [h2, norm_realInclusion₂] at h1
  have hii : ∀ x : Fin n → ℝ, ‖(realRestriction K x).2 - I‖ < r₀ := fun x =>
    lt_of_le_of_lt ((norm_snd_le (realRestriction K x - (x, I))).trans (hiv x)) hηr
  refine ⟨hii, hiv, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact ⟨realRestriction K, ω, γ, I, hγ, hdio, hinv, fun θ => ⟨I, hIB, hii θ⟩, hIB, hfreq, hiv,
    ⟨x, rfl⟩⟩

end Geometry

section RealTorus

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
  {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε γ : ℝ} {gc : GConsts}

/-- The Cauchy constant at `ρ = s/8`: `n (s/16)⁻¹ η = 16 n η / s`. -/
theorem rt_cauchy_const_eq {s : ℝ} (hs : 0 < s) (η : ℝ) :
    (n : ℝ) * (s / 8 / 2)⁻¹ * η = 16 * n * η / s := by
  field_simp
  ring

/-- The numerical facts about `η₀` used by the proof of `real_torus`: `η₀ < r₀` and
`n (s/16)⁻¹ η₀ ≤ 1/2`, from (s3) of `smallness`. -/
theorem rt_eta0_bounds (hD : Data τ s₀ r₀ B h Lh) (hgc : gc.Pos)
    (hSA : SA τ s₀ r₀ B h Lh gc ε γ) :
    eta0 n τ s₀ r₀ gc ε γ < r₀ ∧
      (n : ℝ) * (stripWidth s₀ / 8 / 2)⁻¹ * eta0 n τ s₀ r₀ gc ε γ ≤ 1 / 2 := by
  have hs := stripWidth_pos hD.s₀_pos
  obtain ⟨-, -, hs3, -⟩ := smallness hD hgc hSA
  refine ⟨?_, ?_⟩
  · have h1 := deltaStar_le_quarter_radius s₀ r₀
    have h2 := hD.r₀_pos
    have h3 : muParam s₀ r₀ ≤ r₀ / 8 := by unfold muParam; linarith
    linarith [hs3.2.2.1]
  · rw [rt_cauchy_const_eq hs]
    exact hs3.2.2.2

/-- Blueprint `step:p4:rt-small`, the full bound on `W_ω = K_ω - K⁰_{I_ω}`: on `T_{s/16}`,
`‖DW_ω‖ ≤ 16 n η₀ / s ≤ 1/2`, by `KAM.Head.rt_small_full` at `ρ = s/8` (`‖W_ω‖ ≤ η₀` is
`KAM.Head.normalize`) and (s3) of `KAM.Head.smallness`. -/
theorem rt_small_normDisp (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hSA : SA τ s₀ r₀ B h Lh gc ε γ) {ω : Fin n → ℝ}
    (hω : ω ∈ OmegaGamma h B τ γ) :
    (∀ θ ∈ complexStrip n (stripWidth s₀ / 16),
      ‖fderiv ℂ (normDisp τ s₀ r₀ B h f gc ε γ ω) θ‖ ≤
        16 * n * eta0 n τ s₀ r₀ gc ε γ / stripWidth s₀) ∧
    16 * n * eta0 n τ s₀ r₀ gc ε γ / stripWidth s₀ ≤ 1 / 2 := by
  have hs := stripWidth_pos hD.s₀_pos
  have hρ : 0 < stripWidth s₀ / 8 := by positivity
  obtain ⟨hKd, -, -, -, -, -, -, hKdisp⟩ := normalize hD hP hgc hSA hω
  refine ⟨fun θ hθ => ?_, (smallness hD hgc.toPos hSA).2.2.1.2.2.2⟩
  have hθ' : θ ∈ complexStrip n (stripWidth s₀ / 8 / 2) := by
    rwa [show stripWidth s₀ / 8 / 2 = stripWidth s₀ / 16 by ring]
  have h1 := rt_small_full hρ hKd hKdisp hθ'
  rwa [rt_cauchy_const_eq hs] at h1

/-- Blueprint `bp:p4:real-torus`: the real restriction `k_ω` of `K_ω` is a KAM torus. -/
theorem real_torus (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hSA : SA τ s₀ r₀ B h Lh gc ε γ) {ω : Fin n → ℝ}
    (hω : ω ∈ OmegaGamma h B τ γ) :
    -- (i)
    IsInvariantLagrangianTorus (realHamiltonian h f) ω
      (realRestriction (normTorus τ s₀ r₀ B h f gc ε γ ω)) ∧
    -- (ii)
    (∀ x : Fin n → ℝ,
      ‖(realRestriction (normTorus τ s₀ r₀ B h f gc ε γ ω) x).2 - invFreq h B ω‖ < r₀) ∧
    -- (iii)
    (invFreq h B ω ∈ B ∧ frequencyMap h (invFreq h B ω) = ω) ∧
    -- (iv)
    (∀ x : Fin n → ℝ, ‖realRestriction (normTorus τ s₀ r₀ B h f gc ε γ ω) x -
      (x, invFreq h B ω)‖ ≤ eta0 n τ s₀ r₀ gc ε γ) ∧
    -- consequence
    Set.range (realRestriction (normTorus τ s₀ r₀ B h f gc ε γ ω)) ⊆
      kamCover h f B r₀ τ (eta0 n τ s₀ r₀ gc ε γ) := by
  have hs₀ := hD.s₀_pos
  have hρ : 0 < stripWidth s₀ / 8 := by have := stripWidth_pos hs₀; positivity
  obtain ⟨hKd, hKp, hKr, hKE, -, hKball, hKder, hKdisp⟩ := normalize hD hP hgc hSA hω
  obtain ⟨hIB, hfreq, -⟩ := (inverse_freq hD).2.2.1 ω hω.1
  obtain ⟨hηr, hsm⟩ := rt_eta0_bounds hD hgc.toPos hSA
  have hε1 := (smallness hD hgc.toPos hSA).1.1
  have hK𝔇 : ∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
      normTorus τ s₀ r₀ B h f gc ε γ ω θ ∈ domainD n s₀ r₀ B := fun θ hθ =>
    hKball θ hθ (Metric.mem_ball_self (half_pos (muParam_pos hs₀ hD.r₀_pos)))
  have hΛ := lagrangian hD hP hε1 hρ hSA.gamma_pos hω.2 hKd hKp hK𝔇 ⟨_, hKder⟩ hKE
  have hsmall := fun x => rt_small hρ hKd hKr hKdisp hsm x
  have hinv : IsInvariantLagrangianTorus (realHamiltonian h f) ω
      (realRestriction (normTorus τ s₀ r₀ B h f gc ε γ ω)) :=
    ⟨(rt_analytic hρ hKd hKp hKr).1, (rt_analytic hρ hKd hKp hKr).2,
      rt_embedding (u := angleReal (normTorus τ s₀ r₀ B h f gc ε γ ω)) (fun _ => rfl)
        (angleReal_add_int hρ hKp hKr) (fun x => (hsmall x).1.differentiableAt)
        (fun x => by rw [(hsmall x).1.fderiv]; exact (hsmall x).2),
      fun x => rt_immersion (hsmall x).2,
      fun x u v => rt_lagrangian hρ hKd hKr hΛ x u v,
      rt_ode (isOpen_domainD n s₀ r₀ B) (h1_differentiableOn hD hP)
        (fun y hy => h1_im_eq_zero hD hP (θ := y.1) (I := y.2) hy) (fun y => rfl) hρ hKd hKr hK𝔇
        hKE⟩
  obtain ⟨hii, hiv, hrange⟩ := rt_cover hρ hKr hSA.gamma_pos hω.2 hinv hIB hfreq hKdisp hηr
  exact ⟨hinv, hii, ⟨hIB, hfreq⟩, hiv, hrange⟩

end RealTorus

end KAM.Head

end
