/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Apost.Iteration
public import KAM.Apost.Limit
import KAM.Iso.Apost.ConstantsArith
import KAM.Apost.Exactness
import KAM.Strip.Averages
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Part 2 (isoenergetic iteration): the limit torus and the limit energy

Blueprint nodes `bpI:p2:limit`
(`KAM.Iso.Apost.limit`) and `bpI:p2:energy-limit` (`KAM.Iso.Apost.energy_limit`).

The limits are the explicit `KAM.Iso.Apost.isoLimit` (`K_∞ = lim K_j` on `T_{ρ∞}`, `K` elsewhere)
and `KAM.Iso.Apost.isoSLimit` (`s_∞ = lim s_j`) of the sequence `isoSeq` of `bpI:p2:iteration`.
Both are `limUnder` selectors, so they are landed here together with the theorems that prove the
sequences converge and characterize the definitions as those limits,
exactly as `KAM/Apost` lands `kamLimit` with `limit` (`KAM/Apost/Limit.lean`):

* `limit` proves, under the hypotheses `IterHyp` of `iteration`, that `K_j → isoLimit` uniformly
  with the derivatives, that `s_j → isoSLimit`, and items (a)–(e) of the blueprint;
* `isoLimit_tendsto`, `isoSLimit_tendsto` are the pointwise corollaries, and
  `isoLimit_eq_of_tendsto`, `isoSLimit_eq_of_tendsto` (Hausdorff uniqueness) show that a limit of
  the sequence is `isoLimit θ`, resp. `isoSLimit`; `isoLimit_eq_iff`, `isoSLimit_eq_iff` combine
  both into the characterization `K_∞ θ = z ↔ K_j θ → z`, `s_∞ = l ↔ s_j → l`;
  `isoLimit_of_not_mem` is the value `K` off the strip.

The proof of `limit` mirrors `KAM/Apost/Limit.lean`, whose abstract steps `lim_k`,
`lim_dk`, `lim_holo`, `lim_primary`, `lim_close`, `lim_margins` are reused. New here are the
Cauchy property of the ray parameters `s_j` (`exists_tendsto_of_dist_ray`), the invariance of the
limit at the moving frequency `s_∞ ω*` (`lim_invariance_moving`), and the convergence of the
energy averages under uniform convergence (`tendsto_energyAverage_of_uniform`).

`T_r` is `complexStrip n r`; matrix norms are the operator norms of
`open scoped Matrix.Norms.Operator`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Apost

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear

variable {n : ℕ}

open Classical in
/-- `K_∞ = lim K_j` on `T_{ρ∞}`, `K` elsewhere. -/
def isoLimit (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ωstar : Fin n → ℝ) (E₀ s₀ ρ ρinf : ℝ) : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) :=
  fun θ => if θ ∈ complexStrip n ρinf then
    limUnder atTop (fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ) else K θ

/-- `s_∞ = lim s_j`. -/
def isoSLimit (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ωstar : Fin n → ℝ) (E₀ s₀ ρ ρinf : ℝ) : ℝ :=
  limUnder atTop (fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2)

section Defs

variable (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
  (ωstar : Fin n → ℝ) (E₀ s₀ ρ ρinf : ℝ)

/-- On `T_{ρ∞}`, `K_∞` is the `limUnder` of the sequence. -/
theorem isoLimit_eq {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρinf) :
    isoLimit H K ωstar E₀ s₀ ρ ρinf θ =
      limUnder atTop (fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ) := by
  simp only [isoLimit, hθ, ite_true]

/-- Off `T_{ρ∞}`, `K_∞` is the original `K`. -/
theorem isoLimit_of_not_mem {θ : Fin n → ℂ} (hθ : θ ∉ complexStrip n ρinf) :
    isoLimit H K ωstar E₀ s₀ ρ ρinf θ = K θ := by
  simp only [isoLimit, hθ, ite_false]

/-- Uniqueness: if the sequence `K_j θ` converges to `z` at `θ ∈ T_{ρ∞}`, then `K_∞ θ = z`. -/
theorem isoLimit_eq_of_tendsto {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρinf)
    {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (h : Tendsto (fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ) atTop (𝓝 z)) :
    isoLimit H K ωstar E₀ s₀ ρ ρinf θ = z := by
  rw [isoLimit_eq H K ωstar E₀ s₀ ρ ρinf hθ]
  exact h.limUnder_eq

/-- Uniqueness: if the sequence `s_j` converges to `l`, then `s_∞ = l`. -/
theorem isoSLimit_eq_of_tendsto {l : ℝ}
    (h : Tendsto (fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2) atTop (𝓝 l)) :
    isoSLimit H K ωstar E₀ s₀ ρ ρinf = l :=
  h.limUnder_eq

end Defs

/-! ### The sums `∑ d_j` and `∑ n d_j / δ_j` -/

section Sums

variable {τ M σK σB σT : ℝ} {ρ ρinf γ e : ℝ}

theorem isoDSeq_nonneg (hP : Params n τ M σK σB σT) (hρ : ρinf < ρ) (he : 0 ≤ e) (j : ℕ) :
    0 ≤ isoDSeq n τ M σK σB σT ρ ρinf γ e j := by
  rw [isoDSeq_eq]
  exact mul_nonneg (div_nonneg (zero_le_one.trans (one_le_hatCDelta hP)) (sq_nonneg γ))
    (isoEps_div_nonneg hP hρ he (aExp n τ) j)

/-- `∑ d_j` converges, with `∑ d_j ≤ 2 Ĉ_Δ e/(γ² δ₀^a)` (Lemma `bpI:p2:error-decay` with `j = a`;
the analogue of K's `dSeq_summable_tsum_le`). -/
theorem isoDSeq_summable_tsum_le (hP : Params n τ M σK σB σT) (hρ : ρinf < ρ) (hγ : 0 < γ)
    (he : 0 ≤ e)
    (hq : (2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT * e /
      (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1) :
    Summable (isoDSeq n τ M σK σB σT ρ ρinf γ e) ∧
      ∑' j, isoDSeq n τ M σK σB σT ρ ρinf γ e j ≤
        2 * hatCDelta n τ M σK σB σT * e / (γ ^ 2 * delta0 ρ ρinf ^ aExp n τ) := by
  obtain ⟨hs, ht⟩ := iso_error_decay_sum hP hρ hγ he hq (j := aExp n τ)
    (by linarith [eight_le_aExp hP])
  have hfun : isoDSeq n τ M σK σB σT ρ ρinf γ e = fun j => hatCDelta n τ M σK σB σT / γ ^ 2 *
      (isoEpsSeq n τ M σK σB σT ρ ρinf γ e j / deltaSeq ρ ρinf j ^ aExp n τ) :=
    funext isoDSeq_eq
  have hX : 0 ≤ hatCDelta n τ M σK σB σT / γ ^ 2 :=
    div_nonneg (zero_le_one.trans (one_le_hatCDelta hP)) (sq_nonneg γ)
  have hd : delta0 ρ ρinf ^ aExp n τ ≠ 0 := (Real.rpow_pos_of_pos (delta0_pos hρ) _).ne'
  rw [hfun]
  refine ⟨hs.mul_left _, ?_⟩
  rw [tsum_mul_left]
  calc hatCDelta n τ M σK σB σT / γ ^ 2 *
        ∑' j, isoEpsSeq n τ M σK σB σT ρ ρinf γ e j / deltaSeq ρ ρinf j ^ aExp n τ
      ≤ hatCDelta n τ M σK σB σT / γ ^ 2 * (2 * e / delta0 ρ ρinf ^ aExp n τ) :=
        mul_le_mul_of_nonneg_left ht hX
    _ = 2 * hatCDelta n τ M σK σB σT * e / (γ ^ 2 * delta0 ρ ρinf ^ aExp n τ) := by
        field_simp

/-- `∑ n d_j / δ_j` converges (Lemma `bpI:p2:error-decay` with `j = a + 1`). -/
theorem isoDSeq_div_summable (hP : Params n τ M σK σB σT) (hρ : ρinf < ρ) (hγ : 0 < γ)
    (he : 0 ≤ e)
    (hq : (2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT * e /
      (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1) :
    Summable (fun j => n * isoDSeq n τ M σK σB σT ρ ρinf γ e j / deltaSeq ρ ρinf j) := by
  have hs := (iso_error_decay_sum hP hρ hγ he hq (j := aExp n τ + 1)
    (by linarith [eight_le_aExp hP])).1
  have hfun : (fun j => n * isoDSeq n τ M σK σB σT ρ ρinf γ e j / deltaSeq ρ ρinf j) =
      fun j => n * hatCDelta n τ M σK σB σT / γ ^ 2 *
        (isoEpsSeq n τ M σK σB σT ρ ρinf γ e j / deltaSeq ρ ρinf j ^ (aExp n τ + 1)) :=
    funext fun j => isoDK_term_eq hρ hγ j
  rw [hfun]
  exact hs.mul_left _

/-- The errors `ε_j` tend to `0` (Lemma `bpI:p2:error-decay` with `j = 0`). -/
theorem isoEpsSeq_tendsto_zero (hP : Params n τ M σK σB σT) (hρ : ρinf < ρ) (hγ : 0 < γ)
    (he : 0 ≤ e)
    (hq : (2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT * e /
      (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1) :
    Tendsto (isoEpsSeq n τ M σK σB σT ρ ρinf γ e) atTop (𝓝 0) := by
  have := (iso_error_decay_sum hP hρ hγ he hq (j := 0)
    (by linarith [eight_le_aExp hP])).1.tendsto_atTop_zero
  simpa using this

end Sums

/-! ### The ray parameters -/

section Ray

/-- A sequence `s_j` of ray parameters with `‖s_{j+1} ω* - s_j ω*‖ ≤ d_j`, `d` summable, `ω* ≠ 0`,
converges (it is Cauchy, since `‖s' ω* - s ω*‖ = |s' - s| ‖ω*‖`). -/
theorem exists_tendsto_of_dist_ray {ωstar : Fin n → ℝ} (hω : ωstar ≠ 0) {ss : ℕ → ℝ}
    {d : ℕ → ℝ} (hd : Summable d) (hss : ∀ j, ‖ss (j + 1) • ωstar - ss j • ωstar‖ ≤ d j) :
    ∃ l, Tendsto ss atTop (𝓝 l) := by
  have hpos : 0 < ‖ωstar‖ := norm_pos_iff.2 hω
  have hdist : ∀ j, dist (ss j) (ss (j + 1)) ≤ d j / ‖ωstar‖ := by
    intro j
    have h := hss j
    rw [← sub_smul, norm_smul, Real.norm_eq_abs] at h
    rw [Real.dist_eq, abs_sub_comm, le_div_iff₀ hpos]
    exact h
  exact cauchySeq_tendsto_of_complete
    (cauchySeq_of_summable_dist (Summable.of_nonneg_of_le (fun j => dist_nonneg) hdist
      (hd.div_const _)))

end Ray

/-! ### Invariance of the limit at the moving frequency -/

section Invariance

/-- Step `step:p2:lim-invariance` at the moving frequency: if `K_j θ → L θ`, `DK_j θ → DL θ`,
`s_j → s_∞`, `X_H` is continuous at `L θ`, and `‖E_j θ‖ ≤ ε_j → 0` where `E_j` is the invariance
error of `K_j` at the frequency `s_j ω*`, then the invariance error of `L` at `s_∞ ω*` vanishes. -/
theorem lim_invariance_moving {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ωstar : Fin n → ℝ}
    {Ks : ℕ → (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {L : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ss : ℕ → ℝ} {sl : ℝ} {ε : ℕ → ℝ}
    {θ : Fin n → ℂ} (hX : ContinuousAt (hamiltonianVectorFieldℂ H) (L θ))
    (hKs : Tendsto (fun j => Ks j θ) atTop (𝓝 (L θ)))
    (hDKs : Tendsto (fun j => fderiv ℂ (Ks j) θ) atTop (𝓝 (fderiv ℂ L θ)))
    (hss : Tendsto ss atTop (𝓝 sl))
    (hE : ∀ j, ‖invarianceError H (Ks j) (ss j • ωstar) θ‖ ≤ ε j)
    (hε : Tendsto ε atTop (𝓝 0)) :
    invarianceError H L (sl • ωstar) θ = 0 := by
  have hv : Continuous (fun s : ℝ => (fun i => ((s • ωstar) i : ℂ) : Fin n → ℂ)) := by
    refine continuous_pi fun i => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)
  have hlim : Tendsto (fun j => invarianceError H (Ks j) (ss j • ωstar) θ) atTop
      (𝓝 (invarianceError H L (sl • ωstar) θ)) := by
    have happ : Tendsto (fun j => fderiv ℂ (Ks j) θ (fun i => ((ss j • ωstar) i : ℂ))) atTop
        (𝓝 (fderiv ℂ L θ (fun i => ((sl • ωstar) i : ℂ)))) :=
      ((isBoundedBilinearMap_apply (𝕜 := ℂ)).continuous.tendsto
        (fderiv ℂ L θ, fun i => ((sl • ωstar) i : ℂ))).comp
        (hDKs.prodMk_nhds ((hv.tendsto sl).comp hss))
    unfold invarianceError
    exact (hX.tendsto.comp hKs).sub happ
  exact tendsto_nhds_unique hlim (squeeze_zero_norm hE hε)

end Invariance

/-! ### Energy averages under uniform convergence -/

section Energy

variable {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- If `K_j → L` uniformly on `T_{ρ∞}`, all within `μ/4` of `K`, whose `μ`-balls lie in the open
set `D` where `‖DH‖ ≤ M`, then the energy averages `Ē_H(K_j)` converge to `Ē_H(L)`. -/
theorem tendsto_energyAverage_of_uniform {M μ ρinf : ℝ} (hρinf : 0 < ρinf) (hM0 : 0 ≤ M)
    (hD : IsOpen D) (hH : DifferentiableOn ℂ H D) (hM : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ M)
    (hμ : 0 < μ) {K L : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {Ks : ℕ → (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hball : ∀ θ ∈ complexStrip n ρinf, Metric.ball (K θ) μ ⊆ D)
    (hKs : ∀ j, ∀ θ ∈ complexStrip n ρinf, ‖Ks j θ - K θ‖ ≤ μ / 4)
    (hL : ∀ θ ∈ complexStrip n ρinf, ‖L θ - K θ‖ ≤ μ / 4)
    (hKsd : ∀ j, DifferentiableOn ℂ (Ks j) (complexStrip n ρinf))
    (hLd : DifferentiableOn ℂ L (complexStrip n ρinf))
    (hconv : TendstoUniformlyOn Ks L atTop (complexStrip n ρinf)) :
    Tendsto (fun j => KAM.Iso.energyAverage H (Ks j)) atTop
      (𝓝 (KAM.Iso.energyAverage H L)) := by
  have hmemD : ∀ θ ∈ complexStrip n ρinf, ∀ z, ‖z - K θ‖ < μ → z ∈ D := fun θ hθ z hz =>
    hball θ hθ (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
  have hcont : ∀ F : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ),
      DifferentiableOn ℂ F (complexStrip n ρinf) →
      (∀ θ ∈ complexStrip n ρinf, ‖F θ - K θ‖ ≤ μ / 4) →
      Continuous (fun x : Fin n → ℝ => H (F fun i => (x i : ℂ))) := by
    intro F hF hFK
    have hHF : DifferentiableOn ℂ (fun θ => H (F θ)) (complexStrip n ρinf) :=
      hH.comp hF fun θ hθ => hmemD θ hθ _ (lt_of_le_of_lt (hFK θ hθ) (by linarith))
    exact Exactness.continuous_real_of_differentiableOn hρinf hHF
  have hlip : ∀ θ ∈ complexStrip n ρinf, ∀ a b, ‖a - K θ‖ ≤ μ / 4 → ‖b - K θ‖ ≤ μ / 4 →
      ‖H a - H b‖ ≤ M * ‖a - b‖ := by
    intro θ hθ a b ha hb
    have hmem : ∀ z, ‖z - K θ‖ ≤ μ / 4 → z ∈ Metric.ball (K θ) μ := fun z hz =>
      Metric.mem_ball.2 (by rw [dist_eq_norm]; linarith)
    exact (convex_ball (K θ) μ).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ) (f := H) (C := M)
      (fun x hx => hH.differentiableAt (hD.mem_nhds (hball θ hθ hx)))
      (fun x hx => hM x (hball θ hθ hx)) (hmem b hb) (hmem a ha)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (M + 1) := div_pos hε (by linarith)
  have hlt : M * (ε / (M + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hconv (ε / (M + 1)) hδ] with j hj
  rw [dist_eq_norm]
  have hEq : KAM.Iso.energyAverage H (Ks j) - KAM.Iso.energyAverage H L =
      torusAverage (fun x : Fin n → ℝ =>
        H (Ks j fun i => (x i : ℂ)) - H (L fun i => (x i : ℂ))) := by
    unfold KAM.Iso.energyAverage torusAverage
    rw [MeasureTheory.integral_sub
      (integrableOn_unitCube_of_continuous (hcont _ (hKsd j) (hKs j)))
      (integrableOn_unitCube_of_continuous (hcont _ hLd hL))]
  rw [hEq]
  refine lt_of_le_of_lt (norm_torusAverage_le (A := M * (ε / (M + 1))) ?_) hlt
  intro x _
  have hθ := ofReal_mem_complexStrip hρinf x
  refine (hlip _ hθ _ _ (hKs j _ hθ) (hL _ hθ)).trans ?_
  have h := hj _ hθ
  rw [dist_eq_norm, norm_sub_rev] at h
  exact mul_le_mul_of_nonneg_left h.le hM0

end Energy

/-! ### The limit torus -/

section Limit

variable {τ M σK σB σT σω ν γ : ℝ} {ωstar : Fin n → ℝ}
  {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- The ray parameters converge: `s_j → s_∞`, when `‖s_{j+1} ω* - s_j ω*‖ ≤ d_j` with `d`
summable and `ω* ≠ 0`. -/
theorem tendsto_isoSLimit {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {E₀ s₀ ρ ρinf : ℝ}
    (hω : ωstar ≠ 0) {d : ℕ → ℝ} (hd : Summable d)
    (hsd : ∀ j, ‖(isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).2 • ωstar -
      (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 • ωstar‖ ≤ d j) :
    Tendsto (fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2) atTop
      (𝓝 (isoSLimit H K ωstar E₀ s₀ ρ ρinf)) := by
  obtain ⟨l, hl⟩ := exists_tendsto_of_dist_ray (ss := fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2)
    hω hd hsd
  rw [isoSLimit_eq_of_tendsto H K ωstar E₀ s₀ ρ ρinf hl]
  exact hl

/-- `bpI:p2:limit` (a)–(e). -/
theorem limit (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ) {E₀ ρ ρinf μ e s₀ : ℝ}
    (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hμ : 0 < μ) {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : IterHyp σK σB σT σω ν D H ωstar E₀ ρ μ e s₀ K) (he1 : e ≤ 1)
    (hsmall : hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1) :
    (TendstoUniformlyOn (fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1)
        (isoLimit H K ωstar E₀ s₀ ρ ρinf) atTop (complexStrip n ρinf) ∧
      TendstoUniformlyOn (fun j θ => fderiv ℂ (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ)
        (fderiv ℂ (isoLimit H K ωstar E₀ s₀ ρ ρinf)) atTop (complexStrip n ρinf) ∧
      Tendsto (fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2) atTop
        (𝓝 (isoSLimit H K ωstar E₀ s₀ ρ ρinf)) ∧
      DifferentiableOn ℂ (isoLimit H K ωstar E₀ s₀ ρ ρinf) (complexStrip n ρinf) ∧
      IsPrimaryOnStrip (isoLimit H K ωstar E₀ s₀ ρ ρinf) ρinf ∧
      IsRealOnReals (isoLimit H K ωstar E₀ s₀ ρ ρinf)) ∧
    ((∀ θ ∈ complexStrip n ρinf, ‖isoLimit H K ωstar E₀ s₀ ρ ρinf θ - K θ‖ ≤
        2 * hatCDelta n τ M σK σB σT * e / (γ ^ 2 * delta0 ρ ρinf ^ aExp n τ)) ∧
      ‖isoSLimit H K ωstar E₀ s₀ ρ ρinf • ωstar - s₀ • ωstar‖ ≤
        2 * hatCDelta n τ M σK σB σT * e / (γ ^ 2 * delta0 ρ ρinf ^ aExp n τ) ∧
      2 * hatCDelta n τ M σK σB σT * e / (γ ^ 2 * delta0 ρ ρinf ^ aExp n τ) ≤ μ / 4 ∧
      2 * hatCDelta n τ M σK σB σT * e / (γ ^ 2 * delta0 ρ ρinf ^ aExp n τ) ≤ ν / 2) ∧
    (1 < isoSLimit H K ωstar E₀ s₀ ρ ρinf ∧ isoSLimit H K ωstar E₀ s₀ ρ ρinf < σω ∧
      ν / 2 ≤ rayMargin σω ωstar (isoSLimit H K ωstar E₀ s₀ ρ ρinf)) ∧
    (∀ θ ∈ complexStrip n ρinf, Metric.ball (isoLimit H K ωstar E₀ s₀ ρ ρinf θ) (μ / 2) ⊆ D ∧
      ‖fderiv ℂ (isoLimit H K ωstar E₀ s₀ ρ ρinf) θ‖ ≤ σK - μ / 2) ∧
    (∀ θ ∈ complexStrip n ρinf, invarianceError H (isoLimit H K ωstar E₀ s₀ ρ ρinf)
      (isoSLimit H K ωstar E₀ s₀ ρ ρinf • ωstar) θ = 0) := by
  have hP := hS.toParams
  have hγ := hS.gamma_pos
  have hν := hS.ν_pos
  have hρ0 : 0 < ρ := hρinf.trans hρ
  have h00 : (0 : Fin n → ℂ) ∈ complexStrip n ρ := fun i => by simpa using hρ0
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hK.error_le 0 h00)
  have hd0 := delta0_pos hρ
  have hq := Arith.iso_error_decay_hyp hγ hd0 he0 hsmall
  have st0 : IsoStage n τ M σK σB σT D H ωstar E₀ γ ρ ρinf μ e s₀ K 0 :=
    iso_stage_zero hρ0 hμ he0 he1 hK
  -- `γ ≤ Θ`, from the frequency estimate for `(K, s₀)`
  obtain ⟨hγω, hω⟩ := st0.adm.freq hS
  have hγΘ : γ ≤ Theta n M σK σB σT := hγω.trans hω
  obtain ⟨-, hit⟩ := iteration hS hρinf hρ hμ hK he1 hsmall
  -- the strips
  have hsub : ∀ j, complexStrip n ρinf ⊆ complexStrip n (rSeq ρ ρinf j) := fun j =>
    Triangular.strip_mono
      (((schedule hρinf hρ).2.1).trans ((schedule hρinf hρ).2.2 j).2.1.le)
  have hsubρ : complexStrip n ρinf ⊆ complexStrip n ρ := Triangular.strip_mono hρ.le
  -- the summable bounds
  obtain ⟨hdsum, htsum⟩ := isoDSeq_summable_tsum_le hP hρ hγ he0 hq
  have hdksum := isoDSeq_div_summable hP hρ hγ he0 hq
  -- differences on the strip `T_{ρ∞}`
  have hdiff : ∀ j, ∀ θ ∈ complexStrip n ρinf,
      ‖(isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).1 θ - (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ‖ ≤
        isoDSeq n τ M σK σB σT ρ ρinf γ e j := fun j θ hθ =>
    ((hit j).2.2.2.2.2.1 θ (hsub (j + 1) hθ)).1
  have hddiff : ∀ j, ∀ θ ∈ complexStrip n ρinf,
      ‖fderiv ℂ (isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).1 θ -
          fderiv ℂ (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ‖ ≤
        n * isoDSeq n τ M σK σB σT ρ ρinf γ e j / deltaSeq ρ ρinf j := fun j θ hθ =>
    ((hit j).2.2.2.2.2.1 θ (hsub (j + 1) hθ)).2
  have hsdiff : ∀ j, ‖(isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).2 • ωstar -
      (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 • ωstar‖ ≤ isoDSeq n τ M σK σB σT ρ ρinf γ e j :=
    fun j => (hit j).2.2.2.2.2.2
  have hhol : ∀ j, DifferentiableOn ℂ (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1
      (complexStrip n ρinf) := fun j => (hit j).1.1.holo.mono (hsub j)
  have hprim : ∀ j, IsPrimaryOnStrip (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 ρinf := fun j θ hθ k =>
    (hit j).1.1.primary θ (hsub j hθ) k
  have hreal : ∀ j, IsRealOnReals (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 := fun j =>
    (hit j).1.1.real
  -- steps `lim-k`, `lim-dk`, `lim-holo`, `lim-primary`
  obtain ⟨hconv, hpt, hLG⟩ := lim_k (Ks := fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1)
    hdsum hdiff (fun θ hθ => isoLimit_eq H K ωstar E₀ s₀ ρ ρinf hθ)
  obtain ⟨Λ, hΛ⟩ := lim_dk (Ks := fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1) hdksum hddiff
  obtain ⟨hholo, hconvd⟩ := lim_holo (Ks := fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1)
    hhol hpt hΛ
  have hdpt : ∀ θ ∈ complexStrip n ρinf,
      Tendsto (fun j => fderiv ℂ (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ) atTop
        (𝓝 (fderiv ℂ (isoLimit H K ωstar E₀ s₀ ρ ρinf) θ)) := fun θ hθ => hconvd.tendsto_at hθ
  have hpr := lim_primary (Ks := fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1) hρinf hpt hprim
    hreal
  -- step `lim-close`
  have hclose : ∀ θ ∈ complexStrip n ρinf, ‖isoLimit H K ωstar E₀ s₀ ρ ρinf θ - K θ‖ ≤
      2 * hatCDelta n τ M σK σB σT * e / (γ ^ 2 * delta0 ρ ρinf ^ aExp n τ) := fun θ hθ =>
    ((lim_close (Ks := fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1) hdsum hdiff hLG) θ hθ).trans
      htsum
  obtain ⟨hclμ, hclν⟩ := Arith.iso_closeness_le hP hγ hγΘ hd0 (delta0_le_one ρ ρinf) he0 hμ hν
    hsmall
  -- the ray parameters
  have hs := tendsto_isoSLimit (H := H) (K := K) (E₀ := E₀) (s₀ := s₀) (ρ := ρ) (ρinf := ρinf)
    hS.ωstar_ne hdsum hsdiff
  have hsd : ‖isoSLimit H K ωstar E₀ s₀ ρ ρinf • ωstar - s₀ • ωstar‖ ≤
      2 * hatCDelta n τ M σK σB σT * e / (γ ^ 2 * delta0 ρ ρinf ^ aExp n τ) := by
    have hD : ∀ j, ‖(isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 • ωstar - s₀ • ωstar‖ ≤
        2 * hatCDelta n τ M σK σB σT * e / (γ ^ 2 * delta0 ρ ρinf ^ aExp n τ) := fun j =>
      ((hit j).2.1.2.2.2.1).trans
        ((hdsum.sum_le_tsum (Finset.range j) fun i _ => isoDSeq_nonneg hP hρ he0 i).trans htsum)
    exact le_of_tendsto ((hs.smul_const ωstar).sub_const (s₀ • ωstar)).norm
      (Eventually.of_forall hD)
  obtain ⟨hs1, hs2, hs3⟩ := iso_ray_step hS hK.margin hsd hclν
  -- step `lim-margins`
  have hmarg : ∀ θ ∈ complexStrip n ρinf,
      Metric.ball (isoLimit H K ωstar E₀ s₀ ρ ρinf θ) (μ / 2) ⊆ D := fun θ hθ =>
    lim_margins ((hclose θ hθ).trans hclμ) (hK.ball_sub θ (hsubρ hθ))
  have hdk : ∀ θ ∈ complexStrip n ρinf,
      ‖fderiv ℂ (isoLimit H K ωstar E₀ s₀ ρ ρinf) θ‖ ≤ σK - μ / 2 := by
    intro θ hθ
    refine le_of_tendsto (hdpt θ hθ).norm (Eventually.of_forall fun j => ?_)
    exact ((hit j).2.2.1.1 θ (hsub j hθ)).trans (hit j).2.2.1.2
  -- step `lim-invariance` at the moving frequency
  have hεz := isoEpsSeq_tendsto_zero hP hρ hγ he0 hq
  have hXd : DifferentiableOn ℂ (hamiltonianVectorFieldℂ H) D :=
    differentiableOn_ham (hS.setting (le_refl 1)).toStanding
  refine ⟨⟨hconv, hconvd, hs, hholo, hpr.1, hpr.2⟩, ⟨hclose, hsd, hclμ, hclν⟩,
    ⟨hs1, hs2, by linarith⟩, fun θ hθ => ⟨hmarg θ hθ, hdk θ hθ⟩, fun θ hθ => ?_⟩
  have hmem : isoLimit H K ωstar E₀ s₀ ρ ρinf θ ∈ D :=
    hmarg θ hθ (Metric.mem_ball_self (half_pos hμ))
  exact lim_invariance_moving (Ks := fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1)
    (ss := fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2)
    (ε := isoEpsSeq n τ M σK σB σT ρ ρinf γ e)
    ((hXd.differentiableAt (hS.isOpen.mem_nhds hmem)).continuousAt) (hpt θ hθ) (hdpt θ hθ) hs
    (fun j => (hit j).1.1.error_le θ (hsub j hθ)) hεz

/-- The pointwise convergence `K_j θ → K_∞ θ` on `T_{ρ∞}` (the first part of `limit`). -/
theorem isoLimit_tendsto (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ)
    {E₀ ρ ρinf μ e s₀ : ℝ} (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hμ : 0 < μ)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : IterHyp σK σB σT σω ν D H ωstar E₀ ρ μ e s₀ K) (he1 : e ≤ 1)
    (hsmall : hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρinf) :
    Tendsto (fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ) atTop
      (𝓝 (isoLimit H K ωstar E₀ s₀ ρ ρinf θ)) :=
  (limit hS hρinf hρ hμ hK he1 hsmall).1.1.tendsto_at hθ

/-- The convergence `s_j → s_∞` (the third part of `limit`). -/
theorem isoSLimit_tendsto (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ)
    {E₀ ρ ρinf μ e s₀ : ℝ} (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hμ : 0 < μ)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : IterHyp σK σB σT σω ν D H ωstar E₀ ρ μ e s₀ K) (he1 : e ≤ 1)
    (hsmall : hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1) :
    Tendsto (fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2) atTop
      (𝓝 (isoSLimit H K ωstar E₀ s₀ ρ ρinf)) :=
  (limit hS hρinf hρ hμ hK he1 hsmall).1.2.2.1

/-- Characterization of `isoLimit`: under the hypotheses of `iteration`, `K_∞ θ = z` on `T_{ρ∞}`
exactly when `K_j θ → z`. -/
theorem isoLimit_eq_iff (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ)
    {E₀ ρ ρinf μ e s₀ : ℝ} (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hμ : 0 < μ)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : IterHyp σK σB σT σω ν D H ωstar E₀ ρ μ e s₀ K) (he1 : e ≤ 1)
    (hsmall : hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρinf) {z : (Fin n → ℂ) × (Fin n → ℂ)} :
    isoLimit H K ωstar E₀ s₀ ρ ρinf θ = z ↔
      Tendsto (fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ) atTop (𝓝 z) := by
  refine ⟨fun h => h ▸ isoLimit_tendsto hS hρinf hρ hμ hK he1 hsmall hθ, fun h => ?_⟩
  exact isoLimit_eq_of_tendsto H K ωstar E₀ s₀ ρ ρinf hθ h

/-- Characterization of `isoSLimit`: under the hypotheses of `iteration`, `s_∞ = l` exactly when
`s_j → l`. -/
theorem isoSLimit_eq_iff (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ)
    {E₀ ρ ρinf μ e s₀ : ℝ} (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hμ : 0 < μ)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : IterHyp σK σB σT σω ν D H ωstar E₀ ρ μ e s₀ K) (he1 : e ≤ 1)
    (hsmall : hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1)
    {l : ℝ} :
    isoSLimit H K ωstar E₀ s₀ ρ ρinf = l ↔
      Tendsto (fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2) atTop (𝓝 l) := by
  refine ⟨fun h => h ▸ isoSLimit_tendsto hS hρinf hρ hμ hK he1 hsmall, fun h => ?_⟩
  exact isoSLimit_eq_of_tendsto H K ωstar E₀ s₀ ρ ρinf h

/-- `bpI:p2:energy-limit`. -/
theorem energy_limit (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ) {E₀ ρ ρinf μ e s₀ : ℝ}
    (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hμ : 0 < μ) {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : IterHyp σK σB σT σω ν D H ωstar E₀ ρ μ e s₀ K) (he1 : e ≤ 1)
    (hsmall : hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1) :
    KAM.Iso.energyAverage H (isoLimit H K ωstar E₀ s₀ ρ ρinf) = (E₀ : ℂ) ∧
    Tendsto (fun j => KAM.Iso.energyAverage H (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1) atTop
      (𝓝 (KAM.Iso.energyAverage H (isoLimit H K ωstar E₀ s₀ ρ ρinf))) := by
  have hP := hS.toParams
  have hγ := hS.gamma_pos
  have hρ0 : 0 < ρ := hρinf.trans hρ
  have h00 : (0 : Fin n → ℂ) ∈ complexStrip n ρ := fun i => by simpa using hρ0
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hK.error_le 0 h00)
  have hq := Arith.iso_error_decay_hyp hγ (delta0_pos hρ) he0 hsmall
  obtain ⟨-, hit⟩ := iteration hS hρinf hρ hμ hK he1 hsmall
  obtain ⟨⟨hconv, -, -, hholo, -, -⟩, ⟨hclose, -, hclμ, -⟩, -⟩ :=
    limit hS hρinf hρ hμ hK he1 hsmall
  have hsub : ∀ j, complexStrip n ρinf ⊆ complexStrip n (rSeq ρ ρinf j) := fun j =>
    Triangular.strip_mono
      (((schedule hρinf hρ).2.1).trans ((schedule hρinf hρ).2.2 j).2.1.le)
  have hsubρ : complexStrip n ρinf ⊆ complexStrip n ρ := Triangular.strip_mono hρ.le
  have hT := tendsto_energyAverage_of_uniform hρinf hP.M_pos.le hS.isOpen hS.holo
    (fun z hz => (hS.bounds z hz).1) hμ (K := K)
    (Ks := fun j => (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1)
    (fun θ hθ => hK.ball_sub θ (hsubρ hθ))
    (fun j θ hθ => ((hit j).2.1.2.2.1 θ (hsub j hθ)).trans (hit j).2.1.1)
    (fun θ hθ => (hclose θ hθ).trans hclμ)
    (fun j => (hit j).1.1.holo.mono (hsub j)) hholo hconv
  have hεz := isoEpsSeq_tendsto_zero hP hρ hγ he0 hq
  have h0 : Tendsto (fun j => KAM.Iso.energyAverage H (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1) atTop
      (𝓝 (E₀ : ℂ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun j => (hit j).1.1.energy_le) hεz
  exact ⟨tendsto_nhds_unique hT h0, hT⟩

end Limit

end KAM.Iso.Apost

end
