/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.Averages
public import KAM.Strip.Bridges
public import KAM.Strip.Taylor
public import KAM.Sharp2.TorsionRef
public import KAM.Frozen.Iso.Defs.EnergyAverage
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The step and the new errors (`bp:p2s2hc:struct`, `bp:p2s2hc:error`, `bpI:p2s2hc:errors`)

A step `ΔK` is holomorphic, periodic and real; the new torus is `K₁ = K + ΔK`.

* `linNewError`, `linNewEnergy`: the linearised new errors `Ẽ = E + DX_h(K) ΔK - DΔK ω` and
  `ε̃ = ⟨H∘K⟩ - E₀ + ⟨DH(K) ΔK⟩`, affine in `ΔK`;
* `step_struct` (`bp:p2s2hc:struct`): the structure of the new torus and its ball;
* `invarianceError_step_le` (`bp:p2s2hc:error`): `|E₁| ≤ ℓ_E + (M₂/2) d₀²`, by Taylor;
* `energyAverage_step_le` (`bpI:p2s2hc:errors`(b)): the new energy error, by Taylor for `H`;
* `errDerivMat_step_le` (`bp:p2s2hc:torsion`(e)): Cauchy for the derivative of the new error;
* `ray_step` (`bpI:p2s2hc:errors`(c)): the point `s₁` keeps the margin `ν₁ = ν - d_ω` on the ray.

Soundness never uses that `ΔK` solves the cohomological equations. At `ω = s₁ ω*`,
`linNewError` is the isoenergetic `Ẽ_s` of `bpI:p2s2hc:lin`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology

namespace KAM.Sharp2.Hybrid

open KAM KAM.Torus KAM.Apost KAM.Sharp

variable {n : ℕ}

/-- Definition `bp:p2s2hc:lin`: `Ẽ = E + DX_h(K) ΔK - DΔK ω`. At `ω = s₁ ω*` it is the
isoenergetic `Ẽ_s` of `bpI:p2s2hc:lin`. -/
def linNewError (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (θ : Fin n → ℂ) :
    (Fin n → ℂ) × (Fin n → ℂ) :=
  invarianceError h K ω θ + fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ) (ΔK θ) -
    fderiv ℂ ΔK θ (fun i => (ω i : ℂ))

/-- `bpI:p2s2hc:lin`: the linearised energy error `⟨H∘K⟩ - E₀ + ⟨DH(K) ΔK⟩`. -/
def linNewEnergy (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (E₀ : ℝ) : ℂ :=
  KAM.Iso.energyAverage H K - (E₀ : ℂ) +
    ∫ θ in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
      fderiv ℂ H (K (fun l => (θ l : ℂ))) (ΔK (fun l => (θ l : ℂ)))

/-- A step (Assumption `bp:p2s2hc:standing`(d)): holomorphic on `T_{ρ₀}`, `1`-periodic, real. -/
structure IsStep (ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ρ₀ : ℝ) : Prop where
  holo : DifferentiableOn ℂ ΔK (complexStrip n ρ₀)
  periodic : ∀ θ ∈ complexStrip n ρ₀, ∀ k : Fin n → ℤ, ΔK (θ + fun i => (k i : ℂ)) = ΔK θ
  real : IsRealOnReals ΔK

/-- The strips are nested. -/
theorem strip_le {a b : ℝ} (hab : a ≤ b) : complexStrip n a ⊆ complexStrip n b :=
  fun _ hθ i => (hθ i).trans_le hab

/-- `D(K + ΔK) = DK + DΔK` at a point where both are differentiable. -/
theorem fderiv_add_step {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    (hK : DifferentiableAt ℂ K θ) (hΔ : DifferentiableAt ℂ ΔK θ) :
    fderiv ℂ (K + ΔK) θ = fderiv ℂ K θ + fderiv ℂ ΔK θ :=
  fderiv_add hK hΔ

/-- `L₁ = L + ΔL`. -/
theorem tangentMat_add_step {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    (hK : DifferentiableAt ℂ K θ) (hΔ : DifferentiableAt ℂ ΔK θ) :
    tangentMat (K + ΔK) θ = tangentMat K θ + tangentMat ΔK θ := by
  ext s j
  simp only [Matrix.add_apply, tangentMat_apply, fderiv_add_step hK hΔ,
    _root_.add_apply, map_add, Pi.add_apply]

/-- A ball about a point near `K θ`, inside a ball about `K θ`. -/
theorem ball_add_subset {x w : (Fin n → ℂ) × (Fin n → ℂ)} {μ μ₁ : ℝ} (hμ : ‖w‖ + μ₁ ≤ μ) :
    Metric.ball (x + w) μ₁ ⊆ Metric.ball x μ := by
  intro z hz
  rw [Metric.mem_ball] at hz ⊢
  calc dist z x ≤ dist z (x + w) + dist (x + w) x := dist_triangle _ _ _
    _ < μ₁ + ‖w‖ := add_lt_add_of_lt_of_le hz (by simp [dist_eq_norm])
    _ ≤ μ := by linarith

/-- Lemma `bp:p2s2hc:struct`. -/
theorem step_struct {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ρ₀ ρ₁ μ μ₁ d₀ d₁ ℓ : ℝ}
    (hK : DifferentiableOn ℂ K (complexStrip n ρ₀)) (hKp : IsPrimaryOnStrip K ρ₀)
    (hKr : IsRealOnReals K) (hball : ∀ θ ∈ complexStrip n ρ₀, Metric.ball (K θ) μ ⊆ 𝔅)
    (hDK : ∀ θ ∈ complexStrip n ρ₀, ‖fderiv ℂ K θ‖ ≤ ℓ) (hS : IsStep ΔK ρ₀) (hρ : ρ₁ ≤ ρ₀)
    (hd0 : ∀ θ ∈ complexStrip n ρ₁, ‖ΔK θ‖ ≤ d₀)
    (hd1 : ∀ θ ∈ complexStrip n ρ₁, ‖fderiv ℂ ΔK θ‖ ≤ d₁) (hμ : d₀ + μ₁ ≤ μ) :
    DifferentiableOn ℂ (K + ΔK) (complexStrip n ρ₁) ∧ IsPrimaryOnStrip (K + ΔK) ρ₁ ∧
      IsRealOnReals (K + ΔK) ∧ (∀ θ ∈ complexStrip n ρ₁, Metric.ball ((K + ΔK) θ) μ₁ ⊆ 𝔅) ∧
      ∀ θ ∈ complexStrip n ρ₁, ‖fderiv ℂ (K + ΔK) θ‖ ≤ ℓ + d₁ := by
  have hsub : complexStrip n ρ₁ ⊆ complexStrip n ρ₀ := strip_le hρ
  refine ⟨(hK.mono hsub).add (hS.holo.mono hsub), fun θ hθ k => ?_, fun θ => ?_, fun θ hθ => ?_,
    fun θ hθ => ?_⟩
  · simp only [Pi.add_apply]
    rw [hKp θ (hsub hθ) k, hS.periodic θ (hsub hθ) k]
    abel
  · obtain ⟨z, hz⟩ := hKr θ
    obtain ⟨w, hw⟩ := hS.real θ
    refine ⟨z + w, ?_⟩
    simp only [Pi.add_apply, hz, hw]
    ext i <;> simp
  · refine (ball_add_subset ?_).trans (hball θ (hsub hθ))
    linarith [hd0 θ hθ]
  · have hop := isOpen_complexStrip n ρ₀
    rw [fderiv_add_step (hK.differentiableAt (hop.mem_nhds (hsub hθ)))
      (hS.holo.differentiableAt (hop.mem_nhds (hsub hθ)))]
    exact (norm_add_le _ _).trans (add_le_add (hDK θ (hsub hθ)) (hd1 θ hθ))

/-- The identity of `step:p2s2hc:er-id`: `E₁ = Ẽ + (X_h(K + ΔK) - X_h(K) - DX_h(K) ΔK)`. -/
theorem invarianceError_step_eq {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {θ : Fin n → ℂ}
    (hK : DifferentiableAt ℂ K θ) (hΔ : DifferentiableAt ℂ ΔK θ) :
    invarianceError h (K + ΔK) ω θ = linNewError h K ΔK ω θ +
      (hamiltonianVectorFieldℂ h (K θ + ΔK θ) - hamiltonianVectorFieldℂ h (K θ) -
        fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ) (ΔK θ)) := by
  simp only [linNewError, invarianceError, Pi.add_apply, fderiv_add_step hK hΔ,
    _root_.add_apply]
  abel

/-- The segment `[z, z + w]` lies in `𝔅` when `|w| < μ` and `𝔹_μ(z) ⊆ 𝔅`. -/
theorem segment_add_subset {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {z w : (Fin n → ℂ) × (Fin n → ℂ)} {μ : ℝ} (hball : Metric.ball z μ ⊆ 𝔅) (hw : ‖w‖ < μ) :
    segment ℝ z (z + w) ⊆ 𝔅 := by
  have hμ : 0 < μ := (norm_nonneg w).trans_lt hw
  have hzw : z + w ∈ Metric.ball z μ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  exact ((convex_ball z μ).segment_subset (Metric.mem_ball_self hμ) hzw).trans hball

/-- Lemma `bp:p2s2hc:error`: `|E₁| ≤ ℓ_E + (M₂/2) d₀²` (Taylor, `KAM.taylor_iteratedFDeriv`). -/
theorem invarianceError_step_le {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ω : Fin n → ℝ} {ρ₀ ρ₁ μ M₂ d₀ ℓE : ℝ} (hopen : IsOpen 𝔅)
    (hX : DifferentiableOn ℂ (hamiltonianVectorFieldℂ h) 𝔅)
    (hd2 : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M₂)
    (hK : DifferentiableOn ℂ K (complexStrip n ρ₀)) (hS : IsStep ΔK ρ₀) (hρ : ρ₁ ≤ ρ₀)
    (hball : ∀ θ ∈ complexStrip n ρ₁, Metric.ball (K θ) μ ⊆ 𝔅)
    (hd0 : ∀ θ ∈ complexStrip n ρ₁, ‖ΔK θ‖ ≤ d₀) (hd0μ : d₀ < μ)
    (hlin : ∀ θ ∈ complexStrip n ρ₁, ‖linNewError h K ΔK ω θ‖ ≤ ℓE) :
    ∀ θ ∈ complexStrip n ρ₁, ‖invarianceError h (K + ΔK) ω θ‖ ≤ ℓE + M₂ / 2 * d₀ ^ 2 := by
  intro θ hθ
  have hsub := strip_le (n := n) hρ
  have hop := isOpen_complexStrip n ρ₀
  have hw : ‖ΔK θ‖ < μ := (hd0 θ hθ).trans_lt hd0μ
  have hseg := segment_add_subset (hball θ hθ) hw
  have hT := taylor_iteratedFDeriv hopen hX hd2 hseg
  have hM : 0 ≤ M₂ :=
    (norm_nonneg _).trans (hd2 _ (hball θ hθ (Metric.mem_ball_self ((norm_nonneg _).trans_lt hw))))
  rw [invarianceError_step_eq (hK.differentiableAt (hop.mem_nhds (hsub hθ)))
    (hS.holo.differentiableAt (hop.mem_nhds (hsub hθ)))]
  refine (norm_add_le _ _).trans (add_le_add (hlin θ hθ) (hT.trans ?_))
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hd0 θ hθ) 2) (by positivity)

/-- Lemma `bp:p2s2hc:torsion`(e): Cauchy for the derivative of the new error. -/
theorem errDerivMat_step_le {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K₁ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {ρ₁ δ e₁ : ℝ}
    (hdiff : DifferentiableOn ℂ (invarianceError h K₁ ω) (complexStrip n ρ₁))
    (hE : ∀ θ ∈ complexStrip n ρ₁, ‖invarianceError h K₁ ω θ‖ ≤ e₁) (hδ : 0 < δ) :
    ∀ θ ∈ complexStrip n (ρ₁ - δ), ‖errDerivMat h K₁ ω θ‖ ≤ n * δ⁻¹ * e₁ := by
  intro θ hθ
  rw [errDerivMat, norm_colMat]
  exact (cauchy_strip hdiff hE hδ).2 θ hθ

/-- The Taylor remainder of `H` at a real point of `K`, integrated. -/
theorem norm_energy_remainder_le {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {μ Mh2 d₀R : ℝ} (hopen : IsOpen D) (hH : DifferentiableOn ℂ H D)
    (hd2 : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ Mh2)
    (hball : ∀ θ : Fin n → ℝ, Metric.ball (K fun l => (θ l : ℂ)) μ ⊆ D)
    (hd0 : ∀ θ : Fin n → ℝ, ‖ΔK fun l => (θ l : ℂ)‖ ≤ d₀R) (hd0μ : d₀R < μ) (θ : Fin n → ℝ) :
    ‖H ((K + ΔK) fun l => (θ l : ℂ)) - H (K fun l => (θ l : ℂ)) -
      fderiv ℂ H (K fun l => (θ l : ℂ)) (ΔK fun l => (θ l : ℂ))‖ ≤ Mh2 / 2 * d₀R ^ 2 := by
  have hw : ‖ΔK fun l => (θ l : ℂ)‖ < μ := (hd0 θ).trans_lt hd0μ
  have hT := taylor_iteratedFDeriv hopen hH hd2 (segment_add_subset (hball θ) hw)
  have hM : 0 ≤ Mh2 :=
    (norm_nonneg _).trans (hd2 _ (hball θ (Metric.mem_ball_self ((norm_nonneg _).trans_lt hw))))
  refine hT.trans ?_
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hd0 θ) 2) (by positivity)

/-- Lemma `bpI:p2s2hc:errors`(b): the new energy error (Taylor for `H` at real points). -/
theorem energyAverage_step_le {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {E₀ μ Mh2 d₀R ℓH : ℝ} (hopen : IsOpen D) (hH : DifferentiableOn ℂ H D)
    (hd2 : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ Mh2)
    (hball : ∀ θ : Fin n → ℝ, Metric.ball (K fun l => (θ l : ℂ)) μ ⊆ D)
    (hd0 : ∀ θ : Fin n → ℝ, ‖ΔK fun l => (θ l : ℂ)‖ ≤ d₀R) (hd0μ : d₀R < μ)
    (hint : IntegrableOn (fun θ : Fin n → ℝ => H (K fun l => (θ l : ℂ)))
      (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1))
    (hint₁ : IntegrableOn (fun θ : Fin n → ℝ => H ((K + ΔK) fun l => (θ l : ℂ)))
      (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1))
    (hintD : IntegrableOn (fun θ : Fin n → ℝ =>
      fderiv ℂ H (K fun l => (θ l : ℂ)) (ΔK fun l => (θ l : ℂ)))
      (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1))
    (hlin : ‖linNewEnergy H K ΔK E₀‖ ≤ ℓH) :
    ‖KAM.Iso.energyAverage H (K + ΔK) - (E₀ : ℂ)‖ ≤ ℓH + Mh2 / 2 * d₀R ^ 2 := by
  have e : KAM.Iso.energyAverage H (K + ΔK) - (E₀ : ℂ) = linNewEnergy H K ΔK E₀ +
      torusAverage (fun θ : Fin n → ℝ =>
        H ((K + ΔK) fun l => (θ l : ℂ)) - H (K fun l => (θ l : ℂ)) -
          fderiv ℂ H (K fun l => (θ l : ℂ)) (ΔK fun l => (θ l : ℂ))) := by
    have hd : IntegrableOn (fun θ : Fin n → ℝ =>
        H ((K + ΔK) fun l => (θ l : ℂ)) - H (K fun l => (θ l : ℂ)))
        (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1) := hint₁.sub hint
    simp only [torusAverage]
    rw [integral_sub hd hintD, integral_sub hint₁ hint]
    simp only [linNewEnergy, KAM.Iso.energyAverage]
    abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add hlin (norm_torusAverage_le fun θ _ =>
    norm_energy_remainder_le hopen hH hd2 hball hd0 hd0μ θ))

/-- Lemma `bpI:p2s2hc:errors`(c), step `stepI:p2s2hc:ray`: `1 < s₁ < σ_ω` and the margin
`ν₁ = ν - d_ω` of the new point on the ray. -/
theorem ray_step {ωstar : Fin n → ℝ} {s s₁ σω ν dω : ℝ} (hω : ωstar ≠ 0)
    (hν1 : ν ≤ (s - 1) * ‖ωstar‖) (hν2 : ν ≤ (σω - s) * ‖ωstar‖)
    (hdω : ‖s₁ • ωstar - s • ωstar‖ ≤ dω) (hν : 0 < ν - dω) :
    1 < s₁ ∧ s₁ < σω ∧ ν - dω ≤ (s₁ - 1) * ‖ωstar‖ ∧ ν - dω ≤ (σω - s₁) * ‖ωstar‖ := by
  have hω0 : 0 < ‖ωstar‖ := norm_pos_iff.2 hω
  have e : ‖s₁ • ωstar - s • ωstar‖ = |s₁ - s| * ‖ωstar‖ := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  rw [e] at hdω
  have h1 : (s₁ - s) * ‖ωstar‖ ≤ dω :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hω0.le).trans hdω
  have h2 : (s - s₁) * ‖ωstar‖ ≤ dω := by
    refine (mul_le_mul_of_nonneg_right ?_ hω0.le).trans hdω
    rw [abs_sub_comm]
    exact le_abs_self _
  have h3 : ν - dω ≤ (s₁ - 1) * ‖ωstar‖ := by nlinarith
  have h4 : ν - dω ≤ (σω - s₁) * ‖ωstar‖ := by nlinarith
  refine ⟨?_, ?_, h3, h4⟩
  · have : 0 < (s₁ - 1) * ‖ωstar‖ := hν.trans_le h3
    linarith [(pos_iff_pos_of_mul_pos this).2 hω0]
  · have : 0 < (σω - s₁) * ‖ωstar‖ := hν.trans_le h4
    linarith [(pos_iff_pos_of_mul_pos this).2 hω0]

end KAM.Sharp2.Hybrid

end
