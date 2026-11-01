/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Plane
public import KAM.Planetary.Exponential.Lift
public import KAM.Planetary.Hamiltonian.Algebra
public import KAM.Planetary.SecularForm.Symmetry

/-!
# Rotation invariance of LP's chart, of `H ∘ Ψ` and of the certificate bounds

Design `docs/campaign/design/HD11964-PILOT.md` §6.3 (`coverOk` "modulo rotation") and §9.

The simultaneous rotation `chartRot θ` of LP's Poincaré chart (every mean longitude `λ_i ↦ λ_i + θ`,
every `(ξ_i, η_i) ↦ rot θ (ξ_i, η_i)`, the actions `Λ` fixed) is mapped by the chart to the rotation
of every body vector (`poincareProd_chartRot`, from the per-planet identity `poincare_rotate` of the
secular-form symmetries). The moving Hamiltonian is invariant under that rotation, so
`H ∘ Ψ` is invariant (`liftChartHam_chartRot`). The derivative of `chartRot θ` is symplectic, hence
the chart field is equivariant and the bracket `dF (X_H)` of a rotation-invariant `F` is invariant
(`fderiv_apply_hamiltonianVectorField_comp`). Consequently a bound on `|dF (X_H)|` (or on the range
of `F - Λ`) over a set `S` of representatives extends to every chart point that rotates into `S`
(`bracket_bound_of_rotation`, `range_bound_of_rotation`): the cover need only cover the region
modulo rotation (e.g. `η_b = 0`).

## Main results

* `hamiltonianVectorField_comp`, `fderiv_apply_hamiltonianVectorField_comp`: equivariance under a
  map with symplectic surjective derivative, for invariant Hamiltonians and observables.
* `chartRot`, `chartRotCLM`: the chart rotation and its linear part; `chartRotCLM_symplectic`.
* `poincareProd_chartRot`, `liftChartHam_chartRot`, `chartRot_mem_chartSafe`, `fast_chartRot`,
  `chartAMD_chartRot`.
* `bracket_bound_of_rotation`, `range_bound_of_rotation`.
-/

@[expose] public noncomputable section

open Set Filter Topology KAM KAM.Kepler KAM.Planetary

namespace KAM.Application.LambdaDrift

/-! ### Hamiltonian vector fields under maps with symplectic derivative -/

section Equivariance

variable {d : ℕ}

private theorem symplecticForm_sub_right' (u v w : Phase d) :
    symplecticForm u (v - w) = symplecticForm u v - symplecticForm u w := by
  simp only [symplecticForm, ← Finset.sum_sub_distrib, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Equivariance of the Hamiltonian vector field.** If `R` has the symplectic surjective
derivative `A` at `w`, `H` is differentiable at `R w` and `H ∘ R = H` near `w`, then
`X_H (R w) = A (X_H w)`. -/
theorem hamiltonianVectorField_comp {H : Phase d → ℝ} {R : Phase d → Phase d}
    {A : Phase d →L[ℝ] Phase d} (hA : ∀ u v, symplecticForm (A u) (A v) = symplecticForm u v)
    (hAs : Function.Surjective A) {w : Phase d} (hR : HasFDerivAt R A w)
    (hH : DifferentiableAt ℝ H (R w)) (hinv : (fun x => H (R x)) =ᶠ[𝓝 w] H) :
    hamiltonianVectorField H (R w) = A (hamiltonianVectorField H w) := by
  have hcomp : fderiv ℝ (fun x => H (R x)) w = (fderiv ℝ H (R w)).comp A :=
    (hH.hasFDerivAt.comp w hR).fderiv
  have heq : fderiv ℝ (fun x => H (R x)) w = fderiv ℝ H w := hinv.fderiv_eq
  rw [← sub_eq_zero]
  refine eq_zero_of_symplecticForm_right fun u => ?_
  obtain ⟨v, rfl⟩ := hAs u
  rw [symplecticForm_sub_right', symplecticForm_hamiltonianVectorField, hA,
    symplecticForm_hamiltonianVectorField]
  have : fderiv ℝ H (R w) (A v) = fderiv ℝ H w v := by
    rw [← heq, hcomp]
    rfl
  rw [this, sub_self]

/-- **Invariance of the bracket.** Under the hypotheses of `hamiltonianVectorField_comp`, an
observable `F` differentiable at `R w` with `F ∘ R = F` near `w` has the same derivative along the
Hamiltonian field at `R w` as at `w`. -/
theorem fderiv_apply_hamiltonianVectorField_comp {F H : Phase d → ℝ} {R : Phase d → Phase d}
    {A : Phase d →L[ℝ] Phase d} (hA : ∀ u v, symplecticForm (A u) (A v) = symplecticForm u v)
    (hAs : Function.Surjective A) {w : Phase d} (hR : HasFDerivAt R A w)
    (hH : DifferentiableAt ℝ H (R w)) (hinv : (fun x => H (R x)) =ᶠ[𝓝 w] H)
    (hF : DifferentiableAt ℝ F (R w)) (hFinv : (fun x => F (R x)) =ᶠ[𝓝 w] F) :
    fderiv ℝ F (R w) (hamiltonianVectorField H (R w)) =
      fderiv ℝ F w (hamiltonianVectorField H w) := by
  rw [hamiltonianVectorField_comp hA hAs hR hH hinv]
  have hcomp : fderiv ℝ (fun x => F (R x)) w = (fderiv ℝ F (R w)).comp A :=
    (hF.hasFDerivAt.comp w hR).fderiv
  rw [← hFinv.fderiv_eq, hcomp]
  rfl

end Equivariance

/-! ### The chart rotation -/

section ChartRotation

variable {n : ℕ}

/-- The linear part of the chart rotation: `(ξ_i, η_i) ↦ rot θ (ξ_i, η_i)`, angles and actions
fixed. -/
def chartRotLin (θ : ℝ) (w : Phase (n + n)) : Phase (n + n) :=
  assemble (fast w.2) (fast w.1)
    (fun i => Real.sin θ * slow w.1 i + Real.cos θ * slow w.2 i)
    (fun i => Real.cos θ * slow w.1 i - Real.sin θ * slow w.2 i)

/-- **The chart rotation by `θ`** (design §9): `λ_i ↦ λ_i + θ`, `(ξ_i, η_i) ↦ rot θ (ξ_i, η_i)`,
`Λ_i` fixed, for every planet. -/
def chartRot (θ : ℝ) (w : Phase (n + n)) : Phase (n + n) :=
  assemble (fast w.2) (fun i => fast w.1 i + θ)
    (fun i => Real.sin θ * slow w.1 i + Real.cos θ * slow w.2 i)
    (fun i => Real.cos θ * slow w.1 i - Real.sin θ * slow w.2 i)

private theorem fast_append (a b : Fin n → ℝ) : fast (Fin.append a b) = a :=
  funext fun i => Fin.append_left a b i

private theorem slow_append (a b : Fin n → ℝ) : slow (Fin.append a b) = b :=
  funext fun i => by simp [slow]

/-- The linear part of the chart rotation, as a continuous linear map. -/
def chartRotCLM (θ : ℝ) : Phase (n + n) →L[ℝ] Phase (n + n) :=
  LinearMap.toContinuousLinearMap
    { toFun := chartRotLin θ
      map_add' := fun u v => by
        refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
        refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
        simp [chartRotLin, assemble, fast, slow] <;> ring
      map_smul' := fun c u => by
        refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
        refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
        simp [chartRotLin, assemble, fast, slow] <;> ring }

theorem chartRotCLM_apply (θ : ℝ) (w : Phase (n + n)) : chartRotCLM θ w = chartRotLin θ w := rfl

/-- `chartRot θ` is the affine map `chartRotCLM θ + (θ on the angles)`. -/
theorem chartRot_eq (θ : ℝ) :
    chartRot θ = fun w : Phase (n + n) =>
      chartRotCLM θ w + assemble (0 : Fin n → ℝ) (fun _ => θ) 0 0 := by
  funext w
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
  simp [chartRot, chartRotCLM_apply, chartRotLin, assemble]

theorem hasFDerivAt_chartRot (θ : ℝ) (w : Phase (n + n)) :
    HasFDerivAt (chartRot θ) (chartRotCLM θ) w := by
  rw [chartRot_eq]
  exact (chartRotCLM θ).hasFDerivAt.add_const _

theorem planetBlock_chartRot (θ : ℝ) (w : Phase (n + n)) (i : Fin n) :
    planetBlock (chartRot θ w) i = rotBlock θ (planetBlock w i) := by
  rw [chartRot, SecularForm.planetBlock_assemble]
  simp [rotBlock, rot, planetBlock]

/-- The derivative of the chart rotation is symplectic. -/
theorem chartRotCLM_symplectic (θ : ℝ) (u v : Phase (n + n)) :
    symplecticForm (chartRotCLM θ u) (chartRotCLM θ v) = symplecticForm u v := by
  rw [symplecticForm_blocks, symplecticForm_blocks]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [chartRotCLM_apply, chartRotLin, SecularForm.planetBlock_assemble]
  simp only [planetBlock, symplecticForm, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  linear_combination (slow u.2 i * slow v.1 i - slow u.1 i * slow v.2 i) *
    Real.sin_sq_add_cos_sq θ

theorem chartRotCLM_surjective (θ : ℝ) : Function.Surjective (chartRotCLM (n := n) θ) :=
  (bijective_of_symplectic one_ne_zero (A := chartRotCLM θ) fun u v => by
    rw [one_mul]; exact chartRotCLM_symplectic θ u v).2

theorem fast_chartRot (θ : ℝ) (w : Phase (n + n)) : fast (chartRot θ w).2 = fast w.2 := by
  simp [chartRot, assemble, fast_append]

theorem chartAMD_chartRot (θ : ℝ) (w : Phase (n + n)) : chartAMD (chartRot θ w) = chartAMD w := by
  unfold chartAMD
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [chartRot, assemble, slow_append]
  linear_combination (slow w.1 i ^ 2 + slow w.2 i ^ 2) / 2 * Real.sin_sq_add_cos_sq θ

theorem rotBlock_mem_poincareDom (θ : ℝ) {w : Phase 2} (hw : w ∈ poincareDom) :
    rotBlock θ w ∈ poincareDom := by
  obtain ⟨h1, h2⟩ := hw
  have hΓ : poincareGamma (rotBlock θ w) = poincareGamma w := by
    simp only [poincareGamma, rotBlock, rot, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (w.1 1 ^ 2 + w.2 1 ^ 2) / 2 * Real.sin_sq_add_cos_sq θ
  have h0 : (rotBlock θ w).2 0 = w.2 0 := by simp [rotBlock]
  exact ⟨by rw [h0]; exact h1, by rw [hΓ, h0]; exact h2⟩

theorem chartRot_mem_poincareProdDom (θ : ℝ) {w : Phase (n + n)} (hw : w ∈ poincareProdDom n) :
    chartRot θ w ∈ poincareProdDom n := fun i => by
  rw [planetBlock_chartRot]
  exact rotBlock_mem_poincareDom θ (hw i)

/-- **The chart is rotation-equivariant**: `Ψ (chartRot θ w)` rotates every body vector of `Ψ w`. -/
theorem poincareProd_chartRot (m : Fin n → ℝ) (κ θ : ℝ) {w : Phase (n + n)}
    (hw : w ∈ poincareProdDom n) :
    poincareProd m κ (chartRot θ w) = SecularForm.rotatePhysical θ (poincareProd m κ w) := by
  rw [poincareProd_eq_ofPlanets, poincareProd_eq_ofPlanets]
  unfold SecularForm.rotatePhysical
  rw [SecularForm.ofPlanets_map (rot θ) (rot θ)]
  congr 1
  funext i
  rw [planetBlock_chartRot]
  exact poincare_rotate θ (hw i)

private theorem planeSq_rot'' (g : ℝ) (v : Fin 2 → ℝ) : planeSq (rot g v) = planeSq v := by
  have h := planeLength_rot g v
  unfold planeLength at h
  have h1 : 0 ≤ planeSq (rot g v) := by unfold planeSq; positivity
  have h2 : 0 ≤ planeSq v := by unfold planeSq; positivity
  rw [← Real.sq_sqrt h1, ← Real.sq_sqrt h2, h]

private theorem rot_sub'' (g : ℝ) (v w : Fin 2 → ℝ) : rot g v - rot g w = rot g (v - w) := by
  ext i; fin_cases i <;> simp [rot] <;> ring

/-- The moving Hamiltonian is invariant under the rotation of every body vector. -/
theorem movingHamiltonian_rotatePhysical (G m0 : ℝ) (m : Fin n → ℝ) (μ θ : ℝ)
    (z : Phase (n * 2)) :
    movingHamiltonian G m0 m μ (SecularForm.rotatePhysical θ z) = movingHamiltonian G m0 m μ z := by
  unfold movingHamiltonian SecularForm.rotatePhysical
  simp only [bodyVector_ofBodies, planeSq_rot'', planeLength_rot, planeDot_rot, rot_sub'']

/-- **`H ∘ Ψ` is rotation-invariant** on the chart domain. -/
theorem liftChartHam_chartRot (ν : Fin n → ℝ) (μ θ : ℝ) {w : Phase (n + n)}
    (hw : w ∈ poincareProdDom n) : liftChartHam ν μ (chartRot θ w) = liftChartHam ν μ w := by
  unfold liftChartHam
  rw [poincareProd_chartRot ν 1 θ hw, movingHamiltonian_rotatePhysical]

theorem chartRot_mem_chartSafe (ν : Fin n → ℝ) (θ : ℝ) {w : Phase (n + n)}
    (hw : w ∈ chartSafe ν) : chartRot θ w ∈ chartSafe ν := by
  refine ⟨chartRot_mem_poincareProdDom θ hw.1, ?_⟩
  have hc : NoCollision (poincareProd ν 1 w).1 := hw.2
  show NoCollision (poincareProd ν 1 (chartRot θ w)).1
  rw [poincareProd_chartRot ν 1 θ hw.1]
  unfold SecularForm.rotatePhysical
  unfold NoCollision at hc ⊢
  obtain ⟨hc1, hc2⟩ := hc
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp only [bodyVector_ofBodies, planeLength_rot]
    exact hc1 i
  · simp only [bodyVector_ofBodies, rot_sub'', planeLength_rot]
    exact hc2 i j hij

/-- **Rotation reduction of the bracket bound** (design §6.3, `coverOk` modulo rotation). Let `F`
be differentiable on an open `O ⊆ chartSafe ν`, with `O` and `F` invariant under every chart
rotation. A bound `|dF (X_H)| ≤ η` on a set `S` holds at every point of `R ⊆ O` that some rotation
maps into `S`. -/
theorem bracket_bound_of_rotation {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (μ : ℝ)
    {F : Phase (n + n) → ℝ} {O : Set (Phase (n + n))} (hO : IsOpen O) (hOs : O ⊆ chartSafe ν)
    (hF : DifferentiableOn ℝ F O)
    (hFrot : ∀ θ, ∀ w ∈ O, chartRot θ w ∈ O ∧ F (chartRot θ w) = F w)
    {R S : Set (Phase (n + n))} (hRO : R ⊆ O) (hRS : ∀ w ∈ R, ∃ θ, chartRot θ w ∈ S) {η : ℝ}
    (hS : ∀ w ∈ S, |fderiv ℝ F w (hamiltonianVectorField (liftChartHam ν μ) w)| ≤ η) :
    ∀ w ∈ R, |fderiv ℝ F w (hamiltonianVectorField (liftChartHam ν μ) w)| ≤ η := by
  intro w hw
  obtain ⟨θ, hθ⟩ := hRS w hw
  have hwO := hRO hw
  have hrO := (hFrot θ w hwO).1
  have hdomO : ∀ᶠ x in 𝓝 w, x ∈ O := hO.mem_nhds hwO
  have hinvH : (fun x => liftChartHam ν μ (chartRot θ x)) =ᶠ[𝓝 w] liftChartHam ν μ :=
    hdomO.mono fun x hx => liftChartHam_chartRot ν μ θ (hOs hx).1
  have hinvF : (fun x => F (chartRot θ x)) =ᶠ[𝓝 w] F :=
    hdomO.mono fun x hx => (hFrot θ x hx).2
  have hH : DifferentiableAt ℝ (liftChartHam ν μ) (chartRot θ w) :=
    ((analyticOnNhd_liftChartHam hν μ) _ (hOs hrO)).differentiableAt
  have hFd : DifferentiableAt ℝ F (chartRot θ w) := hF.differentiableAt (hO.mem_nhds hrO)
  have h := fderiv_apply_hamiltonianVectorField_comp (chartRotCLM_symplectic θ)
    (chartRotCLM_surjective θ) (hasFDerivAt_chartRot θ w) hH hinvH hFd hinvF
  rw [← h]
  exact hS _ hθ

/-- **Rotation reduction of the range bound.** If `F` is invariant under every chart rotation on
`O`, a bound `lo ≤ F - Λ_i ≤ hi` on `S` holds at every point of `R ⊆ O` that some rotation maps
into `S`. -/
theorem range_bound_of_rotation {F : Phase (n + n) → ℝ} {O : Set (Phase (n + n))}
    (hFrot : ∀ θ, ∀ w ∈ O, F (chartRot θ w) = F w) {R S : Set (Phase (n + n))} (hRO : R ⊆ O)
    (hRS : ∀ w ∈ R, ∃ θ, chartRot θ w ∈ S) (i : Fin n) {lo hi : ℝ}
    (hS : ∀ w ∈ S, lo ≤ F w - fast w.2 i ∧ F w - fast w.2 i ≤ hi) :
    ∀ w ∈ R, lo ≤ F w - fast w.2 i ∧ F w - fast w.2 i ≤ hi := by
  intro w hw
  obtain ⟨θ, hθ⟩ := hRS w hw
  have h := hS _ hθ
  rwa [hFrot θ w (hRO hw), fast_chartRot] at h

end ChartRotation

end KAM.Application.LambdaDrift

end
