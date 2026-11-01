/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.Transport
public import KAM.ODE.Exit
public import KAM.ODE.Uniqueness

/-!
# Invariance of a physical torus

`IsPhysicalFlowTorus F ν L` says only that the torus lines `τ ↦ L(θ + τ ν)` solve `ż = F(z)`. This
module proves that the **image is invariant**: if `F` is `C¹` on an open set `W` containing the
torus (so `F` is locally Lipschitz there), then a solution of `ż = F(z)` in `W` on an interval
`J` that meets the image at one time equals, on all of `J`, the torus line through that point
(ODE uniqueness, the core `KAM.ODE.gen_uniqueness`).

* `IsPhysicalFlowTorus.hasDerivAt_line`, `isSolutionIn_line`: the line through `L θ₀` at time
  `t₀` is a global solution.
* `IsPhysicalFlowTorus.eqOn_line`: `y t = L (θ₀ + (t - t₀) ν)` for `t ∈ J` when `y t₀ = L θ₀`.
* `IsPhysicalFlowTorus.mem_range_of_solution`, `IsPhysicalFlowTorus.isInvariantSet`
  (`KAM.ODE.IsInvariantSet F W (range L)`).
* `IsPhysicalFlowTorus.forall_solution`: a property of every torus point (an observable bound)
  holds along every solution that meets the torus, at every time of its interval.

In model coordinates, a real model torus is a flow torus of its own Hamiltonian field
(`IsRealModelTorus.isPhysicalFlowTorus_self`); there `F = X_H`, which is `C¹` where `H` is `C²`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Application

open KAM KAM.ODE

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → E}
  {ν : Fin n → ℝ} {L : (Fin n → ℝ) → E}

namespace IsPhysicalFlowTorus

/-- The torus line through `L θ₀` at time `t₀`. -/
theorem hasDerivAt_line (hL : IsPhysicalFlowTorus F ν L) (θ₀ : Fin n → ℝ) (t₀ t : ℝ) :
    HasDerivAt (fun s : ℝ => L (θ₀ + (s - t₀) • ν)) (F (L (θ₀ + (t - t₀) • ν))) t := by
  have e : ∀ s : ℝ, θ₀ + (s - t₀) • ν = (θ₀ - t₀ • ν) + s • ν := fun s => by
    rw [sub_smul]; abel
  simp only [e]
  exact hL (θ₀ - t₀ • ν) t

theorem isSolutionIn_line (hL : IsPhysicalFlowTorus F ν L) {W : Set E} (hLW : ∀ θ, L θ ∈ W)
    (θ₀ : Fin n → ℝ) (t₀ : ℝ) (J : Set ℝ) :
    IsSolutionIn F W J (fun s : ℝ => L (θ₀ + (s - t₀) • ν)) := fun t _ =>
  ⟨hLW _, hL.hasDerivAt_line θ₀ t₀ t⟩

/-- **Uniqueness on the torus**: a solution in `W` (`F` of class `C¹` on the open `W ⊇ range L`)
that meets the torus at `L θ₀` at time `t₀` is the torus line through that point. -/
theorem eqOn_line (hL : IsPhysicalFlowTorus F ν L) {W : Set E} (hW : IsOpen W)
    (hF : ContDiffOn ℝ 1 F W) (hLW : ∀ θ, L θ ∈ W) {J : Set ℝ} (hJ : J.OrdConnected)
    {y : ℝ → E} (hy : IsSolutionIn F W J y) {t₀ : ℝ} (ht₀ : t₀ ∈ J) {θ₀ : Fin n → ℝ}
    (h : y t₀ = L θ₀) : ∀ t ∈ J, y t = L (θ₀ + (t - t₀) • ν) := fun _ ht =>
  gen_uniqueness hW hF hJ ht₀ hy (hL.isSolutionIn_line hLW θ₀ t₀ J) (by simp [h]) ht

/-- **A solution that meets the torus stays on it.** -/
theorem mem_range_of_solution (hL : IsPhysicalFlowTorus F ν L) {W : Set E} (hW : IsOpen W)
    (hF : ContDiffOn ℝ 1 F W) (hLW : ∀ θ, L θ ∈ W) {J : Set ℝ} (hJ : J.OrdConnected)
    {y : ℝ → E} (hy : IsSolutionIn F W J y) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (h : y t₀ ∈ range L) :
    ∀ t ∈ J, y t ∈ range L := by
  obtain ⟨θ₀, hθ₀⟩ := h
  intro t ht
  exact ⟨_, (hL.eqOn_line hW hF hLW hJ hy ht₀ hθ₀.symm t ht).symm⟩

/-- The torus image is an invariant set of `F` in `W` (the core `KAM.ODE.IsInvariantSet`). -/
theorem isInvariantSet (hL : IsPhysicalFlowTorus F ν L) {W : Set E} (hW : IsOpen W)
    (hF : ContDiffOn ℝ 1 F W) (hLW : ∀ θ, L θ ∈ W) : IsInvariantSet F W (range L) :=
  fun _ _ hJ hy _ ht₁ h t ht => hL.mem_range_of_solution hW hF hLW hJ hy ht₁ h t ht

/-- **Observables along solutions**: a property of every torus point holds at every time along
every solution in `W` that meets the torus. -/
theorem forall_solution (hL : IsPhysicalFlowTorus F ν L) {W : Set E} (hW : IsOpen W)
    (hF : ContDiffOn ℝ 1 F W) (hLW : ∀ θ, L θ ∈ W) {P : E → Prop} (hP : ∀ θ, P (L θ))
    {J : Set ℝ} (hJ : J.OrdConnected) {y : ℝ → E} (hy : IsSolutionIn F W J y) {t₀ : ℝ}
    (ht₀ : t₀ ∈ J) (h : y t₀ ∈ range L) : ∀ t ∈ J, P (y t) := fun t ht => by
  obtain ⟨θ, hθ⟩ := hL.mem_range_of_solution hW hF hLW hJ hy ht₀ h t ht
  rw [← hθ]
  exact hP θ

end IsPhysicalFlowTorus

end KAM.Application
