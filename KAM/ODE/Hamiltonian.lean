/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.ODE.Basic
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Nekhoroshev.Defs.IsSolutionOn
public import KAM.Frozen.Iso.Defs.IsHamiltonianSolutionOn
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Hamiltonian layer of the ODE library

Blueprint N Part 3 (`bpN:p3:ham-smooth`, `ham-energy`, `ham-periodic`, `ham-reduction`).

* `KAM.ODE.ham_smooth`, `ham_smooth_c1`: regularity of `X_H`.
* `KAM.ODE.ham_energy`: conservation of `H` along solutions.
* `KAM.ODE.ham_periodic`: invariance of `X_H` and of solutions under integer angle shifts.
* `KAM.ODE.ham_reduction`: the frozen solution predicates are `IsSolutionIn` for `X_H`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace KAM.ODE

section Hamiltonian

variable {n : ℕ}

open KAM in
/-- `bpN:p3:ham-smooth`: `H ∈ C^{k+1}` on open `W` gives `X_H ∈ C^k` there (any `k : WithTop ℕ∞`)
and differentiability of `H` at every point of `W`. -/
theorem ham_smooth {W : Set ((Fin n → ℝ) × (Fin n → ℝ))} {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    (hW : IsOpen W) {k : WithTop ℕ∞} (hH : ContDiffOn ℝ (k + 1) H W) :
    ContDiffOn ℝ k (hamiltonianVectorField H) W ∧ ∀ x ∈ W, DifferentiableAt ℝ H x := by
  refine ⟨?_, fun x hx => ?_⟩
  · have hf : ContDiffOn ℝ k (fderiv ℝ H) W := hH.fderiv_of_isOpen hW le_rfl
    have hc : ∀ v : (Fin n → ℝ) × (Fin n → ℝ),
        ContDiffOn ℝ k (fun x => fderiv ℝ H x v) W := fun v =>
      hf.clm_apply contDiffOn_const
    refine ContDiffOn.prodMk (contDiffOn_pi.2 fun i => hc _) (contDiffOn_pi.2 fun i => ?_)
    exact (hc _).neg
  · have h1 : (1 : WithTop ℕ∞) ≤ k + 1 := by
      calc (1 : WithTop ℕ∞) = 0 + 1 := by simp
        _ ≤ k + 1 := by gcongr; exact zero_le
    have hne : (k + 1 : WithTop ℕ∞) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one h1)
    exact ((hH.differentiableOn hne) x hx).differentiableAt (hW.mem_nhds hx)

/-- `bpN:p3:ham-smooth`, the instance `k = 1` used by all consumers. -/
theorem ham_smooth_c1 {W : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} (hW : IsOpen W) (hH : ContDiffOn ℝ 2 H W) :
    ContDiffOn ℝ 1 (KAM.hamiltonianVectorField H) W :=
  (ham_smooth (k := 1) hW (by rwa [one_add_one_eq_two])).1

/-- Helper: a continuous linear functional on `ℝⁿ × ℝⁿ` evaluated on `(a, 0)`. -/
private theorem clm_fst_eq (ℓ : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] ℝ) (a : Fin n → ℝ) :
    ℓ (a, 0) = ∑ i, a i * ℓ (Pi.single i 1, 0) := by
  have : ((a, 0) : (Fin n → ℝ) × (Fin n → ℝ)) = ∑ i, a i • ((Pi.single i 1 : Fin n → ℝ), 0) := by
    ext j
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  rw [this, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]

/-- Helper: a continuous linear functional on `ℝⁿ × ℝⁿ` evaluated on `(0, b)`. -/
private theorem clm_snd_eq (ℓ : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] ℝ) (b : Fin n → ℝ) :
    ℓ (0, b) = ∑ i, b i * ℓ (0, Pi.single i 1) := by
  have : ((0, b) : (Fin n → ℝ) × (Fin n → ℝ)) = ∑ i, b i • ((0 : Fin n → ℝ), Pi.single i 1) := by
    ext j
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [this, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]

/-- Helper: the symplectic cancellation `ℓ (X_H) = 0` for `ℓ = dH`. -/
private theorem clm_ham_zero (ℓ : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] ℝ) :
    ℓ ((fun i => ℓ (0, Pi.single i 1), fun i => -ℓ (Pi.single i 1, 0)) :
      (Fin n → ℝ) × (Fin n → ℝ)) = 0 := by
  have h : ((fun i => ℓ (0, Pi.single i 1), fun i => -ℓ (Pi.single i 1, 0)) :
      (Fin n → ℝ) × (Fin n → ℝ)) =
      ((fun i => ℓ (0, Pi.single i 1), 0) : (Fin n → ℝ) × (Fin n → ℝ)) +
      ((0, fun i => -ℓ (Pi.single i 1, 0)) : (Fin n → ℝ) × (Fin n → ℝ)) := by
    ext <;> simp
  rw [h, map_add, clm_fst_eq, clm_snd_eq]
  simp only [neg_mul]
  rw [Finset.sum_neg_distrib]
  simp only [mul_comm]
  ring

/-- `bpN:p3:ham-energy`. -/
theorem ham_energy {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : ∀ t ∈ J, DifferentiableAt ℝ H (z t) ∧
      HasDerivAt z (KAM.hamiltonianVectorField H (z t)) t) :
    ∀ t ∈ J, ∀ t' ∈ J, H (z t) = H (z t') := by
  have hd : ∀ t ∈ J, HasDerivAt (fun s => H (z s)) 0 t := fun t ht => by
    have := (hz t ht).1.hasFDerivAt.comp_hasDerivAt t (hz t ht).2
    have h0 := clm_ham_zero (fderiv ℝ H (z t))
    rwa [show fderiv ℝ H (z t) (KAM.hamiltonianVectorField H (z t)) = 0 from h0] at this
  have key : ∀ a ∈ J, ∀ b ∈ J, a ≤ b → H (z b) = H (z a) := by
    intro a ha b hb hab
    have hsub : Icc a b ⊆ J := hJ.out ha hb
    have hcont : ContinuousOn (fun s => H (z s)) (Icc a b) := fun s hs =>
      (hd s (hsub hs)).continuousAt.continuousWithinAt
    exact constant_of_has_deriv_right_zero hcont
      (fun s hs => (hd s (hsub (Ico_subset_Icc_self hs))).hasDerivWithinAt) b ⟨hab, le_rfl⟩
  intro t ht t' ht'
  rcases le_total t t' with h | h
  · exact (key t ht t' ht' h).symm
  · exact key t' ht' t ht h

/-- `bpN:p3:ham-periodic`. -/
theorem ham_periodic {W : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} (hW : IsOpen W)
    (hWk : ∀ k : Fin n → ℤ, (fun x => x + angleShift k) '' W = W)
    (hH : ∀ k : Fin n → ℤ, ∀ x ∈ W, H (x + angleShift k) = H x) :
    (∀ k : Fin n → ℤ, ∀ x ∈ W,
      KAM.hamiltonianVectorField H (x + angleShift k) = KAM.hamiltonianVectorField H x) ∧
    ∀ (J : Set ℝ) (z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)),
      IsSolutionIn (KAM.hamiltonianVectorField H) W J z → ∀ k : Fin n → ℤ,
        IsSolutionIn (KAM.hamiltonianVectorField H) W J (fun t => z t + angleShift k) ∧
        ∀ t ∈ J, H (z t + angleShift k) = H (z t) := by
  have hX : ∀ k : Fin n → ℤ, ∀ x ∈ W,
      KAM.hamiltonianVectorField H (x + angleShift k) = KAM.hamiltonianVectorField H x := by
    intro k x hx
    have hev : (fun y => H (y + angleShift k)) =ᶠ[nhds x] H :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hx) (fun y hy => hH k y hy)
    have hf : fderiv ℝ H (x + angleShift k) = fderiv ℝ H x := by
      rw [← hev.fderiv_eq, fderiv_comp_add_right]
    simp only [KAM.hamiltonianVectorField, hf]
  refine ⟨hX, fun J z hz k => ⟨?_, fun t ht => hH k _ (hz t ht).1⟩⟩
  exact gen_symmetry_translate hz (hWk k) (hX k)

open KAM in
/-- Helper: the differentiability clause of `ham_smooth` on `univ ×ˢ U ⊆ W`. -/
private theorem diff_of_mem {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)}
    {W : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hW : IsOpen W)
    (hUW : (univ : Set (Fin n → ℝ)) ×ˢ U ⊆ W) (hH : ContDiffOn ℝ 2 H W)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x.2 ∈ U) : DifferentiableAt ℝ H x :=
  (ham_smooth (k := 1) hW (by rwa [one_add_one_eq_two])).2 x (hUW ⟨mem_univ _, hx⟩)

/-- `bpN:p3:ham-reduction`: the frozen predicates `IsSolutionOn` and
`IsHamiltonianSolutionOn` are `IsSolutionIn` for `X_H` in `ℝⁿ × U`. The blueprint's
"`U` open" is not used and is omitted. -/
theorem ham_reduction {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)}
    {W : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hW : IsOpen W)
    (hUW : (univ : Set (Fin n → ℝ)) ×ˢ U ⊆ W) (hH : ContDiffOn ℝ 2 H W) :
    ContDiffOn ℝ 1 (KAM.hamiltonianVectorField H) (univ ×ˢ U) ∧
    ∀ (J : Set ℝ) (z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)),
      (KAM.Nekhoroshev.IsSolutionOn H U J z ↔
        IsSolutionIn (KAM.hamiltonianVectorField H) (univ ×ˢ U) J z) ∧
      (IsSolutionIn (KAM.hamiltonianVectorField H) (univ ×ˢ U) J z ↔
        KAM.Iso.IsHamiltonianSolutionOn H U J z) := by
  refine ⟨(ham_smooth_c1 hW hH).mono hUW, fun J z => ⟨⟨fun h t ht => ?_, fun h t ht => ?_⟩,
    ⟨fun h t ht => ?_, fun h t ht => ?_⟩⟩⟩
  · exact ⟨⟨mem_univ _, (h t ht).1⟩, (h t ht).2.2⟩
  · exact ⟨(h t ht).1.2, diff_of_mem hW hUW hH (h t ht).1.2, (h t ht).2⟩
  · exact ⟨(h t ht).1.2, diff_of_mem hW hUW hH (h t ht).1.2, (h t ht).2⟩
  · exact ⟨⟨mem_univ _, (h t ht).1⟩, (h t ht).2.2⟩

end Hamiltonian

end KAM.ODE
