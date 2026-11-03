/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.RealFlow.Basic
public import KAM.Canonical.Symplectic
public import KAM.Frozen.Defs.SymplecticForm

/-!
# The real flow is symplectic and invertible

* `realFlow_hasFDerivAt`: the derivative bridge `ι (D X^t(x) u) = D X^t_ℂ (ι x) (ι u)`.
* `realFlow_symplectic`: `ω (D X^t(x) u) (D X^t(x) v) = ω u v` for the frozen real form
  `KAM.symplecticForm` (derived from `KAM.Canonical.symplectic`).
* `realFlow_neg_realFlow_one`, `realFlow_one_realFlow_neg`: the time `±1` maps are mutually
  inverse on `realInterior W Ω 1`, with images in `realInterior W Ω (1/2)`.
-/

@[expose] public noncomputable section

open Set
open scoped Topology

namespace KAM.EffectiveStability

open KAM.Canonical

variable {n : ℕ}
  {W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}
  {Ω : Set ((Fin n → ℂ) × (Fin n → ℂ))} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}

/-- Derivative bridge for the real flow. -/
theorem realFlow_hasFDerivAt (hφ : DifferentiableOn ℂ φ Ω)
    (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    (hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Ω →
      (φ (KAM.realInclusion₂ n x)).im = 0)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realInterior W Ω (1 / 2)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    ∃ L : ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)),
      HasFDerivAt (realFlow φ Ω t) L x ∧ ∀ u, KAM.realInclusion₂ n (L u) =
        fderiv ℂ (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t) (KAM.realInclusion₂ n x)
          (KAM.realInclusion₂ n u) := by
  refine reMap_hasFDerivAt (((flow_b h).2.1 t ht).differentiableAt
    ((isOpen_gaugeInterior h.isOpen W (1 / 2)).mem_nhds hx)) ?_
  filter_upwards [(isOpen_realInterior h.isOpen (1 / 2)).mem_nhds hx] with y hy
  exact ⟨_, realInclusion₂_realFlow h.isOpen hφ h hreal hy ht⟩

/-- (3) The real flow preserves the frozen real symplectic form; exactly B1's `hΨsymp` shape. -/
theorem realFlow_symplectic (hφ : DifferentiableOn ℂ φ Ω)
    (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    (hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Ω →
      (φ (KAM.realInclusion₂ n x)).im = 0)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realInterior W Ω (1 / 2)) (u v : (Fin n → ℝ) × (Fin n → ℝ)) :
    KAM.symplecticForm (fderiv ℝ (realFlow φ Ω t) x u) (fderiv ℝ (realFlow φ Ω t) x v) =
      KAM.symplecticForm u v := by
  obtain ⟨L, hL, hLι⟩ := realFlow_hasFDerivAt hφ h hreal hx ht
  rw [hL.fderiv]
  have hs := (symplectic hφ h hx ht _ rfl).1 (KAM.realInclusion₂ n u) (KAM.realInclusion₂ n v)
  rw [← hLι, ← hLι] at hs
  have e : ∀ a b : (Fin n → ℝ) × (Fin n → ℝ),
      symplFormC (KAM.realInclusion₂ n a) (KAM.realInclusion₂ n b) =
        ((KAM.symplecticForm a b : ℝ) : ℂ) := fun a b => by
    simp [symplFormC, KAM.symplecticForm]
  rw [e, e] at hs
  exact_mod_cast hs

/-- `ι (X^{1}) x ∈ gaugeInterior (1/2)` and the two inverse identities, in complex form, for real
`x` in `realInterior W Ω 1`. -/
theorem realFlow_mem_realInterior (hΩ : IsOpen Ω) (hφ : DifferentiableOn ℂ φ Ω)
    (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    (hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Ω →
      (φ (KAM.realInclusion₂ n x)).im = 0)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realInterior W Ω 1) {t : ℝ}
    (ht : t = 1 ∨ t = -1) :
    realFlow φ Ω t x ∈ realInterior W Ω (1 / 2) := by
  have hx2 : x ∈ realInterior W Ω (1 / 2) := realInterior_mono (by norm_num) hx
  have ht' : t ∈ Icc (-1 : ℝ) 1 := by rcases ht with rfl | rfl <;> norm_num
  show KAM.realInclusion₂ n (realFlow φ Ω t x) ∈ gaugeInterior W Ω (1 / 2)
  rw [realInclusion₂_realFlow hΩ hφ h hreal hx2 ht']
  obtain ⟨h1, -, h2, -⟩ := flow_c h hx
  rcases ht with rfl | rfl
  · exact h1
  · exact h2

/-- (4) `X^{-1} ∘ X^{1} = id` on `realInterior W Ω 1`. -/
theorem realFlow_neg_realFlow_one (hΩ : IsOpen Ω) (hφ : DifferentiableOn ℂ φ Ω)
    (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    (hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Ω →
      (φ (KAM.realInclusion₂ n x)).im = 0)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realInterior W Ω 1) :
    realFlow φ Ω (-1) (realFlow φ Ω 1 x) = x := by
  have hx2 : x ∈ realInterior W Ω (1 / 2) := realInterior_mono (by norm_num) hx
  have hy := realFlow_mem_realInterior hΩ hφ h hreal hx (Or.inl rfl)
  apply KAM.realInclusion₂_injective n
  rw [realInclusion₂_realFlow hΩ hφ h hreal hy ⟨by norm_num, by norm_num⟩,
    realInclusion₂_realFlow hΩ hφ h hreal hx2 ⟨by norm_num, by norm_num⟩]
  exact (flow_c h hx).2.1

/-- (4) `X^{1} ∘ X^{-1} = id` on `realInterior W Ω 1`. -/
theorem realFlow_one_realFlow_neg (hΩ : IsOpen Ω) (hφ : DifferentiableOn ℂ φ Ω)
    (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    (hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Ω →
      (φ (KAM.realInclusion₂ n x)).im = 0)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realInterior W Ω 1) :
    realFlow φ Ω 1 (realFlow φ Ω (-1) x) = x := by
  have hx2 : x ∈ realInterior W Ω (1 / 2) := realInterior_mono (by norm_num) hx
  have hy := realFlow_mem_realInterior hΩ hφ h hreal hx (Or.inr rfl)
  apply KAM.realInclusion₂_injective n
  rw [realInclusion₂_realFlow hΩ hφ h hreal hy ⟨by norm_num, by norm_num⟩,
    realInclusion₂_realFlow hΩ hφ h hreal hx2 ⟨by norm_num, by norm_num⟩]
  exact (flow_c h hx).2.2.2.1

end KAM.EffectiveStability

end
