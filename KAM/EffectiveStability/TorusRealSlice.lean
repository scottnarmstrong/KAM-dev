/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Apost.Exactness
public import KAM.Application.RealTorus
public import KAM.Strip.RealRestriction
public import KAM.Torus.FrozenAgreement

/-!
# The real slice of a holomorphic primary torus (track B, package B5-LAG, items 2 and 3)

For `K` holomorphic on `T_ρ`, primary and real on reals, write `(x φ, v φ) = realRestriction K φ`
and `u φ = x φ - φ`. This file proves:

* `u`, `v` are `1`-periodic, `x (φ + k) = x φ + k`, and `x, u, v` are smooth
  (`torusRealX_contDiff`, ...);
* the real derivative is the restriction of the complex one (`fderiv_torusRealX_incl`, ...);
* `lagrangeMat K (ι φ) = 0` gives the real Lagrangian condition `(Dx)ᵀ Dv` symmetric
  (`torusReal_lagrangian`);
* the frequency identity `D(x, v) φ ω' = X_{Re h} (x φ, v φ)` for an exactly invariant torus,
  and `h (K (ι φ)) = E` gives `Re h (x φ, v φ) = E` (`torusReal_frequency`,
  `torusReal_energy`), with the real Hamiltonian `KAM.Application.realHam h = Re h ∘ ι₂`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open KAM KAM.Torus Filter

variable {n : ℕ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ρ : ℝ}

/-- The real base map `x φ = Re K^θ (φ)`. -/
def torusRealX (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (φ : Fin n → ℝ) : Fin n → ℝ :=
  (realRestriction K φ).1

/-- The real momentum `v φ = Re K^I (φ)`. -/
def torusRealV (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (φ : Fin n → ℝ) : Fin n → ℝ :=
  (realRestriction K φ).2

/-- The displacement `u φ = x φ - φ`. -/
def torusRealU (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (φ : Fin n → ℝ) : Fin n → ℝ :=
  torusRealX K φ - φ

theorem torusRealX_add_int (hρ : 0 < ρ) (hKp : IsPrimaryOnStrip K ρ) (hreal : IsRealOnReals K)
    (φ : Fin n → ℝ) (k : Fin n → ℤ) :
    torusRealX K (φ + fun i => (k i : ℝ)) = torusRealX K φ + fun i => (k i : ℝ) := by
  simp [torusRealX, realRestriction_add_int hρ hKp hreal φ k]

theorem torusRealU_add_int (hρ : 0 < ρ) (hKp : IsPrimaryOnStrip K ρ) (hreal : IsRealOnReals K)
    (φ : Fin n → ℝ) (k : Fin n → ℤ) :
    torusRealU K (φ + fun i => (k i : ℝ)) = torusRealU K φ := by
  simp only [torusRealU, torusRealX_add_int hρ hKp hreal φ k]
  abel

theorem torusRealV_add_int (hρ : 0 < ρ) (hKp : IsPrimaryOnStrip K ρ) (hreal : IsRealOnReals K)
    (φ : Fin n → ℝ) (k : Fin n → ℤ) :
    torusRealV K (φ + fun i => (k i : ℝ)) = torusRealV K φ := by
  simp [torusRealV, realRestriction_add_int hρ hKp hreal φ k]

theorem torusRealPair_contDiff (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ)) :
    ContDiff ℝ (⊤ : ℕ∞) (realRestriction K) :=
  (analyticOnNhd_realRestriction hρ hK).contDiff

theorem torusRealX_contDiff (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ)) :
    ContDiff ℝ (⊤ : ℕ∞) (torusRealX K) :=
  contDiff_fst.comp (torusRealPair_contDiff hρ hK)

theorem torusRealV_contDiff (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ)) :
    ContDiff ℝ (⊤ : ℕ∞) (torusRealV K) :=
  contDiff_snd.comp (torusRealPair_contDiff hρ hK)

theorem torusRealU_contDiff (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ)) :
    ContDiff ℝ (⊤ : ℕ∞) (torusRealU K) :=
  (torusRealX_contDiff hρ hK).sub contDiff_id

/-- The real derivative of `x` is the restriction of the complex derivative of `K^θ`. -/
theorem fderiv_torusRealX_incl (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hreal : IsRealOnReals K) (φ e : Fin n → ℝ) :
    realInclusion n (fderiv ℝ (torusRealX K) φ e) =
      (fderiv ℂ K (realInclusion n φ) (realInclusion n e)).1 := by
  obtain ⟨hd, hf⟩ := realRestriction_fderiv hρ hK hreal φ
  have h1 : fderiv ℝ (torusRealX K) φ = (ContinuousLinearMap.fst ℝ _ _).comp
      (fderiv ℝ (realRestriction K) φ) :=
    (hd.hasFDerivAt.fst).fderiv
  rw [h1]
  exact congrArg Prod.fst (hf e)

/-- The real derivative of `v` is the restriction of the complex derivative of `K^I`. -/
theorem fderiv_torusRealV_incl (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hreal : IsRealOnReals K) (φ e : Fin n → ℝ) :
    realInclusion n (fderiv ℝ (torusRealV K) φ e) =
      (fderiv ℂ K (realInclusion n φ) (realInclusion n e)).2 := by
  obtain ⟨hd, hf⟩ := realRestriction_fderiv hρ hK hreal φ
  have h1 : fderiv ℝ (torusRealV K) φ = (ContinuousLinearMap.snd ℝ _ _).comp
      (fderiv ℝ (realRestriction K) φ) :=
    (hd.hasFDerivAt.snd).fderiv
  rw [h1]
  exact congrArg Prod.snd (hf e)

/-- **Real Lagrangian condition** (item 2): `(Dx)ᵀ Dv` is symmetric, in the plain form
`∑ₗ (Dx e_i)ₗ (Dv e_j)ₗ = ∑ₗ (Dx e_j)ₗ (Dv e_i)ₗ`, from `Ω_K (ι φ) = 0`. -/
theorem torusReal_lagrangian (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hreal : IsRealOnReals K) {φ : Fin n → ℝ} (hΩ : lagrangeMat K (realInclusion n φ) = 0)
    (i j : Fin n) :
    ∑ l, (fderiv ℝ (torusRealX K) φ (Pi.single i 1)) l *
        (fderiv ℝ (torusRealV K) φ (Pi.single j 1)) l =
      ∑ l, (fderiv ℝ (torusRealX K) φ (Pi.single j 1)) l *
        (fderiv ℝ (torusRealV K) φ (Pi.single i 1)) l := by
  have hx : ∀ l a, tangentMat K (realInclusion n φ) (Sum.inl l) a =
      ((fderiv ℝ (torusRealX K) φ (Pi.single a 1)) l : ℂ) := fun l a => by
    rw [tangentMat_apply, sumVec_apply, Sum.elim_inl,
      ← realInclusion_single a, ← fderiv_torusRealX_incl hρ hK hreal]
    rfl
  have hv : ∀ l a, tangentMat K (realInclusion n φ) (Sum.inr l) a =
      ((fderiv ℝ (torusRealV K) φ (Pi.single a 1)) l : ℂ) := fun l a => by
    rw [tangentMat_apply, sumVec_apply, Sum.elim_inr,
      ← realInclusion_single a, ← fderiv_torusRealV_incl hρ hK hreal]
    rfl
  have h0 := congrFun (congrFun hΩ i) j
  rw [Apost.Exactness.lagrangeMat_apply] at h0
  simp only [hx, hv, Matrix.zero_apply] at h0
  have h1 : ((∑ l, ((fderiv ℝ (torusRealV K) φ (Pi.single i 1)) l *
        (fderiv ℝ (torusRealX K) φ (Pi.single j 1)) l -
      (fderiv ℝ (torusRealX K) φ (Pi.single i 1)) l *
        (fderiv ℝ (torusRealV K) φ (Pi.single j 1)) l) : ℝ) : ℂ) = 0 := by
    rw [← h0]
    push_cast
    rfl
  have h2 := Complex.ofReal_eq_zero.mp h1
  rw [Finset.sum_sub_distrib, sub_eq_zero] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

section Frequency

variable {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}

theorem realInclusion₂_realRestriction (hreal : IsRealOnReals K) (φ : Fin n → ℝ) :
    realInclusion₂ n (realRestriction K φ) = K (realInclusion n φ) :=
  (isRealOnReals_iff.mp hreal φ).symm

/-- **Frequency identity on reals** (item 3). If `K` is real on reals, holomorphic on `T_ρ` with
values in the open set `D` where `h` is holomorphic and real at real points, and
`invarianceError h K ω' = 0` on `T_ρ`, then
`D(x, v) φ ω' = X_{Re h} (x φ, v φ)`. -/
theorem torusReal_frequency (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hreal : IsRealOnReals K) (hD : IsOpen D) (hh : DifferentiableOn ℂ h D)
    (hhreal : ∀ y : (Fin n → ℝ) × (Fin n → ℝ), realInclusion₂ n y ∈ D →
      (h (realInclusion₂ n y)).im = 0)
    (hKD : ∀ θ ∈ complexStrip n ρ, K θ ∈ D) {ω' : Fin n → ℝ}
    (hinv : ∀ θ ∈ complexStrip n ρ, invarianceError h K ω' θ = 0) (φ : Fin n → ℝ) :
    fderiv ℝ (realRestriction K) φ ω' =
      hamiltonianVectorField (Application.realHam h) (realRestriction K φ) := by
  have hz : realInclusion₂ n (realRestriction K φ) ∈ D := by
    rw [realInclusion₂_realRestriction hreal]
    exact hKD _ (realInclusion_mem_complexStrip hρ φ)
  have h1 := hamiltonianVectorField_eq_of_real hD hh hhreal hz
    (H := Application.realHam h) (Eventually.of_forall fun y => rfl)
  have h2 := hinv _ (realInclusion_mem_complexStrip hρ φ)
  rw [invarianceError, sub_eq_zero] at h2
  refine realInclusion₂_injective n ?_
  rw [h1, realInclusion₂_realRestriction hreal, h2,
    (realRestriction_fderiv hρ hK hreal φ).2 ω']
  rfl

/-- Energy on reals: `h ∘ K = E` on the reals gives `Re h (x φ, v φ) = E`. -/
theorem torusReal_energy (hreal : IsRealOnReals K) {E : ℝ} (φ : Fin n → ℝ)
    (hE : h (K (realInclusion n φ)) = (E : ℂ)) :
    Application.realHam h (realRestriction K φ) = E := by
  unfold Application.realHam
  rw [realInclusion₂_realRestriction hreal, hE]
  simp

end Frequency

end KAM.EffectiveStability

end
