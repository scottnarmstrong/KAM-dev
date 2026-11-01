/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.RealRestriction
public import KAM.Frozen.Defs.InvarianceError
public import KAM.Frozen.Defs.IsDiophantine

/-!
# The real model torus of an exact complex torus

No certificate data. An exact complex torus `K∞` (holomorphic on the strip `T_ρ`, primary, real
on the reals, invariant for a holomorphic Hamiltonian `h` at the frequency `ω`, on the level `E`)
has the real restriction `k = Re ∘ K∞ ∘ ι` (`KAM.realRestriction`). This module states what `k`
is in the model's own real coordinates `(θ, I) ∈ ℝⁿ × ℝⁿ`, for the real Hamiltonian
`realHam h = Re h ∘ ι`:

* `IsRealHolo D h`: `D` open, `h` holomorphic on `D` and real at the real points of `D` (the
  standing facts of every certificate Hamiltonian; `KAM/Application/Certified.lean` derives them).
* `IsRealModelTorus H ω E k`: `k` analytic, `k(θ + m) = k(θ) + (m, 0)`, the lines
  `s ↦ k(θ + s ω)` are solutions of Hamilton's equations of `H` (frozen orientation
  `X_H = (∂_I H, -∂_θ H)`), and `H ∘ k = E`.
* `isRealModelTorus_realRestriction`: the real restriction of an exact torus is a real model torus
  of `realHam h` (via `KAM.real_restriction` and `KAM.hamiltonianVectorField_eq_of_real`).
* `IsRealModelTorus.congr`: the same torus for any real Hamiltonian agreeing with `H` on an open
  set containing it (e.g. a closed-form physical expression of the certificate's Hamiltonian).
* `isDiophantine_mul_smul`: `s ω` is `(s γ, τ)`-Diophantine for `s > 0` (the frequency `s∞ ω*`).
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace KAM.Application

open KAM

variable {n : ℕ}

/-- The real form `y ↦ Re h(ι y)` of a complex Hamiltonian, on `ℝⁿ × ℝⁿ`. -/
def realHam (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : (Fin n → ℝ) × (Fin n → ℝ) → ℝ :=
  fun y => (h (realInclusion₂ n y)).re

/-- `h` is holomorphic on the open set `D` and real at the real points of `D`. -/
structure IsRealHolo (D : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : Prop where
  isOpen : IsOpen D
  holo : DifferentiableOn ℂ h D
  real : ∀ y : (Fin n → ℝ) × (Fin n → ℝ), realInclusion₂ n y ∈ D →
    (h (realInclusion₂ n y)).im = 0

section Ham

variable {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {y : (Fin n → ℝ) × (Fin n → ℝ)}

theorem IsRealHolo.differentiableAt_realHam (hh : IsRealHolo D h)
    (hy : realInclusion₂ n y ∈ D) : DifferentiableAt ℝ (realHam h) y :=
  (hamiltonian_real_fderiv hh.isOpen hh.holo hh.real hy (Eventually.of_forall fun _ => rfl)).1

/-- At a real point of `D`, the real Hamiltonian field of `realHam h` is the complex field of
`h`. -/
theorem IsRealHolo.realInclusion₂_hamiltonianVectorField (hh : IsRealHolo D h)
    (hy : realInclusion₂ n y ∈ D) :
    realInclusion₂ n (hamiltonianVectorField (realHam h) y) =
      hamiltonianVectorFieldℂ h (realInclusion₂ n y) :=
  hamiltonianVectorField_eq_of_real hh.isOpen hh.holo hh.real hy
    (Eventually.of_forall fun _ => rfl)

theorem IsRealHolo.ofReal_realHam (hh : IsRealHolo D h) (hy : realInclusion₂ n y ∈ D) :
    ((realHam h y : ℝ) : ℂ) = h (realInclusion₂ n y) :=
  Complex.ext (by simp [realHam]) (by rw [Complex.ofReal_im, hh.real y hy])

end Ham

/-- Hamiltonian vector fields agree where the Hamiltonians agree near the point. -/
theorem hamiltonianVectorField_congr {H₁ H₂ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {y : (Fin n → ℝ) × (Fin n → ℝ)} (h : H₁ =ᶠ[𝓝 y] H₂) :
    hamiltonianVectorField H₁ y = hamiltonianVectorField H₂ y := by
  simp only [hamiltonianVectorField, h.fderiv_eq]

/-- **A real model torus** `k : ℝⁿ → ℝⁿ × ℝⁿ` of the real Hamiltonian `H` at the frequency `ω` on
the energy level `E`: `k` is analytic, `k(θ + m) = k(θ) + (m, 0)` for `m ∈ ℤⁿ`, `H` is
differentiable along `k`, every line `s ↦ k(θ + s ω)` solves Hamilton's equations of `H`
(`X_H = (∂_I H, -∂_θ H)`, `KAM.hamiltonianVectorField`), and `H(k θ) = E`. -/
structure IsRealModelTorus (H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (ω : Fin n → ℝ) (E : ℝ)
    (k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) : Prop where
  analytic : AnalyticOnNhd ℝ k univ
  add_int : ∀ θ (m : Fin n → ℤ), k (θ + fun i => (m i : ℝ)) = k θ + (fun i => (m i : ℝ), 0)
  differentiableAt : ∀ θ, DifferentiableAt ℝ H (k θ)
  flow : ∀ θ t, HasDerivAt (fun s : ℝ => k (θ + s • ω))
    (hamiltonianVectorField H (k (θ + t • ω))) t
  energy : ∀ θ, H (k θ) = E

/-- The same torus for another real Hamiltonian agreeing with `H` on an open set containing it. -/
theorem IsRealModelTorus.congr {H H' : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {ω : Fin n → ℝ} {E : ℝ}
    {k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} (hk : IsRealModelTorus H ω E k)
    {O : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hO : IsOpen O) (hkO : ∀ θ, k θ ∈ O)
    (hHH' : ∀ y ∈ O, H' y = H y) : IsRealModelTorus H' ω E k := by
  have hev : ∀ θ, H' =ᶠ[𝓝 (k θ)] H := fun θ =>
    eventuallyEq_of_mem (hO.mem_nhds (hkO θ)) fun y hy => hHH' y hy
  refine ⟨hk.analytic, hk.add_int, fun θ => ?_, fun θ t => ?_, fun θ => ?_⟩
  · exact (hk.differentiableAt θ).congr_of_eventuallyEq (hev θ)
  · rw [hamiltonianVectorField_congr (hev _)]
    exact hk.flow θ t
  · rw [hHH' _ (hkO θ)]
    exact hk.energy θ

section Exact

variable {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ρ : ℝ}

theorem realInclusion_eq_ofReal (ω : Fin n → ℝ) :
    realInclusion n ω = fun i => (ω i : ℂ) := rfl

/-- The derivative along a line. -/
theorem hasDerivAt_line (θ ω : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => θ + s • ω) ω t := by
  simpa using ((hasDerivAt_id t).smul_const ω).const_add θ

/-- **The real restriction of an exact torus is a real model torus** of `realHam h`, at the same
frequency and on the same level. -/
theorem isRealModelTorus_realRestriction (hh : IsRealHolo D h) (hρ : 0 < ρ)
    (hK : DifferentiableOn ℂ Kinf (complexStrip n ρ)) (hp : IsPrimaryOnStrip Kinf ρ)
    (hr : IsRealOnReals Kinf) (hKD : ∀ x : Fin n → ℝ, Kinf (realInclusion n x) ∈ D)
    {ω : Fin n → ℝ} (hinv : ∀ θ ∈ complexStrip n ρ, invarianceError h Kinf ω θ = 0)
    {E : ℝ} (hE : ∀ θ ∈ complexStrip n ρ, h (Kinf θ) = (E : ℂ)) :
    IsRealModelTorus (realHam h) ω E (realRestriction Kinf) := by
  obtain ⟨han, hd, -, hper⟩ := real_restriction hρ hK hr
  have hKι : ∀ x, Kinf (realInclusion n x) = realInclusion₂ n (realRestriction Kinf x) :=
    isRealOnReals_iff.mp hr
  have hmem : ∀ x, realInclusion₂ n (realRestriction Kinf x) ∈ D := fun x => by
    rw [← hKι]; exact hKD x
  refine ⟨han, hper hp, fun θ => hh.differentiableAt_realHam (hmem θ), fun θ t => ?_,
    fun θ => ?_⟩
  · set x := θ + t • ω
    have hD : fderiv ℝ (realRestriction Kinf) x ω =
        hamiltonianVectorField (realHam h) (realRestriction Kinf x) := by
      apply realInclusion₂_injective n
      rw [(hd x).2 ω, hh.realInclusion₂_hamiltonianVectorField (hmem x), ← hKι,
        realInclusion_eq_ofReal]
      exact (sub_eq_zero.1 (hinv _ (realInclusion_mem_complexStrip hρ x))).symm
    have := (hd x).1.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_line θ ω t)
    rw [hD] at this
    exact this
  · have h1 := hh.ofReal_realHam (hmem θ)
    rw [← hKι, hE _ (realInclusion_mem_complexStrip hρ θ)] at h1
    exact_mod_cast h1

end Exact

/-- An orbit on a real model torus stays on it: its points are values of `k`. -/
theorem IsRealModelTorus.mem_range {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {ω : Fin n → ℝ} {E : ℝ}
    {k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} (_hk : IsRealModelTorus H ω E k)
    (θ : Fin n → ℝ) (t : ℝ) : k (θ + t • ω) ∈ range k :=
  mem_range_self _

/-- The frequency `s ω` of a scaled Diophantine vector is `(s γ, τ)`-Diophantine for `s > 0`. -/
theorem isDiophantine_mul_smul {γ τ s : ℝ} {ω : Fin n → ℝ} (hs : 0 < s)
    (hdio : IsDiophantine γ τ ω) : IsDiophantine (s * γ) τ (s • ω) := by
  intro k hk
  have hsum : ∑ i, (k i : ℝ) * (s • ω) i = s * ∑ i, (k i : ℝ) * ω i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsum, abs_mul, abs_of_pos hs, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (hdio k hk) hs.le

end KAM.Application
