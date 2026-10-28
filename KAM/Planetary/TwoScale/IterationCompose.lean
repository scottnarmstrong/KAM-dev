/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.StepMono
public import KAM.Planetary.TwoScale.StepFreq

/-!
# Two-scale KAM iteration: composition of stage maps and restriction of `KamHyp`

Generic facts used by `iterative` (design package P23-16, node `stepP:p3:it-comp`): the
differentiability, injectivity, reality, lattice-equivariance and symplecticity of a composite
`Φ ∘ Ψ` on a set `V ⊆ Vb`, when `Ψ` has these properties on the open set `Vb` and maps it into the
open set `W` on which `Φ` has them; and the restriction of the hypothesis bundle to a smaller base
set.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {n : ℕ}

/-- The lattice shift of a phase point. -/
abbrev latticeShift (k : Fin n → ℤ) : CPhase n := ((fun i => (k i : ℂ)), 0)

/-- The five invariants carried by a stage map `Φ` on a domain `V`. -/
structure PhaseProps (Φ : CPhase n → CPhase n) (V : Set (CPhase n)) : Prop where
  diff : DifferentiableOn ℂ Φ V
  inj : Set.InjOn Φ V
  real : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ V →
    Φ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n)
  per : ∀ z ∈ V, ∀ k : Fin n → ℤ, Φ (z + latticeShift k) = Φ z + latticeShift k
  symp : ∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ Φ z u) (fderiv ℂ Φ z v) = symplFormC u v

theorem PhaseProps.id (V : Set (CPhase n)) : PhaseProps (id : CPhase n → CPhase n) V where
  diff := differentiableOn_id
  inj := injOn_id _
  real x _ := ⟨x, rfl⟩
  per _ _ _ := rfl
  symp z _ u v := by simp

theorem PhaseProps.comp {Ψ Φ : CPhase n → CPhase n} {Vb W V : Set (CPhase n)}
    (hVb : IsOpen Vb) (hW : IsOpen W) (hV : V ⊆ Vb) (hm : MapsTo Ψ Vb W)
    (hΨ : PhaseProps Ψ Vb) (hΦ : PhaseProps Φ W) : PhaseProps (Φ ∘ Ψ) V where
  diff := (hΦ.diff.comp hΨ.diff hm).mono hV
  inj := (hΦ.inj.comp hΨ.inj hm).mono hV
  real x hx := by
    obtain ⟨y, hy⟩ := hΨ.real x (hV hx)
    have hmem : KAM.realInclusion₂ n y ∈ W := by rw [hy]; exact hm (hV hx)
    obtain ⟨w, hw⟩ := hΦ.real y hmem
    exact ⟨w, by simp only [Function.comp_apply, ← hy, hw]⟩
  per z hz k := by
    simp only [Function.comp_apply, hΨ.per z (hV hz) k]
    exact hΦ.per _ (hm (hV hz)) k
  symp z hz u v := by
    have h1 : DifferentiableAt ℂ Ψ z := (hΨ.diff z (hV hz)).differentiableAt (hVb.mem_nhds (hV hz))
    have h2 : DifferentiableAt ℂ Φ (Ψ z) :=
      (hΦ.diff _ (hm (hV hz))).differentiableAt (hW.mem_nhds (hm (hV hz)))
    rw [fderiv_comp z h2 h1]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hΦ.symp _ (hm (hV hz)), hΨ.symp z (hV hz)]

theorem isOpen_coefficientDom (D : Set (Fin n → ℝ)) (r σ : ℝ) : IsOpen (coefficientDom D r σ) := by
  rw [(conv_data D r σ).2]
  exact (KAM.isOpen_complexStrip n _).prod (isOpen_actionNbhd' D r)

namespace KamHyp

variable {a b : ℕ} {D D' : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

/-- Restriction of the hypothesis bundle to a smaller base set. -/
theorem restrict (H : KamHyp D sbar p h f) (hD : D' ⊆ D) : KamHyp D' sbar p h f := by
  have hN : ∀ r, KAM.actionNbhd D' r ⊆ KAM.actionNbhd D r := fun r I ⟨J, hJ, hI⟩ => ⟨J, hD hJ, hI⟩
  have hdom : ∀ r σ, coefficientDom D' r σ ⊆ coefficientDom D r σ := fun r σ =>
    coefficientDom_mono (hN r) le_rfl
  have hP : polyNbhd (realBase D') p.ρ ⊆ polyNbhd (realBase D) p.ρ := polyNbhd_realBase_subset (hN _)
  refine ⟨H.a_pos, H.b_pos, H.τ_gt, H.positive, H.gamma_order, H.widths, H.normalized, H.L_bound,
    H.holo.mono (hN _), fun z hz => H.real_h z (hdom _ _ hz), fun z hz => H.real_f z (hdom _ _ hz),
    inClass_mono_set H.f_class hP le_rfl, wbound_mono_set H.f_bound hP le_rfl le_rfl,
    H.injective.mono (hN _), fun I hI => H.hessian I (hN _ hI), H.small⟩

end KamHyp

end KAM.Planetary

end
