/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Stability.RealSystem
public import KAM.Canonical.SymplecticForm

/-!
# Conjugation of real orbits by a real symplectic map (`bpN:p7:conjugation`)

If `H' = H ∘ Ψ` on `𝒟_{r',s'}` with `Ψ` holomorphic, symplectic, real on the real points and mapping
`𝒟_{r',s'}` into `𝒟_{r,s}`, then `t ↦ Re Ψ (z t)` is an `H`-orbit in `W_r` whenever `z` is an
`H'`-orbit in `W_{r'}`. The proof works with the complex Hamiltonian fields: `DΨ X_{H'} = X_H ∘ Ψ`
(`KAM.Canonical.map_hamiltonianJ_comp`), restricted to the real points through `real_system` (b).
-/

@[expose] public noncomputable section

open Set

namespace KAM.Stability

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

section Conj

variable {D : Set (Fin n → ℝ)} {r s r' s' : ℝ} {H H' : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

private theorem psi_real_eq (hΨreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ),
      KAM.realInclusion₂ n x ∈ Dom n (cpx D) r' s' →
      Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n))
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : KAM.realInclusion₂ n x ∈ Dom n (cpx D) r' s') :
    Ψ (KAM.realInclusion₂ n x) = KAM.realInclusion₂ n (reMap Ψ x) := by
  obtain ⟨y, hy⟩ := hΨreal x hx
  have : reMap Ψ x = y := by
    unfold reMap
    rw [← hy]
    ext i <;> simp
  rw [this, hy]

private theorem reMap_mem (hs : 0 < s)
    (hΨmap : MapsTo Ψ (Dom n (cpx D) r' s') (Dom n (cpx D) r s))
    (hΨreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Dom n (cpx D) r' s' →
      Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n))
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : KAM.realInclusion₂ n x ∈ Dom n (cpx D) r' s') :
    reMap Ψ x ∈ realStrip D r := by
  rw [← realInclusion₂_mem_Dom_iff D hs, ← psi_real_eq hΨreal hx]
  exact hΨmap hx

private theorem reMap_hasFDerivAt
    (hΨ : DifferentiableOn ℂ Ψ (Dom n (cpx D) r' s'))
    (hΨreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Dom n (cpx D) r' s' →
      Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n))
    (hs' : 0 < s') {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realStrip D r') :
    ∃ L : ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)),
      HasFDerivAt (reMap Ψ) L x ∧ ∀ u, KAM.realInclusion₂ n (L u) =
        fderiv ℂ Ψ (KAM.realInclusion₂ n x) (KAM.realInclusion₂ n u) := by
  have hxD : KAM.realInclusion₂ n x ∈ Dom n (cpx D) r' s' :=
    (realInclusion₂_mem_Dom_iff D hs' x).2 hx
  have hΨd : DifferentiableAt ℂ Ψ (KAM.realInclusion₂ n x) :=
    hΨ.differentiableAt ((isOpen_Dom _ _ _).mem_nhds hxD)
  have h2 : HasFDerivAt (fun y => Ψ (KAM.realInclusion₂ n y))
      (((fderiv ℂ Ψ (KAM.realInclusion₂ n x)).restrictScalars ℝ).comp (KAM.realInclusion₂ n)) x :=
    (hΨd.hasFDerivAt.restrictScalars ℝ).comp x (KAM.realInclusion₂ n).hasFDerivAt
  have h3 : HasFDerivAt (reMap Ψ) ((KAM.realPartCLM₂ n).comp
      (((fderiv ℂ Ψ (KAM.realInclusion₂ n x)).restrictScalars ℝ).comp (KAM.realInclusion₂ n))) x :=
    (KAM.realPartCLM₂ n).hasFDerivAt.comp x h2
  refine ⟨_, h3, fun u => ?_⟩
  have h4 : HasFDerivAt (fun y => KAM.realInclusion₂ n (reMap Ψ y))
      ((KAM.realInclusion₂ n).comp ((KAM.realPartCLM₂ n).comp
      (((fderiv ℂ Ψ (KAM.realInclusion₂ n x)).restrictScalars ℝ).comp (KAM.realInclusion₂ n)))) x :=
    (KAM.realInclusion₂ n).hasFDerivAt.comp x h3
  have hev : (fun y => KAM.realInclusion₂ n (reMap Ψ y)) =ᶠ[nhds x]
      fun y => Ψ (KAM.realInclusion₂ n y) := by
    have hmem : ∀ᶠ y in nhds x, y ∈ realStrip D r' :=
      (isOpen_univ.prod (isOpen_realNbhd D r')).mem_nhds hx
    filter_upwards [hmem] with y hy
    exact (psi_real_eq hΨreal ((realInclusion₂_mem_Dom_iff D hs' y).2 hy)).symm
  have h5 := (h4.congr_of_eventuallyEq hev.symm).unique h2
  exact congrArg (fun L => L u) h5

/-- `bpN:p7:conjugation`. -/
theorem conjugation {D : Set (Fin n → ℝ)} {r s r' s' : ℝ}
    {H H' : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hs : 0 < s) (hs' : 0 < s')
    (hH : InClass (cpx D) r s H) (hHr : RealOn (Dom n (cpx D) r s) H)
    (hH' : InClass (cpx D) r' s' H') (hH'r : RealOn (Dom n (cpx D) r' s') H')
    (hΨ : DifferentiableOn ℂ Ψ (Dom n (cpx D) r' s'))
    (hΨmap : MapsTo Ψ (Dom n (cpx D) r' s') (Dom n (cpx D) r s))
    (hΨreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Dom n (cpx D) r' s' →
      Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n))
    (hΨsympl : ∀ z ∈ Dom n (cpx D) r' s', ∀ v w,
      symplFormC (fderiv ℂ Ψ z v) (fderiv ℂ Ψ z w) = symplFormC v w)
    (hconj : ∀ z ∈ Dom n (cpx D) r' s', H' z = H (Ψ z))
    {J : Set ℝ} {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hz : IsOrbit H' D r' J z) :
    IsOrbit H D r J (fun t => reMap Ψ (z t)) := by
  intro t ht
  obtain ⟨hzt, hzd⟩ := hz t ht
  have hxD : KAM.realInclusion₂ n (z t) ∈ Dom n (cpx D) r' s' :=
    (realInclusion₂_mem_Dom_iff D hs' _).2 hzt
  refine ⟨reMap_mem hs hΨmap hΨreal hxD, ?_⟩
  obtain ⟨L, hL, hLι⟩ := reMap_hasFDerivAt hΨ hΨreal hs' hzt
  have hcomp := hL.comp_hasDerivAt t hzd
  -- the field identity `L X_{H'} = X_H ∘ reMap Ψ`
  have hψx : reMap Ψ (z t) ∈ realStrip D r := reMap_mem hs hΨmap hΨreal hxD
  have hrs' := (real_system hs' hH' hH'r).2.2.1 (z t) hzt
  have hrs := (real_system hs hH hHr).2.2.1 (reMap Ψ (z t)) hψx
  have hΨzd : DifferentiableAt ℂ Ψ (KAM.realInclusion₂ n (z t)) :=
    hΨ.differentiableAt ((isOpen_Dom _ _ _).mem_nhds hxD)
  have hHd : DifferentiableAt ℂ H (Ψ (KAM.realInclusion₂ n (z t))) :=
    hH.differentiableOn.differentiableAt
      ((isOpen_Dom _ _ _).mem_nhds (hΨmap hxD))
  have hev : H' =ᶠ[nhds (KAM.realInclusion₂ n (z t))] fun w => H (Ψ w) :=
    Filter.eventuallyEq_of_mem ((isOpen_Dom _ _ _).mem_nhds hxD) hconj
  have hderiv : fderiv ℂ H' (KAM.realInclusion₂ n (z t)) =
      (fderiv ℂ H (Ψ (KAM.realInclusion₂ n (z t)))).comp
        (fderiv ℂ Ψ (KAM.realInclusion₂ n (z t))) := by
    rw [hev.fderiv_eq]
    exact (hHd.hasFDerivAt.comp _ hΨzd.hasFDerivAt).fderiv
  have hfield := map_hamiltonianJ_comp (fderiv ℂ Ψ (KAM.realInclusion₂ n (z t)))
    (hΨsympl _ hxD) (fderiv ℂ H (Ψ (KAM.realInclusion₂ n (z t))))
  rw [← hderiv] at hfield
  have hmain : L (KAM.hamiltonianVectorField (realH H') (z t)) =
      KAM.hamiltonianVectorField (realH H) (reMap Ψ (z t)) := by
    apply KAM.realInclusion₂_injective n
    rw [hLι, hrs'.2, hrs.2, ← psi_real_eq hΨreal hxD]
    exact hfield
  rw [hmain] at hcomp
  exact hcomp

end Conj

end KAM.Stability

end
