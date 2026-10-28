/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Nekhoroshev.Stability.Gradient
public import KAM.Weighted.Cauchy
public import KAM.Weighted.SupWeighted
public import KAM.Strip.Bridges
public import KAM.Strip.Periodic
public import KAM.ODE.Maximal

/-!
# Real extended systems (`bpN:p11:real-system`)

For `H ∈ O(R,s)^{e,ℝ}`: the real restriction `realHamiltonianExt b R H` is `C^∞` on
`W^e_R = b.realDom R`, periodic in the angles, its weighted field is the restriction of the complex
weighted field (also periodic and `C¹`), and the energy is conserved along orbits.  Also the
fixed-base derivative bound `real_system_bounds` and the resonant-gradient statement
`real_system_resonant`.  The proofs follow Part 7 (`KAM.Stability.real_system`) on the unequal
product `EC n k`: the regrouping is proved by component identities.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.NormalForm

variable {n k : ℕ}

private theorem extCx_eq (z : ER n k) :
    extCx z = (KAM.realInclusion n z.1, KAM.realInclusion (n+(k+k)) z.2) := by
  ext i <;> simp [extCx]

/-- The real points of `EC n k` as a continuous `ℝ`-linear map. -/
private def extCxCLM (n k : ℕ) : ER n k →L[ℝ] EC n k :=
  (KAM.realInclusion n).prodMap (KAM.realInclusion (n+(k+k)))

private theorem extCxCLM_apply (z : ER n k) : extCxCLM n k z = extCx z := (extCx_eq z).symm

private theorem extCx_eq_clm : (extCx : ER n k → EC n k) = extCxCLM n k :=
  funext fun z => (extCxCLM_apply z).symm

private theorem extCx_mem_Dom_iff (b : PartialBlock n k) {R s : ℝ} (hs : 0 < s) (z : ER n k) :
    extCx z ∈ Dom n b.base R s ↔ (extCx z).2 ∈ polyNbhd b.base R := by
  simp only [Dom, mem_prod]
  exact ⟨fun h => h.2, fun h => ⟨KAM.ofReal_mem_complexStrip hs z.1, h⟩⟩

private theorem mem_realDom_iff (b : PartialBlock n k) (R : ℝ) (z : ER n k) :
    z ∈ b.realDom R ↔ (extCx z).2 ∈ polyNbhd b.base R :=
  extCx_mem_Dom_iff b one_pos z

private theorem isOpen_realDom (b : PartialBlock n k) (R : ℝ) : IsOpen (b.realDom R) := by
  have hc : Continuous (extCx : ER n k → EC n k) := by
    rw [extCx_eq_clm]; exact (extCxCLM n k).continuous
  exact (isOpen_Dom (n := n) b.base R 1).preimage hc

private theorem realDom_mono (b : PartialBlock n k) {R R' : ℝ} (h : R' ≤ R) :
    b.realDom R' ⊆ b.realDom R := fun z hz =>
  (mem_realDom_iff b R z).2 (polyNbhd_mono h ((mem_realDom_iff b R' z).1 hz))

private theorem realDom_shift (b : PartialBlock n k) (R : ℝ) (ℓ : Fin n → ℤ) (z : ER n k) :
    (z.1 + (fun i => (ℓ i : ℝ)), z.2) ∈ b.realDom R ↔ z ∈ b.realDom R := by
  rw [mem_realDom_iff, mem_realDom_iff]
  rfl

private theorem hreal_of_ext {b : PartialBlock n k} {R s : ℝ} {H : EC n k → ℂ}
    (hH : ext_class b R s H) (y : ER n k) (hy : extCx y ∈ Dom n b.base R s) :
    (H (extCx y)).im = 0 := by
  have := hH.2 y (by rw [← extCx_eq]; exact hy)
  rwa [← extCx_eq] at this

private theorem realHamiltonianExt_eventually (b : PartialBlock n k) (R : ℝ) (H : EC n k → ℂ)
    {z : ER n k} (hz : z ∈ b.realDom R) :
    ∀ᶠ y in nhds z, realHamiltonianExt b R H y = (H (extCx y)).re := by
  filter_upwards [(isOpen_realDom b R).mem_nhds hz] with y hy
  simp [realHamiltonianExt, indicator_of_mem hy]

/-- Real derivative transport on `EC n k` (the unequal-carrier form of
`KAM.hamiltonian_real_fderiv`). -/
private theorem fderiv_ext_real {V : Set (EC n k)} {H : EC n k → ℂ} {Hr : ER n k → ℝ}
    {z : ER n k} (hV : IsOpen V) (hh : DifferentiableOn ℂ H V)
    (hreal : ∀ y : ER n k, extCx y ∈ V → (H (extCx y)).im = 0)
    (hz : extCx z ∈ V) (hH : ∀ᶠ y in nhds z, Hr y = (H (extCx y)).re) :
    DifferentiableAt ℝ Hr z ∧ ∀ e : ER n k,
      ((fderiv ℝ Hr z e : ℝ) : ℂ) = fderiv ℂ H (extCx z) (extCx e) := by
  set L := extCxCLM n k with hL
  have hz' : L z ∈ V := by rwa [hL, extCxCLM_apply]
  have hhd : DifferentiableAt ℂ H (L z) := hh.differentiableAt (hV.mem_nhds hz')
  have h2 : HasFDerivAt (fun y => H (L y))
      (((fderiv ℂ H (L z)).restrictScalars ℝ).comp L) z :=
    (hhd.hasFDerivAt.restrictScalars ℝ).comp z L.hasFDerivAt
  have h3 : HasFDerivAt (fun y => (H (L y)).re)
      (Complex.reCLM.comp (((fderiv ℂ H (L z)).restrictScalars ℝ).comp L)) z :=
    Complex.reCLM.hasFDerivAt.comp z h2
  have hH' : ∀ᶠ y in nhds z, Hr y = (H (L y)).re := by
    simpa only [hL, extCxCLM_apply] using hH
  have h4 : HasFDerivAt Hr (Complex.reCLM.comp
      (((fderiv ℂ H (L z)).restrictScalars ℝ).comp L)) z := h3.congr_of_eventuallyEq hH'
  refine ⟨h4.differentiableAt, fun e => ?_⟩
  have hmem : ∀ᶠ y in nhds z, L y ∈ V := L.continuous.continuousAt.eventually_mem (hV.mem_nhds hz')
  have hev : (fun y => H (L y)) =ᶠ[nhds z] fun y => ((Hr y : ℝ) : ℂ) := by
    filter_upwards [hH', hmem] with y hy hyV
    rw [hy]
    refine Complex.ext (by simp) ?_
    simpa [hL, extCxCLM_apply] using hreal y (by rwa [← extCxCLM_apply])
  have h5 : HasFDerivAt (fun y => ((Hr y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ Hr z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z h4.differentiableAt.hasFDerivAt
  have h6 := (h2.congr_of_eventuallyEq hev.symm).unique h5
  have := (congrArg (fun L => L e) h6).symm
  simpa [hL, extCxCLM_apply] using this

end KAM.Nekhoroshev

end
