/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Check.Domain

/-!
# The derivative of a tube observable in phase space (T2-CONF, N5b)

For an observable `G x = f (tubeChart V B x)` (`f` and `B` `2π`-periodic in `φ`), the derivative
at a point `x` with all rotated modes nonzero, in closed form: with `w = Vᵀx = (q, p)` and
`dw = Vᵀv`,

  `dI_j = q_j dq_j + p_j dp_j`, `dθ_j = (q_j dp_j - p_j dq_j) / (q_j² + p_j²)` (`polarInvD`),

and `dG(x) v = df(u, φ) (dI - dB(φ)(dφ), dφ)` with `dφ = phiOf dθ` (`shiftD`). This is the chain
`x → w → (I, θ) → (u, φ)` of SR-7; `polarInvD` inverts `fderiv polar` (`polarD_polarInvD`), and
`arg` is never differentiated: the local inverse of `polar` (N2) and periodicity replace it.

* `polarD_polarInvD`, `fderiv_polar_polarInvD`;
* `fderiv_comp_tubeChart_apply`: the closed-form derivative.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Set Filter Topology Matrix Real

variable {n : ℕ}

/-- The inverse of the polar derivative at `polarInv w` (equivalently, the derivative of a smooth
local inverse of `polar` through that lift), for nonzero modes, applied to `dw`:
`(q dq + p dp, (q dp - p dq) / (q² + p²))` per mode. It is not a derivative of `polarInv` itself,
whose `arg` lift is discontinuous on the cut `q = 0`, `p < 0`. -/
def polarInvD (w dw : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun j => w.1 j * dw.1 j + w.2 j * dw.2 j,
    fun j => (w.1 j * dw.2 j - w.2 j * dw.1 j) / (w.1 j ^ 2 + w.2 j ^ 2))

private theorem polarD_polarInvD_aux {q p s S C dq dp : ℝ} (hs : 0 < s)
    (hSC : S ^ 2 + C ^ 2 = 1) (hq : -s * S = q) (hp : s * C = p) :
    -((q * dq + p * dp) / s) * S - s * C * ((q * dp - p * dq) / (q ^ 2 + p ^ 2)) = dq ∧
      (q * dq + p * dp) / s * C - s * S * ((q * dp - p * dq) / (q ^ 2 + p ^ 2)) = dp := by
  subst hq hp
  have hN : (-s * S) ^ 2 + (s * C) ^ 2 = s ^ 2 := by linear_combination s ^ 2 * hSC
  rw [hN]
  have hs0 : s ≠ 0 := hs.ne'
  constructor
  · field_simp
    linear_combination dq * hSC
  · field_simp
    linear_combination dp * hSC

/-- `polarInvD w` inverts the derivative `polarD` of `polar` at `polarInv w`. -/
theorem polarD_polarInvD {w : (Fin n → ℝ) × (Fin n → ℝ)} (hw : ∀ j, 0 < w.1 j ^ 2 + w.2 j ^ 2)
    (dw : (Fin n → ℝ) × (Fin n → ℝ)) : polarD (polarInv w) (polarInvD w dw) = dw := by
  have hpp := polar_polarInv w
  have hy := polarInv_mem_actionPos hw
  have key : ∀ j, -((w.1 j * dw.1 j + w.2 j * dw.2 j) / √(2 * (polarInv w).1 j)) *
        sin ((polarInv w).2 j) - √(2 * (polarInv w).1 j) * cos ((polarInv w).2 j) *
          ((w.1 j * dw.2 j - w.2 j * dw.1 j) / (w.1 j ^ 2 + w.2 j ^ 2)) = dw.1 j ∧
      (w.1 j * dw.1 j + w.2 j * dw.2 j) / √(2 * (polarInv w).1 j) * cos ((polarInv w).2 j) -
        √(2 * (polarInv w).1 j) * sin ((polarInv w).2 j) *
          ((w.1 j * dw.2 j - w.2 j * dw.1 j) / (w.1 j ^ 2 + w.2 j ^ 2)) = dw.2 j := by
    intro j
    have h1 : (polar (polarInv w)).1 j = w.1 j := by rw [hpp]
    have h2 : (polar (polarInv w)).2 j = w.2 j := by rw [hpp]
    simp only [polar] at h1 h2
    exact polarD_polarInvD_aux (Real.sqrt_pos.2 (by have := hy j; positivity))
      (sin_sq_add_cos_sq _) h1 h2
  ext j
  · exact (key j).1
  · exact (key j).2

theorem fderiv_polar_polarInvD {w : (Fin n → ℝ) × (Fin n → ℝ)}
    (hw : ∀ j, 0 < w.1 j ^ 2 + w.2 j ^ 2) (dw : (Fin n → ℝ) × (Fin n → ℝ)) :
    fderiv ℝ polar (polarInv w) (polarInvD w dw) = dw := by
  rw [fderiv_polar_apply (polarInv_mem_actionPos hw)]
  exact polarD_polarInvD hw dw

/-- The derivative of a local inverse `ψ` of `polar` at `w` is `polarInvD w`. -/
theorem fderiv_localInverse_eq {w : (Fin n → ℝ) × (Fin n → ℝ)}
    (hw : ∀ j, 0 < w.1 j ^ 2 + w.2 j ^ 2)
    {ψ : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hψd : DifferentiableAt ℝ ψ w) (hψw : ψ w = polarInv w)
    (hev : ∀ᶠ z in 𝓝 w, polar (ψ z) = z) (dw : (Fin n → ℝ) × (Fin n → ℝ)) :
    fderiv ℝ ψ w dw = polarInvD w dw := by
  have hy := polarInv_mem_actionPos hw
  have hpol : HasFDerivAt polar (fderiv ℝ polar (polarInv w)) (ψ w) := by
    rw [hψw]; exact (differentiableAt_polar hy).hasFDerivAt
  have hc : HasFDerivAt (polar ∘ ψ) ((fderiv ℝ polar (polarInv w)).comp (fderiv ℝ ψ w)) w :=
    hpol.comp w hψd.hasFDerivAt
  have hid : HasFDerivAt (polar ∘ ψ) (ContinuousLinearMap.id ℝ _) w :=
    (hasFDerivAt_id w).congr_of_eventuallyEq (by
      filter_upwards [hev] with z hz using hz)
  have hu := hc.unique hid
  have h1 : fderiv ℝ polar (polarInv w) (fderiv ℝ ψ w dw) = dw := by
    have := congrArg (fun L : _ →L[ℝ] _ => L dw) hu
    simpa using this
  have hinj : Function.Injective (fderiv ℝ polar (polarInv w)) := fun a b h =>
    (polarEquiv hy).injective h
  exact hinj (h1.trans (fderiv_polar_polarInvD hw dw).symm)

/-- **The derivative of a tube observable.** For `2π`-periodic `B` and `f`, at `x` with all rotated
modes nonzero, with `f` differentiable at `tubeChart V B x` and `B` at its `φ`:
`dG(x) v = df(u, φ) (shiftD (dB(φ)) (polarInvD (Vᵀx) (Vᵀv)))`. -/
theorem fderiv_comp_tubeChart_apply {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : Vᵀ * V = 1)
    {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} {f : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    (hBper : ShiftPeriodic B) (hfper : ObsPeriodic f) {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hx : x ∈ modesPos V) (hf : DifferentiableAt ℝ f (tubeChart V B x))
    (hB : DifferentiableAt ℝ B (tubeChart V B x).2) (v : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    fderiv ℝ (fun x => f (tubeChart V B x)) x v =
      fderiv ℝ f (tubeChart V B x)
        (shiftD (fderiv ℝ B (tubeChart V B x).2) (polarInvD (rotMap Vᵀ x) (rotMap Vᵀ v))) := by
  have hw : ∀ j, 0 < (rotMap Vᵀ x).1 j ^ 2 + (rotMap Vᵀ x).2 j ^ 2 := hx
  have hy := polarInv_mem_actionPos hw
  obtain ⟨ψ, hψ, hψy, hev⟩ := exists_polar_localInverse hy (k := 1) one_ne_zero
  rw [polar_polarInv] at hψ hψy hev
  have hψd : DifferentiableAt ℝ ψ (rotMap Vᵀ x) := hψ.differentiableAt one_ne_zero
  have hg : HasFDerivAt (f ∘ shiftChart B)
      ((fderiv ℝ f (tubeChart V B x)).comp (shiftD (fderiv ℝ B (tubeChart V B x).2)))
      (ψ (rotMap Vᵀ x)) := by
    rw [hψy]
    exact hf.hasFDerivAt.comp (polarInv (rotMap Vᵀ x)) (hasFDerivAt_shiftChart hB)
  have hcomp := hg.comp x (hψd.hasFDerivAt.comp x (hasFDerivAt_rotMap Vᵀ x))
  have heq : (fun x' => f (tubeChart V B x')) =ᶠ[𝓝 x]
      ((f ∘ shiftChart B) ∘ ψ ∘ rotMap Vᵀ) := by
    have hev' := ((continuous_rotMap Vᵀ).tendsto x).eventually hev
    filter_upwards [hev'] with x' hx'
    have h := comp_tubeChart_rotMap_polar hV hBper hfper hx'.1
    rw [hx'.2, rotMap_rotMap_transpose hV] at h
    exact h
  rw [heq.fderiv_eq, hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, rotCLM_apply]
  rw [fderiv_localInverse_eq hw hψd hψy (hev.mono fun _ h => h.2)]

end KAM.EffectiveStability.Tube

end
