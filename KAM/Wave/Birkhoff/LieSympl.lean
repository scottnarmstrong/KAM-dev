/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieNeumann

/-!
# Symplecticity of the flow (blueprint-W `bpW:w3:symplectic`, Step Constant form)

Package W3-FLOW, blueprint label `bpW:w3:symplectic`.

`hasDerivAt_omega_pair`: product rule for a continuous complex bilinear form along real curves.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A continuous `ℂ`-bilinear form as a continuous `ℝ`-bilinear map. -/
def bilinReal (Ω : E →L[ℂ] E →L[ℂ] ℂ) : E →L[ℝ] E →L[ℝ] ℂ :=
  (ContinuousLinearMap.restrictScalarsL ℂ E ℂ ℝ ℝ).comp (Ω.restrictScalars ℝ)

theorem bilinReal_apply (Ω : E →L[ℂ] E →L[ℂ] ℂ) (u v : E) : bilinReal Ω u v = Ω u v := rfl

theorem hasDerivAt_omega_pair (Ω : E →L[ℂ] E →L[ℂ] ℂ) {a b : ℝ → E} {a' b' : E} {s : ℝ}
    (ha : HasDerivAt a a' s) (hb : HasDerivAt b b' s) :
    HasDerivAt (fun r => Ω (a r) (b r)) (Ω a' (b s) + Ω (a s) b') s := by
  have h := (bilinReal Ω).hasFDerivAt_of_bilinear ha.hasFDerivAt hb.hasFDerivAt
  refine h.hasDerivAt.congr_deriv ?_
  rw [ContinuousLinearMap.add_apply]
  simp [bilinReal_apply, add_comm]

variable [CompleteSpace E] (T : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E) {C : ℝ}

theorem lieGammaD_zero (w : E) : lieGammaD T 0 w = ContinuousLinearMap.id ℂ E := by
  unfold lieGammaD
  rw [tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
  simp

variable (hC : 0 ≤ C) (hT : ∀ v : Fin 3 → E, ‖T v‖ ≤ C * ∏ i, ‖v i‖)

include hC hT in
/-- (`bpW:w3:symplectic`, Step Constant form) If `Ω(T(ξ,y,y),η)` is symmetric in `(ξ,η)` and
`Ω` is skew, then `Ω(DΓ_t ξ, DΓ_t η) = Ω(ξ,η)`. -/
theorem lie_symplectic
    (hsym : ∀ (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → E), T (fun i => v (σ i)) = T v)
    (Ω : E →L[ℂ] E →L[ℂ] ℂ) (hskew : ∀ u v, Ω u v = -Ω v u)
    (hΩT : ∀ y ξ η, Ω (T ![ξ, y, y]) η = Ω (T ![η, y, y]) ξ)
    (hCp : 0 < C) (t : ℝ) (w ξ η : E) (ht : |t| < 2) (hw : 40 * C * ‖w‖ ^ 2 < 1) :
    Ω (lieGammaD T t w ξ) (lieGammaD T t w η) = Ω ξ η := by
  have hder : ∀ s ∈ Set.Ioo (-2 : ℝ) 2,
      HasDerivAt (fun r : ℝ => Ω (lieGammaD T r w ξ) (lieGammaD T r w η)) 0 s := by
    intro s hs
    have hs' : |s| < 2 := abs_lt.2 ⟨hs.1, hs.2⟩
    have h1 := hasDerivAt_lieGammaD_var T hC hT hsym hCp s w ξ hs' hw
    have h2 := hasDerivAt_lieGammaD_var T hC hT hsym hCp s w η hs' hw
    have h := hasDerivAt_omega_pair Ω h1 h2
    refine h.congr_deriv ?_
    set y := lieGamma T s w
    set a := lieGammaD T s w ξ
    set b := lieGammaD T s w η
    rw [map_smul, ContinuousLinearMap.smul_apply, map_smul, hΩT y a b, hskew a (T ![b, y, y])]
    simp
  have hdiff : DifferentiableOn ℝ (fun r : ℝ => Ω (lieGammaD T r w ξ) (lieGammaD T r w η))
      (Set.Ioo (-2) 2) := fun s hs => (hder s hs).differentiableAt.differentiableWithinAt
  have h := (isOpen_Ioo (a := (-2 : ℝ)) (b := 2)).is_const_of_deriv_eq_zero
    (convex_Ioo (-2 : ℝ) 2).isPreconnected hdiff (fun s hs => (hder s hs).deriv)
    (x := t) (y := 0) (abs_lt.1 ht |> fun h => ⟨h.1, h.2⟩) (by simp)
  simpa [lieGammaD_zero] using h

end KAM.Wave

end
