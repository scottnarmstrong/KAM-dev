/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import KAM.Nekhoroshev.Stability.Gradient
public import KAM.Nekhoroshev.Stability.RealSystem

/-!
# Drift of the actions along an orbit (auxiliary to `bpN:p7:nonresonant`)

* `thetaGradR_realH_re`: the real `θ`-gradient of `realH u` is the real part of `dtheta u`.
* `norm_thetaGradR_le`: the bound `|∂_θ u| ≤ M/(e s)` on real points.
* `thetaGradR_realH_add`, `thetaGradR_h_add`: additivity, and `h(I)` does not contribute.
* `drift_bound`: if `‖∂_θ G^ℝ‖ ≤ B` on `W_ϱ`, a `G`-orbit has `‖I(t) - I(0)‖ ≤ |t| B`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Stability

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

/-- The real `θ`-gradient of `realH u` at a real point is the real part of `∂_θ u`. -/
theorem thetaGradR_realH_re {D : Set (Fin n → ℝ)} {r s : ℝ}
    {g : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hs : 0 < s) (hg : InClass (cpx D) r s g)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realStrip D r) (i : Fin n) :
    thetaGradR (realH g) x i = (dtheta i g (KAM.realInclusion₂ n x)).re := by
  have hxD : KAM.realInclusion₂ n x ∈ Dom n (cpx D) r s := (realInclusion₂_mem_Dom_iff D hs x).2 hx
  have hgd : DifferentiableAt ℂ g (KAM.realInclusion₂ n x) :=
    hg.differentiableOn.differentiableAt ((isOpen_Dom (n := n) (cpx D) r s).mem_nhds hxD)
  have h2 : HasFDerivAt (fun y => g (KAM.realInclusion₂ n y))
      (((fderiv ℂ g (KAM.realInclusion₂ n x)).restrictScalars ℝ).comp (KAM.realInclusion₂ n)) x :=
    (hgd.hasFDerivAt.restrictScalars ℝ).comp x (KAM.realInclusion₂ n).hasFDerivAt
  have h3 := congrArg (fun L => L (Pi.single i 1, 0)) (Complex.reCLM.hasFDerivAt.comp x h2).fderiv
  unfold thetaGradR realH dtheta
  rw [show (fun y => (g (KAM.realInclusion₂ n y)).re) =
    Complex.reCLM ∘ (fun y => g (KAM.realInclusion₂ n y)) from rfl]
  simpa [KAM.realInclusion_single] using h3

/-- `‖∂_θ u^ℝ‖ ≤ M/(e s)` on `W_ϱ`. -/
theorem norm_thetaGradR_le {D : Set (Fin n → ℝ)} {ϱ s M : ℝ} {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hs : 0 < s) (hu : InClass (cpx D) ϱ s u) (hb : WBound (cpx D) ϱ s u M)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realStrip D ϱ) :
    ‖thetaGradR (realH u) x‖ ≤ M / (Real.exp 1 * s) := by
  have h1 := (theta_derivative hs hu hb).1 x.1 x.2 hx.2
  have hM : 0 ≤ M / (Real.exp 1 * s) :=
    le_trans (Finset.sum_nonneg fun j _ => norm_nonneg _) h1.1
  refine (pi_norm_le_iff_of_nonneg hM).2 fun j => ?_
  rw [thetaGradR_realH_re hs hu hx j, Real.norm_eq_abs]
  refine (Complex.abs_re_le_norm _).trans (le_trans ?_ h1.1)
  exact Finset.single_le_sum (f := fun j => ‖dtheta j u (KAM.realInclusion₂ n (x.1, x.2))‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

/-- Additivity of the real `θ`-gradient. -/
theorem thetaGradR_realH_add {D : Set (Fin n → ℝ)} {r s : ℝ}
    {G u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hs : 0 < s) (hG : InClass (cpx D) r s G)
    (hGr : RealOn (Dom n (cpx D) r s) G) (hu : InClass (cpx D) r s u)
    (hur : RealOn (Dom n (cpx D) r s) u) {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realStrip D r) :
    thetaGradR (realH (fun w => G w + u w)) x =
      thetaGradR (realH G) x + thetaGradR (realH u) x := by
  have hd1 := ((real_system hs hG hGr).2.2.1 x hx).1
  have hd2 := ((real_system hs hu hur).2.2.1 x hx).1
  have : realH (fun w => G w + u w) = fun y => realH G y + realH u y := by
    funext y
    simp [realH]
  ext i
  unfold thetaGradR
  have hf : fderiv ℝ (fun y => realH G y + realH u y) x =
      fderiv ℝ (realH G) x + fderiv ℝ (realH u) x := (hd1.hasFDerivAt.add hd2.hasFDerivAt).fderiv
  rw [this, hf]
  rfl

theorem inClass_snd {D : Set (Fin n → ℝ)} {r s : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (polyNbhd (cpx D) r)) :
    InClass (cpx D) r s (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2) :=
  ⟨hh.comp differentiableOn_snd fun _ hz => hz.2, fun _ _ _ => rfl⟩

/-- A function of the actions alone has zero real `θ`-gradient. -/
theorem thetaGradR_snd {D : Set (Fin n → ℝ)} {r s : ℝ} {h : (Fin n → ℂ) → ℂ} (hs : 0 < s)
    (hh : DifferentiableOn ℂ h (polyNbhd (cpx D) r))
    (hhr : RealOn (Dom n (cpx D) r s) (fun w => h w.2)) {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realStrip D r) :
    thetaGradR (realH (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2)) x = 0 := by
  have hd := ((real_system hs (inClass_snd (s := s) hh) hhr).2.2.1 x hx).1
  ext i
  have hc : HasDerivAt (fun t : ℝ => x + t • ((Pi.single i 1 : Fin n → ℝ), (0 : Fin n → ℝ)))
      ((Pi.single i 1 : Fin n → ℝ), (0 : Fin n → ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      ((Pi.single i 1 : Fin n → ℝ), (0 : Fin n → ℝ))).const_add x
  have hd' : HasFDerivAt (realH (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2))
      (fderiv ℝ (realH (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2)) x)
      ((fun t : ℝ => x + t • ((Pi.single i 1 : Fin n → ℝ), (0 : Fin n → ℝ))) 0) := by
    simpa using hd.hasFDerivAt
  have hcomp := hd'.comp_hasDerivAt (0 : ℝ) hc
  have hconst : (realH (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2)) ∘
      (fun t : ℝ => x + t • ((Pi.single i 1 : Fin n → ℝ), (0 : Fin n → ℝ))) =
      fun _ => realH (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2) x := by
    funext t
    simp [realH, KAM.realInclusion₂]
  rw [hconst] at hcomp
  have := hcomp.unique (hasDerivAt_const _ _)
  simpa [thetaGradR] using this

/-- `h(I)` does not contribute to the real `θ`-gradient. -/
theorem thetaGradR_h_add {D : Set (Fin n → ℝ)} {r s : ℝ} {h : (Fin n → ℂ) → ℂ}
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hs : 0 < s)
    (hh : DifferentiableOn ℂ h (polyNbhd (cpx D) r))
    (hhr : RealOn (Dom n (cpx D) r s) (fun w => h w.2)) (hu : InClass (cpx D) r s u)
    (hur : RealOn (Dom n (cpx D) r s) u) {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realStrip D r) :
    thetaGradR (realH (fun w => h w.2 + u w)) x = thetaGradR (realH u) x := by
  rw [thetaGradR_realH_add hs (inClass_snd hh) hhr hu hur hx, thetaGradR_snd hs hh hhr hx,
    zero_add]

/-- If `‖∂_θ G^ℝ‖ ≤ B` on `W_ϱ`, the actions of a `G`-orbit drift at most `|t| B`. -/
theorem drift_bound {G : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {D : Set (Fin n → ℝ)} {ϱ B : ℝ}
    (hB : ∀ x ∈ realStrip D ϱ, ‖thetaGradR (realH G) x‖ ≤ B) {J : Set ℝ} (hJ : J.OrdConnected)
    (h0 : (0 : ℝ) ∈ J) {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hz : IsOrbit G D ϱ J z) {t : ℝ}
    (ht : t ∈ J) : ‖(z t).2 - (z 0).2‖ ≤ |t| * B := by
  have hsub : uIcc (0 : ℝ) t ⊆ J := hJ.uIcc_subset h0 ht
  have hder : ∀ τ ∈ uIcc (0 : ℝ) t, HasDerivWithinAt (fun τ => (z τ).2)
      (-thetaGradR (realH G) (z τ)) (uIcc (0 : ℝ) t) τ := fun τ hτ => by
    have := ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)).hasFDerivAt.comp_hasDerivAt τ
      (hz τ (hsub hτ)).2)
    exact this.hasDerivWithinAt
  have := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le hder
    (fun τ hτ => by rw [norm_neg]; exact hB _ (hz τ (hsub hτ)).1) left_mem_uIcc right_mem_uIcc
  simpa [mul_comm] using this

end KAM.Stability

end
