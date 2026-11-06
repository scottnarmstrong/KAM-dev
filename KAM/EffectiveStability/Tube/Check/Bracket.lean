/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Chart.Shift
public import KAM.EffectiveStability.Tube.Trig.TubeClose

/-!
# The reduced bracket through slice partials, and its perturbation (T2-CONF, N5b)

N2's `reducedBracket f h (u, φ)` uses joint derivatives of functions on `(Fin 3 → ℝ) × (Fin 2 → ℝ)`;
N3's tube models (`TubeClose`) are curried, `F u φ`, with slice partials `upd` (in `u`) and
`pderiv` (in `φ`). This file connects them:

* `sliceBracket F G u φ = Σ_a (D_a F · ∂_{φ_a} G - ∂_{φ_a} F · D_a G)` with
  `D_a = ∂_{u_a} - ∂_{u_2}`, in slice partials;
* `reducedBracket_eq_sliceBracket`: equal to `reducedBracket` when both functions are jointly
  differentiable at `(u, φ)`;
* `abs_sliceBracket_sub_le`: replacing `G` by a model `Ĝ` with `TubeClose G Ĝ r e₀ e₁ e₂` changes
  the bracket at `u` in the box by at most `Σ_a (|D_a F| e₁ + 2 |∂_{φ_a} F| e₂)`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

/-- The reduced bracket in slice partials:
`Σ_a ((∂_{u_a} F - ∂_{u_2} F) ∂_{φ_a} G - ∂_{φ_a} F (∂_{u_a} G - ∂_{u_2} G))` at `(u, φ)`. -/
def sliceBracket (F G : (Fin 3 → ℝ) → (Fin 2 → ℝ) → ℝ) (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) : ℝ :=
  ∑ a : Fin 2,
    ((upd F u φ a.castSucc - upd F u φ 2) * pderiv (G u) φ a -
      pderiv (F u) φ a * (upd G u φ a.castSucc - upd G u φ 2))

theorem fderiv_apply_single_fst_eq_upd {f : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {u : Fin 3 → ℝ} {φ : Fin 2 → ℝ} (hf : DifferentiableAt ℝ f (u, φ)) (l : Fin 3) :
    fderiv ℝ f (u, φ) (Pi.single l 1, 0) = upd (fun v ψ => f (v, ψ)) u φ l := by
  have h : HasFDerivAt (fun v => f (v, φ))
      ((fderiv ℝ f (u, φ)).comp (ContinuousLinearMap.inl ℝ (Fin 3 → ℝ) (Fin 2 → ℝ))) u :=
    hf.hasFDerivAt.comp u (hasFDerivAt_prodMk_left u φ)
  simp only [upd, h.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

theorem fderiv_apply_single_snd_eq_pderiv {f : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {u : Fin 3 → ℝ} {φ : Fin 2 → ℝ} (hf : DifferentiableAt ℝ f (u, φ)) (b : Fin 2) :
    fderiv ℝ f (u, φ) (0, Pi.single b 1) = pderiv (fun ψ => f (u, ψ)) φ b := by
  have h : HasFDerivAt (fun ψ => f (u, ψ))
      ((fderiv ℝ f (u, φ)).comp (ContinuousLinearMap.inr ℝ (Fin 3 → ℝ) (Fin 2 → ℝ))) φ :=
    hf.hasFDerivAt.comp φ (hasFDerivAt_prodMk_right u φ)
  simp only [pderiv, h.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- `reducedBracket` in slice partials, for jointly differentiable `f`, `h`. -/
theorem reducedBracket_eq_sliceBracket {f h : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {u : Fin 3 → ℝ} {φ : Fin 2 → ℝ} (hf : DifferentiableAt ℝ f (u, φ))
    (hh : DifferentiableAt ℝ h (u, φ)) :
    reducedBracket f h (u, φ) =
      sliceBracket (fun v ψ => f (v, ψ)) (fun v ψ => h (v, ψ)) u φ := by
  simp only [reducedBracket, sliceBracket, fderiv_apply_single_fst_eq_upd hf,
    fderiv_apply_single_fst_eq_upd hh, fderiv_apply_single_snd_eq_pderiv hf,
    fderiv_apply_single_snd_eq_pderiv hh]

/-- **Perturbation of the bracket by a tube model.** If `TubeClose G Ĝ r e₀ e₁ e₂` and `u` is in the
box, `|sliceBracket F G u φ - sliceBracket F Ĝ u φ| ≤ Σ_a (|D_a F| e₁ + 2 |∂_{φ_a} F| e₂)`. -/
theorem abs_sliceBracket_sub_le {F G Ĝ : (Fin 3 → ℝ) → (Fin 2 → ℝ) → ℝ} {r e₀ e₁ e₂ : ℝ}
    (hc : TubeClose G Ĝ r e₀ e₁ e₂) {u : Fin 3 → ℝ} (hu : InBox r u) (φ : Fin 2 → ℝ) :
    |sliceBracket F G u φ - sliceBracket F Ĝ u φ| ≤
      ∑ a : Fin 2, (|upd F u φ a.castSucc - upd F u φ 2| * e₁ +
        |pderiv (F u) φ a| * (2 * e₂)) := by
  rw [sliceBracket, sliceBracket, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  have h1 := hc.dφ u hu φ a
  have h2 := hc.du u hu φ a.castSucc
  have h3 := hc.du u hu φ 2
  have hD : |upd G u φ a.castSucc - upd G u φ 2 - (upd Ĝ u φ a.castSucc - upd Ĝ u φ 2)| ≤
      2 * e₂ := by
    calc |upd G u φ a.castSucc - upd G u φ 2 - (upd Ĝ u φ a.castSucc - upd Ĝ u φ 2)|
        = |(upd G u φ a.castSucc - upd Ĝ u φ a.castSucc) - (upd G u φ 2 - upd Ĝ u φ 2)| := by
          ring_nf
      _ ≤ e₂ + e₂ := (abs_sub _ _).trans (add_le_add h2 h3)
      _ = 2 * e₂ := by ring
  calc |(upd F u φ a.castSucc - upd F u φ 2) * pderiv (G u) φ a -
          pderiv (F u) φ a * (upd G u φ a.castSucc - upd G u φ 2) -
        ((upd F u φ a.castSucc - upd F u φ 2) * pderiv (Ĝ u) φ a -
          pderiv (F u) φ a * (upd Ĝ u φ a.castSucc - upd Ĝ u φ 2))|
      = |(upd F u φ a.castSucc - upd F u φ 2) * (pderiv (G u) φ a - pderiv (Ĝ u) φ a) -
          pderiv (F u) φ a * (upd G u φ a.castSucc - upd G u φ 2 -
            (upd Ĝ u φ a.castSucc - upd Ĝ u φ 2))| := by ring_nf
    _ ≤ |upd F u φ a.castSucc - upd F u φ 2| * e₁ + |pderiv (F u) φ a| * (2 * e₂) := by
        refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
        · exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_left hD (abs_nonneg _)

end KAM.EffectiveStability.Tube

end
