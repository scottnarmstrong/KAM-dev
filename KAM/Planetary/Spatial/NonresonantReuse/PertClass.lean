/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.NonresonantReuse.Pert
public import KAM.Planetary.StrongAMD.NonresonantReuse.PertClass

/-!
# The spatial perturbation is in the engine's class

Source: MAIN Lemma 13 with `2n` slow pairs (`LP:MAIN L13 (441–458)`,
`LP:MAIN T19 (599–603)`), N6, track LP, non-frozen.

* `lpPertNM_extClass`: `ext_class b b.rB t (lpPertNM μ b.lam fc)` for `b : PartialBlock n (n + n)`
  (holomorphy and period-one periodicity from `fc`, reality from the real trace), `2π t ≤ 4 s₀`;
* `lpPertNM_sup_le`: the sup bound `μ M/(2π)` on `Dom n b.base b.rB t`;
* `lpPertNM_wbound`: `WBound b.base b.rB s (lpPertNM μ b.lam fc) (lpM₂ n σ M * μ)` via
  `wbound_of_sup_bound` (the constant `lpM₂` is the planar one, dimension-free).
-/

@[expose] public noncomputable section

open KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Nekhoroshev KAM.Weighted Set

namespace KAM.Planetary.Spatial

variable {n : ℕ} {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ rg R M : ℝ}
  {fc : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) → ℂ}

theorem lpTubeNM_mono (hR : 0 < R) {K : Set (Phase (n + (n + n)))} {z}
    (hz : z ∈ complexTubeNM K (R / 2)) : z ∈ complexTubeNM K R :=
  let ⟨x, hx, hlt⟩ := hz
  ⟨x, hx, hlt.trans (half_lt_self hR)⟩

section
variable {rs s₀ b₀ : ℝ} {I0 : Fin n → ℝ} {b : PartialBlock n (n + n)}

theorem lpPertNM_dom_mem (hrs : 0 < rs) (hrg : rs ≤ 4 * rg)
    (hmax : max rs (max (4 * s₀) (4 * b₀)) < R / 2) (hI0 : I0 ∈ strongLevelSet ν L δ)
    (hS : b.S = spatialSecularBall ν δ I0) (hIc : b.Ic = I0) (hrB : b.rB ≤ rs)
    (hrB0 : 0 < b.rB) (hw0 : 0 < b.w) (hw : b.w < 4 * b₀) {t : ℝ} (ht : 0 < t)
    (hts : 2 * Real.pi * t ≤ 4 * s₀) {z : EC n (n + n)} (hz : z ∈ Dom n b.base b.rB t) :
    lpUnrescaleCNM b.lam z ∈ complexTubeNM (spatialStrongCore ν L δ rg) (R / 2) :=
  lpUnrescaleCNM_mem_complexTube hrs hrg hmax hI0 b hS hIc hrB hrB0 hw0 hw ht hts hz.1 hz.2

theorem lpPertNM_extClass (hT : LPChartTubeNM ν L δ rg R M fc) (hrs : 0 < rs)
    (hrg : rs ≤ 4 * rg) (hmax : max rs (max (4 * s₀) (4 * b₀)) < R / 2)
    (hI0 : I0 ∈ strongLevelSet ν L δ) (hS : b.S = spatialSecularBall ν δ I0) (hIc : b.Ic = I0)
    (hrB : b.rB ≤ rs) (hrB0 : 0 < b.rB) (hw0 : 0 < b.w) (hw : b.w < 4 * b₀) {t : ℝ}
    (ht : 0 < t) (hts : 2 * Real.pi * t ≤ 4 * s₀) (μ : ℝ) :
    ext_class b b.rB t (lpPertNM μ b.lam fc) := by
  have hm : ∀ z ∈ Dom n b.base b.rB t,
      lpUnrescaleCNM b.lam z ∈ complexTubeNM (spatialStrongCore ν L δ rg) R := fun z hz =>
    lpTubeNM_mono hT.R_pos (lpPertNM_dom_mem hrs hrg hmax hI0 hS hIc hrB hrB0 hw0 hw ht hts hz)
  refine ⟨⟨?_, fun j z hz => ?_⟩, fun x hx => ?_⟩
  · have hd := (lpUnrescaleCNM_differentiable (n := n) (m := n + n) b.lam)
    exact (hT.hol.comp hd.differentiableOn hm).const_mul _
  · have h1 := (hT.per (Pi.single j 1) _ (hm z hz)).2
    simp only [lpPertNM]
    rw [lpUnrescaleCNM_shift, h1]
  · have e : (KAM.realInclusion n x.1, KAM.realInclusion (n + ((n + n) + (n + n))) x.2) =
        extCx x := by
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [extCx]
    rw [e] at hx ⊢
    have hmx := hm _ hx
    rw [lpUnrescaleCNM_extCx] at hmx
    have := (hT.real _ hmx).2
    simp only [lpPertNM, lpUnrescaleCNM_extCx, this]
    simp [-Complex.ofReal_mul]

theorem lpPertNM_sup_le (hT : LPChartTubeNM ν L δ rg R M fc) (hrs : 0 < rs)
    (hrg : rs ≤ 4 * rg) (hmax : max rs (max (4 * s₀) (4 * b₀)) < R / 2)
    (hI0 : I0 ∈ strongLevelSet ν L δ) (hS : b.S = spatialSecularBall ν δ I0) (hIc : b.Ic = I0)
    (hrB : b.rB ≤ rs) (hrB0 : 0 < b.rB) (hw0 : 0 < b.w) (hw : b.w < 4 * b₀) {t : ℝ}
    (ht : 0 < t) (hts : 2 * Real.pi * t ≤ 4 * s₀) {μ : ℝ} (hμ : 0 ≤ μ) :
    ∀ z ∈ Dom n b.base b.rB t, ‖lpPertNM μ b.lam fc z‖ ≤ μ / (2 * Real.pi) * M := by
  intro z hz
  have hb := hT.bound _ (lpPertNM_dom_mem hrs hrg hmax hI0 hS hIc hrB hrB0 hw0 hw ht hts hz)
  simp only [lpPertNM, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

theorem lpPertNM_wbound (hT : LPChartTubeNM ν L δ rg R M fc) (hrs : 0 < rs)
    (hrg : rs ≤ 4 * rg) (hmax : max rs (max (4 * s₀) (4 * b₀)) < R / 2)
    (hI0 : I0 ∈ strongLevelSet ν L δ) (hS : b.S = spatialSecularBall ν δ I0) (hIc : b.Ic = I0)
    (hrB : b.rB ≤ rs) (hrB0 : 0 < b.rB) (hw0 : 0 < b.w) (hw : b.w < 4 * b₀) {s σ : ℝ}
    (hs : 0 < s) (hσ : 0 < σ) (hts : 2 * Real.pi * (s + σ) ≤ 4 * s₀) {μ : ℝ} (hμ : 0 ≤ μ) :
    WBound b.base b.rB s (lpPertNM μ b.lam fc) (lpM₂ n σ M * μ) := by
  have h := wbound_of_sup_bound (n := n) hs hσ
    (lpPertNM_extClass hT hrs hrg hmax hI0 hS hIc hrB hrB0 hw0 hw (by linarith) hts μ).1
    (lpPertNM_sup_le hT hrs hrg hmax hI0 hS hIc hrB hrB0 hw0 hw (by linarith) hts hμ)
  have e : lpM₂ n σ M * μ = coth (Real.pi * σ) ^ n * (μ / (2 * Real.pi) * M) := by
    unfold lpM₂; ring
  rwa [e]

end

end KAM.Planetary.Spatial

end
