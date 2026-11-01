/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.NonresonantReuse.Pert

/-!
# The perturbation is in the engine's class (package LP-NRR, item 3, second half)

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
Package LP-NRR, MAIN Lemma 13 (`LP:MAIN L13 (441–458)`), N6, track LP, non-frozen.

* `lpPert_extClass`: `ext_class b b.rB t (lpPert μ b.lam fc)` (holomorphy and period-one
  periodicity from `fc`, reality from the real trace), for widths `2π t ≤ 4 s₀`;
* `lpPert_sup_le`: the sup bound `μ M/(2π)` on `Dom n b.base b.rB t`;
* `lpPert_wbound`: `WBound b.base b.rB s (lpPert μ b.lam fc) (lpM₂ n σ M * μ)` via
  `wbound_of_sup_bound`, with `M₂ = coth(πσ)ⁿ M/(2π)`.
-/

@[expose] public noncomputable section

open KAM KAM.Planetary KAM.Nekhoroshev KAM.Weighted Set

namespace KAM.Planetary.StrongAMD

variable {n : ℕ} {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ rg R M : ℝ}
  {fc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → ℂ}

/-- The constant `M₂ = coth(πσ)ⁿ M/(2π)` of `ε = M₂ μ` (`LP:MAIN L13 (444)`). -/
def lpM₂ (n : ℕ) (σ M : ℝ) : ℝ := coth (Real.pi * σ) ^ n * M / (2 * Real.pi)

theorem lpTube_mono (hR : 0 < R) {K : Set (Phase (n + n))} {z} (hz : z ∈ complexTube K (R / 2)) :
    z ∈ complexTube K R :=
  let ⟨x, hx, hlt⟩ := hz
  ⟨x, hx, hlt.trans (half_lt_self hR)⟩

section
variable {rs s₀ b₀ : ℝ} {I0 : Fin n → ℝ} {b : PartialBlock n n}

theorem lpPert_dom_mem (hrs : 0 < rs) (hrg : rs ≤ 4 * rg)
    (hmax : max rs (max (4 * s₀) (4 * b₀)) < R / 2) (hI0 : I0 ∈ strongLevelSet ν L δ)
    (hS : b.S = secularBall ν δ I0) (hIc : b.Ic = I0) (hrB : b.rB ≤ rs) (hrB0 : 0 < b.rB)
    (hw0 : 0 < b.w) (hw : b.w < 4 * b₀) {t : ℝ} (ht : 0 < t) (hts : 2 * Real.pi * t ≤ 4 * s₀)
    {z : EC n n} (hz : z ∈ Dom n b.base b.rB t) :
    lpUnrescaleC b.lam z ∈ complexTube (strongCore ν L δ rg) (R / 2) :=
  lpUnrescaleC_mem_complexTube hrs hrg hmax hI0 b hS hIc hrB hrB0 hw0 hw ht hts hz.1 hz.2

theorem lpPert_extClass (hT : LPChartTube ν L δ rg R M fc) (hrs : 0 < rs) (hrg : rs ≤ 4 * rg)
    (hmax : max rs (max (4 * s₀) (4 * b₀)) < R / 2) (hI0 : I0 ∈ strongLevelSet ν L δ)
    (hS : b.S = secularBall ν δ I0) (hIc : b.Ic = I0) (hrB : b.rB ≤ rs) (hrB0 : 0 < b.rB)
    (hw0 : 0 < b.w) (hw : b.w < 4 * b₀) {t : ℝ} (ht : 0 < t) (hts : 2 * Real.pi * t ≤ 4 * s₀)
    (μ : ℝ) : ext_class b b.rB t (lpPert μ b.lam fc) := by
  have hm : ∀ z ∈ Dom n b.base b.rB t,
      lpUnrescaleC b.lam z ∈ complexTube (strongCore ν L δ rg) R := fun z hz =>
    lpTube_mono hT.R_pos (lpPert_dom_mem hrs hrg hmax hI0 hS hIc hrB hrB0 hw0 hw ht hts hz)
  refine ⟨⟨?_, fun j z hz => ?_⟩, fun x hx => ?_⟩
  · have := (hT.hol.comp (lpUnrescaleC_differentiable (n := n) b.lam).differentiableOn hm)
    exact this.const_mul _
  · have h1 := (hT.per (Pi.single j 1) _ (hm z hz)).2
    simp only [lpPert]
    rw [lpUnrescaleC_shift, h1]
  · have e : (KAM.realInclusion n x.1, KAM.realInclusion (n + (n + n)) x.2) = extCx x := by
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [extCx]
    rw [e] at hx ⊢
    have hmx := hm _ hx
    rw [lpUnrescaleC_extCx] at hmx
    have := (hT.real _ hmx).2
    simp only [lpPert, lpUnrescaleC_extCx, this]
    simp [-Complex.ofReal_mul]

theorem lpPert_sup_le (hT : LPChartTube ν L δ rg R M fc) (hrs : 0 < rs) (hrg : rs ≤ 4 * rg)
    (hmax : max rs (max (4 * s₀) (4 * b₀)) < R / 2) (hI0 : I0 ∈ strongLevelSet ν L δ)
    (hS : b.S = secularBall ν δ I0) (hIc : b.Ic = I0) (hrB : b.rB ≤ rs) (hrB0 : 0 < b.rB)
    (hw0 : 0 < b.w) (hw : b.w < 4 * b₀) {t : ℝ} (ht : 0 < t) (hts : 2 * Real.pi * t ≤ 4 * s₀)
    {μ : ℝ} (hμ : 0 ≤ μ) :
    ∀ z ∈ Dom n b.base b.rB t, ‖lpPert μ b.lam fc z‖ ≤ μ / (2 * Real.pi) * M := by
  intro z hz
  have hb := hT.bound _ (lpPert_dom_mem hrs hrg hmax hI0 hS hIc hrB hrB0 hw0 hw ht hts hz)
  simp only [lpPert, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

theorem lpPert_wbound (hT : LPChartTube ν L δ rg R M fc) (hrs : 0 < rs) (hrg : rs ≤ 4 * rg)
    (hmax : max rs (max (4 * s₀) (4 * b₀)) < R / 2) (hI0 : I0 ∈ strongLevelSet ν L δ)
    (hS : b.S = secularBall ν δ I0) (hIc : b.Ic = I0) (hrB : b.rB ≤ rs) (hrB0 : 0 < b.rB)
    (hw0 : 0 < b.w) (hw : b.w < 4 * b₀) {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ)
    (hts : 2 * Real.pi * (s + σ) ≤ 4 * s₀) {μ : ℝ} (hμ : 0 ≤ μ) :
    WBound b.base b.rB s (lpPert μ b.lam fc) (lpM₂ n σ M * μ) := by
  have h := wbound_of_sup_bound (n := n) hs hσ
    (lpPert_extClass hT hrs hrg hmax hI0 hS hIc hrB hrB0 hw0 hw (by linarith) hts μ).1
    (lpPert_sup_le hT hrs hrg hmax hI0 hS hIc hrB hrB0 hw0 hw (by linarith) hts hμ)
  have e : lpM₂ n σ M * μ = coth (Real.pi * σ) ^ n * (μ / (2 * Real.pi) * M) := by
    unfold lpM₂; ring
  rwa [e]

end

end KAM.Planetary.StrongAMD

end
