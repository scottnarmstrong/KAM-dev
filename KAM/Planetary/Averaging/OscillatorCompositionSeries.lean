/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.OscillatorAdjoint
public import KAM.Planetary.Averaging.OscillatorSeriesAlgebra
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# P Parts 2-3: the oscillator Lie series (`stepP:p2:oi-ratio`)

`OscComposeData` bundles the source premises of the oscillator step, and `osc_lie_series` sums the
`q`-geometric adjoint bounds `|ad_φ^j u / j!| ≤ q^j A` of `osc_adjoint_bound` (applied with the
generator on its original domain and `u` on the one-loss domain): the series converges pointwise on
the two-loss domain, its sum is again in the oscillator class, with weighted bound
`(1 - q)⁻¹ A`, and its weighted tails tend to zero.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md` (Revision 3), package P23-13d.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real Filter Finset

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- Only source premises; no flow, series, remainder or reality conclusion is a field. -/
structure OscComposeData {n m : ℕ} (D : Set (Fin n → ℝ))
    (r rp rq S ρ ρp ρq σ Φ : ℝ) (φ : CHam (n + m)) : Prop where
  hn : 1 ≤ n
  hm : 1 ≤ m
  widths : 0 < ρ ∧ 2 * ρ < r ∧ 0 < ρp ∧ 2 * ρp < rp ∧
    0 < ρq ∧ 2 * ρq < rq ∧ 0 < σ ∧ 2 * σ < S
  phi_class : oscClass D r rp rq S φ
  phi_bound : oscBound D r rp rq S φ Φ
  phi_nonneg : 0 ≤ Φ
  small : Φ ≤ min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ)))

section OscCompositionSeries
variable {n m : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S ρ ρp ρq σ Φ A : ℝ}
  {φ u : CHam (n + m)}

theorem osc_lie_series (H : OscComposeData D r rp rq S ρ ρp ρq σ Φ φ)
    (hu : oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u)
    (hb : oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u A) (hA : 0 ≤ A) :
    let V := oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
    let L := fun z => ∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * adPow φ j u z
    (∀ z ∈ V, HasSum (fun j : ℕ => ((j.factorial : ℂ)⁻¹) * adPow φ j u z) (L z)) ∧
    oscClass D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) L ∧
    oscBound D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) L
      ((1 - oscLieRatio m Φ (min (ρ * σ) (ρp * ρq)))⁻¹ * A) ∧
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' ≥ N,
      oscBound D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
        (fun z => L z - ∑ j ∈ Finset.range N', ((j.factorial : ℂ)⁻¹) * adPow φ j u z) ε := by
  intro V L
  obtain ⟨hρ, hρr, hρp, hρpr, hρq, hρqr, hσ, hσS⟩ := H.widths
  set d := min (ρ * σ) (ρp * ρq) with hd_def
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  obtain ⟨hq0, hqθ, hθ, h169, -⟩ := osc_ratio_range m hd H.phi_nonneg H.small
  set q := oscLieRatio m Φ d with hq
  have hq1 : q < 1 := by
    have : oscTheta m Φ d < 1 := by nlinarith [hq0.trans hqθ]
    linarith
  have e1 : r - ρ - ρ = r - 2 * ρ := by ring
  have e2 : rp - ρp - ρp = rp - 2 * ρp := by ring
  have e3 : rq - ρq - ρq = rq - 2 * ρq := by ring
  have e4 : S - σ - σ = S - 2 * σ := by ring
  have hterm : ∀ j : ℕ,
      oscClass D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
        (fun z => ((j.factorial : ℂ)⁻¹) * adPow φ j u z) ∧
      oscBound D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
        (fun z => ((j.factorial : ℂ)⁻¹) * adPow φ j u z) (q ^ j * A) := fun j => by
    obtain ⟨hc, hbd⟩ := osc_adjoint_bound (r := r - ρ) (rp := rp - ρp) (rq := rq - ρq)
      (S := S - σ) (r₀ := r) (rp₀ := rp) (rq₀ := rq) (S₀ := S) (ρ := ρ) (ρp := ρp) (ρq := ρq)
      (σ := σ) (Φ := Φ) H.hn H.hm H.phi_class hu H.phi_bound hb H.phi_nonneg hA
      ⟨hρ, by linarith, hρp, by linarith, hρq, by linarith, hσ, by linarith⟩
      ⟨by linarith, by linarith, by linarith, by linarith⟩ j
    rw [e1, e2, e3, e4] at hc hbd
    exact ⟨hc.const_mul _, hbd⟩
  have hS2 : 0 < S - 2 * σ := by linarith
  have hb0 : ∀ j : ℕ, 0 ≤ q ^ j * A := fun j => mul_nonneg (pow_nonneg hq0 j) hA
  have hs : Summable fun j : ℕ => q ^ j * A :=
    (summable_geometric_of_lt_one hq0 hq1).mul_right A
  obtain ⟨hcl, hbl, htail⟩ := osc_bound_tsum hS2 (v := fun j => fun z =>
    ((j.factorial : ℂ)⁻¹) * adPow φ j u z) (fun j => (hterm j).1) (fun j => (hterm j).2) hb0 hs
  have hsum : ∑' j : ℕ, q ^ j * A = (1 - q)⁻¹ * A := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1]
  refine ⟨fun z hz => ?_, hcl, by rwa [hsum] at hbl, htail⟩
  exact (Summable.of_norm_bounded hs fun j =>
    oscBound.norm_le (hterm j).1 (hterm j).2 z hz).hasSum
end OscCompositionSeries

end KAM.Planetary

end
