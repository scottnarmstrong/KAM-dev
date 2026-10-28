/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.FiniteChain

/-!
# P Part 2: the accumulated normal form of the finite iteration (`stepP:p2:nfb-concl`, (b))

`Sched.gI` is the sum of the zero modes of the successive remainders. This module shows it is
holomorphic in the action, real, equal to the accumulated generator `gₘ₊₁` on the final domain,
and that `g - f̂₀` is the finite sum of the later zero-mode increments, which gives its weighted
bound. Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-12.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {Dc : Set (Fin (a + b) → ℂ)} {c : Sched} {K α₁ α₂ : ℝ}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)} {ε : ℕ → ℝ} {m : ℕ}

private theorem inClass_mono {D : Set (Fin (a + b) → ℂ)} {r₀ s₀ r s : ℝ} {u : CHam (a + b)}
    (hu : InClass D r₀ s₀ u) (hr : r ≤ r₀) (hs : s ≤ s₀) : InClass D r s u :=
  ⟨hu.differentiableOn.mono (Dom_mono hr hs), fun j z hz => hu.periodic j z (Dom_mono hr hs hz)⟩

private theorem wbound_zero' {D : Set (Fin (a + b) → ℂ)} {r s : ℝ} :
    WBound D r s (fun _ : CPhase (a + b) => (0 : ℂ)) 0 := by
  intro I _
  have h0 : ∀ k : Fin (a + b) → ℤ, coeff (fun _ : CPhase (a + b) => (0 : ℂ)) I k = 0 :=
    fun k => by simp [coeff, KAM.torusCoeffW, KAM.torusAverage]
  simp [WSummable, wsum, h0]

theorem S_pos_succ (hS : IterSetup Dc c K α₁ α₂ h f ε m) : 0 < c.S (m + 1) := by
  have := hS.σ_lt m le_rfl
  rw [Sched.S_succ]; linarith

theorem S_pos_le (hS : IterSetup Dc c K α₁ α₂ h f ε m) {j : ℕ} (hj : j ≤ m + 1) : 0 < c.S j := by
  rcases Nat.lt_or_ge j (m + 1) with hlt | hge
  · exact S_pos hS (by omega)
  · obtain rfl : j = m + 1 := by omega
    exact S_pos_succ hS

theorem R_final_le (hS : IterSetup Dc c K α₁ α₂ h f ε m) {j : ℕ} (hj : j ≤ m + 1) :
    c.R (m + 1) ≤ c.R j :=
  c.R_anti (fun l hl => (hS.ρ_pos l (by omega)).le) hj

theorem S_final_le (hS : IterSetup Dc c K α₁ α₂ h f ε m) {j : ℕ} (hj : j ≤ m + 1) :
    c.S (m + 1) ≤ c.S j :=
  c.S_anti (fun l hl => (hS.σ_pos l (by omega)).le) hj

theorem G_eq_gI (hS : IterSetup Dc c K α₁ α₂ h f ε m) :
    ∀ z ∈ Sched.U Dc c (m + 1), c.G Dc K h f (m + 1) z = c.gI Dc K h f m z.2 := by
  have inv := inv_all hS (m + 1) le_rfl
  intro z hz
  rw [Sched.G_eq_sum c Dc K h f (m + 1)]
  beta_reduce
  rw [Fin.sum_univ_eq_sum_range
    (fun j => homRes K {0} (c.F Dc K h f j) z) (m + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ m + 1 := by have := Finset.mem_range.1 hj; omega
  exact homRes_zero (S_pos_le hS hj') hS.K_nonneg (inv j hj').1 (inv j hj').2.1
    (Dom_mono (R_final_le hS hj') (S_final_le hS hj') hz)

theorem gI_differentiable (hS : IterSetup Dc c K α₁ α₂ h f ε m) :
    DifferentiableOn ℂ (c.gI Dc K h f m) (polyNbhd Dc (c.R (m + 1))) := by
  have inv := inv_all hS (m + 1) le_rfl
  unfold Sched.gI
  refine DifferentiableOn.fun_sum (𝕜 := ℂ) (u := Finset.range (m + 1))
    (A := fun j I => coeff (c.F Dc K h f j) I 0) fun j hj => ?_
  have hj' : j ≤ m + 1 := by have := Finset.mem_range.1 hj; omega
  exact (coeff_differentiableOn (D := Dc) (r := c.R j) (s := c.S j) (u := c.F Dc K h f j)
    (S_pos_le hS hj') (inv j hj').1 0).mono (polyNbhd_mono (R_final_le hS hj'))

theorem gI_real (hS : IterSetup Dc c K α₁ α₂ h f ε m)
    (hsc : ∀ i ≤ m, StepConc Dc c K α₁ α₂ h f ε i) :
    RealOn (Sched.U Dc c (m + 1)) (fun z => c.gI Dc K h f m z.2) := by
  intro x hx
  have := (hsc m le_rfl).real_G x hx
  rwa [G_eq_gI hS _ hx] at this

theorem tail_sum (hS : IterSetup Dc c K α₁ α₂ h f ε m) :
    ∀ l ≤ m, InClass Dc (c.R (m + 1)) (c.S (m + 1))
        (fun z => ∑ j ∈ Finset.range l, homRes K {0} (c.F Dc K h f (j + 1)) z) ∧
      WBound Dc (c.R (m + 1)) (c.S (m + 1))
        (fun z => ∑ j ∈ Finset.range l, homRes K {0} (c.F Dc K h f (j + 1)) z)
        (∑ j ∈ Finset.range l, ε (j + 1)) := by
  have inv := inv_all hS (m + 1) le_rfl
  intro l
  induction l with
  | zero =>
    intro _
    simp only [Finset.sum_range_zero]
    exact ⟨⟨differentiableOn_const 0, fun _ _ _ => rfl⟩, wbound_zero'⟩
  | succ l ih =>
    intro hl
    obtain ⟨i1, i2⟩ := ih (by omega)
    have hH := directHyp_stage hS (i := l + 1) hl (inv (l + 1) (by omega))
    obtain ⟨c1, c2, -⟩ := homRes_stage hH
    have hc1 := inClass_mono c1 (R_final_le hS (by omega : l + 1 ≤ m + 1))
      (S_final_le hS (by omega : l + 1 ≤ m + 1))
    have hc2 := c2.mono (R_final_le hS (by omega : l + 1 ≤ m + 1))
      (S_final_le hS (by omega : l + 1 ≤ m + 1)) le_rfl
    simp only [Finset.sum_range_succ]
    exact ⟨⟨i1.differentiableOn.add hc1.differentiableOn, fun j z hz => by
      simp only [i1.periodic j z hz, hc1.periodic j z hz]⟩,
      wbound_add (S_pos_succ hS) i1 hc1 i2 hc2⟩

/-- `g - f̂₀` is the finite sum of the later zero-mode increments. -/
theorem gen_tail (hS : IterSetup Dc c K α₁ α₂ h f ε m) :
    InClass Dc (c.R (m + 1)) (c.S (m + 1))
      (fun z : CPhase (a + b) => c.gI Dc K h f m z.2 - coeff f z.2 0) ∧
    WBound Dc (c.R (m + 1)) (c.S (m + 1))
      (fun z : CPhase (a + b) => c.gI Dc K h f m z.2 - coeff f z.2 0)
      (∑ j ∈ Finset.range m, ε (j + 1)) := by
  have inv := inv_all hS (m + 1) le_rfl
  obtain ⟨t1, t2⟩ := tail_sum hS m le_rfl
  have heq : EqOn (fun z : CPhase (a + b) => ∑ j ∈ Finset.range m,
      homRes K {0} (c.F Dc K h f (j + 1)) z)
      (fun z => c.gI Dc K h f m z.2 - coeff f z.2 0)
      (Dom (a + b) Dc (c.R (m + 1)) (c.S (m + 1))) := by
    intro z hz
    have e1 : ∀ j ∈ Finset.range m, homRes K {0} (c.F Dc K h f (j + 1)) z =
        coeff (c.F Dc K h f (j + 1)) z.2 0 := fun j hj => by
      have hj' : j + 1 ≤ m + 1 := by have := Finset.mem_range.1 hj; omega
      exact homRes_zero (S_pos_le hS hj') hS.K_nonneg (inv (j + 1) hj').1
        (inv (j + 1) hj').2.1 (Dom_mono (R_final_le hS hj') (S_final_le hS hj') hz)
    simp only [Sched.gI]
    rw [Finset.sum_range_succ' (fun j => coeff (c.F Dc K h f j) z.2 0) m, Finset.sum_congr rfl e1,
      Sched.F_zero]
    ring
  exact ⟨inClass_congr heq t1, wbound_congr (S_pos_succ hS) heq t2⟩

end KAM.Planetary

end
