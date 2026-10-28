/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.OscillatorBracket
public import KAM.Canonical.FlowInverse
public import KAM.Canonical.Symplectic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# P Part 2: the anisotropic gauge and the oscillator domains

The gauge `oscScale` is the diagonal equivalence with `‖oscScale z‖ = oscGauge ρ ρp ρq σ z`;
it is the `W` of the abstract flow theory `KAM.Canonical.flow_a`–`flow_e`. This file also proves
the gauge-ball inclusions between the oscillator domains `V ⊆ U ⊆ O`.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-13.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

section Gauge

/-- Weights `c₁` on the first block and `c₂` on the last block. -/
def blockW (a b : ℕ) (c₁ c₂ : ℝ) : Fin (a + b) → ℝ := Fin.append (fun _ => c₁) (fun _ => c₂)

theorem blockW_castAdd {a b : ℕ} {c₁ c₂ : ℝ} (i : Fin a) : blockW a b c₁ c₂ (Fin.castAdd b i) = c₁ := by
  simp [blockW]

theorem blockW_natAdd {a b : ℕ} {c₁ c₂ : ℝ} (i : Fin b) : blockW a b c₁ c₂ (Fin.natAdd a i) = c₂ := by
  simp [blockW]

theorem blockW_pos {a b : ℕ} {c₁ c₂ : ℝ} (h₁ : 0 < c₁) (h₂ : 0 < c₂) (i : Fin (a + b)) :
    0 < blockW a b c₁ c₂ i := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [blockW_castAdd]; exact h₁
  · rw [blockW_natAdd]; exact h₂

/-- The diagonal scaling `a ↦ (wᵢ⁻¹ aᵢ)`. -/
def blockScale {a b : ℕ} {c₁ c₂ : ℝ} (h₁ : 0 < c₁) (h₂ : 0 < c₂) :
    (Fin (a + b) → ℂ) ≃L[ℂ] (Fin (a + b) → ℂ) :=
  ContinuousLinearEquiv.piCongrRight fun i =>
    ContinuousLinearEquiv.smulLeft
      (Units.mk0 (((blockW a b c₁ c₂ i : ℝ) : ℂ)⁻¹) (by simpa using (blockW_pos h₁ h₂ i).ne'))

theorem blockScale_apply {a b : ℕ} {c₁ c₂ : ℝ} (h₁ : 0 < c₁) (h₂ : 0 < c₂)
    (x : Fin (a + b) → ℂ) (i : Fin (a + b)) :
    blockScale (a := a) (b := b) h₁ h₂ x i = ((blockW a b c₁ c₂ i : ℝ) : ℂ)⁻¹ * x i := rfl

theorem norm_blockScale {a b : ℕ} {c₁ c₂ : ℝ} (h₁ : 0 < c₁) (h₂ : 0 < c₂) (x : Fin (a + b) → ℂ) :
    ‖blockScale (a := a) (b := b) h₁ h₂ x‖ = max (‖firstBlock x‖ / c₁) (‖lastBlock x‖ / c₂) := by
  have key : ∀ i, ‖blockScale (a := a) (b := b) h₁ h₂ x i‖ = ‖x i‖ / blockW a b c₁ c₂ i := fun i => by
    rw [blockScale_apply, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg
      (blockW_pos h₁ h₂ i).le, inv_mul_eq_div]
  have hn1 : 0 ≤ ‖firstBlock (b := b) x‖ / c₁ := by positivity
  have hn2 : 0 ≤ ‖lastBlock (a := a) x‖ / c₂ := by positivity
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left hn1)).2 fun i => ?_
    rw [key]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [blockW_castAdd]
      exact le_max_of_le_left (div_le_div_of_nonneg_right (norm_le_pi_norm (firstBlock x) j) h₁.le)
    · rw [blockW_natAdd]
      exact le_max_of_le_right (div_le_div_of_nonneg_right (norm_le_pi_norm (lastBlock x) j) h₂.le)
  · refine max_le ?_ ?_
    · rw [div_le_iff₀ h₁]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
      have := norm_le_pi_norm (blockScale (a := a) (b := b) h₁ h₂ x) (Fin.castAdd b j)
      rw [key, blockW_castAdd, div_le_iff₀ h₁] at this
      exact this
    · rw [div_le_iff₀ h₂]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
      have := norm_le_pi_norm (blockScale (a := a) (b := b) h₁ h₂ x) (Fin.natAdd a j)
      rw [key, blockW_natAdd, div_le_iff₀ h₂] at this
      exact this

variable {n m : ℕ}

/-- The gauge `W` of `oscGauge`. -/
def oscScale {ρ ρp ρq σ : ℝ} (hρ : 0 < ρ) (hρp : 0 < ρp) (hρq : 0 < ρq) (hσ : 0 < σ) :
    CPhase (n + m) ≃L[ℂ] CPhase (n + m) :=
  (blockScale (a := n) (b := m) hσ hρq).prodCongr (blockScale (a := n) (b := m) hρ hρp)

theorem norm_oscScale {ρ ρp ρq σ : ℝ} (hρ : 0 < ρ) (hρp : 0 < ρp) (hρq : 0 < ρq) (hσ : 0 < σ)
    (z : CPhase (n + m)) : ‖oscScale (n := n) (m := m) hρ hρp hρq hσ z‖ = oscGauge ρ ρp ρq σ z := by
  unfold oscScale oscGauge
  rw [ContinuousLinearEquiv.prodCongr_apply, Prod.norm_def, norm_blockScale, norm_blockScale]
  simp only [max_left_comm, max_assoc]

end Gauge

section Domains

variable {n m : ℕ} {D : Set (Fin n → ℝ)}

theorem mem_oscDom_iff {r rp rq S : ℝ} {z : CPhase (n + m)} :
    z ∈ oscDom (m := m) D r rp rq S ↔
      (∀ i : Fin n, |(z.1 (Fin.castAdd m i)).im| < S) ∧
        firstBlock (b := m) z.2 ∈ KAM.actionNbhd D r ∧
        ‖lastBlock (a := n) z.2‖ < rp ∧ ‖lastBlock (a := n) z.1‖ < rq := by
  have e1 : firstBlock (b := m + m) (oscPack (m := m) z).2 = firstBlock (b := m) z.2 := by
    funext i; simp [oscPack, firstBlock, Fin.append_left]
  have e2 : firstBlock (b := m) (lastBlock (a := n) (oscPack (m := m) z).2) =
      lastBlock (a := n) z.2 := by
    funext i; simp [oscPack, firstBlock, lastBlock, Fin.append_left, Fin.append_right]
  have e3 : lastBlock (a := m) (lastBlock (a := n) (oscPack (m := m) z).2) =
      lastBlock (a := n) z.1 := by
    funext i; simp only [oscPack, lastBlock, Fin.append_right]
  simp only [oscDom, oscParams, mem_preimage, mem_prod, mem_ofPred_eq, KAM.complexStrip, e1, e2,
    e3]
  rfl

/-- Gauge balls: a point within gauge distance `c` of `z ∈ 𝒪(a,b,c',T)` lies in the widened
domain. -/
theorem oscDom_of_gauge_le {ρ ρp ρq σ c a b d T : ℝ} (hρ : 0 < ρ) (hρp : 0 < ρp) (hρq : 0 < ρq)
    (hσ : 0 < σ) {z w : CPhase (n + m)} (hz : z ∈ oscDom (m := m) D a b d T)
    (hw : oscGauge ρ ρp ρq σ (w - z) ≤ c) :
    w ∈ oscDom (m := m) D (a + ρ * c) (b + ρp * c) (d + ρq * c) (T + σ * c) := by
  have h1 : ‖firstBlock (b := m) (w - z).1‖ / σ ≤ c := (le_max_left _ _).trans
    ((le_max_left _ _).trans hw)
  have h2 : ‖firstBlock (b := m) (w - z).2‖ / ρ ≤ c := (le_max_right _ _).trans
    ((le_max_left _ _).trans hw)
  have h3 : ‖lastBlock (a := n) (w - z).1‖ / ρq ≤ c := (le_max_left _ _).trans
    ((le_max_right _ _).trans hw)
  have h4 : ‖lastBlock (a := n) (w - z).2‖ / ρp ≤ c := (le_max_right _ _).trans
    ((le_max_right _ _).trans hw)
  rw [div_le_iff₀ hσ, mul_comm] at h1
  rw [div_le_iff₀ hρ, mul_comm] at h2
  rw [div_le_iff₀ hρq, mul_comm] at h3
  rw [div_le_iff₀ hρp, mul_comm] at h4
  obtain ⟨z1, ⟨J, hJ, hzJ⟩, z3, z4⟩ := mem_oscDom_iff.1 hz
  refine mem_oscDom_iff.2 ⟨fun i => ?_, ⟨J, hJ, ?_⟩, ?_, ?_⟩
  · have hi : |((w - z).1 (Fin.castAdd m i)).im| ≤ σ * c :=
      (Complex.abs_im_le_norm _).trans (((norm_le_pi_norm (firstBlock (b := m) (w - z).1) i)).trans h1)
    have : (w.1 (Fin.castAdd m i)).im = (z.1 (Fin.castAdd m i)).im +
        ((w - z).1 (Fin.castAdd m i)).im := by simp
    rw [this]
    calc _ ≤ |(z.1 (Fin.castAdd m i)).im| + |((w - z).1 (Fin.castAdd m i)).im| := abs_add_le _ _
      _ < T + σ * c := add_lt_add_of_lt_of_le (z1 i) hi
  · calc ‖firstBlock (b := m) w.2 - fun i => (J i : ℂ)‖
        = ‖firstBlock (b := m) (w - z).2 + (firstBlock (b := m) z.2 - fun i => (J i : ℂ))‖ := by
          congr 1; funext i; simp [firstBlock]
      _ ≤ _ := norm_add_le _ _
      _ < ρ * c + a := add_lt_add_of_le_of_lt h2 hzJ
      _ = a + ρ * c := add_comm _ _
  · calc ‖lastBlock (a := n) w.2‖ = ‖lastBlock (a := n) (w - z).2 + lastBlock (a := n) z.2‖ := by
          congr 1; funext i; simp [lastBlock]
      _ ≤ _ := norm_add_le _ _
      _ < ρp * c + b := add_lt_add_of_le_of_lt h4 z3
      _ = b + ρp * c := add_comm _ _
  · calc ‖lastBlock (a := n) w.1‖ = ‖lastBlock (a := n) (w - z).1 + lastBlock (a := n) z.1‖ := by
          congr 1; funext i; simp [lastBlock]
      _ ≤ _ := norm_add_le _ _
      _ < ρq * c + d := add_lt_add_of_le_of_lt h3 z4
      _ = d + ρq * c := add_comm _ _

end Domains

end KAM.Planetary

end
