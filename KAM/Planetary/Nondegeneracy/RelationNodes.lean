/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Nondegeneracy.AnalyticZeros
public import KAM.Planetary.Nondegeneracy.Frequency
public import KAM.Planetary.Nondegeneracy.Stability

/-!
# R-nondegeneracy relation nodes: scalings

Blueprint P, Part 10 (package GAP-P10b): an unsigned export stating the literal conclusion of the
node `bpP:p10:scaling`, built from the landed `scaling` and `scaling_amount`. The nodes
`stepP:p10:F-A`, `F-B`, `F-C`, `ft-pt`, `ft-cover`, `ft-min` and `st-prod` are already closed in
the graph (named to their parents).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {d m : ℕ}

/-- `bpP:p10:scaling`, R-nondegeneracy: a positive diagonal rescaling of the frequency map
preserves (and reflects) R-nondegeneracy. -/
theorem rnd_def_scale_iff {B : Set (Vec d)} {ω : Vec d → Vec m} {s : Vec m}
    (hs : ∀ i, 0 < s i) :
    rnd_def B ω ↔ rnd_def B (fun y i => s i * ω y i) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using scaling h hs (Equiv.refl _)
  · have := scaling h (s := fun i => (s i)⁻¹) (fun i => inv_pos.2 (hs i)) (Equiv.refl _)
    simpa [← mul_assoc, inv_mul_cancel₀ (hs _).ne'] using this

/-- `bpP:p10:scaling`: the index and the amount under a positive diagonal rescaling with entries
in `[lo, hi]`: finiteness of the index is unchanged, the index is unchanged, and the amount
changes by a factor between `lo ^ 2` and `hi ^ 2`. -/
theorem scaling_index_amount {B K : Set (Vec d)} (hB : IsOpen B)
    (hK : IsCompact K) (hKn : K.Nonempty) (hKB : K ⊆ B) (hm : 0 < m)
    {ω : Vec d → Vec m} (hAn : AnalyticOnNhd ℝ ω B) {s : Vec m} {lo hi : ℝ}
    (hlo : 0 < lo) (hs : ∀ i, lo ≤ s i ∧ s i ≤ hi) :
    (rnd_def B ω ↔ rnd_def B (fun y i => s i * ω y i)) ∧
    ((∃ μ : ℕ, 0 < μ ∧ 0 < betaMu ω K μ) ↔
      ∃ μ : ℕ, 0 < μ ∧ 0 < betaMu (fun y i => s i * ω y i) K μ) ∧
    (∀ (h : ∃ μ : ℕ, 0 < μ ∧ 0 < betaFamily (squaredForm ω) (sphere m) K μ)
      (h' : ∃ μ : ℕ, 0 < μ ∧
        0 < betaFamily (squaredForm fun y i => s i * ω y i) (sphere m) K μ),
      index_def (squaredForm ω) (sphere m) K h =
        index_def (squaredForm fun y i => s i * ω y i) (sphere m) K h' ∧
      lo ^ 2 * betaFamily (squaredForm ω) (sphere m) K (index_def (squaredForm ω) (sphere m) K h)
        ≤ betaFamily (squaredForm fun y i => s i * ω y i) (sphere m) K
          (index_def (squaredForm fun y i => s i * ω y i) (sphere m) K h') ∧
      betaFamily (squaredForm fun y i => s i * ω y i) (sphere m) K
          (index_def (squaredForm fun y i => s i * ω y i) (sphere m) K h') ≤
        hi ^ 2 * betaFamily (squaredForm ω) (sphere m) K
          (index_def (squaredForm ω) (sphere m) K h)) := by
  have hsp : ∀ i, 0 < s i := fun i => hlo.trans_le (hs i).1
  have hbd := fun μ => scaling_amount hB hK hKn hKB hm hAn hlo hs μ
  have hiff : ∀ μ, 0 < betaMu ω K μ ↔ 0 < betaMu (fun y i => s i * ω y i) K μ := fun μ => by
    obtain ⟨h1, h2⟩ := hbd μ
    refine ⟨fun h => lt_of_lt_of_le (mul_pos (pow_pos hlo 2) h) h1, fun h => ?_⟩
    by_contra hn
    have h0 : betaMu ω K μ = 0 := le_antisymm (not_lt.1 hn) (betaFamily_nonneg _ _ _ _)
    rw [h0, mul_zero] at h2
    exact absurd h (not_lt.2 h2)
  refine ⟨rnd_def_scale_iff hsp, ⟨fun ⟨μ, hμ, h⟩ => ⟨μ, hμ, (hiff μ).1 h⟩,
    fun ⟨μ, hμ, h⟩ => ⟨μ, hμ, (hiff μ).2 h⟩⟩, fun h h' => ?_⟩
  have hidx : index_def (squaredForm ω) (sphere m) K h =
      index_def (squaredForm fun y i => s i * ω y i) (sphere m) K h' := by
    unfold index_def
    exact Nat.find_congr' fun {μ} => ⟨fun ⟨a, b⟩ => ⟨a, (hiff μ).1 b⟩,
      fun ⟨a, b⟩ => ⟨a, (hiff μ).2 b⟩⟩
  refine ⟨hidx, ?_⟩
  rw [← hidx]
  exact hbd _

end Nondegeneracy
end KAM.Planetary
end
