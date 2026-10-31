/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LemmaOneAssembly
public import KAM.Wave.Homological.Schur
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite-support expansions of the pairings (`bpW:w4:lemma1`, step *The equation*, algebra)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

* `homPairOmega ha hp W c z = ∑ (D ĉ)_j Ω_j z_j`, the pairing `⟨c, Ωz⟩₀` of `L_N` (`bpW:w4:lie`);
* for `z, z'` supported in a finite set `S`, the pairings are finite sums over `S`
  (`homPairRep_fin`, `homPairRep_op_fin`, `homPairOmega_fin`, `homPairOmega_op_fin`), with the
  entries `S(M)_ij = (ΛM)_ij = D_i M̂_ij` (`homSent`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- `⟨c, Ωz⟩₀ = ∑_j (D ĉ)_j Ω_j z_j` in the representative model. -/
def homPairOmega {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (W : ℕ+ → ℝ) (c z : HomL2) : ℂ :=
  ∑' j, homLamDiag ha hp c j * (W j : ℂ) * z j

/-- The entries `S(M)_ij = D_i M̂_ij` of `ΛM`. -/
def homSent {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (M : HomOp) (i j : ℕ+) : ℂ :=
  kamEntry (homLamCLM ha hp M) i j

theorem homOp_apply_fin (M : HomOp) {z : HomL2} {S : Finset ℕ+} (hz : ∀ j ∉ S, z j = 0)
    (i : ℕ+) : M z i = ∑ j ∈ S, kamEntry M i j * z j := by
  rw [← (homOp_hasSum M z i).tsum_eq]
  exact tsum_eq_sum fun j hj => by rw [hz j hj, mul_zero]

theorem homPairRep_fin {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (c : HomL2) {z : HomL2}
    {S : Finset ℕ+} (hz : ∀ j ∉ S, z j = 0) :
    homPairRep ha hp c z = ∑ j ∈ S, homLamDiag ha hp c j * z j :=
  tsum_eq_sum fun j hj => by rw [hz j hj, mul_zero]

theorem homPairRep_op_fin {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (M : HomOp) {z z' : HomL2}
    {S : Finset ℕ+} (hz : ∀ j ∉ S, z j = 0) (hz' : ∀ j ∉ S, z' j = 0) :
    homPairRep ha hp (M z) z' = ∑ i ∈ S, ∑ j ∈ S, homSent ha hp M i j * z j * z' i := by
  rw [homPairRep_fin ha hp _ hz']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [homLamDiag_apply, homOp_apply_fin M hz i, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [homSent, kamEntry_homLamCLM]
  ring

theorem homPairOmega_fin {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (W : ℕ+ → ℝ) (c : HomL2)
    {z : HomL2} {S : Finset ℕ+} (hz : ∀ j ∉ S, z j = 0) :
    homPairOmega ha hp W c z = ∑ j ∈ S, homLamDiag ha hp c j * (W j : ℂ) * z j :=
  tsum_eq_sum fun j hj => by rw [hz j hj, mul_zero]

theorem homPairOmega_op_fin {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (W : ℕ+ → ℝ) (M : HomOp)
    {z z' : HomL2} {S : Finset ℕ+} (hz : ∀ j ∉ S, z j = 0) (hz' : ∀ j ∉ S, z' j = 0) :
    homPairOmega ha hp W (M z) z' =
      ∑ i ∈ S, ∑ j ∈ S, (W i : ℂ) * homSent ha hp M i j * z j * z' i := by
  rw [homPairOmega_fin ha hp W _ hz']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [homLamDiag_apply, homOp_apply_fin M hz i]
  have : homLamD a p i * (∑ j ∈ S, kamEntry M i j * z j) * (W i : ℂ) * z' i =
      ∑ j ∈ S, (W i : ℂ) * (homLamD a p i * kamEntry M i j) * z j * z' i := by
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [homSent, kamEntry_homLamCLM]

end KAM.Wave
