/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.NormalPol
public import KAM.Wave.Homological.Taylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Support for the angle-derivative bounds (blueprint-W `bpW:w4:components` (ii))

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

* `homEntryCLM`, `homNormEntryCLM`: the matrix entries of `HomOp` as continuous linear functionals;
* `homNormalEntry_partial`: entries commute with `∂_{θ_i}`;
* `homLam_entry_eq`: `(ΛM)_ij = M_ij/(ω_{a,p}(i+2) ω_{a,p}(j+2))`, hence `ΛM` is symmetric when `M`
  has symmetric entries (`homLam_entry_symm`);
* `homPairRep_eq`: `⟨c,z⟩₀ = homPairL2 (D ĉ) z`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- The matrix entry `A ↦ A_ij` as a continuous linear functional on `HomOp`. -/
def homEntryCLM (i j : ℕ+) : HomOp →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 i).comp
    (ContinuousLinearMap.apply ℂ HomL2 (kamBasis ℂ j))

theorem homEntryCLM_apply (i j : ℕ+) (A : HomOp) : homEntryCLM i j A = kamEntry A i j := rfl

/-- The true matrix entry `M_ij` as a continuous linear functional on `HomOp`. -/
def homNormEntryCLM (a p : ℝ) (i j : ℕ+) : HomOp →L[ℂ] ℂ :=
  ((ellWeight a p (j + 2) / ellWeight a (p + 1) (i + 2) : ℝ) : ℂ) • homEntryCLM i j

theorem homNormEntryCLM_apply (a p : ℝ) (i j : ℕ+) (A : HomOp) :
    homNormEntryCLM a p i j A = homNormalEntry a p A i j := rfl

/-- Entries commute with `∂_{θ_i}`. -/
theorem homNormalEntry_partial {a p : ℝ} {F : (Fin 2 → ℂ) → HomOp} {θ : Fin 2 → ℂ}
    (hF : DifferentiableAt ℂ F θ) (i : Fin 2) (k l : ℕ+) :
    homNormalEntry a p (homPartial i F θ) k l =
      homPartial i (fun θ => homNormalEntry a p (F θ) k l) θ := by
  unfold homPartial
  have h := ((homNormEntryCLM a p k l).hasFDerivAt.comp θ hF.hasFDerivAt).fderiv
  have e : (fun θ => homNormalEntry a p (F θ) k l) = (homNormEntryCLM a p k l) ∘ F := rfl
  rw [e, h]
  rfl

/-- If every entry of `F θ'` is symmetric for `θ'` near `θ`, so is every entry of `∂_{θ_i} F`. -/
theorem homNormalEntry_partial_symm {a p : ℝ} {F : (Fin 2 → ℂ) → HomOp} {θ : Fin 2 → ℂ}
    (hF : DifferentiableAt ℂ F θ) {U : Set (Fin 2 → ℂ)} (hU : U ∈ nhds θ)
    (hs : ∀ θ' ∈ U, ∀ k l, homNormalEntry a p (F θ') k l = homNormalEntry a p (F θ') l k)
    (i : Fin 2) (k l : ℕ+) :
    homNormalEntry a p (homPartial i F θ) k l = homNormalEntry a p (homPartial i F θ) l k := by
  rw [homNormalEntry_partial hF, homNormalEntry_partial hF]
  have : (fun θ => homNormalEntry a p (F θ) k l) =ᶠ[nhds θ]
      fun θ => homNormalEntry a p (F θ) l k :=
    Filter.eventually_of_mem hU fun θ' hθ' => hs θ' hθ' k l
  unfold homPartial
  rw [this.fderiv_eq]

/-- `(ΛM)_ij = M_ij / (ω_{a,p}(i+2) ω_{a,p}(j+2))`. -/
theorem homLam_entry_eq {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (A : HomOp) (i j : ℕ+) :
    kamEntry (homLamCLM ha hp A) i j =
      homNormalEntry a p A i j / ((homWt a p i : ℂ) * (homWt a p j : ℂ)) := by
  rw [kamEntry_homLamCLM]
  unfold homLamD homNormalEntry
  have h1 : homWt a (p + 1) i ≠ 0 := (homWt_pos a (p + 1) i).ne'
  have h2 : homWt a p i ≠ 0 := (homWt_pos a p i).ne'
  have h3 : homWt a p j ≠ 0 := (homWt_pos a p j).ne'
  have e : homWt a (p + 1) i = ellWeight a (p + 1) (i + 2) := rfl
  have e2 : homWt a p j = ellWeight a p (j + 2) := rfl
  rw [← e, ← e2]
  push_cast
  field_simp
  have h3' : (homWt a p j : ℂ) ≠ 0 := by exact_mod_cast h3
  rw [mul_div_mul_right _ _ h3']

theorem homLam_entry_symm {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) {A : HomOp}
    (hs : ∀ i j, homNormalEntry a p A i j = homNormalEntry a p A j i) (i j : ℕ+) :
    kamEntry (homLamCLM ha hp A) i j = kamEntry (homLamCLM ha hp A) j i := by
  rw [homLam_entry_eq, homLam_entry_eq, hs i j, mul_comm]

theorem homPairRep_eq {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (c z : HomL2) :
    homPairRep ha hp c z = homPairL2 (homLamDiag ha hp c) z := rfl

end KAM.Wave
