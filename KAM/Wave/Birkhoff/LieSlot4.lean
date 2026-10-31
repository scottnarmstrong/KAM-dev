/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieSlot3

/-!
# The literal slot recurrence for `lieMulti` (blueprint-W `bpW:w3:lie-coeff`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-FLOW, blueprint label `bpW:w3:lie-coeff` (audit finding F1).

`lieMulti_slot`: on **all** ordered inputs `w¹, …, w^{2k+3}`,
`Φ_{k+1}(w¹, …, w^{2k+3}) = (1/(k+1)) Σ_{i=1}^{2k+1} Φ_k(…, S(w^i, w^{i+1}, w^{i+2}), …)`,
the source recursion of Definition `bpW:w3:lie-coeff` (`lieContractFin` is the contraction of the
slots `i, i+1, i+2`). With `Φ_0 = id` (`lieMulti` at `0`) this identifies `lieMulti` with the
source family: any family `Ψ_k` with `Ψ_0 = id` satisfying the same recursion on all inputs equals
`lieMulti` (`lieMulti_unique`).
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (T : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E)

/-- The contraction `(w¹, …, w^{2k+3}) ↦ (w¹, …, w^{i-1}, T(w^i, w^{i+1}, w^{i+2}), w^{i+3}, …)`
of `2k+3` slots to `2k+1` slots (`i` is `0`-based). -/
def lieContractFin {k : ℕ} (i : Fin (2 * k + 1)) (w : Fin (2 * (k + 1) + 1) → E) :
    Fin (2 * k + 1) → E := fun j =>
  if h : (j : ℕ) < i then w ⟨j, by omega⟩
  else if (j : ℕ) = i then T ![w ⟨i, by omega⟩, w ⟨i + 1, by omega⟩, w ⟨i + 2, by omega⟩]
  else w ⟨j + 2, by omega⟩

/-- (`bpW:w3:lie-coeff`) The literal slot recurrence of the source for `lieMulti`, on all inputs. -/
theorem lieMulti_slot (k : ℕ) (w : Fin (2 * (k + 1) + 1) → E) :
    lieMulti T (k + 1) w = ((1 : ℂ) / ((k : ℂ) + 1)) •
      ∑ i : Fin (2 * k + 1), lieMulti T k (lieContractFin T i w) := by
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h := lieMb_slot T k (lieExt w)
  rw [lieMulti_eq_lieMb, one_div, eq_inv_smul_iff₀ hk, h]
  rw [← Fin.sum_univ_eq_sum_range (fun i => lieMb T k (lieContract T i (lieExt w))) (2 * k + 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lieMulti_eq_lieMb]
  refine lieMb_congr T k _ _ fun t ht => ?_
  simp only [lieContract, lieExt, lieContractFin]
  have hi := i.2
  by_cases h1 : t < (i : ℕ)
  · simp [h1, show t < 2 * k + 1 by omega, show t < 2 * (k + 1) + 1 by omega]
  · by_cases h2 : t = (i : ℕ)
    · subst h2
      simp [show (i : ℕ) < 2 * k + 1 by omega, show (i : ℕ) < 2 * (k + 1) + 1 by omega,
        show (i : ℕ) + 1 < 2 * (k + 1) + 1 by omega, show (i : ℕ) + 2 < 2 * (k + 1) + 1 by omega]
    · simp [h1, h2, show t < 2 * k + 1 by omega, show t + 2 < 2 * (k + 1) + 1 by omega]

/-- Uniqueness: a family satisfying the source recursion on all inputs is `lieMulti`. -/
theorem lieMulti_unique (Ψ : (k : ℕ) → (Fin (2 * k + 1) → E) → E)
    (h0 : ∀ w, Ψ 0 w = lieMulti T 0 w)
    (hs : ∀ (k : ℕ) (w : Fin (2 * (k + 1) + 1) → E), Ψ (k + 1) w = ((1 : ℂ) / ((k : ℂ) + 1)) •
      ∑ i : Fin (2 * k + 1), Ψ k (lieContractFin T i w)) (k : ℕ) (w : Fin (2 * k + 1) → E) :
    Ψ k w = lieMulti T k w := by
  induction k with
  | zero => exact h0 w
  | succ k ih =>
    rw [hs, lieMulti_slot]
    congr 1
    exact Finset.sum_congr rfl fun i _ => ih _

end KAM.Wave

end
