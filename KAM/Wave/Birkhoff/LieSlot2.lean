/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieSlot1

/-!
# The slot recurrence for the Lie coefficients (blueprint-W `bpW:w3:lie-coeff`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-FLOW, blueprint label `bpW:w3:lie-coeff` (audit finding F1).

`lieMb_slot`: `(k+1) Φ_{k+1}(v) = Σ_{i < 2k+1} Φ_k(v¹, …, T(v^i, v^{i+1}, v^{i+2}), …)` for all
sequences `v` (a hook-length type induction from the block recursion; no symmetry of `T` is
used).
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (T : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E)

theorem lieShift_contract_lt {s i : ℕ} (v : ℕ → E) (h : i < s) :
    lieShift s (lieContract T i v) = lieShift (s + 2) v := by
  funext j
  simp only [lieShift, lieContract]
  rw [if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

theorem lieShift_contract_ge (s i : ℕ) (v : ℕ → E) :
    lieShift s (lieContract T (s + i) v) = lieContract T i (lieShift s v) := by
  funext j
  simp only [lieShift, lieContract]
  by_cases h1 : j < i
  · rw [if_pos (by omega), if_pos h1]
  · by_cases h2 : j = i
    · subst h2
      rw [if_neg (by omega), if_pos rfl, if_neg (by omega), if_pos rfl]
      congr 2
    · rw [if_neg (by omega), if_neg (by omega), if_neg h1, if_neg h2]
      congr 1

theorem lieContract_apply_lt {i j : ℕ} (v : ℕ → E) (h : j < i) :
    lieContract T i v j = v j := by
  simp [lieContract, h]

/-- The term `T(Φ_a(v), Φ_b(S v), Φ_c(S' v))` of the block recursion. -/
def lieG (a b c : ℕ) (v : ℕ → E) : E :=
  T ![lieMb T a v, lieMb T b (lieShift (2 * a + 1) v), lieMb T c (lieShift (2 * a + 2 * b + 2) v)]

theorem lieMb_succ_G (k : ℕ) (v : ℕ → E) :
    lieMb T (k + 1) v = ((1 : ℂ) / ((k : ℂ) + 1)) •
      ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k, lieG T (x 0) (x 1) (x 2) v := lieMb_succ T k v

section Slots

variable (m : Fin 3 → E) (i : Fin 3)

theorem T_sum_slot {ι : Type*} (s : Finset ι) (f : ι → E) :
    ∑ k ∈ s, T (Function.update m i (f k)) = T (Function.update m i (∑ k ∈ s, f k)) := by
  have h := map_sum (T.toMultilinearMap.toLinearMap m i) f s
  simp only [MultilinearMap.toLinearMap_apply, ContinuousMultilinearMap.coe_coe] at h
  exact h.symm

theorem T_smul_slot (c : ℂ) (x : E) :
    T (Function.update m i (c • x)) = c • T (Function.update m i x) := by
  have h := map_smul (T.toMultilinearMap.toLinearMap m i) c x
  simp only [MultilinearMap.toLinearMap_apply, ContinuousMultilinearMap.coe_coe] at h
  exact h

end Slots

theorem T_sum0 {ι : Type*} (s : Finset ι) (f : ι → E) (A B : E) :
    ∑ k ∈ s, T ![f k, A, B] = T ![∑ k ∈ s, f k, A, B] := by
  have e : ∀ y : E, (![y, A, B] : Fin 3 → E) = Function.update ![0, A, B] 0 y := fun y => by
    ext j; fin_cases j <;> simp
  have h := T_sum_slot T ![0, A, B] 0 s f
  simp only [← e] at h
  exact h

theorem T_sum1 {ι : Type*} (s : Finset ι) (f : ι → E) (A B : E) :
    ∑ k ∈ s, T ![A, f k, B] = T ![A, ∑ k ∈ s, f k, B] := by
  have e : ∀ y : E, (![A, y, B] : Fin 3 → E) = Function.update ![A, 0, B] 1 y := fun y => by
    ext j; fin_cases j <;> simp
  have h := T_sum_slot T ![A, 0, B] 1 s f
  simp only [← e] at h
  exact h

theorem T_sum2 {ι : Type*} (s : Finset ι) (f : ι → E) (A B : E) :
    ∑ k ∈ s, T ![A, B, f k] = T ![A, B, ∑ k ∈ s, f k] := by
  have e : ∀ y : E, (![A, B, y] : Fin 3 → E) = Function.update ![A, B, 0] 2 y := fun y => by
    ext j; fin_cases j <;> simp
  have h := T_sum_slot T ![A, B, 0] 2 s f
  simp only [← e] at h
  exact h

theorem T_smul0 (c : ℂ) (x A B : E) : T ![c • x, A, B] = c • T ![x, A, B] := by
  have e : ∀ y : E, (![y, A, B] : Fin 3 → E) = Function.update ![0, A, B] 0 y := fun y => by
    ext j; fin_cases j <;> simp
  have h := T_smul_slot T ![0, A, B] 0 c x
  simp only [← e] at h
  exact h

theorem T_smul1 (c : ℂ) (x A B : E) : T ![A, c • x, B] = c • T ![A, x, B] := by
  have e : ∀ y : E, (![A, y, B] : Fin 3 → E) = Function.update ![A, 0, B] 1 y := fun y => by
    ext j; fin_cases j <;> simp
  have h := T_smul_slot T ![A, 0, B] 1 c x
  simp only [← e] at h
  exact h

theorem T_smul2 (c : ℂ) (x A B : E) : T ![A, B, c • x] = c • T ![A, B, x] := by
  have e : ∀ y : E, (![A, B, y] : Fin 3 → E) = Function.update ![A, B, 0] 2 y := fun y => by
    ext j; fin_cases j <;> simp
  have h := T_smul_slot T ![A, B, 0] 2 c x
  simp only [← e] at h
  exact h

end KAM.Wave

end
