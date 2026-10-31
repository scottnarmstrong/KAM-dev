/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieMulti

/-!
# The Lie coefficients on `ℕ`-indexed inputs (blueprint-W `bpW:w3:lie-coeff`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-FLOW, blueprint label `bpW:w3:lie-coeff` (audit finding F1).

`lieMb T k v` is the block recursion of `lieMulti` read on a sequence `v : ℕ → E` (only the entries
`v 0, …, v (2k)` matter, `lieMb_congr`). It agrees with `lieMulti` on `Fin`-indexed inputs
(`lieMulti_eq_lieMb`). `lieShift`, `lieContract` are the shift and the slot contraction
`(…, w^i, w^{i+1}, w^{i+2}, …) ↦ (…, S(w^i, w^{i+1}, w^{i+2}), …)`.
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (T : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E)

/-- The shift `v ↦ (v (s + i))_i`. -/
def lieShift (s : ℕ) (v : ℕ → E) : ℕ → E := fun i => v (s + i)

/-- The slot contraction at position `i`:
`(…, v i, v (i+1), v (i+2), …) ↦ (…, T(v i, v (i+1), v (i+2)), …)`. -/
def lieContract (i : ℕ) (v : ℕ → E) : ℕ → E := fun j =>
  if j < i then v j else if j = i then T ![v i, v (i + 1), v (i + 2)] else v (j + 2)

/-- The block recursion of `lieMulti` on `ℕ`-indexed inputs. -/
def lieMb : ℕ → (ℕ → E) → E
  | 0, v => v 0
  | k + 1, v => ((1 : ℂ) / ((k : ℂ) + 1)) •
      ∑ x ∈ (Finset.Nat.antidiagonalTuple 3 k).attach,
        T ![lieMb (x.1 0) v, lieMb (x.1 1) (lieShift (2 * x.1 0 + 1) v),
          lieMb (x.1 2) (lieShift (2 * x.1 0 + 2 * x.1 1 + 2) v)]
decreasing_by
  all_goals
    have h := Finset.Nat.mem_antidiagonalTuple.1 x.2
    simp only [Fin.sum_univ_three] at h
    omega

theorem lieMb_succ (k : ℕ) (v : ℕ → E) :
    lieMb T (k + 1) v = ((1 : ℂ) / ((k : ℂ) + 1)) •
      ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k,
        T ![lieMb T (x 0) v, lieMb T (x 1) (lieShift (2 * x 0 + 1) v),
          lieMb T (x 2) (lieShift (2 * x 0 + 2 * x 1 + 2) v)] := by
  rw [lieMb]
  congr 1
  exact sum_attach (Finset.Nat.antidiagonalTuple 3 k)
    (fun x => T ![lieMb T (x 0) v, lieMb T (x 1) (lieShift (2 * x 0 + 1) v),
          lieMb T (x 2) (lieShift (2 * x 0 + 2 * x 1 + 2) v)])

@[simp] theorem lieMb_zero (v : ℕ → E) : lieMb T 0 v = v 0 := by rw [lieMb]

/-- Locality: `lieMb T k v` depends only on `v 0, …, v (2k)`. -/
theorem lieMb_congr (k : ℕ) (v v' : ℕ → E) (h : ∀ i, i < 2 * k + 1 → v i = v' i) :
    lieMb T k v = lieMb T k v' := by
  induction k using Nat.strong_induction_on generalizing v v' with
  | _ k ih =>
    cases k with
    | zero => simpa using h 0 (by omega)
    | succ k =>
      rw [lieMb_succ, lieMb_succ]
      congr 1
      refine sum_congr rfl fun x hx => ?_
      have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
      simp only [Fin.sum_univ_three] at hx'
      have e0 : lieMb T (x 0) v = lieMb T (x 0) v' :=
        ih (x 0) (by omega) v v' fun i hi => h i (by omega)
      have e1 : lieMb T (x 1) (lieShift (2 * x 0 + 1) v) =
          lieMb T (x 1) (lieShift (2 * x 0 + 1) v') :=
        ih (x 1) (by omega) _ _ fun i hi => h _ (by omega)
      have e2 : lieMb T (x 2) (lieShift (2 * x 0 + 2 * x 1 + 2) v) =
          lieMb T (x 2) (lieShift (2 * x 0 + 2 * x 1 + 2) v') :=
        ih (x 2) (by omega) _ _ fun i hi => h _ (by omega)
      rw [e0, e1, e2]

/-- Extension of a `Fin n`-indexed family by zero. -/
def lieExt {n : ℕ} (w : Fin n → E) : ℕ → E := fun i => if h : i < n then w ⟨i, h⟩ else 0

/-- `lieMulti` is `lieMb` on the zero-extension. -/
theorem lieMulti_eq_lieMb (k : ℕ) (w : Fin (2 * k + 1) → E) :
    lieMulti T k w = lieMb T k (lieExt w) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
      simp only [lieMulti, lieMb_zero, lieExt]
      simp
    | succ k =>
      rw [lieMulti_succ, lieMb_succ]
      simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sum_apply]
      congr 1
      refine sum_congr rfl fun x hx => ?_
      have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
      simp only [Fin.sum_univ_three] at hx'
      rw [lieBlockT, dif_pos (sum_blocks hx), lieBlock_apply]
      have key : ∀ (j : Fin 3) (s : ℕ), (∀ b : Fin (2 * x j + 1),
          ((lieBlockEquiv x (2 * (k + 1) + 1) (sum_blocks hx) ⟨j, b⟩ : Fin _) : ℕ) = s + b) →
          lieMulti T (x j) (fun b => w (lieBlockEquiv x (2 * (k + 1) + 1) (sum_blocks hx) ⟨j, b⟩))
            = lieMb T (x j) (lieShift s (lieExt w)) := fun j s hs => by
        rw [ih (x j) (by fin_cases j <;> simp <;> omega)]
        refine lieMb_congr T _ _ _ fun i hi => ?_
        have h1 := hs ⟨i, hi⟩
        have hl' : s + i < 2 * (k + 1) + 1 := by
          have := (lieBlockEquiv x (2 * (k + 1) + 1) (sum_blocks hx) ⟨j, ⟨i, hi⟩⟩).isLt
          rw [h1] at this
          simpa using this
        simp only [lieExt, lieShift]
        rw [dif_pos hi, dif_pos hl']
        congr 1
        ext
        exact h1
      have hoff : ∀ (j : Fin 3) (b : Fin (2 * x j + 1)),
          ((lieBlockEquiv x (2 * (k + 1) + 1) (sum_blocks hx) ⟨j, b⟩ : Fin _) : ℕ) =
            ∑ i : Fin j, (2 * x (Fin.castLE j.2.le i) + 1) + b := fun j b => by
        simp [lieBlockEquiv, finSigmaFinEquiv_apply]
      have s0 := key 0 0 (fun b => by rw [hoff]; simp)
      have s1 := key 1 (2 * x 0 + 1) (fun b => by
        rw [hoff]; simp)
      have s2 := key 2 (2 * x 0 + 2 * x 1 + 2) (fun b => by
        rw [hoff]
        simp
        ring)
      have e : (fun j : Fin 3 => lieMulti T (x j)
          (fun b => w (lieBlockEquiv x (2 * (k + 1) + 1) (sum_blocks hx) ⟨j, b⟩))) =
          ![lieMb T (x 0) (lieExt w), lieMb T (x 1) (lieShift (2 * x 0 + 1) (lieExt w)),
            lieMb T (x 2) (lieShift (2 * x 0 + 2 * x 1 + 2) (lieExt w))] := by
        funext j
        fin_cases j
        · have e0 : lieShift 0 (lieExt w) = lieExt w := by funext i; simp [lieShift]
          rw [e0] at s0
          exact s0
        · exact s1
        · exact s2
      rw [e]

end KAM.Wave

end
