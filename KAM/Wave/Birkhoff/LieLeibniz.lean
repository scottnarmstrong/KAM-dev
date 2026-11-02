/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieDeriv

/-!
# The Leibniz identities (blueprint-W `bpW:w3:leibniz`)

Package W3-FLOW, blueprint label `bpW:w3:leibniz`.

For a symmetric trilinear `T` (`hsym`): `lieDer_succ_sym` is `(k+1) Dφ_{k+1}(w) v = Σ_{a+b+c=k} 3
T(Dφ_a v, φ_b, φ_c)` (part (iv)), and `lieDer_apply_field` is part (i):
`Dφ_k(w) X(w) = (k+1) φ_{k+1}(w)` with `X(w) = T(w,w,w)`.
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

theorem sum_tuple_perm {M : Type*} [AddCommMonoid M] (k : ℕ) (F : (Fin 3 → ℕ) → M)
    (σ : Equiv.Perm (Fin 3)) :
    ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k, F (fun i => x (σ i)) =
      ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k, F x := by
  refine Finset.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl ℕ)) (fun x => ?_) (fun x _ => ?_)
  · simp only [Finset.Nat.mem_antidiagonalTuple]
    have : ∑ i, (Equiv.arrowCongr σ.symm (Equiv.refl ℕ)) x i = ∑ i, x i :=
      Equiv.sum_comp σ x
    rw [this]
  · rfl

/-- For a symmetric `F`: `3 Σ y₀ F(y) = n Σ F(y)` over `y₀ + y₁ + y₂ = n`. -/
theorem sum_tuple_weight {M : Type*} [AddCommGroup M] [Module ℝ M] (n : ℕ) (F : (Fin 3 → ℕ) → M)
    (hF : ∀ (σ : Equiv.Perm (Fin 3)) x, F (fun i => x (σ i)) = F x) :
    (3 : ℝ) • ∑ y ∈ Finset.Nat.antidiagonalTuple 3 n, (y 0 : ℝ) • F y =
      (n : ℝ) • ∑ y ∈ Finset.Nat.antidiagonalTuple 3 n, F y := by
  have h1 : ∑ y ∈ Finset.Nat.antidiagonalTuple 3 n, (y 1 : ℝ) • F y =
      ∑ y ∈ Finset.Nat.antidiagonalTuple 3 n, (y 0 : ℝ) • F y := by
    rw [← sum_tuple_perm n (fun x => (x 0 : ℝ) • F x) (Equiv.swap 0 1)]
    refine sum_congr rfl fun x _ => ?_
    simp [hF (Equiv.swap 0 1) x]
  have h2 : ∑ y ∈ Finset.Nat.antidiagonalTuple 3 n, (y 2 : ℝ) • F y =
      ∑ y ∈ Finset.Nat.antidiagonalTuple 3 n, (y 0 : ℝ) • F y := by
    rw [← sum_tuple_perm n (fun x => (x 0 : ℝ) • F x) (Equiv.swap 0 2)]
    refine sum_congr rfl fun x _ => ?_
    simp [hF (Equiv.swap 0 2) x]
  have h3 : ∑ y ∈ Finset.Nat.antidiagonalTuple 3 n, ((y 0 : ℝ) + y 1 + y 2) • F y =
      (n : ℝ) • ∑ y ∈ Finset.Nat.antidiagonalTuple 3 n, F y := by
    rw [smul_sum]
    refine sum_congr rfl fun y hy => ?_
    have := Finset.Nat.mem_antidiagonalTuple.1 hy
    simp only [Fin.sum_univ_three] at this
    have h : ((y 0 : ℝ) + y 1 + y 2) = n := by exact_mod_cast this
    rw [h]
  rw [← h3]
  simp only [add_smul, sum_add_distrib]
  rw [h1, h2, show (3 : ℝ) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]

/-- Shifting the first coordinate. -/
def tupleBump (x : Fin 3 → ℕ) : Fin 3 → ℕ := Function.update x 0 (x 0 + 1)

theorem tupleBump_injective : Function.Injective tupleBump := by
  intro x y h
  funext i
  have := congrFun h i
  fin_cases i <;> simp [tupleBump, Function.update] at this ⊢ <;> omega

theorem sum_tuple_shift {M : Type*} [AddCommMonoid M] [Module ℝ M] (k : ℕ) (G : (Fin 3 → ℕ) → M) :
    ∑ y ∈ Finset.Nat.antidiagonalTuple 3 (k + 1), (y 0 : ℝ) • G y =
      ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k, ((x 0 : ℝ) + 1) • G (tupleBump x) := by
  have hsub : Finset.image tupleBump (Finset.Nat.antidiagonalTuple 3 k) ⊆
      Finset.Nat.antidiagonalTuple 3 (k + 1) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have := Finset.Nat.mem_antidiagonalTuple.1 hx
    simp only [Fin.sum_univ_three] at this
    simp only [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three, tupleBump,
      Function.update_self]
    simp [Function.update]
    omega
  rw [← Finset.sum_subset hsub (fun y hy hy' => ?_), Finset.sum_image (fun x _ y _ h =>
    tupleBump_injective h)]
  · refine sum_congr rfl fun x _ => ?_
    simp [tupleBump]
  · have hy0 : y 0 = 0 := by
      by_contra h0
      apply hy'
      refine Finset.mem_image.2 ⟨Function.update y 0 (y 0 - 1), ?_, ?_⟩
      · have := Finset.Nat.mem_antidiagonalTuple.1 hy
        simp only [Fin.sum_univ_three] at this
        simp only [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three]
        simp [Function.update]
        omega
      · funext i
        fin_cases i <;> simp [tupleBump, Function.update] <;> omega
    simp [hy0]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (T : ContinuousMultilinearMap ℂ
  (fun _ : Fin 3 => E) E)

theorem toCLM_swap (hsym : ∀ (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → E), T (fun i => v (σ i)) = T v)
    (m : Fin 3 → E) (i : Fin 3) (b : E) :
    T.toContinuousLinearMap (fun j => m (Equiv.swap 0 i j)) 0 b =
      T.toContinuousLinearMap m i b := by
  classical
  simp only [ContinuousMultilinearMap.toContinuousLinearMap_apply]
  have : Function.update (fun j => m (Equiv.swap 0 i j)) 0 b =
      fun j => (Function.update m i b) (Equiv.swap 0 i j) := by
    funext j
    by_cases hj : j = 0
    · subst hj; simp
    · have : Equiv.swap 0 i j ≠ i := by
        intro h
        apply hj
        have := congrArg (Equiv.swap 0 i) h
        simpa using this
      simp [Function.update, hj, this]
  rw [this, hsym (Equiv.swap 0 i) (Function.update m i b)]

theorem sum_toCLM_eq (hsym : ∀ (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → E), T (fun i => v (σ i)) = T v)
    (k : ℕ) (f : ℕ → E) (D : ℕ → E) (i : Fin 3) :
    ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k,
        T.toContinuousLinearMap (fun j => f (x j)) i (D (x i)) =
      ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k,
        T.toContinuousLinearMap (fun j => f (x j)) 0 (D (x 0)) := by
  rw [← sum_tuple_perm k (fun x => T.toContinuousLinearMap (fun j => f (x j)) 0 (D (x 0)))
    (Equiv.swap 0 i)]
  refine sum_congr rfl fun x _ => ?_
  have := toCLM_swap T hsym (fun j => f (x j)) i (D (x i))
  simpa using this.symm

theorem toCLM_zero_apply (m : Fin 3 → E) (b : E) :
    T.toContinuousLinearMap m 0 b = T ![b, m 1, m 2] := by
  classical
  simp only [ContinuousMultilinearMap.toContinuousLinearMap_apply]
  congr 1
  funext j; fin_cases j <;> simp [Function.update]

/-- Part (iv): `(k+1) Dφ_{k+1}(w) v = Σ_{a+b+c=k} 3 T(Dφ_a v, φ_b, φ_c)`. -/
theorem lieDer_succ_sym
    (hsym : ∀ (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → E), T (fun i => v (σ i)) = T v)
    (w : E) (k : ℕ) (v : E) :
    ((k : ℂ) + 1) • lieDer T w (k + 1) v = (3 : ℂ) •
      ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k,
        T ![lieDer T w (x 0) v, lieSeq T w (x 1), lieSeq T w (x 2)] := by
  rw [lieDer_succ]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, smul_smul]
  have hk : ((k : ℂ) + 1) * (1 / ((k : ℂ) + 1)) = 1 := by
    have : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    field_simp
  rw [hk, one_smul]
  rw [Finset.sum_comm]
  have hi : ∀ i : Fin 3, ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k,
      T.toContinuousLinearMap (fun j => lieSeq T w (x j)) i (lieDer T w (x i) v) =
      ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k,
        T ![lieDer T w (x 0) v, lieSeq T w (x 1), lieSeq T w (x 2)] := fun i => by
    rw [sum_toCLM_eq T hsym k (lieSeq T w) (fun a => lieDer T w a v) i]
    exact sum_congr rfl fun x _ => toCLM_zero_apply T _ _
  simp only [Fin.sum_univ_three, hi 0, hi 1, hi 2]
  rw [show (3 : ℂ) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]

/-- Part (i): `Dφ_k(w) X(w) = (k+1) φ_{k+1}(w)` with `X(w) = T(w,w,w)`. -/
theorem lieDer_apply_field
    (hsym : ∀ (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → E), T (fun i => v (σ i)) = T v)
    (w : E) (k : ℕ) : lieDer T w k (T ![w, w, w]) = ((k : ℂ) + 1) • lieSeq T w (k + 1) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
      rw [lieSeq_succ]
      simp [Finset.Nat.antidiagonalTuple_zero_right]
    | succ k =>
      have hne : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      set G : (Fin 3 → ℕ) → E := fun y => T ![lieSeq T w (y 0), lieSeq T w (y 1), lieSeq T w (y 2)]
        with hG
      have h1 := lieDer_succ_sym T hsym w k (T ![w, w, w])
      have h2 : ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k,
          T ![lieDer T w (x 0) (T ![w, w, w]), lieSeq T w (x 1), lieSeq T w (x 2)] =
          ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k, ((x 0 : ℝ) + 1) • G (tupleBump x) := by
        refine sum_congr rfl fun x hx => ?_
        have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
        simp only [Fin.sum_univ_three] at hx'
        rw [ih (x 0) (by omega)]
        have e0 : tupleBump x 0 = x 0 + 1 := by simp [tupleBump]
        have e1 : tupleBump x 1 = x 1 := by simp [tupleBump]
        have e2 : tupleBump x 2 = x 2 := by simp [tupleBump]
        simp only [hG, e0, e1, e2]
        have := toCLM_zero_apply T ![lieSeq T w (x 0 + 1), lieSeq T w (x 1), lieSeq T w (x 2)]
          (((x 0 : ℂ) + 1) • lieSeq T w (x 0 + 1))
        have h3 := toCLM_zero_apply T ![lieSeq T w (x 0 + 1), lieSeq T w (x 1), lieSeq T w (x 2)]
          (lieSeq T w (x 0 + 1))
        simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_zero,
          Matrix.head_cons, Matrix.tail_cons] at this h3
        rw [← this, map_smul, h3, ← Complex.coe_smul]
        push_cast; rfl
      have hGsym : ∀ (σ : Equiv.Perm (Fin 3)) y, G (fun i => y (σ i)) = G y := fun σ y => by
        simp only [hG]
        rw [lieVec_eq (lieSeq T w) (fun i => y (σ i)), lieVec_eq (lieSeq T w) y]
        exact hsym σ (fun j => lieSeq T w (y j))
      have h4 := sum_tuple_weight (k + 1) G hGsym
      rw [← sum_tuple_shift k G] at h2
      have h5 : ∑ y ∈ Finset.Nat.antidiagonalTuple 3 (k + 1), G y =
          (((k + 1 : ℕ) : ℂ) + 1) • lieSeq T w (k + 1 + 1) := by
        rw [lieSeq_succ T w (k + 1), smul_smul]
        have : (((k + 1 : ℕ) : ℂ) + 1) * (1 / (((k + 1 : ℕ) : ℂ) + 1)) = 1 := by
          have : (((k + 1 : ℕ) : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
          field_simp
        rw [this, one_smul]
      simp only [← Complex.coe_smul] at h4 h2
      rw [h2] at h1
      push_cast at h4 h1
      rw [h4, h5, smul_smul] at h1
      have h6 : ((k : ℂ) + 1) • lieDer T w (k + 1) (T ![w, w, w]) =
          ((k : ℂ) + 1) • (((k : ℂ) + 1 + 1) • lieSeq T w (k + 1 + 1)) := by
        rw [h1, smul_smul]
        push_cast
        rfl
      have := smul_right_injective E hne h6
      rw [this]
      push_cast
      rfl

end KAM.Wave

end
