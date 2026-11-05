/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Poly.Deriv
public import KAM.Canonical.Setting
public import KAM.Frozen.Defs.HamiltonianVectorField

/-!
# Cartesian polynomials: Poisson bracket (track B, B2-POLY)

`CartPoly.cartBracket P Q = ∑ i, (∂_{q_i} P ∂_{p_i} Q - ∂_{p_i} P ∂_{q_i} Q)` (position slot first),
the sum running over `i < cartWidth P` (terms beyond vanish formally). With `CartFits n P`:

* over `ℂ`: `(cartBracket P Q).cartEval z = KAM.Canonical.poissonBracket P.cartEval cartEval Q z`;
* over `ℝ`: `(cartBracket P Q).cartEval z = fderiv ℝ cartEval P z (KAM.hamiltonianVectorField
  cartEval Q z)`;
* `CartPoly.cartAdPow` matches `KAM.Canonical.adPow`;
* `(cartBracket (cartAction j) P).cartEval z = z.1 j * (P.cartDp j).cartEval z - z.2 j * (P.cartDq
  j).cartEval z`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

namespace CartPoly

variable {K : Type} [CertCoeff K]

/-- A bound on the lengths of all exponent lists of `P`. -/
def cartWidth : CartPolyK K → ℕ
  | [] => 0
  | m :: P => max (max m.a.length m.b.length) (cartWidth P)

omit [CertCoeff K] in
theorem length_le_width {P : CartPolyK K} {m : CartMonoK K} (h : m ∈ P) :
    m.a.length ≤ cartWidth P ∧ m.b.length ≤ cartWidth P := by
  induction P with
  | nil => simp at h
  | cons m' P ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp [cartWidth]
    · have := ih h
      simp only [cartWidth]
      omega

theorem dq_eq_nil_of_getD {P : CartPolyK K} {i : ℕ} (h : ∀ m ∈ P, m.a.getD i 0 = 0) :
    cartDq i P = [] := by
  induction P with
  | nil => rfl
  | cons m P ih =>
    rw [cartDq_cons, ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))]
    have h0 := h m (List.mem_cons_self ..)
    simp only [CartMonoK.cartMonoDq, h0, ↓reduceIte, List.nil_append]

theorem dp_eq_nil_of_getD {P : CartPolyK K} {i : ℕ} (h : ∀ m ∈ P, m.b.getD i 0 = 0) :
    cartDp i P = [] := by
  induction P with
  | nil => rfl
  | cons m P ih =>
    rw [cartDp_cons, ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))]
    have h0 := h m (List.mem_cons_self ..)
    simp only [CartMonoK.cartMonoDp, h0, ↓reduceIte, List.nil_append]

theorem getD_eq_zero_of_length_le (l : List ℕ) (i : ℕ) (h : l.length ≤ i) : l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

omit [CertCoeff K] in
theorem getD_eq_zero_of_width {P : CartPolyK K} {m : CartMonoK K} (h : m ∈ P) {i : ℕ}
    (hi : cartWidth P ≤ i) : m.a.getD i 0 = 0 ∧ m.b.getD i 0 = 0 := by
  have := length_le_width h
  exact ⟨getD_eq_zero_of_length_le _ _ (by omega), getD_eq_zero_of_length_le _ _ (by omega)⟩

/-- The formal Poisson bracket `∑ i, (∂_{q_i} P ∂_{p_i} Q - ∂_{p_i} P ∂_{q_i} Q)`. -/
def cartBracket (P Q : CartPolyK K) : CartPolyK K :=
  (List.range (cartWidth P)).flatMap fun i => cartSub (cartMul (cartDq i P) (cartDp i Q)) (cartMul
    (cartDp i P) (cartDq i Q))

/-- Iterated cartBracket `ad_χ^k P`: `ad⁰ P = P`, `ad^{k+1} P = {ad^k P, χ}`. -/
def cartAdPow (χ : CartPolyK K) : ℕ → CartPolyK K → CartPolyK K
  | 0, P => P
  | k + 1, P => cartBracket (cartAdPow χ k P) χ

/-! ### Typing data -/

omit [CertCoeff K] in
theorem cartFits_flatMap {n : ℕ} {f : ℕ → CartPolyK K} {L : List ℕ} (h : ∀ i ∈ L, CartFits n (f
    i)) :
    CartFits n (L.flatMap f) := by
  induction L with
  | nil => exact cartFits_nil n
  | cons i L ih =>
    rw [List.flatMap_cons]
    exact cartFits_add (h i (List.mem_cons_self ..)) (ih fun j hj => h j (List.mem_cons_of_mem _
      hj))

theorem cartFits_dq {n : ℕ} (i : ℕ) {P : CartPolyK K} (hP : CartFits n P) : CartFits n (cartDq i
    P) :=
  by
  intro m' hm' k hk
  obtain ⟨m, hm, hm'⟩ := List.mem_flatMap.1 hm'
  have h1 := hP m hm k hk
  unfold CartMonoK.cartMonoDq at hm'
  split_ifs at hm' with h
  · simp at hm'
  · obtain rfl : m' = _ := List.mem_singleton.1 hm'
    have hki : k ≠ i := fun e => h (e ▸ h1.1)
    exact ⟨by rw [getD_set_of_ne_zero _ _ _ _ h]; simpa [hki] using h1.1, h1.2⟩

theorem cartFits_dp {n : ℕ} (i : ℕ) {P : CartPolyK K} (hP : CartFits n P) : CartFits n (cartDp i
    P) :=
  by
  intro m' hm' k hk
  obtain ⟨m, hm, hm'⟩ := List.mem_flatMap.1 hm'
  have h1 := hP m hm k hk
  unfold CartMonoK.cartMonoDp at hm'
  split_ifs at hm' with h
  · simp at hm'
  · obtain rfl : m' = _ := List.mem_singleton.1 hm'
    have hki : k ≠ i := fun e => h (e ▸ h1.2)
    exact ⟨h1.1, by rw [getD_set_of_ne_zero _ _ _ _ h]; simpa [hki] using h1.2⟩

theorem cartFits_bracket {n : ℕ} {P Q : CartPolyK K} (hP : CartFits n P) (hQ : CartFits n Q) :
    CartFits n (cartBracket P Q) :=
  cartFits_flatMap fun i _ =>
    cartFits_sub (cartFits_mul (cartFits_dq i hP) (cartFits_dp i hQ))
      (cartFits_mul (cartFits_dp i hP) (cartFits_dq i hQ))

theorem cartFits_adPow {n : ℕ} {χ P : CartPolyK K} (hχ : CartFits n χ) (hP : CartFits n P) (k : ℕ) :
    CartFits n (cartAdPow χ k P) := by
  induction k with
  | zero => exact hP
  | succ k ih => exact cartFits_bracket ih hχ

theorem dq_eq_nil_of_fits {n : ℕ} {P : CartPolyK K} (hP : CartFits n P) {i : ℕ} (hi : n ≤ i) :
    cartDq i P = [] := dq_eq_nil_of_getD fun m hm => (hP m hm i hi).1

theorem dp_eq_nil_of_fits {n : ℕ} {P : CartPolyK K} (hP : CartFits n P) {i : ℕ} (hi : n ≤ i) :
    cartDp i P = [] := dp_eq_nil_of_getD fun m hm => (hP m hm i hi).2

/-! ### Evaluation of the cartBracket -/

variable {R : Type*} [CommRing R] [Algebra K R] {n : ℕ}

theorem cartEval_flatMap (f : ℕ → CartPolyK K) (L : List ℕ) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (L.flatMap f) z = (L.map fun i => cartEval (f i) z).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    rw [List.flatMap_cons, ← cartAdd, cartEval_add, ih]
    simp

theorem sum_range_eq_of_zero {α : Type*} [AddCommMonoid α] (g : ℕ → α) (W n : ℕ)
    (h : ∀ i, n ≤ i ∨ W ≤ i → g i = 0) :
    ∑ i ∈ Finset.range W, g i = ∑ i ∈ Finset.range n, g i := by
  have h1 : ∑ i ∈ Finset.range W, g i = ∑ i ∈ Finset.range (W + n), g i :=
    Finset.sum_subset (Finset.range_mono (Nat.le_add_right _ _)) fun i hi hni =>
      h i (Or.inr (by simpa using hni))
  have h2 : ∑ i ∈ Finset.range n, g i = ∑ i ∈ Finset.range (W + n), g i :=
    Finset.sum_subset (Finset.range_mono (Nat.le_add_left _ _)) fun i hi hni =>
      h i (Or.inl (by simpa using hni))
  rw [h1, h2]

theorem dq_eq_nil_of_width {P : CartPolyK K} {i : ℕ} (hi : cartWidth P ≤ i) : cartDq i P = [] :=
  dq_eq_nil_of_getD fun _ hm => (getD_eq_zero_of_width hm hi).1

theorem dp_eq_nil_of_width {P : CartPolyK K} {i : ℕ} (hi : cartWidth P ≤ i) : cartDp i P = [] :=
  dp_eq_nil_of_getD fun _ hm => (getD_eq_zero_of_width hm hi).2

/-- Evaluation of the cartBracket as a sum over `Fin n`, for `P` fitting in `n` variables. -/
theorem cartEval_bracket (P Q : CartPolyK K) (hP : CartFits n P) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartBracket P Q) z = ∑ i : Fin n, (cartEval (cartDq i P) z * cartEval (cartDp i Q) z -
      cartEval (cartDp i P) z * cartEval (cartDq i Q) z) := by
  rw [cartBracket, cartEval_flatMap]
  set g : ℕ → R := fun i => cartEval (cartDq i P) z * cartEval (cartDp i Q) z -
      cartEval (cartDp i P) z * cartEval (cartDq i Q) z with hg
  have hl : ((List.range (cartWidth P)).map fun i =>
      cartEval (cartSub (cartMul (cartDq i P) (cartDp i Q)) (cartMul (cartDp i P) (cartDq i Q)))
        z).sum =
      ∑ i ∈ Finset.range (cartWidth P), g i := by
    simp only [cartEval_sub, cartEval_mul, hg]
    rfl
  rw [hl, sum_range_eq_of_zero g (cartWidth P) n, Finset.sum_range g]
  intro i hi
  have h1 : cartDq i P = [] ∧ cartDp i P = [] := by
    rcases hi with hi | hi
    · exact ⟨dq_eq_nil_of_fits hP hi, dp_eq_nil_of_fits hP hi⟩
    · exact ⟨dq_eq_nil_of_width hi, dp_eq_nil_of_width hi⟩
  simp [hg, h1.1, h1.2]

theorem two_half (R : Type*) [CommRing R] [Algebra K R] :
    algebraMap K R (ratCoeff (1 / 2)) * ((2 : ℕ) : R) = 1 := by
  rw [← map_natCast (algebraMap K R), ← map_mul, ratCoeff_half_mul_two, map_one]

theorem cartEval_dq_action (i j : Fin n) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartDq i (cartAction (K := K) j)) z = if i = j then z.1 j else 0 := by
  have h2 : CartMonoK.cartMonoDq i (⟨[], unitExp j 2, ratCoeff (1 / 2)⟩ : CartMonoK K) = [] := by
    simp [CartMonoK.cartMonoDq]
  simp only [cartAction, cartDq_cons, cartDq_nil, h2, List.append_nil]
  by_cases hij : i = j
  · subst hij
    have h1 := cartEval_dq_mono i (⟨unitExp i 2, [], ratCoeff (1 / 2)⟩ : CartMonoK K) z
    simp only [getD_unitExp, List.getD_nil, ite_true, pow_zero, mul_one] at h1
    have hp : ∏ k ∈ Finset.univ.erase i,
        (z.1 k ^ (if (k : ℕ) = i then 2 else 0) : R) = 1 := by
      refine Finset.prod_eq_one fun k hk => ?_
      have hk' : (k : ℕ) ≠ i := fun e => (Finset.mem_erase.1 hk).1 (Fin.ext e)
      simp [hk']
    rw [h1, hp]
    simp only [ite_true, mul_one, two_half (K := K) R, one_mul]
    simp
  · have hij' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
    have h0 : (unitExp j 2).getD i 0 = 0 := by rw [getD_unitExp]; simp [hij']
    simp only [CartMonoK.cartMonoDq, h0, ↓reduceIte, cartEval_nil, hij]

theorem cartEval_dp_action (i j : Fin n) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartDp i (cartAction (K := K) j)) z = if i = j then z.2 j else 0 := by
  have h2 : CartMonoK.cartMonoDp i (⟨unitExp j 2, [], ratCoeff (1 / 2)⟩ : CartMonoK K) = [] := by
    simp [CartMonoK.cartMonoDp]
  simp only [cartAction, cartDp_cons, cartDp_nil, h2, List.nil_append, List.append_nil]
  by_cases hij : i = j
  · subst hij
    have h1 := cartEval_dp_mono i (⟨[], unitExp i 2, ratCoeff (1 / 2)⟩ : CartMonoK K) z
    simp only [getD_unitExp, List.getD_nil, ite_true, pow_zero, one_mul] at h1
    have hp : ∏ k ∈ Finset.univ.erase i,
        (z.2 k ^ (if (k : ℕ) = i then 2 else 0) : R) = 1 := by
      refine Finset.prod_eq_one fun k hk => ?_
      have hk' : (k : ℕ) ≠ i := fun e => (Finset.mem_erase.1 hk).1 (Fin.ext e)
      simp [hk']
    rw [h1, hp]
    simp only [ite_true, mul_one, two_half (K := K) R, one_mul]
    simp
  · have hij' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
    have h0 : (unitExp j 2).getD i 0 = 0 := by rw [getD_unitExp]; simp [hij']
    simp only [CartMonoK.cartMonoDp, h0, ↓reduceIte, hij]
    simp

/-- The cartAction cartBracket: `{I_j, P} = q_j ∂_{p_j} P - p_j ∂_{q_j} P`. -/
theorem cartEval_bracket_action (j : Fin n) (P : CartPolyK K) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartBracket (cartAction (K := K) j) P) z = z.1 j * cartEval (cartDp j P) z - z.2 j *
      cartEval
      (cartDq j P) z := by
  rw [cartEval_bracket _ _ (cartFits_action j.2)]
  simp only [cartEval_dq_action, cartEval_dp_action]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [hi]
  · simp

/-- Over `ℂ`: the formal cartBracket is the repo's Poisson bracket. -/
theorem cartEval_bracket_complex [Algebra K ℂ] (P Q : CartPolyK K) (hP : CartFits n P) (z : (Fin n
    → ℂ) × (Fin n →
  ℂ)) :
    cartEval (cartBracket P Q) z =
      KAM.Canonical.poissonBracket (fun z => cartEval P z) (fun z => cartEval Q z) z := by
  rw [cartEval_bracket P Q hP, KAM.Canonical.poissonBracket]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_eval_q, fderiv_eval_p, fderiv_eval_p, fderiv_eval_q]

/-- Over `ℝ`: the formal cartBracket is the derivative of `P` along the Hamiltonian field of `Q`. -/
theorem cartEval_bracket_real [Algebra K ℝ] (P Q : CartPolyK K) (hP : CartFits n P) (z : (Fin n →
    ℝ) × (Fin n → ℝ)) :
    cartEval (cartBracket P Q) z =
      fderiv ℝ (fun z : (Fin n → ℝ) × (Fin n → ℝ) => cartEval P z) z
        (KAM.hamiltonianVectorField (fun z : (Fin n → ℝ) × (Fin n → ℝ) => cartEval Q z) z) := by
  rw [cartEval_bracket P Q hP, fderiv_eval_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [KAM.hamiltonianVectorField, fderiv_eval_p, fderiv_eval_q]
  ring

theorem cartEval_adPow_complex [Algebra K ℂ] (χ P : CartPolyK K) (hχ : CartFits n χ) (hP :
    CartFits n P) (k : ℕ) :
    (fun z : (Fin n → ℂ) × (Fin n → ℂ) => cartEval (cartAdPow χ k P) z) =
      KAM.Canonical.adPow (fun z => cartEval χ z) k (fun z => cartEval P z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext z
    rw [KAM.Canonical.adPow, ← ih]
    exact cartEval_bracket_complex (cartAdPow χ k P) χ (cartFits_adPow hχ hP k) z

end CartPoly

end KAM.EffectiveStability
