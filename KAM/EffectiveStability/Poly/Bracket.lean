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

`CartPoly.bracket P Q = ∑ i, (∂_{q_i} P ∂_{p_i} Q - ∂_{p_i} P ∂_{q_i} Q)` (position slot first),
the sum running over `i < width P` (terms beyond vanish formally). With `Fits n P`:

* over `ℂ`: `(bracket P Q).eval z = KAM.Canonical.poissonBracket P.eval Q.eval z`;
* over `ℝ`: `(bracket P Q).eval z = fderiv ℝ P.eval z (KAM.hamiltonianVectorField Q.eval z)`;
* `CartPoly.adPow` matches `KAM.Canonical.adPow`;
* `(bracket (action j) P).eval z = z.1 j * (P.dp j).eval z - z.2 j * (P.dq j).eval z`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

namespace CartPoly

/-- A bound on the lengths of all exponent lists of `P`. -/
def width : CartPoly → ℕ
  | [] => 0
  | m :: P => max (max m.a.length m.b.length) (width P)

theorem length_le_width {P : CartPoly} {m : CartMono} (h : m ∈ P) :
    m.a.length ≤ width P ∧ m.b.length ≤ width P := by
  induction P with
  | nil => simp at h
  | cons m' P ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp [width]
    · have := ih h
      simp only [width]
      omega

theorem dq_eq_nil_of_getD {P : CartPoly} {i : ℕ} (h : ∀ m ∈ P, m.a.getD i 0 = 0) :
    dq i P = [] := by
  induction P with
  | nil => rfl
  | cons m P ih =>
    rw [dq_cons, ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))]
    have h0 := h m (List.mem_cons_self ..)
    simp only [CartMono.dq, h0, ↓reduceIte, List.nil_append]

theorem dp_eq_nil_of_getD {P : CartPoly} {i : ℕ} (h : ∀ m ∈ P, m.b.getD i 0 = 0) :
    dp i P = [] := by
  induction P with
  | nil => rfl
  | cons m P ih =>
    rw [dp_cons, ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))]
    have h0 := h m (List.mem_cons_self ..)
    simp only [CartMono.dp, h0, ↓reduceIte, List.nil_append]

theorem getD_eq_zero_of_length_le (l : List ℕ) (i : ℕ) (h : l.length ≤ i) : l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem getD_eq_zero_of_width {P : CartPoly} {m : CartMono} (h : m ∈ P) {i : ℕ}
    (hi : width P ≤ i) : m.a.getD i 0 = 0 ∧ m.b.getD i 0 = 0 := by
  have := length_le_width h
  exact ⟨getD_eq_zero_of_length_le _ _ (by omega), getD_eq_zero_of_length_le _ _ (by omega)⟩

/-- The formal Poisson bracket `∑ i, (∂_{q_i} P ∂_{p_i} Q - ∂_{p_i} P ∂_{q_i} Q)`. -/
def bracket (P Q : CartPoly) : CartPoly :=
  (List.range (width P)).flatMap fun i => sub (mul (dq i P) (dp i Q)) (mul (dp i P) (dq i Q))

/-- Iterated bracket `ad_χ^k P`: `ad⁰ P = P`, `ad^{k+1} P = {ad^k P, χ}`. -/
def adPow (χ : CartPoly) : ℕ → CartPoly → CartPoly
  | 0, P => P
  | k + 1, P => bracket (adPow χ k P) χ

/-! ### Typing data -/

theorem Fits.flatMap {n : ℕ} {f : ℕ → CartPoly} {L : List ℕ} (h : ∀ i ∈ L, Fits n (f i)) :
    Fits n (L.flatMap f) := by
  induction L with
  | nil => exact Fits.nil n
  | cons i L ih =>
    rw [List.flatMap_cons]
    exact Fits.add (h i (List.mem_cons_self ..)) (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem Fits.dq {n : ℕ} (i : ℕ) {P : CartPoly} (hP : Fits n P) : Fits n (dq i P) := by
  intro m' hm' k hk
  obtain ⟨m, hm, hm'⟩ := List.mem_flatMap.1 hm'
  have h1 := hP m hm k hk
  unfold CartMono.dq at hm'
  split_ifs at hm' with h
  · simp at hm'
  · obtain rfl : m' = _ := List.mem_singleton.1 hm'
    have hki : k ≠ i := fun e => h (e ▸ h1.1)
    exact ⟨by rw [getD_set_of_ne_zero _ _ _ _ h]; simpa [hki] using h1.1, h1.2⟩

theorem Fits.dp {n : ℕ} (i : ℕ) {P : CartPoly} (hP : Fits n P) : Fits n (dp i P) := by
  intro m' hm' k hk
  obtain ⟨m, hm, hm'⟩ := List.mem_flatMap.1 hm'
  have h1 := hP m hm k hk
  unfold CartMono.dp at hm'
  split_ifs at hm' with h
  · simp at hm'
  · obtain rfl : m' = _ := List.mem_singleton.1 hm'
    have hki : k ≠ i := fun e => h (e ▸ h1.2)
    exact ⟨h1.1, by rw [getD_set_of_ne_zero _ _ _ _ h]; simpa [hki] using h1.2⟩

theorem Fits.bracket {n : ℕ} {P Q : CartPoly} (hP : Fits n P) (hQ : Fits n Q) :
    Fits n (bracket P Q) :=
  Fits.flatMap fun i _ =>
    Fits.sub ((hP.dq i).mul (hQ.dp i)) ((hP.dp i).mul (hQ.dq i))

theorem Fits.adPow {n : ℕ} {χ P : CartPoly} (hχ : Fits n χ) (hP : Fits n P) (k : ℕ) :
    Fits n (adPow χ k P) := by
  induction k with
  | zero => exact hP
  | succ k ih => exact ih.bracket hχ

theorem dq_eq_nil_of_fits {n : ℕ} {P : CartPoly} (hP : Fits n P) {i : ℕ} (hi : n ≤ i) :
    dq i P = [] := dq_eq_nil_of_getD fun m hm => (hP m hm i hi).1

theorem dp_eq_nil_of_fits {n : ℕ} {P : CartPoly} (hP : Fits n P) {i : ℕ} (hi : n ≤ i) :
    dp i P = [] := dp_eq_nil_of_getD fun m hm => (hP m hm i hi).2

/-! ### Evaluation of the bracket -/

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ}

theorem eval_flatMap (f : ℕ → CartPoly) (L : List ℕ) (z : (Fin n → R) × (Fin n → R)) :
    eval (L.flatMap f) z = (L.map fun i => eval (f i) z).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    rw [List.flatMap_cons, ← add, eval_add, ih]
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

theorem dq_eq_nil_of_width {P : CartPoly} {i : ℕ} (hi : width P ≤ i) : dq i P = [] :=
  dq_eq_nil_of_getD fun _ hm => (getD_eq_zero_of_width hm hi).1

theorem dp_eq_nil_of_width {P : CartPoly} {i : ℕ} (hi : width P ≤ i) : dp i P = [] :=
  dp_eq_nil_of_getD fun _ hm => (getD_eq_zero_of_width hm hi).2

/-- Evaluation of the bracket as a sum over `Fin n`, for `P` fitting in `n` variables. -/
theorem eval_bracket (P Q : CartPoly) (hP : Fits n P) (z : (Fin n → R) × (Fin n → R)) :
    eval (bracket P Q) z = ∑ i : Fin n, (eval (dq i P) z * eval (dp i Q) z -
      eval (dp i P) z * eval (dq i Q) z) := by
  rw [bracket, eval_flatMap]
  set g : ℕ → R := fun i => eval (dq i P) z * eval (dp i Q) z -
      eval (dp i P) z * eval (dq i Q) z with hg
  have hl : ((List.range (width P)).map fun i =>
      eval (sub (mul (dq i P) (dp i Q)) (mul (dp i P) (dq i Q))) z).sum =
      ∑ i ∈ Finset.range (width P), g i := by
    simp only [eval_sub, eval_mul, hg]
    rfl
  rw [hl, sum_range_eq_of_zero g (width P) n, Finset.sum_range g]
  intro i hi
  have h1 : dq i P = [] ∧ dp i P = [] := by
    rcases hi with hi | hi
    · exact ⟨dq_eq_nil_of_fits hP hi, dp_eq_nil_of_fits hP hi⟩
    · exact ⟨dq_eq_nil_of_width hi, dp_eq_nil_of_width hi⟩
  simp [hg, h1.1, h1.2]

theorem two_half (R : Type*) [CommRing R] [Algebra ℚ R] :
    algebraMap ℚ R (1 / 2) * ((2 : ℕ) : R) = 1 := by
  rw [← map_natCast (algebraMap ℚ R), ← map_mul]; norm_num

theorem eval_dq_action (i j : Fin n) (z : (Fin n → R) × (Fin n → R)) :
    eval (dq i (action j)) z = if i = j then z.1 j else 0 := by
  have h2 : CartMono.dq i (⟨[], unitExp j 2, 1 / 2⟩ : CartMono) = [] := by
    simp [CartMono.dq]
  simp only [action, dq_cons, dq_nil, h2, List.append_nil]
  by_cases hij : i = j
  · subst hij
    have h1 := eval_dq_mono i (⟨unitExp i 2, [], 1 / 2⟩ : CartMono) z
    simp only [getD_unitExp, List.getD_nil, ite_true, pow_zero, mul_one] at h1
    have hp : ∏ k ∈ Finset.univ.erase i,
        (z.1 k ^ (if (k : ℕ) = i then 2 else 0) : R) = 1 := by
      refine Finset.prod_eq_one fun k hk => ?_
      have hk' : (k : ℕ) ≠ i := fun e => (Finset.mem_erase.1 hk).1 (Fin.ext e)
      simp [hk']
    rw [h1, hp]
    simp only [ite_true, mul_one, two_half R, one_mul]
    simp
  · have hij' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
    have h0 : (unitExp j 2).getD i 0 = 0 := by rw [getD_unitExp]; simp [hij']
    simp only [CartMono.dq, h0, ↓reduceIte, eval_nil, hij]

theorem eval_dp_action (i j : Fin n) (z : (Fin n → R) × (Fin n → R)) :
    eval (dp i (action j)) z = if i = j then z.2 j else 0 := by
  have h2 : CartMono.dp i (⟨unitExp j 2, [], 1 / 2⟩ : CartMono) = [] := by
    simp [CartMono.dp]
  simp only [action, dp_cons, dp_nil, h2, List.nil_append, List.append_nil]
  by_cases hij : i = j
  · subst hij
    have h1 := eval_dp_mono i (⟨[], unitExp i 2, 1 / 2⟩ : CartMono) z
    simp only [getD_unitExp, List.getD_nil, ite_true, pow_zero, one_mul] at h1
    have hp : ∏ k ∈ Finset.univ.erase i,
        (z.2 k ^ (if (k : ℕ) = i then 2 else 0) : R) = 1 := by
      refine Finset.prod_eq_one fun k hk => ?_
      have hk' : (k : ℕ) ≠ i := fun e => (Finset.mem_erase.1 hk).1 (Fin.ext e)
      simp [hk']
    rw [h1, hp]
    simp only [ite_true, mul_one, two_half R, one_mul]
    simp
  · have hij' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
    have h0 : (unitExp j 2).getD i 0 = 0 := by rw [getD_unitExp]; simp [hij']
    simp only [CartMono.dp, h0, ↓reduceIte, hij]
    simp

/-- The action bracket: `{I_j, P} = q_j ∂_{p_j} P - p_j ∂_{q_j} P`. -/
theorem eval_bracket_action (j : Fin n) (P : CartPoly) (z : (Fin n → R) × (Fin n → R)) :
    eval (bracket (action j) P) z = z.1 j * eval (dp j P) z - z.2 j * eval (dq j P) z := by
  rw [eval_bracket _ _ (Fits.action j.2)]
  simp only [eval_dq_action, eval_dp_action]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [hi]
  · simp

/-- Over `ℂ`: the formal bracket is the repo's Poisson bracket. -/
theorem eval_bracket_complex (P Q : CartPoly) (hP : Fits n P) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    eval (bracket P Q) z =
      KAM.Canonical.poissonBracket (fun z => eval P z) (fun z => eval Q z) z := by
  rw [eval_bracket P Q hP, KAM.Canonical.poissonBracket]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_eval_q, fderiv_eval_p, fderiv_eval_p, fderiv_eval_q]

/-- Over `ℝ`: the formal bracket is the derivative of `P` along the Hamiltonian field of `Q`. -/
theorem eval_bracket_real (P Q : CartPoly) (hP : Fits n P) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    eval (bracket P Q) z =
      fderiv ℝ (fun z : (Fin n → ℝ) × (Fin n → ℝ) => eval P z) z
        (KAM.hamiltonianVectorField (fun z : (Fin n → ℝ) × (Fin n → ℝ) => eval Q z) z) := by
  rw [eval_bracket P Q hP, fderiv_eval_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [KAM.hamiltonianVectorField, fderiv_eval_p, fderiv_eval_q]
  ring

theorem eval_adPow_complex (χ P : CartPoly) (hχ : Fits n χ) (hP : Fits n P) (k : ℕ) :
    (fun z : (Fin n → ℂ) × (Fin n → ℂ) => eval (adPow χ k P) z) =
      KAM.Canonical.adPow (fun z => eval χ z) k (fun z => eval P z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext z
    rw [KAM.Canonical.adPow, ← ih]
    exact eval_bracket_complex (adPow χ k P) χ (hχ.adPow hP k) z

end CartPoly

end KAM.EffectiveStability
