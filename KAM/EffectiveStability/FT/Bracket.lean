/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.FT.Deriv
public import KAM.EffectiveStability.Poly.Bracket
public import KAM.Canonical.Setting
public import KAM.Frozen.Defs.HamiltonianVectorField

/-!
# Fourier–Taylor polynomials: Poisson bracket and Lie sums (track B, B4-FT)

`ftBracket P Q = ∑ i, (∂_{φ_i} P ∂_{J_i} Q - ∂_{J_i} P ∂_{φ_i} Q)` (angle slot first, as in
`KAM.Canonical.poissonBracket`), the sum running over `i < ftWidth P`. With `FTFits n P`:

* over `ℂ`: `ftEvalC (ftBracket P Q) z = KAM.Canonical.poissonBracket (ftEvalC P) (ftEvalC Q) z`;
* over `ℝ`: `ftEvalR (ftBracket P Q) x = fderiv ℝ (ftEvalR P) x (KAM.hamiltonianVectorField
  (ftEvalR Q) x)`;
* `ftAdPow` matches `KAM.Canonical.adPow`, and `ftLieSum χ H L = ∑_{j<L} (1/j!) ad_χ^j H` has the
  evaluation lemma `ftEvalC_lieSum_complex`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

/-- A bound on the lengths of all frequency and exponent lists of `P`. -/
def ftWidth : FTPoly → ℕ
  | [] => 0
  | m :: P => max (max m.k.length m.α.length) (ftWidth P)

theorem ftLength_le_width {P : FTPoly} {m : FTMono} (h : m ∈ P) :
    m.k.length ≤ ftWidth P ∧ m.α.length ≤ ftWidth P := by
  induction P with
  | nil => simp at h
  | cons m' P ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp [ftWidth]
    · have := ih h
      simp only [ftWidth]
      omega

theorem ftGetD_zero_of_width {P : FTPoly} {m : FTMono} (h : m ∈ P) {i : ℕ}
    (hi : ftWidth P ≤ i) : m.k.getD i 0 = 0 ∧ m.α.getD i 0 = 0 := by
  have := ftLength_le_width h
  exact ⟨ftGetD_zero_of_length_le m.k i (by omega), ftGetD_zero_of_length_le m.α i (by omega)⟩

/-- The formal Poisson bracket `∑ i, (∂_{φ_i} P ∂_{J_i} Q - ∂_{J_i} P ∂_{φ_i} Q)`. -/
def ftBracket (P Q : FTPoly) : FTPoly :=
  (List.range (ftWidth P)).flatMap fun i =>
    ftSub (ftMul (ftDφ i P) (ftDJ i Q)) (ftMul (ftDJ i P) (ftDφ i Q))

/-- Iterated bracket `ad_χ^k P`: `ad⁰ P = P`, `ad^{k+1} P = {ad^k P, χ}`. -/
def ftAdPow (χ : FTPoly) : ℕ → FTPoly → FTPoly
  | 0, P => P
  | k + 1, P => ftBracket (ftAdPow χ k P) χ

/-- The finite Lie sum `∑_{j < L} (1/j!) ad_χ^j H`. -/
def ftLieSum (χ H : FTPoly) (L : ℕ) : FTPoly :=
  (List.range L).flatMap fun j => ftSmul (1 / (j.factorial : ℚ)) (ftAdPow χ j H)

/-! ### Typing data -/

theorem ftFits_flatMap {n : ℕ} {f : ℕ → FTPoly} {L : List ℕ} (h : ∀ i ∈ L, FTFits n (f i)) :
    FTFits n (L.flatMap f) := by
  induction L with
  | nil => exact ftFits_nil n
  | cons i L ih =>
    rw [List.flatMap_cons]
    exact ftFits_add (h i (List.mem_cons_self ..)) (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem ftFits_dφ {n : ℕ} (i : ℕ) {P : FTPoly} (hP : FTFits n P) : FTFits n (ftDφ i P) := by
  intro m' hm' k hk
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hm'
  exact hP m hm k hk

theorem ftFits_dJ {n : ℕ} (i : ℕ) {P : FTPoly} (hP : FTFits n P) : FTFits n (ftDJ i P) := by
  intro m' hm' k hk
  obtain ⟨m, hm, hm'⟩ := List.mem_flatMap.1 hm'
  have h1 := hP m hm k hk
  unfold ftMonoDJ at hm'
  split_ifs at hm' with h
  · simp at hm'
  · obtain rfl : m' = _ := List.mem_singleton.1 hm'
    have hki : k ≠ i := fun e => h (e ▸ h1.2)
    exact ⟨h1.1, by rw [getD_set_of_ne_zero _ _ _ _ h]; simpa [hki] using h1.2⟩

theorem ftFits_bracket {n : ℕ} {P Q : FTPoly} (hP : FTFits n P) (hQ : FTFits n Q) :
    FTFits n (ftBracket P Q) :=
  ftFits_flatMap fun i _ =>
    ftFits_sub (ftFits_mul (ftFits_dφ i hP) (ftFits_dJ i hQ))
      (ftFits_mul (ftFits_dJ i hP) (ftFits_dφ i hQ))

theorem ftFits_adPow {n : ℕ} {χ P : FTPoly} (hχ : FTFits n χ) (hP : FTFits n P) (k : ℕ) :
    FTFits n (ftAdPow χ k P) := by
  induction k with
  | zero => exact hP
  | succ k ih => exact ftFits_bracket ih hχ

theorem ftFits_lieSum {n : ℕ} {χ H : FTPoly} (hχ : FTFits n χ) (hH : FTFits n H) (L : ℕ) :
    FTFits n (ftLieSum χ H L) :=
  ftFits_flatMap fun j _ => ftFits_smul _ (ftFits_adPow hχ hH j)

theorem ftDJ_eq_nil_of_getD {P : FTPoly} {i : ℕ} (h : ∀ m ∈ P, m.α.getD i 0 = 0) :
    ftDJ i P = [] := by
  induction P with
  | nil => rfl
  | cons m P ih =>
    rw [ftDJ_cons, ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))]
    have h0 := h m (List.mem_cons_self ..)
    simp only [ftMonoDJ, h0, ↓reduceIte, List.nil_append]

/-! ### Evaluation of the bracket -/

section Eval

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {n : ℕ} (cf sf : 𝕜 → 𝕜) (p : 𝕜)

omit [CharZero 𝕜] in
theorem ftEvalG_flatMap (f : ℕ → FTPoly) (L : List ℕ) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (L.flatMap f) z = (L.map fun i => ftEvalG cf sf p (f i) z).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    rw [List.flatMap_cons, ftEvalG_append, ih]
    simp

theorem ftEvalG_dφ_zero {P : FTPoly} {i : ℕ} (h : ∀ m ∈ P, m.k.getD i 0 = 0)
    (z : (Fin n → 𝕜) × (Fin n → 𝕜)) : ftEvalG cf sf p (ftDφ i P) z = 0 := by
  induction P with
  | nil => simp
  | cons m P ih =>
    rw [ftDφ_cons, ftEvalG_cons, ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))]
    rw [ftMonoEvalG_dφ cf sf p, h m (List.mem_cons_self ..)]
    simp

/-- Evaluation of the bracket as a sum over `Fin n`, for `P` fitting in `n` variables. -/
theorem ftEvalG_bracket (h : FTTrig cf sf) (P Q : FTPoly) (hP : FTFits n P)
    (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (ftBracket P Q) z = ∑ i : Fin n,
      (ftEvalG cf sf p (ftDφ i P) z * ftEvalG cf sf p (ftDJ i Q) z -
        ftEvalG cf sf p (ftDJ i P) z * ftEvalG cf sf p (ftDφ i Q) z) := by
  rw [ftBracket, ftEvalG_flatMap]
  set g : ℕ → 𝕜 := fun i => ftEvalG cf sf p (ftDφ i P) z * ftEvalG cf sf p (ftDJ i Q) z -
      ftEvalG cf sf p (ftDJ i P) z * ftEvalG cf sf p (ftDφ i Q) z with hg
  have hl : ((List.range (ftWidth P)).map fun i => ftEvalG cf sf p
      (ftSub (ftMul (ftDφ i P) (ftDJ i Q)) (ftMul (ftDJ i P) (ftDφ i Q))) z).sum =
      ∑ i ∈ Finset.range (ftWidth P), g i := by
    simp only [ftEvalG_sub, ftEvalG_mul cf sf p h, hg]
    rfl
  rw [hl, CartPoly.sum_range_eq_of_zero g (ftWidth P) n, Finset.sum_range g]
  intro i hi
  have h1 : (∀ m ∈ P, m.k.getD i 0 = 0) ∧ (∀ m ∈ P, m.α.getD i 0 = 0) := by
    rcases hi with hi | hi
    · exact ⟨fun m hm => (hP m hm i hi).1, fun m hm => (hP m hm i hi).2⟩
    · exact ⟨fun m hm => (ftGetD_zero_of_width hm hi).1, fun m hm => (ftGetD_zero_of_width hm hi).2⟩
  simp [hg, ftEvalG_dφ_zero cf sf p h1.1, ftDJ_eq_nil_of_getD h1.2]

end Eval

/-! ### Complex and real correctness -/

variable {n : ℕ}

/-- Over `ℂ`: the formal bracket is the repo's Poisson bracket. -/
theorem ftEvalC_bracket_complex (P Q : FTPoly) (hP : FTFits n P) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    ftEvalC (ftBracket P Q) z =
      KAM.Canonical.poissonBracket (fun z => ftEvalC P z) (fun z => ftEvalC Q z) z := by
  rw [ftEvalC, ftEvalG_bracket _ _ _ ftTrig_complex P Q hP, KAM.Canonical.poissonBracket]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ftEvalC_fderiv_dφ, ftEvalC_fderiv_dJ, ftEvalC_fderiv_dJ, ftEvalC_fderiv_dφ]
  rfl

/-- Over `ℝ`: the formal bracket is the derivative of `P` along the Hamiltonian field of `Q`. -/
theorem ftEvalR_bracket_real (P Q : FTPoly) (hP : FTFits n P) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    ftEvalR (ftBracket P Q) x =
      fderiv ℝ (fun x : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR P x) x
        (KAM.hamiltonianVectorField (fun x : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR Q x) x) := by
  rw [ftEvalR, ftEvalG_bracket _ _ _ ftTrig_real P Q hP]
  rw [show (fun x : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR P x) =
    fun x => ftEvalG Real.cos Real.sin Real.pi P x from rfl,
    fderiv_ftEvalG_apply Real.pi Real.contDiff_cos Real.contDiff_sin Real.hasDerivAt_cos
      Real.hasDerivAt_sin]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [KAM.hamiltonianVectorField, ftEvalR_fderiv_dJ, ftEvalR_fderiv_dφ]
  simp only [ftEvalR]
  ring

theorem ftEvalC_adPow_complex (χ P : FTPoly) (hχ : FTFits n χ) (hP : FTFits n P) (k : ℕ) :
    (fun z : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC (ftAdPow χ k P) z) =
      KAM.Canonical.adPow (fun z => ftEvalC χ z) k (fun z => ftEvalC P z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext z
    rw [KAM.Canonical.adPow, ← ih]
    exact ftEvalC_bracket_complex (ftAdPow χ k P) χ (ftFits_adPow hχ hP k) z

theorem ftEvalG_lieSum {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (cf sf : 𝕜 → 𝕜) (p : 𝕜)
    (χ H : FTPoly) (L : ℕ) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (ftLieSum χ H L) z =
      ∑ j ∈ Finset.range L, ((1 / (j.factorial : ℚ) : ℚ) : 𝕜) *
        ftEvalG cf sf p (ftAdPow χ j H) z := by
  have hs : ∀ L : ℕ, ftLieSum χ H (L + 1) =
      ftLieSum χ H L ++ ftSmul (1 / (L.factorial : ℚ)) (ftAdPow χ L H) := fun L => by
    simp [ftLieSum, List.range_succ]
  induction L with
  | zero => simp [ftLieSum]
  | succ L ih =>
    rw [hs, ftEvalG_append, ih, ftEvalG_smul, Finset.sum_range_succ]

/-- The finite Lie sum evaluates, over `ℂ`, to `∑ (j!)⁻¹ ad_χ^j H`. -/
theorem ftEvalC_lieSum_complex (χ H : FTPoly) (hχ : FTFits n χ) (hH : FTFits n H) (L : ℕ)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    ftEvalC (ftLieSum χ H L) z =
      ∑ j ∈ Finset.range L, ((j.factorial : ℂ)⁻¹) *
        KAM.Canonical.adPow (fun z => ftEvalC χ z) j (fun z => ftEvalC H z) z := by
  rw [ftEvalC, ftEvalG_lieSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← congrFun (ftEvalC_adPow_complex χ H hχ hH j) z]
  simp [ftEvalC]

end KAM.EffectiveStability
