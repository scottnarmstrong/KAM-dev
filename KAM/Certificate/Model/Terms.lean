/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Poly.Ops

/-!
# Terms with rounding errors: the kernel-side toolkit of the model algebra

An error term `(k, c, e)` is a Fourier term `c χ_k` computed by the backend together with a bound
`e` on its rounding error, paid at the weight of its key: on the strip the term stands for an
exact value within `val e · |χ_k|`. This module supplies the backend complex operations with
their error bounds (`CC.addC`, `CC.mulC`), balanced upward sums (`sumUp`: pairwise rounds, so the
kernel evaluates sums of depth about `log₂ N` and never a long accumulator chain), the
strip-weighted radius of a term list (`errRadius`, `CertPoly.supNormUp`), the
sorted merge of two term lists (`mergeErrTerms`, structural; merging is sound for any input
order and complete for lexicographically sorted keys), the direct product (`directItems`), and
the truncation at a cutoff (`truncKeep`, `truncErr`).
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM CertArith

/-- A Fourier term with a rounding-error bound: key, backend coefficient, error. -/
abbrev ErrTerm (α : Type) : Type := CertKey × CC α × α

/-- `|k|₁` of a stored key. -/
def keyDeg (k : CertKey) : ℕ := (k.map Int.natAbs).sum

/-- Lexicographic comparison of stored keys (`.eq` only on equal lists). -/
def keyCmp : CertKey → CertKey → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => if a < b then .lt else if b < a then .gt else keyCmp as bs

theorem keyCmp_eq_eq : ∀ {k l : CertKey}, keyCmp k l = .eq → k = l
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [keyCmp] at h
  | _ :: _, [], h => by simp [keyCmp] at h
  | a :: as, b :: bs, h => by
    simp only [keyCmp] at h
    split_ifs at h with h1 h2
    rw [keyCmp_eq_eq h, show a = b by omega]

section Arith

variable {α : Type} [CertArith α]

/-- Rounded sum of backend complex numbers. -/
def CC.addC (c d : CC α) : CC α := ⟨add c.re d.re, add c.im d.im⟩

/-- Error bound of `CC.addC`. -/
def CC.addErrC (c d : CC α) : α := upAdd (addErr c.re d.re) (addErr c.im d.im)

/-- Rounded product of backend complex numbers. -/
def CC.mulC (c d : CC α) : CC α :=
  ⟨add (mul c.re d.re) (neg (mul c.im d.im)), add (mul c.re d.im) (mul c.im d.re)⟩

/-- Error bound of `CC.mulC`. -/
def CC.mulErrC (c d : CC α) : α :=
  upAdd (CertBall.mulReErr c.re c.im d.re d.im) (CertBall.mulImErr c.re c.im d.re d.im)

/-- Rounded product of a backend complex number by a backend real. -/
def CC.scaleC (s : α) (c : CC α) : CC α := ⟨mul s c.re, mul s c.im⟩

/-- Error bound of `CC.scaleC`. -/
def CC.scaleErrC (s : α) (c : CC α) : α := upAdd (mulErr s c.re) (mulErr s c.im)

variable [LawfulCertArith α]

theorem CC.norm_add_sub_addC (c d : CC α) :
    ‖c.toC + d.toC - (c.addC d).toC‖ ≤ val (c.addErrC d) := by
  have e1 := LawfulCertArith.add_err c.re d.re
  have e2 := LawfulCertArith.add_err c.im d.im
  have u := LawfulCertArith.upAdd_ge (addErr c.re d.re) (addErr c.im d.im)
  refine (norm_le_of_re_im (A := val (addErr c.re d.re)) (B := val (addErr c.im d.im)) ?_ ?_).trans
    u
  · simp only [Complex.sub_re, Complex.add_re, CC.addC, CC.toC]
    rw [abs_sub_comm]; exact e1
  · simp only [Complex.sub_im, Complex.add_im, CC.addC, CC.toC]
    rw [abs_sub_comm]; exact e2

theorem CC.norm_mul_sub_mulC (c d : CC α) :
    ‖c.toC * d.toC - (c.mulC d).toC‖ ≤ val (c.mulErrC d) := by
  have u := LawfulCertArith.upAdd_ge (CertBall.mulReErr c.re c.im d.re d.im)
    (CertBall.mulImErr c.re c.im d.re d.im)
  refine (norm_le_of_re_im (A := val (CertBall.mulReErr c.re c.im d.re d.im))
    (B := val (CertBall.mulImErr c.re c.im d.re d.im)) ?_ ?_).trans u
  · simp only [Complex.sub_re, Complex.mul_re, CC.mulC, CC.toC]
    rw [abs_sub_comm]; exact CertBall.mulReErr_bound _ _ _ _
  · simp only [Complex.sub_im, Complex.mul_im, CC.mulC, CC.toC]
    rw [abs_sub_comm]; exact CertBall.mulImErr_bound _ _ _ _

theorem CC.norm_scale_sub_scaleC (s : α) (c : CC α) :
    ‖(val s : ℂ) * c.toC - (CC.scaleC s c).toC‖ ≤ val (CC.scaleErrC s c) := by
  have e1 := LawfulCertArith.mul_err s c.re
  have e2 := LawfulCertArith.mul_err s c.im
  have u := LawfulCertArith.upAdd_ge (mulErr s c.re) (mulErr s c.im)
  refine (norm_le_of_re_im (A := val (mulErr s c.re)) (B := val (mulErr s c.im)) ?_ ?_).trans u
  · simp only [Complex.sub_re, Complex.mul_re, CC.scaleC, CC.toC, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [abs_sub_comm]; exact e1
  · simp only [Complex.sub_im, Complex.mul_im, CC.scaleC, CC.toC, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    rw [abs_sub_comm]; exact e2

end Arith

/-! ### Balanced upward sums -/

section Sums

variable {α : Type} [CertArith α]

/-- One round of pairwise upward sums: `[a, b, c, d, e] ↦ [a + b, c + d, e]`. -/
def pairUp : List α → List α
  | a :: b :: rest => upAdd a b :: pairUp rest
  | l => l

/-- `r` rounds of `pairUp` (a list of length `≤ 2^r` collapses to at most one entry). -/
def pairRounds : ℕ → List α → List α
  | 0, l => l
  | r + 1, l => pairRounds r (pairUp l)

/-- `Σ g x` rounded upward, summed as a balanced tree (64 rounds of pairwise sums, then a
`foldr` of what remains): the kernel evaluates nested sums of depth about `log₂` of the length,
never a long accumulator chain. -/
def sumUp {β : Type} (g : β → α) (L : List β) : α :=
  (pairRounds 64 (L.map g)).foldr upAdd (ofInt 0)

/-- The weighted size `|e| · w^{|k|₁}` of an error at key `k`, rounded upward. -/
def weightTermUp (W : CertWeight) (k : CertKey) (e : α) : α :=
  upMul (abs e) (ofRatUp (W.w ^ keyDeg k))

/-- The strip-weighted radius `Σ e · w^{|k|₁}` of a list of error terms. -/
def errRadius (W : CertWeight) (L : List (ErrTerm α)) : α :=
  sumUp (fun t => weightTermUp W t.1 t.2.2) L

/-- A kernel-safe upper bound of `sup_{T_ρ} |P|`: `Σ |c_k| w^{|k|₁}` (balanced sum). -/
def CertPoly.supNormUp (W : CertWeight) (P : CertPoly α) : α :=
  sumUp (fun t => weightTermUp W t.1 t.2.normUp) P.terms

variable [LawfulCertArith α]

theorem pairUp_ge : ∀ l : List α, (l.map val).sum ≤ ((pairUp l).map val).sum
  | [] => le_rfl
  | [a] => le_rfl
  | a :: b :: rest => by
    have ih := pairUp_ge rest
    have hu := LawfulCertArith.upAdd_ge a b
    simp only [pairUp, List.map_cons, List.sum_cons]
    linarith

theorem pairRounds_ge : ∀ (r : ℕ) (l : List α),
    (l.map val).sum ≤ ((pairRounds r l).map val).sum
  | 0, _ => le_rfl
  | r + 1, l => (pairUp_ge l).trans (pairRounds_ge r (pairUp l))

theorem foldr_upAdd_ge : ∀ l : List α, (l.map val).sum ≤ val (l.foldr upAdd (ofInt 0))
  | [] => by simp [LawfulCertArith.val_ofInt]
  | a :: l => by
    have ih := foldr_upAdd_ge l
    have hu := LawfulCertArith.upAdd_ge a (l.foldr upAdd (ofInt 0))
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    linarith

theorem sumUp_ge {β : Type} (g : β → α) (L : List β) :
    (L.map fun x => val (g x)).sum ≤ val (sumUp g L) := by
  have h := (pairRounds_ge 64 (L.map g)).trans (foldr_upAdd_ge _)
  rw [List.map_map] at h
  exact h

theorem norm_character_le_keyDeg {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (k : CertKey) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n W.rho) :
    ‖character (certKeyFun n k) θ‖ ≤ (W.w : ℝ) ^ keyDeg k :=
  (norm_character_le_weight hW _ hθ).trans
    (pow_le_pow_right₀ (CertWeight.one_le_w hW) (sum_natAbs_certKeyFun_le n k))

theorem weightTermUp_nonneg {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    (k : CertKey) (e : α) : 0 ≤ val (weightTermUp W k e) := by
  have hw : (0 : ℝ) ≤ ((W.w ^ keyDeg k : ℚ) : ℝ) := by
    have := CertWeight.one_le_w hW
    push_cast; positivity
  have h1 := LawfulCertArith.ofRatUp_ge (α := α) (W.w ^ keyDeg k)
  have h2 := LawfulCertArith.upMul_ge (abs e) (ofRatUp (W.w ^ keyDeg k))
    (by rw [LawfulCertArith.val_abs]; positivity) (hw.trans h1)
  rw [LawfulCertArith.val_abs] at h2
  exact (mul_nonneg (abs_nonneg _) (hw.trans h1)).trans h2

theorem weightTermUp_ge {n : ℕ} {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    (k : CertKey) (e : α) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n W.rho) :
    val e * ‖character (certKeyFun n k) θ‖ ≤ val (weightTermUp W k e) := by
  have hc := norm_character_le_keyDeg hW k hθ
  have hw : (0 : ℝ) ≤ ((W.w ^ keyDeg k : ℚ) : ℝ) := by
    have := CertWeight.one_le_w hW
    push_cast; positivity
  have h1 := LawfulCertArith.ofRatUp_ge (α := α) (W.w ^ keyDeg k)
  have h2 := LawfulCertArith.upMul_ge (abs e) (ofRatUp (W.w ^ keyDeg k))
    (by rw [LawfulCertArith.val_abs]; positivity) (hw.trans h1)
  rw [LawfulCertArith.val_abs] at h2
  push_cast at h1
  calc val e * ‖character (certKeyFun n k) θ‖ ≤ |val e| * ‖character (certKeyFun n k) θ‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ |val e| * val (ofRatUp (W.w ^ keyDeg k) : α) :=
        mul_le_mul_of_nonneg_left (hc.trans h1) (abs_nonneg _)
    _ ≤ _ := h2

theorem sumUp_nonneg {β : Type} {g : β → α} (hg : ∀ x, 0 ≤ val (g x)) (L : List β) :
    0 ≤ val (sumUp g L) :=
  (List.sum_nonneg fun y hy => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy
    exact hg x).trans (sumUp_ge g L)

theorem CertPoly.supNormUp_nonneg {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    (P : CertPoly α) : 0 ≤ val (P.supNormUp W) :=
  sumUp_nonneg (fun _ => weightTermUp_nonneg hW _ _) _

theorem CertPoly.norm_eval_le_supNormUp {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (P : CertPoly α) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n W.rho) : ‖P.eval n θ‖ ≤ val (P.supNormUp W) := by
  refine le_trans ?_ (sumUp_ge _ _)
  unfold CertPoly.eval
  induction P.terms with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (norm_add_le _ _).trans (add_le_add ?_ ih)
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (CC.norm_le_normUp t.2) (norm_nonneg _)).trans
      (weightTermUp_ge hW t.1 t.2.normUp hθ)

end Sums

/-! ### Denotation of error-term lists -/

section Denote

variable {α : Type} [CertArith α]

/-- The value `Σ c χ_k` of a list of error terms. -/
def errTermsEval (n : ℕ) (L : List (ErrTerm α)) (θ : Fin n → ℂ) : ℂ :=
  (L.map fun t => t.2.1.toC * character (certKeyFun n t.1) θ).sum

/-- The pointwise error budget `Σ e |χ_k|` of a list of error terms. -/
def errTermsErr (n : ℕ) (L : List (ErrTerm α)) (θ : Fin n → ℂ) : ℝ :=
  (L.map fun t => val t.2.2 * ‖character (certKeyFun n t.1) θ‖).sum

@[simp] theorem errTermsEval_nil (n : ℕ) (θ : Fin n → ℂ) :
    errTermsEval n ([] : List (ErrTerm α)) θ = 0 := rfl

@[simp] theorem errTermsEval_cons (n : ℕ) (t : ErrTerm α) (L : List (ErrTerm α))
    (θ : Fin n → ℂ) : errTermsEval n (t :: L) θ =
      t.2.1.toC * character (certKeyFun n t.1) θ + errTermsEval n L θ := by
  simp [errTermsEval]

@[simp] theorem errTermsErr_nil (n : ℕ) (θ : Fin n → ℂ) :
    errTermsErr n ([] : List (ErrTerm α)) θ = 0 := rfl

@[simp] theorem errTermsErr_cons (n : ℕ) (t : ErrTerm α) (L : List (ErrTerm α))
    (θ : Fin n → ℂ) : errTermsErr n (t :: L) θ =
      val t.2.2 * ‖character (certKeyFun n t.1) θ‖ + errTermsErr n L θ := by
  simp [errTermsErr]

theorem errTermsEval_append (n : ℕ) (L M : List (ErrTerm α)) (θ : Fin n → ℂ) :
    errTermsEval n (L ++ M) θ = errTermsEval n L θ + errTermsEval n M θ := by
  simp [errTermsEval]

theorem errTermsErr_append (n : ℕ) (L M : List (ErrTerm α)) (θ : Fin n → ℂ) :
    errTermsErr n (L ++ M) θ = errTermsErr n L θ + errTermsErr n M θ := by
  simp [errTermsErr]

theorem errTermsErr_le_errRadius [LawfulCertArith α] {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (L : List (ErrTerm α)) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n W.rho) : errTermsErr n L θ ≤ val (errRadius W L) :=
  le_trans (List.sum_le_sum fun t _ => weightTermUp_ge hW t.1 t.2.2 hθ) (sumUp_ge _ _)

/-- Exact terms with zero error. -/
def CertPoly.toErrTerms (P : CertPoly α) : List (ErrTerm α) :=
  P.terms.map fun t => (t.1, t.2, ofInt 0)

theorem CertPoly.errTermsEval_toErrTerms (n : ℕ) (P : CertPoly α) (θ : Fin n → ℂ) :
    errTermsEval n P.toErrTerms θ = P.eval n θ := by
  simp [errTermsEval, CertPoly.toErrTerms, CertPoly.eval, Function.comp_def]

theorem CertPoly.errTermsErr_toErrTerms [LawfulCertArith α] (n : ℕ) (P : CertPoly α)
    (θ : Fin n → ℂ) : errTermsErr n P.toErrTerms θ = 0 := by
  simp [errTermsErr, CertPoly.toErrTerms, LawfulCertArith.val_ofInt, Function.comp_def]

end Denote

/-! ### Merge -/

section Merge

variable {α : Type} [CertArith α]

/-- Two error terms at the same key, coefficients added (rounding paid in the error). -/
def mergeErrPair (x y : ErrTerm α) : ErrTerm α :=
  (x.1, x.2.1.addC y.2.1, upAdd (upAdd x.2.2 y.2.2) (x.2.1.addErrC y.2.1))

/-- Insert the head `x` of the first list (tail `xs`, whose merge is `rec`) into the second. -/
def mergeErrInsert (x : ErrTerm α) (xs : List (ErrTerm α))
    (rec : List (ErrTerm α) → List (ErrTerm α)) : List (ErrTerm α) → List (ErrTerm α)
  | [] => x :: xs
  | y :: ys =>
    match keyCmp x.1 y.1 with
    | .lt => x :: rec (y :: ys)
    | .gt => y :: mergeErrInsert x xs rec ys
    | .eq => mergeErrPair x y :: rec ys

/-- Merge of two error-term lists: equal keys are added, the order is the lexicographic merge
(sound for any input; complete for sorted inputs). -/
def mergeErrTerms : List (ErrTerm α) → List (ErrTerm α) → List (ErrTerm α)
  | [], ys => ys
  | x :: xs, ys => mergeErrInsert x xs (mergeErrTerms xs) ys

variable [LawfulCertArith α]

theorem mergeErrPair_spec (n : ℕ) {x y : ErrTerm α} (h : x.1 = y.1) (θ : Fin n → ℂ) :
    ‖x.2.1.toC * character (certKeyFun n x.1) θ + y.2.1.toC * character (certKeyFun n y.1) θ -
        (mergeErrPair x y).2.1.toC * character (certKeyFun n (mergeErrPair x y).1) θ‖ +
      val x.2.2 * ‖character (certKeyFun n x.1) θ‖ +
      val y.2.2 * ‖character (certKeyFun n y.1) θ‖ ≤
      val (mergeErrPair x y).2.2 * ‖character (certKeyFun n (mergeErrPair x y).1) θ‖ := by
  simp only [mergeErrPair, ← h]
  set χ := character (certKeyFun n x.1) θ
  have hχ := norm_nonneg χ
  have e := CC.norm_add_sub_addC x.2.1 y.2.1
  have u1 := LawfulCertArith.upAdd_ge x.2.2 y.2.2
  have u2 := LawfulCertArith.upAdd_ge (upAdd x.2.2 y.2.2) (x.2.1.addErrC y.2.1)
  rw [← add_mul, ← sub_mul, norm_mul]
  have := mul_le_mul_of_nonneg_right e hχ
  have := mul_le_mul_of_nonneg_right (u1.trans (by linarith [u2] :
    val (upAdd x.2.2 y.2.2) ≤ val (upAdd (upAdd x.2.2 y.2.2) (x.2.1.addErrC y.2.1)) -
      val (x.2.1.addErrC y.2.1))) hχ
  nlinarith

/-- **Merge contract**: the merged list carries the sum of the two lists, its error budget
pays both budgets and the rounding of every addition. -/
theorem mergeErrTerms_spec (n : ℕ) (θ : Fin n → ℂ) : ∀ (xs ys : List (ErrTerm α)),
    ‖errTermsEval n xs θ + errTermsEval n ys θ - errTermsEval n (mergeErrTerms xs ys) θ‖ +
      errTermsErr n xs θ + errTermsErr n ys θ ≤ errTermsErr n (mergeErrTerms xs ys) θ
  | [], ys => by simp [mergeErrTerms]
  | x :: xs, ys => by
    have hrec := mergeErrTerms_spec n θ xs
    rw [mergeErrTerms]
    induction ys with
    | nil => simp [mergeErrInsert]
    | cons y ys ih =>
      simp only [mergeErrInsert]
      split
      · have h := hrec (y :: ys)
        simp only [errTermsEval_cons, errTermsErr_cons] at h ⊢
        have : x.2.1.toC * character (certKeyFun n x.1) θ + errTermsEval n xs θ +
            (y.2.1.toC * character (certKeyFun n y.1) θ + errTermsEval n ys θ) -
            (x.2.1.toC * character (certKeyFun n x.1) θ +
              errTermsEval n (mergeErrTerms xs (y :: ys)) θ) =
            errTermsEval n xs θ + (y.2.1.toC * character (certKeyFun n y.1) θ +
              errTermsEval n ys θ) - errTermsEval n (mergeErrTerms xs (y :: ys)) θ := by ring
        rw [this]
        linarith
      · simp only [errTermsEval_cons, errTermsErr_cons] at ih ⊢
        have : x.2.1.toC * character (certKeyFun n x.1) θ + errTermsEval n xs θ +
            (y.2.1.toC * character (certKeyFun n y.1) θ + errTermsEval n ys θ) -
            (y.2.1.toC * character (certKeyFun n y.1) θ +
              errTermsEval n (mergeErrInsert x xs (mergeErrTerms xs) ys) θ) =
            x.2.1.toC * character (certKeyFun n x.1) θ + errTermsEval n xs θ +
              errTermsEval n ys θ - errTermsEval n (mergeErrInsert x xs (mergeErrTerms xs) ys) θ :=
          by ring
        rw [this]
        linarith
      · rename_i hk
        have hxy := keyCmp_eq_eq hk
        have h := hrec ys
        have hp := mergeErrPair_spec n hxy θ
        simp only [errTermsEval_cons, errTermsErr_cons] at h ⊢
        set A := x.2.1.toC * character (certKeyFun n x.1) θ
        set B := y.2.1.toC * character (certKeyFun n y.1) θ
        set C := (mergeErrPair x y).2.1.toC * character (certKeyFun n (mergeErrPair x y).1) θ
        have : A + errTermsEval n xs θ + (B + errTermsEval n ys θ) -
            (C + errTermsEval n (mergeErrTerms xs ys) θ) = (A + B - C) +
              (errTermsEval n xs θ + errTermsEval n ys θ -
                errTermsEval n (mergeErrTerms xs ys) θ) := by ring
        rw [this]
        have := norm_add_le (A + B - C) (errTermsEval n xs θ + errTermsEval n ys θ -
          errTermsEval n (mergeErrTerms xs ys) θ)
        linarith

end Merge

/-! ### Direct products and truncation -/

section Direct

variable {α : Type} [CertArith α]

/-- The row `c_s χ_{k_s} · Σ_t c_t χ_{k_t}`: keys added, coefficients multiplied (rounded). -/
def rowItems (s : CertKey × CC α) (bs : List (CertKey × CC α)) : List (ErrTerm α) :=
  bs.map fun t => (packAddZ s.1 t.1, s.2.mulC t.2, s.2.mulErrC t.2)

/-- The direct product of two term lists: the rows merged one after another (equal keys are
added, so a product with a constant factor is a scalar multiplication of the other factor). -/
def directItems (as bs : List (CertKey × CC α)) : List (ErrTerm α) :=
  as.foldl (fun acc s => mergeErrTerms acc (rowItems s bs)) []

/-- Product terms kept at the cutoff: `|k|₁ ≤ cutoff`. -/
def truncKeep (cutoff : ℕ) (t : ErrTerm α) : Bool := Nat.ble (keyDeg t.1) cutoff

/-- A dropped term moves its coefficient size into its error. -/
def truncErr (cutoff : ℕ) (t : ErrTerm α) : ErrTerm α :=
  if truncKeep cutoff t then t else (t.1, t.2.1, upAdd t.2.2 t.2.1.normUp)

/-- The polynomial of the kept terms. -/
def truncPoly (cutoff : ℕ) (L : List (ErrTerm α)) : CertPoly α :=
  ⟨(L.filter (truncKeep cutoff)).map fun t => (t.1, t.2.1)⟩

variable [LawfulCertArith α]

theorem rowItems_spec (n : ℕ) (s : CertKey × CC α) (bs : List (CertKey × CC α))
    (θ : Fin n → ℂ) :
    ‖s.2.toC * character (certKeyFun n s.1) θ * CertPoly.eval n ⟨bs⟩ θ -
        errTermsEval n (rowItems s bs) θ‖ ≤ errTermsErr n (rowItems s bs) θ := by
  induction bs with
  | nil => simp [rowItems, CertPoly.eval]
  | cons t bs ih =>
    have hC : CertPoly.eval n ⟨t :: bs⟩ θ =
        t.2.toC * character (certKeyFun n t.1) θ + CertPoly.eval n ⟨bs⟩ θ := by
      simp [CertPoly.eval]
    have hR : rowItems s (t :: bs) =
        (packAddZ s.1 t.1, s.2.mulC t.2, s.2.mulErrC t.2) :: rowItems s bs := rfl
    rw [hC, hR, errTermsEval_cons, errTermsErr_cons]
    simp only
    rw [certKeyFun_packAddZ, ← character_mul]
    set χs := character (certKeyFun n s.1) θ
    set χt := character (certKeyFun n t.1) θ
    have e := CC.norm_mul_sub_mulC s.2 t.2
    have : s.2.toC * χs * (t.2.toC * χt + CertPoly.eval n ⟨bs⟩ θ) -
        ((s.2.mulC t.2).toC * (χs * χt) + errTermsEval n (rowItems s bs) θ) =
        (s.2.toC * t.2.toC - (s.2.mulC t.2).toC) * (χs * χt) +
          (s.2.toC * χs * CertPoly.eval n ⟨bs⟩ θ - errTermsEval n (rowItems s bs) θ) := by
      ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have := mul_le_mul_of_nonneg_right e (norm_nonneg (χs * χt))
    linarith

/-- **Direct product contract.** -/
theorem directItems_spec (n : ℕ) (as bs : List (CertKey × CC α)) (θ : Fin n → ℂ) :
    ‖CertPoly.eval n ⟨as⟩ θ * CertPoly.eval n ⟨bs⟩ θ - errTermsEval n (directItems as bs) θ‖ ≤
      errTermsErr n (directItems as bs) θ := by
  have key : ∀ (as : List (CertKey × CC α)) (acc : List (ErrTerm α)) (S : ℂ),
      ‖S - errTermsEval n acc θ‖ ≤ errTermsErr n acc θ →
      ‖S + CertPoly.eval n ⟨as⟩ θ * CertPoly.eval n ⟨bs⟩ θ -
          errTermsEval n (as.foldl (fun acc s => mergeErrTerms acc (rowItems s bs)) acc) θ‖ ≤
        errTermsErr n (as.foldl (fun acc s => mergeErrTerms acc (rowItems s bs)) acc) θ := by
    intro as
    induction as with
    | nil => intro acc S h; simpa [CertPoly.eval] using h
    | cons s as ih =>
      intro acc S h
      rw [List.foldl_cons]
      have hS : S + CertPoly.eval n ⟨s :: as⟩ θ * CertPoly.eval n ⟨bs⟩ θ =
          (S + s.2.toC * character (certKeyFun n s.1) θ * CertPoly.eval n ⟨bs⟩ θ) +
            CertPoly.eval n ⟨as⟩ θ * CertPoly.eval n ⟨bs⟩ θ := by
        simp only [CertPoly.eval, List.map_cons, List.sum_cons]
        ring
      rw [hS]
      refine ih _ _ ?_
      have hm := mergeErrTerms_spec n θ acc (rowItems s bs)
      have hr := rowItems_spec n s bs θ
      have : S + s.2.toC * character (certKeyFun n s.1) θ * CertPoly.eval n ⟨bs⟩ θ -
          errTermsEval n (mergeErrTerms acc (rowItems s bs)) θ =
          (S - errTermsEval n acc θ) + (s.2.toC * character (certKeyFun n s.1) θ *
            CertPoly.eval n ⟨bs⟩ θ - errTermsEval n (rowItems s bs) θ) +
          (errTermsEval n acc θ + errTermsEval n (rowItems s bs) θ -
            errTermsEval n (mergeErrTerms acc (rowItems s bs)) θ) := by ring
      rw [this]
      have n1 := norm_add_le ((S - errTermsEval n acc θ) + (s.2.toC *
        character (certKeyFun n s.1) θ * CertPoly.eval n ⟨bs⟩ θ -
          errTermsEval n (rowItems s bs) θ))
        (errTermsEval n acc θ + errTermsEval n (rowItems s bs) θ -
          errTermsEval n (mergeErrTerms acc (rowItems s bs)) θ)
      have n2 := norm_add_le (S - errTermsEval n acc θ) (s.2.toC *
        character (certKeyFun n s.1) θ * CertPoly.eval n ⟨bs⟩ θ -
          errTermsEval n (rowItems s bs) θ)
      linarith
  simpa [directItems] using key as [] 0 (by simp)

/-- **Truncation contract**: dropping the terms beyond the cutoff costs their weighted size. -/
theorem truncPoly_spec (n : ℕ) (cutoff : ℕ) (θ : Fin n → ℂ) : ∀ L : List (ErrTerm α),
    ‖errTermsEval n L θ - (truncPoly cutoff L).eval n θ‖ + errTermsErr n L θ ≤
      errTermsErr n (L.map (truncErr cutoff)) θ
  | [] => by simp [truncPoly, CertPoly.eval]
  | t :: L => by
    have ih := truncPoly_spec n cutoff θ L
    have hev : ∀ M : List (ErrTerm α), (truncPoly cutoff M).eval n θ =
        errTermsEval n (M.filter (truncKeep cutoff)) θ := fun M => by
      simp [truncPoly, CertPoly.eval, errTermsEval, Function.comp_def]
    rw [hev] at ih ⊢
    by_cases hk : truncKeep cutoff t = true
    · rw [List.filter_cons_of_pos hk, List.map_cons]
      simp only [truncErr, hk, ↓reduceIte]
      simp only [errTermsEval_cons, errTermsErr_cons]
      have : t.2.1.toC * character (certKeyFun n t.1) θ + errTermsEval n L θ -
          (t.2.1.toC * character (certKeyFun n t.1) θ +
            errTermsEval n (L.filter (truncKeep cutoff)) θ) =
          errTermsEval n L θ - errTermsEval n (L.filter (truncKeep cutoff)) θ := by ring
      rw [this]
      linarith
    · rw [List.filter_cons_of_neg hk, List.map_cons]
      simp only [truncErr, hk, Bool.false_eq_true, ↓reduceIte]
      simp only [errTermsEval_cons, errTermsErr_cons]
      have : t.2.1.toC * character (certKeyFun n t.1) θ + errTermsEval n L θ -
          errTermsEval n (L.filter (truncKeep cutoff)) θ =
          t.2.1.toC * character (certKeyFun n t.1) θ +
            (errTermsEval n L θ - errTermsEval n (L.filter (truncKeep cutoff)) θ) := by ring
      rw [this]
      have h1 := norm_add_le (t.2.1.toC * character (certKeyFun n t.1) θ)
        (errTermsEval n L θ - errTermsEval n (L.filter (truncKeep cutoff)) θ)
      have hχ := norm_nonneg (character (certKeyFun n t.1) θ)
      have u := LawfulCertArith.upAdd_ge t.2.2 t.2.1.normUp
      have hc := CC.norm_le_normUp t.2.1
      rw [norm_mul] at h1
      have := mul_le_mul_of_nonneg_right
        (show ‖t.2.1.toC‖ + val t.2.2 ≤ val (upAdd t.2.2 t.2.1.normUp) by linarith) hχ
      nlinarith

end Direct

end KAM.Certificate
