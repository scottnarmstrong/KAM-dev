/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Model.Ops

/-!
# Scalar tools of the a-posteriori witnesses

* `CertBall.listSum`: a balanced sum of complex balls (64 rounds of pairwise `CertBall.plus`,
  then a fold of what remains), so the kernel never walks a long accumulator chain;
  `CertPoly.coeffSumBall P` encloses `P(0) = Σ_k c_k` (`CertPoly.mem_coeffSumBall`).
* `CC.negC`, `CertPoly.negP`: exact negation; `CertModel.mul_deg`.
* `expm1Up s N x`: a backend upper bound of `exp x - 1` for `x ≥ 0`, by `s` halvings, the Taylor
  bound of order `N` (`Real.exp_bound'`) and `s` steps `z ↦ z (2 + z)` (that is
  `(1 + z)² - 1`), all rounded upward; `none` if the halved argument exceeds `1` or `N = 0`.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM CertArith

/-! ### Balanced ball sums -/

section BallSum

variable {α : Type} [CertArith α]

/-- One round of pairwise ball sums: `[a, b, c, d, e] ↦ [a + b, c + d, e]`. -/
def CertBall.sumPairs : List (CertBall α) → List (CertBall α)
  | a :: b :: rest => CertBall.plus a b :: CertBall.sumPairs rest
  | l => l

/-- `r` rounds of `CertBall.sumPairs`. -/
def CertBall.sumRounds : ℕ → List (CertBall α) → List (CertBall α)
  | 0, l => l
  | r + 1, l => CertBall.sumRounds r (CertBall.sumPairs l)

/-- A right fold of ball sums (the ball `{0}` for the empty list). -/
def CertBall.foldSum : List (CertBall α) → CertBall α
  | [] => ⟨⟨ofInt 0, ofInt 0⟩, ofInt 0⟩
  | [b] => b
  | b :: c :: l => CertBall.plus b (CertBall.foldSum (c :: l))

/-- The balanced sum of a list of balls (64 pairwise rounds, then a fold). -/
def CertBall.listSum (L : List (CertBall α)) : CertBall α :=
  CertBall.foldSum (CertBall.sumRounds 64 L)

/-- A ball enclosing `P(0) = Σ_k c_k` (exact coefficient balls, balanced sum). -/
def CertPoly.coeffSumBall (P : CertPoly α) : CertBall α :=
  CertBall.listSum (P.terms.map fun t => ⟨t.2, ofInt 0⟩)

/-- The negation `-c` of a backend complex number (exact). -/
def CC.negC (c : CC α) : CC α := ⟨neg c.re, neg c.im⟩

/-- Exact negation of a polynomial. -/
def CertPoly.negP (P : CertPoly α) : CertPoly α :=
  ⟨P.terms.map fun t => (t.1, CC.negC t.2)⟩

/-- The sum of the centres of a list of balls. -/
def ballCentreSum (L : List (CertBall α)) : ℂ := (L.map fun b => b.c.toC).sum

/-- The sum of the radii of a list of balls. -/
def ballRadSum (L : List (CertBall α)) : ℝ := (L.map fun b => val b.r).sum

variable [LawfulCertArith α]

theorem CC.toC_negC (c : CC α) : (CC.negC c).toC = -c.toC := by
  apply Complex.ext <;> simp [CC.negC, CC.toC, LawfulCertArith.val_neg]

theorem CertBall.plus_spec (b₁ b₂ : CertBall α) :
    ‖b₁.c.toC + b₂.c.toC - (CertBall.plus b₁ b₂).c.toC‖ + val b₁.r + val b₂.r ≤
      val (CertBall.plus b₁ b₂).r := by
  have e1 := LawfulCertArith.add_err b₁.c.re b₂.c.re
  have e2 := LawfulCertArith.add_err b₁.c.im b₂.c.im
  have u1 := LawfulCertArith.upAdd_ge b₁.r b₂.r
  have u2 := LawfulCertArith.upAdd_ge (addErr b₁.c.re b₂.c.re) (addErr b₁.c.im b₂.c.im)
  have u3 := LawfulCertArith.upAdd_ge (upAdd b₁.r b₂.r)
    (upAdd (addErr b₁.c.re b₂.c.re) (addErr b₁.c.im b₂.c.im))
  have hc : ‖(b₁.c.toC + b₂.c.toC) - (CertBall.plus b₁ b₂).c.toC‖ ≤
      val (addErr b₁.c.re b₂.c.re) + val (addErr b₁.c.im b₂.c.im) := by
    apply norm_le_of_re_im
    · simp only [Complex.sub_re, Complex.add_re, CertBall.plus, CC.toC]
      rw [abs_sub_comm]; exact e1
    · simp only [Complex.sub_im, Complex.add_im, CertBall.plus, CC.toC]
      rw [abs_sub_comm]; exact e2
  have hr : val (CertBall.plus b₁ b₂).r = val (upAdd (upAdd b₁.r b₂.r)
      (upAdd (addErr b₁.c.re b₂.c.re) (addErr b₁.c.im b₂.c.im))) := rfl
  rw [hr]
  linarith

theorem CertBall.sumPairs_spec : ∀ L : List (CertBall α),
    ‖ballCentreSum L - ballCentreSum (CertBall.sumPairs L)‖ + ballRadSum L ≤
      ballRadSum (CertBall.sumPairs L)
  | [] => by simp [CertBall.sumPairs, ballCentreSum, ballRadSum]
  | [b] => by simp [CertBall.sumPairs, ballCentreSum, ballRadSum]
  | a :: b :: rest => by
    have ih := CertBall.sumPairs_spec rest
    have hp := CertBall.plus_spec a b
    simp only [CertBall.sumPairs, ballCentreSum, ballRadSum, List.map_cons,
      List.sum_cons] at ih hp ⊢
    set X := (rest.map fun b => b.c.toC).sum
    set Y := ((CertBall.sumPairs rest).map fun b => b.c.toC).sum
    have : a.c.toC + (b.c.toC + X) - ((CertBall.plus a b).c.toC + Y) =
        (a.c.toC + b.c.toC - (CertBall.plus a b).c.toC) + (X - Y) := by ring
    rw [this]
    have := norm_add_le (a.c.toC + b.c.toC - (CertBall.plus a b).c.toC) (X - Y)
    linarith

theorem CertBall.sumRounds_spec : ∀ (r : ℕ) (L : List (CertBall α)),
    ‖ballCentreSum L - ballCentreSum (CertBall.sumRounds r L)‖ + ballRadSum L ≤
      ballRadSum (CertBall.sumRounds r L)
  | 0, L => by simp [CertBall.sumRounds]
  | r + 1, L => by
    have h1 := CertBall.sumPairs_spec L
    have h2 := CertBall.sumRounds_spec r (CertBall.sumPairs L)
    simp only [CertBall.sumRounds]
    have := norm_sub_le_norm_sub_add_norm_sub (ballCentreSum L)
      (ballCentreSum (CertBall.sumPairs L))
      (ballCentreSum (CertBall.sumRounds r (CertBall.sumPairs L)))
    linarith

theorem CertBall.foldSum_spec : ∀ L : List (CertBall α),
    ‖ballCentreSum L - (CertBall.foldSum L).c.toC‖ + ballRadSum L ≤ val (CertBall.foldSum L).r
  | [] => by
    simp [CertBall.foldSum, ballCentreSum, ballRadSum, CC.toC, LawfulCertArith.val_ofInt,
      Complex.ext_iff]
  | [b] => by simp [CertBall.foldSum, ballCentreSum, ballRadSum]
  | b :: c :: l => by
    have ih := CertBall.foldSum_spec (c :: l)
    have hp := CertBall.plus_spec b (CertBall.foldSum (c :: l))
    simp only [CertBall.foldSum]
    simp only [ballCentreSum, ballRadSum, List.map_cons, List.sum_cons] at ih ⊢
    set X := c.c.toC + (l.map fun b => b.c.toC).sum
    set F := CertBall.foldSum (c :: l)
    have : b.c.toC + X - (CertBall.plus b F).c.toC =
        (b.c.toC + F.c.toC - (CertBall.plus b F).c.toC) + (X - F.c.toC) := by ring
    rw [this]
    have := norm_add_le (b.c.toC + F.c.toC - (CertBall.plus b F).c.toC) (X - F.c.toC)
    linarith

/-- The balanced sum encloses every value within the summed radii of the summed centres. -/
theorem CertBall.mem_listSum {S : ℂ} {L : List (CertBall α)}
    (h : ‖S - ballCentreSum L‖ ≤ ballRadSum L) : CertBall.Mem S (CertBall.listSum L) := by
  have h1 := CertBall.sumRounds_spec 64 L
  have h2 := CertBall.foldSum_spec (CertBall.sumRounds 64 L)
  unfold CertBall.Mem CertBall.listSum
  have := norm_sub_le_norm_sub_add_norm_sub S (ballCentreSum L)
    (ballCentreSum (CertBall.sumRounds 64 L))
  have := norm_sub_le_norm_sub_add_norm_sub S (ballCentreSum (CertBall.sumRounds 64 L))
    (CertBall.foldSum (CertBall.sumRounds 64 L)).c.toC
  linarith

theorem character_zero_point {n : ℕ} (k : Fin n → ℤ) : character k 0 = 1 := by
  simp [character]

theorem CertPoly.mem_coeffSumBall (n : ℕ) (P : CertPoly α) :
    CertBall.Mem (P.eval n 0) (CertPoly.coeffSumBall P) := by
  apply CertBall.mem_listSum
  have hc : ballCentreSum (P.terms.map fun t => (⟨t.2, ofInt 0⟩ : CertBall α)) = P.eval n 0 := by
    simp [ballCentreSum, CertPoly.eval, character_zero_point, Function.comp_def]
  have hr : ballRadSum (P.terms.map fun t => (⟨t.2, ofInt 0⟩ : CertBall α)) = 0 := by
    simp [ballRadSum, LawfulCertArith.val_ofInt, Function.comp_def]
  rw [hc, hr]
  simp

theorem CertPoly.eval_negP (n : ℕ) (P : CertPoly α) (θ : Fin n → ℂ) :
    P.negP.eval n θ = -P.eval n θ := by
  simp only [CertPoly.negP, CertPoly.eval, List.map_map, Function.comp_def, CC.toC_negC,
    neg_mul]
  induction P.terms with
  | nil => simp
  | cons t L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

omit [LawfulCertArith α] in
theorem CertModel.mul_deg (W : CertWeight) (cfg : ModelConfig α) (key : ProductKey)
    (a b : CertModel α) : (CertModel.mul W cfg key a b).deg = a.deg + b.deg := by
  unfold CertModel.mul
  split <;> rfl

end BallSum

/-! ### Upper bounds of `exp x - 1` -/

section ExpUp

variable {α : Type} [CertArith α]

/-- The Taylor remainder factor `(M + 1) / (M! M)` of `Real.exp_bound'`. -/
def expRemFactor (M : ℕ) : ℚ := ((M : ℚ) + 1) / ((M.factorial : ℚ) * M)

/-- Upward Taylor sum of `exp y - 1`: fuel `k`, current index `m`, `p ≥ y^m`, partial sum `S`;
at fuel `0` the remainder term `y^{m+1} (m + 2)/((m + 1)! (m + 1))` is added. -/
def expSeriesUp (y : α) : ℕ → ℕ → α → α → α
  | 0, m, p, S => upAdd S (upMul (upMul p y) (ofRatUp (expRemFactor (m + 1))))
  | k + 1, m, p, S =>
    expSeriesUp y k (m + 1) (upMul p y)
      (upAdd S (upMul (upMul p y) (ofRatUp (1 / ((m + 1).factorial : ℚ)))))

/-- `s` upward steps `z ↦ z (2 + z) = (1 + z)² - 1`. -/
def expm1SqIter : ℕ → α → α
  | 0, z => z
  | s + 1, z => expm1SqIter s (upMul z (upAdd (ofInt 2) z))

/-- An upper bound of `exp x - 1` for `x ≥ 0` (`none` if `x / 2^s > 1` or `N = 0`). -/
def expm1Up (s N : ℕ) (x : α) : Option α :=
  let y := upMul x (ofRatUp (1 / 2 ^ s))
  if ble y (ofInt 1) && Nat.ble 1 N then
    some (expm1SqIter s (expSeriesUp y (N - 1) 0 (ofInt 1) (ofInt 0)))
  else none

variable [LawfulCertArith α]

theorem expSeriesUp_ge {y : α} {yr : ℝ} (hy0 : 0 ≤ yr) (hy : yr ≤ val y) :
    ∀ (k m : ℕ) (p S : α), yr ^ m ≤ val p →
      val S + (∑ i ∈ Finset.range k, yr ^ (m + i + 1) / ((m + i + 1).factorial : ℝ)) +
        yr ^ (m + k + 1) * (expRemFactor (m + k + 1) : ℝ) ≤ val (expSeriesUp y k m p S)
  | 0, m, p, S, hp => by
    have hp0 : 0 ≤ val p := (pow_nonneg hy0 m).trans hp
    have hpy := LawfulCertArith.upMul_ge p y hp0 (hy0.trans hy)
    have hR : (0 : ℝ) ≤ (expRemFactor (m + 1) : ℝ) := by
      unfold expRemFactor; push_cast; positivity
    have hR' := LawfulCertArith.ofRatUp_ge (α := α) (expRemFactor (m + 1))
    have h1 : yr ^ (m + 1) ≤ val (upMul p y) := by
      rw [pow_succ]
      exact (mul_le_mul hp hy hy0 hp0).trans hpy
    have h2 := LawfulCertArith.upMul_ge (upMul p y) (ofRatUp (expRemFactor (m + 1)))
      ((pow_nonneg hy0 _).trans h1) (hR.trans hR')
    have h3 := LawfulCertArith.upAdd_ge S
      (upMul (upMul p y) (ofRatUp (expRemFactor (m + 1))))
    have h4 : yr ^ (m + 1) * (expRemFactor (m + 1) : ℝ) ≤
        val (upMul p y) * val (ofRatUp (expRemFactor (m + 1)) : α) :=
      mul_le_mul h1 hR' hR ((pow_nonneg hy0 _).trans h1)
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, expSeriesUp]
    linarith
  | k + 1, m, p, S, hp => by
    have hp0 : 0 ≤ val p := (pow_nonneg hy0 m).trans hp
    have hpy := LawfulCertArith.upMul_ge p y hp0 (hy0.trans hy)
    have h1 : yr ^ (m + 1) ≤ val (upMul p y) := by
      rw [pow_succ]
      exact (mul_le_mul hp hy hy0 hp0).trans hpy
    have hF : (0 : ℝ) ≤ ((1 / ((m + 1).factorial : ℚ) : ℚ) : ℝ) := by push_cast; positivity
    have hF' := LawfulCertArith.ofRatUp_ge (α := α) (1 / ((m + 1).factorial : ℚ))
    have h2 := LawfulCertArith.upMul_ge (upMul p y) (ofRatUp (1 / ((m + 1).factorial : ℚ)))
      ((pow_nonneg hy0 _).trans h1) (hF.trans hF')
    have h3 := LawfulCertArith.upAdd_ge S
      (upMul (upMul p y) (ofRatUp (1 / ((m + 1).factorial : ℚ))))
    have h4 : yr ^ (m + 1) / ((m + 1).factorial : ℝ) ≤
        val (upMul p y) * val (ofRatUp (1 / ((m + 1).factorial : ℚ)) : α) := by
      rw [div_eq_mul_one_div]
      push_cast at hF hF' ⊢
      exact mul_le_mul h1 hF' hF ((pow_nonneg hy0 _).trans h1)
    have ih := expSeriesUp_ge hy0 hy k (m + 1) (upMul p y)
      (upAdd S (upMul (upMul p y) (ofRatUp (1 / ((m + 1).factorial : ℚ))))) h1
    simp only [expSeriesUp]
    rw [Finset.sum_range_succ']
    have e1 : ∀ i, m + (i + 1) + 1 = m + 1 + i + 1 := fun i => by omega
    simp only [e1, add_zero]
    linarith

theorem expm1SqIter_ge : ∀ (s : ℕ) (z : α) {w : ℝ}, 0 ≤ w → w ≤ val z →
    (1 + w) ^ 2 ^ s - 1 ≤ val (expm1SqIter s z)
  | 0, z, w, _, hw => by simpa [expm1SqIter] using hw
  | s + 1, z, w, hw0, hw => by
    have h2 := LawfulCertArith.upAdd_ge (ofInt 2) z
    rw [LawfulCertArith.val_ofInt] at h2
    have hm := LawfulCertArith.upMul_ge z (upAdd (ofInt 2) z) (hw0.trans hw)
      (by push_cast at h2; linarith)
    have hw' : w * (2 + w) ≤ val (upMul z (upAdd (ofInt 2) z)) :=
      (mul_le_mul hw (by push_cast at h2; linarith) (by positivity) (hw0.trans hw)).trans hm
    have ih := expm1SqIter_ge s (upMul z (upAdd (ofInt 2) z)) (by positivity) hw'
    simp only [expm1SqIter]
    have : (1 + w * (2 + w)) ^ 2 ^ s = (1 + w) ^ 2 ^ (s + 1) := by
      rw [show 1 + w * (2 + w) = (1 + w) ^ 2 by ring, ← pow_mul, ← pow_succ']
    linarith

/-- **Soundness of `expm1Up`.** -/
theorem expm1Up_sound {s N : ℕ} {x u : α} (hx : 0 ≤ val x) (h : expm1Up s N x = some u) :
    Real.exp (val x) - 1 ≤ val u := by
  unfold expm1Up at h
  simp only at h
  split_ifs at h with hc
  cases h
  simp only [Bool.and_eq_true, Nat.ble_eq] at hc
  obtain ⟨hc1, hN⟩ := hc
  set y : α := upMul x (ofRatUp (1 / 2 ^ s))
  have hq : (0 : ℝ) ≤ ((1 / 2 ^ s : ℚ) : ℝ) := by push_cast; positivity
  have hq' := LawfulCertArith.ofRatUp_ge (α := α) (1 / 2 ^ s)
  have hy := LawfulCertArith.upMul_ge x (ofRatUp (1 / 2 ^ s)) hx (hq.trans hq')
  set yr : ℝ := val x / 2 ^ s
  have hyr0 : 0 ≤ yr := by positivity
  have hyr : yr ≤ val y := by
    have : yr = val x * ((1 / 2 ^ s : ℚ) : ℝ) := by
      simp only [yr]; push_cast; ring
    rw [this]
    exact (mul_le_mul_of_nonneg_left hq' hx).trans hy
  have hy1 := LawfulCertArith.ble_sound _ _ hc1
  rw [LawfulCertArith.val_ofInt] at hy1
  push_cast at hy1
  have hser := expSeriesUp_ge hyr0 hyr (N - 1) 0 (ofInt 1) (ofInt 0)
    (by simp [LawfulCertArith.val_ofInt])
  rw [LawfulCertArith.val_ofInt, Int.cast_zero, zero_add] at hser
  have hb := Real.exp_bound' hyr0 (hyr.trans hy1) hN
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel, zero_add] at hser
  rw [Finset.sum_range_succ'] at hb
  have hrem : yr ^ (M + 1) * ((M + 1 : ℕ) + 1) / (((M + 1).factorial : ℕ) * (M + 1 : ℕ) : ℝ) =
      yr ^ (M + 1) * (expRemFactor (M + 1) : ℝ) := by
    unfold expRemFactor; push_cast; ring
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hb
  push_cast at hb hrem
  have hw : Real.exp yr - 1 ≤ val (expSeriesUp y M 0 (ofInt 1) (ofInt 0)) := by
    linarith
  have hw0 : 0 ≤ Real.exp yr - 1 := by linarith [Real.add_one_le_exp yr]
  have hsq := expm1SqIter_ge s _ hw0 hw
  have : Real.exp (val x) = (1 + (Real.exp yr - 1)) ^ 2 ^ s := by
    rw [add_sub_cancel, ← Real.exp_nat_mul]
    congr 1
    simp only [yr]; push_cast; field_simp
  rw [this]
  exact hsq

end ExpUp

end KAM.Certificate
