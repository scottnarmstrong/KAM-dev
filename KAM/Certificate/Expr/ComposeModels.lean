/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Embedding
public import KAM.Certificate.Expr.Slp
public import KAM.Certificate.Model.Exp
public import KAM.Certificate.Model.Inv

/-!
# Slot models of the composition with an embedding

The building blocks of `Slp.compose` (SO design §1.7), each with its enclosure contract on the
open strip:

* `constModel`: a constant `(re + i im) (2π)^deg` with outward conversion (`ofRatUp`), the
  conversion error in the radius; its key is zero, so a `mul` with a constant operand takes
  `CertModel.mul`'s scalar route (SO-ADVCOUNT lever 1);
* `realCompModel`: an action component `(2π)^{dA_j} A_j`, exact, in the canonical (ascending)
  key order of `CertRealPoly.toSortedPoly` (the zero key has length `n`);
* `charPhaseModel`: the degree-zero model of the character phase `2πi k·(2π)^{dU} U`, the sum
  over the coordinates with `k_j ≠ 0` of the exact multipliers `i k_j` on `U_j` (the backend
  products in the radius) at degree `dU_j + 1`, re-expressed at degree `0`;
* `charExpFun`: the function `exp(2πi k·(2π)^{dU} U)` that a character witness encloses, its
  invariance under the key normalization `CertEmbedding.normKey` (coordinates with syntactically
  zero `U_j` zeroed) and under `-k` with `CertPoly.conjReflect`, term order reversed so that
  ascending keys stay ascending (`CertPoly.reflectSorted`, `charExpFun_reflectSorted`);
* `shiftModel`: multiplication by a character `χ_k` (exact index shift, radius times
  `w^{|k|₁}`);
* `ModelConfig.forWitness`: the advice of witness number `i` at site `s` (keys `s :: i :: rest`
  re-keyed to `s :: rest`), so that the witnesses' internal product keys do not collide (SO-EXPW
  handoff, product keys). The advice is untrusted, so the contracts hold for every book.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM CertArith

section Defs

variable {α : Type} [CertArith α]

/-- The zero model (it encloses `0` exactly). -/
def zeroModel : CertModel α := ⟨0, ⟨[]⟩, ofInt 0⟩

/-- An upper bound of the outward conversion error `ofRatUp q - q`. -/
def ratErrUp (q : ℚ) : α :=
  upAdd (CertArith.add (ofRatUp q) (neg (ofRatDown q))) (addErr (ofRatUp q) (neg (ofRatDown q)))

/-- A key of length `n` with the same index as `k`. -/
def padKey (n : ℕ) (k : CertKey) : CertKey := (List.range n).map fun j => k.getD j 0

/-- The model of the constant `(re + i im) (2π)^deg`: one term at the zero key of length `n`. -/
def constModel (n : ℕ) (re im : ℚ) (deg : ℤ) : CertModel α :=
  ⟨deg, ⟨[(padKey n [], ⟨ofRatUp re, ofRatUp im⟩)]⟩, upAdd (ratErrUp re) (ratErrUp im)⟩

/-- The full polynomial of real data in canonical order: the conjugate terms at `-k` (reversed),
the constant at the zero key of length `n`, the half terms. If the half keys have length `n`, are
lexicographically positive and ascending, the keys are ascending, so the model algebra's sorted
merges combine equal keys (any order is sound). -/
def CertRealPoly.toSortedPoly (n : ℕ) (P : CertRealPoly α) : CertPoly α :=
  ⟨(P.half.reverse.map fun t => (t.1.map Neg.neg, t.2.conj)) ++
    (padKey n [], ⟨P.zero, ofInt 0⟩) :: P.half⟩

/-- The exact model of an optional real component at degree `d` (`0` if missing). -/
def realCompModel (n : ℕ) (d : ℤ) : Option (CertRealPoly α) → CertModel α
  | none => zeroModel
  | some P => ⟨d, P.toSortedPoly n, ofInt 0⟩

/-- The terms of `i m P` (integer `m`) with their rounding errors. -/
def imulItems (m : ℤ) (P : CertPoly α) : List (ErrTerm α) :=
  P.terms.map fun t => (t.1, ⟨neg (mul t.2.im (ofInt m)), mul t.2.re (ofInt m)⟩,
    upAdd (mulErr t.2.im (ofInt m)) (mulErr t.2.re (ofInt m)))

/-- The model of `i m 2π (2π)^d U` for an optional real component `U` (degree `d + 1`). -/
def phaseTermModel (n : ℕ) (W : CertWeight) (d m : ℤ) : Option (CertRealPoly α) → CertModel α
  | none => zeroModel
  | some P =>
    ⟨d + 1, itemsPoly (imulItems m (P.toSortedPoly n)),
      errRadius W (imulItems m (P.toSortedPoly n))⟩

/-- The degree-zero model of the character phase `i · 2π k·(2π)^{dU} U` of the key `k`: the
coordinates `j < n` with `k_j ≠ 0`, each re-expressed at degree `0`. -/
def charPhaseModel (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (pe : PiEnclosure α)
    (k : CertKey) : CertModel α :=
  (List.range n).foldl (fun acc j =>
    if k.getD j 0 = 0 then acc else
      CertModel.add W acc (CertModel.toDeg W pe 0
        (phaseTermModel n W (K.angleDeg.getD j 0) (k.getD j 0) K.angle[j]?))) zeroModel

/-- Syntactically zero real data: no half terms and a zero constant. -/
def CertRealPoly.isZeroData (P : CertRealPoly α) : Bool := P.half.isEmpty && beq P.zero (ofInt 0)

/-- The angle component `U_j` is missing or syntactically zero. -/
def CertEmbedding.angleIsZero (K : CertEmbedding α) (j : ℕ) : Bool :=
  match K.angle[j]? with
  | none => true
  | some P => P.isZeroData

/-- The normalized character index: length `n`, coordinates with syntactically zero `U_j`
zeroed. Character witnesses are keyed by it. -/
def CertEmbedding.normKey (n : ℕ) (K : CertEmbedding α) (k : CertKey) : CertKey :=
  (List.range n).map fun j => if K.angleIsZero j then 0 else k.getD j 0

/-- The conjugate reflection with the term order reversed (ascending keys stay ascending). -/
def CertPoly.reflectSorted (P : CertPoly α) : CertPoly α := ⟨P.conjReflect.terms.reverse⟩

/-- Multiplication of `⟨0, P, r⟩` by the character `χ_k` (`k` of length `n`). -/
def shiftModel (W : CertWeight) (k : CertKey) (P : CertPoly α) (r : α) : CertModel α :=
  ⟨0, P.shift k, weightTermUp W k r⟩

/-- The first entry with key `k`, and its position. -/
def findKeyIdx {β : Type} (k : CertKey) : List (CertKey × β) → Option (ℕ × β)
  | [] => none
  | e :: L => if e.1 = k then some (0, e.2) else (findKeyIdx k L).map fun r => (r.1 + 1, r.2)

/-- The advice entries `s :: i :: rest`, re-keyed to `s :: rest`. -/
def subAdvice (s i : ℕ) (book : AdviceBook) : AdviceBook :=
  book.filterMap fun e =>
    match e.1 with
    | a :: b :: rest => if a = s ∧ b = i then some (a :: rest, e.2) else none
    | _ => none

/-- The configuration of witness number `i` at product site `s`: its own advice book. -/
def ModelConfig.forWitness (cfg : ModelConfig α) (s i : ℕ) : ModelConfig α :=
  { cfg with advice := subAdvice s i cfg.advice }

end Defs

/-- The function `exp(i · 2π k·(2π)^{dU} U(θ))` enclosed by the character witness of `k`. -/
def charExpFun {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α) (k : CertKey)
    (θ : Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * modePhase n k fun i => K.angleAt n i.val θ)

/-! ### Contracts -/

section Contracts

variable {α : Type} [CertArith α]

theorem character_certKeyFun_nil (n : ℕ) (θ : Fin n → ℂ) : character (certKeyFun n []) θ = 1 := by
  simp [certKeyFun_nil, character]

theorem findKeyIdx_mem {β : Type} {k : CertKey} :
    ∀ {L : List (CertKey × β)} {c : ℕ} {b : β}, findKeyIdx k L = some (c, b) → (k, b) ∈ L
  | [], _, _, h => by simp [findKeyIdx] at h
  | e :: L, c, b, h => by
    unfold findKeyIdx at h
    split_ifs at h with he
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rw [← he]
      exact List.mem_cons_self
    · obtain ⟨r, hr, hrc⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hrc
      obtain ⟨-, rfl⟩ := hrc
      exact List.mem_cons_of_mem _ (findKeyIdx_mem (c := r.1) hr)

theorem modePhase_add (n : ℕ) (k : CertKey) (θ s : Fin n → ℂ) :
    modePhase n k (θ + s) = modePhase n k θ + modePhase n k s := by
  simp only [modePhase, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem exp_I_modePhase (n : ℕ) (k : CertKey) (θ : Fin n → ℂ) :
    Complex.exp (Complex.I * modePhase n k θ) = character (certKeyFun n k) θ := by
  simp only [modePhase, character]
  congr 1
  ring

theorem certKeyFun_padKey (n : ℕ) (k : CertKey) : certKeyFun n (padKey n k) = certKeyFun n k := by
  funext i
  simp [certKeyFun, padKey, List.getD_eq_getElem?_getD, i.isLt]

theorem padKey_length (n : ℕ) (k : CertKey) : (padKey n k).length = n := by simp [padKey]

/-- The value of a character slot at `K θ`: `χ_k(θ) · charExpFun k θ`. -/
theorem exp_I_modePhase_eval (n : ℕ) (K : CertEmbedding α) (k : CertKey) (θ : Fin n → ℂ) :
    Complex.exp (Complex.I * modePhase n k (K.eval n θ).1) =
      character (certKeyFun n k) θ * charExpFun n K k θ := by
  have : (K.eval n θ).1 = θ + fun i => K.angleAt n i.val θ := funext fun i => rfl
  rw [this, modePhase_add, mul_add, Complex.exp_add, exp_I_modePhase, charExpFun]

theorem CertPoly.eval_reflectSorted (n : ℕ) (P : CertPoly α) (θ : Fin n → ℂ) :
    P.reflectSorted.eval n θ = P.conjReflect.eval n θ := by
  simp only [CertPoly.eval, CertPoly.reflectSorted, List.map_reverse, List.sum_reverse]

theorem toDeg_deg (W : CertWeight) (pe : PiEnclosure α) (d : ℤ) (a : CertModel α) :
    (CertModel.toDeg W pe d a).deg = d := by
  unfold CertModel.toDeg
  split_ifs with h
  · exact h
  · rfl

theorem conj_mem_complexStrip {n : ℕ} {ρ : ℝ} {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ) :
    (fun i => (starRingEnd ℂ) (θ i)) ∈ complexStrip n ρ := fun i => by
  simpa [Complex.conj_im, abs_neg] using hθ i

/-- The `-k` witness, conjugate-reflected, serves `k`. -/
theorem charExpFun_neg_conj (n : ℕ) (K : CertEmbedding α) (k : CertKey) (θ : Fin n → ℂ) :
    charExpFun n K k θ =
      (starRingEnd ℂ) (charExpFun n K (k.map Neg.neg) fun i => (starRingEnd ℂ) (θ i)) := by
  simp only [charExpFun, ← Complex.exp_conj]
  congr 1
  simp only [modePhase, CertEmbedding.angleAt_conj, certKeyFun_map_neg, map_mul, map_sum,
    Complex.conj_I, Complex.conj_ofReal, map_ofNat, Pi.neg_apply, Int.cast_neg, map_neg,
    map_intCast, neg_mul, Finset.sum_neg_distrib, Complex.conj_conj]
  ring

variable [LawfulCertArith α]

theorem zeroModel_encloses (n : ℕ) (ρ : ℝ) :
    (zeroModel : CertModel α).Encloses n ρ fun _ => 0 := by
  intro θ _
  simp [zeroModel, CertPoly.eval, LawfulCertArith.val_ofInt]

theorem ratErrUp_ge (q : ℚ) : |val (ofRatUp q : α) - q| ≤ val (ratErrUp q : α) := by
  have hu := LawfulCertArith.ofRatUp_ge (α := α) q
  have hd := LawfulCertArith.ofRatDown_le (α := α) q
  have ha := LawfulCertArith.add_err (ofRatUp q : α) (neg (ofRatDown q))
  have hs := LawfulCertArith.upAdd_ge (CertArith.add (ofRatUp q : α) (neg (ofRatDown q)))
    (addErr (ofRatUp q) (neg (ofRatDown q)))
  rw [LawfulCertArith.val_neg] at ha
  rw [abs_of_nonneg (by linarith)]
  unfold ratErrUp
  linarith [(abs_le.mp ha).1]

theorem constModel_encloses (n : ℕ) (ρ : ℝ) (re im : ℚ) (deg : ℤ) :
    (constModel n re im deg : CertModel α).Encloses n ρ fun _ => slpConstVal re im deg := by
  intro θ _
  have hr := ratErrUp_ge (α := α) re
  have hi := ratErrUp_ge (α := α) im
  have hs := LawfulCertArith.upAdd_ge (ratErrUp re : α) (ratErrUp im)
  simp only [constModel, CertPoly.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, certKeyFun_padKey, character_certKeyFun_nil, mul_one, slpConstVal]
  rw [show ((re : ℂ) + (im : ℂ) * Complex.I) * (2 * (Real.pi : ℂ)) ^ deg -
      (2 * (Real.pi : ℂ)) ^ deg * (⟨ofRatUp re, ofRatUp im⟩ : CC α).toC =
      (2 * (Real.pi : ℂ)) ^ deg * (((re : ℂ) + (im : ℂ) * Complex.I) -
        (⟨ofRatUp re, ofRatUp im⟩ : CC α).toC) by ring, norm_mul, norm_two_pi_zpow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_le_of_re_im (A := val (ratErrUp re : α)) (B := val (ratErrUp im : α)) ?_ ?_).trans
    hs
  · simpa [CC.toC, abs_sub_comm] using hr
  · simpa [CC.toC, abs_sub_comm] using hi

/-- The canonical order denotes the real data (needs the laws: backend zero and conjugation). -/
theorem CertRealPoly.eval_toSortedPoly (n : ℕ) (P : CertRealPoly α) (θ : Fin n → ℂ) :
    (P.toSortedPoly n).eval n θ = P.eval n θ := by
  have h0 : (⟨P.zero, ofInt 0⟩ : CC α).toC = (val P.zero : ℂ) := by
    simp [CC.toC, LawfulCertArith.val_ofInt, Complex.ext_iff]
  simp only [CertPoly.eval, CertRealPoly.toSortedPoly, CertRealPoly.eval, List.map_append,
    List.sum_append, List.map_cons, List.sum_cons, List.map_reverse, List.sum_reverse,
    List.map_map, Function.comp_def, CC.toC_conj, certKeyFun_map_neg, h0,
    certKeyFun_padKey, character_certKeyFun_nil, mul_one, List.sum_map_add]
  ring

theorem realCompModel_encloses (n : ℕ) (ρ : ℝ) (d : ℤ) (P : Option (CertRealPoly α)) :
    (realCompModel n d P).Encloses n ρ (realComp n d P) := by
  cases P with
  | none =>
    intro θ hθ
    simpa [realComp, realCompModel] using zeroModel_encloses (α := α) n ρ θ hθ
  | some P =>
    intro θ _
    simp [realCompModel, realComp, CertRealPoly.eval_toSortedPoly, LawfulCertArith.val_ofInt]

theorem imulItems_spec (n : ℕ) (m : ℤ) (θ : Fin n → ℂ) : ∀ L : List (CertKey × CC α),
    ‖Complex.I * (m : ℂ) * (⟨L⟩ : CertPoly α).eval n θ - errTermsEval n (imulItems m ⟨L⟩) θ‖ ≤
      errTermsErr n (imulItems m ⟨L⟩) θ
  | [] => by simp [CertPoly.eval, imulItems]
  | t :: L => by
    have ih := imulItems_spec n m θ L
    have e := norm_deriv_coeff_sub t.2 m
    simp only [imulItems, CertPoly.eval, List.map_cons, List.sum_cons, errTermsEval_cons,
      errTermsErr_cons] at ih ⊢
    set χ := character (certKeyFun n t.1) θ
    set c : CC α := ⟨neg (mul t.2.im (ofInt m)), mul t.2.re (ofInt m)⟩
    rw [show Complex.I * (m : ℂ) * (t.2.toC * χ +
        (L.map fun t => t.2.toC * character (certKeyFun n t.1) θ).sum) -
        (c.toC * χ + errTermsEval n (L.map fun t => (t.1, (⟨neg (mul t.2.im (ofInt m)),
          mul t.2.re (ofInt m)⟩ : CC α), upAdd (mulErr t.2.im (ofInt m))
            (mulErr t.2.re (ofInt m)))) θ) =
        (Complex.I * (m : ℂ) * t.2.toC - c.toC) * χ + (Complex.I * (m : ℂ) *
          (L.map fun t => t.2.toC * character (certKeyFun n t.1) θ).sum -
          errTermsEval n (L.map fun t => (t.1, (⟨neg (mul t.2.im (ofInt m)),
            mul t.2.re (ofInt m)⟩ : CC α), upAdd (mulErr t.2.im (ofInt m))
              (mulErr t.2.re (ofInt m)))) θ) by ring]
    refine (norm_add_le _ _).trans (add_le_add ?_ ih)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right e (norm_nonneg _)

theorem phaseTermModel_encloses {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (d m : ℤ) (P : Option (CertRealPoly α)) :
    (phaseTermModel n W d m P).Encloses n W.rho
      (fun θ => Complex.I * (m : ℂ) * (2 * Real.pi) * realComp n d P θ) := by
  cases P with
  | none =>
    intro θ hθ
    simpa [realComp, phaseTermModel] using zeroModel_encloses (α := α) n W.rho θ hθ
  | some P =>
    intro θ hθ
    have hS := imulItems_spec n m θ (P.toSortedPoly n).terms
    have hR := errTermsErr_le_errRadius hW (imulItems m (P.toSortedPoly n)) hθ
    have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
    simp only [phaseTermModel, itemsPoly_eval, realComp, Option.map_some, Option.getD_some]
    rw [zpow_add_one₀ h2pi, zpow_add_one₀ (by positivity : (2 * Real.pi) ≠ 0),
      ← CertRealPoly.eval_toSortedPoly n P θ]
    rw [show Complex.I * (m : ℂ) * (2 * Real.pi) * ((2 * (Real.pi : ℂ)) ^ d *
        (P.toSortedPoly n).eval n θ) - (2 * (Real.pi : ℂ)) ^ d * (2 * Real.pi) *
          errTermsEval n (imulItems m (P.toSortedPoly n)) θ =
        ((2 * (Real.pi : ℂ)) ^ d * (2 * Real.pi)) * (Complex.I * (m : ℂ) *
          (⟨(P.toSortedPoly n).terms⟩ : CertPoly α).eval n θ -
            errTermsEval n (imulItems m (P.toSortedPoly n)) θ)
        by ring, norm_mul, norm_mul, norm_two_pi_zpow]
    have h2 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by simp [abs_of_pos Real.pi_pos]
    rw [h2]
    exact mul_le_mul_of_nonneg_left (hS.trans hR) (by positivity)

/-- The character phase over the first `m` coordinates. -/
theorem charPhaseModel_aux {n : ℕ} (K : CertEmbedding α) {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true)
    (k : CertKey) : ∀ m : ℕ,
    ((List.range m).foldl (fun acc j =>
      if k.getD j 0 = 0 then acc else
        CertModel.add W acc (CertModel.toDeg W pe 0
          (phaseTermModel n W (K.angleDeg.getD j 0) (k.getD j 0) K.angle[j]?))) zeroModel).deg = 0 ∧
    ((List.range m).foldl (fun acc j =>
      if k.getD j 0 = 0 then acc else
        CertModel.add W acc (CertModel.toDeg W pe 0
          (phaseTermModel n W (K.angleDeg.getD j 0) (k.getD j 0) K.angle[j]?))) zeroModel).Encloses
      n W.rho (fun θ => ∑ j ∈ Finset.range m,
        Complex.I * (k.getD j 0 : ℂ) * (2 * Real.pi) * K.angleAt n j θ)
  | 0 => ⟨rfl, by simpa using zeroModel_encloses (α := α) n W.rho⟩
  | m + 1 => by
    obtain ⟨ih0, ih⟩ := charPhaseModel_aux K hW hpe k m
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Finset.sum_range_succ]
    split_ifs with hk
    · refine ⟨ih0, ?_⟩
      simp only [hk, Int.cast_zero, mul_zero, zero_mul, add_zero]
      exact ih
    · refine ⟨ih0, ?_⟩
      have ht := (phaseTermModel_encloses (α := α) (n := n) hW (K.angleDeg.getD m 0) (k.getD m 0)
        K.angle[m]?).toDeg hW hpe 0
      exact CertModel.Encloses.add hW ih ht (by rw [ih0, toDeg_deg])

theorem charPhaseModel_encloses {n : ℕ} (K : CertEmbedding α) {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true)
    (k : CertKey) : (charPhaseModel n K W pe k).deg = 0 ∧
      (charPhaseModel n K W pe k).Encloses n W.rho
        (fun θ => Complex.I * modePhase n k fun i => K.angleAt n i.val θ) := by
  obtain ⟨h0, h⟩ := charPhaseModel_aux K hW hpe k n
  refine ⟨h0, ?_⟩
  have e : ∀ θ : Fin n → ℂ, (Complex.I * modePhase n k fun i => K.angleAt n i.val θ) =
      ∑ j ∈ Finset.range n, Complex.I * (k.getD j 0 : ℂ) * (2 * Real.pi) * K.angleAt n j θ := by
    intro θ
    rw [Finset.sum_range (fun j => Complex.I * (k.getD j 0 : ℂ) * (2 * Real.pi) *
      K.angleAt n j θ), modePhase, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [certKeyFun]
    ring
  simp only [e]
  exact h

theorem CertRealPoly.eval_of_isZeroData (n : ℕ) {P : CertRealPoly α} (h : P.isZeroData = true)
    (θ : Fin n → ℂ) : P.eval n θ = 0 := by
  simp only [CertRealPoly.isZeroData, Bool.and_eq_true, List.isEmpty_iff] at h
  have hz := LawfulCertArith.beq_sound _ _ h.2
  rw [LawfulCertArith.val_ofInt] at hz
  simp [CertRealPoly.eval, h.1, hz]

theorem CertEmbedding.angleAt_of_angleIsZero (n : ℕ) {K : CertEmbedding α} {j : ℕ}
    (h : K.angleIsZero j = true) (θ : Fin n → ℂ) : K.angleAt n j θ = 0 := by
  unfold CertEmbedding.angleIsZero at h
  unfold CertEmbedding.angleAt realComp
  cases hj : K.angle[j]? with
  | none => simp
  | some P =>
    rw [hj] at h
    simp [CertRealPoly.eval_of_isZeroData n h θ]

/-- Normalization does not change the character exponential. -/
theorem charExpFun_normKey (n : ℕ) (K : CertEmbedding α) (k : CertKey) :
    charExpFun n K (K.normKey n k) = charExpFun n K k := by
  funext θ
  unfold charExpFun
  congr 2
  unfold modePhase
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hk : certKeyFun n (K.normKey n k) i =
      if K.angleIsZero i.val then 0 else certKeyFun n k i := by
    simp [certKeyFun, CertEmbedding.normKey, List.getD_eq_getElem?_getD, i.isLt]
  rw [hk]
  split_ifs with h
  · simp only [CertEmbedding.angleAt_of_angleIsZero n h]; simp
  · rfl

/-- A conjugate-reflected witness of `-k` encloses the character exponential of `k`. -/
theorem charExpFun_reflectSorted {n : ℕ} {ρ : ℝ} (K : CertEmbedding α) (k : CertKey)
    {E : CertPoly α} {r : α}
    (h : (⟨0, E, r⟩ : CertModel α).Encloses n ρ (charExpFun n K (k.map Neg.neg))) :
    (⟨0, E.reflectSorted, r⟩ : CertModel α).Encloses n ρ (charExpFun n K k) := by
  intro θ hθ
  have h1 := h _ (conj_mem_complexStrip hθ)
  simp only [zpow_zero, one_mul, CertPoly.eval_reflectSorted] at h1 ⊢
  rw [charExpFun_neg_conj, CertPoly.eval_conjReflect, ← map_sub, Complex.norm_conj]
  exact h1

/-- Multiplication by `χ_k` (key of length `n`). -/
theorem shiftModel_encloses {n : ℕ} {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    {k : CertKey} (hk : k.length = n) {P : CertPoly α} {r : α} {G : (Fin n → ℂ) → ℂ}
    (h : (⟨0, P, r⟩ : CertModel α).Encloses n W.rho G) :
    (shiftModel W k P r).Encloses n W.rho (fun θ => character (certKeyFun n k) θ * G θ) := by
  intro θ hθ
  have h1 := h θ hθ
  have h2 := weightTermUp_ge hW k r hθ
  simp only [zpow_zero, one_mul] at h1 ⊢
  simp only [shiftModel, zpow_zero, one_mul, CertPoly.eval_shift n k P hk θ, ← mul_sub,
    norm_mul]
  calc ‖character (certKeyFun n k) θ‖ * ‖G θ - P.eval n θ‖
      ≤ ‖character (certKeyFun n k) θ‖ * val r :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ _ := by rw [mul_comm]; exact h2

end Contracts

end KAM.Certificate
