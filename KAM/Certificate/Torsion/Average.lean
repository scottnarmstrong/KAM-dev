/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Torsion.Frame

/-!
# The averaged bordered torsion check

`torsionAvgCheck n T S σTμ` certifies the inverse of the average of the `(n+1) × (n+1)` bordered
torsion from its entrywise models `T` and a constant witness `S`:

* it FIRST checks the exact shapes `HasShape (n + 1) T`, `HasShape (n + 1) S` (list lengths) and
  that every entry of `T` is a degree-`0` model (it has no `π` enclosure to change degrees: a
  model of another degree fails closed);
* the centre `C` of the average is the ball of the zero coefficient of each entry (the zero
  mode, `zeroModeBall`), the radius matrix `R` adds that ball's radius to the model radius;
* `δ_T = ‖I - S C‖ + ‖S‖ ‖R‖ < 1` (row sums, rounded outward; the entries of `I - S C` are
  balls) and `‖S‖/(1 - δ_T) ≤ σT - μ` (in the form `‖S‖ + σ δ_T ≤ σ`, `gramBoundsOk`).

Contracts: `torsionAvgCheck_shape` (law-free) and `torsionAvgCheck_sound`, through
`CertModel.Encloses.average` and `matrix_inv_of_approx_inverse` on the full bordered average.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.Certificate

open KAM CertArith

section Defs

variable {α : Type} [CertArith α]

/-- The exact shape test of a list matrix: `k` rows, each of length `k`. -/
def listShapeOk {β : Type} (k : ℕ) (M : List (List β)) : Bool :=
  M.length == k && M.all fun r => r.length == k

/-- The key `k` denotes the zero mode in dimension `n` (`certKeyFun n k = 0`). -/
def isZeroKeyN (n : ℕ) (k : CertKey) : Bool := (List.range n).all fun i => k.getD i 0 == 0

/-- A ball of the zero coefficient `coeff n 0` of a model's polynomial. -/
def zeroModeBall (n : ℕ) (m : CertModel α) : CertBall α :=
  CertPoly.coeffSumBall ⟨m.poly.terms.filter fun t => isZeroKeyN n t.1⟩

/-- The entry `(i, j)` of a list matrix of backend complex numbers (`0` if missing). -/
def ccEntry (S : List (List (CC α))) (i j : ℕ) : CC α :=
  ((S[i]?).bind fun r => r[j]?).getD ⟨ofInt 0, ofInt 0⟩

/-- The centre of the average of the entry `(l, j)`. -/
def avgCentre (n : ℕ) (T : ModelMatrix α) (l j : ℕ) : CC α :=
  (zeroModeBall n (modelMatrixEntry T l j)).c

/-- The radius of the average of the entry `(l, j)` around `avgCentre`. -/
def avgRadius (n : ℕ) (T : ModelMatrix α) (l j : ℕ) : α :=
  upAdd (zeroModeBall n (modelMatrixEntry T l j)).r (modelMatrixEntry T l j).rad

/-- An upper bound of `|(I - S C)_ij|`: the ball of `δ_ij - Σ_l S_il C_lj`. -/
def avgDefectUp (n : ℕ) (T : ModelMatrix α) (S : List (List (CC α))) (i j : ℕ) : α :=
  let p := CertBall.listSum ((List.finRange (n + 1)).map fun l =>
    CertBall.times ⟨ccEntry S i l.val, ofInt 0⟩ ⟨avgCentre n T l.val j, ofInt 0⟩)
  let d := CertBall.plus (if i = j then CertBall.oneBall else ⟨⟨ofInt 0, ofInt 0⟩, ofInt 0⟩)
    ⟨CC.negC p.c, p.r⟩
  upAdd d.c.normUp d.r

/-- The row sums of the bounds of `I - S C`. -/
def avgDefectRows (n : ℕ) (T : ModelMatrix α) (S : List (List (CC α))) : List α :=
  List.ofFn fun i : Fin (n + 1) =>
    sumUp (fun j : Fin (n + 1) => avgDefectUp n T S i.val j.val) (List.finRange (n + 1))

/-- The row sums of `|S_ij|`. -/
def avgInvRows (n : ℕ) (S : List (List (CC α))) : List α :=
  List.ofFn fun i : Fin (n + 1) =>
    sumUp (fun j : Fin (n + 1) => (ccEntry S i.val j.val).normUp) (List.finRange (n + 1))

/-- The row sums of the radius matrix `R`. -/
def avgRadRows (n : ℕ) (T : ModelMatrix α) : List α :=
  List.ofFn fun i : Fin (n + 1) =>
    sumUp (fun j : Fin (n + 1) => avgRadius n T i.val j.val) (List.finRange (n + 1))

/-- Every entry of the `(n+1) × (n+1)` model matrix has degree `0`. -/
def avgDegOk (n : ℕ) (T : ModelMatrix α) : Bool :=
  (List.range (n + 1)).all fun i => (List.range (n + 1)).all fun j =>
    (modelMatrixEntry T i j).deg == 0

/-- The final tests from the row sums: `a ≥` every row of `I - S C`, `r ≥` every row of `R`,
`0 ≤ r`, and with `δ_T = a + ‖S‖ r` the tests of `gramBoundsOk` (`δ_T < 1`,
`‖S‖ + σ δ_T ≤ σ`). -/
def avgBoundsOk (dRows bRows rRows : List α) (σTμ : ℚ) : Bool :=
  let a := maxCandidate dRows
  let b := maxCandidate bRows
  let r := maxCandidate rRows
  let δ := upAdd a (upMul b r)
  dRows.all (fun x => ble x a) && rRows.all (fun x => ble x r) && ble (ofInt 0) r &&
    gramBoundsOk [δ] bRows δ b σTμ

/-- The averaged bordered torsion check at dimension `n`. It FIRST checks the exact
shapes `HasShape (n + 1) T` and `HasShape (n + 1) S` (decidable list-length tests) and rejects
otherwise; then centre `C` = zero modes, radius matrix `R`; with the constant witness `S`,
`‖I - S C‖ + ‖S‖ ‖R‖ =: δ_T < 1` and `‖S‖/(1-δ_T) ≤ σT - μ`, all on `(n+1) × (n+1)` arrays. -/
def torsionAvgCheck {α : Type} [CertArith α] (n : ℕ) (T : ModelMatrix α)
    (S : List (List (CC α))) (σTμ : ℚ) : Bool :=
  listShapeOk (n + 1) T && listShapeOk (n + 1) S && avgDegOk n T &&
    avgBoundsOk (avgDefectRows n T S) (avgInvRows n S) (avgRadRows n T) σTμ

end Defs

/-! ### Contracts -/

section Sound

variable {α : Type} [CertArith α]

theorem listShapeOk_iff {β : Type} (k : ℕ) (M : List (List β)) :
    listShapeOk k M = true ↔ ModelMatrix.HasShape k M := by
  simp [listShapeOk, ModelMatrix.HasShape]

/-- A passing averaging check has exact `(n+1) × (n+1)` inputs (law-free; shape negative tests). -/
theorem torsionAvgCheck_shape {α : Type} [CertArith α] {n : ℕ} {T : ModelMatrix α}
    {S : List (List (CC α))} {σTμ : ℚ} (h : torsionAvgCheck n T S σTμ = true) :
    ModelMatrix.HasShape (n + 1) T ∧ ModelMatrix.HasShape (n + 1) S := by
  simp only [torsionAvgCheck, Bool.and_eq_true] at h
  exact ⟨(listShapeOk_iff _ _).1 h.1.1.1, (listShapeOk_iff _ _).1 h.1.1.2⟩

theorem isZeroKeyN_iff (n : ℕ) (k : CertKey) : isZeroKeyN n k = true ↔ certKeyFun n k = 0 := by
  simp only [isZeroKeyN, List.all_eq_true, List.mem_range, beq_iff_eq, funext_iff,
    certKeyFun, Pi.zero_apply]
  exact ⟨fun h i => h i.val i.isLt, fun h i hi => h ⟨i, hi⟩⟩

/-- The zero coefficient is the value at `0` of the zero-key terms. -/
theorem CertPoly.coeff_zero_eq (n : ℕ) (P : CertPoly α) :
    P.coeff n 0 = (⟨P.terms.filter fun t => isZeroKeyN n t.1⟩ : CertPoly α).eval n 0 := by
  rw [CertPoly.coeff_eq_sum]
  simp only [CertPoly.eval]
  induction P.terms with
  | nil => simp
  | cons t L ih =>
    by_cases ht : isZeroKeyN n t.1 = true
    · have h0 := (isZeroKeyN_iff n t.1).1 ht
      simp [ht, h0, ih, character_zero_point]
    · have h0 : certKeyFun n t.1 ≠ 0 := fun h => ht ((isZeroKeyN_iff n t.1).2 h)
      simp [ht, h0, ih]

/-- Sums over the bordered index `Fin n ⊕ Unit` through `torsionIdx` are sums over `Fin (n+1)`. -/
theorem sum_torsionIdx {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ∑ a : Fin n ⊕ Unit, g (torsionIdx n a) = ∑ j : Fin (n + 1), g j.val := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_castSucc]
  simp [torsionIdx]

variable [LawfulCertArith α]

theorem CertBall.mem_exact (c : CC α) : CertBall.Mem c.toC (⟨c, ofInt 0⟩ : CertBall α) := by
  simp [CertBall.Mem, LawfulCertArith.val_ofInt]

/-- A balanced sum of balls encloses the sum of their members. -/
theorem CertBall.mem_listSum_of (L : List (ℂ × CertBall α))
    (h : ∀ p ∈ L, CertBall.Mem p.1 p.2) :
    CertBall.Mem (L.map Prod.fst).sum (CertBall.listSum (L.map Prod.snd)) := by
  apply CertBall.mem_listSum
  induction L with
  | nil => simp [ballCentreSum, ballRadSum]
  | cons p L ih =>
    have hp := h p (by simp)
    have ih' := ih fun q hq => h q (by simp [hq])
    simp only [ballCentreSum, ballRadSum, List.map_cons, List.sum_cons] at ih' ⊢
    have e : p.1 + (L.map Prod.fst).sum - (p.2.c.toC + ((L.map Prod.snd).map
        fun b => b.c.toC).sum) = (p.1 - p.2.c.toC) + ((L.map Prod.fst).sum -
          ((L.map Prod.snd).map fun b => b.c.toC).sum) := by ring
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add hp ih')

theorem norm_le_of_mem {w : ℂ} {b : CertBall α} (h : CertBall.Mem w b) :
    ‖w‖ ≤ val (upAdd b.c.normUp b.r) := by
  have h1 := CC.norm_le_normUp b.c
  have h2 := LawfulCertArith.upAdd_ge b.c.normUp b.r
  have : ‖w‖ ≤ ‖w - b.c.toC‖ + ‖b.c.toC‖ := by
    simpa using norm_add_le (w - b.c.toC) b.c.toC
  unfold CertBall.Mem at h
  linarith

/-- The entry bound of `I - S C`. -/
theorem norm_sub_le_avgDefectUp (n : ℕ) (T : ModelMatrix α) (S : List (List (CC α)))
    (i j : ℕ) : ‖(if i = j then (1 : ℂ) else 0) - ∑ l : Fin (n + 1),
      (ccEntry S i l.val).toC * (avgCentre n T l.val j).toC‖ ≤ val (avgDefectUp n T S i j) := by
  set L : List (ℂ × CertBall α) := (List.finRange (n + 1)).map fun l =>
    ((ccEntry S i l.val).toC * (avgCentre n T l.val j).toC,
      CertBall.times ⟨ccEntry S i l.val, ofInt 0⟩ ⟨avgCentre n T l.val j, ofInt 0⟩)
  have hL : ∀ p ∈ L, CertBall.Mem p.1 p.2 := by
    intro p hp
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hp
    exact CertBall.mem_times (CertBall.mem_exact _) (CertBall.mem_exact _)
  have hp := CertBall.mem_listSum_of L hL
  have hfst : (L.map Prod.fst).sum = ∑ l : Fin (n + 1),
      (ccEntry S i l.val).toC * (avgCentre n T l.val j).toC := by
    simp [L, Fin.sum_univ_def, Function.comp_def]
  have hsnd : L.map Prod.snd = (List.finRange (n + 1)).map fun l =>
      CertBall.times ⟨ccEntry S i l.val, ofInt 0⟩ ⟨avgCentre n T l.val j, ofInt 0⟩ := by
    simp [L, Function.comp_def]
  rw [hfst, hsnd] at hp
  unfold avgDefectUp
  dsimp only
  generalize CertBall.listSum ((List.finRange (n + 1)).map fun l =>
    CertBall.times ⟨ccEntry S i l.val, ofInt 0⟩ ⟨avgCentre n T l.val j, ofInt 0⟩) = p at hp ⊢
  have hn : CertBall.Mem (-∑ l : Fin (n + 1), (ccEntry S i l.val).toC *
      (avgCentre n T l.val j).toC) (⟨CC.negC p.c, p.r⟩ : CertBall α) := by
    unfold CertBall.Mem at hp ⊢
    rw [CC.toC_negC, show ∀ x y : ℂ, -x - -y = -(x - y) from fun x y => by ring, norm_neg]
    exact hp
  have hδ : CertBall.Mem (if i = j then (1 : ℂ) else 0)
      (if i = j then CertBall.oneBall else (⟨⟨ofInt 0, ofInt 0⟩, ofInt 0⟩ : CertBall α)) := by
    split_ifs
    · exact CertBall.mem_one
    · simp [CertBall.Mem, CC.toC, LawfulCertArith.val_ofInt, Complex.ext_iff]
  rw [sub_eq_add_neg]
  exact norm_le_of_mem (CertBall.mem_plus hδ hn)

theorem avgBoundsOk_spec {dRows bRows rRows : List α} {σ : ℚ}
    (h : avgBoundsOk dRows bRows rRows σ = true) :
    (∀ x ∈ dRows, val x ≤ val (maxCandidate dRows)) ∧
      (∀ x ∈ rRows, val x ≤ val (maxCandidate rRows)) ∧ 0 ≤ val (maxCandidate rRows) ∧
      (∀ x ∈ bRows, val x ≤ val (maxCandidate bRows)) ∧
      val (upAdd (maxCandidate dRows) (upMul (maxCandidate bRows) (maxCandidate rRows))) < 1 ∧
      0 ≤ val (upAdd (maxCandidate dRows) (upMul (maxCandidate bRows) (maxCandidate rRows))) ∧
      val (maxCandidate bRows) + σ *
        val (upAdd (maxCandidate dRows) (upMul (maxCandidate bRows) (maxCandidate rRows))) ≤ σ := by
  simp only [avgBoundsOk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hd, hr⟩, hr0⟩, hg⟩ := h
  obtain ⟨-, hb, h1, h0, hf⟩ := gramBoundsOk_spec hg
  refine ⟨fun x hx => LawfulCertArith.ble_sound _ _ (hd x hx),
    fun x hx => LawfulCertArith.ble_sound _ _ (hr x hx), ?_, hb, h1, h0, hf⟩
  have := LawfulCertArith.ble_sound _ _ hr0
  rwa [LawfulCertArith.val_ofInt, Int.cast_zero] at this

theorem torsionIdx_injective (n : ℕ) : Function.Injective (torsionIdx n) := by
  rintro (a | _) (b | _) h <;> simp only [torsionIdx, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (Fin.ext h)
  · exact absurd h (Nat.ne_of_lt a.isLt)
  · exact absurd h.symm (Nat.ne_of_lt b.isLt)
  · rfl

/-- **Averaged torsion contract.** -/
theorem torsionAvgCheck_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ω : Fin n → ℝ} {ρ : ℝ} (hρ : 0 < ρ) {T : ModelMatrix α}
    (hT : T.Encloses n (torsionIdx n) ρ (KAM.Iso.extendedTorsion H K ω))
    (hcont : ∀ a b, ContinuousOn (fun θ => KAM.Iso.extendedTorsion H K ω θ a b)
      (complexStrip n ρ))
    (S : List (List (CC α))) (σTμ : ℚ) (h : torsionAvgCheck n T S σTμ = true) :
    IsUnit (KAM.Iso.extendedTorsionAverage H K ω).det ∧
      ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage H K ω)⁻¹ i j‖ ≤ σTμ := by
  simp only [torsionAvgCheck, Bool.and_eq_true] at h
  obtain ⟨⟨-, hdeg⟩, hb⟩ := h
  obtain ⟨hd, hr, hr0, hbr, hδ1, hδ0, hfin⟩ := avgBoundsOk_spec hb
  set a := maxCandidate (avgDefectRows n T S)
  set b := maxCandidate (avgInvRows n S)
  set r := maxCandidate (avgRadRows n T)
  set A := KAM.Iso.extendedTorsionAverage H K ω
  set ι := torsionIdx n
  let Sm : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ := fun x y => (ccEntry S (ι x) (ι y)).toC
  let Cm : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ := fun x y => (avgCentre n T (ι x) (ι y)).toC
  have hrow : ∀ x : Fin n ⊕ Unit, ∃ i : Fin (n + 1), i.val = ι x :=
    fun x => ⟨⟨ι x, torsionIdx_lt n x⟩, rfl⟩
  -- the entries of the average
  have hent : ∀ x y, ‖A x y - Cm x y‖ ≤ val (avgRadius n T (ι x) (ι y)) := by
    intro x y
    obtain ⟨m, hm, hme⟩ := hT x y
    have hm' : modelMatrixEntry T (ι x) (ι y) = m := by
      simp only [modelMatrixEntry] at hm ⊢
      rw [hm, Option.getD_some]
    have hdeg0 : m.deg = 0 := by
      simp only [avgDegOk, List.all_eq_true, List.mem_range, beq_iff_eq] at hdeg
      rw [← hm']
      exact hdeg _ (torsionIdx_lt n x) _ (torsionIdx_lt n y)
    have havg := hme.average hρ (hcont x y)
    rw [hdeg0, zpow_zero, zpow_zero, one_mul, one_mul] at havg
    have hz := CertPoly.mem_coeffSumBall n
      (⟨m.poly.terms.filter fun t => isZeroKeyN n t.1⟩ : CertPoly α)
    rw [← CertPoly.coeff_zero_eq] at hz
    have hu := LawfulCertArith.upAdd_ge (zeroModeBall n m).r m.rad
    simp only [Cm, avgRadius, avgCentre, hm']
    unfold CertBall.Mem at hz
    have hA : A x y = torusAverage (fun v : Fin n → ℝ =>
        KAM.Iso.extendedTorsion H K ω (fun i => (v i : ℂ)) x y) := rfl
    rw [hA]
    refine (norm_sub_le_norm_sub_add_norm_sub _ (m.poly.coeff n 0) _).trans ?_
    unfold zeroModeBall at hu ⊢
    linarith
  -- the radius matrix
  have hR : ‖A - Cm‖ ≤ val r := by
    rw [norm_le_iff_forall_rowSum hr0]
    intro x
    obtain ⟨i, hi⟩ := hrow x
    have hrw := hr _ ((List.mem_ofFn' _ _).mpr ⟨i, rfl⟩)
    refine le_trans ?_ ((sumUp_ge _ _).trans hrw)
    rw [← Fin.sum_univ_def, hi]
    rw [← sum_torsionIdx n (fun j => val (avgRadius n T (ι x) j))]
    exact Finset.sum_le_sum fun y _ => by rw [Matrix.sub_apply]; exact hent x y
  -- the witness
  have hb0 : 0 ≤ val b := by
    refine le_trans ?_ (hbr _ ((List.mem_ofFn' _ _).mpr ⟨0, rfl⟩))
    exact sumUp_nonneg (fun _ => CC.normUp_nonneg _) _
  have hS : ‖Sm‖ ≤ val b := by
    rw [norm_le_iff_forall_rowSum hb0]
    intro x
    obtain ⟨i, hi⟩ := hrow x
    have hrw := hbr _ ((List.mem_ofFn' _ _).mpr ⟨i, rfl⟩)
    refine le_trans ?_ ((sumUp_ge _ _).trans hrw)
    rw [← Fin.sum_univ_def, hi]
    rw [← sum_torsionIdx n (fun j => val (ccEntry S (ι x) j).normUp)]
    exact Finset.sum_le_sum fun y _ => CC.norm_le_normUp _
  -- the centre defect
  have ha0 : 0 ≤ val a := by
    refine le_trans ?_ (hd _ ((List.mem_ofFn' _ _).mpr ⟨0, rfl⟩))
    exact sumUp_nonneg (fun _ => (norm_nonneg _).trans (norm_sub_le_avgDefectUp n T S _ _)) _
  have hD : ‖1 - Sm * Cm‖ ≤ val a := by
    rw [norm_le_iff_forall_rowSum ha0]
    intro x
    obtain ⟨i, hi⟩ := hrow x
    have hrw := hd _ ((List.mem_ofFn' _ _).mpr ⟨i, rfl⟩)
    refine le_trans ?_ ((sumUp_ge _ _).trans hrw)
    rw [← Fin.sum_univ_def, hi]
    rw [← sum_torsionIdx n (fun j => val (avgDefectUp n T S (ι x) j))]
    refine Finset.sum_le_sum fun y _ => ?_
    have he : (1 - Sm * Cm) x y = (if ι x = ι y then (1 : ℂ) else 0) - ∑ l : Fin (n + 1),
        (ccEntry S (ι x) l.val).toC * (avgCentre n T l.val (ι y)).toC := by
      rw [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
        sum_torsionIdx n (fun l => (ccEntry S (ι x) l).toC * (avgCentre n T l (ι y)).toC)]
      congr 1
      by_cases hxy : x = y
      · simp [hxy]
      · have hne : ι x ≠ ι y := (torsionIdx_injective n).ne hxy
        simp [hxy, hne]
    rw [he]
    exact norm_sub_le_avgDefectUp n T S _ _
  -- the defect of `S` against the average
  have hE : ‖1 - Sm * A‖ ≤ val (upAdd a (upMul b r)) := by
    have e : 1 - Sm * A = (1 - Sm * Cm) + Sm * (Cm - A) := by
      rw [Matrix.mul_sub]; abel
    have hm := LawfulCertArith.upMul_ge b r hb0 hr0
    have hu := LawfulCertArith.upAdd_ge a (upMul b r)
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖Sm * (Cm - A)‖ ≤ val b * val r := by
      refine (Matrix.linfty_opNorm_mul _ _).trans ?_
      rw [norm_sub_rev]
      exact mul_le_mul hS hR (norm_nonneg _) hb0
    linarith
  obtain ⟨hU, hInv, -⟩ := matrix_inv_of_approx_inverse hE hδ1 hS
  refine ⟨hU, fun i => (rowSum_le_norm _ i).trans (hInv.trans ?_)⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end Sound

end KAM.Certificate

end
