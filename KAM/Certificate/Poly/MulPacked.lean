/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Poly.OverlapAdd
public import KAM.Certificate.Model.Basic

/-!
# Advice-checked complex products of backend polynomials

`CertPoly.toMants` reads the integer mantissas `(re, im)` of a backend polynomial at scale `P`
through an UNTRUSTED decoder, re-verifying every value by `mantCheck` (zero mantissas are dropped,
so an all-zero part is the empty list). `CertPoly.mulPacked` forms the four real products
(`re·re`, `im·im`, `re·im`, `im·re`) by `packedRealProduct`: an empty factor gives the exact zero
product with no advice and no kernel work (SO-ADVCOUNT lever 2: parity makes three of the four
real products of a lunar complex product identically zero); otherwise the factors are laid out
densely, checked by `checkPackedProduct`, and the result is the combined rounded target
(nonzero slots) plus a remainder bound `Σ_i b_i w^{|k_i|₁} / 2^{2P}` over every product slot
(`b_i = 2^scale` on the target box, `2^(outLog+1)` elsewhere). The coefficients are made exact in
the backend by `ofDyadic` (fail closed). `CertPoly.mulPacked_sound` encloses the EXACT product on
the strip.
-/

@[expose] public section

namespace KAM.Certificate

open KAM CertArith

/-! ### Mantissas -/

/-- The verified mantissas `(re, im)` of one backend coefficient, or `none`. -/
def certMantPair {α : Type} [CertArith α] (dec : ℕ → α → Option ℤ) (P : ℕ) (c : CC α) :
    Option (ℤ × ℤ) :=
  match dec P c.re, dec P c.im with
  | some zr, some zi => if mantCheck P c.re zr && mantCheck P c.im zi then some (zr, zi) else none
  | _, _ => none

/-- The real (`re = true`) or imaginary part of a mantissa pair. -/
def mantSel (re : Bool) (z : ℤ × ℤ) : ℤ := if re then z.1 else z.2

/-- The nonzero real (`re = true`) or imaginary mantissa of a verified term, keyed. -/
def certMantPart {α : Type} [CertArith α] (dec : ℕ → α → Option ℤ) (P : ℕ) (re : Bool)
    (t : CertKey × CC α) : Option (CertKey × ℤ) :=
  match certMantPair dec P t.2 with
  | some z => if mantSel re z = 0 then none else some (t.1, mantSel re z)
  | none => none

/-- Integer mantissas `(re, im)` of a backend polynomial at scale `P`, read with the decoder
`dec` and each verified by `mantCheck` (`none` on any failure: fail closed). Zero mantissas are
dropped, so an all-zero part is the empty list. -/
def CertPoly.toMants {α : Type} [CertArith α] (dec : ℕ → α → Option ℤ) (P : ℕ)
    (p : CertPoly α) : Option (List (CertKey × ℤ) × List (CertKey × ℤ)) :=
  if p.terms.all fun t => (certMantPair dec P t.2).isSome then
    some (p.terms.filterMap (certMantPart dec P true),
      p.terms.filterMap (certMantPart dec P false))
  else none

theorem intEval_nil (n : ℕ) (θ : Fin n → ℂ) : intEval n [] θ = 0 := rfl

theorem intEval_cons (n : ℕ) (t : CertKey × ℤ) (ts : List (CertKey × ℤ)) (θ : Fin n → ℂ) :
    intEval n (t :: ts) θ = (t.2 : ℂ) * character (certKeyFun n t.1) θ + intEval n ts θ := by
  simp [intEval]

theorem intEval_append (n : ℕ) (ts us : List (CertKey × ℤ)) (θ : Fin n → ℂ) :
    intEval n (ts ++ us) θ = intEval n ts θ + intEval n us θ := by
  simp [intEval]

theorem intEval_map_neg (n : ℕ) (ts : List (CertKey × ℤ)) (θ : Fin n → ℂ) :
    intEval n (ts.map fun t => (t.1, -t.2)) θ = -intEval n ts θ := by
  induction ts with
  | nil => simp [intEval_nil]
  | cons t ts ih =>
    rw [List.map_cons, intEval_cons, intEval_cons, ih]
    push_cast
    ring

theorem certMantPair_sound {α : Type} [CertArith α] [LawfulCertArith α]
    {dec : ℕ → α → Option ℤ} {P : ℕ} {c : CC α} {z : ℤ × ℤ} (h : certMantPair dec P c = some z) :
    c.toC = ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) / 2 ^ P := by
  unfold certMantPair at h
  split at h
  · rename_i zr zi _ _
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true] at hc
    rw [CC.toC, Complex.mk_eq_add_mul_I, mantCheck_sound hc.1, mantCheck_sound hc.2]
    push_cast
    ring
  · simp at h

theorem intEval_filterMap_certMantPart {α : Type} [CertArith α] {n : ℕ}
    {dec : ℕ → α → Option ℤ} {P : ℕ} (re : Bool) (θ : Fin n → ℂ) :
    ∀ (ts : List (CertKey × CC α)), (∀ t ∈ ts, (certMantPair dec P t.2).isSome = true) →
    intEval n (ts.filterMap (certMantPart dec P re)) θ = (ts.map fun t =>
      ((mantSel re ((certMantPair dec P t.2).getD (0, 0)) : ℤ) : ℂ) *
        character (certKeyFun n t.1) θ).sum
  | [], _ => by simp [intEval_nil]
  | t :: ts, h => by
    have ih := intEval_filterMap_certMantPart re θ ts fun u hu => h u (by simp [hu])
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (h t (by simp))
    rw [List.map_cons, List.sum_cons, ← ih, hz, Option.getD_some]
    by_cases h0 : mantSel re z = 0
    · rw [List.filterMap_cons_none (by simp [certMantPart, hz, h0]), h0]
      simp
    · rw [List.filterMap_cons_some (b := (t.1, mantSel re z)) (by simp [certMantPart, hz, h0]),
        intEval_cons]

theorem CertPoly.toMants_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {dec : ℕ → α → Option ℤ} {P : ℕ} {p : CertPoly α}
    {m : List (CertKey × ℤ) × List (CertKey × ℤ)} (h : p.toMants dec P = some m)
    (θ : Fin n → ℂ) :
    p.eval n θ = (intEval n m.1 θ + Complex.I * intEval n m.2 θ) / 2 ^ P := by
  unfold CertPoly.toMants at h
  split_ifs at h with hall
  simp only [Option.some.injEq] at h
  subst h
  have hall' : ∀ t ∈ p.terms, (certMantPair dec P t.2).isSome = true := fun t ht =>
    List.all_eq_true.mp hall t ht
  rw [intEval_filterMap_certMantPart true θ p.terms hall',
    intEval_filterMap_certMantPart false θ p.terms hall', CertPoly.eval,
    ← List.sum_map_mul_left, ← List.sum_map_add, div_eq_mul_inv, ← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (hall' t ht)
  simp only [hz, Option.getD_some, mantSel, ite_true, Bool.false_eq_true, ite_false]
  rw [certMantPair_sound hz]
  ring

/-! ### Balanced sums over the product window -/

/-- `Σ_{q < size} f (base + q)` by binary splitting (kernel depth `log size`; `fuel` levels, then
the direct sum). -/
def packRangeSum (f : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, base, size => ((List.range size).map fun q => f (base + q)).sum
  | fuel + 1, base, size =>
    if size ≤ 1 then ((List.range size).map fun q => f (base + q)).sum
    else packRangeSum f fuel base (size / 2) +
      packRangeSum f fuel (base + size / 2) (size - size / 2)

theorem packRangeSum_eq (f : ℕ → ℕ) (fuel : ℕ) : ∀ base size : ℕ,
    packRangeSum f fuel base size = ∑ q ∈ Finset.range size, f (base + q) := by
  induction fuel with
  | zero => intro base size; rw [packRangeSum, list_sum_map_range_eq]
  | succ fuel ih =>
    intro base size
    rw [packRangeSum]
    split_ifs with hs
    · rw [list_sum_map_range_eq]
    · rw [ih, ih]
      conv_rhs => rw [show size = size / 2 + (size - size / 2) by omega, Finset.sum_range_add]
      simp only [Nat.add_assoc]

/-- `max_{q < size} f (base + q)` (`0` on an empty range) by binary splitting. -/
def packRangeMax (f : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, base, size => ((List.range size).map fun q => f (base + q)).foldr max 0
  | fuel + 1, base, size =>
    if size ≤ 1 then ((List.range size).map fun q => f (base + q)).foldr max 0
    else max (packRangeMax f fuel base (size / 2))
      (packRangeMax f fuel (base + size / 2) (size - size / 2))

theorem le_foldr_max_of_mem {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem le_packRangeMax (f : ℕ → ℕ) (fuel : ℕ) : ∀ base size q : ℕ, q < size →
    f (base + q) ≤ packRangeMax f fuel base size := by
  induction fuel with
  | zero =>
    intro base size q hq
    exact le_foldr_max_of_mem (List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩)
  | succ fuel ih =>
    intro base size q hq
    rw [packRangeMax]
    split_ifs with hs
    · exact le_foldr_max_of_mem (List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩)
    · by_cases hq2 : q < size / 2
      · exact (ih base (size / 2) q hq2).trans (le_max_left _ _)
      · have := ih (base + size / 2) (size - size / 2) (q - size / 2) (by omega)
        rw [show base + size / 2 + (q - size / 2) = base + q by omega] at this
        exact this.trans (le_max_right _ _)

/-! ### One real packed product -/

/-- The `ℓ¹` size `|k|₁` of the key of product slot `i`. -/
def PackedAdvice.slotDeg (adv : PackedAdvice) (i : ℕ) : ℕ :=
  ((adv.la.prodKey adv.lb i).map Int.natAbs).sum

/-- The error bound of product slot `i` in units of the product mantissa: `2^scale` on the
target box, `2^(outLog+1)` elsewhere. -/
def PackedAdvice.slotErr (adv : PackedAdvice) (i : ℕ) : ℕ :=
  if adv.inBox i then 2 ^ adv.scale else 2 ^ (adv.outLog + 1)

/-- The largest slot degree over the product window. -/
def PackedAdvice.maxSlotDeg (adv : PackedAdvice) : ℕ :=
  packRangeMax adv.slotDeg adv.prodLen 0 adv.prodLen

/-- The remainder bound of one packed real product on the strip of the weight `w = num/den`,
in natural-number arithmetic: `Σ_i b_i w^{d_i} / 2^P2 = (Σ_i b_i num^{d_i} den^{D-d_i}) /
(den^D · 2^P2)` over every product slot, `D` the largest slot degree. -/
def PackedAdvice.remainderBound (adv : PackedAdvice) (W : CertWeight) (P2 : ℕ) : ℚ :=
  ((packRangeSum (fun i => adv.slotErr i * W.w.num.toNat ^ adv.slotDeg i *
      W.w.den ^ (adv.maxSlotDeg - adv.slotDeg i)) adv.prodLen 0 adv.prodLen : ℕ) : ℚ) /
    ((W.w.den ^ adv.maxSlotDeg * 2 ^ P2 : ℕ) : ℚ)

/-- The keyed nonzero entry of an indexed combined slot. -/
def PackedAdvice.targetEntry (adv : PackedAdvice) (ic : ℕ × ℤ) : Option (CertKey × ℤ) :=
  if ic.2 = 0 then none else some (adv.la.prodKey adv.lb ic.1, ic.2)

/-- The rounded product's integer Fourier data (units `2^scale` of the product mantissa): the
nonzero combined slots with their product keys (indices from `List.range`, literals in the
kernel). -/
def PackedAdvice.targetTerms (adv : PackedAdvice) : List (CertKey × ℤ) :=
  ((List.range adv.prodLen).zip adv.combined).filterMap adv.targetEntry

/-- One real product of integer Fourier data (mantissa scale `P2` of the product): an empty
factor gives the exact zero product (no advice, no kernel work); otherwise the dense factors must
pass `checkPackedProduct`, and the result is the rounded target with the remainder bound. -/
def packedRealProduct (adv : PackedAdvice) (W : CertWeight) (P2 : ℕ)
    (x y : List (CertKey × ℤ)) : Option (List (CertKey × ℤ) × ℚ) :=
  if x.isEmpty || y.isEmpty then some ([], 0) else
    match adv.la.dense x, adv.lb.dense y with
    | some da, some db =>
      if checkPackedProduct adv da db then some (adv.targetTerms, adv.remainderBound W P2)
      else none
    | _, _ => none

theorem intEval_targetEntry (adv : PackedAdvice) (n : ℕ) (θ : Fin n → ℂ) :
    ∀ (cs : List ℤ) (k : ℕ), intEval n (((List.range' k cs.length).zip cs).filterMap
      adv.targetEntry) θ = ∑ j ∈ Finset.range cs.length,
        (cs.getD j 0 : ℂ) * character (certKeyFun n (adv.la.prodKey adv.lb (k + j))) θ
  | [], k => by simp [intEval_nil]
  | c :: cs, k => by
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    have ih := intEval_targetEntry adv n θ cs (k + 1)
    simp only [show ∀ j, k + 1 + j = k + (j + 1) from fun j => by omega] at ih
    by_cases hc : c = 0
    · rw [List.filterMap_cons_none (by simp [PackedAdvice.targetEntry, hc]), ih, hc]
      simp
    · rw [List.filterMap_cons_some (b := (adv.la.prodKey adv.lb k, c))
        (by simp [PackedAdvice.targetEntry, hc]), intEval_cons, ih, add_comm]

theorem intEval_targetTerms (adv : PackedAdvice) (n : ℕ) (θ : Fin n → ℂ) :
    intEval n adv.targetTerms θ = ∑ j ∈ Finset.range adv.combined.length,
      (adv.combined.getD j 0 : ℂ) * character (certKeyFun n (adv.la.prodKey adv.lb j)) θ := by
  rw [PackedAdvice.targetTerms, List.range_eq_range', ← PackedAdvice.combined_length,
    intEval_targetEntry]
  simp

theorem PackedAdvice.shapeOK_compat {adv : PackedAdvice} (h : adv.shapeOK = true) :
    PackLayout.compat adv.la.dims.length adv.la adv.lb = true := by
  simp only [PackedAdvice.shapeOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

theorem remainderBound_mul {adv : PackedAdvice} {W : CertWeight} (hw : 0 < W.w) (P2 : ℕ) :
    ((adv.remainderBound W P2 : ℚ) : ℝ) * 2 ^ P2 = ∑ i ∈ Finset.range adv.prodLen,
      (adv.slotErr i : ℝ) * (W.w : ℝ) ^ adv.slotDeg i := by
  have hnum : (0 : ℤ) < W.w.num := Rat.num_pos.mpr hw
  have hden : (0 : ℝ) < W.w.den := by exact_mod_cast W.w.den_pos
  have hnumR : ((W.w.num.toNat : ℕ) : ℝ) = (W.w.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  have hwR : (W.w : ℝ) = (W.w.num : ℝ) / (W.w.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  rw [PackedAdvice.remainderBound, packRangeSum_eq]
  push_cast
  rw [hnumR, div_mul_eq_mul_div, mul_div_mul_right _ _ (by positivity : (2 : ℝ) ^ P2 ≠ 0),
    Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hd : adv.slotDeg i ≤ adv.maxSlotDeg := by
    simpa [PackedAdvice.maxSlotDeg] using
      le_packRangeMax adv.slotDeg adv.prodLen 0 adv.prodLen i (Finset.mem_range.mp hi)
  rw [Nat.zero_add, hwR, div_pow]
  have hD : (W.w.den : ℝ) ^ adv.maxSlotDeg =
      (W.w.den : ℝ) ^ adv.slotDeg i * (W.w.den : ℝ) ^ (adv.maxSlotDeg - adv.slotDeg i) := by
    rw [← pow_add, Nat.add_sub_cancel' hd]
  rw [hD]
  field_simp

/-- **One real product**: the exact product of the two integer Fourier sums is `2^scale` times
the returned target data up to the returned bound times `2^P2`, on the strip. -/
theorem packedRealProduct_sound {adv : PackedAdvice} {W : CertWeight} {P2 : ℕ}
    {x y : List (CertKey × ℤ)} {out : List (CertKey × ℤ) × ℚ}
    (h : packedRealProduct adv W P2 x y = some out) {s N : ℕ} (hW : checkWeight W s N = true)
    {n : ℕ} {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n W.rho) :
    ‖intEval n x θ * intEval n y θ - 2 ^ adv.scale * intEval n out.1 θ‖ ≤
      ((out.2 : ℚ) : ℝ) * 2 ^ P2 := by
  unfold packedRealProduct at h
  split_ifs at h with hemp
  · simp only [Option.some.injEq] at h
    subst h
    rcases Bool.or_eq_true_iff.mp hemp with he | he <;>
      simp [List.isEmpty_iff.mp he, intEval_nil]
  split at h
  · rename_i da db ha hb
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    have hw1 := CertWeight.one_le_w hW
    have hw0 : (0 : ℚ) < W.w := by exact_mod_cast (zero_lt_one.trans_le hw1)
    obtain ⟨hlen, hsl⟩ := checkPackedProduct_slots hc
    have hcompat := PackedAdvice.shapeOK_compat (checkPackedProduct_guards hc).2.1
    have hconvlen : (listConv da db).length = adv.prodLen := by
      rw [← hlen, PackedAdvice.combined_length]
    rw [PackLayout.intEval_mul_of_compat hcompat ha hb θ, intEval_targetTerms,
      list_sum_map_range_eq, hlen, Finset.mul_sum, ← Finset.sum_sub_distrib,
      remainderBound_mul hw0, ← hconvlen]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hi' := Finset.mem_range.mp hi
    have hdiff : ((listConv da db).getD i 0 : ℂ) *
        character (certKeyFun n (adv.la.prodKey adv.lb i)) θ -
        2 ^ adv.scale * ((adv.combined.getD i 0 : ℂ) *
          character (certKeyFun n (adv.la.prodKey adv.lb i)) θ) =
        (((listConv da db).getD i 0 - 2 ^ adv.scale * adv.combined.getD i 0 : ℤ) : ℂ) *
          character (certKeyFun n (adv.la.prodKey adv.lb i)) θ := by
      push_cast
      ring
    rw [hdiff, norm_mul, Complex.norm_intCast]
    have he := (hsl i hi').1
    have herr : |(((listConv da db).getD i 0 - 2 ^ adv.scale * adv.combined.getD i 0 : ℤ) : ℝ)|
        ≤ (adv.slotErr i : ℝ) := by
      rw [← Int.cast_abs]
      have : ((adv.slotErr i : ℕ) : ℤ) = if adv.inBox i then 2 ^ adv.scale
          else 2 ^ (adv.outLog + 1) := by
        simp only [PackedAdvice.slotErr]
        split_ifs <;> push_cast <;> rfl
      rw [← this] at he
      exact_mod_cast he
    have hchi : ‖character (certKeyFun n (adv.la.prodKey adv.lb i)) θ‖ ≤
        (W.w : ℝ) ^ adv.slotDeg i :=
      (norm_character_le_weight hW _ hθ).trans
        (pow_le_pow_right₀ hw1 (sum_natAbs_certKeyFun_le n _))
    exact mul_le_mul herr hchi (norm_nonneg _) (by positivity)
  · simp at h

/-! ### Exact backend coefficients -/

/-- The backend value `c · 2^sc / 2^P2`, exact or `none` (`ofDyadic` at the reduced exponent). -/
def ofDyadicScaled {α : Type} [CertArith α] (P2 sc : ℕ) (c : ℤ) : Option α :=
  ofDyadic (P2 - sc) (c * 2 ^ (sc - P2))

theorem ofDyadicScaled_sound {α : Type} [CertArith α] [LawfulCertArith α] {P2 sc : ℕ} {c : ℤ}
    {v : α} (h : ofDyadicScaled P2 sc c = some v) :
    val v = (c : ℝ) * 2 ^ sc / 2 ^ P2 := by
  rw [ofDyadic_sound h]
  push_cast
  rcases le_total sc P2 with hle | hle
  · rw [Nat.sub_eq_zero_of_le hle, pow_zero, mul_one]
    have : (2 : ℝ) ^ P2 = 2 ^ (P2 - sc) * 2 ^ sc := by rw [← pow_add, Nat.sub_add_cancel hle]
    rw [this]
    field_simp
  · rw [Nat.sub_eq_zero_of_le hle, pow_zero, div_one]
    have : (2 : ℝ) ^ sc = 2 ^ (sc - P2) * 2 ^ P2 := by rw [← pow_add, Nat.sub_add_cancel hle]
    rw [this]
    field_simp

/-- Backend terms `(k, place v)` with `v = c · 2^sc / 2^P2` made exact, or `none`. -/
def dyadicTerms {α : Type} [CertArith α] (P2 sc : ℕ) (place : α → CC α)
    (ts : List (CertKey × ℤ)) : Option (List (CertKey × CC α)) :=
  if ts.all fun t => (ofDyadicScaled P2 sc t.2 : Option α).isSome then
    some (ts.map fun t => (t.1, place ((ofDyadicScaled P2 sc t.2).getD (ofInt 0))))
  else none

theorem dyadicTerms_sound {α : Type} [CertArith α] [LawfulCertArith α] {P2 sc : ℕ}
    {place : α → CC α} {u : ℂ} (hp : ∀ v, (place v).toC = u * val v) {n : ℕ}
    (θ : Fin n → ℂ) {ts : List (CertKey × ℤ)} {r : List (CertKey × CC α)}
    (h : dyadicTerms P2 sc place ts = some r) :
    (r.map fun t => t.2.toC * character (certKeyFun n t.1) θ).sum =
      u * (2 ^ sc / 2 ^ P2) * intEval n ts θ := by
  unfold dyadicTerms at h
  split_ifs at h with hall
  simp only [Option.some.injEq] at h
  subst h
  rw [intEval, List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hall t ht)
  simp only [Function.comp_apply, hv, Option.getD_some, hp, ofDyadicScaled_sound hv]
  push_cast
  ring

/-! ### The complex product -/

/-- The polynomial part of one advice-checked complex product: four real packed products
(`re·re`, `im·im`, `re·im`, `im·re`) at mantissa scale `P`; the result coefficients are the
combined rounded target slots, made exact in the backend by `ofDyadic`; the radius bounds the
remainder `Σ_k e_k χ_k` on `T_ρ` (target slots `2^(scale-2P)`, other slots `2^(outLog+1-2P)`,
times `w^{|k|₁}`, upward). `none` on any failed decode, layout, shard or exactness check. A real
product with an all-zero factor part is exact zero and costs nothing. -/
def CertPoly.mulPacked {α : Type} [CertArith α] (dec : ℕ → α → Option ℤ) (W : CertWeight)
    (P : ℕ) (rr ii ri ir : PackedAdvice) (a b : CertPoly α) : Option (CertPoly α × α) :=
  (a.toMants dec P).bind fun ma => (b.toMants dec P).bind fun mb =>
  (packedRealProduct rr W (2 * P) ma.1 mb.1).bind fun pRR =>
  (packedRealProduct ii W (2 * P) ma.2 mb.2).bind fun pII =>
  (packedRealProduct ri W (2 * P) ma.1 mb.2).bind fun pRI =>
  (packedRealProduct ir W (2 * P) ma.2 mb.1).bind fun pIR =>
  (dyadicTerms (2 * P) rr.scale (fun v => ⟨v, ofInt 0⟩) pRR.1).bind fun tRR =>
  (dyadicTerms (2 * P) ii.scale (fun v => ⟨v, ofInt 0⟩)
    (pII.1.map fun t => (t.1, -t.2))).bind fun tII =>
  (dyadicTerms (2 * P) ri.scale (fun v => ⟨ofInt 0, v⟩) pRI.1).bind fun tRI =>
  (dyadicTerms (2 * P) ir.scale (fun v => ⟨ofInt 0, v⟩) pIR.1).bind fun tIR =>
  some (⟨tRR ++ tII ++ tRI ++ tIR⟩, ofRatUp (pRR.2 + pII.2 + pRI.2 + pIR.2))

/-- **Packed product contract**: the enclosure of the EXACT product on the strip. -/
theorem CertPoly.mulPacked_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {dec : ℕ → α → Option ℤ} {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    {P : ℕ} {rr ii ri ir : PackedAdvice} {a b : CertPoly α} {out : CertPoly α × α}
    (h : CertPoly.mulPacked dec W P rr ii ri ir a b = some out) :
    ∀ θ ∈ complexStrip n W.rho, ‖a.eval n θ * b.eval n θ - out.1.eval n θ‖ ≤ val out.2 := by
  intro θ hθ
  simp only [CertPoly.mulPacked, Option.bind_eq_some_iff] at h
  obtain ⟨ma, hma, mb, hmb, pRR, hRR, pII, hII, pRI, hRI, pIR, hIR, tRR, htRR, tII, htII,
    tRI, htRI, tIR, htIR, h⟩ := h
  simp only [Option.some.injEq] at h
  subst h
  have hre : ∀ v : α, (⟨v, ofInt 0⟩ : CC α).toC = 1 * val v := fun v => by
    apply Complex.ext <;> simp [CC.toC, LawfulCertArith.val_ofInt]
  have him : ∀ v : α, (⟨ofInt 0, v⟩ : CC α).toC = Complex.I * val v := fun v => by
    apply Complex.ext <;> simp [CC.toC, LawfulCertArith.val_ofInt]
  have eRR := dyadicTerms_sound hre θ htRR
  have eII := dyadicTerms_sound hre θ htII
  have eRI := dyadicTerms_sound him θ htRI
  have eIR := dyadicTerms_sound him θ htIR
  rw [intEval_map_neg] at eII
  have bRR := packedRealProduct_sound hRR hW hθ
  have bII := packedRealProduct_sound hII hW hθ
  have bRI := packedRealProduct_sound hRI hW hθ
  have bIR := packedRealProduct_sound hIR hW hθ
  have hout : CertPoly.eval n ⟨tRR ++ tII ++ tRI ++ tIR⟩ θ =
      (1 * (2 ^ rr.scale / 2 ^ (2 * P)) * intEval n pRR.1 θ +
        1 * (2 ^ ii.scale / 2 ^ (2 * P)) * -intEval n pII.1 θ) +
      Complex.I * (2 ^ ri.scale / 2 ^ (2 * P)) * intEval n pRI.1 θ +
      Complex.I * (2 ^ ir.scale / 2 ^ (2 * P)) * intEval n pIR.1 θ := by
    simp only [CertPoly.eval, List.map_append, List.sum_append, eRR, eII, eRI, eIR]
  rw [CertPoly.toMants_sound hma θ, CertPoly.toMants_sound hmb θ, hout]
  have h2 : (2 : ℂ) ^ (2 * P) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hkey : (intEval n ma.1 θ + Complex.I * intEval n ma.2 θ) / 2 ^ P *
      ((intEval n mb.1 θ + Complex.I * intEval n mb.2 θ) / 2 ^ P) -
      ((1 * (2 ^ rr.scale / 2 ^ (2 * P)) * intEval n pRR.1 θ +
        1 * (2 ^ ii.scale / 2 ^ (2 * P)) * -intEval n pII.1 θ) +
      Complex.I * (2 ^ ri.scale / 2 ^ (2 * P)) * intEval n pRI.1 θ +
      Complex.I * (2 ^ ir.scale / 2 ^ (2 * P)) * intEval n pIR.1 θ) =
      ((intEval n ma.1 θ * intEval n mb.1 θ - 2 ^ rr.scale * intEval n pRR.1 θ) -
        (intEval n ma.2 θ * intEval n mb.2 θ - 2 ^ ii.scale * intEval n pII.1 θ) +
        Complex.I * (intEval n ma.1 θ * intEval n mb.2 θ - 2 ^ ri.scale * intEval n pRI.1 θ) +
        Complex.I * (intEval n ma.2 θ * intEval n mb.1 θ - 2 ^ ir.scale * intEval n pIR.1 θ)) /
        2 ^ (2 * P) := by
    have hP : (2 : ℂ) ^ (2 * P) = ((2 : ℂ) ^ P) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [hP]
    have hD : (2 : ℂ) ^ P ≠ 0 := pow_ne_zero _ two_ne_zero
    generalize (2 : ℂ) ^ P = D at hD ⊢
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hkey, norm_div, norm_pow, Complex.norm_ofNat]
  have hup := LawfulCertArith.ofRatUp_ge (α := α) (pRR.2 + pII.2 + pRI.2 + pIR.2)
  push_cast at hup
  rw [div_le_iff₀ (by positivity)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hup (by positivity))
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  calc _ ≤ ‖intEval n ma.1 θ * intEval n mb.1 θ - 2 ^ rr.scale * intEval n pRR.1 θ‖ +
        ‖intEval n ma.2 θ * intEval n mb.2 θ - 2 ^ ii.scale * intEval n pII.1 θ‖ +
        ‖intEval n ma.1 θ * intEval n mb.2 θ - 2 ^ ri.scale * intEval n pRI.1 θ‖ +
        ‖intEval n ma.2 θ * intEval n mb.1 θ - 2 ^ ir.scale * intEval n pIR.1 θ‖ := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)) ?_
        · rw [norm_mul, hI, one_mul]
        · rw [norm_mul, hI, one_mul]
    _ ≤ _ := by
        rw [show (2 : ℝ) ^ (2 * P) = 2 ^ (2 * P) from rfl]
        nlinarith [bRR, bII, bRI, bIR]

/-- Advice for one model product: `packed` (four real packed products at mantissa scale `P`) or
`direct` (the direct product of Revision 4; tests and the `ℚ` toys). -/
inductive ProductAdvice : Type
  | direct
  | packed (P : ℕ) (rr ii ri ir : PackedAdvice)

/-- The checker's name of a product: `[site, i, j, …]`, assigned deterministically by the call
site (§7: compose 0, exp witnesses 1, reciprocal witnesses 2, Gram 3, torsion 4, invariance 5,
energy 6, SOS 7, graph 8). The generator emits the advice under the same keys. -/
abbrev ProductKey : Type := List ℕ

abbrev AdviceBook : Type := List (ProductKey × ProductAdvice)

end KAM.Certificate
