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

/-- The mantissa loop of `CertPoly.toMants`. -/
def certMantsAux {α : Type} [CertArith α] (dec : ℕ → α → Option ℤ) (P : ℕ) :
    List (CertKey × CC α) → Option (List (CertKey × ℤ) × List (CertKey × ℤ))
  | [] => some ([], [])
  | t :: ts =>
    match dec P t.2.re, dec P t.2.im, certMantsAux dec P ts with
    | some zr, some zi, some m =>
      if mantCheck P t.2.re zr && mantCheck P t.2.im zi then
        some (if zr = 0 then m.1 else (t.1, zr) :: m.1, if zi = 0 then m.2 else (t.1, zi) :: m.2)
      else none
    | _, _, _ => none

/-- Integer mantissas `(re, im)` of a backend polynomial at scale `P`, read with the decoder
`dec` and each verified by `mantCheck` (`none` on any failure: fail closed). Zero mantissas are
dropped, so an all-zero part is the empty list. -/
def CertPoly.toMants {α : Type} [CertArith α] (dec : ℕ → α → Option ℤ) (P : ℕ)
    (p : CertPoly α) : Option (List (CertKey × ℤ) × List (CertKey × ℤ)) :=
  certMantsAux dec P p.terms

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

theorem certMantsAux_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {dec : ℕ → α → Option ℤ} {P : ℕ} (θ : Fin n → ℂ) : ∀ (ts : List (CertKey × CC α))
    {m : List (CertKey × ℤ) × List (CertKey × ℤ)}, certMantsAux dec P ts = some m →
    (ts.map fun t => t.2.toC * character (certKeyFun n t.1) θ).sum =
      (intEval n m.1 θ + Complex.I * intEval n m.2 θ) / 2 ^ P
  | [], m, h => by
    simp only [certMantsAux, Option.some.injEq] at h
    subst h
    simp [intEval_nil]
  | t :: ts, m, h => by
    simp only [certMantsAux] at h
    split at h
    · rename_i zr zi m' hr hi hm
      by_cases hc : (mantCheck P t.2.re zr && mantCheck P t.2.im zi) = true
      · simp only [hc, ite_true, Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true] at hc
        have er := mantCheck_sound hc.1
        have ei := mantCheck_sound hc.2
        have ih := certMantsAux_sound θ ts hm
        have hz : t.2.toC = ((zr : ℂ) + Complex.I * (zi : ℂ)) / 2 ^ P := by
          rw [CC.toC, Complex.mk_eq_add_mul_I, er, ei]
          push_cast
          ring
        rw [List.map_cons, List.sum_cons, ih, hz]
        have e1 : intEval n (if zr = 0 then m'.1 else (t.1, zr) :: m'.1) θ =
            (zr : ℂ) * character (certKeyFun n t.1) θ + intEval n m'.1 θ := by
          split_ifs with h0
          · simp [h0]
          · rw [intEval_cons]
        have e2 : intEval n (if zi = 0 then m'.2 else (t.1, zi) :: m'.2) θ =
            (zi : ℂ) * character (certKeyFun n t.1) θ + intEval n m'.2 θ := by
          split_ifs with h0
          · simp [h0]
          · rw [intEval_cons]
        simp only
        rw [e1, e2]
        ring
      · simp only [hc] at h
        simp at h
    · simp at h

theorem CertPoly.toMants_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {dec : ℕ → α → Option ℤ} {P : ℕ} {p : CertPoly α}
    {m : List (CertKey × ℤ) × List (CertKey × ℤ)} (h : p.toMants dec P = some m)
    (θ : Fin n → ℂ) :
    p.eval n θ = (intEval n m.1 θ + Complex.I * intEval n m.2 θ) / 2 ^ P :=
  certMantsAux_sound θ p.terms h

/-! ### Balanced sums over the product window -/

/-- `Σ_{q < size} f (base + q)` by binary splitting (kernel depth `log size`; `fuel` levels, then
the direct sum). -/
def packRangeSum (f : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, base, size => ((List.range size).map fun q => f (base + q)).sum
  | fuel + 1, base, size =>
    if size ≤ 1 then ((List.range size).map fun q => f (base + q)).sum
    else packRangeSum f fuel base (size / 2) + packRangeSum f fuel (base + size / 2) (size - size / 2)

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

/-- The nonzero combined advice entries, with their product keys, from slot `i`. -/
def packTargetAux (adv : PackedAdvice) : ℕ → List ℤ → List (CertKey × ℤ)
  | _, [] => []
  | i, c :: cs => if c = 0 then packTargetAux adv (i + 1) cs
      else (adv.la.prodKey adv.lb i, c) :: packTargetAux adv (i + 1) cs

/-- The rounded product's integer Fourier data (units `2^scale` of the product mantissa). -/
def PackedAdvice.targetTerms (adv : PackedAdvice) : List (CertKey × ℤ) :=
  packTargetAux adv 0 adv.combined

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

theorem intEval_packTargetAux (adv : PackedAdvice) (n : ℕ) (θ : Fin n → ℂ) :
    ∀ (cs : List ℤ) (i : ℕ), intEval n (packTargetAux adv i cs) θ =
      ∑ j ∈ Finset.range cs.length,
        (cs.getD j 0 : ℂ) * character (certKeyFun n (adv.la.prodKey adv.lb (i + j))) θ
  | [], i => by simp [packTargetAux, intEval_nil]
  | c :: cs, i => by
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    have ih := intEval_packTargetAux adv n θ cs (i + 1)
    simp only [show ∀ j, i + 1 + j = i + (j + 1) from fun j => by omega] at ih
    rw [packTargetAux]
    split_ifs with hc
    · rw [ih, hc]
      simp
    · rw [intEval_cons, ih, add_comm]

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
    rw [PackLayout.intEval_mul_of_compat hcompat ha hb θ, PackedAdvice.targetTerms,
      intEval_packTargetAux, list_sum_map_range_eq, hlen, Finset.mul_sum,
      ← Finset.sum_sub_distrib, remainderBound_mul hw0, ← hconvlen]
    simp only [Nat.zero_add]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hi' := Finset.mem_range.mp hi
    have hdiff : ((listConv da db).getD i 0 : ℂ) * character (certKeyFun n (adv.la.prodKey adv.lb i)) θ -
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
def dyadicTermsAux {α : Type} [CertArith α] (P2 sc : ℕ) (place : α → CC α) :
    List (CertKey × ℤ) → Option (List (CertKey × CC α))
  | [] => some []
  | t :: ts =>
    match ofDyadicScaled P2 sc t.2, dyadicTermsAux P2 sc place ts with
    | some v, some r => some ((t.1, place v) :: r)
    | _, _ => none

theorem dyadicTermsAux_sound {α : Type} [CertArith α] [LawfulCertArith α] {P2 sc : ℕ}
    {place : α → CC α} {u : ℂ} (hp : ∀ v, (place v).toC = u * val v) {n : ℕ}
    (θ : Fin n → ℂ) : ∀ (ts : List (CertKey × ℤ)) {r : List (CertKey × CC α)},
    dyadicTermsAux P2 sc place ts = some r →
    (r.map fun t => t.2.toC * character (certKeyFun n t.1) θ).sum =
      u * (2 ^ sc / 2 ^ P2) * intEval n ts θ
  | [], r, h => by
    simp only [dyadicTermsAux, Option.some.injEq] at h
    subst h
    simp [intEval_nil]
  | t :: ts, r, h => by
    simp only [dyadicTermsAux] at h
    split at h
    · rename_i v r' hv hr
      simp only [Option.some.injEq] at h
      subst h
      rw [List.map_cons, List.sum_cons, dyadicTermsAux_sound hp θ ts hr, intEval_cons, hp,
        ofDyadicScaled_sound hv]
      push_cast
      ring
    · simp at h

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
  (dyadicTermsAux (2 * P) rr.scale (fun v => ⟨v, ofInt 0⟩) pRR.1).bind fun tRR =>
  (dyadicTermsAux (2 * P) ii.scale (fun v => ⟨v, ofInt 0⟩)
    (pII.1.map fun t => (t.1, -t.2))).bind fun tII =>
  (dyadicTermsAux (2 * P) ri.scale (fun v => ⟨ofInt 0, v⟩) pRI.1).bind fun tRI =>
  (dyadicTermsAux (2 * P) ir.scale (fun v => ⟨ofInt 0, v⟩) pIR.1).bind fun tIR =>
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
  have eRR := dyadicTermsAux_sound hre θ _ htRR
  have eII := dyadicTermsAux_sound hre θ _ htII
  have eRI := dyadicTermsAux_sound him θ _ htRI
  have eIR := dyadicTermsAux_sound him θ _ htIR
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
