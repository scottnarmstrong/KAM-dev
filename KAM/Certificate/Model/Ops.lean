/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Model.Terms
public import KAM.Certificate.Arith.PiEnclosure
public import KAM.Strip.Averages

/-!
# The Fourier model algebra

Operations on Fourier models `(2π)^deg (P + T)`, `sup_{T_ρ} |T| ≤ rad`, each with its enclosure
contract:

* `CertModel.add` (same degree): the sorted merge of the two polynomials, the rounding of every
  merged coefficient paid at its weight;
* `CertModel.mul`: the polynomial product by one of three routes, chosen in this order:
  a constant factor (every key zero, including the zero polynomial) is a SCALAR multiplication of
  the other factor (never a packed product, SO-ADVCOUNT lever 1); otherwise the advice under the
  product's key in `cfg.advice` (`packed`: SO-POLY-B's advice-checked `CertPoly.mulPacked`, whose
  zero real or imaginary parts cost nothing; `direct`: the direct product). Product terms with
  `|k|₁ > cfg.cutoff` move into the radius at their weighted size, and the radius adds the cross
  terms `|P_a|_w r_b + |P_b|_w r_a + r_a r_b`. A missing key or a failed packed check gives the
  crude enclosure `⟨deg_a + deg_b, 0, (|P_a|_w + r_a)(|P_b|_w + r_b)⟩`, so the contract is
  unconditional;
* `CertModel.trim`: terms of weighted size `≤ eps` move into the radius;
* `CertModel.toDeg`: re-expression at another degree, with `(2π)^e` enclosed by the Machin
  bounds at the parameters of the validated `π` enclosure;
* `CertModel.ofDeriv`: the exact derivative `∂_j P` at degree `+1`, multipliers `i k_j`;
* `CertModel.Encloses.average`: the real-torus average is the zero coefficient up to the radius.

Weighted norms `|P|_w = Σ |c_k| w^{|k|₁}` leave out the factor `(2π)^deg`.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM CertArith

/-- Truncation/precision controls and the product advice (Revision 5: indexed by the backend
for the mantissa decoder). -/
structure ModelConfig (α : Type) where
  /-- keep only product terms with `|k|₁ ≤ cutoff` -/
  cutoff : ℕ
  /-- Taylor order and halvings of the REAL upper bounds `ratExpUp` (`exp(2B)`, `exp(B)`,
  `exp(η) - 1`); complex pins carry their own counts (`ExpWitness`, Revision 4) -/
  taylorN : ℕ
  halvings : ℕ
  /-- untrusted mantissa decoder (`CertFixed.toMant P` in production); every value it returns is
  re-verified by `mantCheck` -/
  toMant : ℕ → α → Option ℤ
  /-- the advice of every product of the stage this configuration drives (§B′) -/
  advice : AdviceBook

/-- The advice registered under a product key (the first entry with that key). -/
def adviceLookup (book : AdviceBook) (key : ProductKey) : Option ProductAdvice :=
  match book.find? (fun e => e.1 == key) with
  | some e => some e.2
  | none => none

section Defs

variable {α : Type} [CertArith α]

/-- The polynomial of a list of error terms (errors dropped). -/
def itemsPoly (L : List (ErrTerm α)) : CertPoly α := ⟨L.map fun t => (t.1, t.2.1)⟩

/-- Every key of the polynomial is zero (the zero polynomial included): a constant. -/
def CertPoly.isConst (P : CertPoly α) : Bool := P.terms.all fun t => t.1.all fun z => z == 0

def CertModel.add {α : Type} [CertArith α] (W : CertWeight) (a b : CertModel α) :
    CertModel α :=
  ⟨a.deg, itemsPoly (mergeErrTerms a.poly.toErrTerms b.poly.toErrTerms),
    upAdd (upAdd a.rad b.rad) (errRadius W (mergeErrTerms a.poly.toErrTerms b.poly.toErrTerms))⟩

/-- The polynomial product of two models' polynomials as error terms plus a sup-norm error:
scalar route for a constant factor, else by the advice at `key`; `none` if the key is missing or
the packed check fails. -/
def CertModel.polyProduct (W : CertWeight) (cfg : ModelConfig α) (key : ProductKey)
    (a b : CertPoly α) : Option (List (ErrTerm α) × α) :=
  if a.isConst then some (directItems a.terms b.terms, ofInt 0)
  else if b.isConst then some (directItems b.terms a.terms, ofInt 0)
  else
    match adviceLookup cfg.advice key with
    | some .direct => some (directItems a.terms b.terms, ofInt 0)
    | some (.packed P rr ii ri ir) =>
      match CertPoly.mulPacked cfg.toMant W P rr ii ri ir a b with
      | some out => some (out.1.toErrTerms, out.2)
      | none => none
    | none => none

/-- The cross term `n · r` rounded upward; `0` without evaluating `n` when `r` is exactly zero
(an exact factor does not pay for the other factor's weighted norm). -/
def crossUp (n r : α) : α := if beq r (ofInt 0) then ofInt 0 else upMul n r

/-- Model product (Revision 5). The polynomial part comes from `cfg.advice` at `key`:
`packed` ⇒ `CertPoly.mulPacked` (kernel: one multiplication per shard block pair); `direct` ⇒
the direct product. The radius adds the packed remainder and the cross terms
`sup|a| rad_b + sup|b| rad_a + rad_a rad_b`. A missing key or a failed packed check yields the
crude enclosure `⟨deg_a + deg_b, 0, sup|a| · sup|b|⟩` (sound; later margins then fail), so the
contract `CertModel.Encloses.mul` is unconditional and unchanged in meaning. -/
def CertModel.mul {α : Type} [CertArith α] (W : CertWeight) (cfg : ModelConfig α)
    (key : ProductKey) (a b : CertModel α) : CertModel α :=
  match CertModel.polyProduct W cfg key a.poly b.poly with
  | some out =>
    ⟨a.deg + b.deg, truncPoly cfg.cutoff out.1,
      upAdd (upAdd out.2 (errRadius W (out.1.map (truncErr cfg.cutoff))))
        (upAdd (upAdd (crossUp (a.poly.supNormUp W) b.rad) (crossUp (b.poly.supNormUp W) a.rad))
          (upMul a.rad b.rad))⟩
  | none =>
    ⟨a.deg + b.deg, ⟨[]⟩,
      upMul (upAdd (a.poly.supNormUp W) a.rad) (upAdd (b.poly.supNormUp W) b.rad)⟩

/-- A term is dropped by `trim` when its weighted size is at most `eps`. -/
def trimDrop (W : CertWeight) (eps : α) (t : CertKey × CC α) : Bool :=
  ble (weightTermUp W t.1 t.2.normUp) eps

/-- Drop terms of weighted size `≤ eps` into the radius (precision reduction). -/
def CertModel.trim {α : Type} [CertArith α] (W : CertWeight) (eps : α) (a : CertModel α) :
    CertModel α :=
  ⟨a.deg, ⟨a.poly.terms.filter fun t => !trimDrop W eps t⟩,
    upAdd a.rad (CertPoly.supNormUp W ⟨a.poly.terms.filter (trimDrop W eps)⟩)⟩

end Defs

/-- The product model has the sum of the factor degrees. -/
theorem CertModel.mul_deg {α : Type} [CertArith α] (W : CertWeight) (cfg : ModelConfig α)
    (key : ProductKey) (a b : CertModel α) :
    (CertModel.mul W cfg key a b).deg = a.deg + b.deg := by
  unfold CertModel.mul
  split <;> rfl

/-! ### Powers of `2π` from the Machin bounds -/

/-- A positive lower bound of `π`: the better of the Machin bound and `piLoQ`. -/
def piLowPos (k j : ℕ) : ℚ := max (piLowRat k j) piLoQ

/-- An upper bound of `π`: the better of the Machin bound and `piUpQ`. -/
def piUpMin (k j : ℕ) : ℚ := min (piUpRat k j) piUpQ

/-- A rational lower bound of `(2π)^e`. -/
def twoPiZpowLo (k j : ℕ) (e : ℤ) : ℚ :=
  if 0 ≤ e then (2 * piLowPos k j) ^ e.toNat else ((2 * piUpMin k j) ^ (-e).toNat)⁻¹

/-- A rational upper bound of `(2π)^e`. -/
def twoPiZpowHi (k j : ℕ) (e : ℤ) : ℚ :=
  if 0 ≤ e then (2 * piUpMin k j) ^ e.toNat else ((2 * piLowPos k j) ^ (-e).toNat)⁻¹

theorem twoPiZpow_mem (k j : ℕ) (e : ℤ) :
    (twoPiZpowLo k j e : ℝ) ≤ (2 * Real.pi) ^ e ∧ (2 * Real.pi) ^ e ≤ (twoPiZpowHi k j e : ℝ) := by
  have hlo : (piLowPos k j : ℝ) ≤ Real.pi := by
    unfold piLowPos
    push_cast
    exact max_le (piLowRat_lt_pi k j).le piLoQ_lt_pi.le
  have hup : Real.pi ≤ (piUpMin k j : ℝ) := by
    unfold piUpMin
    push_cast
    exact le_min (pi_lt_piUpRat k j).le pi_lt_piUpQ.le
  have hpos : (0 : ℝ) < piLowPos k j := by
    have : (0 : ℝ) < piLoQ := by norm_num [piLoQ]
    unfold piLowPos
    push_cast
    exact this.trans_le (le_max_right _ _)
  have h1 : 2 * (piLowPos k j : ℝ) ≤ 2 * Real.pi := by linarith
  have h2 : 2 * Real.pi ≤ 2 * (piUpMin k j : ℝ) := by linarith
  unfold twoPiZpowLo twoPiZpowHi
  split_ifs with he
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, e = m := ⟨e.toNat, by omega⟩
    simp only [Int.toNat_natCast, zpow_natCast]
    push_cast
    exact ⟨pow_le_pow_left₀ (by positivity) h1 m, pow_le_pow_left₀ (by positivity) h2 m⟩
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, e = -(m : ℤ) := ⟨(-e).toNat, by omega⟩
    simp only [neg_neg, Int.toNat_natCast, zpow_neg, zpow_natCast]
    push_cast
    exact ⟨inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h2 m),
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 m)⟩

section Defs2

variable {α : Type} [CertArith α]

/-- The terms of `s · P` (real backend scalar `s`), with their rounding errors. -/
def scaleItems (s : α) (P : CertPoly α) : List (ErrTerm α) :=
  P.terms.map fun t => (t.1, CC.scaleC s t.2, CC.scaleErrC s t.2)

/-- Re-express a model at another `2π`-degree (validated `π` enclosure `pe`). -/
def CertModel.toDeg {α : Type} [CertArith α] (W : CertWeight) (pe : PiEnclosure α) (d : ℤ)
    (a : CertModel α) : CertModel α :=
  if a.deg = d then a else
    let c : α := ofRatUp (twoPiZpowHi pe.machinK pe.machinJ (a.deg - d))
    let lo : α := ofRatDown (twoPiZpowLo pe.machinK pe.machinJ (a.deg - d))
    let r : α := upAdd (CertArith.add c (neg lo)) (addErr c (neg lo))
    ⟨d, itemsPoly (scaleItems c a.poly),
      upAdd (upMul c a.rad)
        (upAdd (upMul r (a.poly.supNormUp W)) (errRadius W (scaleItems c a.poly)))⟩

/-- The derivative term `i k_j c` of a term (`none` if `k_j = 0`), with its rounding error. -/
def derivItem (j : ℕ) (t : CertKey × CC α) : Option (ErrTerm α) :=
  if t.1.getD j 0 = 0 then none else
    some (t.1, ⟨neg (mul t.2.im (ofInt (t.1.getD j 0))), mul t.2.re (ofInt (t.1.getD j 0))⟩,
      upAdd (mulErr t.2.im (ofInt (t.1.getD j 0))) (mulErr t.2.re (ofInt (t.1.getD j 0))))

/-- The model of `∂_j P` for exact data `P` at degree `d`: coefficients `i k_j c_k` (backend
products, their errors in the radius) at degree `d + 1`. -/
def CertModel.ofDeriv {α : Type} [CertArith α] (W : CertWeight) (j : ℕ) (d : ℤ)
    (P : CertPoly α) : CertModel α :=
  ⟨d + 1, itemsPoly (P.terms.filterMap (derivItem j)),
    errRadius W (P.terms.filterMap (derivItem j))⟩

end Defs2

/-! ### Contracts -/

section Contracts

variable {α : Type} [CertArith α]

theorem itemsPoly_eval (n : ℕ) (L : List (ErrTerm α)) (θ : Fin n → ℂ) :
    (itemsPoly L).eval n θ = errTermsEval n L θ := by
  simp [itemsPoly, CertPoly.eval, errTermsEval, Function.comp_def]

theorem two_pi_zpow_ofReal (d : ℤ) :
    (2 * (Real.pi : ℂ)) ^ d = (((2 * Real.pi) ^ d : ℝ) : ℂ) := by
  push_cast; ring

theorem norm_two_pi_zpow (d : ℤ) : ‖(2 * (Real.pi : ℂ)) ^ d‖ = (2 * Real.pi) ^ d := by
  rw [two_pi_zpow_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

theorem CertModel.Encloses.rad_nonneg {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {m : CertModel α}
    {f : (Fin n → ℂ) → ℂ} (h : m.Encloses n ρ f) : 0 ≤ val m.rad := by
  have h0 : (0 : Fin n → ℂ) ∈ complexStrip n ρ := fun i => by simpa using hρ
  have := (norm_nonneg _).trans (h 0 h0)
  exact nonneg_of_mul_nonneg_right this (by positivity)

variable [LawfulCertArith α]

theorem crossUp_ge (n r : α) (hn : 0 ≤ val n) (hr : 0 ≤ val r) :
    val n * val r ≤ val (crossUp n r) := by
  unfold crossUp
  split_ifs with h
  · rw [LawfulCertArith.beq_sound _ _ h, LawfulCertArith.val_ofInt, Int.cast_zero, mul_zero]
  · exact LawfulCertArith.upMul_ge n r hn hr

theorem CertModel.Encloses.add {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) {a b : CertModel α}
    {f g : (Fin n → ℂ) → ℂ} (ha : a.Encloses n W.rho f) (hb : b.Encloses n W.rho g)
    (hdeg : a.deg = b.deg) : (CertModel.add W a b).Encloses n W.rho (f + g) := by
  intro θ hθ
  have hA := ha θ hθ
  have hB := hb θ hθ
  rw [← hdeg] at hB
  set L := mergeErrTerms a.poly.toErrTerms b.poly.toErrTerms
  have hm := mergeErrTerms_spec n θ a.poly.toErrTerms b.poly.toErrTerms
  rw [CertPoly.errTermsEval_toErrTerms, CertPoly.errTermsEval_toErrTerms,
    CertPoly.errTermsErr_toErrTerms, CertPoly.errTermsErr_toErrTerms] at hm
  have hr := errTermsErr_le_errRadius hW L hθ
  have u1 := LawfulCertArith.upAdd_ge a.rad b.rad
  have u2 := LawfulCertArith.upAdd_ge (upAdd a.rad b.rad) (errRadius W L)
  have hc : (0 : ℝ) < (2 * Real.pi) ^ a.deg := by positivity
  simp only [CertModel.add, itemsPoly_eval, Pi.add_apply]
  set C := (2 * (Real.pi : ℂ)) ^ a.deg
  have : f θ + g θ - C * errTermsEval n L θ = (f θ - C * a.poly.eval n θ) +
      (g θ - C * b.poly.eval n θ) +
      C * (a.poly.eval n θ + b.poly.eval n θ - errTermsEval n L θ) := by ring
  rw [this]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  rw [norm_mul, norm_two_pi_zpow]
  have h3 : (2 * Real.pi) ^ a.deg *
      ‖a.poly.eval n θ + b.poly.eval n θ - errTermsEval n L θ‖ ≤
      (2 * Real.pi) ^ a.deg * val (errRadius W L) :=
    mul_le_mul_of_nonneg_left (by simp at hm; linarith) hc.le
  have h4 : (2 * Real.pi) ^ a.deg * (val a.rad + val b.rad + val (errRadius W L)) ≤
      (2 * Real.pi) ^ a.deg * val (upAdd (upAdd a.rad b.rad) (errRadius W L)) :=
    mul_le_mul_of_nonneg_left (by linarith) hc.le
  nlinarith

/-- The real core of the product estimate. -/
theorem norm_mul_sub_le_core {X Y A B Q C D : ℂ} {c d ra rb na nb E : ℝ}
    (hC : ‖C‖ = c) (hD : ‖D‖ = d) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hX : ‖X - C * A‖ ≤ c * ra) (hY : ‖Y - D * B‖ ≤ d * rb) (hA : ‖A‖ ≤ na) (hB : ‖B‖ ≤ nb)
    (hQ : ‖A * B - Q‖ ≤ E) :
    ‖X * Y - C * D * Q‖ ≤ c * d * (E + (na * rb + nb * ra + ra * rb)) := by
  set u := X - C * A
  set v := Y - D * B
  have hra : 0 ≤ ‖u‖ := norm_nonneg _
  have : X * Y - C * D * Q =
      C * D * (A * B - Q) + C * A * v + D * B * u + u * v := by
    simp only [u, v]; ring
  rw [this]
  have n1 := norm_add_le (C * D * (A * B - Q) + C * A * v + D * B * u) (u * v)
  have n2 := norm_add_le (C * D * (A * B - Q) + C * A * v) (D * B * u)
  have n3 := norm_add_le (C * D * (A * B - Q)) (C * A * v)
  simp only [norm_mul, hC, hD] at n1 n2 n3
  have hu : ‖u‖ ≤ c * ra := hX
  have hv : ‖v‖ ≤ d * rb := hY
  have hA0 := norm_nonneg A
  have hB0 := norm_nonneg B
  have hv0 := norm_nonneg v
  have e1 : c * d * ‖A * B - Q‖ ≤ c * d * E := mul_le_mul_of_nonneg_left hQ (by positivity)
  have e2 : c * ‖A‖ * ‖v‖ ≤ c * na * (d * rb) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hA hc) hv hv0 (by nlinarith)
  have e3 : d * ‖B‖ * ‖u‖ ≤ d * nb * (c * ra) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hB hd) hu hra (by nlinarith)
  have e4 : ‖u‖ * ‖v‖ ≤ (c * ra) * (d * rb) :=
    mul_le_mul hu hv hv0 (hra.trans hu)
  nlinarith

theorem CertModel.polyProduct_sound {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) {cfg : ModelConfig α} {key : ProductKey}
    {a b : CertPoly α} {out : List (ErrTerm α) × α}
    (h : CertModel.polyProduct W cfg key a b = some out) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n W.rho) :
    ‖a.eval n θ * b.eval n θ - errTermsEval n out.1 θ‖ ≤ errTermsErr n out.1 θ + val out.2 := by
  have hdir : ∀ (p q : CertPoly α), ‖p.eval n θ * q.eval n θ -
      errTermsEval n (directItems p.terms q.terms) θ‖ ≤
      errTermsErr n (directItems p.terms q.terms) θ + val (ofInt 0 : α) := fun p q => by
    rw [LawfulCertArith.val_ofInt, Int.cast_zero, add_zero]
    exact directItems_spec n p.terms q.terms θ
  unfold CertModel.polyProduct at h
  split_ifs at h with ha hb
  · simp only [Option.some.injEq] at h; subst h; exact hdir a b
  · simp only [Option.some.injEq] at h; subst h
    rw [mul_comm]; exact hdir b a
  · split at h
    · simp only [Option.some.injEq] at h; subst h; exact hdir a b
    · split at h
      · rename_i o hmp
        simp only [Option.some.injEq] at h; subst h
        rw [CertPoly.errTermsEval_toErrTerms, CertPoly.errTermsErr_toErrTerms, zero_add]
        exact CertPoly.mulPacked_sound hW hmp θ hθ
      · simp at h
    · simp at h

theorem CertModel.Encloses.mul {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (cfg : ModelConfig α)
    (key : ProductKey) {a b : CertModel α} {f g : (Fin n → ℂ) → ℂ} (ha : a.Encloses n W.rho f)
    (hb : b.Encloses n W.rho g) : (CertModel.mul W cfg key a b).Encloses n W.rho (f * g) := by
  intro θ hθ
  have hρ := CertWeight.rho_pos hW
  have ra0 := ha.rad_nonneg hρ
  have rb0 := hb.rad_nonneg hρ
  have hA := a.poly.norm_eval_le_supNormUp hW hθ
  have hB := b.poly.norm_eval_le_supNormUp hW hθ
  have na0 := a.poly.supNormUp_nonneg hW
  have nb0 := b.poly.supNormUp_nonneg hW
  have hc : (0 : ℝ) < (2 * Real.pi) ^ a.deg := by positivity
  have hd : (0 : ℝ) < (2 * Real.pi) ^ b.deg := by positivity
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  have h2pi' : (2 * Real.pi) ≠ 0 := by positivity
  have hsplit : (2 * (Real.pi : ℂ)) ^ (a.deg + b.deg) =
      (2 * (Real.pi : ℂ)) ^ a.deg * (2 * (Real.pi : ℂ)) ^ b.deg := zpow_add₀ h2pi _ _
  have hsplitR : (2 * Real.pi) ^ (a.deg + b.deg) =
      (2 * Real.pi) ^ a.deg * (2 * Real.pi) ^ b.deg := zpow_add₀ h2pi' _ _
  have m1 := crossUp_ge (a.poly.supNormUp W) b.rad na0 rb0
  have m2 := crossUp_ge (b.poly.supNormUp W) a.rad nb0 ra0
  have m3 := LawfulCertArith.upMul_ge a.rad b.rad ra0 rb0
  have u1 := LawfulCertArith.upAdd_ge (crossUp (a.poly.supNormUp W) b.rad)
    (crossUp (b.poly.supNormUp W) a.rad)
  have u2 := LawfulCertArith.upAdd_ge (upAdd (crossUp (a.poly.supNormUp W) b.rad)
    (crossUp (b.poly.supNormUp W) a.rad)) (upMul a.rad b.rad)
  unfold CertModel.mul
  split
  · rename_i out hout
    have hP := CertModel.polyProduct_sound hW hout hθ
    have hT := truncPoly_spec n cfg.cutoff θ out.1
    have hR := errTermsErr_le_errRadius hW (out.1.map (truncErr cfg.cutoff)) hθ
    have hQ : ‖a.poly.eval n θ * b.poly.eval n θ - (truncPoly cfg.cutoff out.1).eval n θ‖ ≤
        val (upAdd out.2 (errRadius W (out.1.map (truncErr cfg.cutoff)))) := by
      have := norm_sub_le_norm_sub_add_norm_sub (a.poly.eval n θ * b.poly.eval n θ)
        (errTermsEval n out.1 θ) ((truncPoly cfg.cutoff out.1).eval n θ)
      have := LawfulCertArith.upAdd_ge out.2 (errRadius W (out.1.map (truncErr cfg.cutoff)))
      linarith
    have core := norm_mul_sub_le_core (norm_two_pi_zpow a.deg) (norm_two_pi_zpow b.deg)
      hc.le hd.le (ha θ hθ) (hb θ hθ) hA hB hQ
    simp only [Pi.mul_apply]
    rw [hsplit, hsplitR]
    refine core.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine le_trans ?_ (LawfulCertArith.upAdd_ge _ _)
    linarith
  · have hQ : ‖a.poly.eval n θ * b.poly.eval n θ - (⟨[]⟩ : CertPoly α).eval n θ‖ ≤
        val (a.poly.supNormUp W) * val (b.poly.supNormUp W) := by
      simp only [CertPoly.eval, List.map_nil, List.sum_nil, sub_zero, norm_mul]
      exact mul_le_mul hA hB (norm_nonneg _) na0
    have core := norm_mul_sub_le_core (norm_two_pi_zpow a.deg) (norm_two_pi_zpow b.deg)
      hc.le hd.le (ha θ hθ) (hb θ hθ) hA hB hQ
    have v1 := LawfulCertArith.upAdd_ge (a.poly.supNormUp W) a.rad
    have v2 := LawfulCertArith.upAdd_ge (b.poly.supNormUp W) b.rad
    have m4 := LawfulCertArith.upMul_ge (upAdd (a.poly.supNormUp W) a.rad)
      (upAdd (b.poly.supNormUp W) b.rad) (by linarith) (by linarith)
    simp only [Pi.mul_apply]
    rw [hsplit, hsplitR]
    refine core.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have : (val (a.poly.supNormUp W) + val a.rad) * (val (b.poly.supNormUp W) + val b.rad) ≤
        val (upAdd (a.poly.supNormUp W) a.rad) * val (upAdd (b.poly.supNormUp W) b.rad) :=
      mul_le_mul v1 v2 (by linarith) (by linarith)
    nlinarith

theorem CertModel.Encloses.trim {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (eps : α) {a : CertModel α}
    {f : (Fin n → ℂ) → ℂ} (ha : a.Encloses n W.rho f) :
    (CertModel.trim W eps a).Encloses n W.rho f := by
  intro θ hθ
  have hA := ha θ hθ
  have hsplit : a.poly.eval n θ = (⟨a.poly.terms.filter fun t => !trimDrop W eps t⟩ :
      CertPoly α).eval n θ + (⟨a.poly.terms.filter (trimDrop W eps)⟩ : CertPoly α).eval n θ := by
    simp only [CertPoly.eval]
    induction a.poly.terms with
    | nil => simp
    | cons t L ih =>
      by_cases ht : trimDrop W eps t = true
      · simp [ht, ih]; ring
      · simp [ht, ih]; ring
  have hD := (⟨a.poly.terms.filter (trimDrop W eps)⟩ : CertPoly α).norm_eval_le_supNormUp hW hθ
  have u := LawfulCertArith.upAdd_ge a.rad
    (CertPoly.supNormUp W ⟨a.poly.terms.filter (trimDrop W eps)⟩)
  have hc : (0 : ℝ) < (2 * Real.pi) ^ a.deg := by positivity
  simp only [CertModel.trim]
  rw [hsplit] at hA
  set C := (2 * (Real.pi : ℂ)) ^ a.deg
  set K := (⟨a.poly.terms.filter fun t => !trimDrop W eps t⟩ : CertPoly α).eval n θ
  set Dr := (⟨a.poly.terms.filter (trimDrop W eps)⟩ : CertPoly α).eval n θ
  have : f θ - C * K = (f θ - C * (K + Dr)) + C * Dr := by ring
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_two_pi_zpow]
  have := mul_le_mul_of_nonneg_left hD hc.le
  have := mul_le_mul_of_nonneg_left u hc.le
  nlinarith

theorem scaleItems_spec (n : ℕ) (c : α) (P : CertPoly α) (θ : Fin n → ℂ) :
    ‖(val c : ℂ) * P.eval n θ - errTermsEval n (scaleItems c P) θ‖ ≤
      errTermsErr n (scaleItems c P) θ := by
  obtain ⟨L⟩ := P
  simp only [scaleItems, CertPoly.eval]
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons, errTermsEval_cons, errTermsErr_cons]
    have e := CC.norm_scale_sub_scaleC c t.2
    have : (val c : ℂ) * (t.2.toC * character (certKeyFun n t.1) θ +
        (L.map fun t => t.2.toC * character (certKeyFun n t.1) θ).sum) -
        ((CC.scaleC c t.2).toC * character (certKeyFun n t.1) θ +
          errTermsEval n (L.map fun t => (t.1, CC.scaleC c t.2, CC.scaleErrC c t.2)) θ) =
        ((val c : ℂ) * t.2.toC - (CC.scaleC c t.2).toC) * character (certKeyFun n t.1) θ +
        ((val c : ℂ) * (L.map fun t => t.2.toC * character (certKeyFun n t.1) θ).sum -
          errTermsEval n (L.map fun t => (t.1, CC.scaleC c t.2, CC.scaleErrC c t.2)) θ) := by
      ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have := mul_le_mul_of_nonneg_right e (norm_nonneg (character (certKeyFun n t.1) θ))
    linarith

/-- The real core of the degree change. -/
theorem norm_toDeg_sub_le_core {F A Q : ℂ} {D X cv r N S ra : ℝ} (hD : 0 < D)
    (hX : X ≤ cv) (hr : cv - X ≤ r) (hra : 0 ≤ ra)
    (hA : ‖F - (D : ℂ) * (X : ℂ) * A‖ ≤ D * X * ra) (hN : ‖A‖ ≤ N)
    (hS : ‖(cv : ℂ) * A - Q‖ ≤ S) : ‖F - (D : ℂ) * Q‖ ≤ D * (cv * ra + (r * N + S)) := by
  have : F - (D : ℂ) * Q = (F - (D : ℂ) * (X : ℂ) * A) + (D : ℂ) * ((X : ℂ) - (cv : ℂ)) * A +
      (D : ℂ) * ((cv : ℂ) * A - Q) := by ring
  rw [this]
  have n1 := norm_add_le ((F - (D : ℂ) * (X : ℂ) * A) + (D : ℂ) * ((X : ℂ) - (cv : ℂ)) * A)
    ((D : ℂ) * ((cv : ℂ) * A - Q))
  have n2 := norm_add_le (F - (D : ℂ) * (X : ℂ) * A) ((D : ℂ) * ((X : ℂ) - (cv : ℂ)) * A)
  have hDn : ‖(D : ℂ)‖ = D := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
  have hXc : ‖(X : ℂ) - (cv : ℂ)‖ = cv - X := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  rw [norm_mul, norm_mul, hDn, hXc] at n2
  rw [norm_mul, hDn] at n1
  have k1 : D * (cv - X) * ‖A‖ ≤ D * (r * N) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hr hN (norm_nonneg _) (by linarith)) hD.le
  have k2 : D * ‖(cv : ℂ) * A - Q‖ ≤ D * S := mul_le_mul_of_nonneg_left hS hD.le
  have k3 : D * X * ra ≤ D * (cv * ra) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hX hra) hD.le
  nlinarith

theorem CertModel.Encloses.toDeg {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) (d : ℤ) {a : CertModel α} {f : (Fin n → ℂ) → ℂ}
    (ha : a.Encloses n W.rho f) : (CertModel.toDeg W pe d a).Encloses n W.rho f := by
  -- the Machin bounds at `pe`'s parameters hold unconditionally; the validated enclosure is
  -- recorded but not needed
  have _hπ := checkPiEnclosure_sound hpe
  unfold CertModel.toDeg
  split_ifs with hd
  · exact ha
  intro θ hθ
  dsimp only
  have hρ := CertWeight.rho_pos hW
  have ra0 := ha.rad_nonneg hρ
  obtain ⟨hlo, hhi⟩ := twoPiZpow_mem pe.machinK pe.machinJ (a.deg - d)
  set lo := twoPiZpowLo pe.machinK pe.machinJ (a.deg - d)
  set hi := twoPiZpowHi pe.machinK pe.machinJ (a.deg - d)
  set c : α := ofRatUp hi
  set Ld : α := ofRatDown lo
  set r : α := upAdd (CertArith.add c (neg Ld)) (addErr c (neg Ld))
  have hc := LawfulCertArith.ofRatUp_ge (α := α) hi
  have hL := LawfulCertArith.ofRatDown_le (α := α) lo
  have hx0 : (0 : ℝ) < (2 * Real.pi) ^ (a.deg - d) := by positivity
  have hcx : (2 * Real.pi) ^ (a.deg - d) ≤ val c := hhi.trans hc
  have hr : val c - (2 * Real.pi) ^ (a.deg - d) ≤ val r := by
    have e1 := LawfulCertArith.add_err c (neg Ld)
    have u := LawfulCertArith.upAdd_ge (CertArith.add c (neg Ld)) (addErr c (neg Ld))
    rw [LawfulCertArith.val_neg, abs_le] at e1
    have : val Ld ≤ (2 * Real.pi) ^ (a.deg - d) := hL.trans hlo
    linarith [e1.1]
  have hr0 : 0 ≤ val r := by linarith
  have hN := a.poly.norm_eval_le_supNormUp hW hθ
  have hN0 := a.poly.supNormUp_nonneg hW
  have hS := (scaleItems_spec n c a.poly θ).trans
    (errTermsErr_le_errRadius hW (scaleItems c a.poly) hθ)
  have m1 := LawfulCertArith.upMul_ge c a.rad (by linarith) ra0
  have m2 := LawfulCertArith.upMul_ge r (a.poly.supNormUp W) hr0 hN0
  have u1 := LawfulCertArith.upAdd_ge (upMul r (a.poly.supNormUp W)) (errRadius W
    (scaleItems c a.poly))
  have u2 := LawfulCertArith.upAdd_ge (upMul c a.rad) (upAdd (upMul r (a.poly.supNormUp W))
    (errRadius W (scaleItems c a.poly)))
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  have hCa : (2 * (Real.pi : ℂ)) ^ a.deg = (((2 * Real.pi) ^ d : ℝ) : ℂ) *
      (((2 * Real.pi) ^ (a.deg - d) : ℝ) : ℂ) := by
    rw [← two_pi_zpow_ofReal, ← two_pi_zpow_ofReal, ← zpow_add₀ h2pi]
    congr 1; ring
  have hRa : (2 * Real.pi) ^ a.deg = (2 * Real.pi) ^ d * (2 * Real.pi) ^ (a.deg - d) := by
    rw [← zpow_add₀ (by positivity : (2 * Real.pi) ≠ 0)]
    congr 1; ring
  have hA := ha θ hθ
  rw [hCa, hRa] at hA
  have core := norm_toDeg_sub_le_core (by positivity) hcx hr ra0 hA hN hS
  simp only [itemsPoly_eval]
  rw [two_pi_zpow_ofReal d]
  refine core.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have : val c * val a.rad + (val r * val (a.poly.supNormUp W) +
      val (errRadius W (scaleItems c a.poly))) ≤ val (upAdd (upMul c a.rad)
        (upAdd (upMul r (a.poly.supNormUp W)) (errRadius W (scaleItems c a.poly)))) := by
    linarith
  exact this

/-- The derivative coefficient `i k c` with its error bound. -/
theorem norm_deriv_coeff_sub (c : CC α) (k : ℤ) :
    ‖Complex.I * (k : ℂ) * c.toC -
        (⟨neg (mul c.im (ofInt k)), mul c.re (ofInt k)⟩ : CC α).toC‖ ≤
      val (upAdd (mulErr c.im (ofInt k)) (mulErr c.re (ofInt k))) := by
  have e1 := LawfulCertArith.mul_err c.im (ofInt (α := α) k)
  have e2 := LawfulCertArith.mul_err c.re (ofInt (α := α) k)
  have u := LawfulCertArith.upAdd_ge (mulErr c.im (ofInt (α := α) k)) (mulErr c.re (ofInt k))
  rw [LawfulCertArith.val_ofInt] at e1 e2
  have hre : (Complex.I * (k : ℂ) * c.toC -
      (⟨neg (mul c.im (ofInt k)), mul c.re (ofInt k)⟩ : CC α).toC).re =
      val (mul c.im (ofInt (α := α) k)) - val c.im * k := by
    simp [CC.toC, LawfulCertArith.val_neg]; ring
  have him : (Complex.I * (k : ℂ) * c.toC -
      (⟨neg (mul c.im (ofInt k)), mul c.re (ofInt k)⟩ : CC α).toC).im =
      -(val (mul c.re (ofInt (α := α) k)) - val c.re * k) := by
    simp [CC.toC]; ring
  refine (norm_le_of_re_im (A := val (mulErr c.im (ofInt (α := α) k)))
    (B := val (mulErr c.re (ofInt (α := α) k))) ?_ ?_).trans u
  · rw [hre]; exact e1
  · rw [him, abs_neg]; exact e2

theorem derivItems_spec {n : ℕ} (j : Fin n) (θ : Fin n → ℂ) :
    ∀ L : List (CertKey × CC α),
    ‖(L.map fun t => Complex.I * ((certKeyFun n t.1 j : ℤ) : ℂ) * t.2.toC *
        character (certKeyFun n t.1) θ).sum - errTermsEval n (L.filterMap (derivItem j.val)) θ‖ ≤
      errTermsErr n (L.filterMap (derivItem j.val)) θ
  | [] => by simp
  | t :: L => by
    have ih := derivItems_spec j θ L
    have hk : certKeyFun n t.1 j = t.1.getD j.val 0 := rfl
    by_cases h0 : t.1.getD j.val 0 = 0
    · have hnone : derivItem j.val t = none := by simp only [derivItem, h0, ↓reduceIte]
      rw [List.filterMap_cons_none hnone, List.map_cons, List.sum_cons, hk, h0]
      simpa using ih
    · have hsome : derivItem j.val t = some (t.1, ⟨neg (mul t.2.im (ofInt (t.1.getD j.val 0))),
          mul t.2.re (ofInt (t.1.getD j.val 0))⟩, upAdd (mulErr t.2.im (ofInt (t.1.getD j.val 0)))
            (mulErr t.2.re (ofInt (t.1.getD j.val 0)))) := by
        simp only [derivItem, h0, ↓reduceIte]
      rw [List.filterMap_cons_some hsome, List.map_cons,
        List.sum_cons, errTermsEval_cons, errTermsErr_cons]
      simp only
      have e := norm_deriv_coeff_sub t.2 (t.1.getD j.val 0)
      rw [hk]
      set χ := character (certKeyFun n t.1) θ
      have : Complex.I * ((t.1.getD j.val 0 : ℤ) : ℂ) * t.2.toC * χ +
          (L.map fun t => Complex.I * ((certKeyFun n t.1 j : ℤ) : ℂ) * t.2.toC *
            character (certKeyFun n t.1) θ).sum -
          ((⟨neg (mul t.2.im (ofInt (t.1.getD j.val 0))),
              mul t.2.re (ofInt (t.1.getD j.val 0))⟩ : CC α).toC * χ +
            errTermsEval n (L.filterMap (derivItem j.val)) θ) =
          (Complex.I * ((t.1.getD j.val 0 : ℤ) : ℂ) * t.2.toC -
            (⟨neg (mul t.2.im (ofInt (t.1.getD j.val 0))),
              mul t.2.re (ofInt (t.1.getD j.val 0))⟩ : CC α).toC) * χ +
          ((L.map fun t => Complex.I * ((certKeyFun n t.1 j : ℤ) : ℂ) * t.2.toC *
            character (certKeyFun n t.1) θ).sum -
            errTermsEval n (L.filterMap (derivItem j.val)) θ) := by ring
      rw [this]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have := mul_le_mul_of_nonneg_right e (norm_nonneg χ)
      linarith

omit [LawfulCertArith α] in
/-- The directional derivative of the evaluation of a term list. -/
theorem hasFDerivAt_termSum {n : ℕ} (j : Fin n) (θ : Fin n → ℂ) :
    ∀ L : List (CertKey × CC α), ∃ D : (Fin n → ℂ) →L[ℂ] ℂ,
      HasFDerivAt (fun θ => (L.map fun t => t.2.toC * character (certKeyFun n t.1) θ).sum) D θ ∧
      D (Pi.single j 1) = (2 * Real.pi) * (L.map fun t => Complex.I *
        ((certKeyFun n t.1 j : ℤ) : ℂ) * t.2.toC * character (certKeyFun n t.1) θ).sum
  | [] => ⟨0, by simpa using hasFDerivAt_const (0 : ℂ) θ, by simp⟩
  | t :: L => by
    obtain ⟨D, hD, hv⟩ := hasFDerivAt_termSum j θ L
    refine ⟨t.2.toC • fderiv ℂ (character (certKeyFun n t.1)) θ + D, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      exact (((differentiable_character _) θ).hasFDerivAt.const_mul t.2.toC).add hD
    · rw [_root_.add_apply, _root_.smul_apply, hv,
        fderiv_character_single, List.map_cons, List.sum_cons, smul_eq_mul]
      ring

theorem CertModel.Encloses.ofDeriv {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (j : Fin n) (d : ℤ)
    (P : CertPoly α) : (CertModel.ofDeriv W j.val d P).Encloses n W.rho
      (fun θ => (2 * (Real.pi : ℂ)) ^ d * fderiv ℂ (P.eval n) θ (Pi.single j 1)) := by
  intro θ hθ
  obtain ⟨D, hD, hv⟩ := hasFDerivAt_termSum j θ P.terms
  have hfd : fderiv ℂ (P.eval n) θ = D := hD.fderiv
  have hS := derivItems_spec j θ P.terms
  have hR := errTermsErr_le_errRadius hW (P.terms.filterMap (derivItem j.val)) hθ
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  simp only [CertModel.ofDeriv, itemsPoly_eval]
  rw [hfd, hv, zpow_add_one₀ h2pi, zpow_add_one₀ (by positivity : (2 * Real.pi) ≠ 0)]
  set S := (P.terms.map fun t => Complex.I * ((certKeyFun n t.1 j : ℤ) : ℂ) * t.2.toC *
    character (certKeyFun n t.1) θ).sum
  have : (2 * (Real.pi : ℂ)) ^ d * (2 * Real.pi * S) -
      (2 * (Real.pi : ℂ)) ^ d * (2 * Real.pi) *
        errTermsEval n (P.terms.filterMap (derivItem j.val)) θ =
      ((2 * (Real.pi : ℂ)) ^ d * (2 * Real.pi)) *
        (S - errTermsEval n (P.terms.filterMap (derivItem j.val)) θ) := by ring
  rw [this, norm_mul, norm_mul, norm_two_pi_zpow]
  have h2 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  rw [h2]
  exact mul_le_mul_of_nonneg_left (hS.trans hR) (by positivity)

omit [LawfulCertArith α] in
/-- The real-torus average of a polynomial is its zero coefficient. -/
theorem CertPoly.torusAverage_eval {n : ℕ} (P : CertPoly α) :
    torusAverage (fun x : Fin n → ℝ => P.eval n fun i => (x i : ℂ)) = P.coeff n 0 := by
  have hcont : ∀ Q : CertPoly α, Continuous fun x : Fin n → ℝ => Q.eval n fun i => (x i : ℂ) :=
    fun Q => (Q.differentiable_eval n).continuous.comp
      (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))
  rw [CertPoly.coeff_eq_sum]
  obtain ⟨L⟩ := P
  induction L with
  | nil => simp [CertPoly.eval, torusAverage]
  | cons t L ih =>
    have hsplit : (fun x : Fin n → ℝ => CertPoly.eval n ⟨t :: L⟩ fun i => (x i : ℂ)) =
        fun x => t.2.toC * character (certKeyFun n t.1) (fun i => (x i : ℂ)) +
          CertPoly.eval n ⟨L⟩ fun i => (x i : ℂ) := by
      funext x; simp [CertPoly.eval]
    have hc1 : Continuous fun x : Fin n → ℝ =>
        t.2.toC * character (certKeyFun n t.1) (fun i => (x i : ℂ)) :=
      continuous_const.mul ((differentiable_character _).continuous.comp
        (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)))
    rw [hsplit, torusAverage, MeasureTheory.integral_add (integrableOn_unitCube_of_continuous hc1)
      (integrableOn_unitCube_of_continuous (hcont ⟨L⟩)), MeasureTheory.integral_const_mul,
      ← torusAverage, ← torusAverage, torusAverage_character, ih]
    simp only [List.map_cons, List.sum_cons]
    split_ifs <;> simp

/-- The real-torus average of an enclosed function is the zero coefficient up to the radius. -/
theorem CertModel.Encloses.average {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {ρ : ℝ} (hρ : 0 < ρ) {a : CertModel α} {f : (Fin n → ℂ) → ℂ} (ha : a.Encloses n ρ f)
    (hf : ContinuousOn f (complexStrip n ρ)) :
    ‖torusAverage (fun x : Fin n → ℝ => f fun i => (x i : ℂ)) -
        (2 * (Real.pi : ℂ)) ^ a.deg * a.poly.coeff n 0‖ ≤ (2 * Real.pi) ^ a.deg * val a.rad := by
  have hemb : Continuous fun x : Fin n → ℝ => fun i => (x i : ℂ) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  have hfc : Continuous fun x : Fin n → ℝ => f fun i => (x i : ℂ) :=
    hf.comp_continuous hemb fun x => ofReal_mem_complexStrip hρ x
  have hpc : Continuous fun x : Fin n → ℝ =>
      (2 * (Real.pi : ℂ)) ^ a.deg * a.poly.eval n fun i => (x i : ℂ) :=
    continuous_const.mul ((a.poly.differentiable_eval n).continuous.comp hemb)
  have havg : torusAverage (fun x : Fin n → ℝ => f fun i => (x i : ℂ)) -
      (2 * (Real.pi : ℂ)) ^ a.deg * a.poly.coeff n 0 =
      torusAverage (fun x : Fin n → ℝ => (f fun i => (x i : ℂ)) -
        (2 * (Real.pi : ℂ)) ^ a.deg * a.poly.eval n fun i => (x i : ℂ)) := by
    rw [← CertPoly.torusAverage_eval, torusAverage, torusAverage, torusAverage,
      MeasureTheory.integral_sub (integrableOn_unitCube_of_continuous hfc)
        (integrableOn_unitCube_of_continuous hpc), MeasureTheory.integral_const_mul]
  rw [havg]
  exact norm_torusAverage_le fun x _ => ha _ (ofReal_mem_complexStrip hρ x)

end Contracts

end KAM.Certificate
