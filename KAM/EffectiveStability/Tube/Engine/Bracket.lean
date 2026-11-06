/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.LitCert
public import KAM.EffectiveStability.Tube.Engine.Regroup

/-!
# The kept bracket coefficients (T2-CONF, N7)

The bracket of a literal observable `f = Σ_{(s, F_s) ∈ Fl} u^s F_s` (sparse models, `g`) and a
model `h = Σ_{t ∈ Hl} u^t H_t` (literals, `k`). For one monomial `p`, the coefficient
`G_p(φ) = Σ_{mon b = p} coef b · val b φ` is a sum of products `F_s · ∂_a H_t` and `∂_a F_s · H_t`
whose terms cancel to about `10⁻¹⁰` of their sizes, so it is computed exactly in one sum.

All operands are literals (`BrD`): certified copies `FL` of the sparse models, derivative literals
`dFL`, `dHL` read with the digit width `Pd.b` (certificates `fCheck`, `dCheck`, collected in
`BrD.Ok`), and the `H_t`. For a list of terms the kernel forms the operands (`brA`, `brB`), the
common scale `brQ` (the rational gcd of the `coef q_A q_B`), the exact `X = Σ c_b Z_A Z_B`
(`prodCheck` with zero errors, slot bound `brBX`) and bounds
`sup |Σ coef b · val b| ≤ |Q| l1P X ≤ G` (`brCheckL`, `brl_sound`). The terms of a monomial are
`brList` (`Regroup`); `brAll_sound`: `|G_p(φ)| ≤ G_p` for all `|p| ≤ L`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.Certificate KAM.CertificateSharp.Packed

/-- The bracket terms of a sparse observable and a literal model. -/
abbrev BrT := BT ((ℕ × ℕ × ℕ) × SpD) (ℕ × ℕ × ℕ)

/-- The `u`-monomial of an observable entry. -/
def muF (i : (ℕ × ℕ × ℕ) × SpD) : Fin 3 → ℕ := monOf i.1

/-- The sparse model of the `F`-side of a term (`∂_a F_s` for `kind`, else `F_s`; used by the
bound of the dropped terms, `Drop`). -/
def brSp (b : BrT) : SpD := if b.kind then b.i.2.deriv b.a else b.i.2

/-- The literal data of the bracket stage: the packing of plain literals `Pb` and of derivative
literals `Pd` (same width and stride), the literal copies of the observable entries and their
derivatives, the `H_t` and their derivatives. -/
structure BrD where
  Pb : Prm
  Pd : Prm
  FL : (ℕ × ℕ × ℕ) × SpD → LitD
  dFL : (ℕ × ℕ × ℕ) × SpD → Fin 2 → LitD
  HL : ℕ × ℕ × ℕ → LitD
  dHL : ℕ × ℕ × ℕ → Fin 2 → LitD

/-- The certificates of the literal data for the entries `Fl` and the monomials `Hl`. -/
structure BrD.Ok (D : BrD) (Fl : List ((ℕ × ℕ × ℕ) × SpD)) (Hl : List (ℕ × ℕ × ℕ)) : Prop where
  hb : 1 ≤ D.Pb.b
  hbd : 1 ≤ D.Pd.b
  hw : D.Pd.w = D.Pb.w
  hS : D.Pd.S = D.Pb.S
  fok : ∀ i ∈ Fl, (D.FL i).ok D.Pb = true
  fl : ∀ i ∈ Fl, litList (D.FL i).C D.Pb.S D.Pb.b (D.FL i).X = i.2.list D.Pb.S ∧
    (D.FL i).C = i.2.C ∧ (D.FL i).par = i.2.par ∧ (D.FL i).q = i.2.q
  dfok : ∀ i ∈ Fl, ∀ a, (D.dFL i a).ok D.Pd = true
  dfl : ∀ i ∈ Fl, ∀ a, litList (D.dFL i a).C D.Pd.S D.Pd.b (D.dFL i a).X =
      dlist (Layout.key (D.FL i).C D.Pb.S) a (D.FL i).par
        (litList (D.FL i).C D.Pb.S D.Pb.b (D.FL i).X) ∧
    (D.dFL i a).C = (D.FL i).C ∧ (D.dFL i a).par = !(D.FL i).par ∧ (D.dFL i a).q = (D.FL i).q
  hok : ∀ t ∈ Hl, (D.HL t).ok D.Pb = true ∧
    symDigOk (D.HL t).par (D.HL t).C D.Pb.b (D.HL t).X = true
  dhok : ∀ t ∈ Hl, ∀ a, (D.dHL t a).ok D.Pd = true
  dhl : ∀ t ∈ Hl, ∀ a, litList (D.dHL t a).C D.Pd.S D.Pd.b (D.dHL t a).X =
      dlist (Layout.key (D.HL t).C D.Pb.S) a (D.HL t).par
        (litList (D.HL t).C D.Pb.S D.Pb.b (D.HL t).X) ∧
    (D.dHL t a).C = (D.HL t).C ∧ (D.dHL t a).par = !(D.HL t).par ∧ (D.dHL t a).q = (D.HL t).q

/-- The observable operand (`∂_a F_s` for `kind`, else `F_s`). -/
def brA (D : BrD) (b : BrT) : Opd :=
  if b.kind then (D.dFL b.i b.a).opd D.Pd else (D.FL b.i).opd D.Pb

/-- The model operand (`H_t` for `kind`, else `∂_a H_t`). -/
def brB (D : BrD) (b : BrT) : Opd :=
  if b.kind then (D.HL b.e).opd D.Pb else (D.dHL b.e b.a).opd D.Pd

/-- The slot bound of the observable operand. -/
def brMxA (D : BrD) (b : BrT) : ℕ := if b.kind then 2 ^ (D.Pd.b - 1) else 2 ^ (D.Pb.b - 1)

/-- The slot bound of the model operand. -/
def brMxB (D : BrD) (b : BrT) : ℕ := if b.kind then 2 ^ (D.Pb.b - 1) else 2 ^ (D.Pd.b - 1)

/-- The product term of a bracket term (zero errors). -/
def brTerm (D : BrD) (Q : ℚ) (b : BrT) : Term :=
  ⟨((b.coef muF monOf : ℚ) * (brA D b).q * (brB D b).q *
      psgn ((brA D b).par && (brB D b).par) / Q).num, 0, (b.coef muF monOf : ℚ),
    brA D b, brB D b, 0, 0, Layout.len (brA D b).C D.Pb.S * brMxA D b, 0, 0,
    Layout.len (brB D b).C D.Pb.S * brMxB D b, brMxB D b, (0, 0, 0)⟩

/-- The packed sum `Σ c 2^sh Z_A Z_B` of a term list (kernel). -/
def brX (ts : List Term) : ℤ := (ts.map fun t => t.c * 2 ^ t.sh * (t.A.Z * t.B.Z)).sum

/-- The rational gcd of two rationals (of their absolute values). -/
def ratGcd (x y : ℚ) : ℚ := (Nat.gcd x.num.natAbs y.num.natAbs : ℚ) / (Nat.lcm x.den y.den : ℚ)

/-- The common scale of a term list: the rational gcd of the `coef q_A q_B` (`1` for none). -/
def brQ (D : BrD) (bl : List BrT) : ℚ :=
  match bl.map (fun b => (b.coef muF monOf : ℚ) * (brA D b).q * (brB D b).q) with
  | [] => 1
  | x :: xs => xs.foldl ratGcd |x|

/-- The product terms of a term list. -/
def brTs (D : BrD) (bl : List BrT) : List Term := bl.map (brTerm D (brQ D bl))

/-- The slot bound of a term list. -/
def brBX (D : BrD) (bl : List BrT) : ℕ := ((brTs D bl).map Term.slotB).sum

/-- **The kernel check of a list of bracket terms** against a claimed bound `G` (load level
`w - 16` for every list, so the masks of the packed `ℓ¹` are shared). -/
def brCheckL (D : BrD) (Ca Cb : ℕ) (pp : Bool) (bl : List BrT) (G : ℚ) : Bool :=
  if bl.isEmpty then decide (0 ≤ G) else
  prodCheck D.Pb.S Ca Cb pp (brQ D bl) (brTs D bl) 0 0 (brBX D bl) &&
    decide (2 * brBX D bl < 2 ^ D.Pb.w) &&
    l1Ok D.Pb.w (Layout.len (Ca + Cb) D.Pb.S) (D.Pb.w - 16) (brX (brTs D bl)) &&
    decide (|brQ D bl| * (l1P D.Pb.w (Layout.len (Ca + Cb) D.Pb.S) (D.Pb.w - 16)
      (brX (brTs D bl)) : ℚ) ≤ G)

/-- The observable value of an entry. -/
noncomputable def brG (w₀ : ℕ) (S : ℕ) (i : (ℕ × ℕ × ℕ) × SpD) : (Fin 2 → ℝ) → ℝ :=
  (i.2.opd w₀ S).eval S

theorem BrD.evalA_false {D : BrD} {Fl Hl} (hD : D.Ok Fl Hl) {i : (ℕ × ℕ × ℕ) × SpD} (hi : i ∈ Fl)
    (w₀ : ℕ) : ((D.FL i).opd D.Pb).eval D.Pb.S = brG w₀ D.Pb.S i := by
  obtain ⟨hl, hC, hpar, hq⟩ := hD.fl i hi
  funext φ
  simp only [Opd.eval, LitD.opd, brG, SpD.opd]
  rw [hl, hC, hpar, hq]

theorem BrD.evalA_true {D : BrD} {Fl Hl} (hD : D.Ok Fl Hl) {i : (ℕ × ℕ × ℕ) × SpD} (hi : i ∈ Fl)
    (w₀ : ℕ) (a : Fin 2) (φ : Fin 2 → ℝ) :
    ((D.dFL i a).opd D.Pd).eval D.Pd.S φ = pderiv (brG w₀ D.Pb.S i) φ a := by
  obtain ⟨hl, hC, hpar, hq⟩ := hD.dfl i hi a
  rw [← BrD.evalA_false hD hi w₀,
    show ((D.FL i).opd D.Pb).eval D.Pb.S = fun φ => ((D.FL i).q : ℝ) *
      evalK (Layout.key (D.FL i).C D.Pb.S) (D.FL i).par
        (litList (D.FL i).C D.Pb.S D.Pb.b (D.FL i).X) φ from rfl,
    C1Close.pderiv_const_mul (differentiable_evalK _ _ _), pderiv_evalK]
  simp only [Opd.eval, LitD.opd]
  rw [hl, hC, hpar, hq, hD.hS]

theorem BrD.evalB_false {D : BrD} {Fl Hl} (hD : D.Ok Fl Hl) {t : ℕ × ℕ × ℕ} (ht : t ∈ Hl)
    (a : Fin 2) (φ : Fin 2 → ℝ) :
    ((D.dHL t a).opd D.Pd).eval D.Pd.S φ = pderiv (((D.HL t).opd D.Pb).eval D.Pb.S) φ a := by
  obtain ⟨hl, hC, hpar, hq⟩ := hD.dhl t ht a
  rw [show ((D.HL t).opd D.Pb).eval D.Pb.S = fun φ => ((D.HL t).q : ℝ) *
      evalK (Layout.key (D.HL t).C D.Pb.S) (D.HL t).par
        (litList (D.HL t).C D.Pb.S D.Pb.b (D.HL t).X) φ from rfl,
    C1Close.pderiv_const_mul (differentiable_evalK _ _ _), pderiv_evalK]
  simp only [Opd.eval, LitD.opd]
  rw [hl, hC, hpar, hq, hD.hS]

theorem LitD.opd_eval_congr {P P' : Prm} (hS : P.S = P'.S) (hb : P.b = P'.b) (d : LitD) :
    (d.opd P).eval P.S = (d.opd P').eval P'.S := by
  funext φ
  simp only [Opd.eval, LitD.opd, hS, hb]

/-- **Soundness of a checked list of bracket terms.** -/
theorem brl_sound {D : BrD} {Ca Cb : ℕ} {pp : Bool} {Fl : List ((ℕ × ℕ × ℕ) × SpD)}
    {Hl : List (ℕ × ℕ × ℕ)} {bl : List BrT} {G : ℚ} {P0 : Prm}
    (hchk : brCheckL D Ca Cb pp bl G = true) (hmem : ∀ b ∈ bl, b.i ∈ Fl ∧ b.e ∈ Hl)
    (hD : D.Ok Fl Hl) (w₀ : ℕ) (hS0 : P0.S = D.Pb.S) (hb0 : P0.b = D.Pb.b) (φ : Fin 2 → ℝ) :
    |(bl.map fun b => (b.coef muF monOf : ℝ) * b.val (brG w₀ D.Pb.S)
        (fun t => ((D.HL t).opd P0).eval P0.S) φ).sum| ≤ G := by
  set k : ℕ × ℕ × ℕ → (Fin 2 → ℝ) → ℝ := fun t => ((D.HL t).opd P0).eval P0.S with hk
  by_cases hbl : bl = []
  · subst hbl
    simp only [brCheckL, List.isEmpty_nil, ite_true, decide_eq_true_eq] at hchk
    simp only [List.map_nil, List.sum_nil, abs_zero]
    exact_mod_cast hchk
  have hne : bl.isEmpty = false := by simpa using hbl
  simp only [brCheckL, hne, Bool.false_eq_true, ite_false, Bool.and_eq_true,
    decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨hprod, hBX⟩, hl1⟩, hG⟩ := hchk
  set Q := brQ D bl with hQ
  set BX := brBX D bl with hBXd
  set ts := brTs D bl with hts
  have hS := hD.hS
  have hA : ∀ t ∈ ts, t.A.Cert D.Pb.w D.Pb.S (fun φ => t.A.eval D.Pb.S φ) t.ea₀ t.ea₁ t.na := by
    intro t ht
    obtain ⟨b, hb', rfl⟩ := List.mem_map.mp ht
    have hi := (hmem b hb').1
    have hwf : (brA D b).WF D.Pb.w D.Pb.S := by
      unfold brA; split_ifs
      · have := LitD.wf (hD.dfok _ hi b.a); rwa [hD.hw, hS] at this
      · exact LitD.wf (hD.fok _ hi)
    have hmx : (brA D b).Mx (brMxA D b) := by
      unfold brA brMxA; split_ifs
      · exact LitD.mx hD.hbd
      · exact LitD.mx hD.hb
    refine ⟨hwf, ?_, ?_⟩
    · simp only [brTerm, Rat.cast_zero]
      exact C1Close.refl (Opd.differentiable_eval _ _)
    · have := l1_le_of_mx hmx
      have hlen : (brA D b).l.length = Layout.len (brA D b).C D.Pb.S := by
        unfold brA; split_ifs
        · simp only [LitD.opd, length_litList, hS]
        · simp only [LitD.opd, length_litList]
      rw [hlen] at this
      simp only [brTerm]
      push_cast
      exact this
  have hB : ∀ t ∈ ts, t.B.Cert D.Pb.w D.Pb.S (fun φ => t.B.eval D.Pb.S φ) t.eb₀ t.eb₁ t.nb ∧
      t.B.Mx t.mxb ∧ symOk t.B.par t.B.l = true ∧ t.B.l.length = Layout.len t.B.C D.Pb.S := by
    intro t ht
    obtain ⟨b, hb', rfl⟩ := List.mem_map.mp ht
    have he := (hmem b hb').2
    obtain ⟨hok, hsym⟩ := hD.hok _ he
    have hKS : 2 * (D.HL b.e).C + 1 ≤ D.Pb.S := by
      simp only [LitD.ok, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1.1.2
    have hwfH := LitD.wf hok
    obtain ⟨hsH, hlH⟩ := LitD.sym hD.hb hKS hsym
    have hwf : (brB D b).WF D.Pb.w D.Pb.S := by
      unfold brB; split_ifs
      · exact hwfH
      · have := LitD.wf (hD.dhok _ he b.a); rwa [hD.hw, hS] at this
    have hmx : (brB D b).Mx (brMxB D b) := by
      unfold brB brMxB; split_ifs
      · exact LitD.mx hD.hb
      · exact LitD.mx hD.hbd
    have hsl : symOk (brB D b).par (brB D b).l = true ∧
        (brB D b).l.length = Layout.len (brB D b).C D.Pb.S := by
      unfold brB; split_ifs
      · exact ⟨hsH, hlH⟩
      · obtain ⟨hl, hC, hpar, -⟩ := hD.dhl _ he b.a
        simp only [LitD.opd]
        rw [hl, hC, hpar]
        exact ⟨symOk_dlist (C := (D.HL b.e).C) (by omega) hsH hwfH.cols hlH b.a, by
          rw [length_dlist]; exact hlH⟩
    refine ⟨⟨hwf, ?_, ?_⟩, hmx, hsl⟩
    · simp only [brTerm, Rat.cast_zero]
      exact C1Close.refl (Opd.differentiable_eval _ _)
    have := l1_le_of_mx hmx
    rw [hsl.2] at this
    simp only [brTerm]
    push_cast
    exact this
  obtain ⟨hclose, hpack, -, hlen, hslot⟩ := prod_sound hprod (fun t => t.A.eval D.Pb.S)
    (fun t => t.B.eval D.Pb.S) hA hB
  -- the model identity
  have hval : (bl.map fun b => (b.coef muF monOf : ℝ) * b.val (brG w₀ D.Pb.S) k φ).sum =
      (ts.map fun t => (t.ρ : ℝ) * (t.A.eval D.Pb.S φ * t.B.eval D.Pb.S φ)).sum := by
    rw [hts, brTs, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun b hb' => ?_)
    have hi := (hmem b hb').1
    have he := (hmem b hb').2
    have hkeq : k = fun t => ((D.HL t).opd D.Pb).eval D.Pb.S :=
      funext fun t => LitD.opd_eval_congr hS0 hb0 (D.HL t)
    simp only [Function.comp_apply, brTerm, BT.val, brA, brB]
    push_cast
    rw [hkeq]
    cases hkind : b.kind
    · simp only [Bool.false_eq_true, ite_false]
      rw [← BrD.evalA_false hD hi w₀, ← hS, BrD.evalB_false hD he b.a φ, hS]
    · simp only [ite_true]
      rw [← hS, BrD.evalA_true hD hi w₀ b.a φ, hS]
  rw [hval]
  have heq := hclose.abs_sub_le φ
  have hle : |(ts.map fun t => (t.ρ : ℝ) * (t.A.eval D.Pb.S φ * t.B.eval D.Pb.S φ)).sum| ≤
      |(Q : ℝ)| * l1 (Term.comb ts) := by
    have h0 : (ts.map fun t => (t.ρ : ℝ) * (t.A.eval D.Pb.S φ * t.B.eval D.Pb.S φ)).sum =
        (Q : ℝ) * evalK (Layout.key (Ca + Cb) D.Pb.S) pp (Term.comb ts) φ := by
      have h1 : (ts.map fun t => (t.ρ : ℝ) * (t.A.eval D.Pb.S φ * t.B.eval D.Pb.S φ)).sum -
          (Q : ℝ) * evalK (Layout.key (Ca + Cb) D.Pb.S) pp (Term.comb ts) φ = 0 := by
        simpa using heq
      linarith
    rw [h0, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_evalK_le _ _ _ _) (abs_nonneg _)
  refine hle.trans ?_
  have hsb : SlotsBounded D.Pb.w (Term.comb ts) := fun c hc => by
    have := hslot c hc
    have h2 : ((2 * BX : ℕ) : ℤ) < ((2 ^ D.Pb.w : ℕ) : ℤ) := by exact_mod_cast hBX
    push_cast at h2
    linarith
  have hl1eq := l1P_eq_of_le hl1 hpack hlen hsb
  have hG' : ((|Q| * (l1P D.Pb.w (Layout.len (Ca + Cb) D.Pb.S) (D.Pb.w - 16) (brX ts) : ℚ) : ℚ) :
      ℝ) ≤ (G : ℝ) := by exact_mod_cast hG
  push_cast at hG'
  have hl1R : ((l1P D.Pb.w (Layout.len (Ca + Cb) D.Pb.S) (D.Pb.w - 16) (brX ts) : ℕ) : ℝ) =
      (l1 (Term.comb ts) : ℝ) := by exact_mod_cast hl1eq
  rw [← hl1R]
  exact hG'

/-! ### One monomial, all monomials -/

/-- **The kernel check of one kept coefficient.** -/
def brCheck (D : BrD) (Ca Cb : ℕ) (pp : Bool) (Fl : List ((ℕ × ℕ × ℕ) × SpD))
    (inH : ℕ × ℕ × ℕ → Bool) (p : ℕ × ℕ × ℕ) (G : ℚ) : Bool :=
  brCheckL D Ca Cb pp (brList Fl muF inH p) G

theorem mem_brList {Fl : List ((ℕ × ℕ × ℕ) × SpD)} {inH : ℕ × ℕ × ℕ → Bool} {p : ℕ × ℕ × ℕ}
    {b : BrT} (hb : b ∈ brList Fl muF inH p) : b.i ∈ Fl ∧ inH b.e = true := by
  simp only [brList, List.mem_flatMap] at hb
  obtain ⟨a, -, i, hi, kind, -, sh, -, hb⟩ := hb
  split_ifs at hb with hk
  · rw [List.mem_singleton] at hb
    subst hb
    simp only [brKeep, Bool.and_eq_true] at hk
    exact ⟨hi, hk.1.2⟩
  · simp at hb

/-- The triples of total degree `≤ L` (graded by the first entry). -/
def monsUpTo (L : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range (L + 1)).flatMap fun a => (List.range (L + 1 - a)).flatMap fun b =>
    (List.range (L + 1 - a - b)).map fun c => (a, b, c)

theorem mem_monsUpTo {L : ℕ} {t : ℕ × ℕ × ℕ} : t ∈ monsUpTo L ↔ t.1 + t.2.1 + t.2.2 ≤ L := by
  obtain ⟨a, b, c⟩ := t
  simp only [monsUpTo, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a', ha, b', hb, c', hc, rfl, rfl, rfl⟩
    omega
  · intro h
    exact ⟨a, by omega, b, by omega, c, by omega, rfl, rfl, rfl⟩

theorem monOf_triple (p : Fin 3 → ℕ) : monOf (p 0, p 1, p 2) = p := by
  funext k
  fin_cases k <;> simp [monOf]

/-- **All kept coefficients**: one `brCheck` per triple of degree `≤ L`. -/
theorem brAll_sound {D : BrD} {Ca Cb : ℕ} {pp : Bool} {Fl : List ((ℕ × ℕ × ℕ) × SpD)}
    {Hl : List (ℕ × ℕ × ℕ)} {inH : ℕ × ℕ × ℕ → Bool} {L : ℕ} {G : ℕ × ℕ × ℕ → ℚ} {P0 : Prm}
    (hall : ∀ t ∈ monsUpTo L, brCheck D Ca Cb pp Fl inH t (G t) = true)
    (hnd : Hl.Nodup) (hin : ∀ t, inH t = true ↔ t ∈ Hl) (hD : D.Ok Fl Hl)
    (w₀ : ℕ) (hS0 : P0.S = D.Pb.S) (hb0 : P0.b = D.Pb.b) (p : Fin 3 → ℕ) (hp : mdeg p ≤ L)
    (φ : Fin 2 → ℝ) :
    |(((bterms Fl Hl).filter fun b => decide (b.mon muF monOf = p)).map
      (fun b => (b.coef muF monOf : ℝ) * b.val (fun i => (i.2.opd w₀ D.Pb.S).eval D.Pb.S)
        (fun t => ((D.HL t).opd P0).eval P0.S) φ)).sum| ≤ G (p 0, p 1, p 2) := by
  have hmem : (p 0, p 1, p 2) ∈ monsUpTo L := by
    rw [mem_monsUpTo]
    simpa [mdeg, Fin.sum_univ_three] using hp
  have h := brl_sound (hall _ hmem) (fun b hb => ⟨(mem_brList hb).1, (hin _).1 (mem_brList hb).2⟩)
    hD w₀ hS0 hb0 φ
  rw [← sum_filter_mon Fl muF hnd hin _ (fun b hb => by rw [hb]; simp), monOf_triple] at h
  exact h

/-! ### The certificates from kernel checks -/

/-- A list is checked in chunks of `m`. -/
theorem all_of_chunks {α : Type*} (l : List α) (f : α → Bool) {m n : ℕ} (hn : l.length ≤ m * n)
    (h : ∀ k < n, ((l.drop (m * k)).take m).all f = true) : l.all f = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, zero_mul] at hn; omega
    · exact h0
  have hk : i / m < n := by
    rw [Nat.div_lt_iff_lt_mul hm]; rw [mul_comm] at hn; omega
  have hc := List.all_eq_true.mp (h _ hk)
  have hr : i % m < m := Nat.mod_lt _ hm
  have hlen : i % m < ((l.drop (m * (i / m))).take m).length := by
    simp only [List.length_take, List.length_drop, lt_min_iff]
    have := Nat.div_add_mod i m
    omega
  have := hc _ (List.getElem_mem hlen)
  simp only [List.getElem_take, List.getElem_drop] at this
  simpa only [Nat.div_add_mod] using this

/-- **The certificates of the literal data** from the kernel checks at a narrow packing `Pc`, `Pcd`
(same stride and digit widths as `Pb`, `Pd`). -/
theorem BrD.ok_of {D : BrD} {Fl : List ((ℕ × ℕ × ℕ) × SpD)} {Hl : List (ℕ × ℕ × ℕ)} {Pc Pcd : Prm}
    (hcS : Pc.S = D.Pb.S) (hcb : Pc.b = D.Pb.b) (hcdS : Pcd.S = D.Pd.S) (hcdb : Pcd.b = D.Pd.b)
    (hb : 1 ≤ D.Pb.b) (hbd : 1 ≤ D.Pd.b) (hw : D.Pd.w = D.Pb.w) (hS : D.Pd.S = D.Pb.S)
    (hf : ∀ i ∈ Fl, ((D.FL i).ok D.Pb && fCheck Pc (D.FL i) i.2) = true)
    (hdf : ∀ i ∈ Fl, (([0, 1] : List (Fin 2)).all fun a =>
      (D.dFL i a).ok D.Pd && dCheck Pc Pcd (D.FL i) (D.dFL i a) a) = true)
    (hh : ∀ t ∈ Hl, ((D.HL t).ok D.Pb &&
      symDigOk (D.HL t).par (D.HL t).C D.Pb.b (D.HL t).X) = true)
    (hdh : ∀ t ∈ Hl, (([0, 1] : List (Fin 2)).all fun a =>
      (D.dHL t a).ok D.Pd && dCheck Pc Pcd (D.HL t) (D.dHL t a) a) = true) :
    D.Ok Fl Hl := by
  have ha : ∀ a : Fin 2, a ∈ ([0, 1] : List (Fin 2)) := fun a => by fin_cases a <;> simp
  refine ⟨hb, hbd, hw, hS, fun i hi => ?_, fun i hi => ?_, fun i hi a => ?_, fun i hi a => ?_,
    fun t ht => ?_, fun t ht a => ?_, fun t ht a => ?_⟩
  · have := hf i hi; simp only [Bool.and_eq_true] at this; exact this.1
  · have := hf i hi; simp only [Bool.and_eq_true] at this
    have h := fCheck_sound this.2
    rwa [hcS, hcb] at h
  · have := List.all_eq_true.mp (hdf i hi) a (ha a)
    simp only [Bool.and_eq_true] at this; exact this.1
  · have := List.all_eq_true.mp (hdf i hi) a (ha a)
    simp only [Bool.and_eq_true] at this
    have h := dCheck_sound this.2
    rwa [hcS, hcb, hcdS, hcdb] at h
  · have := hh t ht; simpa only [Bool.and_eq_true] using this
  · have := List.all_eq_true.mp (hdh t ht) a (ha a)
    simp only [Bool.and_eq_true] at this; exact this.1
  · have := List.all_eq_true.mp (hdh t ht) a (ha a)
    simp only [Bool.and_eq_true] at this
    have h := dCheck_sound this.2
    rwa [hcS, hcb, hcdS, hcdb] at h

end KAM.EffectiveStability.Tube

end
