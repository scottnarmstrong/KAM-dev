/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Comb

/-!
# One checker step: a sum of products, then an output literal (T2-CONF, N7)

**Operands.** `Opd`: a slot list `l` on the square layout of half-width `C` (common stride `S`),
its packed value `Z`, a parity and a rational scale `q`; its value is
`q · evalK (Layout.key C S) par l`.
`Opd.WF`: `packSum w l = Z`, zero padding, at most `Layout.len C S` slots. `Opd.Cert f o e₀ e₁ n`:
well formed, `C1Close f o.eval e₀ e₁`, `l1 l ≤ n`; `Opd.Mx o mx`: every slot `|x| ≤ mx`.

**Products** (`prodCheck`, `prod_sound`). Terms `t = (c, sh, ρ, A, B)`, all `A` on layout `C_a`, all
`B` on `C_b` and symmetric for their parity, with `ρ q_A q_B psgn(p_A ∧ p_B) = Q c 2^sh` for one
rational `Q` (the sign of a product of two odd factors lives in `c`). Then
`Σ_t ρ_t f_{A_t} f_{B_t}` is `C¹`-close to `Q · evalK (Layout.key (C_a+C_b) S) p X`,
`X = lcomb [(c 2^sh, listConv A.l B.l)]`, with the product-rule errors (sup bounds from the claimed
`ℓ¹` bounds, `wl1 ≤ C l1`); the kernel only computes `Σ c 2^sh Z_A Z_B = packSum w X`.

**Output** (`outCheck`, `out_sound`). An output operand `O` on a sub-layout, integers `α_X, α_O`
with `q_O α_X = Q α_O`: the difference `D = α_X packSum X - α_O 2^(w shift) Z_O` is the packing of
the slotwise difference, and its packed `ℓ¹` (`l1P`) bounds the `C¹` distance
(`|Q|/α_X · δ`, and `|Q|/α_X · (C_a + C_b) · δ` for the derivatives).
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.Certificate KAM.CertificateSharp.Packed

/-- A semantic operand. -/
structure Opd where
  C : ℕ
  par : Bool
  q : ℚ
  l : List ℤ
  Z : ℤ

/-- The value of an operand: `q · evalK (Layout.key C S) par l`. -/
noncomputable def Opd.eval (S : ℕ) (o : Opd) (φ : Fin 2 → ℝ) : ℝ :=
  (o.q : ℝ) * evalK (Layout.key o.C S) o.par o.l φ

/-- A well-formed operand. -/
structure Opd.WF (w S : ℕ) (o : Opd) : Prop where
  pack : packSum w o.l = o.Z
  cols : colsOk o.C S o.l = true
  len : o.l.length ≤ Layout.len o.C S

/-- The certificate of an operand for a true function `f`. -/
structure Opd.Cert (w S : ℕ) (f : (Fin 2 → ℝ) → ℝ) (o : Opd) (e₀ e₁ : ℚ) (n : ℕ) : Prop where
  wf : o.WF w S
  close : C1Close f (o.eval S) e₀ e₁
  l1le : l1 o.l ≤ n

/-- A slot bound of an operand. -/
def Opd.Mx (o : Opd) (mx : ℕ) : Prop := ∀ x ∈ o.l, |x| ≤ (mx : ℤ)

theorem Opd.differentiable_eval (S : ℕ) (o : Opd) : Differentiable ℝ (o.eval S) :=
  (differentiable_evalK _ _ _).const_mul _

theorem Opd.abs_eval_le {w S : ℕ} {o : Opd} {n : ℕ} (hl : l1 o.l ≤ n) (φ : Fin 2 → ℝ) :
    |o.eval S φ| ≤ |(o.q : ℝ)| * n := by
  rw [Opd.eval, abs_mul]
  refine mul_le_mul_of_nonneg_left ((abs_evalK_le _ _ _ _).trans ?_) (abs_nonneg _)
  exact_mod_cast hl

theorem Opd.abs_pderiv_eval_le {w S : ℕ} {o : Opd} (hS : 2 * o.C < S) (hwf : o.WF w S) {n : ℕ}
    (hl : l1 o.l ≤ n) (φ : Fin 2 → ℝ) (a : Fin 2) :
    |pderiv (o.eval S) φ a| ≤ |(o.q : ℝ)| * (o.C * n) := by
  rw [show o.eval S = fun φ => (o.q : ℝ) * evalK (Layout.key o.C S) o.par o.l φ from rfl,
    C1Close.pderiv_const_mul (differentiable_evalK _ _ _), abs_mul]
  refine mul_le_mul_of_nonneg_left ((abs_pderiv_evalK_le _ _ _ _ _).trans ?_) (abs_nonneg _)
  have h1 := wl1_le_mul_l1 hS hwf.cols hwf.len a
  have h2 : (o.C : ℤ) * l1 o.l ≤ o.C * n := mul_le_mul_of_nonneg_left hl (by positivity)
  exact_mod_cast h1.trans h2

/-! ### Products -/

/-- A product term with the claims of its two operands. -/
structure Term where
  c : ℤ
  sh : ℕ
  ρ : ℚ
  A : Opd
  B : Opd
  ea₀ : ℚ
  ea₁ : ℚ
  na : ℕ
  eb₀ : ℚ
  eb₁ : ℚ
  nb : ℕ
  mxb : ℕ
  /-- an index for the semantics (which true functions the operands certify); unused by checks -/
  tag : ℕ × ℕ × ℕ := (0, 0, 0)

/-- The value error of a product term (`C1Close.mul`). -/
def Term.err₀ (t : Term) : ℚ := |t.A.q| * t.na * t.eb₀ + |t.B.q| * t.nb * t.ea₀ + t.ea₀ * t.eb₀

/-- The derivative error of a product term (`C1Close.mul`, with `wl1 ≤ C l1`). -/
def Term.err₁ (t : Term) : ℚ :=
  |t.A.q| * (t.A.C * t.na) * t.eb₀ + |t.A.q| * t.na * t.eb₁ + |t.B.q| * (t.B.C * t.nb) * t.ea₀ +
    |t.B.q| * t.nb * t.ea₁ + t.ea₁ * t.eb₀ + t.ea₀ * t.eb₁

/-- The slot bound of a product term. -/
def Term.slotB (t : Term) : ℕ := t.c.natAbs * 2 ^ t.sh * t.na * t.mxb

/-- The kernel check of a sum of products (metadata and rational claims only; no slot is read). -/
def prodCheck (S Ca Cb : ℕ) (p : Bool) (Q : ℚ) (ts : List Term) (E₀ E₁ : ℚ) (BX : ℕ) : Bool :=
  decide (2 * (Ca + Cb) < S) &&
    ts.all (fun t => t.A.C == Ca && t.B.C == Cb && xor t.A.par t.B.par == p &&
      decide (t.ρ * t.A.q * t.B.q * psgn (t.A.par && t.B.par) = Q * t.c * 2 ^ t.sh)) &&
    decide ((ts.map fun t => |t.ρ| * t.err₀).sum ≤ E₀) &&
    decide ((ts.map fun t => |t.ρ| * t.err₁).sum ≤ E₁) &&
    decide ((ts.map Term.slotB).sum ≤ BX)

/-- The exact combination of a list of terms. -/
def Term.comb (ts : List Term) : List ℤ :=
  lcomb (ts.map fun t => (t.c * 2 ^ t.sh, listConv t.A.l t.B.l))

theorem abs_listSum_le {α : Type*} (f : α → ℤ) : ∀ l : List α,
    |(l.map f).sum| ≤ (l.map fun x => |f x|).sum
  | [] => by simp
  | x :: l => by
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add le_rfl (abs_listSum_le f l))

/-- `C1Close` for sums over a list. -/
theorem C1Close.listSum {α : Type*} {F G : α → (Fin 2 → ℝ) → ℝ} {e₀ e₁ : α → ℝ} :
    ∀ ts : List α, (∀ t ∈ ts, C1Close (F t) (G t) (e₀ t) (e₁ t)) →
      C1Close (fun φ => (ts.map fun t => F t φ).sum) (fun φ => (ts.map fun t => G t φ).sum)
        (ts.map e₀).sum (ts.map e₁).sum
  | [], _ => by
    simp only [List.map_nil, List.sum_nil]
    exact C1Close.refl (g := fun _ => (0 : ℝ)) (differentiable_const 0)
  | t :: ts, h => by
    simp only [List.map_cons, List.sum_cons]
    exact (h t (by simp)).add (C1Close.listSum ts fun x hx => h x (by simp [hx]))

theorem length_listConv_le {a b : List ℤ} {La Lb : ℕ} (ha : a.length ≤ La) (hb : b.length ≤ Lb) :
    (listConv a b).length ≤ La + Lb - 1 := by
  by_cases hae : a = []
  · subst hae; simp [listConv]
  by_cases hbe : b = []
  · subst hbe; simp [listConv]
  rw [length_listConv hae hbe]; omega

theorem Layout.len_add (Ca Cb S : ℕ) :
    Layout.len (Ca + Cb) S = Layout.len Ca S + Layout.len Cb S - 1 := by
  unfold Layout.len; rw [Nat.mul_add, add_mul]; omega

/-- **Soundness of a sum of products.** -/
theorem prod_sound {w S Ca Cb : ℕ} {p : Bool} {Q : ℚ} {ts : List Term} {E₀ E₁ : ℚ} {BX : ℕ}
    (hchk : prodCheck S Ca Cb p Q ts E₀ E₁ BX = true) (fA fB : Term → (Fin 2 → ℝ) → ℝ)
    (hA : ∀ t ∈ ts, t.A.Cert w S (fA t) t.ea₀ t.ea₁ t.na)
    (hB : ∀ t ∈ ts, t.B.Cert w S (fB t) t.eb₀ t.eb₁ t.nb ∧ t.B.Mx t.mxb ∧
      symOk t.B.par t.B.l = true ∧ t.B.l.length = Layout.len t.B.C S) :
    C1Close (fun φ => (ts.map fun t => (t.ρ : ℝ) * (fA t φ * fB t φ)).sum)
      (fun φ => (Q : ℝ) * evalK (Layout.key (Ca + Cb) S) p (Term.comb ts) φ) E₀ E₁ ∧
    packSum w (Term.comb ts) = (ts.map fun t => t.c * 2 ^ t.sh * (t.A.Z * t.B.Z)).sum ∧
    colsOk (Ca + Cb) S (Term.comb ts) = true ∧
    (Term.comb ts).length ≤ Layout.len (Ca + Cb) S ∧ ∀ x ∈ Term.comb ts, |x| ≤ (BX : ℤ) := by
  simp only [prodCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hchk
  obtain ⟨⟨⟨⟨hS, hall⟩, hE₀⟩, hE₁⟩, hBX⟩ := hchk
  have hT : ∀ t ∈ ts, t.A.C = Ca ∧ t.B.C = Cb ∧ xor t.A.par t.B.par = p ∧
      t.ρ * t.A.q * t.B.q * psgn (t.A.par && t.B.par) = Q * t.c * 2 ^ t.sh := fun t ht => by
    have := hall t ht
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  -- the per-term product rule
  have hterm : ∀ t ∈ ts, C1Close (fun φ => (t.ρ : ℝ) * (fA t φ * fB t φ))
      (fun φ => (t.ρ : ℝ) * (t.A.eval S φ * t.B.eval S φ)) (((|t.ρ| * t.err₀ : ℚ)) : ℝ)
      (((|t.ρ| * t.err₁ : ℚ)) : ℝ) := by
    intro t ht
    obtain ⟨hAC, hBC, -, -⟩ := hT t ht
    have hA' := hA t ht
    obtain ⟨hB', -, -, -⟩ := hB t ht
    have hSA : 2 * t.A.C < S := by omega
    have hSB : 2 * t.B.C < S := by omega
    have hm := hA'.close.mul hB'.close (P₀ := |(t.A.q : ℝ)| * t.na)
      (P₁ := |(t.A.q : ℝ)| * (t.A.C * t.na)) (Q₀ := |(t.B.q : ℝ)| * t.nb)
      (Q₁ := |(t.B.q : ℝ)| * (t.B.C * t.nb))
      (Opd.abs_eval_le (w := w) hA'.l1le) (Opd.abs_pderiv_eval_le hSA hA'.wf hA'.l1le)
      (Opd.abs_eval_le (w := w) hB'.l1le) (Opd.abs_pderiv_eval_le hSB hB'.wf hB'.l1le)
    have hc := hm.const_mul (t.ρ : ℝ)
    refine hc.mono (le_of_eq ?_) (le_of_eq ?_)
    · simp only [Term.err₀]; push_cast; ring
    · simp only [Term.err₁]; push_cast; ring
  have hsum := C1Close.listSum ts hterm
  -- the model identity
  have hmodel : (fun φ => (ts.map fun t => (t.ρ : ℝ) * (t.A.eval S φ * t.B.eval S φ)).sum) =
      fun φ => (Q : ℝ) * evalK (Layout.key (Ca + Cb) S) p (Term.comb ts) φ := by
    funext φ
    rw [Term.comb, evalK_lcomb, List.map_map, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    obtain ⟨hAC, hBC, hpar, hq⟩ := hT t ht
    obtain ⟨hB', -, hsym, hlen⟩ := hB t ht
    have hA' := hA t ht
    have hS' : 2 * (t.A.C + t.B.C) < S := by omega
    have hmul := evalK_mul (p := t.A.par) hS' hA'.wf.cols hB'.wf.cols hlen hsym φ
    simp only [Function.comp_apply, Opd.eval]
    rw [show (t.ρ : ℝ) * ((t.A.q : ℝ) * evalK (Layout.key t.A.C S) t.A.par t.A.l φ *
        ((t.B.q : ℝ) * evalK (Layout.key t.B.C S) t.B.par t.B.l φ)) =
        (t.ρ * t.A.q * t.B.q : ℚ) * (evalK (Layout.key t.A.C S) t.A.par t.A.l φ *
          evalK (Layout.key t.B.C S) t.B.par t.B.l φ) by push_cast; ring, hmul, ← hAC, ← hBC,
      ← hpar]
    have hq' : ((t.ρ * t.A.q * t.B.q : ℚ) : ℝ) * (psgn (t.A.par && t.B.par) : ℝ) =
        (Q : ℝ) * ((t.c * 2 ^ t.sh : ℤ) : ℝ) := by
      have := congrArg (fun x : ℚ => (x : ℝ)) hq
      push_cast at this ⊢
      linarith
    rw [← mul_assoc, hq']
    push_cast
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hmodel]
    refine hsum.mono ?_ ?_
    · have := congrArg (fun x : ℚ => (x : ℝ)) (rfl : (ts.map fun t => |t.ρ| * t.err₀).sum = _)
      calc ((ts.map fun t => ((|t.ρ| * t.err₀ : ℚ) : ℝ))).sum =
            (((ts.map fun t => |t.ρ| * t.err₀).sum : ℚ) : ℝ) := by
              rw [Rat.cast_list_sum, List.map_map]; rfl
        _ ≤ (E₀ : ℝ) := by exact_mod_cast hE₀
    · calc ((ts.map fun t => ((|t.ρ| * t.err₁ : ℚ) : ℝ))).sum =
            (((ts.map fun t => |t.ρ| * t.err₁).sum : ℚ) : ℝ) := by
              rw [Rat.cast_list_sum, List.map_map]; rfl
        _ ≤ (E₁ : ℝ) := by exact_mod_cast hE₁
  · rw [Term.comb, packSum_lcomb, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    simp only [Function.comp_apply]
    rw [packSum_listConv, (hA t ht).wf.pack, (hB t ht).1.wf.pack]
  · apply colsOk_lcomb
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hAC, hBC, -, -⟩ := hT t ht
    have := colsOk_listConv (Ca := t.A.C) (Cb := t.B.C) (by omega) (hA t ht).wf.cols
      (hB t ht).1.wf.cols
    rwa [hAC, hBC] at this
  · apply length_lcomb_le
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hAC, hBC, -, -⟩ := hT t ht
    rw [Layout.len_add]
    exact length_listConv_le (by rw [← hAC]; exact (hA t ht).wf.len)
      (by rw [← hBC]; exact (hB t ht).1.wf.len)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hg : (Term.comb ts)[i] = (Term.comb ts).getD i 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rw [hg, Term.comb, getD_lcomb, List.map_map]
    refine (abs_listSum_le _ ts).trans ?_
    have hle : ∀ t ∈ ts, |t.c * 2 ^ t.sh * (listConv t.A.l t.B.l).getD i 0| ≤ (t.slotB : ℤ) := by
      intro t ht
      have h1 := abs_listConv_getD_le t.A.l t.B.l i
      have h2 : (maxAbs t.B.l : ℤ) ≤ t.mxb := by exact_mod_cast maxAbs_le (hB t ht).2.1
      have h3 := (hA t ht).l1le
      have hl0 := l1_nonneg t.A.l
      rw [abs_mul, abs_mul, Term.slotB]
      push_cast
      rw [abs_pow, abs_two, Int.abs_eq_natAbs]
      have : |(listConv t.A.l t.B.l).getD i 0| ≤ (t.na : ℤ) * t.mxb := by
        calc _ ≤ l1 t.A.l * (maxAbs t.B.l : ℤ) := h1
          _ ≤ (t.na : ℤ) * t.mxb := mul_le_mul h3 h2 (by positivity) (by positivity)
      calc (t.c.natAbs : ℤ) * 2 ^ t.sh * |(listConv t.A.l t.B.l).getD i 0| ≤
          (t.c.natAbs : ℤ) * 2 ^ t.sh * ((t.na : ℤ) * t.mxb) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    calc (ts.map fun t => |t.c * 2 ^ t.sh * (listConv t.A.l t.B.l).getD i 0|).sum ≤
        (ts.map fun t => (t.slotB : ℤ)).sum := List.sum_le_sum fun t ht => hle t ht
      _ = ((ts.map Term.slotB).sum : ℕ) := by push_cast; rw [List.map_map]; rfl
      _ ≤ BX := by exact_mod_cast hBX

/-! ### The output literal -/

theorem packSum_lsub (w : ℕ) (a b : List ℤ) : packSum w (lsub a b) = packSum w a - packSum w b := by
  rw [packSum_eq_sum_of_le w _ (le_refl _), length_lsub,
    packSum_eq_sum_of_le w a (le_max_left a.length b.length),
    packSum_eq_sum_of_le w b (le_max_right a.length b.length), ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by rw [getD_lsub, sub_mul]

theorem packSum_replicate_zero (w n : ℕ) : packSum w (List.replicate n (0 : ℤ)) = 0 := by
  rw [packSum_replicate]; ring

theorem packSum_embed (w C C' S : ℕ) (d : List ℤ) :
    packSum w (embed C C' S d) = 2 ^ (w * Layout.shift C C' S) * packSum w d := by
  rw [embed, packSum_append, packSum_replicate_zero, List.length_replicate, zero_add]

theorem colsOk_lsub {C S : ℕ} {a b : List ℤ} (ha : colsOk C S a = true) (hb : colsOk C S b = true) :
    colsOk C S (lsub a b) = true := by
  apply colsOk_of_getD
  intro i hi
  simp only [zero_add]
  by_contra hcol
  push Not at hcol
  apply hi
  rw [getD_lsub, getD_eq_zero_of_colsOk ha hcol, getD_eq_zero_of_colsOk hb hcol, sub_zero]

theorem colsOk_embed {C C' S : ℕ} (hC : C' ≤ C) (hS : C + C' < S) {d : List ℤ}
    (hd : colsOk C' S d = true) : colsOk C S (embed C C' S d) = true := by
  apply colsOk_of_getD
  intro i hi
  simp only [zero_add]
  rw [embed, getD_replicate_append] at hi
  split_ifs at hi with h1
  · exact absurd rfl hi
  · have hc := colsOk_spec hd _ hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp h1)
    rw [Nat.add_sub_cancel_left] at hc
    have hS0 : 0 < S := by omega
    have hsplit : Layout.shift C C' S + j = ((C - C') + j % S) + S * ((C - C') + j / S) := by
      have := Nat.mod_add_div j S
      unfold Layout.shift
      conv_lhs => rw [← this]
      ring
    rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega

theorem length_embed_le {C C' S : ℕ} (hC : C' ≤ C) {d : List ℤ} (hd : d.length ≤ Layout.len C' S) :
    (embed C C' S d).length ≤ Layout.len C S := by
  rw [embed, List.length_append, List.length_replicate]
  unfold Layout.shift Layout.len at *
  have : C' * (S + 1) ≤ C * (S + 1) := Nat.mul_le_mul_right _ hC
  have h2 : (C - C') * (S + 1) = C * (S + 1) - C' * (S + 1) := Nat.sub_mul C C' (S + 1)
  have h3 : 2 * C * S + 2 * C = 2 * (C * (S + 1)) := by ring
  have h4 : 2 * C' * S + 2 * C' = 2 * (C' * (S + 1)) := by ring
  omega

theorem getD_append_zeros (cs : List ℤ) (k i : ℕ) :
    (cs ++ List.replicate k 0).getD i 0 = cs.getD i 0 := by
  by_cases hi : i < cs.length
  · rw [List.getD_append _ _ _ _ hi]
  · rw [List.getD_append_right _ _ _ _ (not_lt.mp hi), List.getD_eq_getElem?_getD,
      List.getElem?_replicate]
    rw [List.getD_eq_getElem?_getD (l := cs), List.getElem?_eq_none (not_lt.mp hi)]
    split_ifs <;> rfl

theorem l1_append_zeros (cs : List ℤ) (k : ℕ) : l1 (cs ++ List.replicate k 0) = l1 cs := by
  rw [l1_eq, l1_eq]
  simp_rw [getD_append_zeros]
  symm
  refine sum_subset (range_subset_range.mpr (by simp)) fun i _ hi => ?_
  rw [mem_range, not_lt] at hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

/-- The `ℓ¹` of a list of at most `N` bounded slots from its packed value. -/
theorem l1P_eq_of_le {w N l : ℕ} {D : ℤ} (h : l1Ok w N l D = true) {cs : List ℤ}
    (hD : packSum w cs = D) (hlen : cs.length ≤ N) (hcs : SlotsBounded w cs) :
    (l1P w N l D : ℤ) = l1 cs := by
  rw [l1P_eq h (cs := cs ++ List.replicate (N - cs.length) 0)
    (by rw [packSum_append, packSum_replicate_zero, mul_zero, add_zero, hD])
    (by simp; omega)
    (fun c hc => by
      rcases List.mem_append.mp hc with hc | hc
      · exact hcs c hc
      · rw [(List.mem_replicate.mp hc).2]; simp), l1_append_zeros]

/-- The kernel check of an output literal against an exact combination. -/
def outCheck (w S Cp : ℕ) (Q : ℚ) (Xz : ℤ) (BX : ℕ) (O : Opd) (mxO αX αO lD : ℕ) (E₀ E₁ : ℚ) :
    Bool :=
  decide (O.C ≤ Cp) && decide (Cp + O.C < S) && decide (2 * Cp < S) && decide (0 < αX) &&
    decide (O.q * αX = Q * αO) && decide (2 * (αX * BX + αO * mxO) < 2 ^ w) &&
    l1Ok w (Layout.len Cp S) lD (αX * Xz - αO * 2 ^ (w * Layout.shift Cp O.C S) * O.Z) &&
    decide (|Q| / αX * (l1P w (Layout.len Cp S) lD
      (αX * Xz - αO * 2 ^ (w * Layout.shift Cp O.C S) * O.Z) : ℚ) ≤ E₀) &&
    decide (|Q| / αX * (Cp * l1P w (Layout.len Cp S) lD
      (αX * Xz - αO * 2 ^ (w * Layout.shift Cp O.C S) * O.Z) : ℚ) ≤ E₁)

/-- **Soundness of an output literal.** An exact combination `X` (packed value `X_z`) and an output
operand `O` are `C¹`-close with the packed `ℓ¹` of their scaled difference. -/
theorem out_sound {w S Cp : ℕ} {Q : ℚ} {Xz : ℤ} {BX : ℕ} {O : Opd} {mxO αX αO lD : ℕ} {E₀ E₁ : ℚ}
    (hchk : outCheck w S Cp Q Xz BX O mxO αX αO lD E₀ E₁ = true) {p : Bool} (hp : O.par = p)
    {X : List ℤ} (hXp : packSum w X = Xz) (hXc : colsOk Cp S X = true)
    (hXl : X.length ≤ Layout.len Cp S) (hXb : ∀ x ∈ X, |x| ≤ (BX : ℤ)) (hO : O.WF w S)
    (hOm : O.Mx mxO) :
    C1Close (fun φ => (Q : ℝ) * evalK (Layout.key Cp S) p X φ) (O.eval S) E₀ E₁ := by
  simp only [outCheck, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hC, hS⟩, hS2⟩, hα⟩, hq⟩, hov⟩, hl1⟩, hE₀⟩, hE₁⟩ := hchk
  set D : ℤ := αX * Xz - αO * 2 ^ (w * Layout.shift Cp O.C S) * O.Z with hDdef
  set Dl : List ℤ := lsub (X.map ((αX : ℤ) * ·)) (embed Cp O.C S (O.l.map ((αO : ℤ) * ·)))
    with hDl
  have hDp : packSum w Dl = D := by
    rw [hDl, packSum_lsub, packSum_map_mul, packSum_embed, packSum_map_mul, hXp, hO.pack, hDdef]
    ring
  have hOcols : colsOk Cp S (embed Cp O.C S (O.l.map ((αO : ℤ) * ·))) = true :=
    colsOk_embed hC hS (colsOk_map_mul hO.cols _)
  have hDc : colsOk Cp S Dl = true := colsOk_lsub (colsOk_map_mul hXc _) hOcols
  have hOlen : (embed Cp O.C S (O.l.map ((αO : ℤ) * ·))).length ≤ Layout.len Cp S :=
    length_embed_le hC (by rw [List.length_map]; exact hO.len)
  have hDlen : Dl.length ≤ Layout.len Cp S := by
    rw [hDl, length_lsub, List.length_map]; exact max_le hXl hOlen
  have hDb : SlotsBounded w Dl := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have hg : Dl[i] = Dl.getD i 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rw [hg, hDl, getD_lsub, getD_map_mul, embed, getD_replicate_append]
    have hx : |X.getD i 0| ≤ BX := by
      by_cases h : i < X.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
        exact hXb _ (List.getElem_mem h)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp h)]; simp
    have hy : ∀ j, |(O.l.map ((αO : ℤ) * ·)).getD j 0| ≤ αO * mxO := fun j => by
      rw [getD_map_mul, abs_mul]
      have : |O.l.getD j 0| ≤ mxO := by
        by_cases h : j < O.l.length
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
          exact hOm _ (List.getElem_mem h)
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp h)]; simp
      rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ αO)]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hy' : |(if i < Layout.shift Cp O.C S then (0 : ℤ)
        else (O.l.map ((αO : ℤ) * ·)).getD (i - Layout.shift Cp O.C S) 0)| ≤ αO * mxO := by
      split_ifs
      · simp; positivity
      · exact hy _
    have hov' : (2 : ℤ) * (αX * BX + αO * mxO) < 2 ^ w := by exact_mod_cast hov
    have h1 : |(αX : ℤ) * X.getD i 0| ≤ αX * BX := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ αX)]
      exact mul_le_mul_of_nonneg_left hx (by positivity)
    have := (abs_sub _ _).trans (add_le_add h1 hy')
    linarith
  have hδ := l1P_eq_of_le hl1 hDp hDlen hDb
  have hαX : (0 : ℝ) < αX := by exact_mod_cast hα
  have hqO : (O.q : ℝ) = (Q : ℝ) * αO / αX := by
    have := congrArg (fun x : ℚ => (x : ℝ)) hq
    push_cast at this
    field_simp
    linarith
  have heval : ∀ φ, (Q : ℝ) * evalK (Layout.key Cp S) p X φ - O.eval S φ =
      ((Q : ℝ) / αX) * evalK (Layout.key Cp S) p Dl φ := by
    intro φ
    rw [hDl, evalK_lsub, evalK_map_mul, evalK_embed hC hS (colsOk_map_mul hO.cols _),
      evalK_map_mul, Opd.eval, hqO, hp]
    push_cast
    field_simp
  have hfun : (fun φ => (Q : ℝ) * evalK (Layout.key Cp S) p X φ) - O.eval S =
      fun φ => ((Q : ℝ) / αX) * evalK (Layout.key Cp S) p Dl φ := funext heval
  have hl1R : ((l1 Dl : ℤ) : ℝ) = ((l1P w (Layout.len Cp S) lD D : ℕ) : ℝ) := by
    rw [← hδ]; push_cast; rfl
  have hQa : |(Q : ℝ) / αX| = (|Q| / αX : ℚ) := by
    push_cast; rw [abs_div, abs_of_pos hαX]
  have hF : Differentiable ℝ (fun φ => (Q : ℝ) * evalK (Layout.key Cp S) p X φ) :=
    (differentiable_evalK _ _ _).const_mul _
  refine ⟨hF, O.differentiable_eval S, fun φ => ?_, fun φ a => ?_⟩
  · rw [heval, abs_mul, hQa]
    calc ((|Q| / αX : ℚ) : ℝ) * |evalK (Layout.key Cp S) p Dl φ| ≤
        ((|Q| / αX : ℚ) : ℝ) * ((l1 Dl : ℤ) : ℝ) :=
          mul_le_mul_of_nonneg_left (abs_evalK_le _ _ _ _) (by positivity)
      _ ≤ E₀ := by rw [hl1R]; exact_mod_cast hE₀
  · rw [← C1Close.pderiv_sub hF (O.differentiable_eval S), hfun,
      C1Close.pderiv_const_mul (differentiable_evalK _ _ _), abs_mul, hQa]
    have hw1 := wl1_le_mul_l1 hS2 hDc hDlen a
    have hw1R : ((wl1 (Layout.key Cp S) a Dl : ℤ) : ℝ) ≤ (Cp : ℝ) * ((l1 Dl : ℤ) : ℝ) := by
      exact_mod_cast hw1
    calc ((|Q| / αX : ℚ) : ℝ) * |pderiv (evalK (Layout.key Cp S) p Dl) φ a| ≤
        ((|Q| / αX : ℚ) : ℝ) * ((Cp : ℝ) * ((l1 Dl : ℤ) : ℝ)) :=
          mul_le_mul_of_nonneg_left ((abs_pderiv_evalK_le _ _ _ _ _).trans hw1R) (by positivity)
      _ ≤ E₁ := by rw [hl1R]; exact_mod_cast hE₁

end KAM.EffectiveStability.Tube

end
