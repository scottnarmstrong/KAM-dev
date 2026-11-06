/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Exact

/-!
# Composite certificates (T2-CONF, N7)

* `combOpd`: the exact combination of a sum of products as an operand (layout `C_a + C_b`, scale
  `Q`, packed value `Σ c 2^sh Z_A Z_B`); `combCheck`, `comb_cert` (its certificate, with a kernel
  `ℓ¹` claim);
* `litCheck`, `lit_cert`: a sum of products compared with an output literal: the literal's
  certificate, errors added;
* `lowB_litList`: a lower bound of an even literal from its centre digit and its `ℓ¹`
  (`q (2 c₀ - n)`, for positivity of `B` and of the `√B` witness).
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.Certificate KAM.CertificateSharp.Packed

/-- The packed value of a sum of products (kernel). -/
def Term.combZ (ts : List Term) : ℤ := (ts.map fun t => t.c * 2 ^ t.sh * (t.A.Z * t.B.Z)).sum

/-- The exact combination as an operand. -/
def combOpd (Ca Cb : ℕ) (p : Bool) (Q : ℚ) (ts : List Term) : Opd :=
  ⟨Ca + Cb, p, Q, Term.comb ts, Term.combZ ts⟩

/-- The check of an exact combination: the products, and a packed `ℓ¹` claim `n` at load level
`l`. -/
def combCheck (w S Ca Cb : ℕ) (p : Bool) (Q : ℚ) (ts : List Term) (E₀ E₁ : ℚ) (BX l n : ℕ) :
    Bool :=
  prodCheck S Ca Cb p Q ts E₀ E₁ BX && decide (2 * BX < 2 ^ w) &&
    l1Ok w (Layout.len (Ca + Cb) S) l (Term.combZ ts) &&
    decide (l1P w (Layout.len (Ca + Cb) S) l (Term.combZ ts) ≤ n)

theorem comb_cert {w S Ca Cb : ℕ} {p : Bool} {Q : ℚ} {ts : List Term} {E₀ E₁ : ℚ} {BX l n : ℕ}
    (h : combCheck w S Ca Cb p Q ts E₀ E₁ BX l n = true) (fA fB : Term → (Fin 2 → ℝ) → ℝ)
    (hA : ∀ t ∈ ts, t.A.Cert w S (fA t) t.ea₀ t.ea₁ t.na)
    (hB : ∀ t ∈ ts, t.B.Cert w S (fB t) t.eb₀ t.eb₁ t.nb ∧ t.B.Mx t.mxb ∧
      symOk t.B.par t.B.l = true ∧ t.B.l.length = Layout.len t.B.C S) :
    (combOpd Ca Cb p Q ts).Cert w S (fun φ => (ts.map fun t => (t.ρ : ℝ) * (fA t φ * fB t φ)).sum)
      E₀ E₁ n ∧ (combOpd Ca Cb p Q ts).Mx BX := by
  simp only [combCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hp, hBX⟩, hl⟩, hn⟩ := h
  obtain ⟨hc, hpack, hcols, hlen, hb⟩ := prod_sound hp fA fB hA hB
  have hsb : SlotsBounded w (Term.comb ts) := fun x hx => by
    have := hb x hx
    have h2 : (2 * BX : ℤ) < 2 ^ w := by exact_mod_cast hBX
    linarith
  have hl1 := l1P_eq_of_le hl hpack hlen hsb
  refine ⟨⟨⟨hpack, hcols, hlen⟩, ?_, ?_⟩, hb⟩
  · exact hc
  · show l1 (Term.comb ts) ≤ n
    rw [← hl1]; exact_mod_cast hn

/-- A sum of products compared with an output literal. -/
def litCheck (P : Prm) (Ca Cb : ℕ) (p : Bool) (Q : ℚ) (ts : List Term) (E₀ E₁ : ℚ) (BX : ℕ)
    (d : LitD) (αX αO lD : ℕ) (F₀ F₁ : ℚ) (e₀ e₁ : ℚ) (n : ℕ) : Bool :=
  prodCheck P.S Ca Cb p Q ts E₀ E₁ BX && d.ok P && decide (1 ≤ P.b) && d.par == p &&
    outCheck P.w P.S (Ca + Cb) Q (Term.combZ ts) BX (d.opd P) (2 ^ (P.b - 1)) αX αO lD F₀ F₁ &&
    decide (E₀ + F₀ ≤ e₀) && decide (E₁ + F₁ ≤ e₁) && d.l1Check P n

/-- **The certificate of an output literal.** -/
theorem lit_cert {P : Prm} {Ca Cb : ℕ} {p : Bool} {Q : ℚ} {ts : List Term} {E₀ E₁ : ℚ} {BX : ℕ}
    {d : LitD} {αX αO lD : ℕ} {F₀ F₁ e₀ e₁ : ℚ} {n : ℕ}
    (h : litCheck P Ca Cb p Q ts E₀ E₁ BX d αX αO lD F₀ F₁ e₀ e₁ n = true)
    (fA fB : Term → (Fin 2 → ℝ) → ℝ)
    (hA : ∀ t ∈ ts, t.A.Cert P.w P.S (fA t) t.ea₀ t.ea₁ t.na)
    (hB : ∀ t ∈ ts, t.B.Cert P.w P.S (fB t) t.eb₀ t.eb₁ t.nb ∧ t.B.Mx t.mxb ∧
      symOk t.B.par t.B.l = true ∧ t.B.l.length = Layout.len t.B.C P.S) :
    (d.opd P).Cert P.w P.S (fun φ => (ts.map fun t => (t.ρ : ℝ) * (fA t φ * fB t φ)).sum)
      e₀ e₁ n := by
  simp only [litCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hp, hok⟩, hb⟩, hpar⟩, hout⟩, he₀⟩, he₁⟩, hl1⟩ := h
  obtain ⟨hc, hpack, hcols, hlen, hbd⟩ := prod_sound hp fA fB hA hB
  have hO := out_sound hout hpar hpack hcols hlen hbd (LitD.wf hok) (LitD.mx hb)
  refine ⟨LitD.wf hok, (hc.trans hO).mono ?_ ?_, LitD.l1_le hl1⟩
  · exact_mod_cast he₀
  · exact_mod_cast he₁

/-! ### Lower bounds of even literals -/

theorem litSlot_center (C S b X : ℕ) (hKS : 2 * C + 1 ≤ S) :
    litSlot C S b X (C + S * C) = (dig b X (C + (2 * C + 1) * C) : ℤ) - 2 ^ (b - 1) := by
  unfold litSlot
  rw [(mod_div_of_lt (by omega)).1, (mod_div_of_lt (by omega)).2, if_pos (by omega)]

/-- The centre digit of a literal (kernel: one shift and one mask). -/
def LitD.c0 (P : Prm) (d : LitD) : ℤ :=
  (dig P.b d.X (d.C + (2 * d.C + 1) * d.C) : ℤ) - 2 ^ (P.b - 1)

/-- **Lower bound of an even literal**: `evalK ≥ 2 c₀ - l1`. -/
theorem lowB_litList {P : Prm} {d : LitD} (hKS : 2 * d.C + 1 ≤ P.S) (φ : Fin 2 → ℝ) :
    ((2 * d.c0 P - l1 (d.opd P).l : ℤ) : ℝ) ≤ evalK (Layout.key d.C P.S) false (d.opd P).l φ := by
  refine le_trans (Int.cast_le.mpr ?_) (lowB_le_evalK _ _ φ)
  set L := (d.opd P).l with hL
  set K := 2 * d.C + 1 with hK
  have hS : 0 < P.S := by omega
  set ctr := d.C + P.S * d.C with hctr
  have hctrlt : ctr < L.length := by
    rw [hL, LitD.opd, length_litList]; unfold Layout.len
    have : P.S * d.C ≤ P.S * (2 * d.C) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have hLc : L.getD ctr 0 = d.c0 P := by
    rw [hL, LitD.opd, getD_litList, if_pos (by rw [← length_litList d.C P.S P.b d.X]; exact hctrlt),
      litSlot_center _ _ _ _ hKS]
    rfl
  have hkey : ∀ i, Layout.key d.C P.S i = (0, 0) → i = ctr := by
    intro i hi
    unfold Layout.key at hi
    simp only [Prod.mk.injEq] at hi
    have h1 : i % P.S = d.C := by omega
    have h2 : i / P.S = d.C := by omega
    have := Nat.mod_add_div i P.S
    rw [h1, h2] at this
    omega
  rw [lowB, sumIx_eq _ (a₀ := 0), l1_eq]
  rw [← sum_erase_add _ _ (mem_range.mpr hctrlt), ← sum_erase_add _ _ (mem_range.mpr hctrlt)]
  simp only [zero_add]
  have hrest : ∀ i ∈ (range L.length).erase ctr,
      -(|L.getD i 0| : ℤ) ≤
        (if Layout.key d.C P.S i = (0, 0) then L.getD i 0 else -|L.getD i 0|) := by
    intro i hi
    have hne := (mem_erase.mp hi).1
    rw [if_neg (fun h => hne (hkey i h))]
  have hctrk : Layout.key d.C P.S ctr = (0, 0) := by
    unfold Layout.key
    rw [(mod_div_of_lt (by omega)).1, (mod_div_of_lt (by omega)).2]; simp
  rw [if_pos hctrk, hLc]
  have := sum_le_sum hrest
  rw [sum_neg_distrib] at this
  have habs : d.c0 P ≤ |d.c0 P| := le_abs_self _
  rw [hLc] at *
  linarith

end KAM.EffectiveStability.Tube

end
