/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Types
public import KAM.EffectiveStability.Tube.Engine.Step
public import KAM.EffectiveStability.Tube.Trig.Literal

/-!
# Literal operands and exact inputs (T2-CONF, N7)

* `Prm` (slot width `w`, stride `S`, compact digit width `b`), `LitD` (a whitened compact literal
  with its half-width, parity, scale and spread rounds), `LitD.opd` its operand:
  `LitD.wf` (well formed), `LitD.mx` (slots below `2^(b-1)`), `LitD.sym` (symmetry from the compact
  digits), `LitD.l1_le` (an `ℓ¹` claim checked by `l1P`).
* `LitD.l1Check`: the kernel `ℓ¹` claim (one load check and one packed `ℓ¹`).

The exact-input layer (real-coefficient sums, compact-digit evaluation, the input rounding checks)
is a later stage of the engine and is not part of this module.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.Certificate KAM.CertificateSharp.Packed

/-- The unwhitened compact number. -/
def LitD.X (d : LitD) : ℕ := unwhiten d.salt 288 d.nch d.lit

/-- The packed value (kernel). -/
def LitD.Z (P : Prm) (d : LitD) : ℤ := litZ d.C P.S P.b P.w d.L₁ d.L₂ d.X

/-- The operand of a literal. -/
def LitD.opd (P : Prm) (d : LitD) : Opd := ⟨d.C, d.par, d.q, litList d.C P.S P.b d.X, d.Z P⟩

/-- The structural guard of a literal (metadata only). -/
def LitD.ok (P : Prm) (d : LitD) : Bool :=
  decide (0 < P.b) && decide (P.b ≤ P.w) && decide (2 * d.C + 1 ≤ P.S) &&
    decide ((2 * d.C + 1) * (2 * d.C + 1) ≤ 2 ^ d.L₁) && decide (2 * d.C + 1 ≤ 2 ^ d.L₂)

theorem LitD.wf {P : Prm} {d : LitD} (h : d.ok P = true) : (d.opd P).WF P.w P.S := by
  simp only [LitD.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hb, hbw⟩, hKS⟩, h1⟩, h2⟩ := h
  exact ⟨(litZ_eq hb hbw hKS h1 h2).symm, colsOk_litList _ _ _ _, (length_litList _ _ _ _).le⟩

theorem LitD.mx {P : Prm} {d : LitD} (hb : 1 ≤ P.b) : (d.opd P).Mx (2 ^ (P.b - 1)) := by
  intro x hx
  have := abs_litList_lt hb x hx
  push_cast
  rw [abs_le]; constructor <;> linarith [this.1, this.2]

theorem LitD.sym {P : Prm} {d : LitD} (hb : 1 ≤ P.b) (hKS : 2 * d.C + 1 ≤ P.S)
    (h : symDigOk d.par d.C P.b d.X = true) :
    symOk (d.opd P).par (d.opd P).l = true ∧ (d.opd P).l.length = Layout.len (d.opd P).C P.S :=
  ⟨symOk_litList hb hKS h, length_litList _ _ _ _⟩

/-- The `ℓ¹` claim of a literal (kernel: one load check and one packed `ℓ¹`). -/
def LitD.l1Check (P : Prm) (d : LitD) (n : ℕ) : Bool :=
  d.ok P && decide (1 ≤ P.b) && l1Ok P.w (Layout.len d.C P.S) (P.b - 1) (d.Z P) &&
    decide (l1P P.w (Layout.len d.C P.S) (P.b - 1) (d.Z P) ≤ n)

theorem LitD.l1_le {P : Prm} {d : LitD} {n : ℕ} (h : d.l1Check P n = true) :
    l1 (d.opd P).l ≤ n := by
  simp only [LitD.l1Check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hok, hb⟩, hl⟩, hn⟩ := h
  have hwf := LitD.wf hok
  have hl' := hl
  simp only [l1Ok, Bool.and_eq_true, decide_eq_true_eq] at hl'
  have hsb : SlotsBounded P.w (d.opd P).l := fun c hc => by
    have h1 := abs_litList_lt hb c hc
    have h2 : (2 : ℤ) ^ (P.b - 1 + 2) ≤ 2 ^ P.w := pow_le_pow_right₀ (by norm_num) hl'.1.1.2
    have h3 : (2 : ℤ) ^ (P.b - 1 + 2) = 4 * 2 ^ (P.b - 1) := by rw [pow_add]; ring
    rcases abs_cases c with ⟨hc', -⟩ | ⟨hc', -⟩ <;> rw [hc'] <;> linarith [h1.1, h1.2]
  have := l1P_eq hl hwf.pack (length_litList _ _ _ _) hsb
  rw [← this]
  exact_mod_cast hn

end KAM.EffectiveStability.Tube

end
