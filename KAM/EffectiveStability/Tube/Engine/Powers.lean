/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Types
public import KAM.EffectiveStability.Tube.Engine.Horner
public import KAM.EffectiveStability.Tube.Engine.Witness

/-!
# Exact inputs, witnesses and powers (T2-CONF, N7)

The true functions of the Horner stage: `Bt j = denseCos C_P (Bdat j)` (the exact `B_j`),
`Tt n = denseCos C_T (Tdat n)` (the exact `T_n`), `Pt j k = √(Bt j) ^ k`.

* `tIn`, `TCerts_of`: the `T_n` literals against their exact data;
* `pBase j` (inputs `B_j` and `1`, the witnesses `W_j`, `Y_j`) and `pStep j k` (one power
  `P_j(k)` from `P_j(k - 2) · B_j` for `k ≥ 3`, `Y_j · Y_j` for `k = -2`,
  `P_j(k + 2) · P_j(-2)` for `k ≤ -3`), and `PCerts_of`: all power certificates of the range
  `[-(2M+1), N_max]`, by induction on `|k|`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.Certificate KAM.CertificateSharp.Packed

namespace HData

variable (D : HData)

/-- The exact `B_j`. -/
noncomputable def Bt (j : ℕ) : (Fin 2 → ℝ) → ℝ := denseCos D.CP (D.Bdat j)

/-- The exact `T_n`. -/
noncomputable def Tt (n : ℕ × ℕ × ℕ) : (Fin 2 → ℝ) → ℝ := denseCos D.CT (D.Tdat n)

/-- The true powers `√B_j ^ k`. -/
noncomputable def Pt (j : ℕ) (k : ℤ) : (Fin 2 → ℝ) → ℝ := sqrtPow (D.Bt j) k

/-- The input check of a `T_n`. -/
def tIn (n : ℕ × ℕ × ℕ) : Bool :=
  (D.T n).C == D.CT && inputCheck D.P (D.T n) (D.Tdat n) (D.Tc n).e₀ (D.Tc n).e₁ &&
    (D.T n).l1Check D.P (D.Tc n).n

theorem TCerts_of (h : D.ns.all D.tIn = true) : D.TCerts D.Tt := by
  intro n hn
  have := List.all_eq_true.mp h n hn
  simp only [tIn, Bool.and_eq_true, beq_iff_eq] at this
  obtain ⟨⟨hC, hin⟩, hl⟩ := this
  have hc := input_sound hin
  rw [hC] at hc
  have hok : (D.T n).ok D.P = true := by
    simp only [inputCheck, Bool.and_eq_true] at hin; exact hin.1.1.1.1.1
  exact ⟨LitD.wf hok, hc, LitD.l1_le hl⟩

/-- A one-term product step of two powers. -/
def powTerm (j : ℕ) (kA kB : ℤ) (Q : ℚ) : Term :=
  ⟨cOf 1 (D.Pw j kA).q (D.Pw j kB).q Q, 0, 1, (D.Pw j kA).opd D.P, (D.Pw j kB).opd D.P,
    (D.Pc j kA).e₀, (D.Pc j kA).e₁, (D.Pc j kA).n, (D.Pc j kB).e₀, (D.Pc j kB).e₁, (D.Pc j kB).n,
    2 ^ (D.P.b - 1), (j, 0, 0)⟩

/-- The check of the power `P_j(k)` from `P_j(kA) · P_j(kB)`. -/
def powOk (j : ℕ) (kA kB k : ℤ) (o : OPrm) : Bool :=
  litCheck D.P D.CP D.CP false o.Q [D.powTerm j kA kB o.Q] o.E₀ o.E₁ o.BX (D.Pw j k) o.aX o.aO
      o.lD o.F₀ o.F₁ (D.Pc j k).e₀ (D.Pc j k).e₁ (D.Pc j k).n &&
    (D.Pw j k).C == D.CP && symDigOk false (D.Pw j k).C D.P.b (D.Pw j k).X

/-- The full certificate of a power literal. -/
def PCert (j : ℕ) (k : ℤ) : Prop :=
  ((D.Pw j k).opd D.P).Cert D.P.w D.P.S (D.Pt j k) (D.Pc j k).e₀ (D.Pc j k).e₁ (D.Pc j k).n ∧
    ((D.Pw j k).opd D.P).Mx (2 ^ (D.P.b - 1)) ∧
    symOk ((D.Pw j k).opd D.P).par ((D.Pw j k).opd D.P).l = true ∧
    ((D.Pw j k).opd D.P).l.length = Layout.len ((D.Pw j k).opd D.P).C D.P.S

theorem powOk_cert {j : ℕ} {kA kB k : ℤ} {o : OPrm} (h : D.powOk j kA kB k o = true)
    (hA : D.PCert j kA) (hB : D.PCert j kB)
    (hid : ∀ φ, D.Pt j k φ = D.Pt j kA φ * D.Pt j kB φ) : D.PCert j k := by
  simp only [powOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hl, hC⟩, hsym⟩ := h
  have hc := lit_cert hl (fun _ => D.Pt j kA) (fun _ => D.Pt j kB)
    (fun t ht => by simp only [List.mem_singleton] at ht; subst ht; exact hA.1)
    (fun t ht => by simp only [List.mem_singleton] at ht; subst ht; exact hB)
  have hok : (D.Pw j k).ok D.P = true := by
    simp only [litCheck, Bool.and_eq_true] at hl; exact hl.1.1.1.1.1.1.2
  have hpar : (D.Pw j k).par = false := by
    simp only [litCheck, Bool.and_eq_true, beq_iff_eq] at hl; exact hl.1.1.1.1.2
  have hb : 1 ≤ D.P.b := by
    simp only [litCheck, Bool.and_eq_true, decide_eq_true_eq] at hl; exact hl.1.1.1.1.1.2
  have hKS : 2 * (D.Pw j k).C + 1 ≤ D.P.S := by
    simp only [LitD.ok, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1.1.2
  have hs := LitD.sym (d := D.Pw j k) hb hKS (by rw [hpar]; exact hsym)
  refine ⟨?_, LitD.mx hb, hs⟩
  have hfun : (fun φ => ([D.powTerm j kA kB o.Q].map fun t =>
      (t.ρ : ℝ) * (D.Pt j kA φ * D.Pt j kB φ)).sum) = D.Pt j k := by
    funext φ; simp [powTerm, hid φ]
  rw [hfun] at hc
  exact hc

/-- The base checks of mode `j`: the inputs `B_j` and `1`, the witnesses `W_j`, `Y_j`. -/
def pBase (j : ℕ) (s : SqPrm) (i : IvPrm) : Bool :=
  (D.Pw j 2).C == D.CP && (D.Pw j 0).C == D.CP && (D.Pw j 1).C == D.CP &&
    inputCheck D.P (D.Pw j 2) (D.Bdat j) (D.Pc j 2).e₀ (D.Pc j 2).e₁ &&
    (D.Pw j 2).l1Check D.P (D.Pc j 2).n && symDigOk false (D.Pw j 2).C D.P.b (D.Pw j 2).X &&
    inputCheck D.P (D.Pw j 0) (oneData D.CP) (D.Pc j 0).e₀ (D.Pc j 0).e₁ &&
    (D.Pw j 0).l1Check D.P (D.Pc j 0).n && symDigOk false (D.Pw j 0).C D.P.b (D.Pw j 0).X &&
    sqrtCheck D.P (D.Pw j 2) (D.Pw j 1) (D.Pc j 2).e₀ (D.Pc j 2).e₁ (D.Pc j 2).n (D.Pc j 1).n s.Q
      s.E₀ s.E₁ s.BX s.aX s.aO s.lD s.F₀ s.F₁ s.ρ s.ρ' s.σ₀ s.w₀ (D.Pc j 1).e₀ (D.Pc j 1).e₁ &&
    invCheck D.P (D.Pw j 1) (D.Pw j (-1)) (D.Pw j 0) (D.Pc j 1).e₀ (D.Pc j 1).e₁ (D.Pc j 1).n
      (D.Pc j (-1)).n (D.Pc j 0).n (D.Pc j 0).e₀ (D.Pc j 0).e₁ i.Q i.E₀ i.E₁ i.BX i.aX i.aO i.lD
      i.F₀ i.F₁ i.qq i.qq' s.σ₀ (D.Pc j (-1)).e₀ (D.Pc j (-1)).e₁

/-- All checks of mode `j`. -/
def pAll (j : ℕ) (s : SqPrm) (i : IvPrm) (pp : ℤ → OPrm) : Bool :=
  D.pBase j s i &&
    (List.range (D.Nmax + 1)).all (fun k => decide (k < 3) || D.powOk j (k - 2) 2 k (pp k)) &&
    D.powOk j (-1) (-1) (-2) (pp (-2)) &&
    (List.range (2 * D.M + 2)).all fun k =>
      decide (k < 3) || D.powOk j (-((k : ℤ) - 2)) (-2) (-(k : ℤ)) (pp (-(k : ℤ)))

/-- **All power certificates of a mode.** -/
theorem PCert_of {j : ℕ} {s : SqPrm} {i : IvPrm} {pp : ℤ → OPrm} (h : D.pAll j s i pp = true) :
    ∀ k : ℤ, -(2 * D.M + 1 : ℤ) ≤ k → k ≤ D.Nmax → D.PCert j k := by
  simp only [pAll, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨hbase, hpos⟩, hm2⟩, hneg⟩ := h
  simp only [pBase, Bool.and_eq_true, beq_iff_eq] at hbase
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hC2, hC0⟩, hC1⟩, hinB⟩, hlB⟩, hsB⟩, hin1⟩, hl1⟩, hs1⟩, hsq⟩, hinv⟩ := hbase
  -- the base literals
  have hokB : (D.Pw j 2).ok D.P = true := by
    simp only [inputCheck, Bool.and_eq_true] at hinB; exact hinB.1.1.1.1.1
  have hok1 : (D.Pw j 0).ok D.P = true := by
    simp only [inputCheck, Bool.and_eq_true] at hin1; exact hin1.1.1.1.1.1
  have hb : 1 ≤ D.P.b := by
    simp only [LitD.l1Check, Bool.and_eq_true, decide_eq_true_eq] at hlB; exact hlB.1.1.2
  have hparB : (D.Pw j 2).par = false := by
    simp only [inputCheck, Bool.and_eq_true, Bool.not_eq_true'] at hinB; exact hinB.1.1.1.1.2
  have hpar1 : (D.Pw j 0).par = false := by
    simp only [inputCheck, Bool.and_eq_true, Bool.not_eq_true'] at hin1; exact hin1.1.1.1.1.2
  have hKS : ∀ d : LitD, d.ok D.P = true → 2 * d.C + 1 ≤ D.P.S := fun d hd => by
    simp only [LitD.ok, Bool.and_eq_true, decide_eq_true_eq] at hd; exact hd.1.1.2
  have hcB := input_sound hinB
  rw [hC2] at hcB
  have hBl := LitD.l1_le hlB
  obtain ⟨hsqc, hσB, hWl, hσ, hokW, -, hWsym⟩ := sqrt_sound hsq hcB hBl
  have hBpos : ∀ φ, 0 < D.Bt j φ := fun φ => (pow_pos hσ 2).trans_le (hσB φ)
  have hc1 := input_sound hin1
  rw [hC0, denseCos_oneData] at hc1
  obtain ⟨hinvc, hYl, hokY, hYsym⟩ := invSqrt_sound hinv hsqc hσB hc1
  -- the four base certificates
  have P2 : D.PCert j 2 := by
    refine ⟨⟨LitD.wf hokB, ?_, hBl⟩, LitD.mx hb,
      LitD.sym hb (hKS _ hokB) (by rw [hparB]; exact hsB)⟩
    rw [show D.Pt j 2 = D.Bt j from sqrtPow_two fun φ => (hBpos φ).le]
    exact hcB
  have P0 : D.PCert j 0 := by
    refine ⟨⟨LitD.wf hok1, ?_, LitD.l1_le hl1⟩, LitD.mx hb,
      LitD.sym hb (hKS _ hok1) (by rw [hpar1]; exact hs1)⟩
    rw [show D.Pt j 0 = fun _ => 1 from sqrtPow_zero _]
    exact hc1
  have P1 : D.PCert j 1 := by
    refine ⟨⟨LitD.wf hokW, ?_, hWl⟩, LitD.mx hb, hWsym⟩
    rw [show D.Pt j 1 = fun φ => √(D.Bt j φ) from sqrtPow_one _]
    exact hsqc
  have Pm1 : D.PCert j (-1) := by
    refine ⟨⟨LitD.wf hokY, ?_, hYl⟩, LitD.mx hb, hYsym⟩
    rw [show D.Pt j (-1) = fun φ => 1 / √(D.Bt j φ) from sqrtPow_neg_one _]
    exact hinvc
  -- the positive chain
  have hP : ∀ k : ℕ, k ≤ D.Nmax → D.PCert j k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | rfl | h3
      · exact P0
      · exact P1
      · exact P2
      · have hstep := (hpos k (by omega)).resolve_left (by omega)
        refine D.powOk_cert hstep ?_ P2 fun φ => ?_
        · have := ih (k - 2) (by omega) (by omega)
          rwa [show ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 by omega] at this
        · rw [Pt, Pt, Pt, ← sqrtPow_add (hBpos φ)]; congr 1; ring
  -- the negative chain
  have Pm2 : D.PCert j (-2) :=
    D.powOk_cert hm2 Pm1 Pm1 fun φ => by
      rw [Pt, Pt, ← sqrtPow_add (hBpos φ)]; norm_num
  have hN : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * D.M + 1 → D.PCert j (-(k : ℤ)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk1 hk
      rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | h3
      · simpa using Pm1
      · simpa using Pm2
      · have hstep := (hneg k (by omega)).resolve_left (by omega)
        refine D.powOk_cert hstep ?_ Pm2 fun φ => ?_
        · have := ih (k - 2) (by omega) (by omega) (by omega)
          rwa [show ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 by omega] at this
        · rw [Pt, Pt, Pt, ← sqrtPow_add (hBpos φ)]; congr 1; ring
  intro k hk1 hk2
  rcases le_or_gt 0 k with h0 | h0
  · have := hP k.toNat (by omega)
    rwa [Int.toNat_of_nonneg h0] at this
  · have := hN (-k).toNat (by omega) (by omega)
    rwa [Int.toNat_of_nonneg (by omega), neg_neg] at this

/-- **The power certificates of all three modes.** -/
theorem PCerts_of {s : ℕ → SqPrm} {i : ℕ → IvPrm} {pp : ℕ → ℤ → OPrm}
    (h : ∀ j < 3, D.pAll j (s j) (i j) (pp j) = true) : D.PCerts D.Pt :=
  fun j hj k hk1 hk2 => D.PCert_of (h j hj) k hk1 hk2

end HData

end KAM.EffectiveStability.Tube

end
