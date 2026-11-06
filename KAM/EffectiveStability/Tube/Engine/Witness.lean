/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Block
public import KAM.EffectiveStability.Tube.Witness.InvSqrt

/-!
# Square-root witnesses in the kernel (T2-CONF, N7)

The checks feeding N4's `C1Close.sqrt_witness` and `C1Close.invSqrt_witness` from packed data:
* `sqrtCheck`, `sqrt_sound`: a literal `W` (even, symmetric) with `W·W` compared with the literal of
  `B` (whose certificate is given), `B ≥ σ₀²` and `W ≥ w₀` from centre digits and `ℓ¹`
  (`lowB_litList`): `C1Close √B W e₀ e₁`;
* `invCheck`, `invSqrt_sound`: a literal `Y` with `W·Y` compared with the literal of the constant
  `1`: `C1Close (1/√B) Y e₀ e₁`;
* `oneData`, `denseCos_oneData`: the exact constant `1`;
* `sqrtPow B k = √B ^ k` (`k : ℤ`): the true powers, with `sqrtPow_add` (for `B > 0`).
All error expressions are rational (`sqrtErr₀Q`, …, cast to N4's real ones).
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.Certificate KAM.CertificateSharp.Packed

/-- The term `A · B` of two literal operands with exact (zero-error) certificates. -/
def wTerm (P : Prm) (dA dB : LitD) (na nb : ℕ) : Term :=
  ⟨1, 0, 1, dA.opd P, dB.opd P, 0, 0, na, 0, 0, nb, 2 ^ (P.b - 1), (0, 0, 0)⟩

/-- The exact certificate of a literal for its own value. -/
theorem LitD.self_cert {P : Prm} {d : LitD} (hok : d.ok P = true) {n : ℕ}
    (hn : l1 (d.opd P).l ≤ n) : (d.opd P).Cert P.w P.S ((d.opd P).eval P.S) 0 0 n :=
  ⟨LitD.wf hok, by simpa using C1Close.refl (Opd.differentiable_eval P.S (d.opd P)), hn⟩

theorem single_sum (t : Term) (fA fB : Term → (Fin 2 → ℝ) → ℝ) :
    (fun φ => ([t].map fun t => (t.ρ : ℝ) * (fA t φ * fB t φ)).sum) =
      fun φ => (t.ρ : ℝ) * (fA t φ * fB t φ) := by
  funext φ; simp

/-- `N4`'s value error, rationally. -/
def sqrtErr₀Q (σ₀ w₀ ρ : ℚ) : ℚ := ρ / (σ₀ + w₀)

/-- `N4`'s derivative error, rationally. -/
def sqrtErr₁Q (σ₀ w₀ ρ ρ' ω₁ : ℚ) : ℚ := (ρ' + 2 * sqrtErr₀Q σ₀ w₀ ρ * ω₁) / (2 * σ₀)

/-- The square-root witness check. -/
def sqrtCheck (P : Prm) (dB dW : LitD) (eB₀ eB₁ : ℚ) (nB nW : ℕ) (Q E₀ E₁ : ℚ) (BX αX αO lD : ℕ)
    (F₀ F₁ ρ ρ' σ₀ w₀ e₀ e₁ : ℚ) : Bool :=
  dW.ok P && !dW.par && decide (1 ≤ P.b) && decide (2 * dW.C + 1 ≤ P.S) &&
    symDigOk false dW.C P.b dW.X && dW.l1Check P nW &&
    litCheck P dW.C dW.C false Q [wTerm P dW dW nW nW] E₀ E₁ BX dB αX αO lD F₀ F₁ (ρ - eB₀)
      (ρ' - eB₁) nB &&
    decide (2 * dB.C + 1 ≤ P.S) && !dB.par && decide (0 < dB.q) && decide (0 < σ₀) &&
    decide (σ₀ ^ 2 ≤ dB.q * (2 * dB.c0 P - nB) - eB₀) &&
    decide (0 < dW.q) && decide (0 ≤ w₀) && decide (w₀ ≤ dW.q * (2 * dW.c0 P - nW)) &&
    decide (sqrtErr₀Q σ₀ w₀ ρ ≤ e₀) &&
    decide (sqrtErr₁Q σ₀ w₀ ρ ρ' (dW.q * (dW.C * nW)) ≤ e₁)

theorem lit_ge {P : Prm} {d : LitD} (hKS : 2 * d.C + 1 ≤ P.S) (hq : 0 < d.q) (hpar : d.par = false)
    {n : ℕ} (hn : l1 (d.opd P).l ≤ n) (φ : Fin 2 → ℝ) :
    ((d.q * (2 * d.c0 P - n) : ℚ) : ℝ) ≤ (d.opd P).eval P.S φ := by
  have h1 := lowB_litList (P := P) (d := d) hKS φ
  have h2 : ((2 * d.c0 P - n : ℤ) : ℝ) ≤ ((2 * d.c0 P - l1 (d.opd P).l : ℤ) : ℝ) := by
    exact_mod_cast (by linarith : (2 * d.c0 P - n : ℤ) ≤ 2 * d.c0 P - l1 (d.opd P).l)
  have hq' : (0 : ℝ) < d.q := by exact_mod_cast hq
  have hpar' : (d.opd P).par = false := hpar
  simp only [Opd.eval]
  rw [show (d.opd P).q = d.q from rfl, show (d.opd P).C = d.C from rfl, ← hpar', show
    (d.opd P).par = d.par from rfl] at *
  rw [hpar]
  push_cast at h1 h2 ⊢
  exact mul_le_mul_of_nonneg_left (h2.trans h1) hq'.le

/-- **The square-root witness.** -/
theorem sqrt_sound {P : Prm} {dB dW : LitD} {eB₀ eB₁ : ℚ} {nB nW : ℕ} {Q E₀ E₁ : ℚ}
    {BX αX αO lD : ℕ} {F₀ F₁ ρ ρ' σ₀ w₀ e₀ e₁ : ℚ}
    (h : sqrtCheck P dB dW eB₀ eB₁ nB nW Q E₀ E₁ BX αX αO lD F₀ F₁ ρ ρ' σ₀ w₀ e₀ e₁ = true)
    {Bt : (Fin 2 → ℝ) → ℝ} (hBt : C1Close Bt ((dB.opd P).eval P.S) eB₀ eB₁)
    (hBl : l1 (dB.opd P).l ≤ nB) :
    C1Close (fun φ => √(Bt φ)) ((dW.opd P).eval P.S) e₀ e₁ ∧ (∀ φ, (σ₀ : ℝ) ^ 2 ≤ Bt φ) ∧
      l1 (dW.opd P).l ≤ nW ∧ (0 : ℝ) < σ₀ ∧ dW.ok P = true ∧ 1 ≤ P.b ∧
      symOk (dW.opd P).par (dW.opd P).l = true ∧
      (dW.opd P).l.length = Layout.len (dW.opd P).C P.S := by
  simp only [sqrtCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hok, hpar⟩, hb⟩, hKS⟩, hsym⟩, hWl⟩, hlit⟩, hKSB⟩, hparB⟩, hqB⟩, hσ⟩,
    hσB⟩, hqW⟩, hw₀⟩, hw₀W⟩, he₀⟩, he₁⟩ := h
  have hWl' := LitD.l1_le hWl
  have hWsym := LitD.sym (d := dW) hb hKS (by rw [hpar]; exact hsym)
  have hcert := LitD.self_cert hok hWl'
  have hWW := lit_cert hlit (fun _ => (dW.opd P).eval P.S) (fun _ => (dW.opd P).eval P.S)
    (fun t ht => by simp only [List.mem_singleton] at ht; subst ht; exact hcert)
    (fun t ht => by
      simp only [List.mem_singleton] at ht; subst ht
      refine ⟨hcert, LitD.mx hb, ?_, ?_⟩
      · have := hWsym.1; simpa [wTerm, LitD.opd, hpar] using this
      · exact hWsym.2)
  rw [single_sum] at hWW
  have hclose : C1Close Bt (fun φ => (dW.opd P).eval P.S φ * (dW.opd P).eval P.S φ) ρ ρ' := by
    have := hBt.trans (hWW.close.symm)
    have hfun : (fun φ => ((wTerm P dW dW nW nW).ρ : ℝ) * ((dW.opd P).eval P.S φ *
        (dW.opd P).eval P.S φ)) = fun φ => (dW.opd P).eval P.S φ * (dW.opd P).eval P.S φ := by
      funext φ; simp [wTerm]
    rw [hfun] at this
    exact this.mono (by push_cast; linarith) (by push_cast; linarith)
  have hBd : Differentiable ℝ Bt := hBt.1
  have hWd := Opd.differentiable_eval P.S (dW.opd P)
  have hσ' : (0 : ℝ) < σ₀ := by exact_mod_cast hσ
  have hBge : ∀ φ, (σ₀ : ℝ) ^ 2 ≤ Bt φ := by
    intro φ
    have h1 := lit_ge (P := P) (d := dB) hKSB hqB hparB hBl φ
    have h2 := hBt.abs_sub_le φ
    have h3 : ((σ₀ ^ 2 : ℚ) : ℝ) ≤ ((dB.q * (2 * dB.c0 P - nB) - eB₀ : ℚ) : ℝ) := by
      exact_mod_cast hσB
    push_cast at h1 h3
    rw [abs_le] at h2
    linarith [h2.1]
  have hWge : ∀ φ, (w₀ : ℝ) ≤ (dW.opd P).eval P.S φ := by
    intro φ
    have h1 := lit_ge (P := P) (d := dW) hKS hqW hpar hWl' φ
    have h3 : ((w₀ : ℚ) : ℝ) ≤ ((dW.q * (2 * dW.c0 P - nW) : ℚ) : ℝ) := by exact_mod_cast hw₀W
    linarith
  have hρ : ∀ φ, |Bt φ - (dW.opd P).eval P.S φ * (dW.opd P).eval P.S φ| ≤ (ρ : ℝ) :=
    fun φ => hclose.abs_sub_le φ
  have hρ' : ∀ φ a, |pderiv (fun φ => Bt φ - (dW.opd P).eval P.S φ * (dW.opd P).eval P.S φ) φ a|
      ≤ (ρ' : ℝ) := by
    intro φ a
    rw [show (fun φ => Bt φ - (dW.opd P).eval P.S φ * (dW.opd P).eval P.S φ) =
      Bt - (fun φ => (dW.opd P).eval P.S φ * (dW.opd P).eval P.S φ) from rfl,
      C1Close.pderiv_sub (g := fun φ => (dW.opd P).eval P.S φ * (dW.opd P).eval P.S φ) hBd
        (fun φ => (hWd φ).mul (hWd φ))]
    exact hclose.abs_pderiv_sub_le φ a
  have hω : ∀ φ a, |pderiv ((dW.opd P).eval P.S) φ a| ≤ ((dW.q * (dW.C * nW) : ℚ) : ℝ) := by
    intro φ a
    have := Opd.abs_pderiv_eval_le (w := P.w) (o := dW.opd P) (by
      show 2 * dW.C < P.S; omega) (LitD.wf hok) hWl' φ a
    have hq' : (0 : ℝ) < dW.q := by exact_mod_cast hqW
    rw [show (dW.opd P).q = dW.q from rfl, show (dW.opd P).C = dW.C from rfl,
      abs_of_pos hq'] at this
    push_cast; exact this
  have hw0' : (0 : ℝ) ≤ w₀ := by exact_mod_cast hw₀
  have hsq := C1Close.sqrt_witness hBd hWd hσ' hBge hw0' hWge hρ hρ' hω
  refine ⟨hsq.mono ?_ ?_, hBge, hWl', hσ', hok, hb, hWsym⟩
  · have : sqrtErr₀ (σ₀ : ℝ) (w₀ : ℝ) (ρ : ℝ) = ((sqrtErr₀Q σ₀ w₀ ρ : ℚ) : ℝ) := by
      simp [sqrtErr₀, sqrtErr₀Q]
    rw [this]; exact_mod_cast he₀
  · have : sqrtErr₁ (σ₀ : ℝ) (w₀ : ℝ) (ρ : ℝ) (ρ' : ℝ) ((dW.q * (dW.C * nW) : ℚ) : ℝ) =
        ((sqrtErr₁Q σ₀ w₀ ρ ρ' (dW.q * (dW.C * nW)) : ℚ) : ℝ) := by
      simp [sqrtErr₁, sqrtErr₁Q, sqrtErr₀, sqrtErr₀Q]
    rw [this]; exact_mod_cast he₁

/-! ### The inverse square root -/

/-- `N4`'s inverse-square-root value error, rationally. -/
def invErr₀Q (σ₀ e₀ q Y₀ : ℚ) : ℚ := (q + e₀ * Y₀) / σ₀

/-- `N4`'s inverse-square-root derivative error, rationally. -/
def invErr₁Q (σ₀ e₀ e₁ ω₁ q q' Y₀ Y₁ : ℚ) : ℚ :=
  (q' + e₁ * Y₀ + e₀ * Y₁) / σ₀ + (q + e₀ * Y₀) * (ω₁ + e₁) / σ₀ ^ 2

/-- The inverse-square-root witness check. -/
def invCheck (P : Prm) (dW dY dOne : LitD) (eW₀ eW₁ : ℚ) (nW nY nOne : ℕ) (eO₀ eO₁ : ℚ)
    (Q E₀ E₁ : ℚ) (BX αX αO lD : ℕ) (F₀ F₁ qq qq' σ₀ e₀ e₁ : ℚ) : Bool :=
  dW.ok P && dY.ok P && !dY.par && decide (1 ≤ P.b) && decide (2 * dY.C + 1 ≤ P.S) &&
    decide (2 * dW.C + 1 ≤ P.S) && symDigOk false dY.C P.b dY.X && dY.l1Check P nY &&
    dW.l1Check P nW &&
    litCheck P dW.C dY.C false Q [wTerm P dW dY nW nY] E₀ E₁ BX dOne αX αO lD F₀ F₁ (qq - eO₀)
      (qq' - eO₁) nOne &&
    decide (0 < σ₀) && decide (0 < dW.q) && decide (0 < dY.q) &&
    decide (invErr₀Q σ₀ eW₀ qq (dY.q * nY) ≤ e₀) &&
    decide (invErr₁Q σ₀ eW₀ eW₁ (dW.q * (dW.C * nW)) qq qq' (dY.q * nY) (dY.q * (dY.C * nY)) ≤ e₁)

/-- **The inverse-square-root witness.** -/
theorem invSqrt_sound {P : Prm} {dW dY dOne : LitD} {eW₀ eW₁ : ℚ} {nW nY nOne : ℕ} {eO₀ eO₁ : ℚ}
    {Q E₀ E₁ : ℚ} {BX αX αO lD : ℕ} {F₀ F₁ qq qq' σ₀ e₀ e₁ : ℚ}
    (h : invCheck P dW dY dOne eW₀ eW₁ nW nY nOne eO₀ eO₁ Q E₀ E₁ BX αX αO lD F₀ F₁ qq qq' σ₀ e₀ e₁
      = true) {Bt : (Fin 2 → ℝ) → ℝ}
    (H : C1Close (fun φ => √(Bt φ)) ((dW.opd P).eval P.S) eW₀ eW₁)
    (hB : ∀ φ, (σ₀ : ℝ) ^ 2 ≤ Bt φ)
    (hOne : C1Close (fun _ => (1 : ℝ)) ((dOne.opd P).eval P.S) eO₀ eO₁) :
    C1Close (fun φ => 1 / √(Bt φ)) ((dY.opd P).eval P.S) e₀ e₁ ∧ l1 (dY.opd P).l ≤ nY ∧
      dY.ok P = true ∧ symOk (dY.opd P).par (dY.opd P).l = true ∧
      (dY.opd P).l.length = Layout.len (dY.opd P).C P.S := by
  simp only [invCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hokW, hokY⟩, hparY⟩, hb⟩, hKSY⟩, hKSW⟩, hsym⟩, hYl⟩, hWl⟩, hlit⟩,
    hσ⟩, hqW⟩, hqY⟩, he₀⟩, he₁⟩ := h
  have hYl' := LitD.l1_le hYl
  have hWl' := LitD.l1_le hWl
  have hYsym := LitD.sym (d := dY) hb hKSY (by rw [hparY]; exact hsym)
  have hcW := LitD.self_cert hokW hWl'
  have hcY := LitD.self_cert hokY hYl'
  have hWY := lit_cert hlit (fun _ => (dW.opd P).eval P.S) (fun _ => (dY.opd P).eval P.S)
    (fun t ht => by simp only [List.mem_singleton] at ht; subst ht; exact hcW)
    (fun t ht => by
      simp only [List.mem_singleton] at ht; subst ht
      refine ⟨hcY, LitD.mx hb, ?_, ?_⟩
      · have := hYsym.1; simpa [wTerm, LitD.opd, hparY] using this
      · exact hYsym.2)
  rw [single_sum] at hWY
  have hWd := Opd.differentiable_eval P.S (dW.opd P)
  have hYd := Opd.differentiable_eval P.S (dY.opd P)
  have hclose : C1Close (fun _ => (1 : ℝ))
      (fun φ => (dW.opd P).eval P.S φ * (dY.opd P).eval P.S φ) qq qq' := by
    have := hOne.trans (hWY.close.symm)
    have hfun : (fun φ => ((wTerm P dW dY nW nY).ρ : ℝ) * ((dW.opd P).eval P.S φ *
        (dY.opd P).eval P.S φ)) = fun φ => (dW.opd P).eval P.S φ * (dY.opd P).eval P.S φ := by
      funext φ; simp [wTerm]
    rw [hfun] at this
    exact this.mono (by push_cast; linarith) (by push_cast; linarith)
  have hσ' : (0 : ℝ) < σ₀ := by exact_mod_cast hσ
  have hqW' : (0 : ℝ) < dW.q := by exact_mod_cast hqW
  have hqY' : (0 : ℝ) < dY.q := by exact_mod_cast hqY
  have hω : ∀ φ a, |pderiv ((dW.opd P).eval P.S) φ a| ≤ ((dW.q * (dW.C * nW) : ℚ) : ℝ) := by
    intro φ a
    have := Opd.abs_pderiv_eval_le (w := P.w) (o := dW.opd P) (by
      show 2 * dW.C < P.S; omega) (LitD.wf hokW) hWl' φ a
    rw [show (dW.opd P).q = dW.q from rfl, show (dW.opd P).C = dW.C from rfl,
      abs_of_pos hqW'] at this
    push_cast; exact this
  have hq : ∀ φ, |1 - (dW.opd P).eval P.S φ * (dY.opd P).eval P.S φ| ≤ (qq : ℝ) :=
    fun φ => hclose.abs_sub_le φ
  have hq' : ∀ φ a, |pderiv (fun φ => 1 - (dW.opd P).eval P.S φ * (dY.opd P).eval P.S φ) φ a|
      ≤ (qq' : ℝ) := by
    intro φ a
    rw [show (fun φ => 1 - (dW.opd P).eval P.S φ * (dY.opd P).eval P.S φ) =
      (fun _ => (1 : ℝ)) - (fun φ => (dW.opd P).eval P.S φ * (dY.opd P).eval P.S φ) from rfl,
      C1Close.pderiv_sub (g := fun φ => (dW.opd P).eval P.S φ * (dY.opd P).eval P.S φ)
        (differentiable_const 1) (fun φ => (hWd φ).mul (hYd φ))]
    exact hclose.abs_pderiv_sub_le φ a
  have hY₀ : ∀ φ, |(dY.opd P).eval P.S φ| ≤ ((dY.q * nY : ℚ) : ℝ) := by
    intro φ
    have := Opd.abs_eval_le (w := P.w) (S := P.S) hYl' φ
    rw [show (dY.opd P).q = dY.q from rfl, abs_of_pos hqY'] at this
    push_cast; exact this
  have hY₁ : ∀ φ a, |pderiv ((dY.opd P).eval P.S) φ a| ≤ ((dY.q * (dY.C * nY) : ℚ) : ℝ) := by
    intro φ a
    have := Opd.abs_pderiv_eval_le (w := P.w) (o := dY.opd P) (by
      show 2 * dY.C < P.S; omega) (LitD.wf hokY) hYl' φ a
    rw [show (dY.opd P).q = dY.q from rfl, show (dY.opd P).C = dY.C from rfl,
      abs_of_pos hqY'] at this
    push_cast; exact this
  have hinv := C1Close.invSqrt_witness H hσ' hB hω hYd hq hq' hY₀ hY₁
  refine ⟨hinv.mono ?_ ?_, hYl', hokY, hYsym⟩
  · have : invSqrtErr₀ (σ₀ : ℝ) (eW₀ : ℝ) (qq : ℝ) ((dY.q * nY : ℚ) : ℝ) =
        ((invErr₀Q σ₀ eW₀ qq (dY.q * nY) : ℚ) : ℝ) := by
      simp [invSqrtErr₀, invErr₀Q]
    rw [this]; exact_mod_cast he₀
  · have : invSqrtErr₁ (σ₀ : ℝ) (eW₀ : ℝ) (eW₁ : ℝ) ((dW.q * (dW.C * nW) : ℚ) : ℝ) (qq : ℝ)
        (qq' : ℝ) ((dY.q * nY : ℚ) : ℝ) ((dY.q * (dY.C * nY) : ℚ) : ℝ) =
        ((invErr₁Q σ₀ eW₀ eW₁ (dW.q * (dW.C * nW)) qq qq' (dY.q * nY) (dY.q * (dY.C * nY)) : ℚ) :
          ℝ) := by
      simp [invSqrtErr₁, invErr₁Q]
    rw [this]; exact_mod_cast he₁

/-! ### The constant one and the true powers -/

/-- The exact constant `1` on the square box of half-width `C`. -/
def oneData (C : ℕ) : List ℚ :=
  (List.range ((2 * C + 1) * (2 * C + 1))).map fun i => if i = C + (2 * C + 1) * C then 1 else 0

theorem denseCos_oneData (C : ℕ) : denseCos C (oneData C) = fun _ => 1 := by
  funext φ
  unfold denseCos evalR
  have hctr : C + (2 * C + 1) * C < (2 * C + 1) * (2 * C + 1) := by nlinarith
  rw [sum_eq_single (C + (2 * C + 1) * C)]
  · beta_reduce
    rw [oneData, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hctr]
    simp only [Option.map_some, Option.getD_some, if_pos rfl]
    have hk : boxKey C (C + (2 * C + 1) * C) = (0, 0) := by
      unfold boxKey
      rw [(mod_div_of_lt (S := 2 * C + 1) (by omega)).1, (mod_div_of_lt (S := 2 * C + 1)
        (by omega)).2]
      simp
    rw [hk, kdot_zero, trig_false_zero]; simp
  · intro i hi hne
    beta_reduce
    rw [oneData, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range
      (mem_range.mp hi)]
    simp [hne]
  · intro h; exact absurd (mem_range.mpr hctr) h

/-- The true power `√B ^ k`, `k : ℤ`. -/
noncomputable def sqrtPow (B : (Fin 2 → ℝ) → ℝ) (k : ℤ) (φ : Fin 2 → ℝ) : ℝ := √(B φ) ^ k

theorem sqrtPow_add {B : (Fin 2 → ℝ) → ℝ} {φ : Fin 2 → ℝ} (hB : 0 < B φ) (k l : ℤ) :
    sqrtPow B (k + l) φ = sqrtPow B k φ * sqrtPow B l φ := by
  unfold sqrtPow
  exact zpow_add₀ (Real.sqrt_pos.mpr hB).ne' k l

theorem sqrtPow_one (B : (Fin 2 → ℝ) → ℝ) : sqrtPow B 1 = fun φ => √(B φ) := by
  funext φ; simp [sqrtPow]

theorem sqrtPow_neg_one (B : (Fin 2 → ℝ) → ℝ) : sqrtPow B (-1) = fun φ => 1 / √(B φ) := by
  funext φ; simp [sqrtPow]

theorem sqrtPow_zero (B : (Fin 2 → ℝ) → ℝ) : sqrtPow B 0 = fun _ => 1 := by
  funext φ; simp [sqrtPow]

theorem sqrtPow_two {B : (Fin 2 → ℝ) → ℝ} (hB : ∀ φ, 0 ≤ B φ) : sqrtPow B 2 = B := by
  funext φ; simp [sqrtPow, Real.sq_sqrt (hB φ)]

end KAM.EffectiveStability.Tube

end
