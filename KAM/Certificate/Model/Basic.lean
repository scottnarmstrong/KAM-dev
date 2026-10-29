/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Poly.Basic
public import KAM.Certificate.Arith.Roots
public import KAM.Certificate.Arith.Transcendental
public import KAM.Frozen.Defs.ComplexStrip

/-!
# Fourier models: exact polynomial plus a sup radius on the open strip

`CertModel α` is the function `(2π)^deg (P + T)` with `sup_{T_ρ} |T| ≤ rad`. A `CertWeight`
`w ≥ e^{2πρ}` (checked by `checkWeight`) gives `|χ_k| ≤ w^{|k|₁}` on the strip, whence the
certified sup bound `CertModel.supBound`.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM CertArith

/-- A strip weight `w ≥ e^{2πρ}` (checked by `checkWeight`); `|χ_k| ≤ w^{|k|₁}` on `T_ρ`. -/
structure CertWeight where
  rho : ℚ
  w : ℚ

/-- `0 < ρ` (positive width: no vacuous strip feeds a real-point bound) and `e^{2πρ} ≤ w` via
`ratExpUp` and `piUpQ`. -/
def checkWeight (W : CertWeight) (s N : ℕ) : Bool :=
  decide (0 < W.rho) && decide (ratExpUp (2 * piUpQ * W.rho) s N ≤ W.w)

theorem CertWeight.rho_pos {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) :
    (0 : ℝ) < W.rho := by
  simp only [checkWeight, Bool.and_eq_true, decide_eq_true_eq] at hW
  exact_mod_cast hW.1

theorem CertWeight.exp_le_w {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) :
    Real.exp (2 * Real.pi * W.rho) ≤ W.w := by
  have hρ := CertWeight.rho_pos hW
  simp only [checkWeight, Bool.and_eq_true, decide_eq_true_eq] at hW
  have h0 : (0 : ℚ) ≤ 2 * piUpQ * W.rho := by
    have : (0 : ℚ) < W.rho := by exact_mod_cast hρ
    have : (0 : ℝ) < piUpQ := (Real.pi_pos).trans pi_lt_piUpQ
    have : (0 : ℚ) < piUpQ := by exact_mod_cast this
    positivity
  calc Real.exp (2 * Real.pi * W.rho) ≤ Real.exp ((2 * piUpQ * W.rho : ℚ) : ℝ) := by
        apply Real.exp_le_exp.mpr
        push_cast
        have := pi_lt_piUpQ.le
        nlinarith
    _ ≤ (ratExpUp (2 * piUpQ * W.rho) s N : ℝ) := exp_le_ratExpUp h0 s N
    _ ≤ W.w := by exact_mod_cast hW.2

theorem CertWeight.one_le_w {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) :
    (1 : ℝ) ≤ W.w := by
  refine le_trans ?_ (CertWeight.exp_le_w hW)
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have := CertWeight.rho_pos hW
  positivity

theorem norm_character_le_weight {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (k : Fin n → ℤ) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n W.rho) :
    ‖character k θ‖ ≤ (W.w : ℝ) ^ (∑ i, (k i).natAbs) := by
  refine (norm_character_le k hθ).trans ?_
  have hm : Fourier.modeSize k = ((∑ i, (k i).natAbs : ℕ) : ℝ) := by
    simp [Fourier.modeSize, Nat.cast_sum, Nat.cast_natAbs]
  rw [hm, mul_comm, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) (CertWeight.exp_le_w hW) _

/-- A Fourier model: the function `(2π)^deg (P + T)` with `sup_{T_ρ} |T| ≤ rad`. -/
structure CertModel (α : Type) where
  deg : ℤ
  poly : CertPoly α
  rad : α

/-- `m` encloses `f` on the open strip `T_ρ` (sup norm, `2π`-degree factored out). -/
def CertModel.Encloses {α : Type} [CertArith α] (n : ℕ) (ρ : ℝ) (m : CertModel α)
    (f : (Fin n → ℂ) → ℂ) : Prop :=
  ∀ θ ∈ complexStrip n ρ,
    ‖f θ - (2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n θ‖ ≤ (2 * Real.pi) ^ m.deg * val m.rad

section SupBound

variable {α : Type} [CertArith α]

/-- `Σ |c_k| w^{|k|₁}` over the terms, rounded upward (`|k|₁` of the stored list). -/
def CertPoly.weightedNormUp (W : CertWeight) (P : CertPoly α) : α :=
  P.terms.foldr (fun t acc =>
    upAdd (upMul t.2.normUp (ofRatUp (W.w ^ (t.1.map Int.natAbs).sum))) acc) (ofInt 0)

/-- A rational upper bound of `(2π)^d`: `piUpQ` if `d ≥ 0`, `piLoQ` if `d < 0`. -/
def degFactorUp (d : ℤ) : ℚ := if 0 ≤ d then (2 * piUpQ) ^ d else (2 * piLoQ) ^ d

/-- A certified upper bound for `sup_{T_ρ} |f|` of an enclosed `f`: `Σ |c_k| w^{|k|₁} + rad`
times an upper bound of `(2π)^deg` (`piUpQ` if `deg ≥ 0`, `piLoQ` if `deg < 0`). -/
def CertModel.supBound (W : CertWeight) (m : CertModel α) : α :=
  upMul (ofRatUp (degFactorUp m.deg)) (upAdd (m.poly.weightedNormUp W) m.rad)

theorem sum_natAbs_certKeyFun_le (n : ℕ) (k : CertKey) :
    ∑ i : Fin n, (certKeyFun n k i).natAbs ≤ (k.map Int.natAbs).sum := by
  induction k generalizing n with
  | nil => simp [certKeyFun]
  | cons a l ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [Fin.sum_univ_succ]
      have := ih n
      simp only [certKeyFun, List.getD_cons_zero, List.getD_cons_succ, Fin.val_zero,
        Fin.val_succ, List.map_cons, List.sum_cons] at this ⊢
      omega

theorem two_pi_zpow_le (d : ℤ) : (2 * Real.pi) ^ d ≤ (degFactorUp d : ℝ) := by
  have h1 : (2 * (piLoQ : ℝ)) ≤ 2 * Real.pi := by linarith [piLoQ_lt_pi]
  have h2 : 2 * Real.pi ≤ 2 * (piUpQ : ℝ) := by linarith [pi_lt_piUpQ]
  have hlo : (0 : ℝ) < piLoQ := by norm_num [piLoQ]
  unfold degFactorUp
  split_ifs with hd
  · push_cast
    exact zpow_le_zpow_left₀ hd (by positivity) h2
  · push_cast
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = -(m : ℤ) := ⟨(-d).toNat, by omega⟩
    simp only [zpow_neg, zpow_natCast]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 m)

theorem weightedNormUp_bound [LawfulCertArith α] {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (L : List (CertKey × CC α)) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n W.rho) :
    0 ≤ val (L.foldr (fun t acc =>
        upAdd (upMul t.2.normUp (ofRatUp (W.w ^ (t.1.map Int.natAbs).sum))) acc) (ofInt 0)) ∧
      ‖(L.map fun t => t.2.toC * character (certKeyFun n t.1) θ).sum‖ ≤
        val (L.foldr (fun t acc =>
          upAdd (upMul t.2.normUp (ofRatUp (W.w ^ (t.1.map Int.natAbs).sum))) acc) (ofInt 0)) := by
  induction L with
  | nil => simp [LawfulCertArith.val_ofInt]
  | cons t L ih =>
    obtain ⟨ih0, ih1⟩ := ih
    have hw1 := CertWeight.one_le_w hW
    have hq : (0 : ℝ) ≤ ((W.w ^ (t.1.map Int.natAbs).sum : ℚ) : ℝ) := by
      have : (0 : ℝ) ≤ W.w := by linarith
      push_cast; positivity
    have hr := LawfulCertArith.ofRatUp_ge (α := α) (W.w ^ (t.1.map Int.natAbs).sum)
    have hn := CC.normUp_nonneg t.2
    have hm := LawfulCertArith.upMul_ge t.2.normUp
      (ofRatUp (W.w ^ (t.1.map Int.natAbs).sum)) hn (hq.trans hr)
    have hs := LawfulCertArith.upAdd_ge
      (upMul t.2.normUp (ofRatUp (W.w ^ (t.1.map Int.natAbs).sum)))
      (L.foldr (fun t acc =>
        upAdd (upMul t.2.normUp (ofRatUp (W.w ^ (t.1.map Int.natAbs).sum))) acc) (ofInt 0))
    have hterm : ‖t.2.toC * character (certKeyFun n t.1) θ‖ ≤
        val t.2.normUp * ((W.w : ℝ) ^ (t.1.map Int.natAbs).sum) := by
      rw [norm_mul]
      refine mul_le_mul (CC.norm_le_normUp t.2) ((norm_character_le_weight hW _ hθ).trans ?_)
        (norm_nonneg _) hn
      exact pow_le_pow_right₀ hw1 (sum_natAbs_certKeyFun_le n t.1)
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    push_cast at hq hr hm hs
    refine ⟨by linarith [mul_nonneg hn (hq.trans hr)], ?_⟩
    refine (norm_add_le _ _).trans ?_
    have : val t.2.normUp * ((W.w : ℝ) ^ (t.1.map Int.natAbs).sum) ≤
        val t.2.normUp * val (ofRatUp (W.w ^ (t.1.map Int.natAbs).sum) : α) :=
      mul_le_mul_of_nonneg_left hr hn
    linarith

theorem CertModel.norm_le_supBound [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) {m : CertModel α}
    {f : (Fin n → ℂ) → ℂ} (hm : m.Encloses n W.rho f) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n W.rho) : ‖f θ‖ ≤ val (m.supBound W) := by
  have hρ := CertWeight.rho_pos hW
  have h2pi : (0 : ℝ) < (2 * Real.pi) ^ m.deg := by positivity
  have hrad : 0 ≤ val m.rad := by
    have h0 : (0 : Fin n → ℂ) ∈ complexStrip n W.rho := fun i => by simpa using hρ
    have := (norm_nonneg _).trans (hm 0 h0)
    exact nonneg_of_mul_nonneg_right this h2pi
  obtain ⟨hS0, hS⟩ := weightedNormUp_bound hW m.poly.terms hθ
  have hS0' : 0 ≤ val (m.poly.weightedNormUp W) := hS0
  have hadd := LawfulCertArith.upAdd_ge (m.poly.weightedNormUp W) m.rad
  have hF : (0 : ℝ) ≤ (degFactorUp m.deg : ℝ) := h2pi.le.trans (two_pi_zpow_le _)
  have hF' := LawfulCertArith.ofRatUp_ge (α := α) (degFactorUp m.deg)
  have hmul := LawfulCertArith.upMul_ge (ofRatUp (degFactorUp m.deg))
    (upAdd (m.poly.weightedNormUp W) m.rad) (hF.trans hF') (by
      linarith)
  have hX : ‖(2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n θ‖ ≤
      (2 * Real.pi) ^ m.deg * val (m.poly.weightedNormUp W) := by
    rw [norm_mul, norm_zpow]
    have : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
      rw [norm_mul]; simp [abs_of_pos Real.pi_pos]
    rw [this]
    exact mul_le_mul_of_nonneg_left hS h2pi.le
  have hsub := hm θ hθ
  have hle : ‖f θ‖ ≤ ‖f θ - (2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n θ‖ +
      ‖(2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n θ‖ := by
    simpa using norm_add_le (f θ - (2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n θ)
      ((2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n θ)
  have hpos : 0 ≤ val (upAdd (m.poly.weightedNormUp W) m.rad) := by linarith
  have hmul' : val (ofRatUp (degFactorUp m.deg) : α) * val (upAdd (m.poly.weightedNormUp W) m.rad)
      ≤ val (m.supBound W) := hmul
  calc ‖f θ‖ ≤ (2 * Real.pi) ^ m.deg * (val (m.poly.weightedNormUp W) + val m.rad) := by
        nlinarith
    _ ≤ (degFactorUp m.deg : ℝ) * val (upAdd (m.poly.weightedNormUp W) m.rad) := by
        exact mul_le_mul (two_pi_zpow_le _) hadd (by linarith) hF
    _ ≤ val (ofRatUp (degFactorUp m.deg) : α) *
          val (upAdd (m.poly.weightedNormUp W) m.rad) :=
        mul_le_mul_of_nonneg_right hF' hpos
    _ ≤ val (m.supBound W) := hmul'


end SupBound

end KAM.Certificate
