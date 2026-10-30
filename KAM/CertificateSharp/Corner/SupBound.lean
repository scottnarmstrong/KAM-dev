/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Corner.Vertex
public import KAM.Certificate.Model.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The corner (vertex) sup bound of a Fourier model

`CertModel.cornerLeq W n m b` checks `(2π)^deg (Σ_k |c_k| e^{2πρ σ·k} + rad) ≤ b` at every vertex
`σ ∈ {±1}ⁿ` (`signLists n`), where `e^{2πρ j}` is bounded by `w^j` for `j ≥ 0` and by `wlo^{j}` for
`j < 0`, with `wlo = expLoQ` a Taylor lower bound of `e^{2πρ}` computed from the weight (no new
certificate data). `CertModel.norm_le_of_cornerLeq`: if the check passes and `m` encloses `f`, then
`|f| ≤ b` on the whole strip `T_ρ`. The landed `supBound` charges every coefficient its worst vertex
`w^{|k|₁}` at once; the corner bound commits to one vertex for the whole sum
(`Corner/Vertex.lean`).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp

open KAM KAM.Certificate CertArith

/-! ### Vertices and the integer exponent -/

/-- All sign vectors of length `n`. -/
def signLists : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (signLists n).flatMap fun l => [true :: l, false :: l]

theorem mem_signLists : ∀ {n : ℕ} (σ : Fin n → Bool), List.ofFn σ ∈ signLists n
  | 0, σ => by simp [signLists]
  | n + 1, σ => by
    rw [List.ofFn_succ, signLists, List.mem_flatMap]
    refine ⟨List.ofFn fun i => σ i.succ, mem_signLists _, ?_⟩
    cases σ 0 <;> simp

/-- `Σ_i σ_i k_i` for a key list and a sign list (truncating at the shorter one). -/
def dotList : List ℤ → List Bool → ℤ
  | k :: ks, b :: bs => (if b then k else -k) + dotList ks bs
  | _, _ => 0

theorem sum_key_sgn : ∀ (k : CertKey) {n : ℕ} (σ : Fin n → Bool),
    ∑ i : Fin n, (certKeyFun n k i : ℝ) * sgn (σ i) = (dotList k (List.ofFn σ) : ℝ)
  | [], n, σ => by simp [certKeyFun, dotList, List.ofFn_eq_map] <;> cases n <;> simp [dotList]
  | a :: l, 0, σ => by simp [dotList]
  | a :: l, n + 1, σ => by
    rw [Fin.sum_univ_succ, List.ofFn_succ]
    have ih := sum_key_sgn l (fun i : Fin n => σ i.succ)
    have h0 : certKeyFun (n + 1) (a :: l) 0 = a := by simp [certKeyFun]
    have hs : ∀ i : Fin n, certKeyFun (n + 1) (a :: l) i.succ = certKeyFun n l i := by
      intro i; simp [certKeyFun]
    simp only [hs, h0, ih, dotList]
    cases σ 0 <;> simp [sgn] <;> ring

/-! ### The weight lower bound and the exponential bound -/

/-- `Σ_{j ≤ N} x^j / j!`. -/
def expLoQ (x : ℚ) (N : ℕ) : ℚ := ((List.range (N + 1)).map fun j => x ^ j / (j.factorial : ℚ)).sum

theorem expLoQ_eq (x : ℚ) (N : ℕ) :
    expLoQ x N = ∑ j ∈ Finset.range (N + 1), x ^ j / (j.factorial : ℚ) := by
  unfold expLoQ
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ _ (N + 1)]
    simp

theorem one_le_expLoQ {x : ℚ} (hx : 0 ≤ x) (N : ℕ) : 1 ≤ expLoQ x N := by
  rw [expLoQ_eq, Finset.sum_range_succ']
  have : 0 ≤ ∑ j ∈ Finset.range N, x ^ (j + 1) / ((j + 1).factorial : ℚ) :=
    Finset.sum_nonneg fun j _ => by positivity
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  linarith

/-- The lower weight: a Taylor partial sum of `e^{2π_lo ρ}`. -/
def wloOf (W : CertWeight) (N : ℕ) : ℚ := expLoQ (2 * piLoQ * W.rho) N

theorem wloOf_le_exp {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (N' : ℕ) :
    1 ≤ wloOf W N' ∧ (wloOf W N' : ℝ) ≤ Real.exp (2 * Real.pi * W.rho) := by
  have hρ := CertWeight.rho_pos hW
  have hρq : (0 : ℚ) < W.rho := by exact_mod_cast hρ
  have hpi : (0 : ℚ) < piLoQ := by norm_num [piLoQ]
  have hx : (0 : ℚ) ≤ 2 * piLoQ * W.rho := by positivity
  refine ⟨one_le_expLoQ hx N', ?_⟩
  unfold wloOf
  rw [expLoQ_eq]
  push_cast
  have hxR : (0 : ℝ) ≤ 2 * (piLoQ : ℝ) * W.rho := by exact_mod_cast hx
  have h1 := Real.sum_le_exp_of_nonneg hxR (N' + 1)
  have h2 : Real.exp (2 * (piLoQ : ℝ) * W.rho) ≤ Real.exp (2 * Real.pi * W.rho) := by
    apply Real.exp_le_exp.mpr
    have := piLoQ_lt_pi.le
    nlinarith
  exact h1.trans h2

/-- The bound of `e^{2πρ m}` (`m ∈ ℤ`): `w^m` for `m ≥ 0`, `(wlo^{-m})⁻¹` for `m < 0`. -/
def expUb (W : CertWeight) (wlo : ℚ) (m : ℤ) : ℚ :=
  if 0 ≤ m then W.w ^ m.toNat else (wlo ^ (-m).toNat)⁻¹

theorem exp_le_expUb {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) {wlo : ℚ}
    (h1 : 1 ≤ wlo) (hlo : (wlo : ℝ) ≤ Real.exp (2 * Real.pi * W.rho)) (m : ℤ) :
    Real.exp (2 * Real.pi * W.rho * m) ≤ (expUb W wlo m : ℝ) ∧ 0 ≤ (expUb W wlo m : ℝ) := by
  have hw1 := CertWeight.one_le_w hW
  have hwe := CertWeight.exp_le_w hW
  have hlo0 : (0 : ℝ) < wlo := by
    have : (1 : ℝ) ≤ wlo := by exact_mod_cast h1
    linarith
  unfold expUb
  split_ifs with hm
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = j := ⟨m.toNat, by omega⟩
    simp only [Int.toNat_natCast]
    push_cast
    refine ⟨?_, by positivity⟩
    rw [mul_comm, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) hwe _
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = -(j : ℤ) := ⟨(-m).toNat, by omega⟩
    simp only [neg_neg, Int.toNat_natCast]
    push_cast
    refine ⟨?_, by positivity⟩
    have : Real.exp (2 * Real.pi * W.rho * -(j : ℝ)) = (Real.exp (2 * Real.pi * W.rho) ^ j)⁻¹ := by
      rw [mul_neg, Real.exp_neg, mul_comm, Real.exp_nat_mul]
    rw [this]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hlo0.le hlo _)

/-! ### The corner bound of a model -/

section Model

variable {α : Type} [CertArith α]

/-- `Σ_t |c_t| · expUb(σ·k_t)` at the vertex `l`, rounded upward. -/
def cornerSumUp (W : CertWeight) (wlo : ℚ) (l : List Bool) (P : CertPoly α) : α :=
  P.terms.foldr (fun t acc =>
    upAdd (upMul t.2.normUp (ofRatUp (expUb W wlo (dotList t.1 l)))) acc) (ofInt 0)

/-- `(2π)^deg (cornerSum + rad)` at the vertex `l`, rounded upward. -/
def cornerUp (W : CertWeight) (wlo : ℚ) (l : List Bool) (m : CertModel α) : α :=
  upMul (ofRatUp (degFactorUp m.deg)) (upAdd (cornerSumUp W wlo l m.poly) m.rad)

/-- The corner check: every vertex value is at most `b`. -/
def cornerLeq (W : CertWeight) (wlo : ℚ) (n : ℕ) (m : CertModel α) (b : α) : Bool :=
  (signLists n).all fun l => ble (cornerUp W wlo l m) b

theorem norm_terms_le {n : ℕ} (L : List (CertKey × CC α)) (θ : Fin n → ℂ) :
    ‖(L.map fun t => t.2.toC * character (certKeyFun n t.1) θ).sum‖ ≤
      (L.map fun t => ‖t.2.toC‖ * ‖character (certKeyFun n t.1) θ‖).sum := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    linarith

theorem sum_fin_get {γ : Type} (L : List γ) (g : γ → ℝ) :
    ∑ j : Fin L.length, g (L.get j) = (L.map g).sum := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

variable [LawfulCertArith α]

theorem cornerSumUp_bound {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) {wlo : ℚ}
    (h1 : 1 ≤ wlo) (hlo : (wlo : ℝ) ≤ Real.exp (2 * Real.pi * W.rho)) (l : List Bool)
    (L : List (CertKey × CC α)) :
    0 ≤ val (L.foldr (fun t acc =>
        upAdd (upMul t.2.normUp (ofRatUp (expUb W wlo (dotList t.1 l)))) acc) (ofInt 0)) ∧
      (L.map fun t => ‖t.2.toC‖ * ((expUb W wlo (dotList t.1 l) : ℚ) : ℝ)).sum ≤
        val (L.foldr (fun t acc =>
          upAdd (upMul t.2.normUp (ofRatUp (expUb W wlo (dotList t.1 l)))) acc) (ofInt 0)) := by
  induction L with
  | nil => simp [LawfulCertArith.val_ofInt]
  | cons t L ih =>
    obtain ⟨ih0, ih1⟩ := ih
    have hq := (exp_le_expUb hW h1 hlo (dotList t.1 l)).2
    have hr := LawfulCertArith.ofRatUp_ge (α := α) (expUb W wlo (dotList t.1 l))
    have hn := CC.normUp_nonneg t.2
    have hm := LawfulCertArith.upMul_ge t.2.normUp
      (ofRatUp (expUb W wlo (dotList t.1 l))) hn (hq.trans hr)
    have hs := LawfulCertArith.upAdd_ge
      (upMul t.2.normUp (ofRatUp (expUb W wlo (dotList t.1 l))))
      (L.foldr (fun t acc =>
        upAdd (upMul t.2.normUp (ofRatUp (expUb W wlo (dotList t.1 l)))) acc) (ofInt 0))
    have hnorm := CC.norm_le_normUp t.2
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    have h3 : ‖t.2.toC‖ * ((expUb W wlo (dotList t.1 l) : ℚ) : ℝ) ≤
        val t.2.normUp * val (ofRatUp (expUb W wlo (dotList t.1 l)) : α) :=
      mul_le_mul hnorm hr hq hn
    refine ⟨by linarith [mul_nonneg hn (hq.trans hr)], ?_⟩
    linarith

/-- The vertex weights at `θ`. -/
def vw {n : ℕ} (ρ : ℝ) (θ : Fin n → ℂ) (σ : Fin n → Bool) : ℝ := ∏ i, lam1 ρ (θ i).im (σ i)

theorem vw_nonneg {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ)
    (σ : Fin n → Bool) : 0 ≤ vw ρ θ σ :=
  Finset.prod_nonneg fun i _ => lam1_nonneg hρ (hθ i).le _

theorem vw_sum {n : ℕ} (ρ : ℝ) (θ : Fin n → ℂ) : ∑ σ : Fin n → Bool, vw ρ θ σ = 1 :=
  prod_lam_sum ρ fun i => (θ i).im

/-- **The corner bound in convex-combination form.** If `m` encloses `f`, then at every `θ` of the
strip `|f θ|` is at most the `Λ_σ(θ)`-weighted average of the vertex values `cornerUp σ m`. -/
theorem norm_le_conv {n : ℕ} {W : CertWeight} {s N N' : ℕ} (hW : checkWeight W s N = true)
    {m : CertModel α} {f : (Fin n → ℂ) → ℂ} (hm : m.Encloses n W.rho f) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n W.rho) :
    ‖f θ‖ ≤ ∑ σ : Fin n → Bool, vw W.rho θ σ *
      val (cornerUp W (wloOf W N') (List.ofFn σ) m) := by
  obtain ⟨h1, hlo⟩ := wloOf_le_exp hW N'
  have hρ := CertWeight.rho_pos hW
  have h2pi : (0 : ℝ) < (2 * Real.pi) ^ m.deg := by positivity
  have hrad : 0 ≤ val m.rad := by
    have h0 : (0 : Fin n → ℂ) ∈ complexStrip n W.rho := fun i => by simpa using hρ
    have := (norm_nonneg _).trans (hm 0 h0)
    exact nonneg_of_mul_nonneg_right this h2pi
  set S : (Fin n → Bool) → ℝ := fun σ => (m.poly.terms.map fun t => ‖t.2.toC‖ *
    Real.exp (2 * Real.pi * W.rho * (dotList t.1 (List.ofFn σ) : ℝ))).sum with hS
  -- (a) the per-vertex bound
  have hG : ∀ σ : Fin n → Bool, (2 * Real.pi) ^ m.deg * (S σ + val m.rad) ≤
      val (cornerUp W (wloOf W N') (List.ofFn σ) m) := by
    intro σ
    obtain ⟨hS0, hSb⟩ := cornerSumUp_bound hW h1 hlo (List.ofFn σ) m.poly.terms
    have hS0' : 0 ≤ val (cornerSumUp W (wloOf W N') (List.ofFn σ) m.poly) := hS0
    have hS' : (m.poly.terms.map fun t => ‖t.2.toC‖ *
        ((expUb W (wloOf W N') (dotList t.1 (List.ofFn σ)) : ℚ) : ℝ)).sum ≤
        val (cornerSumUp W (wloOf W N') (List.ofFn σ) m.poly) := hSb
    have hadd := LawfulCertArith.upAdd_ge (cornerSumUp W (wloOf W N') (List.ofFn σ) m.poly) m.rad
    have hF : (0 : ℝ) ≤ (degFactorUp m.deg : ℝ) := h2pi.le.trans (two_pi_zpow_le _)
    have hF' := LawfulCertArith.ofRatUp_ge (α := α) (degFactorUp m.deg)
    have hpos : 0 ≤ val (upAdd (cornerSumUp W (wloOf W N') (List.ofFn σ) m.poly) m.rad) := by
      linarith
    have hmul := LawfulCertArith.upMul_ge (ofRatUp (degFactorUp m.deg))
      (upAdd (cornerSumUp W (wloOf W N') (List.ofFn σ) m.poly) m.rad) (hF.trans hF') hpos
    have hterm : S σ ≤ (m.poly.terms.map fun t => ‖t.2.toC‖ *
        ((expUb W (wloOf W N') (dotList t.1 (List.ofFn σ)) : ℚ) : ℝ)).sum := by
      apply List.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left (exp_le_expUb hW h1 hlo _).1 (norm_nonneg _)
    have hSnn : 0 ≤ S σ := by
      rw [hS]
      exact List.sum_nonneg fun x hx => by
        obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
        exact mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)
    unfold cornerUp
    calc (2 * Real.pi) ^ m.deg * (S σ + val m.rad)
        ≤ (degFactorUp m.deg : ℝ) * val (upAdd
            (cornerSumUp W (wloOf W N') (List.ofFn σ) m.poly) m.rad) :=
          mul_le_mul (two_pi_zpow_le _) (by linarith) (by linarith) hF
      _ ≤ val (ofRatUp (degFactorUp m.deg) : α) * val (upAdd
            (cornerSumUp W (wloOf W N') (List.ofFn σ) m.poly) m.rad) :=
          mul_le_mul_of_nonneg_right hF' hpos
      _ ≤ _ := hmul
  -- (b) the vertex lemma for the polynomial part
  have hy : ∀ i, |(θ i).im| ≤ W.rho := fun i => (hθ i).le
  have hsum : ‖m.poly.eval n θ‖ ≤ ∑ σ : Fin n → Bool, vw W.rho θ σ * S σ := by
    have h1' : ‖m.poly.eval n θ‖ ≤
        (m.poly.terms.map fun t => ‖t.2.toC‖ * ‖character (certKeyFun n t.1) θ‖).sum := by
      unfold CertPoly.eval
      exact norm_terms_le _ θ
    refine h1'.trans ?_
    set L := m.poly.terms with hL
    have hg : ∀ t : CertKey × CC α, ‖character (certKeyFun n t.1) θ‖ =
        Real.exp (-∑ i, (2 * Real.pi * (certKeyFun n t.1 i : ℝ)) * (θ i).im) := fun t => by
      have : 2 * Real.pi * ∑ j, (certKeyFun n t.1 j : ℝ) * (θ j).im =
          ∑ i, (2 * Real.pi * (certKeyFun n t.1 i : ℝ)) * (θ i).im := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [norm_character, this]
    simp only [hg]
    rw [← sum_fin_get L (fun t => ‖t.2.toC‖ *
      Real.exp (-∑ i, (2 * Real.pi * (certKeyFun n t.1 i : ℝ)) * (θ i).im))]
    refine (vertex_sum_conv hρ Finset.univ (fun j => ‖(L.get j).2.toC‖) (fun j => norm_nonneg _)
      (fun j i => 2 * Real.pi * (certKeyFun n (L.get j).1 i : ℝ)) (fun i => (θ i).im) hy).trans
      (le_of_eq ?_)
    refine Finset.sum_congr rfl fun σ _ => ?_
    have e : ∀ j : Fin L.length, W.rho * ∑ i, 2 * Real.pi * (certKeyFun n (L.get j).1 i : ℝ) *
        sgn (σ i) = 2 * Real.pi * W.rho * (dotList (L.get j).1 (List.ofFn σ) : ℝ) := by
      intro j
      rw [← sum_key_sgn (L.get j).1 σ, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    simp only [e]
    rw [vw, hS]
    simp only
    rw [sum_fin_get L (fun t => ‖t.2.toC‖ *
      Real.exp (2 * Real.pi * W.rho * (dotList t.1 (List.ofFn σ) : ℝ)))]
  -- (c) assemble
  have hsub := hm θ hθ
  have hX : ‖(2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n θ‖ ≤
      (2 * Real.pi) ^ m.deg * ∑ σ : Fin n → Bool, vw W.rho θ σ * S σ := by
    rw [norm_mul, norm_zpow]
    have : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
      rw [norm_mul]; simp [abs_of_pos Real.pi_pos]
    rw [this]
    exact mul_le_mul_of_nonneg_left hsum h2pi.le
  have hle : ‖f θ‖ ≤ ‖f θ - (2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n θ‖ +
      ‖(2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n θ‖ := by
    simpa using norm_add_le (f θ - (2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n θ)
      ((2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n θ)
  have hone : (2 * Real.pi) ^ m.deg * val m.rad =
      ∑ σ : Fin n → Bool, vw W.rho θ σ * ((2 * Real.pi) ^ m.deg * val m.rad) := by
    rw [← Finset.sum_mul, vw_sum, one_mul]
  have hmain : ‖f θ‖ ≤ ∑ σ : Fin n → Bool, vw W.rho θ σ *
      ((2 * Real.pi) ^ m.deg * (S σ + val m.rad)) := by
    have : ∑ σ : Fin n → Bool, vw W.rho θ σ * ((2 * Real.pi) ^ m.deg * (S σ + val m.rad)) =
        (2 * Real.pi) ^ m.deg * ∑ σ : Fin n → Bool, vw W.rho θ σ * S σ +
          (2 * Real.pi) ^ m.deg * val m.rad := by
      calc _ = ∑ σ : Fin n → Bool, ((2 * Real.pi) ^ m.deg * (vw W.rho θ σ * S σ) +
            vw W.rho θ σ * ((2 * Real.pi) ^ m.deg * val m.rad)) :=
            Finset.sum_congr rfl fun σ _ => by ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, vw_sum,
            one_mul]
    linarith
  exact hmain.trans (Finset.sum_le_sum fun σ _ =>
    mul_le_mul_of_nonneg_left (hG σ) (vw_nonneg hρ hθ σ))

theorem norm_le_of_cornerLeq {n : ℕ} {W : CertWeight} {s N N' : ℕ}
    (hW : checkWeight W s N = true) {m : CertModel α} {f : (Fin n → ℂ) → ℂ}
    (hm : m.Encloses n W.rho f) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n W.rho) {b : α}
    (h : cornerLeq W (wloOf W N') n m b = true) : ‖f θ‖ ≤ val b := by
  refine (norm_le_conv (N' := N') hW hm hθ).trans ?_
  have hρ := CertWeight.rho_pos hW
  calc _ ≤ ∑ σ : Fin n → Bool, vw W.rho θ σ * val b := by
        refine Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left ?_ (vw_nonneg hρ hθ σ)
        simp only [cornerLeq, List.all_eq_true] at h
        exact LawfulCertArith.ble_sound _ _ (h _ (mem_signLists σ))
    _ = val b := by rw [← Finset.sum_mul, vw_sum, one_mul]

/-! ### Row sums -/

/-- `Σ_j cornerUp l m_j`, rounded upward. -/
def rowCornerUp (W : CertWeight) (wlo : ℚ) (l : List Bool) (ms : List (CertModel α)) : α :=
  ms.foldr (fun m acc => upAdd (cornerUp W wlo l m) acc) (ofInt 0)

/-- The joint row-sum corner check: at every vertex, `Σ_j cornerUp ≤ b`. -/
def rowCornerLeq (W : CertWeight) (wlo : ℚ) (n : ℕ) (ms : List (CertModel α)) (b : α) : Bool :=
  (signLists n).all fun l => ble (rowCornerUp W wlo l ms) b

theorem sum_cornerUp_le (W : CertWeight) (wlo : ℚ) (l : List Bool) (ms : List (CertModel α)) :
    (ms.map fun m => val (cornerUp W wlo l m)).sum ≤ val (rowCornerUp W wlo l ms) := by
  induction ms with
  | nil => simp [rowCornerUp, LawfulCertArith.val_ofInt]
  | cons m ms ih =>
    simp only [rowCornerUp, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
    have := LawfulCertArith.upAdd_ge (cornerUp W wlo l m)
      (ms.foldr (fun m acc => upAdd (cornerUp W wlo l m) acc) (ofInt 0))
    linarith

theorem sum_norm_le_conv {n : ℕ} {W : CertWeight} {s N N' : ℕ}
    (hW : checkWeight W s N = true) (EL : List (CertModel α × ((Fin n → ℂ) → ℂ)))
    (hEL : ∀ p ∈ EL, p.1.Encloses n W.rho p.2) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n W.rho) :
    (EL.map fun p => ‖p.2 θ‖).sum ≤ ∑ σ : Fin n → Bool, vw W.rho θ σ *
      ((EL.map Prod.fst).map fun m => val (cornerUp W (wloOf W N') (List.ofFn σ) m)).sum := by
  induction EL with
  | nil => simp
  | cons p EL ih =>
    have h1 := norm_le_conv (N' := N') hW (hEL p (by simp)) hθ
    have h2 := ih (fun q hq => hEL q (by simp [hq]))
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib]
    linarith

/-- **Row sums.** If `m_j` encloses `f_j` and the joint corner check passes, then
`Σ_j |f_j θ| ≤ b` on the strip: the same vertex is shared by all entries of the row. -/
theorem sum_norm_le_of_rowCornerLeq {n : ℕ} {W : CertWeight} {s N N' : ℕ}
    (hW : checkWeight W s N = true) (EL : List (CertModel α × ((Fin n → ℂ) → ℂ)))
    (hEL : ∀ p ∈ EL, p.1.Encloses n W.rho p.2) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n W.rho)
    {b : α} (h : rowCornerLeq W (wloOf W N') n (EL.map Prod.fst) b = true) :
    (EL.map fun p => ‖p.2 θ‖).sum ≤ val b := by
  have hρ := CertWeight.rho_pos hW
  refine (sum_norm_le_conv (N' := N') hW EL hEL hθ).trans ?_
  calc _ ≤ ∑ σ : Fin n → Bool, vw W.rho θ σ * val b := by
        refine Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left ?_ (vw_nonneg hρ hθ σ)
        simp only [rowCornerLeq, List.all_eq_true] at h
        exact (sum_cornerUp_le W (wloOf W N') (List.ofFn σ) _).trans
          (LawfulCertArith.ble_sound _ _ (h _ (mem_signLists σ)))
    _ = val b := by rw [← Finset.sum_mul, vw_sum, one_mul]

end Model

end KAM.CertificateSharp
