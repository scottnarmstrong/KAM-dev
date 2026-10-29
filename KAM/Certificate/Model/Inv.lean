/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Model.ExpBounds

/-!
# Reciprocal witnesses

The witness `Q ≈ 1/b` for a model `b = (2π)^d (P + T)` (ruling O2). The checker forms the
degree-zero product `u = Q (P + T)` (one advice-checked product, key `[2]`) and the bound
`δ ≥ sup_{T_ρ} |1 - u|` (`oneSubSupUp`: the zero-key coefficients are summed into a ball and
subtracted from `1`, the other terms cost their weighted size). If `δ < 1`, then `b` has no zero
on `T_ρ` and `|1/(P + T) - Q| ≤ sup|Q| δ/(1 - δ)` (scalar Neumann series), whence the radius
`|Q|_w · δ · t` with `t ≥ 1/(1 - δ)` from `recipOneSubUp` (`invWitness_sound`). No lower bound
of `|b|` is assumed.

`recipOneSubUp δ` needs no division: `1/(1 - δ) = Π_{i<k} (1 + δ^{2^i}) / (1 - δ^{2^k})`, and
once `x ≥ δ^{2^k}` passes `2x ≤ 1`, `1/(1 - δ^{2^k}) ≤ 1 + 2x` (at most 64 squarings, else
`none`; for the tiny `δ` of production, the first test passes and `t = 1 + 2δ`).
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM CertArith

section Defs

variable {α : Type} [CertArith α]

/-- Every entry of the key is zero (the constant character). -/
def isZeroKey (k : CertKey) : Bool := k.all fun z => z == 0

/-- An upper bound of `sup_{T_ρ} |1 - u|` for a degree-zero model `u`: the ball `1 - Σ` of the
zero-key coefficients (`|centre|↑ + radius`), the weighted norm of the other terms, the radius
of `u`. -/
def oneSubSupUp (W : CertWeight) (u : CertModel α) : α :=
  let z := CertPoly.coeffSumBall (⟨u.poly.terms.filter fun t => isZeroKey t.1⟩ : CertPoly α)
  let d := CertBall.plus CertBall.oneBall ⟨CC.negC z.c, z.r⟩
  upAdd (upAdd (upAdd d.c.normUp d.r)
    (CertPoly.supNormUp W ⟨u.poly.terms.filter fun t => !isZeroKey t.1⟩)) u.rad

/-- `acc · 1/(1 - x)` bounded by repeated squaring: fuel, `x ≥ δ^{2^i}`, `acc ≥ Π (1 + δ^{2^l})`. -/
def recipBoundAux : ℕ → α → α → Option α
  | 0, _, _ => none
  | f + 1, x, acc =>
    if ble (upAdd x x) (ofInt 1) then some (upMul acc (upAdd (ofInt 1) (upAdd x x)))
    else recipBoundAux f (upMul x x) (upMul acc (upAdd (ofInt 1) x))

/-- An upper bound of `1/(1 - δ)` for `0 ≤ δ < 1` (`none` after 64 squarings). -/
def recipOneSubUp (δ : α) : Option α := recipBoundAux 64 δ (ofInt 1)

end Defs

-- `n` is part of the signed interface (unused: the check is dimension-free).
set_option linter.unusedVariables false in
/-- The radius certified for `1/b` by the witness `Q` (or `none` if `δ < 1` fails). -/
def invWitnessRadius {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (cfg : ModelConfig α)
    (b : CertModel α) (Q : CertPoly α) : Option α :=
  let δ := oneSubSupUp W (CertModel.mul W cfg [2] ⟨0, Q, ofInt 0⟩ ⟨0, b.poly, b.rad⟩)
  if blt δ (ofInt 1) then
    match recipOneSubUp δ with
    | some t => some (upMul (upMul (Q.supNormUp W) δ) t)
    | none => none
  else none

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α]

omit [LawfulCertArith α] in
theorem certKeyFun_eq_zero_of_isZeroKey {n : ℕ} {k : CertKey} (h : isZeroKey k = true) :
    certKeyFun n k = 0 := by
  funext i
  unfold isZeroKey at h
  rw [List.all_eq_true] at h
  simp only [certKeyFun, List.getD_eq_getElem?_getD, Pi.zero_apply]
  cases hk : k[i.val]? with
  | none => rfl
  | some x =>
    have := h x (List.mem_of_getElem? hk)
    simpa using this

omit [LawfulCertArith α] in
/-- A polynomial splits along any filter of its terms. -/
theorem CertPoly.eval_filter_add (n : ℕ) (P : CertPoly α) (p : CertKey × CC α → Bool)
    (θ : Fin n → ℂ) : P.eval n θ =
      (⟨P.terms.filter p⟩ : CertPoly α).eval n θ +
        (⟨P.terms.filter fun t => !p t⟩ : CertPoly α).eval n θ := by
  simp only [CertPoly.eval]
  induction P.terms with
  | nil => simp
  | cons t L ih =>
    by_cases ht : p t = true
    · simp [ht, ih]; ring
    · simp [ht, ih]; ring

omit [LawfulCertArith α] in
/-- A polynomial with zero keys only is constant. -/
theorem CertPoly.eval_zeroKeys (n : ℕ) (L : List (CertKey × CC α)) (θ : Fin n → ℂ) :
    (⟨L.filter fun t => isZeroKey t.1⟩ : CertPoly α).eval n θ =
      (⟨L.filter fun t => isZeroKey t.1⟩ : CertPoly α).eval n 0 := by
  simp only [CertPoly.eval]
  induction L with
  | nil => simp
  | cons t L ih =>
    by_cases ht : isZeroKey t.1 = true
    · simp only [List.filter_cons, ht, ↓reduceIte, List.map_cons, List.sum_cons, ih,
        certKeyFun_eq_zero_of_isZeroKey ht, character_zero_point]
      simp [character]
    · simp [ht, ih]

/-- `oneSubSupUp` bounds `|1 - f|` for every function enclosed by a degree-zero model. -/
theorem norm_one_sub_le_oneSubSupUp {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) {u : CertModel α} {f : (Fin n → ℂ) → ℂ}
    (hu : u.Encloses n W.rho f) (hdeg : u.deg = 0) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n W.rho) : ‖1 - f θ‖ ≤ val (oneSubSupUp W u) := by
  have hf := hu θ hθ
  rw [hdeg, zpow_zero, zpow_zero, one_mul, one_mul, norm_sub_rev] at hf
  have hsplit := CertPoly.eval_filter_add n u.poly (fun t => isZeroKey t.1) θ
  beta_reduce at hsplit
  have hZ := CertPoly.eval_zeroKeys n u.poly.terms θ
  have hz := CertPoly.mem_coeffSumBall n
    (⟨u.poly.terms.filter fun t => isZeroKey t.1⟩ : CertPoly α)
  have hN := (⟨u.poly.terms.filter fun t => !isZeroKey t.1⟩ : CertPoly α).norm_eval_le_supNormUp
    hW hθ
  simp only [oneSubSupUp]
  generalize (⟨u.poly.terms.filter fun t => isZeroKey t.1⟩ : CertPoly α) = Z at hsplit hZ hz ⊢
  generalize (⟨u.poly.terms.filter fun t => !isZeroKey t.1⟩ : CertPoly α) = NZ at hsplit hN ⊢
  generalize CertPoly.coeffSumBall Z = z at hz ⊢
  have hnz : CertBall.Mem (-Z.eval n 0) (⟨CC.negC z.c, z.r⟩ : CertBall α) := by
    unfold CertBall.Mem at hz ⊢
    have e : -Z.eval n 0 - (CC.negC z.c).toC = -(Z.eval n 0 - z.c.toC) := by
      rw [CC.toC_negC]; ring
    rw [e, norm_neg]
    exact hz
  have hd := CertBall.mem_plus CertBall.mem_one hnz
  generalize CertBall.plus CertBall.oneBall ⟨CC.negC z.c, z.r⟩ = d at hd ⊢
  unfold CertBall.Mem at hd
  have hdn : ‖1 - Z.eval n 0‖ ≤ val (upAdd d.c.normUp d.r) := by
    have h1 := CC.norm_le_normUp d.c
    have h2 := LawfulCertArith.upAdd_ge d.c.normUp d.r
    have : ‖1 - Z.eval n 0‖ ≤ ‖1 + -Z.eval n 0 - d.c.toC‖ + ‖d.c.toC‖ := by
      rw [← sub_eq_add_neg]
      simpa using norm_sub_le_norm_sub_add_norm_sub (1 - Z.eval n 0) d.c.toC 0
    linarith
  have u1 := LawfulCertArith.upAdd_ge (upAdd d.c.normUp d.r) (NZ.supNormUp W)
  have u2 := LawfulCertArith.upAdd_ge (upAdd (upAdd d.c.normUp d.r) (NZ.supNormUp W)) u.rad
  have e : 1 - f θ = (1 - Z.eval n 0) - NZ.eval n θ + (u.poly.eval n θ - f θ) := by
    rw [hsplit, ← hZ]; ring
  rw [e]
  have n1 := norm_add_le ((1 - Z.eval n 0) - NZ.eval n θ) (u.poly.eval n θ - f θ)
  have n2 := norm_sub_le (1 - Z.eval n 0) (NZ.eval n θ)
  linarith

theorem recipBoundAux_ge : ∀ (f : ℕ) (x acc : α) {t : α} (y c : ℝ),
    recipBoundAux f x acc = some t → 0 ≤ y → y < 1 → y ≤ val x → 0 ≤ c → c ≤ val acc →
      c / (1 - y) ≤ val t
  | 0, _, _, _, _, _, h => by simp [recipBoundAux] at h
  | f + 1, x, acc, t, y, c, h => by
    intro hy0 hy1 hyx hc0 hca
    have hx0 : 0 ≤ val x := hy0.trans hyx
    have ha0 : 0 ≤ val acc := hc0.trans hca
    have h1y : 0 < 1 - y := by linarith
    unfold recipBoundAux at h
    split_ifs at h with hb
    · cases h
      have hb' := LawfulCertArith.ble_sound _ _ hb
      rw [LawfulCertArith.val_ofInt] at hb'
      have hxx := LawfulCertArith.upAdd_ge x x
      have h1 := LawfulCertArith.upAdd_ge (ofInt 1 : α) (upAdd x x)
      rw [LawfulCertArith.val_ofInt] at h1
      push_cast at hb' h1
      have hm := LawfulCertArith.upMul_ge acc (upAdd (ofInt 1) (upAdd x x)) ha0 (by linarith)
      have hy2 : y ≤ 1 / 2 := by linarith
      rw [div_le_iff₀ h1y]
      have h3 : c * (1 + 2 * y) ≤ val acc * val (upAdd (ofInt 1 : α) (upAdd x x)) :=
        mul_le_mul hca (by linarith) (by linarith) ha0
      have h4 : c ≤ c * (1 + 2 * y) * (1 - y) := by
        nlinarith [mul_nonneg hc0 (mul_nonneg hy0 (by linarith : (0 : ℝ) ≤ 1 - 2 * y))]
      exact h4.trans (mul_le_mul_of_nonneg_right (h3.trans hm) h1y.le)
    · have hxx := LawfulCertArith.upMul_ge x x hx0 hx0
      have h1 := LawfulCertArith.upAdd_ge (ofInt 1 : α) x
      rw [LawfulCertArith.val_ofInt] at h1
      push_cast at h1
      have hm := LawfulCertArith.upMul_ge acc (upAdd (ofInt 1) x) ha0 (by linarith)
      have ih := recipBoundAux_ge f (upMul x x) (upMul acc (upAdd (ofInt 1) x)) (y * y)
        (c * (1 + y)) h (by positivity) (by nlinarith)
        ((mul_le_mul hyx hyx hy0 hx0).trans hxx) (by positivity)
        ((mul_le_mul hca (by linarith) (by linarith) ha0).trans hm)
      have e : c / (1 - y) = c * (1 + y) / (1 - y * y) := by
        rw [div_eq_div_iff (by linarith) (by nlinarith)]
        ring
      rw [e]
      exact ih

theorem recipOneSubUp_ge {δ t : α} (h : recipOneSubUp δ = some t) (h0 : 0 ≤ val δ)
    (h1 : val δ < 1) : 1 / (1 - val δ) ≤ val t :=
  recipBoundAux_ge 64 δ (ofInt 1) (val δ) 1 h h0 h1 le_rfl zero_le_one
    (by rw [LawfulCertArith.val_ofInt]; simp)

theorem invWitness_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (cfg : ModelConfig α)
    {b : CertModel α} {bf : (Fin n → ℂ) → ℂ} (hb : b.Encloses n W.rho bf)
    {Q : CertPoly α} {r : α} (hQ : invWitnessRadius n W cfg b Q = some r) :
    (∀ θ ∈ complexStrip n W.rho, bf θ ≠ 0) ∧
      (⟨-b.deg, Q, r⟩ : CertModel α).Encloses n W.rho (fun θ => (bf θ)⁻¹) := by
  unfold invWitnessRadius at hQ
  simp only at hQ
  set u := CertModel.mul W cfg [2] ⟨0, Q, ofInt 0⟩ ⟨0, b.poly, b.rad⟩
  set δ := oneSubSupUp W u
  split_ifs at hQ with hδ
  split at hQ
  swap
  · simp at hQ
  rename_i t ht
  simp only [Option.some.injEq] at hQ
  subst hQ
  have hρ := CertWeight.rho_pos hW
  have h0 : (0 : Fin n → ℂ) ∈ complexStrip n W.rho := fun i => by simpa using hρ
  set c : ℂ := (2 * (Real.pi : ℂ)) ^ b.deg
  have hcR : (0 : ℝ) < (2 * Real.pi) ^ b.deg := by positivity
  have hc : ‖c‖ = (2 * Real.pi) ^ b.deg := norm_two_pi_zpow b.deg
  have hc0 : c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; linarith
  have hb' : (⟨0, b.poly, b.rad⟩ : CertModel α).Encloses n W.rho (fun θ => c⁻¹ * bf θ) := by
    intro θ hθ
    have := hb θ hθ
    simp only [zpow_zero, one_mul]
    have e : c⁻¹ * bf θ - b.poly.eval n θ = c⁻¹ * (bf θ - c * b.poly.eval n θ) := by
      field_simp
    rw [e, norm_mul, norm_inv, hc]
    rw [inv_mul_le_iff₀ hcR]
    exact this
  have hq : (⟨0, Q, ofInt 0⟩ : CertModel α).Encloses n W.rho (Q.eval n) := by
    intro θ _
    simp [LawfulCertArith.val_ofInt]
  have hu := CertModel.Encloses.mul hW cfg [2] hq hb'
  have hudeg : u.deg = 0 := by rw [CertModel.mul_deg]; rfl
  have hδθ : ∀ θ ∈ complexStrip n W.rho, ‖1 - Q.eval n θ * (c⁻¹ * bf θ)‖ ≤ val δ :=
    fun θ hθ => norm_one_sub_le_oneSubSupUp hW hu hudeg hθ
  have hδ0 : 0 ≤ val δ := (norm_nonneg _).trans (hδθ 0 h0)
  have hδ1 : val δ < 1 := by
    have := LawfulCertArith.blt_sound _ _ hδ
    rwa [LawfulCertArith.val_ofInt, Int.cast_one] at this
  have ht' := recipOneSubUp_ge ht hδ0 hδ1
  have hw0 : ∀ θ ∈ complexStrip n W.rho, Q.eval n θ * (c⁻¹ * bf θ) ≠ 0 := by
    intro θ hθ h
    have := hδθ θ hθ
    rw [h, sub_zero, norm_one] at this
    linarith
  refine ⟨fun θ hθ h => hw0 θ hθ (by rw [h, mul_zero, mul_zero]), ?_⟩
  intro θ hθ
  set w := Q.eval n θ * (c⁻¹ * bf θ)
  have hw := hw0 θ hθ
  have hbf : c⁻¹ * bf θ ≠ 0 := right_ne_zero_of_mul hw
  have hwn : 1 - val δ ≤ ‖w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - w)
    rw [norm_one, sub_sub_cancel] at this
    linarith [hδθ θ hθ]
  have hqn := Q.norm_eval_le_supNormUp hW hθ
  have hqn0 := Q.supNormUp_nonneg hW
  have hm1 := LawfulCertArith.upMul_ge (Q.supNormUp W) δ hqn0 hδ0
  have ht0 : 0 ≤ val t := (by positivity : (0 : ℝ) ≤ 1 / (1 - val δ)).trans ht'
  have hm2 := LawfulCertArith.upMul_ge (upMul (Q.supNormUp W) δ) t
    ((mul_nonneg hqn0 hδ0).trans hm1) ht0
  have hzp : (2 * (Real.pi : ℂ)) ^ (-b.deg) = c⁻¹ := zpow_neg _ _
  have hzpR : (2 * Real.pi) ^ (-b.deg) = ((2 * Real.pi) ^ b.deg)⁻¹ := zpow_neg _ _
  have hbf' : bf θ ≠ 0 := right_ne_zero_of_mul hbf
  have hQ0 : Q.eval n θ ≠ 0 := left_ne_zero_of_mul hw
  have e : (bf θ)⁻¹ - c⁻¹ * Q.eval n θ = c⁻¹ * (Q.eval n θ * (1 - w) / w) := by
    simp only [w]
    field_simp
  rw [hzp, hzpR, e, norm_mul, norm_inv, hc]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hcR.le)
  rw [norm_div, norm_mul]
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [div_le_iff₀ hwpos]
  have h1w : ‖1 - w‖ ≤ val δ := hδθ θ hθ
  have key : val (Q.supNormUp W) * val δ ≤ val (Q.supNormUp W) * val δ * val t * ‖w‖ := by
    have : 1 ≤ val t * ‖w‖ := by
      have h1d : 0 < 1 - val δ := by linarith
      rw [div_le_iff₀ h1d] at ht'
      nlinarith
    nlinarith [mul_nonneg hqn0 hδ0]
  calc ‖Q.eval n θ‖ * ‖1 - w‖ ≤ val (Q.supNormUp W) * val δ :=
        mul_le_mul hqn h1w (norm_nonneg _) hqn0
    _ ≤ val (Q.supNormUp W) * val δ * val t * ‖w‖ := key
    _ ≤ val (upMul (upMul (Q.supNormUp W) δ) t) * ‖w‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (mul_le_mul_of_nonneg_right hm1 ht0).trans hm2

end Sound

end KAM.Certificate
