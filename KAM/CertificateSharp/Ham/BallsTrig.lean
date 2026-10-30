/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Ham.TrigBound

/-!
# The ball pass with the cosh primitive for trigonometric modes

`ballsTrig` is `Slp.balls` with one addition. Every slot carries a shape: `term k a` records
that the slot value `v` satisfies `‖v‖ ≤ a ‖χ_k‖` on the domain, where `χ_k = e^{2πi k·θ}` is
`char k`. A `char k` slot is `term k 1`; a product with a slot of magnitude `m` is `term k (a m)`;
a sum of two `term k` slots is `term k (a + b)`; and the sum of a `term k a` and a `term (-k) b`
slot, which is what a cosine or sine mode and each of its derivatives compiles to, gets the radius
`trigRad` (`max (a L + b W) (a W + b L)`, `≈ (a + b) cosh(2πρ|k|₁)` for `a = b`) instead of
the disc bound `(a + b) w^{|k|₁}`. All other operations are those of `ballStep`.

* `ballsTrig`: the pass (same output type as `Slp.balls`).
* `val_mem_ballsTrig`: every slot value lies in its ball on `certDomain`.
* `invGood_of_ballsTrig`: every `inv` operand is nonzero on the domain.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Certificate CertArith

/-- What is known about a slot besides its ball. -/
inductive TrigShape
  | plain
  | term (k : CertKey) (a : ℚ)

/-- A slot ball with its shape. -/
abbrev TBall : Type := (CC ℚ × ℚ) × TrigShape

/-- The default entry. -/
def tbZero : TBall := (ballZero, .plain)

/-- The magnitude of a slot ball. -/
def tbMag (t : TBall) : ℚ := ballMagQ t.1

/-- The shape of a product. -/
def mulShape (x y : TBall) : TrigShape :=
  match x.2, y.2 with
  | .term k u, _ => .term k (u * tbMag y)
  | _, .term k v => .term k (tbMag x * v)
  | _, _ => .plain

theorem mulShape_cases {x y : TBall} {k : CertKey} {u : ℚ} (h : mulShape x y = .term k u) :
    (∃ u0, x.2 = .term k u0 ∧ u = u0 * tbMag y) ∨
      (x.2 = .plain ∧ ∃ v, y.2 = .term k v ∧ u = tbMag x * v) := by
  unfold mulShape at h
  rcases hx : x.2 with _ | ⟨k0, u0⟩ <;> rcases hy : y.2 with _ | ⟨k1, v1⟩ <;>
    simp [hx, hy] at h
  · obtain ⟨rfl, rfl⟩ := h
    exact Or.inr ⟨rfl, v1, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨u0, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨u0, rfl, rfl⟩

/-- The ball of one operation, with its shape. -/
def stepT (n : ℕ) (WH : CertWeight) (centre radius : List ℚ) (taylorN : ℕ)
    (acc : List TBall) : SlpOp → Option TBall
  | .char k => some ((⟨0, 0⟩, WH.w ^ (k.map Int.natAbs).sum), .term k 1)
  | .mul a b =>
    (ballStep n WH centre radius taylorN (acc.map Prod.fst) (.mul a b)).map fun r =>
      (r, mulShape (acc.getD a tbZero) (acc.getD b tbZero))
  | .add a b =>
    match (acc.getD a tbZero).2, (acc.getD b tbZero).2 with
    | .term k u, .term k' v =>
      if k' = k then
        (ballStep n WH centre radius taylorN (acc.map Prod.fst) (.add a b)).map
          fun r => (r, .term k (u + v))
      else if k' = negKey k then
        some ((⟨0, 0⟩, trigRad WH taylorN k u v), .plain)
      else
        (ballStep n WH centre radius taylorN (acc.map Prod.fst) (.add a b)).map
          fun r => (r, .plain)
    | _, _ =>
      (ballStep n WH centre radius taylorN (acc.map Prod.fst) (.add a b)).map
        fun r => (r, .plain)
  | op =>
    (ballStep n WH centre radius taylorN (acc.map Prod.fst) op).map fun r => (r, .plain)

/-- The shaped balls of the slots of `ops` after the slots `acc`. -/
def ballsAuxT (n : ℕ) (WH : CertWeight) (centre radius : List ℚ) (taylorN : ℕ) :
    List TBall → List SlpOp → Option (List TBall)
  | acc, [] => some acc
  | acc, op :: ops =>
    (stepT n WH centre radius taylorN acc op).bind fun b =>
      ballsAuxT n WH centre radius taylorN (acc ++ [b]) ops

/-- Ball arithmetic of every slot on `D` with the cosh primitive for pairs of conjugate
characters: the balls `(centre, radius)` with `|slot - centre| ≤ radius` on `D`. -/
def ballsTrig (n : ℕ) (p : Slp) (WH : CertWeight) (centre radius : List ℚ) (taylorN : ℕ) :
    Option (List (CC ℚ × ℚ)) :=
  (ballsAuxT n WH centre radius taylorN [] p.ops).map fun bs => bs.map Prod.fst

/-! ### Soundness -/

/-- The shapes of `acc` hold for the values `V` at `z`. -/
def ShapeRel (n : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) (V : List ℂ) (acc : List TBall) : Prop :=
  ∀ i k a, (acc.getD i tbZero).2 = .term k a → ‖V.getD i 0‖ ≤ a * charNorm n k z

/-- Balls and shapes of `acc` hold for the values `V` at `z`. -/
def TRel (n : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) (V : List ℂ) (acc : List TBall) : Prop :=
  BallRel V (acc.map Prod.fst) ∧ ShapeRel n z V acc

theorem TRel.nil (n : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) : TRel n z [] [] :=
  ⟨BallRel.ballRel_nil, fun i k a h => by simp [tbZero] at h⟩

theorem TRel.length {n : ℕ} {z : (Fin n → ℂ) × (Fin n → ℂ)} {V : List ℂ} {acc : List TBall}
    (h : TRel n z V acc) : V.length = acc.length := by
  simpa using h.1.1

theorem tb_fst_getD (acc : List TBall) (i : ℕ) :
    (acc.getD i tbZero).1 = (acc.map Prod.fst).getD i ballZero := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases acc[i]? <;> simp [tbZero]

theorem getD_append_lt {α : Type} (l l' : List α) (d : α) {i : ℕ} (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_ge {α : Type} (l l' : List α) (d : α) {i : ℕ} (h : l.length ≤ i) :
    (l ++ l').getD i d = l'.getD (i - l.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem TRel.snoc {n : ℕ} {z : (Fin n → ℂ) × (Fin n → ℂ)} {V : List ℂ} {acc : List TBall}
    (h : TRel n z V acc) {v : ℂ} {b : TBall} (hb : ‖v - b.1.1.toC‖ ≤ (b.1.2 : ℝ))
    (hs : ∀ k a, b.2 = .term k a → ‖v‖ ≤ a * charNorm n k z) :
    TRel n z (V ++ [v]) (acc ++ [b]) := by
  refine ⟨?_, fun i k a hi => ?_⟩
  · simpa using h.1.ballRel_snoc hb
  · have hl := h.length
    rcases lt_trichotomy i acc.length with hlt | heq | hgt
    · rw [getD_append_lt _ _ _ hlt] at hi
      rw [getD_append_lt _ _ _ (hl ▸ hlt)]
      exact h.2 i k a hi
    · subst heq
      rw [getD_append_ge _ _ _ le_rfl, Nat.sub_self] at hi
      rw [getD_append_ge _ _ _ hl.le, hl, Nat.sub_self]
      simpa using hs k a (by simpa using hi)
    · rw [getD_append_ge _ _ _ hgt.le] at hi
      have : i - acc.length ≠ 0 := by omega
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero this
      rw [hj] at hi
      simp [tbZero] at hi

theorem trig_add_bound {n : ℕ} {WH : CertWeight} {s N : ℕ} (hW : checkWeight WH s N = true)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z.1 ∈ complexStrip n WH.rho) {taylorN : ℕ}
    (k : CertKey) {u v : ℚ} {x y : ℂ}
    (hx : ‖x‖ ≤ u * charNorm n k z) (hy : ‖y‖ ≤ v * charNorm n (negKey k) z) :
    ‖x + y‖ ≤ (trigRad WH taylorN k u v : ℝ) := by
  set m := (k.map Int.natAbs).sum with hm
  set sk := charNorm n k z with hsk
  have hs : 0 < sk := charNorm_pos n k z
  rw [charNorm_negKey] at hy
  have hu : (0 : ℝ) ≤ u := by
    by_contra h
    push Not at h
    nlinarith [norm_nonneg x]
  have hv : (0 : ℝ) ≤ v := by
    by_contra h
    push Not at h
    nlinarith [norm_nonneg y, inv_pos.2 hs]
  have hρ := CertWeight.rho_pos hW
  set A : ℝ := 2 * Real.pi * WH.rho * m with hA
  have hA0 : 0 ≤ A := by positivity
  have hup : sk ≤ Real.exp A := charNorm_le hW k hz
  have hup' : (sk)⁻¹ ≤ Real.exp A := by
    have := charNorm_le hW (negKey k) hz
    rwa [charNorm_negKey, sum_natAbs_negKey] at this
  have hlo : (Real.exp A)⁻¹ ≤ sk := by
    have := inv_anti₀ (inv_pos.2 hs) hup'
    simpa using this
  have hW' : Real.exp A ≤ (WH.w : ℝ) ^ m := by
    have h1 : Real.exp A = Real.exp (2 * Real.pi * WH.rho) ^ m := by
      rw [← Real.exp_nat_mul, hA]; congr 1; ring
    rw [h1]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) (CertWeight.exp_le_w hW) m
  have hL : (Real.exp A)⁻¹ ≤ (expNegUpQ (2 * piLoQ * WH.rho * m) taylorN : ℝ) := by
    refine le_trans ?_ (exp_neg_le_expNegUpQ (x := 2 * piLoQ * WH.rho * m) ?_ taylorN)
    · rw [← Real.exp_neg]
      apply Real.exp_le_exp.2
      have hpl : (piLoQ : ℝ) ≤ Real.pi := piLoQ_lt_pi.le
      have : (0 : ℝ) ≤ WH.rho * m := by positivity
      push_cast
      nlinarith
    · have : (0 : ℚ) < WH.rho := by exact_mod_cast hρ
      have : (0 : ℚ) < piLoQ := by norm_num [piLoQ]
      positivity
  have key := trig_pair_le (a := (u : ℝ)) (b := (v : ℝ)) (s := sk) (l := (Real.exp A)⁻¹)
    (h := Real.exp A) (L := (expNegUpQ (2 * piLoQ * WH.rho * m) taylorN : ℝ))
    (W := (WH.w : ℝ) ^ m) hu hv (inv_pos.2 (Real.exp_pos A)) hlo hup
    (inv_mul_cancel₀ (Real.exp_pos A).ne') hL hW'
  refine (norm_add_le x y).trans ((add_le_add hx hy).trans (key.trans (le_of_eq ?_)))
  unfold trigRad
  simp only [Rat.cast_max, Rat.cast_add, Rat.cast_mul, Rat.cast_pow]
  rfl

theorem stepT_sound {n : ℕ} {WH : CertWeight} {s N : ℕ} (hW : checkWeight WH s N = true)
    {centre radius : List ℚ} {taylorN : ℕ} {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ certDomain n WH.rho centre radius) {V : List ℂ} {acc : List TBall}
    (hR : TRel n z V acc) {op : SlpOp} {b : TBall}
    (h : stepT n WH centre radius taylorN acc op = some b) :
    ‖op.step n z V - b.1.1.toC‖ ≤ (b.1.2 : ℝ) ∧
      ∀ k a, b.2 = .term k a → ‖op.step n z V‖ ≤ a * charNorm n k z := by
  have hBR := hR.1
  -- the plain ball of `op` whenever `ballStep` succeeds
  have plain : ∀ r, ballStep n WH centre radius taylorN (acc.map Prod.fst) op = some r →
      ‖op.step n z V - r.1.toC‖ ≤ (r.2 : ℝ) := fun r hr => ballStep_sound hW hz hBR hr
  cases op with
  | char k =>
    simp only [stepT, Option.some.injEq] at h
    subst h
    refine ⟨?_, fun k' a hk => ?_⟩
    · have := plain (⟨0, 0⟩, WH.w ^ (k.map Int.natAbs).sum) (by simp [ballStep])
      simpa using this
    · simp only [TrigShape.term.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      simp [SlpOp.step, charNorm]
  | mul a b' =>
    simp only [stepT, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    refine ⟨plain r hr, fun k' u hk => ?_⟩
    have ha := hR.2 a
    have hb := hR.2 b'
    have hma : ‖V.getD a 0‖ ≤ (tbMag (acc.getD a tbZero) : ℝ) := by
      have := norm_le_ballMagQ_of_mem (hBR.2 a)
      rwa [← tb_fst_getD] at this
    have hmb : ‖V.getD b' 0‖ ≤ (tbMag (acc.getD b' tbZero) : ℝ) := by
      have := norm_le_ballMagQ_of_mem (hBR.2 b')
      rwa [← tb_fst_getD] at this
    simp only [SlpOp.step, norm_mul]
    rcases mulShape_cases hk with ⟨u0, hsa, rfl⟩ | ⟨-, v1, hsb, rfl⟩
    · calc ‖V.getD a 0‖ * ‖V.getD b' 0‖
          ≤ (u0 * charNorm n k' z) * (tbMag (acc.getD b' tbZero) : ℝ) :=
            mul_le_mul (hR.2 a _ _ hsa) hmb (norm_nonneg _)
              ((norm_nonneg _).trans (hR.2 a _ _ hsa))
        _ = _ := by push_cast; ring
    · calc ‖V.getD a 0‖ * ‖V.getD b' 0‖
          ≤ (tbMag (acc.getD a tbZero) : ℝ) * (v1 * charNorm n k' z) :=
            mul_le_mul hma (hR.2 b' _ _ hsb) (norm_nonneg _) ((norm_nonneg _).trans hma)
        _ = _ := by push_cast; ring
  | add a b' =>
    simp only [stepT] at h
    split at h
    · rename_i k u k' v hsa hsb
      have hx := hR.2 a k u hsa
      have hy := hR.2 b' k' v hsb
      split_ifs at h with h1 h2
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨r, hr, rfl⟩ := h
        refine ⟨plain r hr, fun k0 w hk => ?_⟩
        simp only [TrigShape.term.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        simp only [SlpOp.step]
        rw [h1] at hy
        calc ‖V.getD a 0 + V.getD b' 0‖ ≤ ‖V.getD a 0‖ + ‖V.getD b' 0‖ := norm_add_le _ _
          _ ≤ u * charNorm n k z + v * charNorm n k z := add_le_add hx hy
          _ = _ := by push_cast; ring
      · simp only [Option.some.injEq] at h
        subst h
        refine ⟨?_, fun k0 w hk => by simp at hk⟩
        simp only [SlpOp.step]
        show ‖_ - CC.toC (⟨0, 0⟩ : CC ℚ)‖ ≤ _
        rw [toC_zero_rat, sub_zero]
        rw [h2] at hy
        exact trig_add_bound hW hz.1 k hx hy
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨r, hr, rfl⟩ := h
        exact ⟨plain r hr, fun k0 w hk => by simp at hk⟩
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      exact ⟨plain r hr, fun k0 w hk => by simp at hk⟩
  | const re im deg =>
    simp only [stepT, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    exact ⟨plain r hr, fun k a hk => by simp at hk⟩
  | action j =>
    simp only [stepT, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    exact ⟨plain r hr, fun k a hk => by simp at hk⟩
  | exp a =>
    simp only [stepT, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    exact ⟨plain r hr, fun k a hk => by simp at hk⟩
  | inv a =>
    simp only [stepT, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    exact ⟨plain r hr, fun k a hk => by simp at hk⟩

theorem ballsAuxT_sound {n : ℕ} {WH : CertWeight} {s N : ℕ} (hW : checkWeight WH s N = true)
    {centre radius : List ℚ} {taylorN : ℕ} {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ certDomain n WH.rho centre radius) (ops : List SlpOp) :
    ∀ (V : List ℂ) (acc bs : List TBall), TRel n z V acc →
      ballsAuxT n WH centre radius taylorN acc ops = some bs →
      TRel n z (ops.foldl (fun acc op => acc ++ [op.step n z acc]) V) bs := by
  induction ops with
  | nil =>
    intro V acc bs hR h
    simp only [ballsAuxT, Option.some.injEq] at h
    subst h
    exact hR
  | cons op ops ih =>
    intro V acc bs hR h
    simp only [ballsAuxT, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, h⟩ := h
    obtain ⟨h1, h2⟩ := stepT_sound hW hz hR hb
    exact ih _ _ _ (hR.snoc h1 h2) h

/-- Every slot value lies in its cosh-pass ball on `D`. -/
theorem val_mem_ballsTrig {n : ℕ} (p : Slp) {WH : CertWeight} {s N : ℕ}
    (hW : checkWeight WH s N = true) {centre radius : List ℚ} {taylorN : ℕ}
    {bs : List (CC ℚ × ℚ)} (h : ballsTrig n p WH centre radius taylorN = some bs)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ certDomain n WH.rho centre radius) (i : ℕ) :
    ‖p.val n z i - (bs.getD i ballZero).1.toC‖ ≤ (bs.getD i ballZero).2 := by
  unfold ballsTrig at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨bt, hbt, rfl⟩ := h
  exact (ballsAuxT_sound hW hz p.ops [] [] bt (TRel.nil n z) hbt).1.2 i

/-- Every slot is bounded by its slot magnitude. -/
theorem norm_val_le_slotMagQ_trig {n : ℕ} {p : Slp} {WH : CertWeight} {s N : ℕ}
    (hW : checkWeight WH s N = true) {centre radius : List ℚ} {taylorN : ℕ}
    {bs : List (CC ℚ × ℚ)} (h : ballsTrig n p WH centre radius taylorN = some bs)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ certDomain n WH.rho centre radius) (i : ℕ) :
    ‖p.val n z i‖ ≤ (slotMagQ bs i : ℝ) :=
  norm_le_ballMagQ_of_mem (val_mem_ballsTrig p hW h hz i)

/-! ### Certified denominators -/

theorem ballsAuxT_prefix_inv {n : ℕ} {WH : CertWeight} {centre radius : List ℚ} {taylorN : ℕ}
    (ops : List SlpOp) :
    ∀ (acc bs : List TBall), ballsAuxT n WH centre radius taylorN acc ops = some bs →
      acc <+: bs ∧ ∀ j a : ℕ, ops[j]? = some (SlpOp.inv a) →
        ((bs.map Prod.fst).getD a ballZero).2 <
          max |((bs.map Prod.fst).getD a ballZero).1.re|
            |((bs.map Prod.fst).getD a ballZero).1.im| := by
  induction ops with
  | nil =>
    intro acc bs h
    simp only [ballsAuxT, Option.some.injEq] at h
    subst h
    exact ⟨List.prefix_refl _, fun j a hj => by simp at hj⟩
  | cons op ops ih =>
    intro acc bs h
    simp only [ballsAuxT, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, h⟩ := h
    obtain ⟨hp, hinv⟩ := ih _ _ h
    refine ⟨(List.prefix_append acc [b]).trans hp, fun j a hj => ?_⟩
    cases j with
    | succ j => exact hinv j a hj
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp only [stepT, Option.map_eq_some_iff] at hb
      obtain ⟨r, hr, -⟩ := hb
      simp only [ballStep] at hr
      split_ifs at hr with hlt
      by_cases ha : a < acc.length
      · obtain ⟨t, ht⟩ := (List.prefix_append acc [b]).trans hp
        have : (bs.map Prod.fst).getD a ballZero = (acc.map Prod.fst).getD a ballZero := by
          rw [← ht, List.map_append, getD_append_lt _ _ _ (by simpa using ha)]
        rw [this]
        exact hlt
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hlt
        simp [ballZero] at hlt

/-- Successful cosh-pass ball arithmetic certifies every `inv` operand on `D`. -/
theorem invGood_of_ballsTrig {n : ℕ} (p : Slp) {WH : CertWeight} {s N : ℕ}
    (hW : checkWeight WH s N = true) {centre radius : List ℚ} {taylorN : ℕ}
    {bs : List (CC ℚ × ℚ)} (h : ballsTrig n p WH centre radius taylorN = some bs) :
    SlpInvGood n (certDomain n WH.rho centre radius) p.ops := by
  intro j a hj z hz
  unfold ballsTrig at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨bt, hbt, rfl⟩ := h
  obtain ⟨-, hinv⟩ := ballsAuxT_prefix_inv p.ops [] bt hbt
  have hlt := hinv j a hj
  have ha : a < (bt.map Prod.fst).length := by
    by_contra hna
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hlt
    simp [ballZero] at hlt
  have hmem := val_mem_ballsTrig p hW (bs := bt.map Prod.fst) (taylorN := taylorN)
    (by simp [ballsTrig, hbt]) hz a
  set x := (bt.map Prod.fst).getD a ballZero with hx
  have hmem' : ‖Slp.val n p z a - x.1.toC‖ ≤ (x.2 : ℝ) := hmem
  have hlt' : (x.2 : ℝ) < max |(x.1.re : ℝ)| |(x.1.im : ℝ)| := by exact_mod_cast hlt
  have hmc : max |(x.1.re : ℝ)| |(x.1.im : ℝ)| ≤ ‖x.1.toC‖ :=
    max_le (Complex.abs_re_le_norm x.1.toC) (Complex.abs_im_le_norm x.1.toC)
  exact (inv_ball_bound hlt' hmc hmem').1

theorem nonvanishingOn_of_ballsTrig {n : ℕ} (e : HamExpr n) {WH : CertWeight} {s N : ℕ}
    (hW : checkWeight WH s N = true) {centre radius : List ℚ} {taylorN : ℕ}
    {bs : List (CC ℚ × ℚ)} (h : ballsTrig n e.jet.prog WH centre radius taylorN = some bs) :
    e.NonvanishingOn (certDomain n WH.rho centre radius) :=
  HamExpr.nonvanishingOn_of_inv_good (isOpen_certDomain n WH.rho centre radius) e [.const 0 0 0]
    e.jet.prog.ops (List.prefix_refl _) (invGood_of_ballsTrig e.jet.prog hW h)

end KAM.CertificateSharp

end
