/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Ecc.Defs

/-!
# The tube centre on a cell (T2-CONF, N6)

Soundness of the centre evaluation of the eccentricity checker
(`KAM/EffectiveStability/Tube/Ecc/Defs.lean`):

* `tubeCenter_eq_W`: `B_k(φ)` is `tubeCenterW` at the circle points `e^{iφ₀}, e^{iφ₁}`;
* `abs_tubeCenterW_sub_le`: on unit circle points within `ε₁, ε₂` of the centre points, `B_k` moves
  by at most `ε₁ lipSum₁ + ε₂ lipSum₂`;
* `abs_tubeCenterW_sub_fix_le`: the fixed-point centre `fixCenterW` (coefficients `fixOf K`) is
  within `errSum` of the exact one at unit points;
* `bSumZ_div_eq`: the Gaussian-integer sum `bSumZ` over the tables of a chart point is the
  fixed-point centre, scaled by `2^K N₁^M N₂^M`;
* `globalOK_spec`, `treeSumQ_eq`: the global check unpacked.
-/

@[expose] public section

open Complex

namespace KAM.EffectiveStability.Tube

/-! ### Sums -/

theorem pairSumQ_sum : ∀ l : List ℚ, (pairSumQ l).sum = l.sum
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by simp [pairSumQ, pairSumQ_sum l, add_assoc]

theorem treeSumQ_eq : ∀ (n : ℕ) (l : List ℚ), treeSumQ n l = l.sum
  | 0, l => rfl
  | _ + 1, [] => rfl
  | _ + 1, [_] => by simp [treeSumQ]
  | n + 1, a :: b :: l => by rw [treeSumQ, treeSumQ_eq n, pairSumQ_sum]

theorem cast_list_sum_map {α : Type*} (l : List α) (f : α → ℚ) :
    (((l.map f).sum : ℚ) : ℝ) = (l.map fun x => (f x : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem cast_list_sum_map_int {α : Type*} (l : List α) (f : α → ℤ) :
    (((l.map f).sum : ℤ) : ℝ) = (l.map fun x => (f x : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem abs_list_sum_sub_le {α : Type*} (l : List α) (f g h : α → ℝ)
    (hfg : ∀ x ∈ l, |f x - g x| ≤ h x) :
    |(l.map f).sum - (l.map g).sum| ≤ (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := hfg a (by simp)
    have h2 := ih (fun x hx => hfg x (by simp [hx]))
    calc |f a + (l.map f).sum - (g a + (l.map g).sum)|
        = |(f a - g a) + ((l.map f).sum - (l.map g).sum)| := by ring_nf
      _ ≤ |f a - g a| + |(l.map f).sum - (l.map g).sum| := abs_add_le _ _
      _ ≤ h a + (l.map h).sum := add_le_add h1 h2

theorem list_sum_map_sub {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map f).sum - (l.map g).sum = (l.map fun x => f x - g x).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

theorem list_sum_map_lin {α : Type*} (l : List α) (a b : ℝ) (f g : α → ℝ) :
    (l.map fun x => a * f x + b * g x).sum = a * (l.map f).sum + b * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring

theorem list_sum_map_div_const {α : Type*} (l : List α) (F : α → ℝ) (c : ℝ) :
    (l.map fun x => F x / c).sum = (l.map F).sum / c := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons]; rw [ih, add_div]

/-! ### The global check -/

/-- The global check unpacked. -/
theorem globalOK_spec {d : EccData} (h : globalOK d = true) :
    d.fix = fixOf d.K d.modes ∧ (∀ x ∈ d.fix, x.1.natAbs ≤ d.M ∧ x.2.1.natAbs ≤ d.M) ∧
      ∀ k, lipSum₁ d.modes k ≤ d.L₁ k ∧ lipSum₂ d.modes k ≤ d.L₂ k ∧
        errSum d.K d.modes k ≤ d.tau k := by
  unfold globalOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨of_decide_eq_true h1, fun x hx => ?_, fun k => ?_⟩
  · have := List.all_eq_true.mp h2 x hx
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at this
    exact this
  · have hk : globalOKk d k = true := by
      rcases k with ⟨_ | _ | _ | n, hn⟩
      · exact h3
      · exact h4
      · exact h5
      · omega
    unfold globalOKk at hk
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
      decide_eq_true_eq] at hk
    exact ⟨hk.1.1, hk.1.2, hk.2⟩

/-! ### Circle points -/

theorem norm_exp_mul_I (x : ℝ) : ‖Complex.exp (x * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I x

theorem cos_eq_re_zpow (m₁ m₂ : ℤ) (φ₀ φ₁ : ℝ) :
    Real.cos (m₁ * φ₀ + m₂ * φ₁) =
      (Complex.exp (φ₀ * I) ^ m₁ * Complex.exp (φ₁ * I) ^ m₂).re := by
  rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
  have : (m₁ : ℂ) * (φ₀ * I) + (m₂ : ℂ) * (φ₁ * I) = ((m₁ * φ₀ + m₂ * φ₁ : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

/-- `B_k(φ)` at the circle points. -/
theorem tubeCenter_eq_W (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ) (k : Fin 3)
    (φ : Fin 2 → ℝ) :
    tubeCenter modes Ibar k φ =
      tubeCenterW modes Ibar k (Complex.exp (φ 0 * I)) (Complex.exp (φ 1 * I)) := by
  unfold tubeCenter tubeCenterW
  congr 2
  apply List.map_congr_left
  intro x _
  rw [cos_eq_re_zpow]

theorem norm_pow_sub_pow_le {w P : ℂ} (hw : ‖w‖ = 1) (hP : ‖P‖ = 1) (n : ℕ) :
    ‖w ^ n - P ^ n‖ ≤ n * ‖w - P‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : w ^ (n + 1) - P ^ (n + 1) = w ^ n * (w - P) + (w ^ n - P ^ n) * P := by ring
    rw [e]
    calc ‖w ^ n * (w - P) + (w ^ n - P ^ n) * P‖
        ≤ ‖w ^ n * (w - P)‖ + ‖(w ^ n - P ^ n) * P‖ := norm_add_le _ _
      _ = ‖w - P‖ + ‖w ^ n - P ^ n‖ := by rw [norm_mul, norm_mul, norm_pow, hw, hP]; ring
      _ ≤ ‖w - P‖ + n * ‖w - P‖ := by linarith
      _ = ((n + 1 : ℕ) : ℝ) * ‖w - P‖ := by push_cast; ring

theorem norm_zpow_sub_zpow_le {w P : ℂ} (hw : ‖w‖ = 1) (hP : ‖P‖ = 1) (m : ℤ) :
    ‖w ^ m - P ^ m‖ ≤ |(m : ℝ)| * ‖w - P‖ := by
  cases m with
  | ofNat n => simpa using norm_pow_sub_pow_le hw hP n
  | negSucc n =>
    have hw0 : w ≠ 0 := by intro h; simp [h] at hw
    have hP0 : P ≠ 0 := by intro h; simp [h] at hP
    rw [zpow_negSucc, zpow_negSucc]
    have e : (w ^ (n + 1))⁻¹ - (P ^ (n + 1))⁻¹ =
        (P ^ (n + 1) - w ^ (n + 1)) / (w ^ (n + 1) * P ^ (n + 1)) := by
      field_simp
    rw [e, norm_div, norm_mul, norm_pow, norm_pow, hw, hP, one_pow, mul_one, div_one, norm_sub_rev]
    have h1 := norm_pow_sub_pow_le hw hP (n + 1)
    have h2 : |((Int.negSucc n : ℤ) : ℝ)| = ((n + 1 : ℕ) : ℝ) := by
      rw [Int.cast_negSucc, abs_neg]; push_cast; exact abs_of_nonneg (by positivity)
    rw [h2]; exact h1

theorem norm_mode_sub_le {w₁ w₂ P₁ P₂ : ℂ} (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1) (hP₁ : ‖P₁‖ = 1)
    (hP₂ : ‖P₂‖ = 1) (m₁ m₂ : ℤ) :
    ‖w₁ ^ m₁ * w₂ ^ m₂ - P₁ ^ m₁ * P₂ ^ m₂‖ ≤ |(m₁ : ℝ)| * ‖w₁ - P₁‖ + |(m₂ : ℝ)| * ‖w₂ - P₂‖ := by
  have e : w₁ ^ m₁ * w₂ ^ m₂ - P₁ ^ m₁ * P₂ ^ m₂ =
      (w₁ ^ m₁ - P₁ ^ m₁) * w₂ ^ m₂ + P₁ ^ m₁ * (w₂ ^ m₂ - P₂ ^ m₂) := by ring
  rw [e]
  calc ‖(w₁ ^ m₁ - P₁ ^ m₁) * w₂ ^ m₂ + P₁ ^ m₁ * (w₂ ^ m₂ - P₂ ^ m₂)‖
      ≤ ‖(w₁ ^ m₁ - P₁ ^ m₁) * w₂ ^ m₂‖ + ‖P₁ ^ m₁ * (w₂ ^ m₂ - P₂ ^ m₂)‖ := norm_add_le _ _
    _ = ‖w₁ ^ m₁ - P₁ ^ m₁‖ + ‖w₂ ^ m₂ - P₂ ^ m₂‖ := by
        rw [norm_mul, norm_mul, norm_zpow, norm_zpow, hw₂, hP₁, one_zpow, one_zpow, mul_one,
          one_mul]
    _ ≤ _ := add_le_add (norm_zpow_sub_zpow_le hw₁ hP₁ m₁) (norm_zpow_sub_zpow_le hw₂ hP₂ m₂)

/-! ### Lipschitz and rounding bounds -/

/-- On unit circle points within `ε₁, ε₂` of the unit centre points, `B_k` moves by at most
`ε₁ lipSum₁ + ε₂ lipSum₂`. -/
theorem abs_tubeCenterW_sub_le (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ) (k : Fin 3)
    {w₁ w₂ P₁ P₂ : ℂ} (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1) (hP₁ : ‖P₁‖ = 1) (hP₂ : ‖P₂‖ = 1)
    {ε₁ ε₂ : ℝ} (h₁ : ‖w₁ - P₁‖ ≤ ε₁) (h₂ : ‖w₂ - P₂‖ ≤ ε₂) :
    |tubeCenterW modes Ibar k w₁ w₂ - tubeCenterW modes Ibar k P₁ P₂| ≤
      ε₁ * (lipSum₁ modes k : ℝ) + ε₂ * (lipSum₂ modes k : ℝ) := by
  unfold tubeCenterW lipSum₁ lipSum₂
  rw [treeSumQ_eq, treeSumQ_eq, cast_list_sum_map, cast_list_sum_map]
  have e : ∀ (a b c : ℝ), a + b - (a + c) = b - c := fun a b c => by ring
  rw [e]
  have key := abs_list_sum_sub_le modes
    (fun x => -((modeK x.1 x.2.1 k : ℤ) : ℝ) * (x.2.2 : ℝ) * (w₁ ^ x.1 * w₂ ^ x.2.1).re)
    (fun x => -((modeK x.1 x.2.1 k : ℤ) : ℝ) * (x.2.2 : ℝ) * (P₁ ^ x.1 * P₂ ^ x.2.1).re)
    (fun x => ε₁ * (((|(modeK x.1 x.2.1 k : ℚ)| * |x.2.2| * |(x.1 : ℚ)| : ℚ) : ℝ)) +
      ε₂ * (((|(modeK x.1 x.2.1 k : ℚ)| * |x.2.2| * |(x.2.1 : ℚ)| : ℚ) : ℝ))) ?_
  · exact key.trans (le_of_eq (list_sum_map_lin _ _ _ _ _))
  · intro x _
    have hm := norm_mode_sub_le hw₁ hw₂ hP₁ hP₂ x.1 x.2.1
    have hre : |(w₁ ^ x.1 * w₂ ^ x.2.1).re - (P₁ ^ x.1 * P₂ ^ x.2.1).re| ≤
        ‖w₁ ^ x.1 * w₂ ^ x.2.1 - P₁ ^ x.1 * P₂ ^ x.2.1‖ := by
      rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have hε₁ : 0 ≤ ε₁ := le_trans (norm_nonneg _) h₁
    have hε₂ : 0 ≤ ε₂ := le_trans (norm_nonneg _) h₂
    have e2 : -((modeK x.1 x.2.1 k : ℤ) : ℝ) * (x.2.2 : ℝ) * (w₁ ^ x.1 * w₂ ^ x.2.1).re -
        -((modeK x.1 x.2.1 k : ℤ) : ℝ) * (x.2.2 : ℝ) * (P₁ ^ x.1 * P₂ ^ x.2.1).re =
        -((modeK x.1 x.2.1 k : ℤ) : ℝ) * (x.2.2 : ℝ) *
          ((w₁ ^ x.1 * w₂ ^ x.2.1).re - (P₁ ^ x.1 * P₂ ^ x.2.1).re) := by ring
    rw [e2, abs_mul, abs_mul, abs_neg]
    push_cast
    have hA : 0 ≤ |((modeK x.1 x.2.1 k : ℤ) : ℝ)| * |(x.2.2 : ℝ)| := by positivity
    calc |((modeK x.1 x.2.1 k : ℤ) : ℝ)| * |(x.2.2 : ℝ)| *
          |(w₁ ^ x.1 * w₂ ^ x.2.1).re - (P₁ ^ x.1 * P₂ ^ x.2.1).re|
        ≤ |((modeK x.1 x.2.1 k : ℤ) : ℝ)| * |(x.2.2 : ℝ)| *
          (|(x.1 : ℝ)| * ‖w₁ - P₁‖ + |(x.2.1 : ℝ)| * ‖w₂ - P₂‖) :=
          mul_le_mul_of_nonneg_left (hre.trans hm) hA
      _ ≤ |((modeK x.1 x.2.1 k : ℤ) : ℝ)| * |(x.2.2 : ℝ)| *
          (|(x.1 : ℝ)| * ε₁ + |(x.2.1 : ℝ)| * ε₂) := by gcongr
      _ = _ := by ring

/-- The fixed-point centre at circle points: `Ī_k + Σ_fix (-m_k) (n / 2^K) Re(w₁^{m₁} w₂^{m₂})`. -/
noncomputable def fixCenterW (K : ℕ) (fix : List (ℤ × ℤ × ℤ)) (Ibar : Fin 3 → ℚ) (k : Fin 3)
    (w₁ w₂ : ℂ) : ℝ :=
  (Ibar k : ℝ) + (fix.map fun x =>
    -((modeK x.1 x.2.1 k : ℤ) : ℝ) * ((x.2.2 : ℝ) / 2 ^ K) * (w₁ ^ x.1 * w₂ ^ x.2.1).re).sum

theorem fixOf_sum (K : ℕ) (modes : List (ℤ × ℤ × ℚ)) (k : Fin 3) (w₁ w₂ : ℂ) :
    ((fixOf K modes).map fun x =>
      -((modeK x.1 x.2.1 k : ℤ) : ℝ) * ((x.2.2 : ℝ) / 2 ^ K) * (w₁ ^ x.1 * w₂ ^ x.2.1).re).sum =
    (modes.map fun x =>
      -((modeK x.1 x.2.1 k : ℤ) : ℝ) * ((fixVal K x.2.2 : ℚ) : ℝ) *
        (w₁ ^ x.1 * w₂ ^ x.2.1).re).sum := by
  induction modes with
  | nil => simp [fixOf]
  | cons a l ih =>
    unfold fixOf at ih ⊢
    rw [List.filterMap_cons]
    by_cases h0 : truncQ (a.2.2 * pow2 K) = 0
    · simp only [h0, ite_true, List.map_cons, List.sum_cons]
      rw [ih]; simp [fixVal, h0]
    · simp only [h0, ite_false, List.map_cons, List.sum_cons]
      rw [ih]; simp [fixVal, pow2]

/-- The fixed-point centre is within `errSum` of the exact centre at unit points. -/
theorem abs_tubeCenterW_sub_fix_le (K : ℕ) (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ)
    (k : Fin 3) {P₁ P₂ : ℂ} (hP₁ : ‖P₁‖ = 1) (hP₂ : ‖P₂‖ = 1) :
    |tubeCenterW modes Ibar k P₁ P₂ - fixCenterW K (fixOf K modes) Ibar k P₁ P₂| ≤
      (errSum K modes k : ℝ) := by
  unfold tubeCenterW fixCenterW errSum
  rw [fixOf_sum, treeSumQ_eq, cast_list_sum_map]
  have e : ∀ (a b c : ℝ), a + b - (a + c) = b - c := fun a b c => by ring
  rw [e]
  apply abs_list_sum_sub_le
  intro x _
  have hre : |(P₁ ^ x.1 * P₂ ^ x.2.1).re| ≤ 1 := by
    refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, norm_zpow, norm_zpow, hP₁, hP₂, one_zpow, one_zpow, one_mul]
  have e2 : -((modeK x.1 x.2.1 k : ℤ) : ℝ) * (x.2.2 : ℝ) * (P₁ ^ x.1 * P₂ ^ x.2.1).re -
      -((modeK x.1 x.2.1 k : ℤ) : ℝ) * ((fixVal K x.2.2 : ℚ) : ℝ) * (P₁ ^ x.1 * P₂ ^ x.2.1).re =
      -((modeK x.1 x.2.1 k : ℤ) : ℝ) * ((x.2.2 : ℝ) - ((fixVal K x.2.2 : ℚ) : ℝ)) *
        (P₁ ^ x.1 * P₂ ^ x.2.1).re := by ring
  rw [e2, abs_mul, abs_mul, abs_neg]
  push_cast
  have hA : 0 ≤ |((modeK x.1 x.2.1 k : ℤ) : ℝ)| * |(x.2.2 : ℝ) - ((fixVal K x.2.2 : ℚ) : ℝ)| := by
    positivity
  calc |((modeK x.1 x.2.1 k : ℤ) : ℝ)| * |(x.2.2 : ℝ) - ((fixVal K x.2.2 : ℚ) : ℝ)| *
        |(P₁ ^ x.1 * P₂ ^ x.2.1).re|
      ≤ |((modeK x.1 x.2.1 k : ℤ) : ℝ)| * |(x.2.2 : ℝ) - ((fixVal K x.2.2 : ℚ) : ℝ)| * 1 :=
        mul_le_mul_of_nonneg_left hre hA
    _ = _ := by rw [mul_one]

/-! ### The Gaussian-integer evaluation -/

/-- The integer sum `bSumZ` over the tables of the chart points `P_a = circPt s_a t_a` is
`2^K N₁^M N₂^M (B̃_k(P) - Ī_k)`. -/
theorem bSumZ_div_eq (K M : ℕ) (fix : List (ℤ × ℤ × ℤ)) (Ibar : Fin 3 → ℚ) (k : Fin 3)
    (hM : ∀ x ∈ fix, x.1.natAbs ≤ M ∧ x.2.1.natAbs ≤ M) (s₁ s₂ : Bool) (t₁ t₂ : ℚ) :
    ((Ibar k + (bSumZ fix (GZ.table (circG s₁ t₁) (circN t₁) M)
        (GZ.table (circG s₂ t₂) (circN t₂) M) k : ℚ) /
        (pow2 K * ((circN t₁ ^ M * circN t₂ ^ M : ℤ) : ℚ)) : ℚ) : ℝ) =
      fixCenterW K fix Ibar k (GQ.toC (circPt s₁ t₁)) (GQ.toC (circPt s₂ t₂)) := by
  have hN₁ := circN_pos t₁
  have hN₂ := circN_pos t₂
  have hP₁ : Complex.normSq (GQ.toC (circPt s₁ t₁)) = 1 := by
    rw [← GQ.nsq_eq, nsq_circPt]; simp
  have hP₂ : Complex.normSq (GQ.toC (circPt s₂ t₂)) = 1 := by
    rw [← GQ.nsq_eq, nsq_circPt]; simp
  set N₁ : ℤ := circN t₁
  set N₂ : ℤ := circN t₂
  have hsum : ((bSumZ fix (GZ.table (circG s₁ t₁) N₁ M) (GZ.table (circG s₂ t₂) N₂ M) k : ℤ) : ℝ) =
      ((N₁ : ℝ) ^ M * (N₂ : ℝ) ^ M) * (fix.map fun x =>
        -((modeK x.1 x.2.1 k : ℤ) : ℝ) * (x.2.2 : ℝ) *
          (GQ.toC (circPt s₁ t₁) ^ x.1 * GQ.toC (circPt s₂ t₂) ^ x.2.1).re).sum := by
    unfold bSumZ
    rw [cast_list_sum_map_int]
    induction fix with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih (fun x hx => hM x (by simp [hx])), mul_add]
      congr 1
      obtain ⟨ha₁, ha₂⟩ := hM a (by simp)
      have e₁ := GZ.toC_zpowT (ne_of_gt hN₁) (toC_circG s₁ t₁) hP₁ M a.1 ha₁
      have e₂ := GZ.toC_zpowT (ne_of_gt hN₂) (toC_circG s₂ t₂) hP₂ M a.2.1 ha₂
      push_cast
      rw [GZ.reMul_eq, e₁, e₂]
      have : ((N₁ : ℂ) ^ M * GQ.toC (circPt s₁ t₁) ^ a.1 *
          ((N₂ : ℂ) ^ M * GQ.toC (circPt s₂ t₂) ^ a.2.1)) =
          (((N₁ : ℝ) ^ M * (N₂ : ℝ) ^ M : ℝ) : ℂ) *
            (GQ.toC (circPt s₁ t₁) ^ a.1 * GQ.toC (circPt s₂ t₂) ^ a.2.1) := by push_cast; ring
      rw [this, Complex.re_ofReal_mul]
      ring
  unfold fixCenterW
  have hpos : (0 : ℝ) < (N₁ : ℝ) ^ M * (N₂ : ℝ) ^ M := by positivity
  have e : (fix.map fun x => -((modeK x.1 x.2.1 k : ℤ) : ℝ) * ((x.2.2 : ℝ) / 2 ^ K) *
      (GQ.toC (circPt s₁ t₁) ^ x.1 * GQ.toC (circPt s₂ t₂) ^ x.2.1).re) =
      fix.map fun x => -((modeK x.1 x.2.1 k : ℤ) : ℝ) * (x.2.2 : ℝ) *
        (GQ.toC (circPt s₁ t₁) ^ x.1 * GQ.toC (circPt s₂ t₂) ^ x.2.1).re / 2 ^ K :=
    List.map_congr_left (fun x _ => by ring)
  rw [e, list_sum_map_div_const, Rat.cast_add, Rat.cast_div, Rat.cast_intCast, Rat.cast_mul, pow2,
    Rat.cast_natCast, Rat.cast_intCast, hsum]
  push_cast
  congr 1
  field_simp
