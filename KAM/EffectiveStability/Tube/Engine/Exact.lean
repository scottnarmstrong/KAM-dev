/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Input

/-!
# Exact dense inputs (T2-CONF, N7)

* `evalR κ p n a = Σ_{i<n} a_i trig_p (κ i · φ)` with real coefficients; `pderiv_evalR`,
  `c1Close_evalR` (two such sums are `C¹`-close with the `ℓ¹` and weighted norms of their
  difference).
* `boxKey C i = (i % (2C+1) - C, i / (2C+1) - C)`; `evalK_litList`: the value of a literal is the
  sum over its compact digits.
* `denseCos C cs`: the cosine series of a dense rational list in box order.
* `treeSumG`: a balanced sum in any additive monoid (kernel depth `O(log n)`).
* `inputCheck`, `input_sound`: a literal rounding exact dense data, with the exact errors.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.Certificate KAM.CertificateSharp.Packed

/-! ### Real coefficients -/

/-- `Σ_{i<n} a_i trig_p (κ i · φ)`. -/
noncomputable def evalR (κ : ℕ → ℤ × ℤ) (p : Bool) (n : ℕ) (a : ℕ → ℝ) (φ : Fin 2 → ℝ) : ℝ :=
  ∑ i ∈ range n, a i * trig p (kdot (κ i) φ)

theorem hasFDerivAt_evalR (κ : ℕ → ℤ × ℤ) (p : Bool) (n : ℕ) (a : ℕ → ℝ) (φ : Fin 2 → ℝ) :
    HasFDerivAt (evalR κ p n a)
      (∑ i ∈ range n, (a i * ((psgn p : ℝ) * trig (!p) (kdot (κ i) φ))) • kdotL (κ i)) φ := by
  have h : ∀ i ∈ range n, HasFDerivAt (fun φ => a i * trig p (kdot (κ i) φ))
      ((a i * ((psgn p : ℝ) * trig (!p) (kdot (κ i) φ))) • kdotL (κ i)) φ := by
    intro i _
    have := ((hasDerivAt_trig p (kdot (κ i) φ)).comp_hasFDerivAt φ (hasFDerivAt_kdot (κ i) φ))
    have := this.const_mul (a i)
    rw [smul_smul] at this
    exact this
  have := HasFDerivAt.sum h
  convert this using 1
  ext φ
  simp [evalR]

theorem differentiable_evalR (κ : ℕ → ℤ × ℤ) (p : Bool) (n : ℕ) (a : ℕ → ℝ) :
    Differentiable ℝ (evalR κ p n a) := fun φ => (hasFDerivAt_evalR κ p n a φ).differentiableAt

theorem pderiv_evalR (κ : ℕ → ℤ × ℤ) (p : Bool) (n : ℕ) (a : ℕ → ℝ) (φ : Fin 2 → ℝ)
    (b : Fin 2) : pderiv (evalR κ p n a) φ b =
      evalR κ (!p) n (fun i => (psgn p * kc (κ i) b : ℤ) * a i) φ := by
  rw [pderiv, (hasFDerivAt_evalR κ p n a φ).fderiv, _root_.sum_apply, evalR]
  refine sum_congr rfl fun i _ => ?_
  rw [smul_apply, kdotL_single, smul_eq_mul]
  push_cast
  ring

theorem abs_evalR_le (κ : ℕ → ℤ × ℤ) (p : Bool) (n : ℕ) (a : ℕ → ℝ) (φ : Fin 2 → ℝ) :
    |evalR κ p n a φ| ≤ ∑ i ∈ range n, |a i| := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  calc |a i| * |trig p (kdot (κ i) φ)| ≤ |a i| * 1 :=
        mul_le_mul_of_nonneg_left (abs_trig_le _ _) (abs_nonneg _)
    _ = |a i| := mul_one _

theorem evalR_sub (κ : ℕ → ℤ × ℤ) (p : Bool) (n : ℕ) (a b : ℕ → ℝ) (φ : Fin 2 → ℝ) :
    evalR κ p n a φ - evalR κ p n b φ = evalR κ p n (fun i => a i - b i) φ := by
  rw [evalR, evalR, evalR, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- **Two real trigonometric sums are `C¹`-close** with the norms of their difference. -/
theorem c1Close_evalR (κ : ℕ → ℤ × ℤ) (p : Bool) (n : ℕ) (a b : ℕ → ℝ) {e₀ e₁ : ℝ}
    (h₀ : ∑ i ∈ range n, |a i - b i| ≤ e₀)
    (h₁ : ∀ c : Fin 2, ∑ i ∈ range n, |(kc (κ i) c : ℝ)| * |a i - b i| ≤ e₁) :
    C1Close (evalR κ p n a) (evalR κ p n b) e₀ e₁ := by
  refine ⟨differentiable_evalR _ _ _ _, differentiable_evalR _ _ _ _, fun φ => ?_, fun φ c => ?_⟩
  · rw [evalR_sub]; exact (abs_evalR_le _ _ _ _ _).trans h₀
  · change |pderiv (evalR κ p n a) φ c - pderiv (evalR κ p n b) φ c| ≤ e₁
    rw [pderiv_evalR, pderiv_evalR, evalR_sub]
    refine (abs_evalR_le _ _ _ _ _).trans ((sum_le_sum fun i _ => ?_).trans (h₁ c))
    rw [← mul_sub, abs_mul]
    push_cast
    rw [abs_mul]
    cases p <;> simp [psgn]

/-! ### Literals as compact-digit sums -/

/-- The mode of compact index `i` of the square box of half-width `C`. -/
def boxKey (C i : ℕ) : ℤ × ℤ :=
  (((i % (2 * C + 1) : ℕ) : ℤ) - C, ((i / (2 * C + 1) : ℕ) : ℤ) - C)

theorem evalK_litList {C S b X : ℕ} (hKS : 2 * C + 1 ≤ S) (p : Bool) (φ : Fin 2 → ℝ) :
    evalK (Layout.key C S) p (litList C S b X) φ =
      evalR (boxKey C) p ((2 * C + 1) * (2 * C + 1))
        (fun i => (((dig b X i : ℤ) - 2 ^ (b - 1) : ℤ) : ℝ)) φ := by
  set K := 2 * C + 1 with hK
  have hS : 0 < S := by omega
  have hlen : Layout.len C S ≤ S * K := by unfold Layout.len; rw [hK]; nlinarith
  rw [evalK, length_litList]
  have hext : ∑ i ∈ range (Layout.len C S), ((litList C S b X).getD i 0 : ℝ) *
      trig p (kdot (Layout.key C S i) φ) = ∑ i ∈ range (S * K), ((litList C S b X).getD i 0 : ℝ) *
      trig p (kdot (Layout.key C S i) φ) := by
    refine sum_subset (range_subset_range.mpr hlen) fun i _ hi => ?_
    rw [getD_litList, if_neg (by simpa using hi)]; simp
  rw [hext, sum_range_mul_regroup S _ K, evalR, sum_range_mul_regroup K _ K]
  refine sum_congr rfl fun r hr => ?_
  have hr' := mem_range.mp hr
  symm
  refine sum_subset_zero_on_sdiff (range_subset_range.mpr hKS) (fun c hc => ?_) (fun c hc => ?_)
  · rw [mem_sdiff, mem_range, mem_range] at hc
    rw [getD_litList]
    split_ifs
    · unfold litSlot
      rw [(mod_div_of_lt hc.1).1, if_neg (by omega)]; simp
    · simp
  · have hcK := mem_range.mp hc
    have hlt : c + S * r < Layout.len C S := by
      unfold Layout.len
      have : S * r ≤ S * (2 * C) := Nat.mul_le_mul_left S (by omega)
      nlinarith
    rw [getD_litList, if_pos hlt]
    have e1 := mod_div_of_lt (S := S) (c := c) (r := r) (by omega)
    have e2 := mod_div_of_lt (S := K) (c := c) (r := r) hcK
    unfold litSlot Layout.key boxKey
    rw [← hK, e1.1, e1.2, e2.1, e2.2, if_pos hcK]

/-! ### Balanced sums in a monoid -/

/-- One pass of pairwise sums. -/
def pairSumG {α : Type*} [Add α] : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: l => (a + b) :: pairSumG l

/-- Balanced sum (`fuel` passes). -/
def treeSumG {α : Type*} [AddMonoid α] : ℕ → List α → α
  | _, [] => 0
  | _, [a] => a
  | 0, a :: b :: l => (a :: b :: l).sum
  | f + 1, a :: b :: l => treeSumG f (pairSumG (a :: b :: l))

theorem sum_pairSumG {α : Type*} [AddMonoid α] : ∀ l : List α, (pairSumG l).sum = l.sum
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    rw [pairSumG, List.sum_cons, sum_pairSumG l, List.sum_cons, List.sum_cons, add_assoc]

theorem treeSumG_eq {α : Type*} [AddMonoid α] : ∀ (f : ℕ) (l : List α), treeSumG f l = l.sum
  | _, [] => by simp [treeSumG]
  | _, [a] => by simp [treeSumG]
  | 0, a :: b :: l => rfl
  | f + 1, a :: b :: l => by rw [treeSumG, treeSumG_eq f, sum_pairSumG]

/-! ### Exact dense inputs -/

/-- The cosine series of a dense rational list in box order. -/
noncomputable def denseCos (C : ℕ) (cs : List ℚ) (φ : Fin 2 → ℝ) : ℝ :=
  evalR (boxKey C) false ((2 * C + 1) * (2 * C + 1)) (fun i => ((cs.getD i 0 : ℚ) : ℝ)) φ

/-- The slot differences `c_i - q (d_i - 2^(b-1))` of exact data against compact digits. -/
def inputDiffs (q : ℚ) (b : ℕ) (cs : List ℚ) (ds : List ℕ) : List ℚ :=
  List.zipWith (fun (c : ℚ) (d : ℕ) => c - q * (((d : ℕ) : ℤ) - 2 ^ (b - 1) : ℤ)) cs ds

/-- The kernel check of a literal against exact dense data (even parity). -/
def inputCheck (P : Prm) (d : LitD) (cs : List ℚ) (e₀ e₁ : ℚ) : Bool :=
  d.ok P && !d.par && cs.length == (2 * d.C + 1) * (2 * d.C + 1) &&
    decide (treeSumG 64 ((inputDiffs d.q P.b cs (compactDigits d.C P.b d.X)).map (|·|)) ≤ e₀) &&
    decide (treeSumG 64 (mapIx (fun i x => (|kc (boxKey d.C i) 0| : ℚ) * |x|) 0
      (inputDiffs d.q P.b cs (compactDigits d.C P.b d.X))) ≤ e₁) &&
    decide (treeSumG 64 (mapIx (fun i x => (|kc (boxKey d.C i) 1| : ℚ) * |x|) 0
      (inputDiffs d.q P.b cs (compactDigits d.C P.b d.X))) ≤ e₁)

theorem sum_map_range_g {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n : ℕ, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_map_range_g f n, sum_range_succ]
    simp

theorem eq_map_range_getD {α : Type*} (l : List α) (d : α) :
    l = (List.range l.length).map (fun i => l.getD i d) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

theorem sum_mapIx_eq {α M : Type*} [AddCommMonoid M] (f : ℕ → α → M) (a₀ : α) :
    ∀ (i₀ : ℕ) (l : List α), (mapIx f i₀ l).sum = ∑ i ∈ range l.length, f (i₀ + i) (l.getD i a₀)
  | _, [] => by simp [mapIx]
  | i₀, a :: l => by
    rw [mapIx, List.sum_cons, sum_mapIx_eq f a₀ (i₀ + 1) l, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    congr 1
    omega

theorem getD_inputDiffs {q : ℚ} {b : ℕ} {cs : List ℚ} {ds : List ℕ} {i : ℕ}
    (hi : i < cs.length) (hl : ds.length = cs.length) :
    (inputDiffs q b cs ds).getD i 0 = cs.getD i 0 - q * ((ds.getD i 0 : ℤ) - 2 ^ (b - 1) : ℤ) := by
  unfold inputDiffs
  have hi' : i < ds.length := by rw [hl]; exact hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi']
  rfl

theorem length_inputDiffs {q : ℚ} {b : ℕ} {cs : List ℚ} {ds : List ℕ} (hl : ds.length = cs.length) :
    (inputDiffs q b cs ds).length = cs.length := by
  simp [inputDiffs, hl]

theorem length_compactDigits (C b X : ℕ) :
    (compactDigits C b X).length = (2 * C + 1) * (2 * C + 1) := by
  rw [compactDigits_eq]; simp

theorem getD_compactDigits {C b X i : ℕ} (hi : i < (2 * C + 1) * (2 * C + 1)) :
    (compactDigits C b X).getD i 0 = dig b X i := by
  rw [compactDigits_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- **Soundness of an exact input**: the literal is `C¹`-close to the exact dense cosine series. -/
theorem input_sound {P : Prm} {d : LitD} {cs : List ℚ} {e₀ e₁ : ℚ}
    (h : inputCheck P d cs e₀ e₁ = true) : C1Close (denseCos d.C cs) ((d.opd P).eval P.S) e₀ e₁ := by
  simp only [inputCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true']
    at h
  obtain ⟨⟨⟨⟨⟨hok, hpar⟩, hlen⟩, h0⟩, h1⟩, h2⟩ := h
  have hok' := hok
  simp only [LitD.ok, Bool.and_eq_true, decide_eq_true_eq] at hok'
  obtain ⟨⟨⟨⟨hb, hbw⟩, hKS⟩, -⟩, -⟩ := hok'
  set n := (2 * d.C + 1) * (2 * d.C + 1) with hn
  set ds := compactDigits d.C P.b d.X with hds
  have hdl : ds.length = cs.length := by rw [hds, length_compactDigits, hlen]
  set D := inputDiffs d.q P.b cs ds with hD
  have hDl : D.length = n := by rw [hD, length_inputDiffs hdl, hlen]
  have hDg : ∀ i < n, D.getD i 0 = cs.getD i 0 - d.q * ((dig P.b d.X i : ℤ) - 2 ^ (P.b - 1) : ℤ) :=
    fun i hi => by
      rw [hD, getD_inputDiffs (by rw [hlen]; exact hi) hdl, hds, getD_compactDigits hi]
  -- the model as a real trigonometric sum
  have hmodel : (d.opd P).eval P.S = evalR (boxKey d.C) false n
      (fun i => ((d.q * ((dig P.b d.X i : ℤ) - 2 ^ (P.b - 1) : ℤ) : ℚ) : ℝ)) := by
    funext φ
    simp only [Opd.eval, LitD.opd]
    rw [hpar, evalK_litList hKS, evalR, evalR, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    push_cast; ring
  have hterm : ∀ i ∈ range n, (((cs.getD i 0 : ℚ) : ℝ) -
      ((d.q * ((dig P.b d.X i : ℤ) - 2 ^ (P.b - 1) : ℤ) : ℚ) : ℝ)) = ((D.getD i 0 : ℚ) : ℝ) :=
    fun i hi => by rw [hDg i (mem_range.mp hi)]; push_cast; ring
  rw [hmodel]
  unfold denseCos
  refine c1Close_evalR _ _ _ _ _ ?_ ?_
  · rw [sum_congr rfl fun i hi => by rw [hterm i hi]]
    have hs : (D.map (|·|)).sum = ∑ i ∈ range n, |D.getD i 0| := by
      conv_lhs => rw [eq_map_range_getD D 0]
      rw [List.map_map, hDl, sum_map_range_g]; rfl
    rw [treeSumG_eq, hs] at h0
    have h0' : ((∑ i ∈ range n, |D.getD i 0| : ℚ) : ℝ) ≤ (e₀ : ℝ) := by exact_mod_cast h0
    push_cast at h0'
    exact h0'
  · intro c
    rw [sum_congr rfl fun i hi => by rw [hterm i hi]]
    have hw : ∀ c' : Fin 2, (mapIx (fun i x => (|kc (boxKey d.C i) c'| : ℚ) * |x|) 0 D).sum =
        ∑ i ∈ range n, (|kc (boxKey d.C i) c'| : ℚ) * |D.getD i 0| := fun c' => by
      rw [sum_mapIx_eq _ 0, hDl]; simp
    fin_cases c
    · rw [treeSumG_eq, hw] at h1
      have h1' : ((∑ i ∈ range n, (|kc (boxKey d.C i) 0| : ℚ) * |D.getD i 0| : ℚ) : ℝ) ≤
          (e₁ : ℝ) := by exact_mod_cast h1
      push_cast at h1'
      simpa using h1'
    · rw [treeSumG_eq, hw] at h2
      have h2' : ((∑ i ∈ range n, (|kc (boxKey d.C i) 1| : ℚ) * |D.getD i 0| : ℚ) : ℝ) ≤
          (e₁ : ℝ) := by exact_mod_cast h2
      push_cast at h2'
      simpa using h2'

end KAM.EffectiveStability.Tube

end
