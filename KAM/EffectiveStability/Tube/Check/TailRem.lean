/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Check.TailMaj
public import KAM.EffectiveStability.Tube.Poly.HTildeBounds

/-!
# The remainder budget of `h̃` from `n`-uniform slot tables (T2-CONF, N9 (C))

N5a's `hRem_tube` bounds the partials of the Taylor remainder
`R = Σ_n T_n · binomProdRem (n/2) L B u` by `Σ_n τ_n · remBound(n)`. With the factored majorants of
`TailMaj` and tables `GT K j m ≥ slotHat (n_j/2) …` for all `n_j ≤ K` (likewise `GTD`, `GTP`), every
`remBound(n)` is at most `Π_j hi_j^{n_j} · tailSum(GT |n|)` (`hi_j ≥ √b_max,j`), and the sum over
exponents regroups into
one sum over the rows (`hRem_bounds_rows`):

* `|∂_{u_i} R| ≤ Σ_rows |c| Π_j hi_j^{n_j} · tailSum(update (GT K) i (GTD K i))`,
* `|∂_{φ_a} R| ≤ Σ_rows |c| Π_j hi_j^{n_j} · ((|k₀| + |k₁|) tailSum(GT K) +
  Σ_i β_i tailSum(update (GT K) i (GTP K i)))`,

with `K = |n|` the row's total exponent (`≤ 18`, so `n_j/2 ≤ 9`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Finset Real

variable (E N : ℕ)

theorem slotHat_nonneg {s bmin bmax r : ℝ} {L : ℕ} (hr0 : 0 ≤ r) (hr : r < bmin)
    (hb : bmin ≤ bmax) (m : ℕ) : 0 ≤ slotHat s L bmin bmax r m := by
  have h1 : 0 < bmin - r := by linarith
  have h2 : 0 < bmax := by linarith
  have h3 : 0 < bmin := by linarith
  unfold slotHat; split_ifs <;> positivity

theorem slotHatDu_nonneg {s bmin bmax r : ℝ} {L : ℕ} (hr0 : 0 ≤ r) (hr : r < bmin)
    (hb : bmin ≤ bmax) (m : ℕ) : 0 ≤ slotHatDu s L bmin bmax r m := by
  have h1 : 0 < bmin - r := by linarith
  have h2 : 0 < bmax := by linarith
  have h3 : 0 < bmin := by linarith
  unfold slotHatDu; split_ifs <;> positivity

theorem slotHatP_nonneg {s bmin bmax r : ℝ} {L : ℕ} (hr0 : 0 ≤ r) (hr : r < bmin)
    (hb : bmin ≤ bmax) (m : ℕ) : 0 ≤ slotHatP s L bmin bmax r m := by
  have h1 : 0 < bmin - r := by linarith
  have h2 : 0 < bmax := by linarith
  have h3 : 0 < bmin := by linarith
  unfold slotHatP; split_ifs <;> positivity

/-- `b^{n/2} ≤ hi^n` for `0 ≤ b ≤ hi²`, `hi ≥ 0`. -/
theorem rpow_half_le_pow {b hi : ℝ} (hb : 0 ≤ b) (hhi : 0 ≤ hi) (h : b ≤ hi ^ 2) (n : ℕ) :
    b ^ ((n : ℝ) / 2) ≤ hi ^ n := by
  have e : b ^ ((n : ℝ) / 2) = (√b) ^ n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hb]; congr 1; ring
  rw [e]
  have : √b ≤ hi := by
    rw [show hi = √(hi ^ 2) from (Real.sqrt_sq hhi).symm]; exact Real.sqrt_le_sqrt h
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) this n

theorem halfExp_nonneg (n : Fin 3 → ℕ) (j : Fin 3) : 0 ≤ halfExp n j := by
  unfold halfExp; positivity

theorem halfExp_le_nine {n : Fin 3 → ℕ} (hn : mdeg n ≤ 18) (j : Fin 3) : halfExp n j ≤ 9 := by
  have : n j ≤ 18 := (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
    (mem_univ j)).trans hn
  unfold halfExp
  have : (n j : ℝ) ≤ 18 := by exact_mod_cast this
  linarith

theorem le_mdeg (n : Fin 3 → ℕ) (j : Fin 3) : n j ≤ mdeg n :=
  Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (mem_univ j)

/-- A sum over the exponents of the rows, regrouped as a sum over the rows. -/
theorem sum_expSet_eq_rows (rows : List ((Mon × Mon) × ℤ)) (X : (Fin 3 → ℕ) → ℝ) :
    ∑ n ∈ expSet rows, ((rows.filter fun e => decide (rowExp e = n)).map fun e =>
      |rowCoef E N e|).sum * X n = (rows.map fun e => |rowCoef E N e| * X (rowExp e)).sum := by
  rw [list_sum_eq_sum_filter rowExp (fun e => |rowCoef E N e| * X (rowExp e)) (expSet rows) rows
    (fun a ha => List.mem_toFinset.2 (List.mem_map_of_mem ha))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun e he => ?_)
  rw [(by simpa using (List.mem_filter.1 he).2 : rowExp e = n)]

theorem sum_expSet_eq_rows' (rows : List ((Mon × Mon) × ℤ)) (X : (Fin 3 → ℕ) → ℝ) :
    ∑ n ∈ expSet rows, ((rows.filter fun e => decide (rowExp e = n)).map fun e =>
      |rowCoef E N e| * (|((rowMode e).1 : ℝ)| + |((rowMode e).2 : ℝ)|)).sum * X n =
      (rows.map fun e => |rowCoef E N e| * (|((rowMode e).1 : ℝ)| + |((rowMode e).2 : ℝ)|) *
        X (rowExp e)).sum := by
  rw [list_sum_eq_sum_filter rowExp (fun e => |rowCoef E N e| *
    (|((rowMode e).1 : ℝ)| + |((rowMode e).2 : ℝ)|) * X (rowExp e)) (expSet rows) rows
    (fun a ha => List.mem_toFinset.2 (List.mem_map_of_mem ha))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun e he => ?_)
  rw [(by simpa using (List.mem_filter.1 he).2 : rowExp e = n)]

theorem list_sum_mono {α : Type*} (l : List α) (f g : α → ℝ) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem list_sum_nonneg' {α : Type*} (l : List α) (f : α → ℝ) (h : ∀ a ∈ l, 0 ≤ f a) :
    0 ≤ (l.map f).sum := by
  simpa using list_sum_mono l (fun _ => 0) f h

/-- **The remainder budget, row by row.** -/
theorem hRem_bounds_rows (rows : List ((Mon × Mon) × ℤ)) (B : (Fin 2 → ℝ) → Fin 3 → ℝ) (L : ℕ)
    {bmin bmax β hi : Fin 3 → ℝ} {r : ℝ}
    (hBd : ∀ j, Differentiable ℝ fun φ => B φ j) (hr0 : 0 ≤ r) (hr : ∀ j, r < bmin j)
    (h1 : ∀ j φ, bmin j ≤ B φ j) (h2 : ∀ j φ, B φ j ≤ bmax j)
    (hβ : ∀ j φ a, |fderiv ℝ (fun φ => B φ j) φ (Pi.single a 1)| ≤ β j)
    (hhi : ∀ j, 0 ≤ hi j ∧ bmax j ≤ hi j ^ 2)
    (hdeg : ∀ e ∈ rows, mdeg (rowExp e) ≤ 18)
    {GT GTD GTP : ℕ → Fin 3 → ℕ → ℝ}
    (hGT : ∀ K : ℕ, K ≤ 18 → ∀ nj : ℕ, nj ≤ K → ∀ j m, m < L + 2 →
      slotHat ((nj : ℝ) / 2) L (bmin j) (bmax j) r m ≤ GT K j m)
    (hGTD : ∀ K : ℕ, K ≤ 18 → ∀ nj : ℕ, nj ≤ K → ∀ j m, m < L + 2 →
      slotHatDu ((nj : ℝ) / 2) L (bmin j) (bmax j) r m ≤ GTD K j m)
    (hGTP : ∀ K : ℕ, K ≤ 18 → ∀ nj : ℕ, nj ≤ K → ∀ j m, m < L + 2 →
      slotHatP ((nj : ℝ) / 2) L (bmin j) (bmax j) r m ≤ GTP K j m)
    (φ : Fin 2 → ℝ) (u : Fin 3 → ℝ) (hu : ∀ j, |u j| ≤ r) :
    (∀ i, |fderiv ℝ (fun v => hRem E N rows B L (v, φ)) u (Pi.single i 1)| ≤
      (rows.map fun e => |rowCoef E N e| * (∏ j, hi j ^ rowExp e j) *
        tailSum (Function.update (GT (mdeg (rowExp e))) i (GTD (mdeg (rowExp e)) i)) L).sum) ∧
    (∀ a, |fderiv ℝ (fun ψ => hRem E N rows B L (u, ψ)) φ (Pi.single a 1)| ≤
      (rows.map fun e => |rowCoef E N e| * (∏ j, hi j ^ rowExp e j) *
        ((|((rowMode e).1 : ℝ)| + |((rowMode e).2 : ℝ)|) * tailSum (GT (mdeg (rowExp e))) L +
          ∑ i, β i * tailSum (Function.update (GT (mdeg (rowExp e))) i
            (GTP (mdeg (rowExp e)) i)) L)).sum) := by
  have hb : ∀ j, bmin j ≤ bmax j := fun j => (h1 j 0).trans (h2 j 0)
  have hβ0 : ∀ j, 0 ≤ β j := fun j => (abs_nonneg _).trans (hβ j 0 0)
  have hbmax0 : ∀ j, 0 ≤ bmax j := fun j => by linarith [hr j, hb j]
  -- the `T_n` bounds
  set τ : (Fin 3 → ℕ) → ℝ := fun n =>
    ((rows.filter fun e => decide (rowExp e = n)).map fun e => |rowCoef E N e|).sum with hτdef
  set τ' : (Fin 3 → ℕ) → ℝ := fun n => ((rows.filter fun e => decide (rowExp e = n)).map fun e =>
      |rowCoef E N e| * (|((rowMode e).1 : ℝ)| + |((rowMode e).2 : ℝ)|)).sum with hτ'def
  have hτ : ∀ n φ, |Tn E N rows n φ| ≤ τ n := fun n φ => abs_Tn_le E N rows n φ
  have hτ' : ∀ n φ a, |fderiv ℝ (Tn E N rows n) φ (Pi.single a 1)| ≤ τ' n := by
    intro n φ a
    refine (abs_pderiv_Tn_le E N rows n φ a).trans (list_sum_mono _ _ _ fun e _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    fin_cases a <;> simp [abs_nonneg]
  have hτ0 : ∀ n, 0 ≤ τ n := fun n => list_sum_nonneg' _ _ fun _ _ => abs_nonneg _
  have hτ'0 : ∀ n, 0 ≤ τ' n := fun n => list_sum_nonneg' _ _ fun _ _ => by positivity
  obtain ⟨-, -, hU, -, hP⟩ := hRem_tube E N rows B L hBd hr h1 h2 hβ hτ hτ' φ u hu
  -- the per-exponent factored bounds
  have hexp : ∀ n ∈ expSet rows, mdeg n ≤ 18 := by
    intro n hn
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hn)
    exact hdeg e he
  have hcoef : ∀ n, mdeg n ≤ 18 → (∏ j, bmax j ^ halfExp n j) ≤ ∏ j, hi j ^ n j := fun n _ =>
    Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg (hbmax0 j) _)
      fun j _ => rpow_half_le_pow (hbmax0 j) (hhi j).1 (hhi j).2 (n j)
  -- tables are nonnegative on the relevant `K`
  have hT0 : ∀ n, mdeg n ≤ 18 → ∀ j m, m < L + 2 → 0 ≤ GT (mdeg n) j m := fun n hn j m hm =>
    (slotHat_nonneg hr0 (hr j) (hb j) m).trans (hGT _ hn 0 (Nat.zero_le _) j m hm)
  have hTD0 : ∀ n, mdeg n ≤ 18 → ∀ j m, m < L + 2 → 0 ≤ GTD (mdeg n) j m := fun n hn j m hm =>
    (slotHatDu_nonneg hr0 (hr j) (hb j) m).trans (hGTD _ hn 0 (Nat.zero_le _) j m hm)
  have hTP0 : ∀ n, mdeg n ≤ 18 → ∀ j m, m < L + 2 → 0 ≤ GTP (mdeg n) j m := fun n hn j m hm =>
    (slotHatP_nonneg hr0 (hr j) (hb j) m).trans (hGTP _ hn 0 (Nat.zero_le _) j m hm)
  have hslot : ∀ n, mdeg n ≤ 18 → ∀ j m, m < L + 2 →
      boxMaj (halfExp n) L bmin bmax r j m ≤ bmax j ^ halfExp n j * GT (mdeg n) j m := by
    intro n hn j m hm
    refine (slotMaj_le_hat hr0 (hr j) (hb j) (halfExp_nonneg n j) (halfExp_le_nine hn j) m).trans ?_
    exact mul_le_mul_of_nonneg_left (hGT _ hn (n j) (le_mdeg n j) j m hm)
      (Real.rpow_nonneg (hbmax0 j) _)
  have hbox0 : ∀ n j m, m < L + 2 → 0 ≤ boxMaj (halfExp n) L bmin bmax r j m :=
    fun n j m _ => slotMaj_nonneg hr0 (hr j) m
  have hrem0 : ∀ n, mdeg n ≤ 18 →
      remBound₀ (halfExp n) L bmin bmax r ≤ (∏ j, hi j ^ n j) * tailSum (GT (mdeg n)) L := by
    intro n hn
    refine (tailSum_mono (hbox0 n) (G' := fun j m => bmax j ^ halfExp n j * GT (mdeg n) j m)
      (hslot n hn)).trans ?_
    rw [tailSum_mul_slots]
    exact mul_le_mul_of_nonneg_right (hcoef n hn) (tailSum_nonneg (hT0 n hn))
  have hremU : ∀ n, mdeg n ≤ 18 → ∀ i, remBoundU (halfExp n) L bmin bmax r i ≤
      (∏ j, hi j ^ n j) * tailSum (Function.update (GT (mdeg n)) i (GTD (mdeg n) i)) L := by
    intro n hn i
    have hle : ∀ j m, m < L + 2 →
        Function.update (boxMaj (halfExp n) L bmin bmax r) i
          (slotMajDu (halfExp n i) L (bmin i) (bmax i) r) j m ≤
        Function.update (fun j m => bmax j ^ halfExp n j * GT (mdeg n) j m) i
          (fun m => bmax i ^ halfExp n i * GTD (mdeg n) i m) j m := by
      intro j m hm
      by_cases h : j = i
      · subst h
        simp only [Function.update_self]
        refine (slotMajDu_le_hat hr0 (hr j) (hb j) (halfExp_nonneg n j)
          (halfExp_le_nine hn j) m).trans ?_
        exact mul_le_mul_of_nonneg_left (hGTD _ hn (n j) (le_mdeg n j) j m hm)
          (Real.rpow_nonneg (hbmax0 j) _)
      · simp only [Function.update_of_ne h]; exact hslot n hn j m hm
    have hle0 : ∀ j m, m < L + 2 → 0 ≤ Function.update (boxMaj (halfExp n) L bmin bmax r) i
        (slotMajDu (halfExp n i) L (bmin i) (bmax i) r) j m := by
      intro j m _
      by_cases h : j = i
      · subst h; simp only [Function.update_self]; exact slotMajDu_nonneg hr0 (hr j) m
      · simp only [Function.update_of_ne h]; exact slotMaj_nonneg hr0 (hr j) m
    refine (tailSum_mono hle0 hle).trans ?_
    rw [tailSum_update_mul_slots]
    refine mul_le_mul_of_nonneg_right (hcoef n hn) (tailSum_nonneg fun j m hm => ?_)
    by_cases h : j = i
    · subst h; simp only [Function.update_self]; exact hTD0 n hn j m hm
    · simp only [Function.update_of_ne h]; exact hT0 n hn j m hm
  have hremP : ∀ n, mdeg n ≤ 18 → remBoundPhi (halfExp n) L bmin bmax r β ≤
      (∏ j, hi j ^ n j) *
        ∑ i, β i * tailSum (Function.update (GT (mdeg n)) i (GTP (mdeg n) i)) L := by
    intro n hn
    rw [remBoundPhi, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ (hβ0 i)
    have hle : ∀ j m, m < L + 2 →
        Function.update (boxMaj (halfExp n) L bmin bmax r) i
          (fun m => |halfExp n i| * slotMaj (halfExp n i - 1) L (bmin i) (bmax i) r m) j m ≤
        Function.update (fun j m => bmax j ^ halfExp n j * GT (mdeg n) j m) i
          (fun m => bmax i ^ halfExp n i * GTP (mdeg n) i m) j m := by
      intro j m hm
      by_cases h : j = i
      · subst h
        simp only [Function.update_self]
        refine (slotMajP_le_hat hr0 (hr j) (hb j) (halfExp_nonneg n j)
          (halfExp_le_nine hn j) m).trans ?_
        exact mul_le_mul_of_nonneg_left (hGTP _ hn (n j) (le_mdeg n j) j m hm)
          (Real.rpow_nonneg (hbmax0 j) _)
      · simp only [Function.update_of_ne h]; exact hslot n hn j m hm
    have hle0 : ∀ j m, m < L + 2 → 0 ≤ Function.update (boxMaj (halfExp n) L bmin bmax r) i
        (fun m => |halfExp n i| * slotMaj (halfExp n i - 1) L (bmin i) (bmax i) r m) j m := by
      intro j m _
      by_cases h : j = i
      · subst h; simp only [Function.update_self]
        exact mul_nonneg (abs_nonneg _) (slotMaj_nonneg hr0 (hr j) m)
      · simp only [Function.update_of_ne h]; exact slotMaj_nonneg hr0 (hr j) m
    refine (tailSum_mono hle0 hle).trans ?_
    rw [tailSum_update_mul_slots]
    refine mul_le_mul_of_nonneg_right (hcoef n hn) (tailSum_nonneg fun j m hm => ?_)
    by_cases h : j = i
    · subst h; simp only [Function.update_self]; exact hTP0 n hn j m hm
    · simp only [Function.update_of_ne h]; exact hT0 n hn j m hm
  refine ⟨fun i => (hU i).trans ?_, fun a => (hP a).trans ?_⟩
  · -- `u`-partials
    calc ∑ n ∈ expSet rows, τ n * remBoundU (halfExp n) L bmin bmax r i
        ≤ ∑ n ∈ expSet rows, τ n * ((∏ j, hi j ^ n j) *
            tailSum (Function.update (GT (mdeg n)) i (GTD (mdeg n) i)) L) :=
          Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hremU n (hexp n hn) i) (hτ0 n)
      _ = (rows.map fun e => |rowCoef E N e| * ((∏ j, hi j ^ rowExp e j) *
            tailSum (Function.update (GT (mdeg (rowExp e))) i (GTD (mdeg (rowExp e)) i)) L)).sum :=
          sum_expSet_eq_rows E N rows _
      _ = _ := congrArg List.sum (List.map_congr_left fun e _ => by ring)
  · -- `φ`-partials
    calc ∑ n ∈ expSet rows, (τ' n * remBound₀ (halfExp n) L bmin bmax r +
          τ n * remBoundPhi (halfExp n) L bmin bmax r β)
        ≤ ∑ n ∈ expSet rows, (τ' n * ((∏ j, hi j ^ n j) * tailSum (GT (mdeg n)) L) +
            τ n * ((∏ j, hi j ^ n j) *
              ∑ i, β i * tailSum (Function.update (GT (mdeg n)) i (GTP (mdeg n) i)) L)) :=
          Finset.sum_le_sum fun n hn => add_le_add
            (mul_le_mul_of_nonneg_left (hrem0 n (hexp n hn)) (hτ'0 n))
            (mul_le_mul_of_nonneg_left (hremP n (hexp n hn)) (hτ0 n))
      _ = (rows.map fun e => |rowCoef E N e| *
              (|((rowMode e).1 : ℝ)| + |((rowMode e).2 : ℝ)|) *
            ((∏ j, hi j ^ rowExp e j) * tailSum (GT (mdeg (rowExp e))) L)).sum +
          (rows.map fun e => |rowCoef E N e| * ((∏ j, hi j ^ rowExp e j) *
            ∑ i, β i * tailSum (Function.update (GT (mdeg (rowExp e))) i
              (GTP (mdeg (rowExp e)) i)) L)).sum := by
          rw [Finset.sum_add_distrib]
          exact congrArg₂ (· + ·) (sum_expSet_eq_rows' E N rows _) (sum_expSet_eq_rows E N rows _)
      _ = _ := by
          rw [← List.sum_map_add]
          exact congrArg List.sum (List.map_congr_left fun e _ => by ring)

end KAM.EffectiveStability.Tube

end
