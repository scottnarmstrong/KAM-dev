/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.OscillatorFiniteSetup
public import KAM.Planetary.Averaging.FiniteMulti

/-!
# P Part 2: the `N`-step loss budget of oscillator averaging, combinatorics
(`stepP:p2:oa-iter`)

The schedule of Case A for the four radii (`multiOSched`, built from `multiSched`), the remainder
bounds `ε₀ = E`, `εᵢ = c₁ 4^{1-i}`, the weights `oscW` of the star norm (at most `1/3` for the later
stages and at most `3/(4N)` for the first one) and the geometric sums for the displacements.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, Revision 3, package P23-15.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- The Case A schedule for the four radii. -/
def multiOSched (r rp rq S s N : ℝ) : OSched :=
  ⟨multiSched r S s N, multiSched rp S s N, multiSched rq S s N⟩

/-- The weights of the star norm of stage `i` at stage `j`. -/
def oscW (c : OSched) (i j : ℕ) : ℝ :=
  max (max (c.x.ρ i / (c.x.R j - c.x.R i + c.x.ρ i)) (c.x.σ i / (c.x.S j - c.x.S i + c.x.σ i)))
    (max (c.p.ρ i / (c.p.R j - c.p.R i + c.p.ρ i)) (c.q.ρ i / (c.q.R j - c.q.R i + c.q.ρ i)))

/-- The remainder bounds of Case A: `ε₀ = E`, `εᵢ = c₁ (1/4)^{i-1}` for `i ≥ 1`. -/
def oEps (E c₁ : ℝ) (i : ℕ) : ℝ := if i = 0 then E else c₁ * (1 / 4) ^ (i - 1)

section Eps

theorem oEps_zero (E c₁ : ℝ) : oEps E c₁ 0 = E := by simp [oEps]

theorem oEps_succ (E c₁ : ℝ) (l : ℕ) : oEps E c₁ (l + 1) = c₁ * (1 / 4) ^ l := by simp [oEps]

theorem oEps_nonneg {E c₁ : ℝ} (hE : 0 ≤ E) (hc : 0 ≤ c₁) (i : ℕ) : 0 ≤ oEps E c₁ i := by
  rcases i with _ | l
  · rw [oEps_zero]; exact hE
  · rw [oEps_succ]; positivity

theorem oEps_tail_sum {E c₁ : ℝ} (hc : 0 ≤ c₁) (n : ℕ) :
    ∑ i ∈ Finset.range n, oEps E c₁ (i + 1) ≤ 4 / 3 * c₁ := by
  have : ∑ i ∈ Finset.range n, oEps E c₁ (i + 1) = c₁ * ∑ i ∈ Finset.range n, (1 / 4 : ℝ) ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => oEps_succ E c₁ i
  rw [this]
  have := geom_quarter n
  nlinarith

theorem oEps_n {E c₁ κ : ℝ} {n : ℕ} (hκ : 0 < κ) (hE : 0 ≤ E) (hc : c₁ ≤ 293 * E / (4096 * κ))
    (hnκ : 8 * (n : ℝ) ≤ κ) : (n : ℝ) * c₁ ≤ E / 100 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (n : ℝ) * c₁ ≤ n * (293 * E / (4096 * κ)) := mul_le_mul_of_nonneg_left hc hn
    _ = 293 * E * n / (4096 * κ) := by ring
    _ ≤ E / 100 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_nonneg hE hn]

variable {a s E c₁ κ : ℝ} {n : ℕ}

/-- The action-displacement sum: `a s ∑ ε_i/(e a σ_i) ≤ 3E`. -/
theorem oEps_disp_σ (ha : 0 < a) (hs : 0 < s) (hn : 1 ≤ n) (hE : 0 ≤ E) (hc : 0 ≤ c₁)
    (hnc : (n : ℝ) * c₁ ≤ E / 100) (r S : ℝ) :
    a * s * ∑ i ∈ Finset.range (n + 1),
      oEps E c₁ i / (exp 1 * a * (multiSched r S s n).σ i) ≤ 3 * E := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Finset.sum_range_succ']
  simp only [multi_σ_zero, multi_σ_succ, oEps_zero]
  have hT := oEps_tail_sum (E := E) hc n
  have hsum : ∑ i ∈ Finset.range n, oEps E c₁ (i + 1) / (exp 1 * a * (s / (4 * n))) =
      (∑ i ∈ Finset.range n, oEps E c₁ (i + 1)) / (exp 1 * a * (s / (4 * n))) := by
    rw [Finset.sum_div]
  rw [hsum]
  set T := ∑ i ∈ Finset.range n, oEps E c₁ (i + 1)
  have key : a * s * (T / (exp 1 * a * (s / (4 * n))) + E / (exp 1 * a * (s / 6))) =
      (4 * n * T + 6 * E) / exp 1 := by field_simp
  rw [key]
  have he := exp_one_gt_27
  rw [div_le_iff₀ (by linarith)]
  have : 4 * (n : ℝ) * T ≤ 4 * n * (4 / 3 * c₁) :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  nlinarith

/-- The angle-displacement sum: `a r ∑ ε_i/(a ρ_i) ≤ 9E`. -/
theorem oEps_disp_ρ {r : ℝ} (ha : 0 < a) (hr : 0 < r) (hn : 1 ≤ n) (hE : 0 ≤ E)
    (hc : 0 ≤ c₁) (hnc : (n : ℝ) * c₁ ≤ E / 100) (S : ℝ) :
    a * r * ∑ i ∈ Finset.range (n + 1),
      oEps E c₁ i / (a * (multiSched r S s n).ρ i) ≤ 9 * E := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Finset.sum_range_succ']
  simp only [multi_ρ_zero, multi_ρ_succ, oEps_zero]
  have hT := oEps_tail_sum (E := E) hc n
  have hsum : ∑ i ∈ Finset.range n, oEps E c₁ (i + 1) / (a * (r / (8 * n))) =
      (∑ i ∈ Finset.range n, oEps E c₁ (i + 1)) / (a * (r / (8 * n))) := by
    rw [Finset.sum_div]
  rw [hsum]
  set T := ∑ i ∈ Finset.range n, oEps E c₁ (i + 1)
  have key : a * r * (T / (a * (r / (8 * n))) + E / (a * (r / 8))) = 8 * n * T + 8 * E := by
    field_simp
  rw [key]
  have : 8 * (n : ℝ) * T ≤ 8 * n * (4 / 3 * c₁) :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  nlinarith

end Eps

section Gaps

variable {a S s N : ℝ}

theorem multi_R_gap (hN : 0 < N) (ha : 0 < a) {l j : ℕ} (hj : j < l) :
    3 * (multiSched a S s N).ρ (l + 1) ≤
      (multiSched a S s N).R (j + 1) - (multiSched a S s N).R (l + 1) +
        (multiSched a S s N).ρ (l + 1) := by
  have hjl : (j : ℝ) + 1 ≤ l := by exact_mod_cast hj
  rw [multi_ρ_succ, multi_R_closed, multi_R_closed]
  have : (0 : ℝ) ≤ a / (8 * N) := by positivity
  nlinarith

theorem multi_S_gap (hN : 0 < N) (hs : 0 < s) {l j : ℕ} (hj : j < l) :
    3 * (multiSched a S s N).σ (l + 1) ≤
      (multiSched a S s N).S (j + 1) - (multiSched a S s N).S (l + 1) +
        (multiSched a S s N).σ (l + 1) := by
  have hjl : (j : ℝ) + 1 ≤ l := by exact_mod_cast hj
  rw [multi_σ_succ, multi_S_closed, multi_S_closed]
  have : (0 : ℝ) ≤ s / (4 * N) := by positivity
  nlinarith

theorem multi_R_head (hN : 0 < N) (ha : 0 < a) (l : ℕ) :
    a / 4 ≤ (multiSched a S s N).R 0 - (multiSched a S s N).R (l + 1) +
      (multiSched a S s N).ρ (l + 1) := by
  rw [multi_ρ_succ, multi_R_closed, multi_R_zero]
  have : 0 ≤ 2 * (l : ℝ) * (a / (8 * N)) := by positivity
  have : 0 ≤ a / (8 * N) := by positivity
  linarith

theorem multi_S_head (hN : 0 < N) (hs : 0 < s) (l : ℕ) :
    s / 3 ≤ (multiSched a S s N).S 0 - (multiSched a S s N).S (l + 1) +
      (multiSched a S s N).σ (l + 1) := by
  rw [multi_σ_succ, multi_S_closed, multi_S_zero]
  have : 0 ≤ 2 * (l : ℝ) * (s / (4 * N)) := by positivity
  have : 0 ≤ s / (4 * N) := by positivity
  linarith

theorem ratio_tail {ρ x : ℝ} (hρ : 0 < ρ) (hx : 3 * ρ ≤ x) : 0 ≤ ρ / x ∧ ρ / x ≤ 1 / 3 := by
  have hx0 : 0 < x := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hx0]; linarith

theorem ratio_head {ρ x A B : ℝ} (hρ : 0 < ρ) (hA : 0 < A) (hx : A ≤ x) (hAB : ρ / A ≤ B) :
    0 ≤ ρ / x ∧ ρ / x ≤ B := by
  have hx0 : 0 < x := lt_of_lt_of_le hA hx
  exact ⟨by positivity, (div_le_div_of_nonneg_left hρ.le hA hx).trans hAB⟩

end Gaps

section Weights

variable {r rp rq S s N E c₁ : ℝ}

theorem oscW_tail (hr : 0 < r) (hrp : 0 < rp) (hrq : 0 < rq) (hs : 0 < s) (hN : 0 < N)
    {l j : ℕ} (hj : j < l) :
    0 ≤ oscW (multiOSched r rp rq S s N) (l + 1) (j + 1) ∧
      oscW (multiOSched r rp rq S s N) (l + 1) (j + 1) ≤ 1 / 3 := by
  have h1 := ratio_tail (by rw [multi_ρ_succ]; positivity) (multi_R_gap (S := S) (s := s) hN hr hj)
  have h2 := ratio_tail (by rw [multi_σ_succ]; positivity) (multi_S_gap (a := r) (S := S) hN hs hj)
  have h3 := ratio_tail (by rw [multi_ρ_succ]; positivity)
    (multi_R_gap (S := S) (s := s) hN hrp hj)
  have h4 := ratio_tail (by rw [multi_ρ_succ]; positivity)
    (multi_R_gap (S := S) (s := s) hN hrq hj)
  unfold oscW multiOSched
  exact ⟨le_max_of_le_left (le_max_of_le_left h1.1),
    max_le (max_le h1.2 h2.2) (max_le h3.2 h4.2)⟩

theorem oscW_head (hr : 0 < r) (hrp : 0 < rp) (hrq : 0 < rq) (hs : 0 < s) (hN : 0 < N) (l : ℕ) :
    0 ≤ oscW (multiOSched r rp rq S s N) (l + 1) 0 ∧
      oscW (multiOSched r rp rq S s N) (l + 1) 0 ≤ 3 / (4 * N) := by
  have hρ : ∀ a : ℝ, 0 < a → (multiSched a S s N).ρ (l + 1) / (a / 4) = 1 / (2 * N) := by
    intro a ha; rw [multi_ρ_succ]; field_simp; ring
  have hle : 1 / (2 * N) ≤ 3 / (4 * N) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h1 := ratio_head (by rw [multi_ρ_succ]; positivity) (by positivity : 0 < r / 4)
    (multi_R_head (S := S) (s := s) hN hr l) ((hρ r hr).le.trans hle)
  have hσ : 0 < (multiSched r S s N).σ (l + 1) := by rw [multi_σ_succ]; positivity
  have h2 := ratio_head (B := 3 / (4 * N)) hσ (by positivity : 0 < s / 3)
    (multi_S_head (a := r) (S := S) hN hs l)
    (by rw [multi_σ_succ]; apply le_of_eq; field_simp)
  have h3 := ratio_head (by rw [multi_ρ_succ]; positivity) (by positivity : 0 < rp / 4)
    (multi_R_head (S := S) (s := s) hN hrp l) ((hρ rp hrp).le.trans hle)
  have h4 := ratio_head (by rw [multi_ρ_succ]; positivity) (by positivity : 0 < rq / 4)
    (multi_R_head (S := S) (s := s) hN hrq l) ((hρ rq hrq).le.trans hle)
  unfold oscW multiOSched
  exact ⟨le_max_of_le_left (le_max_of_le_left h1.1),
    max_le (max_le h1.2 h2.2) (max_le h3.2 h4.2)⟩

/-- The star norm of stage `l + 1` is at most `3E/(4N) + 4c₁/9`. -/
theorem multi_rsum (hr : 0 < r) (hrp : 0 < rp) (hrq : 0 < rq) (hs : 0 < s) (hN : 0 < N)
    (hE : 0 ≤ E) (hc : 0 ≤ c₁) (l : ℕ) :
    0 ≤ ∑ j : Fin (l + 1), oscW (multiOSched r rp rq S s N) (l + 1) j * oEps E c₁ j ∧
    ∑ j : Fin (l + 1), oscW (multiOSched r rp rq S s N) (l + 1) j * oEps E c₁ j ≤
      3 * E / (4 * N) + 4 * c₁ / 9 := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j => oscW (multiOSched r rp rq S s N) (l + 1) j * oEps E c₁ j) (l + 1),
    Finset.sum_range_succ']
  have htail : ∀ j ∈ Finset.range l,
      0 ≤ oscW (multiOSched r rp rq S s N) (l + 1) (j + 1) * oEps E c₁ (j + 1) ∧
      oscW (multiOSched r rp rq S s N) (l + 1) (j + 1) * oEps E c₁ (j + 1) ≤
        (1 / 3) * (c₁ * (1 / 4) ^ j) := by
    intro j hj
    obtain ⟨w0, w1⟩ := oscW_tail (S := S) hr hrp hrq hs hN (Finset.mem_range.1 hj)
    have e0 := oEps_nonneg hE hc (j + 1)
    rw [oEps_succ] at e0 ⊢
    exact ⟨mul_nonneg w0 e0, mul_le_mul w1 le_rfl e0 (by norm_num)⟩
  obtain ⟨w0, w1⟩ := oscW_head (S := S) hr hrp hrq hs hN l
  have hhead : 0 ≤ oscW (multiOSched r rp rq S s N) (l + 1) 0 * oEps E c₁ 0 ∧
      oscW (multiOSched r rp rq S s N) (l + 1) 0 * oEps E c₁ 0 ≤ 3 * E / (4 * N) := by
    rw [oEps_zero]
    refine ⟨mul_nonneg w0 hE, (mul_le_mul_of_nonneg_right w1 hE).trans (le_of_eq ?_)⟩
    ring
  refine ⟨add_nonneg (Finset.sum_nonneg fun j hj => (htail j hj).1) hhead.1, ?_⟩
  have hsum := Finset.sum_le_sum fun j hj => (htail j hj).2
  have hg : ∑ j ∈ Finset.range l, (1 / 3) * (c₁ * (1 / 4) ^ j) ≤ (1 / 3) * c₁ * (4 / 3) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have := geom_quarter l
    have h0 : 0 ≤ (1 / 3) * c₁ := by positivity
    nlinarith
  have : (1 / 3) * c₁ * (4 / 3) = 4 * c₁ / 9 := by ring
  linarith [hhead.2]

end Weights

end KAM.Planetary

end
