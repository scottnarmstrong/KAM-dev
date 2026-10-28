/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Canonical.Adjoint
public import KAM.Planetary.Averaging.OscillatorBracket
public import KAM.Planetary.Averaging.OscillatorSeriesAlgebra
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# P Parts 2-3: the oscillator adjoint estimate (`stepP:p2:oi-ratio`)

`oscLieRatio`, `oscTheta`, `osc_ratio_range` and `osc_adjoint_bound`: for `h ≥ 1` the `h`-fold
iterated bracket `ad_φ^h u` is estimated by `h` applications of `osc_bracket`, each with the
losses `(ρ, ρp, ρq, σ)/h` and the generator on its original (outer) domain. At step `i` all four
outer-to-inner ratios are at most `1/(h+1+i)` and the minimum product is `d/h²`, so the step
constant is at most `c_m h² Φ / (d (h+1+i))` with `c_m = 2 (1/e + m)`. The product of the step
constants is `(c_m h² Φ/d)^h h!/(2h)!`, and `(2h)! ≥ (2h/e)^(2h)` gives
`|ad_φ^h u / h!| ≤ q^h A` with `q = e (1 + e m) Φ / (2 d)`. The case `h = 0` is a restriction.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md` (Revision 3), package P23-13c.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real Finset

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

def oscLieRatio (m : ℕ) (Φ d : ℝ) : ℝ := exp 1 * (1 + exp 1 * m) * Φ / (2 * d)
def oscTheta (m : ℕ) (Φ d : ℝ) : ℝ := 2 * exp 1 * (1 + (m : ℝ)) * Φ / d

theorem osc_ratio_range (m : ℕ) {Φ d : ℝ} (hd : 0 < d) (hΦ : 0 ≤ Φ)
    (hs : Φ ≤ d / (16 * (1 + (m : ℝ)))) :
    0 ≤ oscLieRatio m Φ d ∧ oscLieRatio m Φ d ≤ oscTheta m Φ d ∧
    oscTheta m Φ d ≤ exp 1 / 8 ∧
    (16 / 9 : ℝ) * oscTheta m Φ d < 1 ∧ Φ / d ≤ 1 / 4 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have he : 0 < exp 1 := exp_pos 1
  have he4 : exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hb : (0 : ℝ) < 1 + m := by positivity
  set x : ℝ := Φ / d with hx
  have hx0 : 0 ≤ x := div_nonneg hΦ hd.le
  have hxb : x * (16 * (1 + (m : ℝ))) ≤ 1 := by
    rw [hx, div_mul_eq_mul_div, div_le_one hd]
    rwa [le_div_iff₀ (by positivity)] at hs
  have hL : oscLieRatio m Φ d = exp 1 * (1 + exp 1 * m) * x / 2 := by
    unfold oscLieRatio; rw [hx]; field_simp
  have hT : oscTheta m Φ d = 2 * exp 1 * (1 + (m : ℝ)) * x := by
    unfold oscTheta; rw [hx]; field_simp
  rw [hL, hT]
  have hem : exp 1 * m ≤ 4 * m := by nlinarith
  refine ⟨by positivity, ?_, ?_, ?_, ?_⟩
  · have : exp 1 * (1 + exp 1 * m) / 2 ≤ 2 * exp 1 * (1 + (m : ℝ)) := by nlinarith
    calc exp 1 * (1 + exp 1 * m) * x / 2 = exp 1 * (1 + exp 1 * m) / 2 * x := by ring
      _ ≤ 2 * exp 1 * (1 + (m : ℝ)) * x := mul_le_mul_of_nonneg_right this hx0
  · have h8 : 2 * exp 1 * (1 + (m : ℝ)) * x ≤ exp 1 / 8 := by
      nlinarith [mul_nonneg he.le (sub_nonneg.2 hxb)]
    exact h8
  · have h8 : 2 * exp 1 * (1 + (m : ℝ)) * x ≤ exp 1 / 8 := by
      nlinarith [mul_nonneg he.le (sub_nonneg.2 hxb)]
    nlinarith
  · nlinarith [mul_nonneg hx0 hm]

section Adjoint

variable {n m : ℕ} {D : Set (Fin n → ℝ)}

theorem oscBound.mono_gen {r r' rp rp' rq rq' S S' E E' : ℝ} {u : CHam (n + m)}
    (hu : oscBound D r' rp' rq' S' u E) (hr : r ≤ r') (hrp : rp ≤ rp') (hrq : rq ≤ rq')
    (hS : S ≤ S') (hE : E ≤ E') : oscBound D r rp rq S u E' := by
  intro x hx
  obtain ⟨hsum, hle⟩ := hu x (oscParams_mono hr hrp hrq hx)
  have hmono : ∀ k : Fin n → ℤ,
      ‖coeff (oscFunction u) x k‖ * modeWeight S k ≤
        ‖coeff (oscFunction u) x k‖ * modeWeight S' k := fun k =>
    mul_le_mul_of_nonneg_left (modeWeight_mono hS k) (norm_nonneg _)
  have hsum' : WSummable (oscFunction u) S x :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hmono hsum
  exact ⟨hsum', (hsum'.tsum_le_tsum hmono hsum).trans (hle.trans hE)⟩

theorem oscClass.const_mul {r rp rq S : ℝ} (c : ℂ) {u : CHam (n + m)}
    (hu : oscClass D r rp rq S u) : oscClass D r rp rq S (fun z => c * u z) :=
  ⟨hu.1.const_mul c, fun j z hz => by simp only [hu.2 j z hz]⟩

/-- The product of the step constants `C/(h+1+k)`. -/
theorem osc_prod_step (C : ℝ) (h : ℕ) :
    ∏ k ∈ range h, C / ((h : ℝ) + 1 + k) =
      C ^ h * ((h.factorial : ℝ) / ((2 * h).factorial : ℝ)) := by
  have hfac : (h.factorial : ℝ) * ∏ k ∈ range h, ((h : ℝ) + 1 + k) = ((2 * h).factorial : ℝ) := by
    have := Nat.factorial_mul_ascFactorial h h
    rw [Nat.ascFactorial_eq_prod_range] at this
    have h2 : (2 * h).factorial = h.factorial * ∏ k ∈ range h, (h + 1 + k) := by
      rw [two_mul]; exact this.symm
    rw [h2]; push_cast; ring_nf
  have hpos : (0 : ℝ) < ∏ k ∈ range h, ((h : ℝ) + 1 + k) :=
    prod_pos fun k _ => by positivity
  have hf0 : (0 : ℝ) < h.factorial := by exact_mod_cast h.factorial_pos
  have hdiv : (h.factorial : ℝ) / ((2 * h).factorial : ℝ) =
      1 / ∏ k ∈ range h, ((h : ℝ) + 1 + k) := by
    rw [← hfac]; field_simp
  rw [prod_div_distrib, prod_const, card_range, hdiv]
  ring

/-- One outer-to-inner ratio at step `i` of the `h`-fold bracket. -/
theorem osc_ratio_step {r r₀ ρ : ℝ} {h i : ℕ} (hρ : 0 < ρ) (hh : 1 ≤ h) (hr : r + ρ ≤ r₀) :
    ρ / h / (r₀ - (r - i * (ρ / h)) + ρ / h) ≤ 1 / ((h : ℝ) + 1 + i) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hκ : 0 < ρ / h := by positivity
  have hρh : (h : ℝ) * (ρ / h) = ρ := by field_simp
  have hA : ((h : ℝ) + 1 + i) * (ρ / h) ≤ r₀ - (r - i * (ρ / h)) + ρ / h := by nlinarith
  rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hA) (by positivity)]
  nlinarith

/-- The constant of one step is at most `c_m h² Φ/(d (h+1+i))`. -/
theorem osc_step_const_le {r₀ rp₀ rq₀ S₀ r rp rq S ρ ρp ρq σ Φ B : ℝ} {h i : ℕ}
    (hρ : 0 < ρ) (hρp : 0 < ρp) (hρq : 0 < ρq) (hσ : 0 < σ) (hh : 1 ≤ h)
    (hΦ : 0 ≤ Φ) (hB : 0 ≤ B)
    (hr : r + ρ ≤ r₀) (hrp : rp + ρp ≤ rp₀) (hrq : rq + ρq ≤ rq₀) (hS : S + σ ≤ S₀) :
    ((1 / exp 1) * (ρ / h / (r₀ - (r - i * (ρ / h)) + ρ / h) +
        σ / h / (S₀ - (S - i * (σ / h)) + σ / h)) +
      m * (ρq / h / (rq₀ - (rq - i * (ρq / h)) + ρq / h) +
        ρp / h / (rp₀ - (rp - i * (ρp / h)) + ρp / h))) /
      min (ρ / h * (σ / h)) (ρp / h * (ρq / h)) * Φ * B ≤
    (2 * (1 / exp 1 + m) * (h : ℝ) ^ 2 * Φ / (min (ρ * σ) (ρp * ρq) * ((h : ℝ) + 1 + i))) * B := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have he : 0 < exp 1 := exp_pos 1
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hd : 0 < min (ρ * σ) (ρp * ρq) := lt_min (by positivity) (by positivity)
  have hH : (0 : ℝ) < (h : ℝ) + 1 + i := by positivity
  have e1 : ρ / h * (σ / h) = ρ * σ / (h : ℝ) ^ 2 := by field_simp
  have e2 : ρp / h * (ρq / h) = ρp * ρq / (h : ℝ) ^ 2 := by field_simp
  rw [e1, e2, min_div_div_right (by positivity)]
  have r1 := osc_ratio_step (i := i) hρ hh hr
  have r2 := osc_ratio_step (i := i) hσ hh hS
  have r3 := osc_ratio_step (i := i) hρq hh hrq
  have r4 := osc_ratio_step (i := i) hρp hh hrp
  have hW : (1 / exp 1) * (ρ / h / (r₀ - (r - i * (ρ / h)) + ρ / h) +
        σ / h / (S₀ - (S - i * (σ / h)) + σ / h)) +
      m * (ρq / h / (rq₀ - (rq - i * (ρq / h)) + ρq / h) +
        ρp / h / (rp₀ - (rp - i * (ρp / h)) + ρp / h)) ≤
      2 * (1 / exp 1 + m) / ((h : ℝ) + 1 + i) := by
    have : (1 / exp 1) * (1 / ((h : ℝ) + 1 + i) + 1 / ((h : ℝ) + 1 + i)) +
        m * (1 / ((h : ℝ) + 1 + i) + 1 / ((h : ℝ) + 1 + i)) =
        2 * (1 / exp 1 + m) / ((h : ℝ) + 1 + i) := by field_simp; ring
    rw [← this]
    gcongr
  set W : ℝ := (1 / exp 1) * (ρ / h / (r₀ - (r - i * (ρ / h)) + ρ / h) +
        σ / h / (S₀ - (S - i * (σ / h)) + σ / h)) +
      m * (ρq / h / (rq₀ - (rq - i * (ρq / h)) + ρq / h) +
        ρp / h / (rp₀ - (rp - i * (ρp / h)) + ρp / h)) with hWdef
  set d : ℝ := min (ρ * σ) (ρp * ρq) with hddef
  have hnn : 0 ≤ Φ * B := mul_nonneg hΦ hB
  calc W / (d / (h : ℝ) ^ 2) * Φ * B = W * ((h : ℝ) ^ 2 / d) * (Φ * B) := by
        field_simp
    _ ≤ (2 * (1 / exp 1 + m) / ((h : ℝ) + 1 + i)) * ((h : ℝ) ^ 2 / d) * (Φ * B) := by
        gcongr
    _ = _ := by field_simp

/-- The `h`-fold induction: `ad_φ^i u` for `i ≤ h`, each step losing `(ρ, ρp, ρq, σ)/h`. -/
theorem osc_adjoint_induction {r rp rq S r₀ rp₀ rq₀ S₀ ρ ρp ρq σ Φ A : ℝ} {φ u : CHam (n + m)}
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hφ : oscClass D r₀ rp₀ rq₀ S₀ φ) (hu : oscClass D r rp rq S u)
    (hbφ : oscBound D r₀ rp₀ rq₀ S₀ φ Φ) (hbu : oscBound D r rp rq S u A)
    (hΦ : 0 ≤ Φ) (hA : 0 ≤ A)
    (hwidths : 0 < ρ ∧ ρ < r ∧ 0 < ρp ∧ ρp < rp ∧
      0 < ρq ∧ ρq < rq ∧ 0 < σ ∧ σ < S)
    (houter : r + ρ ≤ r₀ ∧ rp + ρp ≤ rp₀ ∧ rq + ρq ≤ rq₀ ∧ S + σ ≤ S₀)
    {h : ℕ} (hh : 1 ≤ h) :
    ∀ i : ℕ, i ≤ h →
      oscClass D (r - i * (ρ / h)) (rp - i * (ρp / h)) (rq - i * (ρq / h)) (S - i * (σ / h))
        (adPow φ i u) ∧
      oscBound D (r - i * (ρ / h)) (rp - i * (ρp / h)) (rq - i * (ρq / h)) (S - i * (σ / h))
        (adPow φ i u)
        ((∏ k ∈ range i, (2 * (1 / exp 1 + m) * (h : ℝ) ^ 2 * Φ /
          (min (ρ * σ) (ρp * ρq) * ((h : ℝ) + 1 + k)))) * A) := by
  obtain ⟨hρ, hρr, hρp, hρpr, hρq, hρqr, hσ, hσS⟩ := hwidths
  obtain ⟨hr, hrp, hrq, hS⟩ := houter
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hκ : 0 < ρ / h := by positivity
  have hκp : 0 < ρp / h := by positivity
  have hκq : 0 < ρq / h := by positivity
  have hl : 0 < σ / h := by positivity
  have hd : 0 < min (ρ * σ) (ρp * ρq) := lt_min (by positivity) (by positivity)
  have he : 0 < exp 1 := exp_pos 1
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hρh : (h : ℝ) * (ρ / h) = ρ := by field_simp
  have hρph : (h : ℝ) * (ρp / h) = ρp := by field_simp
  have hρqh : (h : ℝ) * (ρq / h) = ρq := by field_simp
  have hσh : (h : ℝ) * (σ / h) = σ := by field_simp
  intro i
  induction i with
  | zero => intro _; simpa [adPow] using ⟨hu, hbu⟩
  | succ i ih =>
    intro hi
    obtain ⟨hc, hb⟩ := ih (by omega)
    have hi' : ((i : ℝ) + 1) ≤ h := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hκr : ρ / h < r - i * (ρ / h) := by nlinarith
    have hκpr : ρp / h < rp - i * (ρp / h) := by nlinarith
    have hκqr : ρq / h < rq - i * (ρq / h) := by nlinarith
    have hlσ : σ / h < S - i * (σ / h) := by nlinarith
    have n1 := mul_nonneg hi0 hκ.le
    have n2 := mul_nonneg hi0 hκp.le
    have n3 := mul_nonneg hi0 hκq.le
    have n4 := mul_nonneg hi0 hl.le
    have hnn : 0 ≤ (∏ k ∈ range i, (2 * (1 / exp 1 + m) * (h : ℝ) ^ 2 * Φ /
          (min (ρ * σ) (ρp * ρq) * ((h : ℝ) + 1 + k)))) * A :=
      mul_nonneg (prod_nonneg fun k _ => by positivity) hA
    obtain ⟨hc', hb'⟩ := osc_bracket hn hm hφ hc hbφ hb ⟨hκ, hκr⟩ ⟨hκp, hκpr⟩ ⟨hκq, hκqr⟩
      ⟨hl, hlσ⟩ ⟨by linarith, by linarith, by linarith, by linarith⟩
    have hK := osc_step_const_le (m := m) (r := r) (rp := rp) (rq := rq) (S := S) (i := i)
      (B := (∏ k ∈ range i, (2 * (1 / exp 1 + m) * (h : ℝ) ^ 2 * Φ /
          (min (ρ * σ) (ρp * ρq) * ((h : ℝ) + 1 + k)))) * A) hρ hρp hρq hσ hh hΦ hnn hr hrp hrq hS
    have e1 : r - ((i + 1 : ℕ) : ℝ) * (ρ / h) = r - i * (ρ / h) - ρ / h := by push_cast; ring
    have e2 : rp - ((i + 1 : ℕ) : ℝ) * (ρp / h) = rp - i * (ρp / h) - ρp / h := by
      push_cast; ring
    have e3 : rq - ((i + 1 : ℕ) : ℝ) * (ρq / h) = rq - i * (ρq / h) - ρq / h := by
      push_cast; ring
    have e4 : S - ((i + 1 : ℕ) : ℝ) * (σ / h) = S - i * (σ / h) - σ / h := by push_cast; ring
    rw [e1, e2, e3, e4, adPow_succ_eq_neg]
    refine ⟨hc'.const_mul _, ?_⟩
    refine (osc_bound_const_mul (-1) hb').mono_gen le_rfl le_rfl le_rfl le_rfl ?_
    rw [norm_neg, norm_one, one_mul, prod_range_succ]
    refine hK.trans (le_of_eq ?_)
    ring

/-- Numerical comparison: `(1/h!) C^h h!/(2h)! ≤ q^h` for `C = c_m h² Φ/d`. -/
theorem osc_final_estimate {Φ d A : ℝ} (m : ℕ) (hΦ : 0 ≤ Φ) (hd : 0 < d) (hA : 0 ≤ A) {h : ℕ}
    (hh : 1 ≤ h) :
    ((h.factorial : ℝ))⁻¹ *
        ((2 * (1 / exp 1 + m) * (h : ℝ) ^ 2 * Φ / d) ^ h *
          ((h.factorial : ℝ) / ((2 * h).factorial : ℝ)) * A) ≤
      (oscLieRatio m Φ d) ^ h * A := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have he : 0 < exp 1 := exp_pos 1
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hf0 : (0 : ℝ) < h.factorial := by exact_mod_cast h.factorial_pos
  have hf2 : (0 : ℝ) < (2 * h).factorial := by exact_mod_cast (2 * h).factorial_pos
  set C : ℝ := 2 * (1 / exp 1 + m) * (h : ℝ) ^ 2 * Φ / d with hC
  have hC0 : 0 ≤ C := by positivity
  have h1 : ((h.factorial : ℝ))⁻¹ * (C ^ h * ((h.factorial : ℝ) / ((2 * h).factorial : ℝ)) * A) =
      C ^ h * (1 / ((2 * h).factorial : ℝ)) * A := by
    field_simp
  have h2 : oscLieRatio m Φ d = C * (exp 1 / (2 * h)) ^ 2 := by
    unfold oscLieRatio; rw [hC]; field_simp
  have h3 : 1 / ((2 * h).factorial : ℝ) ≤ (exp 1 / (2 * h)) ^ (2 * h) := by
    have := factorial_ge (2 * h)
    push_cast at this
    have h4 := one_div_le_one_div_of_le (by positivity) this
    rwa [div_pow, one_div_div, ← div_pow] at h4
  rw [h1, h2, mul_pow, ← pow_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by positivity)) hA

end Adjoint

/-- General four-loss adjoint bound; includes the 3/4-loss instance used for identification. -/
theorem osc_adjoint_bound {n m : ℕ} {D : Set (Fin n → ℝ)}
    {r rp rq S r₀ rp₀ rq₀ S₀ ρ ρp ρq σ Φ A : ℝ} {φ u : CHam (n + m)}
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hφ : oscClass D r₀ rp₀ rq₀ S₀ φ) (hu : oscClass D r rp rq S u)
    (hbφ : oscBound D r₀ rp₀ rq₀ S₀ φ Φ) (hbu : oscBound D r rp rq S u A)
    (hΦ : 0 ≤ Φ) (hA : 0 ≤ A)
    (hwidths : 0 < ρ ∧ ρ < r ∧ 0 < ρp ∧ ρp < rp ∧
      0 < ρq ∧ ρq < rq ∧ 0 < σ ∧ σ < S)
    (houter : r + ρ ≤ r₀ ∧ rp + ρp ≤ rp₀ ∧ rq + ρq ≤ rq₀ ∧ S + σ ≤ S₀)
    (j : ℕ) :
    let d := min (ρ * σ) (ρp * ρq)
    oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (adPow φ j u) ∧
    oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)
      (fun z => ((j.factorial : ℂ)⁻¹) * adPow φ j u z)
      ((oscLieRatio m Φ d) ^ j * A) := by
  intro d
  obtain ⟨hρ, hρr, hρp, hρpr, hρq, hρqr, hσ, hσS⟩ := hwidths
  obtain ⟨hr, hrp, hrq, hS⟩ := houter
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hc : oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u :=
      hu.mono (by linarith) (by linarith) (by linarith) (by linarith)
    refine ⟨by simpa [adPow] using hc, ?_⟩
    have hb : oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u A :=
      hbu.mono_gen (by linarith) (by linarith) (by linarith) (by linarith) le_rfl
    simpa [adPow] using hb
  · obtain ⟨hc, hb⟩ := osc_adjoint_induction hn hm hφ hu hbφ hbu hΦ hA
      ⟨hρ, hρr, hρp, hρpr, hρq, hρqr, hσ, hσS⟩ ⟨hr, hrp, hrq, hS⟩ hj j le_rfl
    have hh0 : (0 : ℝ) < j := by exact_mod_cast hj
    have e1 : r - (j : ℝ) * (ρ / j) = r - ρ := by field_simp
    have e2 : rp - (j : ℝ) * (ρp / j) = rp - ρp := by field_simp
    have e3 : rq - (j : ℝ) * (ρq / j) = rq - ρq := by field_simp
    have e4 : S - (j : ℝ) * (σ / j) = S - σ := by field_simp
    rw [e1, e2, e3, e4] at hc hb
    have hprod : ∏ k ∈ range j, (2 * (1 / exp 1 + m) * (j : ℝ) ^ 2 * Φ /
          (min (ρ * σ) (ρp * ρq) * ((j : ℝ) + 1 + k))) =
        ∏ k ∈ range j, ((2 * (1 / exp 1 + m) * (j : ℝ) ^ 2 * Φ / d) / ((j : ℝ) + 1 + k)) :=
      prod_congr rfl fun k _ => (div_div _ _ _).symm
    rw [hprod, osc_prod_step] at hb
    refine ⟨hc, ?_⟩
    refine (osc_bound_const_mul ((j.factorial : ℂ)⁻¹) hb).mono_gen le_rfl le_rfl le_rfl le_rfl ?_
    rw [norm_inv, Complex.norm_natCast]
    exact osc_final_estimate m hΦ hd hA hj

end KAM.Planetary

end
