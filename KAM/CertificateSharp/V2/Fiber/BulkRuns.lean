/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.Bulk
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Two more run types for the bulk walk: across a half-integer, and beside a crossing

`Fiber/Bulk.lean` bounds a run of fibres `b = σ(lo + i)`, `i₀ ≤ i ≤ i₁`, of one row on which the
nearest integer `p` is constant and `x + p` keeps one sign (`blkK`). Two kinds of runs fail that
test and cost the bisection `O(log M)` nodes each:

* **Tent runs** (`tentK`), across a half-integer: `x + p₀ ∈ (0, 1)` on the whole run, with
  `p₀ = -⌊X(i₀)/2^q⌋`. The certified distance `min(Z - Rd, 2^q - Z - Rd)` (`Z = X + p₀ 2^q`) is the
  minimum of two affine functions, so its four endpoint values bound it below on the run. Each fibre
  takes `p ∈ {p₀, p₀ - 1}`, the nearer; the weights use `pm = min(|p₀|, |p₀ - 1|)`, and the term
  `j = 0` uses `max(pm, 1)` (`tent_point`, `tentK_spec`).
* **Crossing runs** (`apK`), beside an integer crossing: `p` constant, one sign, and the certified
  distance `F(i) = sZ(i) - Rd(i)` is affine with the integer slope `d = s σ C₁ - R₁`. Every fibre
  keeps its own lower bound `F(i)/2^q`, and the run's sum is bounded in closed form:
  - `d ≥ 0` (receding: the distance grows as the weights decay), with `u = F₀ - d/2 > 0`:
    `Σ_{j<n} x^j (F₀ + jd)⁻² ≤ (1/u - x^n/(u + nd)) / (d + (1 - x)u)` (`receding_sum_le`, a
    telescoping sum), and `x^n` is bounded below by `powDownK`;
  - `d < 0` (approaching), with `e' = -d`, `F₁ > e'/2`: the weights are at most the largest, and
    `Σ_{k<n} (F₁ + k e')⁻² ≤ n / ((F₁ - e'/2)(F₁ + (n - 1/2) e'))` (`approach_sum_le`).

Both are checked from the run's endpoints only, as `blkK`. A crossing run is accepted by its
quality alone (no tolerance fallback), so a rejected one costs no value. A run's geometric weight
sum is `gsumK n ≥ 2^P Σ_{j<n} x^j` (`gsumK_ge`, from `powDownK`, at the run's own length, no
table), and `blkK_spec_gen` is `blkK_spec` at that length.
-/

@[expose] public section

namespace KAM.CertificateSharp.Fiber

open KAM KAM.Certificate KAM.CertificateSharp

/-! ### Lower bounds of powers, and the geometric sum at any length -/

/-- `⌊ab/2^P⌋`. -/
def mulDownK (P a b : ℕ) : ℕ := Nat.shiftRight (Nat.mul a b) P

/-- One step of binary powering, rounding down. -/
def sqMulDownK (e P r h : ℕ) : ℕ :=
  cond (Nat.beq r 0) (mulDownK P h h) (mulDownK P (mulDownK P h h) e)

/-- `2^P (e/2^P)^j` rounded **down**, by binary powering (`0` when the fuel runs out). -/
def powDownK (e P : ℕ) : ℕ → ℕ → ℕ
  | 0, j => cond (Nat.beq j 0) (pow2 P) 0
  | f + 1, j => cond (Nat.beq j 0) (pow2 P)
      (sqMulDownK e P (Nat.mod j 2) (powDownK e P f (Nat.div j 2)))

theorem mulDownK_le (P a b : ℕ) :
    (mulDownK P a b : ℝ) / 2 ^ P ≤ ((a : ℝ) / 2 ^ P) * ((b : ℝ) / 2 ^ P) := by
  have h2 : (0 : ℝ) < 2 ^ P := by positivity
  have hk : (mulDownK P a b) * 2 ^ P ≤ a * b := by
    show (a * b) >>> P * 2 ^ P ≤ a * b
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_mul_le_self _ _
  have hk' : ((mulDownK P a b : ℕ) : ℝ) * 2 ^ P ≤ (a : ℝ) * b := by exact_mod_cast hk
  rw [div_le_iff₀ h2]
  calc ((mulDownK P a b : ℕ) : ℝ) ≤ (a : ℝ) * b / 2 ^ P := by rw [le_div_iff₀ h2]; exact hk'
    _ = (a : ℝ) / 2 ^ P * ((b : ℝ) / 2 ^ P) * 2 ^ P := by field_simp

theorem powDownK_le (e P : ℕ) : ∀ (f j : ℕ),
    (powDownK e P f j : ℝ) / 2 ^ P ≤ ((e : ℝ) / 2 ^ P) ^ j := by
  have h2 : (0 : ℝ) < 2 ^ P := by positivity
  have hone : ((pow2 P : ℕ) : ℝ) / 2 ^ P = 1 := by rw [pow2_eq]; push_cast; exact div_self h2.ne'
  have hx0 : (0 : ℝ) ≤ (e : ℝ) / 2 ^ P := by positivity
  intro f
  induction f with
  | zero =>
    intro j
    simp only [powDownK, Bool.cond_eq_ite, Nat.beq_eq]
    split_ifs with hj
    · subst hj; rw [hone, pow_zero]
    · simp only [Nat.cast_zero, zero_div]; positivity
  | succ f ih =>
    intro j
    simp only [powDownK, Bool.cond_eq_ite, Nat.beq_eq]
    split_ifs with hj
    · subst hj; rw [hone, pow_zero]
    · set h := powDownK e P f (Nat.div j 2) with hh
      have hih : (h : ℝ) / 2 ^ P ≤ ((e : ℝ) / 2 ^ P) ^ (j / 2) := ih _
      have hh0 : (0 : ℝ) ≤ (h : ℝ) / 2 ^ P := by positivity
      have hsq : (mulDownK P h h : ℝ) / 2 ^ P ≤ ((e : ℝ) / 2 ^ P) ^ (2 * (j / 2)) := by
        refine (mulDownK_le P h h).trans ?_
        rw [pow_mul', sq]
        exact mul_le_mul hih hih hh0 (by positivity)
      unfold sqMulDownK
      simp only [Bool.cond_eq_ite, Nat.beq_eq]
      split_ifs with hr
      · have hj2 : j = 2 * (j / 2) := by
          have : j % 2 = 0 := hr
          omega
        calc (mulDownK P h h : ℝ) / 2 ^ P ≤ ((e : ℝ) / 2 ^ P) ^ (2 * (j / 2)) := hsq
          _ = _ := by rw [← hj2]
      · have hj2 : j = 2 * (j / 2) + 1 := by
          have : j % 2 ≠ 0 := hr
          omega
        refine (mulDownK_le P _ e).trans ?_
        calc (mulDownK P h h : ℝ) / 2 ^ P * ((e : ℝ) / 2 ^ P)
            ≤ ((e : ℝ) / 2 ^ P) ^ (2 * (j / 2)) * ((e : ℝ) / 2 ^ P) :=
              mul_le_mul_of_nonneg_right hsq hx0
          _ = _ := by rw [← pow_succ, ← hj2]

/-- `2^P Σ_{j<n} x^j`, `x = e/2^P < 1`, rounded up: `2^P (2^P - powDown n)/(2^P - e)`. -/
def gsumK (e P n : ℕ) : ℕ :=
  ceilDiv (Nat.mul (pow2 P) (Nat.sub (pow2 P) (powDownK e P 64 n))) (Nat.sub (pow2 P) e)

theorem gsumK_ge {e P : ℕ} (he : e < 2 ^ P) (n : ℕ) :
    ∑ j ∈ Finset.range n, ((e : ℝ) / 2 ^ P) ^ j ≤ (gsumK e P n : ℝ) / 2 ^ P := by
  have h2 : (0 : ℝ) < 2 ^ P := by positivity
  set x : ℝ := (e : ℝ) / 2 ^ P with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one h2]; exact_mod_cast he
  set pd := powDownK e P 64 n with hpd
  have hpdle : (pd : ℝ) / 2 ^ P ≤ x ^ n := powDownK_le e P 64 n
  have hpd2 : pd ≤ 2 ^ P := by
    have : (pd : ℝ) / 2 ^ P ≤ 1 := hpdle.trans (pow_le_one₀ hx0 hx1.le)
    rw [div_le_one h2] at this
    exact_mod_cast this
  have hgeom : ∑ j ∈ Finset.range n, x ^ j = (1 - x ^ n) / (1 - x) := by
    rw [geom_sum_eq hx1.ne, ← neg_div_neg_eq]; ring_nf
  have hden : (0 : ℕ) < 2 ^ P - e := by omega
  have hc := div_le_ceilDiv (2 ^ P * (2 ^ P - pd)) hden
  rw [hgeom]
  simp only [gsumK, Nat.mul_eq, Nat.sub_eq, pow2_eq]
  refine le_trans ?_ (div_le_div_of_nonneg_right hc h2.le)
  rw [Nat.cast_mul, Nat.cast_sub hpd2, Nat.cast_sub he.le]
  push_cast
  have h1x : 0 < 1 - x := by linarith
  have e1 : (1 - x) = ((2 : ℝ) ^ P - e) / 2 ^ P := by rw [hx]; field_simp
  have hD : (0 : ℝ) < (2 : ℝ) ^ P - e := by
    have : (e : ℝ) < 2 ^ P := by exact_mod_cast he
    linarith
  have hmain : (2 : ℝ) ^ P * (1 - x ^ n) ≤ (2 : ℝ) ^ P - pd := by
    have := (div_le_iff₀ h2).mp hpdle
    nlinarith
  have eL : (1 - x ^ n) / (1 - x) = (2 : ℝ) ^ P * (1 - x ^ n) / ((2 : ℝ) ^ P - e) := by
    rw [e1]; field_simp
  have eR : (2 : ℝ) ^ P * ((2 : ℝ) ^ P - pd) / ((2 : ℝ) ^ P - e) / 2 ^ P =
      ((2 : ℝ) ^ P - pd) / ((2 : ℝ) ^ P - e) := by
    field_simp
  rw [eL, eR]
  exact div_le_div_of_nonneg_right hmain hD.le

/-! ### The two closed forms -/

/-- **The receding sum**: for `0 ≤ x < 1`, `d ≥ 0` and `u = F₀ - d/2 > 0`,
`Σ_{j<n} x^j (F₀ + jd)⁻² ≤ (1/u - x^n/(u + nd)) / (d + (1 - x) u)` (telescoping). -/
theorem receding_sum_le {x d u : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (hd : 0 ≤ d) (hu : 0 < u) :
    ∀ n : ℕ, ∑ j ∈ Finset.range n, x ^ j / (u + d / 2 + j * d) ^ 2 ≤
      (1 / u - x ^ n / (u + n * d)) / (d + (1 - x) * u) := by
  have hA : 0 < d + (1 - x) * u := by nlinarith
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hv : 0 < u + n * d := by positivity
    have hv1 : 0 < u + n * d + d := by positivity
    have hw : 0 < u + d / 2 + n * d := by positivity
    have hxn : 0 ≤ x ^ n := pow_nonneg hx0 n
    have hratio : 1 ≤ (d + (1 - x) * (u + n * d)) / (d + (1 - x) * u) := by
      rw [le_div_iff₀ hA]
      nlinarith [mul_nonneg (sub_nonneg.mpr hx1.le) (mul_nonneg (Nat.cast_nonneg n) hd)]
    have hsq : (u + n * d) * (u + n * d + d) ≤ (u + d / 2 + n * d) ^ 2 := by nlinarith
    have h1 : x ^ n / (u + d / 2 + n * d) ^ 2 ≤ x ^ n / ((u + n * d) * (u + n * d + d)) :=
      div_le_div_of_nonneg_left hxn (by positivity) hsq
    have h2 : x ^ n / ((u + n * d) * (u + n * d + d)) ≤
        x ^ n / ((u + n * d) * (u + n * d + d)) *
          ((d + (1 - x) * (u + n * d)) / (d + (1 - x) * u)) :=
      le_mul_of_one_le_right (by positivity) hratio
    have e1 : x ^ n / ((u + n * d) * (u + n * d + d)) *
        ((d + (1 - x) * (u + n * d)) / (d + (1 - x) * u)) =
        (1 / u - x ^ (n + 1) / (u + ((n + 1 : ℕ) : ℝ) * d)) / (d + (1 - x) * u) -
          (1 / u - x ^ n / (u + n * d)) / (d + (1 - x) * u) := by
      push_cast
      field_simp
      ring
    linarith

/-- **The approaching sum**: for `e ≥ 0` and `v = F₁ - e/2 > 0`,
`Σ_{k<n} (F₁ + k e)⁻² ≤ n / (v (v + n e))` (telescoping, `F₁ = v + e/2`). -/
theorem approach_sum_le {e v : ℝ} (he : 0 ≤ e) (hv : 0 < v) :
    ∀ n : ℕ, ∑ k ∈ Finset.range n, 1 / (v + e / 2 + k * e) ^ 2 ≤ n / (v * (v + n * e)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : 0 < v + n * e := by positivity
    have h2 : 0 < v + n * e + e := by positivity
    have hsq : (v + n * e) * (v + n * e + e) ≤ (v + e / 2 + n * e) ^ 2 := by nlinarith
    have hstep : 1 / (v + e / 2 + n * e) ^ 2 ≤ 1 / ((v + n * e) * (v + n * e + e)) :=
      one_div_le_one_div_of_le (by positivity) hsq
    have e1 : (n : ℝ) / (v * (v + n * e)) + 1 / ((v + n * e) * (v + n * e + e)) =
        ((n + 1 : ℕ) : ℝ) / (v * (v + ((n + 1 : ℕ) : ℝ) * e)) := by
      push_cast
      field_simp
      ring
    linarith

/-! ### Plain runs at their own length -/

section Run

variable {D : DBox2} {e P : ℕ}

/-- **Soundness of the run check at the run's own length**: `blkK_spec` with the geometric bound
`Σ_{j < i₁ - i₀ + 1} x^j ≤ g/2^P` of exactly the run's length (`gsumK`), instead of a dyadic one. -/
theorem blkK_spec_gen {ω' : Fin 2 → ℝ} (hω : FreqEncloses 2 D.toBox ω') (he : e ≤ 2 ^ P)
    {g : ℕ} {acc : ℕ → ℕ → ℕ → Bool} {a sg : ℤ} {lo i0 i1 v : ℕ}
    (hg : ∑ j ∈ Finset.range (i1 - i0 + 1), ((e : ℝ) / 2 ^ P) ^ j ≤ (g : ℝ) / 2 ^ P)
    (hsg : sg = 1 ∨ sg = -1) (hi : i0 ≤ i1) (h : blkK D e P g acc a sg lo i0 i1 = some v) :
    BCov ω' ((e : ℝ) / 2 ^ P) (runSet a sg lo i0 (i1 - i0 + 1)) ((v : ℝ) / 2 ^ P) := by
  unfold blkK at h
  set p : ℤ := nearP D.q (colX D a sg lo i0) with hp
  simp only [Bool.cond_eq_ite, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
    Nat.sub_eq, pow2_eq] at h
  split at h
  case isFalse => exact absurd h (by simp)
  rename_i hc
  obtain ⟨⟨⟨⟨hsame, hlt0⟩, hlt1⟩, hup0⟩, hup1⟩ := hc
  split at h
  case isFalse => exact absurd h (by simp)
  simp only [Option.some.injEq] at h
  subst h
  rw [minN_eq]
  obtain ⟨s, hs, hs0, hs1⟩ := sameSign_spec hsame
  -- the affine functions `F = s Z - Rd`, `G = s Z + Rd` along the run
  set cZ : ℤ := a * D.C0 + sg * (lo : ℤ) * D.C1 + p * 2 ^ D.q with hcZ
  set dZ : ℤ := sg * D.C1 with hdZ
  have hZi : ∀ i : ℕ, colZ D a sg p lo i = cZ + dZ * i := fun i => by
    rw [colZ_eq]; push_cast; ring
  have hRi : ∀ i : ℕ, (colR D a lo i : ℤ) = ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ) + D.R1 * i :=
    fun i => by rw [colR_eq]; push_cast; ring
  generalize hZ0 : colZ D a sg p lo i0 = Z0 at *
  generalize hZ1 : colZ D a sg p lo i1 = Z1 at *
  generalize hR0 : colR D a lo i0 = R0 at *
  generalize hR1 : colR D a lo i1 = R1 at *
  set Λ : ℕ := min (Z0.natAbs - R0) (Z1.natAbs - R1) with hΛ
  have hΛ0 : 0 < Λ := lt_min (by omega) (by omega)
  set x : ℝ := (e : ℝ) / 2 ^ P with hx
  have hx0 : 0 ≤ x := by positivity
  have hF : ∀ i, i0 ≤ i → i ≤ i1 →
      (Λ : ℤ) ≤ s * colZ D a sg p lo i - (colR D a lo i : ℤ) := fun i h0 h1 => by
    have key := affine_ge_min (c := s * cZ - ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ))
      (d := s * dZ - D.R1) h0 h1
    have e0 : s * cZ - ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ) + (s * dZ - D.R1) * i0 =
        (Z0.natAbs : ℤ) - R0 := by
      rw [← hs0, ← hZ0, ← hR0, hZi, hRi]; ring
    have e1 : s * cZ - ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ) + (s * dZ - D.R1) * i1 =
        (Z1.natAbs : ℤ) - R1 := by
      rw [← hs1, ← hZ1, ← hR1, hZi, hRi]; ring
    rw [e0, e1] at key
    have hm : (Λ : ℤ) = min ((Z0.natAbs : ℤ) - R0) ((Z1.natAbs : ℤ) - R1) := by
      rw [hΛ, Nat.cast_min, Nat.cast_sub hlt0.le, Nat.cast_sub hlt1.le]
    rw [hm, hZi, hRi]
    linarith
  set U : ℕ := max (Z0.natAbs + R0) (Z1.natAbs + R1) with hU
  have hG : ∀ i, i0 ≤ i → i ≤ i1 →
      s * colZ D a sg p lo i + (colR D a lo i : ℤ) ≤ (U : ℤ) := fun i h0 h1 => by
    have key := affine_le_max (c := s * cZ + ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ))
      (d := s * dZ + D.R1) h0 h1
    have e0 : s * cZ + ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ) + (s * dZ + D.R1) * i0 =
        (Z0.natAbs : ℤ) + R0 := by
      rw [← hs0, ← hZ0, ← hR0, hZi, hRi]; ring
    have e1 : s * cZ + ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ) + (s * dZ + D.R1) * i1 =
        (Z1.natAbs : ℤ) + R1 := by
      rw [← hs1, ← hZ1, ← hR1, hZi, hRi]; ring
    rw [e0, e1] at key
    rw [hU, Nat.cast_max, hZi, hRi]
    push_cast at key ⊢
    linarith
  have hU2 : 2 * (U : ℤ) ≤ 2 ^ D.q := by
    have : 2 * U ≤ 2 ^ D.q := by
      rw [hU]
      rcases le_total (Z0.natAbs + R0) (Z1.natAbs + R1) with h | h
      · rw [max_eq_right h]; exact hup1
      · rw [max_eq_left h]; exact hup0
    exact_mod_cast this
  -- the facts at each mode of the run
  have hmode : ∀ j < i1 - i0 + 1,
      |Diophantine.frequencyDot ω' ![a, sg * ((lo + i0 + j : ℕ) : ℤ)] + p| ≤ 1 / 2 ∧
      (Λ : ℝ) / 2 ^ D.q ≤
        |Diophantine.frequencyDot ω' ![a, sg * ((lo + i0 + j : ℕ) : ℤ)] + p| := fun j hj => by
    have h0 : i0 ≤ i0 + j := Nat.le_add_right _ _
    have h1 : i0 + j ≤ i1 := by omega
    refine run_point hω _ hs (by exact_mod_cast hΛ0) ?_ ?_ hU2
    · have := hF (i0 + j) h0 h1
      rw [colZ_eq, colR_eq] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        natAbs_sg_mul hsg]
      rw [show lo + i0 + j = lo + (i0 + j) by omega]
      exact this
    · have := hG (i0 + j) h0 h1
      rw [colZ_eq, colR_eq] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        natAbs_sg_mul hsg]
      rw [show lo + i0 + j = lo + (i0 + j) by omega]
      exact this
  -- the cover
  have hq : (0 : ℝ) < 2 ^ D.q := by positivity
  have hinj : Set.InjOn (fun j : ℕ => (![a, sg * ((lo + i0 + j : ℕ) : ℤ)] : Fin 2 → ℤ))
      (Finset.range (i1 - i0 + 1) : Set ℕ) := fun j _ j' _ hjj => by
    have h1 := congrFun hjj 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1
    have hsg0 : sg ≠ 0 := by rcases hsg with rfl | rfl <;> norm_num
    have := mul_left_cancel₀ hsg0 h1
    omega
  refine ⟨fun _ => p, fun _ => (Λ : ℝ) / 2 ^ D.q, fun k hk => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨h1, h2⟩ := hmode j (Finset.mem_range.mp hj)
    exact ⟨h1, by positivity, h2⟩
  · rw [runSet, Finset.sum_image hinj]
    set j0 : ℕ := a.natAbs + lo + i0 with hj0
    set cP : ℝ := (if p = 0 then 0 else ((((p.natAbs : ℝ) - 1 / 2) ^ 2)⁻¹)) with hcP
    set Gs : ℝ := ∑ j ∈ Finset.range (i1 - i0 + 1), x ^ j with hGs
    have hterm : ∀ j ∈ Finset.range (i1 - i0 + 1),
        termX x ![a, sg * ((lo + i0 + j : ℕ) : ℤ)] p ((Λ : ℝ) / 2 ^ D.q) =
          x ^ j * (x ^ (j0 + p.natAbs) * ((((Λ : ℝ) / 2 ^ D.q)) ^ 2)⁻¹ +
            x ^ j0 * (cP + x * fiberConst)) := fun j _ => by
      have hm : modeNat (![a, sg * ((lo + i0 + j : ℕ) : ℤ)] : Fin 2 → ℤ) = j0 + j := by
        rw [modeNat_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          natAbs_sg_mul hsg]
        omega
      rw [termX, hm, pow_one]
      rw [show j0 + j + p.natAbs = j + (j0 + p.natAbs) by omega, pow_add, pow_add]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    have hGs : Gs ≤ (g : ℝ) / 2 ^ P := hg
    have hGs0 : 0 ≤ Gs := Finset.sum_nonneg fun j _ => pow_nonneg hx0 j
    have hpw : ∀ m : ℕ, x ^ m ≤ (powUp e P 64 m : ℝ) / 2 ^ P := fun m => powUp_ge he 64 m
    have hx1 : x ≤ (powUp e P 64 1 : ℝ) / 2 ^ P := by simpa using hpw 1
    have key := blkValK_ge (D := D) (x := x) (A := Gs * x ^ (j0 + p.natAbs))
      (B := Gs * x ^ j0) (j0 := j0) (g := g) (p := p) hΛ0 hx1
      (by rw [mul_comm]; exact mul_le_mul (hpw _) hGs hGs0 (by positivity))
      (by positivity)
      (by rw [mul_comm]; exact mul_le_mul (hpw _) hGs hGs0 (by positivity))
    have e1 : Gs * (x ^ (j0 + p.natAbs) * ((((Λ : ℝ) / 2 ^ D.q)) ^ 2)⁻¹ +
        x ^ j0 * (cP + x * fiberConst)) =
        Gs * x ^ (j0 + p.natAbs) * ((((Λ : ℝ) / 2 ^ D.q)) ^ 2)⁻¹ +
          Gs * x ^ j0 * (cP + x * fiberConst) := by ring
    rw [e1]
    exact key


/-! ### Values and sums of runs -/

/-- The first term `⌈2^P · W/2^P · 2^{2q}/Λ²⌉` of a run with weight `W/2^P` and lower bound
`Λ/2^q`. -/
def firstK (D : DBox2) (W Λ : ℕ) : ℕ := ceilDiv (Nat.mul W (pow2 (Nat.mul 2 D.q))) (Nat.mul Λ Λ)

/-- The terms `[p ≠ 0] (|p| - 1/2)⁻² + x C₀` of a run with weight sum `Ws/2^P`, `|p| ≥ pz`
(`pz = 0`: no term `j = 0`). -/
def constK (e P Ws pz : ℕ) : ℕ :=
  Nat.add (cond (Nat.beq pz 0) 0
      (ceilDiv (Nat.mul Ws 4) (Nat.mul (Nat.sub (Nat.mul 2 pz) 1) (Nat.sub (Nat.mul 2 pz) 1))))
    (ceilDiv (Nat.mul (Nat.mul Ws (powUpK e P 64 1)) 14615) (Nat.mul (pow2 P) 2000))

/-- The value of a run: weights `x^{j₀ + pw}` and `x^{j₀}` times `g/2^P`, lower bound `Λ/2^q`. -/
def valK (D : DBox2) (e P j0 g Λ pw pz : ℕ) : ℕ :=
  Nat.add (firstK D (mulUpK P (powUpK e P 64 (Nat.add j0 pw)) g) Λ)
    (constK e P (mulUpK P (powUpK e P 64 j0) g) pz)

theorem firstK_ge {A : ℝ} {W Λ : ℕ} (hΛ : 0 < Λ) (hA : A ≤ (W : ℝ) / 2 ^ P) :
    A * ((((Λ : ℝ) / 2 ^ D.q)) ^ 2)⁻¹ ≤ (firstK D W Λ : ℝ) / 2 ^ P := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hc := div_le_ceilDiv (W * 2 ^ (2 * D.q)) (Nat.mul_pos hΛ hΛ)
  simp only [firstK, Nat.mul_eq, pow2_eq]
  refine le_trans ?_ (div_le_div_of_nonneg_right hc hP.le)
  have hL : ((((Λ : ℝ) / 2 ^ D.q)) ^ 2)⁻¹ = (2 : ℝ) ^ (2 * D.q) / ((Λ : ℝ) * Λ) := by
    rw [div_pow, inv_div, pow_mul']
    ring
  rw [hL]
  calc A * ((2 : ℝ) ^ (2 * D.q) / ((Λ : ℝ) * Λ))
      ≤ (W : ℝ) / 2 ^ P * ((2 : ℝ) ^ (2 * D.q) / ((Λ : ℝ) * Λ)) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
    _ = ((W * 2 ^ (2 * D.q) : ℕ) : ℝ) / ((Λ * Λ : ℕ) : ℝ) / 2 ^ P := by
        push_cast; ring

theorem constK_ge {x B c : ℝ} {Ws pz : ℕ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ (powUp e P 64 1 : ℝ) / 2 ^ P) (hB : B ≤ (Ws : ℝ) / 2 ^ P)
    (hc0 : 0 ≤ c) (hc : c ≤ if pz = 0 then 0 else 4 / (2 * (pz : ℝ) - 1) ^ 2) :
    B * (c + x * fiberConst) ≤ (constK e P Ws pz : ℝ) / 2 ^ P := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hval : (constK e P Ws pz : ℝ) / 2 ^ P =
      ((if pz = 0 then 0 else ceilDiv (Ws * 4) ((2 * pz - 1) * (2 * pz - 1)) : ℕ) : ℝ) / 2 ^ P +
      (ceilDiv (Ws * powUp e P 64 1 * 14615) (2 ^ P * 2000) : ℝ) / 2 ^ P := by
    rw [← add_div]
    congr 1
    simp only [constK, powUpK_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, pow2_eq, Bool.cond_eq_ite,
      Nat.beq_eq]
    push_cast
    rfl
  rw [hval, mul_add]
  refine add_le_add ?_ ?_
  · split_ifs at hc ⊢ with hp0
    · have : c = 0 := le_antisymm hc hc0
      simp [this]
    · have hp1 : 1 ≤ pz := Nat.one_le_iff_ne_zero.mpr hp0
      have hpos : 0 < (2 * pz - 1) * (2 * pz - 1) := Nat.mul_pos (by omega) (by omega)
      have hcd := div_le_ceilDiv (Ws * 4) hpos
      refine le_trans ?_ (div_le_div_of_nonneg_right hcd hP.le)
      have hc2 : (((2 * pz - 1) * (2 * pz - 1) : ℕ) : ℝ) = (2 * (pz : ℝ) - 1) ^ 2 := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
      have h2p : (2 * (pz : ℝ) - 1) ≠ 0 := by
        have : (1 : ℝ) ≤ pz := by exact_mod_cast hp1
        linarith
      calc B * c ≤ (Ws : ℝ) / 2 ^ P * (4 / (2 * (pz : ℝ) - 1) ^ 2) :=
            mul_le_mul hB hc hc0 (by positivity)
        _ = (((Ws * 4 : ℕ) : ℝ) / (((2 * pz - 1) * (2 * pz - 1) : ℕ) : ℝ)) / 2 ^ P := by
            rw [hc2]; push_cast; field_simp
  · have hcd := div_le_ceilDiv (Ws * powUp e P 64 1 * 14615) (by positivity : 0 < 2 ^ P * 2000)
    refine le_trans ?_ (div_le_div_of_nonneg_right hcd hP.le)
    have hC : fiberConst ≤ 14615 / 2000 := by
      unfold fiberConst
      have := Real.pi_pos
      have := Real.pi_lt_d2
      nlinarith
    calc B * (x * fiberConst)
        ≤ (Ws : ℝ) / 2 ^ P * ((powUp e P 64 1 : ℝ) / 2 ^ P * (14615 / 2000)) :=
          mul_le_mul hB (mul_le_mul hx1 hC fiberConst_nonneg (by positivity))
            (mul_nonneg hx0 fiberConst_nonneg) (by positivity)
      _ = ((Ws * powUp e P 64 1 * 14615 : ℕ) : ℝ) / ((2 ^ P * 2000 : ℕ) : ℝ) / 2 ^ P := by
          push_cast; field_simp

/-- A run's sum through its index: the modes `(a, σ(lo + i₀ + j))`, `j < n`. -/
theorem runSet_sum {a sg : ℤ} (hsg : sg = 1 ∨ sg = -1) (lo i0 n : ℕ)
    (Fn : (Fin 2 → ℤ) → ℝ) :
    ∑ k ∈ runSet a sg lo i0 n, Fn k =
      ∑ j ∈ Finset.range n, Fn ![a, sg * ((lo + i0 + j : ℕ) : ℤ)] := by
  rw [runSet, Finset.sum_image]
  intro j _ j' _ hjj
  have := (vec_one_inj hsg hjj).2
  omega

theorem modeNat_run {a sg : ℤ} (hsg : sg = 1 ∨ sg = -1) (n : ℕ) :
    modeNat (![a, sg * (n : ℤ)] : Fin 2 → ℤ) = a.natAbs + n := by
  rw [modeNat_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    natAbs_sg_mul hsg]


/-! ### Tent runs -/

/-- One point of a tent run: if `Λ ≤ Z - Rd` and `Λ ≤ 2^q - Z - Rd` with `Z = X + p₀ 2^q`, then
the nearer of `p₀`, `p₀ - 1` has `Λ/2^q ≤ |x + p| ≤ 1/2`. -/
theorem tent_point {ω' : Fin 2 → ℝ} (hω : FreqEncloses 2 D.toBox ω') (k : Fin 2 → ℤ)
    {p0 Λ : ℤ} (hΛ : 0 < Λ)
    (hL : Λ ≤ k 0 * D.C0 + k 1 * D.C1 + p0 * 2 ^ D.q -
      (((k 0).natAbs * D.R0 + (k 1).natAbs * D.R1 : ℕ) : ℤ))
    (hU : Λ ≤ 2 ^ D.q - (k 0 * D.C0 + k 1 * D.C1 + p0 * 2 ^ D.q) -
      (((k 0).natAbs * D.R0 + (k 1).natAbs * D.R1 : ℕ) : ℤ)) :
    let p : ℤ := if Diophantine.frequencyDot ω' k + p0 ≤ 1 / 2 then p0 else p0 - 1
    |Diophantine.frequencyDot ω' k + p| ≤ 1 / 2 ∧
      (Λ : ℝ) / 2 ^ D.q ≤ |Diophantine.frequencyDot ω' k + p| := by
  intro p
  set X : ℤ := k 0 * D.C0 + k 1 * D.C1 with hX
  set R : ℕ := (k 0).natAbs * D.R0 + (k 1).natAbs * D.R1 with hR
  set y : ℝ := Diophantine.frequencyDot ω' k with hy
  have hq : (0 : ℝ) < 2 ^ D.q := by positivity
  have hd : |y - (X : ℝ) / 2 ^ D.q| ≤ (R : ℝ) / 2 ^ D.q := dot_sub_le_dbox hω k
  have hd' := abs_le.mp hd
  have hL' : (Λ : ℝ) ≤ X + p0 * 2 ^ D.q - R := by exact_mod_cast hL
  have hU' : (Λ : ℝ) ≤ 2 ^ D.q - (X + p0 * 2 ^ D.q) - R := by exact_mod_cast hU
  -- `Λ/2^q ≤ y + p₀ ≤ 1 - Λ/2^q`
  have hlo : (Λ : ℝ) / 2 ^ D.q ≤ y + p0 := by
    rw [div_le_iff₀ hq]
    have : (X : ℝ) / 2 ^ D.q - (R : ℝ) / 2 ^ D.q ≤ y := by linarith
    rw [← sub_div, div_le_iff₀ hq] at this
    nlinarith
  have hhi : y + p0 ≤ 1 - (Λ : ℝ) / 2 ^ D.q := by
    have : y ≤ (X : ℝ) / 2 ^ D.q + (R : ℝ) / 2 ^ D.q := by linarith
    rw [← add_div, le_div_iff₀ hq] at this
    rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hq]
    nlinarith
  have hΛq : (0 : ℝ) < (Λ : ℝ) / 2 ^ D.q := by
    have : (0 : ℝ) < Λ := by exact_mod_cast hΛ
    positivity
  show |y + (if y + p0 ≤ 1 / 2 then p0 else p0 - 1 : ℤ)| ≤ 1 / 2 ∧
    (Λ : ℝ) / 2 ^ D.q ≤ |y + (if y + p0 ≤ 1 / 2 then p0 else p0 - 1 : ℤ)|
  split_ifs with h
  · rw [abs_of_pos (by linarith)]
    exact ⟨h, hlo⟩
  · push_cast
    rw [abs_of_neg (by linarith)]
    constructor <;> linarith

/-- **The tent check** of `b = sg(lo + i)`, `i₀ ≤ i ≤ i₁`: `p₀ = -⌊X(i₀)/2^q⌋`,
`Λ = min(Z - Rd, 2^q - Z - Rd)` over both ends must be positive; then the value with weights
`x^{j₀ + pm}`, `pm = min(|p₀|, |p₀ - 1|)`, and the term `j = 0` at `max(pm, 1)`, if `acc` accepts
it (with the largest distance `2^{q-1}`). -/
def tentK (D : DBox2) (e P g : ℕ) (acc : ℕ → ℕ → ℕ → Bool) (a sg : ℤ) (lo i0 i1 : ℕ) :
    Option ℕ :=
  let Q : ℤ := Int.ofNat (pow2 D.q)
  let p0 : ℤ := -(colX D a sg lo i0 / Q)
  let Z0 : ℤ := colZ D a sg p0 lo i0
  let Z1 : ℤ := colZ D a sg p0 lo i1
  let R0 : ℤ := Int.ofNat (colR D a lo i0)
  let R1 : ℤ := Int.ofNat (colR D a lo i1)
  let Λ : ℕ := minN (minN (Int.toNat (Z0 - R0)) (Int.toNat (Q - Z0 - R0)))
    (minN (Int.toNat (Z1 - R1)) (Int.toNat (Q - Z1 - R1)))
  let pm : ℕ := minN (Int.natAbs p0) (Int.natAbs (p0 - 1))
  cond (Nat.blt 0 Λ)
    (let v : ℕ := valK D e P (Nat.add (Nat.add (Int.natAbs a) lo) i0) g Λ pm (maxN pm 1)
     cond (acc Λ (Nat.shiftRight (pow2 D.q) 1) v) (some v) none)
    none

/-- **Soundness of the tent check.** -/
theorem tentK_spec {ω' : Fin 2 → ℝ} (hω : FreqEncloses 2 D.toBox ω') (he : e ≤ 2 ^ P)
    {g : ℕ} {acc : ℕ → ℕ → ℕ → Bool} {a sg : ℤ} {lo i0 i1 v : ℕ}
    (hg : ∑ j ∈ Finset.range (i1 - i0 + 1), ((e : ℝ) / 2 ^ P) ^ j ≤ (g : ℝ) / 2 ^ P)
    (hsg : sg = 1 ∨ sg = -1) (hi : i0 ≤ i1) (h : tentK D e P g acc a sg lo i0 i1 = some v) :
    BCov ω' ((e : ℝ) / 2 ^ P) (runSet a sg lo i0 (i1 - i0 + 1)) ((v : ℝ) / 2 ^ P) := by
  unfold tentK at h
  simp only [Bool.cond_eq_ite, Nat.blt_eq] at h
  split at h
  case isFalse => exact absurd h (by simp)
  rename_i hΛpos
  split at h
  case isFalse => exact absurd h (by simp)
  simp only [Option.some.injEq] at h
  subst h
  set Q : ℤ := Int.ofNat (pow2 D.q) with hQ
  have hQ' : Q = 2 ^ D.q := by rw [hQ, pow2_eq]; rfl
  set p0 : ℤ := -(colX D a sg lo i0 / Q) with hp0
  set pm : ℕ := minN (Int.natAbs p0) (Int.natAbs (p0 - 1)) with hpm
  set Λ : ℕ := minN (minN (Int.toNat (colZ D a sg p0 lo i0 - Int.ofNat (colR D a lo i0)))
      (Int.toNat (Q - colZ D a sg p0 lo i0 - Int.ofNat (colR D a lo i0))))
    (minN (Int.toNat (colZ D a sg p0 lo i1 - Int.ofNat (colR D a lo i1)))
      (Int.toNat (Q - colZ D a sg p0 lo i1 - Int.ofNat (colR D a lo i1)))) with hΛ
  simp only [minN_eq, Int.ofNat_eq_natCast] at hΛ
  -- the four endpoint values bound `Λ` above
  have hle : ∀ z : ℤ, (Λ : ℤ) ≤ z.toNat → (Λ : ℤ) ≤ z := fun z hz => by
    have : 0 < Λ := hΛpos
    have : 0 < z.toNat := by omega
    rw [Int.toNat_of_nonneg (by omega)] at hz
    exact hz
  have hL0 : (Λ : ℤ) ≤ colZ D a sg p0 lo i0 - colR D a lo i0 := by
    apply hle; rw [hΛ]; push_cast; omega
  have hU0 : (Λ : ℤ) ≤ Q - colZ D a sg p0 lo i0 - colR D a lo i0 := by
    apply hle; rw [hΛ]; push_cast; omega
  have hL1 : (Λ : ℤ) ≤ colZ D a sg p0 lo i1 - colR D a lo i1 := by
    apply hle; rw [hΛ]; push_cast; omega
  have hU1 : (Λ : ℤ) ≤ Q - colZ D a sg p0 lo i1 - colR D a lo i1 := by
    apply hle; rw [hΛ]; push_cast; omega
  -- affine in `i`
  have hZi : ∀ i : ℕ, colZ D a sg p0 lo i =
      (a * D.C0 + sg * (lo : ℤ) * D.C1 + p0 * 2 ^ D.q) + sg * D.C1 * i := fun i => by
    rw [colZ_eq]; push_cast; ring
  have hRi : ∀ i : ℕ, (colR D a lo i : ℤ) = ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ) + D.R1 * i :=
    fun i => by rw [colR_eq]; push_cast; ring
  have hLi : ∀ i, i0 ≤ i → i ≤ i1 → (Λ : ℤ) ≤ colZ D a sg p0 lo i - colR D a lo i := by
    intro i h0 h1
    have key := affine_ge_min
      (c := (a * D.C0 + sg * (lo : ℤ) * D.C1 + p0 * 2 ^ D.q) -
        ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ)) (d := sg * D.C1 - D.R1) h0 h1
    rw [hZi, hRi] at hL0 hL1 ⊢
    have e0 : ∀ j : ℕ, (a * D.C0 + sg * (lo : ℤ) * D.C1 + p0 * 2 ^ D.q) -
        ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ) + (sg * D.C1 - D.R1) * j =
        (a * D.C0 + sg * (lo : ℤ) * D.C1 + p0 * 2 ^ D.q) + sg * D.C1 * j -
          (((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ) + D.R1 * j) := fun j => by ring
    rw [e0, e0, e0] at key
    exact le_trans (le_min hL0 hL1) key
  have hUi : ∀ i, i0 ≤ i → i ≤ i1 → (Λ : ℤ) ≤ Q - colZ D a sg p0 lo i - colR D a lo i := by
    intro i h0 h1
    have key := affine_ge_min
      (c := Q - (a * D.C0 + sg * (lo : ℤ) * D.C1 + p0 * 2 ^ D.q) -
        ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ)) (d := -(sg * D.C1) - D.R1) h0 h1
    rw [hZi, hRi] at hU0 hU1 ⊢
    have e0 : ∀ j : ℕ, Q - (a * D.C0 + sg * (lo : ℤ) * D.C1 + p0 * 2 ^ D.q) -
        ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ) + (-(sg * D.C1) - D.R1) * j =
        Q - ((a * D.C0 + sg * (lo : ℤ) * D.C1 + p0 * 2 ^ D.q) + sg * D.C1 * j) -
          (((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ) + D.R1 * j) := fun j => by ring
    rw [e0, e0, e0] at key
    exact le_trans (le_min hU0 hU1) key
  -- the points
  have hpt : ∀ j < i1 - i0 + 1,
      let k : Fin 2 → ℤ := ![a, sg * ((lo + i0 + j : ℕ) : ℤ)]
      let p : ℤ := if Diophantine.frequencyDot ω' k + p0 ≤ 1 / 2 then p0 else p0 - 1
      |Diophantine.frequencyDot ω' k + p| ≤ 1 / 2 ∧
        (Λ : ℝ) / 2 ^ D.q ≤ |Diophantine.frequencyDot ω' k + p| := by
    intro j hj
    have h0 : i0 ≤ i0 + j := Nat.le_add_right _ _
    have h1 : i0 + j ≤ i1 := by omega
    have hLj := hLi (i0 + j) h0 h1
    have hUj := hUi (i0 + j) h0 h1
    rw [colZ_eq, colR_eq] at hLj hUj
    rw [hQ'] at hUj
    refine tent_point hω _ (by exact_mod_cast hΛpos) ?_ ?_
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        natAbs_sg_mul hsg]
      rw [show lo + i0 + j = lo + (i0 + j) by omega]
      push_cast at hLj ⊢
      linarith
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        natAbs_sg_mul hsg]
      rw [show lo + i0 + j = lo + (i0 + j) by omega]
      push_cast at hUj ⊢
      linarith
  -- the cover
  set x : ℝ := (e : ℝ) / 2 ^ P with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one (by positivity)]; exact_mod_cast he
  set pf : (Fin 2 → ℤ) → ℤ := fun k =>
    if Diophantine.frequencyDot ω' k + p0 ≤ 1 / 2 then p0 else p0 - 1 with hpf
  have hpf_mem : ∀ k, pf k = p0 ∨ pf k = p0 - 1 := fun k => by
    simp only [hpf]; split_ifs <;> simp
  refine ⟨pf, fun _ => (Λ : ℝ) / 2 ^ D.q, fun k hk => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := mem_runSet.mp hk
    obtain ⟨h1, h2⟩ := hpt j hj
    exact ⟨h1, by have : (0 : ℝ) < Λ := by exact_mod_cast hΛpos
                  positivity, h2⟩
  rw [runSet_sum hsg]
  set j0 : ℕ := a.natAbs + lo + i0 with hj0
  set pz : ℕ := maxN pm 1 with hpz
  set cB : ℝ := if pz = 0 then 0 else 4 / (2 * (pz : ℝ) - 1) ^ 2 with hcB
  set L : ℝ := (Λ : ℝ) / 2 ^ D.q with hLdef
  set Gs : ℝ := ∑ j ∈ Finset.range (i1 - i0 + 1), x ^ j with hGs
  have hpz1 : 1 ≤ pz := by rw [hpz, maxN_eq]; exact le_max_right _ _
  have hpmpz : pm ≤ pz := by rw [hpz, maxN_eq]; exact le_max_left _ _
  have hterm : ∀ j ∈ Finset.range (i1 - i0 + 1),
      termX x ![a, sg * ((lo + i0 + j : ℕ) : ℤ)] (pf ![a, sg * ((lo + i0 + j : ℕ) : ℤ)]) L ≤
        x ^ j * (x ^ (j0 + pm) * (L ^ 2)⁻¹ + x ^ j0 * (cB + x * fiberConst)) := by
    intro j _
    set k : Fin 2 → ℤ := ![a, sg * ((lo + i0 + j : ℕ) : ℤ)]
    have hm : modeNat k = j0 + j := by
      rw [modeNat_run hsg]; omega
    have hpk : pm ≤ (pf k).natAbs := by
      rw [hpm, minN_eq]
      rcases hpf_mem k with h | h <;> rw [h]
      · exact min_le_left _ _
      · exact min_le_right _ _
    have hw : x ^ (modeNat k + (pf k).natAbs) ≤ x ^ j * x ^ (j0 + pm) := by
      rw [← pow_add, hm]
      exact pow_le_pow_of_le_one hx0 hx1 (by omega)
    have hcP : (if pf k = 0 then (0 : ℝ) else ((((pf k).natAbs : ℝ) - 1 / 2) ^ 2)⁻¹) ≤ cB := by
      have hcB' : cB = 4 / (2 * (pz : ℝ) - 1) ^ 2 := by
        rw [hcB]; simp only [show ¬ pz = 0 by omega, ↓reduceIte]
      rw [hcB']
      split_ifs with hp
      · positivity
      · have h1 : 1 ≤ (pf k).natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hp)
        have h2 : pz ≤ (pf k).natAbs := by
          rw [hpz, maxN_eq]; exact max_le hpk h1
        have h2' : (pz : ℝ) ≤ (pf k).natAbs := by exact_mod_cast h2
        have h1' : (1 : ℝ) ≤ pz := by exact_mod_cast hpz1
        rw [show (4 : ℝ) / (2 * (pz : ℝ) - 1) ^ 2 = (((pz : ℝ) - 1 / 2) ^ 2)⁻¹ by
          field_simp; ring]
        exact inv_anti₀ (by nlinarith) (by nlinarith)
    have hcP0 : (0 : ℝ) ≤
        (if pf k = 0 then (0 : ℝ) else ((((pf k).natAbs : ℝ) - 1 / 2) ^ 2)⁻¹) := by
      split_ifs <;> positivity
    unfold termX
    rw [hm, pow_one]
    rw [hm] at hw
    have t1 := mul_le_mul_of_nonneg_right hw (inv_nonneg.mpr (sq_nonneg L))
    have t2 : x ^ (j0 + j) * ((if pf k = 0 then (0 : ℝ) else ((((pf k).natAbs : ℝ) - 1 / 2) ^ 2)⁻¹)
        + x * fiberConst) ≤ x ^ j * x ^ j0 * (cB + x * fiberConst) := by
      rw [pow_add, mul_comm (x ^ j0)]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e3 : x ^ j * (x ^ (j0 + pm) * (L ^ 2)⁻¹ + x ^ j0 * (cB + x * fiberConst)) =
        x ^ j * x ^ (j0 + pm) * (L ^ 2)⁻¹ + x ^ j * x ^ j0 * (cB + x * fiberConst) := by ring
    rw [e3]
    exact add_le_add t1 t2
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hGs' : Gs ≤ (g : ℝ) / 2 ^ P := hg
  have hGs0 : 0 ≤ Gs := Finset.sum_nonneg fun j _ => pow_nonneg hx0 j
  have hpw : ∀ m : ℕ, x ^ m ≤ (powUp e P 64 m : ℝ) / 2 ^ P := fun m => powUp_ge he 64 m
  have hΛ0 : 0 < Λ := hΛpos
  have hA : Gs * x ^ (j0 + pm) ≤ (mulUpK P (powUpK e P 64 (Nat.add j0 pm)) g : ℝ) / 2 ^ P := by
    rw [mulUpK_eq, powUpK_eq]
    refine le_trans ?_ (mulUp_ge P _ _)
    rw [mul_comm]; exact mul_le_mul (hpw _) hGs' hGs0 (by positivity)
  have hB : Gs * x ^ j0 ≤ (mulUpK P (powUpK e P 64 j0) g : ℝ) / 2 ^ P := by
    rw [mulUpK_eq, powUpK_eq]
    refine le_trans ?_ (mulUp_ge P _ _)
    rw [mul_comm]; exact mul_le_mul (hpw _) hGs' hGs0 (by positivity)
  have hx1' : x ≤ (powUp e P 64 1 : ℝ) / 2 ^ P := by simpa using hpw 1
  have hcB0 : 0 ≤ cB := by rw [hcB]; split_ifs <;> positivity
  have k1 := firstK_ge (D := D) (P := P) hΛ0 hA
  have k2 := constK_ge (e := e) (P := P) (pz := pz) hx0 hx1' hB hcB0 le_rfl
  have e1 : Gs * (x ^ (j0 + pm) * (L ^ 2)⁻¹ + x ^ j0 * (cB + x * fiberConst)) =
      Gs * x ^ (j0 + pm) * (L ^ 2)⁻¹ + Gs * x ^ j0 * (cB + x * fiberConst) := by ring
  rw [e1]
  have e2 : (valK D e P (Nat.add (Nat.add a.natAbs lo) i0) g Λ pm pz : ℝ) / 2 ^ P =
      (firstK D (mulUpK P (powUpK e P 64 (Nat.add j0 pm)) g) Λ : ℝ) / 2 ^ P +
        (constK e P (mulUpK P (powUpK e P 64 j0) g) pz : ℝ) / 2 ^ P := by
    rw [← add_div]; congr 1; simp only [valK, Nat.add_eq]; push_cast; rfl
  rw [e2]
  exact add_le_add k1 k2


/-! ### Crossing runs -/

/-- The sign of an integer, `1` for `≥ 0`. -/
def sgnZ : ℤ → ℤ
  | Int.ofNat _ => 1
  | Int.negSucc _ => -1

theorem sgnZ_spec {u w : ℤ} (h : sameSign u w = true) :
    (sgnZ u = 1 ∨ sgnZ u = -1) ∧ sgnZ u * u = u.natAbs ∧ sgnZ u * w = w.natAbs := by
  cases u <;> cases w <;> simp only [sameSign, reduceCtorEq] at h
  · simp [sgnZ]
  · refine ⟨Or.inr rfl, ?_, ?_⟩ <;>
    · simp only [sgnZ]; rw [Int.natAbs_negSucc, Int.negSucc_eq]; push_cast; ring

theorem inv_sq_div_pow (y : ℝ) (q : ℕ) : ((y / 2 ^ q) ^ 2)⁻¹ = 2 ^ (2 * q) * (1 / y ^ 2) := by
  rw [div_pow, inv_div, ← pow_mul, mul_comm q 2]
  ring

/-- The receding first term in fixed point: `Σ_{j<n} x^{J+j} ((F₀ + j d)/2^q)⁻² ≤ ⌈…⌉/2^P`. -/
theorem rec_first_le {q F0 dn n Wp J : ℕ} (he : e < 2 ^ P) (hd : dn < 2 * F0)
    (hden : 0 < 2 * dn * 2 ^ P + (2 ^ P - e) * (2 * F0 - dn))
    (hW : ((e : ℝ) / 2 ^ P) ^ J ≤ (Wp : ℝ) / 2 ^ P) :
    ∑ j ∈ Finset.range n, ((e : ℝ) / 2 ^ P) ^ (J + j) *
        ((((F0 + j * dn : ℕ) : ℝ) / 2 ^ q) ^ 2)⁻¹ ≤
      (ceilDiv (Wp * 2 ^ (2 * q + 2) *
        (2 ^ P * (2 * F0 - dn + 2 * n * dn) - powDownK e P 64 n * (2 * F0 - dn)))
        ((2 * dn * 2 ^ P + (2 ^ P - e) * (2 * F0 - dn)) * (2 * F0 - dn) *
          (2 * F0 - dn + 2 * n * dn)) : ℝ) / 2 ^ P := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hq : (0 : ℝ) < 2 ^ q := by positivity
  set x : ℝ := (e : ℝ) / 2 ^ P with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one hP]; exact_mod_cast he
  set u2 : ℕ := 2 * F0 - dn with hu2
  set w2 : ℕ := 2 * F0 - dn + 2 * n * dn with hw2
  set den : ℕ := 2 * dn * 2 ^ P + (2 ^ P - e) * (2 * F0 - dn) with hden'
  set pd : ℕ := powDownK e P 64 n with hpd
  have hu2p : 0 < u2 := by omega
  have hpdle : (pd : ℝ) / 2 ^ P ≤ x ^ n := powDownK_le e P 64 n
  have hpd2 : pd ≤ 2 ^ P := by
    have : (pd : ℝ) / 2 ^ P ≤ 1 := hpdle.trans (pow_le_one₀ hx0 hx1.le)
    rw [div_le_one hP] at this
    exact_mod_cast this
  have hnum : pd * u2 ≤ 2 ^ P * w2 := Nat.mul_le_mul hpd2 (by omega)
  -- the sum through `receding_sum_le`
  set u : ℝ := (u2 : ℝ) / 2 with hu
  have hu0 : 0 < u := by positivity
  have hd0 : (0 : ℝ) ≤ dn := Nat.cast_nonneg _
  have hrec := receding_sum_le hx0 hx1 hd0 hu0 n
  have hF : ∀ j : ℕ, ((F0 + j * dn : ℕ) : ℝ) = u + (dn : ℝ) / 2 + j * dn := fun j => by
    rw [hu, hu2, Nat.cast_sub (by omega)]; push_cast; ring
  have hsum : ∑ j ∈ Finset.range n, x ^ (J + j) * ((((F0 + j * dn : ℕ) : ℝ) / 2 ^ q) ^ 2)⁻¹ =
      x ^ J * 2 ^ (2 * q) * ∑ j ∈ Finset.range n, x ^ j / (u + (dn : ℝ) / 2 + j * dn) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF, pow_add, inv_sq_div_pow]
    ring
  rw [hsum]
  have hA : 0 < (dn : ℝ) + (1 - x) * u := by
    have : 0 < 1 - x := by linarith
    positivity
  have hlow : (1 / u - x ^ n / (u + n * dn)) / ((dn : ℝ) + (1 - x) * u) ≤
      (1 / u - ((pd : ℝ) / 2 ^ P) / (u + n * dn)) / ((dn : ℝ) + (1 - x) * u) := by
    refine div_le_div_of_nonneg_right ?_ hA.le
    have : 0 < u + n * dn := by positivity
    have := div_le_div_of_nonneg_right hpdle this.le
    linarith
  have hu2c : (u2 : ℝ) = 2 * (F0 : ℝ) - dn := by
    rw [hu2, Nat.cast_sub (by omega)]; push_cast; ring
  have hw2c : (w2 : ℝ) = 2 * (F0 : ℝ) - dn + 2 * n * dn := by
    rw [hw2, Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
  have hdenc : (den : ℝ) = 2 * dn * 2 ^ P + (2 ^ P - e) * (2 * (F0 : ℝ) - dn) := by
    rw [hden']; push_cast [Nat.cast_sub he.le, Nat.cast_sub (show dn ≤ 2 * F0 by omega)]; ring
  have hnumc : (((2 ^ P * w2 - pd * u2 : ℕ)) : ℝ) = 2 ^ P * (w2 : ℝ) - pd * u2 := by
    rw [Nat.cast_sub hnum]; push_cast; ring
  have hu2r : (0 : ℝ) < u2 := by exact_mod_cast hu2p
  have hw2r : (0 : ℝ) < w2 := by
    have : 0 < w2 := by omega
    exact_mod_cast this
  have hdenr : (0 : ℝ) < den := by exact_mod_cast hden
  have hval : (1 / u - ((pd : ℝ) / 2 ^ P) / (u + n * dn)) / ((dn : ℝ) + (1 - x) * u) =
      4 * (((2 ^ P * w2 - pd * u2 : ℕ) : ℝ)) / ((den : ℝ) * u2 * w2) := by
    have hun : u + n * dn = (w2 : ℝ) / 2 := by rw [hu, hw2c, hu2c]; ring
    have hA' : (dn : ℝ) + (1 - x) * u = (den : ℝ) / (2 * 2 ^ P) := by
      rw [hdenc, hu, hu2c, hx]; field_simp
    rw [hun, hA', hnumc, hu]
    rw [div_div_eq_mul_div]
    field_simp
    ring
  have hJ0 : 0 ≤ x ^ J * 2 ^ (2 * q) := by positivity
  have hrest : 0 ≤ 4 * (((2 ^ P * w2 - pd * u2 : ℕ) : ℝ)) / ((den : ℝ) * u2 * w2) := by positivity
  calc x ^ J * 2 ^ (2 * q) * ∑ j ∈ Finset.range n, x ^ j / (u + (dn : ℝ) / 2 + j * dn) ^ 2
      ≤ x ^ J * 2 ^ (2 * q) * (4 * (((2 ^ P * w2 - pd * u2 : ℕ) : ℝ)) / ((den : ℝ) * u2 * w2)) :=
        mul_le_mul_of_nonneg_left (hrec.trans (hlow.trans (le_of_eq hval))) hJ0
    _ ≤ (Wp : ℝ) / 2 ^ P * 2 ^ (2 * q) *
          (4 * (((2 ^ P * w2 - pd * u2 : ℕ) : ℝ)) / ((den : ℝ) * u2 * w2)) := by
        gcongr
    _ = ((Wp * 2 ^ (2 * q + 2) * (2 ^ P * w2 - pd * u2) : ℕ) : ℝ) /
          ((den * u2 * w2 : ℕ) : ℝ) / 2 ^ P := by
        push_cast
        ring
    _ ≤ _ := by
        refine div_le_div_of_nonneg_right (div_le_ceilDiv _ ?_) hP.le
        have : 0 < den := hden
        have : 0 < w2 := by omega
        positivity

/-- The approaching first term in fixed point:
`Σ_{j<n} x^{J+j} ((F₁ + (n-1-j) e')/2^q)⁻² ≤ ⌈Wp 2^{2q+2} n / ((2F₁ - e')(2F₁ + (2n-1)e'))⌉/2^P`. -/
theorem app_first_le {q F1 ea n Wp J : ℕ} (he : e ≤ 2 ^ P) (hea : ea < 2 * F1)
    (hW : ((e : ℝ) / 2 ^ P) ^ J ≤ (Wp : ℝ) / 2 ^ P) :
    ∑ j ∈ Finset.range n, ((e : ℝ) / 2 ^ P) ^ (J + j) *
        ((((F1 + (n - 1 - j) * ea : ℕ) : ℝ) / 2 ^ q) ^ 2)⁻¹ ≤
      (ceilDiv (Wp * 2 ^ (2 * q + 2) * n)
        ((2 * F1 - ea) * (2 * F1 + (2 * n - 1) * ea)) : ℝ) / 2 ^ P := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  set x : ℝ := (e : ℝ) / 2 ^ P with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hP]; exact_mod_cast he
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  set v : ℝ := ((2 * F1 - ea : ℕ) : ℝ) / 2 with hv
  have hv0 : 0 < v := by
    have : 0 < 2 * F1 - ea := by omega
    positivity
  have hea0 : (0 : ℝ) ≤ ea := Nat.cast_nonneg _
  have happ := approach_sum_le hea0 hv0 n
  have hF : ∀ k : ℕ, (F1 : ℝ) + k * ea = v + (ea : ℝ) / 2 + k * ea := fun k => by
    rw [hv, Nat.cast_sub (by omega)]; push_cast; ring
  -- weights at most `x^J`, and the sum reflected
  have h1 : ∑ j ∈ Finset.range n,
      x ^ (J + j) * ((((F1 + (n - 1 - j) * ea : ℕ) : ℝ) / 2 ^ q) ^ 2)⁻¹ ≤
      x ^ J * 2 ^ (2 * q) * ∑ k ∈ Finset.range n, 1 / (v + (ea : ℝ) / 2 + k * ea) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    have hjj : n - 1 - (n - 1 - j) = j := by omega
    simp only [hjj]
    rw [← hF j]
    have e1 : ((((F1 + j * ea : ℕ) : ℝ) / 2 ^ q) ^ 2)⁻¹ =
        2 ^ (2 * q) * (1 / ((F1 : ℝ) + j * ea) ^ 2) := by
      rw [inv_sq_div_pow]; push_cast; ring
    rw [e1, pow_add]
    have hxj : x ^ (n - 1 - j) ≤ 1 := pow_le_one₀ hx0 hx1
    have hpos : (0 : ℝ) ≤ 2 ^ (2 * q) * (1 / ((F1 : ℝ) + j * ea) ^ 2) := by positivity
    calc x ^ J * x ^ (n - 1 - j) * (2 ^ (2 * q) * (1 / ((F1 : ℝ) + j * ea) ^ 2))
        ≤ x ^ J * 1 * (2 ^ (2 * q) * (1 / ((F1 : ℝ) + j * ea) ^ 2)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxj (pow_nonneg hx0 _)) hpos
      _ = _ := by ring
  refine h1.trans ?_
  have hAc : ((2 * F1 - ea : ℕ) : ℝ) = 2 * (F1 : ℝ) - ea := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hBc : ((2 * F1 + (2 * n - 1) * ea : ℕ) : ℝ) = 2 * (F1 : ℝ) - ea + 2 * n * ea := by
    push_cast [Nat.cast_sub (show 1 ≤ 2 * n by omega)]; ring
  have hAr : (0 : ℝ) < 2 * (F1 : ℝ) - ea := by
    rw [← hAc]; have : 0 < 2 * F1 - ea := by omega
    exact_mod_cast this
  have hval : (n : ℝ) / (v * (v + n * ea)) =
      4 * n / (((2 * F1 - ea : ℕ) : ℝ) * ((2 * F1 + (2 * n - 1) * ea : ℕ) : ℝ)) := by
    rw [hv, hAc, hBc]
    have h3 : (0 : ℝ) < 2 * (F1 : ℝ) - ea + 2 * n * ea := by positivity
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hJ0 : 0 ≤ x ^ J * 2 ^ (2 * q) := by positivity
  calc x ^ J * 2 ^ (2 * q) * ∑ k ∈ Finset.range n, 1 / (v + (ea : ℝ) / 2 + k * ea) ^ 2
      ≤ x ^ J * 2 ^ (2 * q) * (4 * n / (((2 * F1 - ea : ℕ) : ℝ) *
          ((2 * F1 + (2 * n - 1) * ea : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (happ.trans (le_of_eq hval)) hJ0
    _ ≤ (Wp : ℝ) / 2 ^ P * 2 ^ (2 * q) * (4 * n / (((2 * F1 - ea : ℕ) : ℝ) *
          ((2 * F1 + (2 * n - 1) * ea : ℕ) : ℝ))) := by
        gcongr
    _ = ((Wp * 2 ^ (2 * q + 2) * n : ℕ) : ℝ) /
          (((2 * F1 - ea) * (2 * F1 + (2 * n - 1) * ea) : ℕ) : ℝ) / 2 ^ P := by
        push_cast
        ring
    _ ≤ _ := by
        refine div_le_div_of_nonneg_right (div_le_ceilDiv _ ?_) hP.le
        have : 0 < 2 * F1 - ea := by omega
        have : 0 < 2 * F1 + (2 * n - 1) * ea := by omega
        positivity


/-- **The crossing check** of `b = sg(lo + i)`, `i₀ < i ≤ i₁`: `p = nearP(X(i₀))`, one sign,
`Rd < |Z|` and `2(|Z| + Rd) ≤ 2^q` at both ends (as `blkK`); `F = sZ - Rd` has the integer slope
`d = s σ C₁ - R₁`. Receding (`d ≥ 0`, `d < 2F₀`) or approaching (`d < 0`, `-d < 2F₁`) closed form,
accepted if the near end is at least `s₀|d|` from the crossing (approaching: and the weights vary by
at most `rn/rd`). There is no tolerance fallback: the value is computed only for an accepted run. -/
def apK (D : DBox2) (e P g s0 rn rd : ℕ) (a sg : ℤ) (lo i0 i1 : ℕ) : Option ℕ :=
  let p : ℤ := nearP D.q (colX D a sg lo i0)
  let Z0 : ℤ := colZ D a sg p lo i0
  let Z1 : ℤ := colZ D a sg p lo i1
  let Y0 : ℕ := Int.natAbs Z0
  let Y1 : ℕ := Int.natAbs Z1
  let R0 : ℕ := colR D a lo i0
  let R1 : ℕ := colR D a lo i1
  cond (Nat.blt i0 i1 && sameSign Z0 Z1 && Nat.blt R0 Y0 && Nat.blt R1 Y1 &&
      Nat.ble (Nat.mul 2 (Nat.add Y0 R0)) (pow2 D.q) &&
      Nat.ble (Nat.mul 2 (Nat.add Y1 R1)) (pow2 D.q))
    (let F0 : ℕ := Nat.sub Y0 R0
     let F1 : ℕ := Nat.sub Y1 R1
     let n : ℕ := Nat.add (Nat.sub i1 i0) 1
     let j0 : ℕ := Nat.add (Nat.add (Int.natAbs a) lo) i0
     let pa : ℕ := Int.natAbs p
     let Wp : ℕ := powUpK e P 64 (Nat.add j0 pa)
     let cst : ℕ := constK e P (mulUpK P (powUpK e P 64 j0) g) pa
     let Q4 : ℕ := pow2 (Nat.add (Nat.mul 2 D.q) 2)
     match sgnZ Z0 * sg * D.C1 - (D.R1 : ℤ) with
     | Int.ofNat dn =>
       let u2 : ℕ := Nat.sub (Nat.mul 2 F0) dn
       let w2 : ℕ := Nat.add u2 (Nat.mul (Nat.mul 2 n) dn)
       let den : ℕ := Nat.add (Nat.mul (Nat.mul 2 dn) (pow2 P)) (Nat.mul (Nat.sub (pow2 P) e) u2)
       cond (Nat.blt dn (Nat.mul 2 F0) && Nat.blt 0 den)
         (let v : ℕ := Nat.add (ceilDiv (Nat.mul (Nat.mul Wp Q4)
             (Nat.sub (Nat.mul (pow2 P) w2) (Nat.mul (powDownK e P 64 n) u2)))
             (Nat.mul (Nat.mul den u2) w2)) cst
          cond (Nat.ble (Nat.mul s0 dn) F0) (some v) none)
         none
     | Int.negSucc k =>
       let ea : ℕ := Nat.add k 1
       cond (Nat.blt ea (Nat.mul 2 F1))
         (let v : ℕ := Nat.add (ceilDiv (Nat.mul (Nat.mul Wp Q4) n)
             (Nat.mul (Nat.sub (Nat.mul 2 F1) ea)
               (Nat.add (Nat.mul 2 F1) (Nat.mul (Nat.sub (Nat.mul 2 n) 1) ea)))) cst
          cond (Nat.ble (Nat.mul s0 ea) F1 &&
              Nat.ble (Nat.mul rd (pow2 P)) (Nat.mul rn (powUpK e P 64 (Nat.sub n 1))))
            (some v) none)
         none)
    none

/-- **Soundness of the crossing check.** -/
theorem apK_spec {ω' : Fin 2 → ℝ} (hω : FreqEncloses 2 D.toBox ω') (he : e < 2 ^ P)
    {g s0 rn rd : ℕ} {a sg : ℤ} {lo i0 i1 v : ℕ}
    (hg : ∑ j ∈ Finset.range (i1 - i0 + 1), ((e : ℝ) / 2 ^ P) ^ j ≤ (g : ℝ) / 2 ^ P)
    (hsg : sg = 1 ∨ sg = -1) (h : apK D e P g s0 rn rd a sg lo i0 i1 = some v) :
    BCov ω' ((e : ℝ) / 2 ^ P) (runSet a sg lo i0 (i1 - i0 + 1)) ((v : ℝ) / 2 ^ P) := by
  unfold apK at h
  set p : ℤ := nearP D.q (colX D a sg lo i0) with hp
  simp only [Bool.cond_eq_ite, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq,
    Nat.add_eq, Nat.mul_eq, Nat.sub_eq, pow2_eq] at h
  split at h
  case isFalse => exact absurd h (by simp)
  rename_i hc
  obtain ⟨⟨⟨⟨⟨hi01, hsame⟩, hlt0⟩, hlt1⟩, hup0⟩, hup1⟩ := hc
  obtain ⟨hs, hs0, hs1⟩ := sgnZ_spec hsame
  set sZ : ℤ := sgnZ (colZ D a sg p lo i0) with hsZ
  set x : ℝ := (e : ℝ) / 2 ^ P with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one (by positivity)]; exact_mod_cast he.le
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hq : (0 : ℝ) < 2 ^ D.q := by positivity
  -- the affine distance `F(i) = s Z(i) - Rd(i)`
  set Fz : ℕ → ℤ := fun i => sZ * colZ D a sg p lo i - colR D a lo i with hFz
  generalize hdFg : sZ * sg * D.C1 - (D.R1 : ℤ) = dF at h
  have hdF : dF = sZ * sg * D.C1 - (D.R1 : ℤ) := hdFg.symm
  have hFaff : ∀ j : ℕ, Fz (i0 + j) = Fz i0 + j * dF := fun j => by
    simp only [hFz, hdF, colZ_eq, colR_eq]; push_cast; ring
  have hF0 : Fz i0 = ((colZ D a sg p lo i0).natAbs - colR D a lo i0 : ℕ) := by
    simp only [hFz]; rw [hs0, Nat.cast_sub hlt0.le]
  have hF1 : Fz i1 = ((colZ D a sg p lo i1).natAbs - colR D a lo i1 : ℕ) := by
    simp only [hFz]; rw [hs1, Nat.cast_sub hlt1.le]
  set n : ℕ := i1 - i0 + 1 with hn
  set F0 : ℕ := (colZ D a sg p lo i0).natAbs - colR D a lo i0 with hF0def
  set F1 : ℕ := (colZ D a sg p lo i1).natAbs - colR D a lo i1 with hF1def
  have hF0p : 0 < F0 := by omega
  have hF1p : 0 < F1 := by omega
  have hFi1 : (F1 : ℤ) = F0 + (n - 1 : ℕ) * dF := by
    rw [← hF1, ← hF0, ← hFaff]; congr 1; omega
  have hFpos : ∀ j < n, 0 < Fz (i0 + j) := fun j hj => by
    rw [hFaff, hF0]
    have key := affine_ge_min (c := (F0 : ℤ)) (d := dF) (Nat.zero_le j) (show j ≤ n - 1 by omega)
    simp only [Nat.cast_zero, mul_zero, add_zero] at key
    have key' : min (F0 : ℤ) (F1 : ℤ) ≤ F0 + j * dF := by
      rw [hFi1, mul_comm (((n - 1 : ℕ) : ℤ)) dF, mul_comm (j : ℤ) dF]; exact key
    have : (0 : ℤ) < min (F0 : ℤ) (F1 : ℤ) :=
      lt_min (by exact_mod_cast hF0p) (by exact_mod_cast hF1p)
    linarith
  -- the upper distance `G(i) = s Z(i) + Rd(i)`
  set U : ℕ := max ((colZ D a sg p lo i0).natAbs + colR D a lo i0)
    ((colZ D a sg p lo i1).natAbs + colR D a lo i1) with hU
  have hGle : ∀ j < n, sZ * colZ D a sg p lo (i0 + j) + colR D a lo (i0 + j) ≤ (U : ℤ) := by
    intro j hj
    have key := affine_le_max
      (c := sZ * colZ D a sg p lo i0 + colR D a lo i0) (d := sZ * sg * D.C1 + D.R1)
      (Nat.zero_le j) (show j ≤ n - 1 by omega)
    have ej : ∀ m : ℕ, sZ * colZ D a sg p lo (i0 + m) + colR D a lo (i0 + m) =
        sZ * colZ D a sg p lo i0 + colR D a lo i0 + (sZ * sg * D.C1 + D.R1) * m := fun m => by
      simp only [colZ_eq, colR_eq]; push_cast; ring
    rw [← ej, ← ej, ← ej, show i0 + (n - 1) = i1 by omega] at key
    simp only [add_zero] at key
    rw [hU, Nat.cast_max]
    rw [hs0, hs1] at key
    push_cast at key ⊢
    simpa using key
  have hU2 : 2 * (U : ℤ) ≤ 2 ^ D.q := by
    have : 2 * U ≤ 2 ^ D.q := by
      rw [hU]
      rcases le_total ((colZ D a sg p lo i0).natAbs + colR D a lo i0)
        ((colZ D a sg p lo i1).natAbs + colR D a lo i1) with hh | hh
      · rw [max_eq_right hh]; exact hup1
      · rw [max_eq_left hh]; exact hup0
    exact_mod_cast this
  -- every fibre
  set Lf : (Fin 2 → ℤ) → ℝ := fun k => ((Fz ((k 1).natAbs - lo) : ℤ) : ℝ) / 2 ^ D.q with hLf
  have hk1 : ∀ j : ℕ, ((![a, sg * ((lo + i0 + j : ℕ) : ℤ)] : Fin 2 → ℤ) 1).natAbs - lo = i0 + j :=
    fun j => by
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, natAbs_sg_mul hsg]; omega
  have hpt : ∀ j < n,
      |Diophantine.frequencyDot ω' ![a, sg * ((lo + i0 + j : ℕ) : ℤ)] + p| ≤ 1 / 2 ∧
      ((Fz (i0 + j) : ℤ) : ℝ) / 2 ^ D.q ≤
        |Diophantine.frequencyDot ω' ![a, sg * ((lo + i0 + j : ℕ) : ℤ)] + p| := fun j hj => by
    refine run_point hω _ hs (hFpos j hj) ?_ ?_ hU2
    · simp only [hFz, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        natAbs_sg_mul hsg, colZ_eq, colR_eq]
      rw [show lo + i0 + j = lo + (i0 + j) by omega]
    · have := hGle j hj
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        natAbs_sg_mul hsg]
      rw [colZ_eq, colR_eq] at this
      rw [show lo + i0 + j = lo + (i0 + j) by omega]
      exact this
  -- the cover; first, the sum of the terms `j = 0` and `C₀`
  set j0 : ℕ := a.natAbs + lo + i0 with hj0
  set Gs : ℝ := ∑ j ∈ Finset.range n, x ^ j with hGs
  have hGs0 : 0 ≤ Gs := Finset.sum_nonneg fun j _ => pow_nonneg hx0 j
  have hpw : ∀ m : ℕ, x ^ m ≤ (powUp e P 64 m : ℝ) / 2 ^ P := fun m => powUp_ge he.le 64 m
  set cP : ℝ := if p = 0 then 0 else ((((p.natAbs : ℝ) - 1 / 2) ^ 2)⁻¹) with hcP
  have hcP0 : 0 ≤ cP := by rw [hcP]; split_ifs <;> positivity
  have hcPle : cP ≤ if p.natAbs = 0 then 0 else 4 / (2 * (p.natAbs : ℝ) - 1) ^ 2 := by
    rw [hcP]
    by_cases hp0 : p = 0
    · simp [hp0]
    · have hpa : p.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hp0
      simp only [hp0, hpa, ↓reduceIte]
      have h1 : (1 : ℝ) ≤ p.natAbs := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hpa
      rw [show (4 : ℝ) / (2 * (p.natAbs : ℝ) - 1) ^ 2 = (((p.natAbs : ℝ) - 1 / 2) ^ 2)⁻¹ by
        field_simp; ring]
  have hB : Gs * x ^ j0 ≤ (mulUpK P (powUpK e P 64 j0) g : ℝ) / 2 ^ P := by
    rw [mulUpK_eq, powUpK_eq]
    refine le_trans ?_ (mulUp_ge P _ _)
    rw [mul_comm]; exact mul_le_mul (hpw _) hg hGs0 (by positivity)
  have hx1' : x ≤ (powUp e P 64 1 : ℝ) / 2 ^ P := by simpa using hpw 1
  have hcst := constK_ge (e := e) (P := P) (pz := p.natAbs) hx0 hx1' hB hcP0 hcPle
  have hW : x ^ (j0 + p.natAbs) ≤ (powUpK e P 64 (j0 + p.natAbs) : ℝ) / 2 ^ P := by
    rw [powUpK_eq]; exact hpw _
  -- the sum, split into the first terms and the rest
  have hsplit : ∑ k ∈ runSet a sg lo i0 n, termX x k p (Lf k) =
      ∑ j ∈ Finset.range n, x ^ (j0 + p.natAbs + j) *
        ((((Fz (i0 + j) : ℤ) : ℝ) / 2 ^ D.q) ^ 2)⁻¹ + Gs * x ^ j0 * (cP + x * fiberConst) := by
    rw [runSet_sum hsg, hGs, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [termX, hLf, hk1, modeNat_run hsg, pow_one, hcP]
    rw [show a.natAbs + (lo + i0 + j) + p.natAbs = j0 + p.natAbs + j by omega,
      show a.natAbs + (lo + i0 + j) = j0 + j by omega, pow_add x j0 j]
    ring
  refine ⟨fun _ => p, Lf, fun k hk => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := mem_runSet.mp hk
    have hj' := hj
    obtain ⟨h1, h2⟩ := hpt j hj
    refine ⟨h1, ?_, ?_⟩
    · simp only [hLf, hk1]
      have : (0 : ℝ) < ((Fz (i0 + j) : ℤ) : ℝ) := by exact_mod_cast hFpos j hj'
      positivity
    · simp only [hLf, hk1]; exact h2
  rw [hsplit]
  -- the two closed forms
  cases dF with
  | ofNat dn =>
    simp only [Int.ofNat_eq_natCast] at h hFaff
    split at h
    case isFalse => exact absurd h (by simp)
    rename_i hcd
    obtain ⟨hd2, hden⟩ := hcd
    split at h
    case isFalse => exact absurd h (by simp)
    simp only [Option.some.injEq] at h
    subst h
    have hFj : ∀ j : ℕ, ((Fz (i0 + j) : ℤ) : ℝ) = ((F0 + j * dn : ℕ) : ℝ) := fun j => by
      rw [hFaff, hF0]; push_cast; ring
    have hfirst := rec_first_le (q := D.q) (F0 := F0) (dn := dn) (n := n)
      (Wp := powUpK e P 64 (j0 + p.natAbs)) (J := j0 + p.natAbs) he hd2 hden hW
    simp only [hFj]
    rw [Nat.cast_add, add_div]
    exact add_le_add hfirst hcst
  | negSucc k =>
    simp only at h
    split at h
    case isFalse => exact absurd h (by simp)
    rename_i hea
    split at h
    case isFalse => exact absurd h (by simp)
    simp only [Option.some.injEq] at h
    subst h
    have hFj : ∀ j < n, ((Fz (i0 + j) : ℤ) : ℝ) = ((F1 + (n - 1 - j) * (k + 1) : ℕ) : ℝ) :=
      fun j hj => by
        have e1 : Fz (i0 + j) = (F1 : ℤ) + ((n - 1 - j : ℕ) : ℤ) * ((k + 1 : ℕ) : ℤ) := by
          rw [hFaff, hFi1, hF0, Int.negSucc_eq]
          push_cast [Nat.cast_sub (show j ≤ n - 1 by omega), Nat.cast_sub (show 1 ≤ n by omega)]
          ring
        rw [e1]; push_cast; ring
    have hfirst := app_first_le (q := D.q) (F1 := F1) (ea := k + 1) (n := n)
      (Wp := powUpK e P 64 (j0 + p.natAbs)) (J := j0 + p.natAbs) he.le hea hW
    rw [Finset.sum_congr rfl fun j hj => by rw [hFj j (Finset.mem_range.mp hj)]]
    rw [Nat.cast_add, add_div]
    exact add_le_add hfirst hcst

end Run

end KAM.CertificateSharp.Fiber

end
