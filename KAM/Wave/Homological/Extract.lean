/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Coefficient extraction by roots of unity (blueprint-W `bpW:w4:extract`)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still being built.

For a complex normed space `E` and `g(ζ,η) = ∑_{p+q ≤ 2} g_{pq} ζ^p η^q`, a bound `‖g‖ ≤ K` on the
open polydisc `|ζ| < ρ₁`, `|η| < ρ₂` gives `‖g_{pq}‖ ≤ K ρ₁^{-p} ρ₂^{-q}`. The coefficients are the
family `c : Fin 3 → Fin 3 → E` vanishing for `p + q > 2`. The proof averages over the fourth roots of
unity (W4-E1): `g_{pq} r₁^p r₂^q = (1/16) ∑_{u,v<4} i^{-up-vq} g(r₁ i^u, r₂ i^v)`.
The same holds in one variable (`polyExtract_one`).
-/

@[expose] public section

namespace KAM.Wave

open Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The polynomial `g(ζ,η) = ∑_{p,q} ζ^p η^q c_{pq}` (the coefficients with `p + q > 2` vanish). -/
def polyEval2 (c : Fin 3 → Fin 3 → E) (ζ η : ℂ) : E :=
  ∑ p : Fin 3, ∑ q : Fin 3, (ζ ^ (p : ℕ) * η ^ (q : ℕ)) • c p q

/-- **Roots of unity** (blueprint W4-E1, in the form used): for `2 ≤ m ≤ 6`,
`∑_{u<4} (i^m)^u = 4` if `m = 4` and `0` otherwise. -/
theorem sum_I_pow (m : ℕ) (h2 : 2 ≤ m) (h6 : m ≤ 6) :
    ∑ u ∈ Finset.range 4, (I ^ m) ^ u = if m = 4 then 4 else 0 := by
  interval_cases m <;> simp [Finset.sum_range_succ, pow_succ]

/-- The sum over the sixteen points picks out the coefficient `(p, q)`. -/
theorem sum_weighted_polyEval2 (c : Fin 3 → Fin 3 → E) (r₁ r₂ : ℝ) (p q : Fin 3) :
    ∑ u ∈ Finset.range 4, ∑ v ∈ Finset.range 4,
      ((I ^ u) ^ (4 - (p : ℕ)) * (I ^ v) ^ (4 - (q : ℕ))) •
        polyEval2 c (r₁ * I ^ u) (r₂ * I ^ v) =
      (16 * (r₁ : ℂ) ^ (p : ℕ) * (r₂ : ℂ) ^ (q : ℕ)) • c p q := by
  have hterm : ∀ (u v : ℕ) (p' q' : Fin 3),
      ((I ^ u) ^ (4 - (p : ℕ)) * (I ^ v) ^ (4 - (q : ℕ))) •
        (((r₁ * I ^ u) ^ (p' : ℕ) * (r₂ * I ^ v) ^ (q' : ℕ)) • c p' q') =
      ((r₁ : ℂ) ^ (p' : ℕ) * (r₂ : ℂ) ^ (q' : ℕ) *
        ((I ^ ((p' : ℕ) + (4 - (p : ℕ)))) ^ u * (I ^ ((q' : ℕ) + (4 - (q : ℕ)))) ^ v)) •
        c p' q' := by
    intro u v p' q'
    rw [smul_smul]
    congr 1
    ring
  set T : ℕ → ℕ → Fin 3 → Fin 3 → E := fun u v p' q' =>
    ((r₁ : ℂ) ^ (p' : ℕ) * (r₂ : ℂ) ^ (q' : ℕ) *
        ((I ^ ((p' : ℕ) + (4 - (p : ℕ)))) ^ u * (I ^ ((q' : ℕ) + (4 - (q : ℕ)))) ^ v)) •
      c p' q' with hT
  have hL : ∀ u v : ℕ, ((I ^ u) ^ (4 - (p : ℕ)) * (I ^ v) ^ (4 - (q : ℕ))) •
      polyEval2 c (r₁ * I ^ u) (r₂ * I ^ v) = ∑ p', ∑ q', T u v p' q' := by
    intro u v
    unfold polyEval2
    simp only [Finset.smul_sum, hterm, hT]
  simp only [hL]
  calc ∑ u ∈ Finset.range 4, ∑ v ∈ Finset.range 4, ∑ p' : Fin 3, ∑ q' : Fin 3, T u v p' q'
      = ∑ u ∈ Finset.range 4, ∑ p' : Fin 3, ∑ v ∈ Finset.range 4, ∑ q' : Fin 3, T u v p' q' :=
        Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ p' : Fin 3, ∑ u ∈ Finset.range 4, ∑ v ∈ Finset.range 4, ∑ q' : Fin 3, T u v p' q' :=
        Finset.sum_comm
    _ = ∑ p' : Fin 3, ∑ u ∈ Finset.range 4, ∑ q' : Fin 3, ∑ v ∈ Finset.range 4, T u v p' q' :=
        Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ p' : Fin 3, ∑ q' : Fin 3, ∑ u ∈ Finset.range 4, ∑ v ∈ Finset.range 4, T u v p' q' :=
        Finset.sum_congr rfl fun p' _ => Finset.sum_comm
    _ = (16 * (r₁ : ℂ) ^ (p : ℕ) * (r₂ : ℂ) ^ (q : ℕ)) • c p q := by
      have hinner : ∀ p' q' : Fin 3, ∑ u ∈ Finset.range 4, ∑ v ∈ Finset.range 4, T u v p' q' =
          (((r₁ : ℂ) ^ (p' : ℕ) * (r₂ : ℂ) ^ (q' : ℕ)) *
            ((∑ u ∈ Finset.range 4, (I ^ ((p' : ℕ) + (4 - (p : ℕ)))) ^ u) *
              (∑ v ∈ Finset.range 4, (I ^ ((q' : ℕ) + (4 - (q : ℕ)))) ^ v))) • c p' q' := by
        intro p' q'
        have h1 : ∀ u : ℕ, ∑ v ∈ Finset.range 4, T u v p' q' =
            (∑ v ∈ Finset.range 4, (r₁ : ℂ) ^ (p' : ℕ) * (r₂ : ℂ) ^ (q' : ℕ) *
              ((I ^ ((p' : ℕ) + (4 - (p : ℕ)))) ^ u *
                (I ^ ((q' : ℕ) + (4 - (q : ℕ)))) ^ v)) • c p' q' := fun u => by
          simp only [hT, Finset.sum_smul]
        simp only [h1]
        rw [← Finset.sum_smul]
        congr 1
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
      have hsum : ∀ (p' : Fin 3) (p : Fin 3), ∑ u ∈ Finset.range 4, (I ^ ((p' : ℕ) + (4 - (p : ℕ)))) ^ u =
          if p' = p then 4 else 0 := by
        intro p' p
        rw [sum_I_pow _ (by omega) (by omega)]
        have : ((p' : ℕ) + (4 - (p : ℕ)) = 4) ↔ p' = p := by
          constructor
          · intro h; ext; omega
          · intro h; subst h; omega
        simp only [this]
      simp only [hinner, hsum]
      rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
      · simp only [ite_true]
        refine congrArg (· • c p q) ?_
        ring
      · intro q' _ hq'
        simp [hq']
      · simp
      · intro p' _ hp'
        simp [hp']
      · simp


theorem norm_I_pow (u : ℕ) : ‖I ^ u‖ = 1 := by simp

/-- **Coefficient extraction** (blueprint `bpW:w4:extract`), for all `(p, q) ∈ Fin 3 × Fin 3`:
if `‖g(ζ,η)‖ ≤ K` on `|ζ| < ρ₁`, `|η| < ρ₂`, then `‖c_{pq}‖ ρ₁^p ρ₂^q ≤ K`. -/
theorem polyExtract_mul_le (c : Fin 3 → Fin 3 → E) {ρ₁ ρ₂ K : ℝ} (h₁ : 0 < ρ₁) (h₂ : 0 < ρ₂)
    (hK : ∀ ζ η : ℂ, ‖ζ‖ < ρ₁ → ‖η‖ < ρ₂ → ‖polyEval2 c ζ η‖ ≤ K) (p q : Fin 3) :
    ‖c p q‖ * (ρ₁ ^ (p : ℕ) * ρ₂ ^ (q : ℕ)) ≤ K := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 0 (by simpa using h₁) (by simpa using h₂))
  have key : ∀ t : ℝ, 0 < t → t < 1 →
      ‖c p q‖ * (ρ₁ ^ (p : ℕ) * ρ₂ ^ (q : ℕ)) * t ^ ((p : ℕ) + q) ≤ K := by
    intro t ht0 ht1
    set r₁ := t * ρ₁ with hr₁
    set r₂ := t * ρ₂ with hr₂
    have hr₁p : 0 < r₁ := mul_pos ht0 h₁
    have hr₂p : 0 < r₂ := mul_pos ht0 h₂
    have hid := sum_weighted_polyEval2 c r₁ r₂ p q
    have hnorm : ‖(16 * (r₁ : ℂ) ^ (p : ℕ) * (r₂ : ℂ) ^ (q : ℕ)) • c p q‖ ≤ 16 * K := by
      rw [← hid]
      refine (norm_sum_le _ _).trans ?_
      have : ∀ u ∈ Finset.range 4, ‖∑ v ∈ Finset.range 4,
          ((I ^ u) ^ (4 - (p : ℕ)) * (I ^ v) ^ (4 - (q : ℕ))) •
            polyEval2 c ((r₁ : ℂ) * I ^ u) ((r₂ : ℂ) * I ^ v)‖ ≤ 4 * K := by
        intro u _
        refine (norm_sum_le _ _).trans ?_
        have h4 : ∀ v ∈ Finset.range 4, ‖((I ^ u) ^ (4 - (p : ℕ)) * (I ^ v) ^ (4 - (q : ℕ))) •
            polyEval2 c ((r₁ : ℂ) * I ^ u) ((r₂ : ℂ) * I ^ v)‖ ≤ K := by
          intro v _
          simp only [norm_smul, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
          refine hK _ _ ?_ ?_
          · rw [norm_mul, norm_I_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₁p]
            simp only [mul_one, hr₁]
            nlinarith
          · rw [norm_mul, norm_I_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₂p]
            simp only [mul_one, hr₂]
            nlinarith
        calc ∑ v ∈ Finset.range 4, _ ≤ ∑ _v ∈ Finset.range 4, K := Finset.sum_le_sum h4
          _ = 4 * K := by simp
      calc ∑ u ∈ Finset.range 4, _ ≤ ∑ _u ∈ Finset.range 4, 4 * K := Finset.sum_le_sum this
        _ = 16 * K := by simp; ring
    rw [norm_smul] at hnorm
    have e1 : ‖(16 * (r₁ : ℂ) ^ (p : ℕ) * (r₂ : ℂ) ^ (q : ℕ))‖ =
        16 * (r₁ ^ (p : ℕ) * r₂ ^ (q : ℕ)) := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr₁p, abs_of_pos hr₂p]
      simp
      ring
    rw [e1] at hnorm
    have e2 : r₁ ^ (p : ℕ) * r₂ ^ (q : ℕ) = (ρ₁ ^ (p : ℕ) * ρ₂ ^ (q : ℕ)) * t ^ ((p : ℕ) + q) := by
      rw [hr₁, hr₂, mul_pow, mul_pow, pow_add]; ring
    rw [e2] at hnorm
    nlinarith
  by_contra hcon
  push Not at hcon
  set X := ‖c p q‖ * (ρ₁ ^ (p : ℕ) * ρ₂ ^ (q : ℕ)) with hX
  have hlim : Filter.Tendsto (fun t : ℝ => X * t ^ ((p : ℕ) + q)) (nhdsWithin 1 (Set.Iio 1))
      (nhds X) := by
    have hc : Continuous fun t : ℝ => X * t ^ ((p : ℕ) + q) := by fun_prop
    have := (hc.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    simpa using this
  have hev : ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Iio 1), X * t ^ ((p : ℕ) + q) ≤ K := by
    have : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
      Ioo_mem_nhdsLT (by norm_num)
    filter_upwards [this] with t ht using key t ht.1 ht.2
  exact absurd (le_of_tendsto hlim hev) (not_le.mpr hcon)

/-- **Coefficient extraction** (blueprint `bpW:w4:extract`), two variables: for `p + q ≤ 2`,
`‖g_{pq}‖ ≤ K ρ₁^{-p} ρ₂^{-q}`. -/
theorem polyExtract {c : Fin 3 → Fin 3 → E} {ρ₁ ρ₂ K : ℝ} (h₁ : 0 < ρ₁) (h₂ : 0 < ρ₂)
    (hc : ∀ p q : Fin 3, 2 < (p : ℕ) + q → c p q = 0)
    (hK : ∀ ζ η : ℂ, ‖ζ‖ < ρ₁ → ‖η‖ < ρ₂ → ‖polyEval2 c ζ η‖ ≤ K) (p q : Fin 3)
    (_hpq : (p : ℕ) + q ≤ 2) :
    ‖c p q‖ ≤ K / (ρ₁ ^ (p : ℕ) * ρ₂ ^ (q : ℕ)) := by
  have _ := hc
  rw [le_div_iff₀ (by positivity)]
  exact polyExtract_mul_le c h₁ h₂ hK p q

/-- **Coefficient extraction in one variable** (blueprint `bpW:w4:extract`): `g(ζ) = ∑_{p ≤ 2} g_p ζ^p`
with `‖g‖ ≤ K` on `|ζ| < ρ` gives `‖g_p‖ ≤ K ρ^{-p}`. -/
theorem polyExtract_one (c : Fin 3 → E) {ρ K : ℝ} (hρ : 0 < ρ)
    (hK : ∀ ζ : ℂ, ‖ζ‖ < ρ → ‖∑ p : Fin 3, ζ ^ (p : ℕ) • c p‖ ≤ K) (p : Fin 3) :
    ‖c p‖ ≤ K / ρ ^ (p : ℕ) := by
  let c2 : Fin 3 → Fin 3 → E := fun p q => if q = 0 then c p else 0
  have h := polyExtract_mul_le c2 hρ one_pos (K := K) (fun ζ η hζ _ => by
    have : polyEval2 c2 ζ η = ∑ p : Fin 3, ζ ^ (p : ℕ) • c p := by
      unfold polyEval2
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Fin.sum_univ_three]
      simp [c2]
    rw [this]
    exact hK ζ hζ) p 0
  simp only [c2, ite_true, Fin.val_zero, pow_zero, mul_one] at h
  rw [le_div_iff₀ (by positivity)]
  exact h

end KAM.Wave
