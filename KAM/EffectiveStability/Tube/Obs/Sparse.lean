/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Sparse
public import KAM.EffectiveStability.Tube.Obs.ListObs

/-!
# Bounds of sparse literal models from their entries (T2-CONF, N8)

For a sparse model `d : SpD` (N7) with `d.ok S`, the value is `q · Σ_e m_e trig(k_e · φ)`
(`SpD.eval_eq`). Bounds read off the entries, with no decoding:

* `SpD.abs_eval_le'`: `|eval| ≤ |q| Σ |m|`;
* `SpD.abs_fderiv_eval_le`: `|∂_b eval| ≤ |q| Σ_e |k_{e,b}| |m_e|` (`spW`);
* `SpD.abs_eval_sub_le`: for even parity, `|eval - κ| ≤ |q m₀ - κ| + |q| Σ_{k_e ≠ 0} |m_e|`, with
  `m₀` the
  sum of the mantissas of mode `0` (`spZ0`, `spNZ`);
* `SpD.differentiable_eval`, `SpD.eval_add_two_pi`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Finset

/-- The mode `(c - C, r - C)` of an entry. -/
def spMode (C : ℕ) (e : (ℕ × ℕ) × ℤ) : ℤ × ℤ := (((e.1.1 : ℕ) : ℤ) - C, ((e.1.2 : ℕ) : ℤ) - C)

/-- `Σ_e m_e trig_p(k_e · φ)`. -/
def spSum (p : Bool) (C : ℕ) (es : List ((ℕ × ℕ) × ℤ)) (φ : Fin 2 → ℝ) : ℝ :=
  (es.map fun e => (e.2 : ℝ) * trig p (kdot (spMode C e) φ)).sum

/-- The weighted norm `Σ_e |k_{e,b}| |m_e|`. -/
def spW (C : ℕ) (es : List ((ℕ × ℕ) × ℤ)) (b : Fin 2) : ℕ :=
  (es.map fun e => (kc (spMode C e) b).natAbs * e.2.natAbs).sum

/-- The sum of the mantissas of mode `0`. -/
def spZ0 (C : ℕ) (es : List ((ℕ × ℕ) × ℤ)) : ℤ :=
  ((es.filter fun e => e.1 == (C, C)).map (·.2)).sum

/-- `Σ |m|` over the entries of nonzero mode. -/
def spNZ (C : ℕ) (es : List ((ℕ × ℕ) × ℤ)) : ℕ :=
  ((es.filter fun e => !(e.1 == (C, C))).map (·.2.natAbs)).sum

theorem hasFDerivAt_spSum (p : Bool) (C : ℕ) (es : List ((ℕ × ℕ) × ℤ)) (φ : Fin 2 → ℝ) :
    HasFDerivAt (spSum p C es)
      ((es.map fun e => ((e.2 : ℝ) * ((psgn p : ℝ) * trig (!p) (kdot (spMode C e) φ))) •
        kdotL (spMode C e)).sum) φ := by
  induction es with
  | nil =>
    have h0 : spSum p C [] = fun _ => 0 := by funext φ; simp [spSum]
    rw [h0]; simpa using hasFDerivAt_const (0 : ℝ) φ
  | cons e es ih =>
    have heq : spSum p C (e :: es) =
        fun φ => (e.2 : ℝ) * trig p (kdot (spMode C e) φ) + spSum p C es φ := by
      funext φ; simp [spSum]
    rw [heq]
    simp only [List.map_cons, List.sum_cons]
    have h := ((hasDerivAt_trig p (kdot (spMode C e) φ)).comp_hasFDerivAt φ
      (hasFDerivAt_kdot (spMode C e) φ)).const_mul (e.2 : ℝ)
    rw [smul_smul] at h
    exact h.add ih

theorem abs_fderiv_spSum_le (p : Bool) (C : ℕ) (es : List ((ℕ × ℕ) × ℤ)) (φ : Fin 2 → ℝ)
    (b : Fin 2) : |fderiv ℝ (spSum p C es) φ (Pi.single b 1)| ≤ (spW C es b : ℝ) := by
  rw [(hasFDerivAt_spSum p C es φ).fderiv, clm_list_sum_apply', spW, Nat.cast_list_sum,
    List.map_map]
  refine abs_list_sum_le es _ _ fun e _ => ?_
  rw [_root_.smul_apply, smul_eq_mul, kdotL_single]
  simp only [Function.comp_apply, Nat.cast_mul, Nat.cast_natAbs]
  rw [abs_mul, abs_mul, abs_mul]
  have h1 := abs_trig_le (!p) (kdot (spMode C e) φ)
  have h2 : |((psgn p : ℤ) : ℝ)| = 1 := by cases p <;> simp [psgn]
  rw [h2, one_mul]
  push_cast
  calc |(e.2 : ℝ)| * |trig (!p) (kdot (spMode C e) φ)| * |(kc (spMode C e) b : ℝ)|
      ≤ |(e.2 : ℝ)| * 1 * |(kc (spMode C e) b : ℝ)| := by gcongr
    _ = _ := by ring

theorem abs_spSum_sub_le (C : ℕ) (es : List ((ℕ × ℕ) × ℤ)) (φ : Fin 2 → ℝ) :
    |spSum false C es φ - (spZ0 C es : ℝ)| ≤ (spNZ C es : ℝ) := by
  induction es with
  | nil => simp [spSum, spZ0, spNZ]
  | cons e es ih =>
    by_cases h : e.1 = (C, C)
    · have hk : spMode C e = (0, 0) := by simp [spMode, h]
      have e1 : spSum false C (e :: es) φ = (e.2 : ℝ) + spSum false C es φ := by
        simp [spSum, hk, kdot_zero, trig]
      have e2 : spZ0 C (e :: es) = e.2 + spZ0 C es := by simp [spZ0, h]
      have e3 : spNZ C (e :: es) = spNZ C es := by simp [spNZ, h]
      rw [e1, e2, e3]; push_cast
      calc |(e.2 : ℝ) + spSum false C es φ - ((e.2 : ℝ) + (spZ0 C es : ℝ))|
          = |spSum false C es φ - (spZ0 C es : ℝ)| := by ring_nf
        _ ≤ _ := ih
    · have e1 : spSum false C (e :: es) φ =
          (e.2 : ℝ) * trig false (kdot (spMode C e) φ) + spSum false C es φ := by simp [spSum]
      have e2 : spZ0 C (e :: es) = spZ0 C es := by simp [spZ0, h]
      have e3 : spNZ C (e :: es) = e.2.natAbs + spNZ C es := by simp [spNZ, h]
      rw [e1, e2, e3]; push_cast
      have ht := abs_trig_le false (kdot (spMode C e) φ)
      calc |(e.2 : ℝ) * trig false (kdot (spMode C e) φ) + spSum false C es φ - (spZ0 C es : ℝ)|
          ≤ |(e.2 : ℝ) * trig false (kdot (spMode C e) φ)| +
              |spSum false C es φ - (spZ0 C es : ℝ)| := by
            rw [add_sub_assoc]; exact abs_add_le _ _
        _ ≤ |(e.2 : ℝ)| * 1 + (spNZ C es : ℝ) := by
            rw [abs_mul]; gcongr
        _ = _ := by rw [mul_one, Nat.cast_natAbs, Int.cast_abs]

namespace SpD

theorem eval_fun_eq {w S : ℕ} {d : SpD} (h : d.ok S = true) :
    (d.opd w S).eval S = fun φ => (d.q : ℝ) * spSum d.par d.C d.es φ := by
  funext φ
  rw [eval_eq h]
  rfl

theorem differentiable_eval (w S : ℕ) (d : SpD) : Differentiable ℝ ((d.opd w S).eval S) :=
  Opd.differentiable_eval S _

theorem eval_add_two_pi (w S : ℕ) (d : SpD) (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ) :
    (d.opd w S).eval S (φ + fun a => 2 * Real.pi * m a) = (d.opd w S).eval S φ := by
  simp only [Opd.eval, evalK_add_two_pi]

theorem abs_eval_le' {w S : ℕ} {d : SpD} (h : d.ok S = true) (φ : Fin 2 → ℝ) :
    |(d.opd w S).eval S φ| ≤ |(d.q : ℝ)| * d.l1E :=
  Opd.abs_eval_le (w := w) (l1_list_le h) φ

theorem abs_fderiv_eval_le {w S : ℕ} {d : SpD} (h : d.ok S = true) (φ : Fin 2 → ℝ) (b : Fin 2) :
    |fderiv ℝ ((d.opd w S).eval S) φ (Pi.single b 1)| ≤ |(d.q : ℝ)| * spW d.C d.es b := by
  rw [eval_fun_eq h]
  have hd := (hasFDerivAt_spSum d.par d.C d.es φ).differentiableAt
  rw [fderiv_const_mul hd, _root_.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_fderiv_spSum_le _ _ _ _ _) (abs_nonneg _)

/-- For even parity: `|eval - κ| ≤ |q m₀ - κ| + |q| Σ_{k ≠ 0} |m|`. -/
theorem abs_eval_sub_le {w S : ℕ} {d : SpD} (h : d.ok S = true) (hp : d.par = false) (κ : ℝ)
    (φ : Fin 2 → ℝ) :
    |(d.opd w S).eval S φ - κ| ≤ |(d.q : ℝ) * spZ0 d.C d.es - κ| + |(d.q : ℝ)| * spNZ d.C d.es := by
  rw [eval_fun_eq h, hp]
  have h1 := abs_spSum_sub_le d.C d.es φ
  calc |(d.q : ℝ) * spSum false d.C d.es φ - κ|
      = |((d.q : ℝ) * spZ0 d.C d.es - κ) +
          (d.q : ℝ) * (spSum false d.C d.es φ - spZ0 d.C d.es)| := by
        ring_nf
    _ ≤ |(d.q : ℝ) * spZ0 d.C d.es - κ| +
          |(d.q : ℝ)| * |spSum false d.C d.es φ - spZ0 d.C d.es| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ _ := by gcongr

end SpD

end KAM.EffectiveStability.Tube

end
