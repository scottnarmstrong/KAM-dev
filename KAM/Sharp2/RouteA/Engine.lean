/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.Engine.Schedule
public import KAM.Sharp.Engine.Limit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The stage engine of route A

Blueprint `bp:p2s2:engine` for the additive step. The normalised error is
`x_s = ε_s/(γ⁴ δ_s^{2a})`, `a = 2κ`, with the recurrence `x_{s+1} = 2^{2a} C_{E,s} x_s²`
(audit finding F5: route A has its own normalisation, `2^{4κ}`, not route B's `2^{κ+1}`); this is
`engine_A` of `scripts/apost_sharp/thresholds_v2.py`.

The constants depend on the stage, are constant from the stage `kp` on, and the increments of a cap
`i` are `ϱ_{i,s} ε_s/(γ² δ_s^{a+j_i})`. `RunData` holds (J1)–(J3): the prefix conditions, the tail
conditions **at entry** with downward closure of the conditions on nonnegative errors, the tail decay
and the cap sums, at a majorant `X⋆` of the initial normalised error (audit finding F2).

* `epsA`, `xA`: the errors and the majorising recursion;
* `sumA`: the sums of (J3), with `γ̄²`;
* `SchemeA.run`: the iteration, by induction;
* `SchemeA.limit`: the limit torus.
-/

@[expose] public noncomputable section

open Filter Topology
open KAM.Sharp.Engine

namespace KAM.Sharp2.RouteA

/-- The constants of one stage. -/
structure StageA (k : ℕ) where
  CE : ℝ
  CD : ℝ
  Cp : ℝ
  rate : Fin k → ℝ

/-- `ε₀ = e`, `ε_{s+1} = C_{E,s} ε_s²/(γ⁴ δ_s^{2a})`. -/
def epsA (a lam ρ ρinf γ : ℝ) (CE : ℕ → ℝ) (e : ℝ) : ℕ → ℝ
  | 0 => e
  | s + 1 => CE s * epsA a lam ρ ρinf γ CE e s ^ 2 / (γ ^ 4 * deltaSeq lam ρ ρinf s ^ (2 * a))

/-- `x₀ = X₀`, `x_{s+1} = 2^{2a} C_{E,s} x_s²`. -/
def xA (a : ℝ) (CE : ℕ → ℝ) (X₀ : ℝ) : ℕ → ℝ
  | 0 => X₀
  | s + 1 => 2 ^ (2 * a) * CE s * xA a CE X₀ s ^ 2

/-- The sum of (J3) for a rate `c` with weight exponent `2a - b`: the exact prefix, then twice the
tail term. -/
def sumA (a lam ρ ρinf γb : ℝ) (x c : ℕ → ℝ) (b : ℝ) (kp : ℕ) : ℝ :=
  (∑ t ∈ Finset.range kp, c t * x t * (γb ^ 2 * deltaSeq lam ρ ρinf t ^ (2 * a - b))) +
    2 * c kp * x kp * (γb ^ 2 * deltaSeq lam ρ ρinf kp ^ (2 * a - b))

section Sequences

variable {a lam ρ ρinf γ γb : ℝ} {CE : ℕ → ℝ} {e X₀ : ℝ}

theorem epsA_nonneg (hCE : ∀ s, 0 ≤ CE s) (hlam : 0 < lam) (hρ : ρinf < ρ) (he : 0 ≤ e) (s : ℕ) :
    0 ≤ epsA a lam ρ ρinf γ CE e s := by
  induction s with
  | zero => exact he
  | succ s ih =>
    have hδ := (deltaSeq_pos hlam hρ s).le
    have := hCE s
    simp only [epsA]
    positivity

theorem xA_nonneg (ha : 0 ≤ X₀) (hCE : ∀ s, 0 ≤ CE s) (s : ℕ) : 0 ≤ xA a CE X₀ s := by
  induction s with
  | zero => exact ha
  | succ s ih =>
    have := hCE s
    simp only [xA]
    positivity

/-- `x_s = ε_s/(γ⁴ δ_s^{2a}) ≤ xA X₀ s`. -/
theorem eps_div_le_xA (hCE : ∀ s, 0 ≤ CE s) (hlam : 0 < lam) (hρ : ρinf < ρ) (hγ : 0 < γ)
    (he : 0 ≤ e) (hX : e / (γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a)) ≤ X₀) (s : ℕ) :
    epsA a lam ρ ρinf γ CE e s / (γ ^ 4 * deltaSeq lam ρ ρinf s ^ (2 * a)) ≤ xA a CE X₀ s := by
  induction s with
  | zero => simpa [epsA, xA, deltaSeq] using hX
  | succ s ih =>
    have hδ := deltaSeq_pos hlam hρ s
    have hε := epsA_nonneg (a := a) (γ := γ) hCE hlam hρ he s
    have hp : 0 < deltaSeq lam ρ ρinf s ^ (2 * a) := Real.rpow_pos_of_pos hδ _
    have hsucc : deltaSeq lam ρ ρinf (s + 1) ^ (2 * a) =
        deltaSeq lam ρ ρinf s ^ (2 * a) / 2 ^ (2 * a) := by
      rw [deltaSeq_succ, Real.div_rpow hδ.le (by norm_num)]
    have h2 : (0 : ℝ) < 2 ^ (2 * a) := Real.rpow_pos_of_pos two_pos _
    have e1 : epsA a lam ρ ρinf γ CE e (s + 1) / (γ ^ 4 * deltaSeq lam ρ ρinf (s + 1) ^ (2 * a)) =
        2 ^ (2 * a) * CE s *
          (epsA a lam ρ ρinf γ CE e s / (γ ^ 4 * deltaSeq lam ρ ρinf s ^ (2 * a))) ^ 2 := by
      simp only [epsA]
      rw [hsucc]
      field_simp
    rw [e1]
    simp only [xA]
    have hnn : 0 ≤ epsA a lam ρ ρinf γ CE e s / (γ ^ 4 * deltaSeq lam ρ ρinf s ^ (2 * a)) := by
      positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn ih 2)
      (mul_nonneg h2.le (hCE s))

/-- The tail: `xA` is at most its value at `kp` from `kp` on. -/
theorem xA_tail_le {kp : ℕ} (hX : 0 ≤ X₀) (hCE : ∀ s, 0 ≤ CE s) (ht : ∀ s, kp ≤ s → CE s = CE kp)
    (hJ2 : 2 ^ (2 * a) * CE kp * xA a CE X₀ kp ≤ 1) (t : ℕ) :
    xA a CE X₀ (kp + t) ≤ xA a CE X₀ kp := by
  have h0 := xA_nonneg (a := a) hX hCE
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    rw [← add_assoc]
    simp only [xA]
    rw [ht (kp + t) (by omega)]
    have hc : 0 ≤ 2 ^ (2 * a) * CE kp :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hCE kp)
    calc 2 ^ (2 * a) * CE kp * xA a CE X₀ (kp + t) ^ 2
        = (2 ^ (2 * a) * CE kp * xA a CE X₀ (kp + t)) * xA a CE X₀ (kp + t) := by ring
      _ ≤ (2 ^ (2 * a) * CE kp * xA a CE X₀ kp) * xA a CE X₀ (kp + t) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ih hc) (h0 _)
      _ ≤ 1 * xA a CE X₀ (kp + t) := mul_le_mul_of_nonneg_right hJ2 (h0 _)
      _ ≤ xA a CE X₀ kp := by rw [one_mul]; exact ih

/-- `xA` is superlinear in the initial value: `xA (t X) s ≤ t xA X s`, `0 ≤ t ≤ 1`. -/
theorem xA_scale {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hX : 0 ≤ X₀) (hCE : ∀ s, 0 ≤ CE s) (s : ℕ) :
    xA a CE (t * X₀) s ≤ t * xA a CE X₀ s := by
  induction s with
  | zero => exact le_rfl
  | succ s ih =>
    have h0 := xA_nonneg (a := a) (mul_nonneg ht0 hX) hCE s
    have h1 := xA_nonneg (a := a) hX hCE s
    simp only [xA]
    have hc : 0 ≤ 2 ^ (2 * a) * CE s := mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hCE s)
    have hsq : xA a CE (t * X₀) s ^ 2 ≤ t * xA a CE X₀ s ^ 2 := by
      calc xA a CE (t * X₀) s ^ 2 ≤ (t * xA a CE X₀ s) ^ 2 := pow_le_pow_left₀ h0 ih 2
        _ = t ^ 2 * xA a CE X₀ s ^ 2 := by ring
        _ ≤ t * xA a CE X₀ s ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            nlinarith
    calc _ ≤ 2 ^ (2 * a) * CE s * (t * xA a CE X₀ s ^ 2) := mul_le_mul_of_nonneg_left hsq hc
      _ = _ := by ring

/-- `sumA` scales with the initial value. -/
theorem sumA_scale {t b : ℝ} {c : ℕ → ℝ} {kp : ℕ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hX : 0 ≤ X₀)
    (hCE : ∀ s, 0 ≤ CE s) (hc : ∀ s, 0 ≤ c s) (hlam : 0 < lam) (hρ : ρinf < ρ) :
    sumA a lam ρ ρinf γb (xA a CE (t * X₀)) c b kp ≤ t * sumA a lam ρ ρinf γb (xA a CE X₀) c b kp := by
  have hw : ∀ s, 0 ≤ γb ^ 2 * deltaSeq lam ρ ρinf s ^ (2 * a - b) := fun s =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (deltaSeq_pos hlam hρ s).le _)
  have hterm : ∀ s, c s * xA a CE (t * X₀) s * (γb ^ 2 * deltaSeq lam ρ ρinf s ^ (2 * a - b)) ≤
      t * (c s * xA a CE X₀ s * (γb ^ 2 * deltaSeq lam ρ ρinf s ^ (2 * a - b))) := fun s => by
    calc _ ≤ c s * (t * xA a CE X₀ s) * (γb ^ 2 * deltaSeq lam ρ ρinf s ^ (2 * a - b)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (xA_scale ht0 ht1 hX hCE s) (hc s))
            (hw s)
      _ = _ := by ring
  unfold sumA
  rw [mul_add, Finset.mul_sum]
  refine add_le_add (Finset.sum_le_sum fun s _ => hterm s) ?_
  have := hterm kp
  linarith

/-- `sumA` at `γ̄ = γ` is `γ²` times `sumA` at `1`. -/
theorem sumA_gamma (a lam ρ ρinf γ : ℝ) (x c : ℕ → ℝ) (b : ℝ) (kp : ℕ) :
    sumA a lam ρ ρinf γ x c b kp = γ ^ 2 * sumA a lam ρ ρinf 1 x c b kp := by
  unfold sumA
  rw [mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    ring
  · ring

/-- `δ_{kp+t}^q ≤ δ_kp^q 2^{-t}` for `q ≥ 1`. -/
theorem deltaSeq_rpow_tail {q : ℝ} (hq : 1 ≤ q) (hlam : 0 < lam) (hρ : ρinf < ρ) (kp t : ℕ) :
    deltaSeq lam ρ ρinf (kp + t) ^ q ≤ deltaSeq lam ρ ρinf kp ^ q * (1 / 2 : ℝ) ^ t := by
  have hd0 := (delta0_pos hlam hρ).le
  have hδ := deltaSeq_pos hlam hρ kp
  rw [deltaSeq_rpow hd0 q (kp + t), deltaSeq_rpow hd0 q kp]
  have e : (2 : ℝ) ^ (-(q * ((kp + t : ℕ) : ℝ))) =
      (2 : ℝ) ^ (-(q * (kp : ℝ))) * (2 : ℝ) ^ (-(q * (t : ℝ))) := by
    rw [← Real.rpow_add two_pos]
    congr 1
    push_cast
    ring
  have e2 : (2 : ℝ) ^ (-(q * (t : ℝ))) ≤ (1 / 2 : ℝ) ^ t := by
    have : (1 / 2 : ℝ) ^ t = (2 : ℝ) ^ (-(t : ℝ)) := by
      rw [Real.rpow_neg zero_le_two, Real.rpow_natCast, one_div, inv_pow]
    rw [this]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    nlinarith
  rw [e]
  have h1 : 0 ≤ (2 : ℝ) ^ (-(q * (kp : ℝ))) * delta0 lam ρ ρinf ^ q :=
    mul_nonneg (Real.rpow_nonneg zero_le_two _) (Real.rpow_nonneg hd0 _)
  calc (2 : ℝ) ^ (-(q * (kp : ℝ))) * (2 : ℝ) ^ (-(q * (t : ℝ))) * delta0 lam ρ ρinf ^ q
      = ((2 : ℝ) ^ (-(q * (kp : ℝ))) * delta0 lam ρ ρinf ^ q) * (2 : ℝ) ^ (-(q * (t : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left e2 h1

/-- The hypotheses on the data of a term `c_t ε_t/(γ² δ_t^b)`. -/
structure TermHyp (a lam ρ ρinf γ γb : ℝ) (CE : ℕ → ℝ) (e X₀ : ℝ) (kp : ℕ) : Prop where
  hCE : ∀ s, 0 ≤ CE s
  hlam : 0 < lam
  hρ : ρinf < ρ
  hγ : 0 < γ
  hγb : γ ≤ γb
  he : 0 ≤ e
  hX0 : 0 ≤ X₀
  hX : e / (γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a)) ≤ X₀
  ht : ∀ s, kp ≤ s → CE s = CE kp
  hJ2 : 2 ^ (2 * a) * CE kp * xA a CE X₀ kp ≤ 1

/-- `ε_t/(γ² δ_t^b) ≤ xA t · γ̄² δ_t^{2a-b}`. -/
theorem TermHyp.term_le {kp : ℕ} (H : TermHyp a lam ρ ρinf γ γb CE e X₀ kp) (b : ℝ) (t : ℕ) :
    epsA a lam ρ ρinf γ CE e t / (γ ^ 2 * deltaSeq lam ρ ρinf t ^ b) ≤
      xA a CE X₀ t * (γb ^ 2 * deltaSeq lam ρ ρinf t ^ (2 * a - b)) := by
  have hδ := deltaSeq_pos H.hlam H.hρ t
  have hγ := H.hγ
  have hx := eps_div_le_xA (s := t) H.hCE H.hlam H.hρ hγ H.he H.hX
  have hp : 0 < deltaSeq lam ρ ρinf t ^ b := Real.rpow_pos_of_pos hδ _
  have hq : 0 < deltaSeq lam ρ ρinf t ^ (2 * a - b) := Real.rpow_pos_of_pos hδ _
  have e1 : deltaSeq lam ρ ρinf t ^ (2 * a) =
      deltaSeq lam ρ ρinf t ^ (2 * a - b) * deltaSeq lam ρ ρinf t ^ b := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  have e2 : epsA a lam ρ ρinf γ CE e t / (γ ^ 2 * deltaSeq lam ρ ρinf t ^ b) =
      epsA a lam ρ ρinf γ CE e t / (γ ^ 4 * deltaSeq lam ρ ρinf t ^ (2 * a)) *
        (γ ^ 2 * deltaSeq lam ρ ρinf t ^ (2 * a - b)) := by
    rw [e1]
    field_simp
  rw [e2]
  have hnn : 0 ≤ xA a CE X₀ t := xA_nonneg H.hX0 H.hCE t
  exact mul_le_mul hx (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hγ.le H.hγb 2) hq.le)
    (by positivity) hnn

/-- The tail terms decay geometrically. -/
theorem TermHyp.term_tail {kp : ℕ} (H : TermHyp a lam ρ ρinf γ γb CE e X₀ kp) {b : ℝ}
    (hb : b ≤ 2 * a - 1) (t : ℕ) :
    epsA a lam ρ ρinf γ CE e (kp + t) / (γ ^ 2 * deltaSeq lam ρ ρinf (kp + t) ^ b) ≤
      xA a CE X₀ kp * (γb ^ 2 * deltaSeq lam ρ ρinf kp ^ (2 * a - b)) * (1 / 2 : ℝ) ^ t := by
  have h1 := H.term_le b (kp + t)
  have hn0 : 0 ≤ xA a CE X₀ (kp + t) := xA_nonneg H.hX0 H.hCE _
  have hk0 : 0 ≤ xA a CE X₀ kp := xA_nonneg H.hX0 H.hCE _
  have h2 := xA_tail_le H.hX0 H.hCE H.ht H.hJ2 t
  have h3 := deltaSeq_rpow_tail (q := 2 * a - b) (by linarith) H.hlam H.hρ kp t
  have hg : 0 ≤ γb ^ 2 := sq_nonneg _
  have hdn : 0 ≤ deltaSeq lam ρ ρinf (kp + t) ^ (2 * a - b) :=
    Real.rpow_nonneg (deltaSeq_pos H.hlam H.hρ _).le _
  calc _ ≤ xA a CE X₀ (kp + t) * (γb ^ 2 * deltaSeq lam ρ ρinf (kp + t) ^ (2 * a - b)) := h1
    _ ≤ xA a CE X₀ kp * (γb ^ 2 * (deltaSeq lam ρ ρinf kp ^ (2 * a - b) * (1 / 2 : ℝ) ^ t)) :=
        mul_le_mul h2 (mul_le_mul_of_nonneg_left h3 hg) (by positivity) hk0
    _ = _ := by ring

/-- Terms with a rate `c` constant from `kp` on: nonnegative, summable, with sum at most `sumA`. -/
theorem TermHyp.sum_le {kp : ℕ} (H : TermHyp a lam ρ ρinf γ γb CE e X₀ kp) {c : ℕ → ℝ}
    (hc : ∀ s, 0 ≤ c s) (hct : ∀ s, kp ≤ s → c s = c kp) {b : ℝ} (hb : b ≤ 2 * a - 1) :
    (∀ s, 0 ≤ c s * epsA a lam ρ ρinf γ CE e s / (γ ^ 2 * deltaSeq lam ρ ρinf s ^ b)) ∧
    Summable (fun s => c s * epsA a lam ρ ρinf γ CE e s / (γ ^ 2 * deltaSeq lam ρ ρinf s ^ b)) ∧
    ∀ s, ∑ t ∈ Finset.range s,
        c t * epsA a lam ρ ρinf γ CE e t / (γ ^ 2 * deltaSeq lam ρ ρinf t ^ b) ≤
      sumA a lam ρ ρinf γb (xA a CE X₀) c b kp := by
  set f := fun s => c s * epsA a lam ρ ρinf γ CE e s / (γ ^ 2 * deltaSeq lam ρ ρinf s ^ b) with hf
  have hnn : ∀ s, 0 ≤ f s := fun s => by
    have := epsA_nonneg (a := a) (γ := γ) H.hCE H.hlam H.hρ H.he s
    have := Real.rpow_pos_of_pos (deltaSeq_pos H.hlam H.hρ s) b
    have := hc s
    have := H.hγ
    simp only [hf]
    positivity
  set A := c kp * xA a CE X₀ kp * (γb ^ 2 * deltaSeq lam ρ ρinf kp ^ (2 * a - b)) with hA
  have hA0 : 0 ≤ A := by
    have := xA_nonneg (a := a) H.hX0 H.hCE kp
    have := Real.rpow_nonneg (deltaSeq_pos H.hlam H.hρ kp).le (2 * a - b)
    have := hc kp
    positivity
  have htail : ∀ t, f (kp + t) ≤ A * (1 / 2 : ℝ) ^ t := fun t => by
    have h1 := H.term_tail hb t
    simp only [hf]
    rw [hct (kp + t) (by omega), mul_div_assoc]
    calc _ ≤ c kp * (xA a CE X₀ kp * (γb ^ 2 * deltaSeq lam ρ ρinf kp ^ (2 * a - b)) *
          (1 / 2 : ℝ) ^ t) := mul_le_mul_of_nonneg_left h1 (hc kp)
      _ = _ := by rw [hA]; ring
  have hgeo : Summable (fun t : ℕ => A * (1 / 2 : ℝ) ^ t) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hsum : Summable f := by
    rw [← summable_nat_add_iff kp]
    refine Summable.of_nonneg_of_le (fun t => hnn _) (fun t => ?_) hgeo
    rw [add_comm t kp]
    exact htail t
  refine ⟨hnn, hsum, fun s => ?_⟩
  have h1 : ∑ t ∈ Finset.range s, f t ≤ ∑ t ∈ Finset.range (kp + s), f t :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (by omega)) (fun t _ _ => hnn t)
  have h2 : ∑ t ∈ Finset.range kp, f t ≤
      ∑ t ∈ Finset.range kp, c t * xA a CE X₀ t *
        (γb ^ 2 * deltaSeq lam ρ ρinf t ^ (2 * a - b)) := by
    refine Finset.sum_le_sum fun t _ => ?_
    simp only [hf]
    rw [mul_div_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (H.term_le b t) (hc t)
  have h3 : ∑ i ∈ Finset.range s, f (kp + i) ≤ 2 * A := by
    calc _ ≤ ∑ i ∈ Finset.range s, A * (1 / 2 : ℝ) ^ i := Finset.sum_le_sum fun i _ => htail i
      _ = A * ∑ i ∈ Finset.range s, (1 / 2 : ℝ) ^ i := by rw [Finset.mul_sum]
      _ ≤ A * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le s) hA0
      _ = 2 * A := by ring
  rw [Finset.sum_range_add] at h1
  unfold sumA
  have e2 : 2 * c kp * xA a CE X₀ kp * (γb ^ 2 * deltaSeq lam ρ ρinf kp ^ (2 * a - b)) = 2 * A := by
    rw [hA]; ring
  rw [e2]
  linarith

end Sequences

/-- An abstract additive scheme: states, torus, scalar parameter, stage-indexed admissibility
`Adm s ε m x` (error `ε`, cap values `m`) and step `step s x`. -/
structure SchemeA (n k : ℕ) (α : Type*) where
  tor : α → (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)
  par : α → ℝ
  Adm : ℕ → ℝ → (Fin k → ℝ) → α → Prop
  step : ℕ → α → α

variable {n k : ℕ} {α : Type*}

/-- The iterates. -/
def SchemeA.iter (S : SchemeA n k α) (x₀ : α) : ℕ → α
  | 0 => x₀
  | s + 1 => S.step s (S.iter x₀ s)

/-- (N1), (N2) at each stage. Each instance proves it from the additive step. -/
structure SchemeA.IsNewton (S : SchemeA n k α) (a lam ρ ρinf γ : ℝ) (C : ℕ → StageA k)
    (j : Fin k → ℕ) (Cond : ℕ → ℝ → Prop) (σ : Fin k → ℝ) : Prop where
  adm : ∀ {s : ℕ} {ε : ℝ} {m : Fin k → ℝ} {x : α}, S.Adm s ε m x →
    0 ≤ ε ∧ DifferentiableOn ℂ (S.tor x) (complexStrip n (rSeq lam ρ ρinf s)) ∧
      IsPrimaryOnStrip (S.tor x) (rSeq lam ρ ρinf s) ∧ IsRealOnReals (S.tor x)
  step : ∀ {s : ℕ} {ε : ℝ} {m : Fin k → ℝ} {x : α}, S.Adm s ε m x →
    Cond s (ε / (γ ^ 4 * deltaSeq lam ρ ρinf s ^ (2 * a))) →
    (∀ i, m i + (C s).rate i * ε / (γ ^ 2 * deltaSeq lam ρ ρinf s ^ (a + (j i : ℝ))) ≤ σ i) →
    S.Adm (s + 1) ((C s).CE * ε ^ 2 / (γ ^ 4 * deltaSeq lam ρ ρinf s ^ (2 * a)))
        (fun i => m i + (C s).rate i * ε / (γ ^ 2 * deltaSeq lam ρ ρinf s ^ (a + (j i : ℝ))))
        (S.step s x) ∧
      (∀ θ ∈ complexStrip n (rSeq lam ρ ρinf (s + 1)),
        ‖S.tor (S.step s x) θ - S.tor x θ‖ ≤
          (C s).CD * ε / (γ ^ 2 * deltaSeq lam ρ ρinf s ^ a) ∧
        ‖fderiv ℂ (S.tor (S.step s x)) θ - fderiv ℂ (S.tor x) θ‖ ≤
          n * (C s).CD * ε / (γ ^ 2 * deltaSeq lam ρ ρinf s ^ (a + 1))) ∧
      |S.par (S.step s x) - S.par x| ≤ (C s).Cp * ε / (γ ^ 2 * deltaSeq lam ρ ρinf s ^ a)

/-- (J1)–(J3) at the majorant `Xs` of the initial normalised error. -/
structure RunData (a lam ρ ρinf γb : ℝ) (C : ℕ → StageA k) (j : Fin k → ℕ) (Cond : ℕ → ℝ → Prop)
    (σ m₀ : Fin k → ℝ) (kp : ℕ) (Xs : ℝ) : Prop where
  two_le_a : 2 ≤ a
  j_le : ∀ i, j i ≤ 1
  CE_nonneg : ∀ s, 0 ≤ (C s).CE
  CD_nonneg : ∀ s, 0 ≤ (C s).CD
  Cp_nonneg : ∀ s, 0 ≤ (C s).Cp
  rate_nonneg : ∀ s i, 0 ≤ (C s).rate i
  tail : ∀ s, kp ≤ s → C s = C kp
  Xs_nonneg : 0 ≤ Xs
  down : ∀ s {x y : ℝ}, 0 ≤ x → x ≤ y → Cond s y → Cond s x
  J1 : ∀ s < kp, Cond s (xA a (fun s => (C s).CE) Xs s)
  J1t : ∀ s, kp ≤ s → Cond s (xA a (fun s => (C s).CE) Xs kp)
  J2 : 2 ^ (2 * a) * (C kp).CE * xA a (fun s => (C s).CE) Xs kp ≤ 1
  J3 : ∀ i, m₀ i + sumA a lam ρ ρinf γb (xA a (fun s => (C s).CE) Xs) (fun s => (C s).rate i)
    (a + (j i : ℝ)) kp ≤ σ i

variable {S : SchemeA n k α} {a lam ρ ρinf γ γb : ℝ} {C : ℕ → StageA k} {j : Fin k → ℕ}
  {Cond : ℕ → ℝ → Prop} {σ m₀ : Fin k → ℝ} {kp : ℕ} {Xs e : ℝ} {x₀ : α}

/-- The errors of a run. -/
abbrev runEps (a lam ρ ρinf γ : ℝ) (C : ℕ → StageA k) (e : ℝ) : ℕ → ℝ :=
  epsA a lam ρ ρinf γ (fun s => (C s).CE) e

/-- The cap values of a run. -/
def runCap (a lam ρ ρinf γ : ℝ) (C : ℕ → StageA k) (j : Fin k → ℕ) (m₀ : Fin k → ℝ) (e : ℝ)
    (s : ℕ) : Fin k → ℝ := fun i => m₀ i + ∑ t ∈ Finset.range s,
  (C t).rate i * runEps a lam ρ ρinf γ C e t / (γ ^ 2 * deltaSeq lam ρ ρinf t ^ (a + (j i : ℝ)))

namespace RunData

theorem termHyp (R : RunData a lam ρ ρinf γb C j Cond σ m₀ kp Xs) (hlam : 0 < lam) (hρ : ρinf < ρ)
    (hγ : 0 < γ) (hγb : γ ≤ γb) (he : 0 ≤ e)
    (hX : e / (γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a)) ≤ Xs) :
    TermHyp a lam ρ ρinf γ γb (fun s => (C s).CE) e Xs kp where
  hCE := R.CE_nonneg
  hlam := hlam
  hρ := hρ
  hγ := hγ
  hγb := hγb
  he := he
  hX0 := R.Xs_nonneg
  hX := hX
  ht := fun s hs => by rw [R.tail s hs]
  hJ2 := R.J2

/-- A rate that is constant from `kp` on, with `b ≤ 2a - 1`. -/
theorem sum_rate (R : RunData a lam ρ ρinf γb C j Cond σ m₀ kp Xs)
    (H : TermHyp a lam ρ ρinf γ γb (fun s => (C s).CE) e Xs kp) (i : Fin k) :
    (∀ s, 0 ≤ (C s).rate i * runEps a lam ρ ρinf γ C e s /
      (γ ^ 2 * deltaSeq lam ρ ρinf s ^ (a + (j i : ℝ)))) ∧
    ∀ s, ∑ t ∈ Finset.range s, (C t).rate i * runEps a lam ρ ρinf γ C e t /
        (γ ^ 2 * deltaSeq lam ρ ρinf t ^ (a + (j i : ℝ))) ≤
      sumA a lam ρ ρinf γb (xA a (fun s => (C s).CE) Xs) (fun s => (C s).rate i)
        (a + (j i : ℝ)) kp := by
  have hj : (j i : ℝ) ≤ 1 := by exact_mod_cast R.j_le i
  have ha := R.two_le_a
  obtain ⟨h1, -, h3⟩ := H.sum_le (c := fun s => (C s).rate i) (b := a + (j i : ℝ))
    (fun s => R.rate_nonneg s i) (fun s hs => by simp only [R.tail s hs]) (by linarith)
  exact ⟨h1, h3⟩

end RunData

/-- Blueprint `bp:p2s2:engine` for route A, the iteration: `x_s` is admissible at every stage, the
caps hold, and the increments are those of the stage. -/
theorem SchemeA.run (hS : S.IsNewton a lam ρ ρinf γ C j Cond σ)
    (R : RunData a lam ρ ρinf γb C j Cond σ m₀ kp Xs) (hlam : 0 < lam) (hρ : ρinf < ρ) (hγ : 0 < γ)
    (hγb : γ ≤ γb) (h0 : S.Adm 0 e m₀ x₀)
    (hX : e / (γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a)) ≤ Xs) :
    ∀ s : ℕ,
      S.Adm s (runEps a lam ρ ρinf γ C e s) (runCap a lam ρ ρinf γ C j m₀ e s) (S.iter x₀ s) ∧
      (∀ i, runCap a lam ρ ρinf γ C j m₀ e s i ≤ σ i) ∧
      (∀ θ ∈ complexStrip n (rSeq lam ρ ρinf (s + 1)),
        ‖S.tor (S.iter x₀ (s + 1)) θ - S.tor (S.iter x₀ s) θ‖ ≤
          (C s).CD * runEps a lam ρ ρinf γ C e s / (γ ^ 2 * deltaSeq lam ρ ρinf s ^ a) ∧
        ‖fderiv ℂ (S.tor (S.iter x₀ (s + 1))) θ - fderiv ℂ (S.tor (S.iter x₀ s)) θ‖ ≤
          n * (C s).CD * runEps a lam ρ ρinf γ C e s /
            (γ ^ 2 * deltaSeq lam ρ ρinf s ^ (a + 1))) ∧
      |S.par (S.iter x₀ (s + 1)) - S.par (S.iter x₀ s)| ≤
        (C s).Cp * runEps a lam ρ ρinf γ C e s / (γ ^ 2 * deltaSeq lam ρ ρinf s ^ a) := by
  have he : 0 ≤ e := (hS.adm h0).1
  have H := R.termHyp hlam hρ hγ hγb he hX
  have hsucc : ∀ s, runCap a lam ρ ρinf γ C j m₀ e (s + 1) = fun i =>
      runCap a lam ρ ρinf γ C j m₀ e s i + (C s).rate i * runEps a lam ρ ρinf γ C e s /
        (γ ^ 2 * deltaSeq lam ρ ρinf s ^ (a + (j i : ℝ))) := fun s => by
    funext i
    simp only [runCap, Finset.sum_range_succ]
    ring
  have hcap : ∀ s i, runCap a lam ρ ρinf γ C j m₀ e s i ≤ σ i := fun s i =>
    (add_le_add le_rfl ((R.sum_rate H i).2 s)).trans (R.J3 i)
  have hcond : ∀ s, Cond s (runEps a lam ρ ρinf γ C e s /
      (γ ^ 4 * deltaSeq lam ρ ρinf s ^ (2 * a))) := by
    intro s
    have hx := eps_div_le_xA (a := a) (CE := fun s => (C s).CE) (s := s) R.CE_nonneg hlam hρ hγ he hX
    have hnn : 0 ≤ runEps a lam ρ ρinf γ C e s / (γ ^ 4 * deltaSeq lam ρ ρinf s ^ (2 * a)) := by
      have := epsA_nonneg (a := a) (γ := γ) (CE := fun s => (C s).CE) R.CE_nonneg hlam hρ he s
      have := Real.rpow_pos_of_pos (deltaSeq_pos hlam hρ s) (2 * a)
      positivity
    rcases lt_or_ge s kp with hs | hs
    · exact R.down s hnn hx (R.J1 s hs)
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
      exact R.down _ hnn (hx.trans (xA_tail_le R.Xs_nonneg R.CE_nonneg H.ht R.J2 t))
        (R.J1t _ (by omega))
  have hstep := fun s (hs : S.Adm s (runEps a lam ρ ρinf γ C e s)
      (runCap a lam ρ ρinf γ C j m₀ e s) (S.iter x₀ s)) =>
    hS.step hs (hcond s) (fun i => by
      have := hcap (s + 1) i
      rw [hsucc] at this
      exact this)
  have key : ∀ s, S.Adm s (runEps a lam ρ ρinf γ C e s) (runCap a lam ρ ρinf γ C j m₀ e s)
      (S.iter x₀ s) := by
    intro s
    induction s with
    | zero =>
      have hm : runCap a lam ρ ρinf γ C j m₀ e 0 = m₀ := by funext i; simp [runCap]
      simpa [hm, runEps, epsA, SchemeA.iter] using h0
    | succ s ih =>
      have := (hstep s ih).1
      rw [hsucc]
      exact this
  intro s
  obtain ⟨-, hd, hp⟩ := hstep s (key s)
  exact ⟨key s, hcap s, hd, hp⟩

open Classical in
/-- `K_∞ = lim_s tor x_s` on `T_{ρ∞}`, `tor x₀` elsewhere. -/
def SchemeA.limTor (S : SchemeA n k α) (ρinf : ℝ) (x₀ : α) :
    (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) :=
  fun θ => if θ ∈ complexStrip n ρinf then
    limUnder atTop (fun s => S.tor (S.iter x₀ s) θ) else S.tor x₀ θ

/-- `p_∞ = lim_s par x_s`. -/
def SchemeA.limPar (S : SchemeA n k α) (x₀ : α) : ℝ :=
  limUnder atTop (fun s => S.par (S.iter x₀ s))

/-- Blueprint `bp:p2s2:engine` for route A, the limit: the closeness and the parameter change are
at most the sums of (J3) with the rates `C_ΔK` and `C_p`. -/
theorem SchemeA.limit (hS : S.IsNewton a lam ρ ρinf γ C j Cond σ)
    (R : RunData a lam ρ ρinf γb C j Cond σ m₀ kp Xs) (hlam : 0 < lam) (hρinf : 0 < ρinf)
    (hρ : ρinf < ρ) (hγ : 0 < γ) (hγb : γ ≤ γb) (h0 : S.Adm 0 e m₀ x₀)
    (hX : e / (γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a)) ≤ Xs) :
    TendstoUniformlyOn (fun s => S.tor (S.iter x₀ s)) (S.limTor ρinf x₀) atTop
        (complexStrip n ρinf) ∧
      TendstoUniformlyOn (fun s θ => fderiv ℂ (S.tor (S.iter x₀ s)) θ)
        (fderiv ℂ (S.limTor ρinf x₀)) atTop (complexStrip n ρinf) ∧
      DifferentiableOn ℂ (S.limTor ρinf x₀) (complexStrip n ρinf) ∧
      IsPrimaryOnStrip (S.limTor ρinf x₀) ρinf ∧ IsRealOnReals (S.limTor ρinf x₀) ∧
      (∀ θ ∈ complexStrip n ρinf, ‖S.limTor ρinf x₀ θ - S.tor x₀ θ‖ ≤
        sumA a lam ρ ρinf γb (xA a (fun s => (C s).CE) Xs) (fun s => (C s).CD) a kp) ∧
      (∀ θ ∈ complexStrip n ρinf, ‖S.limTor ρinf x₀ θ - S.tor x₀ θ‖ ≤
        (e / (γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a))) / Xs * (γ ^ 2 *
          sumA a lam ρ ρinf 1 (xA a (fun s => (C s).CE) Xs) (fun s => (C s).CD) a kp)) ∧
      Tendsto (fun s => S.par (S.iter x₀ s)) atTop (𝓝 (S.limPar x₀)) ∧
      |S.limPar x₀ - S.par x₀| ≤
        sumA a lam ρ ρinf γb (xA a (fun s => (C s).CE) Xs) (fun s => (C s).Cp) a kp ∧
      |S.limPar x₀ - S.par x₀| ≤
        (e / (γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a))) / Xs * (γ ^ 2 *
          sumA a lam ρ ρinf 1 (xA a (fun s => (C s).CE) Xs) (fun s => (C s).Cp) a kp) ∧
      Tendsto (runEps a lam ρ ρinf γ C e) atTop (𝓝 0) := by
  have he : 0 ≤ e := (hS.adm h0).1
  have H := R.termHyp hlam hρ hγ hγb he hX
  have ha := R.two_le_a
  have hit := SchemeA.run hS R hlam hρ hγ hγb h0 hX
  have hsch := schedule hlam hρinf hρ
  have hsub : ∀ s, complexStrip n ρinf ⊆ complexStrip n (rSeq lam ρ ρinf s) := fun s =>
    KAM.Apost.Triangular.strip_mono (hsch.2.2.2.2.1 s).le
  obtain ⟨hd0, hdsum, hdS⟩ := H.sum_le (c := fun s => (C s).CD) (b := a) R.CD_nonneg
    (fun s hs => by simp only [R.tail s hs]) (by linarith)
  obtain ⟨hk0, hksum, -⟩ := H.sum_le (c := fun s => n * (C s).CD) (b := a + 1)
    (fun s => mul_nonneg (Nat.cast_nonneg _) (R.CD_nonneg s))
    (fun s hs => by simp only [R.tail s hs]) (by linarith)
  obtain ⟨hp0, hpsum, hpS⟩ := H.sum_le (c := fun s => (C s).Cp) (b := a) R.Cp_nonneg
    (fun s hs => by simp only [R.tail s hs]) (by linarith)
  obtain ⟨-, hesum, -⟩ := H.sum_le (c := fun _ => 1) (b := 0) (fun _ => zero_le_one)
    (fun _ _ => rfl) (by linarith)
  have hdiff : ∀ s, ∀ θ ∈ complexStrip n ρinf,
      ‖S.tor (S.iter x₀ (s + 1)) θ - S.tor (S.iter x₀ s) θ‖ ≤
        (C s).CD * runEps a lam ρ ρinf γ C e s / (γ ^ 2 * deltaSeq lam ρ ρinf s ^ a) :=
    fun s θ hθ => ((hit s).2.2.1 θ (hsub (s + 1) hθ)).1
  have hddiff : ∀ s, ∀ θ ∈ complexStrip n ρinf,
      ‖fderiv ℂ (S.tor (S.iter x₀ (s + 1))) θ - fderiv ℂ (S.tor (S.iter x₀ s)) θ‖ ≤
        n * (C s).CD * runEps a lam ρ ρinf γ C e s /
          (γ ^ 2 * deltaSeq lam ρ ρinf s ^ (a + 1)) :=
    fun s θ hθ => ((hit s).2.2.1 θ (hsub (s + 1) hθ)).2
  have hhol : ∀ s, DifferentiableOn ℂ (S.tor (S.iter x₀ s)) (complexStrip n ρinf) :=
    fun s => (hS.adm (hit s).1).2.1.mono (hsub s)
  have hprim : ∀ s, IsPrimaryOnStrip (S.tor (S.iter x₀ s)) ρinf :=
    fun s θ hθ kk => (hS.adm (hit s).1).2.2.1 θ (hsub s hθ) kk
  have hreal : ∀ s, IsRealOnReals (S.tor (S.iter x₀ s)) :=
    fun s => (hS.adm (hit s).1).2.2.2
  obtain ⟨hconv, hpt, hLG⟩ := KAM.Apost.lim_k (Ks := fun s => S.tor (S.iter x₀ s))
    hdsum hdiff (L := S.limTor ρinf x₀)
    (fun θ hθ => by simp only [SchemeA.limTor, hθ, ite_true])
  obtain ⟨Λ, hΛ⟩ := KAM.Apost.lim_dk (Ks := fun s => S.tor (S.iter x₀ s)) hksum hddiff
  obtain ⟨hholo, hconvd⟩ := KAM.Apost.lim_holo (Ks := fun s => S.tor (S.iter x₀ s)) hhol hpt hΛ
  obtain ⟨hpr, hrr⟩ := KAM.Apost.lim_primary (Ks := fun s => S.tor (S.iter x₀ s))
    hρinf hpt hprim hreal
  have hclose : ∀ θ ∈ complexStrip n ρinf, ‖S.limTor ρinf x₀ θ - S.tor x₀ θ‖ ≤
      sumA a lam ρ ρinf γb (xA a (fun s => (C s).CE) Xs) (fun s => (C s).CD) a kp := fun θ hθ =>
    ((KAM.Apost.lim_close (Ks := fun s => S.tor (S.iter x₀ s)) hdsum hdiff hLG) θ hθ).trans
      (Real.tsum_le_of_sum_range_le hd0 hdS)
  obtain ⟨p, hp, hpb⟩ := converge_par (f := fun s => S.par (S.iter x₀ s)) hpsum
    (fun s => (hit s).2.2.2) (Real.tsum_le_of_sum_range_le hp0 hpS)
  have hlimP : S.limPar x₀ = p := hp.limUnder_eq
  -- the bounds proportional to `e`
  have hXpos : 0 < Xs ∨ e = 0 := by
    rcases R.Xs_nonneg.eq_or_lt with h | h
    · right
      have hD : 0 < γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a) :=
        mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos (delta0_pos hlam hρ) _)
      rw [← h] at hX
      have h1 := (div_le_iff₀ hD).1 hX
      linarith
    · exact Or.inl h
  have hprop : ∀ {c : ℕ → ℝ}, (∀ s, 0 ≤ c s) → (∀ s, kp ≤ s → c s = c kp) →
      ∑' s, c s * runEps a lam ρ ρinf γ C e s / (γ ^ 2 * deltaSeq lam ρ ρinf s ^ a) ≤
        (e / (γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a))) / Xs * (γ ^ 2 *
          sumA a lam ρ ρinf 1 (xA a (fun s => (C s).CE) Xs) c a kp) := by
    intro c hc hct
    have hD : 0 < γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a) :=
      mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos (delta0_pos hlam hρ) _)
    set X₁ := e / (γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a)) with hX₁
    have hX₁0 : 0 ≤ X₁ := div_nonneg he hD.le
    rcases hXpos with hpos | he0
    · set t := X₁ / Xs with ht
      have ht0 : 0 ≤ t := div_nonneg hX₁0 hpos.le
      have ht1 : t ≤ 1 := (div_le_one hpos).2 hX
      have hx1 : X₁ = t * Xs := by rw [ht]; field_simp
      have hJ2' : 2 ^ (2 * a) * (C kp).CE * xA a (fun s => (C s).CE) X₁ kp ≤ 1 := by
        rw [hx1]
        have h2 := xA_scale (a := a) ht0 ht1 R.Xs_nonneg R.CE_nonneg kp
        have h3 : 0 ≤ 2 ^ (2 * a) * (C kp).CE :=
          mul_nonneg (Real.rpow_nonneg (by norm_num) _) (R.CE_nonneg kp)
        have h4 : xA a (fun s => (C s).CE) Xs kp * t ≤ xA a (fun s => (C s).CE) Xs kp :=
          mul_le_of_le_one_right (xA_nonneg R.Xs_nonneg R.CE_nonneg kp) ht1
        calc _ ≤ 2 ^ (2 * a) * (C kp).CE * xA a (fun s => (C s).CE) Xs kp :=
              mul_le_mul_of_nonneg_left (h2.trans (by linarith)) h3
          _ ≤ 1 := R.J2
      have H' : TermHyp a lam ρ ρinf γ γ (fun s => (C s).CE) e X₁ kp :=
        { H with
          hγb := le_rfl
          hX0 := hX₁0
          hX := le_rfl
          hJ2 := hJ2' }
      obtain ⟨h0', -, hS'⟩ := H'.sum_le (c := c) (b := a) hc hct (by linarith)
      refine (Real.tsum_le_of_sum_range_le h0' hS').trans ?_
      rw [hx1, sumA_gamma a lam ρ ρinf γ]
      have := sumA_scale (a := a) (lam := lam) (ρ := ρ) (ρinf := ρinf) (γb := 1) (c := c) (b := a)
        (kp := kp) ht0 ht1 R.Xs_nonneg R.CE_nonneg hc hlam hρ
      calc _ ≤ γ ^ 2 * (t * sumA a lam ρ ρinf 1 (xA a (fun s => (C s).CE) Xs) c a kp) :=
            mul_le_mul_of_nonneg_left this (sq_nonneg _)
        _ = t * (γ ^ 2 * sumA a lam ρ ρinf 1 (xA a (fun s => (C s).CE) Xs) c a kp) := by ring
        _ = _ := rfl
    · have h00 : ∀ s, runEps a lam ρ ρinf γ C e s = 0 := fun s => by
        rw [he0]
        induction s with
        | zero => rfl
        | succ s ih =>
          simp only [runEps, epsA] at ih ⊢
          rw [ih]
          simp
      simp only [h00, mul_zero, zero_div, tsum_zero]
      have hX0 : X₁ = 0 := by rw [hX₁, he0, zero_div]
      rw [hX0, zero_div, zero_mul]
  have hclose' : ∀ θ ∈ complexStrip n ρinf, ‖S.limTor ρinf x₀ θ - S.tor x₀ θ‖ ≤
      (e / (γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a))) / Xs * (γ ^ 2 *
        sumA a lam ρ ρinf 1 (xA a (fun s => (C s).CE) Xs) (fun s => (C s).CD) a kp) := fun θ hθ =>
    ((KAM.Apost.lim_close (Ks := fun s => S.tor (S.iter x₀ s)) hdsum hdiff hLG) θ hθ).trans
      (hprop R.CD_nonneg (fun s hs => by simp only [R.tail s hs]))
  have hpb' : |p - S.par x₀| ≤ (e / (γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a))) / Xs * (γ ^ 2 *
      sumA a lam ρ ρinf 1 (xA a (fun s => (C s).CE) Xs) (fun s => (C s).Cp) a kp) := by
    obtain ⟨p', hp', hpb''⟩ := converge_par (f := fun s => S.par (S.iter x₀ s)) hpsum
      (fun s => (hit s).2.2.2) (hprop R.Cp_nonneg (fun s hs => by simp only [R.tail s hs]))
    rw [tendsto_nhds_unique hp hp']
    exact hpb''
  have hεz : Tendsto (runEps a lam ρ ρinf γ C e) atTop (𝓝 0) := by
    have h1 := hesum.tendsto_atTop_zero.const_mul (γ ^ 2)
    rw [mul_zero] at h1
    refine h1.congr fun s => ?_
    have : γ ^ 2 ≠ 0 := by positivity
    simp only [Real.rpow_zero]
    field_simp
  rw [hlimP]
  exact ⟨hconv, hconvd, hholo, hpr, hrr, hclose, hclose', hp, hpb, hpb', hεz⟩

end KAM.Sharp2.RouteA

end
