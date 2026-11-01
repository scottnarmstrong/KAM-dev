/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.Enum2
public import KAM.CertificateSharp.V2.SmallDivQ
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Certified small-divisor constants for three frequencies

A site of the v2 schedule asks for `SDConst n τ γ b c (ray ω*)`. For `n = 3` and any `τ ∈ ℕ`,
`fiberSiteOk` checks it from the certificate's box of `ω*`:

* the last coordinate is the clock: `ω*₂ ∈ [κc - κr, κc + κr]`, `κlo = κc - κr > 0` (an exact
  clock is `κr = 0`); `ω* = ω*₂ (ω', 1)`, and the box of `ω' = (ω*₀/ω*₂, ω*₁/ω*₂)` is
  `clockBox2` (interval division, `abs_div_sub_div_le`); the witness's dyadic box contains it
  (`dboxOk`), so the walk runs on short integers;
* `(ω', 1)` is `(γ/(κc + κr), τ)`-Diophantine; the walk `walk2 (mode3 …)` and the tail `tailQ`
  bound `S((ω', 1), b) ≤ B` (`smallDivisorSum_snoc2_le_walk`), so `S(ω*, b) ≤ B κlo⁻²`;
* the constant: `2^n B κlo⁻² (γ b^τ)² ≤ (2 · 3.1415 · c)²`; on the ray by `sdSum_ray_le`
  (`sdConst_ray_of_sdSum_le`, any `n`, `τ`).

`SiteWitG` names the test of a site: classical, the lunar bite of `siteOk` (`n = 2`, `τ = 1`), or
the fibered test. `siteOkG` contains `siteOk`; `sdConst_of_siteOkG` has the shape of
`sdConst_of_siteOk`, which is what the engines consume.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate KAM.Sharp2 KAM.CertificateSharp KAM.CertificateSharp.Fiber

/-- **`SDConst` on the ray from a bound of `S(ω*, b)`**, any `n`, `τ`: the rational test is
`2^n S̄ (γ b^τ)² ≤ (2 · 3.1415 · c)²`. -/
theorem sdConst_ray_of_sdSum_le {n τ : ℕ} {ωstar : Fin n → ℝ} {γ b c Sb : ℝ} (hγ : 0 < γ)
    (hb : 0 < b) (hc : 0 < c) (hdio : IsDiophantine γ τ ωstar) (hS : sdSum ωstar b ≤ Sb)
    (hnum : 2 ^ n * Sb * (γ * b ^ τ) ^ 2 ≤ (2 * (31415 / 10000) * c) ^ 2) :
    SDConst n τ γ b c (ray ωstar) := by
  have hτ0 : (0 : ℝ) ≤ τ := Nat.cast_nonneg τ
  refine sdConst_of_sdSum hc hb hγ hτ0 (fun ω hω => ?_) (fun ω hω => ?_)
  · obtain ⟨t, ht, rfl⟩ := hω
    exact isDiophantine_ray hdio ht
  obtain ⟨t, ht, rfl⟩ := hω
  have hSt : sdSum (t • ωstar) b ≤ Sb := (sdSum_ray_le hdio hγ hτ0 ht hb).trans hS
  have hpi := Real.pi_gt_d4
  have hgb : 0 < γ * b ^ τ := by positivity
  have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
  have hX : Real.sqrt (2 ^ n * Sb) * (γ * b ^ τ) ≤ 2 * (31415 / 10000) * c := by
    rw [← Real.sqrt_sq hgb.le, ← Real.sqrt_mul' _ (sq_nonneg _)]
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hnum⟩
  have hle : Real.sqrt (2 ^ n) * Real.sqrt (sdSum (t • ωstar) b) ≤ Real.sqrt (2 ^ n * Sb) := by
    rw [← Real.sqrt_mul h2n]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hSt h2n)
  have hrp : b ^ (-(τ : ℝ)) = (b ^ τ)⁻¹ := by
    rw [Real.rpow_neg hb.le, Real.rpow_natCast]
  rw [hrp]
  have hpi0 : 0 < 2 * Real.pi := by positivity
  have key : Real.sqrt (2 ^ n * Sb) ≤ 2 * Real.pi * (c * (γ⁻¹ * (b ^ τ)⁻¹)) := by
    have e : 2 * Real.pi * (c * (γ⁻¹ * (b ^ τ)⁻¹)) = 2 * Real.pi * c / (γ * b ^ τ) := by
      field_simp
    rw [e, le_div_iff₀ hgb]
    nlinarith
  calc (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n) * Real.sqrt (sdSum (t • ωstar) b)
      = (2 * Real.pi)⁻¹ * (Real.sqrt (2 ^ n) * Real.sqrt (sdSum (t • ωstar) b)) := by ring
    _ ≤ (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n * Sb) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * (c * (γ⁻¹ * (b ^ τ)⁻¹))) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = c * γ⁻¹ * (b ^ τ)⁻¹ := by field_simp

/-- Interval division: `|x/y - cx/cy| ≤ (rx cy + |cx| ry)/((cy - ry) cy)`. -/
theorem abs_div_sub_div_le {x y cx cy rx ry : ℝ} (hx : |x - cx| ≤ rx) (hy : |y - cy| ≤ ry)
    (hlo : 0 < cy - ry) : |x / y - cx / cy| ≤ (rx * cy + |cx| * ry) / ((cy - ry) * cy) := by
  have hry : 0 ≤ ry := (abs_nonneg _).trans hy
  have hcy : 0 < cy := by linarith
  have hy1 := (abs_le.mp hy).1
  have hy0 : 0 < y := by linarith
  have e : x / y - cx / cy = ((x - cx) * cy - cx * (y - cy)) / (y * cy) := by
    field_simp; ring
  have hnum : |(x - cx) * cy - cx * (y - cy)| ≤ rx * cy + |cx| * ry := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hcy]
    exact add_le_add (mul_le_mul_of_nonneg_right hx hcy.le)
      (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
  have hden : (cy - ry) * cy ≤ y * cy := mul_le_mul_of_nonneg_right (by linarith) hcy.le
  rw [e, abs_div, abs_of_pos (mul_pos hy0 hcy)]
  calc |(x - cx) * cy - cx * (y - cy)| / (y * cy)
      ≤ (rx * cy + |cx| * ry) / (y * cy) := div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left ((abs_nonneg _).trans hnum) (mul_pos hlo hcy) hden

/-- The witness of a fibered site: the cut-off `N`, the walk size `2N + 1 ≤ 2^l`, the degree `J`
of the exponential polynomial, the fixed point `2^{-P}`, `e ≥ 2^P e^{-4πb}`, a dyadic box `D` of
`ω'` (containing the certificate's), and the claimed bound `B` of `S((ω', 1), b)`. -/
structure FibWit where
  /-- The mode cut-off of `ω' ∈ ℝ²`. -/
  N : ℕ
  /-- `2N + 1 ≤ 2^l`. -/
  l : ℕ
  /-- The degree of the exponential lower polynomial. -/
  J : ℕ
  /-- The fixed-point precision. -/
  P : ℕ
  /-- The fixed-point upper bound `e/2^P` of `e^{-4πb}`. -/
  e : ℕ
  /-- The dyadic box of `ω'`. -/
  D : DBox2
  /-- The claimed bound of `S((ω', 1), b)`. -/
  B : ℚ

/-- The centre of the clock coordinate (index `2`). -/
def clockC (box : FreqBox) : ℚ := (box.getD 2 (0, 0)).1

/-- The radius of the clock coordinate. -/
def clockR (box : FreqBox) : ℚ := (box.getD 2 (0, 0)).2

/-- The radius of `ω_i/ω₂` by interval division. -/
def clockRad (box : FreqBox) (i : ℕ) : ℚ :=
  ((box.getD i (0, 0)).2 * clockC box + |(box.getD i (0, 0)).1| * clockR box) /
    ((clockC box - clockR box) * clockC box)

/-- The box of `ω' = (ω₀/ω₂, ω₁/ω₂)`, by interval division. -/
def clockBox2 (box : FreqBox) : FreqBox :=
  [((box.getD 0 (0, 0)).1 / clockC box, clockRad box 0),
    ((box.getD 1 (0, 0)).1 / clockC box, clockRad box 1)]

/-- The dyadic box contains `clockBox2`. -/
def dboxOk (box : FreqBox) (D : DBox2) : Bool :=
  decide (|(D.C0 : ℚ) / 2 ^ D.q - (box.getD 0 (0, 0)).1 / clockC box| + clockRad box 0 ≤
    (D.R0 : ℚ) / 2 ^ D.q) &&
  decide (|(D.C1 : ℚ) / 2 ^ D.q - (box.getD 1 (0, 0)).1 / clockC box| + clockRad box 1 ≤
    (D.R1 : ℚ) / 2 ^ D.q)

/-- The Diophantine constant `γ/(κc + κr)` of `(ω', 1)`. -/
def fibGamma (box : FreqBox) (γ : ℚ) : ℚ := γ / (clockC box + clockR box)

/-- The bound of `S((ω', 1), b)` from the walk's sum `s`. -/
def fibBound (box : FreqBox) (γ b : ℚ) (τ : ℕ) (w : FibWit) (s : ℕ) : ℚ :=
  (powUp w.e w.P 64 1 : ℚ) / 2 ^ w.P * (99225 / 30000) + (s : ℚ) / 2 ^ w.P +
    tailQ (fibGamma box γ) (2 * b) τ w.N ((powUp w.e w.P 64 (w.N + 1) : ℚ) / 2 ^ w.P)

/-- The bound test of the walk. -/
def fibSumOk (box : FreqBox) (γ b : ℚ) (τ : ℕ) (w : FibWit) : Bool :=
  match walk2 (mode3K w.D w.e w.P) w.N w.l with
  | none => false
  | some s => decide (fibBound box γ b τ w s ≤ w.B)

/-- **The fibered test at a site**, `n = 3`, any `τ`. -/
def fiberSiteOk (n τ : ℕ) (box : FreqBox) (γ b c : ℚ) (w : FibWit) : Bool :=
  decide (n = 3) && decide (0 < c) && decide (0 < b) && decide (0 < γ) &&
    decide (0 < clockC box - clockR box) && dboxOk box w.D && decide (0 < cLoQ (2 * b) τ w.N) &&
    decide (w.e ≤ 2 ^ w.P) && decide ((2 : ℚ) ^ w.P ≤ w.e * expLowQ (2 * b) w.J) &&
    decide (2 * w.N + 1 ≤ 2 ^ w.l) && fibSumOk box γ b τ w &&
    decide (2 ^ n * w.B * ((clockC box - clockR box) ^ 2)⁻¹ * (γ * b ^ τ) ^ 2 ≤
      (2 * (31415 / 10000) * c) ^ 2)

/-- The clock reduction: `ω* = ω*₂ (ω', 1)` with `ω'` in `clockBox2`, `(ω', 1)` Diophantine at
`γ/(κc + κr)`, and `κlo ≤ ω*₂`. -/
theorem clock_reduce {τ : ℕ} {box : FreqBox} {γ : ℚ} (hγ : 0 < γ)
    (hlo : 0 < clockC box - clockR box) {ωstar : Fin 3 → ℝ} (hω : FreqEncloses 3 box ωstar)
    (hdio : IsDiophantine (γ : ℝ) τ ωstar) :
    ∃ ω' : Fin 2 → ℝ, ωstar = ωstar 2 • (Fin.snoc ω' 1 : Fin 3 → ℝ) ∧
      FreqEncloses 2 (clockBox2 box) ω' ∧
      IsDiophantine ((fibGamma box γ : ℚ) : ℝ) τ (Fin.snoc ω' 1 : Fin 3 → ℝ) ∧
      ((clockC box - clockR box : ℚ) : ℝ) ≤ ωstar 2 := by
  have hlo' : (0 : ℝ) < (clockC box : ℝ) - clockR box := by exact_mod_cast hlo
  have h2 : |ωstar 2 - (clockC box : ℝ)| ≤ (clockR box : ℝ) := hω 2
  have hr0 : (0 : ℝ) ≤ clockR box := (abs_nonneg _).trans h2
  have hlo2 : (clockC box : ℝ) - clockR box ≤ ωstar 2 := by linarith [(abs_le.mp h2).1]
  have hhi2 : ωstar 2 ≤ (clockC box : ℝ) + clockR box := by linarith [(abs_le.mp h2).2]
  have hw2 : 0 < ωstar 2 := by linarith
  set ω' : Fin 2 → ℝ := ![ωstar 0 / ωstar 2, ωstar 1 / ωstar 2] with hω'
  have hsnoc : ωstar = ωstar 2 • (Fin.snoc ω' 1 : Fin 3 → ℝ) := by
    funext i
    fin_cases i <;> simp [hω'] <;> field_simp
  refine ⟨ω', hsnoc, ?_, ?_, by push_cast; exact hlo2⟩
  · intro i
    fin_cases i
    · have h := abs_div_sub_div_le (hω 0) h2 hlo'
      simp only [Fin.val_zero, Fin.isValue] at h
      simpa [hω', clockBox2, clockRad, clockC, clockR] using h
    · have h := abs_div_sub_div_le (hω 1) h2 hlo'
      simp only [Fin.val_one, Fin.isValue] at h
      simpa [hω', clockBox2, clockRad, clockC, clockR] using h
  · intro k hk
    have hd := hdio k hk
    have hpos : 0 < (∑ i, |(k i : ℝ)|) ^ (τ : ℝ) := by
      have : 0 < ∑ i, |(k i : ℝ)| := by
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hk
        exact lt_of_lt_of_le (abs_pos.mpr (by exact_mod_cast hj))
          (Finset.single_le_sum (f := fun i => |(k i : ℝ)|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j))
      positivity
    have hsn : ∀ i, (Fin.snoc ω' 1 : Fin 3 → ℝ) i = (ωstar 2)⁻¹ * ωstar i := fun i => by
      have h := congrFun hsnoc i
      simp only [Pi.smul_apply, smul_eq_mul] at h
      rw [h, ← mul_assoc, inv_mul_cancel₀ hw2.ne', one_mul]
    have e : ∑ i, (k i : ℝ) * (Fin.snoc ω' 1 : Fin 3 → ℝ) i =
        (ωstar 2)⁻¹ * ∑ i, (k i : ℝ) * ωstar i := by
      simp only [hsn, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, abs_mul, abs_of_pos (inv_pos.mpr hw2)]
    have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
    have hκhi : (0 : ℝ) < (clockC box : ℝ) + clockR box := by linarith
    simp only [fibGamma]
    push_cast
    rw [div_div, div_le_iff₀ (mul_pos hκhi hpos)]
    have h1 : (γ : ℝ) ≤ |∑ i, (k i : ℝ) * ωstar i| * (∑ i, |(k i : ℝ)|) ^ (τ : ℝ) := by
      rwa [div_le_iff₀ hpos] at hd
    have h3 : (ωstar 2)⁻¹ * ((clockC box : ℝ) + clockR box) ≥ 1 := by
      rw [ge_iff_le, ← div_eq_inv_mul, le_div_iff₀ hw2, one_mul]; exact hhi2
    have h4 : 0 ≤ |∑ i, (k i : ℝ) * ωstar i| * (∑ i, |(k i : ℝ)|) ^ (τ : ℝ) := by positivity
    calc (γ : ℝ) ≤ |∑ i, (k i : ℝ) * ωstar i| * (∑ i, |(k i : ℝ)|) ^ (τ : ℝ) := h1
      _ ≤ |∑ i, (k i : ℝ) * ωstar i| * (∑ i, |(k i : ℝ)|) ^ (τ : ℝ) *
            ((ωstar 2)⁻¹ * ((clockC box : ℝ) + clockR box)) := le_mul_of_one_le_right h4 h3
      _ = _ := by ring

/-- A dyadic box containing `clockBox2 box` encloses what `clockBox2 box` encloses. -/
theorem encloses_dbox {box : FreqBox} {D : DBox2} (h : dboxOk box D = true) {ω' : Fin 2 → ℝ}
    (hω : FreqEncloses 2 (clockBox2 box) ω') : FreqEncloses 2 D.toBox ω' := by
  simp only [dboxOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h1⟩ := h
  have key : ∀ {x c r c' r' : ℚ} {y : ℝ}, |y - (c : ℝ)| ≤ r → |c' - c| + r ≤ r' →
      |y - (c' : ℝ)| ≤ r' := fun {x c r c' r' y} hy hc => by
    have hc' : |(c' : ℝ) - c| + r ≤ r' := by exact_mod_cast hc
    calc |y - (c' : ℝ)| ≤ |y - c| + |(c' : ℝ) - c| := by
          have := abs_sub_le y (c : ℝ) (c' : ℝ)
          rwa [abs_sub_comm (c : ℝ) (c' : ℝ)] at this
      _ ≤ _ := by linarith
  intro i
  fin_cases i
  · have hy := hω 0
    simp only [clockBox2, Fin.val_zero, Fin.isValue, List.getD_cons_zero] at hy
    simp only [DBox2.toBox, List.getD_cons_zero]
    exact key (x := 0) hy h0
  · have hy := hω 1
    simp only [clockBox2, Fin.val_one, Fin.isValue, List.getD_cons_succ,
      List.getD_cons_zero] at hy
    simp only [DBox2.toBox, List.getD_cons_succ, List.getD_cons_zero]
    exact key (x := 0) hy h1

/-- **Soundness of the fibered test**: `SDConst` on the ray. -/
theorem sdConst_ray_of_fiberSiteOk {n τ : ℕ} {box : FreqBox} {γ b c : ℚ} {w : FibWit}
    (h : fiberSiteOk n τ box γ b c w = true) {ωstar : Fin n → ℝ} (hω : FreqEncloses n box ωstar)
    (hdio : IsDiophantine (γ : ℝ) τ ωstar) : SDConst n τ (γ : ℝ) (b : ℝ) (c : ℝ) (ray ωstar) := by
  simp only [fiberSiteOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, hc⟩, hb⟩, hγ⟩, hlo⟩, hD⟩, hcl⟩, he⟩, hE⟩, hl⟩, hsum⟩, hnum⟩ := h
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hlo' : (0 : ℝ) < ((clockC box - clockR box : ℚ) : ℝ) := by exact_mod_cast hlo
  obtain ⟨ω', hsnoc, hbox, hdio', hκ⟩ := clock_reduce hγ hlo hω hdio
  have hr0 : 0 ≤ clockR box := by
    have : (0 : ℝ) ≤ clockR box := (abs_nonneg _).trans (hω 2)
    exact_mod_cast this
  unfold fibSumOk at hsum
  split at hsum
  · exact absurd hsum (by simp)
  rename_i s hs
  have hK : mode3K w.D w.e w.P = mode3 w.D w.e w.P :=
    funext fun a => funext fun b => mode3K_eq _ _ _ a b
  rw [hK] at hs
  have hB : fibBound box γ b τ w s ≤ w.B := by simpa only [decide_eq_true_eq] using hsum
  have hγd : 0 < fibGamma box γ := div_pos hγ (by linarith)
  have hS := smallDivisorSum_snoc2_le_walk (γ := fibGamma box γ) (δ := 2 * b) he hE hγd
    (by positivity) hcl hl hs (encloses_dbox hD hbox) hdio'
  have hSB : smallDivisorSum (Fin.snoc ω' 1 : Fin 3 → ℝ) (2 * (b : ℝ)) ≤ (w.B : ℝ) := by
    have e : (((2 * b : ℚ)) : ℝ) = 2 * (b : ℝ) := by push_cast; ring
    rw [e] at hS
    refine hS.trans ?_
    exact (Rat.cast_le (K := ℝ)).mpr hB
  have hS0 : 0 ≤ smallDivisorSum (Fin.snoc ω' 1 : Fin 3 → ℝ) (2 * (b : ℝ)) :=
    smallDivisorSum_nonneg _ _
  have hsd : sdSum ωstar b ≤ (w.B : ℝ) * (((clockC box - clockR box : ℚ) : ℝ) ^ 2)⁻¹ := by
    rw [sdSum_eq_smallDivisorSum, hsnoc, smallDivisorSum_smul]
    have hw2 : 0 < ωstar 2 := lt_of_lt_of_le hlo' hκ
    have hsq : ((clockC box - clockR box : ℚ) : ℝ) ^ 2 ≤ (ωstar 2) ^ 2 :=
      pow_le_pow_left₀ hlo'.le hκ 2
    have hinv : ((ωstar 2) ^ 2)⁻¹ ≤ (((clockC box - clockR box : ℚ) : ℝ) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) hsq
    have hB0 : (0 : ℝ) ≤ w.B := hS0.trans hSB
    calc ((ωstar 2) ^ 2)⁻¹ * smallDivisorSum (Fin.snoc ω' 1 : Fin 3 → ℝ) (2 * (b : ℝ))
        ≤ (((clockC box - clockR box : ℚ) : ℝ) ^ 2)⁻¹ * (w.B : ℝ) :=
          mul_le_mul hinv hSB hS0 (by positivity)
      _ = _ := mul_comm _ _
  refine sdConst_ray_of_sdSum_le hγ' hb' hc' hdio hsd ?_
  have := (Rat.cast_le (K := ℝ)).mpr hnum
  push_cast at this ⊢
  linarith

/-- The test of a site: classical, the lunar bite (`n = 2`, `τ = 1`), or fibered (`n = 3`). -/
inductive SiteWitG where
  /-- The classical constant. -/
  | classical
  /-- The lunar bite of `siteOk`. -/
  | bite (w : BiteWit)
  /-- The fibered test of `fiberSiteOk`. -/
  | fiber (w : FibWit)

/-- The test at a site. It contains `siteOk`. -/
def siteOkG (n τ J : ℕ) (box : FreqBox) (κ γ b c : ℚ) : SiteWitG → Bool
  | .classical => siteOk n τ J box κ γ b c none
  | .bite w => siteOk n τ J box κ γ b c (some w)
  | .fiber w => fiberSiteOk n τ box γ b c w

/-- **Soundness of the test at a site**, for a bite `b ≤ 1` (the shape of `sdConst_of_siteOk`). -/
theorem sdConst_of_siteOkG {n τ J : ℕ} {box : FreqBox} {κ γ b c : ℚ} {o : SiteWitG}
    (hn : 1 ≤ n) (hτ : 1 ≤ τ) (hγ : 0 < γ) (hb : 0 < b) (hb1 : b ≤ 1)
    (h : siteOkG n τ J box κ γ b c o = true) {ωstar : Fin n → ℝ} (hω : FreqEncloses n box ωstar)
    (hdio : IsDiophantine (γ : ℝ) τ ωstar) :
    SDConst n τ (γ : ℝ) (b : ℝ) (c : ℝ) (ray ωstar) := by
  cases o with
  | classical => exact sdConst_of_siteOk (J := J) (κ := κ) (o := none) hn hτ hγ hb hb1 h hω hdio
  | bite w => exact sdConst_of_siteOk (J := J) (κ := κ) (o := some w) hn hτ hγ hb hb1 h hω hdio
  | fiber w => exact sdConst_ray_of_fiberSiteOk h hω hdio

end KAM.CertificateSharp.V2

end
