/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Lock.Confine
public import KAM.SpinOrbit.Lock.PO.Orbit
public import KAM.SpinOrbit.Lock.Coords.Maps
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# LOCK-ASSEMBLY, part 1: the glue (design SO-LOCK §1.4, §1.5, §5, §7)

Unfrozen helper code.

* `abs_le_of_libAction_lt`: the action bound gives the coordinate bounds.
* `sqrt_libAction_le`: change of centre, `√𝓘_c ≤ √𝓘_ψ + √π (√Ω r + r'/√Ω)`.
* `lunarOmega = 8/65`.
* `lockLiteralCheck`: the rational literal check of design §1.4 (exact `ℚ` arithmetic, rational
  majorants of `π` and of square roots, the latter re-verified by squaring inside the check);
  `lockLiteralCheck_sound`.
* `lunar_sync_lock_of_barrier_check`, `lunar_sync_lock_of_barrier`: **explicitly conditional**
  helpers. Their hypothesis is a `LockBarrier` around the rational centre, which LOCK-GRAPH
  will produce from the certificate (`lockBarrier_of_certV2`); their conclusion is the shape of
  the headline `lunar_sync_lock`. They never stand in for the headline.
-/

@[expose] public noncomputable section

open Real

namespace KAM.SpinOrbit.Lock

/-! ### Coordinate bounds and change of centre -/

/-- LOCK-CONF corollary: the action bound gives the coordinate bounds. -/
theorem abs_le_of_libAction_lt {Ω I : ℝ} {c : ℝ → ℝ} (hΩ : 0 < Ω) {x : ℝ × ℝ × ℝ}
    (h : libAction Ω c x < I) :
    |x.1 - x.2.2 - c x.2.2| ≤ √(I / (π * Ω)) ∧ |x.2.1 - 1 - deriv c x.2.2| ≤ √(Ω * I / π) := by
  unfold libAction at h
  set X := x.1 - x.2.2 - c x.2.2
  set Y := x.2.1 - 1 - deriv c x.2.2
  have hπ := Real.pi_pos
  have hX : 0 ≤ Ω * X ^ 2 := by positivity
  have hY : 0 ≤ Y ^ 2 / Ω := by positivity
  refine ⟨Real.abs_le_sqrt ?_, Real.abs_le_sqrt ?_⟩
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [le_div_iff₀ hπ]
    have : π * (Y ^ 2 / Ω) ≤ I := by nlinarith
    have hYe : π * (Y ^ 2 / Ω) * Ω = Y ^ 2 * π := by field_simp
    nlinarith

/-- Planar triangle inequality: `√((u+a)² + (v+b)²) ≤ √(u² + v²) + A + B` for `|a| ≤ A`,
`|b| ≤ B`. -/
theorem sqrt_sq_add_sq_le {u v a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) :
    √((u + a) ^ 2 + (v + b) ^ 2) ≤ √(u ^ 2 + v ^ 2) + A + B := by
  set s := √(u ^ 2 + v ^ 2)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = u ^ 2 + v ^ 2 := Real.sq_sqrt (by positivity)
  have hu : |u| ≤ s := Real.abs_le_sqrt (by nlinarith)
  have hv : |v| ≤ s := Real.abs_le_sqrt (by nlinarith)
  have hA : 0 ≤ A := (abs_nonneg _).trans ha
  have hB : 0 ≤ B := (abs_nonneg _).trans hb
  have hua : u * a ≤ s * A := (le_abs_self _).trans (by
    rw [abs_mul]; exact mul_le_mul hu ha (abs_nonneg _) hs)
  have hvb : v * b ≤ s * B := (le_abs_self _).trans (by
    rw [abs_mul]; exact mul_le_mul hv hb (abs_nonneg _) hs)
  have ha2 : a ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs a]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  have hb2 : b ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs b]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg hA hB]

/-- LOCK-ASSEMBLY transfer: change of centre from `c` to `ψ` (triangle inequality in the
`Ω`-norm): `√𝓘_c ≤ √𝓘_ψ + √π (√Ω r + r'/√Ω)` when `|ψ − c| ≤ r`, `|ψ' − c'| ≤ r'`. -/
theorem sqrt_libAction_le {Ω r r' : ℝ} (hΩ : 0 < Ω) {c ψ : ℝ → ℝ}
    (hr : ∀ φ, |ψ φ - c φ| ≤ r) (hr' : ∀ φ, |deriv ψ φ - deriv c φ| ≤ r') (x : ℝ × ℝ × ℝ) :
    √(libAction Ω c x) ≤ √(libAction Ω ψ x) + √π * (√Ω * r + r' / √Ω) := by
  set k := √π
  set w := √Ω
  have hk : 0 < k := Real.sqrt_pos.2 Real.pi_pos
  have hw : 0 < w := Real.sqrt_pos.2 hΩ
  have hk2 : k ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have hw2 : w ^ 2 = Ω := Real.sq_sqrt hΩ.le
  set X := x.1 - x.2.2 - ψ x.2.2
  set Y := x.2.1 - 1 - deriv ψ x.2.2
  set d := ψ x.2.2 - c x.2.2
  set e := deriv ψ x.2.2 - deriv c x.2.2
  have hψ : libAction Ω ψ x = (k * w * X) ^ 2 + (k * Y / w) ^ 2 := by
    unfold libAction; rw [← hk2, ← hw2]; field_simp; rfl
  have hc : libAction Ω c x = (k * w * X + k * w * d) ^ 2 + (k * Y / w + k * e / w) ^ 2 := by
    unfold libAction
    rw [show x.1 - x.2.2 - c x.2.2 = X + d by simp only [X, d]; ring,
      show x.2.1 - 1 - deriv c x.2.2 = Y + e by simp only [Y, e]; ring, ← hk2, ← hw2]
    field_simp
  have ha : |k * w * d| ≤ k * w * r := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (hr _) (by positivity)
  have hb : |k * e / w| ≤ k * r' / w := by
    rw [abs_div, abs_mul, abs_of_pos hk, abs_of_pos hw]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hr' _) hk.le) hw.le
  rw [hc, hψ]
  refine (sqrt_sq_add_sq_le ha hb).trans (le_of_eq ?_)
  ring

/-! ### Bounds on the rational sine centre -/

theorem abs_list_sum_map_le {f g : ℕ → ℝ} (h : ∀ k, |f k| ≤ g k) (l : List ℕ) :
    |(l.map f).sum| ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons k l ih => simpa using (abs_add_le _ _).trans (add_le_add (h k) ih)

theorem hasDerivAt_list_sum_map {g g' : ℕ → ℝ → ℝ} (h : ∀ k x, HasDerivAt (g k) (g' k x) x)
    (l : List ℕ) (x : ℝ) :
    HasDerivAt (fun φ => (l.map fun k => g k φ).sum) ((l.map fun k => g' k x).sum) x := by
  induction l with
  | nil => simpa using hasDerivAt_const x (0 : ℝ)
  | cons k l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h k x).add ih

/-- The sup bound of the centre: `Σ |c_k|`. -/
def lockCentreAbs (cs : List ℚ) : ℚ :=
  ((List.range cs.length).map fun k => |cs.getD k 0|).sum

/-- The sup bound of the centre's derivative, divided by `2π`: `Σ (k+1) |c_k|`. -/
def lockCentreDAbs (cs : List ℚ) : ℚ :=
  ((List.range cs.length).map fun k : ℕ => ((k : ℚ) + 1) * |cs.getD k 0|).sum

theorem abs_lockCentre_le (cs : List ℚ) (φ : ℝ) :
    |lockCentre cs φ| ≤ (lockCentreAbs cs : ℝ) := by
  unfold lockCentre lockCentreAbs
  rw [Rat.cast_list_sum, List.map_map]
  refine abs_list_sum_map_le (fun k => ?_) _
  simp only [Function.comp_apply, Rat.cast_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

theorem hasDerivAt_lockCentre (cs : List ℚ) (φ : ℝ) :
    HasDerivAt (lockCentre cs) ((List.range cs.length).map fun k =>
      ((cs.getD k 0 : ℚ) : ℝ) * (Real.cos (2 * π * (k + 1) * φ) * (2 * π * (k + 1)))).sum φ := by
  unfold lockCentre
  exact hasDerivAt_list_sum_map
    (g := fun k φ => ((cs.getD k 0 : ℚ) : ℝ) * Real.sin (2 * π * (k + 1) * φ))
    (g' := fun k φ =>
      ((cs.getD k 0 : ℚ) : ℝ) * (Real.cos (2 * π * (k + 1) * φ) * (2 * π * (k + 1))))
    (fun k x => (((hasDerivAt_id x).const_mul (2 * π * (k + 1))).sin.const_mul
      ((cs.getD k 0 : ℚ) : ℝ)).congr_deriv (by simp)) _ φ

theorem abs_deriv_lockCentre_le (cs : List ℚ) (φ : ℝ) :
    |deriv (lockCentre cs) φ| ≤ 2 * π * (lockCentreDAbs cs : ℝ) := by
  rw [(hasDerivAt_lockCentre cs φ).deriv]
  unfold lockCentreDAbs
  rw [Rat.cast_list_sum, List.map_map, ← List.sum_map_mul_left]
  refine abs_list_sum_map_le (fun k => ?_) _
  simp only [Function.comp_apply, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_one,
    Rat.cast_abs]
  rw [abs_mul, abs_mul]
  have hπ := Real.pi_pos
  have hk : |2 * π * ((k : ℝ) + 1)| = 2 * π * ((k : ℝ) + 1) := abs_of_pos (by positivity)
  rw [hk]
  have := Real.abs_cos_le_one (2 * π * (k + 1) * φ)
  have h0 : 0 ≤ |((cs.getD k 0 : ℚ) : ℝ)| := abs_nonneg _
  nlinarith [mul_nonneg h0 (by positivity : (0 : ℝ) ≤ 2 * π * ((k : ℝ) + 1))]

/-! ### The rational literal check (design §1.4) -/

/-- `fuel` Newton steps `x ↦ (x + n / x) / 2` for `⌊√n⌋`; only an approximation, whose quality
is never used (the check re-verifies every root by squaring). -/
def lockNatSqrt : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | f + 1, n, x => if x = 0 then 0 else lockNatSqrt f n ((x + n / x) / 2)

/-- A rational approximation from above of `√t`, to about `10⁻⁶` (not verified here). -/
def lockSqrtUp (t : ℚ) : ℚ :=
  let n := t.num.toNat * 10 ^ 12 / t.den + 1
  ((lockNatSqrt 128 n (n + 1) + 1 : ℕ) : ℚ) / 10 ^ 6

theorem lockSqrtUp_nonneg (t : ℚ) : 0 ≤ lockSqrtUp t := by
  unfold lockSqrtUp; positivity

/-- Rational bounds `π ∈ [πlo, πhi]`. -/
def lockPiLo : ℚ := 3141592 / 1000000
def lockPiHi : ℚ := 3141593 / 1000000

/-- The rational literal check of design §1.4 (body: exact ℚ arithmetic with rational majorants
of `π`, `√Ω`, `√·`): `I_in`, `Rψ`, `Rp` are compatible with the barrier range `[lo, hi]`, the
orbit bounds `r₀, r₁` (on `|ψ*|`, `|ψ*′|`) and the centre `cs`. -/
def lockLiteralCheck (Ω : ℚ) (cs : List ℚ) (lo hi r₀ r₁ Iin Rψ Rp : ℚ) : Bool :=
  let r := r₀ + lockCentreAbs cs
  let r' := r₁ + 2 * lockPiHi * lockCentreDAbs cs
  let a₁ := lockSqrtUp (lockPiHi * Ω)
  let a₂ := lockSqrtUp (lockPiHi / Ω)
  let b := lockSqrtUp Iin
  decide (0 < Ω) && decide (0 ≤ r₀) && decide (0 ≤ r₁) && decide (0 ≤ hi) &&
    decide (lockPiHi * Ω ≤ a₁ ^ 2) && decide (lockPiHi / Ω ≤ a₂ ^ 2) &&
    decide (Iin ≤ b ^ 2) && decide ((b + (a₁ * r + a₂ * r')) ^ 2 ≤ lo) &&
    decide (r ≤ Rψ) && decide (hi / (lockPiLo * Ω) ≤ (Rψ - r) ^ 2) &&
    decide (r' ≤ Rp) && decide (Ω * hi / lockPiLo ≤ (Rp - r') ^ 2) && decide (Rψ + r₀ < 1 / 4)

/-- What a passing `lockLiteralCheck` certifies, over `ℝ`. -/
structure LockLiteralFacts (Ω : ℝ) (lo hi r₀ r₁ Iin Rψ Rp R R' : ℝ) : Prop where
  pos : 0 < Ω
  tube : (√Iin + √π * (√Ω * R + R' / √Ω)) ^ 2 ≤ lo
  psi : √(hi / (π * Ω)) + R ≤ Rψ
  spin : √(Ω * hi / π) + R' ≤ Rp
  angle : Rψ + r₀ < 1 / 4

/-- Soundness of `lockLiteralCheck`, with `R = r₀ + Σ|c_k|` and `R' = r₁ + 2π Σ (k+1)|c_k|`. -/
theorem lockLiteralCheck_sound {Ω : ℚ} {cs : List ℚ} {lo hi r₀ r₁ Iin Rψ Rp : ℚ}
    (h : lockLiteralCheck Ω cs lo hi r₀ r₁ Iin Rψ Rp = true) :
    LockLiteralFacts (Ω : ℝ) lo hi r₀ r₁ Iin Rψ Rp ((r₀ : ℝ) + lockCentreAbs cs)
      ((r₁ : ℝ) + 2 * π * lockCentreDAbs cs) := by
  simp only [lockLiteralCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hΩ, hr₀⟩, hr₁⟩, hhi⟩, ha₁⟩, ha₂⟩, hb⟩, htube⟩, hr⟩, hpsi⟩, hr'⟩, hspin⟩,
    hang⟩ := h
  have ha₁0 := lockSqrtUp_nonneg (lockPiHi * Ω)
  have ha₂0 := lockSqrtUp_nonneg (lockPiHi / Ω)
  have hb0 := lockSqrtUp_nonneg Iin
  set a₁ := lockSqrtUp (lockPiHi * Ω)
  set a₂ := lockSqrtUp (lockPiHi / Ω)
  set b := lockSqrtUp Iin
  have hπlo : (lockPiLo : ℝ) < π := by
    have := Real.pi_gt_d6; simp only [lockPiLo]; push_cast; linarith
  have hπhi : π < (lockPiHi : ℝ) := by
    have := Real.pi_lt_d6; simp only [lockPiHi]; push_cast; linarith
  have hπl0 : (0 : ℝ) < lockPiLo := by simp only [lockPiLo]; norm_num
  have hπ := Real.pi_pos
  have hΩr : (0 : ℝ) < Ω := by exact_mod_cast hΩ
  have hsΩ := Real.sqrt_pos.2 hΩr
  have hr₀r : (0 : ℝ) ≤ r₀ := by exact_mod_cast hr₀
  have hr₁r : (0 : ℝ) ≤ r₁ := by exact_mod_cast hr₁
  have hhir : (0 : ℝ) ≤ hi := by exact_mod_cast hhi
  have hA : (0 : ℝ) ≤ lockCentreAbs cs := (abs_nonneg _).trans (abs_lockCentre_le cs 0)
  have hD : (0 : ℝ) ≤ lockCentreDAbs cs := by
    have := (abs_nonneg _).trans (abs_deriv_lockCentre_le cs 0)
    exact nonneg_of_mul_nonneg_right (by linarith) (by positivity : (0 : ℝ) < 2 * π)
  have hr : (r₀ : ℝ) + lockCentreAbs cs ≤ Rψ := by exact_mod_cast hr
  have hr' : (r₁ : ℝ) + 2 * lockPiHi * lockCentreDAbs cs ≤ Rp := by exact_mod_cast hr'
  have hR'RH : (r₁ : ℝ) + 2 * π * lockCentreDAbs cs ≤ r₁ + 2 * lockPiHi * lockCentreDAbs cs := by
    nlinarith
  have root : ∀ {t a : ℝ}, 0 ≤ a → t ≤ a ^ 2 → √t ≤ a := fun ha h =>
    Real.sqrt_le_iff.2 ⟨ha, h⟩
  refine ⟨hΩr, ?_, ?_, ?_,
    (by have := (Rat.cast_lt (K := ℝ)).2 hang; push_cast at this ⊢; linarith)⟩
  · have e1 : √π * √(Ω : ℝ) ≤ a₁ := by
      rw [← Real.sqrt_mul hπ.le]
      refine root (by exact_mod_cast ha₁0) ?_
      have : ((lockPiHi * Ω : ℚ) : ℝ) ≤ ((a₁ ^ 2 : ℚ) : ℝ) := by exact_mod_cast ha₁
      push_cast at this; nlinarith
    have e2 : √π / √(Ω : ℝ) ≤ a₂ := by
      rw [← Real.sqrt_div hπ.le]
      refine root (by exact_mod_cast ha₂0) ?_
      have : ((lockPiHi / Ω : ℚ) : ℝ) ≤ ((a₂ ^ 2 : ℚ) : ℝ) := by exact_mod_cast ha₂
      push_cast at this
      exact (div_le_div_of_nonneg_right hπhi.le hΩr.le).trans this
    have e3 : √(Iin : ℝ) ≤ b := root (by exact_mod_cast hb0) (by exact_mod_cast hb)
    have ht : (((b + (a₁ * (r₀ + lockCentreAbs cs) +
        a₂ * (r₁ + 2 * lockPiHi * lockCentreDAbs cs))) ^ 2 : ℚ) : ℝ) ≤ lo := by
      exact_mod_cast htube
    push_cast at ht
    refine le_trans (pow_le_pow_left₀ (by positivity) ?_ 2) ht
    have ha₁r : (0 : ℝ) ≤ a₁ := by exact_mod_cast ha₁0
    have ha₂r : (0 : ℝ) ≤ a₂ := by exact_mod_cast ha₂0
    have hR : 0 ≤ (r₀ : ℝ) + lockCentreAbs cs := by positivity
    have hR' : 0 ≤ (r₁ : ℝ) + 2 * π * lockCentreDAbs cs := by positivity
    have : √π * (√(Ω : ℝ) * (r₀ + lockCentreAbs cs) + (r₁ + 2 * π * lockCentreDAbs cs) / √Ω) =
        (√π * √(Ω : ℝ)) * (r₀ + lockCentreAbs cs) +
          (√π / √(Ω : ℝ)) * (r₁ + 2 * π * lockCentreDAbs cs) := by ring
    rw [this]
    have := mul_le_mul e1 le_rfl hR ha₁r
    have := mul_le_mul e2 hR'RH hR' ha₂r
    linarith
  · have hp : ((hi / (lockPiLo * Ω) : ℚ) : ℝ) ≤ (((Rψ - (r₀ + lockCentreAbs cs)) ^ 2 : ℚ) : ℝ) := by
      exact_mod_cast hpsi
    push_cast at hp
    have : √((hi : ℝ) / (π * Ω)) ≤ Rψ - (r₀ + lockCentreAbs cs) := root (by linarith)
      ((div_le_div_of_nonneg_left hhir (by positivity)
        (mul_le_mul_of_nonneg_right hπlo.le hΩr.le)).trans hp)
    linarith
  · have hp : ((Ω * hi / lockPiLo : ℚ) : ℝ) ≤
        (((Rp - (r₁ + 2 * lockPiHi * lockCentreDAbs cs)) ^ 2 : ℚ) : ℝ) := by
      exact_mod_cast hspin
    push_cast at hp
    have : √((Ω : ℝ) * hi / π) ≤ Rp - (r₁ + 2 * lockPiHi * lockCentreDAbs cs) :=
      root (by linarith)
        ((div_le_div_of_nonneg_left (by positivity) hπl0 hπlo.le).trans hp)
    linarith

/-- `Ω` for the lunar tube (LOCK-GEN: the roundest elliptic polar coordinates at N = 65). -/
def lunarOmega : ℚ := 8 / 65

theorem lunar_literalCheck :
    lockLiteralCheck lunarOmega lunarLockCentre (132 / 10000) (163 / 10000) (17 / 1000000)
      (27 / 200000) (129 / 10000) (21 / 100) (26 / 1000) = true := by
  decide +kernel

/-! ### The parametric critical path (explicitly conditional helpers) -/

/-- **Conditional helper, not the headline.** A librational barrier around the rational centre
`cs` whose action range lies in `[lo, hi]`, plus a passing literal check, gives the headline
shape with output literals `Rψ`, `Rp`. The barrier is what LOCK-GRAPH will deliver. -/
theorem lunar_sync_lock_of_barrier_check {Ω : ℚ} {cs : List ℚ} {lo hi Iin Rψ Rp : ℚ}
    {Iin' Iout : ℝ} (B : LockBarrier (Ω : ℝ) (lockCentre cs) Iin' Iout) (hlo : (lo : ℝ) ≤ Iin')
    (hhi : Iout ≤ hi)
    (hlit : lockLiteralCheck Ω cs lo hi (17 / 1000000) (27 / 200000) Iin Rψ Rp = true)
    (q₀ p₀ φ₀ : ℝ) (h₀ : libAction (Ω : ℝ) lunarSyncOrbit (q₀, p₀, φ₀) < Iin) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).1 - (z t).2.2 - lunarSyncOrbit (z t).2.2| ≤ Rψ ∧
        |(z t).2.1 - 1 - deriv lunarSyncOrbit (z t).2.2| ≤ Rp ∧
        |(z t).1 - (z t).2.2| < 1 / 4) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z := by
  have F := lockLiteralCheck_sound hlit
  have hΩ := F.pos
  set c := lockCentre cs
  set ψ := lunarSyncOrbit
  set R := (((17 / 1000000 : ℚ) : ℝ) + lockCentreAbs cs)
  set R' := (((27 / 200000 : ℚ) : ℝ) + 2 * π * lockCentreDAbs cs)
  have hψ0 : ∀ φ, |ψ φ| ≤ ((17 / 1000000 : ℚ) : ℝ) := fun φ => by
    push_cast; exact (lunarSyncOrbit_bound φ).1
  have hψ1 : ∀ φ, |deriv ψ φ| ≤ ((27 / 200000 : ℚ) : ℝ) := fun φ => by
    push_cast; exact (lunarSyncOrbit_bound φ).2
  have hr : ∀ φ, |ψ φ - c φ| ≤ R := fun φ =>
    (abs_sub _ _).trans (add_le_add (hψ0 φ) (abs_lockCentre_le cs φ))
  have hr' : ∀ φ, |deriv ψ φ - deriv c φ| ≤ R' := fun φ =>
    (abs_sub _ _).trans (add_le_add (hψ1 φ) (abs_deriv_lockCentre_le cs φ))
  -- the initial point lies inside the barrier
  have hinit : libAction (Ω : ℝ) c (q₀, p₀, φ₀) < Iin' := by
    have h1 := sqrt_libAction_le hΩ hr hr' (q₀, p₀, φ₀)
    have h0 : 0 ≤ libAction (Ω : ℝ) ψ (q₀, p₀, φ₀) := by unfold libAction; positivity
    have h2 : √(libAction (Ω : ℝ) ψ (q₀, p₀, φ₀)) < √(Iin : ℝ) := Real.sqrt_lt_sqrt h0 h₀
    have hδ : 0 ≤ √π * (√(Ω : ℝ) * R + R' / √Ω) := by
      have := (abs_nonneg _).trans (hr 0)
      have := (abs_nonneg _).trans (hr' 0)
      positivity
    have h3 : √(libAction (Ω : ℝ) c (q₀, p₀, φ₀)) < √(Iin : ℝ) + √π * (√(Ω : ℝ) * R + R' / √Ω) :=
      by linarith
    rw [Real.sqrt_lt' (lt_of_le_of_lt (Real.sqrt_nonneg _) h3)] at h3
    linarith [F.tube]
  obtain ⟨z, hz, hI, huniq⟩ :=
    lock_confinement hΩ ((lockCentre_contDiff cs).of_le le_top) B _ hinit
  refine ⟨z, hz, fun t => ?_, huniq⟩
  obtain ⟨hX, hY⟩ := abs_le_of_libAction_lt hΩ ((hI t).trans_le hhi)
  have hXψ : |(z t).1 - (z t).2.2 - ψ (z t).2.2| ≤ Rψ := by
    have := hr (z t).2.2
    calc _ = |((z t).1 - (z t).2.2 - c (z t).2.2) - (ψ (z t).2.2 - c (z t).2.2)| := by ring_nf
      _ ≤ _ := abs_sub _ _
      _ ≤ _ := add_le_add hX this
      _ ≤ Rψ := F.psi
  refine ⟨hXψ, ?_, ?_⟩
  · have := hr' (z t).2.2
    calc _ = |((z t).2.1 - 1 - deriv c (z t).2.2) - (deriv ψ (z t).2.2 - deriv c (z t).2.2)| := by
          ring_nf
      _ ≤ _ := abs_sub _ _
      _ ≤ _ := add_le_add hY this
      _ ≤ Rp := F.spin
  · calc |(z t).1 - (z t).2.2| = |((z t).1 - (z t).2.2 - ψ (z t).2.2) + ψ (z t).2.2| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ Rψ + ((17 / 1000000 : ℚ) : ℝ) := add_le_add hXψ (hψ0 _)
      _ < 1 / 4 := F.angle

/-- **Conditional helper, not the headline** `lunar_sync_lock`. Given a librational barrier for
`Ω = lunarOmega` around `lunarLockCentre` whose inner and outer actions lie in
`[132/10000, 163/10000]` (the conclusion LOCK-GRAPH/DATA will deliver; LOCK-GEN-1 has
`P ∈ [0.013238, 0.016258]`), the conclusion of `lunar_sync_lock` holds. -/
theorem lunar_sync_lock_of_barrier {Iin Iout : ℝ}
    (B : LockBarrier (lunarOmega : ℝ) (lockCentre lunarLockCentre) Iin Iout)
    (hlo : 132 / 10000 ≤ Iin) (hhi : Iout ≤ 163 / 10000) (q₀ p₀ φ₀ : ℝ)
    (h₀ : libAction lunarOmega lunarSyncOrbit (q₀, p₀, φ₀) < 129 / 10000) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).1 - (z t).2.2 - lunarSyncOrbit (z t).2.2| ≤ 21 / 100 ∧
        |(z t).2.1 - 1 - deriv lunarSyncOrbit (z t).2.2| ≤ 26 / 1000 ∧
        |(z t).1 - (z t).2.2| < 1 / 4) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z := by
  have := lunar_sync_lock_of_barrier_check (lo := 132 / 10000) (hi := 163 / 10000) B
    (by push_cast; exact hlo) (by push_cast; exact hhi) lunar_literalCheck q₀ p₀ φ₀
    (by push_cast; exact h₀)
  push_cast at this
  exact this

end KAM.SpinOrbit.Lock

end
