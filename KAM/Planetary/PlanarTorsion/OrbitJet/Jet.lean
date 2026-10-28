/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# Planar quartic torsion: one-variable jets of order four

A small algebra of truncated polynomials `Jet5` (coefficients of `t⁰, …, t⁴`) and the predicate
`IsJet f a` (`f t = a.ev t + O(t⁵)` as `t → 0`), closed under sums, products, constants and the
exponential, together with the contraction lemma `isJet_of_fixedPoint` for the Kepler fixed-point
equation `y = t (A e^y - B e^{-y}) / 2`.  This is the elementary asymptotic engine of
`OrbitJet/Expansion`; nothing here mentions the Kepler problem.
-/

@[expose] public noncomputable section

open Filter Asymptotics Topology

namespace KAM.Planetary.OrbitJet

/-- Coefficients of a polynomial of degree at most four in a real variable `t`. -/
@[ext] structure Jet5 where
  a0 : ℂ
  a1 : ℂ
  a2 : ℂ
  a3 : ℂ
  a4 : ℂ

namespace Jet5

def ev (a : Jet5) (t : ℝ) : ℂ := a.a0 + a.a1 * t + a.a2 * t ^ 2 + a.a3 * t ^ 3 + a.a4 * t ^ 4

def add (a b : Jet5) : Jet5 := ⟨a.a0 + b.a0, a.a1 + b.a1, a.a2 + b.a2, a.a3 + b.a3, a.a4 + b.a4⟩

def neg (a : Jet5) : Jet5 := ⟨-a.a0, -a.a1, -a.a2, -a.a3, -a.a4⟩

def smul (c : ℂ) (a : Jet5) : Jet5 := ⟨c * a.a0, c * a.a1, c * a.a2, c * a.a3, c * a.a4⟩

/-- Truncated product. -/
def mul (a b : Jet5) : Jet5 :=
  ⟨a.a0 * b.a0, a.a0 * b.a1 + a.a1 * b.a0, a.a0 * b.a2 + a.a1 * b.a1 + a.a2 * b.a0,
    a.a0 * b.a3 + a.a1 * b.a2 + a.a2 * b.a1 + a.a3 * b.a0,
    a.a0 * b.a4 + a.a1 * b.a3 + a.a2 * b.a2 + a.a3 * b.a1 + a.a4 * b.a0⟩

def const (c : ℂ) : Jet5 := ⟨c, 0, 0, 0, 0⟩

/-- The variable `t`. -/
def var : Jet5 := ⟨0, 1, 0, 0, 0⟩

/-- The degree-four Taylor polynomial of the exponential, as a jet. -/
def exp (a : Jet5) : Jet5 :=
  add (add (add (add (const 1) a) (smul (1 / 2) (mul a a))) (smul (1 / 6) (mul a (mul a a))))
    (smul (1 / 24) (mul a (mul a (mul a a))))

theorem continuous_ev (a : Jet5) : Continuous a.ev := by unfold ev; fun_prop

theorem ev_add (a b : Jet5) (t : ℝ) : (add a b).ev t = a.ev t + b.ev t := by
  simp only [ev, add]; ring

theorem ev_neg (a : Jet5) (t : ℝ) : (neg a).ev t = -a.ev t := by
  simp only [ev, neg]; ring

theorem ev_smul (c : ℂ) (a : Jet5) (t : ℝ) : (smul c a).ev t = c * a.ev t := by
  simp only [ev, smul]; ring

theorem ev_const (c : ℂ) (t : ℝ) : (const c).ev t = c := by simp [ev, const]

theorem ev_var (t : ℝ) : var.ev t = t := by simp [ev, var]

/-- The truncation error of a product. -/
def mulRem (a b : Jet5) (t : ℝ) : ℂ :=
  (a.a1 * b.a4 + a.a2 * b.a3 + a.a3 * b.a2 + a.a4 * b.a1) +
    (a.a2 * b.a4 + a.a3 * b.a3 + a.a4 * b.a2) * t + (a.a3 * b.a4 + a.a4 * b.a3) * t ^ 2 +
    a.a4 * b.a4 * t ^ 3

theorem ev_mul (a b : Jet5) (t : ℝ) :
    a.ev t * b.ev t = (mul a b).ev t + t ^ 5 * mulRem a b t := by
  simp only [ev, mul, mulRem]; ring

theorem continuous_mulRem (a b : Jet5) : Continuous (mulRem a b) := by unfold mulRem; fun_prop

end Jet5

open Jet5

/-- `f t = a.ev t + O(t⁵)` as `t → 0`. -/
def IsJet (f : ℝ → ℂ) (a : Jet5) : Prop :=
  (fun t => f t - a.ev t) =O[𝓝 0] fun t : ℝ => t ^ 5

private theorem pow5_isBigO_one : (fun t : ℝ => t ^ 5) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
  ((continuous_pow 5).tendsto 0).isBigO_one ℝ

private theorem cpow5_isBigO : (fun t : ℝ => (t : ℂ) ^ 5) =O[𝓝 0] fun t : ℝ => t ^ 5 :=
  IsBigO.of_bound 1 (Eventually.of_forall fun t => by simp)

private theorem cself_isBigO : (fun t : ℝ => (t : ℂ)) =O[𝓝 0] fun t : ℝ => t :=
  IsBigO.of_bound 1 (Eventually.of_forall fun t => by simp)

private theorem ev_isBigO_one (a : Jet5) : a.ev =O[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
  (a.continuous_ev.tendsto 0).isBigO_one ℝ

theorem IsJet.bigO {f : ℝ → ℂ} {a : Jet5} (h : IsJet f a) :
    (fun t => f t - a.ev t) =O[𝓝 0] fun t : ℝ => t ^ 5 := h

theorem IsJet.isBigO_one {f : ℝ → ℂ} {a : Jet5} (h : IsJet f a) :
    f =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := by
  have := (h.bigO.trans pow5_isBigO_one).add (ev_isBigO_one a)
  simpa using this

theorem IsJet.add {f g : ℝ → ℂ} {a b : Jet5} (hf : IsJet f a) (hg : IsJet g b) :
    IsJet (fun t => f t + g t) (Jet5.add a b) := by
  have := hf.bigO.add hg.bigO
  refine this.congr_left fun t => ?_
  simp only [ev_add]; ring

theorem IsJet.neg {f : ℝ → ℂ} {a : Jet5} (hf : IsJet f a) :
    IsJet (fun t => -f t) (Jet5.neg a) := by
  refine hf.bigO.neg_left.congr_left fun t => ?_
  simp only [ev_neg]; ring

theorem IsJet.sub {f g : ℝ → ℂ} {a b : Jet5} (hf : IsJet f a) (hg : IsJet g b) :
    IsJet (fun t => f t - g t) (Jet5.add a (Jet5.neg b)) := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

theorem IsJet.const_mul (c : ℂ) {f : ℝ → ℂ} {a : Jet5} (hf : IsJet f a) :
    IsJet (fun t => c * f t) (Jet5.smul c a) := by
  have := hf.bigO.const_mul_left c
  refine this.congr_left fun t => ?_
  simp only [ev_smul]; ring

theorem IsJet.mul {f g : ℝ → ℂ} {a b : Jet5} (hf : IsJet f a) (hg : IsJet g b) :
    IsJet (fun t => f t * g t) (Jet5.mul a b) := by
  have h1 : (fun t => f t * (g t - b.ev t)) =O[𝓝 0] fun t : ℝ => t ^ 5 := by
    have := hf.isBigO_one.mul hg.bigO
    simpa using this
  have h2 : (fun t => (f t - a.ev t) * b.ev t) =O[𝓝 0] fun t : ℝ => t ^ 5 := by
    have := hf.bigO.mul (ev_isBigO_one b)
    simpa using this
  have h3 : (fun t => t ^ 5 * mulRem a b t) =O[𝓝 0] fun t : ℝ => t ^ 5 := by
    have := cpow5_isBigO.mul (((continuous_mulRem a b).tendsto 0).isBigO_one ℝ)
    simpa using this
  have := (h1.add h2).add h3
  refine this.congr_left fun t => ?_
  have := ev_mul a b t
  simp only; linear_combination (-1 : ℂ) * this

theorem isJet_const (c : ℂ) : IsJet (fun _ => c) (Jet5.const c) := by
  simp only [IsJet, ev_const, sub_self]; exact isBigO_zero _ _

theorem isJet_var : IsJet (fun t : ℝ => (t : ℂ)) Jet5.var := by
  simp only [IsJet, ev_var, sub_self]; exact isBigO_zero _ _

theorem isJet_ev (a : Jet5) : IsJet a.ev a := by
  simp only [IsJet, sub_self]; exact isBigO_zero _ _

theorem IsJet.congr {f g : ℝ → ℂ} {a : Jet5} (hf : IsJet f a) (h : ∀ t, f t = g t) :
    IsJet g a := by
  have : f = g := funext h
  rwa [← this]

theorem IsJet.congr_jet {f : ℝ → ℂ} {a b : Jet5} (hf : IsJet f a) (h : a = b) : IsJet f b := by
  rwa [← h]

/-- A jet with vanishing constant term is `O(t)`. -/
theorem IsJet.isBigO_self {f : ℝ → ℂ} {a : Jet5} (hf : IsJet f a) (h0 : a.a0 = 0) :
    f =O[𝓝 0] fun t : ℝ => t := by
  have h5 : (fun t : ℝ => t ^ 5) =O[𝓝 0] fun t : ℝ => t := by
    refine IsBigO.of_bound 1 ?_
    have : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 := by
      have := Metric.ball_mem_nhds (0 : ℝ) one_pos
      filter_upwards [this] with t ht
      simpa using ht
    filter_upwards [this] with t ht
    simp only [norm_pow, Real.norm_eq_abs, one_mul]
    calc |t| ^ 5 ≤ |t| ^ 1 := pow_le_pow_of_le_one (abs_nonneg t) ht.le (by norm_num)
      _ = |t| := pow_one _
  have hev : a.ev =O[𝓝 0] fun t : ℝ => t := by
    have e : a.ev = fun t : ℝ => t * (a.a1 + a.a2 * t + a.a3 * t ^ 2 + a.a4 * t ^ 3) := by
      funext t; simp only [ev, h0]; ring
    rw [e]
    have hc : Continuous fun t : ℝ => a.a1 + a.a2 * t + a.a3 * t ^ 2 + a.a4 * t ^ 3 := by
      fun_prop
    have := cself_isBigO.mul ((hc.tendsto 0).isBigO_one ℝ)
    simpa using this
  have := (hf.bigO.trans h5).add hev
  refine this.congr_left fun t => ?_
  simp

theorem isJet_exp {y : ℝ → ℂ} {a : Jet5} (hy : IsJet y a) (h0 : a.a0 = 0) :
    IsJet (fun t => Complex.exp (y t)) (Jet5.exp a) := by
  have hyO := hy.isBigO_self h0
  have h1 : IsJet (fun t => 1 + y t + 1 / 2 * (y t * y t) + 1 / 6 * (y t * (y t * y t)) +
      1 / 24 * (y t * (y t * (y t * y t)))) (Jet5.exp a) :=
    ((((isJet_const 1).add hy).add ((hy.mul hy).const_mul (1 / 2))).add
      ((hy.mul (hy.mul hy)).const_mul (1 / 6))).add
      ((hy.mul (hy.mul (hy.mul hy))).const_mul (1 / 24))
  have hlim : Tendsto y (𝓝 0) (𝓝 0) := hyO.trans_tendsto (tendsto_id)
  have hsmall : ∀ᶠ t in 𝓝 0, ‖y t‖ ≤ 1 := by
    filter_upwards [Metric.tendsto_nhds.1 hlim 1 one_pos] with t ht
    simpa using ht.le
  have h2 : (fun t => Complex.exp (y t) - (1 + y t + 1 / 2 * (y t * y t) +
      1 / 6 * (y t * (y t * y t)) + 1 / 24 * (y t * (y t * (y t * y t))))) =O[𝓝 0]
        fun t : ℝ => (y t) ^ 5 := by
    refine IsBigO.of_bound (1 / 100) ?_
    filter_upwards [hsmall] with t ht
    have key := Complex.exp_bound ht (n := 5) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at key
    have e : (1 + y t + 1 / 2 * (y t * y t) + 1 / 6 * (y t * (y t * y t)) +
        1 / 24 * (y t * (y t * (y t * y t)))) =
        (1 + y t + y t ^ 2 / 2 + y t ^ 3 / 6 + y t ^ 4 / 24) := by ring
    rw [e, norm_pow, mul_comm]
    simpa using key
  have h3 := h2.trans (hyO.pow 5)
  have := h3.add h1.bigO
  refine this.congr_left fun t => ?_
  ring

/-- The Kepler fixed-point map `s ↦ t (A e^s - B e^{-s}) / 2`. -/
def kepPhi (A B : ℂ) (t : ℝ) (s : ℂ) : ℂ :=
  (t : ℂ) * (A * Complex.exp s - B * Complex.exp (-s)) / 2

private theorem norm_exp_le_two {s : ℂ} (hs : ‖s‖ ≤ 1 / 2) : ‖Complex.exp s‖ ≤ 2 := by
  refine (Complex.norm_exp_le_exp_norm s).trans ?_
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_add (1 / 2) (1 / 2)
  have h3 : Real.exp ‖s‖ ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 hs
  have h4 := Real.exp_pos (1 / 2)
  norm_num at h2
  nlinarith

private theorem norm_exp_sub_le {s s' : ℂ} (hs : ‖s‖ ≤ 1 / 2) (hs' : ‖s'‖ ≤ 1 / 2) :
    ‖Complex.exp s - Complex.exp s'‖ ≤ 4 * ‖s - s'‖ := by
  have hd : ‖s - s'‖ ≤ 1 := (norm_sub_le _ _).trans (by linarith)
  have e : Complex.exp s - Complex.exp s' =
      Complex.exp s' * (Complex.exp (s - s') - 1) := by
    rw [mul_sub, ← Complex.exp_add]; simp
  rw [e, norm_mul]
  have h1 := norm_exp_le_two hs'
  have h2 := Complex.norm_exp_sub_one_le hd
  have h3 := norm_nonneg (Complex.exp (s - s') - 1)
  nlinarith

private theorem norm_kepPhi_sub_le (A B : ℂ) (t : ℝ) {s s' : ℂ} (hs : ‖s‖ ≤ 1 / 2)
    (hs' : ‖s'‖ ≤ 1 / 2) :
    ‖kepPhi A B t s - kepPhi A B t s'‖ ≤ 2 * |t| * (‖A‖ + ‖B‖) * ‖s - s'‖ := by
  have h1 := norm_exp_sub_le hs hs'
  have h2 := norm_exp_sub_le (s := -s) (s' := -s') (by simpa using hs) (by simpa using hs')
  have e : kepPhi A B t s - kepPhi A B t s' = (t : ℂ) / 2 *
      (A * (Complex.exp s - Complex.exp s') - B * (Complex.exp (-s) - Complex.exp (-s'))) := by
    unfold kepPhi; ring
  have e2 : ‖-s - -s'‖ = ‖s - s'‖ := by rw [← norm_neg]; congr 1; ring
  rw [e2] at h2
  rw [e, norm_mul]
  have h3 : ‖A * (Complex.exp s - Complex.exp s') - B * (Complex.exp (-s) - Complex.exp (-s'))‖
      ≤ ‖A‖ * (4 * ‖s - s'‖) + ‖B‖ * (4 * ‖s - s'‖) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    gcongr
  have h4 : ‖(t : ℂ) / 2‖ = |t| / 2 := by simp
  rw [h4]
  have h5 : 0 ≤ |t| / 2 := by positivity
  calc |t| / 2 * ‖_‖ ≤ |t| / 2 * (‖A‖ * (4 * ‖s - s'‖) + ‖B‖ * (4 * ‖s - s'‖)) :=
        mul_le_mul_of_nonneg_left h3 h5
    _ = 2 * |t| * (‖A‖ + ‖B‖) * ‖s - s'‖ := by ring

/-- The contraction argument: an exact solution of `y = kepPhi A B t y`, small of order `t`, that is
approximately fixed by a polynomial `a.ev` to order `t⁵`, is that jet. -/
theorem isJet_of_fixedPoint (A B : ℂ) (a : Jet5) (h0 : a.a0 = 0) {y : ℝ → ℂ}
    (hy : ∀ᶠ t in 𝓝 (0 : ℝ), y t = kepPhi A B t (y t)) (hyO : y =O[𝓝 0] fun t : ℝ => t)
    (hfix : (fun t => kepPhi A B t (a.ev t) - a.ev t) =O[𝓝 0] fun t : ℝ => t ^ 5) :
    IsJet y a := by
  have hyl : Tendsto y (𝓝 0) (𝓝 0) := hyO.trans_tendsto tendsto_id
  have hevl : Tendsto a.ev (𝓝 0) (𝓝 0) := by
    have := a.continuous_ev.tendsto 0
    simpa [ev, h0] using this
  have hs1 : ∀ᶠ t in 𝓝 (0 : ℝ), ‖y t‖ ≤ 1 / 2 := by
    filter_upwards [Metric.tendsto_nhds.1 hyl (1 / 2) (by norm_num)] with t ht
    simpa using ht.le
  have hs2 : ∀ᶠ t in 𝓝 (0 : ℝ), ‖a.ev t‖ ≤ 1 / 2 := by
    filter_upwards [Metric.tendsto_nhds.1 hevl (1 / 2) (by norm_num)] with t ht
    simpa using ht.le
  have hs3 : ∀ᶠ t in 𝓝 (0 : ℝ), 2 * |t| * (‖A‖ + ‖B‖) ≤ 1 / 2 := by
    have hc : Continuous fun t : ℝ => 2 * |t| * (‖A‖ + ‖B‖) := by fun_prop
    have := hc.tendsto 0
    simp only [abs_zero, mul_zero, zero_mul] at this
    filter_upwards [Metric.tendsto_nhds.1 this (1 / 2) (by norm_num)] with t ht
    have := (le_abs_self _).trans ht.le
    simpa [Real.dist_eq] using this
  have hb : (fun t => y t - a.ev t) =O[𝓝 0] fun t => kepPhi A B t (a.ev t) - a.ev t := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [hy, hs1, hs2, hs3] with t h h1 h2 h3
    have hl := norm_kepPhi_sub_le A B t h1 h2
    have e : y t - a.ev t = (kepPhi A B t (y t) - kepPhi A B t (a.ev t)) +
        (kepPhi A B t (a.ev t) - a.ev t) := by rw [← h]; ring
    have hn := (norm_add_le (kepPhi A B t (y t) - kepPhi A B t (a.ev t))
      (kepPhi A B t (a.ev t) - a.ev t))
    rw [← e] at hn
    have hm : 2 * |t| * (‖A‖ + ‖B‖) * ‖y t - a.ev t‖ ≤ 1 / 2 * ‖y t - a.ev t‖ :=
      mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    linarith
  exact hb.trans hfix

end KAM.Planetary.OrbitJet

end
