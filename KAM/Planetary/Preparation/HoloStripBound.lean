/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.HoloStripGeometry

/-!
# The complexified fixed perturbation on the strip (P11A-P2c, `stepP:p11:hc-strip`)

`p11hsFHat D w = -G Σ_{i<j} m_i m_j s_ij^{-1/2}` (principal root) on a complex phase point `w` of
`P11Phase (n+n)` (fast block first), with `s_ij = p11hsSep` the complexified squared separation of
the Poincaré planets of `w`. On the set `p11hsGood` where `Re s_ij ≥ (a_j-a_i)²/4` it is
holomorphic (`p11hsFHat_differentiableOn`), bounded by the explicit constant `p11hsMInf`
(`p11hsFHat_norm_le`), and `2π`-periodic in each fast angle (`p11hsFHat_shift`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler SecularForm

section Bound

variable {n : ℕ}

/-- The fast (angle) block of a complex phase point. -/
def p11hsAngle (w : P11Phase (n + n)) : CVec n := fun i => w.1 (Fin.castAdd n i)

/-- The slow block `(ξ, Λ, η)` of a complex phase point. -/
def p11hsSlow (w : P11Phase (n + n)) : CSlow n :=
  (fun i => w.1 (Fin.natAdd n i), fun i => w.2 (Fin.castAdd n i), fun i => w.2 (Fin.natAdd n i))

/-- `f̂_fix` complexified: `-G Σ_{i<j} m_i m_j s_ij^{-1/2}` with the principal root. -/
def p11hsFHat (D : Data n) (w : P11Phase (n + n)) : ℂ :=
  -(D.G : ℂ) * ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
    (D.m i : ℂ) * D.m j * p11hsSep D (p11hsAngle w) (p11hsSlow w) i j ^ (-1 / 2 : ℂ)

/-- The good set: imaginary angles below `1/4`, slow part in the polydisc, strip bound. -/
def p11hsGood (D : Data n) (a : Vec n) (r : ℝ) : Set (P11Phase (n + n)) :=
  {w | (∀ l, |(p11hsAngle w l).im| < 1 / 4) ∧ p11hsSlow w ∈ polydisc D a r ∧
    ∀ i j : Fin n, i < j → (a j - a i) ^ 2 / 4 ≤ (p11hsSep D (p11hsAngle w) (p11hsSlow w) i j).re}

/-- The explicit sup bound `G Σ_{i<j} m_i m_j · 2 / (a_j - a_i)`. -/
def p11hsMInf (D : Data n) (a : Vec n) : ℝ :=
  D.G * ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), D.m i * D.m j * (2 / (a j - a i))

theorem p11hsMInf_nonneg (D : Data n) {a : Vec n} (ha : a ∈ axes n) : 0 ≤ p11hsMInf D a := by
  unfold p11hsMInf
  refine mul_nonneg D.hG.le (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j hj => ?_)
  have hij : i < j := (Finset.mem_filter.1 hj).2
  have : 0 < a j - a i := sub_pos.2 (ha.2 hij)
  have := D.hm i; have := D.hm j
  positivity

theorem norm_cpow_neg_half_le {s : ℂ} {c : ℝ} (hc : 0 < c) (hs : c ^ 2 ≤ s.re) :
    ‖s ^ (-1 / 2 : ℂ)‖ ≤ 1 / c := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; nlinarith
  have hsn : c ^ 2 ≤ ‖s‖ := hs.trans (Complex.re_le_norm s)
  rw [Complex.norm_cpow_of_ne_zero hs0]
  have h1 : (-1 / 2 : ℂ).re = -1 / 2 := by norm_num
  have h2 : (-1 / 2 : ℂ).im = 0 := by norm_num
  rw [h1, h2, mul_zero, Real.exp_zero, div_one]
  have h3 : ‖s‖ ^ (-1 / 2 : ℝ) ≤ (c ^ 2) ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hsn (by norm_num)
  refine h3.trans (le_of_eq ?_)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
  norm_num
  rw [Real.rpow_neg_one]

theorem p11hsFHat_norm_le (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    {w : P11Phase (n + n)} (hw : w ∈ p11hsGood D a r) : ‖p11hsFHat D w‖ ≤ p11hsMInf D a := by
  unfold p11hsFHat p11hsMInf
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg D.hG.le]
  refine mul_le_mul_of_nonneg_left ?_ D.hG.le
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hij : i < j := (Finset.mem_filter.1 hj).2
  have hpos : 0 < (a j - a i) / 2 := by linarith [sub_pos.2 (ha.2 hij)]
  have h := norm_cpow_neg_half_le hpos (s := p11hsSep D (p11hsAngle w) (p11hsSlow w) i j)
    (by have := hw.2.2 i j hij; nlinarith)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (D.hm i).le,
    Real.norm_of_nonneg (D.hm j).le]
  have : 1 / ((a j - a i) / 2) = 2 / (a j - a i) := by field_simp
  rw [this] at h
  have := D.hm i; have := D.hm j
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem differentiable_p11hsBlock (k : Fin n) :
    Differentiable ℂ (fun w : P11Phase (n + n) => p11hsBlock (p11hsAngle w) (p11hsSlow w) k) := by
  refine Differentiable.prodMk (differentiable_pi.2 fun c => ?_)
    (differentiable_pi.2 fun c => ?_) <;> fin_cases c <;>
    simp [p11hsAngle, p11hsSlow] <;> fun_prop

theorem differentiableOn_p11hsPlanet (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a) (k : Fin n) :
    DifferentiableOn ℂ (fun w => p11hsPlanet D (p11hsAngle w) (p11hsSlow w) k)
      (p11hsGood D a r) := by
  have h := (poincare_holomorphic (m := D.m k) (κ := D.G * D.m0) (Λo := action D a k)
    (D.hm k) (mul_pos D.hG D.hm0) (action_pos D ha k)).2.2.1
  exact h.comp (differentiable_p11hsBlock k).differentiableOn fun w hw =>
    p11hsBlock_mem_nbhd D ha hr hw.2.1 hw.1 k

theorem differentiableOn_p11hsSep (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a) (i j : Fin n) :
    DifferentiableOn ℂ (fun w => p11hsSep D (p11hsAngle w) (p11hsSlow w) i j)
      (p11hsGood D a r) := by
  unfold p11hsSep
  refine DifferentiableOn.fun_sum fun c _ => ?_
  have hc : ∀ k, DifferentiableOn ℂ (fun w => (p11hsPlanet D (p11hsAngle w) (p11hsSlow w) k).1 c)
      (p11hsGood D a r) := fun k =>
    (show Differentiable ℂ (fun v : (Fin 2 → ℂ) × (Fin 2 → ℂ) => v.1 c) by fun_prop
      ).comp_differentiableOn (differentiableOn_p11hsPlanet D ha hr k)
  exact ((hc i).sub (hc j)).pow 2

/-- `hc-strip`: `f̂_fix` is holomorphic on the good set. -/
theorem p11hsFHat_differentiableOn (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a) : DifferentiableOn ℂ (p11hsFHat D) (p11hsGood D a r) := by
  unfold p11hsFHat
  refine DifferentiableOn.const_mul ?_ _
  refine DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j hj => ?_
  have hij : i < j := (Finset.mem_filter.1 hj).2
  refine DifferentiableOn.const_mul ?_ _
  refine (differentiableOn_p11hsSep D ha hr i j).cpow_const fun w hw => ?_
  have h := hw.2.2 i j hij
  have : 0 < (a j - a i) ^ 2 / 4 := by
    have : 0 < a j - a i := sub_pos.2 (ha.2 hij)
    positivity
  exact Complex.mem_slitPlane_iff.2 (Or.inl (by linarith))

/-- `hc-F` (periodicity): an integer `2π`-shift of the fast angles leaves `f̂_fix` unchanged. -/
theorem p11hsFHat_shift (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ} (hr : r < rho D a)
    {w w' : P11Phase (n + n)} (hw : p11hsSlow w ∈ polydisc D a r)
    (hl : ∀ l, |(p11hsAngle w l).im| < 1 / 4) (k : Fin n → ℤ)
    (hang : p11hsAngle w' = fun l => p11hsAngle w l + 2 * π * (k l : ℂ))
    (hsl : p11hsSlow w' = p11hsSlow w) : p11hsFHat D w' = p11hsFHat D w := by
  unfold p11hsFHat
  rw [hang, hsl]
  simp only [p11hsSep_shift D ha hr hw hl k]

theorem p11hsPlanet_im_zero (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a) {w : P11Phase (n + n)} (hw : w ∈ p11hsGood D a r)
    (him : ∀ l, (w.1 l).im = 0 ∧ (w.2 l).im = 0) (k : Fin n) (c : Fin 2) :
    ((p11hsPlanet D (p11hsAngle w) (p11hsSlow w) k).1 c).im = 0 := by
  have hmem := p11hsBlock_mem_nbhd D ha hr hw.2.1 hw.1 k
  have hre : ∀ z : ℂ, z.im = 0 → z = ((z.re : ℝ) : ℂ) := fun z h => Complex.ext (by simp) (by simp [h])
  set b : Phase 2 := (![(w.1 (Fin.castAdd n k)).re, (w.1 (Fin.natAdd n k)).re],
    ![(w.2 (Fin.castAdd n k)).re, (w.2 (Fin.natAdd n k)).re]) with hb
  have hblk : p11hsBlock (p11hsAngle w) (p11hsSlow w) k = phaseToC b := by
    refine Prod.ext (funext fun e => ?_) (funext fun e => ?_) <;> fin_cases e <;>
      simp [p11hsBlock, p11hsAngle, p11hsSlow, phaseToC, hb] <;>
      first
      | exact hre _ (him _).1
      | exact hre _ (him _).2
  have hreal := (poincare_holomorphic (m := D.m k) (κ := D.G * D.m0) (Λo := action D a k)
    (D.hm k) (mul_pos D.hG D.hm0) (action_pos D ha k)).2.2.2.2 b (hblk ▸ hmem)
  unfold p11hsPlanet
  rw [hblk, hreal.2]
  simp [phaseToC]

theorem p11hsSep_im_zero (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a) {w : P11Phase (n + n)} (hw : w ∈ p11hsGood D a r)
    (him : ∀ l, (w.1 l).im = 0 ∧ (w.2 l).im = 0) (i j : Fin n) :
    (p11hsSep D (p11hsAngle w) (p11hsSlow w) i j).im = 0 := by
  unfold p11hsSep
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  have h1 := p11hsPlanet_im_zero D ha hr hw him i c
  have h2 := p11hsPlanet_im_zero D ha hr hw him j c
  rw [pow_two, Complex.mul_im]
  simp [h1, h2]

/-- At real phase points `f̂_fix` is real. -/
theorem p11hsFHat_real (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a) {w : P11Phase (n + n)} (hw : w ∈ p11hsGood D a r)
    (him : ∀ l, (w.1 l).im = 0 ∧ (w.2 l).im = 0) : (p11hsFHat D w).im = 0 := by
  have hterm : ∀ i j : Fin n, i < j →
      p11hsSep D (p11hsAngle w) (p11hsSlow w) i j ^ (-1 / 2 : ℂ) =
        (((p11hsSep D (p11hsAngle w) (p11hsSlow w) i j).re ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
    intro i j hij
    have him' := p11hsSep_im_zero D ha hr hw him i j
    have hpos : 0 < (p11hsSep D (p11hsAngle w) (p11hsSlow w) i j).re := by
      have := hw.2.2 i j hij
      have : 0 < (a j - a i) ^ 2 / 4 := by
        have : 0 < a j - a i := sub_pos.2 (ha.2 hij)
        positivity
      linarith
    have hs : p11hsSep D (p11hsAngle w) (p11hsSlow w) i j =
        (((p11hsSep D (p11hsAngle w) (p11hsSlow w) i j).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simpa using him')
    rw [Complex.ofReal_cpow hpos.le]
    rw [← hs]
    norm_num
  have : p11hsFHat D w = ((-(D.G) * ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
      D.m i * D.m j * (p11hsSep D (p11hsAngle w) (p11hsSlow w) i j).re ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
    unfold p11hsFHat
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    rw [hterm i j (Finset.mem_filter.1 hj).2]
  rw [this, Complex.ofReal_im]

end Bound

end KAM.Planetary

end
