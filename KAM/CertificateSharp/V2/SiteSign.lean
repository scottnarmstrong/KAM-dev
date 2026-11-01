/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.SmallDivQ

/-!
# Sites of a frequency with a negative last coordinate, on a short box

`siteOk` reads a box whose last coordinate is an exact `κ > 0`. This module uses it unchanged on a
box chosen by the witness:

* **Sign.** `sdConst_ray_of_neg`: a small-divisor constant on the ray of `-ω*` is one on the ray of
  `ω*`, because `cohR (-ω) g = -cohR ω g` (`cohR_neg`). So a test run on the reflected box
  `negBox box`, whatever the test, serves `ω*`. The statement is about `SDConst` and not about one
  checker: it applies to `siteOk` and to any other site test with the same conclusion.
* **Short box.** `siteOk` adds the terms of `balBound` as exact rationals, whose size follows the
  digits of the box. A site needs only an enclosure, so the witness gives a short box `bw`, and
  `coverOk` checks that it contains the certificate's box.

`sdConst_of_siteOk_sign` puts the two together, with the conclusion of `sdConst_of_siteOk`.
-/

@[expose] public section

open scoped Matrix.Norms.Operator

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Apost KAM.Certificate KAM.Sharp2 KAM.CertificateSharp

/-! ### The reflected box -/

/-- The box of `-ω`. -/
def negBox (box : FreqBox) : FreqBox := box.map fun b => (-b.1, b.2)

theorem negBox_getD (box : FreqBox) (i : ℕ) :
    (negBox box).getD i (0, 0) = (-(box.getD i (0, 0)).1, (box.getD i (0, 0)).2) := by
  induction box generalizing i with
  | nil => simp [negBox]
  | cons b box ih =>
    cases i with
    | zero => simp [negBox]
    | succ i => simpa [negBox] using ih i

theorem freqEncloses_negBox {n : ℕ} {box : FreqBox} {ω : Fin n → ℝ} (h : FreqEncloses n box ω) :
    FreqEncloses n (negBox box) (-ω) := fun i => by
  have := h i
  rw [negBox_getD]
  simp only [Pi.neg_apply, Rat.cast_neg]
  rwa [show -ω i - -((box.getD i.val (0, 0)).1 : ℝ) =
    -(ω i - ((box.getD i.val (0, 0)).1 : ℝ)) by ring, abs_neg]

theorem isDiophantine_neg {n : ℕ} {γ τ : ℝ} {ω : Fin n → ℝ} (h : IsDiophantine γ τ ω) :
    IsDiophantine γ τ (-ω) := fun k hk => by
  have := h k hk
  simpa only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, abs_neg] using this

/-! ### The small-divisor constant under reflection -/

theorem flowMultiplier_neg {n : ℕ} (ω : Fin n → ℝ) (k : Fin n → ℤ) :
    Diophantine.flowMultiplier (-ω) k = -Diophantine.flowMultiplier ω k := by
  simp [Diophantine.flowMultiplier, Diophantine.frequencyDot, Finset.sum_neg_distrib, mul_comm]

theorem solve_neg {n : ℕ} (ω : Fin n → ℝ) (a : (Fin n → ℤ) → ℂ) (k : Fin n → ℤ) :
    Diophantine.solve (-ω) a k = -Diophantine.solve ω a k := by
  unfold Diophantine.solve
  split_ifs
  · simp
  · rw [flowMultiplier_neg, div_neg]

/-- `𝓡_{-ω} g = -𝓡_ω g`. -/
theorem cohR_neg {n p : ℕ} (ω : Fin n → ℝ) (g : (Fin n → ℂ) → Fin p → ℂ) (θ : Fin n → ℂ) :
    cohR (-ω) g θ = -cohR ω g θ := by
  funext i
  simp only [cohR, cohSolution, Pi.neg_apply, solve_neg, neg_mul, tsum_neg]

theorem neg_mem_ray {n : ℕ} {ωstar ω : Fin n → ℝ} (h : ω ∈ ray ωstar) : -ω ∈ ray (-ωstar) := by
  obtain ⟨s, hs, rfl⟩ := h
  exact ⟨s, hs, by rw [smul_neg]⟩

/-- **The reflection of a small-divisor constant.** -/
theorem sdConst_ray_of_neg {n : ℕ} {κ γ δ c : ℝ} {ωstar : Fin n → ℝ}
    (h : SDConst n κ γ δ c (ray (-ωstar))) : SDConst n κ γ δ c (ray ωstar) where
  c_pos := h.c_pos
  delta_pos := h.delta_pos
  sol := fun ω hω r hr p g H hg hp hb ha θ hθ => by
    have := h.sol (-ω) (neg_mem_ray hω) hr g H hg hp hb ha θ hθ
    rwa [cohR_neg, norm_neg] at this
  apriori := fun ω hω r hr p q u H hu hp ha hb θ hθ => by
    refine h.apriori (-ω) (neg_mem_ray hω) hr u H hu hp ha (fun θ' hθ' => ?_) θ hθ
    have e : (fun l => (((-ω) l : ℝ) : ℂ)) = -fun l => ((ω l : ℝ) : ℂ) := by
      funext l
      simp
    rw [e, map_neg, norm_neg]
    exact hb θ' hθ'
  real := fun ω hω r hr p g H hg hp hb ha θ => by
    have := h.real (-ω) (neg_mem_ray hω) hr g H hg hp hb ha θ
    rwa [cohR_neg, norm_neg] at this

/-! ### The box of a site -/

/-- `-ω` or `ω`, by the witness's sign. -/
def signVec {n : ℕ} (neg : Bool) (ω : Fin n → ℝ) : Fin n → ℝ := if neg then -ω else ω

/-- The box of `signVec neg ω`. -/
def signBox (neg : Bool) (box : FreqBox) : FreqBox := if neg then negBox box else box

theorem freqEncloses_signBox {n : ℕ} (neg : Bool) {box : FreqBox} {ω : Fin n → ℝ}
    (h : FreqEncloses n box ω) : FreqEncloses n (signBox neg box) (signVec neg ω) := by
  cases neg
  · exact h
  · exact freqEncloses_negBox h

theorem isDiophantine_signVec {n : ℕ} (neg : Bool) {γ τ : ℝ} {ω : Fin n → ℝ}
    (h : IsDiophantine γ τ ω) : IsDiophantine γ τ (signVec neg ω) := by
  cases neg
  · exact h
  · exact isDiophantine_neg h

theorem sdConst_ray_of_signVec {n : ℕ} (neg : Bool) {κ γ δ c : ℝ} {ω : Fin n → ℝ}
    (h : SDConst n κ γ δ c (ray (signVec neg ω))) : SDConst n κ γ δ c (ray ω) := by
  cases neg
  · exact h
  · exact sdConst_ray_of_neg h

/-- The box `bw` contains the box `box`, in the first `n` coordinates. -/
def coverOk (n : ℕ) (box bw : FreqBox) : Bool :=
  (List.range n).all fun i =>
    decide (|(bw.getD i (0, 0)).1 - (box.getD i (0, 0)).1| + (box.getD i (0, 0)).2 ≤
      (bw.getD i (0, 0)).2)

/-- A box contains itself. -/
theorem coverOk_self (n : ℕ) (box : FreqBox) : coverOk n box box = true := by
  simp [coverOk]

theorem freqEncloses_of_coverOk {n : ℕ} {box bw : FreqBox} {ω : Fin n → ℝ}
    (hc : coverOk n box bw = true) (h : FreqEncloses n box ω) : FreqEncloses n bw ω := fun i => by
  simp only [coverOk, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  have h1 := h i
  have h2 := (Rat.cast_le (K := ℝ)).mpr (hc i.val i.isLt)
  push_cast at h2
  have h3 := abs_add_le (ω i - ((box.getD i.val (0, 0)).1 : ℝ))
    (((box.getD i.val (0, 0)).1 : ℝ) - ((bw.getD i.val (0, 0)).1 : ℝ))
  rw [sub_add_sub_cancel, abs_sub_comm ((box.getD i.val (0, 0)).1 : ℝ)] at h3
  linarith

/-- **Soundness of a site with a sign and a short box**: `siteOk` on `bw`, which contains the
box of `signVec neg ω*`, gives the constant on the ray of `ω*`. -/
theorem sdConst_of_siteOk_sign {n τ J : ℕ} {box bw : FreqBox} {κ γ b c : ℚ} {o : Option BiteWit}
    (neg : Bool) (hn : 1 ≤ n) (hτ : 1 ≤ τ) (hγ : 0 < γ) (hb : 0 < b) (hb1 : b ≤ 1)
    (hc : coverOk n (signBox neg box) bw = true) (h : siteOk n τ J bw κ γ b c o = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n box ωstar)
    (hdio : IsDiophantine (γ : ℝ) τ ωstar) :
    SDConst n τ (γ : ℝ) (b : ℝ) (c : ℝ) (ray ωstar) :=
  sdConst_ray_of_signVec neg (sdConst_of_siteOk hn hτ hγ hb hb1 h
    (freqEncloses_of_coverOk hc (freqEncloses_signBox neg hω)) (isDiophantine_signVec neg hdio))

end KAM.CertificateSharp.V2

end
