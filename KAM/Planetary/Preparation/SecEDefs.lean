/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Preparation.PreparedBasic

/-!
# The domain `E` of Step E and the mapping iff (`bpP:p11:sec-E`)

`E = {|Im (θ, ζ)| < σ_F/72, |r|_∞ < 2, |ρ'|_∞ < π/2}` is `p11SecE`, on its whole complex carrier,
and `p11Rescale_polydisc_iff` is the source's assertion that `A_ε` maps the entire radius-`(2, π/2)`
action polydisc into `V₂/2` if and only if `2 ε ≤ s₂/2` (standing regime `0 < ε`, `0 < n`).
-/

@[expose] public noncomputable section
open Set
namespace KAM.Planetary

variable {n : ℕ}

/-- The action polydisc `{|r|_∞ < 2, |ρ'|_∞ < π/2}` of Step E (centre `0`). -/
def p11SecEPolydisc (n : ℕ) : Set (P11CVec (n+n)) := p11Box 0 2 (Real.pi/2)

/-- The domain `E` of `bpP:p11:sec-E`: angle strip of width `σ_F/72` times the polydisc. -/
def p11SecE (C : P11SecularData n) : Set (P11Phase (n+n)) :=
  KAM.complexStrip (n+n) (C.sigma/72) ×ˢ p11SecEPolydisc n

theorem mem_p11SecE {C : P11SecularData n} {z : P11Phase (n+n)} :
    z ∈ p11SecE C ↔ (∀ i, |(z.1 i).im| < C.sigma/72) ∧
      (∀ i : Fin n, ‖z.2 (Fin.castAdd n i)‖ < 2) ∧
      ∀ i : Fin n, ‖z.2 (Fin.natAdd n i)‖ < Real.pi/2 := by
  simp [p11SecE, p11SecEPolydisc, p11Box, KAM.complexStrip, Set.mem_prod]

/-- The mapping iff of `bpP:p11:sec-E`: `A_ε` maps the whole polydisc `{|r|<2, |ρ'|<π/2}` into
`V₂/2` (radii `s₂/2` about `J₀`, `π ε/2` about `ρ̃₀`) iff `2 ε ≤ s₂/2`. -/
theorem p11Rescale_polydisc_iff (C : P11SecularData n) (nu eps : ℝ) (hn : 0 < n)
    (heps : 0 < eps) :
    (∀ z : P11Phase (n+n), z.2 ∈ p11SecEPolydisc n →
      (p11Rescale C.J0 eps z).2 ∈
        p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2)) ↔
      2*eps ≤ p11s2 C nu eps/2 := by
  have hfast : ∀ (z : P11Phase (n+n)) (i : Fin n),
      (p11Rescale C.J0 eps z).2 (Fin.castAdd n i) - p11SlowCenter C eps (Fin.castAdd n i) =
        (eps : ℂ) * z.2 (Fin.castAdd n i) := fun z i => by
    simp [p11Rescale, p11SlowCenter, Fin.append_left]
  have hslow : ∀ (z : P11Phase (n+n)) (i : Fin n),
      (p11Rescale C.J0 eps z).2 (Fin.natAdd n i) - p11SlowCenter C eps (Fin.natAdd n i) =
        (eps : ℂ) * z.2 (Fin.natAdd n i) := fun z i => by
    simp [p11Rescale, p11SlowCenter]; ring
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    set r := p11s2 C nu eps/2 with hr
    set t : ℝ := max 0 (r/eps) with ht
    have ht2 : t < 2 := max_lt (by norm_num) ((div_lt_iff₀ heps).2 (by linarith))
    have hrt : r ≤ eps*t := by
      rcases le_total r 0 with h0 | h0
      · exact h0.trans (by positivity)
      · calc r = eps*(r/eps) := by field_simp
          _ ≤ eps*t := mul_le_mul_of_nonneg_left (le_max_right _ _) heps.le
    let z : P11Phase (n+n) := (0, Fin.append (fun _ : Fin n => (t : ℂ)) (fun _ => 0))
    have hz : z.2 ∈ p11SecEPolydisc n := by
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simp only [z, Pi.zero_apply, sub_zero, Fin.append_left, Complex.norm_real,
          Real.norm_eq_abs]
        rw [abs_of_nonneg (le_max_left _ _)]; exact ht2
      · simp only [z, Pi.zero_apply, sub_zero, Fin.append_right, norm_zero]; positivity
    have h1 := (h z hz).1 ⟨0, hn⟩
    rw [hfast, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heps] at h1
    simp only [z, Fin.append_left, Complex.norm_real, Real.norm_eq_abs] at h1
    rw [abs_of_nonneg (le_max_left (0:ℝ) (r/eps))] at h1
    linarith
  · intro h z hz
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [hfast, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heps]
      have := hz.1 i
      simp only [Pi.zero_apply, sub_zero] at this
      nlinarith
    · rw [hslow, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heps]
      have := hz.2 i
      simp only [Pi.zero_apply, sub_zero] at this
      nlinarith

/-- The mapping iff on `E` itself (`0 < σ_F` makes the angle strip nonempty). -/
theorem p11Rescale_secE_iff (C : P11SecularData n) (nu eps : ℝ) (hn : 0 < n) (hσ : 0 < C.sigma)
    (heps : 0 < eps) :
    (∀ z ∈ p11SecE C, (p11Rescale C.J0 eps z).2 ∈
        p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2)) ↔
      2*eps ≤ p11s2 C nu eps/2 := by
  rw [← p11Rescale_polydisc_iff C nu eps hn heps]
  refine ⟨fun h z hz => ?_, fun h z hz => h z hz.2⟩
  have hθ : (0 : P11CVec (n+n)) ∈ KAM.complexStrip (n+n) (C.sigma/72) := fun i => by
    simpa using (by positivity : 0 < C.sigma/72)
  have := h (0, z.2) ⟨hθ, hz⟩
  simpa [p11Rescale] using this

end KAM.Planetary

end
