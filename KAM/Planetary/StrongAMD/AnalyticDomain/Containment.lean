/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.AnalyticDomain.Safety
public import KAM.Planetary.Exponential.ComplexTube

/-!
# Containment of MAIN's domain (22) in the complex tube of the core

Package LP-DOM, `LP:MAIN L8 (261–271)` with amendment N3 (`r_* ≤ 4 r_g`), track LP, non-frozen; the
statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

D5 `strongCore_containment`: a complex chart point `z = ((λ, ξ), (Λ, η))` whose complex actions lie
within `r_*` of `I⁰ ∈ L_δ`, whose fast angles have `‖Im λ‖_∞ < 4s`, and whose complex slow
coordinates `(ξ, η)` lie within sup distance `4b` of a real point of the ball
`{(ξ, η) : ∑ (ξ_i² + η_i²)/2 ≤ B(I⁰) - δ/4}` (MAIN (21), (22)) lies in `complexTube core (R/2)`
as soon as `max r_* (max (4s) (4b)) < R/2`.  Shape: the chart point is a pair of vectors in
`Fin (n + n) → ℂ` (fast block first, as `tube` is typed on `Phase (n + n)`).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set Metric

variable {n : ℕ} {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ r : ℝ}

/-- The real slow ball `{(ξ, η) : ∑ (ξ_i² + η_i²)/2 ≤ B(I⁰) - δ/4}` of MAIN (21). -/
def secularBall (ν : Fin n → ℝ) (δ : ℝ) (I0 : Fin n → ℝ) : Set (Phase n) :=
  {y | ∑ i, (y.1 i ^ 2 + y.2 i ^ 2) / 2 ≤ strongThreshold ν I0 - δ / 4}

/-- D5 (`LP:MAIN L8 (261–271)`, (22), N3). -/
theorem strongCore_containment {rs s b R : ℝ} (hrs : 0 < rs) (hrg : rs ≤ 4 * r)
    (hmax : max rs (max (4 * s) (4 * b)) < R / 2)
    {I0 : Fin n → ℝ} (hI0 : I0 ∈ strongLevelSet ν L δ)
    {z : (Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)}
    (hact : ‖(fun i => z.2 (Fin.castAdd n i)) - fun i => ((I0 i : ℝ) : ℂ)‖ < rs)
    (hang : ‖fun i => (z.1 (Fin.castAdd n i)).im‖ < 4 * s)
    (hslow : ∃ y ∈ secularBall ν δ I0,
      ‖(fun i => z.1 (Fin.natAdd n i)) - fun i => ((y.1 i : ℝ) : ℂ)‖ < 4 * b ∧
      ‖(fun i => z.2 (Fin.natAdd n i)) - fun i => ((y.2 i : ℝ) : ℂ)‖ < 4 * b) :
    z ∈ complexTube (strongCore ν L δ r) (R / 2) := by
  obtain ⟨y, hy, hy1, hy2⟩ := hslow
  have hR : 0 < R / 2 := lt_of_le_of_lt (le_max_of_le_left hrs.le) hmax
  have hmax1 : rs < R / 2 := lt_of_le_of_lt (le_max_left _ _) hmax
  have hmax2 : 4 * s < R / 2 :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hmax
  have hmax3 : 4 * b < R / 2 :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hmax
  have hpi := Real.pi_pos
  set k : Fin n → ℤ := fun i => ⌊(z.1 (Fin.castAdd n i)).re / (2 * Real.pi)⌋ with hk
  set x : Phase (n + n) :=
    (Fin.append (fun i => (z.1 (Fin.castAdd n i)).re - 2 * Real.pi * (k i : ℝ)) y.1,
     Fin.append (fun i => (z.2 (Fin.castAdd n i)).re) y.2) with hx
  have hxcore : x ∈ strongCore ν L δ r := by
    refine ⟨fun i => ?_, I0, hI0, ?_, ?_⟩
    · have e1 := Int.floor_le ((z.1 (Fin.castAdd n i)).re / (2 * Real.pi))
      have e2 := Int.lt_floor_add_one ((z.1 (Fin.castAdd n i)).re / (2 * Real.pi))
      rw [le_div_iff₀ (by positivity)] at e1
      rw [div_lt_iff₀ (by positivity)] at e2
      simp only [fast, hx, Fin.append_left, hk]
      constructor <;> nlinarith
    · have h4 : (0 : ℝ) ≤ 4 * r := by linarith
      rw [pi_norm_le_iff_of_nonneg h4]
      intro i
      have h1 := (norm_le_pi_norm ((fun i => z.2 (Fin.castAdd n i)) -
        fun i => ((I0 i : ℝ) : ℂ)) i).trans_lt hact
      simp only [Pi.sub_apply] at h1
      have h2 := Complex.abs_re_le_norm (z.2 (Fin.castAdd n i) - ((I0 i : ℝ) : ℂ))
      rw [Complex.sub_re, Complex.ofReal_re] at h2
      simp only [fast, hx, Fin.append_left, Pi.sub_apply, Real.norm_eq_abs]
      linarith
    · have : chartAMD x = ∑ i, (y.1 i ^ 2 + y.2 i ^ 2) / 2 := by
        simp [chartAMD, slow, hx]
      rw [this]
      exact hy
  refine ⟨x + fastShift k, ⟨k, x, hxcore, rfl⟩, ?_⟩
  rw [Prod.norm_def]
  refine max_lt ?_ ?_
  · rw [pi_norm_lt_iff hR]
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have h1 : ‖z.1 (Fin.castAdd n i) - ((z.1 (Fin.castAdd n i)).re : ℂ)‖ =
          |(z.1 (Fin.castAdd n i)).im| := by
        have : z.1 (Fin.castAdd n i) - (((z.1 (Fin.castAdd n i)).re : ℝ) : ℂ) =
            ((z.1 (Fin.castAdd n i)).im : ℂ) * Complex.I := by
          apply Complex.ext <;> simp
        rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have h2 := (norm_le_pi_norm (fun i => (z.1 (Fin.castAdd n i)).im) i)
      rw [Real.norm_eq_abs] at h2
      simp only [KAM.Nekhoroshev.complexifyPhase, Prod.fst_sub, Pi.sub_apply, hx, fastShift,
        Prod.fst_add, Pi.add_apply, Fin.append_left]
      have : z.1 (Fin.castAdd n i) - (((z.1 (Fin.castAdd n i)).re - 2 * Real.pi * (k i : ℝ) +
          2 * Real.pi * (k i : ℝ) : ℝ) : ℂ) = z.1 (Fin.castAdd n i) -
          (((z.1 (Fin.castAdd n i)).re : ℝ) : ℂ) := by
        congr 2; ring
      rw [this, h1]
      linarith
    · have h1 := (norm_le_pi_norm ((fun i => z.1 (Fin.natAdd n i)) -
        fun i => ((y.1 i : ℝ) : ℂ)) i).trans_lt hy1
      simp only [Pi.sub_apply] at h1
      simp only [KAM.Nekhoroshev.complexifyPhase, Prod.fst_sub, Pi.sub_apply, hx, fastShift,
        Prod.fst_add, Pi.add_apply, Fin.append_right, add_zero, Pi.zero_apply]
      linarith
  · rw [pi_norm_lt_iff hR]
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have h1 := (norm_le_pi_norm ((fun i => z.2 (Fin.castAdd n i)) -
        fun i => ((I0 i : ℝ) : ℂ)) i).trans_lt hact
      simp only [Pi.sub_apply] at h1
      have h2 : ‖z.2 (Fin.castAdd n i) - ((z.2 (Fin.castAdd n i)).re : ℂ)‖ =
          |(z.2 (Fin.castAdd n i)).im| := by
        have : z.2 (Fin.castAdd n i) - (((z.2 (Fin.castAdd n i)).re : ℝ) : ℂ) =
            ((z.2 (Fin.castAdd n i)).im : ℂ) * Complex.I := by
          apply Complex.ext <;> simp
        rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have h3 := Complex.abs_im_le_norm (z.2 (Fin.castAdd n i) - ((I0 i : ℝ) : ℂ))
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h3
      simp only [KAM.Nekhoroshev.complexifyPhase, Prod.snd_sub, Pi.sub_apply, hx, fastShift,
        Prod.snd_add, Pi.add_apply, Fin.append_left, Pi.zero_apply, add_zero]
      rw [h2]
      linarith
    · have h1 := (norm_le_pi_norm ((fun i => z.2 (Fin.natAdd n i)) -
        fun i => ((y.2 i : ℝ) : ℂ)) i).trans_lt hy2
      simp only [Pi.sub_apply] at h1
      simp only [KAM.Nekhoroshev.complexifyPhase, Prod.snd_sub, Pi.sub_apply, hx, fastShift,
        Prod.snd_add, Pi.add_apply, Fin.append_right, Pi.zero_apply, add_zero]
      linarith

end KAM.Planetary.StrongAMD

end
