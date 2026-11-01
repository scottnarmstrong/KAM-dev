/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.AnalyticDomain.Safety
public import KAM.Planetary.Spatial.ComplexTube

/-!
# Containment of MAIN's spatial domain (22) in the complex tube of the core

Package LP-SP-DOM, `LP:MAIN L18 (580–597)` with `LP:MAIN L8 (261–271)` and amendments N3, N12,
track LP, non-frozen. The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

D5 `spatialStrongCore_containment`: a complex chart point `z = ((λ, ξ, v), (I, η, u))` (fast block
first, `n` fast and `2n` slow coordinates per factor) whose complex actions lie within `r_*` of
`I⁰ ∈ L_δ` (`r_* ≤ 4 r_g`, N3), whose fast angles have `‖Im λ‖_∞ < 4s`, and whose complex slow
coordinates (all `2n` pairs) lie within sup distance `4b` of a real point of the ball
`{z ∈ ℝ^{4n} : |z|₂²/2 ≤ B(I⁰) − δ/4}` (MAIN (47)) lies in `complexTubeNM core (R/2)` as soon as
`max r_* (max (4s) (4b)) < R/2`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set Metric

variable {n : ℕ} {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ r : ℝ}

/-- The real slow ball `{z ∈ ℝ^{4n} : |z|₂²/2 ≤ B(I⁰) − δ/4}` of MAIN (47), over all `2n` slow pairs. -/
def spatialSecularBall (ν : Fin n → ℝ) (δ : ℝ) (I0 : Fin n → ℝ) : Set (Phase (n + n)) :=
  {y | ((∑ k, y.1 k ^ 2) + ∑ k, y.2 k ^ 2) / 2 ≤ strongThreshold ν I0 - δ / 4}

/-- D5 (`LP:MAIN L18 (595)`, `LP:MAIN L8 (261–271)`, (22), N3): all `2n` slow pairs. -/
theorem spatialStrongCore_containment {rs s b R : ℝ} (hrs : 0 < rs) (hrg : rs ≤ 4 * r)
    (hmax : max rs (max (4 * s) (4 * b)) < R / 2)
    {I0 : Fin n → ℝ} (hI0 : I0 ∈ strongLevelSet ν L δ)
    {z : (Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)}
    (hact : ‖(fun i => z.2 (Fin.castAdd (n + n) i)) - fun i => ((I0 i : ℝ) : ℂ)‖ < rs)
    (hang : ‖fun i => (z.1 (Fin.castAdd (n + n) i)).im‖ < 4 * s)
    (hslow : ∃ y ∈ spatialSecularBall ν δ I0,
      ‖(fun i : Fin (n + n) => z.1 (Fin.natAdd n i)) - fun i => ((y.1 i : ℝ) : ℂ)‖ < 4 * b ∧
      ‖(fun i : Fin (n + n) => z.2 (Fin.natAdd n i)) - fun i => ((y.2 i : ℝ) : ℂ)‖ < 4 * b) :
    z ∈ complexTubeNM (spatialStrongCore ν L δ r) (R / 2) := by
  obtain ⟨y, hy, hy1, hy2⟩ := hslow
  have hR : 0 < R / 2 := lt_of_le_of_lt (le_max_of_le_left hrs.le) hmax
  have hmax1 : rs < R / 2 := lt_of_le_of_lt (le_max_left _ _) hmax
  have hmax2 : 4 * s < R / 2 :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hmax
  have hmax3 : 4 * b < R / 2 :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hmax
  have hpi := Real.pi_pos
  set k : Fin n → ℤ := fun i => ⌊(z.1 (Fin.castAdd (n + n) i)).re / (2 * Real.pi)⌋ with hk
  set x : Phase (n + (n + n)) :=
    (Fin.append (fun i => (z.1 (Fin.castAdd (n + n) i)).re - 2 * Real.pi * (k i : ℝ)) y.1,
     Fin.append (fun i => (z.2 (Fin.castAdd (n + n) i)).re) y.2) with hx
  have hxcore : x ∈ spatialStrongCore ν L δ r := by
    refine ⟨fun i => ?_, I0, hI0, ?_, ?_⟩
    · have e1 := Int.floor_le ((z.1 (Fin.castAdd (n + n) i)).re / (2 * Real.pi))
      have e2 := Int.lt_floor_add_one ((z.1 (Fin.castAdd (n + n) i)).re / (2 * Real.pi))
      rw [le_div_iff₀ (by positivity)] at e1
      rw [div_lt_iff₀ (by positivity)] at e2
      simp only [fast, hx, Fin.append_left, hk]
      constructor <;> nlinarith
    · have h4 : (0 : ℝ) ≤ 4 * r := by linarith
      rw [pi_norm_le_iff_of_nonneg h4]
      intro i
      have h1 := (norm_le_pi_norm ((fun i => z.2 (Fin.castAdd (n + n) i)) -
        fun i => ((I0 i : ℝ) : ℂ)) i).trans_lt hact
      simp only [Pi.sub_apply] at h1
      have h2 := Complex.abs_re_le_norm (z.2 (Fin.castAdd (n + n) i) - ((I0 i : ℝ) : ℂ))
      rw [Complex.sub_re, Complex.ofReal_re] at h2
      simp only [fast, hx, Fin.append_left, Pi.sub_apply, Real.norm_eq_abs]
      linarith
    · have : spatialSlowDeficit x = ((∑ k, y.1 k ^ 2) + ∑ k, y.2 k ^ 2) / 2 := by
        simp [spatialSlowDeficit, slow, hx]
      rw [this]
      exact hy
  refine ⟨x + fastShift k, ⟨k, x, hxcore, rfl⟩, ?_⟩
  rw [Prod.norm_def]
  refine max_lt ?_ ?_
  · rw [pi_norm_lt_iff hR]
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have h1 : ‖z.1 (Fin.castAdd (n + n) i) - ((z.1 (Fin.castAdd (n + n) i)).re : ℂ)‖ =
          |(z.1 (Fin.castAdd (n + n) i)).im| := by
        have : z.1 (Fin.castAdd (n + n) i) - (((z.1 (Fin.castAdd (n + n) i)).re : ℝ) : ℂ) =
            ((z.1 (Fin.castAdd (n + n) i)).im : ℂ) * Complex.I := by
          apply Complex.ext <;> simp
        rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have h2 := (norm_le_pi_norm (fun i => (z.1 (Fin.castAdd (n + n) i)).im) i)
      rw [Real.norm_eq_abs] at h2
      simp only [KAM.Nekhoroshev.complexifyPhase, Prod.fst_sub, Pi.sub_apply, hx, fastShift,
        Prod.fst_add, Pi.add_apply, Fin.append_left]
      have : z.1 (Fin.castAdd (n + n) i) - (((z.1 (Fin.castAdd (n + n) i)).re - 2 * Real.pi * (k i : ℝ) +
          2 * Real.pi * (k i : ℝ) : ℝ) : ℂ) = z.1 (Fin.castAdd (n + n) i) -
          (((z.1 (Fin.castAdd (n + n) i)).re : ℝ) : ℂ) := by
        congr 2; ring
      rw [this, h1]
      linarith
    · have h1 := (norm_le_pi_norm ((fun i : Fin (n + n) => z.1 (Fin.natAdd n i)) -
        fun i => ((y.1 i : ℝ) : ℂ)) i).trans_lt hy1
      simp only [Pi.sub_apply] at h1
      simp only [KAM.Nekhoroshev.complexifyPhase, Prod.fst_sub, Pi.sub_apply, hx, fastShift,
        Prod.fst_add, Pi.add_apply, Fin.append_right, add_zero, Pi.zero_apply]
      linarith
  · rw [pi_norm_lt_iff hR]
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have h1 := (norm_le_pi_norm ((fun i => z.2 (Fin.castAdd (n + n) i)) -
        fun i => ((I0 i : ℝ) : ℂ)) i).trans_lt hact
      simp only [Pi.sub_apply] at h1
      have h2 : ‖z.2 (Fin.castAdd (n + n) i) - ((z.2 (Fin.castAdd (n + n) i)).re : ℂ)‖ =
          |(z.2 (Fin.castAdd (n + n) i)).im| := by
        have : z.2 (Fin.castAdd (n + n) i) - (((z.2 (Fin.castAdd (n + n) i)).re : ℝ) : ℂ) =
            ((z.2 (Fin.castAdd (n + n) i)).im : ℂ) * Complex.I := by
          apply Complex.ext <;> simp
        rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have h3 := Complex.abs_im_le_norm (z.2 (Fin.castAdd (n + n) i) - ((I0 i : ℝ) : ℂ))
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h3
      simp only [KAM.Nekhoroshev.complexifyPhase, Prod.snd_sub, Pi.sub_apply, hx, fastShift,
        Prod.snd_add, Pi.add_apply, Fin.append_left, Pi.zero_apply, add_zero]
      rw [h2]
      linarith
    · have h1 := (norm_le_pi_norm ((fun i : Fin (n + n) => z.2 (Fin.natAdd n i)) -
        fun i => ((y.2 i : ℝ) : ℂ)) i).trans_lt hy2
      simp only [Pi.sub_apply] at h1
      simp only [KAM.Nekhoroshev.complexifyPhase, Prod.snd_sub, Pi.sub_apply, hx, fastShift,
        Prod.snd_add, Pi.add_apply, Fin.append_right, Pi.zero_apply, add_zero]
      linarith

end KAM.Planetary.Spatial

end
