/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.OrbitJet.Expansion

/-!
# Planar quartic torsion: the complex form of the regular Kepler equation

The unit-axis orbit in complex notation, `p11c_orbit lam v = k e^{iF} - z + (d / (1 + k)) z` with
`z = v₀ + i v₁`, `k = √(1 - |v|²)` and `d = v · e_F`, and the Kepler equation `Φ(F, v) = λ` as the
fixed-point equation `y = (b e^{iλ} e^y - z e^{-iλ} e^{-y}) / 2` for `y = i (F - λ)`.
-/

@[expose] public noncomputable section

open Filter Asymptotics Topology Real

namespace KAM.Planetary.OrbitJet

open KAM KAM.Kepler Jet5

theorem orbit_eq_complex (lam : ℝ) (v : Fin 2 → ℝ) :
    p11c_orbit lam v = ((√(1 - planeSq v) : ℝ) : ℂ) *
        Complex.exp ((keplerLong lam v : ℝ) * Complex.I)
      - ((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) +
      ((planeDot v (orbitalUnit (keplerLong lam v)) : ℝ) : ℂ) *
        (((1 / (1 + √(1 - planeSq v)) : ℝ)) : ℂ) * ((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) := by
  have hE : Complex.exp ((keplerLong lam v : ℝ) * Complex.I) =
      ((Real.cos (keplerLong lam v) : ℝ) : ℂ) + ((Real.sin (keplerLong lam v) : ℝ) : ℂ) *
        Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [hE]
  apply Complex.ext
  · simp [p11c_orbit, orbitalUnit, div_eq_mul_inv, Matrix.vecHead, Matrix.vecTail]
  · simp [p11c_orbit, orbitalUnit, div_eq_mul_inv, Matrix.vecHead, Matrix.vecTail]

theorem kepler_complex (v : Fin 2 → ℝ) (F lam : ℝ) (hF : keplerPhi v F = lam) :
    Complex.I * ((F : ℂ) - lam) =
      (((v 0 : ℂ) - Complex.I * (v 1 : ℂ)) * Complex.exp ((F : ℂ) * Complex.I) -
        ((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) * Complex.exp (-((F : ℂ) * Complex.I))) / 2 ∧
    ((planeDot v (orbitalUnit F) : ℝ) : ℂ) =
      (((v 0 : ℂ) - Complex.I * (v 1 : ℂ)) * Complex.exp ((F : ℂ) * Complex.I) +
        ((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) * Complex.exp (-((F : ℂ) * Complex.I))) / 2 := by
  have hE : Complex.exp ((F : ℂ) * Complex.I) = Complex.cos F + Complex.sin F * Complex.I :=
    Complex.exp_mul_I _
  have hEb : Complex.exp (-((F : ℂ) * Complex.I)) = Complex.cos F - Complex.sin F * Complex.I := by
    rw [← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]; ring
  have hFc : (F : ℂ) - (v 0 : ℂ) * Complex.sin F + (v 1 : ℂ) * Complex.cos F = lam := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hF
    simpa [keplerPhi] using this
  have hd : ((planeDot v (orbitalUnit F) : ℝ) : ℂ) =
      (v 0 : ℂ) * Complex.cos F + (v 1 : ℂ) * Complex.sin F := by
    simp [planeDot, Fin.sum_univ_two, orbitalUnit]
  rw [hE, hEb, hd]
  constructor
  · linear_combination Complex.I * hFc
  · linear_combination ((v 1 : ℂ) * Complex.sin F) * Complex.I_sq

theorem exp_split (lam F : ℝ) :
    Complex.exp ((F : ℂ) * Complex.I) =
      Complex.exp (Complex.I * lam) * Complex.exp (Complex.I * ((F : ℂ) - lam)) ∧
    Complex.exp (-((F : ℂ) * Complex.I)) =
      Complex.exp (-(Complex.I * lam)) * Complex.exp (-(Complex.I * ((F : ℂ) - lam))) := by
  constructor <;> (rw [← Complex.exp_add]; congr 1; ring)

theorem isJet_kepPhi {A B : ℂ} {y : ℝ → ℂ} {a : Jet5} (hy : IsJet y a) (h0 : a.a0 = 0) :
    IsJet (fun t => kepPhi A B t (y t)) (kepJet A B a) := by
  have h1 := isJet_exp hy h0
  have h2 := isJet_exp hy.neg (a := Jet5.neg a) (by simp [Jet5.neg, h0])
  have h3 := isJet_var.mul ((h1.const_mul A).add (h2.const_mul B).neg)
  have h4 := h3.const_mul (1 / 2)
  refine h4.congr fun t => ?_
  unfold kepPhi; ring

private theorem planeSq_two' (v : Fin 2 → ℝ) : planeSq v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

private theorem planeSq_smul'' (t : ℝ) (w : Fin 2 → ℝ) :
    planeSq (t • w) = t ^ 2 * planeSq w := by
  simp only [planeSq_two', Pi.smul_apply, smul_eq_mul]; ring

theorem IsJet.congr_ev {f g : ℝ → ℂ} {a : Jet5} (hf : IsJet f a)
    (h : ∀ᶠ t : ℝ in 𝓝 0, f t = g t) : IsJet g a :=
  hf.bigO.congr' (h.mono fun t ht => by simp [ht]) EventuallyEq.rfl

/-- Along every line the unit-axis orbit is the displayed degree-four jet, up to `O(t⁵)`. -/
theorem orbit_line_isJet (lam : ℝ) (w : Fin 2 → ℝ) :
    IsJet (fun t : ℝ => p11c_orbit lam (t • w))
      (refJet ((w 0 : ℂ) + Complex.I * (w 1 : ℂ)) ((w 0 : ℂ) - Complex.I * (w 1 : ℂ))
        (Complex.exp (Complex.I * lam)) (Complex.exp (-(Complex.I * lam)))) := by
  set ζ : ℂ := (w 0 : ℂ) + Complex.I * (w 1 : ℂ) with hζ
  set ζb : ℂ := (w 0 : ℂ) - Complex.I * (w 1 : ℂ) with hζb
  set X : ℂ := Complex.exp (Complex.I * lam) with hX
  set Xi : ℂ := Complex.exp (-(Complex.I * lam)) with hXi
  have hXXi : X * Xi = 1 := by rw [hX, hXi, ← Complex.exp_add]; simp
  set cR : ℝ := planeSq w with hcRdef
  have hcR : 0 ≤ cR := by rw [hcRdef, planeSq_two']; positivity
  have hc : ζ * ζb = (cR : ℂ) := by
    rw [hcRdef, planeSq_two']; push_cast
    rw [hζ, hζb]; linear_combination (-(w 1 : ℂ) ^ 2) * Complex.I_sq
  have hlen : ∀ᶠ t : ℝ in 𝓝 0, planeLength (t • w) < 1 := by
    have hcont : Continuous fun t : ℝ => |t| * planeLength w := by fun_prop
    have := hcont.tendsto 0
    simp only [abs_zero, zero_mul] at this
    filter_upwards [Metric.tendsto_nhds.1 this 1 one_pos] with t ht
    rw [planeLength_smul]
    exact (le_abs_self _).trans_lt
      (by simpa [Real.dist_eq] using ht : |(|t| * planeLength w)| < 1)
  set A : ℂ := ζb * X with hA
  set B : ℂ := ζ * Xi with hB
  set y : ℝ → ℂ := fun t => Complex.I * (((keplerLong lam (t • w) : ℝ) : ℂ) - lam) with hy
  have hyfix : ∀ᶠ t : ℝ in 𝓝 0, y t = kepPhi A B t (y t) := by
    filter_upwards [hlen] with t ht
    obtain ⟨hK1, -⟩ := kepler_complex (t • w) (keplerLong lam (t • w)) lam
      (keplerPhi_keplerLong ht lam)
    obtain ⟨e1, e2⟩ := exp_split lam (keplerLong lam (t • w))
    rw [e1, e2] at hK1
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul] at hK1
    calc y t = _ := hK1
      _ = _ := by simp only [kepPhi, hA, hB, hζ, hζb]; ring
  have hyO : y =O[𝓝 0] fun t : ℝ => t := by
    refine IsBigO.of_bound (|w 0| + |w 1|) ?_
    filter_upwards [hlen] with t ht
    have hF := keplerPhi_keplerLong ht lam
    simp only [keplerPhi, Pi.smul_apply, smul_eq_mul] at hF
    have e : keplerLong lam (t • w) - lam =
        t * w 0 * Real.sin (keplerLong lam (t • w)) -
          t * w 1 * Real.cos (keplerLong lam (t • w)) := by
      linarith
    have hn : ‖y t‖ = |keplerLong lam (t • w) - lam| := by
      simp only [hy, norm_mul, Complex.norm_I, one_mul]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hn, e, Real.norm_eq_abs]
    have h1 := Real.abs_sin_le_one (keplerLong lam (t • w))
    have h2 := Real.abs_cos_le_one (keplerLong lam (t • w))
    have b0 : |t * w 0 * Real.sin (keplerLong lam (t • w))| ≤ |t| * |w 0| := by
      rw [abs_mul, abs_mul]; exact mul_le_of_le_one_right (by positivity) h1
    have b1 : |t * w 1 * Real.cos (keplerLong lam (t • w))| ≤ |t| * |w 1| := by
      rw [abs_mul, abs_mul]; exact mul_le_of_le_one_right (by positivity) h2
    have := abs_sub (t * w 0 * Real.sin (keplerLong lam (t • w)))
      (t * w 1 * Real.cos (keplerLong lam (t • w)))
    nlinarith
  have hfix : (fun t => kepPhi A B t ((aJet A B).ev t) - (aJet A B).ev t) =O[𝓝 0]
      fun t : ℝ => t ^ 5 := by
    have h1 := isJet_kepPhi (A := A) (B := B) (isJet_ev (aJet A B)) rfl
    rw [kepJet_aJet] at h1
    exact h1.bigO
  have hyJ : IsJet y (aJet A B) := isJet_of_fixedPoint A B (aJet A B) rfl hyfix hyO hfix
  have hk : IsJet (fun t : ℝ => ((√(1 - t ^ 2 * cR) : ℝ) : ℂ)) (kJet (ζ * ζb)) := by
    rw [hc]; exact isJet_sqrt cR hcR
  have hw : IsJet (fun t : ℝ => ((1 / (1 + √(1 - t ^ 2 * cR)) : ℝ) : ℂ)) (wJet (ζ * ζb)) := by
    rw [hc]; exact isJet_inv_sqrt cR hcR
  have hEx := isJet_exp hyJ rfl
  have hEn := isJet_exp hyJ.neg (a := Jet5.neg (aJet A B)) (by simp [Jet5.neg, aJet])
  have hz := isJet_var.const_mul ζ
  have hpd := (isJet_var.mul (((hEx.const_mul A).add (hEn.const_mul B)))).const_mul (1 / 2)
  set f : ℝ → ℂ := fun t => ((√(1 - t ^ 2 * cR) : ℝ) : ℂ) * (X * Complex.exp (y t)) +
    -(ζ * (t : ℂ)) + 1 / 2 * ((t : ℂ) * (A * Complex.exp (y t) + B * Complex.exp (-y t))) *
      ((1 / (1 + √(1 - t ^ 2 * cR)) : ℝ) : ℂ) * (ζ * (t : ℂ)) with hf
  have total : IsJet f _ := ((hk.mul (hEx.const_mul X)).add hz.neg).add ((hpd.mul hw).mul hz)
  have key : ∀ᶠ t : ℝ in 𝓝 0, f t = p11c_orbit lam (t • w) := by
    filter_upwards [hlen] with t ht
    obtain ⟨-, hK2⟩ := kepler_complex (t • w) (keplerLong lam (t • w)) lam
      (keplerPhi_keplerLong ht lam)
    obtain ⟨e1, e2⟩ := exp_split lam (keplerLong lam (t • w))
    rw [e1, e2] at hK2
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul] at hK2
    rw [orbit_eq_complex, e1, planeSq_smul'', hK2]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, hf, hy, hA, hB, hζ, hζb, hX, hXi,
      hcRdef]
    ring
  have := (total.congr_ev key).congr_jet (oJet_eq_refJet ζ ζb X Xi hXXi)
  exact this

end KAM.Planetary.OrbitJet

end
