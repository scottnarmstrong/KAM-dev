/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.OrbitJet
public import KAM.Planetary.PlanarTorsion.PairJet.Rot

/-!
# Planar quartic torsion: the jet of the pair integrand along a line

Blueprint P, Part 11b (`stepP:p11b:pj-formal`, `stepP:p11b:pj-bin`): for fixed angles `l` and a
direction `w`, the function `t ↦ |α z_orb(l₀; t w₀) - z_orb(l₁; t w₁)|⁻¹` equals, up to `O(t⁵)`, the
degree-four polynomial whose coefficients are the binomial expansion of `N^{-1/2}` for the jet `N`
    of
`|α z₁ - z₂|²` (`p11cPJray`).  The inverse square root of a jet is identified without any Taylor
series by uniqueness: if `P² N = 1 (mod t⁵)` and `G² N = 1`, then `G = P + O(t⁵)`.
-/

@[expose] public noncomputable section
open Filter Asymptotics Topology Set Real
namespace KAM.Planetary
open KAM.Planetary.OrbitJet

/-- The integrand of the pair average at the angles `l` and the slow variable `z`. -/
def p11cPJF (a : ℝ) (l : Fin 2 → ℝ) (z : Phase 2) : ℝ :=
  ‖(a : ℂ) * p11c_orbit (l 0) ![z.1 0, z.2 0] - p11c_orbit (l 1) ![z.1 1, z.2 1]‖⁻¹

/-! ### Complex conjugation of jets -/

/-- The complex conjugate jet. -/
def p11cPJconj (a : Jet5) : Jet5 :=
  ⟨(starRingEnd ℂ) a.a0, (starRingEnd ℂ) a.a1, (starRingEnd ℂ) a.a2, (starRingEnd ℂ) a.a3,
    (starRingEnd ℂ) a.a4⟩

theorem p11cPJconj_ev (a : Jet5) (t : ℝ) : (p11cPJconj a).ev t = (starRingEnd ℂ) (a.ev t) := by
  simp [Jet5.ev, p11cPJconj, map_add, map_mul, map_pow, Complex.conj_ofReal]

theorem p11cPJ_isJet_conj {f : ℝ → ℂ} {a : Jet5} (h : IsJet f a) :
    IsJet (fun t => (starRingEnd ℂ) (f t)) (p11cPJconj a) := by
  unfold IsJet at h ⊢
  obtain ⟨C, hC⟩ := h.bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hC] with t ht
  have : ‖(starRingEnd ℂ) (f t) - (p11cPJconj a).ev t‖ = ‖f t - a.ev t‖ := by
    rw [p11cPJconj_ev, ← map_sub, RCLike.norm_conj]
  rw [this]; exact ht

theorem p11cPJ_tendsto_of_isJet {f : ℝ → ℂ} {a : Jet5} (h : IsJet f a) :
    Tendsto f (𝓝 0) (𝓝 a.a0) := by
  have h1 : Tendsto (fun t => f t - a.ev t) (𝓝 0) (𝓝 0) := by
    refine h.bigO.trans_tendsto ?_
    simpa using ((continuous_pow 5).tendsto (0 : ℝ))
  have h2 : Tendsto a.ev (𝓝 0) (𝓝 a.a0) := by
    have := a.continuous_ev.tendsto 0
    simpa [Jet5.ev] using this
  simpa using h1.add h2

/-! ### The inverse norm of a jet -/

theorem p11cPJ_isJet_inv_norm {u : ℝ → ℂ} {U P : Jet5} (hu : IsJet u U) (hU : U.a0 ≠ 0)
    (hP0 : P.a0 = ((‖U.a0‖⁻¹ : ℝ) : ℂ))
    (hPP : Jet5.mul (Jet5.mul P P) (Jet5.mul U (p11cPJconj U)) = Jet5.const 1) :
    IsJet (fun t => (((‖u t‖⁻¹ : ℝ)) : ℂ)) P := by
  set N : ℝ → ℂ := fun t => u t * (starRingEnd ℂ) (u t) with hNdef
  have hN : IsJet N (Jet5.mul U (p11cPJconj U)) := hu.mul (p11cPJ_isJet_conj hu)
  have hH : IsJet (fun t => P.ev t) P := isJet_ev P
  have hHHN := (hH.mul hH).mul hN
  rw [hPP] at hHHN
  have hHHN' : (fun t => P.ev t * P.ev t * N t - 1) =O[𝓝 0] fun t : ℝ => t ^ 5 := by
    refine hHHN.bigO.congr_left fun t => ?_
    simp [Jet5.ev_const]
  have hut : Tendsto u (𝓝 0) (𝓝 U.a0) := p11cPJ_tendsto_of_isJet hu
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ), u t ≠ 0 := hut.eventually_ne hU
  have hnorm0 : 0 < ‖U.a0‖ := norm_pos_iff.2 hU
  have hG : Tendsto (fun t => (((‖u t‖⁻¹ : ℝ)) : ℂ)) (𝓝 0) (𝓝 (((‖U.a0‖⁻¹ : ℝ)) : ℂ)) := by
    have := (hut.norm.inv₀ hnorm0.ne')
    exact (Complex.continuous_ofReal.tendsto _).comp this
  have hHt : Tendsto (fun t => P.ev t) (𝓝 0) (𝓝 P.a0) := by
    have := P.continuous_ev.tendsto 0
    rwa [show P.ev (0 : ℝ) = P.a0 by simp [Jet5.ev]] at this
  have hNt : Tendsto N (𝓝 0) (𝓝 (U.a0 * (starRingEnd ℂ) U.a0)) :=
    hut.mul ((Complex.continuous_conj.tendsto _).comp hut)
  set G : ℝ → ℂ := fun t => (((‖u t‖⁻¹ : ℝ)) : ℂ) with hGdef
  have hK : Tendsto (fun t => (G t + P.ev t) * N t) (𝓝 0)
      (𝓝 (((((‖U.a0‖⁻¹ : ℝ)) : ℂ) + P.a0) * (U.a0 * (starRingEnd ℂ) U.a0))) :=
    (hG.add hHt).mul hNt
  have hL : ((((‖U.a0‖⁻¹ : ℝ)) : ℂ) + P.a0) * (U.a0 * (starRingEnd ℂ) U.a0) ≠ 0 := by
    rw [hP0, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have : ((‖U.a0‖⁻¹ : ℝ) : ℂ) + ((‖U.a0‖⁻¹ : ℝ) : ℂ) = ((2 * ‖U.a0‖⁻¹ : ℝ) : ℂ) := by
      push_cast; ring
    rw [this]
    have h2 : (2 * ‖U.a0‖⁻¹ : ℝ) * ‖U.a0‖ ^ 2 ≠ 0 := by positivity
    exact_mod_cast h2
  have hprod : (fun t => (G t - P.ev t) * ((G t + P.ev t) * N t)) =O[𝓝 0] fun t : ℝ => t ^ 5 := by
    refine (hHHN'.neg_left).congr' ?_ EventuallyEq.rfl
    filter_upwards [hne] with t ht
    have hGN : G t * G t * N t = 1 := by
      simp only [hGdef, hNdef]
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have h1 : ‖u t‖ ≠ 0 := norm_ne_zero_iff.2 ht
      have h' : ((‖u t‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1
      push_cast
      field_simp
    linear_combination -hGN
  have hinv : (fun t => ((G t + P.ev t) * N t)⁻¹) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
    (hK.inv₀ hL).isBigO_one ℝ
  have hKne : ∀ᶠ t in 𝓝 (0 : ℝ), (G t + P.ev t) * N t ≠ 0 := hK.eventually_ne hL
  have h5 := hprod.mul hinv
  unfold IsJet
  refine h5.congr' ?_ ?_
  · filter_upwards [hKne] with t ht
    exact mul_inv_cancel_right₀ ht _
  · filter_upwards with t
    simp

/-! ### The jets of the pair integrand -/

/-- The jet of `N^{-1/2}` given the jet `N` of `N` and `S = N₀^{-1/2}`. -/
def p11cPJcJet (N : Jet5) (S : ℂ) : Jet5 :=
  ⟨S, -(1 / 2) * S ^ 3 * N.a1, -(1 / 2) * S ^ 3 * N.a2 + 3 / 8 * S ^ 5 * N.a1 ^ 2,
    -(1 / 2) * S ^ 3 * N.a3 + 3 / 4 * S ^ 5 * (N.a1 * N.a2) - 5 / 16 * S ^ 7 * N.a1 ^ 3,
    -(1 / 2) * S ^ 3 * N.a4 + 3 / 4 * S ^ 5 * (N.a1 * N.a3) + 3 / 8 * S ^ 5 * N.a2 ^ 2 -
      15 / 16 * S ^ 7 * (N.a1 ^ 2 * N.a2) + 35 / 128 * S ^ 9 * N.a1 ^ 4⟩

theorem p11cPJcJet_sq (N : Jet5) (S : ℂ) (hS : S ^ 2 * N.a0 = 1) :
    Jet5.mul (Jet5.mul (p11cPJcJet N S) (p11cPJcJet N S)) N = Jet5.const 1 := by
  have hS0 : S ≠ 0 := by
    intro h; rw [h] at hS; simp at hS
  have h0 : N.a0 = (S ^ 2)⁻¹ := by
    field_simp; linear_combination hS
  ext <;> simp only [Jet5.mul, p11cPJcJet, Jet5.const, h0] <;> field_simp <;> ring

theorem p11cPJ_N_rot (a ζ0 ζb0 ζ1 ζb1 X0 Xi0 X1 Xi1 : ℂ) (h0 : X0 * Xi0 = 1)
    (h1 : X1 * Xi1 = 1) :
    Jet5.mul (Jet5.add (Jet5.smul a (refJet ζ0 ζb0 X0 Xi0)) (Jet5.neg (refJet ζ1 ζb1 X1 Xi1)))
      (Jet5.add (Jet5.smul a (refJet ζb0 ζ0 Xi0 X0)) (Jet5.neg (refJet ζb1 ζ1 Xi1 X1))) =
    p11cPJN a (ζ0 * Xi0) (ζb0 * X0) (ζ1 * Xi1) (ζb1 * X1) (X0 * Xi1) (Xi0 * X1) := by
  have hX0 : X0 ≠ 0 := left_ne_zero_of_mul_eq_one h0
  have hX1 : X1 ≠ 0 := left_ne_zero_of_mul_eq_one h1
  obtain rfl : Xi0 = X0⁻¹ := eq_inv_of_mul_eq_one_right h0
  obtain rfl : Xi1 = X1⁻¹ := eq_inv_of_mul_eq_one_right h1
  ext <;> simp only [Jet5.mul, Jet5.add, Jet5.smul, Jet5.neg, refJet, p11cPJN, p11cPJv, p11cPJj1,
    p11cPJj2, p11cPJj3, p11cPJj4] <;> field_simp <;> ring

theorem p11cPJE_one (θ : ℝ) : p11cPJE 1 θ = Complex.exp (Complex.I * (θ : ℂ)) := by
  simp [p11cPJE]

theorem p11cPJE_neg_one (θ : ℝ) : p11cPJE (-1) θ = Complex.exp (-(Complex.I * (θ : ℂ))) := by
  unfold p11cPJE; congr 1; push_cast; ring

theorem p11cPJS_sq {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (θ : ℝ) :
    p11cPJS a θ ^ 2 * p11cKer a θ = 1 := by
  have h := p11cPJS_pow ha 2 θ
  have hk := p11cKer_pos ha θ
  rw [h]
  have : p11cKer a θ ^ (((2 : ℕ) : ℝ) / 2) = p11cKer a θ := by
    norm_num
  rw [this]
  field_simp

/-- The rotated jet of `|α z₁ - z₂|²` at the angles `l`. -/
def p11cPJrotN (a : ℝ) (ζ1 ζb1 ζ2 ζb2 : ℂ) (l : Fin 2 → ℝ) : Jet5 :=
  p11cPJN (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE 1 (l 0)) (ζ2 * p11cPJE (-1) (l 1))
    (ζb2 * p11cPJE 1 (l 1)) (p11cPJE 1 (l 0) * p11cPJE (-1) (l 1))
    (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1))

/-- The jet of the pair integrand along the line `t ↦ t w`, in rotated variables. -/
def p11cPJrot (a : ℝ) (ζ1 ζb1 ζ2 ζb2 : ℂ) (l : Fin 2 → ℝ) : Jet5 :=
  p11cPJcJet (p11cPJrotN a ζ1 ζb1 ζ2 ζb2 l) ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ)

theorem p11cPJconj_refJet (ζ ζb X Xi : ℂ) :
    p11cPJconj (refJet ζ ζb X Xi) =
      refJet ((starRingEnd ℂ) ζ) ((starRingEnd ℂ) ζb) ((starRingEnd ℂ) X) ((starRingEnd ℂ) Xi) := by
  ext <;> simp [p11cPJconj, refJet, map_add, map_sub, map_mul, map_div₀, map_pow, map_ofNat]

theorem p11cPJconj_add (A B : Jet5) :
    p11cPJconj (Jet5.add A B) = Jet5.add (p11cPJconj A) (p11cPJconj B) := by
  ext <;> simp [p11cPJconj, Jet5.add]

theorem p11cPJconj_smul (c : ℂ) (A : Jet5) :
    p11cPJconj (Jet5.smul c A) = Jet5.smul ((starRingEnd ℂ) c) (p11cPJconj A) := by
  ext <;> simp [p11cPJconj, Jet5.smul]

theorem p11cPJconj_neg (A : Jet5) : p11cPJconj (Jet5.neg A) = Jet5.neg (p11cPJconj A) := by
  ext <;> simp [p11cPJconj, Jet5.neg]

theorem p11cPJ_cos_two (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ)) + Complex.exp (-(Complex.I * (x : ℂ))) =
      ((2 * Real.cos x : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  rw [show Complex.I * (x : ℂ) = (x : ℂ) * Complex.I by ring,
    show -((x : ℂ) * Complex.I) = -(x : ℂ) * Complex.I by ring]
  ring

/-- Along every line the pair integrand is the degree-four jet `p11cPJrot`, up to `O(t⁵)`. -/
theorem p11cPJ_ray {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (l : Fin 2 → ℝ) (w : Phase 2) :
    IsJet (fun t : ℝ => ((p11cPJF a l (t • w) : ℝ) : ℂ))
      (p11cPJrot a ((w.1 0 : ℂ) + Complex.I * (w.2 0 : ℂ)) ((w.1 0 : ℂ) - Complex.I * (w.2 0 : ℂ))
        ((w.1 1 : ℂ) + Complex.I * (w.2 1 : ℂ)) ((w.1 1 : ℂ) - Complex.I * (w.2 1 : ℂ)) l) := by
  set ζ0 : ℂ := (w.1 0 : ℂ) + Complex.I * (w.2 0 : ℂ) with hζ0
  set ζb0 : ℂ := (w.1 0 : ℂ) - Complex.I * (w.2 0 : ℂ) with hζb0
  set ζ1 : ℂ := (w.1 1 : ℂ) + Complex.I * (w.2 1 : ℂ) with hζ1
  set ζb1 : ℂ := (w.1 1 : ℂ) - Complex.I * (w.2 1 : ℂ) with hζb1
  set X0 : ℂ := Complex.exp (Complex.I * (l 0 : ℂ)) with hX0
  set Xi0 : ℂ := Complex.exp (-(Complex.I * (l 0 : ℂ))) with hXi0
  set X1 : ℂ := Complex.exp (Complex.I * (l 1 : ℂ)) with hX1
  set Xi1 : ℂ := Complex.exp (-(Complex.I * (l 1 : ℂ))) with hXi1
  have hXX0 : X0 * Xi0 = 1 := by rw [hX0, hXi0, ← Complex.exp_add]; simp
  have hXX1 : X1 * Xi1 = 1 := by rw [hX1, hXi1, ← Complex.exp_add]; simp
  have hO0 := orbit_line_isJet (l 0) ![w.1 0, w.2 0]
  have hO1 := orbit_line_isJet (l 1) ![w.1 1, w.2 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hO0 hO1
  set U : Jet5 := Jet5.add (Jet5.smul (a : ℂ) (refJet ζ0 ζb0 X0 Xi0))
    (Jet5.neg (refJet ζ1 ζb1 X1 Xi1)) with hU
  have hu : IsJet (fun t : ℝ => (a : ℂ) * p11c_orbit (l 0) (t • ![w.1 0, w.2 0]) -
      p11c_orbit (l 1) (t • ![w.1 1, w.2 1])) U := (hO0.const_mul (a : ℂ)).sub hO1
  have hcζ0 : (starRingEnd ℂ) ζ0 = ζb0 := by
    simp [hζ0, hζb0, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg]
  have hcζb0 : (starRingEnd ℂ) ζb0 = ζ0 := by
    simp [hζ0, hζb0, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hcζ1 : (starRingEnd ℂ) ζ1 = ζb1 := by
    simp [hζ1, hζb1, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg]
  have hcζb1 : (starRingEnd ℂ) ζb1 = ζ1 := by
    simp [hζ1, hζb1, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hcX0 : (starRingEnd ℂ) X0 = Xi0 := by
    rw [hX0, hXi0, ← Complex.exp_conj]; simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hcXi0 : (starRingEnd ℂ) Xi0 = X0 := by
    rw [hX0, hXi0, ← Complex.exp_conj]; simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hcX1 : (starRingEnd ℂ) X1 = Xi1 := by
    rw [hX1, hXi1, ← Complex.exp_conj]; simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hcXi1 : (starRingEnd ℂ) Xi1 = X1 := by
    rw [hX1, hXi1, ← Complex.exp_conj]; simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hcU : p11cPJconj U = Jet5.add (Jet5.smul (a : ℂ) (refJet ζb0 ζ0 Xi0 X0))
      (Jet5.neg (refJet ζb1 ζ1 Xi1 X1)) := by
    rw [hU, p11cPJconj_add, p11cPJconj_smul, p11cPJconj_neg, p11cPJconj_refJet, p11cPJconj_refJet,
      hcζ0, hcζb0, hcX0, hcXi0, hcζ1, hcζb1, hcX1, hcXi1, Complex.conj_ofReal]
  set Nj : Jet5 := p11cPJrotN a ζ0 ζb0 ζ1 ζb1 l with hNj
  have hNj' : Nj = p11cPJN (a : ℂ) (ζ0 * Xi0) (ζb0 * X0) (ζ1 * Xi1) (ζb1 * X1) (X0 * Xi1)
      (Xi0 * X1) := by
    simp only [hNj, p11cPJrotN, p11cPJE_one, p11cPJE_neg_one, hX0, hXi0, hX1, hXi1]
  have hMul : Jet5.mul U (p11cPJconj U) = Nj := by
    rw [hcU, hNj', hU]
    exact p11cPJ_N_rot (a : ℂ) ζ0 ζb0 ζ1 ζb1 X0 Xi0 X1 Xi1 hXX0 hXX1
  have hker := p11cKer_pos ha (l 0 - l 1)
  have hN0 : Nj.a0 = ((p11cKer a (l 0 - l 1) : ℝ) : ℂ) := by
    have hr : X0 * Xi1 + Xi0 * X1 = ((2 * Real.cos (l 0 - l 1) : ℝ) : ℂ) := by
      rw [← p11cPJ_cos_two]
      simp only [hX0, hXi0, hX1, hXi1, ← Complex.exp_add]
      congr 2 <;> push_cast <;> ring
    simp only [hNj, p11cPJrotN, p11cPJN, p11cPJv, Jet5.add, Jet5.mul, Jet5.smul, Jet5.neg,
      p11cPJE_one, p11cPJE_neg_one, ← hX0, ← hXi0, ← hX1, ← hXi1]
    unfold p11cKer
    push_cast
    push_cast at hr
    linear_combination (-(a : ℂ)) * hr
  set S : ℂ := ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) with hS
  have hS2 : S ^ 2 * Nj.a0 = 1 := by
    rw [hN0, hS]
    exact_mod_cast p11cPJS_sq ha (l 0 - l 1)
  have hUa0 : U.a0 = (a : ℂ) * X0 - X1 := by
    simp [hU, refJet, Jet5.add, Jet5.smul, Jet5.neg, sub_eq_add_neg]
  have hnorm2 : ‖U.a0‖ ^ 2 = p11cKer a (l 0 - l 1) := by
    have h1 := congrArg Jet5.a0 hMul
    simp only [Jet5.mul, p11cPJconj] at h1
    rw [hN0, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h1
    exact_mod_cast h1
  have hUne : U.a0 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm2
    simp at hnorm2
    linarith
  have hP0 : (p11cPJcJet Nj S).a0 = ((‖U.a0‖⁻¹ : ℝ) : ℂ) := by
    have hs : ‖U.a0‖ = √(p11cKer a (l 0 - l 1)) := by
      rw [← hnorm2, Real.sqrt_sq (norm_nonneg _)]
    simp only [p11cPJcJet, hS, hs]
    congr 1
    unfold p11cPJS
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hker.le]
  have hPP : Jet5.mul (Jet5.mul (p11cPJcJet Nj S) (p11cPJcJet Nj S))
      (Jet5.mul U (p11cPJconj U)) = Jet5.const 1 := by
    rw [hMul]
    exact p11cPJcJet_sq Nj S hS2
  have key := p11cPJ_isJet_inv_norm hu hUne hP0 hPP
  refine key.congr fun t => ?_
  have h0 : (![(t • w).1 0, (t • w).2 0] : Fin 2 → ℝ) = t • ![w.1 0, w.2 0] := by
    ext i; fin_cases i <;> simp
  have h1 : (![(t • w).1 1, (t • w).2 1] : Fin 2 → ℝ) = t • ![w.1 1, w.2 1] := by
    ext i; fin_cases i <;> simp
  simp only [p11cPJF, h0, h1]

end KAM.Planetary

end
