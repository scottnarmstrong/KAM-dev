/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.LaplaceReduction

/-!
# Planar quartic torsion: the torus average of a Fourier mode times a power of the kernel

Blueprint P, Part 11b (`stepP:p11b:pj-avg`): for `g` continuous and `2π`-periodic, the mean over
`[0,2π]²` of `e^{i p λ₁} e^{i r λ₂} g(λ₁ - λ₂)` vanishes unless `p + r = 0`, and equals
`(2π)⁻¹ ∫ e^{i p θ} g(θ) dθ` (a mean over a period) otherwise.  For `g = s^{-e/2}`, with `s` the
kernel `1 + a² - 2 a cos θ`, this is the Laplace coefficient `b_{e/2}^{(|p|)}`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Real Function Filter
open scoped Topology
namespace KAM.Planetary

/-- The kernel power `s^{-1/2}`. -/
def p11cPJS (a θ : ℝ) : ℝ := p11cKer a θ ^ (-(1 / 2 : ℝ))

theorem p11cPJS_pow {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (e : ℕ) (θ : ℝ) :
    p11cPJS a θ ^ e = (p11cKer a θ ^ ((e : ℝ) / 2))⁻¹ := by
  unfold p11cPJS
  rw [← Real.rpow_natCast, ← Real.rpow_mul (p11cKer_pos ha θ).le, ← Real.rpow_neg
    (p11cKer_pos ha θ).le]
  congr 1; ring

theorem p11cPJS_continuous {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : Continuous (p11cPJS a) :=
  (p11cKer_contDiff a).rpow_const fun θ => Or.inl (p11cKer_pos ha θ).ne'

theorem p11cPJS_periodic (a : ℝ) : Function.Periodic (p11cPJS a) (2 * π) := by
  intro θ; unfold p11cPJS p11cKer; rw [cos_add_two_pi]

theorem p11cPJS_even (a θ : ℝ) : p11cPJS a (-θ) = p11cPJS a θ := by
  unfold p11cPJS p11cKer; rw [cos_neg]

theorem p11cPJS_two_pi_sub (a θ : ℝ) : p11cPJS a (2 * π - θ) = p11cPJS a θ := by
  rw [show 2 * π - θ = -θ + 2 * π by ring, p11cPJS_periodic a (-θ), p11cPJS_even]

/-- A Banach-valued integral over `[0,2π]²` as an iterated interval integral. -/
theorem p11cPJ_integral_cell_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : (Fin 2 → ℝ) → E}
    (hg : ContinuousOn g (Set.pi univ fun _ : Fin 2 => Icc (0 : ℝ) (2 * π))) :
    ∫ t in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)), g t =
      ∫ s in (0 : ℝ)..2 * π, ∫ t in (0 : ℝ)..2 * π, g ![s, t] := by
  set e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ) with he
  have hmp : MeasurePreserving e volume volume := volume_preserving_piFinTwo (fun _ => ℝ)
  set S : Set (ℝ × ℝ) := Icc 0 (2 * π) ×ˢ Icc 0 (2 * π) with hS
  set h : ℝ × ℝ → E := fun y => g ![y.1, y.2] with hh
  have hcell : (Set.pi univ fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)) = e ⁻¹' S := by
    ext t
    simp only [Set.mem_pi, mem_univ, forall_true_left, mem_preimage, mem_prod, mem_Icc,
      Fin.forall_fin_two, MeasurableEquiv.piFinTwo_apply, he, hS]
  have hg' : ∀ x : Fin 2 → ℝ, g x = h (e x) := by
    intro x
    simp only [hh, he, MeasurableEquiv.piFinTwo_apply]
    congr 1; ext i; fin_cases i <;> rfl
  have hcont : ContinuousOn h S := by
    refine hg.comp ?_ ?_
    · fun_prop
    · rintro ⟨a, b⟩ ⟨ha, hb⟩
      have : (![a, b] : Fin 2 → ℝ) ∈ e ⁻¹' S := by
        simp [he, hS]
        exact ⟨⟨ha.1, hb.1⟩, ha.2, hb.2⟩
      rwa [← hcell] at this
  have hint : IntegrableOn h S := hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  calc ∫ t in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)), g t = ∫ x in e ⁻¹' S, h (e x) :=
      by
        rw [hcell]
        exact setIntegral_congr_fun (e.measurable (hS ▸ measurableSet_Icc.prod measurableSet_Icc))
          (fun x _ => hg' x)
    _ = ∫ y in S, h y := hmp.setIntegral_preimage_emb e.measurableEmbedding h S
    _ = ∫ s in Icc 0 (2 * π), ∫ t in Icc 0 (2 * π), h (s, t) := setIntegral_prod _ hint
    _ = _ := by
        have h2π : (0 : ℝ) ≤ 2 * π := by positivity
        simp only [intervalIntegral.integral_of_le h2π, integral_Icc_eq_integral_Ioc]
        rfl

/-- The Fourier mode `e^{i n θ}`. -/
def p11cPJE (n : ℤ) (θ : ℝ) : ℂ := Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))

theorem p11cPJE_add_int (n m : ℤ) (θ : ℝ) : p11cPJE n θ * p11cPJE m θ = p11cPJE (n + m) θ := by
  unfold p11cPJE; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem p11cPJE_add_real (n : ℤ) (θ φ : ℝ) : p11cPJE n (θ + φ) = p11cPJE n θ * p11cPJE n φ := by
  unfold p11cPJE; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem p11cPJE_neg_real (n : ℤ) (θ : ℝ) : p11cPJE n (-θ) = p11cPJE (-n) θ := by
  unfold p11cPJE; congr 1; push_cast; ring

theorem p11cPJE_zero (θ : ℝ) : p11cPJE 0 θ = 1 := by simp [p11cPJE]

theorem p11cPJE_two_pi (n : ℤ) : p11cPJE n (2 * π) = 1 := by
  unfold p11cPJE
  have := Complex.exp_int_mul_two_pi_mul_I n
  rw [← this]; congr 1; push_cast; ring

theorem p11cPJE_period (n : ℤ) (θ : ℝ) : p11cPJE n (θ + 2 * π) = p11cPJE n θ := by
  rw [p11cPJE_add_real, p11cPJE_two_pi, mul_one]

theorem p11cPJE_continuous (n : ℤ) : Continuous (p11cPJE n) := by
  unfold p11cPJE; fun_prop

/-- Inner integral by the periodic shift. -/
theorem p11cPJ_inner {g : ℝ → ℂ} (hgp : Function.Periodic g (2 * π)) (r : ℤ) (s : ℝ) :
    ∫ t in (0 : ℝ)..2 * π, p11cPJE r t * g (s - t) =
      p11cPJE r s * ∫ θ in (0 : ℝ)..2 * π, p11cPJE (-r) θ * g θ := by
  set F : ℝ → ℂ := fun θ => p11cPJE r s * (p11cPJE (-r) θ * g θ) with hF
  have h1 : ∀ t : ℝ, p11cPJE r t * g (s - t) = F (s - t) := by
    intro t
    simp only [hF]
    have : p11cPJE r t = p11cPJE r s * p11cPJE (-r) (s - t) := by
      rw [sub_eq_add_neg, p11cPJE_add_real, p11cPJE_neg_real, neg_neg, ← mul_assoc,
        p11cPJE_add_int, add_neg_cancel, p11cPJE_zero, one_mul]
    rw [this]; ring
  have hFp : Function.Periodic F (2 * π) := by
    intro θ
    simp only [hF]
    rw [p11cPJE_period, hgp θ]
  simp_rw [h1]
  rw [intervalIntegral.integral_comp_sub_left F s]
  have h3 : ∫ θ in s - 2 * π..s - 0, F θ = ∫ θ in (0 : ℝ)..2 * π, F θ := by
    have := hFp.intervalIntegral_add_eq (s - 2 * π) 0
    rw [show s - 2 * π + 2 * π = s by ring, zero_add] at this
    rw [sub_zero]; exact this
  rw [h3]
  simp only [hF]
  rw [intervalIntegral.integral_const_mul]

theorem p11cPJ_integral_E {n : ℤ} (hn : n ≠ 0) :
    ∫ s in (0 : ℝ)..2 * π, p11cPJE n s = 0 := by
  have hc : Complex.I * (n : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hn)
  have := integral_exp_mul_complex (a := (0 : ℝ)) (b := 2 * π) hc
  have h2 : ∀ x : ℝ, p11cPJE n x = Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) := fun x => rfl
  simp_rw [h2]
  rw [this]
  have := p11cPJE_two_pi n
  unfold p11cPJE at this
  push_cast at this ⊢
  rw [this]; simp

/-- The mean of a mode against a periodic function of the difference of the two angles. -/
theorem p11cPJ_cell {g : ℝ → ℂ} (hgc : Continuous g) (hgp : Function.Periodic g (2 * π))
    (p r : ℤ) :
    ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)),
        p11cPJE p (l 0) * p11cPJE r (l 1) * g (l 0 - l 1) =
      (∫ s in (0 : ℝ)..2 * π, p11cPJE (p + r) s) *
        ∫ θ in (0 : ℝ)..2 * π, p11cPJE (-r) θ * g θ := by
  have hc : Continuous fun l : Fin 2 → ℝ => p11cPJE p (l 0) * p11cPJE r (l 1) * g (l 0 - l 1) := by
    have := p11cPJE_continuous p
    have := p11cPJE_continuous r
    fun_prop
  rw [p11cPJ_integral_cell_two hc.continuousOn]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1 : ∀ s : ℝ, ∫ t in (0 : ℝ)..2 * π, p11cPJE p s * p11cPJE r t * g (s - t) =
      p11cPJE (p + r) s * ∫ θ in (0 : ℝ)..2 * π, p11cPJE (-r) θ * g θ := by
    intro s
    have : ∀ t : ℝ, p11cPJE p s * p11cPJE r t * g (s - t) =
        p11cPJE p s * (p11cPJE r t * g (s - t)) := fun t => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul, p11cPJ_inner hgp r s, ← mul_assoc,
      p11cPJE_add_int]
  simp_rw [h1]
  rw [intervalIntegral.integral_mul_const]

theorem p11cPJ_cell_charged {g : ℝ → ℂ} (hgc : Continuous g) (hgp : Function.Periodic g (2 * π))
    {p r : ℤ} (h : p + r ≠ 0) :
    ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)),
        p11cPJE p (l 0) * p11cPJE r (l 1) * g (l 0 - l 1) = 0 := by
  rw [p11cPJ_cell hgc hgp, p11cPJ_integral_E h, zero_mul]

theorem p11cPJ_cell_neutral {g : ℝ → ℂ} (hgc : Continuous g) (hgp : Function.Periodic g (2 * π))
    (p : ℤ) :
    ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)),
        p11cPJE p (l 0) * p11cPJE (-p) (l 1) * g (l 0 - l 1) =
      (2 * π : ℝ) * ∫ θ in (0 : ℝ)..2 * π, p11cPJE p θ * g θ := by
  rw [p11cPJ_cell hgc hgp, neg_neg, add_neg_cancel]
  simp only [p11cPJE_zero, intervalIntegral.integral_const, mul_one, sub_zero,
    Complex.real_smul]

/-- The mean of `e^{i p θ} s(θ)^{-e/2}` over a period is the Laplace coefficient. -/
theorem p11cPJ_laplace {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (e : ℕ) (p : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, p11cPJE p θ * ((p11cPJS a θ ^ e : ℝ) : ℂ) =
      ((2 * π * p11c_laplace ((e : ℝ) / 2) p a : ℝ) : ℂ) := by
  set h : ℝ → ℝ := fun θ => p11cPJS a θ ^ e with hh
  have hhc : Continuous h := (p11cPJS_continuous ha).pow e
  have hsym : ∀ θ, h (2 * π - θ) = h θ := fun θ => by simp only [hh, p11cPJS_two_pi_sub]
  have hE : ∀ θ : ℝ, p11cPJE p θ = ((Real.cos ((p : ℝ) * θ) : ℝ) : ℂ) +
      Complex.I * ((Real.sin ((p : ℝ) * θ) : ℝ) : ℂ) := by
    intro θ
    unfold p11cPJE
    rw [show Complex.I * (p : ℂ) * (θ : ℂ) = (((p : ℝ) * θ : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_mul_I]
    push_cast
    ring
  have hsin : ∫ θ in (0 : ℝ)..2 * π, Real.sin ((p : ℝ) * θ) * h θ = 0 := by
    have h1 := intervalIntegral.integral_comp_sub_left
      (fun θ => Real.sin ((p : ℝ) * θ) * h θ) (a := 0) (b := 2 * π) (2 * π)
    simp only [sub_zero, sub_self] at h1
    have h2 : ∀ θ : ℝ, Real.sin ((p : ℝ) * (2 * π - θ)) * h (2 * π - θ) =
        -(Real.sin ((p : ℝ) * θ) * h θ) := by
      intro θ
      rw [hsym]
      have : (p : ℝ) * (2 * π - θ) = -((p : ℝ) * θ) + (p : ℤ) * (2 * π) := by ring
      rw [this, show ((p : ℝ) * (2 * π)) = ((p : ℤ) : ℝ) * (2 * π) by rfl,
        Real.sin_add_int_mul_two_pi, Real.sin_neg]
      ring
    simp_rw [h2] at h1
    rw [intervalIntegral.integral_neg] at h1
    linarith
  have hcos : ∫ θ in (0 : ℝ)..2 * π, Real.cos ((p : ℝ) * θ) * h θ =
      2 * π * p11c_laplace ((e : ℝ) / 2) p a := by
    unfold p11c_laplace
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hh, p11cPJS_pow ha, div_eq_mul_inv, p11cKer]
  have hc1 : Continuous fun θ : ℝ => ((Real.cos ((p : ℝ) * θ) * h θ : ℝ) : ℂ) := by fun_prop
  have hc2 : Continuous fun θ : ℝ => ((Real.sin ((p : ℝ) * θ) * h θ : ℝ) : ℂ) := by fun_prop
  have : ∀ θ : ℝ, p11cPJE p θ * ((h θ : ℝ) : ℂ) =
      ((Real.cos ((p : ℝ) * θ) * h θ : ℝ) : ℂ) +
        Complex.I * ((Real.sin ((p : ℝ) * θ) * h θ : ℝ) : ℂ) := fun θ => by
    rw [hE]; push_cast; ring
  show ∫ θ in (0 : ℝ)..2 * π, p11cPJE p θ * ((h θ : ℝ) : ℂ) = _
  simp_rw [this]
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
    ((hc2.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, hsin, hcos]
  simp

end KAM.Planetary

end
