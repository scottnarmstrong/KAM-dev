/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowAverageKey

/-!
# Slow averaging: the polar chart on the slow-stage domain (P11A-P7b)

Holomorphy of `p11PolarC` where `Re ρ̃ > 0`, membership of `p11PolarC z` in the fast domain,
reality of `p11PolarC` at real points, and 1-periodicity in all angles.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators
namespace KAM.Planetary

section Dom

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- Points whose oscillator actions have positive real part. -/
def p11RePos (n : ℕ) : Set (P11Phase (n + n)) := {z | ∀ i : Fin n, 0 < (z.2 (Fin.natAdd n i)).re}

theorem p11RePos_isOpen (n : ℕ) : IsOpen (p11RePos n) := by
  have : p11RePos n = ⋂ i : Fin n, {z : P11Phase (n + n) | 0 < (z.2 (Fin.natAdd n i)).re} := by
    ext z; simp [p11RePos]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (Complex.continuous_re.comp (by fun_prop))

theorem p11_sqrt_differentiableAt {a : ℂ} (ha : 0 < a.re) :
    DifferentiableAt ℂ Complex.sqrt a := by
  unfold Complex.sqrt
  exact (differentiableAt_id.cpow (differentiableAt_const _) (Or.inl ha))

theorem p11_polarC_differentiableOn : DifferentiableOn ℂ (p11PolarC (n := n)) (p11RePos n) := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  have hs : ∀ i : Fin n, DifferentiableAt ℂ
      (fun w : P11Phase (n + n) => Complex.sqrt (w.2 (Fin.natAdd n i) / Real.pi)) z := by
    intro i
    have h1 : DifferentiableAt ℂ (fun w : P11Phase (n + n) => w.2 (Fin.natAdd n i) / Real.pi) z :=
      by fun_prop
    have h2 : 0 < (z.2 (Fin.natAdd n i) / Real.pi).re := by
      rw [Complex.div_ofReal_re]; exact div_pos (hz i) Real.pi_pos
    exact (p11_sqrt_differentiableAt h2).comp z h1
  refine DifferentiableAt.prodMk ?_ ?_
  · refine differentiableAt_pi.2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]; fun_prop
    · simp only [Fin.append_right]
      exact (hs i).mul (by fun_prop)
  · refine differentiableAt_pi.2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]; fun_prop
    · simp only [Fin.append_right]
      exact (hs i).mul (by fun_prop)

/-- Polar point of a point of the slow-stage domain is in the fast domain, with `‖Π‖ ≤ 4 √ε`. -/
theorem p11_polarC_mem (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hsm : 64 * eps < C.rz ^ 2) {z : P11Phase (n + n)}
    (hz1 : z.1 ∈ KAM.complexStrip (n + n) (C.sigma / 6))
    (hJ : ‖p11SlowJ z.2 - KAM.realInclusion n C.J0‖ < p11s1 C eps / 2)
    (hρ : ‖p11SlowR z.2‖ < 3 * Real.pi * eps) :
    ‖p11PolPt z‖ ≤ 4 * Real.sqrt eps ∧ ‖p11PolPt z‖ < C.rz / 2 ∧
      p11PolarC z ∈ p11WorkingDom n C.J0 (C.sigma / 6) (p11s1 C eps / 2) (C.rz / 2) := by
  obtain ⟨-, -, -, -, -, hσ0, hσ1, hrz0, -⟩ := fast_consts hC
  have hpi := Real.pi_pos
  have he0 : 0 ≤ Real.sqrt eps := Real.sqrt_nonneg _
  have he2 : Real.sqrt eps ^ 2 = eps := Real.sq_sqrt heps.le
  have hzim : ∀ i : Fin n, |(z.1 (Fin.natAdd n i)).im| ≤ 1 / 8 := fun i =>
    (hz1 (Fin.natAdd n i)).le.trans (by linarith)
  have h1 := p11PolPt_norm_le z hzim
  have hs3 : Real.sqrt (‖p11SlowR z.2‖ / Real.pi) ≤ 2 * Real.sqrt eps := by
    have : ‖p11SlowR z.2‖ / Real.pi ≤ (2 * Real.sqrt eps) ^ 2 := by
      rw [div_le_iff₀ hpi]; nlinarith
    exact (Real.sqrt_le_left (by positivity)).2 this
  have hP : ‖p11PolPt z‖ ≤ 4 * Real.sqrt eps := by linarith
  have hPr : ‖p11PolPt z‖ < C.rz / 2 := by
    refine lt_of_le_of_lt hP ?_
    have : (4 * Real.sqrt eps) ^ 2 < (C.rz / 2) ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) this
  refine ⟨hP, hPr, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [p11PolarC, Fin.append_left] using hz1 (Fin.castAdd n i)
  · have h : (fun i : Fin n => (p11PolarC z).2 (Fin.castAdd n i)) = p11SlowJ z.2 := by
      funext i; simp [p11PolarC, p11SlowJ]
    show ‖(fun i : Fin n => (p11PolarC z).2 (Fin.castAdd n i)) - _‖ < _
    rw [h]; exact hJ
  · exact lt_of_le_of_lt (by
      rw [Prod.norm_def]; exact le_max_left _ _ |>.trans' le_rfl) hPr
  · exact lt_of_le_of_lt (by
      rw [Prod.norm_def]; exact le_max_right _ _ |>.trans' le_rfl) hPr

/-- The polar chart maps real points with positive oscillator actions to real points. -/
theorem p11_polarC_real {z : Phase (n + n)} (hz : ∀ i : Fin n, 0 < z.2 (Fin.natAdd n i)) :
    p11PolarC (KAM.realInclusion₂ (n + n) z) = KAM.realInclusion₂ (n + n) (p11PolarR z) := by
  have hre : ∀ w : P11Phase (n + n), (∀ i, (w.1 i).im = 0) → (∀ i, (w.2 i).im = 0) →
      w = KAM.realInclusion₂ (n + n) ((fun i => (w.1 i).re), (fun i => (w.2 i).re)) := by
    intro w h1 h2
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · exact Complex.ext (by simp) (by simp [h1 i])
    · exact Complex.ext (by simp) (by simp [h2 i])
  have hsq : ∀ (a b : ℝ) (ha : 0 ≤ a), (Complex.sqrt ((a : ℂ) / (Real.pi : ℂ)) *
      Complex.sin (2 * (Real.pi : ℂ) * (b : ℂ))).im = 0 ∧
      (Complex.sqrt ((a : ℂ) / (Real.pi : ℂ)) * Complex.cos (2 * (Real.pi : ℂ) * (b : ℂ))).im = 0 := by
    intro a b ha
    have h' : Complex.sqrt ((a : ℂ) / (Real.pi : ℂ)) = ((Real.sqrt (a / Real.pi) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_div]; exact p11_sqrt_ofReal (div_nonneg ha Real.pi_pos.le)
    have hs : Complex.sin (2 * (Real.pi : ℂ) * (b : ℂ)) = ((Real.sin (2 * Real.pi * b) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sin]; push_cast; rfl
    have hc : Complex.cos (2 * (Real.pi : ℂ) * (b : ℂ)) = ((Real.cos (2 * Real.pi * b) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cos]; push_cast; rfl
    rw [h', hs, hc, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    exact ⟨Complex.ofReal_im _, Complex.ofReal_im _⟩
  have := hre (p11PolarC (KAM.realInclusion₂ (n + n) z)) (fun j => ?_) (fun j => ?_)
  · exact this
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [p11PolarC, Fin.append_left]
    · simp only [p11PolarC, Fin.append_right, KAM.realInclusion₂_apply, KAM.realInclusion_apply]
      exact (hsq _ _ (hz i).le).1
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [p11PolarC, Fin.append_left]
    · simp only [p11PolarC, Fin.append_right, KAM.realInclusion₂_apply, KAM.realInclusion_apply]
      exact (hsq _ _ (hz i).le).2

theorem p11_natAdd_ne_castAdd (i j : Fin n) : Fin.natAdd n i ≠ Fin.castAdd n j := by
  have := j.isLt
  rw [Ne, Fin.ext_iff]; simp; omega

theorem p11_addNat_ne_castAdd (i j : Fin n) : i.addNat n ≠ Fin.castAdd n j := by
  have := j.isLt
  rw [Ne, Fin.ext_iff]; simp; omega

/-- The shift by a basis vector of the `θ`-angles is a lattice translation in the fast chart. -/
theorem p11_append_single (j : Fin n) :
    Fin.append (fun i : Fin n => (((Pi.single j (1 : ℤ) : Fin n → ℤ) i : ℤ) : ℂ))
      (0 : Fin n → ℂ) = (Pi.single (Fin.castAdd n j) 1 : P11CVec (n + n)) := by
  funext x
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x
  · simp [Pi.single_apply, Fin.castAdd_inj]
  · simp [Pi.single_apply, p11_addNat_ne_castAdd]

/-- `f₁` is `1`-periodic in the `θ`-angles (lattice clause of the fast chart plus periodicity
of `F`). -/
theorem p11_f1_periodic (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast)
    {z : P11Phase (n + n)}
    (hz : z ∈ p11WorkingDom n C.J0 (C.sigma / 6) (p11s1 C eps / 2) (C.rz / 2)) (j : Fin n) :
    Fast.f1 (z.1 + Pi.single (Fin.castAdd n j) 1, z.2) = Fast.f1 z := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, hrC1, hσ0, hσ1, hrz0, hrz1, hMF⟩ := fast_consts hC
  obtain ⟨-, -, -, -, -, -, -, -, hlat, hmaps, hid, -⟩ := hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hper, -⟩ := hC
  set e : P11CVec (n + n) := Pi.single (Fin.castAdd n j) 1 with he
  have hz' : (z.1 + e, z.2) ∈ p11WorkingDom n C.J0 (C.sigma / 6) (p11s1 C eps / 2) (C.rz / 2) := by
    obtain ⟨h1, h2, h3, h4⟩ := hz
    refine ⟨fun i => ?_, h2, ?_, h4⟩
    · have := h1 i
      simp only [Pi.add_apply, he, Pi.single_apply]
      split_ifs <;> simpa using this
    · convert h3 using 2
      funext i
      simp [he, p11_addNat_ne_castAdd]
  have hmap := hlat z hz (Pi.single j 1)
  rw [p11_append_single] at hmap
  have hm2 : Fast.map z ∈ p11WorkingDom n C.J0 (2 * C.sigma) (2 * C.rC) C.rz := by
    obtain ⟨a, b, c, d⟩ := hmaps hz
    exact ⟨fun i => lt_of_lt_of_le (a i) (by linarith),
      b.trans_le (by linarith [p11s1_le C eps]), c, d⟩
  have hFp := hper _ hm2 j
  have hnat : ∀ i : Fin n, ((z.1 + e) (Fin.natAdd n i)) = z.1 (Fin.natAdd n i) := by
    intro i
    simp [he, p11_addNat_ne_castAdd]
  have e1 := hid z hz
  have e2 := hid _ hz'
  have hW : p11WorkingH C eps (Fast.map (z.1 + e, z.2)) = p11WorkingH C eps (Fast.map z) := by
    rw [hmap]
    unfold p11WorkingH
    have hsplit : Fast.map z + (Pi.single (Fin.castAdd n j) 1, (0 : P11CVec (n + n))) =
        ((Fast.map z).1 + Pi.single (Fin.castAdd n j) 1, (Fast.map z).2) :=
      Prod.ext rfl (add_zero _)
    rw [hsplit, hFp]
  have hGeq : (fun i : Fin n => (z.1 + e) (Fin.natAdd n i)) =
      fun i : Fin n => z.1 (Fin.natAdd n i) := funext hnat
  simp only [hGeq] at e2
  rw [hW] at e2
  linear_combination e1 - e2

end Dom

end KAM.Planetary

end
