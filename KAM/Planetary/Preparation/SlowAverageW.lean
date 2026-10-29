/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowAverageF2

/-!
# Slow averaging: holomorphy, reality and periodicity of `f₂`, and its weighted bound
(P11A-P7b, graph steps `as-osc`, `as-concl`)
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators
namespace KAM.Planetary

section W

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- Pointwise data of a point of the strip `σ/6` over the box. -/
theorem p11_slow_pt (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) (hsm : 64 * eps < C.rz ^ 2) {z : P11Phase (n + n)}
    (hz : z ∈ KAM.complexStrip (n + n) (C.sigma / 6) ×ˢ p11SlowAvgBox C eps) :
    (p11SlowJ z.2, p11SlowR z.2) ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
        ball (0 : P11CVec n) (Real.pi * (C.rz / 2) ^ 2 / 4) ∧
      (∀ i, 0 < (p11SlowR z.2 i).re) ∧ z ∈ p11RePos n ∧
      (p11SlowJ z.2, p11PolPt z) ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
        ball (0 : P11Phase n) (C.rz / 2) ∧
      p11PolarC z ∈ p11WorkingDom n C.J0 (C.sigma / 6) (p11s1 C eps / 2) (C.rz / 2) := by
  obtain ⟨-, -, -, hrC0, -, hσ0, hσ1, hrz0, -⟩ := fast_consts hC
  have hs0 := p11s1_pos hC heps hεM
  obtain ⟨hz1, hI⟩ := hz
  obtain ⟨hJ4, hρ, hre⟩ := p11SlowAvgBox_mem heps hs0 hI
  have hJ2 : ‖p11SlowJ z.2 - KAM.realInclusion n C.J0‖ < p11s1 C eps / 2 := by linarith
  obtain ⟨-, hPr, hU⟩ := p11_polarC_mem hC heps hsm hz1 hJ2 hρ
  have hpi := Real.pi_pos
  refine ⟨⟨mem_ball_iff_norm.2 hJ2, mem_ball_zero_iff.2 ?_⟩, hre, hre, ⟨mem_ball_iff_norm.2 hJ2,
    mem_ball_zero_iff.2 hPr⟩, hU⟩
  have : 3 * Real.pi * eps < Real.pi * (C.rz / 2) ^ 2 / 4 := by nlinarith
  linarith

theorem p11SlowJ_differentiable : Differentiable ℂ (fun I : P11CVec (n + n) => p11SlowJ I) := by
  unfold p11SlowJ; fun_prop

theorem p11SlowR_differentiable : Differentiable ℂ (fun I : P11CVec (n + n) => p11SlowR I) := by
  unfold p11SlowR; fun_prop

/-- Holomorphy of the secular part `C + Σ Ω ρ̃/2π`. -/
theorem p11SlowSec_differentiableOn (hC : P11SecularSpec D C) {s : ℝ} (hs : s ≤ 2 * C.rC) :
    DifferentiableOn ℂ (p11SlowSec C)
      {I : P11CVec (n + n) | ‖p11SlowJ I - KAM.realInclusion n C.J0‖ < s} := by
  obtain ⟨hOm, -⟩ := secular_extract hC
  have hmem : ∀ I ∈ {I : P11CVec (n + n) | ‖p11SlowJ I - KAM.realInclusion n C.J0‖ < s},
      p11SlowJ I ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) := fun I hI =>
    mem_ball_iff_norm.2 (lt_of_lt_of_le hI hs)
  have h1 : DifferentiableOn ℂ (fun I : P11CVec (n + n) => C.C (p11SlowJ I))
      {I : P11CVec (n + n) | ‖p11SlowJ I - KAM.realInclusion n C.J0‖ < s} :=
    (p11C_differentiableOn hC).comp p11SlowJ_differentiable.differentiableOn hmem
  have h2 : DifferentiableOn ℂ (fun I : P11CVec (n + n) => ∑ i : Fin n,
      C.Omega (p11SlowJ I) i / (2 * Real.pi) * I (Fin.natAdd n i))
      {I : P11CVec (n + n) | ‖p11SlowJ I - KAM.realInclusion n C.J0‖ < s} := by
    refine DifferentiableOn.fun_sum fun i _ => ?_
    have h0 : DifferentiableOn ℂ (fun I : P11CVec (n + n) => C.Omega (p11SlowJ I) i)
        {I : P11CVec (n + n) | ‖p11SlowJ I - KAM.realInclusion n C.J0‖ < s} :=
      (differentiableOn_pi.1 hOm i).comp p11SlowJ_differentiable.differentiableOn hmem
    have h3 : DifferentiableOn ℂ (fun I : P11CVec (n + n) => I (Fin.natAdd n i))
        {I : P11CVec (n + n) | ‖p11SlowJ I - KAM.realInclusion n C.J0‖ < s} :=
      Differentiable.differentiableOn (by fun_prop)
    have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      have := Real.pi_pos
      exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 this.ne')
    have h4 := (h0.mul (differentiableOn_const ((2 * (Real.pi : ℂ))⁻¹))).mul h3
    exact h4.congr fun I _ => by simp [div_eq_mul_inv]
  exact h1.add h2

/-- `f₂` is holomorphic on the strip `σ/6` over the box. -/
theorem p11_slow_f2_differentiableOn (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) {AR AB : P11CVec n × P11CVec n → ℂ}
    (hP : P11SlowPolarOut C Fast eps AR AB) (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) (hsm : 64 * eps < C.rz ^ 2) :
    DifferentiableOn ℂ (p11SlowF2 C Fast eps (p11SlowZ AR AB))
      (KAM.complexStrip (n + n) (C.sigma / 6) ×ˢ p11SlowAvgBox C eps) := by
  obtain ⟨-, -, hf1d, -, hGd, -⟩ := id hF
  obtain ⟨hARd, hABd, -⟩ := hP
  set S := KAM.complexStrip (n + n) (C.sigma / 6) ×ˢ p11SlowAvgBox C eps with hS
  have hpt := fun z (hz : z ∈ S) => p11_slow_pt hC heps hεM hsm hz
  have hPol : DifferentiableOn ℂ p11PolarC S :=
    p11_polarC_differentiableOn.mono fun z hz => (hpt z hz).2.2.1
  have hPi : DifferentiableOn ℂ (fun z : P11Phase (n + n) => p11PolPt z) S := by
    refine DifferentiableOn.prodMk ?_ ?_
    · exact differentiableOn_pi.2 fun i => differentiableOn_pi.1 hPol.fst (Fin.natAdd n i)
    · exact differentiableOn_pi.2 fun i => differentiableOn_pi.1 hPol.snd (Fin.natAdd n i)
  have hJ : DifferentiableOn ℂ (fun z : P11Phase (n + n) => p11SlowJ z.2) S :=
    (p11SlowJ_differentiable.comp differentiable_snd).differentiableOn
  have hR : DifferentiableOn ℂ (fun z : P11Phase (n + n) => p11SlowR z.2) S :=
    (p11SlowR_differentiable.comp differentiable_snd).differentiableOn
  have hJR : DifferentiableOn ℂ (fun z : P11Phase (n + n) => (p11SlowJ z.2, p11SlowR z.2)) S :=
    hJ.prodMk hR
  have hG : DifferentiableOn ℂ (fun z : P11Phase (n + n) => Fast.G (p11SlowJ z.2, p11PolPt z)) S :=
    hGd.comp (hJ.prodMk hPi) fun z hz => (hpt z hz).2.2.2.1
  have hsec : DifferentiableOn ℂ (fun z : P11Phase (n + n) => p11SlowSec C z.2) S := by
    obtain ⟨-, -, -, hrC0, -⟩ := fast_consts hC
    have := (p11SlowSec_differentiableOn hC (s := p11s1 C eps / 2)
      (by linarith [p11s1_le C eps])).comp
      differentiable_snd.differentiableOn (fun z hz => (mem_ball_iff_norm.1 (hpt z hz).1.1 : _))
    exact this
  have hZ : DifferentiableOn ℂ (fun z : P11Phase (n + n) => p11SlowZ AR AB z.2) S :=
    (hARd.comp hJR fun z hz => (hpt z hz).1).add (hABd.comp hJR fun z hz => (hpt z hz).1)
  have hf1 : DifferentiableOn ℂ (fun z : P11Phase (n + n) => Fast.f1 (p11PolarC z)) S :=
    hf1d.comp hPol fun z hz => (hpt z hz).2.2.2.2
  exact (((hG.sub (hsec.add hZ)).const_smul eps).add hf1 : _)

theorem p11PolarC_shift_theta (z : P11Phase (n + n)) (j : Fin n) :
    p11PolarC (z.1 + Pi.single (Fin.castAdd n j) 1, z.2) =
      ((p11PolarC z).1 + Pi.single (Fin.castAdd n j) 1, (p11PolarC z).2) := by
  refine Prod.ext (funext fun x => ?_) (funext fun x => ?_) <;>
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x
  · simp [p11PolarC, Fin.append_left]
  · simp [p11PolarC, p11_addNat_ne_castAdd]
  · simp [p11PolarC, Fin.append_left]
  · simp [p11PolarC, p11_addNat_ne_castAdd]

theorem p11PolarC_shift_zeta (z : P11Phase (n + n)) (j : Fin n) :
    p11PolarC (z.1 + Pi.single (Fin.natAdd n j) 1, z.2) = p11PolarC z := by
  have hper : ∀ a : ℂ, Complex.sin (2 * Real.pi * (a + 1)) = Complex.sin (2 * Real.pi * a) ∧
      Complex.cos (2 * Real.pi * (a + 1)) = Complex.cos (2 * Real.pi * a) := by
    intro a
    have : (2 * (Real.pi : ℂ) * (a + 1)) = 2 * Real.pi * a + 2 * Real.pi := by ring
    rw [this, Complex.sin_add_two_pi, Complex.cos_add_two_pi]
    exact ⟨rfl, rfl⟩
  have hsh : ∀ i : Fin n, (z.1 + (Pi.single (Fin.natAdd n j) 1 : P11CVec (n + n)))
      (Fin.natAdd n i) = z.1 (Fin.natAdd n i) + (if i = j then 1 else 0) := by
    intro i
    by_cases h : i = j
    · subst h; simp
    · have : Fin.natAdd n i ≠ Fin.natAdd n j := fun h' => h (by simpa [Fin.ext_iff] using h')
      simp [h]
  refine Prod.ext (funext fun x => ?_) (funext fun x => ?_) <;>
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x
  · simp [p11PolarC, Fin.append_left, p11_addNat_ne_castAdd]
  · simp only [p11PolarC, Fin.append_right, hsh]
    split_ifs
    · rw [(hper _).1]
    · rw [add_zero]
  · simp [p11PolarC, Fin.append_left]
  · simp only [p11PolarC, Fin.append_right, hsh]
    split_ifs
    · rw [(hper _).2]
    · rw [add_zero]

/-- `f₂` is `1`-periodic in every angle. -/
theorem p11_slow_f2_periodic (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) (Z : P11CVec (n + n) → ℂ) (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) (hsm : 64 * eps < C.rz ^ 2) :
    ∀ z ∈ KAM.complexStrip (n + n) (C.sigma / 6) ×ˢ p11SlowAvgBox C eps, ∀ i : Fin (n + n),
      p11SlowF2 C Fast eps Z (z.1 + Pi.single i 1, z.2) = p11SlowF2 C Fast eps Z z := by
  intro z hz i
  have hw := (p11_slow_pt hC heps hεM hsm hz).2.2.2.2
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have h := p11PolarC_shift_theta z j
    have hPt : p11PolPt (z.1 + Pi.single (Fin.castAdd n j) 1, z.2) = p11PolPt z := by
      unfold p11PolPt
      rw [h]
      refine Prod.ext (funext fun i => ?_) rfl
      simp [p11_addNat_ne_castAdd]
    have hf1 := p11_f1_periodic hC Fast hF hw j
    unfold p11SlowF2
    rw [hPt, h, hf1]
  · have h := p11PolarC_shift_zeta z j
    have hPt : p11PolPt (z.1 + Pi.single (Fin.natAdd n j) 1, z.2) = p11PolPt z := by
      unfold p11PolPt
      rw [h]
    unfold p11SlowF2
    rw [hPt, h]

/-- The weighted bound for `f₂` at width `σ/12` (graph step `as-osc`, via
`KAM.summableWeighted_torusCoeffW`, `1`-periodicity of `f₁` in `θ`, and the sup bound on the
strip of width `σ/6`). -/
theorem p11_slow_f2_wbound (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) {AR AB : P11CVec n × P11CVec n → ℂ}
    (hP : P11SlowPolarOut C Fast eps AR AB) (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) (hsm : 64 * eps < C.rz ^ 2) {c1 : ℝ}
    (hrate : p11eta1 C eps ≤ c1 * eps * Real.log (1 / eps) ^ (2 * C.tau + 1)) :
    p11WBound (p11SlowAvgBox C eps) (C.sigma / 12) (p11SlowF2 C Fast eps (p11SlowZ AR AB))
      ((Real.cosh (Real.pi * (C.sigma / 12)) / Real.sinh (Real.pi * (C.sigma / 12))) ^ (n + n) *
        (p11SlowC0 C c1 * eps ^ (5 / 2 : ℝ) * Real.log (1 / eps) ^ (2 * C.tau + 1))) := by
  obtain ⟨-, -, -, -, -, hσ0, -⟩ := fast_consts hC
  intro I hI
  have hS := p11_slow_f2_differentiableOn hC Fast hF hP heps hεM hsm
  have hper := p11_slow_f2_periodic hC Fast hF (p11SlowZ AR AB) heps hεM hsm
  have hsup := p11_slow_f2_sup hC Fast hF hP heps hεM hsm hrate
  have hmem : ∀ θ ∈ KAM.complexStrip (n + n) (C.sigma / 6), (θ, I) ∈
      KAM.complexStrip (n + n) (C.sigma / 6) ×ˢ p11SlowAvgBox C eps := fun θ hθ => ⟨hθ, hI⟩
  have hu : DifferentiableOn ℂ (fun θ : P11CVec (n + n) =>
      p11SlowF2 C Fast eps (p11SlowZ AR AB) (θ, I)) (KAM.complexStrip (n + n) (C.sigma / 6)) :=
    hS.comp (by fun_prop : DifferentiableOn ℂ (fun θ : P11CVec (n + n) => (θ, I)) _) hmem
  have h := KAM.summableWeighted_torusCoeffW (n := n + n) (ρ := C.sigma / 6) (δ := C.sigma / 12)
    (by linarith) (by linarith) hu (fun i θ hθ => hper (θ, I) (hmem θ hθ) i)
    (fun θ hθ => hsup (θ, I) (hmem θ hθ))
  have e : C.sigma / 6 - C.sigma / 12 = C.sigma / 12 := by ring
  rw [e] at h
  exact h

end W

end KAM.Planetary

end
