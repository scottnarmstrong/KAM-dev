/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowAverageW

/-!
# Slow averaging: the averaged Hamiltonian identity and reality (P11A-P7b, `as-osc`)

`p11_slow_secZ_eq`: on the box, `C + Σ Ω ρ̃/2π + Ẑ = 𝒜 G` (so `h₀ = h + ε 𝒜 G`); `h₀` and `f₂` are
real at real points.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators
namespace KAM.Planetary

section Real

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- Data of a point of the action box. -/
theorem p11_slow_box_pt (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) (hsm : 64 * eps < C.rz ^ 2) {I : P11CVec (n + n)}
    (hI : I ∈ p11SlowBox C eps) :
    (p11SlowJ I, p11SlowR I) ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
        ball (0 : P11CVec n) (Real.pi * (C.rz / 2) ^ 2 / 4) ∧
      (∀ i, 0 < (p11SlowR I i).re) := by
  obtain ⟨-, -, -, -, -, -, -, hrz0, -⟩ := fast_consts hC
  have hs0 := p11s1_pos hC heps hεM
  obtain ⟨hJ4, hρ, hre⟩ := p11SlowBox_mem heps hs0 hI
  have hpi := Real.pi_pos
  refine ⟨⟨mem_ball_iff_norm.2 (by linarith), mem_ball_zero_iff.2 ?_⟩, hre⟩
  have : 3 * Real.pi * eps < Real.pi * (C.rz / 2) ^ 2 / 4 := by nlinarith
  linarith

/-- `C + Σ Ω ρ̃/2π + Ẑ = 𝒜 G` on the box (`polar_avg` (b), (d)). -/
theorem p11_slow_secZ_eq (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) {AR AB : P11CVec n × P11CVec n → ℂ}
    (hP : P11SlowPolarOut C Fast eps AR AB) (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) (hsm : 64 * eps < C.rz ^ 2) {I : P11CVec (n + n)}
    (hI : I ∈ p11SlowBox C eps) :
    p11SlowSec C I + p11SlowZ AR AB I = p11PolarAverage Fast.G (p11SlowJ I, p11SlowR I) := by
  obtain ⟨hz, hre⟩ := p11_slow_box_pt hC heps hεM hsm hI
  obtain ⟨-, -, -, -, hAe⟩ := id hP
  exact p11_slow_key hC Fast hF heps hεM (fun z hz hre => (hAe z hz hre).1)
    (fun z hz hre => (hAe z hz hre).2) hz hre

theorem p11SlowJ_real (I : P11Vec (n + n)) :
    p11SlowJ (KAM.realInclusion (n + n) I) = KAM.realInclusion n (fun i => I (Fin.castAdd n i)) := by
  funext i; simp [p11SlowJ]

theorem p11SlowR_real (I : P11Vec (n + n)) :
    p11SlowR (KAM.realInclusion (n + n) I) = KAM.realInclusion n (fun i => I (Fin.natAdd n i)) := by
  funext i; simp [p11SlowR]

/-- The polar average of `G` is real at real data of the box. -/
theorem p11_slow_PA_real (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hsm : 64 * eps < C.rz ^ 2) {I : P11Vec (n + n)}
    (hI : KAM.realInclusion (n + n) I ∈ p11SlowBox C eps) :
    (p11PolarAverage Fast.G (p11SlowJ (KAM.realInclusion (n + n) I),
      p11SlowR (KAM.realInclusion (n + n) I))).im = 0 := by
  obtain ⟨hz, hre⟩ := p11_slow_box_pt hC heps hεM hsm hI
  rw [p11SlowJ_real, p11SlowR_real]
  rw [p11SlowJ_real, p11SlowR_real] at hz
  refine p11_slow_avg_real hC Fast hF ?_ (fun i => ?_) ?_
  · have := mem_ball_iff_norm.1 hz.1
    rwa [← map_sub, KAM.norm_realInclusion] at this
  · have := hre i
    simpa [p11SlowR_real] using this
  · have := mem_ball_zero_iff.1 hz.2
    rw [KAM.norm_realInclusion] at this
    have hpi := Real.pi_pos
    have : 0 < Real.pi * (C.rz / 2) ^ 2 := by
      obtain ⟨-, -, -, -, -, -, -, hrz0, -⟩ := fast_consts hC
      positivity
    linarith [mem_ball_zero_iff.1 hz.2, KAM.norm_realInclusion (fun i => I (Fin.natAdd n i))]

/-- `h₀` is real at real points of the box. -/
theorem p11_slow_h0_real (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) {AR AB : P11CVec n × P11CVec n → ℂ}
    (hP : P11SlowPolarOut C Fast eps AR AB) (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) (hsm : 64 * eps < C.rz ^ 2) {I : P11Vec (n + n)}
    (hI : KAM.realInclusion (n + n) I ∈ p11SlowBox C eps) :
    (p11SlowH0 C eps (p11SlowZ AR AB) (KAM.realInclusion (n + n) I)).im = 0 := by
  obtain ⟨-, hh, -⟩ := id hC
  have hs0 := p11s1_pos hC heps hεM
  obtain ⟨hJ4, -, -⟩ := p11SlowBox_mem heps hs0 hI
  have hJ : ‖(fun i => I (Fin.castAdd n i)) - C.J0‖ < 2 * C.rC := by
    rw [p11SlowJ_real, ← map_sub, KAM.norm_realInclusion] at hJ4
    linarith [p11s1_le C eps, (fast_consts hC).2.2.2.1]
  have hhr := (hh _ hJ).2
  have hq := p11_slow_secZ_eq hC Fast hF hP heps hεM hsm hI
  have hPA := p11_slow_PA_real hC Fast hF heps hεM hsm hI
  unfold p11SlowH0
  rw [hq]
  have : (fun i : Fin n => (KAM.realInclusion (n + n) I) (Fin.castAdd n i)) =
      KAM.realInclusion n (fun i => I (Fin.castAdd n i)) := rfl
  rw [this]
  simp [Complex.add_im, Complex.mul_im, hhr, hPA]

/-- `f₂` is real at the real points of the strip over the box. -/
theorem p11_slow_f2_real (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) {AR AB : P11CVec n × P11CVec n → ℂ}
    (hP : P11SlowPolarOut C Fast eps AR AB) (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) (hsm : 64 * eps < C.rz ^ 2) :
    KAM.Canonical.RealOn (KAM.complexStrip (n + n) (C.sigma / 6) ×ˢ p11SlowBox C eps)
      (p11SlowF2 C Fast eps (p11SlowZ AR AB)) := by
  obtain ⟨-, -, -, hf1r, -, hGr, -⟩ := id hF
  intro x hx
  obtain ⟨hz, hre, -, hG, hU⟩ := p11_slow_pt hC heps hεM hsm hx
  have hxpos : ∀ i : Fin n, 0 < x.2 (Fin.natAdd n i) := fun i => by
    have := hre i
    simpa [p11SlowR] using this
  have hpol := p11_polarC_real hxpos
  -- the polar point is real
  have hPt : p11PolPt (KAM.realInclusion₂ (n + n) x) = KAM.realInclusion₂ n
      ((fun i => (p11PolarR x).1 (Fin.natAdd n i)), (fun i => (p11PolarR x).2 (Fin.natAdd n i))) := by
    unfold p11PolPt
    rw [hpol]
    rfl
  have hGim : (Fast.G (p11SlowJ (KAM.realInclusion₂ (n + n) x).2,
      p11PolPt (KAM.realInclusion₂ (n + n) x))).im = 0 := by
    rw [hPt]
    have hJ' : p11SlowJ (KAM.realInclusion₂ (n + n) x).2 =
        KAM.realInclusion n (fun i => x.2 (Fin.castAdd n i)) := p11SlowJ_real x.2
    rw [hJ']
    have hJn : ‖(fun i => x.2 (Fin.castAdd n i)) - C.J0‖ < p11s1 C eps / 2 := by
      have := mem_ball_iff_norm.1 hG.1
      rw [hJ', ← map_sub, KAM.norm_realInclusion] at this
      exact this
    refine hGr _ hJn _ ?_
    have := mem_ball_zero_iff.1 hG.2
    rwa [hPt, KAM.norm_realInclusion₂] at this
  have hsecim : (p11SlowSec C (KAM.realInclusion₂ (n + n) x).2 +
      p11SlowZ AR AB (KAM.realInclusion₂ (n + n) x).2).im = 0 := by
    have hI : (KAM.realInclusion₂ (n + n) x).2 ∈ p11SlowBox C eps := hx.2
    rw [p11_slow_secZ_eq hC Fast hF hP heps hεM hsm hI]
    exact p11_slow_PA_real hC Fast hF heps hεM hsm (I := x.2) hI
  have hf1im : (Fast.f1 (p11PolarC (KAM.realInclusion₂ (n + n) x))).im = 0 := by
    rw [hpol]
    refine hf1r _ ?_
    rw [← hpol]; exact hU
  unfold p11SlowF2
  rw [Complex.add_im, Complex.mul_im, Complex.sub_im, hGim, hsecim, hf1im]
  simp

end Real

end KAM.Planetary

end
