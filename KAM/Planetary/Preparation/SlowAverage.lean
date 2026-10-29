/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowAverageJet
public import KAM.Planetary.Preparation.SlowAverageReal

/-!
# Slow averaging, polar normalization (P11A-P7b; plan steps 1-2 of `avg_slow`)

`P11SlowOscSpec C Fast eps c Z h0 f2` collects the outputs of graph step `stepP:p11:as-osc`
(`bpP:p11:avg-slow` (a)): the holomorphic `Ẑ = 𝒜(R₄ + ε ḡ)`, `h₀ = h + ε (C + Σ Ω ρ̃/2π + Ẑ)`
and `f₂ = ε (G ∘ Π - (C + Σ Ω ρ̃/2π + Ẑ)) + f₁ ∘ Π` on the box `D(J₀, s₁/4) × D(2πε, πε)`
(`p11SlowBox`), which contains the box `V₂` of `P11SlowSpecOf` since `s₂ ≤ s₁/4`.

* the fast identity `h₀ + f₂ = H ∘ (Φ¹ ∘ Π)` (`P11SlowSpecOf`, clause 1),
* `h₀ = h + ε 𝒜 G` (clause 2) and `h₀ = h + ε (C + Σ Ω ρ̃/2π + Ẑ)` (clause 3),
* `Ẑ` holomorphic on `D(J₀, s₁/2) × D(0, π r_z²/16)` with the `J`-jets of `∂ρ̃ Ẑ` (clauses 4-5),
  and the sup bound `‖Ẑ‖ ≤ 2^{2n} (M_F/16 + η₁)`,
* holomorphy and reality of `h₀`, `f₂`, 1-periodicity of `f₂` in all angles,
* the weighted bound `wn(f₂) ≤ c ε^{5/2} (log 1/ε)^{2τ+1}` at width `σ/12`.

`p11_slow_osc` states the existence for all small `ε` and all fast data (unsigned; consumed by
P7c/P7d).
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric Filter
open scoped BigOperators
namespace KAM.Planetary

section Main

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- Outputs of graph step `stepP:p11:as-osc` (unsigned; all fields are existential outputs). -/
def P11SlowOscSpec (C : P11SecularData n) (Fast : P11FastData n) (eps c : ℝ)
    (Z h0 : P11CVec (n + n) → ℂ) (f2 : P11Phase (n + n) → ℂ) : Prop :=
  let V := p11SlowBox C eps
  let s := C.sigma / 12
  let E := c * eps ^ (5 / 2 : ℝ) * Real.log (1 / eps) ^ (2 * C.tau + 1)
  (∀ z ∈ KAM.complexStrip (n + n) s ×ˢ V,
    h0 z.2 + f2 z = p11WorkingH C eps (Fast.map (p11PolarC z))) ∧
  (∀ I ∈ V, h0 I = C.h (fun i : Fin n => I (Fin.castAdd n i)) +
    eps * p11PolarAverage Fast.G ((fun i : Fin n => I (Fin.castAdd n i)),
      fun i : Fin n => I (Fin.natAdd n i))) ∧
  (∀ I ∈ V, h0 I = C.h (fun i : Fin n => I (Fin.castAdd n i)) +
    eps * (C.C (fun i : Fin n => I (Fin.castAdd n i)) +
      (∑ i : Fin n, C.Omega (fun j : Fin n => I (Fin.castAdd n j)) i / (2 * Real.pi) *
        I (Fin.natAdd n i)) + Z I)) ∧
  DifferentiableOn ℂ Z
    {I : P11CVec (n + n) |
      ‖(fun i : Fin n => I (Fin.castAdd n i)) - KAM.realInclusion n C.J0‖ < p11s1 C eps / 2 ∧
      ‖(fun i : Fin n => I (Fin.natAdd n i))‖ < Real.pi * C.rz ^ 2 / 16} ∧
  (∀ I ∈ {I : P11CVec (n + n) |
      ‖(fun i : Fin n => I (Fin.castAdd n i)) - KAM.realInclusion n C.J0‖ < p11s1 C eps / 2 ∧
      ‖(fun i : Fin n => I (Fin.natAdd n i))‖ < Real.pi * C.rz ^ 2 / 16},
    ‖Z I‖ ≤ 2 ^ (2 * n) * (C.MF / 16 + p11eta1 C eps)) ∧
  (∀ alpha : Fin n → ℕ, ∀ J, ‖J - KAM.realInclusion n C.J0‖ < p11s1 C eps / 4 →
    ∀ rho : P11CVec n, ‖rho - (fun _ => (2 * Real.pi * eps : ℂ))‖ < Real.pi * eps →
      ‖p11PartialVec alpha
        (fun J => fun i : Fin n =>
          fderiv ℂ (fun rho : P11CVec n => Z (Fin.append J rho)) rho (Pi.single i 1)) J‖ ≤
        c * (eps + p11eta1 C eps) * (∏ i, ((alpha i).factorial : ℝ)) *
          (4 / p11s1 C eps) ^ (∑ i, alpha i)) ∧
  DifferentiableOn ℂ h0 V ∧
  DifferentiableOn ℂ f2 (KAM.complexStrip (n + n) s ×ˢ V) ∧
  KAM.Canonical.RealOn (KAM.complexStrip (n + n) s ×ˢ V) f2 ∧
  (∀ I : P11Vec (n + n), KAM.realInclusion (n + n) I ∈ V →
    (h0 (KAM.realInclusion (n + n) I)).im = 0) ∧
  (∀ z ∈ KAM.complexStrip (n + n) s ×ˢ V, ∀ i : Fin (n + n),
    f2 (z.1 + Pi.single i 1, z.2) = f2 z) ∧
  p11WBound V s f2 E

/-- Existence of the objects `Ẑ`, `h₀`, `f₂` for one `ε` (graph steps `as-osc`, `as-concl`). -/
theorem p11_slow_osc_at (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hsm : 128 * eps < C.rz ^ 2) {c1 c : ℝ}
    (hrate : p11eta1 C eps ≤ c1 * eps * Real.log (1 / eps) ^ (2 * C.tau + 1))
    (hcZ : p11SlowCZ C ≤ c)
    (hcw : (Real.cosh (Real.pi * (C.sigma / 12)) / Real.sinh (Real.pi * (C.sigma / 12))) ^ (n + n) *
      p11SlowC0 C c1 ≤ c) :
    ∃ Z h0 : P11CVec (n + n) → ℂ, ∃ f2 : P11Phase (n + n) → ℂ,
      P11SlowOscSpec C Fast eps c Z h0 f2 := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, hrC1, hσ0, hσ1, hrz0, hrz1, hMF⟩ := fast_consts hC
  obtain ⟨AR, AB, hP⟩ := p11_slow_polar_out hC Fast hF heps hεM
  have hsm64 : 64 * eps < C.rz ^ 2 := by linarith
  have hs0 := p11s1_pos hC heps hεM
  have hη0 := p11eta1_pos hC heps hεM
  refine ⟨p11SlowZ AR AB, p11SlowH0 C eps (p11SlowZ AR AB), p11SlowF2 C Fast eps (p11SlowZ AR AB),
    ?_⟩
  have hsub : KAM.complexStrip (n + n) (C.sigma / 12) ⊆ KAM.complexStrip (n + n) (C.sigma / 6) :=
    fun θ hθ i => (hθ i).trans (by linarith)
  have hSsub : KAM.complexStrip (n + n) (C.sigma / 12) ×ˢ p11SlowBox C eps ⊆
      KAM.complexStrip (n + n) (C.sigma / 6) ×ˢ p11SlowBox C eps := prod_mono hsub subset_rfl
  have hidd := hF.2.2.2.2.2.2.2.2.2.2.1
  have hZm : ∀ I : P11CVec (n + n),
      I ∈ {I : P11CVec (n + n) |
        ‖(fun i : Fin n => I (Fin.castAdd n i)) - KAM.realInclusion n C.J0‖ < p11s1 C eps / 2 ∧
        ‖(fun i : Fin n => I (Fin.natAdd n i))‖ < Real.pi * C.rz ^ 2 / 16} →
      I ∈ {I : P11CVec (n + n) |
        ‖(fun i : Fin n => I (Fin.castAdd n i)) - KAM.realInclusion n C.J0‖ < p11s1 C eps / 2 ∧
        ‖(fun i : Fin n => I (Fin.natAdd n i))‖ < Real.pi * C.rz ^ 2 / 16} ∧
      (p11SlowJ I, p11SlowR I) ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
        ball (0 : P11CVec n) (Real.pi * (C.rz / 2) ^ 2 / 4) := by
    intro I hI
    refine ⟨hI, mem_ball_iff_norm.2 hI.1, mem_ball_zero_iff.2 ?_⟩
    have : Real.pi * (C.rz / 2) ^ 2 / 4 = Real.pi * C.rz ^ 2 / 16 := by ring
    rw [this]; exact hI.2
  have hboxZ : ∀ I ∈ p11SlowBox C eps,
      I ∈ {I : P11CVec (n + n) |
        ‖(fun i : Fin n => I (Fin.castAdd n i)) - KAM.realInclusion n C.J0‖ < p11s1 C eps / 2 ∧
        ‖(fun i : Fin n => I (Fin.natAdd n i))‖ < Real.pi * C.rz ^ 2 / 16} := by
    intro I hI
    obtain ⟨hJ4, hρ, -⟩ := p11SlowBox_mem heps hs0 hI
    have hpi := Real.pi_pos
    have hJ4' : ‖(fun i : Fin n => I (Fin.castAdd n i)) - KAM.realInclusion n C.J0‖ <
        p11s1 C eps / 4 := hJ4
    refine ⟨by linarith, ?_⟩
    have : 3 * Real.pi * eps < Real.pi * C.rz ^ 2 / 16 := by nlinarith
    exact lt_trans hρ this
  have hZd : DifferentiableOn ℂ (p11SlowZ AR AB)
      {I : P11CVec (n + n) |
        ‖(fun i : Fin n => I (Fin.castAdd n i)) - KAM.realInclusion n C.J0‖ < p11s1 C eps / 2 ∧
        ‖(fun i : Fin n => I (Fin.natAdd n i))‖ < Real.pi * C.rz ^ 2 / 16} := by
    obtain ⟨hARd, hABd, -⟩ := id hP
    have hJR : DifferentiableOn ℂ (fun I : P11CVec (n + n) => (p11SlowJ I, p11SlowR I))
        {I : P11CVec (n + n) |
        ‖(fun i : Fin n => I (Fin.castAdd n i)) - KAM.realInclusion n C.J0‖ < p11s1 C eps / 2 ∧
        ‖(fun i : Fin n => I (Fin.natAdd n i))‖ < Real.pi * C.rz ^ 2 / 16} :=
      (p11SlowJ_differentiable.differentiableOn).prodMk p11SlowR_differentiable.differentiableOn
    exact (hARd.comp hJR fun I hI => (hZm I hI).2).add (hABd.comp hJR fun I hI => (hZm I hI).2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the fast identity
    intro z hz
    obtain ⟨-, -, -, -, hU⟩ := p11_slow_pt hC heps hεM hsm64 (hSsub hz)
    have hid' := hidd _ hU
    have e1 : (fun i : Fin n => (p11PolarC z).2 (Fin.castAdd n i)) =
        fun i => z.2 (Fin.castAdd n i) := by funext i; simp [p11PolarC]
    have hPt : ((fun i : Fin n => (p11PolarC z).1 (Fin.natAdd n i)),
        fun i : Fin n => (p11PolarC z).2 (Fin.natAdd n i)) = p11PolPt z := rfl
    rw [e1, hPt] at hid'
    rw [hid']
    unfold p11SlowH0 p11SlowF2 p11SlowJ
    ring
  · intro I hI
    unfold p11SlowH0
    rw [p11_slow_secZ_eq hC Fast hF hP heps hεM hsm64 hI]
    rfl
  · intro I hI
    rfl
  · -- holomorphy of `Ẑ`
    exact hZd
  · -- bound of `Ẑ`
    intro I hI
    obtain ⟨hz, hS⟩ := hZm I hI
    obtain ⟨-, -, hARb, hABb, -⟩ := id hP
    have h1 := hARb _ hS
    have h2 := hABb _ hS
    simp only at h1 h2
    have hr : 0 < Real.pi * (C.rz / 2) ^ 2 := by positivity
    have h3 : 4 * ‖p11SlowR I‖ / (Real.pi * (C.rz / 2) ^ 2) ≤ 1 := by
      rw [div_le_one hr]
      have : ‖p11SlowR I‖ < Real.pi * (C.rz / 2) ^ 2 / 4 := mem_ball_zero_iff.1 hS.2
      linarith
    have h4 : (4 * ‖p11SlowR I‖ / (Real.pi * (C.rz / 2) ^ 2)) ^ 2 ≤ 1 :=
      pow_le_one₀ (by positivity) h3
    have h5 : 2 ^ (2 * n) * (C.MF / 16) * (4 * ‖p11SlowR I‖ / (Real.pi * (C.rz / 2) ^ 2)) ^ 2 ≤
        2 ^ (2 * n) * (C.MF / 16) := by
      calc _ ≤ 2 ^ (2 * n) * (C.MF / 16) * 1 := by gcongr
        _ = _ := mul_one _
    unfold p11SlowZ
    refine (norm_add_le _ _).trans ?_
    have : ‖AR (p11SlowJ I, p11SlowR I)‖ ≤ 2 ^ (2 * n) * (C.MF / 16) := by
      refine h1.trans ?_
      exact h5
    nlinarith
  · -- jets
    exact p11_slow_Z_jets hC Fast heps hεM hsm hP hcZ
  · -- `h₀` holomorphic on the box
    have hbox : p11SlowBox C eps ⊆
        {I : P11CVec (n + n) | ‖p11SlowJ I - KAM.realInclusion n C.J0‖ < p11s1 C eps / 4} :=
      fun I hI => (p11SlowBox_mem heps hs0 hI).1
    have hh : DifferentiableOn ℂ (fun I : P11CVec (n + n) => C.h (p11SlowJ I))
        (p11SlowBox C eps) := by
      obtain ⟨-, -, -, -, hhd, -⟩ := id hC
      exact hhd.comp p11SlowJ_differentiable.differentiableOn fun I hI =>
        mem_ball_iff_norm.2 (lt_of_lt_of_le (hbox hI) (by linarith [p11s1_le C eps]))
    have hsec := (p11SlowSec_differentiableOn hC (s := p11s1 C eps / 4)
      (by linarith [p11s1_le C eps])).mono hbox
    have hZb := hZd.mono (fun I hI => hboxZ I hI)
    exact hh.add ((hsec.add hZb).const_smul (eps : ℂ))
  · exact (p11_slow_f2_differentiableOn hC Fast hF hP heps hεM hsm64).mono hSsub
  · exact fun x hx => p11_slow_f2_real hC Fast hF hP heps hεM hsm64 x (hSsub hx)
  · exact fun I hI => p11_slow_h0_real hC Fast hF hP heps hεM hsm64 hI
  · exact fun z hz i => p11_slow_f2_periodic hC Fast hF (p11SlowZ AR AB) heps hεM hsm64 z
      (hSsub hz) i
  · intro I hI
    obtain ⟨hs, hw⟩ := p11_slow_f2_wbound hC Fast hF hP heps hεM hsm64 hrate I hI
    refine ⟨hs, hw.trans ?_⟩
    have hε1 : eps ≤ Real.exp (-1) := le_trans (by nlinarith) hεM
    have hL : 1 ≤ Real.log (1 / eps) := log_inv_ge_one heps hε1
    have h0 : 0 ≤ eps ^ (5 / 2 : ℝ) * Real.log (1 / eps) ^ (2 * C.tau + 1) :=
      mul_nonneg (Real.rpow_nonneg heps.le _) (Real.rpow_nonneg (by linarith) _)
    calc _ = ((Real.cosh (Real.pi * (C.sigma / 12)) / Real.sinh (Real.pi * (C.sigma / 12))) ^
          (n + n) * p11SlowC0 C c1) * (eps ^ (5 / 2 : ℝ) * Real.log (1 / eps) ^ (2 * C.tau + 1)) :=
          by ring
      _ ≤ c * (eps ^ (5 / 2 : ℝ) * Real.log (1 / eps) ^ (2 * C.tau + 1)) :=
          mul_le_mul_of_nonneg_right hcw h0
      _ = _ := by ring

/-- **P11A-P7b main output** (graph steps `stepP:p11:as-osc` and, for the weighted bound,
`stepP:p11:as-concl`; `bpP:p11:avg-slow` (a)): constants `c ≥ 1`, `ε₂ > 0`, depending only on
the secular data, such that for every `ε ≤ ε₂` and every fast datum satisfying `P11FastSpec`
there are `Ẑ`, `h₀`, `f₂` with `P11SlowOscSpec`.  Unsigned; consumed by P7c and P7d. -/
theorem p11_slow_osc (hC : P11SecularSpec D C) :
    ∃ c eps2 : ℝ, 1 ≤ c ∧ 0 < eps2 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ eps2 →
      ∀ Fast : P11FastData n, P11FastSpec C eps Fast →
        ∃ Z h0 : P11CVec (n + n) → ℂ, ∃ f2 : P11Phase (n + n) → ℂ,
          P11SlowOscSpec C Fast eps c Z h0 f2 := by
  obtain ⟨-, -, -, -, -, -, -, hrz0, -, hMF⟩ := fast_consts hC
  obtain ⟨c1, eps1, h1, hrate⟩ := p11eta1_source_rate hC
  have hM0 : 0 < C.MF := by linarith
  refine ⟨max 1 (max (p11SlowCZ C) ((Real.cosh (Real.pi * (C.sigma / 12)) /
    Real.sinh (Real.pi * (C.sigma / 12))) ^ (n + n) * p11SlowC0 C c1)),
    min (min (Real.exp (-1) / C.MF) (C.rz ^ 2 / 129)) eps1, le_max_left _ _, ?_, ?_⟩
  · exact lt_min (lt_min (div_pos (Real.exp_pos _) hM0) (by positivity)) h1
  · intro eps heps hle Fast hF
    have h1' : eps ≤ Real.exp (-1) / C.MF := hle.trans ((min_le_left _ _).trans (min_le_left _ _))
    have h2' : eps ≤ C.rz ^ 2 / 129 := hle.trans ((min_le_left _ _).trans (min_le_right _ _))
    have h3' : eps ≤ eps1 := hle.trans (min_le_right _ _)
    refine p11_slow_osc_at hC Fast hF heps ?_ ?_ (hrate eps heps h3')
      ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _))
    · rwa [le_div_iff₀ hM0] at h1'
    · have : 0 < C.rz ^ 2 := by positivity
      rw [le_div_iff₀ (by norm_num)] at h2'
      linarith

end Main

end KAM.Planetary

end
