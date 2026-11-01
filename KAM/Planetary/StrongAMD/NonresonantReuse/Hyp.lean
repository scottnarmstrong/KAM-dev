/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Nekhoroshev.Partial.Nonresonant
public import KAM.Planetary.StrongAMD.NonresonantReuse.Kepler
public import KAM.Planetary.StrongAMD.NonresonantReuse.PertClass
public import KAM.Planetary.Exponential.Lift

/-!
# The engine hypotheses and the trace identity (package LP-NRR, items 4 and 5)

Package LP-NRR, MAIN Lemma 13 (`LP:MAIN L13 (429–464)`), N6, track LP, non-frozen.

* `lpTrace`: on `b.realDom b.rB`,
  `((liftFast (lpKepler ν) + lpPert μ b.lam fc) (extCx y)).re`
  `= lpRescaleHam b.lam (liftChartHam ν μ) y`;
* `lpExtNFHyp`: the engine bundle `ExtNFHyp b s K α L 2 ε {0} (lpKepler ν) (lpPert μ b.lam fc)`,
  field by field.  Its numeric premises are the scale inequalities of `lp_scale_choice`; nothing
  about drift or AMD is assumed.
-/

@[expose] public noncomputable section

open KAM KAM.Planetary KAM.Nekhoroshev KAM.Weighted KAM.NormalForm Set

namespace KAM.Planetary.StrongAMD

variable {n : ℕ} {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ rg R M : ℝ}
  {fc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → ℂ}

theorem lp_coth_pos {x : ℝ} (hx : 0 < x) : 0 < coth x :=
  div_pos (Real.cosh_pos x) (Real.sinh_pos_iff.2 hx)

theorem lpM₂_pos {σ : ℝ} (hσ : 0 < σ) (hM : 0 < M) : 0 < lpM₂ n σ M := by
  have := lp_coth_pos (mul_pos Real.pi_pos hσ)
  unfold lpM₂
  positivity

section
variable {rs s₀ b₀ : ℝ} {I0 : Fin n → ℝ} {b : PartialBlock n n}

/-- Item 5: the trace identity on the real domain. -/
theorem lpTrace (hν : ∀ i, 0 < ν i) (hT : LPChartTube ν L δ rg R M fc) (hrs : 0 < rs)
    (hrg : rs ≤ 4 * rg) (hmax : max rs (max (4 * s₀) (4 * b₀)) < R / 2) (hs₀ : 0 < s₀)
    (hI0 : I0 ∈ strongLevelSet ν L δ) (hS : b.S = secularBall ν δ I0) (hIc : b.Ic = I0)
    (hrB : b.rB ≤ rs) (hrB0 : 0 < b.rB) (hw0 : 0 < b.w) (hw : b.w < 4 * b₀) (μ : ℝ)
    {y : ER n n} (hy : y ∈ b.realDom b.rB) :
    ((liftFast (lpKepler ν) + lpPert μ b.lam fc : EC n n → ℂ) (extCx y)).re =
      lpRescaleHam b.lam (liftChartHam ν μ) y := by
  have hpi := Real.pi_pos
  have ht : 0 < 2 * s₀ / Real.pi := by positivity
  have hts : 2 * Real.pi * (2 * s₀ / Real.pi) ≤ 4 * s₀ := by
    rw [le_iff_eq_or_lt]; left; field_simp; ring
  have hz : extCx y ∈ Dom n b.base b.rB (2 * s₀ / Real.pi) :=
    ⟨fun i => by simpa [extCx] using ht, hy.2⟩
  have hmem := lpPert_dom_mem hrs hrg hmax hI0 hS hIc hrB hrB0 hw0 hw ht hts hz
  rw [lpUnrescaleC_extCx] at hmem
  obtain ⟨hws, hfc⟩ := hT.real _ (lpTube_mono hT.R_pos hmem)
  have hfa : fast (lpUnrescale b.lam y).2 = fastAction y := by
    funext i; simp [lpUnrescale_apply, lpUnrescaleFun, fast, fastAction]
  have hfa' : fastAction (extCx y) = fun i => ((fastAction y i : ℝ) : ℂ) := rfl
  simp only [Pi.add_apply, liftFast, lpPert, lpUnrescaleC_extCx, hfc]
  unfold lpKepler
  rw [hfa', planetaryKeplerC_ofReal, ← Complex.ofReal_div, ← Complex.ofReal_mul,
    ← Complex.ofReal_add, Complex.ofReal_re]
  unfold lpRescaleHam liftChartHam
  rw [movingHamiltonian_poincareProd_split hν μ hws, hfa]
  simp only [keplerSumGen, RCLike.ofReal_real_eq_id, id_eq]
  ring

end

section
variable {rs s₀ b₀ : ℝ} {I0 : Fin n → ℝ} {b : PartialBlock n n}

/-- Item 4: the engine bundle, field by field. -/
theorem lpExtNFHyp (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hT : LPChartTube ν L δ rg R M fc)
    (hrs : 0 < rs) (hrg : rs ≤ 4 * rg) (hmax : max rs (max (4 * s₀) (4 * b₀)) < R / 2)
    (hI0 : I0 ∈ strongLevelSet ν L δ) (hS : b.S = secularBall ν δ I0) (hIc : b.Ic = I0)
    (hrB : b.rB ≤ rs) (hrB0 : 0 < b.rB) (hw0 : 0 < b.w) (hw : b.w < 4 * b₀)
    {Imin : ℝ} (hImin : 0 < Imin) (hI : ∀ i, Imin ≤ I0 i) (hρ : b.rB ≤ Imin / 2)
    {γ τ K s σ μ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    (hdio : ∀ k : Fin n → ℤ, k ≠ 0 →
      γ * KAM.Fourier.modeSize k ^ (-τ) ≤ |∑ i, (k i : ℝ) * lpFrequency ν I0 i|)
    (hM : 0 < M) (hs : 0 < s) (hσ : 0 < σ) (hμ : 0 < μ)
    (hts : 2 * Real.pi * (s + σ) ≤ 4 * s₀) (hK1 : 1 ≤ K)
    (hKL : K * lpKeplerLip ν Imin * b.rB ≤ γ / (2 * Real.pi) * K ^ (-τ) / 2)
    (hSL : 64 * Real.pi * n * s * b.rB ≤ b.w ^ 2) (hcut : 6 ≤ 2 * Real.pi * K * s) :
    ExtNFHyp b s K (γ / (2 * Real.pi) * K ^ (-τ)) (lpKeplerLip ν Imin) 2 (lpM₂ n σ M * μ) {0}
      (lpKepler ν) (lpPert μ b.lam fc) := by
  have hpi := Real.pi_pos
  have hI0ne : ∀ i, I0 i ≠ 0 := fun i => (hImin.trans_le (hI i)).ne'
  have hbase : ({KAM.realInclusion n b.Ic} : Set (Fin n → ℂ)) = {KAM.realInclusion n I0} := by
    rw [hIc]
  have hnd : 1 ≤ n := by omega
  have hK0 : 0 < K := by linarith
  refine
    { n_pos := hnd
      k_pos := hnd
      radius_pos := hrB0
      slow_width_pos := hw0
      s_pos := hs
      K_pos := hK0
      alpha_pos := by positivity
      L_nonneg := lpKeplerLip_nonneg hν Imin
      p_gt := by norm_num
      eps_pos := mul_pos (lpM₂_pos hσ hM) hμ
      symmetric := fun j => by simp
      hol := ?_
      real := fun I _ => lpKepler_real ν I
      nr := ?_
      lip := ?_
      divisor_size := by linarith
      slow := hSL
      pert := ?_
      bound := ?_
      cutoff := hcut }
  · rw [hIc]; exact lpKepler_differentiableOn hImin hI hρ
  · rw [hbase]; exact lpKepler_isNonresonant hI0ne hγ.le hτ.le hdio hK1
  · rw [hbase]; exact lpKepler_freqLipschitz hν hImin hI hρ
  · exact lpPert_extClass hT hrs hrg hmax hI0 hS hIc hrB hrB0 hw0 hw hs
      (by linarith [hts, mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) hpi) hσ]) μ
  · exact lpPert_wbound hT hrs hrg hmax hI0 hS hIc hrB hrB0 hw0 hw hs hσ hts hμ.le

end

end KAM.Planetary.StrongAMD

end
