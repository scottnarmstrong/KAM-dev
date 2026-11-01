/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Nekhoroshev.Defs.HasDefiniteFastPart
public import KAM.Frozen.Nekhoroshev.Defs.RealPart
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Planetary.Exponential.KeplerData
public import KAM.Planetary.StrongAMD.Threshold.Defs

/-!
# The Kepler part as the fast Hamiltonian of the partial-convexity Nekhoroshev theorem

Package LP3-KEP, plan row `docs/tracks/LP/lp3/LP3-PLAN.md` (LP3-KEP); track LP, non-frozen.
The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

For `h = planetaryKeplerC ν = -∑ ν_i³ / (2 I_i²)` and for `-h`, on sharp fast sets `G' ⊆ U_ρ₀`
(`U_ρ₀ = cthickening ρ₀ U`, `U ⊆ chamber ν` compact, `ρ₀ = Imin / 4`) and every collar
`0 < ρ ≤ ρ₀`, every premise of `KAM.Nekhoroshev.partialConvex_nekhoroshev` concerning only the fast
Hamiltonian: `hhol`, `hC2`, `hreal`, `hHess` and `hdef` (the sealed `HasDefiniteFastPart`, sign
`σ = -1` for `h` and `σ = 1` for `-h`).  All constants depend only on `(ν, U)`, never on `G'`
or `ρ`:

* `exists_keplerMargin`: `Imin`, `Imax` and the coordinate margins on the complex collar;
* `keplerC_clauses`, `keplerC_definite`: the clauses for `h` (explicit `Mcomplex`, `g`, `m`);
* `lp3_kepler_data`: the packaged corollary, for `h` and `-h`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open Set Metric

variable {n : ℕ}

/-- A finite family of positive numbers has a positive common lower bound. -/
theorem exists_pos_le_forall_fin (δ : Fin n → ℝ) (hδ : ∀ i, 0 < δ i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ δ i := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨1, one_pos, fun i => (h.false i).elim⟩
  · obtain ⟨i0, hi0⟩ := Finite.exists_min δ
    exact ⟨δ i0, hδ i0, hi0⟩

/-- A compact `U ⊆ chamber ν` has uniform coordinate bounds `0 < Imin ≤ I_i ≤ Imax`. -/
theorem exists_chamber_bounds {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)} (hUc : IsCompact U)
    (hUch : U ⊆ chamber ν) :
    ∃ Imin Imax : ℝ, 0 < Imin ∧ 0 < Imax ∧ ∀ I ∈ U, ∀ i, Imin ≤ I i ∧ I i ≤ Imax := by
  have hlow : ∀ i, ∃ δ : ℝ, 0 < δ ∧ ∀ I ∈ U, δ ≤ I i := fun i => by
    rcases U.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨I0, hI0, hmin⟩ := hUc.exists_isMinOn hne (continuous_apply i).continuousOn
      exact ⟨I0 i, (hUch hI0).1 i, fun I hI => hmin hI⟩
  choose δ hδ hδle using hlow
  obtain ⟨Imin, hIminpos, hIminle⟩ := exists_pos_le_forall_fin δ hδ
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hUc.isBounded
  refine ⟨Imin, max C 1, hIminpos, lt_max_of_lt_right one_pos, fun I hI i => ⟨?_, ?_⟩⟩
  · exact (hIminle i).trans (hδle i I hI)
  · calc I i ≤ ‖I i‖ := le_abs_self _
      _ ≤ ‖I‖ := norm_le_pi_norm I i
      _ ≤ C := hC I hI
      _ ≤ max C 1 := le_max_left _ _

/-- Every point of the complex `ρ`-neighbourhood of `G' ⊆ cthickening ρ₀ U` has real parts within
`ρ₀ + ρ` of a common point `u ∈ U`. -/
theorem actionNbhd_re_near {U G' : Set (Fin n → ℝ)} (hUc : IsCompact U) {ρ₀ ρ : ℝ}
    (hρ₀ : 0 ≤ ρ₀) (hG' : G' ⊆ cthickening ρ₀ U) {z : Fin n → ℂ}
    (hz : z ∈ KAM.actionNbhd G' ρ) :
    ∃ u ∈ U, ∀ i, |(z i).re - u i| < ρ₀ + ρ := by
  obtain ⟨J, hJ, hlt⟩ := hz
  have hJ' := hG' hJ
  rw [hUc.cthickening_eq_biUnion_closedBall hρ₀] at hJ'
  obtain ⟨u, hu, hJu⟩ := Set.mem_iUnion₂.1 hJ'
  refine ⟨u, hu, fun i => ?_⟩
  have h1 : |J i - u i| ≤ ρ₀ := by
    have := dist_le_pi_dist J u i
    rw [Real.dist_eq] at this
    exact this.trans (mem_closedBall.1 hJu)
  have hdiff : ‖z i - (J i : ℂ)‖ ≤ ‖z - fun j => (J j : ℂ)‖ :=
    norm_le_pi_norm (z - fun j => (J j : ℂ)) i
  have hre : |(z i).re - J i| ≤ ‖z i - (J i : ℂ)‖ := by
    have := Complex.abs_re_le_norm (z i - (J i : ℂ))
    simpa using this
  calc |(z i).re - u i| = |((z i).re - J i) + (J i - u i)| := by ring_nf
    _ ≤ |(z i).re - J i| + |J i - u i| := abs_add_le _ _
    _ < ρ + ρ₀ := by linarith [hre.trans hdiff |>.trans_lt hlt]
    _ = ρ₀ + ρ := add_comm _ _

/-- **Positivity margin** (statement 1).  For compact `U ⊆ chamber ν` there are `0 < Imin` and
`0 < Imax` with `Imin ≤ I_i ≤ Imax` on `U` such that, with the collar `ρ₀ = Imin / 4`, every
`G' ⊆ cthickening ρ₀ U` and every `0 < ρ ≤ ρ₀`, the complex neighbourhood `actionNbhd G' ρ` has
`Imin / 2 ≤ Re z_i` (hence `Imin / 4 ≤ ‖z_i‖`) and its real points have
`Imin / 2 ≤ I_i ≤ Imax + Imin / 2`. -/
theorem exists_keplerMargin {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)} (hUc : IsCompact U)
    (hUch : U ⊆ chamber ν) :
    ∃ Imin Imax : ℝ, 0 < Imin ∧ 0 < Imax ∧ (∀ I ∈ U, ∀ i, Imin ≤ I i ∧ I i ≤ Imax) ∧
      ∀ G' : Set (Fin n → ℝ), G' ⊆ cthickening (Imin / 4) U → ∀ ρ : ℝ, ρ ≤ Imin / 4 →
        (∀ z ∈ KAM.actionNbhd G' ρ, ∀ i, Imin / 2 ≤ (z i).re ∧ Imin / 4 ≤ ‖z i‖) ∧
        ∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ KAM.actionNbhd G' ρ →
          ∀ i, Imin / 2 ≤ I i ∧ I i ≤ Imax + Imin / 2 := by
  obtain ⟨Imin, Imax, hmin, hmax, hb⟩ := exists_chamber_bounds hUc hUch
  refine ⟨Imin, Imax, hmin, hmax, hb, fun G' hG' ρ hρ => ?_⟩
  have key : ∀ z ∈ KAM.actionNbhd G' ρ, ∀ i, Imin / 2 ≤ (z i).re ∧ (z i).re ≤ Imax + Imin / 2 := by
    intro z hz i
    obtain ⟨u, hu, hnear⟩ := actionNbhd_re_near hUc (by positivity) hG' hz
    have h1 := abs_lt.1 (hnear i)
    have h2 := hb u hu i
    constructor <;> linarith [h2.1, h2.2]
  refine ⟨fun z hz i => ⟨(key z hz i).1, ?_⟩, fun I hI i => ?_⟩
  · have := (key z hz i).1
    linarith [Complex.re_le_norm (z i)]
  · have := key _ hI i
    simpa using this

/-- The explicit complex Hessian constant `∑ 3 ν_i³ / c⁴` (here `c = Imin / 2`). -/
def keplerHessConst (ν : Fin n → ℝ) (c : ℝ) : ℝ := ∑ i, 3 * ν i ^ 3 / c ^ 4

theorem keplerHessConst_pos [NeZero n] {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {c : ℝ}
    (hc : 0 < c) : 0 < keplerHessConst ν c :=
  Finset.sum_pos (fun i _ => by have := hν i; positivity) Finset.univ_nonempty

/-- Holomorphy, complex `C²`, reality on real points and the complex Hessian bound for
`h = planetaryKeplerC ν`, on any set of points with real part `≥ c > 0`. -/
theorem keplerC_clauses {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {c : ℝ} (hc : 0 < c)
    {G' : Set (Fin n → ℝ)} {ρ : ℝ}
    (hmarg : ∀ z ∈ KAM.actionNbhd G' ρ, ∀ i, c ≤ (z i).re) :
    DifferentiableOn ℂ (planetaryKeplerC ν) (KAM.actionNbhd G' ρ) ∧
    ContDiffOn ℂ 2 (planetaryKeplerC ν) (KAM.actionNbhd G' ρ) ∧
    (∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ KAM.actionNbhd G' ρ →
      (planetaryKeplerC ν (fun i => (I i : ℂ))).im = 0) ∧
    (∀ z ∈ KAM.actionNbhd G' ρ, ‖fderiv ℂ (fderiv ℂ (planetaryKeplerC ν)) z‖ ≤
      keplerHessConst ν c) := by
  have hz0 : ∀ z ∈ KAM.actionNbhd G' ρ, ∀ i, z i ≠ 0 := fun z hz i h0 => by
    have := hmarg z hz i
    rw [h0] at this
    simp at this
    linarith
  have hCD : ContDiffOn ℂ 2 (planetaryKeplerC ν) (KAM.actionNbhd G' ρ) :=
    (keplerSumGen_contDiffOn (𝕜 := ℂ) ν 2).mono fun z hz => hz0 z hz
  refine ⟨hCD.differentiableOn (by norm_num), hCD, ?_, ?_⟩
  · intro I _
    rw [planetaryKeplerC_ofReal]
    exact Complex.ofReal_im _
  · intro z hz
    refine (keplerSumGen_hess_norm_le (𝕜 := ℂ) ν (hz0 z hz)).trans ?_
    unfold keplerHessConst
    refine Finset.sum_le_sum fun i _ => ?_
    have hre : c ≤ ‖z i‖ := (hmarg z hz i).trans (Complex.re_le_norm (z i))
    rw [abs_of_pos (hν i)]
    have := hν i
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hc.le hre 4)

/-- The same clauses for `-h`, by negation (the same Hessian constant). -/
theorem keplerCNeg_clauses {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {c : ℝ} (hc : 0 < c)
    {G' : Set (Fin n → ℝ)} {ρ : ℝ}
    (hmarg : ∀ z ∈ KAM.actionNbhd G' ρ, ∀ i, c ≤ (z i).re) :
    DifferentiableOn ℂ (-planetaryKeplerC ν) (KAM.actionNbhd G' ρ) ∧
    ContDiffOn ℂ 2 (-planetaryKeplerC ν) (KAM.actionNbhd G' ρ) ∧
    (∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ KAM.actionNbhd G' ρ →
      ((-planetaryKeplerC ν) (fun i => (I i : ℂ))).im = 0) ∧
    (∀ z ∈ KAM.actionNbhd G' ρ, ‖fderiv ℂ (fderiv ℂ (-planetaryKeplerC ν)) z‖ ≤
      keplerHessConst ν c) := by
  obtain ⟨h1, h2, h3, h4⟩ := keplerC_clauses hν hc hmarg
  refine ⟨h1.neg, h2.neg, fun I hI => by simpa using h3 I hI, fun z hz => ?_⟩
  have e1 : fderiv ℂ (-planetaryKeplerC ν) = -fderiv ℂ (planetaryKeplerC ν) :=
    funext fun _ => fderiv_neg
  rw [e1, fderiv_neg, ContinuousLinearMap.opNorm_neg]
  exact h4 z hz

/-- **Definite fast part** (statement 3), `σ = -1`: the real Hessian of `realPart h` is
`diag (-3 ν_i³ / I_i⁴)`; constants `g = νmin³ / Ibar³`, `m = 3 νmin³ / Ibar⁴` for real points with
`0 < I_i ≤ Ibar` and `0 < νmin ≤ ν_i`. -/
theorem keplerC_definite (hn : 1 ≤ n) {ν : Fin n → ℝ} {νmin Ibar : ℝ} (hνmin : 0 < νmin)
    (hle : ∀ i, νmin ≤ ν i) (hIbar : 0 < Ibar) {G' : Set (Fin n → ℝ)} {ρ : ℝ}
    (hreal : ∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ KAM.actionNbhd G' ρ →
      ∀ i, 0 < I i ∧ I i ≤ Ibar) :
    KAM.Nekhoroshev.HasDefiniteFastPart G' ρ (νmin ^ 3 / Ibar ^ 3) (3 * νmin ^ 3 / Ibar ^ 4)
      (planetaryKeplerC ν) := by
  have hνpos : ∀ i, 0 < ν i := fun i => hνmin.trans_le (hle i)
  refine ⟨by positivity, by positivity, ?_, -1, Or.inr rfl, fun I hI => ?_⟩
  · rw [realPart_planetaryKeplerC]
    exact (keplerSumGen_contDiffOn (𝕜 := ℝ) ν 3).mono fun I hI i => (hreal I hI i).1.ne'
  · have hnz : ∀ i, I i ≠ 0 := fun i => (hreal I hI i).1.ne'
    refine ⟨?_, fun w => ?_⟩
    · let i0 : Fin n := ⟨0, by omega⟩
      refine le_trans ?_ (norm_le_pi_norm (KAM.frequencyMap (planetaryKeplerC ν) I) i0)
      show _ ≤ ‖fderiv ℝ (KAM.Nekhoroshev.realPart (planetaryKeplerC ν)) I (Pi.single i0 1)‖
      rw [realPart_planetaryKeplerC, keplerSumGen_real_freq _ hnz]
      have hi := hreal I hI i0
      have := hνpos i0
      rw [Real.norm_of_nonneg (by have := hi.1; positivity)]
      exact div_le_div₀ (by positivity) (pow_le_pow_left₀ hνmin.le (hle i0) 3)
        (pow_pos hi.1 3) (pow_le_pow_left₀ hi.1.le hi.2 3)
    · show _ ≤ _ * fderiv ℝ (fderiv ℝ (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))) I w w
      rw [realPart_planetaryKeplerC, keplerSumGen_real_hess _ hnz, Finset.mul_sum]
      have : -1 * -∑ i, 3 * ν i ^ 3 / I i ^ 4 * w i ^ 2
          = ∑ i, 3 * ν i ^ 3 / I i ^ 4 * w i ^ 2 := by ring
      rw [this]
      refine Finset.sum_le_sum fun i _ => ?_
      have hi := hreal I hI i
      have hm : 3 * νmin ^ 3 / Ibar ^ 4 ≤ 3 * ν i ^ 3 / I i ^ 4 :=
        div_le_div₀ (by have := hνpos i; positivity)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hνmin.le (hle i) 3) (by norm_num))
          (pow_pos hi.1 4) (pow_le_pow_left₀ hi.1.le hi.2 4)
      exact mul_le_mul_of_nonneg_right hm (sq_nonneg _)

/-- **Packaged fast-part data of `partialConvex_nekhoroshev`** for `h = planetaryKeplerC ν` and
`-h`.  The constants `ρ₀, g, m, Mcomplex` depend only on `(ν, U)`; for every `G' ⊆ cthickening ρ₀ U`
and `0 < ρ ≤ ρ₀`, the premises `hhol`, `hC2`, `hreal`, `hHess`, `hdef` hold for `h` and for `-h`. -/
theorem lp3_kepler_data (hn : 1 ≤ n) {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) :
    ∃ ρ₀ g m Mcomplex : ℝ, 0 < ρ₀ ∧ 0 < g ∧ 0 < m ∧ 0 < Mcomplex ∧
      ∀ G' : Set (Fin n → ℝ), G' ⊆ cthickening ρ₀ U → ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
        (DifferentiableOn ℂ (planetaryKeplerC ν) (KAM.actionNbhd G' ρ) ∧
          ContDiffOn ℂ 2 (planetaryKeplerC ν) (KAM.actionNbhd G' ρ) ∧
          (∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ KAM.actionNbhd G' ρ →
            (planetaryKeplerC ν (fun i => (I i : ℂ))).im = 0) ∧
          (∀ z ∈ KAM.actionNbhd G' ρ,
            ‖fderiv ℂ (fderiv ℂ (planetaryKeplerC ν)) z‖ ≤ Mcomplex) ∧
          KAM.Nekhoroshev.HasDefiniteFastPart G' ρ g m (planetaryKeplerC ν)) ∧
        (DifferentiableOn ℂ (-planetaryKeplerC ν) (KAM.actionNbhd G' ρ) ∧
          ContDiffOn ℂ 2 (-planetaryKeplerC ν) (KAM.actionNbhd G' ρ) ∧
          (∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ KAM.actionNbhd G' ρ →
            ((-planetaryKeplerC ν) (fun i => (I i : ℂ))).im = 0) ∧
          (∀ z ∈ KAM.actionNbhd G' ρ,
            ‖fderiv ℂ (fderiv ℂ (-planetaryKeplerC ν)) z‖ ≤ Mcomplex) ∧
          KAM.Nekhoroshev.HasDefiniteFastPart G' ρ g m (-planetaryKeplerC ν)) := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨Imin, Imax, hmin, hmax, -, hM⟩ := exists_keplerMargin hUc hUch
  obtain ⟨νmin, hνmin, hνle⟩ := exists_pos_le_forall_fin ν hν
  have hIbar : 0 < Imax + Imin / 2 := by positivity
  refine ⟨Imin / 4, νmin ^ 3 / (Imax + Imin / 2) ^ 3, 3 * νmin ^ 3 / (Imax + Imin / 2) ^ 4,
    keplerHessConst ν (Imin / 2), by positivity, by positivity, by positivity,
    keplerHessConst_pos hν (by positivity), fun G' hG' ρ _ hρ => ?_⟩
  obtain ⟨hz, hr⟩ := hM G' hG' ρ hρ
  have hmarg : ∀ z ∈ KAM.actionNbhd G' ρ, ∀ i, Imin / 2 ≤ (z i).re :=
    fun z h i => (hz z h i).1
  have hreal : ∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ KAM.actionNbhd G' ρ →
      ∀ i, 0 < I i ∧ I i ≤ Imax + Imin / 2 :=
    fun I h i => ⟨by linarith [(hr I h i).1], (hr I h i).2⟩
  have hdef := keplerC_definite hn hνmin hνle hIbar hreal
  obtain ⟨a1, a2, a3, a4⟩ := keplerC_clauses hν (by positivity : 0 < Imin / 2) hmarg
  obtain ⟨b1, b2, b3, b4⟩ := keplerCNeg_clauses hν (by positivity : 0 < Imin / 2) hmarg
  exact ⟨⟨a1, a2, a3, a4, hdef⟩, ⟨b1, b2, b3, b4, hasDefiniteFastPart_neg hdef⟩⟩

end KAM.Planetary.StrongAMD

end
