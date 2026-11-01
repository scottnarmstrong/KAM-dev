/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.RealFlowPicard
public import KAM.Wave.KamStep.RealTaylorFun
public import KAM.Wave.Homological.CompleteZeroReal
public import KAM.Wave.Homological.ModifiedReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Reality clauses of the KAM step (blueprint-W `bpW:w5:step` (i), (ii); `bpW:w5:new-ham` (ii))

Off-frontier, source-faithful infrastructure (W5-REAL, item 1); the dependency graph is still being
built.

* `stepTheorem_reality_of_eps0_pos` (`WaveStepHyp`, non-modified case): `Φ` maps real points of
  `D_+` to real points, and `P_+` is real at the real points of `D_+`.
* `stepTheoremMod_reality_of_eps0_pos` (`StepHypMod`, modified case): the same.

These two are conditional helpers: `WaveStepHyp`, `StepHypMod` carry the non-source premise
`ε₀ > 0`. The source-facing clauses are conjuncts of `stepTheorem`, `stepTheoremMod`
(`StepTheoremSrc.lean`), derived through the splitting `(ε₀*, ε₁*)`.
* `kamDomain_star_mem`: the domains `D(s,r)` are invariant under complex conjugation of all
  coordinates (the other half of "`P_+` is real", `bpW:w5:class`).

Route. `R` is real (`stepTaylorOf_isRealTaylor`), so `F` is real by W4
(`homLemma1Complete_real_gen`; modified case `homModSolveTaylor_isReal`); hence `X_F` is real at
real points (`stepField_real`) and its flow is real (`stepFlow_real`). For `P_+` use
`H ∘ Φ = N_+ + P_+ + â₀` (`StepCore.conj_eq`): `N`, `N_+` (real frequencies) and `P` are real at
real points, `Φ w` is real and `â₀ = [a]` is real.

The `StepCore` statements `StepCore.phi_real_of_FT_real`, `StepCore.Pplus_real_of_FT_real` are
conditional helpers: they assume that the abstract solution family `FT` is real, which `StepCore`
does not record; `WaveStepHyp` and `StepHypMod` discharge it from W4.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

namespace KAM.Wave

open KAM

/-- **`D(s,r)` is invariant under conjugation** of all coordinates. -/
theorem kamDomain_star_mem {s r : ℝ} {w : KamPhase} (hw : w ∈ kamDomain s r) :
    (star w.1, star w.2.1, star w.2.2.1, star w.2.2.2) ∈ kamDomain s r := by
  obtain ⟨h1, h2, h3⟩ := hw
  refine ⟨fun i => ?_, ?_, ?_⟩
  · simpa [Pi.star_apply, Complex.star_def] using h1 i
  · simpa [norm_star] using h2
  · simpa [norm_star] using h3

/-- The normal form `N = ⟨ω, y⟩ + Σ Ω_j z_j \bar z_j` is real at real points. -/
theorem stepNfun_real {a p γ K0 : ℝ} {Ω : ℕ+ → ℝ} (hG : HomGuard a p γ) (hK0 : 0 ≤ K0)
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (ω : Fin 2 → ℝ) {w : KamPhase}
    (hw : StepReal w) : (stepNfun hG hK0 hΩ ω w).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  unfold stepNfun homNfun
  have hzb : stepZb w = star (stepZ w) := stepZb_eq_star hw
  simp only [stepToHom_apply, homPrY, homPrZ, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', map_add, homLomega_apply,
    homNOmegaCLM_apply, map_sum, map_mul, Complex.conj_ofReal, hzb, Complex.conj_tsum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.conj_eq_iff_im.mpr (hw.2.1 k)]
  · refine tsum_congr fun j => ?_
    have hc : conj (homNcoef a p Ω j) = homNcoef a p Ω j := by
      unfold homNcoef; rw [map_div₀, map_pow, Complex.conj_ofReal, Complex.conj_ofReal]
    rw [hc, lp.star_apply, Complex.star_def, Complex.conj_conj]
    ring

variable {a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF : ℝ} {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}
  {FT : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ)}

namespace StepCore

variable (H : StepCore a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF Par ω Ω P X FT)
include H

/-- `R_ξ` is real (`bpW:w5:taylor` (i)). -/
theorem R_isRealTaylor {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) : (H.R ξ).isRealTaylor := by
  rw [H.R_eq hξ]
  exact stepTaylorOf_isRealTaylor H.ha H.hp H.hpb H.hs H.hr (H.hP ξ hξ) (H.hper ξ hξ) (H.hb ξ hξ)
    (H.hreal ξ hξ)

/-- `â₀ = [a]` is real. -/
theorem a0_im {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) : (H.a0 ξ).im = 0 := by
  have := homCoeff_zero_clm Complex.imCLM (f := (H.R ξ).a0)
    (fun x => by rw [Complex.imCLM_apply]; exact (H.R_isRealTaylor hξ x).1)
  simpa [StepCore.a0] using this

variable [Fact (0 < r)]

/-- `Φ` maps real points of `D_+` to real points, conditional helper: it assumes that the abstract
solution family `FT` is real (discharged for `WaveStepHyp`, `StepHypMod`). -/
theorem phi_real_of_FT_real (hFT : ∀ ξ ∈ Par, (FT ξ).isRealTaylor) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 5 * σ) (η * r))
    (hwr : StepReal (StepPhase.toK w)) : StepReal (StepPhase.toK (H.Phi ξ w)) :=
  stepFlow_real H.ha H.hp H.hpb H.hσ H.hσ1 (by linarith [H.hσs, H.hσ]) (FT ξ) (H.F_field ξ hξ)
    H.M₀_pos H.mf_lt
    (fun _ _ hzr => stepField_real H.ha H.hp H.hpb (by linarith [H.hσs, H.hσ] : 0 < s - σ) (FT ξ)
      (hFT ξ hξ) hzr)
    (H.Dplus_sub_U hw) hwr ⟨by norm_num, le_rfl⟩

/-- `P_+` is real at the real points of `D_+`, conditional helper (assumes `FT` real). -/
theorem Pplus_real_of_FT_real (hFT : ∀ ξ ∈ Par, (FT ξ).isRealTaylor) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ Par) {w : StepPhase r} (hw : w ∈ stepDomain r (s - 5 * σ) (η * r))
    (hwr : StepReal (StepPhase.toK w)) : (H.Pplus ξ w).im = 0 := by
  have hc := congrArg Complex.im (H.conj_eq hξ hw)
  have hΦ := H.phi_real_of_FT_real hFT hξ hw hwr
  have h1 := stepNfun_real H.hG H.hK0 (homOmega_le H.freq hξ) (ω ξ) hΦ
  have hr := H.hr
  have hD : StepPhase.toK (H.Phi ξ w) ∈ kamDomain s r :=
    kamDomain_mono (by linarith [H.hσ]) (by have := H.hη0; positivity)
      (by nlinarith [H.hη, H.hη0]) (H.phi_mem hξ hw)
  have h2 := H.hreal ξ hξ _ hD hΦ
  have h3 := stepNfun_real H.hG H.hKp (H.omegaPlus_bound hξ) (H.omegaPlus ξ) hwr
  have h4 := H.a0_im hξ
  simp only [Complex.add_im] at hc
  linarith

end StepCore

namespace WaveStepHyp

variable (H : WaveStepHyp a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
include H

/-- `F_ξ` is real (W4 `bpW:w4:lemma1` (i), `homLemma1Complete_real_gen`). -/
theorem FT_isRealTaylor : ∀ ξ ∈ Par, (H.FT ξ).isRealTaylor := fun ξ hξ => by
  rw [H.FT_eq hξ]
  exact (homLemma1Complete_real_gen H.freq H.mel H.hτ H.hα H.hσ H.hσs' hξ (H.R ξ)
    (H.core.R_isRealTaylor hξ)).1

end WaveStepHyp

namespace StepHypMod

variable {β : ℝ} (H : StepHypMod a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
include H

/-- The `p+1` Taylor family `R_ξ` is real. -/
theorem R1_isRealTaylor {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) : (H.R1 ξ).isRealTaylor := by
  have : Fact (0 < r) := ⟨H.hr⟩
  unfold StepHypMod.R1
  rw [stepTaylorFam_of_mem H.ha H.hp (homModPP1 p) H.hs H.hr H.hP H.hper H.hb hξ]
  exact stepTaylorOf_isRealTaylor H.ha H.hp (homModPP1 p) H.hs H.hr (H.hP ξ hξ) (H.hper ξ hξ)
    (H.hb ξ hξ) (H.hreal ξ hξ)

/-- `F_ξ` (modified divisors) is real (`homModSolveTaylor_isReal`). -/
theorem FT_isRealTaylor : ∀ ξ ∈ Par, (H.FT ξ).isRealTaylor := fun ξ hξ => by
  unfold StepHypMod.FT
  rw [stepFTfamMod_of_mem H.hτ H.hα H.hσ H.hσs' H.hβ0 H.hβ H.mel H.R1 hξ]
  exact homModSolveTaylor_isReal _ _ _ _ _ _ _ (H.R1_isRealTaylor hξ)

end StepHypMod

/-- **Reality clauses of the KAM step** (blueprint `bpW:w5:step` (i) "`Φ` is real on real points"
and (ii) "`P_+` is real"; `bpW:w5:flow` (iv), `bpW:w5:new-ham` (ii)), non-modified case: for
`ξ ∈ Π`, `Φ = H.core.Phi ξ` maps the real points of `D_+ = D(s-5σ, ηr)` to real points, and
`P_+ = H.core.Pplus ξ` is real at the real points of `D_+` (`D_+` is conjugation invariant,
`kamDomain_star_mem`). -/
theorem stepTheorem_reality_of_eps0_pos
    (H : WaveStepHyp a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) [Fact (0 < r)] :
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), StepReal (StepPhase.toK w) →
      StepReal (StepPhase.toK (H.core.Phi ξ w))) ∧
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), StepReal (StepPhase.toK w) →
      (H.core.Pplus ξ w).im = 0) :=
  ⟨fun _ hξ _ hw hwr => H.core.phi_real_of_FT_real H.FT_isRealTaylor hξ hw hwr,
    fun _ hξ _ hw hwr => H.core.Pplus_real_of_FT_real H.FT_isRealTaylor hξ hw hwr⟩

/-- **Reality clauses of the KAM step**, modified case (blueprint `bpW:w5:step` (i), (ii) for
`StepHypMod`; `Φ = H.core.Phi ξ`, `P_+ = H.core.Pplus ξ`). -/
theorem stepTheoremMod_reality_of_eps0_pos {β : ℝ}
    (H : StepHypMod a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) [Fact (0 < r)] :
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), StepReal (StepPhase.toK w) →
      StepReal (StepPhase.toK (H.core.Phi ξ w))) ∧
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), StepReal (StepPhase.toK w) →
      (H.core.Pplus ξ w).im = 0) :=
  ⟨fun _ hξ _ hw hwr => H.core.phi_real_of_FT_real H.FT_isRealTaylor hξ hw hwr,
    fun _ hξ _ hw hwr => H.core.Pplus_real_of_FT_real H.FT_isRealTaylor hξ hw hwr⟩

end KAM.Wave
