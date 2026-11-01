/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.Bridge
public import KAM.Wave.KamStep.StepTheoremSrc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the hypotheses of the iterative lemma at stage `ν` (`bpW:w6:iter-lemma`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:iter-lemma` (milestone W6).

Fixed: `a = p = 1`, `p_+ = p + 1/2 = 3/2`, `τ = 24`, W4's guard constant `γ_G = e^{-6}/3`
(`homGuard_one_one`). For the data `d` of Definition `bpW:w6:sequences`:

* `W6StageCore d ν Π ω Ω P X`: the hypotheses of Lemma `bpW:w6:iter-lemma` at stage `ν`, except the
  reality of `P`: frequencies satisfying `(bpW:w5:freq)` on `Π` with `M_ω + M_Ω ≤ M_ν`, the conditions
  `(bpW:w6:melnikov)` at level `α_ν` on `Π` (W7 index, Dirichlet weight), a periodic family
  `P ∈ 𝒮_{p_+}(D_ν)` on `Π` with `|X_P|^{λ_ν}_{r_ν, D_ν} ≤ ε_ν`;
* `W6Stage`: the same with `P` real (all hypotheses of the lemma at stage `ν`);
* `W6Stage.stepHyp`: W5's step data `StepHypSrc` at stage `ν` (step `il-small`), with
  `s_ν, σ_ν, η_ν, r_ν, α_ν, λ_ν, ε_ν`;
* the objects of the step at stage `ν`: `Φ_{ν+1}` (`W6Stage.PhiN`), `ω_{ν+1}`, `Ω_{ν+1}`
  (`omN`, `OmN`), `P_{ν+1}`, `X_{P_{ν+1}}` (`PN`, `XN`), and `Π_{ν+1}` (`PiN`).
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

/-- W4's guard constant `γ_G = e^{-6}/3` for `a = p = 1` (`homGuard_one_one`). -/
def w6GamG : ℝ := Real.exp (-6) / 3

namespace W6SeqData

variable {d : W6SeqData}

theorem r_pos (hd : d.Valid) : ∀ ν, 0 < d.r ν
  | 0 => hd.r0_pos
  | ν + 1 => mul_pos (eta_pos hd ν) (r_pos hd ν)

theorem s_pos (hd : d.Valid) (ν : ℕ) : 0 < d.s ν := by
  have h := sInf_le_s hd ν
  unfold sInf at h
  have := hd.s0_pos
  linarith

theorem five_sigma_lt (hd : d.Valid) (ν : ℕ) : 5 * d.sigma ν < d.s ν := by
  have h1 := sigma_le_s_div_six hd ν
  have h2 := sigma_pos hd ν
  linarith

end W6SeqData

theorem HomFreqHyp.mono {Par Par' : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ Mω' : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hPar : Par' ⊆ Par) (hM : Mω ≤ Mω') : HomFreqHyp Par' ω Ω M0 Mω' MΩ where
  consts_nonneg := ⟨h.consts_nonneg.1, h.consts_nonneg.2.1.trans hM, h.consts_nonneg.2.2⟩
  tail ξ hξ j := h.tail ξ (hPar hξ) j
  lipOmega ξ hξ ζ hζ :=
    (h.lipOmega ξ (hPar hξ) ζ (hPar hζ)).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  lipTail ξ hξ ζ hζ j := h.lipTail ξ (hPar hξ) ζ (hPar hζ) j

theorem FamBound.mono_lam {Pa Pa' : Set (Fin 2 → ℝ)} {V V' : Set KamPhase} {r lam lam' ε ε' : ℝ}
    {X : (Fin 2 → ℝ) → KamPhase → KamPhase} (h : FamBound Pa V r lam ε X) (hPa : Pa' ⊆ Pa)
    (hV : V' ⊆ V) (hlam : lam' ≤ lam) (hε : ε ≤ ε') :
    FamBound Pa' V' r lam' ε' X := by
  obtain ⟨ε₀, ε₁, h0, h1, hs, hb, hl⟩ := h
  refine ⟨ε₀, ε₁, h0, h1, ?_, fun ξ hξ w hw => hb ξ (hPa hξ) w (hV hw),
    fun ξ hξ ζ hζ w hw => hl ξ (hPa hξ) ζ (hPa hζ) w (hV hw)⟩
  have : lam' * ε₁ ≤ lam * ε₁ := mul_le_mul_of_nonneg_right hlam h1
  linarith

/-- The hypotheses of Lemma `bpW:w6:iter-lemma` at stage `ν`, except the reality of `P`. -/
structure W6StageCore (d : W6SeqData) (ν : ℕ) (Pi : Set (Fin 2 → ℝ))
    (ω : (Fin 2 → ℝ) → Fin 2 → ℝ) (Ω : (Fin 2 → ℝ) → ℕ+ → ℝ) (P : (Fin 2 → ℝ) → KamPhase → ℂ)
    (X : (Fin 2 → ℝ) → KamPhase → KamPhase) : Prop where
  /-- `(bpW:w5:freq)` on `Π` with `M_ω + M_Ω ≤ M_ν` -/
  freq : ∃ T Mω MΩ : ℝ, HomFreqHyp Pi ω Ω T Mω MΩ ∧ Mω + MΩ ≤ d.M ν
  /-- `(bpW:w6:melnikov)` at level `α_ν` on `Π` -/
  mel : W6Mel (d.alpha ν) Pi ω (fun ξ => w6Om7 (Ω ξ))
  /-- `P ∈ 𝒮_{p_+}(D_ν)`, `p_+ = 3/2` -/
  smooth : ∀ ξ ∈ Pi, IsSmoothing (a := 1) (p := 1) (pb := 3 / 2) zero_le_one (by norm_num)
    (d.dom ν) (P ξ) (X ξ)
  /-- `P` is periodic -/
  per : ∀ ξ ∈ Pi, ∀ i, ∀ w ∈ d.dom ν, P ξ (w + stepTau i) = P ξ w
  /-- `|X_P|^{λ_ν}_{r_ν, D_ν} ≤ ε_ν` -/
  bound : FamBound Pi (d.dom ν) (d.r ν) (d.lam ν) (d.eps ν) X

/-- The hypotheses of Lemma `bpW:w6:iter-lemma` at stage `ν` (blueprint `bpW:w6:iter-lemma`). -/
structure W6Stage (d : W6SeqData) (ν : ℕ) (Pi : Set (Fin 2 → ℝ))
    (ω : (Fin 2 → ℝ) → Fin 2 → ℝ) (Ω : (Fin 2 → ℝ) → ℕ+ → ℝ) (P : (Fin 2 → ℝ) → KamPhase → ℂ)
    (X : (Fin 2 → ℝ) → KamPhase → KamPhase) : Prop
    extends W6StageCore d ν Pi ω Ω P X where
  /-- `P` is real -/
  real : ∀ ξ ∈ Pi, ∀ w ∈ d.dom ν, StepReal w → (P ξ w).im = 0

namespace W6Stage

variable {d : W6SeqData} {ν : ℕ} {Pi : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
  {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {P : (Fin 2 → ℝ) → KamPhase → ℂ}
  {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

/-- The tail constant `M₀` of `(bpW:w5:freq)` at stage `ν` (a choice). -/
def T (h : W6Stage d ν Pi ω Ω P X) : ℝ := h.freq.choose

/-- The constant `M_Ω` at stage `ν` (a choice); `M_ω` is replaced by `M_ν - M_Ω`. -/
def MO (h : W6Stage d ν Pi ω Ω P X) : ℝ := h.freq.choose_spec.choose_spec.choose

/-- The sup part `ε₀` of the bound `ε_ν` (a choice). -/
def e0 (h : W6Stage d ν Pi ω Ω P X) : ℝ := h.bound.choose

/-- The Lipschitz part `ε₁` of the bound `ε_ν` (a choice). -/
def e1 (h : W6Stage d ν Pi ω Ω P X) : ℝ := h.bound.choose_spec.choose

theorem freq_spec (h : W6Stage d ν Pi ω Ω P X) :
    HomFreqHyp Pi ω Ω h.T (d.M ν - h.MO) h.MO := by
  obtain ⟨hf, hle⟩ := h.freq.choose_spec.choose_spec.choose_spec
  exact hf.mono subset_rfl (by unfold MO; linarith)

theorem bound_spec (h : W6Stage d ν Pi ω Ω P X) :
    0 ≤ h.e0 ∧ 0 ≤ h.e1 ∧ h.e0 + d.lam ν * h.e1 ≤ d.eps ν ∧
      (∀ ξ ∈ Pi, ∀ w ∈ d.dom ν, kamNorm (d.r ν) (X ξ w) ≤ h.e0) ∧
      (∀ ξ ∈ Pi, ∀ ζ ∈ Pi, ∀ w ∈ d.dom ν,
        kamNorm (d.r ν) (X ξ w - X ζ w) ≤ h.e1 * ‖ξ - ζ‖) :=
  h.bound.choose_spec.choose_spec

/-- **W5's step applies at stage `ν`** (blueprint `bpW:w6:iter-lemma`, step `il-small`). -/
theorem stepHyp (hd : d.Valid) (hsmall : d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T)
    (h : W6Stage d ν Pi ω Ω P X) :
    StepHypSrc 1 1 (3 / 2) (d.s ν) (d.r ν) (d.sigma ν) (d.eta ν) w6Tau (d.alpha ν) (d.lam ν)
      (d.eps ν) h.e0 h.e1 w6GamG h.T (d.M ν - h.MO) h.MO Pi ω Ω P X := by
  obtain ⟨b0, b1, bs, bb, bl⟩ := h.bound_spec
  have hM := W6SeqData.M_pos hd ν
  exact
  { ha := zero_le_one
    hp := zero_le_one
    hpb := by norm_num
    hp1 := by norm_num
    hpp := by norm_num
    hG := homGuard_one_one
    hτ := by rw [w6Tau_eq]; norm_num
    hα := W6SeqData.alpha_pos hd ν
    hs := W6SeqData.s_pos hd ν
    hr := W6SeqData.r_pos hd ν
    hσ := W6SeqData.sigma_pos hd ν
    hσ1 := (W6SeqData.sigma_le_quarter hd ν).trans (by norm_num)
    hσs := W6SeqData.five_sigma_lt hd ν
    hη0 := W6SeqData.eta_pos hd ν
    hη := W6SeqData.eta_le hd hsmall ν
    freq := h.freq_spec
    hM := by rw [sub_add_cancel]; exact hM
    hlam0 := (W6SeqData.lam_pos hd ν).le
    hlam := by rw [sub_add_cancel]; exact le_rfl
    mel := by
      rw [w6Tau_eq]
      exact w6_homMelnikov_of_mel (W6SeqData.alpha_pos hd ν) h.mel
    hP := h.smooth
    hper := h.per
    hreal := h.real
    hε₀ := b0
    hεpos := W6SeqData.eps_pos hd ν
    hε₁ := b1
    hb := bb
    hdiff := bl
    hε := bs
    small := W6SeqData.eps_le_small hd hsmall ν }

theorem factRPos (hd : d.Valid) (ν : ℕ) : Fact (0 < d.r ν) := ⟨W6SeqData.r_pos hd ν⟩

/-- `ω_{ν+1}` (on `Π_ν`). -/
def omN (hd : d.Valid) (hsmall : d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T)
    (h : W6Stage d ν Pi ω Ω P X) : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  (h.stepHyp hd hsmall).hyp.core.omegaPlus

/-- `Ω_{ν+1}` (on `Π_ν`; W5 index). -/
def OmN (hd : d.Valid) (hsmall : d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T)
    (h : W6Stage d ν Pi ω Ω P X) : (Fin 2 → ℝ) → ℕ+ → ℝ :=
  (h.stepHyp hd hsmall).hyp.core.OmegaPlus

/-- `Φ_{ν+1}` (on `Π_ν`), a map of `𝒫` with the norm `|·|_{r_ν}`. -/
def PhiN (hd : d.Valid) (hsmall : d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T)
    (h : W6Stage d ν Pi ω Ω P X) (ξ : Fin 2 → ℝ) : StepPhase (d.r ν) → StepPhase (d.r ν) :=
  haveI := factRPos hd ν
  (h.stepHyp hd hsmall).hyp.core.Phi ξ

/-- `P_{ν+1}` (on `Π_ν`). -/
def PN (hd : d.Valid) (hsmall : d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T)
    (h : W6Stage d ν Pi ω Ω P X) : (Fin 2 → ℝ) → KamPhase → ℂ :=
  haveI := factRPos hd ν
  fun ξ w => (h.stepHyp hd hsmall).hyp.core.Pplus ξ (StepPhase.ofK (r := d.r ν) w)

/-- `X_{P_{ν+1}}` (on `Π_ν`). -/
def XN (hd : d.Valid) (hsmall : d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T)
    (h : W6Stage d ν Pi ω Ω P X) : (Fin 2 → ℝ) → KamPhase → KamPhase :=
  haveI := factRPos hd ν
  fun ξ w => StepPhase.toK ((h.stepHyp hd hsmall).hyp.core.Xplus ξ (StepPhase.ofK (r := d.r ν) w))

/-- `Π_{ν+1} = Π_ν ∖ ⋃_{(k,l) ∈ Z, |k| > K_ν} R^{ν+1}_{kl}`, the zones of `(ω_{ν+1}, Ω_{ν+1})` at
level `α_{ν+1}` on `Π_ν`. -/
def PiN (hd : d.Valid) (hsmall : d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T)
    (h : W6Stage d ν Pi ω Ω P X) : Set (Fin 2 → ℝ) :=
  Pi \ ⋃ (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) (_ : InZ k l ∧ d.K ν < kAbs k),
    zoneSet Pi (h.omN hd hsmall) (fun ξ => w6Om7 (h.OmN hd hsmall ξ)) (d.alpha (ν + 1)) k l

theorem PiN_subset (hd : d.Valid) (hsmall : d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T)
    (h : W6Stage d ν Pi ω Ω P X) : h.PiN hd hsmall ⊆ Pi := Set.sdiff_subset

end W6Stage

end KAM.Wave
