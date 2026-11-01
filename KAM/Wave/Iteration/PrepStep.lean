/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.PrepMel
public import KAM.Wave.Iteration.IterLemma
public import KAM.Wave.Iteration.WaveData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the preparatory step (`bpW:w6:prep-step`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:prep-step` (milestone W6).

`W6PrepHyp m hm Π α r ε P X`: the hypotheses of Lemma `bpW:w6:prep-step` (`Π ⊆ {|ξ|_∞ ≤ 1/2}`
Borel, `0 < α ≤ α₀`, `r > 0`, a real periodic `P ∈ 𝒮_{p+1}(D(s, r))` on `Π ∖ Ξ`,
`0 < ε ≤ γα`, `|X_P|^λ_{r, D(s,r)} ≤ ε`, `λ = α/M`, `s = 1/8`). Then:

* `W6PrepHyp.prepStepHyp`: W5's step in the modified case applies on `Π ∖ Ξ` (`β = 1/4`,
  `p_+ = 3/2`, level `α̂`, `σ_P`, `η_P`), steps `p-data`, `p-div`; the objects `Φ_P`, `(ω_0, Ω_0)`,
  `P_0` are `W6PrepHyp.{PhiP, om0, Om0, P0, X0}`;
* (i): `w6_homMelnikovMod_of_prep`, `w6_prep_divisors` (module `PrepMel`);
* (ii): `W6PrepHyp.shift_omega`, `W6PrepHyp.shift_Omega`, `W6PrepHyp.freq0`;
* (iii): `W6PrepHyp.phiP_bounds`; (iv), (v): `W6PrepHyp.size`.

Deviations (W5 interface): (ii) is obtained with the weight `J^{1/2}` (W5's `stepTheoremMod` (iii)
gives `(j+2)^{p_+-p}`), not `J`; (iii) with `2M_{F,P}` (W5's clause (v)), not `M_{F,P}`. The
reality of `Φ_P`, `P_0` is W5's reality clause (not in this base).
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

section

variable (m : ℝ) (hm : 0 < m)

/-- `B = (1/2)(1/λ₁ + 1/λ₂)` bounds `|⟨b, ξ⟩|` on `{|ξ|_∞ ≤ 1/2}`. -/
def w6BB : ℝ := 1 / 2 * (1 / lam m hm 1 + 1 / lam m hm 2)

theorem w6BB_nonneg : 0 ≤ w6BB m hm := by
  unfold w6BB; have := lam_pnat_pos hm 1; have := lam_pnat_pos hm 2; positivity

theorem w6_abs_waveB_le {ξ : Fin 2 → ℝ} (hξ : ‖ξ‖ ≤ 1 / 2) : |waveB m hm ξ| ≤ w6BB m hm := by
  unfold waveB w6BB
  rw [Fin.sum_univ_two]
  have h1 := lam_pnat_pos hm 1
  have h2 := lam_pnat_pos hm 2
  have e0 : |ξ 0| ≤ 1 / 2 := by
    have := norm_le_pi_norm ξ 0; rw [Real.norm_eq_abs] at this; linarith
  have e1 : |ξ 1| ≤ 1 / 2 := by
    have := norm_le_pi_norm ξ 1; rw [Real.norm_eq_abs] at this; linarith
  have a0 : ((0 : Fin 2) : ℕ).succPNat = 1 := rfl
  have a1 : ((1 : Fin 2) : ℕ).succPNat = 2 := rfl
  rw [a0, a1]
  calc |ξ 0 / lam m hm 1 + ξ 1 / lam m hm 2| ≤ |ξ 0| / lam m hm 1 + |ξ 1| / lam m hm 2 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_div, abs_div, abs_of_pos h1, abs_of_pos h2]
    _ ≤ 1 / 2 / lam m hm 1 + 1 / 2 / lam m hm 2 := by gcongr
    _ = _ := by ring

end

/-- The hypotheses of Lemma `bpW:w6:prep-step` (`s = 1/8`, `λ = α/M`). -/
structure W6PrepHyp (m : ℝ) (hm : 0 < m) (Pi : Set (Fin 2 → ℝ)) (α r ε : ℝ)
    (P : (Fin 2 → ℝ) → KamPhase → ℂ) (X : (Fin 2 → ℝ) → KamPhase → KamPhase) : Prop where
  meas : MeasurableSet Pi
  sub : ∀ ξ ∈ Pi, ‖ξ‖ ≤ 1 / 2
  hα : 0 < α
  hα0 : α ≤ measAlpha0 m hm
  hr : 0 < r
  /-- `P ∈ 𝒮_{p+1}(D(s, r))` on `Π ∖ Ξ` -/
  smooth : ∀ ξ ∈ Pi \ prepSet m hm Pi α, IsSmoothing (a := 1) (p := 1) (pb := 1 + 1) zero_le_one
    (by norm_num) (kamDomain w6S r) (P ξ) (X ξ)
  per : ∀ ξ ∈ Pi \ prepSet m hm Pi α, ∀ i, ∀ w ∈ kamDomain w6S r, P ξ (w + stepTau i) = P ξ w
  real : ∀ ξ ∈ Pi \ prepSet m hm Pi α, ∀ w ∈ kamDomain w6S r, StepReal w → (P ξ w).im = 0
  hε : 0 < ε
  hεγ : ε ≤ w6Gamma m hm * α
  bound : FamBound (Pi \ prepSet m hm Pi α) (kamDomain w6S r) r (α / w6M m hm) ε X

namespace W6PrepHyp

variable {m : ℝ} {hm : 0 < m} {Pi : Set (Fin 2 → ℝ)} {α r ε : ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

/-- The sup part of `ε` (a choice). -/
def w6PrepE0 (H : W6PrepHyp m hm Pi α r ε P X) : ℝ := H.bound.choose

/-- The Lipschitz part of `ε` (a choice). -/
def w6PrepE1 (H : W6PrepHyp m hm Pi α r ε P X) : ℝ := H.bound.choose_spec.choose

/-- `M₀` of `(bpW:w5:freq)` for the wave frequencies on `Π`. -/
def w6PrepTail (m : ℝ) (hm : 0 < m) : ℝ := m / 2 + 3 / (2 * π) * w6BB m hm

/-- **W5's step applies in the modified case** (blueprint `bpW:w6:prep-step`, steps `p-data`,
`p-div`): on `Π ∖ Ξ` with `s = 1/8`, `σ_P`, `η_P`, level `α̂`, `β = 1/4`, `p_+ = 3/2`. -/
theorem prepStepHyp (H : W6PrepHyp m hm Pi α r ε P X) :
    StepHypModSrc 1 1 (3 / 2) w6S r w6SigmaP (w6EtaP α ε) w6Tau (alphaHat α) (1 / 4)
      (α / w6M m hm) ε H.w6PrepE0 H.w6PrepE1 w6GamG (w6PrepTail m hm) (waveMomega m hm)
      (waveMOmega m hm)
      (Pi \ prepSet m hm Pi α) (waveFreqTan m hm) (waveFreqNor m hm) P X := by
  obtain ⟨b0, b1, bs, bb, bl⟩ := H.bound.choose_spec.choose_spec
  have hM := w6M_pos m hm
  exact
  { ha := zero_le_one
    hp := zero_le_one
    hpb := by norm_num
    hp1 := by norm_num
    hpp := by norm_num
    hG := homGuard_one_one
    hτ := by rw [w6Tau_eq]; norm_num
    hα := alphaHat_pos H.hα
    hs := by unfold w6S; norm_num
    hr := H.hr
    hσ := w6SigmaP_pos
    hσ1 := by rw [w6SigmaP_val]; norm_num
    hσs := by rw [w6SigmaP_val]; unfold w6S; norm_num
    hη0 := w6EtaP_pos H.hα H.hε
    hη := w6EtaP_le H.hα H.hα0 H.hε H.hεγ
    freq := homFreqHyp_wave m hm _ (w6BB_nonneg m hm) fun ξ hξ =>
      w6_abs_waveB_le m hm (H.sub ξ hξ.1)
    hM := hM
    hlam0 := (div_pos H.hα hM).le
    hlam := w6prep_lam_le H.hα H.hα0
    hβ0 := by norm_num
    h2β := by norm_num
    mel := by rw [w6Tau_eq]; exact w6_homMelnikovMod_of_prep m hm H.hα
    hP := H.smooth
    hper := H.per
    hreal := H.real
    hε₀ := b0
    hεpos := H.hε
    hε₁ := b1
    hb := bb
    hdiff := bl
    hε := bs
    small := w6prep_small H.hα H.hα0 H.hε H.hεγ }

theorem factR (H : W6PrepHyp m hm Pi α r ε P X) : Fact (0 < r) := ⟨H.hr⟩

/-- `ω_0 = ω⁰ + ω̂_P` on `Π ∖ Ξ`. -/
def om0 (H : W6PrepHyp m hm Pi α r ε P X) : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  H.prepStepHyp.hyp.core.omegaPlus

/-- `Ω_0 = Ω⁰ + Ω̂_P` on `Π ∖ Ξ` (W5 index). -/
def Om0 (H : W6PrepHyp m hm Pi α r ε P X) : (Fin 2 → ℝ) → ℕ+ → ℝ :=
  H.prepStepHyp.hyp.core.OmegaPlus

/-- `Φ_P` (norm `|·|_r`). -/
def PhiP (H : W6PrepHyp m hm Pi α r ε P X) (ξ : Fin 2 → ℝ) : StepPhase r → StepPhase r :=
  haveI := H.factR
  H.prepStepHyp.hyp.core.Phi ξ

/-- `P_0`. -/
def w6P0 (H : W6PrepHyp m hm Pi α r ε P X) : (Fin 2 → ℝ) → KamPhase → ℂ :=
  haveI := H.factR
  fun ξ w => H.prepStepHyp.hyp.core.Pplus ξ (StepPhase.ofK (r := r) w)

/-- `X_{P_0}`. -/
def X0 (H : W6PrepHyp m hm Pi α r ε P X) : (Fin 2 → ℝ) → KamPhase → KamPhase :=
  haveI := H.factR
  fun ξ w => StepPhase.toK (H.prepStepHyp.hyp.core.Xplus ξ (StepPhase.ofK (r := r) w))

/-- **(ii), `ω`** (`bpW:w6:prep-step` (ii)): `|ω̂_P| + λ |ω̂_P|^ℒ ≤ 6πε` on `Π ∖ Ξ`. -/
theorem shift_omega (H : W6PrepHyp m hm Pi α r ε P X) :
    ∃ b₀ b₁ : ℝ, 0 ≤ b₀ ∧ 0 ≤ b₁ ∧ b₀ + α / w6M m hm * b₁ ≤ 6 * π * ε ∧
      (∀ ξ ∈ Pi \ prepSet m hm Pi α, ‖H.om0 ξ - omegaTan m hm ξ‖ ≤ b₀) ∧
      ∀ ξ ∈ Pi \ prepSet m hm Pi α, ∀ ζ ∈ Pi \ prepSet m hm Pi α,
        ‖(H.om0 ξ - omegaTan m hm ξ) - (H.om0 ζ - omegaTan m hm ζ)‖ ≤ b₁ * ‖ξ - ζ‖ := by
  have := H.factR
  exact (stepTheoremMod H.prepStepHyp).2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **(ii), `Ω`** (`bpW:w6:prep-step` (ii), with the weight `J^{1/2}`; W7 index, `J = j + 3`):
`J^{1/2} (|Ω̂_{P,J}| + λ |Ω̂_{P,J}|^ℒ) ≤ 3ε` on `Π ∖ Ξ`. -/
theorem shift_Omega (H : W6PrepHyp m hm Pi α r ε P X) :
    ∃ c₀ c₁ : ℝ, 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ c₀ + α / w6M m hm * c₁ ≤ 3 * ε ∧
      (∀ ξ ∈ Pi \ prepSet m hm Pi α, ∀ n : ℕ,
        normLab n ^ (1 / 2 : ℝ) * |w6Om7 (H.Om0 ξ) n - omegaNor m hm ξ n| ≤ c₀) ∧
      ∀ ξ ∈ Pi \ prepSet m hm Pi α, ∀ ζ ∈ Pi \ prepSet m hm Pi α, ∀ n : ℕ,
        normLab n ^ (1 / 2 : ℝ) * |(w6Om7 (H.Om0 ξ) n - omegaNor m hm ξ n) -
          (w6Om7 (H.Om0 ζ) n - omegaNor m hm ζ n)| ≤ c₁ * ‖ξ - ζ‖ := by
  have := H.factR
  obtain ⟨c₀, c₁, h0, h1, hs, hb, hl⟩ :=
    (stepTheoremMod H.prepStepHyp).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have e : ((3 / 2 : ℝ) - 1) = 1 / 2 := by norm_num
  have hN : ∀ ξ n, omegaNor m hm ξ n = waveFreqNor m hm ξ n.succPNat := fun ξ n => by
    rw [waveFreqNor_eq_omegaNor, Nat.natPred_succPNat]
  refine ⟨c₀, c₁, h0, h1, hs, fun ξ hξ n => ?_, fun ξ hξ ζ hζ n => ?_⟩
  · have := hb ξ hξ n.succPNat
    rw [e, ← W6Stage.normLab_eq_succPNat] at this
    rw [hN]; exact this
  · have := hl ξ hξ ζ hζ n.succPNat
    rw [e, ← W6Stage.normLab_eq_succPNat] at this
    rw [hN, hN]; exact this

/-- **(ii), frequency hypotheses** (`bpW:w6:prep-step` (ii)): `(ω_0, Ω_0)` satisfy
`(bpW:w5:freq)` on `Π ∖ Ξ` with `M_ω + M_Ω ≤ M_0 = 2M`. -/
theorem freq0 (H : W6PrepHyp m hm Pi α r ε P X) :
    ∃ T' Mω MΩ : ℝ, HomFreqHyp (Pi \ prepSet m hm Pi α) H.om0 H.Om0 T' Mω MΩ ∧
      Mω + MΩ ≤ w6M0 m hm := by
  have := H.factR
  have hl : 0 < α / w6M m hm := div_pos H.hα (w6M_pos m hm)
  have h := (stepTheoremMod H.prepStepHyp).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hl
  refine ⟨_, _, _, h, ?_⟩
  obtain ⟨h1, h2⟩ := w6prep_lip_growth (m := m) (hm := hm) H.hα H.hε.le H.hεγ
  have e : waveMomega m hm + 6 * π * ε / (α / w6M m hm) + (waveMOmega m hm + 3 * ε /
      (α / w6M m hm)) = w6M m hm + (6 * π + 3) * ε / (α / w6M m hm) := by
    unfold w6M; ring
  rw [e]
  unfold w6M0
  linarith

/-- **(iii)** (`bpW:w6:prep-step` (iii), with `2M_{F,P}`): `|Φ_P - id| ≤ A₀`, `Φ_P - id` is
`A₁`-Lipschitz in `ξ` (norm `|·|_r`), `A₀ + λ A₁ ≤ 2 M_{F,P}`, on `D_0 = D(s_0, η_P r)`. -/
theorem phiP_bounds (H : W6PrepHyp m hm Pi α r ε P X) :
    ∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ A₀ + α / w6M m hm * A₁ ≤ 2 * w6MFP α ε ∧
      ∀ ξ ∈ Pi \ prepSet m hm Pi α, ∀ ζ ∈ Pi \ prepSet m hm Pi α,
        ∀ w ∈ stepDomain r w6S0 (w6EtaP α ε * r),
        haveI := H.factR
        ‖H.PhiP ξ w - w‖ ≤ A₀ ∧
        ‖(H.PhiP ξ w - w) - (H.PhiP ζ w - w)‖ ≤ A₁ * ‖ξ - ζ‖ := by
  have := H.factR
  obtain ⟨A₀, A₁, B₀, B₁, a0, a1, -, -, ha, -, hall⟩ :=
    (stepTheoremMod H.prepStepHyp).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact ⟨A₀, A₁, a0, a1, ha, fun ξ hξ ζ hζ w hw =>
    ⟨(hall ξ hξ ζ hζ w hw).1, (hall ξ hξ ζ hζ w hw).2.1⟩⟩

/-- **(iv), (v)** (`bpW:w6:prep-step` (iv), (v)): `P_0 ∈ 𝒮_{p_+}(D_0)`, periodic, and
`|X_{P_0}|^{λ_0}_{r_0, D_0} ≤ ε^♭_0 = 2C^♮_2 ε^{4/3}(α̂σ_P^{t^♮})^{-1/3} ≤ γ₁ α̌`
(`λ_0 = α̌/M_0`, `r_0 = η_P r`, `D_0 = D(s_0, r_0)`); the same with `λ = α/M`. -/
theorem w6size (H : W6PrepHyp m hm Pi α r ε P X) :
    (∀ ξ ∈ Pi \ prepSet m hm Pi α, IsSmoothing (a := 1) (p := 1) (pb := 3 / 2) zero_le_one
      (by norm_num) (kamDomain w6S0 (w6EtaP α ε * r)) (H.w6P0 ξ) (H.X0 ξ)) ∧
    (∀ ξ ∈ Pi \ prepSet m hm Pi α, ∀ i, ∀ w ∈ kamDomain w6S0 (w6EtaP α ε * r),
      H.w6P0 ξ (w + stepTau i) = H.w6P0 ξ w) ∧
    FamBound (Pi \ prepSet m hm Pi α) (kamDomain w6S0 (w6EtaP α ε * r)) (w6EtaP α ε * r)
      (α / w6M m hm) (w6EpsFlat α ε) H.X0 ∧
    FamBound (Pi \ prepSet m hm Pi α) (kamDomain w6S0 (w6EtaP α ε * r)) (w6EtaP α ε * r)
      (alphaCheck α / w6M0 m hm) (w6EpsFlat α ε) H.X0 ∧
    w6EpsFlat α ε ≤ w6Gamma1 m hm * alphaCheck α := by
  have := H.factR
  obtain ⟨-, -, -, -, -, -, -, -, c6, c7, -, c8, -⟩ := stepTheoremMod H.prepStepHyp
  have hle := w6EpsFlat_le (m := m) (hm := hm) H.hα H.hε.le H.hεγ
  -- `C^♮_2 (ε²/(α̂ σ_P^{t^♮} η_P²) + η_P ε) = 2 C^♮_2 ε η_P = ε^♭_0`
  have hq := w6QP_pos H.hα H.hε
  have hη3 : w6EtaP α ε ^ 3 = w6QP α ε := by
    unfold w6EtaP; rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]; norm_num
  have hB : 0 < alphaHat α * w6SigmaP ^ w6Tn :=
    mul_pos (alphaHat_pos H.hα) (w6SigmaP_rpow_pos _)
  have hη := w6EtaP_pos H.hα H.hε
  set η := w6EtaP α ε with hηdef
  set B := alphaHat α * w6SigmaP ^ w6Tn with hBdef
  have hε' : ε = η ^ 3 * B := by
    rw [hη3]; unfold w6QP; rw [div_mul_cancel₀ _ hB.ne']
  have heq : stepC2n w6Tau * (ε ^ 2 / (alphaHat α * w6SigmaP ^ stepTn w6Tau *
      η ^ 2) + η * ε) = w6EpsFlat α ε := by
    rw [w6EpsFlat_eq H.hα H.hε]
    have e2 : ε ^ 2 / (alphaHat α * w6SigmaP ^ stepTn w6Tau * η ^ 2) = η * ε := by
      change ε ^ 2 / (B * η ^ 2) = _
      rw [hε']
      field_simp
    rw [e2, ← hηdef]
    unfold w6C2n
    ring
  have hfb : FamBound (Pi \ prepSet m hm Pi α) (kamDomain w6S0 (w6EtaP α ε * r))
      (w6EtaP α ε * r) (α / w6M m hm) (w6EpsFlat α ε) H.X0 := heq ▸ c8
  refine ⟨c6, c7, hfb, hfb.mono_lam subset_rfl subset_rfl (w6lam0_le_lam H.hα H.hα0) le_rfl, hle⟩

end W6PrepHyp

end KAM.Wave
