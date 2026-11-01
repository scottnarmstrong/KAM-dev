/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.ShellInit
public import KAM.Wave.Iteration.ConvSource
public import KAM.Wave.Iteration.ToriPrep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W8: the KAM iteration on one shell (blueprint `bpW:w8:sharp-prep`, `bpW:w8:shell-iter`,
`bpW:w8:w6-general`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint labels `bpW:w8:sharp-prep`, `bpW:w8:shell-iter`, `bpW:w8:w6-general`
(milestone W8).

Model. Shell `n` runs Lemma `bpW:w6:prep-step` with the data of `bpW:w8:shell-data` (iv)
(`Π = Π_n`, `α = α_n`, `r = r_n`, `ε = ε^♯_n`) for the perturbation `P` (field `X`) of
Proposition `bpW:w5:initial`. The results below are stated for any `H : W8ShellPrep m hm n P X`
(the hypotheses of that lemma for shell `n`); `w8ShellPrep_of_initial` builds `H` from the
conclusion of `bpW:w5:initial`. The starting size is `ε_{0,n} = κ_n^{4/3} γ₁ α̌_n` (`w8Eps0W`).

* `w8_epsFlat_shell`, `w8_sharpPrep` (`bpW:w8:sharp-prep`): `η_P = (ε^♯_n/(α̂_n σ_P^{53}))^{1/3}`,
  `|X_{P_0}|^{λ_0}_{r_0, D_0} ≤ ε^♭_{0,n} = 2C^♮_2 (ε^♯_n)^{4/3} (α̂_n σ_P^{53})^{-1/3}`
  (`λ_0 = α̌_n/(2M)`), `0 < ε^♭_{0,n} ≤ ε_{0,n} ≤ γ₁ α̌_n`;
* shell-iteration objects (`bpW:w8:shell-iter`): `w8ShellSeqData`, `w8ShellStart`,
  `w8ShellGamma` (`Γ_n = Π^{(n)}_*`), `w8ShellOmega` (`ω^{(n)}_*`), `w8ShellNu`
  (`ν^{(n)}_* = ω^{(n)}_*/2π`), `w8ShellFamily` (the admissible family), `w8ShellExcl`
  (`ℰ^{(n)}`), `w8ShellEtor` (`e^{(n)}_tor`, formula `w8ShellEtor_eq`), `w8ShellEpsOm`
  (`ε^{(n)}_ω`), `w8ShellTorusKam` (`Φ^{(n)}_P ∘ Φ^{(n)}_*`, the torus in KAM coordinates; the
  torus `Ψ̃^{(n)}_ξ = 𝒜_ξ ∘ Φ^{(n)}_P ∘ Φ^{(n)}_*` needs W5's `bpW:w5:action-angle`, not here);
* `w8_w6General` (`bpW:w8:w6-general`): Lemmas `bpW:w6:applicable`, `bpW:w6:freq-lip`,
  `bpW:w6:exclusion`, `bpW:w6:final-freq` for the shell iteration; the W6 part of Theorem
  `bpW:w6:tori` with `e_tor = e^{(n)}_tor` is the conditional helper
  `w8ShellToriKam_of_stepSmooth` (named W5 dependencies `W6StepSmooth`, `W6StepSmoothMod`).

Deviation (inherited from W6-ITER D4): in `bpW:w6:freq-lip` the constants are `ε₁ = 0`,
`ε₂ = 3γα_n + 4ε_{0,n}` (blueprint `ε₁ = 3γα_n`, `ε₂ = 4ε_{0,n}`); W7's estimates hold for every
admissible family.
-/

@[expose] public noncomputable section

open Set Real

namespace KAM.Wave

/-- `ε_{0,n} = κ_n^{4/3} γ₁ α̌_n` for the W5–W6 constants (blueprint `bpW:w8:shells`). -/
abbrev w8Eps0W (m : ℝ) (hm : 0 < m) (n : ℕ) : ℝ :=
  w8eps0 m hm (w8Upstream m hm) (w8T0W m hm) n

section

variable {m : ℝ} (hm : 0 < m)

local notation "𝔱" => w8T0W m hm

/-- The data of Lemma `bpW:w7:measure` for shell `n` (`Π_n` Borel in `{|ξ| ≤ 1/2}`,
`0 < α_n ≤ α₀`). -/
theorem w8MeasSetup (n : ℕ) : MeasSetup m hm (w8Pi 𝔱 n) (w8alpha 𝔱 n) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := w8_shellData_prep hm n
  exact ⟨h1, h2, h3, h4⟩

/-- **Comparison** (blueprint `bpW:w8:sharp-prep`, Step `stepW:w8:sp-cmp`):
`0 < ε^♭_{0,n} ≤ ε_{0,n} ≤ γ₁ α̌_n`. -/
theorem w8_epsFlat_shell (n : ℕ) :
    0 < w6EpsFlat (w8alpha 𝔱 n) (w8epsSharp m hm 𝔱 n) ∧
      w6EpsFlat (w8alpha 𝔱 n) (w8epsSharp m hm 𝔱 n) ≤ w8Eps0W m hm n ∧
      w8Eps0W m hm n ≤ w6Gamma1 m hm * alphaCheck (w8alpha 𝔱 n) := by
  set u := w8Upstream m hm
  obtain ⟨-, -, hα, -, -, hε, -, -⟩ := w8_shellData_prep hm n
  obtain ⟨hκ1, -⟩ := w8kappa_le hm u n
  set α := w8alpha 𝔱 n
  set ε := w8epsSharp m hm 𝔱 n
  set κ := w8kappa m hm u 𝔱 n with hκdef
  have hγ := w6Gamma_pos m hm
  have hγ1 := w6Gamma1_pos m hm
  have hκ0 : 0 < κ := by
    rw [hκdef, w8kappa]; exact div_pos hε (mul_pos u.gam_pos hα)
  have hc : 0 < alphaCheck α := Real.rpow_pos_of_pos hα _
  have hκ43 : κ ^ (4 / 3 : ℝ) ≤ 1 := Real.rpow_le_one hκ0.le hκ1 (by norm_num)
  have hκ43p : 0 ≤ κ ^ (4 / 3 : ℝ) := Real.rpow_nonneg hκ0.le _
  have heps0 : w8Eps0W m hm n = κ ^ (4 / 3 : ℝ) * w6Gamma1 m hm * alphaCheck α := rfl
  refine ⟨w6EpsFlat_pos hα hε, ?_, ?_⟩
  · have hdiv := w6EpsFlat_div hα hε.le
    have hεα : ε / α = κ * w6Gamma m hm := by
      rw [hκdef, w8kappa]
      show ε / α = ε / (w6Gamma m hm * α) * w6Gamma m hm
      field_simp
    rw [hεα, Real.mul_rpow hκ0.le hγ.le] at hdiv
    have hs := Real.rpow_pos_of_pos w6SigmaP_pos (w6Tn / 3)
    have es : w6SigmaP ^ (-(w6Tn / 3)) = (w6SigmaP ^ (w6Tn / 3))⁻¹ :=
      Real.rpow_neg w6SigmaP_pos.le _
    have harith := w6prep_size_arith m hm
    have hflat : w6EpsFlat α ε = alphaCheck α * κ ^ (4 / 3 : ℝ) *
        (2 * w6C2n * w6Gamma m hm ^ (4 / 3 : ℝ) / w6SigmaP ^ (w6Tn / 3)) := by
      rw [div_eq_iff hc.ne'] at hdiv
      rw [hdiv, es]
      ring
    rw [hflat, heps0]
    have : alphaCheck α * κ ^ (4 / 3 : ℝ) * (2 * w6C2n * w6Gamma m hm ^ (4 / 3 : ℝ) /
        w6SigmaP ^ (w6Tn / 3)) ≤ alphaCheck α * κ ^ (4 / 3 : ℝ) * w6Gamma1 m hm :=
      mul_le_mul_of_nonneg_left harith (by positivity)
    linarith
  · rw [heps0]
    have : κ ^ (4 / 3 : ℝ) * (w6Gamma1 m hm * alphaCheck α) ≤ 1 * (w6Gamma1 m hm * alphaCheck α) :=
      mul_le_mul_of_nonneg_right hκ43 (by positivity)
    linarith

end

/-! ### The shell iteration (`bpW:w8:shell-iter`) -/

section Defs

variable {m : ℝ} {hm : 0 < m} {n : ℕ} {P : (Fin 2 → ℝ) → KamPhase → ℂ}
  {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

/-- The sequence data of the shell iteration: Definition `bpW:w6:wave-iteration` for shell `n`
with the starting size `ε_{0,n}` (`r_0 = η_P r_n`, `α_0^{it} = α̌_n`, `M_0 = 2M`). -/
def w8ShellSeqData (m : ℝ) (hm : 0 < m) (n : ℕ) : W6SeqData :=
  w6WaveSeq m hm (w8alpha (w8T0W m hm) n) (w8rn (w8T0W m hm) n) (w8epsSharp m hm (w8T0W m hm) n)
    (w8Eps0W m hm n)

/-- The starting state of the shell iteration (`Π_{-1} = Π_n ∖ Ξ`, `(ω_0, Ω_0)`, `P_0`). -/
def w8ShellStart (H : W8ShellPrep m hm n P X) : W6State :=
  w6Start (w8ShellSeqData m hm n) (w8Pi (w8T0W m hm) n \
    prepSet m hm (w8Pi (w8T0W m hm) n) (w8alpha (w8T0W m hm) n)) H.om0 H.Om0 H.w6P0 H.X0

/-- `Γ_n = Π^{(n)}_*` (blueprint `bpW:w8:shell-iter`). -/
def w8ShellGamma (H : W8ShellPrep m hm n P X) : Set (Fin 2 → ℝ) := H.wavePiStar (w8Eps0W m hm n)

/-- `ω^{(n)}_*` (blueprint `bpW:w8:shell-iter`). -/
def w8ShellOmega (H : W8ShellPrep m hm n P X) (ξ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  w6OmStar (w8ShellSeqData m hm n) (w8ShellStart H) ξ

/-- `ν^{(n)}_* = ω^{(n)}_*/(2π)` (blueprint `bpW:w8:shell-iter`). -/
def w8ShellNu (H : W8ShellPrep m hm n P X) (ξ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (2 * π)⁻¹ • w8ShellOmega H ξ

/-- The admissible family `(D^{(n)}_μ, ω^{(n)}_μ, Ω^{(n)}_μ, K_μ)` of the shell iteration
(blueprint `bpW:w8:shell-iter`, Lemma `bpW:w6:freq-lip`). -/
def w8ShellFamily (H : W8ShellPrep m hm n P X) :
    AdmissibleFamily m hm (w8Pi (w8T0W m hm) n) (w8alpha (w8T0W m hm) n) :=
  H.w6WaveFamily (w8MeasSetup hm n) (w8_epsFlat_shell hm n).2.1 (w8_epsFlat_shell hm n).2.2

/-- The excluded set `ℰ^{(n)}` of the shell iteration (blueprint `bpW:w8:shell-iter`). -/
def w8ShellExcl (H : W8ShellPrep m hm n P X) : Set (Fin 2 → ℝ) :=
  exclSet m hm (w8ShellFamily H)

/-- `e^{(n)}_tor = c^♮_F ε^♯_n/(α̂_n σ_P^{52}) + 5 c_F ε_{0,n}/(α̌_n σ_0^{51})`
(blueprint `bpW:w8:shell-iter`; formula `w8ShellEtor_eq`). -/
def w8ShellEtor (m : ℝ) (hm : 0 < m) (n : ℕ) : ℝ :=
  w6Etor m hm (w8alpha (w8T0W m hm) n) (w8rn (w8T0W m hm) n) (w8epsSharp m hm (w8T0W m hm) n)
    (w8Eps0W m hm n)

/-- `ε^{(n)}_ω = 6πγα_n + 8πε_{0,n}` (blueprint `bpW:w8:shell-iter`). -/
def w8ShellEpsOm (m : ℝ) (hm : 0 < m) (n : ℕ) : ℝ :=
  6 * π * w6Gamma m hm * w8alpha (w8T0W m hm) n + 8 * π * w8Eps0W m hm n

/-- The torus of shell `n` in KAM coordinates, `θ ↦ Φ^{(n)}_P(Φ^{(n)}_*(θ))` (blueprint
`bpW:w8:shell-iter`, `bpW:w6:tori`; `Ψ̃^{(n)}_ξ = 𝒜_ξ ∘ w8ShellTorusKam H · ξ`). -/
def w8ShellTorusKam (H : W8ShellPrep m hm n P X) (θ : Fin 2 → ℂ) (ξ : Fin 2 → ℝ) : KamPhase :=
  H.w6TorusKam (w8Eps0W m hm n) θ ξ

theorem w8ShellGamma_eq (H : W8ShellPrep m hm n P X) :
    w8ShellGamma H = w6PiStarIt (w8ShellSeqData m hm n) (w8ShellStart H) := rfl

/-- The formula of `e^{(n)}_tor` (blueprint `bpW:w8:shell-iter`). -/
theorem w8ShellEtor_eq (m : ℝ) (hm : 0 < m) (n : ℕ) :
    w8ShellEtor m hm n =
      w6CFn * w8epsSharp m hm (w8T0W m hm) n / (w8alphaHat (w8T0W m hm) n * w6SigmaP ^ 52) +
        5 * (w6CF * w8Eps0W m hm n / (alphaCheck (w8alpha (w8T0W m hm) n) * w6Sigma0 ^ 51)) := by
  have e1 : w6SigmaP ^ (w6Tn - 1) = w6SigmaP ^ (52 : ℕ) := by
    rw [w6Tn_eq, ← Real.rpow_natCast]; norm_num
  have e2 : (w8ShellSeqData m hm n).sigma 0 ^ (w6T - 1) = w6Sigma0 ^ (51 : ℕ) := by
    rw [w8ShellSeqData, w6WaveSeq_sigma_zero, w6T_eq, ← Real.rpow_natCast]; norm_num
  unfold w8ShellEtor w6Etor w6MFP W6SeqData.ePhi stepMF
  rw [e1]
  change _ + 5 * (w6CF * w8Eps0W m hm n / (alphaCheck (w8alpha (w8T0W m hm) n) *
    (w8ShellSeqData m hm n).sigma 0 ^ (w6T - 1))) = _
  rw [e2]
  rfl

end Defs

/-! ### Sharp size (`bpW:w8:sharp-prep`) and W6 on one shell (`bpW:w8:w6-general`) -/

section Labels

variable {m : ℝ} {hm : 0 < m} {n : ℕ} {P : (Fin 2 → ℝ) → KamPhase → ℂ}
  {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

local notation "𝔱" => w8T0W m hm
local notation "𝔞" => w8alpha (w8T0W m hm) n
local notation "𝔢" => w8epsSharp m hm (w8T0W m hm) n
local notation "𝔯" => w8rn (w8T0W m hm) n
local notation "𝔓" => w8Pi (w8T0W m hm) n \ prepSet m hm (w8Pi (w8T0W m hm) n)
  (w8alpha (w8T0W m hm) n)

/-- **Sharp size after the preparatory step** (blueprint `bpW:w8:sharp-prep`): running Lemma
`bpW:w6:prep-step` with the data of `bpW:w8:shell-data` (iv), `η_P = (ε^♯_n/(α̂_n σ_P^{53}))^{1/3}`
and, with `λ_0 = α̌_n/(2M)`, `r_0 = η_P r_n`, `D_0 = D(s_0, r_0)`:
`|X_{P_0}|^{λ_0}_{r_0, D_0} ≤ ε^♭_{0,n} = 2C^♮_2 (ε^♯_n)^{4/3} (α̂_n σ_P^{53})^{-1/3}`,
`ε^♭_{0,n} ≤ ε_{0,n} ≤ γ₁ α̌_n`, and `ε^♭_{0,n} > 0`. -/
theorem w8_sharpPrep (H : W8ShellPrep m hm n P X) :
    w6EtaP 𝔞 𝔢 = (𝔢 / (w8alphaHat 𝔱 n * w6SigmaP ^ (53 : ℝ))) ^ (1 / 3 : ℝ) ∧
      w6EpsFlat 𝔞 𝔢 = 2 * w6C2n * 𝔢 ^ (4 / 3 : ℝ) *
        (w8alphaHat 𝔱 n * w6SigmaP ^ (53 : ℝ)) ^ (-(1 / 3 : ℝ)) ∧
      FamBound 𝔓 (kamDomain w6S0 (w6EtaP 𝔞 𝔢 * 𝔯)) (w6EtaP 𝔞 𝔢 * 𝔯)
        (alphaCheck 𝔞 / (2 * w6M m hm)) (w6EpsFlat 𝔞 𝔢) H.X0 ∧
      w6EpsFlat 𝔞 𝔢 ≤ w8Eps0W m hm n ∧ w8Eps0W m hm n ≤ w6Gamma1 m hm * alphaCheck 𝔞 ∧
      0 < w6EpsFlat 𝔞 𝔢 := by
  obtain ⟨hp, hle, hhi⟩ := w8_epsFlat_shell hm n
  refine ⟨by rw [w6EtaP, w6QP, w6Tn_eq]; rfl, by rw [w6EpsFlat, w6Tn_eq]; rfl, ?_, hle, hhi, hp⟩
  exact H.w6size.2.2.2.1

/-- **W6 with the sharp starting size** (blueprint `bpW:w8:w6-general`): for the shell iteration
(starting size `ε_{0,n} ∈ [ε^♭_{0,n}, γ₁ α̌_n]`),
* Lemma `bpW:w6:applicable`: the hypotheses of Proposition `bpW:w6:convergence` (`β₀ = β_*`);
* Lemma `bpW:w6:freq-lip`: the admissible family, with `ε_ω = ε^{(n)}_ω`, `ε₁ = 0`,
  `ε₂ = 3γα_n + 4ε_{0,n}` (deviation D4 of W6-ITER) and `θ = 425(1+M) max(γ, γ₁) ≤ θ₀`;
* Lemma `bpW:w6:exclusion`: `Π_n ∖ Γ_n ⊆ ℰ^{(n)}`;
* Lemma `bpW:w6:final-freq`: on `Γ_n`, `|⟨k, ω^{(n)}_*⟩| ≥ α̌_n/(2A_k)` (`k ≠ 0`),
  `|ω^{(n)}_* - ω⁰| ≤ ε^{(n)}_ω`, and `ω^{(n)}_*` is `(N_A + θ)`-Lipschitz.
Theorem `bpW:w6:tori` (W6 part) is `w8ShellToriKam_of_stepSmooth`. -/
theorem w8_w6General (H : W8ShellPrep m hm n P X) :
    W6ConvHyp (w8ShellSeqData m hm n) 𝔓 H.om0 H.Om0 H.w6P0 H.X0 (measBetaStar m) ∧
      ((∀ ν, IsFreqPair m hm (w8Pi 𝔱 n) 𝔞 ((w8ShellFamily H).D ν) ((w8ShellFamily H).ω ν)
        ((w8ShellFamily H).Ω ν) (w8ShellEpsOm m hm n) 0
        (3 * w6Gamma m hm * 𝔞 + 4 * w8Eps0W m hm n) (w6Theta m hm)) ∧
        w6Theta m hm ≤ measTheta0 m hm) ∧
      w8Pi 𝔱 n \ w8ShellGamma H ⊆ w8ShellExcl H ∧
      (∀ ξ ∈ w8ShellGamma H, ∀ k : Fin 2 → ℤ, k ≠ 0 →
        alphaCheck 𝔞 / (2 * kAk k) ≤ |∑ i, (k i : ℝ) * w8ShellOmega H ξ i|) ∧
      (∀ ξ ∈ w8ShellGamma H, ‖w8ShellOmega H ξ - omegaTan m hm ξ‖ ≤ w8ShellEpsOm m hm n) ∧
      (∀ ξ ∈ w8ShellGamma H, ∀ ζ ∈ w8ShellGamma H,
        ‖w8ShellOmega H ξ - w8ShellOmega H ζ‖ ≤ (measNA m hm + w6Theta m hm) * ‖ξ - ζ‖) := by
  obtain ⟨-, hlo, hhi⟩ := w8_epsFlat_shell hm n
  have hS := w8MeasSetup hm n
  obtain ⟨f1, f2, f3⟩ := H.w6FinalFreq hS hlo hhi
  refine ⟨H.w6Applicable hlo hhi, ⟨fun ν => (w8ShellFamily H).pair ν, w6Theta_le m hm⟩,
    H.w6Exclusion hS hlo hhi, f1, f2, f3⟩

/-- **The tori of one shell in KAM coordinates** (W6 part of Theorem `bpW:w6:tori` for the shell
iteration, blueprint `bpW:w8:w6-general`, Step `stepW:w8:g-tori`; conditional helper on the
named W5 dependencies `W6StepSmooth`, `W6StepSmoothMod`): for `Ψ(θ) = Φ^{(n)}_P(Φ^{(n)}_*(θ))`,
holomorphy, periodicity and reality, joint continuity on `T_{s_∞} × Γ_n`, values in
`D(s - 4σ_P, 2η_P r_n)` with `Ψ(θ) - ιθ = ιV`, `|V|_{p_+, r_n} ≤ e^{(n)}_tor`, and the invariance
in `𝒫^{p-1}` on `T_{s_0/2}`. -/
theorem w8ShellToriKam_of_stepSmooth (hS : W6StepSmooth) (hSm : W6StepSmoothMod)
    (H : W8ShellPrep m hm n P X) :
    (∀ ξ ∈ w8ShellGamma H,
      DifferentiableOn ℂ (fun θ => w8ShellTorusKam H θ ξ)
        (complexStrip 2 (w8ShellSeqData m hm n).sInfty) ∧
      (∀ θ ∈ complexStrip 2 (w8ShellSeqData m hm n).sInfty, ∀ i : Fin 2,
        w8ShellTorusKam H (θ + _root_.Pi.single i 1) ξ = w8ShellTorusKam H θ ξ + stepTau i) ∧
      ∀ x : Fin 2 → ℝ, StepReal (w8ShellTorusKam H (fun i => (x i : ℂ)) ξ)) ∧
    ContinuousOn (fun q : (Fin 2 → ℂ) × (Fin 2 → ℝ) => w8ShellTorusKam H q.1 q.2)
      (complexStrip 2 (w8ShellSeqData m hm n).sInfty ×ˢ w8ShellGamma H) ∧
    (∀ θ ∈ complexStrip 2 (w8ShellSeqData m hm n).sInfty, ∀ ξ ∈ w8ShellGamma H,
      w8ShellTorusKam H θ ξ ∈ kamDomain (w6S - 4 * w6SigmaP) (2 * w6EtaP 𝔞 𝔢 * 𝔯) ∧
      ∃ V : KamPhase, w8ShellTorusKam H θ ξ - w6TorusPt θ = w6Iota V ∧
        kamNorm 𝔯 V ≤ w8ShellEtor m hm n) ∧
    ∀ ξ ∈ w8ShellGamma H, ∀ θ ∈ complexStrip 2 (w6S0 / 2), ∀ {K0 : ℝ}
      (hΩ0 : ∀ j : ℕ+, |waveFreqNor m hm ξ j| ≤ K0 * ((j : ℝ) + 2)),
      w6Field hΩ0 (waveFreqTan m hm ξ) (H.prepStepHyp.hyp.X' ξ) (w8ShellTorusKam H θ ξ) =
        w6IotaPred (fderiv ℂ (fun θ' => w8ShellTorusKam H θ' ξ) θ
          (w6NuVec (w8ShellOmega H ξ))) := by
  obtain ⟨-, hlo, hhi⟩ := w8_epsFlat_shell hm n
  exact H.w6ToriKam_of_stepSmooth hS hSm hlo hhi

end Labels

end KAM.Wave

end
