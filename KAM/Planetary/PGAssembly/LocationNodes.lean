/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.Main

/-!
# P Part 5: literal exports of the torus nodes (GAP-P5b)

Append-only exports stating the literal conclusions of `bpP:p5:kset` (relative closedness and
`σ`-compactness of `D₀`: `pgD0_relClosed`), `stepP:p5:tc-freq` (`tc_freq_node`) and
`bpP:p5:torus-conv` (`torus_conv_node`). The index `J ∈ pgD0` stands for `ω = ω₀(J) ∈ Ω_*`.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

/-- `bpP:p5:kset`: `D₀` is relatively closed in `D` (the trace of a closed set) and
`σ`-compact. -/
theorem pgD0_relClosed (d : PGData a b) {r mu : ℝ} (h : admissible d (pgRstar d) r mu) :
    (∃ C : Set (Fin (a+b) → ℝ), IsClosed C ∧ pgD0 d r mu = pgActionDomain d r mu ∩ C) ∧
      IsSigmaCompact (pgD0 d r mu) := by
  refine ⟨?_, fam_isSigmaCompact_D0 h⟩
  obtain ⟨-, -, -, hD⟩ := pg_kam_dictionary d r mu h
  obtain ⟨u, hu, hue⟩ := continuousOn_iff_isClosed.1 (fam_continuousOn_realFreq h)
    (twoScaleDiophantine a b (pgKamScale d r mu).γ₁ (pgKamScale d r mu).γ₂
      (pgKamScale d r mu).τ) (fam_isClosed_twoScale _ _ _ _ _)
  obtain ⟨-, -, -, hl1, -⟩ := kh_dyn h
  have hρ : 0 < (params d r mu).rho := by
    show 0 < (params d r mu).l1 / 2; linarith
  refine ⟨u, hu, ?_⟩
  rw [← hD]
  ext J
  have hDsub : J ∈ pgActionDomain d r mu → J ∈ realNbhd (pgActionDomain d r mu)
      (params d r mu).rho := fun hJ => ⟨J, hJ, by simpa using hρ⟩
  constructor
  · rintro ⟨hJ, hg⟩
    have : J ∈ (realFreq (kamH d mu)) ⁻¹' _ ∩ realNbhd (pgActionDomain d r mu)
        (params d r mu).rho := ⟨hg, hDsub hJ⟩
    rw [hue] at this
    exact ⟨hJ, this.1⟩
  · rintro ⟨hJ, he⟩
    refine ⟨hJ, ?_⟩
    have : J ∈ u ∩ realNbhd (pgActionDomain d r mu) (params d r mu).rho := ⟨he, hDsub hJ⟩
    rw [← hue] at this
    exact this.1

/-- `stepP:p5:tc-freq`: for `J ∈ D₀`, the frequency `w = ω₀(J)/2π` has fast part bounded by
`C_w`, slow part by `C_w μ` (`C_w` independent of `(r, μ)`), and is `(min γ₁ γ₂, τ)`-
Diophantine with `τ = n + 1 > a + b`. -/
theorem tc_freq_node (d : PGData a b) : ∃ Cw : ℝ, 0 < Cw ∧ ∀ r mu : ℝ,
    admissible d (pgRstar d) r mu → ∀ J ∈ pgD0 d r mu,
      ‖(blockFast ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) : Fin a → ℝ)‖ ≤ Cw ∧
      ‖(blockSlow ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) : Fin b → ℝ)‖ ≤ Cw*mu ∧
      KAM.IsDiophantine (min (params d r mu).gamma1 (params d r mu).gamma2) (pgTau a b)
        ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) ∧
      pgTau a b = ((a+b:ℕ):ℝ) + 1 ∧ ((a+b:ℕ):ℝ) < pgTau a b := by
  obtain ⟨Cw, hCw, hfreq⟩ := frequency_bounds d
  refine ⟨Cw, hCw, fun r mu h J hJ => ⟨(hfreq r mu h J hJ).1, (hfreq r mu h J hJ).2, ?_,
    rfl, by unfold pgTau; linarith⟩⟩
  obtain ⟨hr0, -, hmu0, -⟩ := h
  have hk0 := pgScales_k0_pos d
  have hrp : 0 < r ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hr0 _
  have h1 : 0 < (params d r mu).gamma1 := by
    show 0 < (pgScales d).k0 * r ^ (5 / 2 : ℝ); positivity
  have h2 : 0 < (params d r mu).gamma2 := by
    show 0 < mu * (pgScales d).k0 * r ^ (5 / 2 : ℝ); positivity
  have htau : ((a + b : ℕ) : ℝ) < pgTau a b := by unfold pgTau; linarith
  exact (cp10_isDiophantine h1 h2 htau hJ.2).1

/-- `bpP:p5:torus-conv`: for every `J ∈ D₀` (that is, `ω = ω₀(J) ∈ Ω_*`) the torus
`K_ω = physicalTorus J` is a frozen cylinder torus of `H_μ` in `C(V, r)` with frequency
`w = ω`, `w` is `(min γ₁ γ₂, τ)`-Diophantine with `τ = n + 1 > a + b`, and the frequency
bounds hold with a constant `C_w` independent of `(r, μ)`; `K_ω(ℝⁿ) ⊆ C(V, r)`. -/
theorem torus_conv_node (d : PGData a b) : ∃ Cw : ℝ, 0 < Cw ∧ ∀ r mu : ℝ,
    ∀ h : admissible d (pgRstar d) r mu, ∀ J ∈ pgD0 d r mu,
      IsCylinderTorus (degenerateHamiltonian d.H0 d.P mu) (cylinder d.V r)
        ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J)
        (physicalTorus d r mu h (pgFamily d r mu h) J) ∧
      KAM.IsDiophantine (min (params d r mu).gamma1 (params d r mu).gamma2) (pgTau a b)
        ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) ∧
      pgTau a b = ((a+b:ℕ):ℝ) + 1 ∧ ((a+b:ℕ):ℝ) < pgTau a b ∧
      ‖(blockFast ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) : Fin a → ℝ)‖ ≤ Cw ∧
      ‖(blockSlow ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) : Fin b → ℝ)‖ ≤ Cw*mu ∧
      range (physicalTorus d r mu h (pgFamily d r mu h) J) ⊆ cylinder d.V r := by
  obtain ⟨Cw, hCw, hfr⟩ := tc_freq_node d
  refine ⟨Cw, hCw, fun r mu h J hJ => ?_⟩
  obtain ⟨hf, hs, hdio, htau, htau'⟩ := hfr r mu h J hJ
  have hspec := (torus_conv d r mu h).choose_spec
  have hT := hspec.2.2.2.2.2.2 J hJ
  refine ⟨hT, hdio, htau, htau', hf, hs, ?_⟩
  rintro _ ⟨θ, rfl⟩
  exact (hT.2.1 θ).1

end KAM.Planetary

end
