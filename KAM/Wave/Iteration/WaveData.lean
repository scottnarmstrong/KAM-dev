/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.Constants
public import KAM.Wave.Iteration.ConvArith
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# W6: the data of the wave iteration (blueprint `bpW:w6:wave-iteration`, `bpW:w6:prep-step`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint labels `bpW:w6:wave-iteration`, `bpW:w6:prep-step` (steps `p-data`,
`p-step`, `p-size`, the arithmetic only) and `bpW:w6:to-w8` ("Starting size"), milestone W6.

For `0 < α ≤ α₀`, `α̂ = α^{44/47}`, `α̌ = α^{48/47}`, a majorant `ε > 0`, `r > 0`:
`q_P = ε/(α̂ σ_P^{t^♮})`, `η_P = q_P^{1/3}`, `r₀ = η_P r`,
`ε^♭_0 = 2 C^♮_2 ε^{4/3} (α̂ σ_P^{t^♮})^{-1/3}` (`bpW:w6:prep-step` (iv)),
`M_{F,P} = c^♮_F ε/(α̂ σ_P^{t^♮-1})` (`bpW:w6:prep-step` (iii)), the sequence data of the iteration
(`s₀ = 7/64`, `r₀ = η_P r`, `α₀^{it} = α̌`, `M₀ = 2M`, starting size `ε₀`) and
`e_tor = M_{F,P} + e_Φ` (`bpW:w6:tori` (iv)).

Results (no W5 step is used; these are the numerical parts of the cited steps):
* step `p-data`: `q_P ≤ (c^♮_0)^{-3}`, `η_P ≤ 1/8`, W5's smallness (modified case)
  `ε ≤ α̂ σ_P^{t^♮} η_P²/c^♮_0`, `σ_P ≤ min(1/4, s/6)`, `λ = α/M ≤ α̂/M`;
* step `p-step`: `(6π+3) ε/λ ≤ 22γM ≤ M`;
* step `p-size`: `2C^♮_2 ε η_P = ε^♭_0 ≤ γ₁ α̌` (via `α^{4/3} α̂^{-1/3} = α̌`), and (v): `λ₀ ≤ λ`;
* the iteration data are valid and small: `ε₀ ≤ γ₁ α̌` gives `ε₀ ≤ γ₀ α̌ σ₀^t`;
* "Starting size" of `bpW:w6:to-w8`: `ε^♭_0/α̌ = 2C^♮_2 σ_P^{-t^♮/3} (ε/α)^{4/3}`,
  `M_{F,P} = c^♮_F σ_P^{1-t^♮} α^{3/47} (ε/α)`, and for `ε₀ = ε^♭_0`:
  `e_tor ≤ c^♮_F σ_P^{1-t^♮} (ε/α) + 10 c_F C^♮_2 σ₀^{1-t} σ_P^{-t^♮/3} (ε/α)^{4/3}`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

/-! ### Signs of the modified constants -/

theorem waveC_zero_ge_one : 1 ≤ waveC 0 := by
  have e : waveC 0 = (1 + Real.pi⁻¹) ^ 2 := by unfold waveC; simp
  rw [e]
  have : 0 ≤ Real.pi⁻¹ := inv_nonneg.2 Real.pi_pos.le
  nlinarith

theorem w6CFn_ge : 612 ≤ w6CFn := by
  unfold w6CFn stepCFn waveBNconst
  have h0 := waveC_zero_ge_one
  have h1 := waveC_nonneg (q := 2) (by norm_num)
  have h2 := waveC_nonneg (q := 2 * w6Tau) (by unfold w6Tau; norm_num)
  have h3 := waveC_nonneg (q := 2 * w6Tau + 2) (by unfold w6Tau; norm_num)
  have hC : 17 ≤ stepC1 := by unfold stepC1; have := one_le_homKS; linarith
  have hb : 4 ≤ 4 * (waveC 0 + waveC 2 + waveC (2 * w6Tau) + waveC (2 * w6Tau + 2)) := by linarith
  nlinarith

theorem w6C0n_ge : 8 ≤ w6C0n := by
  have := w6CFn_ge; unfold w6C0n stepC0n; unfold w6CFn at this; linarith

/-- `α^{4/3} α̂^{-1/3} = α̌` for `α > 0` (`4/3 - 44/141 = 48/47`). -/
theorem alpha_rpow_identity {α : ℝ} (hα : 0 < α) :
    α ^ (4 / 3 : ℝ) * alphaHat α ^ (-(1 / 3 : ℝ)) = alphaCheck α := by
  unfold alphaHat alphaCheck
  rw [← Real.rpow_mul hα.le, ← Real.rpow_add hα]
  norm_num

/-! ### Definitions -/

/-- `q_P = ε/(α̂ σ_P^{t^♮})`. -/
def w6QP (α ε : ℝ) : ℝ := ε / (alphaHat α * w6SigmaP ^ w6Tn)

/-- `η_P = (ε/(α̂ σ_P^{t^♮}))^{1/3}` (blueprint `bpW:w6:prep-step`). -/
def w6EtaP (α ε : ℝ) : ℝ := w6QP α ε ^ (1 / 3 : ℝ)

/-- `ε^♭_0 = 2 C^♮_2 ε^{4/3} (α̂ σ_P^{t^♮})^{-1/3}` (blueprint `bpW:w6:prep-step` (iv)). -/
def w6EpsFlat (α ε : ℝ) : ℝ :=
  2 * w6C2n * ε ^ (4 / 3 : ℝ) * (alphaHat α * w6SigmaP ^ w6Tn) ^ (-(1 / 3 : ℝ))

/-- `M_{F,P} = c^♮_F ε/(α̂ σ_P^{t^♮-1})` (blueprint `bpW:w6:prep-step` (iii)). -/
def w6MFP (α ε : ℝ) : ℝ := stepMF w6CFn w6Tn (alphaHat α) w6SigmaP ε

/-- The sequence data of the wave iteration (blueprint `bpW:w6:wave-iteration`): `s₀ = 7/64`,
`r₀ = η_P r`, `α₀^{it} = α̌`, `M₀ = 2M` and the starting size `ε₀` (a parameter). -/
def w6WaveSeq (m : ℝ) (hm : 0 < m) (α r ε ε₀ : ℝ) : W6SeqData where
  s0 := w6S0
  r0 := w6EtaP α ε * r
  al0 := alphaCheck α
  M0 := w6M0 m hm
  eps0 := ε₀

/-- `e_tor = M_{F,P} + e_Φ` (blueprint `bpW:w6:tori` (iv)), `e_Φ = 5 c_F ε₀/(α̌ σ₀^{t-1})`. -/
def w6Etor (m : ℝ) (hm : 0 < m) (α r ε ε₀ : ℝ) : ℝ :=
  w6MFP α ε + (w6WaveSeq m hm α r ε ε₀).ePhi

section

variable {m : ℝ} {hm : 0 < m} {α ε : ℝ}

theorem w6SigmaP_rpow_pos (x : ℝ) : 0 < w6SigmaP ^ x := Real.rpow_pos_of_pos w6SigmaP_pos x

theorem alphaHat_pos (hα : 0 < α) : 0 < alphaHat α := Real.rpow_pos_of_pos hα _

theorem w6QP_pos (hα : 0 < α) (hε : 0 < ε) : 0 < w6QP α ε :=
  div_pos hε (mul_pos (alphaHat_pos hα) (w6SigmaP_rpow_pos _))

theorem w6EtaP_pos (hα : 0 < α) (hε : 0 < ε) : 0 < w6EtaP α ε :=
  Real.rpow_pos_of_pos (w6QP_pos hα hε) _

/-- Step `p-data`: `q_P ≤ γ/σ_P^{t^♮} ≤ (c^♮_0)^{-3}`. -/
theorem w6QP_le (hα : 0 < α) (hα0 : α ≤ measAlpha0 m hm) (hεγ : ε ≤ w6Gamma m hm * α) :
    w6QP α ε ≤ w6C0n⁻¹ ^ 3 := by
  obtain ⟨-, -, hαh, -, -, -⟩ := alpha_facts m hm hα hα0
  have hh := alphaHat_pos hα
  have hs := w6SigmaP_rpow_pos w6Tn
  have hg := w6Gamma_pos m hm
  refine le_trans ?_ (w6prep_data_arith m hm)
  unfold w6QP
  rw [div_le_div_iff₀ (by positivity) hs]
  calc ε * w6SigmaP ^ w6Tn ≤ w6Gamma m hm * α * w6SigmaP ^ w6Tn := by gcongr
    _ ≤ w6Gamma m hm * alphaHat α * w6SigmaP ^ w6Tn := by gcongr
    _ = w6Gamma m hm * (alphaHat α * w6SigmaP ^ w6Tn) := by ring

theorem w6EtaP_le_inv (hα : 0 < α) (hα0 : α ≤ measAlpha0 m hm) (hε : 0 < ε)
    (hεγ : ε ≤ w6Gamma m hm * α) : w6EtaP α ε ≤ w6C0n⁻¹ := by
  have h := Real.rpow_le_rpow (w6QP_pos hα hε).le (w6QP_le hα hα0 hεγ)
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hc := w6C0n_pos
  rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.2 hc.le)] at h
  norm_num at h
  exact h

/-- Step `p-data`: `η_P ≤ 1/8`. -/
theorem w6EtaP_le (hα : 0 < α) (hα0 : α ≤ measAlpha0 m hm) (hε : 0 < ε)
    (hεγ : ε ≤ w6Gamma m hm * α) : w6EtaP α ε ≤ 1 / 8 := by
  refine (w6EtaP_le_inv hα hα0 hε hεγ).trans ?_
  rw [one_div]; exact inv_anti₀ (by norm_num) w6C0n_ge

/-- Step `p-data`: W5's smallness (modified case) `ε ≤ α̂ σ_P^{t^♮} η_P²/c^♮_0`
(`bpW:w5:small`). -/
theorem w6prep_small (hα : 0 < α) (hα0 : α ≤ measAlpha0 m hm) (hε : 0 < ε)
    (hεγ : ε ≤ w6Gamma m hm * α) :
    ε ≤ alphaHat α * w6SigmaP ^ w6Tn * w6EtaP α ε ^ 2 / w6C0n := by
  have hq := w6QP_pos hα hε
  have hc0 := w6C0n_pos
  have hη0 := w6EtaP_pos hα hε
  have hη := w6EtaP_le_inv hα hα0 hε hεγ
  have hB : 0 < alphaHat α * w6SigmaP ^ w6Tn := mul_pos (alphaHat_pos hα) (w6SigmaP_rpow_pos _)
  have hη3 : w6EtaP α ε ^ 3 = w6QP α ε := by
    unfold w6EtaP; rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]; norm_num
  have he : ε = w6EtaP α ε ^ 3 * (alphaHat α * w6SigmaP ^ w6Tn) := by
    rw [hη3, w6QP, div_mul_cancel₀ _ hB.ne']
  rw [le_div_iff₀ hc0]
  have h1 : w6EtaP α ε * w6C0n ≤ 1 := by
    calc w6EtaP α ε * w6C0n ≤ w6C0n⁻¹ * w6C0n := by gcongr
      _ = 1 := inv_mul_cancel₀ hc0.ne'
  conv_lhs => rw [he]
  calc w6EtaP α ε ^ 3 * (alphaHat α * w6SigmaP ^ w6Tn) * w6C0n
      = (w6EtaP α ε * w6C0n) * (w6EtaP α ε ^ 2 * (alphaHat α * w6SigmaP ^ w6Tn)) := by ring
    _ ≤ 1 * (w6EtaP α ε ^ 2 * (alphaHat α * w6SigmaP ^ w6Tn)) := by gcongr
    _ = _ := by ring

/-- Step `p-data`: `σ_P ≤ min(1/4, s/6)`. -/
theorem w6SigmaP_le_min : w6SigmaP ≤ min (1 / 4) (w6S / 6) := by
  rw [w6SigmaP_val]; unfold w6S; norm_num

/-- Step `p-data`: `λ = α/M ≤ α̂/M`. -/
theorem w6prep_lam_le (hα : 0 < α) (hα0 : α ≤ measAlpha0 m hm) :
    α / w6M m hm ≤ alphaHat α / w6M m hm := by
  obtain ⟨-, -, hαh, -, -, -⟩ := alpha_facts m hm hα hα0
  exact div_le_div_of_nonneg_right hαh (w6M_pos m hm).le

/-- Step `p-step`: `(6π+3) ε/λ ≤ 22 γ M ≤ M`, `λ = α/M`. -/
theorem w6prep_lip_growth (hα : 0 < α) (hε : 0 ≤ ε) (hεγ : ε ≤ w6Gamma m hm * α) :
    (6 * π + 3) * ε / (α / w6M m hm) ≤ 22 * w6Gamma m hm * w6M m hm ∧
      22 * w6Gamma m hm * w6M m hm ≤ w6M m hm := by
  have hM := w6M_pos m hm
  have hg := w6Gamma_pos m hm
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  refine ⟨?_, by have := w6twentytwo_gamma_le m hm; nlinarith⟩
  rw [div_le_iff₀ (div_pos hα hM)]
  have e : 22 * w6Gamma m hm * w6M m hm * (α / w6M m hm) = 22 * (w6Gamma m hm * α) := by
    field_simp
  rw [e]
  have h6 : 6 * π + 3 ≤ 22 := by linarith
  calc (6 * π + 3) * ε ≤ 22 * ε := by gcongr
    _ ≤ 22 * (w6Gamma m hm * α) := by gcongr

/-- `ε^♭_0 = 2 C^♮_2 ε η_P` (blueprint `bpW:w6:prep-step`, step `p-size`). -/
theorem w6EpsFlat_eq (hα : 0 < α) (hε : 0 < ε) :
    w6EpsFlat α ε = 2 * w6C2n * ε * w6EtaP α ε := by
  have hB : 0 < alphaHat α * w6SigmaP ^ w6Tn := mul_pos (alphaHat_pos hα) (w6SigmaP_rpow_pos _)
  unfold w6EpsFlat w6EtaP w6QP
  rw [Real.div_rpow hε.le hB.le, Real.rpow_neg hB.le,
    show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add hε, Real.rpow_one]
  ring

theorem w6EpsFlat_pos (hα : 0 < α) (hε : 0 < ε) : 0 < w6EpsFlat α ε := by
  rw [w6EpsFlat_eq hα hε]
  have := w6EtaP_pos hα hε; have := w6C2n_pos; positivity

/-- `ε^♭_0 = 2 C^♮_2 σ_P^{-t^♮/3} ε^{4/3} α̂^{-1/3}`. -/
theorem w6EpsFlat_eq' (hα : 0 < α) :
    w6EpsFlat α ε = 2 * w6C2n * w6SigmaP ^ (-(w6Tn / 3)) * (ε ^ (4 / 3 : ℝ) *
      alphaHat α ^ (-(1 / 3 : ℝ))) := by
  unfold w6EpsFlat
  rw [Real.mul_rpow (alphaHat_pos hα).le (w6SigmaP_rpow_pos _).le,
    ← Real.rpow_mul w6SigmaP_pos.le]
  rw [show w6Tn * -(1 / 3 : ℝ) = -(w6Tn / 3) by ring]
  ring

/-- Step `p-size` (blueprint `bpW:w6:prep-step` (iv)): `ε ≤ γα ⇒ ε^♭_0 ≤ γ₁ α̌`. -/
theorem w6EpsFlat_le (hα : 0 < α) (hε : 0 ≤ ε) (hεγ : ε ≤ w6Gamma m hm * α) :
    w6EpsFlat α ε ≤ w6Gamma1 m hm * alphaCheck α := by
  rw [w6EpsFlat_eq' hα]
  have hg := w6Gamma_pos m hm
  have hC := w6C2n_pos
  have hc := Real.rpow_pos_of_pos hα (48 / 47 : ℝ)
  have hh : 0 ≤ alphaHat α ^ (-(1 / 3 : ℝ)) := (Real.rpow_pos_of_pos (alphaHat_pos hα) _).le
  have h1 : ε ^ (4 / 3 : ℝ) ≤ w6Gamma m hm ^ (4 / 3 : ℝ) * α ^ (4 / 3 : ℝ) := by
    rw [← Real.mul_rpow hg.le hα.le]
    exact Real.rpow_le_rpow hε hεγ (by norm_num)
  have hsz := w6prep_size_arith m hm
  have hs := w6SigmaP_rpow_pos (w6Tn / 3)
  have es : w6SigmaP ^ (-(w6Tn / 3)) = (w6SigmaP ^ (w6Tn / 3))⁻¹ := Real.rpow_neg w6SigmaP_pos.le _
  rw [es]
  calc 2 * w6C2n * (w6SigmaP ^ (w6Tn / 3))⁻¹ * (ε ^ (4 / 3 : ℝ) * alphaHat α ^ (-(1 / 3 : ℝ)))
      ≤ 2 * w6C2n * (w6SigmaP ^ (w6Tn / 3))⁻¹ *
        (w6Gamma m hm ^ (4 / 3 : ℝ) * α ^ (4 / 3 : ℝ) * alphaHat α ^ (-(1 / 3 : ℝ))) := by
        gcongr
    _ = 2 * w6C2n * w6Gamma m hm ^ (4 / 3 : ℝ) / w6SigmaP ^ (w6Tn / 3) *
        (α ^ (4 / 3 : ℝ) * alphaHat α ^ (-(1 / 3 : ℝ))) := by ring
    _ = 2 * w6C2n * w6Gamma m hm ^ (4 / 3 : ℝ) / w6SigmaP ^ (w6Tn / 3) * alphaCheck α := by
        rw [alpha_rpow_identity hα]
    _ ≤ w6Gamma1 m hm * alphaCheck α := mul_le_mul_of_nonneg_right hsz hc.le

/-- (v) of `bpW:w6:prep-step`: `λ₀ = α̌/M₀ ≤ λ = α/M`. -/
theorem w6lam0_le_lam (hα : 0 < α) (hα0 : α ≤ measAlpha0 m hm) :
    alphaCheck α / w6M0 m hm ≤ α / w6M m hm := by
  obtain ⟨hc0, hcα, -, -, -, -⟩ := alpha_facts m hm hα hα0
  have hM := w6M_pos m hm
  unfold w6M0
  rw [div_le_div_iff₀ (by positivity) hM]
  nlinarith

/-! ### The iteration data -/

variable (m hm) in
theorem w6WaveSeq_sigma_zero (r ε ε₀ : ℝ) : (w6WaveSeq m hm α r ε ε₀).sigma 0 = w6Sigma0 := by
  simp [W6SeqData.sigma, w6WaveSeq, w6Sigma0]

/-- The data of Definition `bpW:w6:wave-iteration` satisfy the standing conditions of
`bpW:w6:sequences`. -/
theorem w6WaveSeq_valid (hα : 0 < α) (hα0 : α ≤ measAlpha0 m hm) {r ε₀ : ℝ} (hr : 0 < r)
    (hε : 0 < ε) (hε₀ : 0 < ε₀) : (w6WaveSeq m hm α r ε ε₀).Valid := by
  obtain ⟨hc0, hcα, -, h27, -, -⟩ := alpha_facts m hm hα hα0
  have hαh : α ≤ alphaHat α := (alpha_facts m hm hα hα0).2.2.1
  refine ⟨?_, ?_, ?_, hc0, ?_, w6M0_pos m hm, hε₀⟩
  · show 0 < w6S0; rw [w6S0_val]; norm_num
  · show w6S0 ≤ 1; rw [w6S0_val]; norm_num
  · show 0 < w6EtaP α ε * r; have := w6EtaP_pos hα hε; positivity
  · show alphaCheck α ≤ 1; linarith

/-- Lemma `bpW:w6:applicable`, first clause: `ε₀ ≤ γ₁ α̌ ≤ γ₀ σ₀^t α₀^{it}`, i.e. the smallness
of `bpW:w6:iter-lemma` for the iteration data. -/
theorem w6WaveSeq_small (hα : 0 < α) (hα0 : α ≤ measAlpha0 m hm) {r ε₀ : ℝ}
    (hε₀ : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) :
    (w6WaveSeq m hm α r ε ε₀).eps0 ≤
      w6Gamma0 * (w6WaveSeq m hm α r ε ε₀).al0 * (w6WaveSeq m hm α r ε ε₀).sigma 0 ^ w6T := by
  rw [w6WaveSeq_sigma_zero]
  have h := (w6applicable_arith (m := m) (hm := hm) hα hα0).1
  show ε₀ ≤ w6Gamma0 * alphaCheck α * w6Sigma0 ^ w6T
  linarith

/-! ### Starting size (blueprint `bpW:w6:to-w8`) -/

/-- `ε^♭_0/α̌ = 2 C^♮_2 σ_P^{-t^♮/3} (ε/α)^{4/3}`. -/
theorem w6EpsFlat_div (hα : 0 < α) (hε : 0 ≤ ε) :
    w6EpsFlat α ε / alphaCheck α =
      2 * w6C2n * w6SigmaP ^ (-(w6Tn / 3)) * (ε / α) ^ (4 / 3 : ℝ) := by
  rw [w6EpsFlat_eq' hα, ← alpha_rpow_identity hα, Real.div_rpow hε hα.le]
  have h1 := Real.rpow_pos_of_pos hα (4 / 3 : ℝ)
  have h2 := Real.rpow_pos_of_pos (alphaHat_pos hα) (-(1 / 3 : ℝ))
  field_simp

/-- `M_{F,P} = c^♮_F σ_P^{1-t^♮} α^{3/47} (ε/α)`. -/
theorem w6MFP_eq (hα : 0 < α) :
    w6MFP α ε = w6CFn * w6SigmaP ^ (1 - w6Tn) * α ^ (3 / 47 : ℝ) * (ε / α) := by
  unfold w6MFP stepMF alphaHat
  have h1 : α ^ (44 / 47 : ℝ) = α / α ^ (3 / 47 : ℝ) := by
    rw [eq_div_iff (Real.rpow_pos_of_pos hα _).ne', ← Real.rpow_add hα]; norm_num
  have h2 : w6SigmaP ^ (w6Tn - 1) = (w6SigmaP ^ (1 - w6Tn))⁻¹ := by
    rw [← Real.rpow_neg w6SigmaP_pos.le]; ring_nf
  rw [h1, h2]
  have := Real.rpow_pos_of_pos hα (3 / 47 : ℝ)
  have := w6SigmaP_rpow_pos (1 - w6Tn)
  field_simp

theorem w6MFP_le (hα : 0 < α) (hα1 : α ≤ 1) (hε : 0 ≤ ε) :
    w6MFP α ε ≤ w6CFn * w6SigmaP ^ (1 - w6Tn) * (ε / α) := by
  rw [w6MFP_eq hα]
  have h := Real.rpow_le_one hα.le hα1 (by norm_num : (0 : ℝ) ≤ 3 / 47)
  have : 0 ≤ w6CFn * w6SigmaP ^ (1 - w6Tn) := by
    have := w6CFn_pos; have := w6SigmaP_rpow_pos (1 - w6Tn); positivity
  have : 0 ≤ ε / α := div_nonneg hε hα.le
  calc w6CFn * w6SigmaP ^ (1 - w6Tn) * α ^ (3 / 47 : ℝ) * (ε / α)
      ≤ w6CFn * w6SigmaP ^ (1 - w6Tn) * 1 * (ε / α) := by gcongr
    _ = _ := by ring

/-- `e_Φ = 5 c_F σ₀^{1-t} ε₀/α̌` for the iteration data. -/
theorem w6WaveSeq_ePhi (hα : 0 < α) (r ε ε₀ : ℝ) :
    (w6WaveSeq m hm α r ε ε₀).ePhi = 5 * w6CF * w6Sigma0 ^ (1 - w6T) * (ε₀ / alphaCheck α) := by
  unfold W6SeqData.ePhi stepMF
  rw [w6WaveSeq_sigma_zero]
  show 5 * (w6CF * ε₀ / (alphaCheck α * w6Sigma0 ^ (w6T - 1))) = _
  have h2 : w6Sigma0 ^ (w6T - 1) = (w6Sigma0 ^ (1 - w6T))⁻¹ := by
    rw [← Real.rpow_neg w6Sigma0_pos.le]; ring_nf
  rw [h2]
  have := Real.rpow_pos_of_pos hα (48 / 47 : ℝ)
  have : 0 < alphaCheck α := this
  have := Real.rpow_pos_of_pos w6Sigma0_pos (1 - w6T)
  field_simp

/-- **Starting size** (blueprint `bpW:w6:to-w8`): with the sharp choice `ε₀ = ε^♭_0`,
`e_tor ≤ c^♮_F σ_P^{1-t^♮} (ε/α) + 10 c_F C^♮_2 σ₀^{1-t} σ_P^{-t^♮/3} (ε/α)^{4/3}`. -/
theorem w6Etor_sharp_le (hα : 0 < α) (hα1 : α ≤ 1) (hε : 0 ≤ ε) (r : ℝ) :
    w6Etor m hm α r ε (w6EpsFlat α ε) ≤ w6CFn * w6SigmaP ^ (1 - w6Tn) * (ε / α) +
      10 * w6CF * w6C2n * w6Sigma0 ^ (1 - w6T) * w6SigmaP ^ (-(w6Tn / 3)) *
        (ε / α) ^ (4 / 3 : ℝ) := by
  unfold w6Etor
  rw [w6WaveSeq_ePhi hα, w6EpsFlat_div hα hε]
  have := w6MFP_le hα hα1 hε
  have e : 5 * w6CF * w6Sigma0 ^ (1 - w6T) *
      (2 * w6C2n * w6SigmaP ^ (-(w6Tn / 3)) * (ε / α) ^ (4 / 3 : ℝ)) =
      10 * w6CF * w6C2n * w6Sigma0 ^ (1 - w6T) * w6SigmaP ^ (-(w6Tn / 3)) *
        (ε / α) ^ (4 / 3 : ℝ) := by ring
  linarith

end

end KAM.Wave
