/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.Index
public import KAM.Wave.Homological.Melnikov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The weak bracket with the normal form, sequence level (blueprint-W `bpW:w4:lie` (i), (ii), (iv))

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

This file proves the sequence-space content of `bpW:w4:lie` for given gradients
`F_z, F_{\bar z} ∈ ℓ^N_{a,p+1}` and a given `θ`-derivative term `Fθω = (1/2π) ⟨ω, F_θ⟩` (a complex
number):

* `homOmega_le`: `|Ω_j| ≤ (1+M₀)(j+2)` from the frequency hypotheses;
* `homLie_Omega_mem` (i): `Ωz ∈ ℓ^N_{a,p-1}` with `‖Ωz‖_{a,p-1} ≤ (1+M₀)‖z‖_{a,p}`, and
  `homLie_pairing_summable_gen` (i): the pairings converge absolutely with the bound of
  `bpW:w4:pairing`;
* `homLieSeq`, `homWeakBracket` and `homWeakBracket_eq_neg_lieN` (ii): `⟨⟨N,F⟩⟩ = -L_N F`;
* the guard (G): `HomGuard a p γ`, its verification for the wave consumer `a = p = 1`
  (`homGuard_one_one`), and (iv): `homNOmega_le_gen` (`|N_Ω(z, \bar z)| ≤ (1+M₀) γ ‖z‖ ‖\bar z‖`).

Not done here: the coefficient identity (iii) and the Fréchet derivative (iv), which need the Taylor
class `𝒯_s` and the Banach structure of `ℓ^N_{a,p}`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- `|Ω_j| ≤ (1 + M₀)(j+2)` (blueprint `bpW:w4:lie`, step *Bounds*). -/
theorem homOmega_le {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (j : ℕ+) : |Ω ξ j| ≤ (1 + M0) * ((j : ℝ) + 2) := by
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast Nat.succ_le_of_lt j.pos
  have h1 : (j : ℝ) ^ (1 / 2 : ℝ) * |Ω ξ j - ((j : ℝ) + 2)| ≤ M0 := h.tail ξ hξ j
  have h2 : |Ω ξ j - ((j : ℝ) + 2)| ≤ M0 := by
    have hr : (1 : ℝ) ≤ (j : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hj (by norm_num)
    have : |Ω ξ j - ((j : ℝ) + 2)| ≤ (j : ℝ) ^ (1 / 2 : ℝ) * |Ω ξ j - ((j : ℝ) + 2)| :=
      le_mul_of_one_le_left (abs_nonneg _) hr
    linarith
  have hM0 := h.consts_nonneg.1
  calc |Ω ξ j| = |((j : ℝ) + 2) + (Ω ξ j - ((j : ℝ) + 2))| := by ring_nf
    _ ≤ |((j : ℝ) + 2)| + |Ω ξ j - ((j : ℝ) + 2)| := abs_add_le _ _
    _ ≤ ((j : ℝ) + 2) + M0 := by rw [abs_of_pos (by positivity)]; linarith
    _ ≤ (1 + M0) * ((j : ℝ) + 2) := by nlinarith

/-- **`Ω z ∈ ℓ^N_{a,p-1}`** (blueprint `bpW:w4:lie` (i)). -/
theorem homLie_Omega_mem {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {a p : ℝ} {z : ℕ+ → ℂ} (hz : HomNormal a p z) :
    ∃ hy : HomNormal a (p - 1) (fun j => (Ω ξ j : ℂ) * z j),
      homNorm hy ≤ (1 + M0) * homNorm hz :=
  homNormal_mul (by linarith [h.consts_nonneg.1]) (fun j => by
    simpa [Complex.norm_real] using homOmega_le h hξ j) hz

/-- **Absolute convergence of the pairings** (blueprint `bpW:w4:lie` (i)): for `F ∈ ℓ^N_{a,p_+}`
    (`p_+ = pb`, `1 ≤ p + p_+`)
and `z ∈ ℓ^N_{a,p}` (`a, p ≥ 0`), `⟨F, Ωz⟩₀` converges absolutely with
`|⟨F, Ωz⟩₀| ≤ (1+M₀) ‖F‖_{a,p_+} ‖z‖_{a,p}`. -/
theorem homLie_pairing_summable_gen {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {a p pb : ℝ} (ha : 0 ≤ a) (hp1 : 1 ≤ p + pb) {F z : ℕ+ → ℂ}
    (hF : HomNormal a pb F) (hz : HomNormal a p z) :
    Summable (fun j => ‖F j * ((Ω ξ j : ℂ) * z j)‖) ∧
      ‖∑' j, F j * ((Ω ξ j : ℂ) * z j)‖ ≤ (1 + M0) * (homNorm hF * homNorm hz) := by
  obtain ⟨hy, hn⟩ := homLie_Omega_mem h hξ hz
  have hq : 0 ≤ pb + (p - 1) := by linarith
  refine ⟨(homPair_le ha hq hF hy).1, ?_⟩
  calc _ ≤ homNorm hF * homNorm hy := norm_homPair_le ha hq hF hy
    _ ≤ homNorm hF * ((1 + M0) * homNorm hz) :=
        mul_le_mul_of_nonneg_left hn (homNorm_nonneg hF)
    _ = _ := by ring

/-- The pairing `⟨x, x'⟩₀ = ∑_j x_j x'_j` (no conjugation). -/
def homPair0 (x x' : ℕ+ → ℂ) : ℂ := ∑' j, x j * x' j

theorem homPair0_comm (x x' : ℕ+ → ℂ) : homPair0 x x' = homPair0 x' x := by
  unfold homPair0
  exact tsum_congr fun j => mul_comm _ _

/-- The expression `L_N F = (1/2π)⟨ω, F_θ⟩ - i⟨F_z, Ωz⟩₀ + i⟨F_{\bar z}, Ω\bar z⟩₀`
(blueprint `bpW:w4:lie`), with `Fθω = (1/2π)⟨ω, F_θ⟩` and the gradients as sequences. -/
def homLieSeq (Fθω : ℂ) (Fz Fzb Ωz Ωzb : ℕ+ → ℂ) : ℂ :=
  Fθω - Complex.I * homPair0 Fz Ωz + Complex.I * homPair0 Fzb Ωzb

/-- The weak bracket `⟨⟨N,F⟩⟩ = -(1/2π)⟨ω,F_θ⟩ + ⟨Ω\bar z, Ż⟩₀ + ⟨Ωz, \dot{\bar Z}⟩₀`,
`(Ż, \dot{\bar Z}) = (-iF_{\bar z}, iF_z)`. -/
def homWeakBracket (Fθω : ℂ) (Fz Fzb Ωz Ωzb : ℕ+ → ℂ) : ℂ :=
  -Fθω + homPair0 Ωzb (fun j => -Complex.I * Fzb j) + homPair0 Ωz (fun j => Complex.I * Fz j)

/-- **`⟨⟨N,F⟩⟩ = -L_N F`** (blueprint `bpW:w4:lie` (ii)), valid whenever the two pairings are
defined (here: whenever they are summable). -/
theorem homWeakBracket_eq_neg_lieN {Fθω : ℂ} {Fz Fzb Ωz Ωzb : ℕ+ → ℂ} :
    homWeakBracket Fθω Fz Fzb Ωz Ωzb = -homLieSeq Fθω Fz Fzb Ωz Ωzb := by
  unfold homWeakBracket homLieSeq homPair0
  have e1 : (∑' j, Ωzb j * (-Complex.I * Fzb j)) = -Complex.I * ∑' j, Fzb j * Ωzb j := by
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring
  have e2 : (∑' j, Ωz j * (Complex.I * Fz j)) = Complex.I * ∑' j, Fz j * Ωz j := by
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring
  rw [e1, e2]
  ring

/-- **The guard (G)**: `(j+2)/ω_{a,p}(j+2)² ≤ γ` for all `j ≥ 1`. -/
def HomGuard (a p γ : ℝ) : Prop := ∀ j : ℕ+, ((j : ℝ) + 2) / homWt a p j ^ 2 ≤ γ

/-- **The guard (G) holds for the wave consumer** `a = p = 1`, with `γ = e^{-6}/3` (blueprint
`bpW:w4:lie`, discussion of (G)). -/
theorem homGuard_one_one : HomGuard 1 1 (Real.exp (-6) / 3) := by
  intro j
  have hJ : (3 : ℝ) ≤ (j : ℝ) + 2 := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast Nat.succ_le_of_lt j.pos
    linarith
  have hw : homWt 1 1 j = ((j : ℝ) + 2) * Real.exp ((j : ℝ) + 2) := by
    unfold homWt ellWeight
    push_cast
    rw [Real.rpow_one, one_mul]
  rw [hw, div_le_div_iff₀ (by positivity) (by norm_num)]
  set J : ℝ := (j : ℝ) + 2 with hJdef
  have hE : 1 ≤ Real.exp (-6) * Real.exp (J + J) := by
    rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
  have hsq : (J * Real.exp J) ^ 2 = J ^ 2 * Real.exp (J + J) := by
    rw [mul_pow, sq (Real.exp J), ← Real.exp_add]
  rw [hsq]
  calc J * 3 ≤ J ^ 2 := by nlinarith
    _ ≤ J ^ 2 * (Real.exp (-6) * Real.exp (J + J)) := le_mul_of_one_le_right (by positivity) hE
    _ = _ := by ring

/-- **The guarded form** `N_Ω(z, \bar z) = ∑_j Ω_j z_j \bar z_j` (blueprint `bpW:w4:lie` (iv)):
under (G) the series converges absolutely and `|N_Ω(z,\bar z)| ≤ (1+M₀) γ ‖z‖ ‖\bar z‖`. -/
theorem homNOmega_le_gen {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {a p pb γ : ℝ} (hG : HomGuard a p γ) {z zb : ℕ+ → ℂ}
    (hz : HomNormal a p z) (hzb : HomNormal a p zb) :
    Summable (fun j => ‖(Ω ξ j : ℂ) * z j * zb j‖) ∧
      ‖∑' j, (Ω ξ j : ℂ) * z j * zb j‖ ≤ (1 + M0) * γ * (homNorm hz * homNorm hzb) := by
  have hγ : 0 ≤ γ := (by have := homWt_pos a p 1; positivity : (0 : ℝ) ≤ _).trans (hG 1)
  have hM0 : 0 ≤ 1 + M0 := by linarith [h.consts_nonneg.1]
  obtain ⟨hs, hle⟩ := summable_tsum_mul_le
    (A := fun j => homWt a p j * ‖z j‖) (B := fun j => homWt a p j * ‖zb j‖)
    (fun j => by have := homWt_pos a p j; positivity)
    (fun j => by have := homWt_pos a p j; positivity)
    (homNorm_nonneg hz) (homNorm_nonneg hzb) (homNorm_hasSum hz) (homNorm_hasSum hzb)
  have hb : ∀ j, ‖(Ω ξ j : ℂ) * z j * zb j‖ ≤
      (1 + M0) * γ * ((homWt a p j * ‖z j‖) * (homWt a p j * ‖zb j‖)) := by
    intro j
    have hw := homWt_pos a p j
    have h1 := homOmega_le h hξ j
    have h2 : ((j : ℝ) + 2) ≤ γ * homWt a p j ^ 2 := by
      have := hG j
      rwa [div_le_iff₀ (by positivity)] at this
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |Ω ξ j| * ‖z j‖ * ‖zb j‖ ≤ ((1 + M0) * ((j : ℝ) + 2)) * ‖z j‖ * ‖zb j‖ := by gcongr
      _ ≤ ((1 + M0) * (γ * homWt a p j ^ 2)) * ‖z j‖ * ‖zb j‖ := by gcongr
      _ = _ := by ring
  have hsum : Summable (fun j => ‖(Ω ξ j : ℂ) * z j * zb j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hb (hs.mul_left _)
  refine ⟨hsum, ?_⟩
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  refine (hsum.tsum_le_tsum hb (hs.mul_left _)).trans ?_
  rw [tsum_mul_left]
  nlinarith [mul_le_mul_of_nonneg_left hle (mul_nonneg hM0 hγ)]

end KAM.Wave
