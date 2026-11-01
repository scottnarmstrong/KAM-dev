/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LemmaOneLip
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Modified divisors for the preparatory step (blueprint-W `bpW:w5:w4-modified`, hypotheses)

Off-frontier, source-faithful infrastructure (W5-MODIFIED, blueprint `bpW:w5:w4-modified`); the
dependency graph is still being built.

* `HomMelnikovMod τ α β Π ω Ω`: every divisor of `bpW:w4:melnikov` satisfies the bound of
  `(H_α)`, except the divisors `δ^Q_{k,ij}`, `i ≠ j`, for which only
  `|δ^Q_{k,ij}| ≥ (α/A_k) |i-j| / (min(i,j)+2)^β` is assumed (`bpW:w5:modified`);
* `homModRatio a p p₊ j = ω_{a,p₊}(j+2)/ω_{a,p+1}(j+2) = (j+2)^{p₊-p-1}` (`= I^{-c}`,
  `c = p+1-p₊`), the factor converting the `p+1`-weighted matrix of an operator into its
  `p₊`-weighted matrix;
* `homModDQ`, `homModDQt`: the twisted multipliers `I^{-c}/(iδ^Q_{k,ij})`, `I^{-c}/(iδ^Q_{k,ji})`
  of step `m-sup`;
* `HomModMultBounds`, `HomModMultLip`: the bounds of all division operators at one parameter and
  their Lipschitz bounds, derived from the source premises in `homModMultBounds_of`
  (`β ≤ c`, step `m-sup`) and `homModMultLip_of` (`2β ≤ c`, step `m-lip`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- **Modified Melnikov conditions** (blueprint `bpW:w5:w4-modified`, `bpW:w5:modified`): the
divisors `δ⁰_k` (`k ≠ 0`), `δ^±_{k,j}`, `δ^P_{k,ij}`, `δ^{P'}_{k,ij}` and `δ^Q_{k,jj}` (`k ≠ 0`)
satisfy the bound `α w/A_k` of `(H_α)` with their weights `w` (`bpW:w4:melnikov`), and the
divisors `δ^Q_{k,ij}`, `i ≠ j`, only `|δ^Q_{k,ij}| ≥ (α/A_k)|i-j|/(min(i,j)+2)^β`. -/
structure HomMelnikovMod (τ α β : ℝ) (Par : Set (Fin 2 → ℝ)) (ω : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (Ω : (Fin 2 → ℝ) → ℕ+ → ℝ) : Prop where
  d0 : ∀ ξ ∈ Par, ∀ k : Fin 2 → ℤ, k ≠ 0 → α * 1 / waveA τ k ≤ |homDelta0 (ω ξ) k|
  dp : ∀ ξ ∈ Par, ∀ (k : Fin 2 → ℤ) (j : ℕ+),
    α * (j : ℝ) / waveA τ k ≤ |homDeltaPlus (ω ξ) (Ω ξ) k j|
  dm : ∀ ξ ∈ Par, ∀ (k : Fin 2 → ℤ) (j : ℕ+),
    α * (j : ℝ) / waveA τ k ≤ |homDeltaMinus (ω ξ) (Ω ξ) k j|
  dP : ∀ ξ ∈ Par, ∀ (k : Fin 2 → ℤ) (i j : ℕ+),
    α * ((i : ℝ) + j) / waveA τ k ≤ |homDeltaP (ω ξ) (Ω ξ) k i j|
  dP' : ∀ ξ ∈ Par, ∀ (k : Fin 2 → ℤ) (i j : ℕ+),
    α * ((i : ℝ) + j) / waveA τ k ≤ |homDeltaP' (ω ξ) (Ω ξ) k i j|
  dQd : ∀ ξ ∈ Par, ∀ k : Fin 2 → ℤ, k ≠ 0 → ∀ j : ℕ+,
    α * 1 / waveA τ k ≤ |homDeltaQ (ω ξ) (Ω ξ) k j j|
  dQ : ∀ ξ ∈ Par, ∀ (k : Fin 2 → ℤ) (i j : ℕ+), i ≠ j →
    α / waveA τ k * (|(i : ℝ) - j| / (min (i : ℝ) j + 2) ^ β) ≤ |homDeltaQ (ω ξ) (Ω ξ) k i j|

/-- The weight ratio `ρ_j = ω_{a,p₊}(j+2)/ω_{a,p+1}(j+2)`. -/
def homModRatio (a p pb : ℝ) (j : ℕ+) : ℝ := homWt a pb j / homWt a (p + 1) j

theorem homModRatio_eq (a p pb : ℝ) (j : ℕ+) :
    homModRatio a p pb j = ((j : ℝ) + 2) ^ (pb - (p + 1)) := by
  unfold homModRatio homWt
  rw [ellWeight_div_ellWeight]
  push_cast
  ring_nf

theorem homModRatio_pos (a p pb : ℝ) (j : ℕ+) : 0 < homModRatio a p pb j :=
  div_pos (homWt_pos a pb j) (homWt_pos a (p + 1) j)

/-- `ρ_I x^e ≤ 1` for `0 < x ≤ I = i+2` and `0 ≤ e ≤ p+1-p₊`. -/
theorem homModRatio_mul_rpow_le {a p pb e x : ℝ} (he : 0 ≤ e) (hc : e ≤ p + 1 - pb) (i : ℕ+)
    (hx0 : 0 < x) (hx : x ≤ (i : ℝ) + 2) : homModRatio a p pb i * x ^ e ≤ 1 := by
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast i.pos
  have hI : (1 : ℝ) ≤ (i : ℝ) + 2 := by linarith
  have hI0 : (0 : ℝ) < (i : ℝ) + 2 := by linarith
  rw [homModRatio_eq]
  have h1 : x ^ e ≤ ((i : ℝ) + 2) ^ e := Real.rpow_le_rpow hx0.le hx he
  calc ((i : ℝ) + 2) ^ (pb - (p + 1)) * x ^ e
      ≤ ((i : ℝ) + 2) ^ (pb - (p + 1)) * ((i : ℝ) + 2) ^ e :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hI0.le _)
    _ = ((i : ℝ) + 2) ^ (pb - (p + 1) + e) := (Real.rpow_add hI0 _ _).symm
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hI (by linarith)

theorem homModRatio_le_one {a p pb : ℝ} (hc : pb ≤ p + 1) (i : ℕ+) : homModRatio a p pb i ≤ 1 := by
  have := homModRatio_mul_rpow_le (a := a) (p := p) (pb := pb) (e := 0) le_rfl (by linarith) i
    (x := 1) one_pos
    (by have : (1 : ℝ) ≤ i := by exact_mod_cast i.pos
        linarith)
  simpa using this

theorem norm_homModRatio_le {a p pb : ℝ} (hc : pb ≤ p + 1) (i : ℕ+) :
    ‖(homModRatio a p pb i : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (homModRatio_pos a p pb i)]
  exact homModRatio_le_one hc i

/-- The twisted multiplier `ρ_i/(iδ^Q_{k,ij})` of `Q` (step `m-sup`). -/
def homModDQ (a p pb : ℝ) (w : Fin 2 → ℝ) (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (i j : ℕ+) : ℂ :=
  (homModRatio a p pb i : ℂ) * homDQ w W k i j

/-- The twisted multiplier `ρ_i/(iδ^Q_{k,ji})` of `Q^T`. -/
def homModDQt (a p pb : ℝ) (w : Fin 2 → ℝ) (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (i j : ℕ+) : ℂ :=
  (homModRatio a p pb i : ℂ) * homDQ w W k j i

/-- The bounds of the division operators at one parameter (`bpW:w5:w4-modified`, steps `m-sup`,
`m-other`): as in W4 for `a, b, c^±, P, P'`, and the Hadamard bounds of the twisted `Q`
multipliers. -/
structure HomModMultBounds (a p pb τ α : ℝ) (w : Fin 2 → ℝ) (W : ℕ+ → ℝ) : Prop where
  a0 : ∀ k, ‖homMultA0 w k‖ ≤ 1 * waveA τ k / α
  dp : ∀ k j, ‖homMultDp w W k j‖ ≤ 1 * waveA τ k / α
  dm : ∀ k j, ‖homMultDm w W k j‖ ≤ 1 * waveA τ k / α
  P : ∀ k, HomHadamardBound (homDP w W k) (waveA τ k / α)
  P' : ∀ k, HomHadamardBound (homDP' w W k) (waveA τ k / α)
  Q : ∀ k, HomHadamardBound (homModDQ a p pb w W k) (waveA τ k / α)
  Qt : ∀ k, HomHadamardBound (homModDQt a p pb w W k) (waveA τ k / α)
  nz0 : ∀ k, k ≠ 0 → homDelta0 w k ≠ 0
  nzp : ∀ k j, homDeltaPlus w W k j ≠ 0
  nzm : ∀ k j, homDeltaMinus w W k j ≠ 0
  nzP : ∀ k i j, homDeltaP w W k i j ≠ 0
  nzP' : ∀ k i j, homDeltaP' w W k i j ≠ 0
  nzQ : ∀ k i j, (k ≠ 0 ∨ i ≠ j) → homDeltaQ w W k i j ≠ 0

/-- The Lipschitz bounds of the division operators (`bpW:w5:w4-modified`, step `m-lip`). -/
structure HomModMultLip (a p pb τ α M d : ℝ) (w₁ : Fin 2 → ℝ) (W₁ : ℕ+ → ℝ) (w₂ : Fin 2 → ℝ)
    (W₂ : ℕ+ → ℝ) : Prop where
  a0 : ∀ k, ‖homMultA0 w₁ k - homMultA0 w₂ k‖ ≤ homLipC τ α M d k
  dp : ∀ k j, ‖homMultDp w₁ W₁ k j - homMultDp w₂ W₂ k j‖ ≤ homLipC τ α M d k
  dm : ∀ k j, ‖homMultDm w₁ W₁ k j - homMultDm w₂ W₂ k j‖ ≤ homLipC τ α M d k
  P : ∀ k, HomHadamardBound (fun i j => homDP w₁ W₁ k i j - homDP w₂ W₂ k i j)
    (homLipC τ α M d k)
  P' : ∀ k, HomHadamardBound (fun i j => homDP' w₁ W₁ k i j - homDP' w₂ W₂ k i j)
    (homLipC τ α M d k)
  Q : ∀ k, HomHadamardBound (fun i j => homModDQ a p pb w₁ W₁ k i j - homModDQ a p pb w₂ W₂ k i j)
    (homLipC τ α M d k)
  Qt : ∀ k, HomHadamardBound
    (fun i j => homModDQt a p pb w₁ W₁ k i j - homModDQt a p pb w₂ W₂ k i j) (homLipC τ α M d k)

/-- Lipschitz bound of `1/(iδ)` from a lower bound `L` at both points. -/
theorem norm_homInv_sub_le_of_lower {δ₁ δ₂ L D : ℝ} (hL : 0 < L) (h1 : L ≤ |δ₁|) (h2 : L ≤ |δ₂|)
    (hD : |δ₁ - δ₂| ≤ D) : ‖homInv δ₁ - homInv δ₂‖ ≤ D / L ^ 2 := by
  have hn1 : δ₁ ≠ 0 := fun h => by rw [h, abs_zero] at h1; linarith
  have hn2 : δ₂ ≠ 0 := fun h => by rw [h, abs_zero] at h2; linarith
  rw [norm_homInv_sub hn1 hn2, div_sub_div _ _ hn1 hn2, abs_div, abs_mul]
  simp only [one_mul, mul_one]
  have hp : 0 < |δ₁| * |δ₂| := by positivity
  rw [div_le_div_iff₀ hp (by positivity), abs_sub_comm]
  have hLL : L ^ 2 ≤ |δ₁| * |δ₂| := by rw [sq]; exact mul_le_mul h1 h2 hL.le (abs_nonneg _)
  have hD0 : 0 ≤ D := (abs_nonneg _).trans hD
  calc |δ₁ - δ₂| * L ^ 2 ≤ D * L ^ 2 := mul_le_mul_of_nonneg_right hD (by positivity)
    _ ≤ D * (|δ₁| * |δ₂|) := mul_le_mul_of_nonneg_left hLL hD0

section freq

variable {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {M0 Mω MΩ : ℝ}

theorem homOmega_sub_le (h : HomFreqHyp Par ω Ω M0 Mω MΩ) {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par)
    (hζ : ζ ∈ Par) (j : ℕ+) : |Ω ξ j - Ω ζ j| ≤ MΩ * ‖ξ - ζ‖ := by
  have hj := h.lipTail ξ hξ ζ hζ j
  have hj1 : (1 : ℝ) ≤ (j : ℝ) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast j.pos) (by norm_num)
  have := abs_nonneg (Ω ξ j - Ω ζ j)
  nlinarith

theorem homPairZ_omega_sub_le (h : HomFreqHyp Par ω Ω M0 Mω MΩ) {ξ ζ : Fin 2 → ℝ}
    (hξ : ξ ∈ Par) (hζ : ζ ∈ Par) (k : Fin 2 → ℤ) :
    |homPairZ k (ω ξ) - homPairZ k (ω ζ)| ≤ Fourier.modeSize k * (Mω * ‖ξ - ζ‖) := by
  rw [homPairZ_sub]
  exact (abs_homPairZ_le k _).trans
    (mul_le_mul_of_nonneg_left (h.lipOmega ξ hξ ζ hζ) (Fourier.modeSize_nonneg k))

/-- A divisor `⟨k,ω⟩ + ε₁Ω_i + ε₂Ω_j` (`|ε_m| ≤ 1`) moves by at most `2(1+|k|₁)M|ξ-ζ|`. -/
theorem homDiv_sub_le (h : HomFreqHyp Par ω Ω M0 Mω MΩ) {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par)
    (hζ : ζ ∈ Par) (k : Fin 2 → ℤ) (i j : ℕ+) (e₁ e₂ : ℝ) (he₁ : |e₁| ≤ 1) (he₂ : |e₂| ≤ 1) :
    |(homPairZ k (ω ξ) + e₁ * Ω ξ i + e₂ * Ω ξ j) - (homPairZ k (ω ζ) + e₁ * Ω ζ i + e₂ * Ω ζ j)|
      ≤ 2 * (1 + Fourier.modeSize k) * (Mω + MΩ) * ‖ξ - ζ‖ := by
  have hk := homPairZ_omega_sub_le h hξ hζ k
  have hi := homOmega_sub_le h hξ hζ i
  have hj := homOmega_sub_le h hξ hζ j
  obtain ⟨_, hMω, hMΩ⟩ := h.consts_nonneg
  have hd := norm_nonneg (ξ - ζ)
  have hk0 := Fourier.modeSize_nonneg k
  have e1 : |e₁ * (Ω ξ i - Ω ζ i)| ≤ MΩ * ‖ξ - ζ‖ := by
    rw [abs_mul]
    calc |e₁| * |Ω ξ i - Ω ζ i| ≤ 1 * |Ω ξ i - Ω ζ i| :=
          mul_le_mul_of_nonneg_right he₁ (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hi
  have e2 : |e₂ * (Ω ξ j - Ω ζ j)| ≤ MΩ * ‖ξ - ζ‖ := by
    rw [abs_mul]
    calc |e₂| * |Ω ξ j - Ω ζ j| ≤ 1 * |Ω ξ j - Ω ζ j| :=
          mul_le_mul_of_nonneg_right he₂ (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hj
  have hsplit : (homPairZ k (ω ξ) + e₁ * Ω ξ i + e₂ * Ω ξ j) -
      (homPairZ k (ω ζ) + e₁ * Ω ζ i + e₂ * Ω ζ j) =
      (homPairZ k (ω ξ) - homPairZ k (ω ζ)) + e₁ * (Ω ξ i - Ω ζ i) + e₂ * (Ω ξ j - Ω ζ j) := by
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) e2).trans ?_)
  nlinarith [mul_nonneg hk0 (mul_nonneg hMΩ hd), mul_nonneg hMω hd, mul_nonneg hMΩ hd,
    mul_nonneg hk0 (mul_nonneg hMω hd)]

end freq

/-- `D / (αw/A)² ≤ homLipC/w` for `w ≥ 1`, `D = 2(1+|k|₁)M d`. -/
theorem homLipC_div_sq_le {τ α M d w : ℝ} (hα : 0 < α) (hM : 0 ≤ M) (hd : 0 ≤ d) (hw : 1 ≤ w)
    (k : Fin 2 → ℤ) :
    2 * (1 + Fourier.modeSize k) * M * d / (α * w / waveA τ k) ^ 2 ≤ homLipC τ α M d k / w := by
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  have hk0 := Fourier.modeSize_nonneg k
  have hw0 : 0 < w := by linarith
  have e : 2 * (1 + Fourier.modeSize k) * M * d / (α * w / waveA τ k) ^ 2 =
      homLipC τ α M d k / w / w := by
    unfold homLipC; field_simp
  rw [e]
  exact div_le_self (div_nonneg (homLipC_nonneg hM hd k) hw0.le) hw

section derive

variable {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {M0 Mω MΩ τ α β : ℝ}

theorem homMelnikovMod_pos_of {τ α w : ℝ} (hα : 0 < α) (hw : 0 < w) (k : Fin 2 → ℤ) :
    0 < α * w / waveA τ k := by
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  positivity

theorem ne_zero_of_lower {L δ : ℝ} (hL : 0 < L) (h : L ≤ |δ|) : δ ≠ 0 := fun h0 => by
  rw [h0, abs_zero] at h; linarith

theorem norm_homInv_le_div {τ α w δ : ℝ} (hα : 0 < α) (hw : 0 < w) (k : Fin 2 → ℤ)
    (h : α * w / waveA τ k ≤ |δ|) : ‖homInv δ‖ ≤ waveA τ k / α / w := by
  refine (norm_homInv_le (homMelnikovMod_pos_of hα hw k) h).trans (le_of_eq ?_)
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  field_simp

theorem one_le_natCast_pnat (j : ℕ+) : (1 : ℝ) ≤ j := by exact_mod_cast j.pos

theorem min_add_two_pos (i j : ℕ+) : 0 < min (i : ℝ) j + 2 := by
  have := one_le_natCast_pnat i; have := one_le_natCast_pnat j
  have : 1 ≤ min (i : ℝ) j := le_min (by assumption) (by assumption)
  linarith

/-- The lower bound of the twisted `Q` divisors, rewritten as `α w/A` with
`w = |i-j|/(min(i,j)+2)^β`. -/
theorem homModQ_lower (hH : HomMelnikovMod τ α β Par ω Ω) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par)
    (k : Fin 2 → ℤ) {i j : ℕ+} (hij : i ≠ j) :
    α * (|(i : ℝ) - j| / (min (i : ℝ) j + 2) ^ β) / waveA τ k ≤
      |homDeltaQ (ω ξ) (Ω ξ) k i j| := by
  have := hH.dQ ξ hξ k i j hij
  calc _ = α / waveA τ k * (|(i : ℝ) - j| / (min (i : ℝ) j + 2) ^ β) := by ring
    _ ≤ _ := this

theorem abs_sub_pnat_pos {i j : ℕ+} (hij : i ≠ j) : 0 < |(i : ℝ) - j| := by
  rw [abs_pos, sub_ne_zero]; exact_mod_cast hij

theorem one_le_abs_sub_pnat {i j : ℕ+} (hij : i ≠ j) : 1 ≤ |(i : ℝ) - j| := by
  have : (i : ℤ) ≠ j := by exact_mod_cast hij
  have h2 : (1 : ℤ) ≤ |(i : ℤ) - j| := Int.one_le_abs (sub_ne_zero.mpr this)
  have h3 : (1 : ℝ) ≤ |((i : ℤ) - j : ℤ)| := by exact_mod_cast h2
  simpa using h3

/-- The twisted `Q` multiplier: `|ρ_i/(iδ^Q_{k,ij})| ≤ A_k/(α|i-j|)` for `i ≠ j`, when
`β ≤ p+1-p₊` (step `m-sup`). -/
theorem norm_homModDQ_off_le {a p pb : ℝ} (hα : 0 < α) (hβ0 : 0 ≤ β) (hβ : β ≤ p + 1 - pb)
    (hH : HomMelnikovMod τ α β Par ω Ω) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (k : Fin 2 → ℤ)
    {i j : ℕ+} (hij : i ≠ j) (i' : ℕ+) (hi' : i' = i ∨ i' = j) :
    ‖(homModRatio a p pb i' : ℂ) * homDQ (ω ξ) (Ω ξ) k i j‖ ≤
      waveA τ k / α / |(i : ℝ) - (j : ℝ)| := by
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  have hx0 := min_add_two_pos i j
  have hxβ : 0 < (min (i : ℝ) j + 2) ^ β := Real.rpow_pos_of_pos hx0 β
  have hab := abs_sub_pnat_pos hij
  have hw : 0 < |(i : ℝ) - j| / (min (i : ℝ) j + 2) ^ β := div_pos hab hxβ
  have hnot : ¬(k = 0 ∧ i = j) := fun h => hij h.2
  rw [homDQ, ite_eq_right hnot, norm_mul]
  have h1 := norm_homInv_le_div hα hw k (homModQ_lower hH hξ k hij)
  have hr : ‖(homModRatio a p pb i' : ℂ)‖ * (min (i : ℝ) j + 2) ^ β ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (homModRatio_pos a p pb i')]
    refine homModRatio_mul_rpow_le hβ0 hβ i' hx0 ?_
    rcases hi' with rfl | rfl
    · linarith [min_le_left (i' : ℝ) j]
    · linarith [min_le_right (i : ℝ) i']
  have hr0 : 0 ≤ ‖(homModRatio a p pb i' : ℂ)‖ := norm_nonneg _
  calc ‖(homModRatio a p pb i' : ℂ)‖ * ‖homInv (homDeltaQ (ω ξ) (Ω ξ) k i j)‖
      ≤ ‖(homModRatio a p pb i' : ℂ)‖ *
          (waveA τ k / α / (|(i : ℝ) - j| / (min (i : ℝ) j + 2) ^ β)) :=
        mul_le_mul_of_nonneg_left h1 hr0
    _ = (‖(homModRatio a p pb i' : ℂ)‖ * (min (i : ℝ) j + 2) ^ β) *
          (waveA τ k / α / |(i : ℝ) - j|) := by field_simp
    _ ≤ 1 * (waveA τ k / α / |(i : ℝ) - j|) :=
        mul_le_mul_of_nonneg_right hr (by positivity)
    _ = _ := one_mul _

/-- The diagonal of the twisted `Q` multiplier. -/
theorem norm_homModDQ_diag_le {a p pb : ℝ} (hα : 0 < α) (hc : pb ≤ p + 1)
    (hH : HomMelnikovMod τ α β Par ω Ω) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (k : Fin 2 → ℤ)
    (i : ℕ+) : ‖(homModRatio a p pb i : ℂ) * homDQ (ω ξ) (Ω ξ) k i i‖ ≤ waveA τ k / α := by
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  rw [norm_mul]
  by_cases hk : k = 0
  · rw [homDQ, ite_eq_left ⟨hk, rfl⟩, norm_zero, mul_zero]; positivity
  · rw [homDQ, ite_eq_right (fun h => hk h.1)]
    have h1 := norm_homInv_le_div hα one_pos k (hH.dQd ξ hξ k hk i)
    rw [div_one] at h1
    calc ‖(homModRatio a p pb i : ℂ)‖ * ‖homInv (homDeltaQ (ω ξ) (Ω ξ) k i i)‖
        ≤ 1 * (waveA τ k / α) := mul_le_mul (norm_homModRatio_le hc i) h1 (norm_nonneg _)
          zero_le_one
      _ = _ := one_mul _

theorem homDP_bound_mod (hα : 0 < α) (hH : HomMelnikovMod τ α β Par ω Ω) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ Par) (k : Fin 2 → ℤ) :
    HomHadamardBound (homDP (ω ξ) (Ω ξ) k) (waveA τ k / α) := by
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  refine homHadamardBound_of_weight (by positivity) (fun i j => (i : ℝ) + j) ?_ ?_ ?_
  · intro i j _
    have := one_le_natCast_pnat i; have := one_le_natCast_pnat j
    rw [abs_le]; constructor <;> linarith
  · intro i j; have := one_le_natCast_pnat i; have := one_le_natCast_pnat j; linarith
  · intro i j
    have := one_le_natCast_pnat i; have := one_le_natCast_pnat j
    exact norm_homInv_le_div hα (by positivity) k (hH.dP ξ hξ k i j)

theorem homDP'_bound_mod (hα : 0 < α) (hH : HomMelnikovMod τ α β Par ω Ω) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ Par) (k : Fin 2 → ℤ) :
    HomHadamardBound (homDP' (ω ξ) (Ω ξ) k) (waveA τ k / α) := by
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  refine homHadamardBound_of_weight (by positivity) (fun i j => (i : ℝ) + j) ?_ ?_ ?_
  · intro i j _
    have := one_le_natCast_pnat i; have := one_le_natCast_pnat j
    rw [abs_le]; constructor <;> linarith
  · intro i j; have := one_le_natCast_pnat i; have := one_le_natCast_pnat j; linarith
  · intro i j
    have := one_le_natCast_pnat i; have := one_le_natCast_pnat j
    exact norm_homInv_le_div hα (by positivity) k (hH.dP' ξ hξ k i j)

/-- **The division operators at one parameter** (`bpW:w5:w4-modified`, steps `m-sup`,
`m-other`), from the source premises: `HomMelnikovMod`, `α > 0`, `0 ≤ β ≤ p+1-p₊`. -/
theorem homModMultBounds_of {a p pb : ℝ} (hα : 0 < α) (hβ0 : 0 ≤ β) (hβ : β ≤ p + 1 - pb)
    (hH : HomMelnikovMod τ α β Par ω Ω) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    HomModMultBounds a p pb τ α (ω ξ) (Ω ξ) := by
  have hc : pb ≤ p + 1 := by linarith
  have hA : ∀ k : Fin 2 → ℤ, 0 < waveA τ k := fun k => lt_of_lt_of_le one_pos (waveA_ge_one k)
  refine ⟨fun k => ?_, fun k j => ?_, fun k j => ?_, homDP_bound_mod hα hH hξ,
    homDP'_bound_mod hα hH hξ, fun k => ⟨fun i j hij => ?_, fun i => ?_⟩,
    fun k => ⟨fun i j hij => ?_, fun i => ?_⟩, fun k hk => ?_, fun k j => ?_, fun k j => ?_,
    fun k i j => ?_, fun k i j => ?_, fun k i j hkij => ?_⟩
  · by_cases hk : k = 0
    · rw [homMultA0, ite_eq_left hk, norm_zero]; have := hA k; positivity
    · rw [homMultA0, ite_eq_right hk]
      have := norm_homInv_le_div hα one_pos k (hH.d0 ξ hξ k hk)
      rw [div_one] at this; rw [one_mul]; exact this
  · have hj := one_le_natCast_pnat j
    refine (norm_homInv_le_div hα (by positivity) k (hH.dp ξ hξ k j)).trans ?_
    rw [one_mul]; exact div_le_self (div_nonneg (hA k).le hα.le) hj
  · have hj := one_le_natCast_pnat j
    refine (norm_homInv_le_div hα (by positivity) k (hH.dm ξ hξ k j)).trans ?_
    rw [one_mul]; exact div_le_self (div_nonneg (hA k).le hα.le) hj
  · exact norm_homModDQ_off_le hα hβ0 hβ hH hξ k hij i (Or.inl rfl)
  · exact norm_homModDQ_diag_le hα hc hH hξ k i
  · have hji : j ≠ i := Ne.symm hij
    have := norm_homModDQ_off_le (a := a) (p := p) (pb := pb) hα hβ0 hβ hH hξ k hji i (Or.inr rfl)
    rwa [abs_sub_comm] at this
  · exact norm_homModDQ_diag_le hα hc hH hξ k i
  · exact ne_zero_of_lower (homMelnikovMod_pos_of hα one_pos k) (hH.d0 ξ hξ k hk)
  · exact ne_zero_of_lower (homMelnikovMod_pos_of hα (by have := one_le_natCast_pnat j; linarith)
      k) (hH.dp ξ hξ k j)
  · exact ne_zero_of_lower (homMelnikovMod_pos_of hα (by have := one_le_natCast_pnat j; linarith)
      k) (hH.dm ξ hξ k j)
  · exact ne_zero_of_lower (homMelnikovMod_pos_of hα
      (by have := one_le_natCast_pnat i; have := one_le_natCast_pnat j; linarith) k)
      (hH.dP ξ hξ k i j)
  · exact ne_zero_of_lower (homMelnikovMod_pos_of hα
      (by have := one_le_natCast_pnat i; have := one_le_natCast_pnat j; linarith) k)
      (hH.dP' ξ hξ k i j)
  · by_cases hij : i = j
    · subst hij
      have hk : k ≠ 0 := hkij.resolve_right (fun h => h rfl)
      exact ne_zero_of_lower (homMelnikovMod_pos_of hα one_pos k) (hH.dQd ξ hξ k hk i)
    · have hx0 := min_add_two_pos i j
      have hw : 0 < |(i : ℝ) - j| / (min (i : ℝ) j + 2) ^ β :=
        div_pos (abs_sub_pnat_pos hij) (Real.rpow_pos_of_pos hx0 β)
      exact ne_zero_of_lower (homMelnikovMod_pos_of hα hw k) (homModQ_lower hH hξ k hij)

end derive

section lip

variable {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {M0 Mω MΩ τ α β : ℝ}

/-- Lipschitz bound of `1/(iδ)` for a divisor with weight `w ≥ 1` (step `divlip`). -/
theorem norm_homInv_sub_le_weight {w δ₁ δ₂ M d : ℝ} (hα : 0 < α) (hM : 0 ≤ M) (hd : 0 ≤ d)
    (hw : 1 ≤ w) (k : Fin 2 → ℤ) (h1 : α * w / waveA τ k ≤ |δ₁|) (h2 : α * w / waveA τ k ≤ |δ₂|)
    (hD : |δ₁ - δ₂| ≤ 2 * (1 + Fourier.modeSize k) * M * d) :
    ‖homInv δ₁ - homInv δ₂‖ ≤ homLipC τ α M d k / w :=
  (norm_homInv_sub_le_of_lower (homMelnikovMod_pos_of hα (by linarith) k) h1 h2 hD).trans
    (homLipC_div_sq_le hα hM hd hw k)

/-- The twisted `Q` multipliers are Lipschitz with `homLipC/|i-j|` off the diagonal, when
`2β ≤ p+1-p₊` (step `m-lip`). -/
theorem norm_homModDQ_sub_off_le {a p pb : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hα : 0 < α)
    (hβ0 : 0 ≤ β) (h2β : 2 * β ≤ p + 1 - pb) (hH : HomMelnikovMod τ α β Par ω Ω)
    {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (hζ : ζ ∈ Par) (k : Fin 2 → ℤ) {i j : ℕ+} (hij : i ≠ j)
    (i' : ℕ+) (hi' : i' = i ∨ i' = j) :
    ‖(homModRatio a p pb i' : ℂ) * homDQ (ω ξ) (Ω ξ) k i j -
        (homModRatio a p pb i' : ℂ) * homDQ (ω ζ) (Ω ζ) k i j‖ ≤
      homLipC τ α (Mω + MΩ) ‖ξ - ζ‖ k / |(i : ℝ) - (j : ℝ)| := by
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  have hM : 0 ≤ Mω + MΩ := by linarith [h.consts_nonneg.2.1, h.consts_nonneg.2.2]
  have hd := norm_nonneg (ξ - ζ)
  have hx0 := min_add_two_pos i j
  have hxβ : 0 < (min (i : ℝ) j + 2) ^ β := Real.rpow_pos_of_pos hx0 β
  have hab := abs_sub_pnat_pos hij
  have hab1 := one_le_abs_sub_pnat hij
  have hw : 0 < |(i : ℝ) - j| / (min (i : ℝ) j + 2) ^ β := div_pos hab hxβ
  have hnot : ¬(k = 0 ∧ i = j) := fun h => hij h.2
  rw [homDQ, homDQ, ite_eq_right hnot, ite_eq_right hnot, ← mul_sub, norm_mul]
  have hD : |homDeltaQ (ω ξ) (Ω ξ) k i j - homDeltaQ (ω ζ) (Ω ζ) k i j| ≤
      2 * (1 + Fourier.modeSize k) * (Mω + MΩ) * ‖ξ - ζ‖ := by
    have := homDiv_sub_le h hξ hζ k i j 1 (-1) (by norm_num) (by norm_num)
    refine le_trans (le_of_eq ?_) this
    unfold homDeltaQ; congr 1; ring
  have h1 := norm_homInv_sub_le_of_lower (homMelnikovMod_pos_of hα hw k)
    (homModQ_lower hH hξ k hij) (homModQ_lower hH hζ k hij) hD
  have hsq : ((min (i : ℝ) j + 2) ^ β) ^ 2 = (min (i : ℝ) j + 2) ^ (2 * β) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; ring_nf
  have hr : homModRatio a p pb i' * (min (i : ℝ) j + 2) ^ (2 * β) ≤ 1 := by
    refine homModRatio_mul_rpow_le (by linarith) h2β i' hx0 ?_
    rcases hi' with rfl | rfl
    · linarith [min_le_left (i' : ℝ) j]
    · linarith [min_le_right (i : ℝ) i']
  have hρ : ‖(homModRatio a p pb i' : ℂ)‖ = homModRatio a p pb i' := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (homModRatio_pos a p pb i')]
  rw [hρ]
  have hL : 2 * (1 + Fourier.modeSize k) * (Mω + MΩ) * ‖ξ - ζ‖ /
      (α * (|(i : ℝ) - j| / (min (i : ℝ) j + 2) ^ β) / waveA τ k) ^ 2 =
      homLipC τ α (Mω + MΩ) ‖ξ - ζ‖ k / |(i : ℝ) - j| / |(i : ℝ) - j| *
        (min (i : ℝ) j + 2) ^ (2 * β) := by
    rw [← hsq]; unfold homLipC; field_simp
  rw [hL] at h1
  have hC := homLipC_nonneg (τ := τ) (α := α) hM hd k
  have hρ0 := (homModRatio_pos a p pb i').le
  calc homModRatio a p pb i' * ‖homInv (homDeltaQ (ω ξ) (Ω ξ) k i j) -
        homInv (homDeltaQ (ω ζ) (Ω ζ) k i j)‖
      ≤ homModRatio a p pb i' * (homLipC τ α (Mω + MΩ) ‖ξ - ζ‖ k / |(i : ℝ) - j| /
          |(i : ℝ) - j| * (min (i : ℝ) j + 2) ^ (2 * β)) := mul_le_mul_of_nonneg_left h1 hρ0
    _ = (homModRatio a p pb i' * (min (i : ℝ) j + 2) ^ (2 * β)) *
          (homLipC τ α (Mω + MΩ) ‖ξ - ζ‖ k / |(i : ℝ) - j| / |(i : ℝ) - j|) := by ring
    _ ≤ 1 * (homLipC τ α (Mω + MΩ) ‖ξ - ζ‖ k / |(i : ℝ) - j| / |(i : ℝ) - j|) :=
        mul_le_mul_of_nonneg_right hr (by positivity)
    _ ≤ _ := by rw [one_mul]; exact div_le_self (by positivity) hab1

/-- The Lipschitz bound of `1/(iδ⁰_k)` (zero for `k = 0`). -/
theorem norm_homMultA0_sub_le_mod (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hα : 0 < α)
    (hH : HomMelnikovMod τ α β Par ω Ω) {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (hζ : ζ ∈ Par)
    (k : Fin 2 → ℤ) :
    ‖homMultA0 (ω ξ) k - homMultA0 (ω ζ) k‖ ≤ homLipC τ α (Mω + MΩ) ‖ξ - ζ‖ k := by
  have hM : 0 ≤ Mω + MΩ := by linarith [h.consts_nonneg.2.1, h.consts_nonneg.2.2]
  have hd := norm_nonneg (ξ - ζ)
  by_cases hk : k = 0
  · rw [homMultA0, homMultA0, ite_eq_left hk, ite_eq_left hk, sub_self, norm_zero]
    exact homLipC_nonneg hM hd k
  · rw [homMultA0, homMultA0, ite_eq_right hk, ite_eq_right hk]
    have hD : |homDelta0 (ω ξ) k - homDelta0 (ω ζ) k| ≤
        2 * (1 + Fourier.modeSize k) * (Mω + MΩ) * ‖ξ - ζ‖ := by
      have := homDiv_sub_le h hξ hζ k 1 1 0 0 (by norm_num) (by norm_num)
      refine le_trans (le_of_eq ?_) this
      unfold homDelta0; congr 1; ring
    have := norm_homInv_sub_le_weight hα hM hd le_rfl k (hH.d0 ξ hξ k hk) (hH.d0 ζ hζ k hk) hD
    rwa [div_one] at this

/-- The diagonal of the twisted `Q` multipliers is Lipschitz with `homLipC`. -/
theorem norm_homModDQ_sub_diag_le {a p pb : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hα : 0 < α)
    (hc : pb ≤ p + 1) (hH : HomMelnikovMod τ α β Par ω Ω) {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par)
    (hζ : ζ ∈ Par) (k : Fin 2 → ℤ) (i : ℕ+) :
    ‖(homModRatio a p pb i : ℂ) * homDQ (ω ξ) (Ω ξ) k i i -
        (homModRatio a p pb i : ℂ) * homDQ (ω ζ) (Ω ζ) k i i‖ ≤
      homLipC τ α (Mω + MΩ) ‖ξ - ζ‖ k := by
  have hM : 0 ≤ Mω + MΩ := by linarith [h.consts_nonneg.2.1, h.consts_nonneg.2.2]
  have hd := norm_nonneg (ξ - ζ)
  rw [← mul_sub, norm_mul]
  have hC := homLipC_nonneg (τ := τ) (α := α) hM hd k
  refine (mul_le_mul_of_nonneg_right (norm_homModRatio_le hc i) (norm_nonneg _)).trans ?_
  rw [one_mul]
  by_cases hk : k = 0
  · rw [homDQ, homDQ, ite_eq_left ⟨hk, rfl⟩, ite_eq_left ⟨hk, rfl⟩, sub_self, norm_zero]
    exact hC
  · rw [homDQ, homDQ, ite_eq_right (fun h => hk h.1), ite_eq_right (fun h => hk h.1)]
    have hD : |homDeltaQ (ω ξ) (Ω ξ) k i i - homDeltaQ (ω ζ) (Ω ζ) k i i| ≤
        2 * (1 + Fourier.modeSize k) * (Mω + MΩ) * ‖ξ - ζ‖ := by
      have := homDiv_sub_le h hξ hζ k i i 1 (-1) (by norm_num) (by norm_num)
      refine le_trans (le_of_eq ?_) this
      unfold homDeltaQ; congr 1; ring
    have := norm_homInv_sub_le_weight hα hM hd le_rfl k (hH.dQd ξ hξ k hk i) (hH.dQd ζ hζ k hk i)
      hD
    rwa [div_one] at this

/-- **The Lipschitz bounds of the division operators** (`bpW:w5:w4-modified`, step `m-lip`),
from the source premises, when `2β ≤ p+1-p₊`. -/
theorem homModMultLip_of {a p pb : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hα : 0 < α)
    (hβ0 : 0 ≤ β) (h2β : 2 * β ≤ p + 1 - pb) (hH : HomMelnikovMod τ α β Par ω Ω)
    {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (hζ : ζ ∈ Par) :
    HomModMultLip a p pb τ α (Mω + MΩ) ‖ξ - ζ‖ (ω ξ) (Ω ξ) (ω ζ) (Ω ζ) := by
  have hM : 0 ≤ Mω + MΩ := by linarith [h.consts_nonneg.2.1, h.consts_nonneg.2.2]
  have hd := norm_nonneg (ξ - ζ)
  have hc : pb ≤ p + 1 := by linarith
  have hC := fun k => homLipC_nonneg (τ := τ) (α := α) hM hd k
  refine ⟨norm_homMultA0_sub_le_mod h hα hH hξ hζ, fun k j => ?_, fun k j => ?_, fun k => ?_,
    fun k => ?_, fun k => ⟨fun i j hij => ?_, fun i => ?_⟩, fun k => ⟨fun i j hij => ?_,
    fun i => ?_⟩⟩
  · have hj := one_le_natCast_pnat j
    have hD : |homDeltaPlus (ω ξ) (Ω ξ) k j - homDeltaPlus (ω ζ) (Ω ζ) k j| ≤
        2 * (1 + Fourier.modeSize k) * (Mω + MΩ) * ‖ξ - ζ‖ := by
      have := homDiv_sub_le h hξ hζ k j j (-1) 0 (by norm_num) (by norm_num)
      refine le_trans (le_of_eq ?_) this
      unfold homDeltaPlus; congr 1; ring
    exact (norm_homInv_sub_le_weight hα hM hd hj k (hH.dp ξ hξ k j) (hH.dp ζ hζ k j) hD).trans
      (div_le_self (hC k) hj)
  · have hj := one_le_natCast_pnat j
    have hD : |homDeltaMinus (ω ξ) (Ω ξ) k j - homDeltaMinus (ω ζ) (Ω ζ) k j| ≤
        2 * (1 + Fourier.modeSize k) * (Mω + MΩ) * ‖ξ - ζ‖ := by
      have := homDiv_sub_le h hξ hζ k j j 1 0 (by norm_num) (by norm_num)
      refine le_trans (le_of_eq ?_) this
      unfold homDeltaMinus; congr 1; ring
    exact (norm_homInv_sub_le_weight hα hM hd hj k (hH.dm ξ hξ k j) (hH.dm ζ hζ k j) hD).trans
      (div_le_self (hC k) hj)
  · refine homHadamardBound_of_weight (hC k) (fun i j => (i : ℝ) + j) ?_ ?_ ?_
    · intro i j _
      have := one_le_natCast_pnat i; have := one_le_natCast_pnat j
      rw [abs_le]; constructor <;> linarith
    · intro i j; have := one_le_natCast_pnat i; have := one_le_natCast_pnat j; linarith
    · intro i j
      have := one_le_natCast_pnat i; have := one_le_natCast_pnat j
      have hD : |homDeltaP (ω ξ) (Ω ξ) k i j - homDeltaP (ω ζ) (Ω ζ) k i j| ≤
          2 * (1 + Fourier.modeSize k) * (Mω + MΩ) * ‖ξ - ζ‖ := by
        have := homDiv_sub_le h hξ hζ k i j (-1) (-1) (by norm_num) (by norm_num)
        refine le_trans (le_of_eq ?_) this
        unfold homDeltaP; congr 1; ring
      exact norm_homInv_sub_le_weight hα hM hd (by linarith) k (hH.dP ξ hξ k i j)
        (hH.dP ζ hζ k i j) hD
  · refine homHadamardBound_of_weight (hC k) (fun i j => (i : ℝ) + j) ?_ ?_ ?_
    · intro i j _
      have := one_le_natCast_pnat i; have := one_le_natCast_pnat j
      rw [abs_le]; constructor <;> linarith
    · intro i j; have := one_le_natCast_pnat i; have := one_le_natCast_pnat j; linarith
    · intro i j
      have := one_le_natCast_pnat i; have := one_le_natCast_pnat j
      have hD : |homDeltaP' (ω ξ) (Ω ξ) k i j - homDeltaP' (ω ζ) (Ω ζ) k i j| ≤
          2 * (1 + Fourier.modeSize k) * (Mω + MΩ) * ‖ξ - ζ‖ := by
        have := homDiv_sub_le h hξ hζ k i j 1 1 (by norm_num) (by norm_num)
        refine le_trans (le_of_eq ?_) this
        unfold homDeltaP'; congr 1; ring
      exact norm_homInv_sub_le_weight hα hM hd (by linarith) k (hH.dP' ξ hξ k i j)
        (hH.dP' ζ hζ k i j) hD
  · exact norm_homModDQ_sub_off_le h hα hβ0 h2β hH hξ hζ k hij i (Or.inl rfl)
  · exact norm_homModDQ_sub_diag_le h hα hc hH hξ hζ k i
  · have := norm_homModDQ_sub_off_le (a := a) (p := p) (pb := pb) h hα hβ0 h2β hH hξ hζ k
      (Ne.symm hij) i (Or.inr rfl)
    rwa [abs_sub_comm] at this
  · exact norm_homModDQ_sub_diag_le h hα hc hH hξ hζ k i

end lip

end KAM.Wave
