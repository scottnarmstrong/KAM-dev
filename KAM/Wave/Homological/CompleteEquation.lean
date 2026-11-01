/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.CompleteLieExpand
import Mathlib.Tactic.Linarith

/-!
# Lemma 1 (ii): the bracket and the guarded forms of the homological equation

Off-frontier, source-faithful infrastructure (W4-COMPLETE); the dependency graph is still
being built. Blueprint label: `bpW:w4:lemma1` (ii), step `stepW:w4:equation` (second and third
forms), with `bpW:w4:lie` (ii), (iv).

The landed W4 export `homLemma1_equation_all_gen` is the first form `L_N F + N̂ = R - â₀` on
`T_{s-σ} × ℂ² × (ℓ^N_{a,p})²`. Here:

* `homWeakBracketN_gen`: the weak bracket `⟨⟨N,F⟩⟩(θ,y,z,\bar z)` of `bpW:w4:lie` for a Taylor
  Hamiltonian `F`, i.e. the sequence-level `homWeakBracket` applied to
  `(1/2π)⟨ω,F_θ⟩`, the true gradients `F_z, F_{\bar z}` and `Ωz, Ω\bar z` (true coordinates);
  `homWeakBracketN_eq_neg_lieN_gen`: `⟨⟨N,F⟩⟩ = -L_N F` (`bpW:w4:lie` (ii));
* `homHamField_gen`: the Hamiltonian field
  `X_F = ((1/2π)F_y, -(1/2π)F_θ, -iF_{\bar z}, iF_z)` on the phase space `HomPhase`
  (`(θ, y, z, \bar z)` slots; the normal components embedded `ℓ^N_{a,p_+} ⊂ ℓ^N_{a,p}`);
  `homDN_hamField_gen`: under the guard (G), `DN(w)·X_F(w) = -L_N F(w)` (`bpW:w4:lie` (iv));
* `homLemma1Complete_bracket_gen`: `R + ⟨⟨N,F⟩⟩ = N̂ + â₀`;
* `homLemma1Complete_guarded_gen`: under (G), `R + DN·X_F = N̂ + â₀`;
* `homLemma1Complete_equation_gen`: the three forms of (ii) together;
* the same at `p_+ = p + 1` (the original W4 setting): `homLemma1Complete_bracket`,
  `homLemma1Complete_guarded`, `homLemma1Complete_equation`.

All are stated from the source premises of Theorem `bpW:w4:lemma1` (`HomFreqHyp`,
`HomMelnikov`, positivity, `ξ ∈ Π`, `|X_R|_r ≤ ε`); the general-`p_+` versions also take
`1 ≤ p + p_+` (automatic at `p_+ = p + 1`), as `homLemma1_equation_all_gen` does.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

/-- The carrier evidence in true coordinates: `∑_j c_j (Ω_j z_j)` converges. -/
theorem homOmegaCarrier_true (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {W : ℕ+ → ℝ}
    (hC : HomOmegaCarrier ha hp hpb W) (c z : HomL2) :
    Summable fun j => homTrueCoord a pb c j * ((W j : ℂ) * homTrueCoord a p z j) :=
  (hC c z).congr fun j => by
    linear_combination (-(W j : ℂ)) * homTrueCoord_mul_eq ha hp hpb c z j

/-- **The weak bracket `⟨⟨N,F⟩⟩`** (`bpW:w4:lie`) of a Taylor Hamiltonian `F` at
`(θ, y, z, \bar z)`: `-(1/2π)⟨ω,F_θ⟩ + ⟨Ω\bar z, Ż⟩₀ + ⟨Ωz, \dot{\bar Z}⟩₀`,
`(Ż, \dot{\bar Z}) = (-iF_{\bar z}, iF_z)`, i.e. the sequence-level `homWeakBracket` of the true
gradients and of `Ωz, Ω\bar z`; the pairings converge by the carrier evidence `hC`. -/
def homWeakBracketN_gen (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {W : ℕ+ → ℝ}
    (hC : HomOmegaCarrier ha hp hpb W) (w : Fin 2 → ℝ) (F : HomTaylor_gen a p pb s)
    (θ y : Fin 2 → ℂ) (z zb : HomL2) : ℂ :=
  homWeakBracket ((2 * Real.pi : ℂ)⁻¹ * ∑ l, (w l : ℂ) * homRtheta_gen ha hp hpb F l θ y z zb)
    (fun j => homTrueCoord a pb (homRz_gen F θ z zb) j)
    (fun j => homTrueCoord a pb (homRzb_gen F θ z zb) j)
    (fun j => (W j : ℂ) * homTrueCoord a p z j) (fun j => (W j : ℂ) * homTrueCoord a p zb j)
    (homOmegaCarrier_true ha hp hpb hC _ z) (homOmegaCarrier_true ha hp hpb hC _ zb)

/-- **`⟨⟨N,F⟩⟩ = -L_N F`** (`bpW:w4:lie` (ii)) for a Taylor Hamiltonian `F`, at every point. -/
theorem homWeakBracketN_eq_neg_lieN_gen (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {W : ℕ+ → ℝ}
    (hC : HomOmegaCarrier ha hp hpb W) (w : Fin 2 → ℝ) (F : HomTaylor_gen a p pb s)
    (θ y : Fin 2 → ℂ) (z zb : HomL2) :
    homWeakBracketN_gen ha hp hpb hC w F θ y z zb = -homLieN_gen ha hp hpb hC w F θ y z zb := by
  unfold homWeakBracketN_gen
  rw [homWeakBracket_eq_neg_lieN, homLieN_gen_eq]
  unfold homLieSeq homPair0 homPair0Raw homPairOmega_gen homPairOmegaRaw_gen
  have e : ∀ c x : HomL2, (∑' j, homTrueCoord a pb c j * ((W j : ℂ) * homTrueCoord a p x j)) =
      ∑' j, homLamDiag_gen ha (homPP hp hpb) c j * (W j : ℂ) * x j := fun c x =>
    tsum_congr fun j => by
      linear_combination (W j : ℂ) * homTrueCoord_mul_eq ha hp hpb c x j
  rw [e, e]

/-- **The Hamiltonian field** `X_F = ((1/2π)F_y, -(1/2π)F_θ, Ż, \dot{\bar Z})`,
`(Ż, \dot{\bar Z}) = (-iF_{\bar z}, iF_z)` (`bpW:w4:taylor`, `bpW:w4:hameq`), as a vector of the
phase space `HomPhase = ℂ² × ℂ² × ℓ^N_{a,p} × ℓ^N_{a,p}` (slots `(θ, y, z, \bar z)`; the normal
components `∈ ℓ^N_{a,p_+}` embedded in `ℓ^N_{a,p}` by `homEmbed_gen`). -/
def homHamField_gen (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (F : HomTaylor_gen a p pb s)
    (θ y : Fin 2 → ℂ) (z zb : HomL2) : HomPhase :=
  ((2 * Real.pi : ℂ)⁻¹ • homRy_gen F θ,
    (fun i => -(2 * Real.pi : ℂ)⁻¹ * homRtheta_gen ha hp hpb F i θ y z zb),
    (-Complex.I) • homEmbed_gen a p pb hpb (homRzb_gen F θ z zb),
    Complex.I • homEmbed_gen a p pb hpb (homRz_gen F θ z zb))

/-- **`DN(w)·X_F(w) = -L_N F(w)`** (`bpW:w4:lie` (iv)) for the full field `X_F` (the
`θ`-component does not enter since `N` is independent of `θ`). -/
theorem homDN_hamField_gen {γ K0 : ℝ} {Ω : ℕ+ → ℝ} (hG : HomGuard a p γ) (hK0 : 0 ≤ K0)
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (ω : Fin 2 → ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p)
    (hpb : p ≤ pb) (F : HomTaylor_gen a p pb s) (θ y : Fin 2 → ℂ) (z zb : HomL2) :
    homDN hG hK0 hΩ ω (θ, y, z, zb) (homHamField_gen ha hp hpb F θ y z zb) =
      -homLieN_gen ha hp hpb (homOmegaCarrier_of_guard (γ := γ) ha hp hpb hG hK0 hΩ) ω F θ y z
        zb := by
  rw [← homLemma_lie_iv_gen hG hK0 hΩ ω ha hp hpb F θ y z zb, homDN_apply, homDN_apply]
  rfl

section source

variable {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {M0 Mω MΩ σ τ α : ℝ}

/-- **Lemma 1 (ii), bracket form** (`bpW:w4:lemma1` (ii), step `stepW:w4:equation`; general
`p_+`, from the source premises): `R + ⟨⟨N,F⟩⟩ = N̂ + â₀` on `T_{s-σ} × ℂ² × (ℓ^N_{a,p})²`, for any
carrier evidence of the pairings of the weak bracket. -/
theorem homLemma1Complete_bracket_gen (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hH : HomMelnikov τ α Par ω Ω) (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hp1 : 1 ≤ p + pb)
    {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (R : HomTaylor_gen a p pb s)
    (hX : HomFieldBound_gen ha hp hpb r ε R) (hC : HomOmegaCarrier ha hp hpb (Ω ξ))
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ)) (y : Fin 2 → ℂ) (z zb : HomL2) :
    homRval_gen ha hp hpb R θ y z zb + homWeakBracketN_gen ha hp hpb hC (ω ξ)
        (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) θ y z zb =
      homNhat_gen R y z zb + homCoeff R.a0 0 := by
  rw [homWeakBracketN_eq_neg_lieN_gen]
  have heq := homLemma1_equation_all_gen h hH ha hp hpb hp1 hr hτ hα hσ hσs hξ R hX hθ y z zb
  have e : homLieN_gen ha hp hpb hC (ω ξ)
      (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) θ y z zb =
    homLieN_gen ha hp hpb (homOmegaCarrier_of_bound ha hp hpb hp1
      (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le h hξ)) (ω ξ)
      (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) θ y z zb := rfl
  rw [e]
  linear_combination -heq

/-- **Lemma 1 (ii), guarded form** (`bpW:w4:lemma1` (ii), step `stepW:w4:equation`; general
`p_+`, from the source premises): under the guard (G) (`HomGuard a p γ`),
`R + DN·X_F = N̂ + â₀` on `T_{s-σ} × ℂ² × (ℓ^N_{a,p})²`, with `DN(w)` the Fréchet derivative of
`N = ⟨ω(ξ),y⟩ + N_Ω(z,\bar z)` at `w = (θ,y,z,\bar z)` (`homNfun_hasFDerivAt`) and `X_F` the
Hamiltonian field of `F`. -/
theorem homLemma1Complete_guarded_gen (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hH : HomMelnikov τ α Par ω Ω) (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hp1 : 1 ≤ p + pb)
    {γ : ℝ} (hG : HomGuard a p γ) {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α)
    (hσ : 0 < σ) (hσs : σ < s) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (R : HomTaylor_gen a p pb s)
    (hX : HomFieldBound_gen ha hp hpb r ε R) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ))
    (y : Fin 2 → ℂ) (z zb : HomL2) :
    homRval_gen ha hp hpb R θ y z zb +
        homDN hG (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le h hξ) (ω ξ)
          (θ, y, z, zb) (homHamField_gen ha hp hpb
            (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) θ y z zb) =
      homNhat_gen R y z zb + homCoeff R.a0 0 := by
  rw [homDN_hamField_gen]
  have heq := homLemma1_equation_all_gen h hH ha hp hpb hp1 hr hτ hα hσ hσs hξ R hX hθ y z zb
  have e : homLieN_gen ha hp hpb (homOmegaCarrier_of_guard (γ := γ) ha hp hpb hG
      (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le h hξ)) (ω ξ)
      (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) θ y z zb =
    homLieN_gen ha hp hpb (homOmegaCarrier_of_bound ha hp hpb hp1
      (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le h hξ)) (ω ξ)
      (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) θ y z zb := rfl
  rw [e]
  linear_combination -heq

/-- **Lemma 1 (ii), all three forms** (`bpW:w4:lemma1` (ii); general `p_+`, from the source
premises), on `T_{s-σ} × ℂ² × (ℓ^N_{a,p})²`: `L_N F + N̂ = R - â₀`; equivalently
`R + ⟨⟨N,F⟩⟩ = N̂ + â₀`; and, under the guard (G), `R + DN·X_F = N̂ + â₀`. -/
theorem homLemma1Complete_equation_gen (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hH : HomMelnikov τ α Par ω Ω) (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hp1 : 1 ≤ p + pb)
    {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (R : HomTaylor_gen a p pb s)
    (hX : HomFieldBound_gen ha hp hpb r ε R) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ))
    (y : Fin 2 → ℂ) (z zb : HomL2) :
    homLieN_gen ha hp hpb
        (homOmegaCarrier_of_bound ha hp hpb hp1 (by linarith [h.consts_nonneg.1] :
          0 ≤ 1 + M0) (homOmega_le h hξ)) (ω ξ)
        (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) θ y z zb
      + homNhat_gen R y z zb = homRval_gen ha hp hpb R θ y z zb - homCoeff R.a0 0 ∧
    homRval_gen ha hp hpb R θ y z zb + homWeakBracketN_gen ha hp hpb
        (homOmegaCarrier_of_bound ha hp hpb hp1 (by linarith [h.consts_nonneg.1] :
          0 ≤ 1 + M0) (homOmega_le h hξ)) (ω ξ)
        (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) θ y z zb =
      homNhat_gen R y z zb + homCoeff R.a0 0 ∧
    ∀ {γ : ℝ} (hG : HomGuard a p γ),
      homRval_gen ha hp hpb R θ y z zb +
          homDN hG (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le h hξ) (ω ξ)
            (θ, y, z, zb) (homHamField_gen ha hp hpb
              (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) θ y z zb) =
        homNhat_gen R y z zb + homCoeff R.a0 0 :=
  ⟨homLemma1_equation_all_gen h hH ha hp hpb hp1 hr hτ hα hσ hσs hξ R hX hθ y z zb,
    homLemma1Complete_bracket_gen h hH ha hp hpb hp1 hr hτ hα hσ hσs hξ R hX _ hθ y z zb,
    fun hG => homLemma1Complete_guarded_gen h hH ha hp hpb hp1 hG hr hτ hα hσ hσs hξ R hX hθ y
      z zb⟩

/-- The weak bracket at `p_+ = p + 1`. -/
abbrev homWeakBracketN (ha : 0 ≤ a) (hp : 0 ≤ p) {W : ℕ+ → ℝ}
    (hC : HomOmegaCarrier ha hp (homPlusOne_le p) W) (w : Fin 2 → ℝ) (F : HomTaylor a p s)
    (θ y : Fin 2 → ℂ) (z zb : HomL2) : ℂ :=
  homWeakBracketN_gen ha hp (homPlusOne_le p) hC w F θ y z zb

/-- The Hamiltonian field at `p_+ = p + 1`. -/
abbrev homHamField (ha : 0 ≤ a) (hp : 0 ≤ p) (F : HomTaylor a p s) (θ y : Fin 2 → ℂ)
    (z zb : HomL2) : HomPhase :=
  homHamField_gen ha hp (homPlusOne_le p) F θ y z zb

/-- **Lemma 1 (ii), all three forms, `p_+ = p + 1`** (`bpW:w4:lemma1` (ii), step
`stepW:w4:equation`; the original W4 setting, from the source premises), on
`T_{s-σ} × ℂ² × (ℓ^N_{a,p})²`: `L_N F + N̂ = R - â₀`; equivalently `R + ⟨⟨N,F⟩⟩ = N̂ + â₀`;
and, under the guard (G) (in particular for `a = p = 1`, `homGuard_one_one`),
`R + DN·X_F = N̂ + â₀`. -/
theorem homLemma1Complete_equation (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hH : HomMelnikov τ α Par ω Ω) (ha : 0 ≤ a) (hp : 0 ≤ p) {r ε : ℝ} (hr : 0 < r)
    (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par)
    (R : HomTaylor a p s) (hX : HomFieldBound ha hp r ε R) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (s - σ)) (y : Fin 2 → ℂ) (z zb : HomL2) :
    homLieN_gen ha hp (homPlusOne_le p)
        (homOmegaCarrier_of_bound ha hp (homPlusOne_le p) (by linarith)
          (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le h hξ)) (ω ξ)
        (homSolveTaylor hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) θ y z zb
      + homNhat R y z zb = homRval ha hp R θ y z zb - homCoeff R.a0 0 ∧
    homRval ha hp R θ y z zb + homWeakBracketN ha hp
        (homOmegaCarrier_of_bound ha hp (homPlusOne_le p) (by linarith)
          (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le h hξ)) (ω ξ)
        (homSolveTaylor hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) θ y z zb =
      homNhat R y z zb + homCoeff R.a0 0 ∧
    ∀ {γ : ℝ} (hG : HomGuard a p γ),
      homRval ha hp R θ y z zb +
          homDN hG (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le h hξ) (ω ξ)
            (θ, y, z, zb) (homHamField ha hp
              (homSolveTaylor hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) θ y z zb) =
        homNhat R y z zb + homCoeff R.a0 0 :=
  homLemma1Complete_equation_gen h hH ha hp (homPlusOne_le p) (by linarith) hr hτ hα hσ hσs hξ R
    hX hθ y z zb

/-- **Lemma 1 (ii), bracket form, `p_+ = p + 1`** (`bpW:w4:lemma1` (ii)). -/
theorem homLemma1Complete_bracket (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hH : HomMelnikov τ α Par ω Ω) (ha : 0 ≤ a) (hp : 0 ≤ p) {r ε : ℝ} (hr : 0 < r)
    (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par)
    (R : HomTaylor a p s) (hX : HomFieldBound ha hp r ε R)
    (hC : HomOmegaCarrier ha hp (homPlusOne_le p) (Ω ξ)) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (s - σ)) (y : Fin 2 → ℂ) (z zb : HomL2) :
    homRval ha hp R θ y z zb + homWeakBracketN ha hp hC (ω ξ)
        (homSolveTaylor hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) θ y z zb =
      homNhat R y z zb + homCoeff R.a0 0 :=
  homLemma1Complete_bracket_gen h hH ha hp (homPlusOne_le p) (by linarith) hr hτ hα hσ hσs hξ R hX
    hC hθ y z zb

/-- **Lemma 1 (ii), guarded form, `p_+ = p + 1`** (`bpW:w4:lemma1` (ii)): under (G),
`R + DN·X_F = N̂ + â₀`. -/
theorem homLemma1Complete_guarded (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hH : HomMelnikov τ α Par ω Ω) (ha : 0 ≤ a) (hp : 0 ≤ p) {γ : ℝ} (hG : HomGuard a p γ)
    {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (R : HomTaylor a p s) (hX : HomFieldBound ha hp r ε R)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ)) (y : Fin 2 → ℂ) (z zb : HomL2) :
    homRval ha hp R θ y z zb +
        homDN hG (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le h hξ) (ω ξ)
          (θ, y, z, zb) (homHamField ha hp
            (homSolveTaylor hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) θ y z zb) =
      homNhat R y z zb + homCoeff R.a0 0 :=
  homLemma1Complete_guarded_gen h hH ha hp (homPlusOne_le p) (by linarith) hG hr hτ hα hσ hσs hξ
    R hX hθ y z zb

end source

end KAM.Wave
