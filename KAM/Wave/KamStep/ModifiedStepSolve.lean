/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepSolve
public import KAM.Wave.Homological.ModifiedLipField
public import KAM.Wave.Homological.ModifiedEquation
public import KAM.Wave.Homological.ModifiedReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W4 with modified divisors on the phase space of W5 (`bpW:w5:w4-modified`)

The solve outputs of `bpW:w5:w4-modified` on `KamPhase`, in the form consumed by the step
(compare `stepSolve_fam`, `stepSolve_equation` for unmodified divisors):
* `stepSolveMod_fieldBound`: (i) `|X_F|_{p₊,r} ≤ C₁B^W_σ ε/α` on `D(s-σ,r)`;
* `stepSolveMod_fam`: (ii) for `0 ≤ λ ≤ α/M`, `|X_F|^λ_{r,D(s-σ,r)} ≤ (3C₁B^♮_σ/α)(ε + λε^L)`
  as a `FamBound` (when `2β ≤ p+1-p₊`);
* `stepSolveMod_equation`: (i) the equation `R + DN·X_F = N̂ + â₀` under the guard
  (`bpW:w4:lemma1` (ii), third form), with `X_F` in the `p₊`-target;
* (iii) is `waveBN_le` (`KAM.Wave.KamStep.LatticeBN`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

section Fam

variable {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {M0 Mω MΩ τ α β : ℝ}

/-- **`bpW:w5:w4-modified` (i), field bound on `KamPhase`**: `|X_F|_{p₊,r} ≤ C₁B^W_σ ε/α` on
`D(s-σ,r)`. -/
theorem stepSolveMod_fieldBound (hH : HomMelnikovMod τ α β Par ω Ω) (hβ0 : 0 ≤ β)
    (hβ : β ≤ p + 1 - pb) (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε σ : ℝ} (hr : 0 < r)
    (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par)
    (R : HomTaylor_gen a p (p + 1) s) (hX : HomFieldBound_gen ha hp (homModPP1 p) r ε R)
    {w : KamPhase} (hw : w ∈ kamDomain (s - σ) r) :
    kamNorm r (stepField ha hp hpb (homModSolveTaylor hτ hα hσ hσs (homMod_pb_le hβ0 hβ)
        (homModMultBounds_of hα hβ0 hβ hH hξ) R) w) ≤
      (7 + 10 * homKS) * (waveBW τ σ * ε / α) := by
  rw [kamNorm_stepField ha hp hpb _ hr]
  exact homModLemma_fieldBound hH hβ0 hβ ha hp hpb hr hτ hα hσ hσs hξ R hX _ _ _ _
    (homDomain_stepZ hw)

/-- **`bpW:w5:w4-modified` (ii), `λ`-form on `KamPhase`**: for the family `F_ξ` of solutions with
modified divisors for a family `R_ξ ∈ 𝒯_s` (`p̄ = p+1`) with `|X_{R_ξ}|_{p+1,r} ≤ ε` and
`|X_{R_ξ} - X_{R_ζ}|_{p+1,r} ≤ ε^L|ξ-ζ|`, `2β ≤ p+1-p₊` and `0 ≤ λ ≤ α/M`:
`|X_F|^λ_{r,D(s-σ,r)} ≤ (3C₁B^♮_σ/α)(ε + λε^L)` in the `p₊` norm. -/
theorem stepSolveMod_fam (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hH : HomMelnikovMod τ α β Par ω Ω)
    (hβ0 : 0 ≤ β) (h2β : 2 * β ≤ p + 1 - pb) (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    {r ε εL lam σ : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσs : σ < s) (hM : 0 < Mω + MΩ) (hlam0 : 0 ≤ lam) (hlam : lam ≤ α / (Mω + MΩ))
    (hε : 0 ≤ ε) (hεL : 0 ≤ εL) (R : (Fin 2 → ℝ) → HomTaylor_gen a p (p + 1) s)
    (F : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ))
    (hF : ∀ ξ (hξ : ξ ∈ Par), F ξ = homModSolveTaylor hτ hα hσ hσs
      (homMod_pb_le hβ0 (homMod_beta_le hβ0 h2β))
      (homModMultBounds_of hα hβ0 (homMod_beta_le hβ0 h2β) hH hξ) (R ξ))
    (hR : ∀ ξ ∈ Par, HomFieldBound_gen ha hp (homModPP1 p) r ε (R ξ))
    (hRL : ∀ ξ ∈ Par, ∀ ζ ∈ Par,
      HomFieldBound_gen ha hp (homModPP1 p) r (εL * ‖ξ - ζ‖) ((R ξ).homSub (R ζ))) :
    FamBound Par (kamDomain (s - σ) r) r lam
      (3 * (7 + 10 * homKS) * waveBN τ σ / α * (ε + lam * εL))
      (fun ξ w => stepField ha hp hpb (F ξ) w) := by
  have hB := waveBW_nonneg τ σ
  have hBN := hB.trans (waveBW_le_waveBN hτ hσ)
  have hK1 := one_le_homKS
  refine ⟨(7 + 10 * homKS) * (waveBW τ σ * ε / α),
    (7 + 10 * homKS) * (waveBN τ σ / α * (εL + 2 * (Mω + MΩ) * ε / α)), by positivity,
    by positivity, ?_, ?_, ?_⟩
  · have := (homModLemma2 (α := α) (M := Mω + MΩ) (lam := lam) (σ := σ) (ε := ε) (εL := εL) hτ hα
      hM hlam0 hlam hσ hσ1 hε hεL).1
    unfold homLamNorm at this
    exact this
  · intro ξ hξ w hw
    show kamNorm r (stepField ha hp hpb (F ξ) w) ≤ _
    rw [hF ξ hξ]
    exact stepSolveMod_fieldBound hH hβ0 (homMod_beta_le hβ0 h2β) ha hp hpb hr hτ hα hσ hσs hξ
      (R ξ) (hR ξ hξ) hw
  · intro ξ hξ ζ hζ w hw
    have hb := homModLemma_lipschitz h hH hβ0 h2β ha hp hpb hr hτ hα hεL hσ hσs hξ hζ (R ξ) (R ζ)
      (hR ξ hξ) (hR ζ hζ) (hRL ξ hξ ζ hζ)
    rw [← hF ξ hξ, ← hF ζ hζ] at hb
    have hθ : w.1 ∈ complexStrip 2 (s - σ) := fun i => hw.1 i
    rw [← stepField_sub ha hp hpb _ _ hθ, kamNorm_stepField ha hp hpb _ hr]
    have := hb _ _ _ _ (homDomain_stepZ hw)
    refine this.trans (le_of_eq ?_)
    ring

end Fam

section Equation

variable {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {M0 Mω MΩ τ α β : ℝ}

/-- **`bpW:w5:w4-modified` (i), the equation on `KamPhase`** (`R + DN·X_F = N̂ + â₀`, from
`homModLemma_equation_all` and `bpW:w4:lie` (iv)): at every `w` with `θ ∈ T_{s-σ}`,
`R(w) + DN(w)(ι X_F(w)) = N̂(w) + â₀`, with `R`, `N̂` in the class `p̄ = p+1` and `X_F` in the
`p₊`-target. -/
theorem stepSolveMod_equation (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hH : HomMelnikovMod τ α β Par ω Ω) (hβ0 : 0 ≤ β) (hβ : β ≤ p + 1 - pb) (ha : 0 ≤ a)
    (hp : 0 ≤ p) (hpb : p ≤ pb) (hp1 : 1 ≤ p + pb) {γ : ℝ} (hG : HomGuard a p γ) {r : ℝ}
    (hr : 0 < r) {ε : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) {σ : ℝ} (hσ : 0 < σ) (hσs : σ < s)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (R : HomTaylor_gen a p (p + 1) s)
    (hX : HomFieldBound_gen ha hp (homModPP1 p) r ε R) {w : KamPhase}
    (hw : w.1 ∈ complexStrip 2 (s - σ)) :
    waveStepFun ha (homPP hp (homModPP1 p)) R w +
        ((homDN hG (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le h hξ) (ω ξ)
            (stepToHom w)).comp stepToHom)
          (kamHomEmbed a p pb hpb (stepField ha hp hpb
            (homModSolveTaylor hτ hα hσ hσs (homMod_pb_le hβ0 hβ)
              (homModMultBounds_of hα hβ0 hβ hH hξ) R) w)) =
      waveStepFun ha (homPP hp (homModPP1 p)) (homNhatTaylor_gen R) w + homCoeff R.a0 0 := by
  rw [stepNfun_lie hG (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le h hξ) (ω ξ)
    ha hp hpb]
  have heq := homModLemma_equation_all h hH hβ0 hβ ha hp hpb hp1 hr hτ hα hσ hσs hξ R hX hw w.2.1
    (stepZ w) (stepZb w)
  rw [stepFun_eq_homRval ha hp (homModPP1 p), stepFun_eq_homRval ha hp (homModPP1 p),
    homNhatTaylor_val_gen ha hp (homModPP1 p)]
  linear_combination -heq

end Equation

end KAM.Wave
