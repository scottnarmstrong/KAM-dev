/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LemmaOneLipBounds
public import KAM.Wave.Homological.NhatTaylor
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# P96-K Lemma 1 for the wave setting (`bpW:w4:lemma1`)

Assembly of the statements of Theorem `bpW:w4:lemma1` from the earlier modules:

* (i) `homSolveTaylor_gen` (membership in `𝒯_{s-σ}`), `homLemma1_zero_modes_gen`;
* (ii) `homLemma1_equation_gen` (`L_N F + N̂ = R - â₀`, finitely supported `z, \bar z`);
* (iii) `homLemma1_fieldBound_gen`, `homLemma1_lipschitz_gen`;
* (iv) `homNhat_coeff_bounds_gen`, `homNhat_fieldBound_gen`, `homNhat_lipschitz_gen`.

`homLemma1_lipschitz_gen` and `homNhat_lipschitz_gen` bound the fields of the *difference* of the
solutions (resp. corrections) at two parameters; the field of `R(ξ) - R(ζ)` is
`X_{R(ξ)} - X_{R(ζ)}` since fields are linear in the components (`TaylorSub.lean`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s σ τ α M d : ℝ} {w₁ w₂ : Fin 2 → ℝ} {W₁ W₂ : ℕ+ → ℝ}

/-- Hypothesis-taking variant for Lemma 1 (iii), Lipschitz bound: assumes the gates `HomMultBounds`,
`HomMultLip`. The source-premise export is `homLemma1_lipschitz_gen`. -/
theorem homLemma1_lipschitz_of_gates_gen (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε εL : ℝ} (hr
  : 0 < r)
    (hτ
    : 0 ≤ τ)
    (hα : 0 < α) (hM : 0 ≤ M) (hd : 0 ≤ d) (hεL : 0 ≤ εL) (hσ : 0 < σ) (hσs : σ < s)
    (hm₁ : HomMultBounds τ α w₁ W₁) (hm₂ : HomMultBounds τ α w₂ W₂)
    (hL : HomMultLip τ α M d w₁ W₁ w₂ W₂) (R₁ R₂ : HomTaylor_gen a p pb s)
    (hX₁ : HomFieldBound_gen ha hp hpb r ε R₁) (hX₂ : HomFieldBound_gen ha hp hpb r ε R₂)
    (hXL : HomFieldBound_gen ha hp hpb r (εL * d) (R₁.homSub R₂)) :
    HomFieldBound_gen ha hp hpb r ((7 + 10 * homKS) * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d))
      ((homSolveTaylor_gen hτ hα hσ hσs hm₁ R₁).homSub (homSolveTaylor_gen hτ hα hσ hσs hm₂ R₂)) :=
          by
  intro θ y z zb hdom
  have hs : 0 < s := hσ.trans hσs
  have hε : 0 ≤ ε := by
    have hθ' : θ ∈ complexStrip 2 s := fun j => by have := hdom.1 j; linarith
    exact (homXnorm_nonneg_gen ha hp hpb hr R₁ θ 0 0 0).trans
      (hX₁ θ 0 0 0 (homDomain_y hθ' hr (by simpa using pow_pos hr 2)))
  have hE0 : 0 ≤ waveBW τ σ / α * (εL + 2 * M * ε / α) * d := by
    have := waveBW_nonneg τ σ; positivity
  exact homXnorm_le_of_components_gen ha hp hpb hr one_le_homKS hE0 _
    (homF_sub_compBounds_gen ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂ hXL
        hdom.1)
    hdom.2.1.le hdom.2.2

theorem HomTaylor_gen.ext_of {T T' : HomTaylor_gen a p pb s} (h1 : T.a0 = T'.a0) (h2 : T.b = T'.b)
    (h3 : T.cp = T'.cp) (h4 : T.cm = T'.cm) (h5 : T.P = T'.P) (h6 : T.P' = T'.P')
    (h7 : T.Q = T'.Q) (h8 : T.Qt = T'.Qt) : T = T' := by
  cases T; cases T'
  simp only at h1 h2 h3 h4 h5 h6 h7 h8
  subst h1 h2 h3 h4 h5 h6 h7 h8
  rfl

theorem homCoeff_sub_banach {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {s : ℝ}
    (hs : 0 < s) {u v : (Fin 2 → ℂ) → E} (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hv : DifferentiableOn ℂ v (complexStrip 2 s)) (k : Fin 2 → ℤ) :
    homCoeff (fun z => u z - v z) k = homCoeff u k - homCoeff v k :=
  kamFourierBanach_coeff_sub (homContinuous_restrict hs hu) (homContinuous_restrict hs hv) k

/-- `N̂` is linear in `R`. -/
theorem homNhatTaylor_sub_gen (hs : 0 < s) (R₁ R₂ : HomTaylor_gen a p pb s) :
    (homNhatTaylor_gen R₁).homSub (homNhatTaylor_gen R₂) = homNhatTaylor_gen (R₁.homSub R₂) := by
  refine HomTaylor_gen.ext_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · funext z; simp [HomTaylor_gen.homSub, homNhatTaylor_gen]
  · funext z
    show homCoeff R₁.b 0 - homCoeff R₂.b 0 = homCoeff (fun z => R₁.b z - R₂.b z) 0
    rw [homCoeff_sub_banach hs R₁.comp_b.1 R₂.comp_b.1]
  · funext z; simp [HomTaylor_gen.homSub, homNhatTaylor_gen]
  · funext z; simp [HomTaylor_gen.homSub, homNhatTaylor_gen]
  · funext z; simp [HomTaylor_gen.homSub, homNhatTaylor_gen]
  · funext z; simp [HomTaylor_gen.homSub, homNhatTaylor_gen]
  · funext z
    show kamEntryDiagCLM (homCoeff R₁.Q 0) - kamEntryDiagCLM (homCoeff R₂.Q 0) =
      kamEntryDiagCLM (homCoeff (fun z => R₁.Q z - R₂.Q z) 0)
    rw [homCoeff_sub_banach hs R₁.comp_Q.1 R₂.comp_Q.1]
    refine homOp_ext_entries fun i j => ?_
    simp only [kamEntry_sub', kamEntry_diagCLM]
    split_ifs <;> simp
  · funext z
    show kamEntryDiagCLM (homCoeff R₁.Q 0) - kamEntryDiagCLM (homCoeff R₂.Q 0) =
      kamEntryDiagCLM (homCoeff (fun z => R₁.Q z - R₂.Q z) 0)
    rw [homCoeff_sub_banach hs R₁.comp_Q.1 R₂.comp_Q.1]
    refine homOp_ext_entries fun i j => ?_
    simp only [kamEntry_sub', kamEntry_diagCLM]
    split_ifs <;> simp

/-- **Lemma 1 (iii), Lipschitz bound** from the source premises: `|X_{F(ξ)} - X_{F(ζ)}|_r ≤
C₁ B^W_σ (ε^L + 2Mε/α) d/α` on `D(s-σ,r)`, `C₁ = 7 + 10K_S`, `M = M_ω + M_Ω`, `d = |ξ-ζ|`. -/
theorem homLemma1_lipschitz_gen {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hH : HomMelnikov τ α Par ω Ω) (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε εL : ℝ}
    (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hεL : 0 ≤ εL) (hσ : 0 < σ) (hσs : σ < s)
    {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (hζ : ζ ∈ Par) (R₁ R₂ : HomTaylor_gen a p pb s)
    (hX₁ : HomFieldBound_gen ha hp hpb r ε R₁) (hX₂ : HomFieldBound_gen ha hp hpb r ε R₂)
    (hXL : HomFieldBound_gen ha hp hpb r (εL * ‖ξ - ζ‖) (R₁.homSub R₂)) :
    HomFieldBound_gen ha hp hpb r
      ((7 + 10 * homKS) * (waveBW τ σ / α * (εL + 2 * (Mω + MΩ) * ε / α) * ‖ξ - ζ‖))
      ((homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R₁).homSub
       (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hζ) R₂)) :=
  homLemma1_lipschitz_of_gates_gen ha hp hpb hr hτ hα
    (by linarith [h.consts_nonneg.2.1, h.consts_nonneg.2.2]) (norm_nonneg _) hεL hσ hσs
    (homMultBounds_of h hα hH hξ) (homMultBounds_of h hα hH hζ) (homMultLip_of h hα hH hξ hζ)
    R₁ R₂ hX₁ hX₂ hXL

/-- **Lemma 1 (iv), Lipschitz bound for `N̂`**: `|X_{N̂(ξ)} - X_{N̂(ζ)}|_r ≤ 2 ε^L d`. -/
theorem homNhat_lipschitz_gen (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r εL : ℝ} (hr : 0 < r) (hs
    : 0
    < s)
    (R₁ R₂ : HomTaylor_gen a p pb s) (hXL : HomFieldBound_gen ha hp hpb r (εL * d) (R₁.homSub R₂)) :
    HomFieldBound_gen ha hp hpb r (2 * (εL * d)) ((homNhatTaylor_gen R₁).homSub (homNhatTaylor_gen
        R₂)) := by
  rw [homNhatTaylor_sub_gen hs]
  exact homNhat_fieldBound_gen ha hp hpb hr hs (R₁.homSub R₂) hXL

theorem homKS_lt_29 : homKS < 2.9 := by
  have h1 : (1.73 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 := Real.pi_lt_d2
  unfold homKS
  have h3 : Real.pi / Real.sqrt 3 < 1.9 := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  linarith

/-- The norm `|X|^λ = ε_X + λ ε_X^L` of Lemma 2. -/
def homLamNorm (lam εX εXL : ℝ) : ℝ := εX + lam * εXL

/-- **P96-K Lemma 2 and bound (4)** (`bpW:w4:lemma2`): for `M > 0`, `0 ≤ λ ≤ α/M`, with
`(ε_R, ε_R^L)` the uniform and Lipschitz bounds of `X_R` and `C₁ = 7 + 10K_S`:

* `|X_{N̂}|^λ ≤ 2|X_R|^λ` (from the bounds `2ε`, `2ε^L` of `homNhat_fieldBound_gen`,
  `homNhat_lipschitz_gen`);
* `|X_F|^λ ≤ (3C₁B^W_σ/α)|X_R|^λ` (from the bounds `C₁Bε/α` and `C₁B(ε^L + 2Mε/α)/α` of
  `homLemma1_fieldBound_gen`, `homLemma1_lipschitz_gen`);
* `B^W_σ ≤ b_W(τ) σ^{-(2τ+3)}` for `0 < σ ≤ 1` (`bpW:w4:lattice` (iv)); `3C₁ < 108`. -/
theorem homLemma2 {τ α M lam σ ε εL : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hM : 0 < M)
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ α / M) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 ≤ ε)
    (hεL : 0 ≤ εL) :
    homLamNorm lam (2 * ε) (2 * εL) ≤ 2 * homLamNorm lam ε εL ∧
      homLamNorm lam ((7 + 10 * homKS) * (waveBW τ σ * ε / α))
        ((7 + 10 * homKS) * (waveBW τ σ / α * (εL + 2 * M * ε / α))) ≤
        3 * (7 + 10 * homKS) * waveBW τ σ / α * homLamNorm lam ε εL ∧
      3 * (7 + 10 * homKS) < 108 ∧
      waveBW τ σ ≤ waveBWconst τ / σ ^ (2 * τ + 3) := by
  have hB := waveBW_nonneg τ σ
  have hK := homKS_lt_29
  have hK1 := one_le_homKS
  refine ⟨by unfold homLamNorm; linarith, ?_, by norm_num at hK ⊢; linarith, waveBW_le hτ hσ hσ1⟩
  unfold homLamNorm
  have hlM : lam * M / α ≤ 1 := by
    rw [div_le_one hα]
    have := mul_le_mul_of_nonneg_right hlam hM.le
    rwa [div_mul_cancel₀ _ hM.ne'] at this
  have hC : 0 ≤ (7 + 10 * homKS) * waveBW τ σ / α := by positivity
  have key : ε + lam * (εL + 2 * M * ε / α) ≤ 3 * (ε + lam * εL) := by
    have h1 : lam * (2 * M * ε / α) = 2 * ε * (lam * M / α) := by ring
    have h2 : 2 * ε * (lam * M / α) ≤ 2 * ε := by nlinarith
    nlinarith [mul_nonneg hlam0 hεL]
  calc (7 + 10 * homKS) * (waveBW τ σ * ε / α) +
        lam * ((7 + 10 * homKS) * (waveBW τ σ / α * (εL + 2 * M * ε / α)))
      = (7 + 10 * homKS) * waveBW τ σ / α * (ε + lam * (εL + 2 * M * ε / α)) := by ring
    _ ≤ (7 + 10 * homKS) * waveBW τ σ / α * (3 * (ε + lam * εL)) :=
        mul_le_mul_of_nonneg_left key hC
    _ = _ := by ring

end KAM.Wave
