/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepTheoremSrc
public import KAM.Wave.Iteration.Strong
import Mathlib.Tactic.Linarith

/-!
# W6: strong conjugacy at regular points (blueprint `bpW:w6:strong`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:strong` (milestone W6).

Model (W5-REAL, `KamStep/RealNField.lean`): `𝒫 = 𝒫^p` is `StepPhase r` in the `p`-representatives;
`𝒫^{p_+}` is the range of `ι = stepEmbedCLM a p pb hpb r`; a field with values in `𝒫^{p-1}` is a
map `KamPhase → KamPhase` read in the `(p-1)`-representatives; the pairing of `𝒫^{p-1}` with
`𝒫^{p_+}` is `ϖ_{p-1,p_+} = stepSymp (q := p - 1) (q' := pb)`; "`X ∈ 𝒫`" for such a field value
means `X = ι_{p→p-1} A` with `A ∈ 𝒫` (`ι_{p→p-1} = kamHomEmbed a (p - 1) p`).

* `stepSymp_embed_pred_eq`: `ϖ_{p-1,p_+}(ι_{p→p-1} V, W) = ϖ_{p,p}(V, ι W)` (both are the true
  pairing);
* `w6StrongConj` (`bpW:w6:strong`): pointwise at `w`; only the hypotheses at the point `w` are
  used (`DΦ(w)` symplectic on `𝒫`, onto `𝒫^{p_+}` from `𝒫^{p_+}`, the weak conjugacy for all
  `W ∈ 𝒫^{p_+}`), so the blueprint's version on an open set `O` follows at every `w ∈ O`;
* `stepTheorem_strong`: the instance for W5's step map `Φ` (`stepTheorem`, `StepHypSrc`), with
  `X_H = X_N + X_P`, `X_{H_+} = X_{N_+} + X_{P_+}`.
-/

@[expose] public section

namespace KAM.Wave

variable {a p pb : ℝ}

/-- `ϖ_{p-1,p_+}(ι_{p→p-1} V, W) = ϖ_{p,p}(V, ι_{p_+→p} W)`: both are the true pairing. -/
theorem stepSymp_embed_pred_eq (ha : 0 ≤ a) (hpb : p ≤ pb) (hpp : 0 ≤ p + p)
    (hqq : 0 ≤ (p - 1) + pb) (hpm : p - 1 ≤ p) (V W : KamPhase) :
    stepSymp (q := p - 1) (q' := pb) ha hqq (kamHomEmbed a (p - 1) p hpm V) W =
      stepSymp (q := p) (q' := p) ha hpp V (kamHomEmbed a p pb hpb W) := by
  unfold stepSymp
  simp only [kamHomEmbed_apply]
  conv_lhs => rw [← homEmbed_gen_self a pb W.2.2.2, ← homEmbed_gen_self a pb W.2.2.1]
  conv_rhs => rw [← homEmbed_gen_self a p V.2.2.1, ← homEmbed_gen_self a p V.2.2.2]
  rw [stepPair_embed_eq_true, stepPair_embed_eq_true, stepPair_embed_eq_true,
    stepPair_embed_eq_true]

/-- **Strong conjugacy at regular points** (blueprint `bpW:w6:strong`), at a point `w`: if `DΦ(w)`
is symplectic on `𝒫`, maps `𝒫^{p_+}` onto `𝒫^{p_+}`, and the fields `X_H` (at `Φ w`) and `X_{H_+}`
(at `w`), valued in `𝒫^{p-1}`, satisfy `ϖ(X_H(Φw), DΦ(w)W) = ϖ(X_{H_+}(w), W)` for all
`W ∈ 𝒫^{p_+}`, and `X_{H_+}(w) = A ∈ 𝒫`, then `X_H(Φw) = DΦ(w) A` (in `𝒫^{p-1}`). -/
theorem w6StrongConj (ha : 0 ≤ a) (hpb : p ≤ pb) (hpp : 0 ≤ p + p) (hqq : 0 ≤ (p - 1) + pb)
    (hpm : p - 1 ≤ p) {r : ℝ} [Fact (0 < r)] (Φ : StepPhase r → StepPhase r) (w : StepPhase r)
    (hsymp : ∀ W W' : StepPhase r,
      stepSympCLM (q := p) (q' := p) ha hpp r (fderiv ℂ Φ w W) (fderiv ℂ Φ w W') =
        stepSympCLM (q := p) (q' := p) ha hpp r W W')
    (honto : ∀ W'' : StepPhase r, ∃ W' : StepPhase r,
      fderiv ℂ Φ w (stepEmbedCLM a p pb hpb r W') = stepEmbedCLM a p pb hpb r W'')
    (XH XHp : KamPhase → KamPhase)
    (hweak : ∀ W' W'' : StepPhase r,
      fderiv ℂ Φ w (stepEmbedCLM a p pb hpb r W') = stepEmbedCLM a p pb hpb r W'' →
      stepSymp (q := p - 1) (q' := pb) ha hqq (XH (StepPhase.toK (Φ w))) (StepPhase.toK W'') =
        stepSymp (q := p - 1) (q' := pb) ha hqq (XHp (StepPhase.toK w)) (StepPhase.toK W'))
    {A : StepPhase r} (hA : XHp (StepPhase.toK w) = kamHomEmbed a (p - 1) p hpm (StepPhase.toK A)) :
    XH (StepPhase.toK (Φ w)) =
      kamHomEmbed a (p - 1) p hpm (StepPhase.toK (fderiv ℂ Φ w A)) := by
  refine sub_eq_zero.1 (stepSymp_nondeg (q := p - 1) (q' := pb) ha hqq fun W'' => ?_)
  obtain ⟨W', hW'⟩ := honto (StepPhase.ofK W'')
  have h1 := hweak W' (StepPhase.ofK W'') hW'
  have h2 := hsymp A (stepEmbedCLM a p pb hpb r W')
  rw [hW'] at h2
  simp only [stepSympCLM_apply, stepEmbedCLM_apply] at h2
  have h1' : stepSymp (q := p - 1) (q' := pb) ha hqq (XH (StepPhase.toK (Φ w))) W'' =
      stepSymp (q := p - 1) (q' := pb) ha hqq (XHp (StepPhase.toK w)) (StepPhase.toK W') := h1
  have h2' : stepSymp (q := p) (q' := p) ha hpp (StepPhase.toK (fderiv ℂ Φ w A))
      (kamHomEmbed a p pb hpb W'') =
      stepSymp (q := p) (q' := p) ha hpp (StepPhase.toK A)
        (kamHomEmbed a p pb hpb (StepPhase.toK W')) := h2
  rw [stepSymp_sub_left, h1', hA, stepSymp_embed_pred_eq ha hpb hpp hqq hpm,
    stepSymp_embed_pred_eq ha hpb hpp hqq hpm, h2']
  exact sub_self _

variable {s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ : ℝ} {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

/-- **Strong conjugacy for W5's step map** (`bpW:w6:strong` applied to `bpW:w5:step` (i)): for
`ξ ∈ Π`, `w ∈ D_+`, if `X_{H_+}(w) = X_{N_+}(w) + X_{P_+}(w) = A ∈ 𝒫`, then
`X_H(Φ w) = X_N(Φ w) + X_P(Φ w) = DΦ(w) A` in `𝒫^{p-1}` (`Φ = H.hyp.core.Phi ξ`). -/
theorem stepTheorem_strong
    (H : StepHypSrc a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) [Fact (0 < r)]
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) (hpm : p - 1 ≤ p) {A : StepPhase r}
    (hA : stepXN (a := a) (p := p) (H.hyp.core.omegaPlus_bound hξ) (H.hyp.core.omegaPlus ξ)
        (StepPhase.toK w) +
      kamHomEmbed a (p - 1) pb H.hyp.core.hpm (StepPhase.toK (H.hyp.core.Xplus ξ w)) =
        kamHomEmbed a (p - 1) p hpm (StepPhase.toK A)) :
    stepXN (a := a) (p := p) (homOmega_le H.freq hξ) (ω ξ) (StepPhase.toK (H.hyp.core.Phi ξ w)) +
      kamHomEmbed a (p - 1) pb H.hyp.core.hpm (X ξ (StepPhase.toK (H.hyp.core.Phi ξ w))) =
        kamHomEmbed a (p - 1) p hpm (StepPhase.toK (fderiv ℂ (H.hyp.core.Phi ξ) w A)) := by
  obtain ⟨-, -, -, hs, -, -, hon, hwc, -⟩ := stepTheorem_clauses H
  exact w6StrongConj H.ha H.hpb H.hyp.core.two_p H.hyp.core.hqq1 hpm (H.hyp.core.Phi ξ) w
    (hs ξ hξ w hw) (hon ξ hξ w hw).2
    (fun z => stepXN (a := a) (p := p) (homOmega_le H.freq hξ) (ω ξ) z +
      kamHomEmbed a (p - 1) pb H.hyp.core.hpm (X ξ z))
    (fun z => stepXN (a := a) (p := p) (H.hyp.core.omegaPlus_bound hξ) (H.hyp.core.omegaPlus ξ) z +
      kamHomEmbed a (p - 1) pb H.hyp.core.hpm
        (StepPhase.toK (H.hyp.core.Xplus ξ (StepPhase.ofK (r := r) z))))
    (hwc ξ hξ w hw) hA

end KAM.Wave
