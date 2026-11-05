/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorChainPhysical

/-!
# The disc physical variant of `oscillatorChain_physical` (track B, B3-CHAINK, OD-B18)

`oscillatorChain_physical_disc` has the premises of `oscillatorChain_physical`, but the physical
initial box is the *disc* `(q_i² + p_i²)/2 ≤ a'_i ≤ σ_i²` instead of the coordinate box: the
chain inverse moves each coordinate by at most `tail = oscTail l`, hence the point of the plane
`(q_i, p_i)` by at most `√2 · tail`, and the start has plane radius `≤ √2 σ_i`; so the chart action
is at most `(σ_i + tail)²` (`hs3'`). The coordinate radii `s` only feed the domain budget
`OscPhysDom n s l 0` (through `2 σ² ≤ s²`). The proof is the shared tail
`oscillatorChain_physical_core`; the two theorems differ only in the chart-action bound.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set CartPoly

variable {n : ℕ} {K : Type} [CertCoeff K] [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ]
  [CertNormLe K ℝ] [CertNormLe K ℂ]

/-- The plane estimate behind the disc variant: a point of plane radius `√2 σ` displaced by at
most `e` in each coordinate has `q² + p² ≤ 2 (σ + e)²`. -/
theorem discPlane_sq_le {q p dq dp σ e : ℝ} (hσ : 0 ≤ σ) (he : 0 ≤ e)
    (hA : q ^ 2 + p ^ 2 ≤ 2 * σ ^ 2) (h1 : |dq| ≤ e) (h2 : |dp| ≤ e) :
    (q + dq) ^ 2 + (p + dp) ^ 2 ≤ 2 * (σ + e) ^ 2 := by
  have hB : dq ^ 2 + dp ^ 2 ≤ 2 * e ^ 2 := by
    have a1 : dq ^ 2 ≤ e ^ 2 := sq_le_sq' (by linarith [abs_le.1 h1]) (by linarith [abs_le.1 h1])
    have a2 : dp ^ 2 ≤ e ^ 2 := sq_le_sq' (by linarith [abs_le.1 h2]) (by linarith [abs_le.1 h2])
    linarith
  have hcs : (q * dq + p * dp) ^ 2 ≤ (q ^ 2 + p ^ 2) * (dq ^ 2 + dp ^ 2) := by
    nlinarith [sq_nonneg (q * dp - p * dq)]
  have hAB : (q ^ 2 + p ^ 2) * (dq ^ 2 + dp ^ 2) ≤ (2 * σ ^ 2) * (2 * e ^ 2) :=
    mul_le_mul hA hB (by positivity) (by positivity)
  have hc : q * dq + p * dp ≤ 2 * σ * e := by
    have h : (q * dq + p * dp) ^ 2 ≤ (2 * σ * e) ^ 2 := by nlinarith
    exact (abs_le_of_sq_le_sq' h (by positivity)).2
  nlinarith

/-- **Disc physical `m`-generator confinement** (track B, B3-CHAINK, OD-B18): the conclusion of
`oscillatorChain_physical`, with the coordinate-box premises `hs1`, `hs3` replaced by the disc
data `σ`, `hσ1 : a' ≤ σ²`, `2 σ² ≤ s²` and `hs3' : (σ + tail)² ≤ a`. -/
theorem oscillatorChain_physical_disc {H Nact P : CartPolyK K}
    (hH : CartFits n H) (hN : CartFits n Nact) (hP : CartFits n P)
    (hA : cartActOnly Nact = true) {l : List (OscStepK K)} (hok : OscChainOK n Nact P l H)
    {δc : ℝ} (hδc : 0 < δc) (a b η : Fin n → ℝ) (εb T : ℝ) (hεb : 0 < εb) (hT : 0 ≤ T)
    (rl : List ℚ) (r : Fin n → ℝ) (hrl : ∀ i : Fin n, ((rl.getD i 0 : ℚ) : ℝ) = r i)
    (hr0 : ∀ i, 0 ≤ r i) (hdom1 : ∀ i, 2 * (b i + εb) ≤ r i ^ 2) (hdom : OscDomOK n r δc l)
    (hη : ∀ j, 0 ≤ η j)
    (hdrift : ∀ j : Fin n, ((cartSupBound (cartBracket (cartAction j) P) rl rl : ℚ) : ℝ) ≤
      η j - 2 * r j * (oscChainBound n l H : ℝ) / δc)
    (hmargin : ∀ j, a j + T * η j < b j)
    (a' s d : Fin n → ℝ) (hs0 : ∀ i, 0 ≤ s i)
    (σ : Fin n → ℝ) (hσ0 : ∀ i, 0 ≤ σ i) (hσ1 : ∀ i, a' i ≤ σ i ^ 2)
    (hsσ : ∀ i, 2 * σ i ^ 2 ≤ s i ^ 2) (hs2 : OscPhysDom n s l 0)
    (hs3' : ∀ i, (σ i + (oscTail l : ℝ)) ^ 2 ≤ a i)
    (hd : ∀ j, (oscTail l : ℝ) * (2 * r j + (oscTail l : ℝ)) ≤ d j)
    (z₀ : (Fin n → ℝ) × (Fin n → ℝ))
    (hz₀ : ∀ j, KAM.Planetary.oscillatorAction z₀.2 z₀.1 j ≤ a' j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = z₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
        HasDerivAt z (KAM.hamiltonianVectorField
          (fun w : (Fin n → ℝ) × (Fin n → ℝ) => cartEval H w) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = z₀ →
        (∀ t ∈ I, y t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
          HasDerivAt y (KAM.hamiltonianVectorField
            (fun w : (Fin n → ℝ) × (Fin n → ℝ) => cartEval H w) (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → ∀ j,
        |KAM.Planetary.oscillatorAction (z t).2 (z t).1 j -
            KAM.Planetary.oscillatorAction z₀.2 z₀.1 j| ≤ 2 * d j + η j * |t| ∧
          KAM.Planetary.oscillatorAction (z t).2 (z t).1 j ≤ a j + η j * T + d j := by
  have hl := hok.stepsOK
  have he : 0 ≤ (oscTail l : ℝ) := by exact_mod_cast oscTail_nonneg_of hl
  refine oscillatorChain_physical_core hH hN hP hA hok hδc a b η εb T hεb hT rl r hrl hr0 hdom1
    hdom hη hdrift hmargin a' s d hs0 (fun i => by linarith [hσ1 i, hsσ i]) hs2 hd z₀ hz₀ ?_
  intro w hdisp j
  have hA' : z₀.1 j ^ 2 + z₀.2 j ^ 2 ≤ 2 * σ j ^ 2 := by
    have := hz₀ j
    have h2 := hσ1 j
    simp only [KAM.Planetary.oscillatorAction] at this
    linarith
  have key := discPlane_sq_le (hσ0 j) he hA' (dq := w.1 j - z₀.1 j) (dp := w.2 j - z₀.2 j)
    (hdisp j).1 (hdisp j).2
  have h3 := hs3' j
  simp only [add_sub_cancel] at key
  simp only [KAM.Planetary.oscillatorAction]
  linarith

end KAM.EffectiveStability

end
