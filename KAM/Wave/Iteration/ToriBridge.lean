/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.Invariance
public import KAM.Wave.KamStep.ActionAngleConj
public import KAM.Wave.KamStep.Initial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: bridges between W5's action–angle map and the W6 tori (`bpW:w6:tori`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:tori` (steps `t-bk`, `t-close`, `t-an`).

The W6 tori live in KAM coordinates (`KamPhase`, `𝒫`, normal components as representatives) and
W5's action–angle lemma (`bpW:w5:action-angle`) in Birkhoff coordinates (`BirkSpace`, weighted
coordinates). This module records the identifications used to compose them:

* `aaXN_ofReal_eq_stepXN`: for real `ξ`, W5's `X_{N_ξ}` (`aaXN`, complex `Ω⁰`) is the field
  `stepXN` of the unperturbed real frequencies `(ω⁰, Ω⁰)` (`waveFreqTan`, `waveFreqNor`);
* `kamHomEmbed_stepRhoK`: the reweighted field `D_ρ X` of the modified step, read in `𝒫^{p-1}`,
  is `X` read in `𝒫^{p-1}` (`ι_{p_+ → p-1} D_ρ = ι_{p+1 → p-1}`);
* `birkEmbed_aaDer`: `ι_{q → q'} D𝒜_ξ(w) = D𝒜_ξ(w) ι_{q → q'}` (the derivative of `𝒜_ξ` commutes
  with the weight embeddings);
* `aaNormal_kamHomEmbed`: the normal part of `𝒜_ξ` commutes with the weight embeddings;
* `w6_periodic_zsmul`: unit-step periodicity on a translation-invariant set gives integer
  periodicity.
-/

@[expose] public noncomputable section

open Set Complex

namespace KAM.Wave

open KAM

variable {m : ℝ} {hm : 0 < m}

/-- W5's field `X_{N_ξ}` (`aaXN`) at a real parameter is the field `stepXN` of the unperturbed
frequencies `(ω⁰(ξ), Ω⁰(ξ))` (any bound `K0` of `Ω⁰` as typing data). -/
theorem aaXN_ofReal_eq_stepXN (ξ : Fin 2 → ℝ) {K0 : ℝ}
    (hΩ : ∀ j : ℕ+, |waveFreqNor m hm ξ j| ≤ K0 * ((j : ℝ) + 2)) (w : KamPhase) :
    aaXN m hm (aaOfReal ξ) w = stepXN (a := 1) (p := 1) hΩ (waveFreqTan m hm ξ) w := by
  have hc : ∀ j : ℕ+, aaXNcoef m hm (aaOfReal ξ) j = stepXNcoef 1 1 (waveFreqNor m hm ξ) j :=
      fun j => by
    unfold aaXNcoef stepXNcoef
    rw [aaOmegaN0_ofReal, homWt_pred_div]
    push_cast
    rfl
  have hD : ∀ x : HomL2, aaXNdiag m hm (aaOfReal ξ) x = stepXNdiag (a := 1) (p := 1) hΩ x :=
    fun x => by
      ext j
      simp only [aaXNdiag, stepXNdiag, weightedDiagCLM_apply, hc]
  unfold aaXN stepXN
  refine Prod.ext (funext fun i => ?_) (Prod.ext rfl (Prod.ext (hD _) ?_))
  · simp only [aaOmega0_ofReal]
  · simp only [hD]

/-- `ι_{p_+ → p-1} ∘ D_ρ = ι_{p+1 → p-1}` on `KamPhase` (`a = p = 1`, `p_+ = 3/2`): the reweighted
field of the modified step and the original field are the same vector of `𝒫^{p-1}`. -/
theorem kamHomEmbed_stepRhoK (hc : (3 / 2 : ℝ) ≤ 1 + 1) (h1 : (1 : ℝ) - 1 ≤ 3 / 2)
    (h2 : (1 : ℝ) - 1 ≤ 1 + 1) (W : KamPhase) :
    kamHomEmbed 1 (1 - 1) (3 / 2) h1 (stepRhoK 1 1 (3 / 2) hc W) =
      kamHomEmbed 1 (1 - 1) (1 + 1) h2 W := by
  have hx : ∀ x : HomL2, homEmbed_gen 1 (1 - 1) (3 / 2) h1 (homModRho 1 1 (3 / 2) hc x) =
      homEmbed_gen 1 (1 - 1) (1 + 1) h2 x := fun x => by
    ext j
    simp only [homEmbed_gen, weightedDiagCLM_apply, homEmbedCoef_gen, homModRho_apply,
      homModRatio]
    have h0 : (homWt 1 (3 / 2) j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos 1 (3 / 2) j).ne'
    have h0' : (homWt 1 (1 + 1) j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos 1 (1 + 1) j).ne'
    push_cast
    field_simp
  obtain ⟨θ, y, u, v⟩ := W
  rw [stepRhoK_apply, kamHomEmbed_apply, kamHomEmbed_apply]
  simp only [hx]

/-- `ι_{q → q'} D𝒜_ξ(w) W = D𝒜_ξ(w) (ι_{q → q'} W)` (`q' ≤ q`; `aaDer a q` acts on
`q`-representatives with values in `𝔚` weighted at `(a, q)`). -/
theorem birkEmbed_aaDer {a q q' : ℝ} (h : q' ≤ q) (ξ : Fin 2 → ℂ) (w W : KamPhase) :
    birkEmbed a q q' h (aaDer a q ξ w W) = aaDer a q' ξ w (kamHomEmbed a q' q h W) := by
  refine birkSpace_ext_coord a q' fun l => ?_
  obtain ⟨b, J⟩ := l
  rw [birkCoord_birkEmbed]
  rcases modeIdx_cases J with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · rw [birkCoord_aaDer_tan, birkCoord_aaDer_tan, aaDerTanL_kamHomEmbed]
  · have hq : (homWt a q j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a q j).ne'
    have hq' : (homWt a q' j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a q' j).ne'
    have h2 := birkSqrt2_ne
    cases b
    · rw [birkCoord_aaDer_nor_false, birkCoord_aaDer_nor_false]
      simp only [kamHomEmbed_apply, homEmbed_gen, weightedDiagCLM_apply, homEmbedCoef_gen]
      push_cast
      field_simp
    · rw [birkCoord_aaDer_nor_true, birkCoord_aaDer_nor_true]
      simp only [kamHomEmbed_apply, homEmbed_gen, weightedDiagCLM_apply, homEmbedCoef_gen]
      push_cast
      field_simp

/-- The normal part of `𝒜_ξ` commutes with the weight embeddings:
`ŵ(ι_{q' → q} V) = ι_{q' → q} ŵ(V)` (`q ≤ q'`). -/
theorem aaNormal_kamHomEmbed {a q q' : ℝ} (h : q ≤ q') (V : KamPhase) :
    aaNormal (kamHomEmbed a q q' h V) = birkEmbed a q' q h (aaNormal V) := by
  ext ⟨b, J⟩
  rw [birkEmbed_apply]
  rcases modeIdx_cases J with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · rw [aaNormal_tan, aaNormal_tan, mul_zero]
  · cases b <;> dsimp only
    · rw [aaNormal_nor_false, aaNormal_nor_false]
      simp only [kamHomEmbed_apply, homEmbed_gen, weightedDiagCLM_apply, homEmbedCoef_gen,
        embedRatio, homWt, RCLike.ofReal_eq_complex_ofReal]
      ring
    · rw [aaNormal_nor_true, aaNormal_nor_true]
      simp only [kamHomEmbed_apply, homEmbed_gen, weightedDiagCLM_apply, homEmbedCoef_gen,
        embedRatio, homWt, RCLike.ofReal_eq_complex_ofReal]
      ring

/-- `ŵ` vanishes on `ιθ = (θ, 0, 0, 0)`. -/
theorem aaNormal_w6TorusPt (θ : Fin 2 → ℂ) : aaNormal (w6TorusPt θ) = 0 := by
  have h0 : ∀ J, aaShiftFun (0 : HomL2) J = 0 := fun J => by
    unfold aaShiftFun; split_ifs <;> rfl
  ext ⟨b, J⟩
  rw [aaNormal_apply]
  simp [w6TorusPt, h0]

/-- Unit-step periodicity on a set invariant under `± e` gives integer periodicity. -/
theorem w6_periodic_zsmul {E F : Type*} [AddCommGroup E] {S : Set E} {f : E → F} {e : E}
    (hS : ∀ z ∈ S, z + e ∈ S ∧ z - e ∈ S) (hf : ∀ z ∈ S, f (z + e) = f z) :
    ∀ n : ℤ, ∀ z ∈ S, z + n • e ∈ S ∧ f (z + n • e) = f z := by
  intro n
  induction n using Int.induction_on with
  | zero => intro z hz; simpa using hz
  | succ n ih =>
    intro z hz
    obtain ⟨h1, h2⟩ := ih z hz
    have e1 : z + ((n : ℤ) + 1) • e = (z + (n : ℤ) • e) + e := by rw [add_smul, one_smul, add_assoc]
    rw [e1]
    exact ⟨(hS _ h1).1, (hf _ h1).trans h2⟩
  | pred n ih =>
    intro z hz
    obtain ⟨h1, h2⟩ := ih z hz
    have e1 : z + (-(n : ℤ) - 1) • e = (z + (-(n : ℤ)) • e) - e := by
      rw [sub_smul, one_smul, add_sub_assoc]
    rw [e1]
    have hm := (hS _ h1).2
    refine ⟨hm, ?_⟩
    have := hf _ hm
    rw [sub_add_cancel] at this
    exact this.symm.trans h2

end KAM.Wave
