/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.IterationStage

/-!
# Two-scale KAM: the iteration (`bpP:p3:iterative`)

All stage witnesses of Proposition 3 (P3a) are introduced in one existence theorem, by a
dependent induction on `StageInv` (`IterationStage`): stage `0` is the restriction to the
Diophantine base set with `Φ₀ = id`, and stage `j + 1` is produced from stage `j` by `step`, with
`Φ_{j+1} = Φⱼ ∘ Ψ_{j+1}`. The statement is that of `P23Signatures.lean`. Design package P23-16.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- P3 iterative: common sequences are existentially quantified once, not chosen
by a default-valued function. Limits below remain local obligations on these witnesses. -/
theorem iterative {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)} (H : KamHyp D sbar p h f) :
    ∃ (Ds : ℕ → Set (Fin (a + b) → ℝ)) (hs : ℕ → (Fin (a + b) → ℂ) → ℂ)
      (fs : ℕ → CHam (a + b)) (Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b))
      (is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)),
      Ds 0 = dioBase D h p ∧ hs 0 = h ∧ fs 0 = f ∧ Φ 0 = id ∧ is 0 = id ∧
      (∀ j, KamHyp (Ds j) sbar (seq p j) (hs j) (fs j)) ∧
      (∀ j, Φ (j + 1) = Φ j ∘ Ψ (j + 1)) ∧
      (∀ j, let pj := seq p j
        DifferentiableOn ℂ (is (j + 1)) (KAM.actionNbhd (Ds j) (rhoHat pj / 16)) ∧
        (∀ I ∈ KAM.actionNbhd (Ds j) (rhoHat pj / 16),
          freq (hs (j + 1)) (is (j + 1) I) = freq (hs j) I ∧
          ‖firstBlock (b := b) (is (j + 1) I - I)‖ ≤ 10 * (p.Mbar₁ / p.Mbar) * eHat pj * rhoHat pj ∧
          ‖lastBlock (a := a) (is (j + 1) I - I)‖ ≤ 10 * (p.Mbar₂ / p.Mbar) * eHat pj * rhoHat pj) ∧
        (∀ I ∈ Ds j, ∀ J ∈ Ds j,
          ‖(is (j + 1) (KAM.realInclusion (a + b) I) - KAM.realInclusion (a + b) I) -
            (is (j + 1) (KAM.realInclusion (a + b) J) - KAM.realInclusion (a + b) J)‖ ≤
              640 * (a + b) * eHat pj * ‖I - J‖) ∧
        Ds (j + 1) = (fun I => fun k => (is (j + 1) (KAM.realInclusion (a + b) I) k).re) '' Ds j) ∧
      (∀ j, let pj := seq p j
        let V := coefficientDom (Ds j) pj.ρ (sbar + pj.s)
        DifferentiableOn ℂ (Φ j) V ∧ Set.InjOn (Φ j) V ∧
        (∀ x : Phase (a + b), KAM.realInclusion₂ (a + b) x ∈ V →
          Φ j (KAM.realInclusion₂ (a + b) x) ∈ range (KAM.realInclusion₂ (a + b))) ∧
        (∀ z ∈ V, ∀ k : Fin (a + b) → ℤ,
          Φ j (z + ((fun i => (k i : ℂ)), 0)) = Φ j z + ((fun i => (k i : ℂ)), 0)) ∧
        MapsTo (Φ j) V (coefficientDom D p.ρ (sbar + p.s)) ∧
        (∀ z ∈ V, h (Φ j z).2 + f (Φ j z) = hs j z.2 + fs j z) ∧
        (∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ (Φ j) z u) (fderiv ℂ (Φ j) z v) = symplFormC u v)) ∧
      (∀ j, Ds (j + 1) ⊆ realTube (Ds j) (rhoHat (seq p j) / 16) ∧
        realFreq (hs j) '' Ds j = realFreq h '' dioBase D h p ∧
        MapsTo (is (j + 1)) (realBase (Ds j)) (realBase (Ds (j + 1)))) ∧
      (∀ j, let pj := seq p j
        let V := coefficientDom (Ds (j + 1)) (rhoHat pj / 16) (sbar + pj.s / 12)
        DifferentiableOn ℂ (Ψ (j + 1)) V ∧
        (∀ x : Phase (a + b), KAM.realInclusion₂ (a + b) x ∈ V →
          Ψ (j + 1) (KAM.realInclusion₂ (a + b) x) ∈ range (KAM.realInclusion₂ (a + b))) ∧
        (∀ z ∈ V, ∀ k : Fin (a + b) → ℤ,
          Ψ (j + 1) (z + ((fun i => (k i : ℂ)), 0)) = Ψ (j + 1) z + ((fun i => (k i : ℂ)), 0)) ∧
        (∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ (Ψ (j + 1)) z u)
          (fderiv ℂ (Ψ (j + 1)) z v) = symplFormC u v) ∧
        MapsTo (Ψ (j + 1)) V (coefficientDom (Ds j) (rhoHat pj) (sbar + pj.s)) ∧
        (∀ z ∈ V,
          ‖firstBlock (b := b) ((Ψ (j + 1) z).2 - z.2)‖ ≤
            3 / 4 * (p.Mhat / p.M) * eHat pj * rhoHat pj ∧
          ‖lastBlock (a := a) ((Ψ (j + 1) z).2 - z.2)‖ ≤ 3 / 4 * eHat pj * rhoHat pj ∧
          2 * π * ‖(Ψ (j + 1) z).1 - z.1‖ ≤ 3 / 4 * eHat pj * pj.s)) ∧
      (∀ j, eHat (seq p (j + 1)) < eHat (seq p j) ^ 2 ∧
        rhoHat (seq p j) / (2 * (24 : ℝ) ^ (p.τ + 1)) ≤ rhoHat (seq p (j + 1)) ∧
        rhoHat (seq p (j + 1)) ≤ rhoHat (seq p j) / 16 ∧
        cutoff (seq p j) ≤ 24 ^ j * cutoff p) := by
  have key : ∀ j, ∀ S : {S : Stage a b // StageInv D sbar p h f j S},
      ∃ (S' : {S : Stage a b // StageInv D sbar p h f (j + 1) S})
        (Ψ : CPhase (a + b) → CPhase (a + b)) (is : (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)),
        StepRel sbar p j S.1 S'.1 Ψ is := fun j S => by
    obtain ⟨S', Ψ, is, hI, hR⟩ := stage_step j S.1 S.2
    exact ⟨⟨S', hI⟩, Ψ, is, hR⟩
  choose F Ψf isf hrel using key
  let T : ∀ j, {S : Stage a b // StageInv D sbar p h f j S} := fun j =>
    Nat.rec ⟨_, stage_zero H⟩ (fun j Tj => F j Tj) j
  have hR : ∀ j, StepRel sbar p j (T j).1 (T (j + 1)).1 (Ψf j (T j)) (isf j (T j)) :=
    fun j => hrel j (T j)
  refine ⟨fun j => (T j).1.D, fun j => (T j).1.h, fun j => (T j).1.f,
    fun n => Nat.casesOn n id (fun j => Ψf j (T j)), fun j => (T j).1.Φ,
    fun n => Nat.casesOn n id (fun j => isf j (T j)), ?_⟩
  have hc : ∀ j, cutoff (seq p j) ≤ (24 : ℝ) ^ j * cutoff p := by
    intro j
    induction j with
    | zero => simp [seq]
    | succ j ih =>
      calc cutoff (seq p (j + 1)) ≤ 24 * cutoff (seq p j) := (hR j).cutoff_le
        _ ≤ 24 * ((24 : ℝ) ^ j * cutoff p) := by gcongr
        _ = (24 : ℝ) ^ (j + 1) * cutoff p := by ring
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun j => (T j).2.hyp, fun j => (hR j).comp,
    fun j => ⟨(hR j).is_diff, (hR j).is_freq, (hR j).is_lip, (hR j).D_eq⟩,
    fun j => ?_, fun j => ⟨(hR j).tube, (T j).2.freq_eq, (hR j).maps_is⟩,
    fun j => ⟨(hR j).psi.diff, (hR j).psi.real, (hR j).psi.per, (hR j).psi.symp,
      (hR j).psi_maps, (hR j).psi_bd⟩,
    fun j => ⟨(hR j).eHat_sq, (hR j).rho_lo, (hR j).rho_hi, hc j⟩⟩
  have hI := (T j).2
  exact ⟨hI.phase.diff, hI.phase.inj, hI.phase.real, hI.phase.per, hI.maps, hI.conj,
    hI.phase.symp⟩

end KAM.Planetary

end
