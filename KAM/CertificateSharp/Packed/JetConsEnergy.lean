/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetConsInv

/-!
# The packed energy check on the jet's boundary

The landed `checkEnergy` composes `H ∘ K` at `cfgFull` (`Slp.compose … [v0]`) and bounds the zero
mode of `H ∘ K - E₀` plus the model radius (`energyOk`). `checkEnergyJ` certifies **the same
proposition** (`checkEnergyJ_sound`: the conclusion of `checkEnergy_sound_of`) from the jet's packed
model of the `v0` slot (`jetFullOk`): its zero-key slot at scale `2^P` is an exact complex rational
`z` within the node's radius of the torus average of `H ∘ K` (`PEnc.average`), so
`|⟨H ∘ K⟩ - E₀| ≤ |Re z - E₀| + |Im z| + r` (`enOk`).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Torus KAM.Certificate KAM.Certificate.CertArith

section Defs

variable {α : Type} [CertArith α] (n : ℕ)

/-- The guards of the zero-key read-out on the book's box: the layout, its dimension, its zero
key, and the slot bound of the jet nodes. -/
def enGuard (ib : PIBook) : Bool :=
  layoutWf ib.Lb && ib.Lb.dims.length == n && (ib.Lb.slot (List.replicate n 0)).isSome &&
    decide (2 * ib.bJ < 2 ^ ib.Lb.width)

/-- **The energy bound** from the zero mode `z` of the `v0` node: `|Re z - E₀| + |Im z| + r ≤ err`
(upward). -/
def enOk (J : HamJet) (js : JSlots α) (ib : PIBook) (E0 err : ℚ) : Bool :=
  ble (upAdd (ofRatUp (|(ptDigit n ib.Lb ib.P (js.x J.v0)).1 - E0| +
      |(ptDigit n ib.Lb ib.P (js.x J.v0)).2|)) (js.r J.v0)) (ofRatDown err)

end Defs

/-- **The packed energy check on the jet's boundary** at the certificate's data: the jet chain at
`cfgFull` (the same Boolean term as in `checkInvarianceJ`), the guards, the bound. No landed
`Slp.compose`. -/
def checkEnergyJ {n : ℕ} {α : Type} [CertArith α] (ib : PIBook) (jd : JetData)
    (c : TorusCertificate n α) : Bool :=
  jetFullOk ib jd c && enGuard n ib &&
    enOk n c.ham.jet (jetSlots (α := α) jd) ib c.params.E0 c.params.err

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}

/-- A complex rational minus a rational: the `ℓ¹` size bound. -/
theorem norm_qC_sub_le (z : ℚ × ℚ) (E0 : ℚ) :
    ‖qC z - ((E0 : ℝ) : ℂ)‖ ≤ |(z.1 : ℝ) - E0| + |(z.2 : ℝ)| := by
  have h := norm_qC_le (z.1 - E0, z.2)
  have e1 : qC (z.1 - E0, z.2) = qC z - ((E0 : ℝ) : ℂ) := by
    unfold qC
    push_cast
    ring
  rw [e1] at h
  refine h.trans (le_of_eq ?_)
  unfold qAbs1
  push_cast
  rfl

/-- **Soundness of the packed energy sub-check on the jet's boundary**: the conclusion of the
landed `checkEnergy_sound_of`, under its hypotheses. -/
theorem checkEnergyJ_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    {ib : PIBook} {jd : JetData} (h : checkEnergyJ ib jd c = true) :
    ‖KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ)‖ ≤ c.params.err := by
  have S := checkStatic_sound hs
  have hρ : (0 : ℝ) < c.weight.rho := by
    rw [S.hrho]; exact S.hρinf.trans S.hρinfρ
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.K θ ∈ c.D := by
    intro θ hθ
    rw [S.hrho] at hθ
    exact hE.1 θ hθ (Metric.mem_ball_self S.hμ)
  -- continuity of `H ∘ K` on the strip
  have hHd : DifferentiableOn ℂ c.H c.D :=
    (c.ham.contDiffOn_eval (isOpen_certDomain _ _ _ _) hH.1).differentiableOn (by simp)
  have hHK : ContinuousOn (fun θ => c.H (c.K θ)) (complexStrip n c.weight.rho) :=
    hHd.continuousOn.comp (c.emb.differentiable_eval n).continuous.continuousOn hKD
  simp only [checkEnergyJ, enGuard, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hjet, ⟨⟨hw, hdim⟩, hz⟩, hA⟩, hok⟩ := h
  -- the `v0` node and its zero mode
  have hv := (jetFullOk_sound hs hjet _ List.mem_cons_self).congr
    (g := fun θ => c.H (c.K θ)) fun θ _ => c.ham.jet_v0 _
  have havg := PEnc.average hw hdim (slot_zslot hz) hA hρ hHK hv
  set z := ptDigit n ib.Lb ib.P ((jetSlots (α := α) jd).x c.ham.jet.v0)
  have hdig : qC z = ((slotAt ib.Lb.width (zslot n ib.Lb)
      ((jetSlots (α := α) jd).x c.ham.jet.v0).re : ℂ) + Complex.I * (slotAt ib.Lb.width
      (zslot n ib.Lb) ((jetSlots (α := α) jd).x c.ham.jet.v0).im : ℂ)) / 2 ^ ib.P := by
    simp only [z]
    unfold qC ptDigit
    push_cast
    ring
  have hEa : torusAverage (fun v : Fin n → ℝ => c.H (c.K fun j => (v j : ℂ))) =
      KAM.Iso.energyAverage c.H c.K := rfl
  rw [hEa, ← hdig] at havg
  have hb := (LawfulCertArith.ble_sound _ _ hok).trans (LawfulCertArith.ofRatDown_le _)
  have hu := LawfulCertArith.upAdd_ge (ofRatUp (|z.1 - c.params.E0| + |z.2|) : α)
    ((jetSlots (α := α) jd).r c.ham.jet.v0)
  have hq := LawfulCertArith.ofRatUp_ge (α := α) (|z.1 - c.params.E0| + |z.2|)
  have hz' := norm_qC_sub_le z c.params.E0
  have hcast : ((|z.1 - c.params.E0| + |z.2| : ℚ) : ℝ) = |(z.1 : ℝ) - c.params.E0| + |(z.2 : ℝ)| :=
    by push_cast; rfl
  rw [hcast] at hq
  calc ‖KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ)‖
      ≤ ‖KAM.Iso.energyAverage c.H c.K - qC z‖ + ‖qC z - ((c.params.E0 : ℝ) : ℂ)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ val ((jetSlots (α := α) jd).r c.ham.jet.v0) + (|(z.1 : ℝ) - c.params.E0| + |(z.2 : ℝ)|) :=
        add_le_add havg hz'
    _ ≤ c.params.err := by linarith

omit [LawfulCertArith α] in
/-- The packed energy check on the jet's boundary from its parts. -/
theorem checkEnergyJ_of {c : TorusCertificate n α} {ib : PIBook} {jd : JetData}
    (hjet : jetFullOk ib jd c = true) (hg : enGuard n ib = true)
    (hok : enOk n c.ham.jet (jetSlots (α := α) jd) ib c.params.E0 c.params.err = true) :
    checkEnergyJ ib jd c = true := by
  simp only [checkEnergyJ, hjet, hg, hok, Bool.and_self]

end Sound

end KAM.CertificateSharp.Packed
