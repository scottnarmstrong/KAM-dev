/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorChain.Basic

/-!
# Chains of normalization steps: holomorphy and bounds of the pushed-forward remainders

For a chain `l` of steps with `OscDomOK`:

* `oscChainTheta_oscBound`: a point within `r + c` of the origin (coordinatewise) lies in
  `oscChainDom l` and its image under `Θ_l` is within `r + c + ∑ ε_k δ_k`;
* `differentiableOn_oscChainRem`: `oscChainRem l Q` is holomorphic on the open set `oscChainDom l`;
* `norm_oscChainRem_le`: on `OscBound r δc` points, `‖oscChainRem l Q‖ ≤ oscChainBound n l Q`.
-/

@[expose] public noncomputable section

open Set KAM.Canonical

namespace KAM.EffectiveStability

open CartPoly

variable {n : ℕ}

/-- The open domain on which the composite flow `Θ_l` is defined with every intermediate point in
the half interior of the next polydisc. -/
def oscChainDom : List OscStep → Set ((Fin n → ℂ) × (Fin n → ℂ))
  | [] => univ
  | s :: l => oscChainDom l ∩ oscChainTheta l ⁻¹' cpolyOpen ((s.ρ : ℝ) - (s.δ : ℝ) / 2)

theorem cpolyOpen_sub_subset_gaugeInterior {s : OscStep} (hs : OscStepOK n s) :
    cpolyOpen (n := n) ((s.ρ : ℝ) - (s.δ : ℝ) / 2) ⊆
      gaugeInterior (gaugeScalar (s.δ : ℝ) hs.delta_posℝ) (cpolyOpen (s.ρ : ℝ)) (1 / 2) := by
  intro z hz
  refine mem_gaugeInterior_cpolyOpen hs.delta_posℝ (by norm_num) fun i => ?_
  have h1 := (hz i).1
  have h2 := (hz i).2
  constructor <;> linarith

theorem norm_coord_le_prod (v : (Fin n → ℂ) × (Fin n → ℂ)) (i : Fin n) :
    ‖v.1 i‖ ≤ ‖v‖ ∧ ‖v.2 i‖ ≤ ‖v‖ :=
  ⟨(norm_le_pi_norm v.1 i).trans (le_max_left _ _),
    (norm_le_pi_norm v.2 i).trans (le_max_right _ _)⟩

/-- A step flow moves each coordinate by at most `ε δ`. -/
theorem oscStepFlow_oscBound {s : OscStep} (hs : OscStepOK n s) {r : Fin n → ℝ} {c : ℝ}
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ cpolyOpen (n := n) ((s.ρ : ℝ) - (s.δ : ℝ) / 2))
    (hb : OscBound r c z) : OscBound r (c + (s.ε : ℝ) * (s.δ : ℝ)) (oscStepFlow s z) := by
  have hδ := hs.delta_posℝ
  have hS := hs.smallField hδ
  have hz' := cpolyOpen_sub_subset_gaugeInterior hs hz
  obtain ⟨-, -, -, hd⟩ := flow_a hS hz'
  have h1 := hd 1 ⟨by norm_num, le_rfl⟩
  rw [norm_gaugeScalar_apply, div_le_iff₀ hδ, abs_one, one_mul] at h1
  intro i
  have hc := norm_coord_le_prod (oscStepFlow s z - z) i
  have e1 : ‖(oscStepFlow s z).1 i‖ ≤ ‖z.1 i‖ + ‖(oscStepFlow s z - z).1 i‖ := by
    simpa using norm_add_le (z.1 i) ((oscStepFlow s z - z).1 i)
  have e2 : ‖(oscStepFlow s z).2 i‖ ≤ ‖z.2 i‖ + ‖(oscStepFlow s z - z).2 i‖ := by
    simpa using norm_add_le (z.2 i) ((oscStepFlow s z - z).2 i)
  have h1' : ‖oscStepFlow s z - z‖ ≤ (s.ε : ℝ) * (s.δ : ℝ) := h1
  have := hb i
  constructor <;> linarith [hc.1, hc.2]

section Chain

variable {r : Fin n → ℝ} {δc : ℝ}

theorem oscChainDom_isOpen_and_differentiableOn {l : List OscStep}
    (hl : ∀ s ∈ l, OscStepOK n s) :
    IsOpen (oscChainDom (n := n) l) ∧ DifferentiableOn ℂ (oscChainTheta (n := n) l)
      (oscChainDom l) := by
  induction l with
  | nil => exact ⟨isOpen_univ, differentiableOn_id⟩
  | cons s l ih =>
    obtain ⟨ho, hd⟩ := ih (fun t ht => hl t (by simp [ht]))
    have hs := hl s (by simp)
    have hδ := hs.delta_posℝ
    have hS := hs.smallField hδ
    have hfl : DifferentiableOn ℂ (oscStepFlow (n := n) s)
        (gaugeInterior (gaugeScalar (s.δ : ℝ) hδ) (cpolyOpen (s.ρ : ℝ)) (1 / 2)) :=
      (flow_b hS).2.1 1 ⟨by norm_num, le_rfl⟩
    refine ⟨ContinuousOn.isOpen_inter_preimage hd.continuousOn ho (isOpen_cpolyOpen _), ?_⟩
    show DifferentiableOn ℂ (oscStepFlow s ∘ oscChainTheta l) (oscChainDom l ∩
      oscChainTheta l ⁻¹' cpolyOpen ((s.ρ : ℝ) - (s.δ : ℝ) / 2))
    exact hfl.comp (hd.mono inter_subset_left) (fun z hz =>
      cpolyOpen_sub_subset_gaugeInterior hs hz.2)

theorem OscChainOK.stepsOK {Nact P : CartPoly} :
    ∀ {l : List OscStep} {Q : CartPoly}, OscChainOK n Nact P l Q → ∀ s ∈ l, OscStepOK n s
  | [], _, _ => fun s hs => by simp at hs
  | t :: l, Q, h => fun s hs => by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact h.1
    · exact OscChainOK.stepsOK h.2.2 s hs

theorem oscChainTheta_oscBound {l : List OscStep} (hl : ∀ s ∈ l, OscStepOK n s)
    (hD : OscDomOK n r δc l) {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : OscBound r δc z) :
    z ∈ oscChainDom l ∧ OscBound r (δc + (oscTail l : ℝ)) (oscChainTheta l z) := by
  induction l with
  | nil => exact ⟨mem_univ _, by simpa [oscTail, oscChainTheta] using hz⟩
  | cons s l ih =>
    obtain ⟨h1, h2, h3⟩ := hD
    obtain ⟨hzd, hzb⟩ := ih (fun t ht => hl t (by simp [ht])) h3
    have hs := hl s (by simp)
    have hmem : oscChainTheta l z ∈ cpolyOpen (n := n) ((s.ρ : ℝ) - (s.δ : ℝ) / 2) := by
      intro i
      constructor <;> linarith [(hzb i).1, (hzb i).2, h2 i]
    refine ⟨⟨hzd, hmem⟩, ?_⟩
    have := oscStepFlow_oscBound hs hmem hzb
    have e : δc + (oscTail (s :: l) : ℝ) = δc + (oscTail l : ℝ) + (s.ε : ℝ) * (s.δ : ℝ) := by
      simp only [oscTail]; push_cast; ring
    rw [e]
    exact this

theorem differentiableOn_oscChainRem {l : List OscStep} (hl : ∀ s ∈ l, OscStepOK n s) :
    ∀ Q : CartPoly, DifferentiableOn ℂ (oscChainRem (n := n) l Q) (oscChainDom l) := by
  induction l with
  | nil => intro Q; exact differentiableOn_const 0
  | cons s l ih =>
    intro Q
    have hl' : ∀ t ∈ l, OscStepOK n t := fun t ht => hl t (by simp [ht])
    obtain ⟨-, hd⟩ := oscChainDom_isOpen_and_differentiableOn hl'
    have hs := hl s (by simp)
    have hδ := hs.delta_posℝ
    have hS := hs.smallField hδ
    have h1 : DifferentiableOn ℂ (fun z => stepRem s.gen Q (s.ρ : ℝ) s.order (oscChainTheta l z))
        (oscChainDom (n := n) (s :: l)) :=
      (differentiableOn_stepRem hS s.order).comp (hd.mono inter_subset_left) (fun z hz =>
        cpolyOpen_sub_subset_gaugeInterior hs hz.2)
    exact h1.add ((ih hl' s.out).mono inter_subset_left)

theorem norm_oscChainRem_le {Nact P : CartPoly} :
    ∀ {l : List OscStep} {Q : CartPoly}, CartFits n Q → OscChainOK n Nact P l Q →
      OscDomOK n r δc l → ∀ {z : (Fin n → ℂ) × (Fin n → ℂ)}, OscBound r δc z →
      ‖oscChainRem l Q z‖ ≤ (oscChainBound n l Q : ℝ)
  | [], Q, _, _, _, z, _ => by simp [oscChainRem, oscChainBound]
  | s :: l, Q, hQ, hok, hD, z, hz => by
    obtain ⟨hs, -, hrest⟩ := hok
    obtain ⟨-, h2, h3⟩ := hD
    obtain ⟨-, hzb⟩ := oscChainTheta_oscBound (OscChainOK.stepsOK hrest) h3 hz
    have hδ := hs.delta_posℝ
    have hS := hs.smallField hδ
    have hmem : oscChainTheta l z ∈ cpolyOpen (n := n) ((s.ρ : ℝ) - (s.δ : ℝ) / 2) := by
      intro i
      constructor <;> linarith [(hzb i).1, (hzb i).2, h2 i]
    have h1 := norm_stepRem_le hs.fits_gen hQ hS (List.replicate n s.ρ)
      (fun i => by rw [replicate_getD_oscRad]) hs.order_pos
      (cpolyOpen_sub_subset_gaugeInterior hs hmem)
    have h4 := norm_oscChainRem_le hs.fits_out hrest h3 hz
    show ‖stepRem s.gen Q (s.ρ : ℝ) s.order (oscChainTheta l z) + oscChainRem l s.out z‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    simp only [oscChainBound]
    push_cast
    exact add_le_add h1 h4

end Chain

end KAM.EffectiveStability
