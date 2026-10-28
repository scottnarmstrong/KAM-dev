/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.OscillatorBracket
public import KAM.Nekhoroshev.NormalForm.Homological
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# P Part 2: the oscillator generator (`bpP:p2:osc-iter`, generator clauses)

`oscGen` is the homological polynomial of the oscillator step. Its flat transport is the
parametric generator `homGenParam` with the frequency field `x ↦ freq h (firstBlock x)`, so the
class and the weighted bound follow from the upstream `homological_param`, applied at every flat
parameter on a small ball (`D = {x}`). Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`,
package P23-13.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- P2 oscillator homological polynomial, same coefficients as Weighted.coeff. -/
def oscGen {n m : ℕ} (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam (n + m)) : CHam (n + m) :=
  fun z => ∑' k : Fin n → ℤ, (zBall n K \ {0}).indicator (fun k =>
    coeff (oscFunction f) (oscPack z).2 k /
      (2 * (π : ℂ) * Complex.I * dotC k (freq h (firstBlock (b := m) z.2))) *
        KAM.character k (firstBlock (b := m) z.1)) k

section Flat

variable {n m : ℕ} {D : Set (Fin n → ℝ)}

/-- The flat frequency field `x ↦ ω(I)` of the flat parameter `(I, p, q)`. -/
def oscFreq (n m : ℕ) (h : (Fin n → ℂ) → ℂ) : (Fin (n + (m + m)) → ℂ) → Fin n → ℂ :=
  fun x => freq h (firstBlock (b := m + m) x)

theorem oscFunction_oscGen (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam (n + m))
    (y : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ)) :
    oscFunction (oscGen K h f) y = homGenParam K {0} (oscFreq n m h) (oscFunction f) y := by
  have e : oscFunction (oscGen K h f) y = oscGen K h f (oscUnpack y) := rfl
  rw [e]
  unfold oscGen homGenParam oscFreq
  rw [oscPack_oscUnpack]
  have h1 : firstBlock (b := m) (oscUnpack (m := m) y).2 = firstBlock (b := m + m) y.2 := by
    funext i; simp [oscUnpack, firstBlock, Fin.append_left]
  have h2 : firstBlock (b := m) (oscUnpack (m := m) y).1 = y.1 := by
    funext i; simp [oscUnpack, firstBlock, Fin.append_left]
  simp only [h1, h2]

theorem differentiableAt_oscFreq {r : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D r)) {x : Fin (n + (m + m)) → ℂ}
    (hx : firstBlock (b := m + m) x ∈ KAM.actionNbhd D r) :
    DifferentiableAt ℂ (oscFreq n m h) x := by
  have h1 : DifferentiableAt ℂ (freq h) (firstBlock (b := m + m) x) :=
    differentiableAt_freq (isOpen_actionNbhd D r) hh hx
  have h2 : DifferentiableAt ℂ (fun x : Fin (n + (m + m)) → ℂ => firstBlock (b := m + m) x) x :=
    differentiableAt_pi.2 fun i => differentiableAt_apply _ _
  exact h1.comp x h2

/-- Local form of the homological solve at a flat parameter `x`, on a small ball. -/
theorem osc_hom_local {r rp rq S K α δ : ℝ} {h : (Fin n → ℂ) → ℂ} {f : CHam (n + m)}
    (hS : 0 < S) (hK : 0 ≤ K) (hα : 0 < α)
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D r))
    (hdiv : DivisorBound (KAM.actionNbhd D r) K {0} h α)
    (hf : oscClass D r rp rq S f) (hδ : oscBound D r rp rq S f δ)
    {x : Fin (n + (m + m)) → ℂ} (hx : x ∈ oscParams (m := m) D r rp rq) :
    ∃ ε : ℝ, 0 < ε ∧ ball x ε ⊆ oscParams (m := m) D r rp rq ∧
      InClass ({x} : Set (Fin (n + (m + m)) → ℂ)) ε S
        (homGenParam K {0} (oscFreq n m h) (oscFunction f)) ∧
      WBound ({x} : Set (Fin (n + (m + m)) → ℂ)) ε S
        (homGenParam K {0} (oscFreq n m h) (oscFunction f)) (δ / (2 * π * α)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_oscParams (m := m) D r rp rq) x hx
  refine ⟨ε, hε, hball, ?_⟩
  have hF := hf.flat
  have hc : InClass ({x} : Set (Fin (n + (m + m)) → ℂ)) ε S (oscFunction f) :=
    hF.inClass hball le_rfl
  have hb : WBound ({x} : Set (Fin (n + (m + m)) → ℂ)) ε S (oscFunction f) δ := by
    intro I hI
    rw [polyNbhd_singleton] at hI
    exact hδ I (hball hI)
  have hω : DifferentiableOn ℂ (oscFreq n m h) (polyNbhd ({x} : Set (Fin (n + (m + m)) → ℂ)) ε) := by
    intro I hI
    rw [polyNbhd_singleton] at hI
    exact (differentiableAt_oscFreq hh (hball hI).1).differentiableWithinAt
  have hdir : ∀ I ∈ polyNbhd ({x} : Set (Fin (n + (m + m)) → ℂ)) ε, ∀ k ∈ zBall n K \ {0},
      α / 1 ≤ ‖dotC k (oscFreq n m h I)‖ := by
    intro I hI k hk
    rw [polyNbhd_singleton] at hI
    rw [div_one]
    exact hdiv _ (hball hI).1 k hk
  obtain ⟨c1, -, -, -, -, -, -, -, c9, -⟩ :=
    homological_param (ω := oscFreq n m h) (q := 1) le_rfl hα hS hK hω hdir hc hb
  refine ⟨c1, ?_⟩
  simpa using c9

/-- Class and weighted bound of the oscillator generator. -/
theorem oscGen_class_bound {r rp rq S K α δ : ℝ} {h : (Fin n → ℂ) → ℂ} {f : CHam (n + m)}
    (hS : 0 < S) (hK : 0 ≤ K) (hα : 0 < α)
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D r))
    (hdiv : DivisorBound (KAM.actionNbhd D r) K {0} h α)
    (hf : oscClass D r rp rq S f) (hδ : oscBound D r rp rq S f δ) :
    oscClass D r rp rq S (oscGen K h f) ∧
      oscBound D r rp rq S (oscGen K h f) (δ / (2 * π * α)) := by
  have loc := fun {x} (hx : x ∈ oscParams (m := m) D r rp rq) =>
    osc_hom_local hS hK hα hh hdiv hf hδ hx
  have hflat : FClass S (oscParams (m := m) D r rp rq)
      (homGenParam K {0} (oscFreq n m h) (oscFunction f)) := by
    refine ⟨fun z hz => ?_, fun j z hz => ?_⟩
    · obtain ⟨ε, hε, hball, hI, -⟩ := loc hz.2
      refine (hI.differentiableOn.differentiableAt ?_).differentiableWithinAt
      refine (KAM.isOpen_complexStrip n S |>.prod (isOpen_polyNbhd _ _)).mem_nhds ?_
      exact ⟨hz.1, by rw [polyNbhd_singleton]; exact mem_ball_self hε⟩
    · obtain ⟨ε, hε, hball, hI, -⟩ := loc hz.2
      exact hI.periodic j z ⟨hz.1, by rw [polyNbhd_singleton]; exact mem_ball_self hε⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h1 : oscGen K h f = (homGenParam K {0} (oscFreq n m h) (oscFunction f)) ∘ oscPackL := by
      funext z
      have := oscFunction_oscGen K h f (oscPack z)
      simp only [oscFunction, Function.comp, s_osc_data] at this
      exact this
    rw [h1]
    exact hflat.1.comp (oscPackL (m := m)).differentiableOn fun z hz => hz
  · intro j z hz
    have h2 := hflat.2 j (oscPack z) hz
    have e : ∀ w, oscGen K h f w = homGenParam K {0} (oscFreq n m h) (oscFunction f) (oscPack w) :=
      fun w => by
        have := oscFunction_oscGen K h f (oscPack w)
        simp only [oscFunction, Function.comp, s_osc_data] at this
        exact this
    rw [e, e]
    have hadd : oscPack (z.1 + Pi.single (Fin.castAdd m j) 1, z.2) =
        ((oscPack z).1 + Pi.single j 1, (oscPack z).2) := by
      have h1 : ((z.1 + Pi.single (Fin.castAdd m j) 1, z.2) : CPhase (n + m)) =
          z + (Pi.single (Fin.castAdd m j) 1, 0) := by ext <;> simp
      rw [h1]
      have h2 := (oscPackL (m := m)).map_add z (Pi.single (Fin.castAdd m j) 1, 0)
      change oscPack (z + _) = oscPack z + oscPack _ at h2
      rw [h2, oscPack_theta]
      ext <;> simp
    rw [hadd]
    exact h2
  · refine oscBound_of_flat hS (fun y _ => oscFunction_oscGen K h f y) fun x hx => ?_
    obtain ⟨ε, hε, hball, -, hB⟩ := loc hx
    exact hB x (by rw [polyNbhd_singleton]; exact mem_ball_self hε)

end Flat

end KAM.Planetary

end
