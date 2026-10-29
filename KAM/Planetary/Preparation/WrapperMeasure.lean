/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PG.Setting
public import KAM.ODE.Basic
public import KAM.Frozen.Planetary.Defs.Phase

/-!
# The saturated torus family (P11A-P10, `stepP:p11:wr-meas`, first half)

`A = ⋃_k (B + ι_k)`: the set of all points of all tori of the family is Borel, invariant under the
integer angle lattice and of positive measure when the parameter cell image `B` is.
-/

@[expose] public noncomputable section
open Set MeasureTheory
namespace KAM.Planetary

section Measure

variable {N : ℕ}

/-- All points of all tori of the family. -/
def p11TorusUnion (good : Set (Fin N → ℝ)) (torus : (Fin N → ℝ) → (Fin N → ℝ) → Phase N) :
    Set (Phase N) := {z | ∃ b ∈ good, ∃ θ, z = torus b θ}

theorem p11TorusUnion_eq {good : Set (Fin N → ℝ)} {torus : (Fin N → ℝ) → (Fin N → ℝ) → Phase N}
    (hlat : ∀ b ∈ good, ∀ θ (k : Fin N → ℤ),
      torus b (θ + fun i => (k i : ℝ)) = torus b θ + KAM.ODE.angleShift k) :
    p11TorusUnion good torus = ⋃ k : Fin N → ℤ, (fun z => z + KAM.ODE.angleShift k) ''
      ((fun z : Phase N => torus z.2 z.1) '' (unitCube N ×ˢ good)) := by
  ext z
  simp only [p11TorusUnion, mem_setOf_eq, mem_iUnion, mem_image]
  constructor
  · rintro ⟨b, hb, θ, rfl⟩
    refine ⟨fun i => ⌊θ i⌋, _, ⟨(fun i => Int.fract (θ i), b), ⟨fun i _ => ?_, hb⟩, rfl⟩, ?_⟩
    · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · have : θ = (fun i => Int.fract (θ i)) + fun i => ((⌊θ i⌋ : ℤ) : ℝ) := by
        funext i; exact (Int.fract_add_floor (θ i)).symm
      show torus b (fun i => Int.fract (θ i)) + KAM.ODE.angleShift (fun i => ⌊θ i⌋) = torus b θ
      rw [← hlat b hb, ← this]
  · rintro ⟨k, _, ⟨⟨θ, b⟩, ⟨-, hb⟩, rfl⟩, rfl⟩
    exact ⟨b, hb, θ + fun i => (k i : ℝ), (hlat b hb θ k).symm⟩

theorem p11TorusUnion_props {good : Set (Fin N → ℝ)}
    {torus : (Fin N → ℝ) → (Fin N → ℝ) → Phase N}
    (hlat : ∀ b ∈ good, ∀ θ (k : Fin N → ℤ),
      torus b (θ + fun i => (k i : ℝ)) = torus b θ + KAM.ODE.angleShift k)
    (hB : MeasurableSet ((fun z : Phase N => torus z.2 z.1) '' (unitCube N ×ˢ good)))
    (hpos : 0 < volume ((fun z : Phase N => torus z.2 z.1) '' (unitCube N ×ˢ good))) :
    MeasurableSet (p11TorusUnion good torus) ∧
      (∀ k : Fin N → ℤ, (fun z => z + KAM.ODE.angleShift k) '' p11TorusUnion good torus =
        p11TorusUnion good torus) ∧ 0 < volume (p11TorusUnion good torus) := by
  refine ⟨?_, fun k => ?_, ?_⟩
  · rw [p11TorusUnion_eq hlat]
    exact MeasurableSet.iUnion fun k =>
      (MeasurableEquiv.addRight (KAM.ODE.angleShift k)).measurableSet_image.2 hB
  · ext z
    constructor
    · rintro ⟨_, ⟨b, hb, θ, rfl⟩, rfl⟩
      exact ⟨b, hb, θ + fun i => (k i : ℝ), (hlat b hb θ k).symm⟩
    · rintro ⟨b, hb, θ, rfl⟩
      refine ⟨torus b (θ - fun i => (k i : ℝ)), ⟨b, hb, _, rfl⟩, ?_⟩
      have := hlat b hb (θ - fun i => (k i : ℝ)) k
      simp only [sub_add_cancel] at this
      exact this.symm
  · refine lt_of_lt_of_le hpos (measure_mono ?_)
    rintro z ⟨⟨θ, b⟩, ⟨-, hb⟩, rfl⟩
    exact ⟨b, hb, θ, rfl⟩

end Measure

end KAM.Planetary

end
