/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.ChartMem

/-!
# P Part 5: the chart `phi` and the location of the torus (`bpP:p5:phi-chart`, `bpP:p5:location`)

`phi_chart` shows that `phi = realAverageMap ∘ oscillatorPolar` is a chart on the open set
`phiDomain`, equivariant under the lattice and injective modulo it; `location` places the scaled
action collar inside `phiDomain` and its image inside the cylinder.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-CH.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

theorem phi_chart (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    IsOpen (phiDomain d r mu) ∧ IsChart 1 (phi d r mu h) (phiDomain d r mu) ∧
    (∀ z ∈ phiDomain d r mu, ∀ k : Fin (a+b) → ℤ, z+fullShift k ∈ phiDomain d r mu ∧
      phi d r mu h (z+fullShift k) = phi d r mu h z+fastShift (blockFast k)) ∧
    (∀ z ∈ phiDomain d r mu, ∀ z' ∈ phiDomain d r mu, ∀ k : Fin a → ℤ,
      phi d r mu h z' = phi d r mu h z+fastShift k → ∃ m : Fin (a+b) → ℤ, z'=z+fullShift m) := by
  obtain ⟨-, hinj, -, -, -, -, -, hper, hreal, hchart, -⟩ := (avg d r mu h).choose_spec
  have hshift : ∀ z ∈ phiDomain d r mu, ∀ k : Fin (a+b) → ℤ, z+fullShift k ∈ phiDomain d r mu ∧
      phi d r mu h (z+fullShift k) = phi d r mu h z+fastShift (blockFast k) := fun z hz k => by
    refine ⟨phiDomain_fullShift hz k, ?_⟩
    have hz' := phiDomain_fullShift hz k
    unfold phi
    simp only [Function.comp_apply, oscillatorPolar_fullShift]
    refine realAverageMap_add_fastShift hper hreal (polar_mem_averagingDomain h hz) _ ?_
    have := polar_mem_averagingDomain h hz'
    rwa [oscillatorPolar_fullShift] at this
  refine ⟨isOpen_phiDomain, ?_, hshift, ?_⟩
  · have := (disc_measure_chart.1.mono (fun z hz => phiDomain_slow_pos h hz)).comp hchart
      (fun z hz => polar_mem_averagingDomain h hz)
    rw [one_mul] at this
    exact this
  · intro z hz z' hz' k hk
    have hm0 : blockFast (Fin.append k (0 : Fin b → ℤ)) = k := by
      funext i; simp [blockFast, Fin.append_left]
    obtain ⟨hz1, hphi1⟩ := hshift z hz (Fin.append k (0 : Fin b → ℤ))
    rw [hm0] at hphi1
    have heq : phi d r mu h z' = phi d r mu h (z + fullShift (Fin.append k (0 : Fin b → ℤ))) := by
      rw [hphi1]; exact hk
    have h1 := polar_mem_averagingDomain h hz'
    have h2 := polar_mem_averagingDomain h hz1
    have hp : oscillatorPolar z' = oscillatorPolar (z + fullShift (Fin.append k (0 : Fin b → ℤ))) := by
      apply KAM.realInclusion₂_injective
      apply hinj h1 h2
      rw [hreal _ h1, hreal _ h2]
      exact congrArg (KAM.realInclusion₂ (a+b)) heq
    rw [oscillatorPolar_fullShift, hm0] at hp
    exact oscillatorPolar_lattice (phiDomain_slow_pos h hz') (phiDomain_slow_pos h hz) k hp

end KAM.Planetary

end
