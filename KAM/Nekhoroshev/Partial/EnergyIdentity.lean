/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.RealSystem
public import KAM.Head.Frequency

/-!
# The frequency-free energy identity (Part 11, package N11-L1)

Along an orbit `y` of `liftFast h + g + fs` in the extended phase space, `fs ∘ y` has
derivative `∂_θ fs · ω(I) + {fs, g}_c` (`bpN:p11:eq:lie`, step `ef-id`): the Poisson bracket of
`fs` with `fs` vanishes and `h` depends on the fast action only.  Consequently (step `ef-C`) the
pairing of `ω(I(0))` with the transverse part `ΔI - P ΔI` of the fast displacement is controlled
by the oscillation of `fs`, with no bound on `ω`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.NormalForm

variable {n k : ℕ}

/-! ### Reality and the class of the total Hamiltonian -/

private theorem fastAction_extCx (z : ER n k) :
    fastAction (extCx z) = KAM.realInclusion n (fastAction z) := by
  ext i; simp [fastAction, extCx]

private theorem fast_mem_polyNbhd (b : PartialBlock n k) {R : ℝ} {z : EC n k}
    (hz : z.2 ∈ polyNbhd b.base R) :
    fastAction z ∈ polyNbhd {KAM.realInclusion n b.Ic} R := by
  obtain ⟨J, ⟨x, -, rfl⟩, hlt⟩ := hz
  refine ⟨KAM.realInclusion n b.Ic, rfl, lt_of_le_of_lt ?_ hlt⟩
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have := norm_le_pi_norm (z.2 - Fin.append (fun i => (b.Ic i : ℂ))
    (Fin.append (fun i => ((x.1 i / b.lam : ℝ) : ℂ)) (fun i => ((x.2 i / b.lam : ℝ) : ℂ))))
    (Fin.castAdd (k + k) i)
  simpa [fastAction] using this

private theorem differentiableAt_fastAction (z : EC n k) :
    DifferentiableAt ℂ (fun z : EC n k => fastAction z) z :=
  differentiableAt_pi.2 fun i =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + (k + k)) => ℂ)
      (Fin.castAdd (k + k) i)).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ)
        (Fin (n + (k + k)) → ℂ))).differentiableAt

private theorem differentiableOn_liftFast (b : PartialBlock n k) {R s : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} R)) :
    DifferentiableOn ℂ (liftFast h : EC n k → ℂ) (Dom n b.base R s) := fun z hz =>
  ((hh _ (fast_mem_polyNbhd b hz.2)).differentiableAt
    ((isOpen_polyNbhd _ R).mem_nhds (fast_mem_polyNbhd b hz.2))).comp_differentiableWithinAt z
    (differentiableAt_fastAction z).differentiableWithinAt

/-- The fast part of the Hamiltonian is an extended-class function. -/
theorem ext_class_liftFast (b : PartialBlock n k) {R s m M : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : RealFastConvex b.Ic R m M h) : ext_class b R s (liftFast h) :=
  ⟨⟨differentiableOn_liftFast b hh.hol, fun _ _ _ => rfl⟩, fun (x : ER n k) hx => by
    have h0 := fast_mem_polyNbhd b (z := extCx x) hx.2
    rw [fastAction_extCx] at h0
    have h1 := hh.real _ h0
    rw [← fastAction_extCx] at h1
    exact h1⟩

theorem ext_class_add (b : PartialBlock n k) {R s : ℝ} {u v : EC n k → ℂ}
    (hu : ext_class b R s u) (hv : ext_class b R s v) : ext_class b R s (u + v) :=
  ⟨⟨hu.1.differentiableOn.add hv.1.differentiableOn, fun j z hz => by
    simp only [Pi.add_apply, hu.1.periodic j z hz, hv.1.periodic j z hz]⟩, fun x hx => by
    simp [Pi.add_apply, hu.2 x hx, hv.2 x hx]⟩

end KAM.Nekhoroshev

end
