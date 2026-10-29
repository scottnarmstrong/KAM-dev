/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Hamiltonian.Transport
public import KAM.Planetary.Hamiltonian.Liouville
public import KAM.Kepler.Basic
public import KAM.Frozen.Planetary.Defs.IsPhysicalTorus

/-!
# Transport helpers for the wrapper (P11A-P10, `stepP:p11:wr-tor`)

Reindexing `Fin d ≃ Fin e` of a physical torus, and changing the Hamiltonian of a lattice torus
by one that agrees with it on an open neighbourhood of its range.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace KAM.Planetary

section Transport

theorem p11_isPhysicalTorus_cast {d e : ℕ} (h : d = e) {H : Phase e → ℝ} {w : Fin d → ℝ}
    {K : (Fin d → ℝ) → Phase d} (hK : IsPhysicalTorus (H ∘ KAM.Kepler.phaseCast h) w K) :
    IsPhysicalTorus H (fun i => w (Fin.cast h.symm i))
      (fun θ => KAM.Kepler.phaseCast h (K (fun i => θ (Fin.cast h i)))) := by
  subst h
  have hpc : ∀ z : Phase d, KAM.Kepler.phaseCast (rfl : d = d) z = z := fun z => by
    ext i <;> rfl
  have e3 : H ∘ KAM.Kepler.phaseCast (rfl : d = d) = H := funext fun z => by
    simp [Function.comp, hpc]
  rw [e3] at hK
  have e1 : (fun θ : Fin d → ℝ => KAM.Kepler.phaseCast (rfl : d = d)
      (K (fun i => θ (Fin.cast rfl i)))) = K := funext fun θ => by rw [hpc]; rfl
  rw [e1]
  exact hK

theorem p11_latticeTorus_congr {d : ℕ} {L : (Fin d → ℤ) → Phase d} {G G' : Phase d → ℝ}
    {Oc O : Set (Phase d)} {w : Fin d → ℝ} {K : (Fin d → ℝ) → Phase d}
    (hK : IsLatticeTorus L G Oc w K) (hO : IsOpen O) (hsub : Oc ⊆ O) (hEq : EqOn G G' O) :
    IsLatticeTorus L G' O w K := by
  obtain ⟨⟨hKan, hKO⟩, hlat, hinj, hD, hLag, hflow⟩ := hK
  have hev : ∀ θ, G' =ᶠ[𝓝 (K θ)] G := fun θ =>
    Filter.eventually_of_mem (hO.mem_nhds (hsub (hKO θ).1)) fun x hx => (hEq hx).symm
  refine ⟨⟨hKan, fun θ => ⟨hsub (hKO θ).1, ((hKO θ).2).congr_of_eventuallyEq (hev θ)⟩⟩, hlat,
    hinj, hD, hLag, fun θ t => ?_⟩
  have hv : KAM.hamiltonianVectorField G' (K (θ + t • w)) =
      KAM.hamiltonianVectorField G (K (θ + t • w)) := by
    unfold KAM.hamiltonianVectorField
    rw [(hev (θ + t • w)).fderiv_eq]
  rw [hv]
  exact hflow θ t

end Transport

end KAM.Planetary

end
