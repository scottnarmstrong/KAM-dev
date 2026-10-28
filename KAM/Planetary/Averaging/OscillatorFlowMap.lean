/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.OscillatorFlow
public import KAM.Canonical.VectorField
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# P Part 2: the time-one map of an oscillator Hamiltonian

For `φ` of oscillator class with weighted bound `E` and `E/d ≤ 1/2` (`d = min (ρσ) (ρpρq)`), the
abstract flow theory `flow_a`–`flow_e` with the gauge `oscScale` gives the properties of
`Ψ = flow X_φ 𝒪 1` on the domains `V ⊆ U ⊆ 𝒪`: holomorphy, maps-to, injectivity, inverse flow,
fast-lattice equivariance, symplecticity, gauge displacement and derivative bounds, reality.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-13.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

section Shift

variable {n m : ℕ} {D : Set (Fin n → ℝ)}

/-- The translation of the fast angles by `a`. -/
def fastShift {n m : ℕ} (a : Fin n → ℂ) : CPhase (n + m) := (Fin.append a (0 : Fin m → ℂ), 0)

theorem fastShift_add (a b : Fin n → ℂ) : fastShift (m := m) (a + b) = fastShift a + fastShift b := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [fastShift, Fin.append_left, Fin.append_right]
  · simp [fastShift]

theorem fastShift_zero : fastShift (m := m) (0 : Fin n → ℂ) = 0 := by
  refine Prod.ext (funext fun i => ?_) rfl
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [fastShift, Fin.append_left, Fin.append_right]

theorem oscDom_add_shift {r rp rq S : ℝ} {a : Fin n → ℂ} (ha : ∀ i, (a i).im = 0)
    {z : CPhase (n + m)} (hz : z ∈ oscDom (m := m) D r rp rq S) :
    z + fastShift a ∈ oscDom (m := m) D r rp rq S := by
  obtain ⟨z1, z2, z3, z4⟩ := mem_oscDom_iff.1 hz
  refine mem_oscDom_iff.2 ⟨fun i => ?_, ?_, ?_, ?_⟩
  · simpa [fastShift, Fin.append_left, ha i] using z1 i
  · simpa [fastShift] using z2
  · simpa [fastShift] using z3
  · have : lastBlock (a := n) (z + fastShift (m := m) a).1 = lastBlock (a := n) z.1 := by
      funext i; simp [fastShift, lastBlock, Fin.append_right]
    rw [this]; exact z4

theorem oscDom_shift_image {r rp rq S : ℝ} {a : Fin n → ℂ} (ha : ∀ i, (a i).im = 0) :
    (fun w => w + fastShift (m := m) a) '' oscDom (m := m) D r rp rq S =
      oscDom (m := m) D r rp rq S := by
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact oscDom_add_shift ha hw
  · intro w hw
    refine ⟨w + fastShift (-a), oscDom_add_shift (fun i => by simp [ha i]) hw, ?_⟩
    simp only
    rw [add_assoc, ← fastShift_add, neg_add_cancel, fastShift_zero, add_zero]

theorem fastShift_single (j : Fin n) :
    fastShift (m := m) (Pi.single j 1) = (Pi.single (Fin.castAdd m j) 1, 0) := by
  refine Prod.ext (funext fun i => ?_) rfl
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · simp only [fastShift, Fin.append_left, Pi.single_apply, Fin.ext_iff, Fin.val_castAdd]
  · simp only [fastShift, Fin.append_right, Pi.zero_apply, Pi.single_apply, Fin.ext_iff,
      Fin.val_natAdd]
    split_ifs with h
    · have h' : n + a.val = j.val := h
      have := j.isLt; omega
    · rfl

/-- A function of oscillator class is invariant under all real translations of the fast angles
that are integer combinations of the unit vectors; here: all integer ones. -/
theorem oscClass.periodic_int {r rp rq S : ℝ} {u : CHam (n + m)} (hu : oscClass D r rp rq S u)
    (k : Fin n → ℤ) {z : CPhase (n + m)} (hz : z ∈ oscDom (m := m) D r rp rq S) :
    u (z + fastShift (fun i => (k i : ℂ))) = u z := by
  let G : AddSubgroup (Fin n → ℝ) :=
    { carrier := {a | ∀ z ∈ oscDom (m := m) D r rp rq S,
        u (z + fastShift (fun i => (a i : ℂ))) = u z}
      zero_mem' := fun z _ => by
        have e : (fun i => (((0 : Fin n → ℝ) i : ℝ) : ℂ)) = 0 := by ext; simp
        rw [e, fastShift_zero, add_zero]
      add_mem' := by
        intro a b ha hb z hz
        have h1 := hb _ (oscDom_add_shift (a := fun i => (a i : ℂ)) (fun i => by simp) hz)
        have h2 := ha z hz
        have e : (fun i => (((a + b) i : ℝ) : ℂ)) =
            (fun i => (a i : ℂ)) + (fun i => (b i : ℂ)) := by ext; simp
        rw [e, fastShift_add, ← add_assoc]
        exact h1.trans h2
      neg_mem' := by
        intro a ha z hz
        have hw : z + fastShift (m := m) (fun i => (((-a) i : ℝ) : ℂ)) ∈
            oscDom (m := m) D r rp rq S :=
          oscDom_add_shift (fun i => by simp) hz
        have := ha _ hw
        have e : (fun i => (((-a) i : ℝ) : ℂ)) = -(fun i => (a i : ℂ)) := by ext; simp
        rw [add_assoc, ← fastShift_add] at this
        have e2 : (fun i => (((-a) i : ℝ) : ℂ)) + (fun i => (a i : ℂ)) = 0 := by ext; simp
        rw [e2, fastShift_zero, add_zero] at this
        exact this.symm }
  have hj : ∀ j : Fin n, Pi.single j (1 : ℝ) ∈ G := fun j z hz => by
    have e : (fun i => ((Pi.single j (1 : ℝ) : Fin n → ℝ) i : ℂ)) = Pi.single j 1 := by
      ext i; by_cases h : i = j <;> simp [h]
    rw [e, fastShift_single]
    have e3 : z + (Pi.single (Fin.castAdd m j) 1, 0) =
        (z.1 + Pi.single (Fin.castAdd m j) 1, z.2) := by ext <;> simp
    rw [e3]
    exact hu.2 j z hz
  have hk : (fun i => (k i : ℝ)) ∈ G := by
    have : (fun i => (k i : ℝ)) = ∑ j, k j • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact G.sum_mem fun j _ => G.zsmul_mem (hj j) _
  have := hk z hz
  simpa using this

theorem oscClass.field_periodic {r rp rq S r₀ rp₀ rq₀ S₀ : ℝ} {φ : CHam (n + m)}
    (hφ : oscClass D r rp rq S φ) (h : oscDom (m := m) D r₀ rp₀ rq₀ S₀ ⊆ oscDom D r rp rq S)
    (k : Fin n → ℤ) {w : CPhase (n + m)} (hw : w ∈ oscDom (m := m) D r₀ rp₀ rq₀ S₀) :
    KAM.hamiltonianVectorFieldℂ φ (w + fastShift (fun i => (k i : ℂ))) =
      KAM.hamiltonianVectorFieldℂ φ w := by
  have hev : (fun x => φ (x + fastShift (m := m) (fun i => (k i : ℂ)))) =ᶠ[nhds w] φ := by
    filter_upwards [(isOpen_oscDom (m := m) D r₀ rp₀ rq₀ S₀).mem_nhds hw] with x hx
    exact hφ.periodic_int k (h hx)
  have hf : fderiv ℂ φ (w + fastShift (m := m) (fun i => (k i : ℂ))) = fderiv ℂ φ w := by
    rw [← fderiv_comp_add_right, hev.fderiv_eq]
  simp only [KAM.hamiltonianVectorFieldℂ, hf]

end Shift

end KAM.Planetary

end
