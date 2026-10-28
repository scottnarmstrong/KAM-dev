/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.OscillatorFiniteStep
public import KAM.Planetary.Averaging.FiniteChain

/-!
# P Part 2: composition of the oscillator finite averaging stages (`stepP:p2:oa-concl`)

`OSched.Ψ` is the composition `Φ₀ ∘ ⋯ ∘ Φ_M`. Given the stage data of `ostep_conc`, the telescope of
N6-4, the fast-lattice law, reality and the Hamiltonian identity of each stage give the structural
conclusions of `osc_averaging` on `oscDom (R_{M+1}, Rp_{M+1}, Rq_{M+1}, S_{M+1})`, the summed
component displacements, and the weighted bound of the accumulated normal form minus its first
term. Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, Revision 3, package P23-15.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- The composed map `Φ₀ ∘ ⋯ ∘ Φ_M`. -/
def OSched.Ψ {n m : ℕ} (c : OSched) (D : Set (Fin n → ℝ)) (K : ℝ) (h : (Fin n → ℂ) → ℂ)
    (f : CHam (n + m)) (M : ℕ) : CPhase (n + m) → CPhase (n + m) := chain (c.Φ D K h f) M

section Seminorms

variable (n m : ℕ)

def semiF1 : Seminorm ℂ (CPhase (n + m)) :=
  (normSeminorm ℂ (Fin n → ℂ)).comp ((LinearMap.funLeft ℂ ℂ (Fin.castAdd m)).comp
    (LinearMap.fst ℂ (Fin (n + m) → ℂ) (Fin (n + m) → ℂ)))

def semiF2 : Seminorm ℂ (CPhase (n + m)) :=
  (normSeminorm ℂ (Fin n → ℂ)).comp ((LinearMap.funLeft ℂ ℂ (Fin.castAdd m)).comp
    (LinearMap.snd ℂ (Fin (n + m) → ℂ) (Fin (n + m) → ℂ)))

def semiL1 : Seminorm ℂ (CPhase (n + m)) :=
  (normSeminorm ℂ (Fin m → ℂ)).comp ((LinearMap.funLeft ℂ ℂ (Fin.natAdd n)).comp
    (LinearMap.fst ℂ (Fin (n + m) → ℂ) (Fin (n + m) → ℂ)))

def semiL2 : Seminorm ℂ (CPhase (n + m)) :=
  (normSeminorm ℂ (Fin m → ℂ)).comp ((LinearMap.funLeft ℂ ℂ (Fin.natAdd n)).comp
    (LinearMap.snd ℂ (Fin (n + m) → ℂ) (Fin (n + m) → ℂ)))

theorem semiF1_apply (w : CPhase (n + m)) : semiF1 n m w = ‖firstBlock (b := m) w.1‖ := rfl

theorem semiF2_apply (w : CPhase (n + m)) : semiF2 n m w = ‖firstBlock (b := m) w.2‖ := rfl

theorem semiL1_apply (w : CPhase (n + m)) : semiL1 n m w = ‖lastBlock (a := n) w.1‖ := rfl

theorem semiL2_apply (w : CPhase (n + m)) : semiL2 n m w = ‖lastBlock (a := n) w.2‖ := rfl

end Seminorms

section Assembly

variable {n m : ℕ} {D : Set (Fin n → ℝ)} {c : OSched} {K α : ℝ} {h : (Fin n → ℂ) → ℂ}
  {f : CHam (n + m)} {ε : ℕ → ℝ} {M : ℕ}

theorem OIter.stage_mapsTo (hS : OIter D c K α h f ε M) {i : ℕ} (hi : i ≤ M) :
    MapsTo (c.Φ D K h f i) (c.U (m := m) D (i + 1)) (c.U D i) := by
  obtain ⟨h1, -, h3, -, h5, -, h7, -⟩ := hS.widths i hi
  have sc := hS.stage hi
  refine (sc.mapsTo.mono_left (hS.U_sub_big hi)).mono_right (oscDom_mono ?_ ?_ ?_ ?_) <;> linarith

/-- Structural conclusions of `osc_averaging` on the final domain. -/
theorem OIter.struct (hS : OIter D c K α h f ε M) :
    let V := c.U (m := m) D (M + 1)
    DifferentiableOn ℂ (c.Ψ D K h f M) V ∧ InjOn (c.Ψ D K h f M) V ∧
    MapsTo (c.Ψ D K h f M) V (oscDom D c.x.r c.p.r c.q.r c.x.s) ∧
    (∀ z ∈ V, ∀ v w, symplFormC (fderiv ℂ (c.Ψ D K h f M) z v) (fderiv ℂ (c.Ψ D K h f M) z w) =
      symplFormC v w) ∧
    (∀ k : Fin n → ℤ, ∀ z ∈ V, c.Ψ D K h f M (z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) =
      c.Ψ D K h f M z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) ∧
    (∀ x : Phase (n + m), KAM.realInclusion₂ (n + m) x ∈ V →
      c.Ψ D K h f M (KAM.realInclusion₂ (n + m) x) ∈ range (KAM.realInclusion₂ (n + m))) := by
  intro V
  have hU : ∀ i ≤ M, c.U (m := m) D (i + 1) ⊆ c.U D i := fun i hi => hS.U_succ_subset hi
  have hmap := fun i (hi : i ≤ M) => hS.stage_mapsTo hi
  obtain ⟨-, -, t3, t4⟩ := telescope hU hmap
  obtain ⟨td, tsy⟩ := t3 (fun i hi => isOpen_oscDom _ _ _ _ _)
    (fun i hi => (hS.stage hi).diff.mono (hS.U_sub_big hi))
    (fun i hi z hz => (hS.stage hi).sympl z (hS.U_sub_big hi hz))
  have h0 : c.U (m := m) D 0 = oscDom D c.x.r c.p.r c.q.r c.x.s := rfl
  refine ⟨td, t4 fun i hi => (hS.stage hi).inj, h0 ▸ (telescope hU hmap).1, tsy, ?_, ?_⟩
  · intro k z hz
    refine chain_trans' (U := c.U D) (Φ := c.Φ D K h f) hmap (fun i hi z hz => ?_) z hz
    exact (hS.stage hi).trans k z (hS.U_sub_big hi hz)
  · exact chain_real (U := c.U D) (Φ := c.Φ D K h f) hmap fun i hi => (hS.stage hi).real_Φ

/-- The Hamiltonian identity `H ∘ Ψ = h + g + f_*`. -/
theorem OIter.ident (hS : OIter D c K α h f ε M) :
    ∀ z ∈ c.U (m := m) D (M + 1), h (firstBlock (b := m) (c.Ψ D K h f M z).2) +
        f (c.Ψ D K h f M z) =
      h (firstBlock (b := m) z.2) + c.G D K h f (M + 1) z + c.F D K h f (M + 1) z := by
  have hmap := fun i (hi : i ≤ M) => hS.stage_mapsTo hi
  have := chain_ident (U := c.U D) (Φ := c.Φ D K h f) (m := M)
    (H₀ := fun w => h (firstBlock (b := m) w.2) + f w)
    (Hs := fun i w => h (firstBlock (b := m) w.2) + c.G D K h f i w + c.F D K h f i w) hmap
    (fun i hi z hz => (hS.stage hi).ident z hz) (by funext w; simp [OSched.G_zero, OSched.F_zero])
  intro z hz
  simpa [OSched.Ψ] using this z hz

/-- Summed component displacements. -/
theorem OIter.disp (hS : OIter D c K α h f ε M) :
    ∀ z ∈ c.U (m := m) D (M + 1),
      ‖firstBlock (b := m) ((c.Ψ D K h f M z).1 - z.1)‖ ≤
        ∑ i ∈ Finset.range (M + 1), ε i / (2 * π * α * c.x.ρ i) ∧
      ‖firstBlock (b := m) ((c.Ψ D K h f M z).2 - z.2)‖ ≤
        ∑ i ∈ Finset.range (M + 1), ε i / (exp 1 * (2 * π * α) * c.x.σ i) ∧
      ‖lastBlock (a := n) ((c.Ψ D K h f M z).1 - z.1)‖ ≤
        ∑ i ∈ Finset.range (M + 1), ε i / (2 * π * α * c.p.ρ i) ∧
      ‖lastBlock (a := n) ((c.Ψ D K h f M z).2 - z.2)‖ ≤
        ∑ i ∈ Finset.range (M + 1), ε i / (2 * π * α * c.q.ρ i) := by
  have hU : ∀ i ≤ M, c.U (m := m) D (i + 1) ⊆ c.U D i := fun i hi => hS.U_succ_subset hi
  have hmap := fun i (hi : i ≤ M) => hS.stage_mapsTo hi
  have T := (telescope hU hmap).2.1
  intro z hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact T (semiF1 n m) (fun i => ε i / (2 * π * α * c.x.ρ i))
      (fun i hi w hw => ((hS.stage hi).disp w (hS.U_sub_big hi hw)).1) z hz
  · exact T (semiF2 n m) (fun i => ε i / (exp 1 * (2 * π * α) * c.x.σ i))
      (fun i hi w hw => ((hS.stage hi).disp w (hS.U_sub_big hi hw)).2.1) z hz
  · exact T (semiL1 n m) (fun i => ε i / (2 * π * α * c.p.ρ i))
      (fun i hi w hw => ((hS.stage hi).disp w (hS.U_sub_big hi hw)).2.2.1) z hz
  · exact T (semiL2 n m) (fun i => ε i / (2 * π * α * c.q.ρ i))
      (fun i hi w hw => ((hS.stage hi).disp w (hS.U_sub_big hi hw)).2.2.2) z hz

end Assembly

end KAM.Planetary

end
