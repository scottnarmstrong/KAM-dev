/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.FiniteStep

/-!
# P Part 2: composition of the finite averaging stages (`stepP:p2:nfb-concl`, `stepP:p2:nfb-disp`)

`Sched.Ψ` is the composition `Φ₀ ∘ ⋯ ∘ Φ_m`, `Sched.gI` the θ-independent normal form
`∑_{j ≤ m} f̂ⱼ,₀`. Given `StepConc` at every stage, the telescope of N6-4 together with the
fast-lattice law, reality and the Hamiltonian identity of each stage give the structural
conclusions of `nfb` on `𝒟_{R_{m+1},S_{m+1}}`, the weighted bounds of `g - f̂₀` and the
summed component displacements. Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-12.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ}

namespace Sched

variable {n : ℕ}

/-- The composed map `Φ₀ ∘ ⋯ ∘ Φ_m`. -/
def Ψ (c : Sched) (D : Set (Fin n → ℂ)) (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam n) (m : ℕ) :
    CPhase n → CPhase n := chain (c.Φ D K h f) m

/-- The θ-independent accumulated normal form `∑_{j ≤ m} (f_j)^_0`. -/
def gI (c : Sched) (D : Set (Fin n → ℂ)) (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam n) (m : ℕ)
    (I : Fin n → ℂ) : ℂ := ∑ j ∈ Finset.range (m + 1), coeff (c.F D K h f j) I 0

end Sched

section ChainLaws

variable {n : ℕ} {U : ℕ → Set (CPhase n)} {Φ : ℕ → CPhase n → CPhase n}

theorem chain_trans' {t : Fin n → ℂ} {m : ℕ} (hmap : ∀ i ≤ m, MapsTo (Φ i) (U (i + 1)) (U i))
    (htr : ∀ i ≤ m, ∀ z ∈ U (i + 1), Φ i (z + (t, 0)) = Φ i z + (t, 0)) :
    ∀ z ∈ U (m + 1), chain Φ m (z + (t, 0)) = chain Φ m z + (t, 0) := by
  induction m with
  | zero => exact fun z hz => htr 0 le_rfl z hz
  | succ m ih =>
    intro z hz
    have hle : ∀ i ≤ m, i ≤ m + 1 := fun i hi => hi.trans (Nat.le_succ _)
    have h1 := ih (fun i hi => hmap i (hle i hi)) (fun i hi => htr i (hle i hi))
    have hz' : Φ (m + 1) z ∈ U (m + 1) := hmap (m + 1) le_rfl hz
    show chain Φ m (Φ (m + 1) (z + (t, 0))) = chain Φ m (Φ (m + 1) z) + (t, 0)
    rw [htr (m + 1) le_rfl z hz]
    exact h1 _ hz'

theorem chain_real {m : ℕ} (hmap : ∀ i ≤ m, MapsTo (Φ i) (U (i + 1)) (U i))
    (hre : ∀ i ≤ m, ∀ x : Phase n, KAM.realInclusion₂ n x ∈ U (i + 1) →
      Φ i (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n)) :
    ∀ x : Phase n, KAM.realInclusion₂ n x ∈ U (m + 1) →
      chain Φ m (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n) := by
  induction m with
  | zero => exact hre 0 le_rfl
  | succ m ih =>
    intro x hx
    have hle : ∀ i ≤ m, i ≤ m + 1 := fun i hi => hi.trans (Nat.le_succ _)
    have h1 := ih (fun i hi => hmap i (hle i hi)) (fun i hi => hre i (hle i hi))
    obtain ⟨x', hx'⟩ := hre (m + 1) le_rfl x hx
    have hmem : KAM.realInclusion₂ n x' ∈ U (m + 1) := by
      rw [hx']; exact hmap (m + 1) le_rfl hx
    show chain Φ m (Φ (m + 1) (KAM.realInclusion₂ n x)) ∈ _
    rw [← hx']
    exact h1 x' hmem

theorem chain_ident {H₀ : CPhase n → ℂ} {Hs : ℕ → CPhase n → ℂ} {m : ℕ}
    (hmap : ∀ i ≤ m, MapsTo (Φ i) (U (i + 1)) (U i))
    (hid : ∀ i ≤ m, ∀ z ∈ U (i + 1), Hs i (Φ i z) = Hs (i + 1) z)
    (h0 : H₀ = Hs 0) :
    ∀ z ∈ U (m + 1), H₀ (chain Φ m z) = Hs (m + 1) z := by
  subst h0
  induction m with
  | zero => exact fun z hz => hid 0 le_rfl z hz
  | succ m ih =>
    intro z hz
    have hle : ∀ i ≤ m, i ≤ m + 1 := fun i hi => hi.trans (Nat.le_succ _)
    have h1 := ih (fun i hi => hmap i (hle i hi)) (fun i hi => hid i (hle i hi))
    have hz' : Φ (m + 1) z ∈ U (m + 1) := hmap (m + 1) le_rfl hz
    show Hs 0 (chain Φ m (Φ (m + 1) z)) = _
    rw [h1 _ hz']
    exact hid (m + 1) le_rfl z hz

end ChainLaws

section Assembly

variable {Dc : Set (Fin (a + b) → ℂ)} {c : Sched} {K α₁ α₂ : ℝ} {h : (Fin (a + b) → ℂ) → ℂ}
  {f : CHam (a + b)} {ε : ℕ → ℝ} {m : ℕ}

/-- The stage domains `𝒟_{Rᵢ,Sᵢ}`. -/
abbrev Sched.U (Dc : Set (Fin (a + b) → ℂ)) (c : Sched) (i : ℕ) : Set (CPhase (a + b)) :=
  Dom (a + b) Dc (c.R i) (c.S i)

theorem U_succ_subset (hS : IterSetup Dc c K α₁ α₂ h f ε m) {i : ℕ} (hi : i ≤ m) :
    Sched.U Dc c (i + 1) ⊆ Sched.U Dc c i :=
  Dom_mono (by rw [Sched.R_succ]; linarith [hS.ρ_pos i hi])
    (by rw [Sched.S_succ]; linarith [hS.σ_pos i hi])

theorem stage_mapsTo (hS : IterSetup Dc c K α₁ α₂ h f ε m) {i : ℕ} (hi : i ≤ m)
    (sc : StepConc Dc c K α₁ α₂ h f ε i) :
    MapsTo (c.Φ Dc K h f i) (Sched.U Dc c (i + 1)) (Sched.U Dc c i) := by
  have hρ := hS.ρ_pos i hi
  have hσ := hS.σ_pos i hi
  refine (sc.mapsTo.mono_left (Dom_mono ?_ ?_)).mono_right (Dom_mono ?_ ?_)
  · rw [Sched.R_succ]; linarith
  · rw [Sched.S_succ]; linarith
  · linarith
  · linarith

theorem stage_sub_big (hS : IterSetup Dc c K α₁ α₂ h f ε m) {i : ℕ} (hi : i ≤ m) :
    Sched.U Dc c (i + 1) ⊆
      Dom (a + b) Dc (c.R i - 3 * c.ρ i / 2) (c.S i - 3 * c.σ i / 2) := by
  have hρ := hS.ρ_pos i hi
  have hσ := hS.σ_pos i hi
  refine Dom_mono ?_ ?_
  · rw [Sched.R_succ]; linarith
  · rw [Sched.S_succ]; linarith

/-- The block seminorms of the telescope. -/
def semiFirst (a b : ℕ) : Seminorm ℂ (CPhase (a + b)) :=
  (normSeminorm ℂ (Fin a → ℂ)).comp
    ((LinearMap.funLeft ℂ ℂ (Fin.castAdd b)).comp (LinearMap.snd ℂ (Fin (a + b) → ℂ) (Fin (a + b) → ℂ)))

def semiLast (a b : ℕ) : Seminorm ℂ (CPhase (a + b)) :=
  (normSeminorm ℂ (Fin b → ℂ)).comp
    ((LinearMap.funLeft ℂ ℂ (Fin.natAdd a)).comp (LinearMap.snd ℂ (Fin (a + b) → ℂ) (Fin (a + b) → ℂ)))

def semiAngle (a b : ℕ) : Seminorm ℂ (CPhase (a + b)) :=
  (normSeminorm ℂ (Fin (a + b) → ℂ)).comp (LinearMap.fst ℂ (Fin (a + b) → ℂ) (Fin (a + b) → ℂ))

theorem semiFirst_apply (w : CPhase (a + b)) : semiFirst a b w = ‖firstBlock (b := b) w.2‖ := rfl

theorem semiLast_apply (w : CPhase (a + b)) : semiLast a b w = ‖lastBlock (a := a) w.2‖ := rfl

theorem semiAngle_apply (w : CPhase (a + b)) : semiAngle a b w = ‖w.1‖ := rfl

/-- Structural conclusions of `nfb` on the final domain. -/
theorem finite_struct (hS : IterSetup Dc c K α₁ α₂ h f ε m)
    (hsc : ∀ i ≤ m, StepConc Dc c K α₁ α₂ h f ε i) :
    let V := Sched.U Dc c (m + 1)
    DifferentiableOn ℂ (c.Ψ Dc K h f m) V ∧ InjOn (c.Ψ Dc K h f m) V ∧
    MapsTo (c.Ψ Dc K h f m) V (Dom (a + b) Dc c.r c.s) ∧
    (∀ z ∈ V, ∀ v w, symplFormC (fderiv ℂ (c.Ψ Dc K h f m) z v) (fderiv ℂ (c.Ψ Dc K h f m) z w) =
      symplFormC v w) ∧
    (∀ k : Fin (a + b) → ℤ, ∀ z ∈ V, c.Ψ Dc K h f m (z + ((fun i => (k i : ℂ)), 0)) =
      c.Ψ Dc K h f m z + ((fun i => (k i : ℂ)), 0)) ∧
    (∀ x : Phase (a + b), KAM.realInclusion₂ (a + b) x ∈ V →
      c.Ψ Dc K h f m (KAM.realInclusion₂ (a + b) x) ∈ range (KAM.realInclusion₂ (a + b))) := by
  intro V
  have hU : ∀ i ≤ m, Sched.U Dc c (i + 1) ⊆ Sched.U Dc c i := fun i hi => U_succ_subset hS hi
  have hmap := fun i (hi : i ≤ m) => stage_mapsTo hS hi (hsc i hi)
  obtain ⟨-, -, t3, t4⟩ := telescope hU hmap
  obtain ⟨td, tsy⟩ := t3 (fun i hi => isOpen_Dom _ _ _)
    (fun i hi => (hsc i hi).diff.mono (stage_sub_big hS hi))
    (fun i hi z hz => (hsc i hi).sympl z hz)
  have h0 : Sched.U Dc c 0 = Dom (a + b) Dc c.r c.s := rfl
  refine ⟨td, t4 fun i hi => (hsc i hi).inj, h0 ▸ (telescope hU hmap).1, tsy, ?_, ?_⟩
  · intro k z hz
    refine chain_trans' (U := Sched.U Dc c) (Φ := c.Φ Dc K h f) hmap (fun i hi z hz => ?_) z hz
    have e : z + ((fun j => (k j : ℂ)), 0) = (z.1 + (fun j => (k j : ℂ)), z.2) := by
      ext <;> simp
    rw [e]
    exact (hsc i hi).trans k z (stage_sub_big hS hi hz)
  · exact chain_real (U := Sched.U Dc c) (Φ := c.Φ Dc K h f) hmap fun i hi => (hsc i hi).real_Φ

/-- The Hamiltonian identity `H ∘ Ψ = h + g + f_*`. -/
theorem finite_ident (hS : IterSetup Dc c K α₁ α₂ h f ε m)
    (hsc : ∀ i ≤ m, StepConc Dc c K α₁ α₂ h f ε i) :
    ∀ z ∈ Sched.U Dc c (m + 1), h (c.Ψ Dc K h f m z).2 + f (c.Ψ Dc K h f m z) =
      h z.2 + c.G Dc K h f (m + 1) z + c.F Dc K h f (m + 1) z := by
  have hmap := fun i (hi : i ≤ m) => stage_mapsTo hS hi (hsc i hi)
  have := chain_ident (U := Sched.U Dc c) (Φ := c.Φ Dc K h f) (m := m)
    (H₀ := fun w => h w.2 + f w)
    (Hs := fun i w => h w.2 + c.G Dc K h f i w + c.F Dc K h f i w) hmap
    (fun i hi z hz => by
      have := (hsc i hi).ident z hz
      simpa using this) (by funext w; simp [Sched.G_zero, Sched.F_zero])
  intro z hz
  have := this z hz
  simpa [Sched.Ψ] using this

/-- Summed component displacements. -/
theorem finite_disp (hS : IterSetup Dc c K α₁ α₂ h f ε m)
    (hsc : ∀ i ≤ m, StepConc Dc c K α₁ α₂ h f ε i) :
    ∀ z ∈ Sched.U Dc c (m + 1),
      ‖firstBlock (b := b) ((c.Ψ Dc K h f m z).2 - z.2)‖ ≤
        ∑ i ∈ Finset.range (m + 1), 1 * ε i / (exp 1 * (2 * π * α₁) * c.σ i) ∧
      ‖lastBlock (a := a) ((c.Ψ Dc K h f m z).2 - z.2)‖ ≤
        ∑ i ∈ Finset.range (m + 1), 1 * ε i / (exp 1 * (2 * π * α₂) * c.σ i) ∧
      ‖(c.Ψ Dc K h f m z).1 - z.1‖ ≤
        ∑ i ∈ Finset.range (m + 1), 1 * ε i / (2 * π * α₂ * c.ρ i) := by
  have hU : ∀ i ≤ m, Sched.U Dc c (i + 1) ⊆ Sched.U Dc c i := fun i hi => U_succ_subset hS hi
  have hmap := fun i (hi : i ≤ m) => stage_mapsTo hS hi (hsc i hi)
  have T := (telescope hU hmap).2.1
  intro z hz
  refine ⟨?_, ?_, ?_⟩
  · have := T (semiFirst a b) (fun i => 1 * ε i / (exp 1 * (2 * π * α₁) * c.σ i))
      (fun i hi w hw => ((hsc i hi).disp w (stage_sub_big hS hi hw)).1) z hz
    exact this
  · have := T (semiLast a b) (fun i => 1 * ε i / (exp 1 * (2 * π * α₂) * c.σ i))
      (fun i hi w hw => ((hsc i hi).disp w (stage_sub_big hS hi hw)).2.1) z hz
    exact this
  · have := T (semiAngle a b) (fun i => 1 * ε i / (2 * π * α₂ * c.ρ i))
      (fun i hi w hw => ((hsc i hi).disp w (stage_sub_big hS hi hw)).2.2) z hz
    exact this

end Assembly

end KAM.Planetary

end
