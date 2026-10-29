/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Adapters
import KAM.Strip.Limits

/-!
# The Hamiltonian hypothesis H1

Blueprint Part 4, `bp:p4:h1`. For `ε ≤ 1`, the domain `𝔇 = T_{s/2} × B_{r₀/2}`
and the Hamiltonian `𝐡 = h + f` satisfy the block H1 of the frozen G1 and G2
(`KAM.aposteriori_kam`, `KAM.local_uniqueness_flow`) with the constant `M`.

The three steps of the blueprint proof are the following.

* `step:p4:h1-open`: `𝔇` is open (`KAM.Head.isOpen_domainD`) and invariant under integer shifts of
  `θ` (`KAM.add_intCast_mem_complexStrip`).
* `step:p4:h1-holo`: holomorphy, periodicity and reality of `𝐡` on `𝔇`, from those of `h` on
  `B_{r₀}` and of `f` on `D(s₀, r₀) ⊇ 𝔇` (`KAM.Head.h1_domainD_subset_domain`).
* `step:p4:h1-bounds`: the derivative block is `KAM.Head.derivative_bounds_design` (d).
-/

@[expose] public noncomputable section

namespace KAM.Head

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
  {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}

/-- `𝔇 ⊆ D(s₀, r₀) = T_{s₀} × B_{r₀}`. -/
theorem h1_domainD_subset_domain (n : ℕ) {s₀ r₀ : ℝ} (hs₀ : 0 < s₀) (hr₀ : 0 < r₀)
    (B : Set (Fin n → ℝ)) : domainD n s₀ r₀ B ⊆ complexStrip n s₀ ×ˢ actionNbhd B r₀ :=
  (domainD_subset_domainD' n hs₀ hr₀ B).trans (domainD'_subset n hs₀ hr₀ B)

/-- Step `step:p4:h1-open`: `𝔇` is invariant under `θ ↦ θ + k`, `k ∈ ℤⁿ`. -/
theorem h1_domainD_add_intCast {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ domainD n s₀ r₀ B)
    (k : Fin n → ℤ) : (z.1 + (fun i => (k i : ℂ)), z.2) ∈ domainD n s₀ r₀ B :=
  ⟨add_intCast_mem_complexStrip hz.1 k, hz.2⟩

/-- Step `step:p4:h1-holo`: `𝐡 = h ∘ snd + f` is holomorphic on `𝔇`. -/
theorem h1_differentiableOn (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε) :
    DifferentiableOn ℂ (hbold h f) (domainD n s₀ r₀ B) := by
  have hr := hD.r₀_pos
  have h1 : DifferentiableOn ℂ (fun z : (Fin n → ℂ) × (Fin n → ℂ) => h z.2)
      (domainD n s₀ r₀ B) :=
    hD.holo.comp differentiableOn_snd fun z hz => actionNbhd_mono B (half_le_self hr.le) hz.2
  exact h1.add (hP.holo.mono (h1_domainD_subset_domain n hD.s₀_pos hr B))

/-- Step `step:p4:h1-holo`: `𝐡` is `ℤⁿ`-periodic in `θ` on `𝔇`. -/
theorem h1_add_intCast (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ domainD n s₀ r₀ B) (k : Fin n → ℤ) :
    hbold h f (z.1 + (fun i => (k i : ℂ)), z.2) = hbold h f z := by
  have := hP.periodic z (h1_domainD_subset_domain n hD.s₀_pos hD.r₀_pos B hz) k
  simp only [hbold]
  rw [this]

/-- Step `step:p4:h1-holo`: `𝐡` is real at real points of `𝔇`. -/
theorem h1_im_eq_zero (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    {θ I : Fin n → ℝ}
    (hz : ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ domainD n s₀ r₀ B) :
    (hbold h f ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0 := by
  have hr := hD.r₀_pos
  have hI : (fun i => (I i : ℂ)) ∈ actionNbhd B r₀ := actionNbhd_mono B (half_le_self hr.le) hz.2
  have hz' := h1_domainD_subset_domain n hD.s₀_pos hr B hz
  simp only [hbold, Complex.add_im]
  rw [hD.real I hI, hP.real θ I hz', add_zero]

/-- Blueprint `bp:p4:h1`: for `ε ≤ 1`, `(𝔇, 𝐡)` satisfies the block H1 of the frozen G1 and G2
with `M` (the H1 conjuncts verbatim, `𝔅 := 𝔇`, `h := 𝐡`). -/
theorem h1 (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε) (hε : ε ≤ 1) :
    IsOpen (domainD n s₀ r₀ B) ∧
    (∀ z ∈ domainD n s₀ r₀ B, ∀ k : Fin n → ℤ,
      (z.1 + (fun i => (k i : ℂ)), z.2) ∈ domainD n s₀ r₀ B) ∧
    DifferentiableOn ℂ (hbold h f) (domainD n s₀ r₀ B) ∧
    (∀ z ∈ domainD n s₀ r₀ B, ∀ k : Fin n → ℤ,
      hbold h f (z.1 + (fun i => (k i : ℂ)), z.2) = hbold h f z) ∧
    (∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ domainD n s₀ r₀ B →
      (hbold h f ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) ∧
    (∀ z ∈ domainD n s₀ r₀ B,
      ‖fderiv ℂ (hbold h f) z‖ ≤ Mconst s₀ r₀ B h ∧
      ‖hamiltonianVectorFieldℂ (hbold h f) z‖ ≤ Mconst s₀ r₀ B h ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ (hbold h f)) z‖ ≤ Mconst s₀ r₀ B h ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ (hbold h f)) z‖ ≤ Mconst s₀ r₀ B h) :=
  ⟨isOpen_domainD n s₀ r₀ B, fun _ hz k => h1_domainD_add_intCast hz k,
    h1_differentiableOn hD hP, fun _ hz k => h1_add_intCast hD hP hz k,
    fun _ _ hz => h1_im_eq_zero hD hP hz,
    fun z hz => (derivative_bounds_design hD.s₀_pos hD.r₀_pos hD.isBounded hD.holo hP.holo
      hP.bound).2.2.2 hε z hz⟩

end KAM.Head

end
