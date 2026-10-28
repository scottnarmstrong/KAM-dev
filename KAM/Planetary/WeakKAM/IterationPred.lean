/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.IterationFacts

/-! # P11B iteration: stage predicates and coherent prefixes

`IterPre` collects the fields of `SelectionIteration` about the index `ν` itself (chain,
remainder, normal form); `IterPost` collects those about the step `ν → ν + 1`. `IterPrefix ν c`
says both hold up to `ν`. `ChainAgree` records that a chain extension does not change the
data a prefix reads, so the predicates transfer along a coherent sequence of chains.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

/-- The fields of `SelectionIteration` at the index `ν`. -/
structure IterPre (d : SelectionData n) (f : SelectionPhaseC n → ℂ) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) : Prop where
  chain : SelectionFiniteChain d a c ν
  energy_holo : DifferentiableOn ℂ (selectionEnergy c ν)
    (actionNbhd (c.K ν) (selectiont a ν))
  frequency_derivative : ∀ b ∈ actionNbhd (c.K ν) (selectiont a ν),
    ‖fderiv ℂ (selectionFrequency d c ν) b‖ ≤ 2 * d.C₁
  remainder_holo : DifferentiableOn ℂ (c.R ν)
    (selectionDomain (selectionr a ν) (selections a ν) (actionNbhd (c.K ν) (selectiont a ν)))
  remainder_bound : ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (c.K ν) (selectiont a ν)), ‖c.R ν x‖ ≤ selectionε a ν
  remainder_periodic : ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (c.K ν) (selectiont a ν)), ∀ k : Fin n → ℤ,
    c.R ν ((x.1.1 + (fun i => (k i : ℂ)), x.1.2), x.2) = c.R ν x
  remainder_real : ∀ z : Phase n, ∀ b : SelectionR n,
    (phaseToC z, selectionReal b) ∈ selectionDomain (selectionr a ν) (selections a ν)
      (actionNbhd (c.K ν) (selectiont a ν)) → (c.R ν (phaseToC z, selectionReal b)).im = 0
  normal_form : ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (c.K ν) (selectiont a ν)),
    selectionInitial d f (selectionCompose c x.2 ν x.1, x.2) =
      selectionEnergy c ν x.2 +
        (∑ i, selectionFrequency d c ν x.2 i * x.1.2 i) + c.R ν x

/-- The fields of `SelectionIteration` describing the step `ν → ν + 1`. -/
structure IterPost (d : SelectionData n) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) : Prop where
  increment_holo : DifferentiableOn ℂ (c.Δh ν) (actionNbhd (c.K ν) (selectiont a ν))
  increment_real : ∀ b : SelectionR n,
    selectionReal b ∈ actionNbhd (c.K ν) (selectiont a ν) → (c.Δh ν (selectionReal b)).im = 0
  energy_bound : ∀ b ∈ actionNbhd (c.K ν) (selectiont a ν), ‖c.Δh ν b‖ ≤ 2 * selectionε a ν
  map_holo : DifferentiableOn ℂ (fun x : SelectionPoint n => c.X ν x.2 x.1)
    (selectionDomain (selectionr a (ν + 1)) (selections a (ν + 1))
      (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1))))
  map_domain : ∀ x ∈ selectionDomain (selectionr a (ν + 1)) (selections a (ν + 1))
    (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1))),
    (c.X ν x.2 x.1, x.2) ∈ selectionDomain (selectionr a (ν + 1) + selectionσ a ν)
      (selections a ν) (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1)))
  map_periodic : ∀ x ∈ selectionDomain (selectionr a (ν + 1)) (selections a (ν + 1))
    (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1))), ∀ k : Fin n → ℤ,
    c.X ν x.2 (x.1 + ((fun i => (k i : ℂ)), 0)) = c.X ν x.2 x.1 + ((fun i => (k i : ℂ)), 0)
  map_real : ∀ z : Phase n, ∀ b : SelectionR n,
    (phaseToC z, selectionReal b) ∈ selectionDomain (selectionr a (ν + 1))
      (selections a (ν + 1)) (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1))) →
    ∃ w : Phase n, c.X ν (selectionReal b) (phaseToC z) = phaseToC w
  map_symplectic : ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1))),
    ∀ u v : SelectionPhaseC n,
    Canonical.symplFormC (fderiv ℂ (c.X ν x.2) x.1 u) (fderiv ℂ (c.X ν x.2) x.1 v) =
      Canonical.symplFormC u v
  map_angle_bound : ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1))),
    ‖(c.X ν x.2 x.1).1 - x.1.1‖ ≤ selectionA a ν
  map_action_bound : ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1))),
    ‖(c.X ν x.2 x.1).2 - x.1.2‖ ≤ selectionAlpha a ν
  map_derivative_bound : ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1))),
    ‖fderiv ℂ (c.X ν x.2) x.1 - ContinuousLinearMap.id ℂ (SelectionPhaseC n)‖
      ≤ selectionMapBudget a ν
  map_parameter_bound : ∀ t' : ℝ, 0 < t' → t' < selectiont a (ν + 1) →
    ∀ z : SelectionPhaseC n, z.1 ∈ complexStrip n (selectionr a (ν + 1)) →
    ‖z.2‖ < selections a (ν + 1) → ∀ b ∈ actionNbhd (c.K (ν + 1)) t', ∀ j : ℕ,
    ‖iteratedFDeriv ℂ j (fun b' => c.X ν b' z - z) b‖ ≤
      (j : ℝ) ^ j * max (selectionA a ν) (selectionAlpha a ν) /
        (selectiont a (ν + 1) - t') ^ j
  map_affine : ∀ b ∈ actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1)),
    ∃ Θ : SelectionC n → SelectionC n,
    ∃ A : SelectionC n → (SelectionC n →L[ℂ] SelectionC n),
    ∃ v : SelectionC n → SelectionC n,
    ∀ z : SelectionPhaseC n, z.1 ∈ complexStrip n (selectionr a (ν + 1)) →
      ‖z.2‖ < selections a (ν + 1) → c.X ν b z = (Θ z.1, A z.1 z.2 + v z.1)
  map_injective : ∀ b ∈ actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1)),
    InjOn (c.X ν b) {z | z.1 ∈ complexStrip n (selectionr a (ν + 1)) ∧
      ‖z.2‖ < selections a (ν + 1)}
  real_angle_derivative : ∀ b : SelectionR n,
    selectionReal b ∈ actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1)) → ∀ θ,
    ‖fderiv ℝ (fun v : SelectionR n =>
        selectionRe ((c.X ν (selectionReal b) (selectionReal v, 0)).1)) θ -
      ContinuousLinearMap.id ℝ (SelectionR n)‖ ≤ Real.exp (selectionRealBudget a ν) - 1

/-- A finite coherent prefix of an iteration. -/
def IterPrefix (d : SelectionData n) (f : SelectionPhaseC n → ℂ) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) : Prop :=
  ∀ j ≤ ν, IterPre d f a c j ∧ (j < ν → IterPost d a c j)

theorem selectionCollar_mono {K K' : Set (SelectionR n)} {t t' : ℝ} (hK : K' ⊆ K) (ht : t' ≤ t) :
    actionNbhd K' t' ⊆ actionNbhd K t := by
  rintro z ⟨J, hJ, hz⟩
  exact ⟨J, hK hJ, hz.trans_le ht⟩

/-- The data a prefix of length `ν` reads agree for the chains `c` and `c'`. -/
structure ChainAgree (ν : ℕ) (c c' : SelectionChain n) : Prop where
  K : ∀ j ≤ ν, c'.K j = c.K j
  R : ∀ j ≤ ν, c'.R j = c.R j
  Δω : ∀ j < ν, c'.Δω j = c.Δω j
  Δh : ∀ j < ν, c'.Δh j = c.Δh j
  X : ∀ j < ν, c'.X j = c.X j

theorem ChainAgree.mono {ν μ : ℕ} {c c' : SelectionChain n} (h : ChainAgree ν c c')
    (hμ : μ ≤ ν) : ChainAgree μ c c' :=
  ⟨fun j hj => h.K j (hj.trans hμ), fun j hj => h.R j (hj.trans hμ),
    fun j hj => h.Δω j (lt_of_lt_of_le hj hμ), fun j hj => h.Δh j (lt_of_lt_of_le hj hμ),
    fun j hj => h.X j (lt_of_lt_of_le hj hμ)⟩

theorem selectionFrequency_congr (d : SelectionData n) {c c' : SelectionChain n} {j : ℕ}
    (h : ∀ i < j, c'.Δω i = c.Δω i) : selectionFrequency d c' j = selectionFrequency d c j := by
  funext b
  unfold selectionFrequency
  rw [Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]]

theorem selectionEnergy_congr {c c' : SelectionChain n} {j : ℕ}
    (h : ∀ i < j, c'.Δh i = c.Δh i) : selectionEnergy c' j = selectionEnergy c j := by
  funext b
  unfold selectionEnergy
  rw [Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]]

theorem selectionCompose_congr {c c' : SelectionChain n} (b : SelectionC n) {j : ℕ}
    (h : ∀ i < j, c'.X i = c.X i) : selectionCompose c' b j = selectionCompose c b j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show selectionCompose c' b j ∘ c'.X j b = selectionCompose c b j ∘ c.X j b
    rw [ih fun i hi => h i (by omega), h j (by omega)]

theorem selectionRetained_congr (a : SelectionSchedule n) (d : SelectionData n)
    {c c' : SelectionChain n} {j : ℕ} (hK : c'.K j = c.K j) (h : ∀ i < j, c'.Δω i = c.Δω i) :
    selectionRetained a d c' j = selectionRetained a d c j := by
  unfold selectionRetained
  rw [hK, selectionFrequency_congr d h]

variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}

theorem IterPre.transfer {ν : ℕ} {c c' : SelectionChain n} (h : ChainAgree ν c c')
    (P : IterPre d f a c ν) : IterPre d f a c' ν := by
  have hK := h.K ν le_rfl
  have hR := h.R ν le_rfl
  have hf := selectionFrequency_congr d (c := c) (c' := c') (j := ν) h.Δω
  have he := selectionEnergy_congr (c := c) (c' := c') (j := ν) h.Δh
  have hc : ∀ b, selectionCompose c' b ν = selectionCompose c b ν := fun b =>
    selectionCompose_congr b h.X
  have hch : SelectionFiniteChain d a c' ν := by
    have Q := P.chain
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [h.K 0 (Nat.zero_le _)]; exact Q.initial
    · intro j hj; rw [h.K j hj]; exact Q.compact j hj
    · intro j hj; rw [h.K j hj]; exact Q.nonempty j hj
    · intro j hj; rw [h.K (j + 1) (by omega), h.K j (by omega)]; exact Q.nested j hj
    · intro j hj; rw [h.Δω j hj, h.K j (by omega)]; exact Q.holomorphic j hj
    · intro j hj b hb
      rw [h.K j (by omega)] at hb
      rw [h.Δω j hj]
      exact Q.real j hj b hb
    · intro j hj b hb
      rw [h.K j (by omega)] at hb
      rw [h.Δω j hj]
      exact Q.bound j hj b hb
    · intro j hj
      rw [h.K (j + 1) (by omega), selectionRetained_congr a d (h.K j (by omega))
        fun i hi => h.Δω i (by omega)]
      exact Q.retained j hj
  refine ⟨hch, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hK, he]; exact P.energy_holo
  · rw [hK, hf]; exact P.frequency_derivative
  · rw [hK, hR]; exact P.remainder_holo
  · rw [hK, hR]; exact P.remainder_bound
  · rw [hK, hR]; exact P.remainder_periodic
  · rw [hK, hR]; exact P.remainder_real
  · simp only [hK, hR, he, hf, hc]; exact P.normal_form

theorem IterPost.transfer {ν : ℕ} {c c' : SelectionChain n} (h : ChainAgree (ν + 1) c c')
    (P : IterPost d a c ν) : IterPost d a c' ν := by
  have hK := h.K ν (by omega)
  have hK1 := h.K (ν + 1) le_rfl
  have hX := h.X ν (by omega)
  have hH := h.Δh ν (by omega)
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15⟩ := P
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [hK, hK1, hX, hH]) <;> assumption

theorem IterPrefix.transfer {ν : ℕ} {c c' : SelectionChain n} (h : ChainAgree ν c c')
    (P : IterPrefix d f a c ν) : IterPrefix d f a c' ν := fun j hj =>
  ⟨(P j hj).1.transfer (h.mono hj), fun hlt =>
    ((P j hj).2 hlt).transfer (h.mono (Nat.succ_le_of_lt hlt))⟩

end KAM.Planetary

end
