/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Oscillator
public import KAM.EffectiveStability.Torus
public import KAM.Frozen.Defs.SymplecticForm

/-!
# Chains of canonical charts (track B, B2-COMPOSE)

`IsCanonicalChart Ψ Ψinv D V` bundles the five chart premises of the B1 headline theorems.
Such charts are stable under composition (chain rule, symplectic forms compose, left inverses
compose), so a normalization `Ψ = Ψ₁ ∘ ⋯ ∘ Ψ_m` of real time-one flows is again a chart.
Includes finite chains (lists), the transfer of a pulled-back Hamiltonian identity, and
convenience wrappers of `oscillator_confinement` and `torus_confinement`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set

/-- The bundle of the B1 chart premises: `Ψ` is a `C²` map on the open set `D`, takes `D` into
`V`, preserves the frozen symplectic form on `D` and has the left inverse `Ψinv` on `D`. -/
structure IsCanonicalChart {n : ℕ}
    (Ψ Ψinv : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ))
    (D V : Set ((Fin n → ℝ) × (Fin n → ℝ))) : Prop where
  chart_open : IsOpen D
  chart_smooth : ContDiffOn ℝ 2 Ψ D
  chart_maps : MapsTo Ψ D V
  chart_symp : ∀ w ∈ D, ∀ u v, KAM.symplecticForm (fderiv ℝ Ψ w u) (fderiv ℝ Ψ w v) =
    KAM.symplecticForm u v
  chart_leftInv : ∀ w ∈ D, Ψinv (Ψ w) = w

variable {n : ℕ}

/-- Composition of canonical charts with matching domains. -/
theorem IsCanonicalChart.chart_comp {Ψ₁ Ψ₁inv Ψ₂ Ψ₂inv :
      (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    {D₁ V₁ D₂ V₂ : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    (h₂ : IsCanonicalChart Ψ₂ Ψ₂inv D₂ V₂) (h₁ : IsCanonicalChart Ψ₁ Ψ₁inv D₁ V₁)
    (hsub : V₂ ⊆ D₁) : IsCanonicalChart (Ψ₁ ∘ Ψ₂) (Ψ₂inv ∘ Ψ₁inv) D₂ V₁ := by
  have hm : MapsTo Ψ₂ D₂ D₁ := fun w hw => hsub (h₂.chart_maps hw)
  refine ⟨h₂.chart_open, h₁.chart_smooth.comp h₂.chart_smooth hm,
    fun w hw => h₁.chart_maps (hm hw), ?_, ?_⟩
  · intro w hw u v
    have hd₂ : DifferentiableAt ℝ Ψ₂ w :=
      (h₂.chart_smooth.contDiffAt (h₂.chart_open.mem_nhds hw)).differentiableAt (by norm_num)
    have hd₁ : DifferentiableAt ℝ Ψ₁ (Ψ₂ w) :=
      (h₁.chart_smooth.contDiffAt (h₁.chart_open.mem_nhds (hm hw))).differentiableAt
        (by norm_num)
    have hc : fderiv ℝ (Ψ₁ ∘ Ψ₂) w = (fderiv ℝ Ψ₁ (Ψ₂ w)).comp (fderiv ℝ Ψ₂ w) :=
      fderiv_comp w hd₁ hd₂
    rw [hc]
    simp only [ContinuousLinearMap.comp_apply]
    rw [h₁.chart_symp _ (hm hw), h₂.chart_symp w hw]
  · intro w hw
    simp only [Function.comp_apply]
    rw [h₁.chart_leftInv _ (hm hw), h₂.chart_leftInv w hw]

/-- The identity is a canonical chart on any open set. -/
theorem IsCanonicalChart.id_chart {D : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hD : IsOpen D) :
    IsCanonicalChart (id : (Fin n → ℝ) × (Fin n → ℝ) → _) id D D :=
  ⟨hD, contDiffOn_id, fun _ hw => hw, fun w _ u v => by simp, fun _ _ => rfl⟩

/-- Shrinking the domain (to an open subset) and enlarging the target. -/
theorem IsCanonicalChart.mono_chart {Ψ Ψinv :
      (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    {D V D' V' : Set ((Fin n → ℝ) × (Fin n → ℝ))} (h : IsCanonicalChart Ψ Ψinv D V)
    (hD' : IsOpen D') (hD : D' ⊆ D) (hV : V ⊆ V') : IsCanonicalChart Ψ Ψinv D' V' :=
  ⟨hD', h.chart_smooth.mono hD, fun _ hw => hV (h.chart_maps (hD hw)),
    fun w hw => h.chart_symp w (hD hw), fun w hw => h.chart_leftInv w (hD hw)⟩

/-- One link of a chain of charts: map, left inverse, domain, target. -/
structure ChartStep (n : ℕ) where
  stepMap : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)
  stepInv : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)
  stepDom : Set ((Fin n → ℝ) × (Fin n → ℝ))
  stepTgt : Set ((Fin n → ℝ) × (Fin n → ℝ))

/-- The composite `Ψ₁ ∘ ⋯ ∘ Ψ_m` of a list of steps (outermost first). -/
def chartChainMap : List (ChartStep n) → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)
  | [] => id
  | c :: l => c.stepMap ∘ chartChainMap l

/-- The composite left inverse `Ψ_minv ∘ ⋯ ∘ Ψ₁inv`. -/
def chartChainInv : List (ChartStep n) → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)
  | [] => id
  | c :: l => chartChainInv l ∘ c.stepInv

/-- The target of the chain, given the domain `D` of the innermost position. -/
def chartChainTarget (D : Set ((Fin n → ℝ) × (Fin n → ℝ))) :
    List (ChartStep n) → Set ((Fin n → ℝ) × (Fin n → ℝ))
  | [] => D
  | c :: _ => c.stepTgt

/-- Matching data: each step is a canonical chart and the image region of the inner part
lies in the domain of the next outer step. -/
def ChartChainOK (D : Set ((Fin n → ℝ) × (Fin n → ℝ))) : List (ChartStep n) → Prop
  | [] => IsOpen D
  | c :: l => IsCanonicalChart c.stepMap c.stepInv c.stepDom c.stepTgt ∧
      chartChainTarget D l ⊆ c.stepDom ∧ ChartChainOK D l

/-- A chain of charts with matching domains composes to a canonical chart from `D` to the
outermost target. -/
theorem chartChain_isCanonical (D : Set ((Fin n → ℝ) × (Fin n → ℝ))) :
    ∀ l : List (ChartStep n), ChartChainOK D l →
      IsCanonicalChart (chartChainMap l) (chartChainInv l) D (chartChainTarget D l)
  | [], h => IsCanonicalChart.id_chart h
  | _ :: l, ⟨hc, hsub, hl⟩ => (chartChain_isCanonical D l hl).chart_comp hc hsub

/-- Transfer of a pulled-back Hamiltonian identity through a composition. -/
theorem hamiltonian_comp_transfer
    {Ψ₁ Ψ₂ : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    {H K₁ K₂ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {D₁ D₂ : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    (h₁ : ∀ w ∈ D₁, H (Ψ₁ w) = K₁ w) (h₂ : ∀ w ∈ D₂, K₁ (Ψ₂ w) = K₂ w)
    (hm : MapsTo Ψ₂ D₂ D₁) : ∀ w ∈ D₂, H ((Ψ₁ ∘ Ψ₂) w) = K₂ w := fun w hw => by
  simp only [Function.comp_apply]
  rw [h₁ _ (hm hw), h₂ w hw]

/-- Convenience wrapper of `oscillator_confinement` with the five chart premises bundled. -/
theorem oscillator_confinement_of_chart (a b η : Fin n → ℝ) (ε T : ℝ) (hε : 0 < ε) (hT : 0 ≤ T)
    (hη : ∀ j, 0 ≤ η j) (hmargin : ∀ j, a j + T * η j < b j)
    (V : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hV : IsOpen V)
    (H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (hH : ContDiffOn ℝ 2 H V)
    (Ψ Ψinv : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ))
    (hΨ : IsCanonicalChart Ψ Ψinv (osc (fun j => b j + ε)) V)
    (N : (Fin n → ℝ) → ℝ) (R : (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (hR : DifferentiableOn ℝ R {w | ∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j < b j + ε})
    (hHΨ : ∀ w : (Fin n → ℝ) × (Fin n → ℝ),
      (∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j < b j + ε) →
      H (Ψ w) = N (KAM.Planetary.oscillatorAction w.2 w.1) + R w)
    (hRη : ∀ w : (Fin n → ℝ) × (Fin n → ℝ),
      (∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j ≤ b j) →
      ∀ j, |w.1 j * fderiv ℝ R w (0, Pi.single j 1) - w.2 j * fderiv ℝ R w (Pi.single j 1, 0)|
        ≤ η j)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ))
    (hw₀ : ∀ j, KAM.Planetary.oscillatorAction w₀.2 w₀.1 j ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = Ψ w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ V ∧ HasDerivAt z (KAM.hamiltonianVectorField H (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = Ψ w₀ →
        (∀ t ∈ I, y t ∈ V ∧ HasDerivAt y (KAM.hamiltonianVectorField H (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → Ψ (Ψinv (z t)) = z t ∧
        ∀ j, |KAM.Planetary.oscillatorAction (Ψinv (z t)).2 (Ψinv (z t)).1 j -
            KAM.Planetary.oscillatorAction w₀.2 w₀.1 j| ≤ η j * |t| ∧
          KAM.Planetary.oscillatorAction (Ψinv (z t)).2 (Ψinv (z t)).1 j ≤ a j + η j * T :=
  oscillator_confinement a b η ε T hε hT hη hmargin V hV H hH Ψ Ψinv hΨ.chart_smooth
    (fun _ hw => hΨ.chart_maps hw) hΨ.chart_symp hΨ.chart_leftInv N R hR hHΨ hRη w₀ hw₀

/-- Convenience wrapper of `torus_confinement` with the five chart premises bundled. -/
theorem torus_confinement_of_chart (a b η : Fin n → ℝ) (ε T : ℝ) (hε : 0 < ε) (hT : 0 ≤ T)
    (hη : ∀ j, 0 ≤ η j) (hmargin : ∀ j, a j + T * η j < b j)
    (V : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hV : IsOpen V)
    (H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (hH : ContDiffOn ℝ 2 H V)
    (Ψ Ψinv : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ))
    (hΨ : IsCanonicalChart Ψ Ψinv (cyl (fun j => b j + ε)) V)
    (N : (Fin n → ℝ) → ℝ) (R : (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (hR : DifferentiableOn ℝ R {w | ∀ j, |w.2 j| < b j + ε})
    (hRper : ∀ (k : Fin n → ℤ) (w : (Fin n → ℝ) × (Fin n → ℝ)), (∀ j, |w.2 j| < b j + ε) →
      R (w + (fun i => (k i : ℝ), 0)) = R w)
    (hHΨ : ∀ w : (Fin n → ℝ) × (Fin n → ℝ), (∀ j, |w.2 j| < b j + ε) →
      H (Ψ w) = N w.2 + R w)
    (hRη : ∀ w : (Fin n → ℝ) × (Fin n → ℝ), (∀ j, |w.2 j| ≤ b j) →
      ∀ j, |fderiv ℝ R w (Pi.single j 1, 0)| ≤ η j)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hw₀ : ∀ j, |w₀.2 j| ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = Ψ w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ V ∧ HasDerivAt z (KAM.hamiltonianVectorField H (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = Ψ w₀ →
        (∀ t ∈ I, y t ∈ V ∧ HasDerivAt y (KAM.hamiltonianVectorField H (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → Ψ (Ψinv (z t)) = z t ∧
        ∀ j, |(Ψinv (z t)).2 j - w₀.2 j| ≤ η j * |t| ∧ |(Ψinv (z t)).2 j| ≤ a j + η j * T :=
  torus_confinement a b η ε T hε hT hη hmargin V hV H hH Ψ Ψinv hΨ.chart_smooth
    (fun _ hw => hΨ.chart_maps hw) hΨ.chart_symp hΨ.chart_leftInv N R hR hRper hHΨ hRη w₀ hw₀

/-- Smoke test: the identity chart composed with itself. -/
theorem chart_id_comp_id {D : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hD : IsOpen D) :
    IsCanonicalChart ((id : (Fin n → ℝ) × (Fin n → ℝ) → _) ∘ id) (id ∘ id) D D :=
  (IsCanonicalChart.id_chart hD).chart_comp (IsCanonicalChart.id_chart hD) subset_rfl

end KAM.EffectiveStability
