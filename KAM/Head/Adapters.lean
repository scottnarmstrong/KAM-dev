/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Defs
public import KAM.Head.DerivativeBounds
public import KAM.Head.TorsionRegular
public import KAM.Head.Shift
public import KAM.Head.MixedDifference
public import KAM.Torus.FrozenAgreement

/-!
# Adapters from the Part 4 support lemmas to the forms the Part 4 proofs consume

The Part 4 proofs consume four support lemmas in a form that differs from the one in which they
are proved. The original names stay untouched; the consumed forms are proved here under the new
names `*_design`, from the original lemmas. Later modules call the adapters, and use the consumed
names in their own statements only through them.

| Consumed form | Original lemma | Adapter |
|---|---|---|
| `derivative_bounds` | `KAM.Head.derivative_bounds` | `KAM.Head.derivative_bounds_design` |
| `torsion_regular` | `KAM.Head.torsion_regular` | `KAM.Head.torsion_regular_design` |
| `shift` | `KAM.Head.phase_shift` | `KAM.Head.shift_design` |
| `mixed_difference` | `KAM.Head.mixed_difference` | `KAM.Head.mixed_difference_design` |
| `Hconst s₀ r₀ B h j` | `derivConstH n s₀ r₀ (hBound h B r₀) j` | `Hconst_eq_derivConstH` |
| `Fconst n s₀ r₀ j` | `derivConstF n s₀ r₀ j` | `Fconst_eq_derivConstF` |
| `Mconst s₀ r₀ B h` | `derivConstM n s₀ r₀ (hBound h B r₀)` | `Mconst_eq_derivConstM` |

What differs, adapter by adapter:

* `derivative_bounds_design`: the original statement has six conjunction blocks (the vector-field
  bounds of (c) are a separate block, and the order of `j` and the point is swapped in (b), (c));
  the constants are `derivConst*`. The adapter regroups the blocks and rewrites the constants.
* `torsion_regular_design`: the original hypothesis is `det G_K ≠ 0`, here `IsUnit (det G_K)`. The
  original column identity (b) is for the direction `ω`; the consumed one is for every direction `v`
  (the underlying `KAM.Torus.sumVec_fderiv_normalFrame` is for every direction). The original (c)
  has two extra items (the formula for `X_N` and `⟨T⟩ = avg T`, both dropped), and the original (d)
  uses `IsZPeriodicOn` and also lists `fderiv K`; the consumed uses `IsPeriodicOn`
  (`IsZPeriodicOn.isPeriodicOn`).
* `shift_design`: the Hamiltonian of clause (b) is universally quantified inside the clause, and
  clause (d) lists `IsNormalized (phaseShift K (-phaseAverage K))` instead of the iff.
* `mixed_difference_design`: the same statement; only the implicit binder `Q` moved.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology KAM.Torus

namespace KAM.Head

/-! ### The constants -/

/-- `H_j` of the consumed form is the original `derivConstH` at `M_h = hBound h B r₀`. -/
theorem Hconst_eq_derivConstH {n : ℕ} (s₀ r₀ : ℝ) (B : Set (Fin n → ℝ))
    (h : (Fin n → ℂ) → ℂ) (j : ℕ) :
    Hconst s₀ r₀ B h j = derivConstH n s₀ r₀ (hBound h B r₀) j := by
  simp only [Hconst, derivConstH, div_eq_mul_inv, inv_pow]

/-- `F_j` of the consumed form is the original `derivConstF`. -/
theorem Fconst_eq_derivConstF (n : ℕ) (s₀ r₀ : ℝ) (j : ℕ) :
    Fconst n s₀ r₀ j = derivConstF n s₀ r₀ j := by
  simp only [Fconst, derivConstF, div_eq_mul_inv, inv_pow]

/-- `M` of the consumed form is the original `derivConstM` at `M_h = hBound h B r₀`. -/
theorem Mconst_eq_derivConstM {n : ℕ} (s₀ r₀ : ℝ) (B : Set (Fin n → ℝ))
    (h : (Fin n → ℂ) → ℂ) :
    Mconst s₀ r₀ B h = derivConstM n s₀ r₀ (hBound h B r₀) := by
  simp only [Mconst, derivConstM, div_eq_mul_inv, inv_pow]

/-! ### The adapters -/

/-- Blueprint `bp:p4:derivative-bounds` in the form the Part 4 proofs consume (adapter of
`KAM.Head.derivative_bounds`). -/
theorem derivative_bounds_design {n : ℕ} {s₀ r₀ : ℝ} (hs₀ : 0 < s₀) (hr₀ : 0 < r₀)
    {B : Set (Fin n → ℝ)} (hB : Bornology.IsBounded B) {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (actionNbhd B r₀)) {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hf : DifferentiableOn ℂ f (complexStrip n s₀ ×ˢ actionNbhd B r₀))
    (hfε : ∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ‖f z‖ ≤ ε) :
    -- (a)
    ((∀ z ∈ domainD n s₀ r₀ B, Metric.closedBall z (deltaStar s₀ r₀) ⊆ domainD' n s₀ r₀ B) ∧
      ∀ I ∈ actionNbhd B (r₀ / 2),
        Metric.closedBall I (deltaStar s₀ r₀) ⊆ actionNbhd B (3 * r₀ / 4)) ∧
    -- (b)
    (∀ I ∈ actionNbhd B (r₀ / 2), ∀ j ∈ ({1, 2, 3} : Set ℕ),
      ‖iteratedFDeriv ℂ j h I‖ ≤ Hconst s₀ r₀ B h j) ∧
    -- (c)
    (∀ z ∈ domainD n s₀ r₀ B,
      (∀ j ∈ ({1, 2, 3} : Set ℕ), ‖iteratedFDeriv ℂ j f z‖ ≤ Fconst n s₀ r₀ j * ε) ∧
      ‖hamiltonianVectorFieldℂ f z‖ ≤ Fconst n s₀ r₀ 1 * ε ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ f) z‖ ≤ Fconst n s₀ r₀ 2 * ε) ∧
    -- (d)
    (ε ≤ 1 → ∀ z ∈ domainD n s₀ r₀ B,
      ‖fderiv ℂ (hbold h f) z‖ ≤ Mconst s₀ r₀ B h ∧
      ‖hamiltonianVectorFieldℂ (hbold h f) z‖ ≤ Mconst s₀ r₀ B h ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ (hbold h f)) z‖ ≤ Mconst s₀ r₀ B h ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ (hbold h f)) z‖ ≤ Mconst s₀ r₀ B h) := by
  obtain ⟨a1, a2, b, c, d, e⟩ := derivative_bounds hs₀ hr₀ hB hh hf hfε
  refine ⟨⟨a1, a2⟩, fun I hI j hj => ?_, fun z hz => ?_, fun hε z hz => ?_⟩
  · rw [Hconst_eq_derivConstH]
    exact b j hj I hI
  · refine ⟨fun j hj => ?_, ?_, ?_⟩
    · rw [Fconst_eq_derivConstF]
      exact c j hj z hz
    · rw [Fconst_eq_derivConstF]
      exact (d z hz).1
    · rw [Fconst_eq_derivConstF]
      exact (d z hz).2
  · simp only [Mconst_eq_derivConstM]
    exact e hε z hz

/-- Blueprint `bp:p4:torsion-regular` in the form the Part 4 proofs consume (adapter of
`KAM.Head.torsion_regular`). `K(T_ρ) ⊆ 𝔇`, `det G_K` a
unit on `T_ρ`; frames in the Part 2 carrier (`KAM.Torus`). -/
theorem torsion_regular_design {n : ℕ} {s₀ r₀ : ℝ} (hs₀ : 0 < s₀) (hr₀ : 0 < r₀)
    {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ} (hh : DifferentiableOn ℂ h (actionNbhd B r₀))
    {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (complexStrip n s₀ ×ˢ actionNbhd B r₀))
    (hfper : ∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ∀ k : Fin n → ℤ,
      f (z.1 + (fun i => (k i : ℂ)), z.2) = f z)
    {ρ : ℝ} (hρ : 0 < ρ) {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hK𝔇 : ∀ θ ∈ complexStrip n ρ, K θ ∈ domainD n s₀ r₀ B)
    (hG : ∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K θ).det) (ω : Fin n → ℝ) :
    -- (a)
    ((∀ θ ∈ complexStrip n ρ, gramMatrix K θ * (gramMatrix K θ)⁻¹ = 1 ∧
        (gramMatrix K θ)⁻¹ * gramMatrix K θ = 1) ∧
      DifferentiableOn ℂ (fun θ => (gramMatrix K θ)⁻¹) (complexStrip n ρ) ∧
      ∀ θ ∈ complexStrip n ρ,
        fderiv ℂ (fun θ' => (gramMatrix K θ')⁻¹) θ (fun l => (ω l : ℂ)) =
          -((gramMatrix K θ)⁻¹ * fderiv ℂ (gramMatrix K) θ (fun l => (ω l : ℂ)) *
            (gramMatrix K θ)⁻¹)) ∧
    -- (b)
    (DifferentiableOn ℂ (normalMat K) (complexStrip n ρ) ∧
      ∀ θ ∈ complexStrip n ρ, ∀ (j : Fin n) (v : Fin n → ℂ),
        sumVec n (fderiv ℂ (fun θ' => normalFrame K θ' j) θ v) =
          fun s => fderiv ℂ (normalMat K) θ v s j) ∧
    -- (c)
    ((∀ θ ∈ complexStrip n ρ, torsion (hbold h f) K ω θ =
        (normalMat K θ)ᵀ * omegaZeroMatrix n * normalFieldMat (hbold h f) K ω θ) ∧
      DifferentiableOn ℂ (torsion (hbold h f) K ω) (complexStrip n ρ) ∧
      Continuous (fun x : Fin n → ℝ => torsion (hbold h f) K ω (fun l => (x l : ℂ)))) ∧
    -- (d)
    (IsPrimaryOnStrip K ρ →
      IsPeriodicOn (angleDisplacement K) ρ ∧ IsPeriodicOn (fun θ => (K θ).2) ρ ∧
      IsPeriodicOn (tangentMat K) ρ ∧ IsPeriodicOn (gramMatrix K) ρ ∧
      IsPeriodicOn (normalMat K) ρ ∧ IsPeriodicOn (torsion (hbold h f) K ω) ρ) := by
  have hdet : ∀ θ ∈ complexStrip n ρ, (gramMatrix K θ).det ≠ 0 :=
    fun θ hθ => (isUnit_iff_ne_zero).1 (hG θ hθ)
  obtain ⟨ha, hb, hc, hd⟩ := torsion_regular hs₀ hr₀ hh hf hfper hρ hK hK𝔇 hdet ω
  refine ⟨ha, ⟨hb.1, fun θ hθ j v => ?_⟩, ⟨hc.2.1, hc.2.2.1, hc.2.2.2.1⟩, fun hprim => ?_⟩
  · exact sumVec_fderiv_normalFrame
      (hb.1.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθ)) j v
  · obtain ⟨p1, p2, -, p4, p5, p6, p7⟩ := hd hprim
    exact ⟨p1.isPeriodicOn, p2.isPeriodicOn, p4.isPeriodicOn, p5.isPeriodicOn, p6.isPeriodicOn,
      p7.isPeriodicOn⟩

/-- Blueprint `bp:p4:shift` in the form the Part 4 proofs consume (adapter of
`KAM.Head.phase_shift`). -/
theorem shift_design {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : DifferentiableOn ℂ K (complexStrip n ρ)) (hKp : IsPrimaryOnStrip K ρ)
    (hKr : IsRealOnReals K) (a ω : Fin n → ℝ) :
    -- (a)
    (DifferentiableOn ℂ (phaseShift K a) (complexStrip n ρ) ∧
      IsPrimaryOnStrip (phaseShift K a) ρ ∧ IsRealOnReals (phaseShift K a) ∧
      ∀ θ ∈ complexStrip n ρ,
        fderiv ℂ (phaseShift K a) θ = fderiv ℂ K (θ + fun i => (a i : ℂ))) ∧
    -- (b)
    (∀ φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ,
      (∀ θ ∈ complexStrip n ρ, invarianceError φ (phaseShift K a) ω θ =
        invarianceError φ K ω (θ + fun i => (a i : ℂ))) ∧
      ((∀ θ ∈ complexStrip n ρ, invarianceError φ K ω θ = 0) →
        ∀ θ ∈ complexStrip n ρ, invarianceError φ (phaseShift K a) ω θ = 0)) ∧
    -- (c)
    ((∀ A : ℝ, (∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ K θ‖ ≤ A) →
        ∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ (phaseShift K a) θ‖ ≤ A) ∧
      ∀ (S : Set ((Fin n → ℂ) × (Fin n → ℂ))) (β : ℝ),
        (∀ θ ∈ complexStrip n ρ, Metric.ball (K θ) β ⊆ S) →
        ∀ θ ∈ complexStrip n ρ, Metric.ball (phaseShift K a θ) β ⊆ S) ∧
    -- (d)
    (phaseAverage (phaseShift K a) = phaseAverage K + a ∧
      IsNormalized (phaseShift K (-phaseAverage K)) ∧
      (IsNormalized K → IsNormalized (phaseShift K a) → a = 0)) ∧
    -- (e)
    ∀ I : Fin n → ℝ,
      (∀ A : ℝ, (∀ x : Fin n → ℝ,
          ‖K (fun i => (x i : ℂ)) - unperturbedTorus I (fun i => (x i : ℂ))‖ ≤ A) →
        ‖phaseAverage K‖ ≤ A) ∧
      ∀ θ : Fin n → ℂ, ‖phaseShift K a θ - unperturbedTorus I θ‖ ≤
        ‖K (θ + fun i => (a i : ℂ)) - unperturbedTorus I (θ + fun i => (a i : ℂ))‖ + ‖a‖ := by
  obtain ⟨ha, -, hc, hd, he⟩ := phase_shift hρ hK hKp hKr a ω (fun _ => 0)
  exact ⟨ha, fun φ => (phase_shift hρ hK hKp hKr a ω φ).2.1, hc,
    ⟨hd.1, (hd.2.1 (-phaseAverage K)).2 rfl, hd.2.2⟩, he⟩

/-- Blueprint `bp:p4:mixed-difference` in the form the Part 4 proofs consume (adapter of
`KAM.Head.mixed_difference`). -/
theorem mixed_difference_design {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {F : (Fin n → ℂ) → Fin n → ℂ} (hF : DifferentiableOn ℂ F U) {a v w : Fin n → ℂ}
    (hP : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1, a + t • v + t' • w ∈ U) {Q : ℝ}
    (hQ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℂ 2 F (a + t • v + t' • w)‖ ≤ Q) :
    ‖F (a + v + w) - F (a + v) - F (a + w) + F a‖ ≤ Q * ‖v‖ * ‖w‖ :=
  mixed_difference hU hF hP hQ

end KAM.Head

end
