/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.Data
public import KAM.Head.DerivativeBounds

/-! # P11B initial remainder (`initial`)

The initial remainder `selectionInitial` of the translated Hamiltonian `h(b + η) + f(θ, b + η)`
over the frozen frequency, its holomorphy, the Taylor bound `ε + n C₁ s₀² / 2`, periodicity and
reality. The Taylor estimate uses the Hessian bound along the segment `[b, b + η]` and the
fencing theorem for the one-variable function `s ↦ h(b + sη) - h b - s Dh(b) η`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

def selectionInitial (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (x : SelectionPoint n) : ℂ :=
  d.h (x.2 + x.1.2) + f (x.1.1, x.2 + x.1.2) - d.h x.2

/-- Segment points `b + s η` stay in `B_{t₀ + s₀}`. -/
theorem selectionInitial_segment_mem {K : Set (SelectionR n)} {b η : SelectionC n}
    {t₀ s₀ : ℝ} (hb : b ∈ actionNbhd K t₀) (hη : ‖η‖ < s₀) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : b + (s : ℂ) • η ∈ actionNbhd K (t₀ + s₀) := by
  obtain ⟨J, hJ, hbJ⟩ := hb
  refine ⟨J, hJ, ?_⟩
  have h1 : ‖(s : ℂ) • η‖ ≤ ‖η‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hs0]
    exact mul_le_of_le_one_left (norm_nonneg _) hs1
  calc ‖b + (s : ℂ) • η - fun i => (J i : ℂ)‖
      = ‖(b - fun i => (J i : ℂ)) + (s : ℂ) • η‖ := by congr 1; abel
    _ ≤ ‖b - fun i => (J i : ℂ)‖ + ‖(s : ℂ) • η‖ := norm_add_le _ _
    _ < t₀ + s₀ := by linarith

theorem selectionInitial_actionNbhd_mono {K : Set (SelectionR n)} {r r' : ℝ} (h : r ≤ r') :
    actionNbhd K r ⊆ actionNbhd K r' := fun _ ⟨J, hJ, hI⟩ => ⟨J, hJ, lt_of_lt_of_le hI h⟩

/-- Directional derivative of the frequency as a sum over coordinate derivatives. -/
theorem selectionInitial_fderiv_apply (h : SelectionC n → ℂ) (b η : SelectionC n) :
    fderiv ℂ h b η = ∑ i, fderiv ℂ h b (Pi.single i 1) * η i := by
  conv_lhs => rw [show η = ∑ i, η i • (Pi.single i 1 : SelectionC n) by
    ext j; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

/-- The frequency vector is holomorphic on the open collar. -/
theorem selectionInitial_gradient_differentiableOn (d : SelectionData n) :
    DifferentiableOn ℂ (fun z i => fderiv ℂ d.h z (Pi.single i 1))
      (actionNbhd d.K (2 * d.ϑ)) := by
  have hU := KAM.Head.isOpen_actionNbhd d.K (2 * d.ϑ)
  have hF := (KAM.holomorphic_regularity_of_finiteDimensional hU d.holo).1
  refine differentiableOn_pi.2 fun i => ?_
  exact hF.clm_apply (differentiableOn_const _)

/-- Second-order Taylor remainder of the frequency along a collar segment. -/
theorem selectionInitial_taylor (d : SelectionData n) {t₀ s₀ : ℝ} (ht' : t₀ ≤ d.ϑ)
    (hs' : s₀ ≤ d.ϑ) {b η : SelectionC n} (hb : b ∈ actionNbhd d.K t₀) (hη : ‖η‖ < s₀) :
    ‖d.h (b + η) - d.h b - ∑ i, fderiv ℂ d.h b (Pi.single i 1) * η i‖ ≤
      n / 2 * d.C₁ * ‖η‖ ^ 2 := by
  have hU := KAM.Head.isOpen_actionNbhd d.K (2 * d.ϑ)
  have hmem : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → b + (s : ℂ) • η ∈ actionNbhd d.K (2 * d.ϑ) :=
    fun s h0 h1 => selectionInitial_actionNbhd_mono (by linarith)
      (selectionInitial_segment_mem hb hη h0 h1)
  set g : SelectionC n → SelectionC n := fun z i => fderiv ℂ d.h z (Pi.single i 1) with hg
  have hgd := selectionInitial_gradient_differentiableOn d
  -- gradient Lipschitz bound along the segment
  have hLip : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ i, ‖g (b + (s : ℂ) • η) i - g b i‖ ≤
      d.C₁ * (s * ‖η‖) := by
    intro s h0 h1 i
    have hconv : Convex ℝ (segment ℝ b (b + η)) := convex_segment _ _
    have hseg : ∀ z ∈ segment ℝ b (b + η), z ∈ actionNbhd d.K (2 * d.ϑ) := by
      intro z hz
      rw [segment_eq_image'] at hz
      obtain ⟨u, ⟨hu0, hu1⟩, rfl⟩ := hz
      have := hmem u hu0 hu1
      simpa [add_sub_cancel_left, Complex.coe_smul] using this
    have hdiff : ∀ z ∈ segment ℝ b (b + η), DifferentiableAt ℂ g z := fun z hz =>
      (hgd z (hseg z hz)).differentiableAt (hU.mem_nhds (hseg z hz))
    have hb' : b ∈ segment ℝ b (b + η) := left_mem_segment _ _ _
    have hbnd : ∀ z ∈ segment ℝ b (b + η), ‖fderiv ℂ g z‖ ≤ d.C₁ := fun z hz =>
      d.hessian z (hseg z hz)
    have hs : b + (s : ℂ) • η ∈ segment ℝ b (b + η) := by
      rw [segment_eq_image']
      exact ⟨s, ⟨h0, h1⟩, by simp [Complex.coe_smul]⟩
    have := hconv.norm_image_sub_le_of_norm_fderiv_le hdiff hbnd hb' hs
    calc ‖g (b + (s : ℂ) • η) i - g b i‖ = ‖(g (b + (s : ℂ) • η) - g b) i‖ := rfl
      _ ≤ ‖g (b + (s : ℂ) • η) - g b‖ := norm_le_pi_norm _ i
      _ ≤ d.C₁ * ‖b + (s : ℂ) • η - b‖ := this
      _ = d.C₁ * (s * ‖η‖) := by
        congr 1
        rw [add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_of_nonneg h0]
  -- fencing argument
  set φ : ℝ → ℂ := fun s => d.h (b + (s : ℂ) • η) - d.h b -
    (s : ℂ) * ∑ i, fderiv ℂ d.h b (Pi.single i 1) * η i with hφ
  set φ' : ℝ → ℂ := fun s => ∑ i, η i * (g (b + (s : ℂ) • η) i - g b i) with hφ'
  have hderiv : ∀ s ∈ Ico (0 : ℝ) 1, HasDerivWithinAt φ (φ' s) (Ici s) s := by
    intro s hs
    have hz := hmem s hs.1 hs.2.le
    have hh : HasFDerivAt d.h (fderiv ℂ d.h (b + (s : ℂ) • η)) (b + (s : ℂ) • η) :=
      ((d.holo _ hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt
    have hline : HasDerivAt (fun s : ℝ => b + (s : ℂ) • η) η s := by
      have := ((hasDerivAt_id s).ofReal_comp).smul_const η
      simpa using this.const_add b
    have h1 := (hh.restrictScalars ℝ).comp_hasDerivAt s hline
    have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * ∑ i, fderiv ℂ d.h b (Pi.single i 1) * η i)
        (∑ i, fderiv ℂ d.h b (Pi.single i 1) * η i) s := by
      simpa using (hasDerivAt_id s).ofReal_comp.mul_const
        (∑ i, fderiv ℂ d.h b (Pi.single i 1) * η i)
    refine ((h1.sub_const _).sub h2).hasDerivWithinAt.congr_deriv ?_
    simp only [φ', ContinuousLinearMap.coe_restrictScalars']
    rw [selectionInitial_fderiv_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [g]; ring
  have hcont : ContinuousOn φ (Icc 0 1) := by
    intro s hs
    have hz := hmem s hs.1 hs.2
    have hh : ContinuousAt d.h (b + (s : ℂ) • η) :=
      ((d.holo _ hz).differentiableAt (hU.mem_nhds hz)).continuousAt
    have hl : Continuous fun s : ℝ => b + (s : ℂ) • η := by fun_prop
    refine ContinuousAt.continuousWithinAt ?_
    exact ((ContinuousAt.comp (g := d.h) (x := s) hh hl.continuousAt).sub continuousAt_const).sub
      (by fun_prop)
  set c : ℝ := n * d.C₁ * ‖η‖ ^ 2 with hc
  have hC : 0 ≤ d.C₁ := by linarith [d.hessian_normalized]
  have hB : ∀ s : ℝ, HasDerivAt (fun s : ℝ => c / 2 * s ^ 2) (c * s) s := by
    intro s
    convert (hasDerivAt_pow 2 s).const_mul (c / 2) using 1
    simp; ring
  have hres := image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont hderiv
    (B := fun s : ℝ => c / 2 * s ^ 2) (B' := fun s => c * s)
    (by simp [φ]) hB (by
      intro s hs
      have h0 := hs.1
      have h1 := hs.2.le
      calc ‖φ' s‖ ≤ ∑ i, ‖η i * (g (b + (s : ℂ) • η) i - g b i)‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin n, (‖η‖ * (d.C₁ * (s * ‖η‖))) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [norm_mul]
            exact mul_le_mul (norm_le_pi_norm η i) (hLip s h0 h1 i) (norm_nonneg _)
              (norm_nonneg _)
        _ = c * s := by simp [hc]; ring)
    (x := 1) ⟨zero_le_one, le_rfl⟩
  have := hres
  simp only [φ, hc, Complex.ofReal_one, one_smul, one_mul, one_pow, mul_one] at this
  simpa [hc, mul_comm, mul_assoc, mul_left_comm, div_eq_mul_inv] using this

/-- `initial`: Taylor remainder, periodicity and reality of the initial remainder. -/
theorem initial (d : SelectionData n) (f : SelectionPhaseC n → ℂ) (ε t₀ s₀ : ℝ)
    (hf : SelectionPerturbation d f ε) (ht : 0 < t₀) (ht' : t₀ ≤ d.ϑ)
    (_hs : 0 < s₀) (hs' : s₀ ≤ d.ϑ) :
    DifferentiableOn ℂ (fun x => selectionInitial d f x -
      ∑ i, fderiv ℂ d.h x.2 (Pi.single i 1) * x.1.2 i)
      (selectionDomain d.strip s₀ (actionNbhd d.K t₀)) ∧
    (∀ x ∈ selectionDomain d.strip s₀ (actionNbhd d.K t₀),
      ‖selectionInitial d f x - ∑ i, fderiv ℂ d.h x.2 (Pi.single i 1) * x.1.2 i‖
        ≤ ε + n / 2 * d.C₁ * s₀ ^ 2) ∧
    (∀ x ∈ selectionDomain d.strip s₀ (actionNbhd d.K t₀), ∀ k : Fin n → ℤ,
      selectionInitial d f ((x.1.1 + (fun i => (k i : ℂ)), x.1.2), x.2) = selectionInitial d f x) ∧
    ∀ z : Phase n, ∀ b : SelectionR n,
      (phaseToC z, selectionReal b) ∈ selectionDomain d.strip s₀ (actionNbhd d.K t₀) →
      (selectionInitial d f (phaseToC z, selectionReal b)).im = 0 := by
  have hU := KAM.Head.isOpen_actionNbhd d.K (2 * d.ϑ)
  have hsum : ∀ x : SelectionPoint n, x ∈ selectionDomain d.strip s₀ (actionNbhd d.K t₀) →
      x.2 + x.1.2 ∈ actionNbhd d.K (2 * d.ϑ) := by
    intro x hx
    obtain ⟨-, hη, hb⟩ := hx
    have := selectionInitial_segment_mem hb hη (s := 1) zero_le_one le_rfl
    simpa using selectionInitial_actionNbhd_mono (by linarith) this
  have hb2 : ∀ x : SelectionPoint n, x ∈ selectionDomain d.strip s₀ (actionNbhd d.K t₀) →
      x.2 ∈ actionNbhd d.K (2 * d.ϑ) := fun x hx =>
    selectionInitial_actionNbhd_mono (by linarith) hx.2.2
  have hfmem : ∀ x : SelectionPoint n, x ∈ selectionDomain d.strip s₀ (actionNbhd d.K t₀) →
      (x.1.1, x.2 + x.1.2) ∈ complexStrip n d.strip ×ˢ actionNbhd d.K (2 * d.ϑ) :=
    fun x hx => ⟨hx.1, hsum x hx⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    have hsum_d : DifferentiableAt ℂ (fun x : SelectionPoint n => x.2 + x.1.2) x := by fun_prop
    have h1 : DifferentiableAt ℂ (fun x : SelectionPoint n => d.h (x.2 + x.1.2)) x :=
      DifferentiableAt.comp x
        ((d.holo _ (hsum x hx)).differentiableAt (hU.mem_nhds (hsum x hx))) hsum_d
    have hopen : IsOpen (complexStrip n d.strip ×ˢ actionNbhd d.K (2 * d.ϑ)) :=
      (isOpen_complexStrip n d.strip).prod hU
    have h2 : DifferentiableAt ℂ (fun x : SelectionPoint n => f (x.1.1, x.2 + x.1.2)) x := by
      have hmap : DifferentiableAt ℂ (fun x : SelectionPoint n => (x.1.1, x.2 + x.1.2)) x := by
        fun_prop
      exact DifferentiableAt.comp x
        ((hf.holo _ (hfmem x hx)).differentiableAt (hopen.mem_nhds (hfmem x hx))) hmap
    have h3 : DifferentiableAt ℂ (fun x : SelectionPoint n => d.h x.2) x :=
      DifferentiableAt.comp x
        ((d.holo _ (hb2 x hx)).differentiableAt (hU.mem_nhds (hb2 x hx))) (by fun_prop)
    have h4 : DifferentiableAt ℂ (fun x : SelectionPoint n =>
        ∑ i, fderiv ℂ d.h x.2 (Pi.single i 1) * x.1.2 i) x := by
      have hg : DifferentiableAt ℂ (fun z i => fderiv ℂ d.h z (Pi.single i 1)) x.2 :=
        (selectionInitial_gradient_differentiableOn d x.2 (hb2 x hx)).differentiableAt
          (hU.mem_nhds (hb2 x hx))
      refine DifferentiableAt.fun_sum fun i _ => ?_
      have hgi := differentiableAt_pi.1 hg i
      exact (DifferentiableAt.comp x hgi (by fun_prop)).mul (by fun_prop)
    exact ((h1.add h2).sub h3 |>.sub h4).differentiableWithinAt
  · intro x hx
    have hT := selectionInitial_taylor d ht' hs' hx.2.2 hx.2.1
    have hfb := hf.bound _ (hfmem x hx)
    have heq : selectionInitial d f x - ∑ i, fderiv ℂ d.h x.2 (Pi.single i 1) * x.1.2 i =
        (d.h (x.2 + x.1.2) - d.h x.2 - ∑ i, fderiv ℂ d.h x.2 (Pi.single i 1) * x.1.2 i) +
          f (x.1.1, x.2 + x.1.2) := by simp only [selectionInitial]; ring
    rw [heq]
    have hC : 0 ≤ d.C₁ := by linarith [d.hessian_normalized]
    have hsq : ‖x.1.2‖ ^ 2 ≤ s₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx.2.1.le 2
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ n / 2 * d.C₁ * ‖x.1.2‖ ^ 2 + ε := add_le_add hT hfb
      _ ≤ ε + n / 2 * d.C₁ * s₀ ^ 2 := by
        have : 0 ≤ (n : ℝ) / 2 * d.C₁ := by positivity
        nlinarith
  · intro x hx k
    have := hf.periodic _ (hfmem x hx) k
    simpa [selectionInitial] using this
  · intro z b hx
    have hs1 := hsum _ hx
    have hb1 := hb2 _ hx
    have hf1 := hfmem _ hx
    have e : selectionReal b + (fun i => ((z.2 i : ℝ) : ℂ)) = selectionReal (b + z.2) := by
      ext i; simp [selectionReal]
    have e : selectionReal b + (fun i => ((z.2 i : ℝ) : ℂ)) = selectionReal (b + z.2) := by
      ext i; simp [selectionReal]
    have key : selectionInitial d f (phaseToC z, selectionReal b) =
        d.h (selectionReal (b + z.2)) + f (phaseToC (z.1, b + z.2)) - d.h (selectionReal b) := by
      simp only [selectionInitial, phaseToC]
      rw [e]; rfl
    have hR1 := d.real (b + z.2) (by rw [← e]; exact hs1)
    have hR2 := d.real b hb1
    have hR3 : (f (phaseToC (z.1, b + z.2))).im = 0 := hf.real _ (by
      have h1 : (phaseToC (z.1, b + z.2)) =
          ((phaseToC z).1, selectionReal b + (phaseToC z).2) := by
        refine Prod.ext rfl ?_
        ext i; simp [phaseToC, selectionReal]
      rw [h1]; exact hf1)
    rw [key]
    simp [hR1, hR2, hR3]

end KAM.Planetary
