/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.ExtFlow
public import KAM.Nekhoroshev.Partial.VectorField
public import KAM.Nekhoroshev.Partial.RealSystem
public import KAM.Nekhoroshev.Partial.Symplectic
public import KAM.Canonical.FlowInverse
public import KAM.Weighted.Cauchy
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The canonical map `Φ = X¹_φ` on the extended phase space (`bpN:p11:canonical-map`)

Part 11, package N11-F2. The canonical map `Φ = extFlow … 1` and its inverse `Ψ = extFlow … (-1)`
are obtained from the generic Part 5 flow of the weighted field `wfield b.c φ` on
`Ω = 𝒟_{R-ρ,s-σ}`, with the gauge `W = diag(σ⁻¹, ρ⁻¹)` of the scaled norm `scaled ρ σ`:

* `canonical_map_core`: every clause of the source statement except the canonical identity
  (holomorphy and images of `Φ`, `Ψ` on `U = 𝒟_{R-3ρ/2,s-3σ/2}`, the displacement bounds
  including the slow one, integer angle equivariance, two-sided inverse and `Φ z ∈ U` on
  `𝒟_{R-2ρ,s-2σ}`, the derivative estimate, reality);
* `canonical_map_of_pos`: the same together with `ExtCanonical b.c U Φ`, valid for `0 < b.c`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Nekhoroshev

open KAM.Weighted

variable {n k : ℕ}

/-! ### The gauge -/

/-- The gauge `diag(σ⁻¹, ρ⁻¹)` of `scaled ρ σ` on the extended coordinates. -/
private def extGauge (ρ σ : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ) : EC n k ≃L[ℂ] EC n k :=
  (ContinuousLinearEquiv.smulLeft (Units.mk0 ((σ : ℂ)⁻¹) (by simpa using hσ.ne'))).prodCongr
    (ContinuousLinearEquiv.smulLeft (Units.mk0 ((ρ : ℂ)⁻¹) (by simpa using hρ.ne')))

private theorem norm_extGauge {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (z : EC n k) :
    ‖extGauge ρ σ hρ hσ z‖ = scaled ρ σ z := by
  simp [extGauge, scaled, Prod.norm_def, norm_smul, abs_of_pos hρ, abs_of_pos hσ,
    div_eq_inv_mul]

/-- A point at scaled distance `≤ c` from `𝒟_{r₀, s₀}` lies in `𝒟_{r₀ + ρ c, s₀ + σ c}`. -/
private theorem dom_of_scaled_le {D : Set (Fin (n+(k+k)) → ℂ)} {ρ σ c r₀ s₀ : ℝ} (hρ : 0 < ρ)
    (hσ : 0 < σ) (hc : 0 < c) (hr₀ : 0 < r₀) (hs₀ : 0 < s₀) {z w : EC n k}
    (hz : z ∈ Dom n D r₀ s₀) (hw : scaled ρ σ (w - z) ≤ c) :
    w ∈ Dom n D (r₀ + ρ * c) (s₀ + σ * c) := by
  have h1 : ‖w.1 - z.1‖ / σ ≤ c := (le_max_left _ _).trans hw
  have h2 : ‖w.2 - z.2‖ / ρ ≤ c := (le_max_right _ _).trans hw
  have hρc := mul_pos hρ hc
  have hσc := mul_pos hσ hc
  refine polydisc_subset_Dom hr₀ (by linarith) hs₀ (by linarith) hz ⟨?_, ?_⟩
  · rw [div_le_iff₀ hσ] at h1
    linarith
  · rw [div_le_iff₀ hρ] at h2
    linarith

/-! ### Regularity, periodicity and reality of the weighted field -/

private theorem differentiableOn_wfield (c : ℝ) {U : Set (EC n k)} (hU : IsOpen U)
    {φ : EC n k → ℂ} (hφ : DifferentiableOn ℂ φ U) : DifferentiableOn ℂ (wfield c φ) U := by
  have h := (KAM.holomorphic_regularity_of_finiteDimensional hU hφ).1
  have hc : ∀ a : EC n k, DifferentiableOn ℂ (fun z => fderiv ℂ φ z a) U := fun a =>
    h.clm_apply (differentiableOn_const a)
  refine DifferentiableOn.prodMk (differentiableOn_pi.2 fun i => hc _)
    (differentiableOn_pi.2 fun j => ?_)
  refine ext_cases (P := fun j => DifferentiableOn ℂ (fun z => (wfield c φ z).2 j) U)
    (fun i => ?_) (fun i => ?_) (fun i => ?_) j
  · simpa only [wfield, Fin.append_left] using (hc _).neg
  · simpa only [wfield, Fin.append_right, Fin.append_left] using
      (differentiableOn_const (c : ℂ)).mul (hc _)
  · simpa only [wfield, Fin.append_right] using
      (differentiableOn_const (-(c : ℂ))).mul (hc _)

private theorem wfield_real (b : PartialBlock n k) {R s ρ σ : ℝ} {φ : EC n k → ℂ}
    (hR : 0 < R) (hs : 0 < s) (hρR : ρ ≤ R) (hσs : σ ≤ s) (hH : ext_class b R s φ)
    (z : ER n k) (hz : extCx z ∈ Dom n b.base (R-ρ) (s-σ)) :
    extCx (extRe (wfield b.c φ (extCx z))) = wfield b.c φ (extCx z) := by
  have _ := hσs
  have hz' : z ∈ b.realDom R :=
    ⟨KAM.ofReal_mem_complexStrip one_pos z.1, polyNbhd_mono (by linarith) hz.2⟩
  have h := (real_system b hR hs hH).2.2.1 z hz'
  rw [← h]
  have : extRe (extCx (realWfield b.c (realHamiltonianExt b R φ) z)) =
      realWfield b.c (realHamiltonianExt b R φ) z :=
    Prod.ext (funext fun i => by simp [extRe, extCx]) (funext fun i => by simp [extRe, extCx])
  rw [this]

private theorem prod_add_mk (w : EC n k) (a : Fin n → ℂ) :
    w + (a, 0) = (w.1 + a, w.2) := Prod.ext rfl (add_zero _)

private theorem dom_shift {D : Set (Fin (n+(k+k)) → ℂ)} {r s : ℝ} {a : Fin n → ℂ}
    (ha : ∀ i, (a i).im = 0) {z : EC n k} (hz : z ∈ Dom n D r s) :
    (z.1 + a, z.2) ∈ Dom n D r s :=
  ⟨fun i => by simpa [ha i] using hz.1 i, hz.2⟩

/-- The field of a periodic function is invariant under integer angle translations. -/
private theorem wfield_periodic (c : ℝ) {D : Set (Fin (n+(k+k)) → ℂ)} {r s r₀ s₀ : ℝ}
    {φ : EC n k → ℂ} (hφ : InClass D r s φ) (hr : r₀ ≤ r) (hs : s₀ ≤ s) (ℓ : Fin n → ℤ)
    {w : EC n k} (hw : w ∈ Dom n D r₀ s₀) :
    wfield c φ (w + ((fun i => (ℓ i : ℂ)), 0)) = wfield c φ w := by
  have hev : (fun x => φ (x + ((fun i => (ℓ i : ℂ)), 0))) =ᶠ[nhds w] φ := by
    filter_upwards [(isOpen_Dom (n := n) D r₀ s₀).mem_nhds hw] with x hx
    have hx' := Dom_mono hr hs hx
    have := KAM.periodic_int_shift (u := fun θ => φ (θ, x.2))
      (fun i θ hθ => hφ.periodic i (θ, x.2) ⟨hθ, hx'.2⟩) ℓ hx'.1
    rw [prod_add_mk]
    exact this
  have hf : fderiv ℂ φ (w + ((fun i => (ℓ i : ℂ)), 0)) = fderiv ℂ φ w := by
    rw [← fderiv_comp_add_right, hev.fderiv_eq]
  simp only [wfield, hf]

/-! ### Component bounds for the field and mean value along trajectories -/

private theorem wfield_comp_bound (b : PartialBlock n k) (hk : 1 ≤ k) {R s ρ σ U : ℝ}
    {φ : EC n k → ℂ} (hρ : 0 < ρ) (hρR : ρ < R) (hσ : 0 < σ) (hσs : σ < s)
    (hSL : slowLoss b.c ρ σ k) (hU : 0 ≤ U) (hφ : InClass b.base R s φ)
    (hb : WBound b.base R s φ U) :
    ∀ z ∈ Dom n b.base (R-ρ) (s-σ), ‖(wfield b.c φ z).1‖ ≤ U/ρ ∧
      ‖fastAction (wfield b.c φ z)‖ ≤ U/(Real.exp 1*σ) ∧ ‖slowPair (wfield b.c φ z)‖ ≤ b.c*U/ρ := by
  intro z hz
  obtain ⟨hs1, hs2⟩ := vf b hk hρ hρR hσ hσs hSL hU hφ hb z hz
  have hcl := cauchy_loss hφ hb hρ hρR hσ hσs
  have hφθ : ∀ j, InClass b.base R (s - σ) (dtheta j φ) := fun j =>
    inClass_fderiv_apply ⟨hφ.differentiableOn.mono (Dom_mono le_rfl (by linarith)),
      fun l w hw => hφ.periodic l w (Dom_mono le_rfl (by linarith) hw)⟩ (Pi.single j 1, 0)
  have hθ : ∀ j, ‖dtheta j φ z‖ ≤ U / (Real.exp 1 * σ) := fun j =>
    sup_le_wbound (hφθ j) (hcl.2.1 j) z (Dom_mono (by linarith) le_rfl hz)
  refine ⟨?_, ?_, hs2⟩
  · have h1 : ‖(wfield b.c φ z).1‖ / σ ≤ U / (ρ * σ) := (le_max_left _ _).trans hs1
    rw [div_le_iff₀ hσ] at h1
    refine h1.trans_eq ?_
    field_simp
  · refine (pi_norm_le_iff_of_nonneg (div_nonneg hU (by positivity))).2 fun i => ?_
    simp only [fastAction, wfield, Fin.append_left, norm_neg]
    exact hθ i

private def fastCLM (n k : ℕ) : EC n k →L[ℝ] (Fin n → ℂ) :=
  (ContinuousLinearMap.pi fun i : Fin n =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+(k+k)) => ℂ)
      (Fin.castAdd (k+k) i)).comp (ContinuousLinearMap.snd ℝ (Fin n → ℂ) (Fin (n+(k+k)) → ℂ))

private def slowCLM (n k : ℕ) : EC n k →L[ℝ] (Fin k → ℂ) × (Fin k → ℂ) :=
  ((ContinuousLinearMap.pi fun i : Fin k =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+(k+k)) => ℂ)
      (Fin.natAdd n (Fin.castAdd k i))).prod
    (ContinuousLinearMap.pi fun i : Fin k =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+(k+k)) => ℂ)
        (Fin.natAdd n (Fin.natAdd k i)))).comp
    (ContinuousLinearMap.snd ℝ (Fin n → ℂ) (Fin (n+(k+k)) → ℂ))

/-- Mean value along a trajectory: a component of the field bounded by `C` along the trajectory
moves by at most `C |t|`. -/
private theorem component_mvt {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : EC n k →L[ℝ] G) {X : EC n k → EC n k} {Ω : Set (EC n k)} {γ : ℝ → EC n k}
    (hsol : KAM.ODE.IsSolutionIn X Ω (Icc (-1) 1) γ) {C : ℝ}
    (hC : ∀ t ∈ Icc (-1 : ℝ) 1, ‖L (X (γ t))‖ ≤ C) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖L (γ t) - L (γ 0)‖ ≤ C * |t| := by
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => L (γ t)) (f' := fun t => L (X (γ t))) (C := C)
    (fun x hx => (L.hasFDerivAt.comp_hasDerivAt x (hsol x hx).2).hasDerivWithinAt) hC h0 ht
  simpa using this

/-! ### The statements -/

theorem canonical_map_core (b : PartialBlock n k) (hk : 1 ≤ k) {R s ρ σ V : ℝ}
    {φ : EC n k → ℂ}
    (hρ : 0 < ρ) (hρR : ρ < R/2) (hσ : 0 < σ) (hσs : σ < s/2)
    (hSL : slowLoss b.c ρ σ k) (hV : 0 ≤ V) (hsmall : V/(ρ*σ) ≤ 1/2)
    (hφ : InClass b.base R s φ) (hb : WBound b.base R s φ V) :
    let Φ := extFlow b R s ρ σ φ 1
    let Ψ := extFlow b R s ρ σ φ (-1)
    let U := Dom n b.base (R-3*ρ/2) (s-3*σ/2)
    DifferentiableOn ℂ Φ U ∧ DifferentiableOn ℂ Ψ U ∧ MapsTo Φ U (Dom n b.base (R-ρ) (s-σ)) ∧
    MapsTo Ψ U (Dom n b.base (R-ρ) (s-σ)) ∧
    (∀ z ∈ U, ‖(Φ z).1-z.1‖ ≤ V/ρ ∧ ‖fastAction (Φ z)-fastAction z‖ ≤ V/(Real.exp 1*σ) ∧
      ‖slowPair (Φ z)-slowPair z‖ ≤ b.c*V/ρ) ∧
    (∀ z ∈ U, ∀ ℓ : Fin n → ℤ,
      Φ (z.1+(fun i => (ℓ i:ℂ)), z.2) = Φ z+((fun i => (ℓ i:ℂ)),0)) ∧
    (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), Ψ (Φ z) = z ∧ Φ (Ψ z) = z ∧ Φ z ∈ U) ∧
    (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), ∀ v : EC n k,
      scaled ρ σ (fderiv ℂ Φ z v-v) ≤ 2*(V/(ρ*σ))*scaled ρ σ v) ∧
    (extReal (Dom n b.base R s) φ → ∀ z : ER n k, extCx z ∈ U →
      extCx (extRe (Φ (extCx z))) = Φ (extCx z)) := by
  intro Φ Ψ U
  have hR : 0 < R := by linarith
  have hs : 0 < s := by linarith
  have hρ1 : ρ < R := by linarith
  have hσ1 : σ < s := by linarith
  obtain ⟨W, hW⟩ : ∃ W : EC n k ≃L[ℂ] EC n k, ∀ z, ‖W z‖ = scaled ρ σ z :=
    ⟨extGauge ρ σ hρ hσ, norm_extGauge hρ hσ⟩
  have hε : 0 ≤ V / (ρ * σ) := div_nonneg hV (mul_pos hρ hσ).le
  have hvf := vf b hk hρ hρ1 hσ hσ1 hSL hV hφ hb
  have hF : KAM.Canonical.SmallField W (Dom n b.base (R-ρ) (s-σ)) (wfield b.c φ)
      (V / (ρ * σ)) :=
    { isOpen := isOpen_Dom _ _ _
      differentiableOn := differentiableOn_wfield b.c (isOpen_Dom _ _ _)
        (hφ.differentiableOn.mono (Dom_mono (by linarith) (by linarith)))
      eps_nonneg := hε
      eps_le := hsmall
      bound := fun z hz => by rw [hW]; exact (hvf z hz).1 }
  have hgh : U ⊆ KAM.Canonical.gaugeInterior W (Dom n b.base (R-ρ) (s-σ)) (1/2) := by
    intro z hz w hw
    rw [hW] at hw
    have := dom_of_scaled_le hρ hσ (by norm_num : (0:ℝ) < 1/2) (by linarith) (by linarith) hz hw
    exact Dom_mono (by linarith) (by linarith) this
  have hg1 : Dom n b.base (R-2*ρ) (s-2*σ) ⊆
      KAM.Canonical.gaugeInterior W (Dom n b.base (R-ρ) (s-σ)) 1 := by
    intro z hz w hw
    rw [hW] at hw
    have := dom_of_scaled_le hρ hσ (by norm_num : (0:ℝ) < 1) (by linarith) (by linarith) hz hw
    exact Dom_mono (by linarith) (by linarith) this
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hm1 : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  refine ⟨((KAM.Canonical.flow_b hF).2.1 1 h1).mono hgh,
    ((KAM.Canonical.flow_b hF).2.1 (-1) hm1).mono hgh,
    fun z hz => (KAM.Canonical.flow_b hF).2.2.1 1 h1 z (hgh hz),
    fun z hz => (KAM.Canonical.flow_b hF).2.2.1 (-1) hm1 z (hgh hz), ?_, ?_, ?_, ?_, ?_⟩
  · -- displacement
    intro z hz
    obtain ⟨h0, hsol, -, -⟩ := KAM.Canonical.flow_a hF (hgh hz)
    have hcb := wfield_comp_bound b hk hρ hρ1 hσ hσ1 hSL hV hφ hb
    have a1 := component_mvt (ContinuousLinearMap.fst ℝ (Fin n → ℂ) (Fin (n+(k+k)) → ℂ)) hsol
      (C := V/ρ) (fun t ht => (hcb _ (hsol t ht).1).1) h1
    have a2 := component_mvt (fastCLM n k) hsol (C := V/(Real.exp 1*σ))
      (fun t ht => (hcb _ (hsol t ht).1).2.1) h1
    have a3 := component_mvt (slowCLM n k) hsol (C := b.c*V/ρ)
      (fun t ht => (hcb _ (hsol t ht).1).2.2) h1
    simp only [h0, abs_one, mul_one] at a1 a2 a3
    exact ⟨a1, a2, a3⟩
  · -- integer angle equivariance
    intro z hz ℓ
    have hτΩ : (fun w => w + ((fun i => (ℓ i : ℂ)), (0 : Fin (n+(k+k)) → ℂ))) ''
        Dom n b.base (R-ρ) (s-σ) = Dom n b.base (R-ρ) (s-σ) := by
      refine Subset.antisymm ?_ ?_
      · rintro _ ⟨w, hw, rfl⟩
        beta_reduce
        rw [prod_add_mk]
        exact dom_shift (a := fun i => (ℓ i : ℂ)) (fun i => by simp) hw
      · intro w hw
        refine ⟨(w.1 + fun i => ((-ℓ i : ℤ) : ℂ), w.2), dom_shift (fun i => by simp) hw, ?_⟩
        beta_reduce
        rw [prod_add_mk]
        ext i <;> simp
    have hτF : ∀ w ∈ Dom n b.base (R-ρ) (s-σ), wfield b.c φ
        (w + ((fun i => (ℓ i : ℂ)), (0 : Fin (n+(k+k)) → ℂ))) = wfield b.c φ w :=
      fun w hw => wfield_periodic b.c hφ (by linarith) (by linarith) ℓ hw
    have := (KAM.Canonical.flow_d hF hτΩ hτF).2 z (hgh hz) 1 h1
    rwa [prod_add_mk] at this
  · -- two-sided inverse and image
    intro z hz
    obtain ⟨-, e1, -, e2, -⟩ := KAM.Canonical.flow_c hF (hg1 hz)
    refine ⟨e1, e2, ?_⟩
    have hz' : z ∈ U := Dom_mono (by linarith) (by linarith) hz
    have hdisp := (KAM.Canonical.flow_a hF (hgh hz')).2.2.2 1 h1
    rw [hW, abs_one, one_mul] at hdisp
    have := dom_of_scaled_le hρ hσ (by norm_num : (0:ℝ) < 1/2) (by linarith) (by linarith) hz
      (hdisp.trans hsmall)
    exact Dom_mono (by linarith) (by linarith) this
  · -- derivative estimate
    intro z hz v
    obtain ⟨-, -, -, -, h⟩ := KAM.Canonical.flow_c hF (hg1 hz)
    have := h 1 h1 v
    rwa [hW, hW] at this
  · -- reality
    intro hreal z hz
    exact flow_real W hF (wfield_real b hR hs hρ1.le hσ1.le ⟨hφ, hreal⟩) (hgh hz)
      (t := 1) (by simp)

/-- The signed `canonical_map` for a block with positive slow weight `b.c`. -/
theorem canonical_map_of_pos (b : PartialBlock n k) (hk : 1 ≤ k) {R s ρ σ V : ℝ}
    {φ : EC n k → ℂ} (hc : 0 < b.c)
    (hρ : 0 < ρ) (hρR : ρ < R/2) (hσ : 0 < σ) (hσs : σ < s/2)
    (hSL : slowLoss b.c ρ σ k) (hV : 0 ≤ V) (hsmall : V/(ρ*σ) ≤ 1/2)
    (hφ : InClass b.base R s φ) (hb : WBound b.base R s φ V) :
    let Φ := extFlow b R s ρ σ φ 1
    let Ψ := extFlow b R s ρ σ φ (-1)
    let U := Dom n b.base (R-3*ρ/2) (s-3*σ/2)
    DifferentiableOn ℂ Φ U ∧ DifferentiableOn ℂ Ψ U ∧ MapsTo Φ U (Dom n b.base (R-ρ) (s-σ)) ∧
    MapsTo Ψ U (Dom n b.base (R-ρ) (s-σ)) ∧
    ExtCanonical b.c U Φ ∧
    (∀ z ∈ U, ‖(Φ z).1-z.1‖ ≤ V/ρ ∧ ‖fastAction (Φ z)-fastAction z‖ ≤ V/(Real.exp 1*σ) ∧
      ‖slowPair (Φ z)-slowPair z‖ ≤ b.c*V/ρ) ∧
    (∀ z ∈ U, ∀ ℓ : Fin n → ℤ,
      Φ (z.1+(fun i => (ℓ i:ℂ)), z.2) = Φ z+((fun i => (ℓ i:ℂ)),0)) ∧
    (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), Ψ (Φ z) = z ∧ Φ (Ψ z) = z ∧ Φ z ∈ U) ∧
    (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), ∀ v : EC n k,
      scaled ρ σ (fderiv ℂ Φ z v-v) ≤ 2*(V/(ρ*σ))*scaled ρ σ v) ∧
    (extReal (Dom n b.base R s) φ → ∀ z : ER n k, extCx z ∈ U →
      extCx (extRe (Φ (extCx z))) = Φ (extCx z)) := by
  intro Φ Ψ U
  obtain ⟨c1, c2, c3, c4, c6, c7, c8, c9, c10⟩ :=
    canonical_map_core b hk hρ hρR hσ hσs hSL hV hsmall hφ hb
  have hR : 0 < R := by linarith
  have hs : 0 < s := by linarith
  obtain ⟨W, hW⟩ : ∃ W : EC n k ≃L[ℂ] EC n k, ∀ z, ‖W z‖ = scaled ρ σ z :=
    ⟨extGauge ρ σ hρ hσ, norm_extGauge hρ hσ⟩
  have hvf := vf b hk hρ (by linarith) hσ (by linarith) hSL hV hφ hb
  have hF : KAM.Canonical.SmallField W (Dom n b.base (R-ρ) (s-σ)) (wfield b.c φ)
      (V / (ρ * σ)) :=
    { isOpen := isOpen_Dom _ _ _
      differentiableOn := differentiableOn_wfield b.c (isOpen_Dom _ _ _)
        (hφ.differentiableOn.mono (Dom_mono (by linarith) (by linarith)))
      eps_nonneg := div_nonneg hV (mul_pos hρ hσ).le
      eps_le := hsmall
      bound := fun z hz => by rw [hW]; exact (hvf z hz).1 }
  have hgh : U ⊆ KAM.Canonical.gaugeInterior W (Dom n b.base (R-ρ) (s-σ)) (1/2) := by
    intro z hz w hw
    rw [hW] at hw
    have := dom_of_scaled_le hρ hσ (by norm_num : (0:ℝ) < 1/2) (by linarith) (by linarith) hz hw
    exact Dom_mono (by linarith) (by linarith) this
  have hcan := symplectic (isOpen_Dom (n := n) b.base (R-ρ) (s-σ)) hc φ
    (hφ.differentiableOn.mono (Dom_mono (by linarith) (by linarith))) W hF (t := 1) (by simp)
  exact ⟨c1, c2, c3, c4, fun z hz u v => hcan z (hgh hz) u v, c6, c7, c8, c9, c10⟩

end KAM.Nekhoroshev

end
