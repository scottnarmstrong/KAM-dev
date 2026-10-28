/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.FlowInverse
public import KAM.Canonical.Symplectic
public import KAM.Canonical.VectorField
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The canonical map `Φ = X¹_φ` on weighted domains (`bpN:p5:canonical-map`)

Blueprint-N Part 5, node `bpN:p5:canonical-map` (design
`docs/tracks/N/design/PART145-LEAN-DESIGN.md`, package C5-10).

* `KAM.Canonical.CanonData`: the source premises `0 < ρ < r/2`, `0 < σ < s/2`, `φ ∈ O(r,s)` of
  finite norm `Φ`, `Φ/(ρσ) ≤ 1/2`; `.omega` is `Ω = 𝒟_{r-ρ,s-σ}` and `.gauge` the gauge `ν_{ρ,σ}`;
* `KAM.Canonical.canonical_map_a`: field bound, definedness on `𝒟_{r-3ρ/2,s-3σ/2}`, displacement
  and the explicit component bounds (mean value along the trajectory, with `vf_bound`);
* `canonical_map_b`: integer angle translations (`flow_d`) and reality (`flow_e`);
* `canonical_map_c`: the derivative bound (`flow_c`); `canonical_map_d`: symplecticity
  (`symplectic`); `canonical_map_e`: two-sided inverse (`flow_c`).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Canonical

open KAM.Weighted

variable {n : ℕ}

/-- Source premises of `bpN:p5:canonical-map`: `0 < ρ < r/2`, `0 < σ < s/2`, `φ ∈ Os r s` of finite
norm `Φ`, `ε = Φ/(ρσ) ≤ 1/2`. -/
structure CanonData (D : Set (Fin n → ℂ)) (r s ρ σ Φ : ℝ) (φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : Prop where
  hρ : 0 < ρ
  hρr : ρ < r / 2
  hσ : 0 < σ
  hσs : σ < s / 2
  φ_class : InClass D r s φ
  Φ_nonneg : 0 ≤ Φ
  φ_bound : WBound D r s φ Φ
  eps_le : Φ / (ρ * σ) ≤ 1 / 2

def CanonData.omega {D : Set (Fin n → ℂ)} {r s ρ σ Φ : ℝ} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (_ : CanonData D r s ρ σ Φ φ) : Set ((Fin n → ℂ) × (Fin n → ℂ)) := Dom n D (r - ρ) (s - σ)

def CanonData.gauge {D : Set (Fin n → ℂ)} {r s ρ σ Φ : ℝ} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hd : CanonData D r s ρ σ Φ φ) :
    ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ)) := scaleCLE ρ σ hd.hρ hd.hσ

/-! ### Helper lemmas -/

/-- A point at scaled distance `≤ c` from `𝒟_{r₀, s₀}` lies in `𝒟_{r₀ + ρ c, s₀ + σ c}`. -/
private theorem dom_of_scaledNorm_le {D : Set (Fin n → ℂ)} {ρ σ c r₀ s₀ : ℝ} (hρ : 0 < ρ)
    (hσ : 0 < σ) (hc : 0 < c) (hr₀ : 0 < r₀) (hs₀ : 0 < s₀) {z w : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ Dom n D r₀ s₀) (hw : scaledNorm ρ σ (w - z) ≤ c) :
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

/-- Real translations of the angles preserve `𝒟_{r,s}`. -/
private theorem dom_shift {D : Set (Fin n → ℂ)} {r s : ℝ} {a : Fin n → ℂ} (ha : ∀ i, (a i).im = 0)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ Dom n D r s) : (z.1 + a, z.2) ∈ Dom n D r s :=
  ⟨fun i => by simpa [ha i] using hz.1 i, hz.2⟩

private theorem prod_add_mk {w : (Fin n → ℂ) × (Fin n → ℂ)} (a : Fin n → ℂ) :
    w + (a, 0) = (w.1 + a, w.2) := Prod.ext rfl (add_zero _)

/-- Periodicity of a function of class `Os r s` under all integer translations of the angles. -/
private theorem periodic_int {D : Set (Fin n → ℂ)} {r s : ℝ} {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hu : InClass D r s u) (k : Fin n → ℤ) {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ Dom n D r s) : u (z.1 + (fun i => (k i : ℂ)), z.2) = u z := by
  let G : AddSubgroup (Fin n → ℝ) :=
    { carrier := {a | ∀ z ∈ Dom n D r s, u (z.1 + (fun i => (a i : ℂ)), z.2) = u z}
      zero_mem' := fun z _ => by
        have : (z.1 + fun i => (((0 : Fin n → ℝ) i : ℝ) : ℂ)) = z.1 := by ext; simp
        rw [this]
      add_mem' := by
        intro a b ha hb z hz
        have h1 := hb _ (dom_shift (a := fun i => (a i : ℂ)) (fun i => by simp) hz)
        have h2 := ha z hz
        have e : (fun i => (((a + b) i : ℝ) : ℂ)) =
            (fun i => (a i : ℂ)) + (fun i => (b i : ℂ)) := by ext; simp
        rw [e, ← add_assoc]
        exact h1.trans h2
      neg_mem' := by
        intro a ha z hz
        have hw : (z.1 + (fun i => ((-a) i : ℂ)), z.2) ∈ Dom n D r s :=
          dom_shift (fun i => by simp) hz
        have := ha _ hw
        simp only [Pi.neg_apply, Complex.ofReal_neg] at this ⊢
        rw [← this]
        congr 2
        ext i
        simp }
  have hj : ∀ j : Fin n, Pi.single j (1 : ℝ) ∈ G := fun j z hz => by
    have := hu.periodic j z hz
    rw [← this]
    congr 2
    ext i
    by_cases h : i = j <;> simp [Pi.single_apply, h]
  have hk : (fun i => (k i : ℝ)) ∈ G := by
    have : (fun i => (k i : ℝ)) = ∑ j, k j • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact G.sum_mem fun j _ => G.zsmul_mem (hj j) _
  simpa using hk z hz

/-- The field of a periodic function is invariant under integer angle translations. -/
private theorem field_periodic {D : Set (Fin n → ℂ)} {r s r₀ s₀ : ℝ}
    {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hφ : InClass D r s φ) (hr : r₀ ≤ r) (hs : s₀ ≤ s)
    (k : Fin n → ℤ) {w : (Fin n → ℂ) × (Fin n → ℂ)} (hw : w ∈ Dom n D r₀ s₀) :
    KAM.hamiltonianVectorFieldℂ φ (w + ((fun i => (k i : ℂ)), 0)) =
      KAM.hamiltonianVectorFieldℂ φ w := by
  have hev : (fun x => φ (x + ((fun i => (k i : ℂ)), 0))) =ᶠ[nhds w] φ := by
    filter_upwards [(isOpen_Dom (n := n) D r₀ s₀).mem_nhds hw] with x hx
    have := periodic_int hφ k (Dom_mono hr hs hx)
    rw [← this, prod_add_mk]
  have hf : fderiv ℂ φ (w + ((fun i => (k i : ℂ)), 0)) = fderiv ℂ φ w := by
    rw [← fderiv_comp_add_right, hev.fderiv_eq]
  simp only [KAM.hamiltonianVectorFieldℂ, hf]

/-- Mean value along a trajectory: a component of the field bounded by `C` along the trajectory
moves by at most `C |t|`. -/
private theorem component_mvt {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℝ] G)
    {X : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {Ω : Set ((Fin n → ℂ) × (Fin n → ℂ))} {γ : ℝ → (Fin n → ℂ) × (Fin n → ℂ)}
    (hsol : KAM.ODE.IsSolutionIn X Ω (Icc (-1) 1) γ) {C : ℝ}
    (hC : ∀ t ∈ Icc (-1 : ℝ) 1, ‖L (X (γ t))‖ ≤ C) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖L (γ t) - L (γ 0)‖ ≤ C * |t| := by
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => L (γ t)) (f' := fun t => L (X (γ t))) (C := C)
    (fun x hx => (L.hasFDerivAt.comp_hasDerivAt x (hsol x hx).2).hasDerivWithinAt) hC h0 ht
  simpa using this

namespace CanonData

variable {D : Set (Fin n → ℂ)} {r s ρ σ Φ : ℝ} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

theorem norm_gauge (hd : CanonData D r s ρ σ Φ φ) (x : (Fin n → ℂ) × (Fin n → ℂ)) :
    ‖hd.gauge x‖ = scaledNorm ρ σ x := norm_scaleCLE hd.hρ hd.hσ x

theorem phi_div_nonneg (hd : CanonData D r s ρ σ Φ φ) : 0 ≤ Φ / (ρ * σ) :=
  div_nonneg hd.Φ_nonneg (mul_pos hd.hρ hd.hσ).le

theorem omega_subset (hd : CanonData D r s ρ σ Φ φ) : hd.omega ⊆ Dom n D r s :=
  Dom_mono (by linarith [hd.hρ]) (by linarith [hd.hσ])

/-- `vf_bound` on `Ω = 𝒟_{r-ρ,s-σ}`. -/
theorem field_bound (hd : CanonData D r s ρ σ Φ φ) :
    ∀ z ∈ hd.omega, (∀ i, ‖dI i φ z‖ ≤ Φ / ρ) ∧
      (∀ i, ‖dtheta i φ z‖ ≤ Φ / (Real.exp 1 * σ)) ∧
      scaledNorm ρ σ (KAM.hamiltonianVectorFieldℂ φ z) ≤ Φ / (ρ * σ) := fun z hz =>
  vf_bound hd.φ_class hd.φ_bound hd.hρ (by linarith [hd.hρ, hd.hρr]) hd.hσ
    (by linarith [hd.hσ, hd.hσs]) z hz

/-- The two components of the field on `Ω`. -/
theorem field_comp_bound (hd : CanonData D r s ρ σ Φ φ) {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ hd.omega) :
    ‖(KAM.hamiltonianVectorFieldℂ φ z).1‖ ≤ Φ / ρ ∧
      ‖(KAM.hamiltonianVectorFieldℂ φ z).2‖ ≤ Φ / (Real.exp 1 * σ) := by
  obtain ⟨hI, hθ, -⟩ := hd.field_bound z hz
  have hρ := hd.hρ
  have hσ := hd.hσ
  refine ⟨(pi_norm_le_iff_of_nonneg (div_nonneg hd.Φ_nonneg hρ.le)).2 hI,
    (pi_norm_le_iff_of_nonneg (div_nonneg hd.Φ_nonneg (by positivity))).2 fun i => ?_⟩
  simpa [KAM.hamiltonianVectorFieldℂ, dtheta] using hθ i

theorem smallField (hd : CanonData D r s ρ σ Φ φ) :
    SmallField hd.gauge hd.omega (KAM.hamiltonianVectorFieldℂ φ) (Φ / (ρ * σ)) where
  isOpen := isOpen_Dom _ _ _
  differentiableOn := differentiableOn_hamField (isOpen_Dom _ _ _)
    (hd.φ_class.differentiableOn.mono hd.omega_subset)
  eps_nonneg := hd.phi_div_nonneg
  eps_le := hd.eps_le
  bound z hz := by
    rw [hd.norm_gauge]
    exact (hd.field_bound z hz).2.2

theorem gaugeInterior_half (hd : CanonData D r s ρ σ Φ φ) :
    Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2) ⊆ gaugeInterior hd.gauge hd.omega (1 / 2) := by
  intro z hz w hw
  rw [hd.norm_gauge] at hw
  have := dom_of_scaledNorm_le hd.hρ hd.hσ (by norm_num : (0 : ℝ) < 1 / 2)
    (by linarith [hd.hρr, hd.hρ]) (by linarith [hd.hσs, hd.hσ]) hz hw
  exact Dom_mono (by linarith) (by linarith) this

theorem gaugeInterior_one (hd : CanonData D r s ρ σ Φ φ) :
    Dom n D (r - 2 * ρ) (s - 2 * σ) ⊆ gaugeInterior hd.gauge hd.omega 1 := by
  intro z hz w hw
  rw [hd.norm_gauge] at hw
  have := dom_of_scaledNorm_le hd.hρ hd.hσ (by norm_num : (0 : ℝ) < 1)
    (by linarith [hd.hρr, hd.hρ]) (by linarith [hd.hσs, hd.hσ]) hz hw
  exact Dom_mono (by linarith) (by linarith) this

end CanonData

/-! ### The statements -/

/-- (a) field bound, definedness on `𝒟_{r-3ρ/2, s-3σ/2}`, displacement, explicit components (`t = ±1`). -/
theorem canonical_map_a {D : Set (Fin n → ℂ)} {r s ρ σ Φ : ℝ} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hd : CanonData D r s ρ σ Φ φ) :
    (∀ z ∈ hd.omega, scaledNorm ρ σ (KAM.hamiltonianVectorFieldℂ φ z) ≤ Φ / (ρ * σ)) ∧
    SmallField hd.gauge hd.omega (KAM.hamiltonianVectorFieldℂ φ) (Φ / (ρ * σ)) ∧
    Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2) ⊆ gaugeInterior hd.gauge hd.omega (1 / 2) ∧
    (∀ t ∈ Icc (-1 : ℝ) 1, DifferentiableOn ℂ (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t)
      (Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2))) ∧
    (∀ z ∈ Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2), ∀ t ∈ Icc (-1 : ℝ) 1,
      flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z ∈ hd.omega ∧
      scaledNorm ρ σ (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z - z) ≤ |t| * (Φ / (ρ * σ))) ∧
    (∀ z ∈ Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2),
      ‖(flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z).1 - z.1‖ ≤ Φ / ρ ∧
      ‖(flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z).2 - z.2‖ ≤ Φ / (Real.exp 1 * σ) ∧
      ‖(flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega (-1) z).1 - z.1‖ ≤ Φ / ρ ∧
      ‖(flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega (-1) z).2 - z.2‖ ≤ Φ / (Real.exp 1 * σ)) := by
  have hsf := hd.smallField
  have hgi := hd.gaugeInterior_half
  refine ⟨fun z hz => (hd.field_bound z hz).2.2, hsf, hgi, fun t ht => ?_, fun z hz t ht => ?_,
    fun z hz => ?_⟩
  · exact ((flow_b hsf).2.1 t ht).mono hgi
  · refine ⟨(flow_b hsf).2.2.1 t ht z (hgi hz), ?_⟩
    have := (flow_a hsf (hgi hz)).2.2.2 t ht
    rwa [hd.norm_gauge] at this
  · obtain ⟨h0, hsol, -, -⟩ := flow_a hsf (hgi hz)
    have key : ∀ t ∈ Icc (-1 : ℝ) 1,
        ‖(flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z).1 - z.1‖ ≤ Φ / ρ * |t| ∧
        ‖(flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z).2 - z.2‖ ≤
          Φ / (Real.exp 1 * σ) * |t| := by
      intro t ht
      have h1 := component_mvt (ContinuousLinearMap.fst ℝ (Fin n → ℂ) (Fin n → ℂ)) hsol
        (C := Φ / ρ) (fun t ht => (hd.field_comp_bound (hsol t ht).1).1) ht
      have h2 := component_mvt (ContinuousLinearMap.snd ℝ (Fin n → ℂ) (Fin n → ℂ)) hsol
        (C := Φ / (Real.exp 1 * σ)) (fun t ht => (hd.field_comp_bound (hsol t ht).1).2) ht
      simp only [h0, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at h1 h2
      exact ⟨h1, h2⟩
    have hp : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
    have hm : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
    obtain ⟨a1, a2⟩ := key 1 hp
    obtain ⟨b1, b2⟩ := key (-1) hm
    simp only [abs_neg, abs_one, mul_one] at a1 a2 b1 b2
    exact ⟨a1, a2, b1, b2⟩

/-- (b) integer angle translations and reality. -/
theorem canonical_map_b {D : Set (Fin n → ℂ)} {r s ρ σ Φ : ℝ} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hd : CanonData D r s ρ σ Φ φ) :
    (∀ k : Fin n → ℤ, ∀ z ∈ Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2),
      flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 (z.1 + (fun i => (k i : ℂ)), z.2) =
        flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z + ((fun i => (k i : ℂ)), 0)) ∧
    (RealOn (Dom n D r s) φ → ∀ x : (Fin n → ℝ) × (Fin n → ℝ),
      KAM.realInclusion₂ n x ∈ Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2) →
        flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 (KAM.realInclusion₂ n x) ∈
          range (KAM.realInclusion₂ n)) := by
  have hsf := hd.smallField
  have hgi := hd.gaugeInterior_half
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  refine ⟨fun k z hz => ?_, fun hφr x hx => ?_⟩
  · have hτΩ : (fun w => w + ((fun i => (k i : ℂ)), (0 : Fin n → ℂ))) '' hd.omega = hd.omega := by
      refine Subset.antisymm ?_ ?_
      · rintro _ ⟨w, hw, rfl⟩
        beta_reduce
        rw [prod_add_mk]
        exact dom_shift (a := fun i => (k i : ℂ)) (fun i => by simp) hw
      · intro w hw
        refine ⟨(w.1 + fun i => ((-k i : ℤ) : ℂ), w.2), dom_shift (fun i => by simp) hw, ?_⟩
        beta_reduce
        rw [prod_add_mk]
        ext i <;> simp
    have hτF : ∀ w ∈ hd.omega, KAM.hamiltonianVectorFieldℂ φ
        (w + ((fun i => (k i : ℂ)), (0 : Fin n → ℂ))) = KAM.hamiltonianVectorFieldℂ φ w :=
      fun w hw => field_periodic hd.φ_class (by linarith [hd.hρ]) (by linarith [hd.hσ]) k hw
    have := (flow_d hsf hτΩ hτF).2 z (hgi hz) 1 h1
    have e : z + ((fun i => (k i : ℂ)), (0 : Fin n → ℂ)) = (z.1 + fun i => (k i : ℂ), z.2) := by
      exact prod_add_mk _
    rwa [e] at this
  · have hreal : ∀ w ∈ hd.omega, w ∈ range (KAM.realInclusion₂ n) →
        KAM.hamiltonianVectorFieldℂ φ w ∈ range (KAM.realInclusion₂ n) := by
      rintro w hw ⟨y, rfl⟩
      obtain ⟨⟨-, h2⟩, -⟩ := KAM.hamiltonian_real (isOpen_Dom (n := n) D r s)
        hd.φ_class.differentiableOn (fun y hy => hφr y hy) (z := y) (hd.omega_subset hw)
        (H := fun y' => (φ (KAM.realInclusion₂ n y')).re) (Filter.Eventually.of_forall fun _ => rfl)
      exact ⟨_, h2⟩
    exact flow_e hsf hreal _ (hgi hx) ⟨x, rfl⟩ 1 h1

/-- (c) derivative `|W(DΦ - 1)W⁻¹| ≤ 2Φ/(ρσ)` on `𝒟_{r-2ρ, s-2σ}` (every `X^t`). -/
theorem canonical_map_c {D : Set (Fin n → ℂ)} {r s ρ σ Φ : ℝ} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hd : CanonData D r s ρ σ Φ φ) :
    ∀ z ∈ Dom n D (r - 2 * ρ) (s - 2 * σ), ∀ t ∈ Icc (-1 : ℝ) 1, ∀ v,
      scaledNorm ρ σ (fderiv ℂ (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t) z v - v) ≤
        2 * (Φ / (ρ * σ)) * scaledNorm ρ σ v := by
  intro z hz t ht v
  obtain ⟨-, -, -, -, h⟩ := flow_c hd.smallField (hd.gaugeInterior_one hz)
  have := h t ht v
  rwa [hd.norm_gauge, hd.norm_gauge] at this

/-- (d) `(DΦ)ᵀ J DΦ = J` on `𝒟_{r-3ρ/2, s-3σ/2}` (the hypotheses of `canonical_*` hold there by (a)). -/
theorem canonical_map_d {D : Set (Fin n → ℂ)} {r s ρ σ Φ : ℝ} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hd : CanonData D r s ρ σ Φ φ) :
    ∀ z ∈ Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2), ∀ v w,
      symplFormC (fderiv ℂ (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1) z v)
        (fderiv ℂ (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1) z w) = symplFormC v w := by
  intro z hz v w
  exact (symplectic (hd.φ_class.differentiableOn.mono hd.omega_subset) hd.smallField
    (hd.gaugeInterior_half hz) (t := 1) ⟨by norm_num, le_rfl⟩ _ rfl).1 v w

/-- (e) `Ψ = X⁻¹` is a two-sided inverse on `𝒟_{r-2ρ, s-2σ}`. -/
theorem canonical_map_e {D : Set (Fin n → ℂ)} {r s ρ σ Φ : ℝ} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hd : CanonData D r s ρ σ Φ φ) :
    ∀ z ∈ Dom n D (r - 2 * ρ) (s - 2 * σ),
      flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega (-1) (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z) = z ∧
      flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega (-1) z) = z ∧
      flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z ∈ Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2) := by
  intro z hz
  have hsf := hd.smallField
  obtain ⟨-, h1, -, h2, -⟩ := flow_c hsf (hd.gaugeInterior_one hz)
  refine ⟨h1, h2, ?_⟩
  have hz' : z ∈ Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2) :=
    Dom_mono (by linarith [hd.hρ]) (by linarith [hd.hσ]) hz
  have hdisp := (flow_a hsf (hd.gaugeInterior_half hz')).2.2.2 1 ⟨by norm_num, le_rfl⟩
  rw [hd.norm_gauge, abs_one, one_mul] at hdisp
  have := dom_of_scaledNorm_le hd.hρ hd.hσ (by norm_num : (0 : ℝ) < 1 / 2)
    (by linarith [hd.hρr, hd.hρ]) (by linarith [hd.hσs, hd.hσ]) hz (hdisp.trans hd.eps_le)
  exact Dom_mono (by linarith) (by linarith) this

end KAM.Canonical

end
