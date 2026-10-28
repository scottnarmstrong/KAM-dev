/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.AffineFlowBasic

/-!
# Affine flow: gauge interiors, displacement and periodicity (P11A-C6)

Gauge-interior inclusions `U ⊆ Ω^{1/2}`, `V ⊆ Ω^1` for `U = Dom (3s/4) (r-3σ/2)`,
`V = Dom (s/2) (r-2σ)` and `Ω = Dom s (r-σ)` in the gauge `scaleCLE (s/2) σ`; the displacement
estimates of `stepP:p11a:af-flow` along trajectories; integer-lattice periodicity of the field.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

variable {n : ℕ} {p0 : P11CVec n → ℂ} {p1 : P11CVec n → P11CVec n} {r s sigma A : ℝ}

theorem norm_affineGauge_le_iff (H : P11AffineHyp p0 p1 r s sigma A) (u : P11Phase n) (c : ℝ) :
    ‖affineGauge H u‖ ≤ c ↔ ‖u.1‖ ≤ c*sigma ∧ ‖u.2‖ ≤ c*(s/2) := by
  have hσ := H.sigma_pos
  have hs : 0 < s/2 := by linarith [H.s_pos]
  unfold affineGauge
  rw [KAM.Canonical.norm_scaleCLE, KAM.Canonical.scaledNorm, max_le_iff, div_le_iff₀ hσ,
    div_le_iff₀ hs]

theorem mem_gaugeInterior {H : P11AffineHyp p0 p1 r s sigma A} {a b c : ℝ}
    (ha : a + c*(s/2) ≤ s) (hb : b + c*sigma ≤ r - sigma) {z : P11Phase n}
    (hz : z ∈ KAM.Weighted.Dom n {0} a b) :
    z ∈ KAM.Canonical.gaugeInterior (affineGauge H) (KAM.Weighted.Dom n {0} s (r-sigma)) c := by
  intro w hw
  rw [norm_affineGauge_le_iff] at hw
  rw [mem_Dom_iff] at hz ⊢
  obtain ⟨hw1, hw2⟩ := hw
  simp only [Prod.fst_sub, Prod.snd_sub] at hw1 hw2
  refine ⟨fun i => ?_, ?_⟩
  · have h1 : |(w.1 i).im| ≤ |(z.1 i).im| + ‖w.1 - z.1‖ := by
      calc |(w.1 i).im| = |(z.1 i).im + ((w.1 i) - (z.1 i)).im| := by simp
        _ ≤ |(z.1 i).im| + |((w.1 i) - (z.1 i)).im| := abs_add_le _ _
        _ ≤ |(z.1 i).im| + ‖w.1 - z.1‖ := by
          gcongr
          exact (Complex.abs_im_le_norm _).trans (norm_le_pi_norm (w.1 - z.1) i)
    linarith [hz.1 i]
  · have : ‖w.2‖ ≤ ‖z.2‖ + ‖w.2 - z.2‖ := by
      calc ‖w.2‖ = ‖z.2 + (w.2 - z.2)‖ := by simp
        _ ≤ _ := norm_add_le _ _
    linarith [hz.2]

/-! ### Periodicity -/

section Periodic

variable {W : Type*}

theorem complexStrip_add_int (ρ : ℝ) (k : Fin n → ℤ) {x : P11CVec n}
    (hx : x ∈ KAM.complexStrip n ρ) : x + (fun i => (k i : ℂ)) ∈ KAM.complexStrip n ρ := by
  intro i
  simpa using hx i

theorem periodic_single_int {f : P11CVec n → W} {ρ : ℝ}
    (hper : ∀ j : Fin n, ∀ x ∈ KAM.complexStrip n ρ, f (x + Pi.single j 1) = f x)
    (j : Fin n) {x : P11CVec n} (hx : x ∈ KAM.complexStrip n ρ) (m : ℤ) :
    f (x + (m : ℂ) • Pi.single j 1) = f x := by
  have hmem : ∀ m : ℤ, x + (m : ℂ) • Pi.single j 1 ∈ KAM.complexStrip n ρ := by
    intro m i
    have : ((Pi.single j (1:ℂ) : P11CVec n) i).im = 0 := by
      by_cases h : i = j <;> simp [h]
    simpa [this] using hx i
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
    have := hper j _ (hmem m)
    rw [← ih, ← this]
    congr 1
    push_cast
    module
  | pred m ih =>
    have := hper j (x + ((-(m : ℤ) - 1 : ℤ) : ℂ) • Pi.single j 1) (hmem _)
    rw [← ih, ← this]
    congr 1
    push_cast
    module

theorem periodic_int {f : P11CVec n → W} {ρ : ℝ}
    (hper : ∀ j : Fin n, ∀ x ∈ KAM.complexStrip n ρ, f (x + Pi.single j 1) = f x)
    (k : Fin n → ℤ) {x : P11CVec n} (hx : x ∈ KAM.complexStrip n ρ) :
    f (x + (fun i => (k i : ℂ))) = f x := by
  have key : ∀ S : Finset (Fin n), f (x + (fun i => if i ∈ S then (k i : ℂ) else 0)) = f x := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, ite_false]
      rw [show (fun _ : Fin n => (0:ℂ)) = 0 from rfl, add_zero]
    | insert j S hj ih =>
      have hmem : x + (fun i => if i ∈ S then (k i : ℂ) else 0) ∈ KAM.complexStrip n ρ := by
        intro i
        have : ((if i ∈ S then (k i : ℂ) else 0)).im = 0 := by split_ifs <;> simp
        simpa [this] using hx i
      have := periodic_single_int hper j hmem (k j)
      rw [← ih, ← this]
      congr 1
      funext i
      by_cases hij : i = j
      · subst hij; simp [hj]
      · simp [hij]
  simpa using key Finset.univ

variable [NormedAddCommGroup W] [NormedSpace ℂ W] in
theorem fderiv_periodic_int {f : P11CVec n → W} {ρ : ℝ}
    (hper : ∀ j : Fin n, ∀ x ∈ KAM.complexStrip n ρ, f (x + Pi.single j 1) = f x)
    (k : Fin n → ℤ) {x : P11CVec n} (hx : x ∈ KAM.complexStrip n ρ) :
    fderiv ℂ f (x + (fun i => (k i : ℂ))) = fderiv ℂ f x := by
  have hev : (fun y => f (y + (fun i => (k i : ℂ)))) =ᶠ[nhds x] f := by
    filter_upwards [(KAM.isOpen_complexStrip n ρ).mem_nhds hx] with y hy
    exact periodic_int hper k hy
  rw [← fderiv_comp_add_right, hev.fderiv_eq]

end Periodic

theorem strip_sub_sigma_subset (H : P11AffineHyp p0 p1 r s sigma A) :
    KAM.complexStrip n (r-sigma) ⊆ KAM.complexStrip n r := fun θ hθ i =>
  (hθ i).trans (by linarith [H.sigma_pos])

/-- The field is invariant under the integer translations `(k, 0)`. -/
theorem field_add_int (H : P11AffineHyp p0 p1 r s sigma A) (k : Fin n → ℤ) {w : P11Phase n}
    (hw : w ∈ KAM.Weighted.Dom n {0} s (r-sigma)) :
    KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1) (w + ((fun i => (k i : ℂ)), 0)) =
      KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1) w := by
  rw [mem_Dom_iff] at hw
  have h1 := strip_sub_sigma_subset H hw.1
  have h2 := complexStrip_add_int r k h1
  have e1 : (w + ((fun i => (k i : ℂ)), 0)).1 = w.1 + fun i => (k i : ℂ) := rfl
  have e2 : (w + ((fun i => (k i : ℂ)), 0)).2 = w.2 := by simp
  refine Prod.ext ?_ ?_
  · rw [field_fst H (by rw [e1]; exact h2), field_fst H h1, e1]
    exact periodic_int H.per1 k h1
  · funext i
    rw [field_snd H (by rw [e1]; exact h2), field_snd H h1, e1, e2,
      fderiv_periodic_int H.per0 k h1, fderiv_periodic_int H.per1 k h1]

theorem image_add_int_Dom (k : Fin n → ℤ) (a b : ℝ) :
    (fun w : P11Phase n => w + ((fun i => (k i : ℂ)), 0)) '' KAM.Weighted.Dom n {0} a b =
      KAM.Weighted.Dom n {0} a b := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_Dom_iff] at hu ⊢
    exact ⟨complexStrip_add_int b k hu.1, by simpa using hu.2⟩
  · intro hw
    refine ⟨w - ((fun i => (k i : ℂ)), 0), ?_, by simp⟩
    rw [mem_Dom_iff] at hw ⊢
    refine ⟨?_, by simpa using hw.2⟩
    have := complexStrip_add_int b (-k) hw.1
    have e : w.1 - (fun i => (k i : ℂ)) = w.1 + fun i => (((-k) i : ℤ) : ℂ) := by
      funext i; simp [sub_eq_add_neg]
    simpa [e] using this

theorem U_sub_half (H : P11AffineHyp p0 p1 r s sigma A) :
    KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2) ⊆
      KAM.Canonical.gaugeInterior (affineGauge H) (KAM.Weighted.Dom n {0} s (r-sigma)) (1/2) :=
  fun _ hz => mem_gaugeInterior (by linarith [H.s_pos]) (by linarith [H.sigma_pos]) hz

theorem V_sub_one (H : P11AffineHyp p0 p1 r s sigma A) :
    KAM.Weighted.Dom n {0} (s/2) (r-2*sigma) ⊆
      KAM.Canonical.gaugeInterior (affineGauge H) (KAM.Weighted.Dom n {0} s (r-sigma)) 1 :=
  fun _ hz => mem_gaugeInterior (by linarith [H.s_pos]) (by linarith [H.sigma_pos]) hz

theorem V_sub_U (H : P11AffineHyp p0 p1 r s sigma A) :
    KAM.Weighted.Dom (m := n) n {0} (s/2) (r-2*sigma) ⊆
      KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2) := by
  intro z hz
  rw [mem_Dom_iff] at hz ⊢
  exact ⟨fun i => (hz.1 i).trans (by linarith [H.sigma_pos]), by linarith [hz.2, H.s_pos]⟩

end KAM.Planetary

end
