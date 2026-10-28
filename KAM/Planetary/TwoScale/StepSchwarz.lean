/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.RealRestriction

/-!
# Two-scale KAM step: Schwarz reflection on a real-centred polydisc

A holomorphic map on a polydisc centred at a real point which is real at the real points of the
polydisc commutes with complex conjugation (`schwarz_vec`). Proof: the one-variable identity
theorem applied coordinate by coordinate (the pattern of `KAM.strip_identity`). Used for the
reality of `ĩ₊` in the step (`stepP:p3:st-ihat`), design package P23-14.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology

namespace KAM.Planetary

variable {n : ℕ}

private theorem differentiable_update' (θ : Fin n → ℂ) (j : Fin n) :
    Differentiable ℂ (fun ζ : ℂ => Function.update θ j ζ) := by
  rw [differentiable_pi]
  intro i
  by_cases h : i = j
  · subst h
    simp
  · simp [Function.update_of_ne h]

theorem hasDerivAt_conj_conj {u : ℂ → ℂ} {z d : ℂ} (hu : HasDerivAt u d (starRingEnd ℂ z)) :
    HasDerivAt (fun ζ => starRingEnd ℂ (u (starRingEnd ℂ ζ))) (starRingEnd ℂ d) z := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at hu ⊢
  have hc : Tendsto (starRingEnd ℂ) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (Complex.continuous_conj.tendsto 0).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun t ht => by simpa using ht
  have h2 := (Complex.continuous_conj.tendsto d).comp (hu.comp hc)
  refine h2.congr fun t => ?_
  simp [map_add, map_sub, map_mul, map_inv₀]

theorem differentiableAt_conj_conj {u : ℂ → ℂ} {z : ℂ} (hu : DifferentiableAt ℂ u (starRingEnd ℂ z)) :
    DifferentiableAt ℂ (fun ζ => starRingEnd ℂ (u (starRingEnd ℂ ζ))) z :=
  (hasDerivAt_conj_conj hu.hasDerivAt).differentiableAt

private theorem update_mem_ball {c : Fin n → ℝ} {r : ℝ} (hr : 0 < r) {θ : Fin n → ℂ}
    (hθ : θ ∈ ball (KAM.realInclusion n c) r) (j : Fin n) {ζ : ℂ} (hζ : ζ ∈ ball ((c j : ℝ) : ℂ) r) :
    Function.update θ j ζ ∈ ball (KAM.realInclusion n c) r := by
  rw [mem_ball, dist_eq_norm, pi_norm_lt_iff hr]
  intro i
  by_cases h : i = j
  · subst h
    simpa [dist_eq_norm] using hζ
  · have := (pi_norm_lt_iff hr).1 (by simpa [mem_ball, dist_eq_norm] using hθ) i
    simpa [Function.update_of_ne h] using this

/-- Identity theorem on a real-centred polydisc, for functions that are holomorphic in each
single coordinate. -/
theorem polydisc_identity {c : Fin n → ℝ} {r : ℝ} (hr : 0 < r) {w : (Fin n → ℂ) → ℂ}
    (hw : ∀ θ ∈ ball (KAM.realInclusion n c) r, ∀ j : Fin n,
      DifferentiableOn ℂ (fun ζ : ℂ => w (Function.update θ j ζ)) (ball ((c j : ℝ) : ℂ) r))
    (h0 : ∀ x : Fin n → ℝ, KAM.realInclusion n x ∈ ball (KAM.realInclusion n c) r →
      w (KAM.realInclusion n x) = 0) :
    ∀ θ ∈ ball (KAM.realInclusion n c) r, w θ = 0 := by
  have hclaim : ∀ m : ℕ, ∀ θ ∈ ball (KAM.realInclusion n c) r,
      (∀ i : Fin n, m ≤ i.val → (θ i).im = 0) → w θ = 0 := by
    intro m
    induction m with
    | zero =>
      intro θ hθ him
      have : θ = KAM.realInclusion n (fun i => (θ i).re) := by
        ext i
        exact Complex.ext (by simp) (by simpa using him i (Nat.zero_le _))
      rw [this] at hθ ⊢
      exact h0 _ hθ
    | succ m ih =>
      intro θ hθ him
      by_cases hm : m < n
      · set j : Fin n := ⟨m, hm⟩ with hj
        set φ : ℂ → ℂ := fun ζ => w (Function.update θ j ζ) with hφ
        have hφd := hw θ hθ j
        have hφan : AnalyticOnNhd ℂ φ (ball ((c j : ℝ) : ℂ) r) := hφd.analyticOnNhd isOpen_ball
        have hcen : ((c j : ℝ) : ℂ) ∈ ball ((c j : ℝ) : ℂ) r := mem_ball_self hr
        have hreal : ∀ x : ℝ, (x : ℂ) ∈ ball ((c j : ℝ) : ℂ) r → φ (x : ℂ) = 0 := by
          intro x hx
          apply ih _ (update_mem_ball hr hθ j hx)
          intro i hi
          by_cases hij : i = j
          · subst hij; simp
          · have : m + 1 ≤ i.val := by
              have : i.val ≠ m := fun h => hij (Fin.ext h)
              omega
            simpa [Function.update_of_ne hij] using him i this
        have hlim : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (c j)) (𝓝[≠] ((c j : ℝ) : ℂ)) := by
          refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            ((Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds)
            (eventually_nhdsWithin_of_forall fun x hx => ?_)
          simpa using hx
        have hev : ∀ᶠ x : ℝ in 𝓝[≠] (c j), φ (x : ℂ) = 0 := by
          have : ∀ᶠ x : ℝ in 𝓝 (c j), (x : ℂ) ∈ ball ((c j : ℝ) : ℂ) r :=
            Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hcen)
          exact (this.filter_mono nhdsWithin_le_nhds).mono fun x hx => hreal x hx
        have hfreq : ∃ᶠ z in 𝓝[≠] ((c j : ℝ) : ℂ), φ z = 0 := hlim.frequently hev.frequently
        have hzero := hφan.eqOn_zero_of_preconnected_of_frequently_eq_zero
          (convex_ball _ _).isPreconnected hcen hfreq
        have hθj : θ j ∈ ball ((c j : ℝ) : ℂ) r := by
          have := (pi_norm_lt_iff hr).1 (by simpa [mem_ball, dist_eq_norm] using hθ) j
          simpa [mem_ball, dist_eq_norm] using this
        have := hzero hθj
        simpa [hφ] using this
      · apply ih θ hθ
        intro i _
        exact absurd i.isLt (by omega)
  intro θ hθ
  exact hclaim n θ hθ fun i hi => absurd i.isLt (by omega)

/-- Schwarz reflection (scalar). -/
theorem schwarz_scalar {c : Fin n → ℝ} {r : ℝ} (hr : 0 < r) {u : (Fin n → ℂ) → ℂ}
    (hu : DifferentiableOn ℂ u (ball (KAM.realInclusion n c) r))
    (hreal : ∀ x : Fin n → ℝ, KAM.realInclusion n x ∈ ball (KAM.realInclusion n c) r →
      (u (KAM.realInclusion n x)).im = 0) :
    ∀ z ∈ ball (KAM.realInclusion n c) r,
      u (fun i => starRingEnd ℂ (z i)) = starRingEnd ℂ (u z) := by
  have hsym : ∀ θ ∈ ball (KAM.realInclusion n c) r,
      (fun i => starRingEnd ℂ (θ i)) ∈ ball (KAM.realInclusion n c) r := by
    intro θ hθ
    rw [mem_ball, dist_eq_norm, pi_norm_lt_iff hr] at hθ ⊢
    intro i
    have := hθ i
    simp only [Pi.sub_apply] at this ⊢
    have e : (fun i => starRingEnd ℂ (θ i)) i - KAM.realInclusion n c i =
        starRingEnd ℂ (θ i - KAM.realInclusion n c i) := by simp
    rw [e, Complex.norm_conj]
    exact this
  have key := polydisc_identity (c := c) (r := r) hr
    (w := fun z => starRingEnd ℂ (u (fun i => starRingEnd ℂ (z i))) - u z) ?_ ?_
  · intro z hz
    have h1 := sub_eq_zero.1 (key z hz)
    rw [← h1]; simp
  · intro θ hθ j
    have hθ' := hsym θ hθ
    set B : ℂ → ℂ := fun ζ' => u (Function.update (fun i => starRingEnd ℂ (θ i)) j ζ') with hB
    have hBd : DifferentiableOn ℂ B (ball ((c j : ℝ) : ℂ) r) :=
      hu.comp (differentiable_update' _ j).differentiableOn fun ζ hζ => update_mem_ball hr hθ' j hζ
    have hA : DifferentiableOn ℂ (fun ζ : ℂ => starRingEnd ℂ (B (starRingEnd ℂ ζ)))
        (ball ((c j : ℝ) : ℂ) r) := by
      intro ζ hζ
      have hζ' : starRingEnd ℂ ζ ∈ ball ((c j : ℝ) : ℂ) r := by
        rw [mem_ball, dist_eq_norm] at hζ ⊢
        have e : starRingEnd ℂ ζ - ((c j : ℝ) : ℂ) = starRingEnd ℂ (ζ - ((c j : ℝ) : ℂ)) := by simp
        rw [e, Complex.norm_conj]; exact hζ
      exact (differentiableAt_conj_conj
        ((hBd _ hζ').differentiableAt (isOpen_ball.mem_nhds hζ'))).differentiableWithinAt
    have hC : DifferentiableOn ℂ (fun ζ : ℂ => u (Function.update θ j ζ))
        (ball ((c j : ℝ) : ℂ) r) :=
      hu.comp (differentiable_update' _ j).differentiableOn fun ζ hζ => update_mem_ball hr hθ j hζ
    refine (hA.congr fun ζ _ => ?_).sub hC
    simp only [hB]
    congr 3
    ext i
    by_cases h : i = j
    · subst h; simp
    · simp [Function.update_of_ne h]
  · intro x hx
    have := hreal x hx
    have e : (fun i => starRingEnd ℂ (KAM.realInclusion n x i)) = KAM.realInclusion n x := by
      ext i; simp
    simp only [e]
    rw [Complex.conj_eq_iff_im.mpr this]; ring

/-- Schwarz reflection (vector valued). -/
theorem schwarz_vec {m : ℕ} {c : Fin n → ℝ} {r : ℝ} (hr : 0 < r) {F : (Fin n → ℂ) → (Fin m → ℂ)}
    (hF : DifferentiableOn ℂ F (ball (KAM.realInclusion n c) r))
    (hreal : ∀ x : Fin n → ℝ, KAM.realInclusion n x ∈ ball (KAM.realInclusion n c) r →
      ∀ i, (F (KAM.realInclusion n x) i).im = 0) :
    ∀ z ∈ ball (KAM.realInclusion n c) r,
      F (fun i => starRingEnd ℂ (z i)) = fun i => starRingEnd ℂ (F z i) := by
  intro z hz
  funext i
  exact schwarz_scalar hr (u := fun z => F z i)
    (differentiableOn_pi.1 hF i) (fun x hx => hreal x hx i) z hz

end KAM.Planetary

end
