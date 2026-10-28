/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.Direct
public import KAM.Canonical.TransformSeries
public import KAM.Canonical.Adjoint

/-!
# P Part 2: splitting of the generating function and componentwise displacement (`bpP:p2:split`)

`firstGen` is the part `φ⁽¹⁾` of `homGen K {0} h f` supported on the modes with `k₁ ≠ 0`;
`directMap` is the time-one map of `homGen K {0} h f`, i.e. the N `iterMap` with `Λ = {0}`.
`split` follows the three source steps: the coefficient bounds (`stepP:p2:sp-coef`), the
field bounds on `𝒟_{r-ρ,s-σ}` (`stepP:p2:sp-field`), and the mean value inequality along the
trajectory (`stepP:p2:sp-int`). Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-10.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

def firstGen {a b : ℕ} (K : ℝ) (h : (Fin (a + b) → ℂ) → ℂ) (f : CHam (a + b)) : CHam (a + b) :=
  projMode {k | firstBlock (b := b) k ≠ 0} (homGen K {0} h f)

def directMap {n : ℕ} (D : Set (Fin n → ℂ)) (r s ρ σ K : ℝ)
    (h : (Fin n → ℂ) → ℂ) (f : CHam n) : CPhase n → CPhase n :=
  flow (KAM.hamiltonianVectorFieldℂ (homGen K {0} h f)) (Dom n D (r - ρ) (s - σ)) 1

section Coefficients

variable {n : ℕ}

private theorem finite_zBall' (K : ℝ) : (zBall n K).Finite := by
  refine (KAM.modeCutoff n ⌈K⌉₊).finite_toSet.subset fun k hk => ?_
  have hk' : KAM.Fourier.modeSize k ≤ K := hk
  exact KAM.mem_modeCutoff.2 (hk'.trans (Nat.le_ceil K))

/-- The coefficient `1_{Z_K \ {0}}(k) f̂ₖ(I)/(2πi k·ω(I))` of `homGen K {0} h f`. -/
private def genC (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam n) (k : Fin n → ℤ) (I : Fin n → ℂ) : ℂ :=
  (zBall n K \ {0}).indicator
    (fun k => coeff f I k / (2 * (Real.pi : ℂ) * Complex.I * dotC k (freq h I))) k

private theorem homGen_eq_series (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam n) :
    homGen K {0} h f = fourierSeries (genC K h f) := by
  funext z
  unfold homGen fourierSeries genC
  refine tsum_congr fun k => ?_
  by_cases hk : k ∈ zBall n K \ {0} <;> simp [hk]

private theorem summable_genC (K s : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam n) (I : Fin n → ℂ) :
    Summable fun k => ‖genC K h f k I‖ * modeWeight s k := by
  refine summable_of_ne_finset_zero (s := (finite_zBall' (n := n) K).toFinset) fun k hk => ?_
  have : k ∉ zBall n K \ {0} := fun h' => hk (by simpa using h'.1)
  simp [genC, this]

private theorem coeff_homGen {s : ℝ} (hs : 0 < s) (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam n)
    (I : Fin n → ℂ) (k : Fin n → ℤ) : coeff (homGen K {0} h f) I k = genC K h f k I := by
  rw [homGen_eq_series]
  exact KAM.torusCoeff_fourierSum hs.le (summable_genC K s h f I) k

private theorem norm_div_divisor_le {c d : ℂ} {α q : ℝ} (hα : 0 < α) (hq : 1 ≤ q)
    (hd : α / q ≤ ‖d‖) :
    ‖c / (2 * (Real.pi : ℂ) * Complex.I * d)‖ ≤ q / (2 * Real.pi * α) * ‖c‖ := by
  have hq0 : 0 < q := by linarith
  have hd0 : 0 < ‖d‖ := lt_of_lt_of_le (div_pos hα hq0) hd
  have hn : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * d‖ = 2 * Real.pi * ‖d‖ := by
    simp [abs_of_pos Real.pi_pos]
  rw [norm_div, hn]
  have hπ := Real.pi_pos
  rw [div_le_iff₀ (by positivity)]
  have h1 : α ≤ q * ‖d‖ := by
    have := (div_le_iff₀ hq0).1 hd
    linarith
  have : q / (2 * Real.pi * α) * ‖c‖ * (2 * Real.pi * ‖d‖) = ‖c‖ * (q * ‖d‖ / α) := by
    field_simp
  rw [this]
  have h5 : 1 ≤ q * ‖d‖ / α := by rwa [le_div_iff₀ hα, one_mul]
  nlinarith [norm_nonneg c]

end Coefficients

section Derivative

variable {n : ℕ}

private theorem character_add_smul_single {k : Fin n → ℤ} {j : Fin n} (hkj : k j = 0)
    (θ : Fin n → ℂ) (t : ℂ) :
    KAM.character k (θ + t • Pi.single j 1) = KAM.character k θ := by
  rw [KAM.character_add]
  have : KAM.character k (t • (Pi.single j 1 : Fin n → ℂ)) = 1 := by
    unfold KAM.character
    rw [Finset.sum_eq_single j]
    · simp [hkj]
    · intro i _ hij
      simp [hij]
    · simp
  rw [this, mul_one]

/-- A class function whose coefficients vanish for `kⱼ ≠ 0` has `∂_{θⱼ} u = 0`. -/
private theorem dtheta_eq_zero_of_modes {D : Set (Fin n → ℂ)} {r s M : ℝ} {u : CHam n}
    (hs : 0 < s) (hu : InClass D r s u) (hb : WBound D r s u M) (j : Fin n)
    (hmodes : ∀ I ∈ polyNbhd D r, ∀ k, k j ≠ 0 → coeff u I k = 0) {z : CPhase n}
    (hz : z ∈ Dom n D r s) : dtheta j u z = 0 := by
  have hrep := (coefficients_repr hs hu hb).1
  have hopen := isOpen_Dom (n := n) D r s
  let path : ℂ → CPhase n := fun t => (z.1 + t • Pi.single j 1, z.2)
  have hpath : HasDerivAt path (Pi.single j 1, (0 : Fin n → ℂ)) 0 := by
    have h1 : HasDerivAt (fun t : ℂ => z.1 + t • (Pi.single j 1 : Fin n → ℂ)) (Pi.single j 1)
        0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single j 1 : Fin n → ℂ)).const_add z.1
    exact h1.prodMk (hasDerivAt_const _ _)
  have hp0 : path 0 = z := by simp [path]
  have hev : ∀ᶠ t in nhds (0 : ℂ), path t ∈ Dom n D r s :=
    hpath.continuousAt.eventually (hopen.mem_nhds (by rw [hp0]; exact hz))
  have hconst : ∀ᶠ t in nhds (0 : ℂ), u (path t) = u z := by
    filter_upwards [hev] with t ht
    have h1 := hrep _ ht
    have h2 := hrep z hz
    have : (fun k => KAM.character k (path t).1 • coeff u (path t).2 k) =
        fun k => KAM.character k z.1 • coeff u z.2 k := by
      funext k
      by_cases hkj : k j = 0
      · simp only [path, character_add_smul_single hkj]
      · simp [path, hmodes z.2 hz.2 k hkj]
    rw [this] at h1
    exact h1.unique h2
  have hud : HasFDerivAt u (fderiv ℂ u z) (path 0) := by
    rw [hp0]
    exact (hu.differentiableOn.differentiableAt (hopen.mem_nhds hz)).hasFDerivAt
  have h1 : HasDerivAt (u ∘ path) (fderiv ℂ u z (Pi.single j 1, 0)) 0 :=
    hud.comp_hasDerivAt (0 : ℂ) hpath
  have h2 : HasDerivAt (u ∘ path) 0 0 :=
    (hasDerivAt_const (0 : ℂ) (u z)).congr_of_eventuallyEq
      (by filter_upwards [hconst] with t ht; simpa using ht)
  exact h1.unique h2

end Derivative

section Split

variable {a b : ℕ} {D : Set (Fin (a + b) → ℂ)} {r s K α₁ α₂ q δ : ℝ}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

/-- `stepP:p2:sp-coef`, class and weighted bound of `φ⁽¹⁾`. -/
theorem firstGen_class_bound (H : DirectHyp D r s K α₂ q δ {0} h f) (hα : α₂ ≤ α₁)
    (hd : TwoDiv (polyNbhd D r) K α₁ α₂ q h) :
    InClass D r s (firstGen K h f) ∧ WBound D r s (firstGen K h f) (q * δ / (2 * π * α₁)) := by
  obtain ⟨c1, c2, -⟩ := direct H
  obtain ⟨p1, p2, p3, -⟩ :=
    projections H.s_pos c1 c2 {k : Fin (a + b) → ℤ | firstBlock (b := b) k ≠ 0}
  refine ⟨p1, fun I hI => ?_⟩
  have hα₁ : 0 < α₁ := lt_of_lt_of_le H.α_pos hα
  have hc0 : 0 ≤ q / (2 * π * α₁) := by
    have := H.q_ge
    have := Real.pi_pos
    positivity
  have hle : ∀ k, ‖coeff (firstGen K h f) I k‖ * modeWeight s k ≤
      q / (2 * π * α₁) * (‖coeff f I k‖ * modeWeight s k) := fun k => by
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    show ‖coeff (projMode _ (homGen K {0} h f)) I k‖ ≤ _
    rw [p2 I hI k]
    by_cases hk : k ∈ {k : Fin (a + b) → ℤ | firstBlock (b := b) k ≠ 0}
    · rw [Set.indicator_of_mem hk, coeff_homGen H.s_pos]
      by_cases hZ : k ∈ zBall (a + b) K \ {0}
      · simp only [genC, Set.indicator_of_mem hZ]
        have hk' : ¬ firstBlock (b := b) k = 0 := hk
        have hk0 : k ≠ 0 := fun h0 => hk' (by subst h0; rfl)
        have hdk := hd I hI k hk0 hZ.1
        simp only [hk', ↓reduceIte] at hdk
        exact norm_div_divisor_le hα₁ H.q_ge hdk
      · simp only [genC, Set.indicator_of_notMem hZ, norm_zero]
        exact mul_nonneg hc0 (norm_nonneg _)
    · rw [Set.indicator_of_notMem hk, norm_zero]
      exact mul_nonneg hc0 (norm_nonneg _)
  obtain ⟨h1, h2⟩ := H.bound I hI
  have h1' : Summable fun k => q / (2 * π * α₁) * (‖coeff f I k‖ * modeWeight s k) := h1.mul_left _
  have hs' : Summable (fun k => ‖coeff (firstGen K h f) I k‖ * modeWeight s k) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hle h1'
  refine ⟨hs', (hs'.tsum_le_tsum hle h1').trans ?_⟩
  rw [tsum_mul_left]
  calc q / (2 * π * α₁) * ∑' k, ‖coeff f I k‖ * modeWeight s k
      ≤ q / (2 * π * α₁) * δ := mul_le_mul_of_nonneg_left h2 hc0
    _ = q * δ / (2 * π * α₁) := by ring

/-- `stepP:p2:sp-coef`: `φ - φ⁽¹⁾` has no coefficients with `k₁ ≠ 0`. -/
theorem split_coeff (H : DirectHyp D r s K α₂ q δ {0} h f) (hα : α₂ ≤ α₁)
    (hd : TwoDiv (polyNbhd D r) K α₁ α₂ q h) :
    ∀ I ∈ polyNbhd D r, ∀ k, firstBlock (b := b) k ≠ 0 →
      coeff (homGen K {0} h f - firstGen K h f) I k = 0 := by
  intro I hI k hk
  obtain ⟨c1, -, -⟩ := direct H
  obtain ⟨F1, -⟩ := firstGen_class_bound H hα hd
  have e : homGen K {0} h f - firstGen K h f =
      fun z => homGen K {0} h f z + (-1 : ℂ) * firstGen K h f z := by
    funext z; simp [sub_eq_add_neg]
  rw [e, coeff_add H.s_pos c1 (inClass_const_mul (-1) F1) hI k, coeff_const_mul]
  have := (projections H.s_pos c1 (direct H).2.1
    {k : Fin (a + b) → ℤ | firstBlock (b := b) k ≠ 0}).2.1 I hI k
  have h2 : coeff (firstGen K h f) I k = coeff (homGen K {0} h f) I k := by
    show coeff (projMode _ (homGen K {0} h f)) I k = _
    rw [this, Set.indicator_of_mem hk]
  rw [h2]; ring

/-- `∂_{θ_i} φ = ∂_{θ_i} φ⁽¹⁾` for `i` in the first block, since `φ - φ⁽¹⁾` has only modes
with `k₁ = 0`. -/
theorem dtheta_firstGen_eq (H : DirectHyp D r s K α₂ q δ {0} h f) (hα : α₂ ≤ α₁)
    (hd : TwoDiv (polyNbhd D r) K α₁ α₂ q h) {z : CPhase (a + b)} (hz : z ∈ Dom (a + b) D r s)
    (i : Fin a) :
    dtheta (Fin.castAdd b i) (homGen K {0} h f) z =
      dtheta (Fin.castAdd b i) (firstGen K h f) z := by
  obtain ⟨c1, c2, -⟩ := direct H
  obtain ⟨F1, F2⟩ := firstGen_class_bound H hα hd
  have hu : InClass D r s (fun z => homGen K {0} h f z + (-1 : ℂ) * firstGen K h f z) :=
    ⟨c1.differentiableOn.add (inClass_const_mul (-1) F1).differentiableOn, fun j z hz => by
      rw [c1.periodic j z hz, (inClass_const_mul (-1) F1).periodic j z hz]⟩
  have hb := wbound_add H.s_pos c1 (inClass_const_mul (-1) F1) c2 (wbound_const_mul (-1) F2)
  have hcoef := split_coeff H hα hd
  have e : homGen K {0} h f - firstGen K h f =
      fun z => homGen K {0} h f z + (-1 : ℂ) * firstGen K h f z := by
    funext z; simp [sub_eq_add_neg]
  have h0 := dtheta_eq_zero_of_modes H.s_pos hu hb (Fin.castAdd b i) (fun I hI k hk => by
    rw [← e]
    refine hcoef I hI k fun h0 => hk ?_
    simpa [firstBlock] using congrFun h0 i) hz
  have hop := isOpen_Dom (n := a + b) D r s
  have hφ := (c1.differentiableOn.differentiableAt (hop.mem_nhds hz)).hasFDerivAt
  have hφ1 := (F1.differentiableOn.differentiableAt (hop.mem_nhds hz)).hasFDerivAt
  have : fderiv ℂ (fun z => homGen K {0} h f z + (-1 : ℂ) * firstGen K h f z) z =
      fderiv ℂ (homGen K {0} h f) z + (-1 : ℂ) • fderiv ℂ (firstGen K h f) z :=
    (hφ.add (hφ1.const_mul (-1 : ℂ))).fderiv
  unfold dtheta at h0 ⊢
  rw [this] at h0
  simp only [add_apply, smul_apply, smul_eq_mul] at h0
  linear_combination h0

/-- Mean value along a trajectory: a component of the field bounded by `C` along the trajectory
moves by at most `C |t|`. -/
private theorem component_mvt {n : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : (CPhase n) →L[ℝ] G)
    {X : CPhase n → CPhase n} {Ω : Set (CPhase n)} {γ : ℝ → CPhase n}
    (hsol : KAM.ODE.IsSolutionIn X Ω (Icc (-1) 1) γ) {C : ℝ}
    (hC : ∀ t ∈ Icc (-1 : ℝ) 1, ‖L (X (γ t))‖ ≤ C) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖L (γ t) - L (γ 0)‖ ≤ C * |t| := by
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => L (γ t)) (f' := fun t => L (X (γ t))) (C := C)
    (fun x hx => (L.hasFDerivAt.comp_hasDerivAt x (hsol x hx).2).hasDerivWithinAt) hC h0 ht
  simpa using this

theorem split {a b : ℕ} {D : Set (Fin (a + b) → ℂ)} {r s K α₁ α₂ q δ ρ σ : ℝ}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}
    (H : DirectHyp D r s K α₂ q δ {0} h f)
    (hα : α₂ ≤ α₁) (hd : TwoDiv (polyNbhd D r) K α₁ α₂ q h)
    (hρ : 0 < ρ) (hρr : 2 * ρ < r) (hσ : 0 < σ) (hσs : 2 * σ < s)
    (hsmall : q * δ / (2 * π * α₂ * ρ * σ) ≤ 1 / 4) :
    WBound D r s (firstGen K h f) (q * δ / (2 * π * α₁)) ∧
    (∀ I ∈ polyNbhd D r, ∀ k, firstBlock (b := b) k ≠ 0 →
      coeff (homGen K {0} h f - firstGen K h f) I k = 0) ∧
    ∀ z ∈ Dom (a + b) D (r - 3 * ρ / 2) (s - 3 * σ / 2),
      ‖firstBlock (b := b) ((directMap D r s ρ σ K h f z).2 - z.2)‖ ≤
        q * δ / (exp 1 * (2 * π * α₁) * σ) ∧
      ‖lastBlock (a := a) ((directMap D r s ρ σ K h f z).2 - z.2)‖ ≤
        q * δ / (exp 1 * (2 * π * α₂) * σ) ∧
      ‖(directMap D r s ρ σ K h f z).1 - z.1‖ ≤ q * δ / (2 * π * α₂ * ρ) := by
  have hα₁ : 0 < α₁ := lt_of_lt_of_le H.α_pos hα
  have hα₂ := H.α_pos
  have hq := H.q_ge
  have hπ := Real.pi_pos
  have hq0 : 0 < q := by linarith
  obtain ⟨c1, c2, -⟩ := direct H
  obtain ⟨F1, F2⟩ := firstGen_class_bound H hα hd
  have hΦ0 : 0 ≤ q * δ / (2 * π * α₂) := by
    have := H.δ_nonneg
    positivity
  have hcan : CanonData D r s ρ σ (q * δ / (2 * π * α₂)) (homGen K {0} h f) := by
    refine ⟨hρ, by linarith, hσ, by linarith, c1, hΦ0, c2, ?_⟩
    have e : q * δ / (2 * π * α₂) / (ρ * σ) = q * δ / (2 * π * α₂ * ρ * σ) := by
      rw [div_div]; ring_nf
    rw [e]; linarith
  refine ⟨F2, split_coeff H hα hd, fun z hz => ?_⟩
  obtain ⟨-, -, -, -, -, h6⟩ := canonical_map_a hcan
  obtain ⟨b1, b2, -, -⟩ := h6 z hz
  have hρ' : ρ < r := by linarith
  have hσ' : σ < s := by linarith
  have hC1 : 0 ≤ q * δ / (exp 1 * (2 * π * α₂) * σ) := by
    have := H.δ_nonneg
    positivity
  refine ⟨?_, ?_, ?_⟩
  · -- first block of the action displacement: mean value along the trajectory
    obtain ⟨h0, hsol, -, -⟩ := flow_a hcan.smallField (hcan.gaugeInterior_half hz)
    let L : CPhase (a + b) →L[ℝ] (Fin a → ℂ) :=
      ContinuousLinearMap.pi fun i => (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (a + b) => ℂ) (Fin.castAdd b i)).comp
          (ContinuousLinearMap.snd ℝ (Fin (a + b) → ℂ) (Fin (a + b) → ℂ))
    have hL : ∀ w : CPhase (a + b), L w = firstBlock (b := b) w.2 := fun w => rfl
    have hC1' : 0 ≤ q * δ / (exp 1 * (2 * π * α₁) * σ) := by
      have := H.δ_nonneg
      positivity
    have key := component_mvt L hsol (C := q * δ / (exp 1 * (2 * π * α₁) * σ))
      (fun t ht => by
        have hw := (hsol t ht).1
        have hw' : flow (KAM.hamiltonianVectorFieldℂ (homGen K {0} h f))
            hcan.omega t z ∈ Dom (a + b) D (r - ρ) (s - σ) := hw
        refine (pi_norm_le_iff_of_nonneg hC1').2 fun i => ?_
        rw [hL]
        have hb1 := (vf_bound F1 F2 hρ hρ' hσ hσ' _ hw').2.1 (Fin.castAdd b i)
        have h1 := dtheta_firstGen_eq H hα hd (hcan.omega_subset hw') i
        have e : q * δ / (2 * π * α₁) / (exp 1 * σ) = q * δ / (exp 1 * (2 * π * α₁) * σ) := by
          field_simp
        rw [e] at hb1
        have h2 : ‖(KAM.hamiltonianVectorFieldℂ (homGen K {0} h f)
            (flow (KAM.hamiltonianVectorFieldℂ (homGen K {0} h f))
              hcan.omega t z)).2 (Fin.castAdd b i)‖ =
            ‖dtheta (Fin.castAdd b i) (homGen K {0} h f)
              (flow (KAM.hamiltonianVectorFieldℂ (homGen K {0} h f))
                hcan.omega t z)‖ := by
          simp [KAM.hamiltonianVectorFieldℂ, dtheta]
        show ‖(KAM.hamiltonianVectorFieldℂ (homGen K {0} h f) _).2 (Fin.castAdd b i)‖ ≤ _
        rw [h2, h1]
        exact hb1) (t := 1) ⟨by norm_num, le_rfl⟩
    rw [h0, abs_one, mul_one] at key
    exact key
  · have e : q * δ / (2 * π * α₂) / (exp 1 * σ) = q * δ / (exp 1 * (2 * π * α₂) * σ) := by
      field_simp
    calc ‖lastBlock (a := a) ((directMap D r s ρ σ K h f z).2 - z.2)‖
        ≤ ‖(directMap D r s ρ σ K h f z).2 - z.2‖ :=
          (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm _ (Fin.natAdd a i)
      _ ≤ q * δ / (exp 1 * (2 * π * α₂) * σ) := by rw [← e]; exact b2
  · have e : q * δ / (2 * π * α₂) / ρ = q * δ / (2 * π * α₂ * ρ) := by
      rw [div_div]
    rw [← e]
    exact b1

end Split

end KAM.Planetary

end
