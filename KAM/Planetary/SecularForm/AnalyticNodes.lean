/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Analytic
public import KAM.Planetary.SecularForm.ParameterIntegral

/-!
# Secular form: literal exports for the analyticity nodes

Blueprint P, Part 8, graph-gap package GAP-P8b. Unsigned exports stating the literal conclusions of
the proof steps `stepP:p8:pa-unif`, `stepP:p8:pa-hol`, `stepP:p8:pa-avg` and of the proposition
`bpP:p8:perturbation-analytic` (bundle `perturbation_analytic_full`), built from the landed
`AnalyticGeometry`, `AnalyticRegularity`, `AnalyticReal`, `Analytic` and `ParameterIntegral`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm
variable {n : ℕ}

/-- At a real point the assembled phase lies in the domain of the product chart. -/
private theorem assemble_mem_dom (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a) {x : Slow n} (hx : x ∈ realDisc D a r) (t : Vec n) :
    assemble x.2.1 t x.2.2 x.1 ∈ poincareProdDom n := by
  intro i
  have hΛ := action_pos D ha i
  have h := (poincare_holomorphic (m := D.m i) (κ := D.G * D.m0) (Λo := action D a i)
    (D.hm i) (mul_pos D.hG D.hm0) hΛ).2.2.2.2
  have hb : blockC t (inclusion x) i = phaseToC (planetBlock (assemble x.2.1 t x.2.2 x.1) i) := by
    rw [planetBlock_assemble_slow]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;>
      simp [blockC, inclusion, phaseToC]
  have hmem := blockC_mem_nbhd D ha hr (t := t) hx i
  rw [hb] at hmem
  exact (h _ hmem).1

private theorem gap_pos {a : Vec n} (ha : a ∈ axes n) {i j : Fin n} (hij : i < j) :
    0 < (a j - a i) ^ 2 / 2 := by
  have : a i < a j := ha.2 hij
  have : 0 < a j - a i := by linarith
  positivity

/-- Under the separation bound, real points of the polydisc are collision free. -/
private theorem mem_collisionFree (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a)
    (hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re)
    {x : Slow n} (hx : x ∈ realDisc D a r) (t : Vec n) :
    poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1) ∈ collisionFreeDomain n := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have hw := assemble_mem_dom D ha hr hx t
  have hreg := poincareProd_mem_regionProd D.hm hκ hw
  set z := poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1) with hz
  have hsq : ∀ i j, i < j → 0 < planeSq (bodyVector z.1 i - bodyVector z.1 j) := by
    intro i j hij
    have h := hsep t (inclusion x) hx i j hij
    rw [separationC_inclusion D ha hr hx, Complex.ofReal_re] at h
    exact lt_of_lt_of_le (gap_pos ha hij) h
  refine ⟨fun i => (hreg i).1, fun i j hij => ?_⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact Real.sqrt_pos.2 (hsq i j h)
  · have := hsq j i h
    have e : planeSq (bodyVector z.1 i - bodyVector z.1 j) =
        planeSq (bodyVector z.1 j - bodyVector z.1 i) := by
      unfold planeSq
      exact Finset.sum_congr rfl fun k _ => by simp only [Pi.sub_apply]; ring
    exact Real.sqrt_pos.2 (e ▸ this)

/-- `stepP:p8:pa-unif`: one radius `ρ* < ρ₀/2` with `Re s_ij ≥ (a_j - a_i)²/2` for all angles; at
real points `s_ij = |q_i - q_j|²`, `|q_i - q_j| ≥ (a_j - a_i)/√2`, and the position is collision
free for every angle. -/
theorem perturbation_unif (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    ∃ r : ℝ, 0 < r ∧ r < rho D a / 2 ∧
      (∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
        ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re) ∧
      ∀ x ∈ realDisc D a r, ∀ t : Vec n,
        (∀ i j, separationC D t (inclusion x) i j =
          ((planeSq (bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 i -
            bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 j) : ℝ) :
            ℂ)) ∧
        (∀ i j, i < j → (a j - a i) / √2 ≤
          planeLength (bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 i -
            bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 j)) ∧
        poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1) ∈ collisionFreeDomain n := by
  obtain ⟨r0, hr0, hrho0, hsep0⟩ := exists_radius D ha
  have hρ := rho_pos D ha
  set r := min r0 (rho D a / 4) with hrdef
  have hr : 0 < r := lt_min hr0 (by positivity)
  have hrhalf : r < rho D a / 2 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hrr : r < rho D a := by linarith
  have hsub : polydisc D a r ⊆ polydisc D a r0 := by
    rw [polydisc_eq_ball D a hr, polydisc_eq_ball D a hr0]
    exact Metric.ball_subset_ball (min_le_left _ _)
  have hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re :=
    fun t x hx i j hij => hsep0 t x (hsub hx) i j hij
  refine ⟨r, hr, hrhalf, hsep, fun x hx t => ⟨fun i j => ?_, fun i j hij => ?_, ?_⟩⟩
  · exact separationC_inclusion D ha hrr hx t i j
  · have h := hsep t (inclusion x) hx i j hij
    rw [separationC_inclusion D ha hrr hx, Complex.ofReal_re] at h
    have h2 : ((a j - a i) / √2) ^ 2 ≤ planeSq (bodyVector
        (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 i -
        bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 j) := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      exact h
    have h3 : 0 ≤ (a j - a i) / √2 := by
      have : a i < a j := ha.2 hij
      have : 0 < a j - a i := by linarith
      positivity
    exact Real.le_sqrt_of_sq_le h2
  · exact mem_collisionFree D ha hrr hsep hx t

/-- `bpP:p8:perturbation-analytic` (b), periodicity: `f̂` is `2π`-periodic in each angle. -/
theorem perturbationC_periodic (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a) (b : Bool) {x : CSlow n} (hx : x ∈ polydisc D a r) (t : Vec n)
    (i : Fin n) :
    perturbationC D b (Function.update t i (t i + 2 * π)) x = perturbationC D b t x := by
  have hp : ∀ k, planetC D (Function.update t i (t i + 2 * π)) x k = planetC D t x k := by
    intro k
    by_cases hk : k = i
    · subst hk
      have := planetC_periodic D ha hr hx k (t k)
      simpa [planetC, Function.update_self] using this
    · simp [planetC, Function.update_of_ne hk]
  unfold perturbationC separationC
  simp only [hp]

/-! ### Differentiation under the cell integral on the slow carrier -/

section CellDiff

/-- Differentiation under the cell integral when the derivative is jointly continuous. -/
private theorem hasFDerivAt_cell_integral_gen {S E : Type*} [NormedAddCommGroup S]
    [NormedSpace ℝ S] [ProperSpace S] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {U : Set S} (hU : IsOpen U) {G : Vec n → S → E}
    (hG : ContinuousOn (fun z : Vec n × S => G z.1 z.2) (cell n ×ˢ U))
    (hGd : ∀ t ∈ cell n, DifferentiableOn ℝ (G t) U)
    (hG' : ContinuousOn (fun z : Vec n × S => fderiv ℝ (G z.1) z.2) (cell n ×ˢ U))
    {x : S} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ t in cell n, G t y) (∫ t in cell n, fderiv ℝ (G t) x) x := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  have hsub : Metric.closedBall x (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hK : IsCompact (cell n ×ˢ Metric.closedBall x (ε / 2)) :=
    isCompact_cell.prod (isCompact_closedBall x (ε / 2))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hG'.mono (prod_mono subset_rfl hsub))
  have hmeas : ∀ y ∈ U, AEStronglyMeasurable (fun t => G t y) (volume.restrict (cell n)) := by
    intro y hy
    have : ContinuousOn (fun t => G t y) (cell n) :=
      hG.comp (continuousOn_id.prodMk continuousOn_const) fun t ht => ⟨ht, hy⟩
    exact this.aestronglyMeasurable measurableSet_cell
  have hfin : volume.restrict (cell n) univ < ⊤ := by
    rw [Measure.restrict_apply_univ]; exact isCompact_cell.measure_lt_top
  have : IsFiniteMeasure (volume.restrict (cell n)) := ⟨hfin⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y t => G t y) (F' := fun y t => fderiv ℝ (G t) y) (bound := fun _ => C)
    (s := Metric.closedBall x (ε / 2)) (Metric.closedBall_mem_nhds x (by linarith))
    ?_ ?_ ?_ ?_ (integrable_const C) ?_
  · exact Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => hmeas y hy
  · have : ContinuousOn (fun t => G t x) (cell n) :=
      hG.comp (continuousOn_id.prodMk continuousOn_const) fun t ht => ⟨ht, hx⟩
    exact this.integrableOn_compact isCompact_cell
  · have : ContinuousOn (fun t => fderiv ℝ (G t) x) (cell n) :=
      hG'.comp (continuousOn_id.prodMk continuousOn_const) fun t ht => ⟨ht, hx⟩
    exact this.aestronglyMeasurable measurableSet_cell
  · refine (ae_restrict_iff' measurableSet_cell).2 (Eventually.of_forall fun t ht y hy => ?_)
    exact hC (t, y) ⟨ht, hy⟩
  · refine (ae_restrict_iff' measurableSet_cell).2 (Eventually.of_forall fun t ht y hy => ?_)
    exact ((hGd t ht).differentiableAt (hU.mem_nhds (hsub hy))).hasFDerivAt

/-- Finite-order differentiation under the cell integral. -/
private theorem cell_iteratedFDeriv_integral {S E : Type*} [NormedAddCommGroup S]
    [NormedSpace ℝ S] [ProperSpace S] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set S} (hU : IsOpen U) {f : Vec n → S → E} (k : ℕ)
    (hCont : ∀ j : ℕ, j ≤ k → ContinuousOn
      (fun z : Vec n × S => iteratedFDeriv ℝ j (f z.1) z.2)
      (cell n ×ˢ U))
    (hSmooth : ∀ t ∈ cell n, ContDiffOn ℝ k (f t) U)
    {x : S} (hx : x ∈ U) :
    iteratedFDeriv ℝ k (fun y => ∫ t in cell n, f t y) x =
      ∫ t in cell n, iteratedFDeriv ℝ k (f t) x := by
  have key : ∀ j : ℕ, j ≤ k → ∀ y ∈ U,
      iteratedFDeriv ℝ j (fun y => ∫ t in cell n, f t y) y =
        ∫ t in cell n, iteratedFDeriv ℝ j (f t) y := by
    intro j
    induction j with
    | zero =>
      intro _ y _
      exact ((continuousMultilinearCurryFin0 ℝ S E).symm.toContinuousLinearEquiv
        |>.integral_comp_comm (fun t => f t y)).symm
    | succ j ih =>
      intro hj y hy
      have hjk : j ≤ k := (Nat.le_succ j).trans hj
      let e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => S) E
      have hdiff : ∀ t ∈ cell n, DifferentiableOn ℝ (iteratedFDeriv ℝ j (f t)) U := by
        intro t ht
        have h := (hSmooth t ht).differentiableOn_iteratedFDerivWithin
          (m := j) (by exact_mod_cast Nat.lt_of_succ_le hj) hU.uniqueDiffOn
        exact h.congr fun z hz => (iteratedFDerivWithin_of_isOpen j hU hz).symm
      have hfd : ∀ z : Vec n × S, fderiv ℝ (iteratedFDeriv ℝ j (f z.1)) z.2 =
          e (iteratedFDeriv ℝ (j + 1) (f z.1) z.2) := fun z => rfl
      have hG' : ContinuousOn (fun z : Vec n × S => fderiv ℝ (iteratedFDeriv ℝ j (f z.1)) z.2)
          (cell n ×ˢ U) := by
        simp_rw [hfd]
        exact e.continuous.comp_continuousOn (hCont (j + 1) hj)
      have hD := hasFDerivAt_cell_integral_gen hU (hCont j hjk) hdiff hG' hy
      have heq : iteratedFDeriv ℝ j (fun y => ∫ t in cell n, f t y) =ᶠ[𝓝 y]
          fun y => ∫ t in cell n, iteratedFDeriv ℝ j (f t) y :=
        Filter.eventually_of_mem (hU.mem_nhds hy) fun z hz => ih hjk z hz
      have h1 : fderiv ℝ (iteratedFDeriv ℝ j (fun y => ∫ t in cell n, f t y)) y =
          ∫ t in cell n, fderiv ℝ (iteratedFDeriv ℝ j (f t)) y := by
        rw [heq.fderiv_eq]; exact hD.fderiv
      show e.symm (fderiv ℝ (iteratedFDeriv ℝ j (fun y => ∫ t in cell n, f t y)) y) = _
      rw [h1]
      have : CompleteSpace (S →L[ℝ] S [×j]→L[ℝ] E) := inferInstance
      exact (LinearIsometry.integral_comp_comm (𝕜 := ℝ) e.symm.toLinearIsometry
        (fun t => fderiv ℝ (iteratedFDeriv ℝ j (f t)) y)).symm
  exact key k le_rfl x hx

/-- Partial derivatives of a jointly smooth function on an open set. -/
private theorem iteratedFDeriv_slice {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Set (Vec n × S)} (hW : IsOpen W) {k : ℕ} {F : Vec n × S → E}
    (hF : ContDiffOn ℝ k F W) {t : Vec n} {y : S} (hty : (t, y) ∈ W) (j : ℕ) (hj : j ≤ k) :
    iteratedFDeriv ℝ j (fun y' => F (t, y')) y =
      (iteratedFDeriv ℝ j F (t, y)).compContinuousLinearMap
        fun _ => (ContinuousLinearMap.inr ℝ (Vec n) S) := by
  set ι := ContinuousLinearMap.inr ℝ (Vec n) S with hι
  set a : Vec n × S := (t, 0) with ha
  set T : Set (Vec n × S) := (fun z => a + z) ⁻¹' W with hT
  have hTo : IsOpen T := hW.preimage (continuous_const.add continuous_id)
  have hFa : ContDiffOn ℝ k (fun z => F (a + z)) T :=
    hF.comp (contDiff_const.add contDiff_id).contDiffOn (fun z hz => hz)
  have hy : ι y ∈ T := by simpa [hT, ha, hι] using hty
  have h1 := ι.iteratedFDerivWithin_comp_right (f := fun z => F (a + z)) hFa hTo.uniqueDiffOn
    ((hTo.preimage ι.continuous).uniqueDiffOn) hy (i := j) (by exact_mod_cast hj)
  rw [iteratedFDerivWithin_of_isOpen _ hTo hy,
    iteratedFDerivWithin_of_isOpen _ (hTo.preimage ι.continuous) (by exact hy)] at h1
  have hfun : (fun y' => F (t, y')) = (fun z => F (a + z)) ∘ ι := by
    funext y'; simp [ha, hι]
  rw [hfun, h1, iteratedFDeriv_comp_add_left]
  simp [ha, hι]

end CellDiff

/-! ### The averaged derivatives -/

/-- The assembly `(t, (ξ, Λ, η)) ↦ assemble Λ t η ξ` is real-linear. -/
private def assembleLM (n : ℕ) : Vec n × Slow n →ₗ[ℝ] Phase (n + n) where
  toFun z := assemble z.2.2.1 z.1 z.2.2.2 z.2.1
  map_add' z z' := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [assemble]
  map_smul' c z := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [assemble]

private def assembleCLM (n : ℕ) : Vec n × Slow n →L[ℝ] Phase (n + n) :=
  LinearMap.toContinuousLinearMap (assembleLM n)

private theorem assembleCLM_apply (t : Vec n) (x : Slow n) :
    assembleCLM n (t, x) = assemble x.2.1 t x.2.2 x.1 := rfl

/-- Differentiation of the angle integral at real points. -/
private theorem iteratedFDeriv_cell_integral (D : Data n) {a : Vec n} (ha : a ∈ axes n)
    {r : ℝ} (hr : r < rho D a)
    (hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re)
    (b : Bool) (k : ℕ) {x : Slow n} (hx : x ∈ realDisc D a r) (hr0 : 0 < r) :
    iteratedFDeriv ℝ k (fun y : Slow n => ∫ t in cell n,
        perturbation D b (assemble y.2.1 t y.2.2 y.1)) x =
      ∫ t in cell n, iteratedFDeriv ℝ k
        (fun y : Slow n => perturbation D b (assemble y.2.1 t y.2.2 y.1)) x := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  set L := assembleCLM n with hL
  set W : Set (Vec n × Slow n) := L ⁻¹' (poincareProdDom n ∩
    poincareProd D.m (D.G * D.m0) ⁻¹' collisionFreeDomain n) with hW
  have hWo : IsOpen W := (isOpen_poincareProd_preimage D.hm hκ).preimage L.continuous
  set F : Vec n × Slow n → ℝ := fun z => perturbation D b (L z) with hF
  have hFan : AnalyticOnNhd ℝ F W := by
    have hmaps : MapsTo L W (poincareProdDom n ∩
        poincareProd D.m (D.G * D.m0) ⁻¹' collisionFreeDomain n) := fun z hz => hz
    cases b
    · exact (analyticOnNhd_fFix_poincareProd D.hm hκ).comp (L.analyticOnNhd _) hmaps
    · exact (analyticOnNhd_fMov_poincareProd D.hm hκ).comp (L.analyticOnNhd _) hmaps
  have hFk : ContDiffOn ℝ k F W := hFan.contDiffOn hWo.uniqueDiffOn
  have hmem : ∀ t : Vec n, ∀ y ∈ realDisc D a r, (t, y) ∈ W := fun t y hy =>
    ⟨assemble_mem_dom D ha hr hy t, mem_collisionFree D ha hr hsep hy t⟩
  have hcontW : ∀ j : ℕ, j ≤ k → ContinuousOn (fun z => iteratedFDeriv ℝ j F z) W := by
    intro j hj
    have := hFk.continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast hj)
      hWo.uniqueDiffOn
    exact this.congr fun z hz => (iteratedFDerivWithin_of_isOpen j hWo hz).symm
  have hcontj : ∀ j : ℕ, j ≤ k → ContinuousOn
      (fun z : Vec n × Slow n => iteratedFDeriv ℝ j (fun y => F (z.1, y)) z.2)
      (cell n ×ˢ realDisc D a r) := by
    intro j hj
    have hLm := (ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := ℝ)
      (fun _ : Fin j => ContinuousLinearMap.inr ℝ (Vec n) (Slow n))).continuous
    refine (hLm.comp_continuousOn (hcontW j hj)).mono ?_ |>.congr ?_
    · rintro ⟨t, y⟩ ⟨_, hy⟩
      exact hmem t y hy
    · rintro ⟨t, y⟩ ⟨_, hy⟩
      exact iteratedFDeriv_slice hWo hFk (hmem t y hy) j hj
  exact cell_iteratedFDeriv_integral (isOpen_realDisc D a hr0) (f := fun t y => F (t, y)) k
    hcontj (fun t _ => hFk.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun y hy => hmem t y hy)) hx

/-- The holomorphy and analyticity of the average, under the separation bound. -/
private theorem secular_regular (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr0 : 0 < r) (hr : r < rho D a)
    (hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re) (b : Bool) :
    DifferentiableOn ℂ (secularC D b) (polydisc D a r) ∧
      AnalyticOnNhd ℝ (secular D b) (realDisc D a r) := by
  have hU : IsOpen (polydisc D a r) := by
    rw [polydisc_eq_ball D a hr0]; exact Metric.isOpen_ball
  have hol := differentiableOn_perturbationC D ha hr hsep hr0 b
  have hcont := continuousOn_perturbationC D ha hr hsep b
  have hS : DifferentiableOn ℂ (secularC D b) (polydisc D a r) := by
    unfold secularC
    exact (e_param_cslow hU (f := fun t x => perturbationC D b t x)
      (hcont.mono (prod_mono (subset_univ (cell n)) subset_rfl))
      fun t _ => hol t).const_smul ((2 * π) ^ (-(n : ℤ)))
  refine ⟨hS, fun x hx => ?_⟩
  have hA' : AnalyticOnNhd ℂ (secularC D b) (polydisc D a r) :=
    analyticOnNhd_of_differentiableOn hU hS
  have hA : AnalyticAt ℂ (secularC D b) (inclusion x) := hA' _ hx
  have h1 : AnalyticAt ℝ (fun y => (secularC D b (inclusion y)).re) x :=
    (Complex.reCLM.analyticAt _).comp
      ((hA.restrictScalars (𝕜 := ℝ)).comp ((inclusionCLM n).analyticAt x))
  refine h1.congr ?_
  filter_upwards [(isOpen_realDisc D a hr0).mem_nhds hx] with y hy
  rw [secularC_inclusion D ha hr b hy, Complex.ofReal_re]

/-- `stepP:p8:pa-hol`: `f̂_fix` and `f̂_mov` are holomorphic in the slow variables, jointly
continuous, `2π`-periodic in the angles, and equal `f_fix ∘ Ψ` resp. `f_mov ∘ Ψ` at real points. -/
theorem perturbation_hol (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr0 : 0 < r) (hr : r < rho D a)
    (hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re) (b : Bool) :
    (∀ t, DifferentiableOn ℂ (perturbationC D b t) (polydisc D a r)) ∧
    ContinuousOn (fun z : Vec n × CSlow n => perturbationC D b z.1 z.2)
      (univ ×ˢ polydisc D a r) ∧
    (∀ x ∈ polydisc D a r, ∀ t i,
      perturbationC D b (Function.update t i (t i + 2 * π)) x = perturbationC D b t x) ∧
    (∀ x ∈ realDisc D a r, ∀ t,
      perturbationC D b t (inclusion x) =
        ((if b then fMov D.G D.m0 D.m (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1))
          else fFix D.G D.m (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)) : ℝ) :
          ℂ)) :=
  ⟨differentiableOn_perturbationC D ha hr hsep hr0 b, continuousOn_perturbationC D ha hr hsep b,
    fun _ hx t i => perturbationC_periodic D ha hr b hx t i,
    fun x hx t => by rw [perturbationC_inclusion D ha hr b hx t]; rfl⟩

/-- `stepP:p8:pa-avg`: `S` is holomorphic on the polydisc, real at real points, real analytic on
the real disc, and `∂^α S = ⟨∂^α f̂⟩` (every iterated derivative is the angle average). -/
theorem perturbation_avg (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr0 : 0 < r) (hr : r < rho D a)
    (hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re) (b : Bool) :
    DifferentiableOn ℂ (secularC D b) (polydisc D a r) ∧
    (∀ x ∈ realDisc D a r, secularC D b (inclusion x) = (secular D b x : ℂ)) ∧
    AnalyticOnNhd ℝ (secular D b) (realDisc D a r) ∧
    ∀ k : ℕ, ∀ x ∈ realDisc D a r, iteratedFDeriv ℝ k (secular D b) x =
      avg (fun t => iteratedFDeriv ℝ k
        (fun y : Slow n => perturbation D b (assemble y.2.1 t y.2.2 y.1)) x) := by
  obtain ⟨hS, hA⟩ := secular_regular D ha hr0 hr hsep b
  refine ⟨hS, fun x hx => secularC_inclusion D ha hr b hx, hA, fun k x hx => ?_⟩
  have hI := iteratedFDeriv_cell_integral D ha hr hsep b k hx hr0
  have hc : ((2 * π) ^ (-(n : ℤ)) : ℝ) ≠ 0 := by positivity
  have hsec : secular D b = fun y : Slow n => ((2 * π) ^ (-(n : ℤ)) : ℝ) •
      ∫ t in cell n, perturbation D b (assemble y.2.1 t y.2.2 y.1) := by
    funext y; simp [secular, secularAverage, cell]
  have hcd : ContDiffAt ℝ k (fun y : Slow n => ∫ t in cell n,
      perturbation D b (assemble y.2.1 t y.2.2 y.1)) x := by
    have h : ContDiffAt ℝ k (fun y : Slow n => ((2 * π) ^ (-(n : ℤ)) : ℝ)⁻¹ • secular D b y) x :=
      ((hA x hx).const_smul (c := ((2 * π) ^ (-(n : ℤ)) : ℝ)⁻¹)).contDiffAt
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    rw [hsec]; simp
  rw [hsec]
  refine (iteratedFDeriv_const_smul_apply
    (a := ((2 * π) ^ (-(n : ℤ)) : ℝ)) hcd).trans ?_
  rw [hI]
  rfl

/-! ### The averaged derivatives at complex slow points -/

open scoped ContDiff

/-- The complexified perturbation is real smooth in the angles and the (complex) slow variables
on the polydisc. -/
private theorem contDiffOn_perturbationC (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a)
    (hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re) (b : Bool) :
    ContDiffOn ℝ ∞ (fun z : Vec n × CSlow n => perturbationC D b z.1 z.2)
      (univ ×ˢ polydisc D a r) := by
  have hblock : ∀ i, ContDiff ℝ ∞ (fun z : Vec n × CSlow n => blockC z.1 z.2 i) := by
    intro i
    refine ContDiff.prodMk (contDiff_pi.2 fun k => ?_) (contDiff_pi.2 fun k => ?_) <;>
      fin_cases k <;> simp <;>
      first | fun_prop | exact Complex.ofRealCLM.contDiff.comp (by fun_prop)
  have hplanet : ∀ i, ContDiffOn ℝ ∞ (fun z : Vec n × CSlow n => planetC D z.1 z.2 i)
      (univ ×ˢ polydisc D a r) := by
    intro i
    have hΛ := action_pos D ha i
    obtain ⟨hopen, -, hd, -⟩ := poincare_holomorphic (m := D.m i) (κ := D.G * D.m0)
      (Λo := action D a i) (D.hm i) (mul_pos D.hG D.hm0) hΛ
    have hC : ContDiffOn ℝ ∞ (poincareC (D.m i) (D.G * D.m0)) (poincareNbhd (action D a i)) :=
      ((analyticOnNhd_of_differentiableOn hopen hd).contDiffOn (n := ∞)
        hopen.uniqueDiffOn).restrict_scalars ℝ
    exact hC.comp (hblock i).contDiffOn fun z hz => blockC_mem_nbhd D ha hr hz.2 i
  have hfst : ∀ i c, ContDiffOn ℝ ∞ (fun z : Vec n × CSlow n => (planetC D z.1 z.2 i).1 c)
      (univ ×ˢ polydisc D a r) := fun i c =>
    (show ContDiff ℝ ∞ (fun v : (Fin 2 → ℂ) × (Fin 2 → ℂ) => v.1 c) by fun_prop).comp_contDiffOn
      (hplanet i)
  have hsnd : ∀ i c, ContDiffOn ℝ ∞ (fun z : Vec n × CSlow n => (planetC D z.1 z.2 i).2 c)
      (univ ×ˢ polydisc D a r) := fun i c =>
    (show ContDiff ℝ ∞ (fun v : (Fin 2 → ℂ) × (Fin 2 → ℂ) => v.2 c) by fun_prop).comp_contDiffOn
      (hplanet i)
  have hsepC : ∀ i j, ContDiffOn ℝ ∞ (fun z : Vec n × CSlow n => separationC D z.1 z.2 i j)
      (univ ×ˢ polydisc D a r) := fun i j => by
    unfold separationC
    exact ContDiffOn.sum fun c _ => ((hfst i c).sub (hfst j c)).pow 2
  have hpow : ContDiffOn ℂ ∞ (fun s : ℂ => s ^ (-1 / 2 : ℂ)) Complex.slitPlane :=
    (differentiableOn_id.cpow_const (c := (-1 / 2 : ℂ)) (fun x hx => hx)).contDiffOn
      Complex.isOpen_slitPlane
  unfold perturbationC
  refine ContDiffOn.add (ContDiffOn.mul contDiffOn_const ?_) ?_
  · refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j hj => ?_
    have hij : i < j := (Finset.mem_filter.1 hj).2
    refine ContDiffOn.mul contDiffOn_const ?_
    exact (hpow.restrict_scalars ℝ).comp (hsepC i j) fun z hz =>
      separationC_slit D ha hsep hz.2 hij
  · cases b
    · simpa using contDiffOn_const (c := (0 : ℂ))
    · simp only [ite_true]
      refine ContDiffOn.div_const (ContDiffOn.sum fun c _ => ?_) _
      exact (ContDiffOn.sum fun i _ => hsnd i c).pow 2

/-- Differentiation of the angle integral at complex slow points, with real derivatives. -/
private theorem iteratedFDeriv_cell_integral_complex (D : Data n) {a : Vec n} (ha : a ∈ axes n)
    {r : ℝ} (hr0 : 0 < r) (hr : r < rho D a)
    (hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re)
    (b : Bool) (k : ℕ) {x : CSlow n} (hx : x ∈ polydisc D a r) :
    iteratedFDeriv ℝ k (fun y : CSlow n => ∫ t in cell n, perturbationC D b t y) x =
      ∫ t in cell n, iteratedFDeriv ℝ k (perturbationC D b t) x := by
  have hU : IsOpen (polydisc D a r) := by
    rw [polydisc_eq_ball D a hr0]; exact Metric.isOpen_ball
  set W : Set (Vec n × CSlow n) := univ ×ˢ polydisc D a r with hW
  have hWo : IsOpen W := isOpen_univ.prod hU
  set F : Vec n × CSlow n → ℂ := fun z => perturbationC D b z.1 z.2 with hF
  have hFk : ContDiffOn ℝ k F W :=
    (contDiffOn_perturbationC D ha hr hsep b).of_le (by exact_mod_cast le_top)
  have hmem : ∀ t : Vec n, ∀ y ∈ polydisc D a r, (t, y) ∈ W := fun t y hy => ⟨mem_univ _, hy⟩
  have hcontW : ∀ j : ℕ, j ≤ k → ContinuousOn (fun z => iteratedFDeriv ℝ j F z) W := by
    intro j hj
    have := hFk.continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast hj)
      hWo.uniqueDiffOn
    exact this.congr fun z hz => (iteratedFDerivWithin_of_isOpen j hWo hz).symm
  have hcontj : ∀ j : ℕ, j ≤ k → ContinuousOn
      (fun z : Vec n × CSlow n => iteratedFDeriv ℝ j (fun y => F (z.1, y)) z.2)
      (cell n ×ˢ polydisc D a r) := by
    intro j hj
    have hLm := (ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := ℂ)
      (fun _ : Fin j => ContinuousLinearMap.inr ℝ (Vec n) (CSlow n))).continuous
    refine (hLm.comp_continuousOn (hcontW j hj)).mono ?_ |>.congr ?_
    · rintro ⟨t, y⟩ ⟨_, hy⟩
      exact hmem t y hy
    · rintro ⟨t, y⟩ ⟨_, hy⟩
      exact iteratedFDeriv_slice hWo hFk (hmem t y hy) j hj
  exact cell_iteratedFDeriv_integral hU (f := fun t y => F (t, y)) k
    hcontj (fun t _ => hFk.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun y hy => hmem t y hy)) hx

/-- `stepP:p8:pa-avg`, complex slow points: `∂^α S = ⟨∂^α f̂⟩` for every order and every point of
the complex polydisc, with complex derivatives of the holomorphic `secularC` and `perturbationC`. -/
theorem perturbation_avg_complex (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr0 : 0 < r) (hr : r < rho D a)
    (hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re) (b : Bool) :
    ∀ k : ℕ, ∀ x ∈ polydisc D a r, iteratedFDeriv ℂ k (secularC D b) x =
      avg (fun t => iteratedFDeriv ℂ k (perturbationC D b t) x) := by
  intro k x hx
  have hU : IsOpen (polydisc D a r) := by
    rw [polydisc_eq_ball D a hr0]; exact Metric.isOpen_ball
  obtain ⟨hS, -⟩ := secular_regular D ha hr0 hr hsep b
  have hSC : ContDiffAt ℂ k (secularC D b) x :=
    (analyticOnNhd_of_differentiableOn hU hS x hx).contDiffAt
  have hPC : ∀ t, ContDiffAt ℂ k (perturbationC D b t) x := fun t =>
    (analyticOnNhd_of_differentiableOn hU
      (differentiableOn_perturbationC D ha hr hsep hr0 b t) x hx).contDiffAt
  have hsec : secularC D b = fun y : CSlow n => ((2 * π) ^ (-(n : ℤ)) : ℝ) •
      ∫ t in cell n, perturbationC D b t y := rfl
  have hcd : ContDiffAt ℝ k (fun y : CSlow n => ∫ t in cell n, perturbationC D b t y) x := by
    have h : ContDiffAt ℝ k (fun y : CSlow n =>
        ((2 * π) ^ (-(n : ℤ)) : ℝ)⁻¹ • secularC D b y) x :=
      (hSC.restrict_scalars ℝ).const_smul (((2 * π) ^ (-(n : ℤ)) : ℝ)⁻¹)
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    rw [hsec]; simp
  have hreal : iteratedFDeriv ℝ k (secularC D b) x =
      ((2 * π) ^ (-(n : ℤ)) : ℝ) • ∫ t in cell n, iteratedFDeriv ℝ k (perturbationC D b t) x := by
    rw [hsec]
    refine (iteratedFDeriv_const_smul_apply
      (a := ((2 * π) ^ (-(n : ℤ)) : ℝ)) hcd).trans ?_
    rw [iteratedFDeriv_cell_integral_complex D ha hr0 hr hsep b k hx]
  let R := ContinuousMultilinearMap.restrictScalarsₗᵢ (𝕜 := ℂ) (𝕜' := ℝ) (ι := Fin k)
    (E := fun _ => CSlow n) (G := ℂ)
  have hL : R (iteratedFDeriv ℂ k (secularC D b) x) = iteratedFDeriv ℝ k (secularC D b) x :=
    hSC.restrictScalars_iteratedFDeriv
  have hI : ∫ t in cell n, iteratedFDeriv ℝ k (perturbationC D b t) x =
      R (∫ t in cell n, iteratedFDeriv ℂ k (perturbationC D b t) x) := by
    have : CompleteSpace (ContinuousMultilinearMap ℝ (fun _ : Fin k => CSlow n) ℂ) :=
      ContinuousMultilinearMap.completeSpace
        (.of_seq fun _u x hux => (hux.isVonNBounded_range ℝ).insert x)
    rw [← LinearIsometry.integral_comp_comm R]
    exact integral_congr_ae
      (Eventually.of_forall fun t => (hPC t).restrictScalars_iteratedFDeriv.symm)
  apply R.injective
  rw [hL, hreal, hI, avg, map_smul]

/-- `bpP:p8:perturbation-analytic`: the bundle. -/
theorem perturbation_analytic_full (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    ∃ r : ℝ, 0 < r ∧ r < rho D a / 2 ∧
    (∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re) ∧
    (∀ x ∈ realDisc D a r, ∀ t : Vec n,
      (∀ i j, separationC D t (inclusion x) i j =
        ((planeSq (bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 i -
          bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 j) : ℝ) :
          ℂ)) ∧
      (∀ i j, i < j → (a j - a i) / √2 ≤
        planeLength (bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 i -
          bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 j)) ∧
      poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1) ∈ collisionFreeDomain n) ∧
    ∀ b : Bool,
      ((∀ t, DifferentiableOn ℂ (perturbationC D b t) (polydisc D a r)) ∧
        ContinuousOn (fun z : Vec n × CSlow n => perturbationC D b z.1 z.2)
          (univ ×ˢ polydisc D a r) ∧
        (∀ x ∈ polydisc D a r, ∀ t i,
          perturbationC D b (Function.update t i (t i + 2 * π)) x = perturbationC D b t x) ∧
        (∀ x ∈ realDisc D a r, ∀ t,
          perturbationC D b t (inclusion x) =
            ((if b then fMov D.G D.m0 D.m
                (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1))
              else fFix D.G D.m
                (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)) : ℝ) : ℂ))) ∧
      DifferentiableOn ℂ (secularC D b) (polydisc D a r) ∧
      (∀ x ∈ realDisc D a r, secularC D b (inclusion x) = (secular D b x : ℂ)) ∧
      AnalyticOnNhd ℝ (secular D b) (realDisc D a r) ∧
      (∀ k : ℕ, ∀ x ∈ realDisc D a r, iteratedFDeriv ℝ k (secular D b) x =
        avg (fun t => iteratedFDeriv ℝ k
          (fun y : Slow n => perturbation D b (assemble y.2.1 t y.2.2 y.1)) x)) ∧
      ∀ k : ℕ, ∀ x ∈ polydisc D a r, iteratedFDeriv ℂ k (secularC D b) x =
        avg (fun t => iteratedFDeriv ℂ k (perturbationC D b t) x) := by
  obtain ⟨r, hr0, hrh, hsep, hreal⟩ := perturbation_unif D ha
  have hρ := rho_pos D ha
  have hr : r < rho D a := by linarith
  exact ⟨r, hr0, hrh, hsep, hreal, fun b => ⟨perturbation_hol D ha hr0 hr hsep b,
    ⟨(perturbation_avg D ha hr0 hr hsep b).1, (perturbation_avg D ha hr0 hr hsep b).2.1,
      (perturbation_avg D ha hr0 hr hsep b).2.2.1, (perturbation_avg D ha hr0 hr hsep b).2.2.2,
      perturbation_avg_complex D ha hr0 hr hsep b⟩⟩⟩

end SecularForm
end KAM.Planetary
end
