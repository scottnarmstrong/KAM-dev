/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.PicardFamilies
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Parameter derivatives of Picard integrals

Blueprint N Part 12 (`bpN:p12:ext-dep#parameter-integral`, `#linear`).

* `KAM.Nekhoroshev.hasFDerivAt_intervalIntegral_comp`: differentiation under the integral sign
  for `x ↦ ∫₀ᵗ F (U τ x) dτ`, with derivative `∫₀ᵗ DF (U τ x) ∘ DU τ x`, by Mathlib's dominated
  derivative theorem.
* `KAM.Nekhoroshev.linear_family`: the continuous linear Volterra fixed family
  `Y t x = id + ∫₀ᵗ G τ x ∘ Y τ x`, obtained by contraction on bounded continuous families of
  continuous linear maps.
-/

@[expose] public noncomputable section

open Set Metric Function Filter
open scoped NNReal Topology BoundedContinuousFunction Interval Classical

namespace KAM.Nekhoroshev

section ParameterIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `bpN:p12:ext-dep#parameter-integral`: differentiation of `x ↦ ∫₀ᵗ F (U τ x) dτ` at `x`.
`U τ` is differentiable with derivative `U' τ z` on a neighbourhood `B` of `x`, `F` has derivative
`F' w` at every value `U τ z`, both derivatives are bounded uniformly, and the integrands are
continuous in time. -/
theorem hasFDerivAt_intervalIntegral_comp {F : E → E} {F' : E → E →L[ℝ] E}
    {U : ℝ → E → E} {U' : ℝ → E → E →L[ℝ] E} {t : ℝ} {B : Set E} {x : E} {Λ M : ℝ}
    (hB : B ∈ 𝓝 x)
    (hU : ∀ τ ∈ [[0, t]], ∀ z ∈ B, HasFDerivAt (U τ) (U' τ z) z)
    (hF : ∀ τ ∈ [[0, t]], ∀ z ∈ B, HasFDerivAt F (F' (U τ z)) (U τ z))
    (hFb : ∀ τ ∈ [[0, t]], ∀ z ∈ B, ‖F' (U τ z)‖ ≤ Λ)
    (hUb : ∀ τ ∈ [[0, t]], ∀ z ∈ B, ‖U' τ z‖ ≤ M)
    (hFc : ∀ z ∈ B, ContinuousOn (fun τ => F (U τ z)) [[0, t]])
    (hDc : ContinuousOn (fun τ => (F' (U τ x)).comp (U' τ x)) [[0, t]]) :
    HasFDerivAt (fun z => ∫ τ in (0 : ℝ)..t, F (U τ z))
      (∫ τ in (0 : ℝ)..t, (F' (U τ x)).comp (U' τ x)) x := by
  have hx : x ∈ B := mem_of_mem_nhds hB
  have hsub : Ι (0 : ℝ) t ⊆ [[0, t]] := uIoc_subset_uIcc
  have hdiff : ∀ τ ∈ [[0, t]], ∀ z ∈ B,
      HasFDerivAt (fun w => F (U τ w)) ((F' (U τ z)).comp (U' τ z)) z := fun τ hτ z hz =>
    (hF τ hτ z hz).comp z (hU τ hτ z hz)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (H := E) (F := fun z τ => F (U τ z))
    (F' := fun z τ => (F' (U τ z)).comp (U' τ z)) (bound := fun _ => Λ * M) hB ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.eventually_of_mem hB fun z hz =>
      ((hFc z hz).mono hsub).aestronglyMeasurable measurableSet_uIoc
  · exact (hFc x hx).intervalIntegrable
  · exact (hDc.mono hsub).aestronglyMeasurable measurableSet_uIoc
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc fun τ hτ z hz => ?_
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hFb τ (hsub hτ) z hz) (hUb τ (hsub hτ) z hz)
      (norm_nonneg _) ((norm_nonneg _).trans (hFb τ (hsub hτ) z hz)))
  · exact intervalIntegrable_const
  · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc fun τ hτ z hz => hdiff τ (hsub hτ) z hz

end ParameterIntegral

section Volterra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {x₀ : E} {a r Λ : ℝ}

/-- The Volterra integrand `τ ↦ G (τ, x) ∘ Z (τ, x)`, clamped to `[-a, a]` in time. -/
def voltInt (ha : 0 ≤ a) (Gb : PicardBase x₀ a r → E →L[ℝ] E)
    (Z : PicardBase x₀ a r →ᵇ (E →L[ℝ] E)) (x : closedBall x₀ r) (τ : ℝ) : E →L[ℝ] E :=
  (Gb (Set.projIcc (-a) a (neg_le_self ha) τ, x)).comp
    (Z (Set.projIcc (-a) a (neg_le_self ha) τ, x))

/-- The Volterra operator `Z ↦ (t, x) ↦ id + ∫₀ᵗ G (τ, x) ∘ Z (τ, x) dτ`, as a function. -/
def voltFun (ha : 0 ≤ a) (Gb : PicardBase x₀ a r → E →L[ℝ] E)
    (Z : PicardBase x₀ a r →ᵇ (E →L[ℝ] E)) (p : PicardBase x₀ a r) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + ∫ τ in (0 : ℝ)..p.1, voltInt ha Gb Z p.2 τ

theorem continuous_voltInt (ha : 0 ≤ a) {Gb : PicardBase x₀ a r → E →L[ℝ] E}
    (hG : Continuous Gb) (Z : PicardBase x₀ a r →ᵇ (E →L[ℝ] E)) :
    Continuous (fun q : PicardBase x₀ a r × ℝ => voltInt ha Gb Z q.1.2 q.2) := by
  have hp : Continuous fun q : PicardBase x₀ a r × ℝ =>
      ((Set.projIcc (-a) a (neg_le_self ha) q.2, q.1.2) : PicardBase x₀ a r) :=
    (continuous_projIcc.comp continuous_snd).prodMk (continuous_snd.comp continuous_fst)
  exact (hG.comp hp).clm_comp (Z.continuous.comp hp)

theorem continuous_voltFun (ha : 0 ≤ a) {Gb : PicardBase x₀ a r → E →L[ℝ] E}
    (hG : Continuous Gb) (Z : PicardBase x₀ a r →ᵇ (E →L[ℝ] E)) :
    Continuous (voltFun ha Gb Z) := by
  unfold voltFun
  refine continuous_const.add ?_
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun (p : PicardBase x₀ a r) τ => voltInt ha Gb Z p.2 τ)
    (continuous_voltInt ha hG Z) (continuous_subtype_val.comp continuous_fst)

theorem norm_voltInt_le (ha : 0 ≤ a) {Gb : PicardBase x₀ a r → E →L[ℝ] E}
    (hb : ∀ p, ‖Gb p‖ ≤ Λ) (Z : PicardBase x₀ a r →ᵇ (E →L[ℝ] E)) (x : closedBall x₀ r) (τ : ℝ) :
    ‖voltInt ha Gb Z x τ‖ ≤ Λ * ‖Z‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (hb _) (Z.norm_coe_le_norm _) (norm_nonneg _) ((norm_nonneg _).trans (hb
      (Set.projIcc (-a) a (neg_le_self ha) τ, x))))

theorem norm_integral_voltInt_le (ha : 0 ≤ a) {Gb : PicardBase x₀ a r → E →L[ℝ] E}
    (hb : ∀ p, ‖Gb p‖ ≤ Λ) (Z : PicardBase x₀ a r →ᵇ (E →L[ℝ] E)) (p : PicardBase x₀ a r) :
    ‖∫ τ in (0 : ℝ)..p.1, voltInt ha Gb Z p.2 τ‖ ≤ a * Λ * ‖Z‖ := by
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (hb (⟨0, by simp [ha], by simp [ha]⟩, p.2))
  have h1 : ‖∫ τ in (0 : ℝ)..p.1, voltInt ha Gb Z p.2 τ‖ ≤ Λ * ‖Z‖ * |(p.1 : ℝ) - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun τ _ => norm_voltInt_le ha hb Z _ _
  have h2 : |(p.1 : ℝ) - 0| ≤ a := by
    rw [sub_zero, abs_le]; exact ⟨by linarith [p.1.2.1], p.1.2.2⟩
  calc _ ≤ Λ * ‖Z‖ * |(p.1 : ℝ) - 0| := h1
    _ ≤ Λ * ‖Z‖ * a := by gcongr
    _ = a * Λ * ‖Z‖ := by ring

/-- The Volterra operator on bounded continuous families of linear maps. -/
def voltMap (ha : 0 ≤ a) {Gb : PicardBase x₀ a r → E →L[ℝ] E} (hG : Continuous Gb)
    (hb : ∀ p, ‖Gb p‖ ≤ Λ) (Z : PicardBase x₀ a r →ᵇ (E →L[ℝ] E)) :
    PicardBase x₀ a r →ᵇ (E →L[ℝ] E) :=
  BoundedContinuousFunction.mkOfBound ⟨voltFun ha Gb Z, continuous_voltFun ha hG Z⟩
    (2 * (1 + a * Λ * ‖Z‖)) (fun p q => by
      have hn : ∀ p, ‖voltFun ha Gb Z p‖ ≤ 1 + a * Λ * ‖Z‖ := fun p =>
        (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.norm_id_le) (norm_integral_voltInt_le ha hb Z p))
      calc dist _ _ ≤ ‖voltFun ha Gb Z p‖ + ‖voltFun ha Gb Z q‖ := dist_le_norm_add_norm _ _
        _ ≤ _ := by linarith [hn p, hn q])

theorem voltMap_apply (ha : 0 ≤ a) {Gb : PicardBase x₀ a r → E →L[ℝ] E} (hG : Continuous Gb)
    (hb : ∀ p, ‖Gb p‖ ≤ Λ) (Z : PicardBase x₀ a r →ᵇ (E →L[ℝ] E)) (p : PicardBase x₀ a r) :
    voltMap ha hG hb Z p = voltFun ha Gb Z p := rfl

theorem contractingWith_voltMap (ha : 0 ≤ a) {Gb : PicardBase x₀ a r → E →L[ℝ] E}
    (hG : Continuous Gb) (hb : ∀ p, ‖Gb p‖ ≤ Λ) (hΛ : 0 ≤ Λ) (hq : a * Λ < 1) :
    ContractingWith (Real.toNNReal (a * Λ)) (voltMap ha hG hb) := by
  have hK : ((Real.toNNReal (a * Λ) : ℝ≥0) : ℝ) = a * Λ :=
    Real.coe_toNNReal _ (mul_nonneg ha hΛ)
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun Z Z' => ?_⟩
  · rw [← NNReal.coe_lt_coe, hK]; simpa using hq
  · rw [hK]
    refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun p => ?_
    have hint : ∀ W : PicardBase x₀ a r →ᵇ (E →L[ℝ] E), IntervalIntegrable
        (fun τ => voltInt ha Gb W p.2 τ) MeasureTheory.volume 0 p.1 := fun W =>
      Continuous.intervalIntegrable ((continuous_voltInt ha hG W).comp
        (continuous_const.prodMk continuous_id)) _ _
    rw [voltMap_apply, voltMap_apply, voltFun, voltFun, dist_eq_norm]
    have e : (ContinuousLinearMap.id ℝ E + ∫ τ in (0 : ℝ)..p.1, voltInt ha Gb Z p.2 τ) -
        (ContinuousLinearMap.id ℝ E + ∫ τ in (0 : ℝ)..p.1, voltInt ha Gb Z' p.2 τ) =
        ∫ τ in (0 : ℝ)..p.1, (voltInt ha Gb Z p.2 τ - voltInt ha Gb Z' p.2 τ) := by
      rw [intervalIntegral.integral_sub (hint Z) (hint Z')]; abel
    rw [e]
    have hd : ∀ τ, ‖voltInt ha Gb Z p.2 τ - voltInt ha Gb Z' p.2 τ‖ ≤ Λ * dist Z Z' := by
      intro τ
      have : voltInt ha Gb Z p.2 τ - voltInt ha Gb Z' p.2 τ =
          (Gb (Set.projIcc (-a) a (neg_le_self ha) τ, p.2)).comp
            (Z (Set.projIcc (-a) a (neg_le_self ha) τ, p.2) -
              Z' (Set.projIcc (-a) a (neg_le_self ha) τ, p.2)) := by
        simp [voltInt, ContinuousLinearMap.comp_sub]
      rw [this]
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      refine mul_le_mul (hb _) ?_ (norm_nonneg _) hΛ
      rw [← dist_eq_norm]
      exact BoundedContinuousFunction.dist_coe_le_dist _
    have h1 : ‖∫ τ in (0 : ℝ)..p.1, (voltInt ha Gb Z p.2 τ - voltInt ha Gb Z' p.2 τ)‖ ≤
        Λ * dist Z Z' * |(p.1 : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun τ _ => hd τ
    have h2 : |(p.1 : ℝ) - 0| ≤ a := by
      rw [sub_zero, abs_le]; exact ⟨by linarith [p.1.2.1], p.1.2.2⟩
    calc _ ≤ Λ * dist Z Z' * |(p.1 : ℝ) - 0| := h1
      _ ≤ Λ * dist Z Z' * a := by gcongr
      _ = a * Λ * dist Z Z' := by ring

/-- `bpN:p12:ext-dep#linear`: for a continuous family `G` of linear maps with `‖G‖ ≤ Λ`,
`a Λ < 1`, on `[-a, a] × closedBall x₀ r`, the linear Volterra equation
`Y t x = id + ∫₀ᵗ G τ x ∘ Y τ x` has a continuous solution family with `‖Y‖ ≤ 1 / (1 - a Λ)`. -/
theorem linear_family [CompleteSpace E] {G : ℝ → E → E →L[ℝ] E} (ha : 0 ≤ a) (hΛ : 0 ≤ Λ)
    (hq : a * Λ < 1)
    (hGc : ContinuousOn (fun p : ℝ × E => G p.1 p.2) (Icc (-a) a ×ˢ closedBall x₀ r))
    (hGb : ∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r, ‖G t x‖ ≤ Λ) :
    ∃ Y : ℝ → E → E →L[ℝ] E,
      ContinuousOn (fun p : ℝ × E => Y p.1 p.2) (Icc (-a) a ×ˢ closedBall x₀ r) ∧
      (∀ t ∈ Icc (-a) a, ∀ x ∈ closedBall x₀ r, ‖Y t x‖ ≤ 1 / (1 - a * Λ)) ∧
      ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc (-a) a,
        Y t x = ContinuousLinearMap.id ℝ E + ∫ τ in (0 : ℝ)..t, (G τ x).comp (Y τ x) := by
  set Gb : PicardBase x₀ a r → E →L[ℝ] E := fun p => G p.1.1 p.2.1 with hGbdef
  have hG : Continuous Gb := by
    refine hGc.comp_continuous ?_ fun p => ⟨p.1.2, p.2.2⟩
    exact (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hb : ∀ p, ‖Gb p‖ ≤ Λ := fun p => hGb _ p.1.2 _ p.2.2
  have hc := contractingWith_voltMap ha hG hb hΛ hq
  haveI : Nonempty (PicardBase x₀ a r →ᵇ (E →L[ℝ] E)) := ⟨0⟩
  set Zs := ContractingWith.fixedPoint (voltMap ha hG hb) hc with hZs
  have hfix : voltMap ha hG hb Zs = Zs :=
    ContractingWith.fixedPoint_isFixedPt (f := voltMap ha hG hb) hc
  have hZeq : ∀ p, Zs p = voltFun ha Gb Zs p := fun p => by
    rw [← voltMap_apply ha hG hb, hfix]
  let Y : ℝ → E → E →L[ℝ] E := fun t x =>
    if hx : x ∈ closedBall x₀ r then Zs (Set.projIcc (-a) a (neg_le_self ha) t, ⟨x, hx⟩) else 0
  have hY : ∀ {t : ℝ}, t ∈ Icc (-a) a → ∀ {x : E} (hx : x ∈ closedBall x₀ r),
      Y t x = Zs (⟨t, ‹t ∈ Icc (-a) a›⟩, ⟨x, hx⟩) := by
    intro t ht x hx
    simp [Y, hx, Set.projIcc_of_mem _ ht]
  refine ⟨Y, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : Continuous fun q : ↥(Icc (-a) a ×ˢ closedBall x₀ r) =>
        Zs (⟨q.1.1, (mem_prod.1 q.2).1⟩, ⟨q.1.2, (mem_prod.1 q.2).2⟩) := by
      refine Zs.continuous.comp (Continuous.prodMk ?_ ?_)
      · exact (continuous_fst.comp continuous_subtype_val).subtype_mk _
      · exact (continuous_snd.comp continuous_subtype_val).subtype_mk _
    refine this.congr fun q => ?_
    exact (hY _ _).symm
  · have hpos : 0 < 1 - a * Λ := by linarith
    have hN : ‖Zs‖ ≤ 1 / (1 - a * Λ) := by
      have h1 : ‖Zs‖ ≤ 1 + a * Λ * ‖Zs‖ := by
        refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p => ?_
        rw [hZeq]
        exact (norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le
          (norm_integral_voltInt_le ha hb Zs p))
      rw [le_div_iff₀ hpos]; nlinarith
    intro t ht x hx
    rw [hY ht hx]
    exact (Zs.norm_coe_le_norm _).trans hN
  · intro x hx t ht
    rw [hY ht hx, hZeq, voltFun]
    congr 1
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    have hτ' : τ ∈ Icc (-a) a := by
      refine uIcc_subset_Icc ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩ ht hτ
    simp only [voltInt, hGbdef]
    rw [hY hτ' hx, Set.projIcc_of_mem _ hτ']

end Volterra

end KAM.Nekhoroshev
