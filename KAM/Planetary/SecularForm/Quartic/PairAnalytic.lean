/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.PairDecomp

/-!
# Secular form: joint analyticity of the pair average

Blueprint P, Part 8, `stepP:p8:q4-str`: the literal pair average `pairSlowSecular` is the secular
function of the two-planet system built from the pair data, hence jointly real analytic in the two
actions and the four slow coordinates near every point with `aᵢ < aⱼ`, `u = 0`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

variable {n : ℕ}

/-- The two-planet data of the pair `(i, j)`. -/
def q4_pairData (D : Data n) (i j : Fin n) : Data 2 where
  G := D.G
  m0 := D.m0
  m := ![D.m i, D.m j]
  hG := D.hG
  hm0 := D.hm0
  hm := fun k => by fin_cases k <;> simp [D.hm i, D.hm j]
  hn := by norm_num

/-- The pair slow variables `((I, J), ((ξᵢ, ηᵢ), (ξⱼ, ηⱼ)))` as a point of `Slow 2`. -/
def pairEmbLM : (ℝ × ℝ) × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) →ₗ[ℝ] Slow 2 where
  toFun p := (![p.2.1 0, p.2.2 0], ![p.1.1, p.1.2], ![p.2.1 1, p.2.2 1])
  map_add' p q := by
    refine Prod.ext (funext fun k => ?_) (Prod.ext (funext fun k => ?_) (funext fun k => ?_)) <;>
      fin_cases k <;> simp
  map_smul' c p := by
    refine Prod.ext (funext fun k => ?_) (Prod.ext (funext fun k => ?_) (funext fun k => ?_)) <;>
      fin_cases k <;> simp

def pairEmb : (ℝ × ℝ) × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) →L[ℝ] Slow 2 :=
  LinearMap.toContinuousLinearMap pairEmbLM

theorem pairEmb_apply (p : (ℝ × ℝ) × ((Fin 2 → ℝ) × (Fin 2 → ℝ))) :
    pairEmb p = (![p.2.1 0, p.2.2 0], ![p.1.1, p.1.2], ![p.2.1 1, p.2.2 1]) := rfl

theorem vec2_eta (u : Fin 2 → ℝ) : (![u 0, u 1] : Fin 2 → ℝ) = u := by
  ext k; fin_cases k <;> rfl

theorem q4_pairSlowSecular_pairData (D : Data n) (i j : Fin n) (I J : ℝ)
    (w : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    pairSlowSecular (q4_pairData D i j) 0 1 I J w = pairSlowSecular D i j I J w := by
  simp [pairSlowSecular, q4_pairData]

theorem q4_action_axis (D : Data n) {I : Vec n} (hI : ∀ i, 0 < I i) : action D (axis D I) = I := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  funext i
  have h1 : D.G * D.m0 * (I i ^ 2 / (D.m i ^ 2 * (D.G * D.m0))) = (I i / D.m i) ^ 2 := by
    field_simp [(D.hm i).ne', D.hG.ne', D.hm0.ne']
  have h2 : D.m i ≠ 0 := (D.hm i).ne'
  simp only [action, axis, h1]
  rw [Real.sqrt_sq (div_pos (hI i) (D.hm i)).le]
  field_simp

theorem axis_mem_axes (D : Data n) {I : Vec n} (hI : ∀ i, 0 < I i)
    (hmono : ∀ i j, i < j → axis D I i < axis D I j) : axis D I ∈ axes n :=
  ⟨fun i => by
    have := D.hG; have := D.hm0; have := D.hm i; have := hI i
    unfold axis; positivity, fun i j hij => hmono i j hij⟩

/-- The real neighbourhood of `((I₀, J₀), 0)` on which the pair average is the secular function of
the two-planet system. -/
theorem pair_secular_nbhd (D : Data n) (i j : Fin n) {I0 J0 : ℝ} (hI : 0 < I0)
    (hJ : 0 < J0)
    (hab : I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) < J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) :
    ∃ N : Set ((ℝ × ℝ) × ((Fin 2 → ℝ) × (Fin 2 → ℝ))), IsOpen N ∧ ((I0, J0), 0) ∈ N ∧
      (∀ p ∈ N, pairEmb p ∈ slowDom (q4_pairData D i j)) ∧
      (∀ p ∈ N, pairSlowSecular D i j p.1.1 p.1.2 p.2 =
        secular (q4_pairData D i j) false (pairEmb p)) ∧
      (AnalyticOnNhd ℝ (fun p => secular (q4_pairData D i j) false (pairEmb p)) N ∧
        ∀ p ∈ N, Continuous fun q : ℝ × ℝ =>
          pairKernel (q4_pairData D i j) (pairEmb p) 0 1 q.1 q.2) := by
  set D2 := q4_pairData D i j with hD2
  set a2 : Vec 2 := axis D2 ![I0, J0] with ha2
  have hpos : ∀ k, 0 < (![I0, J0] : Vec 2) k := fun k => by fin_cases k <;> simpa
  have hmono : ∀ k l : Fin 2, k < l → axis D2 ![I0, J0] k < axis D2 ![I0, J0] l := by
    intro k l hkl
    have : k = 0 ∧ l = 1 := by
      fin_cases k <;> fin_cases l <;> simp_all
    obtain ⟨rfl, rfl⟩ := this
    simpa [axis, hD2, q4_pairData] using hab
  have ha : a2 ∈ axes 2 := axis_mem_axes D2 hpos hmono
  have hact : action D2 a2 = ![I0, J0] := q4_action_axis D2 hpos
  obtain ⟨r, hr, hrho, hsep, hb⟩ := perturbation_analytic D2 ha
  have hAn := (hb false).2.2.2.2.1
  have hbase : pairEmb ((I0, J0), 0) ∈ realDisc D2 a2 r := by
    intro k
    refine ⟨?_, ?_, ?_⟩ <;> fin_cases k <;>
      simp [pairEmb_apply, inclusion, hact, hr]
  refine ⟨pairEmb ⁻¹' realDisc D2 a2 r, (isOpen_realDisc D2 a2 hr).preimage pairEmb.continuous,
    hbase, fun p hp => realDisc_subset_slowDom D2 ha hrho hp, fun p hp => ?_,
    ⟨fun p hp => (hAn _ hp).comp (pairEmb.analyticAt _), fun p hp => ?_⟩⟩
  swap
  · exact continuous_pairKernel_comp D2 ha hrho hsep hp (i := 0) (j := 1) (by decide)
      (f := fun q : ℝ × ℝ => q.1) (g := fun q : ℝ × ℝ => q.2) continuous_fst continuous_snd
  rw [secular_false_eq_pairs D2 ha hrho hsep hp]
  have h0 : (Finset.univ.filter (fun j : Fin 2 => 0 < j)) = {1} := by decide
  have h1 : (Finset.univ.filter (fun j : Fin 2 => 1 < j)) = ∅ := by decide
  simp only [Fin.sum_univ_two, pairEmb_apply, h0, h1, Finset.sum_singleton,
    Finset.sum_empty, add_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, vec2_eta, Prod.mk.eta]
  exact (q4_pairSlowSecular_pairData D i j _ _ _).symm

theorem q4_analyticAt_pairSlowSecular (D : Data n) (i j : Fin n) {I0 J0 : ℝ} (hI : 0 < I0)
    (hJ : 0 < J0)
    (hab : I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) < J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) :
    AnalyticAt ℝ (fun p : (ℝ × ℝ) × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
      pairSlowSecular D i j p.1.1 p.1.2 p.2) ((I0, J0), 0) := by
  obtain ⟨N, hN, h0, -, hF, hA, -⟩ := pair_secular_nbhd D i j hI hJ hab
  refine (hA _ h0).congr ?_
  filter_upwards [hN.mem_nhds h0] with p hp
  exact (hF p hp).symm

end SecularForm
end KAM.Planetary
end
