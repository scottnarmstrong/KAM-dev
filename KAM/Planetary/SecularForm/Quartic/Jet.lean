/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.Coefficients

/-!
# Secular form: the quartic jet of the fixed-model secular function

Blueprint P, Part 8, `stepP:p8:q4-str`: the fourth derivative of `slowSecular D false I` at `u = 0`
is the sum over pairs `i < j` of the six-monomial quartic parts of the pair averages.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

variable {n : ℕ}

/-- The slow coordinates `((ξᵢ, ηᵢ), (ξⱼ, ηⱼ))` of the pair `(i, j)`. -/
def pairProjLM (i j : Fin n) : (Vec n × Vec n) →ₗ[ℝ] PairW where
  toFun u := (![u.1 i, u.2 i], ![u.1 j, u.2 j])
  map_add' p q := by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;> simp
  map_smul' c p := by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;> simp

def pairProj (i j : Fin n) : (Vec n × Vec n) →L[ℝ] PairW :=
  LinearMap.toContinuousLinearMap (pairProjLM i j)

theorem pairProj_apply (i j : Fin n) (u : Vec n × Vec n) :
    pairProj i j u = (![u.1 i, u.2 i], ![u.1 j, u.2 j]) := rfl

theorem action_axes_lt (D : Data n) {a : Vec n} (ha : a ∈ axes n) {i j : Fin n} (hij : i < j) :
    action D a i ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) <
      action D a j ^ 2 / (D.m j ^ 2 * (D.G * D.m0)) := by
  rw [action_sq_div D ha i, action_sq_div D ha j]
  exact ha.2 hij

theorem quartic_jet (D : Data n) {I : Vec n} (hI : I ∈ actionDomain D) (u : Vec n × Vec n) :
    iteratedFDeriv ℝ 4 (slowSecular D false I) 0 (fun _ => u) / 24 =
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), ∑ k,
        quarticCoeff D i j (I i, I j) k * quarticMonomials ![u.1 i, u.2 i] ![u.1 j, u.2 j] k := by
  obtain ⟨a, ha, rfl⟩ := hI
  obtain ⟨r, hr, hrho, hsep, hb⟩ := perturbation_analytic D ha
  have hpos : ∀ i, 0 < action D a i := fun i => action_pos D ha i
  let emb : Vec n × Vec n → Slow n := fun u => (u.1, action D a, u.2)
  have hemb : Continuous emb := by fun_prop
  have hopen : IsOpen (emb ⁻¹' realDisc D a r) := (isOpen_realDisc D a hr).preimage hemb
  have hx0 : ((0 : Vec n), action D a, (0 : Vec n)) ∈ realDisc D a r := by
    refine fun i => ⟨?_, ?_, ?_⟩ <;> simp [inclusion, hr]
  set f : Fin n → Fin n → PairW → ℝ := fun i j w =>
    pairSlowSecular D i j (action D a i) (action D a j) w with hf
  have hsum : slowSecular D false (action D a) =ᶠ[𝓝 (0 : Vec n × Vec n)]
      fun u => ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), f i j (pairProj i j u) := by
    filter_upwards [hopen.mem_nhds (show (0 : Vec n × Vec n) ∈ emb ⁻¹' realDisc D a r from hx0)]
      with u hu
    exact secular_false_eq_pairs D ha hrho hsep hu
  have hcdAt : ∀ i j, i < j →
      ContDiffAt ℝ 4 (fun u : Vec n × Vec n => f i j (pairProj i j u)) 0 := by
    intro i j hij
    obtain ⟨U, hU, h0, hcd⟩ := pair_contDiffOn D i j (hpos i) (hpos j) (action_axes_lt D ha hij)
    have : ContDiffAt ℝ 4 (f i j) (pairProj i j 0) := by
      rw [map_zero]; exact hcd.contDiffAt (hU.mem_nhds h0)
    exact this.comp 0 (pairProj i j).contDiff.contDiffAt
  have hjet : ∀ i j, i < j →
      iteratedFDeriv ℝ 4 (fun u : Vec n × Vec n => f i j (pairProj i j u)) 0 (fun _ => u) =
        24 * ∑ k, quarticCoeff D i j (action D a i, action D a j) k *
          quarticMonomials ![u.1 i, u.2 i] ![u.1 j, u.2 j] k := by
    intro i j hij
    have hab := action_axes_lt D ha hij
    obtain ⟨U, hU, h0, hcd⟩ := pair_contDiffOn D i j (hpos i) (hpos j) hab
    have key := iteratedFDeriv_comp_clm_of_isOpen hU hcd (pairProj i j) (x := 0)
      (by rw [map_zero]; exact h0) (le_refl 4)
    have h1 := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Vec n × Vec n) ℝ =>
      T (fun _ => u)) key
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero] at h1
    have e := pairQuartic_eq D i j (hpos i) (hpos j) hab (pairProj i j u)
    unfold pairQuartic at e
    have e2 : iteratedFDeriv ℝ 4 (fun u : Vec n × Vec n => f i j (pairProj i j u)) 0
        (fun _ => u) = iteratedFDeriv ℝ 4 (fun w' : PairW => f i j w') 0
        (fun _ => pairProj i j u) := h1
    rw [e2]
    have : iteratedFDeriv ℝ 4 (fun w' : PairW => f i j w') 0 (fun _ => pairProj i j u) =
        24 * (iteratedFDeriv ℝ 4 (fun w' : PairW => f i j w') 0
          (fun _ => pairProj i j u) / 24) := by
      ring
    rw [this]
    congr 1
  rw [(hsum.iteratedFDeriv ℝ 4).self_of_nhds,
    iteratedFDeriv_fun_sum_apply (fun i _ => ContDiffAt.sum fun j hj =>
      hcdAt i j (Finset.mem_filter.1 hj).2),
    sum_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_fun_sum_apply (fun j hj => hcdAt i j (Finset.mem_filter.1 hj).2),
    sum_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hjet i j (Finset.mem_filter.1 hj).2]
  ring

end SecularForm
end KAM.Planetary
end
