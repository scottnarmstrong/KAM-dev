/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quadratic.PairIdentify
public import KAM.Planetary.SecularForm.Analytic

/-!
# Quadratic part: the pair average near the circular point

Blueprint P, Part 8, `stepP:p8:qf-pair` (package S8-Q). Near `(u, v) = 0` the literal pair average
`pairSlowSecular D i j I J` is the two-planet secular function; hence it is real analytic there and
inherits the symmetries of `secular`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
namespace SecularForm
variable {n : ℕ}

/-- The two-planet slow point with actions `(I, J)` and `(u, v) = ((ξᵢ, ηᵢ), (ξⱼ, ηⱼ))`. -/
def embedSlow (I J : ℝ) (w : Vec 2 × Vec 2) : Slow 2 :=
  (![w.1 0, w.2 0], ![I, J], ![w.1 1, w.2 1])

theorem continuous_embedSlow (I J : ℝ) : Continuous (embedSlow I J) := by
  unfold embedSlow
  refine Continuous.prodMk ?_ (continuous_const.prodMk ?_)
  all_goals
    rw [continuous_pi_iff]
    intro c; fin_cases c <;> simp <;> fun_prop

theorem analyticAt_embedSlow (I J : ℝ) (w : Vec 2 × Vec 2) : AnalyticAt ℝ (embedSlow I J) w := by
  unfold embedSlow
  have hfst : ∀ k : Fin 2, AnalyticAt ℝ (fun w : Vec 2 × Vec 2 => w.1 k) w := fun k =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).comp
      (ContinuousLinearMap.fst ℝ (Vec 2) (Vec 2))).analyticAt w
  have hsnd : ∀ k : Fin 2, AnalyticAt ℝ (fun w : Vec 2 × Vec 2 => w.2 k) w := fun k =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).comp
      (ContinuousLinearMap.snd ℝ (Vec 2) (Vec 2))).analyticAt w
  refine AnalyticAt.prod (AnalyticAt.pi fun c => ?_) (AnalyticAt.prod analyticAt_const
    (AnalyticAt.pi fun c => ?_))
  · fin_cases c
    · simpa using hfst 0
    · simpa using hsnd 0
  · fin_cases c
    · simpa using hfst 1
    · simpa using hsnd 1

theorem mem_slowDom_of_realDisc (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a) {x : Slow n} (hx : x ∈ realDisc D a r) : x ∈ slowDom D := by
  rw [mem_slowDom_iff]
  intro i
  have h := hx i
  have h1 := rho_le_half D a i
  have h2 := rho_le_sqrt D a i
  have hpos := action_pos D ha i
  simp only [inclusion, Complex.norm_real, Real.norm_eq_abs] at h
  obtain ⟨hξ, hΛ, hη⟩ := h
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hΛ
  have hr0 : 0 ≤ r := (abs_nonneg _).trans hξ.le
  have hΛ' := abs_lt.1 hΛ
  refine ⟨by linarith, ?_⟩
  have hs : r ^ 2 ≤ action D a i / 256 := by
    have hsq : √(action D a i) ^ 2 = action D a i := Real.sq_sqrt hpos.le
    have : r ≤ √(action D a i) / 16 := by linarith
    nlinarith
  have hξ2 : x.1 i ^ 2 < r ^ 2 := by nlinarith [abs_lt.1 hξ, sq_abs (x.1 i)]
  have hη2 : x.2.2 i ^ 2 < r ^ 2 := by nlinarith [abs_lt.1 hη, sq_abs (x.2.2 i)]
  linarith

theorem pairSeparated_of_realDisc (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a)
    (hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re)
    {x : Slow n} (hx : x ∈ realDisc D a r) : PairSeparated D x := by
  intro i j hij s s' heq
  classical
  set t : Vec n := Function.update (fun _ => s') i s with ht
  have hti : t i = s := by simp [ht]
  have htj : t j = s' := by simp [ht, hij.ne']
  have h1 := hsep t (inclusion x) hx i j hij
  rw [separationC_inclusion D ha hr hx t i j, Complex.ofReal_re] at h1
  have hb : ∀ k, bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 k =
      pairPos D x k (t k) := fun k => by
    rw [poincareProd_assemble, bodyVector_ofPlanets_fst]
    simp [pairPos]
  rw [hb i, hb j, hti, htj, heq, sub_self] at h1
  have h0 : planeSq (0 : Fin 2 → ℝ) = 0 := by simp [planeSq]
  rw [h0] at h1
  have : 0 < (a j - a i) ^ 2 / 2 := by
    have := ha.2 hij
    positivity
  linarith

theorem pairData_self (D : Data 2) : pairData D 0 1 = D := by
  obtain ⟨G, m0, m, hG, hm0, hm, hn⟩ := D
  simp only [pairData, Data.mk.injEq, true_and]
  funext k; fin_cases k <;> rfl

theorem pairSlow_embedSlow (I J : ℝ) (w : Vec 2 × Vec 2) :
    pairSlow (embedSlow I J w) 0 1 = embedSlow I J w := by
  unfold pairSlow embedSlow
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

theorem pairSlowSecular_pairData (D : Data n) (i j : Fin n) (I J : ℝ) (w : Vec 2 × Vec 2) :
    pairSlowSecular (pairData D i j) 0 1 I J w = pairSlowSecular D i j I J w := by
  simp [pairSlowSecular, pairData]

theorem secular_embedSlow_eq (D : Data n) (i j : Fin n) (I J : ℝ) (w : Vec 2 × Vec 2)
    (hw : embedSlow I J w ∈ slowDom (pairData D i j))
    (hsep : PairSeparated (pairData D i j) (embedSlow I J w)) :
    secular (pairData D i j) false (embedSlow I J w) = pairSlowSecular D i j I J w := by
  have h := secular_pair_eq (pairData D i j) hw (i := 0) (j := 1)
    (hsep 0 1 (by decide))
  rw [pairData_self, pairSlow_embedSlow] at h
  rw [h, pairSlowSecular_pairData]
  congr 1
  refine Prod.ext ?_ ?_ <;> ext k <;> fin_cases k <;> rfl

theorem axes_pair {a : Vec n} (ha : a ∈ axes n) {i j : Fin n} (hij : i < j) :
    (![a i, a j] : Vec 2) ∈ axes 2 := by
  refine ⟨fun k => by fin_cases k <;> simp [ha.1], ?_⟩
  intro k l hkl
  fin_cases k <;> fin_cases l <;> simp_all [ha.2 hij]

theorem action_pair (D : Data n) (a : Vec n) (i j : Fin n) :
    action (pairData D i j) ![a i, a j] 0 = action D a i ∧
    action (pairData D i j) ![a i, a j] 1 = action D a j := by
  simp [action, pairData]

/-- The neighbourhood of the circular point on which the pair average is the two-planet secular
function: the data of `perturbation_analytic` for the pair `(i, j)`. -/
theorem exists_pair_nbhd (D : Data n) {a : Vec n} (ha : a ∈ axes n) {i j : Fin n} (hij : i < j) :
    ∃ W : Set (Vec 2 × Vec 2), W ∈ 𝓝 (0 : Vec 2 × Vec 2) ∧
      AnalyticAt ℝ (secular (pairData D i j) false)
        (embedSlow (action D a i) (action D a j) 0) ∧
      ∀ w ∈ W, embedSlow (action D a i) (action D a j) w ∈ slowDom (pairData D i j) ∧
        PairSeparated (pairData D i j) (embedSlow (action D a i) (action D a j) w) := by
  have ha2 := axes_pair ha hij
  obtain ⟨hA0, hA1⟩ := action_pair D a i j
  obtain ⟨r, hr0, hrho, hsepC, hall⟩ := perturbation_analytic (pairData D i j) ha2
  have hA := (hall false).2.2.2.2.1
  have hopen := isOpen_realDisc (pairData D i j) ![a i, a j] hr0
  have h0 : embedSlow (action D a i) (action D a j) 0 ∈
      realDisc (pairData D i j) ![a i, a j] r := by
    intro k
    fin_cases k
    · simp [embedSlow, inclusion, hA0, hr0]
    · simp [embedSlow, inclusion, hA1, hr0]
  refine ⟨embedSlow (action D a i) (action D a j) ⁻¹' realDisc (pairData D i j) ![a i, a j] r,
    (hopen.preimage (continuous_embedSlow _ _)).mem_nhds h0, hA _ h0, fun w hw => ⟨?_, ?_⟩⟩
  · exact mem_slowDom_of_realDisc _ ha2 hrho hw
  · exact pairSeparated_of_realDisc _ ha2 hrho hsepC hw

theorem analyticAt_pairSlowSecular (D : Data n) {a : Vec n} (ha : a ∈ axes n) {i j : Fin n}
    (hij : i < j) : AnalyticAt ℝ (pairSlowSecular D i j (action D a i) (action D a j)) 0 := by
  obtain ⟨W, hW, hA, hgood⟩ := exists_pair_nbhd D ha hij
  have hc := hA.comp (analyticAt_embedSlow (action D a i) (action D a j) 0)
  refine hc.congr ?_
  filter_upwards [hW] with w hw
  exact secular_embedSlow_eq D i j _ _ w (hgood w hw).1 (hgood w hw).2

/-- The reflection `η ↦ -η` of both planets, on `(u, v)`. -/
def pairReflect (w : Vec 2 × Vec 2) : Vec 2 × Vec 2 := (![w.1 0, -w.1 1], ![w.2 0, -w.2 1])

/-- The quarter turn of both planets, on `(u, v)`. -/
def pairQuarter (w : Vec 2 × Vec 2) : Vec 2 × Vec 2 := (![-w.1 1, w.1 0], ![-w.2 1, w.2 0])

theorem continuous_pairReflect : Continuous pairReflect := by
  unfold pairReflect
  refine Continuous.prodMk ?_ ?_ <;> rw [continuous_pi_iff] <;> intro c <;> fin_cases c <;>
    simp <;> fun_prop

theorem continuous_pairQuarter : Continuous pairQuarter := by
  unfold pairQuarter
  refine Continuous.prodMk ?_ ?_ <;> rw [continuous_pi_iff] <;> intro c <;> fin_cases c <;>
    simp <;> fun_prop

theorem pairReflect_zero : pairReflect 0 = 0 := by
  ext k <;> fin_cases k <;> simp [pairReflect]

theorem pairQuarter_zero : pairQuarter 0 = 0 := by
  ext k <;> fin_cases k <;> simp [pairQuarter]

theorem pairSlowSecular_reflect (D : Data n) {a : Vec n} (ha : a ∈ axes n) {i j : Fin n}
    (hij : i < j) : ∀ᶠ w in 𝓝 (0 : Vec 2 × Vec 2),
      pairSlowSecular D i j (action D a i) (action D a j) (pairReflect w) =
        pairSlowSecular D i j (action D a i) (action D a j) w := by
  obtain ⟨W, hW, -, hgood⟩ := exists_pair_nbhd D ha hij
  have hW' : ∀ᶠ w in 𝓝 (0 : Vec 2 × Vec 2), pairReflect w ∈ W :=
    (continuous_pairReflect.continuousAt.eventually (by rw [pairReflect_zero]; exact hW))
  filter_upwards [hW, hW'] with w hw hw'
  rw [← secular_embedSlow_eq D i j _ _ w (hgood w hw).1 (hgood w hw).2,
    ← secular_embedSlow_eq D i j _ _ _ (hgood _ hw').1 (hgood _ hw').2]
  have := (evenness (pairData D i j) (hgood w hw).1 false 0).2.1
  convert this using 2
  unfold embedSlow pairReflect
  simp only [Prod.mk.injEq, true_and]
  constructor <;> (ext k; fin_cases k <;> simp)

theorem pairSlowSecular_quarter (D : Data n) {a : Vec n} (ha : a ∈ axes n) {i j : Fin n}
    (hij : i < j) : ∀ᶠ w in 𝓝 (0 : Vec 2 × Vec 2),
      pairSlowSecular D i j (action D a i) (action D a j) (pairQuarter w) =
        pairSlowSecular D i j (action D a i) (action D a j) w := by
  obtain ⟨W, hW, -, hgood⟩ := exists_pair_nbhd D ha hij
  have hW' : ∀ᶠ w in 𝓝 (0 : Vec 2 × Vec 2), pairQuarter w ∈ W :=
    (continuous_pairQuarter.continuousAt.eventually (by rw [pairQuarter_zero]; exact hW))
  filter_upwards [hW, hW'] with w hw hw'
  rw [← secular_embedSlow_eq D i j _ _ w (hgood w hw).1 (hgood w hw).2,
    ← secular_embedSlow_eq D i j _ _ _ (hgood _ hw').1 (hgood _ hw').2]
  have := (evenness (pairData D i j) (hgood w hw).1 false (π / 2)).2.2.2
  convert this using 2
  unfold embedSlow pairQuarter rotateSlow rot
  simp
  ext k; fin_cases k <;> simp

end SecularForm
end KAM.Planetary
end
