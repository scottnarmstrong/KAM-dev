/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PatchHessian
public import KAM.Planetary.SecularForm.Analytic

/-!
# Complex-angle separation and the uniform strip (P11A-P2c, `stepP:p11:hc-strip`)

The complexified squared separation `p11hsSep` of two planets, with a COMPLEX angle `λ`
(`SecularForm.separationC` only has real angles): it agrees with `separationC` at real angles,
is `2π`-periodic in each angle, and `p11hs_strip` is the uniform strip bound
`Re s_ij ≥ (a_j - a_i)² / 4` for `|Im λ_i| ≤ 2π σ'` on the polydisc, obtained from the real-angle
bound `exists_radius` by compactness of `[0, 2π]ⁿ × closedBall` and periodicity.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler SecularForm

section Geometry

variable {n : ℕ}

/-- The `i`-th complex planet block with complex angle `lam i`. -/
def p11hsBlock (lam : CVec n) (x : CSlow n) (i : Fin n) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  (![lam i, x.1 i], ![x.2.1 i, x.2.2 i])

/-- The `i`-th planet's complexified plane position/momentum at complex angle. -/
def p11hsPlanet (D : Data n) (lam : CVec n) (x : CSlow n) (i : Fin n) :
    (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  poincareC (D.m i) (D.G * D.m0) (p11hsBlock lam x i)

/-- The complexified squared separation at complex angles. -/
def p11hsSep (D : Data n) (lam : CVec n) (x : CSlow n) (i j : Fin n) : ℂ :=
  ∑ c : Fin 2, ((p11hsPlanet D lam x i).1 c - (p11hsPlanet D lam x j).1 c) ^ 2

theorem p11hsSep_real (D : Data n) (t : Vec n) (x : CSlow n) (i j : Fin n) :
    p11hsSep D (fun l => (t l : ℂ)) x i j = separationC D t x i j := rfl

theorem p11hsBlock_mem_nbhd (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a) {lam : CVec n} {x : CSlow n} (hx : x ∈ polydisc D a r)
    (hl : ∀ l, |(lam l).im| < 1 / 4) (i : Fin n) :
    p11hsBlock lam x i ∈ poincareNbhd (action D a i) := by
  have h := blockC_mem_nbhd D ha hr (t := fun _ => 0) hx i
  refine ⟨?_, h.2.1, h.2.2.1, h.2.2.2⟩
  simpa [p11hsBlock] using hl i

theorem continuousOn_p11hsSep (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a) (i j : Fin n) :
    ContinuousOn (fun z : CVec n × CSlow n => p11hsSep D z.1 z.2 i j)
      {z | (∀ l, |(z.1 l).im| < 1 / 4) ∧ z.2 ∈ polydisc D a r} := by
  have hpl : ∀ k : Fin n, ContinuousOn (fun z : CVec n × CSlow n => p11hsPlanet D z.1 z.2 k)
      {z | (∀ l, |(z.1 l).im| < 1 / 4) ∧ z.2 ∈ polydisc D a r} := by
    intro k
    have hΛ := action_pos D ha k
    have h := (poincare_holomorphic (m := D.m k) (κ := D.G * D.m0) (Λo := action D a k)
      (D.hm k) (mul_pos D.hG D.hm0) hΛ).2.2.1
    have hc : Continuous (fun z : CVec n × CSlow n => p11hsBlock z.1 z.2 k) := by
      refine Continuous.prodMk (continuous_pi fun c => ?_) (continuous_pi fun c => ?_) <;>
        fin_cases c <;> simp <;> fun_prop
    exact h.continuousOn.comp hc.continuousOn fun z hz =>
      p11hsBlock_mem_nbhd D ha hr hz.2 hz.1 k
  unfold p11hsSep
  refine continuousOn_finsetSum _ fun c _ => ?_
  have hi := (continuous_apply c).comp_continuousOn
    ((continuous_fst).comp_continuousOn (hpl i))
  have hj := (continuous_apply c).comp_continuousOn
    ((continuous_fst).comp_continuousOn (hpl j))
  exact (hi.sub hj).pow 2

/-- Integer `2π`-shifts of the angle of one block leave the complex chart unchanged. -/
theorem p11hs_poincareC_shift {m κ Λo : ℝ} (hm : 0 < m) (hκ : 0 < κ) (hΛ : 0 < Λo)
    {w : (Fin 2 → ℂ) × (Fin 2 → ℂ)} (hw : w ∈ poincareNbhd Λo) (k : ℤ) :
    poincareC m κ (Function.update w.1 0 (w.1 0 + 2 * π * k), w.2) = poincareC m κ w := by
  have hper := (poincare_holomorphic hm hκ hΛ).2.2.2.1
  have hmem : ∀ k : ℤ, (Function.update w.1 0 (w.1 0 + 2 * π * k), w.2) ∈ poincareNbhd Λo := by
    intro k
    obtain ⟨h1, h2, h3, h4⟩ := hw
    refine ⟨?_, h2, ?_, ?_⟩
    · simpa using h1
    · simpa [Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)] using h3
    · simpa using h4
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have h := (hper _ (hmem k)).2
    rw [← ih, ← h]
    congr 2
    simp only [Function.update_self, Function.update_idem]
    push_cast
    ring_nf
  | pred k ih =>
    have h := (hper _ (hmem (-(k : ℤ) - 1))).2
    rw [← ih, ← h]
    congr 2
    simp only [Function.update_self, Function.update_idem]
    push_cast
    ring_nf

/-- The planet's chart is unchanged by replacing the angle by an integer `2π`-shift. -/
theorem p11hsPlanet_shift (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a) {lam : CVec n} {x : CSlow n} (hx : x ∈ polydisc D a r)
    (hl : ∀ l, |(lam l).im| < 1 / 4) (k : Fin n → ℤ) (i : Fin n) :
    p11hsPlanet D (fun l => lam l + 2 * π * (k l : ℂ)) x i = p11hsPlanet D lam x i := by
  have h := p11hs_poincareC_shift (m := D.m i) (κ := D.G * D.m0) (Λo := action D a i)
    (D.hm i) (mul_pos D.hG D.hm0) (action_pos D ha i) (p11hsBlock_mem_nbhd D ha hr hx hl i) (k i)
  unfold p11hsPlanet
  rw [← h]
  congr 1
  refine Prod.ext (funext fun c => ?_) rfl
  fin_cases c <;> simp [p11hsBlock, Function.update_of_ne]

theorem p11hsSep_shift (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a) {lam : CVec n} {x : CSlow n} (hx : x ∈ polydisc D a r)
    (hl : ∀ l, |(lam l).im| < 1 / 4) (k : Fin n → ℤ) (i j : Fin n) :
    p11hsSep D (fun l => lam l + 2 * π * (k l : ℂ)) x i j = p11hsSep D lam x i j := by
  unfold p11hsSep
  rw [p11hsPlanet_shift D ha hr hx hl k i, p11hsPlanet_shift D ha hr hx hl k j]

/-- Topological core: continuity of `Re g` along `(τ, t, x) ↦ (t + iτ, x)` at `τ = 0`. -/
theorem p11hs_continuousAt_re {g : CVec n × CSlow n → ℂ} {U : Set (CVec n × CSlow n)}
    (hU : IsOpen U) (hg : ContinuousOn g U) {y : Vec n × CSlow n}
    (h0 : ((fun l => (y.1 l : ℂ)), y.2) ∈ U) :
    ContinuousAt (fun p : Vec n × (Vec n × CSlow n) =>
      (g ((fun l => (p.2.1 l : ℂ) + (p.1 l : ℂ) * Complex.I), p.2.2)).re) (0, y) := by
  have hmap : Continuous (fun p : Vec n × (Vec n × CSlow n) =>
      ((fun l => (p.2.1 l : ℂ) + (p.1 l : ℂ) * Complex.I : CVec n), p.2.2)) := by
    refine Continuous.prodMk (continuous_pi fun l => ?_) (by fun_prop)
    fun_prop
  have h0' : (fun p : Vec n × (Vec n × CSlow n) =>
      ((fun l => (p.2.1 l : ℂ) + (p.1 l : ℂ) * Complex.I : CVec n), p.2.2)) (0, y) ∈ U := by
    convert h0 using 2
    funext l; simp
  have h1 : ContinuousAt g ((fun p : Vec n × (Vec n × CSlow n) =>
      ((fun l => (p.2.1 l : ℂ) + (p.1 l : ℂ) * Complex.I : CVec n), p.2.2)) (0, y)) :=
    hg.continuousAt (hU.mem_nhds h0')
  have h2 := ContinuousAt.comp (f := fun p : Vec n × (Vec n × CSlow n) =>
      ((fun l => (p.2.1 l : ℂ) + (p.1 l : ℂ) * Complex.I : CVec n), p.2.2)) (x := (0, y))
    h1 hmap.continuousAt
  exact Complex.continuous_re.continuousAt.comp h2

theorem isOpen_p11hsU (D : Data n) {a : Vec n} {r0 : ℝ} (hr0 : 0 < r0) :
    IsOpen {z : CVec n × CSlow n | (∀ l, |(z.1 l).im| < 1 / 4) ∧ z.2 ∈ polydisc D a r0} := by
  have h1 : IsOpen {z : CVec n × CSlow n | ∀ l, |(z.1 l).im| < 1 / 4} := by
    have : {z : CVec n × CSlow n | ∀ l, |(z.1 l).im| < 1 / 4} =
        ⋂ l, {z | |(z.1 l).im| < 1 / 4} := by ext; simp
    rw [this]
    exact isOpen_iInter_of_finite fun l => isOpen_lt (by fun_prop) continuous_const
  have h2 : IsOpen (Prod.snd ⁻¹' polydisc D a r0 : Set (CVec n × CSlow n)) := by
    have : IsOpen (polydisc D a r0) := by
      rw [polydisc_eq_ball D a hr0]; exact Metric.isOpen_ball
    exact this.preimage continuous_snd
  exact h1.inter h2

/-- The compact set of real angles in one period and slow coordinates in a closed ball. -/
def p11hsK (D : Data n) (a : Vec n) (r : ℝ) : Set (Vec n × CSlow n) :=
  Set.Icc (0 : Vec n) (fun _ => 2 * π) ×ˢ Metric.closedBall (center D a) r

theorem isCompact_p11hsK (D : Data n) (a : Vec n) (r : ℝ) : IsCompact (p11hsK D a r) :=
  isCompact_Icc.prod (isCompact_closedBall _ _)

/-- Uniform (in the angle) persistence of the real-angle bound for small imaginary parts. -/
theorem p11hs_eventually (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r0 r'' : ℝ}
    (hr0 : 0 < r0) (hrho : r0 < rho D a) (hr''r0 : r'' < r0)
    (hall : ∀ t x, x ∈ polydisc D a r0 → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re) (i j : Fin n) (hij : i < j) :
    ∀ᶠ τ in 𝓝 (0 : Vec n), ∀ y ∈ p11hsK D a r'',
      (a j - a i) ^ 2 / 4 ≤
        (p11hsSep D (fun l => (y.1 l : ℂ) + (τ l : ℂ) * Complex.I) y.2 i j).re := by
  have hball : Metric.closedBall (center D a) r'' ⊆ polydisc D a r0 := by
    rw [polydisc_eq_ball D a hr0]; exact Metric.closedBall_subset_ball hr''r0
  refine (isCompact_p11hsK D a r'').eventually_forall_of_forall_eventually fun y hy => ?_
  have hgap : 0 < (a j - a i) ^ 2 / 4 := by
    have : a i < a j := ha.2 hij
    have : 0 < a j - a i := by linarith
    positivity
  have hyx : y.2 ∈ polydisc D a r0 := hball hy.2
  have hat := p11hs_continuousAt_re (isOpen_p11hsU D hr0) (continuousOn_p11hsSep D ha hrho i j)
    (y := y) ⟨fun l => by simp, hyx⟩
  have hval : (a j - a i) ^ 2 / 4 < (p11hsSep D (fun l => (y.1 l : ℂ)) y.2 i j).re := by
    have := hall y.1 y.2 hyx i j hij
    rw [p11hsSep_real]
    linarith
  have hat' : ContinuousAt (fun p : Vec n × (Vec n × CSlow n) =>
      (p11hsSep D (fun l => (p.2.1 l : ℂ) + (p.1 l : ℂ) * Complex.I) p.2.2 i j).re) (0, y) := hat
  have hval' : (a j - a i) ^ 2 / 4 < (p11hsSep D
      (fun l => (y.1 l : ℂ) + ((0 : Vec n) l : ℂ) * Complex.I) y.2 i j).re := by
    convert hval using 4
    simp
  exact (hat'.eventually (lt_mem_nhds hval')).mono fun _ h => h.le

/-- `hc-strip`: the uniform strip bound `Re s_ij ≥ (a_j - a_i)²/4` on the polydisc of every
radius `r' < r₀` (`r₀` the real-angle radius of `exists_radius`), for all complex angles with
`|Im λ_i| ≤ 2π σ'`, `σ' ≤ min (1/4) (1/(16π))`. -/
theorem p11hs_strip (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 < rho D a ∧ ∀ r' : ℝ, r' < r0 → ∃ σ' : ℝ, 0 < σ' ∧ σ' ≤ 1 / 4 ∧
      2 * π * σ' ≤ 1 / 8 ∧ ∀ lam : CVec n, (∀ l, |(lam l).im| ≤ 2 * π * σ') →
        ∀ x ∈ polydisc D a r', ∀ i j : Fin n, i < j →
          (a j - a i) ^ 2 / 4 ≤ (p11hsSep D lam x i j).re := by
  obtain ⟨r0, hr0, hrho, hall⟩ := exists_radius D ha
  refine ⟨r0, hr0, hrho, fun r' hr' => ?_⟩
  by_cases hr'0 : r' ≤ 0
  · refine ⟨1 / (16 * π), by positivity, ?_, ?_, fun lam _ x hx i j _ => ?_⟩
    · rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
    · field_simp; norm_num
    · exfalso
      have := (hx i).1
      have := norm_nonneg (x.1 i)
      linarith
  push Not at hr'0
  set r'' := (r' + r0) / 2 with hr''
  have hr''r0 : r'' < r0 := by rw [hr'']; linarith
  have hr'r'' : r' < r'' := by rw [hr'']; linarith
  have hev' : ∀ᶠ τ in 𝓝 (0 : Vec n), ∀ i j : Fin n, i < j → ∀ y ∈ p11hsK D a r'',
      (a j - a i) ^ 2 / 4 ≤
        (p11hsSep D (fun l => (y.1 l : ℂ) + (τ l : ℂ) * Complex.I) y.2 i j).re := by
    refine (eventually_all.2 fun i => eventually_all.2 fun j => ?_)
    by_cases hij : i < j
    · exact (p11hs_eventually D ha hr0 hrho hr''r0 hall i j hij).mono fun τ h _ => h
    · exact Eventually.of_forall fun τ h => absurd h hij
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 hev'
  set σ' : ℝ := min (1 / (16 * π)) (ε / (4 * π)) with hσ'
  have hσ0 : 0 < σ' := lt_min (by positivity) (by positivity)
  have hσ1 : 2 * π * σ' ≤ 1 / 8 := by
    calc 2 * π * σ' ≤ 2 * π * (1 / (16 * π)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
      _ = 1 / 8 := by field_simp; norm_num
  have hσε : 2 * π * σ' < ε := by
    calc 2 * π * σ' ≤ 2 * π * (ε / (4 * π)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = ε / 2 := by field_simp; norm_num
      _ < ε := by linarith
  refine ⟨σ', hσ0, ?_, hσ1, fun lam hlam x hx i j hij => ?_⟩
  · calc σ' ≤ 1 / (16 * π) := min_le_left _ _
      _ ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_gt_three]
  have hl4 : ∀ l, |(lam l).im| < 1 / 4 := fun l => by linarith [hlam l]
  have hxb : x ∈ Metric.ball (center D a) r' := by
    rw [← polydisc_eq_ball D a hr'0]; exact hx
  have hxr0 : x ∈ polydisc D a r0 := by
    rw [polydisc_eq_ball D a hr0]
    exact Metric.ball_subset_ball (by linarith) hxb
  -- reduce the real part of the angle to `[0, 2π)`
  set kk : Fin n → ℤ := fun l => ⌊(lam l).re / (2 * π)⌋ with hkk
  set t' : Vec n := fun l => (lam l).re - 2 * π * kk l with ht'
  set τ : Vec n := fun l => (lam l).im with hτ
  have hlam' : (fun l => (t' l : ℂ) + (τ l : ℂ) * Complex.I) =
      fun l => lam l + 2 * π * ((-kk l : ℤ) : ℂ) := by
    funext l
    apply Complex.ext <;> simp [ht', hτ]
    ring
  have hmem : (t', x) ∈ p11hsK D a r'' := by
    refine ⟨⟨fun l => ?_, fun l => ?_⟩, ?_⟩
    · have := Int.floor_le ((lam l).re / (2 * π))
      have h2 : 2 * π * (kk l : ℝ) ≤ (lam l).re := by
        have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * π)).1 this
        linarith
      show 0 ≤ (lam l).re - 2 * π * kk l
      linarith
    · have := Int.lt_floor_add_one ((lam l).re / (2 * π))
      have h2 : (lam l).re < 2 * π * ((kk l : ℝ) + 1) := by
        have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * π)).1 this
        linarith
      show (lam l).re - 2 * π * kk l ≤ 2 * π
      nlinarith
    · exact Metric.ball_subset_closedBall (Metric.ball_subset_ball hr'r''.le hxb)
  have hτε : dist τ 0 < ε := by
    rw [dist_zero_right]
    refine (pi_norm_lt_iff hε).2 fun l => ?_
    rw [Real.norm_eq_abs]
    exact lt_of_le_of_lt (hlam l) hσε
  have := hεP hτε i j hij (t', x) hmem
  rw [hlam', p11hsSep_shift D ha hrho hxr0 hl4] at this
  exact this

end Geometry

end KAM.Planetary

end
