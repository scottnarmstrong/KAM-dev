/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Nondegeneracy.DiagonalTensor
public import KAM.Planetary.Nondegeneracy.AnalyticZeros

/-!
# Nondegeneracy: finite type, index and amount, CP09 Lemma 1

Blueprint P, Part 10 (`bpP:p10:finite-type`, `bpP:p10:index-def`, `bpP:p10:cp09-lemma1`): the
literal infimum `betaFamily` of the diagonal jet maxima over a compact parameter set and a compact
patch, the unit sphere, the squared scalar form, the finite-type theorem by compactness, the
least positive index with its monotone amount, and the corollaries for R-nondegenerate maps
(squared, unsquared and product families).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {d m : ℕ}

def betaFamily {C : Type*} (g : C → Vec d → ℝ) (C0 : Set C) (K : Set (Vec d)) (μ : ℕ) : ℝ :=
  sInf ((fun z : C × Vec d => jetMax (g z.1) μ z.2) '' (C0 ×ˢ K))
def sphere (m : ℕ) : Set (Vec m) := {c | length2 c = 1}
def squaredForm (ω : Vec d → Vec m) (c : Vec m) (y : Vec d) : ℝ := (∑ i, c i*ω y i)^2
def betaMu (ω : Vec d → Vec m) (K : Set (Vec d)) (μ : ℕ) : ℝ :=
  betaFamily (squaredForm ω) (sphere m) K μ
/-- No fallback value for an undefined index. -/
def index_def {C : Type*} (g : C → Vec d → ℝ) (C0 : Set C) (K : Set (Vec d))
    (h : ∃ μ : ℕ, 0 < μ ∧ 0 < betaFamily g C0 K μ) : ℕ := Nat.find h

/-! ### Jets: nonnegativity, Lipschitz dependence, the recursion in the order -/

lemma scalarJet_nonneg (g : Vec d → ℝ) (ν : ℕ) (y : Vec d) : 0 ≤ scalarJet g ν y := by
  unfold scalarJet
  split_ifs
  · exact abs_nonneg _
  · exact Real.sSup_nonneg (by rintro r ⟨v, -, rfl⟩; exact abs_nonneg _)

lemma norm_le_one_of_length2 {v : Vec d} (hv : length2 v = 1) : ‖v‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Real.norm_eq_abs]
  refine Real.abs_le_sqrt ?_ |>.trans hv.le
  have := Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg (v j))
    (Finset.mem_univ i)
  simpa using this

/-- The diagonal sup over the Euclidean unit sphere, as a function of the tensor. -/
def jetOp {ν : ℕ} (T : (Fin d → ℝ) [×ν]→L[ℝ] ℝ) : ℝ :=
  sSup {r | ∃ v : Vec d, length2 v = 1 ∧ r = |T (fun _ => v)|}

lemma abs_diag_le {ν : ℕ} (T : (Fin d → ℝ) [×ν]→L[ℝ] ℝ) {v : Vec d} (hv : length2 v = 1) :
    |T (fun _ => v)| ≤ ‖T‖ := by
  have h1 := T.le_opNorm (fun _ => v)
  have h2 : ∏ _i : Fin ν, ‖v‖ ≤ 1 :=
    by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
       exact pow_le_one₀ (norm_nonneg _) (norm_le_one_of_length2 hv)
  rw [Real.norm_eq_abs] at h1
  calc |T (fun _ => v)| ≤ ‖T‖ * ∏ _i : Fin ν, ‖v‖ := h1
    _ ≤ ‖T‖ * 1 := by gcongr
    _ = ‖T‖ := mul_one _

lemma bddAbove_jetOp {ν : ℕ} (T : (Fin d → ℝ) [×ν]→L[ℝ] ℝ) :
    BddAbove {r | ∃ v : Vec d, length2 v = 1 ∧ r = |T (fun _ => v)|} :=
  ⟨‖T‖, by rintro r ⟨v, hv, rfl⟩; exact abs_diag_le T hv⟩

lemma jetOp_nonneg {ν : ℕ} (T : (Fin d → ℝ) [×ν]→L[ℝ] ℝ) : 0 ≤ jetOp T :=
  Real.sSup_nonneg (by rintro r ⟨v, -, rfl⟩; exact abs_nonneg _)

lemma jetOp_le_add {ν : ℕ} (T T' : (Fin d → ℝ) [×ν]→L[ℝ] ℝ) :
    jetOp T ≤ jetOp T' + ‖T - T'‖ := by
  refine Real.sSup_le ?_ (add_nonneg (jetOp_nonneg T') (norm_nonneg _))
  rintro r ⟨v, hv, rfl⟩
  have h1 : |T (fun _ => v)| ≤ |T' (fun _ => v)| + |(T - T') (fun _ => v)| := by
    have : T (fun _ => v) = T' (fun _ => v) + (T - T') (fun _ => v) := by simp
    rw [this]; exact abs_add_le _ _
  have h2 : |T' (fun _ => v)| ≤ jetOp T' := le_csSup (bddAbove_jetOp T') ⟨v, hv, rfl⟩
  linarith [abs_diag_le (T - T') hv]

lemma jetOp_lipschitz {ν : ℕ} :
    LipschitzWith 1 (jetOp : ((Fin d → ℝ) [×ν]→L[ℝ] ℝ) → ℝ) := by
  refine LipschitzWith.of_dist_le_mul fun T T' => ?_
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · linarith [jetOp_le_add T T']
  · have := jetOp_le_add T' T
    rw [norm_sub_rev] at this
    linarith

lemma scalarJet_continuousOn {C : Type*} [TopologicalSpace C] {g : C → Vec d → ℝ}
    {S : Set (C × Vec d)} (ν : ℕ)
    (hCont : ContinuousOn (fun z : C × Vec d => iteratedFDeriv ℝ ν (g z.1) z.2) S) :
    ContinuousOn (fun z : C × Vec d => scalarJet (g z.1) ν z.2) S := by
  rcases Nat.eq_zero_or_pos ν with rfl | hν
  · have := hCont.norm
    refine this.congr fun z _ => ?_
    simp [scalarJet, norm_iteratedFDeriv_zero]
  · refine (jetOp_lipschitz.continuous.comp_continuousOn hCont).congr fun z _ => ?_
    simp [scalarJet, jetOp, hν.ne']

lemma jetMax_zero (g : Vec d → ℝ) (y : Vec d) : jetMax g 0 y = scalarJet g 0 y := by
  have : {ν : ℕ | ν ≤ 0} = {0} := by ext; simp
  simp [jetMax]

lemma jetMax_succ (g : Vec d → ℝ) (μ : ℕ) (y : Vec d) :
    jetMax g (μ + 1) y = max (jetMax g μ y) (scalarJet g (μ + 1) y) := by
  have h : {ν : ℕ | ν ≤ μ + 1} = insert (μ + 1) {ν : ℕ | ν ≤ μ} := by
    ext ν; simp [Nat.le_succ_iff, or_comm]
  have hfin : ((fun ν => scalarJet g ν y) '' {ν : ℕ | ν ≤ μ}).Finite :=
    (Set.finite_le_nat μ).image _
  unfold jetMax
  rw [h, Set.image_insert_eq, csSup_insert hfin.bddAbove ⟨_, ⟨0, by simp, rfl⟩⟩, max_comm]

lemma jetMax_nonneg (g : Vec d → ℝ) (μ : ℕ) (y : Vec d) : 0 ≤ jetMax g μ y :=
  Real.sSup_nonneg (by rintro r ⟨ν, -, rfl⟩; exact scalarJet_nonneg g ν y)

lemma scalarJet_le_jetMax (g : Vec d → ℝ) {ν μ : ℕ} (h : ν ≤ μ) (y : Vec d) :
    scalarJet g ν y ≤ jetMax g μ y :=
  le_csSup ((((Set.finite_le_nat μ).image _)).bddAbove) ⟨ν, h, rfl⟩

lemma jetMax_mono (g : Vec d → ℝ) (y : Vec d) : Monotone (fun μ => jetMax g μ y) :=
  monotone_nat_of_le_succ fun μ => by
    simp only [jetMax_succ]; exact le_max_left _ _

lemma jetMax_continuousOn {C : Type*} [TopologicalSpace C] {g : C → Vec d → ℝ}
    {S : Set (C × Vec d)}
    (hCont : ∀ ν : ℕ, ContinuousOn (fun z : C × Vec d => iteratedFDeriv ℝ ν (g z.1) z.2) S)
    (μ : ℕ) : ContinuousOn (fun z : C × Vec d => jetMax (g z.1) μ z.2) S := by
  induction μ with
  | zero =>
    simp only [jetMax_zero]; exact scalarJet_continuousOn 0 (hCont 0)
  | succ μ ih =>
    simp only [jetMax_succ]; exact ih.sup (scalarJet_continuousOn _ (hCont _))

/-! ### The infimum `betaFamily` -/

lemma betaFamily_nonneg {C : Type*} (g : C → Vec d → ℝ) (C0 : Set C) (K : Set (Vec d)) (μ : ℕ) :
    0 ≤ betaFamily g C0 K μ :=
  Real.sInf_nonneg (by rintro r ⟨z, -, rfl⟩; exact jetMax_nonneg _ _ _)

lemma betaFamily_le {C : Type*} {g : C → Vec d → ℝ} {C0 : Set C} {K : Set (Vec d)} {μ : ℕ}
    {c : C} (hc : c ∈ C0) {y : Vec d} (hy : y ∈ K) :
    betaFamily g C0 K μ ≤ jetMax (g c) μ y :=
  csInf_le ⟨0, by rintro r ⟨z, -, rfl⟩; exact jetMax_nonneg _ _ _⟩ ⟨(c, y), ⟨hc, hy⟩, rfl⟩

lemma betaFamily_mono {C : Type*} {g : C → Vec d → ℝ} {C0 : Set C} {K : Set (Vec d)}
    (hCn : C0.Nonempty) (hKn : K.Nonempty) : Monotone (betaFamily g C0 K) := by
  intro μ μ' h
  refine le_csInf ((hCn.prod hKn).image _) ?_
  rintro r ⟨z, hz, rfl⟩
  exact (betaFamily_le hz.1 hz.2).trans (jetMax_mono _ _ h)

/-- On a compact nonempty product the infimum is attained. -/
lemma betaFamily_attained {C : Type*} [MetricSpace C] {g : C → Vec d → ℝ} {C0 : Set C}
    {K : Set (Vec d)} (hC : IsCompact C0) (hCn : C0.Nonempty) (hK : IsCompact K)
    (hKn : K.Nonempty) {μ : ℕ}
    (hc : ContinuousOn (fun z : C × Vec d => jetMax (g z.1) μ z.2) (C0 ×ˢ K)) :
    ∃ z ∈ C0 ×ˢ K, betaFamily g C0 K μ = jetMax (g z.1) μ z.2 := by
  obtain ⟨z, hz, hmin⟩ := (hC.prod hK).exists_isMinOn (hCn.prod hKn) hc
  refine ⟨z, hz, ?_⟩
  refine IsLeast.csInf_eq ⟨⟨z, hz, rfl⟩, ?_⟩
  rintro r ⟨w, hw, rfl⟩
  exact hmin hw

theorem index_amount {C : Type*} [MetricSpace C] {g : C → Vec d → ℝ} {C0 : Set C}
    (hC : IsCompact C0) (hCn : C0.Nonempty) {K : Set (Vec d)}
    (hK : IsCompact K) (hKn : K.Nonempty)
    (hCont : ∀ ν : ℕ, ContinuousOn (fun z : C × Vec d => iteratedFDeriv ℝ ν (g z.1) z.2) (C0 ×ˢ K))
    (h : ∃ μ : ℕ, 0 < μ ∧ 0 < betaFamily g C0 K μ) :
    0 < index_def g C0 K h ∧ 0 < betaFamily g C0 K (index_def g C0 K h) ∧
    Monotone (betaFamily g C0 K) ∧
    (∀ μ : ℕ, 0 < μ → (0 < betaFamily g C0 K μ ↔ index_def g C0 K h ≤ μ)) := by
  have hspec : 0 < index_def g C0 K h ∧ 0 < betaFamily g C0 K (index_def g C0 K h) :=
    Nat.find_spec h
  have hmono := betaFamily_mono (g := g) hCn hKn
  refine ⟨hspec.1, hspec.2, hmono, fun μ hμ => ⟨fun hp => ?_, fun hle => ?_⟩⟩
  · exact Nat.find_min' h ⟨hμ, hp⟩
  · exact lt_of_lt_of_le hspec.2 (hmono hle)

/-! ### Finite type -/

/-- If every diagonal jet of an analytic function vanishes at a point, it vanishes near the point. -/
lemma eventuallyEq_zero_of_scalarJet {f : Vec d → ℝ} {x : Vec d} (hf : AnalyticAt ℝ f x)
    (h0 : ∀ ν : ℕ, scalarJet f ν x = 0) : f =ᶠ[𝓝 x] 0 := by
  have hdiag : ∀ (ν : ℕ) (y : Vec d), iteratedFDeriv ℝ ν f x (fun _ => y) = 0 := by
    intro ν y
    rcases Nat.eq_zero_or_pos ν with rfl | hν
    · have := h0 0
      simp only [scalarJet, ite_true, abs_eq_zero] at this
      simp [iteratedFDeriv_zero_apply, this]
    · set T := iteratedFDeriv ℝ ν f x with hT
      have hunit : ∀ v : Vec d, length2 v = 1 → T (fun _ => v) = 0 := by
        intro v hv
        have h1 := h0 ν
        simp only [scalarJet, hν.ne', ite_false] at h1
        have h2 : |T (fun _ => v)| ≤ 0 := h1 ▸ le_csSup (bddAbove_jetOp T) ⟨v, hv, rfl⟩
        exact abs_nonpos_iff.1 h2
      by_cases hy : y = 0
      · subst hy
        have : T (fun _ => (0 : Vec d)) = 0 := by
          haveI : Nonempty (Fin ν) := ⟨⟨0, hν⟩⟩
          exact T.map_zero
        exact this
      · have hc : 0 < length2 y := by
          unfold length2
          refine Real.sqrt_pos.2 ?_
          by_contra hn
          apply hy
          have hsum : ∑ i, y i ^ 2 = 0 :=
            le_antisymm (not_lt.1 hn) (Finset.sum_nonneg fun i _ => sq_nonneg _)
          funext i
          have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (y i))).1 hsum i
            (Finset.mem_univ i)
          simpa using this
        have hv : length2 ((length2 y)⁻¹ • y) = 1 := by
          have : length2 ((length2 y)⁻¹ • y) = (length2 y)⁻¹ * length2 y := by
            unfold length2
            simp only [Pi.smul_apply, smul_eq_mul]
            have : ∑ i, ((√(∑ i, y i ^ 2))⁻¹ * y i) ^ 2 =
                ((√(∑ i, y i ^ 2))⁻¹) ^ 2 * ∑ i, y i ^ 2 := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
            rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.2 (Real.sqrt_nonneg _))]
          rw [this]; exact inv_mul_cancel₀ hc.ne'
        have hy' : (fun _ : Fin ν => y) = fun _ => length2 y • ((length2 y)⁻¹ • y) := by
          funext _; rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
        rw [hy', T.map_smul_univ, hunit _ hv, smul_zero]
  obtain ⟨p, r, hp⟩ := hf
  have hball : ∀ᶠ y in 𝓝 x, y - x ∈ Metric.eball (0 : Vec d) r := by
    have ht : Tendsto (fun y : Vec d => y - x) (𝓝 x) (𝓝 0) := by
      simpa using (tendsto_id.sub_const x : Tendsto (fun y : Vec d => y - x) (𝓝 x) (𝓝 (x - x)))
    exact ht.eventually (Metric.eball_mem_nhds 0 hp.r_pos)
  filter_upwards [hball] with y hy
  have hs := hp.hasSum hy
  have hz : (fun n => p n fun _ => y - x) = fun _ => 0 := by
    funext n
    have := hp.factorial_smul (y - x) n
    rw [hdiag n (y - x)] at this
    have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
    rw [nsmul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hn
  rw [hz] at hs
  have := hs.unique hasSum_zero
  simpa using this

/-- Pointwise step: some jet of order `ν` is nonzero at every point of a nonvanishing analytic
function's domain. -/
lemma exists_scalarJet_pos {B : Set (Vec d)} (hB : IsOpen B) (hBc : IsConnected B)
    {f : Vec d → ℝ} (hf : AnalyticOnNhd ℝ f B) (hne : ∃ y ∈ B, f y ≠ 0) {x : Vec d}
    (hx : x ∈ B) : ∃ ν : ℕ, 0 < scalarJet f ν x := by
  by_contra hcon
  push Not at hcon
  have h0 : ∀ ν : ℕ, scalarJet f ν x = 0 := fun ν =>
    le_antisymm (hcon ν) (scalarJet_nonneg f ν x)
  have hev := eventuallyEq_zero_of_scalarJet (hf x hx) h0
  obtain ⟨y, hy, hy0⟩ := hne
  exact hy0 (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hBc.isPreconnected hx hev hy)

theorem finite_type {C : Type*} [MetricSpace C] {C0 : Set C} (hC : IsCompact C0) (hCn : C0.Nonempty)
    {B K : Set (Vec d)} (hB : IsOpen B) (hBc : IsConnected B)
    (hK : IsCompact K) (hKn : K.Nonempty) (hKB : K ⊆ B) {g : C → Vec d → ℝ}
    (hAn : ∀ c ∈ C0, AnalyticOnNhd ℝ (g c) B)
    (hNe : ∀ c ∈ C0, ∃ y ∈ B, g c y ≠ 0)
    (hCont : ∀ ν : ℕ, ContinuousOn (fun z : C × Vec d => iteratedFDeriv ℝ ν (g z.1) z.2) (C0 ×ˢ B)) :
    ∃ μ : ℕ, 0 < μ ∧ 0 < betaFamily g C0 K μ ∧
      ∀ c ∈ C0, ∀ y ∈ K, betaFamily g C0 K μ ≤ jetMax (g c) μ y := by
  have hS : IsCompact (C0 ×ˢ K) := hC.prod hK
  have hCont' : ∀ ν : ℕ,
      ContinuousOn (fun z : C × Vec d => iteratedFDeriv ℝ ν (g z.1) z.2) (C0 ×ˢ K) :=
    fun ν => (hCont ν).mono (prod_mono subset_rfl hKB)
  have hJ := jetMax_continuousOn hCont'
  -- open cover by the sets where the jet maximum of order `ν` is positive
  have hopen : ∀ ν : ℕ, ∃ u : Set (C × Vec d), IsOpen u ∧
      (fun z : C × Vec d => jetMax (g z.1) ν z.2) ⁻¹' Ioi 0 ∩ (C0 ×ˢ K) = u ∩ (C0 ×ˢ K) :=
    fun ν => continuousOn_iff'.1 (hJ ν) _ isOpen_Ioi
  choose u huo hu using hopen
  have hcover : C0 ×ˢ K ⊆ ⋃ ν : ℕ, u ν := by
    intro z hz
    obtain ⟨ν, hν⟩ := exists_scalarJet_pos hB hBc (hAn z.1 hz.1) (hNe z.1 hz.1) (hKB hz.2)
    have : z ∈ (fun z : C × Vec d => jetMax (g z.1) ν z.2) ⁻¹' Ioi 0 ∩ (C0 ×ˢ K) :=
      ⟨lt_of_lt_of_le hν (scalarJet_le_jetMax _ le_rfl _), hz⟩
    rw [hu ν] at this
    exact mem_iUnion.2 ⟨ν, this.1⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover u huo hcover
  set μ := t.sup id + 1 with hμ
  have hpos : ∀ z ∈ C0 ×ˢ K, 0 < jetMax (g z.1) μ z.2 := by
    intro z hz
    obtain ⟨ν, hνt, hzν⟩ := mem_iUnion₂.1 (ht hz)
    have : z ∈ (fun z : C × Vec d => jetMax (g z.1) ν z.2) ⁻¹' Ioi 0 ∩ (C0 ×ˢ K) := by
      rw [hu ν]; exact ⟨hzν, hz⟩
    have hνμ : ν ≤ μ := (Finset.le_sup (f := id) hνt).trans (Nat.le_succ _)
    exact lt_of_lt_of_le this.1 (jetMax_mono _ _ hνμ)
  obtain ⟨z, hz, hz'⟩ := betaFamily_attained hC hCn hK hKn (g := g) (μ := μ) (hJ μ)
  exact ⟨μ, Nat.succ_pos _, hz' ▸ hpos z hz, fun c hc y hy => betaFamily_le hc hy⟩

lemma analyticAt_fsum {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset ι)
    {f : ι → E → ℝ} {x : E} (h : ∀ i ∈ s, AnalyticAt ℝ (f i) x) :
    AnalyticAt ℝ (fun y => ∑ i ∈ s, f i y) x := by
  simpa [Finset.sum_fn] using Finset.analyticAt_sum s h

lemma analyticAt_fprod {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset ι)
    {f : ι → E → ℝ} {x : E} (h : ∀ i ∈ s, AnalyticAt ℝ (f i) x) :
    AnalyticAt ℝ (fun y => ∏ i ∈ s, f i y) x := by
  simpa [Finset.prod_fn] using Finset.analyticAt_prod s h

/-! ### Families expanding over a finite index -/

/-- If `g c y = ∑ₖ pₖ(c) hₖ(y)` with continuous `pₖ` and analytic `hₖ`, then each `g c` is
analytic and the iterated derivatives are jointly continuous. -/
lemma expansion {C ι : Type*} [TopologicalSpace C] [Fintype ι] {B : Set (Vec d)} (hB : IsOpen B)
    {g : C → Vec d → ℝ} {p : ι → C → ℝ} (hp : ∀ k, Continuous (p k)) {h : ι → Vec d → ℝ}
    (hh : ∀ k, AnalyticOnNhd ℝ (h k) B) (hg : ∀ c y, g c y = ∑ k, p k c * h k y) :
    (∀ c, AnalyticOnNhd ℝ (g c) B) ∧
    ∀ ν : ℕ, ContinuousOn (fun z : C × Vec d => iteratedFDeriv ℝ ν (g z.1) z.2)
      (univ ×ˢ B) := by
  have hgc : ∀ c, g c = fun y => ∑ k, p k c • h k y := by
    intro c; funext y; simp [hg]
  refine ⟨fun c => ?_, fun ν => ?_⟩
  · have : g c = fun y => ∑ k ∈ Finset.univ, p k c * h k y := funext (hg c)
    rw [this]
    exact fun y hy => analyticAt_fsum _ fun k _ => analyticAt_const.mul (hh k y hy)
  · have hcd : ∀ k, ContDiffOn ℝ ν (h k) B := fun k => (hh k).contDiffOn hB.uniqueDiffOn
    have hcont : ∀ k, ContinuousOn (iteratedFDeriv ℝ ν (h k)) B := fun k =>
      ((hcd k).continuousOn_iteratedFDerivWithin le_rfl hB.uniqueDiffOn).congr
        (iteratedFDerivWithin_of_isOpen ν hB).symm
    have heq : EqOn (fun z : C × Vec d => iteratedFDeriv ℝ ν (g z.1) z.2)
        (fun z => ∑ k, p k z.1 • iteratedFDeriv ℝ ν (h k) z.2) (univ ×ˢ B) := by
      rintro ⟨c, y⟩ ⟨-, hy⟩
      simp only
      rw [← iteratedFDerivWithin_of_isOpen ν hB hy, hgc c,
        iteratedFDerivWithin_fun_sum_apply hB.uniqueDiffOn hy
          (fun k _ => ((hcd k) y hy).const_smul (p k c))]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := iteratedFDerivWithin_const_smul_apply (a := p k c) ((hcd k) y hy)
        hB.uniqueDiffOn hy
      exact this.trans (congrArg _ (iteratedFDerivWithin_of_isOpen ν hB hy))
    refine ContinuousOn.congr ?_ heq
    refine continuousOn_finsetSum _ fun k _ => ?_
    exact ((hp k).comp continuous_fst).continuousOn.smul
      ((hcont k).comp continuousOn_snd fun z hz => hz.2)

lemma continuous_length2 : Continuous (length2 : Vec m → ℝ) :=
  Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2)

lemma isCompact_sphere : IsCompact (sphere m) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_eq continuous_length2 continuous_const)
    ((Metric.isBounded_closedBall (x := (0 : Vec m)) (r := 1)).subset fun c hc => by
      simpa using norm_le_one_of_length2 (show length2 c = 1 from hc))

lemma sphere_nonempty (hm : 0 < m) : (sphere m).Nonempty :=
  ⟨Pi.single ⟨0, hm⟩ 1, by simp [sphere, length2, Pi.single_apply]⟩

lemma ne_zero_of_mem_sphere {c : Vec m} (hc : c ∈ sphere m) : c ≠ 0 := by
  rintro rfl
  have : length2 (0 : Vec m) = 0 := by simp [length2]
  exact zero_ne_one (this.symm.trans hc)

lemma analytic_coord {B : Set (Vec d)} {ω : Vec d → Vec m} (hAn : AnalyticOnNhd ℝ ω B) (i : Fin m) :
    AnalyticOnNhd ℝ (fun y => ω y i) B := fun y hy =>
  ((ContinuousLinearMap.proj i : Vec m →L[ℝ] ℝ).analyticAt _).comp (hAn y hy)

theorem cp09_lemma1 (hm : 0 < m) {B K : Set (Vec d)}
    (hB : IsOpen B) (hBc : IsConnected B) (hK : IsCompact K) (hKn : K.Nonempty) (hKB : K ⊆ B)
    {ω : Vec d → Vec m} (hAn : AnalyticOnNhd ℝ ω B) (hR : rnd_def B ω) :
    ∃ μ : ℕ, 0 < μ ∧ 0 < betaMu ω K μ ∧
      ∀ c ∈ sphere m, ∀ y ∈ K, betaMu ω K μ ≤ jetMax (squaredForm ω c) μ y := by
  obtain ⟨hAn', hCont⟩ := expansion (C := Vec m) (ι := Fin m × Fin m) hB
    (g := squaredForm ω) (p := fun k c => c k.1 * c k.2) (h := fun k y => ω y k.1 * ω y k.2)
    (fun k => (continuous_apply k.1).mul (continuous_apply k.2))
    (fun k => (analytic_coord hAn k.1).mul (analytic_coord hAn k.2))
    (fun c y => by
      simp only [squaredForm, sq, Finset.sum_mul_sum, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
  refine finite_type isCompact_sphere (sphere_nonempty hm) hB hBc hK hKn hKB
    (fun c _ => hAn' c) (fun c hc => ?_) (fun ν => (hCont ν).mono (prod_mono (subset_univ _) subset_rfl))
  obtain ⟨y, hy, hne⟩ := hR c (ne_zero_of_mem_sphere hc)
  exact ⟨y, hy, pow_ne_zero 2 hne⟩

theorem cp09_unsquared (hm : 0 < m) {B K : Set (Vec d)}
    (hB : IsOpen B) (hBc : IsConnected B) (hK : IsCompact K) (hKn : K.Nonempty) (hKB : K ⊆ B)
    {ω : Vec d → Vec m} (hAn : AnalyticOnNhd ℝ ω B) (hR : rnd_def B ω) :
    ∃ μ : ℕ, 0 < μ ∧ 0 < betaFamily (fun c y => ∑ i, c i*ω y i) (sphere m) K μ := by
  obtain ⟨hAn', hCont⟩ := expansion (C := Vec m) (ι := Fin m) hB
    (g := fun c y => ∑ i, c i*ω y i) (p := fun k c => c k) (h := fun k y => ω y k)
    (fun k => continuous_apply k) (fun k => analytic_coord hAn k) (fun c y => rfl)
  obtain ⟨μ, hμ, hβ, -⟩ := finite_type isCompact_sphere (sphere_nonempty hm) hB hBc hK hKn hKB
    (fun c _ => hAn' c) (fun c hc => hR c (ne_zero_of_mem_sphere hc))
    (fun ν => (hCont ν).mono (prod_mono (subset_univ _) subset_rfl))
  exact ⟨μ, hμ, hβ⟩

theorem cp09_product {r : ℕ} {dims : Fin r → ℕ} (hm : ∀ l, 0 < dims l) {B K : Set (Vec d)}
    (hB : IsOpen B) (hBc : IsConnected B) (hK : IsCompact K) (hKn : K.Nonempty) (hKB : K ⊆ B)
    {ω : (l : Fin r) → Vec d → Vec (dims l)}
    (hAn : ∀ l, AnalyticOnNhd ℝ (ω l) B) (hR : ∀ l, rnd_def B (ω l)) :
    ∃ μ : ℕ, 0 < μ ∧ 0 < betaFamily
      (fun (c : (l : Fin r) → Vec (dims l)) y => ∏ l, ∑ i, c l i*ω l y i)
      {c | ∀ l, c l ∈ sphere (dims l)} K μ := by
  obtain ⟨hAn', hCont⟩ := expansion (C := (l : Fin r) → Vec (dims l))
    (ι := (l : Fin r) → Fin (dims l)) hB
    (g := fun c y => ∏ l, ∑ i, c l i*ω l y i) (p := fun k c => ∏ l, c l (k l))
    (h := fun k y => ∏ l, ω l y (k l))
    (fun k => continuous_finsetProd _ fun l _ => (continuous_apply (k l)).comp (continuous_apply l))
    (fun k y hy => analyticAt_fprod _ fun l _ => analytic_coord (hAn l) (k l) y hy)
    (fun c y => by
      have := Finset.prod_univ_sum (fun l => (Finset.univ : Finset (Fin (dims l))))
        (fun l i => c l i * ω l y i)
      rw [Fintype.piFinset_univ] at this
      rw [this]
      exact Finset.sum_congr rfl fun k _ => by rw [Finset.prod_mul_distrib])
  have hC : IsCompact {c : (l : Fin r) → Vec (dims l) | ∀ l, c l ∈ sphere (dims l)} := by
    have : {c : (l : Fin r) → Vec (dims l) | ∀ l, c l ∈ sphere (dims l)} =
        Set.pi univ fun l => sphere (dims l) := by ext; simp
    rw [this]
    exact isCompact_univ_pi fun l => isCompact_sphere
  have hCn : {c : (l : Fin r) → Vec (dims l) | ∀ l, c l ∈ sphere (dims l)}.Nonempty := by
    choose c hc using fun l => sphere_nonempty (hm l)
    exact ⟨c, hc⟩
  have hNe : ∀ c ∈ {c : (l : Fin r) → Vec (dims l) | ∀ l, c l ∈ sphere (dims l)},
      ∃ y ∈ B, ∏ l, ∑ i, c l i*ω l y i ≠ 0 := by
    intro c hc
    have hf : ∀ l, AnalyticOnNhd ℝ (fun y => ∑ i, c l i * ω l y i) B := fun l y hy =>
      analyticAt_fsum _ fun i _ => analyticAt_const.mul (analytic_coord (hAn l) i y hy)
    have hne : ∀ l, ∃ y ∈ B, (fun y => ∑ i, c l i * ω l y i) y ≠ 0 := fun l =>
      hR l (c l) (ne_zero_of_mem_sphere (hc l))
    obtain ⟨-, hcl, -⟩ := generic hB hBc hf hne
    obtain ⟨y0, hy0⟩ := hBc.nonempty
    obtain ⟨y, -, hy⟩ := mem_closure_iff.1 (hcl hy0) univ isOpen_univ trivial
    exact ⟨y, hy.1, Finset.prod_ne_zero_iff.2 fun l _ => hy.2 l⟩
  obtain ⟨μ, hμ, hβ, -⟩ := finite_type hC hCn hB hBc hK hKn hKB
    (fun c _ => hAn' c) hNe
    (fun ν => (hCont ν).mono (prod_mono (subset_univ _) subset_rfl))
  exact ⟨μ, hμ, hβ⟩

end Nondegeneracy
end KAM.Planetary
end
