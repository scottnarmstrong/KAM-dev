/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarAssembly.ChartData
public import KAM.Planetary.PlanarAssembly.SlowSmall
public import KAM.Planetary.PlanarAssembly.DataBox
public import KAM.Planetary.PlanarAssembly.Geometry
public import KAM.Planetary.PlanarAssembly.Boxes
public import KAM.Planetary.PlanarTorsion.Patch
public import KAM.Planetary.Newtonian.Tube
public import KAM.Frozen.Planetary.Defs.Cylinder
public import KAM.Frozen.Planetary.Defs.CircularTube
public import KAM.Planetary.Hamiltonian.Chart

/-!
# Planar assembly: the joint P-G data (Part 12)

Blueprint P, Part 12 (`bpP:p12:data`, `bpP:p12:chart`, `bpP:p12:pg-hypotheses` and their steps):
`PlanarAssembly.pg_hypotheses` is the single joint construction of the action boxes, the open
set `O`, the Birkhoff map `T`, the radii and the secular jets.  The good cube and the map `T` come
from the owner declaration `patch` (T21, containing `birkhoff_form` of T16): the jets are the
actual `p11c_secular fhat I 0`, `2 σ` and `p11c_beta`, and the Hamiltonian identity is the
product-chart splitting for the fast-action preserving `T`.  The Hamiltonian-form clause and the
periodicity use only the exports of `PlanarBirkhoffResult` and the product chart; the smallness of
the slow part of `T` is `p12c_slow_small`.  Nothing is imported from a P-G theorem.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function
open scoped BigOperators

namespace KAM.Planetary
open KAM KAM.Kepler

namespace PlanarAssembly

private theorem tube_isOpen {O' : Set (Fin 2 → ℝ)} (hO' : IsOpen O') (rS : ℝ) :
    IsOpen (p11c_tube O' rS) := by
  have h1 : Continuous fun w : Phase (2 + 2) => p11cL_act w := by
    unfold p11cL_act; fun_prop
  have h2 : Continuous fun w : Phase (2 + 2) => p11c_slowLength (p11cL_slow w) := by
    unfold p11c_slowLength p11cL_slow; fun_prop
  exact (hO'.preimage h1).inter (isOpen_lt h2 continuous_const)

private theorem shift_mem_tube {O' : Set (Fin 2 → ℝ)} {rS : ℝ} {z : Phase (2 + 2)}
    (hz : z ∈ p11c_tube O' rS) (k : Fin 2 → ℤ) :
    z + fastShift (a := 2) (b := 2) k ∈ p11c_tube O' rS := by
  have e1 : p11cL_act (z + fastShift (a := 2) (b := 2) k) = p11cL_act z := by
    funext i; simp [p11cL_act, fastShift]
  have e2 : p11cL_slow (z + fastShift (a := 2) (b := 2) k) = p11cL_slow z := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
      simp [p11cL_slow, fastShift, Fin.append_right]
  refine ⟨?_, ?_⟩
  · show p11cL_act (z + fastShift (a := 2) (b := 2) k) ∈ O'
    rw [e1]; exact hz.1
  · show p11c_slowLength (p11cL_slow (z + fastShift (a := 2) (b := 2) k)) < rS
    rw [e2]; exact hz.2

private theorem slowLength_lt {z : Phase (2 + 2)} {r0 rS : ℝ} (hrS : 0 < rS)
    (hr : 0 ≤ r0) (hr0 : r0 ≤ rS / 2)
    (hz : ∀ j : Fin 2, z.2 (Fin.natAdd 2 j) ^ 2 + z.1 (Fin.natAdd 2 j) ^ 2 ≤ r0 ^ 2) :
    p11c_slowLength (p11cL_slow z) < rS := by
  have h0 := hz 0
  have h1 := hz 1
  have hsq : r0 ^ 2 ≤ (rS / 2) ^ 2 := pow_le_pow_left₀ hr hr0 2
  unfold p11c_slowLength
  rw [sqrt_lt' hrS, Fin.sum_univ_two]
  show z.1 (Fin.natAdd 2 0) ^ 2 + z.2 (Fin.natAdd 2 0) ^ 2 +
    (z.1 (Fin.natAdd 2 1) ^ 2 + z.2 (Fin.natAdd 2 1) ^ 2) < rS ^ 2
  nlinarith

/-- Joint output of data, chart and pg-hypotheses. All derived clauses are conclusions.
T, O, V and the jet witnesses are shared, selected once before the coupling.
The 11b writer owns their finer source characterization; see the upstream table.
This projection is not a certificate of canonical jets, the axis cube, or a common
moving/fixed T. Exact characterization exports must be reconciled before P12-C/P13-A. -/
theorem pg_hypotheses (G m0 : ℝ) (m a : Fin 2 → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : a 0 < a 1) (η : ℝ) (hη : 0 < η) :
    ∃ (V W : Set (Fin 2 → ℝ)) (O : Set (Phase 4)) (T : Phase 4 → Phase 4)
      (r0 δ B : ℝ) (P0 : ℝ → (Fin 2 → ℝ) → ℝ)
      (Ω : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ))
      (β : ℝ → (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ),
      IsOpen V ∧ IsConnected V ∧ Bornology.IsBounded V ∧
      IsOpen W ∧ closure V ⊆ W ∧
      (∃ A dc : ℝ, 0 < A ∧ 0 < dc ∧ ∀ t : ℝ, 0 < t → t < dc →
        volume {I : Fin 2 → ℝ | ∃ J ∈ frontier V, dist I J < t} ≤
          ENNReal.ofReal (A * t)) ∧
      0 < r0 ∧ 0 < δ ∧ 0 < B ∧
      IsOpen O ∧ closure (cylinder (b := 2) V r0) ⊆ O ∧
      (∀ z ∈ O, ∀ k : Fin 2 → ℤ, z + fastShift (a := 2) (b := 2) k ∈ O) ∧
      MapsTo T O (poincareProdDom 2) ∧
      MapsTo (total_chart G m0 m T) O (collisionFreeDomain 2) ∧
      AnalyticOnNhd ℝ (total_chart G m0 m T) O ∧
      IsSymplecticOn 1 (total_chart G m0 m T) O ∧
      (∀ z ∈ O, Bijective (fderiv ℝ (total_chart G m0 m T) z)) ∧
      (∀ z ∈ O, ∀ k : Fin 2 → ℤ,
        total_chart G m0 m T (z + fastShift (a := 2) (b := 2) k) = total_chart G m0 m T z) ∧
      (∀ z ∈ O, ∀ z' ∈ O, total_chart G m0 m T z' = total_chart G m0 m T z →
        ∃ k : Fin 2 → ℤ, z' = z + fastShift (a := 2) (b := 2) k) ∧
      (∀ μ : ℝ, ∀ z ∈ O, movingHamiltonian G m0 m μ (total_chart G m0 m T z) =
        degenerateHamiltonian (a := 2) (b := 2) (kepler_h (G * m0) m)
          (perturbation G m0 m T) μ z) ∧
      (∀ r : ℝ, 0 < r → r ≤ r0 → 2 * r ^ 2 ≤ δ →
        MapsTo (total_chart G m0 m T) (cylinder (b := 2) V r)
          (circularTube G m0 m a (tubeRadius η (axisGap a)))) ∧
      AnalyticOnNhd ℝ (fun z : ℝ × Phase 4 => perturbation G m0 m T z.1 z.2)
        (Icc 0 1 ×ˢ closure (cylinder (b := 2) V r0)) ∧
      (∀ μ ∈ Icc (0 : ℝ) 1, ∀ z ∈ cylinder (b := 2) V r0, ∀ k : Fin 2 → ℤ,
        perturbation G m0 m T μ (z + fastShift (a := 2) (b := 2) k) =
          perturbation G m0 m T μ z) ∧
      HasFastDiffeomorphism (kepler_h (G * m0) m) W ∧
      HasSecularBirkhoffForm (perturbation G m0 m T) V r0 1 P0 Ω β ∧
      (∀ μ ∈ Icc (0 : ℝ) 1, ∀ I ∈ V, B ≤ |(β μ I).det|) ∧
      (∀ μ ∈ Icc (0 : ℝ) 1, ∀ I ∈ V, (β μ I).IsSymm) := by
  classical
  set p : PlanarData := ⟨G, m0, m⟩ with hpdef
  have hp : p.Valid := ⟨hG, hm0, hm⟩
  have hκ : 0 < G * m0 := mul_pos hG hm0
  have haxes : a ∈ p11c_axes := ⟨ha 0, hsep⟩
  have hinja : Function.Injective a := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> linarith
  -- the tube radius and the forward tube
  have hγ := (axisData_canonical (n := 2) (by norm_num) ha hinja).gap_pos
  have hζ := tubeRadius_pos hη hγ
  obtain ⟨δft, hδft, -, hft⟩ := forward_tube G m0 m a hG hm0 hm ha _ hζ
  -- an axis neighbourhood on which the actions are within δft of the centre
  have hev : ∀ᶠ b in nhds a, ∀ i, |p.actions b i - p.actions a i| ≤ δft := by
    refine Filter.eventually_all.2 fun i => ?_
    have hc : Continuous fun b : Fin 2 → ℝ => p.actions b i := by
      unfold PlanarData.actions; fun_prop
    filter_upwards [hc.continuousAt.eventually (Metric.closedBall_mem_nhds (p.actions a i) hδft)]
      with b hb
    simpa [Real.dist_eq] using hb
  obtain ⟨η1, hη1, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  -- the good cube and the Birkhoff map
  obtain ⟨a0, r, B, hr, hB, hgood, hBB, -, rS, CS, hrS, -, hres⟩ := patch p hp a haxes η1 hη1
  obtain ⟨O', hO', hKO, -, -, F, chi, -, -, T, hT, -, hch, hinjT, hact, htr, hdom, hf⟩ := hres
  have hgoodr : ∀ b ∈ closedBall a0 r, b ∈ ball a η1 ∧ b ∈ p11c_axes ∧
      (p11c_beta p b).det ≠ 0 := fun b hb =>
    have h := hgood (closedBall_subset_closedBall (by linarith) hb)
    ⟨h.1, h.2.1, h.2.2.2⟩
  have hpos : ∀ i, r < a0 i := by
    have hb : (fun j => a0 j - 2 * r) ∈ p11c_axes := by
      refine (hgood ?_).2.1
      rw [mem_closedBall, dist_pi_le_iff (by positivity)]
      intro i
      simp [Real.dist_eq, abs_of_nonneg hr.le]
    have h1 := hb.1
    have h2 := h1.trans hb.2
    simp only at h1 h2
    exact Fin.forall_fin_two.2 ⟨by linarith, by linarith⟩
  obtain ⟨lo, hi, hlo, hlohi, hbox⟩ := p12c_box p hp a0 hr hpos
  have hhi : ∀ i, 0 < hi i := fun i => (hlo i).trans (hlohi i)
  set V : Set (Fin 2 → ℝ) := pi univ (fun i => Ioo (lo i) (hi i)) with hV
  set K0 : Set (Fin 2 → ℝ) := pi univ (fun i => Icc (lo i) (hi i)) with hK0
  set W : Set (Fin 2 → ℝ) := pi univ (fun i => Ioo (lo i / 2) (2 * hi i)) with hW
  have hVK0 : V ⊆ K0 := pi_mono fun i _ => Ioo_subset_Icc_self
  have hK0c : IsCompact K0 := isCompact_univ_pi fun i => isCompact_Icc
  have hK0cl : IsClosed K0 := isClosed_set_pi fun i _ => isClosed_Icc
  have hVopen : IsOpen V := isOpen_set_pi finite_univ fun i _ => isOpen_Ioo
  have hVsub : V ⊆ p.actions '' closedBall a0 r := hVK0.trans hbox
  have hVint : V ⊆ interior (p.actions '' closedBall a0 r) := interior_maximal hVsub hVopen
  have hK0O' : K0 ⊆ O' := hbox.trans hKO
  have hK0W : K0 ⊆ W := fun I hI i _ => by
    have h1 := (hI i (mem_univ i)).1
    have h2 := (hI i (mem_univ i)).2
    have := hlo i
    have := hhi i
    exact ⟨by linarith, by linarith⟩
  -- smallness of the slow part of T
  have hcont : ContinuousOn (p11c_rotationLift p ∘ p11c_liftFlow chi.eval) (p11c_tube O' rS) := by
    rw [← hT]; exact hch.1.continuousOn
  obtain ⟨ρ, hρ, hsm⟩ := p12c_slow_small p chi hrS hK0c hK0O' hcont (Real.sqrt_pos.2 hδft)
  rw [← hT] at hsm
  set r0 : ℝ := min (rS / 2) ρ with hr0
  have hr0pos : 0 < r0 := lt_min (by positivity) hρ
  have hr0S : r0 ≤ rS / 2 := min_le_left _ _
  have hr0ρ : r0 ≤ ρ := min_le_right _ _
  set O : Set (Phase 4) := p11c_tube O' rS with hO
  have hOopen : IsOpen O := tube_isOpen hO' rS
  have hshiftO : ∀ z ∈ O, ∀ k : Fin 2 → ℤ, z + fastShift (a := 2) (b := 2) k ∈ O :=
    fun z hz k => shift_mem_tube hz k
  -- the closed cylinder lies in the tube
  set C : Set (Phase (2 + 2)) := {z | fast z.2 ∈ K0} ∩
    ⋂ j : Fin 2, {z | slow z.2 j ^ 2 + slow z.1 j ^ 2 ≤ r0 ^ 2} with hC
  have hCclosed : IsClosed C := by
    refine IsClosed.inter (hK0cl.preimage ?_) (isClosed_iInter fun j => isClosed_le ?_
      continuous_const)
    · refine continuous_pi fun i => ?_
      unfold fast; fun_prop
    · unfold slow; fun_prop
  have hcylC : cylinder (b := 2) V r0 ⊆ C := fun z hz =>
    ⟨hVK0 hz.1, mem_iInter.2 fun j => (hz.2 j).le⟩
  have hCO : C ⊆ O := fun z hz => ⟨hK0O' hz.1, slowLength_lt hrS hr0pos.le hr0S fun j =>
    mem_iInter.1 hz.2 j⟩
  have hclO : closure (cylinder (b := 2) V r0) ⊆ O :=
    (closure_minimal hcylC hCclosed).trans hCO
  -- the chart
  have hTm : MapsTo T O (poincareProdDom 2) := fun w hw => (hdom w hw).1
  obtain ⟨hTan, hTsy⟩ := chart_of_birkhoff (G := G) (m0 := m0) hm hκ hch.1 hch.2 hTm
  have hshift : ∀ z ∈ O, ∀ k : Fin 2 → ℤ,
      T (z + fastShift (a := 2) (b := 2) k) = T z + fastShift (a := 2) (b := 2) k :=
    fun z hz k => htr z hz (fun i => 2 * π * (k i : ℝ))
  have hper : ∀ z ∈ O, ∀ k : Fin 2 → ℤ,
      total_chart G m0 m T (z + fastShift (a := 2) (b := 2) k) = total_chart G m0 m T z := by
    intro z hz k
    show poincareProd m (G * m0) (T (z + fastShift (a := 2) (b := 2) k)) =
      poincareProd m (G * m0) (T z)
    rw [hshift z hz k]
    exact (poincareProd_lattice hm hκ (hdom z hz).1 k).2
  have hBNF := hf (p11c_hatMov p) (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨hAn, P0, -, -, hBNF⟩ := hBNF
  have hr0le : r0 ≤ rS / √2 := by
    refine hr0S.trans ?_
    exact div_le_div_of_nonneg_left hrS.le (by positivity)
      (Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩)
  have hβ : ∀ I ∈ V, p.axes I ∈ closedBall a0 r ∧ p.axes I ∈ p11c_axes := by
    intro I hI
    obtain ⟨b, hb, rfl⟩ := hVsub hI
    have := (hgoodr b hb).2.1
    rw [p11cB_axes_actions p hp this]
    exact ⟨hb, this⟩
  refine ⟨V, W, O, T, r0, 1, B, fun _ => P0, fun _ I j => 2 * p11c_sigma p (p.axes I) j,
    fun _ I => p11c_beta p (p.axes I), hVopen, ?_, ?_, ?_, ?_, ?_, hr0pos, one_pos, hB, hOopen,
    hclO, hshiftO, hTm, ?_, hTan, hTsy, ?_, hper, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- connected
    refine ⟨?_, (convex_pi fun i _ => convex_Ioo (lo i) (hi i)).isPreconnected⟩
    exact ⟨fun i => (lo i + hi i) / 2, fun i _ => ⟨by linarith [hlohi i], by linarith [hlohi i]⟩⟩
  · -- bounded
    refine (Metric.isBounded_Icc lo hi).subset ?_
    intro I hI
    exact ⟨fun i => (hI i (mem_univ i)).1.le, fun i => (hI i (mem_univ i)).2.le⟩
  · exact isOpen_set_pi finite_univ fun i _ => isOpen_Ioo
  · exact (closure_minimal hVK0 hK0cl).trans hK0W
  · -- collar
    have hd : ∀ i, 0 < (hi i - lo i) / 2 := fun i => by linarith [hlohi i]
    refine ⟨4 * ((hi 0 - lo 0) + (hi 1 - lo 1)), min ((hi 0 - lo 0) / 2) ((hi 1 - lo 1) / 2),
      by linarith [hlohi 0, hlohi 1], lt_min (hd 0) (hd 1), fun t ht htd => ?_⟩
    exact collar lo hi hlohi t ht (Fin.forall_fin_two.2
      ⟨htd.trans_le (min_le_left _ _), htd.trans_le (min_le_right _ _)⟩)
  · -- collision free
    intro z hz
    exact (hdom z hz).2
  · -- bijective derivative
    intro z hz
    exact IsChart.bijective_fderiv one_pos ⟨hTan, hTsy⟩ hz
  · -- injective modulo the lattice
    intro z hz z' hz' h
    obtain ⟨k, hk⟩ := (poincareProd_eq_iff hm hκ (hdom z hz).1 (hdom z' hz').1).1 h.symm
    refine ⟨k, hinjT hz' (shift_mem_tube hz k) ?_⟩
    rw [hshift z hz k]
    exact hk
  · -- Hamiltonian identity
    intro μ z hz
    exact chart_hamiltonian_of_preserves_fast hm hκ (hdom z hz).1 (hact z hz) μ
  · -- tube
    intro r hrpos hrr _ z hz
    have hz0 : z ∈ cylinder (b := 2) V r0 := ⟨hz.1, fun j => (hz.2 j).trans_le
      (pow_le_pow_left₀ hrpos.le hrr 2)⟩
    have hzO : z ∈ O := hCO (hcylC hz0)
    have hbnd : ∀ j : Fin 2, |slow z.1 j| < r0 ∧ |slow z.2 j| < r0 := by
      intro j
      have h := hz0.2 j
      exact ⟨abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (slow z.2 j)]) hr0pos.le,
        abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (slow z.1 j)]) hr0pos.le⟩
    have hnorm : ‖p11cL_slow z‖ < ρ := by
      refine lt_of_lt_of_le ?_ hr0ρ
      rw [Prod.norm_def]
      refine max_lt ((pi_norm_lt_iff hr0pos).2 fun j => ?_) ((pi_norm_lt_iff hr0pos).2 fun j => ?_)
      · exact (hbnd j).1
      · exact (hbnd j).2
    have hsmall := hsm z (hVK0 hz.1) hnorm
    have hfastT : fast (a := 2) (b := 2) (T z).2 = fast (a := 2) (b := 2) z.2 := hact z hzO
    obtain ⟨b, hb, hbI⟩ := hVsub hz.1
    have hba := hball b (hgoodr b hb).1
    have h1 : ∀ i, |fast (a := 2) (b := 2) (T z).2 i - action_center G m0 m a i| ≤ δft := by
      intro i
      rw [hfastT, ← hbI]
      exact hba i
    have h2 : ∀ i, poincareGamma (planetBlock (n := 2) (T z) i) ≤ δft := by
      intro i
      have hg : poincareGamma (planetBlock (n := 2) (T z) i) =
          ((slow (T z).1 i) ^ 2 + (slow (T z).2 i) ^ 2) / 2 := by
        simp [poincareGamma, planetBlock]
      rw [hg]
      have hε := Real.sq_sqrt hδft.le
      have e1 : |slow (T z).1 i| ≤ ‖p11cL_slow (T z)‖ :=
        (norm_le_pi_norm (p11cL_slow (T z)).1 i).trans (le_max_left _ _)
      have e2 : |slow (T z).2 i| ≤ ‖p11cL_slow (T z)‖ :=
        (norm_le_pi_norm (p11cL_slow (T z)).2 i).trans (le_max_right _ _)
      have s1 : slow (T z).1 i ^ 2 ≤ δft := by
        rw [← sq_abs]; nlinarith [abs_nonneg (slow (T z).1 i)]
      have s2 : slow (T z).2 i ^ 2 ≤ δft := by
        rw [← sq_abs]; nlinarith [abs_nonneg (slow (T z).2 i)]
      linarith
    exact (hft (T z) h1 h2).2.2
  · -- analyticity of the coupling
    intro u hu
    exact (hAn u.2 (hclO hu.2)).comp (analyticAt_snd (𝕜 := ℝ))
  · -- periodicity of the coupling
    intro μ _ z hz k
    have hzO : z ∈ O := hCO (hcylC hz)
    show fMov G m0 m (total_chart G m0 m T (z + fastShift (a := 2) (b := 2) k)) =
      fMov G m0 m (total_chart G m0 m T z)
    rw [hper z hzO k]
  · -- fast diffeomorphism
    exact fast_diffeo (G * m0) m (fun i => lo i / 2) (fun i => 2 * hi i) hκ hm
      (fun i => by have := hlo i; positivity)
      (fun i => by have := hhi i; have := hlo i; have := hlohi i; linarith)
  · -- Birkhoff form
    have h := hBNF 1 one_pos r0 hr0pos hr0le
    intro μ hμ I hI
    exact h μ hμ I (hVint hI)
  · intro μ _ I hI
    obtain ⟨hc, hax⟩ := hβ I hI
    have := (hBB _ hc).1
    exact this
  · intro μ _ I hI
    obtain ⟨hc, hax⟩ := hβ I hI
    exact (hBB _ hc).2

end PlanarAssembly
end KAM.Planetary
end
