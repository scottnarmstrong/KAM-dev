/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.Jets
public import KAM.Strip.AnalyticTaylor

/-!
# P Part 5: the uniform fifth-order remainder (`bpP:p5:uniform-remainder`)

`schwarz_order_five` is the higher-order Schwarz lemma (`stepP:p5:ur-schwarz`): a holomorphic
function on a disc, bounded by `M` and vanishing to order five at the centre, satisfies
`‖g z‖ ≤ M / R ^ 5 * ‖z‖ ^ 5`. It is derived from the maximum principle for `g z / z ^ 5` on
circles of radius `R' < R`, then `R' ↑ R`.

`uniform_remainder` (`stepP:p5:ur-bound`, `stepP:p5:ur-schwarz`) bounds the average by the
extension bound `MP`, the jets by Cauchy estimates, and applies `schwarz_order_five` on the complex
line through `x` using the vanishing remainder jet of `birkhoff_ext`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-REM.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology MeasureTheory
open scoped BigOperators

namespace KAM.Planetary

variable {a b : ℕ}

/-- Order-five factorisation: a function holomorphic near `0` and with vanishing jet of order
`≤ 4` has a holomorphic quotient by `z ^ 5`, bounded on circles. -/
theorem schwarz_quotient_bound {R M : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hbound : ∀ z ∈ ball (0:ℂ) R, ‖g z‖ ≤ M)
    (hjet : ∀ k : ℕ, k ≤ 4 → iteratedDeriv k g 0 = 0) {R' : ℝ} (hR'0 : 0 < R') (hR' : R' < R) :
    ∀ z ∈ closedBall (0:ℂ) R', ‖g z‖ ≤ M / R' ^ 5 * ‖z‖ ^ 5 := by
  have hopen : IsOpen (ball (0:ℂ) R) := isOpen_ball
  have hg0 : AnalyticAt ℂ g 0 := hg.analyticAt (hopen.mem_nhds (by simpa using hR))
  have hord : ((5 : ℕ) : ℕ∞) ≤ analyticOrderAt g 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg0).2
      fun i hi => hjet i (by omega)
  obtain ⟨k, hk, hev⟩ := (natCast_le_analyticOrderAt hg0).1 hord
  set h : ℂ → ℂ := Function.update (fun z => (z ^ 5)⁻¹ * g z) 0 (k 0) with hh
  have hev' : ∀ᶠ z in 𝓝 (0:ℂ), h z = k z := by
    have hne : ∀ᶠ z in 𝓝[≠] (0:ℂ), h z = k z := by
      filter_upwards [(nhdsWithin_le_nhds hev), self_mem_nhdsWithin] with z hz hz0
      have hz0' : z ≠ 0 := hz0
      rw [hh, Function.update_of_ne hz0', hz]
      simp only [sub_zero, smul_eq_mul]
      field_simp
    have h0 : h 0 = k 0 := by simp [hh]
    rw [eventually_nhdsWithin_iff] at hne
    filter_upwards [hne] with z hz
    by_cases hz0 : z = 0
    · rw [hz0, h0]
    · exact hz hz0
  have hdiff : DifferentiableOn ℂ h (closedBall 0 R') := by
    intro z hz
    have hzR : z ∈ ball (0:ℂ) R := by
      rw [mem_ball_zero_iff]; rw [mem_closedBall_zero_iff] at hz; linarith
    by_cases hz0 : z = 0
    · subst hz0
      exact ((hk.differentiableAt).congr_of_eventuallyEq hev').differentiableWithinAt
    · have : DifferentiableAt ℂ h z := by
        have hgz : DifferentiableAt ℂ g z := hg.differentiableAt (hopen.mem_nhds hzR)
        have hq : DifferentiableAt ℂ (fun z => (z ^ 5)⁻¹ * g z) z :=
          ((differentiableAt_id.pow 5).inv (pow_ne_zero 5 hz0)).mul hgz
        refine hq.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
        simp [hh, Function.update_of_ne hw]
      exact this.differentiableWithinAt
  have hdc : DiffContOnCl ℂ h (ball 0 R') := by
    refine ⟨hdiff.mono ball_subset_closedBall, ?_⟩
    rw [closure_ball _ hR'0.ne']
    exact hdiff.continuousOn
  have hfront : ∀ z ∈ frontier (ball (0:ℂ) R'), ‖h z‖ ≤ M / R' ^ 5 := by
    intro z hz
    rw [frontier_ball _ hR'0.ne', mem_sphere_zero_iff_norm] at hz
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hz; linarith
    have hzR : z ∈ ball (0:ℂ) R := by rw [mem_ball_zero_iff]; linarith
    rw [hh, Function.update_of_ne hz0, norm_mul, norm_inv, norm_pow, hz, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right (hbound z hzR) (by positivity)
  intro z hz
  have hzcl : z ∈ closure (ball (0:ℂ) R') := by rwa [closure_ball _ hR'0.ne']
  have hbd := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) hdc hfront hzcl
  by_cases hz0 : z = 0
  · subst hz0
    have := hjet 0 (by omega)
    simp only [iteratedDeriv_zero] at this
    simp [this]
  · rw [hh, Function.update_of_ne hz0, norm_mul, norm_inv, norm_pow] at hbd
    have hzpos : 0 < ‖z‖ ^ 5 := by positivity
    rw [inv_mul_le_iff₀ hzpos] at hbd
    simpa [mul_comm] using hbd

/-- Higher-order Schwarz, used after restricting to a complex line. -/
theorem schwarz_order_five {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hbound : ∀ z ∈ ball (0:ℂ) R, ‖g z‖ ≤ M)
    (hjet : ∀ k : ℕ, k ≤ 4 → iteratedDeriv k g 0 = 0) :
    ∀ z ∈ ball (0:ℂ) R, ‖g z‖ ≤ M/R^5*‖z‖^5 := by
  intro z hz
  have _ := hM
  rw [mem_ball_zero_iff] at hz
  have hlim : Tendsto (fun R' : ℝ => M / R' ^ 5 * ‖z‖ ^ 5) (𝓝[<] R) (𝓝 (M / R ^ 5 * ‖z‖ ^ 5)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have : ContinuousAt (fun R' : ℝ => M / R' ^ 5 * ‖z‖ ^ 5) R := by
      have : R ^ 5 ≠ 0 := by positivity
      fun_prop (disch := assumption)
    exact this.tendsto
  refine ge_of_tendsto hlim ?_
  have hev : ∀ᶠ R' in 𝓝[<] R, ‖z‖ < R' := by
    have : Ioo ‖z‖ R ∈ 𝓝[<] R := Ioo_mem_nhdsLT hz
    filter_upwards [this] with R' hR' using hR'.1
  filter_upwards [hev, self_mem_nhdsWithin] with R' hzR' hR'lt
  have hR'0 : 0 < R' := lt_of_le_of_lt (norm_nonneg z) hzR'
  exact schwarz_quotient_bound hR hg hbound hjet hR'0 hR'lt z
    (by rw [mem_closedBall_zero_iff]; exact hzR'.le)

/-! ### Bounds for the complex average and its jets -/

theorem actionNbhd_mono_quarter (d : PGData a b) {I : Fin a → ℂ}
    (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 4)) :
    I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2) := by
  have := (pgExtension d).delta_pos
  obtain ⟨J, hJ, hlt⟩ := hI
  exact ⟨J, hJ, by linarith⟩

theorem pgOscRadius_lt_one (d : PGData a b) : pgOscRadius d < 1 := by
  have h1 := (pgExtension d).delta_lt
  have h2 : pgOscRadius d ≤ (pgExtension d).delta / 4 := min_le_right _ _
  linarith

/-- The complex average is bounded by the extension bound `MP`. -/
theorem complexAverage_norm_le (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {z : JetE a b} (hz : z ∈ avgDom d) : ‖complexAverage d mu z.1 z.2‖ ≤ (pgExtension d).MP := by
  have hpi := Real.pi_pos
  have hMP := (pgExtension d).MP_pos
  set Q : Set (Fin a → ℝ) := pi univ fun _ : Fin a => Icc (0 : ℝ) (2 * Real.pi) with hQdef
  have hQ : IsCompact Q := isCompact_univ_pi fun _ => isCompact_Icc
  have hvol : (volume Q).toReal = (2 * Real.pi) ^ a := by
    rw [hQdef, Set.pi_univ_Icc, Real.volume_Icc_pi_toReal (fun _ => by simp; positivity)]
    simp
  have hint : ‖∫ phi in Q, (pgExtension d).P mu
      (assembleComplex z.1 (KAM.realInclusion a phi) z.2.2 z.2.1)‖ ≤
      (pgExtension d).MP * (volume Q).toReal :=
    norm_setIntegral_le_of_norm_le_const hQ.measure_lt_top fun phi _ =>
      (pgExtension d).bound mu hmu _ (avgInt_mem d hz phi)
  unfold complexAverage
  rw [norm_mul, norm_inv, norm_pow]
  have h2 : ‖((2 * Real.pi : ℝ) : ℂ)‖ = 2 * Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  push_cast at h2
  rw [h2]
  rw [hvol] at hint
  have hpos : 0 < (2 * Real.pi) ^ a := by positivity
  calc ((2 * Real.pi) ^ a)⁻¹ * _ ≤
        ((2 * Real.pi) ^ a)⁻¹ * ((pgExtension d).MP * (2 * Real.pi) ^ a) := by gcongr
    _ = (pgExtension d).MP := by field_simp

theorem complexAverage_differentiableOn (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℂ} (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) :
    DifferentiableOn ℂ (complexAverage d mu I) (ball 0 (pgOscRadius d)) := by
  have hf : DifferentiableOn ℂ (fun x : PGComplexPhase b => ((I, x) : JetE a b))
      (ball 0 (pgOscRadius d)) :=
    ((differentiable_const I).prodMk differentiable_id).differentiableOn
  exact (avgFun_differentiableOn d hmu).comp hf fun x hx => ⟨hI, by simpa using hx⟩

theorem remainder_slice_differentiableOn (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℂ} (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) :
    DifferentiableOn ℂ (pgRemainder d mu I) (ball 0 (pgOscRadius d)) := by
  have hf : DifferentiableOn ℂ (fun x : PGComplexPhase b => ((I, x) : JetE a b))
      (ball 0 (pgOscRadius d)) :=
    ((differentiable_const I).prodMk differentiable_id).differentiableOn
  exact (pgRemainder_differentiableOn d hmu).comp hf fun x hx => ⟨hI, by simpa using hx⟩

/-- Cauchy estimate for the jets of the average at `x = 0`, uniform in `mu` and `I`. -/
theorem jet_norm_le (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℂ} (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) (n : ℕ) :
    ‖iteratedFDeriv ℂ n (complexAverage d mu I) 0‖ ≤
      (n / (pgOscRadius d / 2)) ^ n * (pgExtension d).MP := by
  have hpos := pgOscRadius_pos d
  refine KAM.norm_iteratedFDeriv_le_of_closedBall isOpen_ball
    (complexAverage_differentiableOn d hmu hI) (half_pos hpos)
    (closedBall_subset_ball (by linarith)) (fun w hw => ?_) n
  have hw' : ‖w‖ < pgOscRadius d := by
    rw [mem_closedBall_zero_iff] at hw; linarith
  exact complexAverage_norm_le d hmu (z := (I, w)) ⟨hI, hw'⟩

theorem norm_single_le_one (j : Fin b) : ‖(Pi.single j (1 : ℂ) : Fin b → ℂ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem norm_yvec_le_one (j : Fin b) :
    ‖((0 : Fin b → ℂ), (Pi.single j (1 : ℂ) : Fin b → ℂ))‖ ≤ 1 := by
  rw [Prod.norm_def]
  simpa using norm_single_le_one j

theorem mlin_apply_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}
    (M : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) ℂ) (m : Fin n → E)
    (hm : ∀ i, ‖m i‖ ≤ 1) : ‖M m‖ ≤ ‖M‖ :=
  (M.le_opNorm m).trans (mul_le_of_le_one_right (norm_nonneg _)
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hm i))

theorem norm_cOsc_le {x : PGComplexPhase b} (hx : ‖x‖ ≤ 1) (j : Fin b) : ‖cOsc x j‖ ≤ 1 := by
  have h1 : ‖x.1 j‖ ≤ 1 := (norm_le_pi_norm x.1 j).trans ((le_max_left _ _).trans hx)
  have h2 : ‖x.2 j‖ ≤ 1 := (norm_le_pi_norm x.2 j).trans ((le_max_right _ _).trans hx)
  unfold cOsc
  have h2' : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_div, h2']
  have : ‖x.1 j ^ 2 + x.2 j ^ 2‖ ≤ 2 := by
    calc _ ≤ ‖x.1 j ^ 2‖ + ‖x.2 j ^ 2‖ := norm_add_le _ _
      _ ≤ 1 + 1 := by
        rw [norm_pow, norm_pow]
        gcongr <;> simp [pow_le_one₀, h1, h2]
      _ = 2 := by norm_num
  linarith [div_le_one_of_le₀ this (by norm_num : (0:ℝ) ≤ 2)]

theorem cPoly_norm_le {c0 : ℂ} {Om : Fin b → ℂ} {be : Matrix (Fin b) (Fin b) ℂ} {A0 A2 A4 : ℝ}
    (h0 : ‖c0‖ ≤ A0) (h2 : ∀ j, ‖Om j‖ ≤ A2) (h4 : ∀ i j, ‖be i j‖ ≤ A4)
    {x : PGComplexPhase b} (hx : ‖x‖ ≤ 1) :
    ‖cPoly c0 Om be x‖ ≤ A0 + b * A2 + b ^ 2 * A4 := by
  unfold cPoly
  have hS1 : ‖∑ j, Om j * cOsc x j‖ ≤ b * A2 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖Om j * cOsc x j‖ ≤ ∑ _j : Fin b, A2 := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]
          exact (mul_le_of_le_one_right (norm_nonneg _) (norm_cOsc_le hx j)).trans (h2 j)
      _ = b * A2 := by simp
  have hS2 : ‖(1 / 2 : ℂ) * ∑ i, ∑ j, be i j * cOsc x i * cOsc x j‖ ≤ b ^ 2 * A4 := by
    have hn : ‖∑ i, ∑ j, be i j * cOsc x i * cOsc x j‖ ≤ b ^ 2 * A4 := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i, ‖∑ j, be i j * cOsc x i * cOsc x j‖ ≤ ∑ _i : Fin b, (b * A4 : ℝ) :=
            Finset.sum_le_sum fun i _ => by
              refine (norm_sum_le _ _).trans ?_
              calc ∑ j, ‖be i j * cOsc x i * cOsc x j‖ ≤ ∑ _j : Fin b, A4 :=
                    Finset.sum_le_sum fun j _ => by
                      rw [norm_mul, norm_mul]
                      exact ((mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
                        (norm_cOsc_le hx j)).trans
                        (mul_le_of_le_one_right (norm_nonneg _) (norm_cOsc_le hx i))).trans
                        (h4 i j)
                _ = b * A4 := by simp
        _ = b ^ 2 * A4 := by simp; ring
    have h12 : ‖(1 / 2 : ℂ)‖ ≤ 1 := by norm_num
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) h12).trans hn
  calc _ ≤ ‖c0 + ∑ j, Om j * cOsc x j‖ + ‖(1 / 2 : ℂ) * ∑ i, ∑ j, be i j * cOsc x i * cOsc x j‖ :=
        norm_add_le _ _
    _ ≤ (‖c0‖ + ‖∑ j, Om j * cOsc x j‖) + _ := by gcongr; exact norm_add_le _ _
    _ ≤ A0 + b * A2 + b ^ 2 * A4 := by linarith

theorem pgRemainder_eq_cPoly (d : PGData a b) (mu : ℝ) (I : Fin a → ℂ) (x : PGComplexPhase b) :
    pgRemainder d mu I x = complexAverage d mu I x -
      cPoly (jetP0 d mu I) (jetOmega d mu I) (jetBeta d mu I) x := by
  have hf : blockFast (Fin.append I (fun j => (x.1 j ^ 2 + x.2 j ^ 2) / 2) :
      Fin (a + b) → ℂ) = I := funext fun i => Fin.append_left _ _ i
  have hs : ∀ j, blockSlow (Fin.append I (fun j => (x.1 j ^ 2 + x.2 j ^ 2) / 2) :
      Fin (a + b) → ℂ) j = cOsc x j := fun j => Fin.append_right _ _ j
  unfold pgRemainder jetPolynomial cPoly
  rw [hf]
  simp only [hs]

/-- The remainder is bounded uniformly on the half-disc, by the extension bound and the Cauchy
estimates for the jets (`stepP:p5:ur-bound`). -/
theorem remainder_bound (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℂ} (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2))
    {x : PGComplexPhase b} (hx : ‖x‖ < pgOscRadius d / 2) :
    ‖pgRemainder d mu I x‖ ≤ (pgExtension d).MP +
      ((pgExtension d).MP + b * ((2 / (pgOscRadius d / 2)) ^ 2 * (pgExtension d).MP) +
        b ^ 2 * ((4 / (pgOscRadius d / 2)) ^ 4 * (pgExtension d).MP)) := by
  have hpos := pgOscRadius_pos d
  have hx1 : ‖x‖ ≤ 1 := by linarith [pgOscRadius_lt_one d]
  have hxd : x ∈ ball (0 : PGComplexPhase b) (pgOscRadius d) := by
    rw [mem_ball_zero_iff]; linarith
  rw [pgRemainder_eq_cPoly]
  refine (norm_sub_le _ _).trans (add_le_add (complexAverage_norm_le d hmu (z := (I, x))
    ⟨hI, by simpa using hxd⟩) (cPoly_norm_le (x := x) ?_ (fun j => ?_) (fun i j => ?_) hx1))
  · have := complexAverage_norm_le d hmu (z := (I, (0 : PGComplexPhase b))) (mem_avgDom_zero d hI)
    exact this
  · have h := jet_norm_le d hmu hI 2
    refine (mlin_apply_le _ _ fun _ => norm_yvec_le_one j).trans ?_
    simpa using h
  · have h := jet_norm_le d hmu hI 4
    have h' : ‖iteratedFDeriv ℂ 4 (complexAverage d mu I) 0‖ ≤
        (4 / (pgOscRadius d / 2)) ^ 4 * (pgExtension d).MP := by simpa using h
    unfold jetBeta
    by_cases hij : i = j
    · simp only [hij, ite_true]
      rw [norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans
        ((mlin_apply_le _ _ fun _ => norm_yvec_le_one j).trans h')
    · simp only [hij, ite_false]
      exact (mlin_apply_le _ _ fun k => by
        by_cases hk : k.val < 2 <;> simp only [hk, ite_true, ite_false] <;>
          [exact norm_yvec_le_one i; exact norm_yvec_le_one j]).trans h'

theorem remainder_const_pos (d : PGData a b) :
    0 < (pgExtension d).MP +
      ((pgExtension d).MP + b * ((2 / (pgOscRadius d / 2)) ^ 2 * (pgExtension d).MP) +
        b ^ 2 * ((4 / (pgOscRadius d / 2)) ^ 4 * (pgExtension d).MP)) := by
  have := (pgExtension d).MP_pos
  positivity

theorem uniform_remainder (d : PGData a b) : ∃ r1 CQ : ℝ,
    0 < r1 ∧ r1 ≤ pgOscRadius d ∧ 0 < CQ ∧
    ∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/4),
      ∀ x : PGComplexPhase b, ‖x‖ ≤ r1 → ‖pgRemainder d mu I x‖ ≤ CQ*‖x‖^5 := by
  have hpos := pgOscRadius_pos d
  set R : ℝ := pgOscRadius d / 2 with hRdef
  have hR : 0 < R := half_pos hpos
  set M1 : ℝ := (pgExtension d).MP +
      ((pgExtension d).MP + b * ((2 / (pgOscRadius d / 2)) ^ 2 * (pgExtension d).MP) +
        b ^ 2 * ((4 / (pgOscRadius d / 2)) ^ 4 * (pgExtension d).MP)) with hM1
  have hM1pos : 0 < M1 := remainder_const_pos d
  refine ⟨pgOscRadius d / 4, M1 / R ^ 5, by positivity, by linarith, by positivity, ?_⟩
  intro mu hmu I hI x hx
  have hI' := actionNbhd_mono_quarter d hI
  by_cases hx0 : x = 0
  · subst hx0
    have h := remainder_jet_tube d hmu hI' 0 (by norm_num)
    have h0 := congrArg (fun M => M (fun _ => (0 : PGComplexPhase b))) h
    simp only [iteratedFDeriv_zero_apply] at h0
    simp [h0]
  have hs : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hsR : ‖x‖ < R := by rw [hRdef]; linarith
  have hscale : ∀ t : ℂ, ‖t‖ < R / ‖x‖ → ‖t • x‖ < R := fun t ht => by
    rw [norm_smul]
    rwa [lt_div_iff₀ hs] at ht
  have hdiff := remainder_slice_differentiableOn d hmu hI'
  have hg : DifferentiableOn ℂ (fun t : ℂ => pgRemainder d mu I (t • x)) (ball 0 (R / ‖x‖)) :=
    hdiff.comp (differentiable_id.smul_const x).differentiableOn fun t ht =>
      mem_ball_zero_iff.2 ((hscale t (mem_ball_zero_iff.1 ht)).trans_le (by rw [hRdef]; linarith))
  have hjet : ∀ k : ℕ, k ≤ 4 → iteratedDeriv k (fun t : ℂ => pgRemainder d mu I (t • x)) 0 = 0 := by
    intro k hk
    have := KAM.iteratedDeriv_line_eq_iteratedFDeriv isOpen_ball hdiff
      (w := 0) (by simpa using hpos) x k
    simp only [zero_add] at this
    rw [this, remainder_jet_tube d hmu hI' k hk]
    rfl
  have key := schwarz_order_five (R := R / ‖x‖) (M := M1) (div_pos hR hs) hM1pos.le hg
    (fun t ht => remainder_bound d hmu hI' (hscale t (mem_ball_zero_iff.1 ht))) hjet 1
    (by rw [mem_ball_zero_iff, norm_one, lt_div_iff₀ hs, one_mul]; exact hsR)
  simp only [one_smul, norm_one, one_pow, mul_one] at key
  refine key.trans (le_of_eq ?_)
  field_simp

end KAM.Planetary

end
