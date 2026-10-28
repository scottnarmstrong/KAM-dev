/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.Coefficients
public import KAM.Nekhoroshev.Averaging.Rank
public import KAM.Nekhoroshev.Averaging.SlabBox
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Part N12: slab volumes uniform in the direction (`bpN:p12:slab`)

The frequency slab `vol {I ∈ G : |e · ω(I)| ≤ v} ≤ C₁ v`, uniformly in the unit direction `e`.

* `sl-cover`: by uniform continuity of `M = Dω` on a compact neighbourhood of `G` and finitely many
  cubes `closedBall x r`, `x ∈ t`, covering `G`; the constants `r`, `t` do not depend on `e`
  because the coordinate `∂ⱼ (e · ω) = (Mᵀ e)ⱼ` is linear in `e`.
* `sl-box`: `AvgSlab.volume_box_le` in a cube where one coordinate derivative has modulus `≥ cc`.
* `sl-sum`: sum over the cubes for `v ≤ λ/2`; for `v > λ/2` use `vol G ≤ (2 vol G / λ) v`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Nekhoroshev

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

namespace AvgSlab

/-- `e · ω(I)`. -/
def lineFun (h : (Fin n → ℂ) → ℂ) (e I : Fin n → ℝ) : ℝ :=
  ∑ i, e i * KAM.frequencyMap h I i

/-- `(Mᵀ e)ⱼ`, the `j`-th partial derivative of `lineFun h e`. -/
def gradFun (h : (Fin n → ℂ) → ℂ) (j : Fin n) (e I : Fin n → ℝ) : ℝ :=
  ∑ i, avgM h I i j * e i

theorem closedBall_subset_domain (d : AveragingData n R s h f) :
    closedBall (0 : Fin n → ℝ) (7 * R / 8) ⊆ realActionDomain n R s := by
  intro I hI
  rw [realActionDomain_eq d.hR d.hs]
  simp only [mem_closedBall, dist_zero_right, mem_ball] at hI ⊢
  linarith [d.hR, d.hs]

/-- Uniform continuity of `M` near `G`, with a radius independent of everything else. -/
theorem unif_M (d : AveragingData n R s h f) {θ : ℝ} (hθ : 0 < θ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R / 8 ∧ ∀ I ∈ closedBall (0 : Fin n → ℝ) (7 * R / 8),
      ∀ I' ∈ closedBall (0 : Fin n → ℝ) (7 * R / 8), dist I I' ≤ 2 * r →
        ∀ i j, |avgM h I i j - avgM h I' i j| ≤ θ := by
  have hR := d.hR
  have hU := isOpen_realActionDomain (n := n) d.hR d.hs
  have hf2 := AvgRank.contDiffOn_freq d
  have hdc : ContinuousOn (fderiv ℝ (KAM.frequencyMap h)) (realActionDomain n R s) :=
    hf2.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hsub := closedBall_subset_domain d
  have hcont : ContinuousOn (fun I : Fin n → ℝ => fun i j => avgM h I i j)
      (closedBall (0 : Fin n → ℝ) (7 * R / 8)) := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    have : ContinuousOn (fun I => avgM h I i j) (realActionDomain n R s) :=
      (continuous_apply i).comp_continuousOn
        (ContinuousOn.clm_apply hdc (continuousOn_const (c := (Pi.single j (1 : ℝ) : Fin n → ℝ))))
    exact this.mono hsub
  have huc := (isCompact_closedBall (0 : Fin n → ℝ) (7 * R / 8)).uniformContinuousOn_of_continuous
    hcont
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc θ hθ
  refine ⟨min (δ / 4) (R / 8), lt_min (by positivity) (by positivity), min_le_right _ _,
    fun I hI I' hI' hd i j => ?_⟩
  have hlt : dist I I' < δ := by
    have := min_le_left (δ / 4) (R / 8)
    linarith
  have h1 := hδ' I hI I' hI' hlt
  have h2 : dist (avgM h I i j) (avgM h I' i j) ≤ dist (fun i j => avgM h I i j)
      (fun i j => avgM h I' i j) :=
    (dist_le_pi_dist (fun j => avgM h I i j) (fun j => avgM h I' i j) j).trans
      (dist_le_pi_dist (fun i j => avgM h I i j) (fun i j => avgM h I' i j) i)
  rw [Real.dist_eq] at h2
  exact h2.trans h1.le

theorem hasDerivAt_line (d : AveragingData n R s h f) {I : Fin n → ℝ}
    (hI : I ∈ realActionDomain n R s) (e : Fin n → ℝ) (j : Fin n) :
    HasDerivAt (fun t => lineFun h e (Function.update I j t)) (gradFun h j e I) (I j) := by
  have hU := isOpen_realActionDomain (n := n) d.hR d.hs
  have hD : DifferentiableAt ℝ (KAM.frequencyMap h) I :=
    ((AvgRank.contDiffOn_freq d).differentiableOn (by norm_num)).differentiableAt
      (hU.mem_nhds hI)
  have h2 : HasFDerivAt (KAM.frequencyMap h) (fderiv ℝ (KAM.frequencyMap h) I)
      (Function.update I j (I j)) := by
    rw [Function.update_eq_self]; exact hD.hasFDerivAt
  have hcomp := h2.comp_hasDerivAt (I j) (hasDerivAt_update I j (I j))
  have key : ∀ i, HasDerivAt (fun t => e i * KAM.frequencyMap h (Function.update I j t) i)
      (e i * avgM h I i j) (I j) := fun i =>
    ((hasDerivAt_pi.1 hcomp i).const_mul (e i) : _)
  have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => key i
  refine this.congr_deriv ?_
  unfold gradFun
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- A coordinate of a vector with large Euclidean norm is large. -/
theorem exists_coord {N : ℕ} (hN : 0 < N) (a : Fin N → ℝ) {T : ℝ} (hT : T ≤ ∑ j, a j ^ 2) :
    ∃ j, T / N ≤ a j ^ 2 := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ : Fin N => T / N) (g := fun j => a j ^ 2) (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ (by positivity)]
      exact hT)
  exact ⟨j, hj⟩


/-- Frequency slab, uniform in the unit direction (the `avgQ`-free core of `slab`). -/
theorem slab_freq (d : AveragingData n R s h f) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ e : Fin n → ℝ, euclid e = 1 → ∀ v : ℝ, 0 < v →
      volume {I ∈ avgG n R | |∑ i, e i * KAM.frequencyMap h I i| ≤ v} ≤
        ENNReal.ofReal (C₁ * v) := by
  have hn := d.hn
  have hR := d.hR
  have hdom := closedBall_subset_domain d
  have hU := isOpen_realActionDomain (n := n) d.hR d.hs
  have hfc : ContinuousOn (KAM.frequencyMap h) (realActionDomain n R s) :=
    (AvgRank.contDiffOn_freq d).continuousOn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨lam, hlam, hlamb⟩ := «lambda» d
  have hNpos : 0 < m + 1 := Nat.succ_pos m
  set N : ℝ := ((m + 1 : ℕ) : ℝ) with hN
  have hNr : 0 < N := by positivity
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
  set cc : ℝ := lam / (4 * Real.sqrt N) with hcc
  have hccpos : 0 < cc := by positivity
  obtain ⟨r, hr0, hrR, hunif⟩ := unif_M d (θ := cc / N) (by positivity)
  obtain ⟨t₀, htG₀, htfin, hcover₀⟩ := finite_cover_balls_of_compact
    (isCompact_closedBall (0 : Fin (m + 1) → ℝ) (3 * R / 4)) hr0
  set t : Finset (Fin (m + 1) → ℝ) := htfin.toFinset with ht
  have htG : ∀ x ∈ t, x ∈ closedBall (0 : Fin (m + 1) → ℝ) (3 * R / 4) := fun x hx =>
    htG₀ (htfin.mem_toFinset.1 hx)
  have hcover : closedBall (0 : Fin (m + 1) → ℝ) (3 * R / 4) ⊆ ⋃ x ∈ t, ball x r := by
    intro I hI
    have := hcover₀ hI
    simpa [ht] using this
  have hGdef : avgG (m + 1) R = closedBall 0 (3 * R / 4) := rfl
  -- a cube around a point of `G` stays in the good compact set
  have hcb : ∀ x ∈ avgG (m + 1) R, ∀ I ∈ closedBall x r,
      I ∈ closedBall (0 : Fin (m + 1) → ℝ) (7 * R / 8) := by
    intro x hx I hI
    rw [hGdef, mem_closedBall, dist_zero_right] at hx
    rw [mem_closedBall] at hI
    rw [mem_closedBall, dist_zero_right]
    have := norm_le_norm_add_norm_sub' I x
    have h3 : ‖I - x‖ = dist I x := (dist_eq_norm I x).symm
    linarith
  have hbox : ∀ e : Fin (m + 1) → ℝ, euclid e = 1 → ∀ v : ℝ, 0 < v → v ≤ lam / 2 →
      ∀ x ∈ avgG (m + 1) R,
      volume (closedBall x r ∩ avgG (m + 1) R ∩ {I | |lineFun h e I| ≤ v}) ≤
        ENNReal.ofReal ((2 * r) ^ m * (2 * v / cc)) := by
    intro e he v hv hvl x hx
    rcases (closedBall x r ∩ avgG (m + 1) R ∩ {I | |lineFun h e I| ≤ v}).eq_empty_or_nonempty
      with hE | ⟨I₀, ⟨hI₀b, hI₀G⟩, hI₀v⟩
    · rw [hE]; simp
    have hI₀v' : |lineFun h e I₀| ≤ v := hI₀v
    -- a large coordinate of `Mᵀ e` at `I₀`
    have hsq := hlamb I₀ hI₀G e he
    rw [AvgRank.euclid_sq] at hsq
    have hφ2 : (∑ i, e i * KAM.frequencyMap h I₀ i) ^ 2 ≤ (lam / 2) ^ 2 := by
      have : |lineFun h e I₀| ≤ lam / 2 := hI₀v'.trans hvl
      have h0 : (lineFun h e I₀) ^ 2 ≤ (lam / 2) ^ 2 :=
        sq_le_sq' (by linarith [(abs_le.1 this).1]) (abs_le.1 this).2
      exact h0
    obtain ⟨j, hj⟩ := exists_coord hNpos (fun j => ∑ i, avgM h I₀ i j * e i)
      (T := 3 * lam ^ 2 / 4) (by nlinarith [hsq, hφ2])
    have h2cc : 2 * cc ≤ |gradFun h j e I₀| := by
      have h2 : (2 * cc) ^ 2 = lam ^ 2 / (4 * N) := by
        rw [hcc]; field_simp; rw [Real.sq_sqrt hNr.le]; ring
      have : (2 * cc) ^ 2 ≤ (gradFun h j e I₀) ^ 2 := by
        rw [h2]
        refine le_trans ?_ hj
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg lam, hNr]
      have := sq_le_sq.1 this
      rwa [abs_of_pos (by positivity)] at this
    have he1 : ∀ i, |e i| ≤ 1 := fun i => by
      have := ((norm_le_euclid e).1).trans he.le
      simpa [Real.norm_eq_abs] using (norm_le_pi_norm e i).trans this
    have hg : ∀ I ∈ closedBall x r, cc ≤ |gradFun h j e I| := by
      intro I hI
      have hd : dist I I₀ ≤ 2 * r := by
        have := dist_triangle_right I I₀ x
        rw [mem_closedBall] at hI hI₀b
        linarith
      have hM := hunif I (hcb x hx I hI) I₀ (hcb x hx I₀ hI₀b) hd
      have hdiff : |gradFun h j e I - gradFun h j e I₀| ≤ cc := by
        unfold gradFun
        rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i, |avgM h I i j * e i - avgM h I₀ i j * e i|
            ≤ ∑ _i : Fin (m + 1), cc / N := Finset.sum_le_sum fun i _ => by
              rw [← sub_mul, abs_mul]
              calc |avgM h I i j - avgM h I₀ i j| * |e i| ≤ cc / N * 1 :=
                    mul_le_mul (hM i j) (he1 i) (abs_nonneg _) (by positivity)
                _ = cc / N := mul_one _
          _ = cc := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              rw [← hN]; field_simp
      have := abs_sub_abs_le_abs_sub (gradFun h j e I₀) (gradFun h j e I)
      rw [abs_sub_comm] at this
      linarith
    have hrcb : ∀ I ∈ closedBall x r, I ∈ realActionDomain (m + 1) R s :=
      fun I hI => hdom (hcb x hx I hI)
    have hφc : ContinuousOn (lineFun h e) (closedBall x r) := by
      refine continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ?_
      exact ((continuous_apply i).comp_continuousOn hfc).mono hrcb
    have hb := AvgSlab.volume_box_le (φ := lineFun h e) (g := gradFun h j e) (j := j) (c := x)
      (r := r) (c₁ := cc) (v := v) hr0.le hccpos hφc
      (fun I hI => hasDerivAt_line d (hrcb I hI) e j) hg
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)] at hb
    refine le_trans (measure_mono ?_) hb
    rintro I ⟨⟨hI1, -⟩, hI3⟩
    exact ⟨hI1, hI3⟩
  set V : ℝ := (2 * (3 * R / 4)) ^ (m + 1) with hV
  have hV0 : 0 ≤ V := by positivity
  set a : ℝ := (t.card : ℝ) * ((2 * r) ^ m * (2 / cc)) with ha
  have ha0 : 0 ≤ a := by positivity
  refine ⟨max 1 (max a (2 * V / lam)), le_max_left _ _, fun e he v hv => ?_⟩
  by_cases hvl : v ≤ lam / 2
  · have hcov : {I ∈ avgG (m + 1) R | |∑ i, e i * KAM.frequencyMap h I i| ≤ v} ⊆
        ⋃ x ∈ t, (closedBall x r ∩ avgG (m + 1) R ∩ {I | |lineFun h e I| ≤ v}) := by
      rintro I ⟨hIG, hIv⟩
      have := hcover hIG
      simp only [mem_iUnion] at this ⊢
      obtain ⟨x, hxt, hx⟩ := this
      exact ⟨x, hxt, ⟨ball_subset_closedBall hx, hIG⟩, hIv⟩
    calc volume {I ∈ avgG (m + 1) R | |∑ i, e i * KAM.frequencyMap h I i| ≤ v}
        ≤ volume (⋃ x ∈ t, (closedBall x r ∩ avgG (m + 1) R ∩ {I | |lineFun h e I| ≤ v})) :=
          measure_mono hcov
      _ ≤ ∑ x ∈ t, volume (closedBall x r ∩ avgG (m + 1) R ∩ {I | |lineFun h e I| ≤ v}) :=
          measure_biUnion_finset_le t _
      _ ≤ t.card • ENNReal.ofReal ((2 * r) ^ m * (2 * v / cc)) :=
          Finset.sum_le_card_nsmul _ _ _ fun x hx => hbox e he v hv hvl x (htG x hx)
      _ = ENNReal.ofReal (a * v) := by
          rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          rw [ha]; ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
          ((le_max_left _ _).trans (le_max_right _ _)) hv.le)
  · rw [not_le] at hvl
    calc volume {I ∈ avgG (m + 1) R | |∑ i, e i * KAM.frequencyMap h I i| ≤ v}
        ≤ volume (avgG (m + 1) R) := measure_mono fun I hI => hI.1
      _ = ENNReal.ofReal V := by
          rw [hGdef, Real.volume_pi_closedBall _ (by positivity), Fintype.card_fin]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc V = 2 * V / lam * (lam / 2) := by field_simp
            _ ≤ 2 * V / lam * v := mul_le_mul_of_nonneg_left hvl.le (by positivity)
            _ ≤ _ := mul_le_mul_of_nonneg_right
                ((le_max_right _ _).trans' (le_max_right _ _)) hv.le

end AvgSlab

theorem slab (d : AveragingData n R s h f) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧
      (∀ e : Fin n → ℝ, euclid e = 1 → ∀ v : ℝ, 0 < v →
        volume {I ∈ avgG n R | |∑ i, e i * KAM.frequencyMap h I i| ≤ v} ≤
          ENNReal.ofReal (C₁ * v)) ∧
      ∀ k : Fin n → ℤ, k ≠ 0 → ∀ u : ℝ, 0 < u →
        volume {I ∈ avgG n R | |avgQ h k I| ≤ u} ≤
          ENNReal.ofReal (C₁ * u / euclid (fun j => (k j : ℝ))) := by
  obtain ⟨C₁, hC₁, hC⟩ := AvgSlab.slab_freq d
  refine ⟨C₁, hC₁, hC, fun k hk u hu => ?_⟩
  set K : ℝ := euclid (fun j => (k j : ℝ)) with hK
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hKsq : K ^ 2 = ∑ j, (k j : ℝ) ^ 2 := AvgRank.euclid_sq _ |>.trans (by simp)
  have hKpos : 0 < K := by
    refine lt_of_le_of_ne hK0 fun h0 => hk ?_
    rw [← h0] at hKsq
    have : ∑ j, (k j : ℝ) ^ 2 = 0 := by rw [← hKsq]; ring
    funext j
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 this j
      (Finset.mem_univ j)
    simpa using this
  have he : euclid (fun j => (k j : ℝ) / K) = 1 := by
    have h2 : euclid (fun j => (k j : ℝ) / K) ^ 2 = 1 := by
      rw [AvgRank.euclid_sq]
      simp only [div_pow]
      rw [← Finset.sum_div, ← hKsq]
      field_simp
    have h0 : 0 ≤ euclid (fun j => (k j : ℝ) / K) := Real.sqrt_nonneg _
    nlinarith
  have hset : {I ∈ avgG n R | |avgQ h k I| ≤ u} =
      {I ∈ avgG n R | |∑ i, (fun j => (k j : ℝ) / K) i * KAM.frequencyMap h I i| ≤ u / K} := by
    ext I
    simp only [mem_ofPred_eq, and_congr_right_iff]
    intro _
    have : avgQ h k I = K * ∑ i, (k i : ℝ) / K * KAM.frequencyMap h I i := by
      unfold avgQ
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by field_simp
    rw [this, abs_mul, abs_of_pos hKpos, ← le_div_iff₀' hKpos]
  rw [hset]
  have := hC _ he (u / K) (by positivity)
  rwa [← mul_div_assoc] at this

/-- Derived constant specification; it is NEVER a premise of a source theorem. -/
def AvgSlabBound (h : (Fin n → ℂ) → ℂ) (R C₁ : ℝ) : Prop :=
  1 ≤ C₁ ∧ ∀ k : Fin n → ℤ, k ≠ 0 → ∀ u : ℝ, 0 < u →
    volume {I ∈ avgG n R | |avgQ h k I| ≤ u} ≤
      ENNReal.ofReal (C₁ * u / euclid (fun j => (k j : ℝ)))

/-- The numerical slab specification is constructed from the source data. -/
theorem exists_avgSlabBound (d : AveragingData n R s h f) : ∃ C₁ : ℝ, AvgSlabBound h R C₁ := by
  obtain ⟨C₁, hC₁, -, hk⟩ := slab d
  exact ⟨C₁, hC₁, hk⟩

end KAM.Nekhoroshev

end
