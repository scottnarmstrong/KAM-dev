/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.Setting
public import KAM.Nekhoroshev.Interfaces.Norms

/-!
# Part N12: uniform transversality (`bpN:p12:lambda`)

Node `lambda`. Under either alternative of the frozen `HasAveragingFrequencyRank`, the continuous
function `(I, e) ↦ |Mᵀ e|₂² + (e · ω(I))²` is positive on the compact set `avgG × {|e|₂ = 1}`
(`la-inj`: a vector annihilating the range of a surjective map is zero), hence has a positive
minimum (`la-cpt`), whose square root is the constant `lam`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Nekhoroshev

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

namespace AvgRank

theorem contDiffOn_freq (d : AveragingData n R s h f) :
    ContDiffOn ℝ 2 (KAM.frequencyMap h) (realActionDomain n R s) := by
  have hg : ContDiffOn ℝ 3 (realPart h) (realActionDomain n R s) := d.hh.2.2.2.2
  have hU := isOpen_realActionDomain (n := n) d.hR d.hs
  have hd : ContDiffOn ℝ 2 (fderiv ℝ (realPart h)) (realActionDomain n R s) :=
    hg.fderiv_of_isOpen hU (by norm_num)
  refine contDiffOn_pi.2 fun i => ?_
  exact ContDiffOn.clm_apply hd (contDiffOn_const (c := (Pi.single i (1 : ℝ) : Fin n → ℝ)))

theorem avgG_subset_actionBall (d : AveragingData n R s h f) : avgG n R ⊆ actionBall n R := by
  intro I hI
  have := d.hR
  simp only [avgG, actionBall, mem_closedBall, mem_ball, dist_zero_right] at hI ⊢
  linarith

theorem avgG_subset_domain (d : AveragingData n R s h f) : avgG n R ⊆ realActionDomain n R s := by
  intro I hI
  rw [realActionDomain_eq d.hR d.hs]
  have := avgG_subset_actionBall d hI
  simp only [actionBall, mem_ball, dist_zero_right] at this ⊢
  linarith [d.hs]

theorem fderiv_apply_eq (I v : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (KAM.frequencyMap h) I v i = ∑ j, avgM h I i j * v j := by
  have hsing : ∀ j, (Pi.single j (v j) : Fin n → ℝ) = v j • Pi.single j 1 := fun j => by
    ext k
    by_cases hk : k = j <;> simp [hk]
  conv_lhs => rw [← Finset.univ_sum_single v]
  simp [hsing, avgM, mul_comm]

theorem euclid_sq (x : Fin n → ℝ) : euclid x ^ 2 = ∑ i, x i ^ 2 := by
  unfold euclid
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

/-- `la-inj`: a vector annihilating the range of a surjective map is zero. -/
theorem false_of_orth {V : Type*} {e : Fin n → ℝ} (he : euclid e = 1)
    {g : V → Fin n → ℝ} (hg : Function.Surjective g)
    (horth : ∀ w, ∑ i, e i * g w i = 0) : False := by
  obtain ⟨w, hw⟩ := hg e
  have h1 := horth w
  rw [hw] at h1
  have h2 := euclid_sq e
  rw [he] at h2
  simp only [sq] at h2
  rw [h1] at h2
  norm_num at h2

/-- The quantity `|Mᵀ e|₂² + (e · ω)²`, written without `euclid`. -/
def gap (h : (Fin n → ℂ) → ℂ) (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∑ j, (∑ i, avgM h p.1 i j * p.2 i) ^ 2 + (∑ i, p.2 i * KAM.frequencyMap h p.1 i) ^ 2

theorem gap_pos (d : AveragingData n R s h f) {I e : Fin n → ℝ} (hI : I ∈ avgG n R)
    (he : euclid e = 1) : 0 < gap h (I, e) := by
  have hIa := avgG_subset_actionBall d hI
  have hnn : 0 ≤ gap h (I, e) :=
    add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
  refine lt_of_le_of_ne hnn fun h0 => ?_
  have hA : 0 ≤ ∑ j, (∑ i, avgM h I i j * e i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB : 0 ≤ (∑ i, e i * KAM.frequencyMap h I i) ^ 2 := sq_nonneg _
  have hA0 : ∑ j, (∑ i, avgM h I i j * e i) ^ 2 = 0 := by
    have : gap h (I, e) = _ + _ := rfl
    linarith
  have hB0 : ∑ i, e i * KAM.frequencyMap h I i = 0 := by
    have : gap h (I, e) = _ + _ := rfl
    have hB' : (∑ i, e i * KAM.frequencyMap h I i) ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (two_ne_zero) |>.1 hB'
  have hcol : ∀ j, ∑ i, avgM h I i j * e i = 0 := fun j =>
    pow_eq_zero_iff (two_ne_zero) |>.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 hA0 j (Finset.mem_univ j))
  have horth1 : ∀ v : Fin n → ℝ,
      ∑ i, e i * fderiv ℝ (KAM.frequencyMap h) I v i = 0 := by
    intro v
    simp only [fderiv_apply_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := hcol j
    calc ∑ i, e i * (avgM h I i j * v j) = (∑ i, avgM h I i j * e i) * v j := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [this, zero_mul]
  rcases d.hrank with hr | hr
  · exact false_of_orth he (hr I hIa) horth1
  · obtain ⟨_, hs'⟩ := hr I hIa
    refine false_of_orth he hs' fun w => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
    rw [Finset.sum_add_distrib, horth1 w.1]
    have : ∑ i, e i * (w.2 * KAM.frequencyMap h I i) =
        w.2 * ∑ i, e i * KAM.frequencyMap h I i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hB0]; ring

theorem gap_continuousOn (d : AveragingData n R s h f) :
    ContinuousOn (gap h) (avgG n R ×ˢ {e : Fin n → ℝ | euclid e = 1}) := by
  have hU := isOpen_realActionDomain (n := n) d.hR d.hs
  have hf2 := contDiffOn_freq d
  have hfc : ContinuousOn (KAM.frequencyMap h) (realActionDomain n R s) := hf2.continuousOn
  have hdc : ContinuousOn (fderiv ℝ (KAM.frequencyMap h)) (realActionDomain n R s) :=
    hf2.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hsub := avgG_subset_domain d
  have hfst : ContinuousOn Prod.fst (avgG n R ×ˢ {e : Fin n → ℝ | euclid e = 1}) :=
    continuousOn_fst
  have hmaps : MapsTo Prod.fst (avgG n R ×ˢ {e : Fin n → ℝ | euclid e = 1})
      (realActionDomain n R s) := fun p hp => hsub hp.1
  have hent : ∀ i j, ContinuousOn (fun p : (Fin n → ℝ) × (Fin n → ℝ) => avgM h p.1 i j)
      (avgG n R ×ˢ {e : Fin n → ℝ | euclid e = 1}) := by
    intro i j
    have : ContinuousOn (fun I => avgM h I i j) (realActionDomain n R s) :=
      (continuous_apply i).comp_continuousOn
        (ContinuousOn.clm_apply hdc (continuousOn_const (c := (Pi.single j (1 : ℝ) : Fin n → ℝ))))
    exact this.comp hfst hmaps
  have hom : ∀ i, ContinuousOn (fun p : (Fin n → ℝ) × (Fin n → ℝ) => KAM.frequencyMap h p.1 i)
      (avgG n R ×ˢ {e : Fin n → ℝ | euclid e = 1}) := fun i =>
    ((continuous_apply i).comp_continuousOn hfc).comp hfst hmaps
  have he : ∀ i, ContinuousOn (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.2 i)
      (avgG n R ×ˢ {e : Fin n → ℝ | euclid e = 1}) := fun i =>
    ((continuous_apply i).comp continuous_snd).continuousOn
  unfold gap
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum _ fun j _ => ?_
    exact (continuousOn_finsetSum _ fun i _ => (hent i j).mul (he i)).pow 2
  · exact (continuousOn_finsetSum _ fun i _ => (he i).mul (hom i)).pow 2

theorem isCompact_sphere : IsCompact {e : Fin n → ℝ | euclid e = 1} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · refine isClosed_eq ?_ continuous_const
    unfold euclid
    fun_prop
  · refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset fun e he => ?_
    have := (norm_le_euclid e).1
    simp only [mem_ofPred_eq] at he
    simpa [he] using this

end AvgRank

/-- Node `lambda`; escaped keyword preserves the graph's snake-case name. -/
theorem «lambda» (d : AveragingData n R s h f) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ I ∈ avgG n R, ∀ e : Fin n → ℝ, euclid e = 1 →
      (euclid (fun j => ∑ i, avgM h I i j * e i)) ^ 2 +
        (∑ i, e i * KAM.frequencyMap h I i) ^ 2 ≥ lam ^ 2 := by
  have hconv : ∀ I (e : Fin n → ℝ), (euclid (fun j => ∑ i, avgM h I i j * e i)) ^ 2 +
      (∑ i, e i * KAM.frequencyMap h I i) ^ 2 = AvgRank.gap h (I, e) := fun I e => by
    rw [AvgRank.euclid_sq]; rfl
  have hK : IsCompact (avgG n R ×ˢ {e : Fin n → ℝ | euclid e = 1}) :=
    (isCompact_closedBall _ _).prod AvgRank.isCompact_sphere
  rcases (avgG n R ×ˢ {e : Fin n → ℝ | euclid e = 1}).eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, fun I hI e he => ?_⟩
    exact absurd (hE.subset (show (I, e) ∈ avgG n R ×ˢ {e : Fin n → ℝ | euclid e = 1} from
      ⟨hI, he⟩)) (notMem_empty _)
  · obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne (AvgRank.gap_continuousOn d)
    have hpos := AvgRank.gap_pos d hp.1 hp.2
    refine ⟨Real.sqrt (AvgRank.gap h p), Real.sqrt_pos.2 hpos, fun I hI e he => ?_⟩
    rw [hconv, Real.sq_sqrt hpos.le]
    exact hmin (show (I, e) ∈ _ from ⟨hI, he⟩)

end KAM.Nekhoroshev

end
