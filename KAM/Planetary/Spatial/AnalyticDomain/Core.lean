/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.AnalyticDomain.Core
public import KAM.Planetary.Spatial.Product

/-!
# The whole-sublevel spatial analytic domain: the sharp core

Source: `LP:MAIN L18 (580–597)` with `LP:MAIN L8 (244–271)`, amendments N2, N3 and
N12; track LP, non-frozen.

Layout as in the spatial product chart: a chart point is `w : Phase (n + (n + n))` (`n` fast pairs, `2n` slow
pairs; `fast w.1 = λ`, `slow w.1 = (ξ | v)`, `fast w.2 = I`, `slow w.2 = (η | u)`).

* D2 `spatialStrongCore ν L δ r` (MAIN (47)): fast angles in `[0, 2π]`, an `I⁰ ∈ L_δ` within
  `4 r` of the actions, and `(Σ slow²)/2 ≤ B(I⁰) − δ/4`; `isCompact_spatialStrongCore`.
* `spatialStrongCore_margin`: `I ∈ U` and `(Σ slow²)/2 ≤ B(I) − 3δ/16` (MAIN line 590).
* `spatialStrongCore_subset_dom`: `Γ_i + Z_i < I_i` (MAIN line 587), so core points lie in
  `spatialPoincareProdDom n`.

The dimension-free threshold, `𝓛_δ` and the shared tube (`strongLevelSet`, `IsSharedTube`) are the
action-only objects of the analytic domain and are reused unchanged.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set Metric

variable {n : ℕ}

/-- The squared slow norm over two, `(|slow w.1|² + |slow w.2|²)/2`: MAIN's `|z|₂²/2` for the
`2n` slow pairs (`LP:MAIN L18 (47)`). -/
def spatialSlowDeficit (w : Phase (n + (n + n))) : ℝ :=
  ((∑ k, slow w.1 k ^ 2) + ∑ k, slow w.2 k ^ 2) / 2

/-- D2 (`LP:MAIN L18 (47)`): the spatial sharp core. Chart points with fast angles in `[0, 2π]`,
an `I⁰ ∈ L_δ` with `‖I − I⁰‖ ≤ 4 r`, and `(Σ slow²)/2 ≤ B(I⁰) − δ/4`. -/
def spatialStrongCore (ν : Fin n → ℝ) (L : Set (Fin n → ℝ)) (δ r : ℝ) :
    Set (Phase (n + (n + n))) :=
  {w | (∀ i, 0 ≤ fast w.1 i ∧ fast w.1 i ≤ 2 * Real.pi) ∧
    ∃ I0 ∈ strongLevelSet ν L δ, ‖fast w.2 - I0‖ ≤ 4 * r ∧
      spatialSlowDeficit w ≤ strongThreshold ν I0 - δ / 4}

section Core

variable {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ r : ℝ}

theorem continuous_spatialFast_snd : Continuous fun w : Phase (n + (n + n)) => fast w.2 :=
  continuous_pi fun _ => (continuous_apply _).comp continuous_snd

theorem continuous_spatialSlowDeficit : Continuous (spatialSlowDeficit (n := n)) := by
  unfold spatialSlowDeficit
  refine Continuous.div_const (Continuous.add ?_ ?_) _
  · refine continuous_finsetSum _ fun k _ => ?_
    exact (((continuous_apply _).comp continuous_fst : Continuous fun w : Phase (n + (n + n)) =>
      slow w.1 k)).pow 2
  · refine continuous_finsetSum _ fun k _ => ?_
    exact (((continuous_apply _).comp continuous_snd : Continuous fun w : Phase (n + (n + n)) =>
      slow w.2 k)).pow 2

/-- A point of `Phase (a + b)` with all four coordinate blocks bounded by `R` has norm `≤ R`. -/
theorem spatialPhase_norm_le {a b : ℕ} {R : ℝ} (hR : 0 ≤ R) {w : Phase (a + b)}
    (h1 : ∀ i, |fast w.1 i| ≤ R) (h2 : ∀ j, |slow w.1 j| ≤ R)
    (h3 : ∀ i, |fast w.2 i| ≤ R) (h4 : ∀ j, |slow w.2 j| ≤ R) : ‖w‖ ≤ R := by
  rw [Prod.norm_def]
  refine max_le ?_ ?_ <;> rw [pi_norm_le_iff_of_nonneg hR] <;> intro j <;>
    rw [Real.norm_eq_abs] <;> refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa [fast] using h1 i
  · simpa [slow] using h2 i
  · simpa [fast] using h3 i
  · simpa [slow] using h4 i

/-- The spatial core is compact: the projection of a compact subset of `Phase × L_δ`. -/
theorem isCompact_spatialStrongCore (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hL : IsCompact L)
    (hLch : L ⊆ chamber ν) (hδ : 0 < δ) :
    IsCompact (spatialStrongCore ν L δ r) := by
  have hLδc := isCompact_strongLevelSet hν hn hL hLch δ
  have hLδch : strongLevelSet ν L δ ⊆ chamber ν := strongLevelSet_subset.trans hLch
  set T : Set (Phase (n + (n + n)) × (Fin n → ℝ)) :=
    {p | p.2 ∈ strongLevelSet ν L δ ∧
      (∀ i : Fin n, 0 ≤ fast p.1.1 i ∧ fast p.1.1 i ≤ 2 * Real.pi) ∧
      ‖fast p.1.2 - p.2‖ ≤ 4 * r ∧ spatialSlowDeficit p.1 ≤ strongThreshold ν p.2 - δ / 4}
    with hT
  have hcore : spatialStrongCore ν L δ r = Prod.fst '' T := by
    ext w
    constructor
    · rintro ⟨h1, I0, hI0, h2, h3⟩
      exact ⟨(w, I0), ⟨hI0, h1, h2, h3⟩, rfl⟩
    · rintro ⟨⟨w', I0⟩, ⟨hI0, h1, h2, h3⟩, rfl⟩
      exact ⟨h1, I0, hI0, h2, h3⟩
  rw [hcore]
  refine IsCompact.image ?_ continuous_fst
  obtain ⟨M, hM⟩ := hLδc.isBounded.exists_norm_le
  obtain ⟨C, hC⟩ := hLδc.exists_bound_of_continuousOn
    ((continuousOn_strongThreshold hν hn).mono hLδch)
  have hcl : IsClosed T := by
    have hS : IsClosed ((Set.univ : Set (Phase (n + (n + n)))) ×ˢ strongLevelSet ν L δ) :=
      isClosed_univ.prod hLδc.isClosed
    have hg : ContinuousOn (fun p : Phase (n + (n + n)) × (Fin n → ℝ) =>
        spatialSlowDeficit p.1 - strongThreshold ν p.2 + δ / 4)
        ((Set.univ : Set (Phase (n + (n + n)))) ×ˢ strongLevelSet ν L δ) := by
      refine ((continuous_spatialSlowDeficit.comp continuous_fst).continuousOn.sub ?_).add
        continuousOn_const
      exact ((continuousOn_strongThreshold hν hn).mono hLδch).comp continuous_snd.continuousOn
        (fun p hp => hp.2)
    have h1 := hg.preimage_isClosed_of_isClosed hS (isClosed_Iic (a := (0 : ℝ)))
    have hang : IsClosed {p : Phase (n + (n + n)) × (Fin n → ℝ) |
        ∀ i : Fin n, 0 ≤ fast p.1.1 i ∧ fast p.1.1 i ≤ 2 * Real.pi} := by
      simp only [Set.ofPred_forall]
      refine isClosed_iInter fun i => ?_
      have : Continuous fun p : Phase (n + (n + n)) × (Fin n → ℝ) => fast p.1.1 i :=
        (continuous_apply _).comp (continuous_fst.comp continuous_fst)
      exact (isClosed_le continuous_const this).inter (isClosed_le this continuous_const)
    have hd : IsClosed {p : Phase (n + (n + n)) × (Fin n → ℝ) | ‖fast p.1.2 - p.2‖ ≤ 4 * r} :=
      isClosed_le ((continuous_spatialFast_snd.comp continuous_fst).sub continuous_snd).norm
        continuous_const
    convert h1.inter (hang.inter hd) using 1
    ext p
    simp only [hT, mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_Iic,
      mem_ofPred_eq]
    constructor
    · rintro ⟨a, b, c, d⟩
      exact ⟨⟨a, by linarith⟩, b, c⟩
    · rintro ⟨⟨a, d⟩, b, c⟩
      exact ⟨a, b, c, by linarith⟩
  refine Metric.isCompact_of_isClosed_isBounded hcl ?_
  set C' : ℝ := max C 0 with hC'
  set R : ℝ := 2 * Real.pi + |M| + 4 * |r| + 1 + 2 * C' with hR
  have hpi := Real.pi_pos
  have hR0 : 0 ≤ R := by positivity
  refine ((Metric.isBounded_closedBall (x := (0 : Phase (n + (n + n)))) (r := R)).prod
    (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := M))).subset ?_
  rintro ⟨w, I0⟩ ⟨hI0, hang, hd, hamd⟩
  dsimp only at hI0 hang hd hamd
  refine ⟨?_, ?_⟩
  · have hB : |strongThreshold ν I0| ≤ C := by
      have := hC I0 hI0
      rwa [Real.norm_eq_abs] at this
    have hA : spatialSlowDeficit w ≤ C' := by
      have h0 : spatialSlowDeficit w ≤ strongThreshold ν I0 := by linarith
      exact h0.trans ((le_abs_self _).trans hB) |>.trans (le_max_left _ _)
    have hC'0 : 0 ≤ C' := le_max_right _ _
    have hS1 : 0 ≤ ∑ k, slow w.1 k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    have hS2 : 0 ≤ ∑ k, slow w.2 k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    have hA' : (∑ k, slow w.1 k ^ 2) + ∑ k, slow w.2 k ^ 2 ≤ 2 * C' := by
      unfold spatialSlowDeficit at hA
      linarith
    have hsl1 : ∀ k, |slow w.1 k| ≤ 1 + 2 * C' := fun k => by
      refine abs_le_of_sq_le ?_
      have := Finset.single_le_sum (f := fun j => slow w.1 j ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ k)
      linarith
    have hsl2 : ∀ k, |slow w.2 k| ≤ 1 + 2 * C' := fun k => by
      refine abs_le_of_sq_le ?_
      have := Finset.single_le_sum (f := fun j => slow w.2 j ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ k)
      linarith
    have hMI : ‖I0‖ ≤ M := hM I0 hI0
    have hΛ : ∀ i, |fast w.2 i| ≤ |M| + 4 * |r| := fun i => by
      have h1 : ‖fast w.2 i‖ ≤ ‖fast w.2‖ := norm_le_pi_norm _ i
      have h2 : ‖fast w.2‖ ≤ ‖I0‖ + 4 * r := by
        have := norm_le_norm_add_norm_sub' (fast w.2) I0
        linarith
      rw [Real.norm_eq_abs] at h1
      have := le_abs_self M
      have := le_abs_self r
      linarith
    rw [mem_closedBall_zero_iff]
    have := abs_nonneg M
    have := abs_nonneg r
    refine spatialPhase_norm_le hR0 (fun i => ?_) (fun k => ?_) (fun i => ?_) (fun k => ?_)
    · have := hang i
      rw [abs_le]
      constructor <;> nlinarith [this.1, this.2]
    · linarith [hsl1 k]
    · linarith [hΛ i]
    · linarith [hsl2 k]
  · rw [mem_closedBall_zero_iff]; exact hM I0 hI0

/-- The action of a core point and its slow-norm margin (`LP:MAIN L18 (588–590)`):
`I ∈ U` and `(Σ slow²)/2 ≤ B(I) − 3δ/16`. -/
theorem spatialStrongCore_margin (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hg : IsSharedTube ν L δ r)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialStrongCore ν L δ r) :
    fast w.2 ∈ sharedTube ν L δ r ∧
      spatialSlowDeficit w ≤ strongThreshold ν (fast w.2) - 3 * δ / 16 := by
  obtain ⟨-, I0, hI0, hd, hamd⟩ := hw
  have hdist : dist (fast w.2) I0 ≤ 4 * r := by rwa [dist_eq_norm]
  have hI : fast w.2 ∈ sharedTube ν L δ r := mem_cthickening_of_dist_le _ _ _ _ hI0 hdist
  have hI0U : I0 ∈ sharedTube ν L δ r := self_subset_cthickening _ hI0
  have hmod := abs_strongThreshold_sub_le_modulus hν hn hg.compact hg.subset_chamber hI0U hI
    (r := 4 * r) (by rwa [norm_sub_rev])
  have := hg.modulus
  have h2 := (abs_le.1 (hmod.trans this)).2
  refine ⟨hI, ?_⟩
  linarith

/-- Each `Γ_i + Z_i` is at most the total slow deficit. -/
theorem spatialGammaBody_add_spatialZBody_le (w : Phase (n + (n + n))) (i : Fin n) :
    spatialGammaBody w i + spatialZBody w i ≤ spatialSlowDeficit w := by
  unfold spatialSlowDeficit
  rw [← sum_gamma_add_z_eq_half_slow_sq]
  exact Finset.single_le_sum (f := fun j => spatialGammaBody w j + spatialZBody w j)
    (fun j _ => by unfold spatialGammaBody spatialZBody spatialGamma spatialZ; positivity)
    (Finset.mem_univ i)

/-- Every core point lies in the product chart domain (`LP:MAIN L18 (587)`):
`Γ_i + Z_i < I_i` (and `I_i > 0`). -/
theorem spatialStrongCore_subset_dom (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    (hg : IsSharedTube ν L δ r) (hδ : 0 < δ) :
    spatialStrongCore ν L δ r ⊆ spatialPoincareProdDom n := by
  intro w hw i
  obtain ⟨hI, hamd⟩ := spatialStrongCore_margin hν hn hg hw
  have hIpos : 0 < fast w.2 i := (hg.subset_chamber hI).1 i
  have hle := spatialGammaBody_add_spatialZBody_le w i
  have hB := strongThreshold_le_action ν (fast w.2) i
  have h0 : (spatialBlock w i).2 0 = fast w.2 i := spatialBlock_snd_zero w i
  refine ⟨by rw [h0]; exact hIpos, ?_⟩
  show spatialGammaBody w i + spatialZBody w i < (spatialBlock w i).2 0
  rw [h0]
  linarith

end Core

end KAM.Planetary.Spatial

end
