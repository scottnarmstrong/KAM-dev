/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.Sequences
public import KAM.Wave.Measure.Measure

/-!
# W6: the parameter sets and the exclusion (blueprint `bpW:w6:convergence` (i), `bpW:w6:exclusion`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint labels `bpW:w6:convergence` (part (i), step `c-par`) and
`bpW:w6:exclusion` (milestone W6).

The parameter sets of the iteration are built from the frequencies `(ω_ν, Ω_ν)` by removing
resonance zones; this construction (and so part (i) of Proposition `bpW:w6:convergence` and the
exclusion lemma) does not depend on how the frequencies were obtained, so it is stated for
arbitrary sequences. With `Π_{-1}` given, `w6PiSeq … 0 = Π_{-1}` and
`w6PiSeq … (ν+1) = Π_ν = Π_{ν-1} ∖ ⋃_{(k,l) ∈ Z, |k| > K_{ν-1}} R^ν_{kl}`, where
`R^ν_{kl} = {ξ ∈ Π_{ν-1} : |⟨k, ω_ν⟩ + ⟨l, Ω_ν⟩| < α_ν ⟨l⟩/A_k}` is W7's `zoneSet` (Dirichlet
weight `⟨l⟩`) at level `α_ν`, and `K_{ν-1}` is `Kp ν` (with `Kp 0 = K_{-1} = 0` in the iteration).
In W7's indexing, `D_ν = Π_{ν-1} = w6PiSeq … ν`. `Π_* = ⋂_ν Π_ν` is `w6PiStar`.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace KAM.Wave

variable (P0 : Set (Fin 2 → ℝ)) (ω : ℕ → (Fin 2 → ℝ) → Fin 2 → ℝ) (Ω : ℕ → (Fin 2 → ℝ) → ℕ → ℝ)
  (a : ℕ → ℝ) (Kp : ℕ → ℝ)

/-- The zones removed at stage `ν`: `⋃_{(k,l) ∈ Z, |k| > K_{ν-1}} R^ν_{kl}` on the domain `D`. -/
def w6Removed (D : Set (Fin 2 → ℝ)) (ν : ℕ) : Set (Fin 2 → ℝ) :=
  ⋃ (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) (_ : InZ k l ∧ Kp ν < kAbs k), zoneSet D (ω ν) (Ω ν) (a ν) k l

/-- The parameter sets `Π_{ν-1}` (index `ν`): `Π_{-1} = P0`, `Π_ν = Π_{ν-1} ∖ ⋃ R^ν_{kl}`
(blueprint `bpW:w6:iter-lemma`, `bpW:w6:convergence`). -/
def w6PiSeq : ℕ → Set (Fin 2 → ℝ)
  | 0 => P0
  | ν + 1 => w6PiSeq ν \ w6Removed ω Ω a Kp (w6PiSeq ν) ν

/-- `Π_* = ⋂_ν Π_ν`. -/
def w6PiStar : Set (Fin 2 → ℝ) := ⋂ ν, w6PiSeq P0 ω Ω a Kp ν

theorem w6PiSeq_succ (ν : ℕ) :
    w6PiSeq P0 ω Ω a Kp (ν + 1) =
      w6PiSeq P0 ω Ω a Kp ν \ w6Removed ω Ω a Kp (w6PiSeq P0 ω Ω a Kp ν) ν := rfl

theorem w6PiSeq_antitone : Antitone (w6PiSeq P0 ω Ω a Kp) :=
  antitone_nat_of_succ_le fun _ => sdiff_subset

theorem w6PiSeq_subset (ν : ℕ) : w6PiSeq P0 ω Ω a Kp ν ⊆ P0 :=
  w6PiSeq_antitone P0 ω Ω a Kp (Nat.zero_le ν)

theorem w6PiStar_subset_seq (ν : ℕ) : w6PiStar P0 ω Ω a Kp ⊆ w6PiSeq P0 ω Ω a Kp ν :=
  iInter_subset _ ν

theorem w6PiStar_subset : w6PiStar P0 ω Ω a Kp ⊆ P0 := w6PiStar_subset_seq P0 ω Ω a Kp 0

/-- **Parameters** (blueprint `bpW:w6:convergence` (i), step `c-par`):
`Π_{-1} ∖ Π_* = ⋃_{ν ≥ 0} ⋃_{(k,l) ∈ Z, |k| > K_{ν-1}} R^ν_{kl}`, with `R^ν_{kl} ⊆ Π_{ν-1}`. -/
theorem w6Convergence_params :
    P0 \ w6PiStar P0 ω Ω a Kp =
      ⋃ (ν : ℕ) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) (_ : InZ k l ∧ Kp ν < kAbs k),
        zoneSet (w6PiSeq P0 ω Ω a Kp ν) (ω ν) (Ω ν) (a ν) k l := by
  ext ξ
  simp only [mem_sdiff, mem_iUnion, w6PiStar, mem_iInter, not_forall]
  constructor
  · rintro ⟨hξ, hex⟩
    classical
    let n := Nat.find hex
    have hn : ξ ∉ w6PiSeq P0 ω Ω a Kp n := Nat.find_spec hex
    have hn0 : n ≠ 0 := by
      intro h; apply hn; rw [h]; exact hξ
    obtain ⟨ν, hν⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hmem : ξ ∈ w6PiSeq P0 ω Ω a Kp ν := by
      by_contra h
      have := Nat.find_min' hex h
      omega
    rw [hν, w6PiSeq_succ] at hn
    simp only [mem_sdiff, not_and, not_not] at hn
    have := hn hmem
    simp only [w6Removed, mem_iUnion] at this
    obtain ⟨k, l, hkl, hz⟩ := this
    exact ⟨ν, k, l, hkl, hz⟩
  · rintro ⟨ν, k, l, hkl, hz⟩
    have hD : ξ ∈ w6PiSeq P0 ω Ω a Kp ν := hz.1
    refine ⟨w6PiSeq_subset P0 ω Ω a Kp ν hD, ν + 1, ?_⟩
    rw [w6PiSeq_succ]
    intro h
    apply h.2
    simp only [w6Removed, mem_iUnion]
    exact ⟨k, l, hkl, hz⟩

theorem w6Zone_subset (ν : ℕ) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) :
    zoneSet (w6PiSeq P0 ω Ω a Kp ν) (ω ν) (Ω ν) (a ν) k l ⊆ w6PiSeq P0 ω Ω a Kp ν :=
  fun _ h => h.1

theorem continuousOn_w6ZoneFun {D : Set (Fin 2 → ℝ)} {w : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {W : (Fin 2 → ℝ) → ℕ → ℝ} (hw : ContinuousOn w D) (hW : ∀ j, ContinuousOn (fun ξ => W ξ j) D)
    (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) :
    ContinuousOn (fun ξ => ∑ i, (k i : ℝ) * w ξ i + linF l (W ξ)) D := by
  refine ContinuousOn.add ?_ ?_
  · exact continuousOn_finsetSum _ fun i _ =>
      continuousOn_const.mul ((continuous_apply i).comp_continuousOn hw)
  · unfold linF Finsupp.sum
    exact continuousOn_finsetSum _ fun j _ => continuousOn_const.mul (hW j)

/-- **Borel** (blueprint `bpW:w6:convergence` (i)): if `Π_{-1}` is Borel and the `ω_ν`, `Ω_{ν,j}` are
continuous on `Π_{ν-1}`, every `Π_ν` and `Π_*` are Borel. -/
theorem w6PiSeq_measurableSet (hP0 : MeasurableSet P0)
    (hω : ∀ ν, ContinuousOn (ω ν) (w6PiSeq P0 ω Ω a Kp ν))
    (hΩ : ∀ ν j, ContinuousOn (fun ξ => Ω ν ξ j) (w6PiSeq P0 ω Ω a Kp ν)) :
    (∀ ν, MeasurableSet (w6PiSeq P0 ω Ω a Kp ν)) ∧ MeasurableSet (w6PiStar P0 ω Ω a Kp) := by
  have h : ∀ ν, MeasurableSet (w6PiSeq P0 ω Ω a Kp ν) := by
    intro ν
    induction ν with
    | zero => exact hP0
    | succ n ih =>
      rw [w6PiSeq_succ]
      refine ih.diff ?_
      unfold w6Removed
      exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun l =>
        MeasurableSet.iUnion fun _ => measurableSet_abs_lt_of_continuousOn ih
          (continuousOn_w6ZoneFun (hω n) (hΩ n) k l) _
  exact ⟨h, MeasurableSet.iInter h⟩

/-- **Borel** (blueprint `bpW:w6:freq-lip`, step `fl-borel`): `Π_{-1} = Π ∖ Ξ` is Borel; no
admissible family is used. -/
theorem w6PiMinus_measurableSet (m : ℝ) (hm : 0 < m) {Pi : Set (Fin 2 → ℝ)} {α : ℝ}
    (hS : MeasSetup m hm Pi α) : MeasurableSet (Pi \ prepSet m hm Pi α) := by
  refine hS.meas.diff ?_
  unfold prepSet
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun l =>
    MeasurableSet.iUnion fun _ => measurableSet_prepZone m hm hS _ k l

theorem zoneSet_mono_level {D : Set (Fin 2 → ℝ)} {w : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {W : (Fin 2 → ℝ) → ℕ → ℝ} {b c : ℝ} (hbc : b ≤ c) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) :
    zoneSet D w W b k l ⊆ zoneSet D w W c k l := by
  rintro ξ ⟨hξ, h⟩
  refine ⟨hξ, lt_of_lt_of_le h ?_⟩
  have hA : 0 < kAk k := lt_of_lt_of_le one_pos (kAk_pos k)
  have hJ : 0 ≤ japL l := le_trans zero_le_one (japL_ge_one l)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbc hJ) hA.le

/-- **Exclusion** (blueprint `bpW:w6:exclusion`), for the parameter sets built from an admissible
family `F` for `(Π, α)` (W7's `AdmissibleFamily`): if `D_ν = Π_{ν-1}` is the set obtained from
`Π_{-1} = Π ∖ Ξ` by removing the zones of `(F.ω ν, F.Ω ν)` with `|k| > K_{ν-1}` (`F.Kprev`) at levels
`a ν ≤ α̌`, then `Π ∖ Π_* ⊆ ℰ`. -/
theorem w6_exclusion (m : ℝ) (hm : 0 < m) {Pi : Set (Fin 2 → ℝ)} {α : ℝ}
    (F : AdmissibleFamily m hm Pi α) (a : ℕ → ℝ) (ha : ∀ ν, a ν ≤ alphaCheck α)
    (hD : ∀ ν, F.D ν = w6PiSeq (Pi \ prepSet m hm Pi α) F.ω F.Ω a (F.Kprev m hm) ν) :
    Pi \ w6PiStar (Pi \ prepSet m hm Pi α) F.ω F.Ω a (F.Kprev m hm) ⊆ exclSet m hm F := by
  intro ξ ⟨hξ, hnot⟩
  by_cases hX : ξ ∈ prepSet m hm Pi α
  · exact Or.inl hX
  · right
    have h1 : ξ ∈ (Pi \ prepSet m hm Pi α) \
        w6PiStar (Pi \ prepSet m hm Pi α) F.ω F.Ω a (F.Kprev m hm) := ⟨⟨hξ, hX⟩, hnot⟩
    rw [w6Convergence_params] at h1
    simp only [mem_iUnion] at h1
    obtain ⟨ν, k, l, hkl, hz⟩ := h1
    simp only [iterSet, mem_iUnion]
    refine ⟨ν, k, l, hkl, ?_⟩
    rw [hD ν]
    exact zoneSet_mono_level (ha ν) k l hz

/-- **Exclusion** for the iteration levels `α_ν` of `bpW:w6:sequences` with `α₀^{it} = α̌` and the
thresholds `K_ν` (blueprint `bpW:w6:exclusion`: "the thresholds are `K_ν ≥ 2^ν` and the levels
`α_ν ≤ α̌`"). -/
theorem w6_exclusion_seq (m : ℝ) (hm : 0 < m) {Pi : Set (Fin 2 → ℝ)} {α : ℝ}
    (d : W6SeqData) (hd : d.Valid) (hal : d.al0 = alphaCheck α)
    (F : AdmissibleFamily m hm Pi α) (hK : ∀ ν, F.K ν = d.K ν)
    (hD : ∀ ν, F.D ν = w6PiSeq (Pi \ prepSet m hm Pi α) F.ω F.Ω d.alpha d.Kprev ν) :
    Pi \ w6PiStar (Pi \ prepSet m hm Pi α) F.ω F.Ω d.alpha d.Kprev ⊆ exclSet m hm F := by
  have hKp : F.Kprev m hm = d.Kprev := by
    funext ν; cases ν with
    | zero => rfl
    | succ n => exact hK n
  rw [← hKp] at hD ⊢
  exact w6_exclusion m hm F d.alpha (fun ν => hal ▸ W6SeqData.alpha_le hd ν) hD

end KAM.Wave
