/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Modulus
public import KAM.Planetary.StrongAMD.PlanarDictionary
public import KAM.Planetary.Exponential.Setting

/-!
# The whole-sublevel planar analytic domain: level set, shared tube, sharp core

Source: `LP:MAIN L8 (244–271)` with amendments N2 and N3, track LP, non-frozen.

* D0 `isCompact_strongLSet`, `strongLSet_subset_chamber`: the image `𝓛` of a compact positive
  strictly ordered `𝒜` under `a ↦ (ν_i √a_i)_i` is compact and lies in the chamber.
* D1 `exists_isSharedTube`: `L_δ` is compact and some `r_g > 0` makes `U = cthickening (4 r_g) L_δ`
  a compact subset of the chamber with `Ω_B(4 r_g) ≤ δ/16` (N2).
* D2 `strongCore`: the sharp core (fast angles in `[0, 2π]`, an `I⁰ ∈ L_δ` within `4 r_g`, and
  `chartAMD w ≤ B(I⁰) - δ/4`); it is compact and lies in `poincareProdDom n`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set Metric

variable {n : ℕ}

/-- `𝒜` is positive and strictly ordered (`a_i > 0`, `a_1 < ⋯ < a_n`). -/
def PositiveStrictlyOrdered (A : Set (Fin n → ℝ)) : Prop :=
  ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j

/-- MAIN's `𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}` (`LP:MAIN L8 (245)`). -/
def strongLSet (ν : Fin n → ℝ) (A : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  (fun a i => ν i * Real.sqrt (a i)) '' A

/-- `𝓛_δ = {I ∈ 𝓛 : δ ≤ B(I)}`, for a general set `L`. -/
def strongLevelSet (ν : Fin n → ℝ) (L : Set (Fin n → ℝ)) (δ : ℝ) : Set (Fin n → ℝ) :=
  {I | I ∈ L ∧ δ ≤ strongThreshold ν I}

/-! ### D0 -/

theorem isCompact_strongLSet {ν : Fin n → ℝ} {A : Set (Fin n → ℝ)} (hA : IsCompact A) :
    IsCompact (strongLSet ν A) := by
  refine hA.image ?_
  exact continuous_pi fun i => continuous_const.mul
    (Real.continuous_sqrt.comp (continuous_apply i))

theorem strongLSet_subset_chamber {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {A : Set (Fin n → ℝ)}
    (hA : PositiveStrictlyOrdered A) : strongLSet ν A ⊆ chamber ν := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨h0, hlt⟩ := hA a ha
  have hax : ∀ i, actionAxis ν (fun i => ν i * Real.sqrt (a i)) i = a i := fun i => by
    unfold actionAxis
    have := (hν i).ne'
    rw [mul_div_cancel_left₀ _ this, Real.sq_sqrt (h0 i).le]
  refine ⟨fun i => mul_pos (hν i) (Real.sqrt_pos.2 (h0 i)), fun i j hij => ?_⟩
  rw [hax, hax]
  exact hlt i j hij

/-! ### D1 -/

theorem isCompact_strongLevelSet {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {L : Set (Fin n → ℝ)} (hL : IsCompact L) (hLch : L ⊆ chamber ν) (δ : ℝ) :
    IsCompact (strongLevelSet ν L δ) := by
  have hcl : IsClosed (L ∩ strongThreshold ν ⁻¹' Set.Ici δ) :=
    ((continuousOn_strongThreshold hν hn).mono hLch).preimage_isClosed_of_isClosed
      hL.isClosed isClosed_Ici
  have := hL.of_isClosed_subset hcl inter_subset_left
  exact this

theorem strongLevelSet_subset {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ : ℝ} :
    strongLevelSet ν L δ ⊆ L := fun _ h => h.1

/-- The data of the shared tube (amendment N2): `r_g > 0` such that
`U = cthickening (4 r_g) L_δ` is compact, inside the chamber, and `Ω_B(4 r_g) ≤ δ/16`. -/
structure IsSharedTube (ν : Fin n → ℝ) (L : Set (Fin n → ℝ)) (δ r : ℝ) : Prop where
  pos : 0 < r
  compact : IsCompact (cthickening (4 * r) (strongLevelSet ν L δ))
  subset_chamber : cthickening (4 * r) (strongLevelSet ν L δ) ⊆ chamber ν
  modulus : strongThresholdModulus ν (cthickening (4 * r) (strongLevelSet ν L δ)) (4 * r) ≤
    δ / 16

theorem strongThresholdModulus_mono_set {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U V : Set (Fin n → ℝ)} (hUV : U ⊆ V) (hVc : IsCompact V) (hVch : V ⊆ chamber ν) (r : ℝ) :
    strongThresholdModulus ν U r ≤ strongThresholdModulus ν V r := by
  refine Real.sSup_le ?_ (strongThresholdModulus_nonneg ν V r)
  rintro x ⟨I, hI, J, hJ, hIJ, rfl⟩
  exact abs_strongThreshold_sub_le_modulus hν hn hVc hVch (hUV hI) (hUV hJ) hIJ

/-- D1 (`LP:MAIN L8 (257)`, N2): the shared tube exists. -/
theorem exists_isSharedTube {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {L : Set (Fin n → ℝ)} (hL : IsCompact L) (hLch : L ⊆ chamber ν) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, IsSharedTube ν L δ r := by
  have hLδc := isCompact_strongLevelSet hν hn hL hLch δ
  have hLδch : strongLevelSet ν L δ ⊆ chamber ν := strongLevelSet_subset.trans hLch
  obtain ⟨ρ, hρ, hUc, hUch⟩ := exists_cthickening_compact ν hLδc hLδch
  have ht := tendsto_strongThresholdModulus hν hn hUc hUch
  rw [Metric.tendsto_nhdsWithin_nhds] at ht
  obtain ⟨η, hη, hη'⟩ := ht (δ / 16) (by positivity)
  set r : ℝ := min ρ (η / 2) / 4 with hr
  have hr0 : 0 < r := by positivity
  have h4 : 4 * r = min ρ (η / 2) := by rw [hr]; ring
  have hsub : cthickening (4 * r) (strongLevelSet ν L δ) ⊆
      cthickening ρ (strongLevelSet ν L δ) :=
    cthickening_mono (by rw [h4]; exact min_le_left _ _) _
  refine ⟨r, hr0, ?_, hsub.trans hUch, ?_⟩
  · exact hLδc.cthickening
  · refine (strongThresholdModulus_mono_set hν hn hsub hUc hUch _).trans ?_
    have hpos : (0 : ℝ) < 4 * r := by positivity
    have hlt : dist (4 * r) 0 < η := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hpos, h4]
      exact (min_le_right _ _).trans_lt (by linarith)
    have := hη' hpos hlt
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (strongThresholdModulus_nonneg ν _ _)] at this
    exact this.le

/-! ### D2: the sharp core -/

/-- The shared compact action set `U = cthickening (4 r) 𝓛_δ` (N2), used by the core. -/
abbrev _root_.KAM.Planetary.StrongAMD.sharedTube (ν : Fin n → ℝ) (L : Set (Fin n → ℝ))
    (δ r : ℝ) : Set (Fin n → ℝ) :=
  cthickening (4 * r) (strongLevelSet ν L δ)

/-- The sharp core (`LP:MAIN L8 (251, 261)`, (21)): chart points with fast angles in `[0, 2π]`, an
`I⁰ ∈ L_δ` with `‖Λ - I⁰‖ ≤ 4 r_g`, and `chartAMD w ≤ B(I⁰) - δ/4`. -/
def strongCore (ν : Fin n → ℝ) (L : Set (Fin n → ℝ)) (δ r : ℝ) : Set (Phase (n + n)) :=
  {w | (∀ i, 0 ≤ fast w.1 i ∧ fast w.1 i ≤ 2 * Real.pi) ∧
    ∃ I0 ∈ strongLevelSet ν L δ, ‖fast w.2 - I0‖ ≤ 4 * r ∧
      chartAMD w ≤ strongThreshold ν I0 - δ / 4}

section Core

variable {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ r : ℝ}

theorem continuous_fast_snd : Continuous fun w : Phase (n + n) => fast w.2 :=
  continuous_pi fun _ => (continuous_apply _).comp continuous_snd

theorem continuous_chartAMD : Continuous fun w : Phase (n + n) => chartAMD w := by
  unfold chartAMD
  refine continuous_finsetSum _ fun i _ => ?_
  have a : Continuous fun w : Phase (n + n) => slow w.1 i :=
    (continuous_apply _).comp continuous_fst
  have b : Continuous fun w : Phase (n + n) => slow w.2 i :=
    (continuous_apply _).comp continuous_snd
  exact ((a.pow 2).add (b.pow 2)).div_const _

/-- If every coordinate of both blocks is bounded by `R`, the point is in `closedBall 0 R`. -/
theorem norm_le_of_coord_le {R : ℝ} (hR : 0 ≤ R) {w : Phase (n + n)}
    (h1 : ∀ j, |w.1 j| ≤ R) (h2 : ∀ j, |w.2 j| ≤ R) : ‖w‖ ≤ R := by
  rw [Prod.norm_def]
  refine max_le ?_ ?_ <;> rw [pi_norm_le_iff_of_nonneg hR] <;> intro j <;>
    rw [Real.norm_eq_abs]
  · exact h1 j
  · exact h2 j

theorem abs_le_of_sq_le {x A : ℝ} (hx : x ^ 2 ≤ 2 * A) : |x| ≤ 1 + 2 * A := by
  by_contra h
  push Not at h
  nlinarith [sq_abs x, abs_nonneg x]

/-- The core is compact: the projection of a compact subset of `Phase × L_δ`. -/
theorem isCompact_strongCore (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hL : IsCompact L)
    (hLch : L ⊆ chamber ν) (hδ : 0 < δ) :
    IsCompact (strongCore ν L δ r) := by
  have hLδc := isCompact_strongLevelSet hν hn hL hLch δ
  have hLδch : strongLevelSet ν L δ ⊆ chamber ν := strongLevelSet_subset.trans hLch
  set T : Set (Phase (n + n) × (Fin n → ℝ)) :=
    {p | p.2 ∈ strongLevelSet ν L δ ∧ (∀ i : Fin n, 0 ≤ fast p.1.1 i ∧ fast p.1.1 i ≤ 2 * Real.pi) ∧
      ‖fast p.1.2 - p.2‖ ≤ 4 * r ∧ chartAMD p.1 ≤ strongThreshold ν p.2 - δ / 4} with hT
  have hcore : strongCore ν L δ r = Prod.fst '' T := by
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
  -- closedness
  have hcl : IsClosed T := by
    have hS : IsClosed ((Set.univ : Set (Phase (n + n))) ×ˢ strongLevelSet ν L δ) :=
      isClosed_univ.prod hLδc.isClosed
    have hg : ContinuousOn (fun p : Phase (n + n) × (Fin n → ℝ) =>
        chartAMD p.1 - strongThreshold ν p.2 + δ / 4)
        ((Set.univ : Set (Phase (n + n))) ×ˢ strongLevelSet ν L δ) := by
      refine ((continuous_chartAMD.comp continuous_fst).continuousOn.sub ?_).add
        continuousOn_const
      exact ((continuousOn_strongThreshold hν hn).mono hLδch).comp continuous_snd.continuousOn
        (fun p hp => hp.2)
    have h1 := hg.preimage_isClosed_of_isClosed hS (isClosed_Iic (a := (0 : ℝ)))
    have hang : IsClosed {p : Phase (n + n) × (Fin n → ℝ) |
        ∀ i : Fin n, 0 ≤ fast p.1.1 i ∧ fast p.1.1 i ≤ 2 * Real.pi} := by
      simp only [Set.ofPred_forall]
      refine isClosed_iInter fun i => ?_
      have : Continuous fun p : Phase (n + n) × (Fin n → ℝ) => fast p.1.1 i :=
        (continuous_apply _).comp (continuous_fst.comp continuous_fst)
      exact (isClosed_le continuous_const this).inter (isClosed_le this continuous_const)
    have hd : IsClosed {p : Phase (n + n) × (Fin n → ℝ) | ‖fast p.1.2 - p.2‖ ≤ 4 * r} :=
      isClosed_le ((continuous_fast_snd.comp continuous_fst).sub continuous_snd).norm
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
  -- boundedness
  refine Metric.isCompact_of_isClosed_isBounded hcl ?_
  set C' : ℝ := max C 0 with hC'
  set R : ℝ := 2 * Real.pi + |M| + 4 * |r| + 1 + 2 * C' with hR
  have hpi := Real.pi_pos
  have hR0 : 0 ≤ R := by positivity
  refine ((Metric.isBounded_closedBall (x := (0 : Phase (n + n))) (r := R)).prod
    (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := M))).subset ?_
  rintro ⟨w, I0⟩ ⟨hI0, hang, hd, hamd⟩
  dsimp only at hI0 hang hd hamd
  refine ⟨?_, ?_⟩
  · have hB : |strongThreshold ν I0| ≤ C := by
      have := hC I0 hI0
      rwa [Real.norm_eq_abs] at this
    have hA : chartAMD w ≤ C' := by
      have h0 : chartAMD w ≤ strongThreshold ν I0 := by linarith
      exact h0.trans ((le_abs_self _).trans hB) |>.trans (le_max_left _ _)
    have hsl : ∀ i, (slow w.1 i) ^ 2 + (slow w.2 i) ^ 2 ≤ 2 * C' := fun i => by
      have := Finset.single_le_sum (f := fun j => ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2)
        (fun j _ => by positivity) (Finset.mem_univ i)
      unfold chartAMD at hA
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
    dsimp only
    have hC'0 : 0 ≤ C' := le_max_right _ _
    refine norm_le_of_coord_le hR0 (fun j => ?_) (fun j => ?_)
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · have := hang i
        simp only [fast] at this
        rw [abs_le]; constructor <;> nlinarith [this.1, this.2, abs_nonneg M, abs_nonneg r]
      · have := abs_le_of_sq_le ((le_add_of_nonneg_right (sq_nonneg _)).trans (hsl i))
        simp only [slow] at this
        have := abs_nonneg M; have := abs_nonneg r
        linarith
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · have := hΛ i
        simp only [fast] at this
        linarith
      · have := abs_le_of_sq_le ((le_add_of_nonneg_left (sq_nonneg _)).trans (hsl i))
        simp only [slow] at this
        have := abs_nonneg M; have := abs_nonneg r
        linarith
  · rw [mem_closedBall_zero_iff]; exact hM I0 hI0

/-- The action of a core point and its AMD margin (`LP:MAIN L8 (251)`):
`Λ ∈ U` and `ΣΓ ≤ B(Λ) - 3δ/16`. -/
theorem strongCore_margin (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hg : IsSharedTube ν L δ r)
    {w : Phase (n + n)} (hw : w ∈ strongCore ν L δ r) :
    fast w.2 ∈ sharedTube ν L δ r ∧
      chartAMD w ≤ strongThreshold ν (fast w.2) - 3 * δ / 16 := by
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

/-- Every core point lies in the Poincaré chart domain (`LP:MAIN L8 (251)`): `Γ_i < I_i`. -/
theorem strongCore_subset_dom (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hg : IsSharedTube ν L δ r)
    (hδ : 0 < δ) : strongCore ν L δ r ⊆ poincareProdDom n := by
  intro w hw i
  obtain ⟨hI, hamd⟩ := strongCore_margin hν hn hg hw
  have hIpos : 0 < fast w.2 i := (hg.subset_chamber hI).1 i
  have h0 : (planetBlock w i).2 0 = fast w.2 i := by simp [planetBlock]
  have hΓ : poincareGamma (planetBlock w i) = lpGamma w i := by
    simp [poincareGamma, lpGamma, planetBlock, slow]
  have hle : lpGamma w i ≤ chartAMD w := by
    rw [chartAMD_eq_sum_lpGamma]
    exact Finset.single_le_sum (f := lpGamma w) (fun j _ => by unfold lpGamma; positivity)
      (Finset.mem_univ i)
  have hB := strongThreshold_le_action ν (fast w.2) i
  refine ⟨by rw [h0]; exact hIpos, ?_⟩
  rw [hΓ, h0]
  linarith

end Core

end KAM.Planetary.StrongAMD

end
