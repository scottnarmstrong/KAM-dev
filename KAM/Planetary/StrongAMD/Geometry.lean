/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Threshold
public import KAM.Planetary.StrongAMD.Orbital
public import KAM.Planetary.StrongAMD.Momentum
public import KAM.Planetary.Newtonian.Models

/-!
# The uniform strong barrier (deficit form and physical form)

Source: `LP:MAIN L5 (162–175)` with amendments N2 (one shared compact `U`) and N11
(`d_⋆ := a_min m² / (2 I_max²)` first); track LP, non-frozen.

Everything is stated for an arbitrary compact `U ⊆ chamber ν` given as data.

* G0 `actionAxis_actionVector`: on physical states `actionAxis ν (Λ z) i = keplerAxis ν z i`.
* G1 `exists_deficitBarrier`: the deficit form, uniform positive `dS`, `dP`.
* G2 `strongBarrier_physical`: the physical form, with `R, P, c`, and the MOM projection bound.
* G3 `exists_barrierCompact`: all barrier states lie in one compact collision-free set.
* `perihelionFloor_le` (N11): the explicit floor `d_⋆` for the perihelion distance.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Kepler KAM.Planetary

variable {n : ℕ}

/-- A physical state: every planet is off the star and has negative Kepler energy. -/
def IsPhysicalState (ν : Fin n → ℝ) (z : Phase (n * 2)) : Prop :=
  ∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0

/-- The action vector `Λ z = (Λ_i)`. -/
def actionVector (ν : Fin n → ℝ) (z : Phase (n * 2)) : Fin n → ℝ := fun i => keplerAction ν z i

/-- The conclusion of `LP:MAIN L5 (164)`, deficit form, for given constants `dS`, `dP`:
every `I ∈ U` and every list `e ∈ [0,1]^n` with `∑ I_i D(e_i) ≤ B(I) - m` has perihelion
`a_i (1 - e_i) ≥ dS` and adjacent annulus gaps `a_{i+1}(1 - e_{i+1}) - a_i (1 + e_i) ≥ dP`. -/
def DeficitBarrier (ν : Fin n → ℝ) (U : Set (Fin n → ℝ)) (m dS dP : ℝ) : Prop :=
  ∀ I ∈ U, ∀ e : Fin n → ℝ, (∀ i, e i ∈ Set.Icc (0 : ℝ) 1) →
    ∑ i, I i * eccDeficit (e i) ≤ strongThreshold ν I - m →
    (∀ i, dS ≤ actionAxis ν I i * (1 - e i)) ∧
    ∀ a : AdjIdx n, dP ≤ actionAxis ν I a.upperIdx * (1 - e a.upperIdx) -
      actionAxis ν I a.1 * (1 + e a.1)

/-- A barrier state: physical, with `Λ z ∈ U` and `C ≤ B (Λ z) - m` (`LP:MAIN L5 (164)`). -/
def BarrierState (ν : Fin n → ℝ) (U : Set (Fin n → ℝ)) (m : ℝ) (z : Phase (n * 2)) : Prop :=
  IsPhysicalState ν z ∧ actionVector ν z ∈ U ∧
    strongAMD ν z ≤ strongThreshold ν (actionVector ν z) - m

theorem IsPhysicalState.orbital {ν : Fin n → ℝ} {z : Phase (n * 2)} (hν : ∀ i, 0 < ν i)
    (hz : IsPhysicalState ν z) :
    ∀ i, 0 < ν i ∧ 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0 :=
  fun i => ⟨hν i, (hz i).1, (hz i).2⟩

/-- G0 (bridge): on physical states the action axis of `Λ z` is the Kepler axis. -/
theorem actionAxis_actionVector {ν : Fin n → ℝ} {z : Phase (n * 2)} (hν : ∀ i, 0 < ν i)
    (hz : IsPhysicalState ν z) (i : Fin n) :
    actionAxis ν (actionVector ν z) i = keplerAxis ν z i := by
  obtain ⟨-, -, h3, -⟩ := orbital_identities i (hz.orbital hν i)
  unfold actionAxis actionVector
  rw [div_pow, h3]
  have := (hν i).ne'
  field_simp

/-! ### Compactness helpers -/

theorem exists_pos_forall_le_on_compact {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    {K : Set X} (hK : IsCompact K) (f : ι → X → ℝ) (hf : ∀ i, ContinuousOn (f i) K)
    (hpos : ∀ i, ∀ x ∈ K, 0 < f i x) : ∃ d, 0 < d ∧ ∀ i, ∀ x ∈ K, d ≤ f i x := by
  have each : ∀ i, ∃ d, 0 < d ∧ ∀ x ∈ K, d ≤ f i x := by
    intro i
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, one_pos, by simp⟩
    · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne (hf i)
      exact ⟨f i x₀, hpos i x₀ hx₀, fun x hx => hmin hx⟩
  choose d hd0 hd using each
  classical
  have key : ∀ s : Finset ι, ∃ d, 0 < d ∧ ∀ i ∈ s, ∀ x ∈ K, d ≤ f i x := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_pos, by simp⟩
    | insert a s ha ih =>
      obtain ⟨d', hd'0, hd'⟩ := ih
      refine ⟨min d' (d a), lt_min hd'0 (hd0 a), fun i hi x hx => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact (min_le_right _ _).trans (hd _ x hx)
      · exact (min_le_left _ _).trans (hd' i hi x hx)
  obtain ⟨d, hd0', hd'⟩ := key Finset.univ
  exact ⟨d, hd0', fun i => hd' i (Finset.mem_univ i)⟩

/-- The set `K_m` of `LP:MAIN L5 (167)` (pairs `(I, e)`). -/
def deficitRegion (ν : Fin n → ℝ) (U : Set (Fin n → ℝ)) (m : ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {x | x.1 ∈ U ∧ (∀ i, x.2 i ∈ Set.Icc (0 : ℝ) 1) ∧
    ∑ i, x.1 i * eccDeficit (x.2 i) ≤ strongThreshold ν x.1 - m}

theorem isCompact_deficitRegion {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) (m : ℝ) :
    IsCompact (deficitRegion ν U m) := by
  set S : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    U ×ˢ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1) with hS
  have hSc : IsCompact S := hUc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  set g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ :=
    fun x => ∑ i, x.1 i * eccDeficit (x.2 i) - strongThreshold ν x.1 + m with hg
  have hcont : ContinuousOn g S := by
    have h1 : Continuous fun x : (Fin n → ℝ) × (Fin n → ℝ) =>
        ∑ i, x.1 i * eccDeficit (x.2 i) := by
      have := continuous_eccDeficit
      fun_prop
    have h2 : ContinuousOn (fun x : (Fin n → ℝ) × (Fin n → ℝ) => strongThreshold ν x.1) S :=
      (continuousOn_strongThreshold hν hn).comp continuousOn_fst
        (fun x hx => hUch hx.1)
    exact (h1.continuousOn.sub h2).add continuousOn_const
  have hcl := hcont.preimage_isClosed_of_isClosed hSc.isClosed (isClosed_Iic (a := (0 : ℝ)))
  have heq : deficitRegion ν U m = S ∩ g ⁻¹' Set.Iic 0 := by
    ext x
    simp only [deficitRegion, hS, hg, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod,
      Set.mem_pi, Set.mem_univ, true_implies, Set.mem_preimage, Set.mem_Iic]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, by linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, by linarith⟩
  rw [heq]
  exact hSc.of_isClosed_subset hcl Set.inter_subset_left

theorem eccDeficit_one : eccDeficit 1 = 1 := by simp [eccDeficit]

/-- Every eccentricity in the deficit region is strictly below one. -/
theorem lt_one_of_mem_deficitRegion {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)} {m : ℝ} (hm : 0 < m)
    (hUch : U ⊆ chamber ν) {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ deficitRegion ν U m)
    (i : Fin n) : x.2 i < 1 := by
  obtain ⟨hU, he, hsum⟩ := hx
  refine lt_of_le_of_ne (he i).2 fun h1 => ?_
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ x.1 j * eccDeficit (x.2 j) := fun j _ =>
    mul_nonneg ((hUch hU).1 j).le (eccDeficit_nonneg (he j))
  have hle : x.1 i * eccDeficit (x.2 i) ≤ ∑ j, x.1 j * eccDeficit (x.2 j) :=
    Finset.single_le_sum hnn (Finset.mem_univ i)
  rw [h1, eccDeficit_one, mul_one] at hle
  have := strongThreshold_le_action ν x.1 i
  linarith

/-- Every adjacent annulus gap is positive in the deficit region (`LP:MAIN L5 (166)`). -/
theorem gap_pos_of_mem_deficitRegion {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)} {m : ℝ} (hm : 0 < m)
    (hUch : U ⊆ chamber ν) {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ deficitRegion ν U m)
    (a : AdjIdx n) :
    0 < actionAxis ν x.1 a.upperIdx * (1 - x.2 a.upperIdx) -
      actionAxis ν x.1 a.1 * (1 + x.2 a.1) := by
  by_contra hle
  push Not at hle
  obtain ⟨hU, he, hsum⟩ := hx
  have hfeas := pairThreshold_le_of_feasible ν x.1 a.1 a.upperIdx (he a.1) (he a.upperIdx)
    (by linarith)
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ x.1 j * eccDeficit (x.2 j) := fun j _ =>
    mul_nonneg ((hUch hU).1 j).le (eccDeficit_nonneg (he j))
  have hne : a.1 ≠ a.upperIdx := (AdjIdx.lt_upperIdx a).ne
  have hpair : x.1 a.1 * eccDeficit (x.2 a.1) + x.1 a.upperIdx * eccDeficit (x.2 a.upperIdx) ≤
      ∑ j, x.1 j * eccDeficit (x.2 j) := by
    rw [← Finset.sum_pair (f := fun j => x.1 j * eccDeficit (x.2 j)) hne]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hnn j
      (Finset.mem_univ j)
  have := strongThreshold_le_pair ν x.1 a
  have hfe : pairObjective x.1 a.1 a.upperIdx (x.2 a.1, x.2 a.upperIdx) =
      x.1 a.1 * eccDeficit (x.2 a.1) + x.1 a.upperIdx * eccDeficit (x.2 a.upperIdx) := rfl
  linarith

/-- G1 (`LP:MAIN L5 (164)`, deficit form, second sentence): uniform positive perihelion and
adjacent-gap bounds depending only on `ν, U, m`. -/
theorem exists_deficitBarrier {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {m : ℝ} (hm : 0 < m) :
    ∃ dS dP : ℝ, 0 < dS ∧ 0 < dP ∧ DeficitBarrier ν U m dS dP := by
  have hK := isCompact_deficitRegion hν hn hUc hUch m
  have hsub : deficitRegion ν U m ⊆ (U ×ˢ Set.univ) := fun x hx => ⟨hx.1, trivial⟩
  have hax : ∀ i, ContinuousOn (fun x : (Fin n → ℝ) × (Fin n → ℝ) => actionAxis ν x.1 i)
      (deficitRegion ν U m) := fun i =>
    ((continuous_actionAxis ν i).comp continuous_fst).continuousOn
  obtain ⟨dS, hdS, hS⟩ := exists_pos_forall_le_on_compact hK
    (fun (i : Fin n) (x : (Fin n → ℝ) × (Fin n → ℝ)) => actionAxis ν x.1 i * (1 - x.2 i))
    (fun i => (hax i).mul (by fun_prop))
    (fun i x hx => mul_pos (actionAxis_pos hν (hUch hx.1) i)
      (by linarith [lt_one_of_mem_deficitRegion hm hUch hx i]))
  obtain ⟨dP, hdP, hP⟩ := exists_pos_forall_le_on_compact hK
    (fun (a : AdjIdx n) (x : (Fin n → ℝ) × (Fin n → ℝ)) =>
      actionAxis ν x.1 a.upperIdx * (1 - x.2 a.upperIdx) - actionAxis ν x.1 a.1 * (1 + x.2 a.1))
    (fun a => ((hax _).mul (by fun_prop)).sub ((hax _).mul (by fun_prop)))
    (fun a x hx => gap_pos_of_mem_deficitRegion hm hUch hx a)
  exact ⟨dS, dP, hdS, hdP, fun I hI e he hsum =>
    ⟨fun i => hS i (I, e) ⟨hI, he, hsum⟩, fun a => hP a (I, e) ⟨hI, he, hsum⟩⟩⟩

/-! ### Physical form -/

/-- Ordered radial intervals: from adjacent gaps, `A_i + dP ≤ P_j` for all `i < j`. -/
theorem chain_gap {P A : Fin n → ℝ} {dP : ℝ} (hdP : 0 ≤ dP) (hPA : ∀ k, P k ≤ A k)
    (hgap : ∀ a : AdjIdx n, dP ≤ P a.upperIdx - A a.1) {i j : Fin n} (hij : i < j) :
    dP ≤ P j - A i := by
  have key : ∀ d : ℕ, ∀ i j : Fin n, j.val = i.val + d + 1 → dP ≤ P j - A i := by
    intro d
    induction d with
    | zero =>
      intro i j hj
      have := hgap ⟨i, by have := j.2; omega⟩
      have hji : AdjIdx.upperIdx (⟨i, by have := j.2; omega⟩ : AdjIdx n) = j := Fin.ext (by
        show i.val + 1 = j.val
        omega)
      rw [hji] at this
      exact this
    | succ d ih =>
      intro i j hj
      have hk : j.val - 1 < n := by have := j.2; omega
      set k : Fin n := ⟨j.val - 1, hk⟩
      have h1 := ih i k (by show j.val - 1 = i.val + d + 1; omega)
      have h2 := hgap ⟨k, by show j.val - 1 + 1 < n; have := j.2; omega⟩
      have hkj : AdjIdx.upperIdx
          (⟨k, by show j.val - 1 + 1 < n; have := j.2; omega⟩ : AdjIdx n) = j :=
        Fin.ext (by show j.val - 1 + 1 = j.val; omega)
      rw [hkj] at h2
      have := hPA k
      show dP ≤ P j - A i
      simp only at h2
      linarith
  exact key (j.val - i.val - 1) i j (by have := hij; rw [Fin.lt_def] at this; omega)

theorem planeLength_le_add_sub (v w : Fin 2 → ℝ) :
    planeLength w - planeLength v ≤ planeLength (v - w) := by
  have h := planeLength_add_le (w - v) v
  rw [sub_add_cancel, planeLength_sub_comm] at h
  linarith

theorem exists_axis_bound {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)} (hUc : IsCompact U) :
    ∃ M : ℝ, 0 < M ∧ ∀ I ∈ U, ∀ i, actionAxis ν I i ≤ M := by
  have hc : ContinuousOn (fun I : Fin n → ℝ => ∑ i, actionAxis ν I i) U :=
    (continuous_finsetSum _ fun i _ => continuous_actionAxis ν i).continuousOn
  obtain ⟨C, hC⟩ := hUc.exists_bound_of_continuousOn hc
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun I hI i => ?_⟩
  have h1 : actionAxis ν I i ≤ ∑ j, actionAxis ν I j :=
    Finset.single_le_sum (f := fun j => actionAxis ν I j) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h2 := (le_abs_self _).trans (hC I hI)
  exact h1.trans (h2.trans (le_max_left _ _))

/-- G2 (`LP:MAIN L5 (164, 169–171)`, physical form): with the constants of the deficit form, and
explicit `R, P, c > 0`, every barrier state has perihelion `≥ dS`, adjacent gaps `≥ dP`,
`|q_i| ≥ dS`, `|q_i - q_j| ≥ dP` for all `i ≠ j`, `|q_i| ≤ R`, `|p_i| ≤ P`, `E_i ≤ -c`, and
`m ≤ |L_i|` with every `L_i` of the sign of the total momentum. -/
theorem strongBarrier_physical {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {m : ℝ} (hm : 0 < m) :
    ∃ dS dP R P c : ℝ, 0 < dS ∧ 0 < dP ∧ 0 < R ∧ 0 < P ∧ 0 < c ∧ DeficitBarrier ν U m dS dP ∧
      ∀ z : Phase (n * 2), BarrierState ν U m z →
        (∀ i, dS ≤ keplerAxis ν z i * (1 - planeLength (keplerEccVector ν z i))) ∧
        (∀ a : AdjIdx n, dP ≤ keplerAxis ν z a.upperIdx *
            (1 - planeLength (keplerEccVector ν z a.upperIdx)) -
          keplerAxis ν z a.1 * (1 + planeLength (keplerEccVector ν z a.1))) ∧
        (∀ i, dS ≤ planeLength (bodyVector z.1 i)) ∧
        (∀ i j, i ≠ j → dP ≤ planeLength (bodyVector z.1 i - bodyVector z.1 j)) ∧
        (∀ i, planeLength (bodyVector z.1 i) ≤ R) ∧
        (∀ i, planeLength (bodyVector z.2 i) ≤ P) ∧
        (∀ i, keplerEnergy ν z i ≤ -c) ∧
        (∀ i, m ≤ |planeCross (bodyVector z.1 i) (bodyVector z.2 i)| ∧
          0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i) * totalMomentum z) := by
  have hi0 : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨dS, dP, hdS, hdP, hB⟩ := exists_deficitBarrier hν hn hUc hUch hm
  obtain ⟨M, hM, hMa⟩ := exists_axis_bound (ν := ν) hUc
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ ν
    ⟨(⟨0, by omega⟩ : Fin n), Finset.mem_univ _⟩
  obtain ⟨i0, -, hi0'⟩ := Finset.exists_min_image Finset.univ ν
    ⟨(⟨0, by omega⟩ : Fin n), Finset.mem_univ _⟩
  refine ⟨dS, dP, 2 * M, ν j0 * Real.sqrt (2 / dS), ν i0 / (2 * M), hdS, hdP, by positivity,
    by have := hν j0; positivity, by have := hν i0; positivity, hB, ?_⟩
  rintro z ⟨hphys, hU, hC⟩
  have hz := hphys.orbital hν
  have he : ∀ i, planeLength (keplerEccVector ν z i) ∈ Set.Icc (0 : ℝ) 1 := fun i =>
    ⟨planeLength_nonneg _, (orbital_identities i (hz i)).2.2.2.2.1⟩
  have hsum : ∑ i, actionVector ν z i * eccDeficit (planeLength (keplerEccVector ν z i)) ≤
      strongThreshold ν (actionVector ν z) - m :=
    (sum_action_mul_eccDeficit_le_strongAMD hz).trans hC
  obtain ⟨hS, hG⟩ := hB _ hU _ he hsum
  simp only [actionAxis_actionVector hν hphys] at hS hG
  refine ⟨hS, hG, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hS i).trans (orbital_identities i (hz i)).2.2.2.2.2.2.2.1
  · intro i j hij
    have hq : ∀ k, keplerAxis ν z k * (1 - planeLength (keplerEccVector ν z k)) ≤
        planeLength (bodyVector z.1 k) := fun k => (orbital_identities k (hz k)).2.2.2.2.2.2.2.1
    have hq' : ∀ k, planeLength (bodyVector z.1 k) ≤
        keplerAxis ν z k * (1 + planeLength (keplerEccVector ν z k)) := fun k =>
      (orbital_identities k (hz k)).2.2.2.2.2.2.2.2.1
    have hPA : ∀ k, keplerAxis ν z k * (1 - planeLength (keplerEccVector ν z k)) ≤
        keplerAxis ν z k * (1 + planeLength (keplerEccVector ν z k)) := fun k =>
      mul_le_mul_of_nonneg_left (by linarith [planeLength_nonneg (keplerEccVector ν z k)])
        (orbital_identities k (hz k)).1.le
    have hord : ∀ {k l : Fin n}, k < l →
        dP ≤ planeLength (bodyVector z.1 l - bodyVector z.1 k) := fun {k l} hkl => by
      have hc := chain_gap hdP.le hPA hG hkl
      have h1 := planeLength_le_add_sub (bodyVector z.1 k) (bodyVector z.1 l)
      rw [planeLength_sub_comm] at h1
      have := hq l
      have := hq' k
      linarith
    rcases lt_or_gt_of_ne hij with h | h
    · rw [planeLength_sub_comm]; exact hord h
    · exact hord h
  · intro i
    obtain ⟨ha, -, -, -, he1, -, -, -, hap, -⟩ := orbital_identities i (hz i)
    have h1 := hMa _ hU i
    rw [actionAxis_actionVector hν hphys] at h1
    have h2 := planeLength_nonneg (keplerEccVector ν z i)
    calc planeLength (bodyVector z.1 i) ≤ keplerAxis ν z i * (1 + _) := hap
      _ ≤ keplerAxis ν z i * 2 := mul_le_mul_of_nonneg_left (by linarith) ha.le
      _ ≤ 2 * M := by linarith
  · intro i
    obtain ⟨ha, -, -, -, -, -, -, -, -, hp2⟩ := orbital_identities i (hz i)
    have hq : dS ≤ planeLength (bodyVector z.1 i) :=
      (hS i).trans (orbital_identities i (hz i)).2.2.2.2.2.2.2.1
    have hq0 : 0 < planeLength (bodyVector z.1 i) := (hphys i).1
    have hν' := hν i
    have hνj : ν i ≤ ν j0 := hj0 i (Finset.mem_univ i)
    refine Real.sqrt_le_iff.2 ⟨by have := hν j0; positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity), hp2]
    have h1 : 2 / planeLength (bodyVector z.1 i) - 1 / keplerAxis ν z i ≤ 2 / dS := by
      have : 2 / planeLength (bodyVector z.1 i) ≤ 2 / dS :=
        div_le_div_of_nonneg_left (by norm_num) hdS hq
      have : 0 < 1 / keplerAxis ν z i := by positivity
      linarith
    calc ν i ^ 2 * (2 / planeLength (bodyVector z.1 i) - 1 / keplerAxis ν z i)
        ≤ ν i ^ 2 * (2 / dS) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ ≤ ν j0 ^ 2 * (2 / dS) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hν'.le hνj 2) (by positivity)
  · intro i
    have ha := (orbital_identities i (hz i)).1
    have h1 := hMa _ hU i
    rw [actionAxis_actionVector hν hphys] at h1
    have hE : keplerEnergy ν z i = -(ν i / (2 * keplerAxis ν z i)) := by
      have := (hphys i).2.ne
      have := (hν i).ne'
      unfold keplerAxis
      field_simp
    rw [hE]
    have h3 : ν i0 / (2 * M) ≤ ν i / (2 * keplerAxis ν z i) :=
      div_le_div₀ (hν i).le (hi0' i (Finset.mem_univ i)) (by positivity) (by linarith)
    linarith
  · have hC' : ∀ i, strongAMD ν z ≤ keplerAction ν z i - m := fun i => by
      have := strongThreshold_le_action ν (actionVector ν z) i
      have h : actionVector ν z i = keplerAction ν z i := rfl
      linarith
    intro i
    obtain ⟨-, h2, h3⟩ := cross_sign_and_margin hz hm hC' i
    exact ⟨h3, h2⟩

/-! ### Compactness -/

theorem continuous_planeLength' : Continuous planeLength := by
  have : planeSq = fun w : Fin 2 → ℝ => ∑ k, w k ^ 2 := rfl
  have h : Continuous planeSq := by rw [this]; fun_prop
  exact Real.continuous_sqrt.comp h

theorem continuous_bodyVector' (i : Fin n) :
    Continuous (fun q : Fin (n * 2) → ℝ => bodyVector q i) := by
  unfold bodyVector; fun_prop

/-- The compact set of barrier states for given constants. -/
def barrierCompact (n : ℕ) (dS dP R P : ℝ) : Set (Phase (n * 2)) :=
  {z | (∀ i, dS ≤ planeLength (bodyVector z.1 i) ∧ planeLength (bodyVector z.1 i) ≤ R ∧
      planeLength (bodyVector z.2 i) ≤ P) ∧
    ∀ i j, i ≠ j → dP ≤ planeLength (bodyVector z.1 i - bodyVector z.1 j)}

theorem barrierCompact_isCompact {dS dP R P : ℝ} (hR : 0 ≤ R) (hP : 0 ≤ P) :
    IsCompact (barrierCompact n dS dP R P) := by
  have hcl : IsClosed (barrierCompact n dS dP R P) := by
    have e : barrierCompact n dS dP R P = (⋂ i,
        {z : Phase (n * 2) | dS ≤ planeLength (bodyVector z.1 i)} ∩
        {z | planeLength (bodyVector z.1 i) ≤ R} ∩
        {z | planeLength (bodyVector z.2 i) ≤ P}) ∩
        ⋂ i, ⋂ j, ⋂ (_ : i ≠ j),
          {z : Phase (n * 2) | dP ≤ planeLength (bodyVector z.1 i - bodyVector z.1 j)} := by
      ext z
      simp only [barrierCompact, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun i => ⟨⟨(h1 i).1, (h1 i).2.1⟩, (h1 i).2.2⟩, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun i => ⟨(h1 i).1.1, (h1 i).1.2, (h1 i).2⟩, h2⟩
    rw [e]
    refine IsClosed.inter (isClosed_iInter fun i => ?_) (isClosed_iInter fun i =>
      isClosed_iInter fun j => isClosed_iInter fun _ => ?_)
    · have c1 : Continuous fun z : Phase (n * 2) => planeLength (bodyVector z.1 i) :=
        continuous_planeLength'.comp ((continuous_bodyVector' i).comp continuous_fst)
      have c2 : Continuous fun z : Phase (n * 2) => planeLength (bodyVector z.2 i) :=
        continuous_planeLength'.comp ((continuous_bodyVector' i).comp continuous_snd)
      exact ((isClosed_le continuous_const c1).inter (isClosed_le c1 continuous_const)).inter
        (isClosed_le c2 continuous_const)
    · exact isClosed_le continuous_const (continuous_planeLength'.comp
        (((continuous_bodyVector' i).comp continuous_fst).sub
          ((continuous_bodyVector' j).comp continuous_fst)))
  have hbd : Bornology.IsBounded (barrierCompact n dS dP R P) := by
    have hcoord : ∀ (w : Fin (n * 2) → ℝ) (C : ℝ), 0 ≤ C →
        (∀ i, planeLength (bodyVector w i) ≤ C) → ‖w‖ ≤ C := by
      intro w C hC h
      refine (pi_norm_le_iff_of_nonneg hC).2 fun a => ?_
      have ha : finProdFinEquiv (finProdFinEquiv.symm a) = a := Equiv.apply_symm_apply _ _
      set p := finProdFinEquiv.symm a
      have hw : w a = bodyVector w p.1 p.2 := by unfold bodyVector; rw [← ha]
      rw [hw]
      exact (norm_le_pi_norm (bodyVector w p.1) p.2).trans
        ((KAM.Kepler.norm_le_planeLength _).trans (h p.1))
    refine isBounded_iff_forall_norm_le.2 ⟨max R P, fun z hz => ?_⟩
    rw [Prod.norm_def]
    refine max_le (le_max_of_le_left ?_) (le_max_of_le_right ?_)
    · exact hcoord _ _ hR fun i => (hz.1 i).2.1
    · exact hcoord _ _ hP fun i => (hz.1 i).2.2
  exact Metric.isCompact_of_isClosed_isBounded hcl hbd

theorem barrierCompact_subset {dS dP R P : ℝ} (hdS : 0 < dS) (hdP : 0 < dP) :
    barrierCompact n dS dP R P ⊆ collisionFreeDomain n := fun _ hz =>
  ⟨fun i => hdS.trans_le (hz.1 i).1, fun i j hij => hdP.trans_le (hz.2 i j hij)⟩

/-- G3 (`LP:MAIN L5 (172)`): all barrier states lie in one compact subset of the nonsingular
physical region. -/
theorem exists_barrierCompact {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {m : ℝ} (hm : 0 < m) :
    ∃ K : Set (Phase (n * 2)), IsCompact K ∧ K ⊆ collisionFreeDomain n ∧
      ∀ z, BarrierState ν U m z → z ∈ K := by
  obtain ⟨dS, dP, R, P, c, hdS, hdP, hR, hP, -, -, h⟩ :=
    strongBarrier_physical hν hn hUc hUch hm
  refine ⟨barrierCompact n dS dP R P, barrierCompact_isCompact hR.le hP.le,
    barrierCompact_subset hdS hdP, fun z hz => ?_⟩
  obtain ⟨-, -, h3, h4, h5, h6, -⟩ := h z hz
  exact ⟨fun i => ⟨h3 i, h5 i, h6 i⟩, h4⟩

/-! ### N11: the explicit perihelion floor `d_⋆` -/

/-- `d_⋆ := a_min m² / (2 I_max²)` (amendment N11, `LP:MAIN L5 (174)`, (16)). -/
def perihelionFloor (aMin Imax m : ℝ) : ℝ := aMin * m ^ 2 / (2 * Imax ^ 2)

/-- N11 / (16): on a barrier state whose action vector has all axes `≥ aMin > 0` and all actions
`≤ Imax`, the perihelion is at least `d_⋆ = a_min m² / (2 I_max²)`, hence also `|q_i| ≥ d_⋆`
and `|p_i| ≤ ν_i √(2 / d_⋆)`. -/
theorem perihelionFloor_le {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {U : Set (Fin n → ℝ)} {m : ℝ}
    (hm : 0 < m) {aMin Imax : ℝ} (haMin : 0 < aMin)
    (hax : ∀ I ∈ U, ∀ i, aMin ≤ actionAxis ν I i) (hI : ∀ I ∈ U, ∀ i, I i ≤ Imax)
    {z : Phase (n * 2)} (hz : BarrierState ν U m z) (i : Fin n) :
    perihelionFloor aMin Imax m ≤
        keplerAxis ν z i * (1 - planeLength (keplerEccVector ν z i)) ∧
      perihelionFloor aMin Imax m ≤ planeLength (bodyVector z.1 i) ∧
      planeLength (bodyVector z.2 i) ≤ ν i * Real.sqrt (2 / perihelionFloor aMin Imax m) := by
  obtain ⟨hphys, hU, hC⟩ := hz
  have hzo := hphys.orbital hν
  obtain ⟨ha, hΛ, -, -, he1, habs, -, hper, -, hp2⟩ := orbital_identities i (hzo i)
  have hsum := sum_action_mul_eccDeficit_le_strongAMD hzo
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ keplerAction ν z j *
      (1 - Real.sqrt (1 - planeLength (keplerEccVector ν z j) ^ 2)) := fun j _ => by
    obtain ⟨-, hΛj, -, -, hej, -⟩ := orbital_identities j (hzo j)
    refine mul_nonneg hΛj.le ?_
    have := eccDeficit_nonneg (u := planeLength (keplerEccVector ν z j))
      ⟨planeLength_nonneg _, hej⟩
    exact this
  have hle1 := Finset.single_le_sum hnn (Finset.mem_univ i)
  have hB := strongThreshold_le_action ν (actionVector ν z) i
  have hact : actionVector ν z i = keplerAction ν z i := rfl
  set e := planeLength (keplerEccVector ν z i) with he
  set s := Real.sqrt (1 - e ^ 2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hΛs : m ≤ keplerAction ν z i * s := by nlinarith
  have hImax : keplerAction ν z i ≤ Imax := by rw [← hact]; exact hI _ hU i
  have he0 : 0 ≤ e := planeLength_nonneg _
  have hsq : s ^ 2 = 1 - e ^ 2 := Real.sq_sqrt (by nlinarith)
  have hImax_pos : 0 < Imax := hΛ.trans_le hImax
  have hs_ge : m / Imax ≤ s := by
    rw [div_le_iff₀ hImax_pos]
    nlinarith [mul_le_mul_of_nonneg_right hImax hs0]
  have hs2 : (m / Imax) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) hs_ge 2
  have h1e : s ^ 2 / 2 ≤ 1 - e := by nlinarith [sq_nonneg (1 - e)]
  have ha_ge : aMin ≤ keplerAxis ν z i := by
    rw [← actionAxis_actionVector hν hphys]; exact hax _ hU i
  have hfl : perihelionFloor aMin Imax m ≤ keplerAxis ν z i * (1 - e) := by
    calc perihelionFloor aMin Imax m = aMin * ((m / Imax) ^ 2 / 2) := by
          unfold perihelionFloor; field_simp
      _ ≤ aMin * (1 - e) := mul_le_mul_of_nonneg_left (by linarith) haMin.le
      _ ≤ keplerAxis ν z i * (1 - e) := mul_le_mul_of_nonneg_right ha_ge (by linarith)
  have hq := hfl.trans hper
  have hd0 : 0 < perihelionFloor aMin Imax m := by unfold perihelionFloor; positivity
  refine ⟨hfl, hq, ?_⟩
  have hν' := hν i
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by positivity), hp2]
  have h2 : 2 / planeLength (bodyVector z.1 i) ≤ 2 / perihelionFloor aMin Imax m :=
    div_le_div_of_nonneg_left (by norm_num) hd0 hq
  have h3 : 0 < 1 / keplerAxis ν z i := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)

end KAM.Planetary.StrongAMD
