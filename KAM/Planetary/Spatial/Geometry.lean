/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Geometry
public import KAM.Planetary.Spatial.Orbital
public import KAM.Planetary.Spatial.Momentum

/-!
# The uniform strong barrier in dimension three (physical form)

Source: `LP:MAIN L5 (162–175)` with `d = 3` and amendments N2 (one shared compact `U`)
and N11 (`d_⋆ := a_min m² / (2 I_max²)` first); track LP, non-frozen.

The threshold side is dimension-free and reused from the planar package: `strongThreshold`,
`DeficitBarrier`, `exists_deficitBarrier` (the deficit form: `dS, dP` depend on `ν, U, m` only),
`exists_axis_bound`, `chain_gap`.  Only the physical side is spatial.

* G0 `actionAxis_spatialActionVector`: `actionAxis ν (Λ z) i = spatialKeplerAxis ν z i`.
* G2 `spatialStrongBarrier_physical`: the physical form, with the projection margin `m ≤ L_i · L̂`.
* G3 `exists_spatialBarrierCompact`: all barrier states lie in one compact collision-free set.
* `spatialPerihelionFloor_le` (N11).

-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD

variable {n : ℕ}

/-- The action vector `Λ z = (Λ_i)` of a spatial state. -/
def spatialActionVector (ν : Fin n → ℝ) (z : Phase (n * 3)) : Fin n → ℝ :=
  fun i => spatialKeplerAction ν z i

/-- A spatial barrier state (`LP:MAIN L5 (164)`, `d = 3`): negative energy on every planet,
`Λ z ∈ U` and `C ≤ B (Λ z) - m`. -/
def SpatialBarrierState (ν : Fin n → ℝ) (U : Set (Fin n → ℝ)) (m : ℝ) (z : Phase (n * 3)) :
    Prop :=
  SpatialNegativeEnergy ν z ∧ spatialActionVector ν z ∈ U ∧
    spatialStrongAMD ν z ≤ strongThreshold ν (spatialActionVector ν z) - m

/-- G0 (bridge): on negative-energy states the action axis of `Λ z` is the spatial Kepler axis. -/
theorem actionAxis_spatialActionVector {ν : Fin n → ℝ} {z : Phase (n * 3)}
    (hz : SpatialNegativeEnergy ν z) (i : Fin n) :
    actionAxis ν (spatialActionVector ν z) i = spatialKeplerAxis ν z i := by
  have hν : 0 < ν i := (hz i).1
  obtain ⟨-, -, h3, -⟩ := spatial_orbital_identities i (hz i)
  unfold actionAxis spatialActionVector
  rw [div_pow, h3]
  have := hν.ne'
  field_simp

/-! ### Euclidean length helpers -/

theorem spaceLength_le_add_sub (v w : Fin 3 → ℝ) :
    spaceLength w - spaceLength v ≤ spaceLength (v - w) := by
  have h := spaceLength_add_le (w - v) v
  rw [sub_add_cancel, spaceLength_sub_comm] at h
  linarith

theorem norm_le_spaceLength (v : Fin 3 → ℝ) : ‖v‖ ≤ spaceLength v := by
  rw [pi_norm_le_iff_of_nonneg (spaceLength_nonneg v)]
  intro i
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  rw [spaceSq_def]
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

/-! ### Physical form -/

/-- G2 (`LP:MAIN L5 (164, 169–171)`, `d = 3`): with the constants of the deficit form, and explicit
`R, P, c > 0`, every spatial barrier state has perihelion `≥ dS`, adjacent gaps `≥ dP`,
`|q_i| ≥ dS`, `|q_i - q_j| ≥ dP` for `i ≠ j`, `|q_i| ≤ R`, `|p_i| ≤ P`, `E_i ≤ -c`, and the
projection margin `L ≠ 0`, `m ≤ L_i · L̂` for every `i`. -/
theorem spatialStrongBarrier_physical {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {m : ℝ} (hm : 0 < m) :
    ∃ dS dP R P c : ℝ, 0 < dS ∧ 0 < dP ∧ 0 < R ∧ 0 < P ∧ 0 < c ∧ DeficitBarrier ν U m dS dP ∧
      ∀ z : Phase (n * 3), SpatialBarrierState ν U m z →
        (∀ i, dS ≤ spatialKeplerAxis ν z i * (1 - spaceLength (spatialKeplerEccVector ν z i))) ∧
        (∀ a : AdjIdx n, dP ≤ spatialKeplerAxis ν z a.upperIdx *
            (1 - spaceLength (spatialKeplerEccVector ν z a.upperIdx)) -
          spatialKeplerAxis ν z a.1 * (1 + spaceLength (spatialKeplerEccVector ν z a.1))) ∧
        (∀ i, dS ≤ spaceLength (bodyVector3 z.1 i)) ∧
        (∀ i j, i ≠ j → dP ≤ spaceLength (bodyVector3 z.1 i - bodyVector3 z.1 j)) ∧
        (∀ i, spaceLength (bodyVector3 z.1 i) ≤ R) ∧
        (∀ i, spaceLength (bodyVector3 z.2 i) ≤ P) ∧
        (∀ i, spatialKeplerEnergy ν z i ≤ -c) ∧
        (angularMomentum3 z ≠ 0 ∧ ∀ i, m ≤
          spaceDot (planetAngularMomentum3 z i) (spatialUnit (angularMomentum3 z))) := by
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
  have hz : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 z.1 i) ∧ spatialKeplerEnergy ν z i < 0 :=
    hphys
  have he : ∀ i, spaceLength (spatialKeplerEccVector ν z i) ∈ Set.Icc (0 : ℝ) 1 := fun i =>
    ⟨spaceLength_nonneg _, (spatial_orbital_identities i (hz i)).2.2.2.2.1⟩
  have hsum : ∑ i, spatialActionVector ν z i *
      eccDeficit (spaceLength (spatialKeplerEccVector ν z i)) ≤
      strongThreshold ν (spatialActionVector ν z) - m :=
    (sum_action_mul_eccDeficit_le_spatialStrongAMD hphys).trans hC
  obtain ⟨hS, hG⟩ := hB _ hU _ he hsum
  simp only [actionAxis_spatialActionVector hphys] at hS hG
  refine ⟨hS, hG, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hS i).trans (spatial_orbital_identities i (hz i)).2.2.2.2.2.2.2.1
  · intro i j hij
    have hq : ∀ k, spatialKeplerAxis ν z k * (1 - spaceLength (spatialKeplerEccVector ν z k)) ≤
        spaceLength (bodyVector3 z.1 k) := fun k =>
      (spatial_orbital_identities k (hz k)).2.2.2.2.2.2.2.1
    have hq' : ∀ k, spaceLength (bodyVector3 z.1 k) ≤
        spatialKeplerAxis ν z k * (1 + spaceLength (spatialKeplerEccVector ν z k)) := fun k =>
      (spatial_orbital_identities k (hz k)).2.2.2.2.2.2.2.2.1
    have hPA : ∀ k, spatialKeplerAxis ν z k * (1 - spaceLength (spatialKeplerEccVector ν z k)) ≤
        spatialKeplerAxis ν z k * (1 + spaceLength (spatialKeplerEccVector ν z k)) := fun k =>
      mul_le_mul_of_nonneg_left (by linarith [spaceLength_nonneg (spatialKeplerEccVector ν z k)])
        (spatial_orbital_identities k (hz k)).1.le
    have hord : ∀ {k l : Fin n}, k < l →
        dP ≤ spaceLength (bodyVector3 z.1 l - bodyVector3 z.1 k) := fun {k l} hkl => by
      have hc := chain_gap hdP.le hPA hG hkl
      have h1 := spaceLength_le_add_sub (bodyVector3 z.1 k) (bodyVector3 z.1 l)
      rw [spaceLength_sub_comm] at h1
      have := hq l
      have := hq' k
      linarith
    rcases lt_or_gt_of_ne hij with h | h
    · rw [spaceLength_sub_comm]; exact hord h
    · exact hord h
  · intro i
    obtain ⟨ha, -, -, -, he1, -, -, -, hap, -⟩ := spatial_orbital_identities i (hz i)
    have h1 := hMa _ hU i
    rw [actionAxis_spatialActionVector hphys] at h1
    have h2 := spaceLength_nonneg (spatialKeplerEccVector ν z i)
    calc spaceLength (bodyVector3 z.1 i) ≤ spatialKeplerAxis ν z i * (1 + _) := hap
      _ ≤ spatialKeplerAxis ν z i * 2 := mul_le_mul_of_nonneg_left (by linarith) ha.le
      _ ≤ 2 * M := by linarith
  · intro i
    obtain ⟨ha, -, -, -, -, -, -, -, -, hp2⟩ := spatial_orbital_identities i (hz i)
    have hq : dS ≤ spaceLength (bodyVector3 z.1 i) :=
      (hS i).trans (spatial_orbital_identities i (hz i)).2.2.2.2.2.2.2.1
    have hq0 : 0 < spaceLength (bodyVector3 z.1 i) := (hz i).2.1
    have hν' := hν i
    have hνj : ν i ≤ ν j0 := hj0 i (Finset.mem_univ i)
    refine Real.sqrt_le_iff.2 ⟨by have := hν j0; positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity), hp2]
    have h1 : 2 / spaceLength (bodyVector3 z.1 i) - 1 / spatialKeplerAxis ν z i ≤ 2 / dS := by
      have : 2 / spaceLength (bodyVector3 z.1 i) ≤ 2 / dS :=
        div_le_div_of_nonneg_left (by norm_num) hdS hq
      have : 0 < 1 / spatialKeplerAxis ν z i := by positivity
      linarith
    calc ν i ^ 2 * (2 / spaceLength (bodyVector3 z.1 i) - 1 / spatialKeplerAxis ν z i)
        ≤ ν i ^ 2 * (2 / dS) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ ≤ ν j0 ^ 2 * (2 / dS) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hν'.le hνj 2) (by positivity)
  · intro i
    have ha := (spatial_orbital_identities i (hz i)).1
    have h1 := hMa _ hU i
    rw [actionAxis_spatialActionVector hphys] at h1
    have hE : spatialKeplerEnergy ν z i = -(ν i / (2 * spatialKeplerAxis ν z i)) := by
      have := (hz i).2.2.ne
      have := (hν i).ne'
      unfold spatialKeplerAxis
      field_simp
    rw [hE]
    have h3 : ν i0 / (2 * M) ≤ ν i / (2 * spatialKeplerAxis ν z i) :=
      div_le_div₀ (hν i).le (hi0' i (Finset.mem_univ i)) (by positivity) (by linarith)
    linarith
  · have hC' : ∀ i, spatialStrongAMD ν z ≤ spatialKeplerAction ν z i - m := fun i => by
      have := strongThreshold_le_action ν (spatialActionVector ν z) i
      have h : spatialActionVector ν z i = spatialKeplerAction ν z i := rfl
      linarith
    exact ⟨(proj_margin hphys hm hC' ⟨0, by omega⟩).1, fun i => (proj_margin hphys hm hC' i).2⟩

/-! ### Compactness -/

theorem continuous_bodyVector3' (i : Fin n) :
    Continuous (fun q : Fin (n * 3) → ℝ => bodyVector3 q i) := by
  unfold bodyVector3; fun_prop

/-- The compact set of barrier states for given constants. -/
def spatialBarrierCompact (n : ℕ) (dS dP R P : ℝ) : Set (Phase (n * 3)) :=
  {z | (∀ i, dS ≤ spaceLength (bodyVector3 z.1 i) ∧ spaceLength (bodyVector3 z.1 i) ≤ R ∧
      spaceLength (bodyVector3 z.2 i) ≤ P) ∧
    ∀ i j, i ≠ j → dP ≤ spaceLength (bodyVector3 z.1 i - bodyVector3 z.1 j)}

theorem spatialBarrierCompact_isCompact {dS dP R P : ℝ} (hR : 0 ≤ R) (hP : 0 ≤ P) :
    IsCompact (spatialBarrierCompact n dS dP R P) := by
  have hcl : IsClosed (spatialBarrierCompact n dS dP R P) := by
    have e : spatialBarrierCompact n dS dP R P = (⋂ i,
        {z : Phase (n * 3) | dS ≤ spaceLength (bodyVector3 z.1 i)} ∩
        {z | spaceLength (bodyVector3 z.1 i) ≤ R} ∩
        {z | spaceLength (bodyVector3 z.2 i) ≤ P}) ∩
        ⋂ i, ⋂ j, ⋂ (_ : i ≠ j),
          {z : Phase (n * 3) | dP ≤ spaceLength (bodyVector3 z.1 i - bodyVector3 z.1 j)} := by
      ext z
      simp only [spatialBarrierCompact, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun i => ⟨⟨(h1 i).1, (h1 i).2.1⟩, (h1 i).2.2⟩, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun i => ⟨(h1 i).1.1, (h1 i).1.2, (h1 i).2⟩, h2⟩
    rw [e]
    refine IsClosed.inter (isClosed_iInter fun i => ?_) (isClosed_iInter fun i =>
      isClosed_iInter fun j => isClosed_iInter fun _ => ?_)
    · have c1 : Continuous fun z : Phase (n * 3) => spaceLength (bodyVector3 z.1 i) :=
        continuous_spaceLength.comp ((continuous_bodyVector3' i).comp continuous_fst)
      have c2 : Continuous fun z : Phase (n * 3) => spaceLength (bodyVector3 z.2 i) :=
        continuous_spaceLength.comp ((continuous_bodyVector3' i).comp continuous_snd)
      exact ((isClosed_le continuous_const c1).inter (isClosed_le c1 continuous_const)).inter
        (isClosed_le c2 continuous_const)
    · exact isClosed_le continuous_const (continuous_spaceLength.comp
        (((continuous_bodyVector3' i).comp continuous_fst).sub
          ((continuous_bodyVector3' j).comp continuous_fst)))
  have hbd : Bornology.IsBounded (spatialBarrierCompact n dS dP R P) := by
    have hcoord : ∀ (w : Fin (n * 3) → ℝ) (C : ℝ), 0 ≤ C →
        (∀ i, spaceLength (bodyVector3 w i) ≤ C) → ‖w‖ ≤ C := by
      intro w C hC h
      refine (pi_norm_le_iff_of_nonneg hC).2 fun a => ?_
      have ha : finProdFinEquiv (finProdFinEquiv.symm a) = a := Equiv.apply_symm_apply _ _
      set p := finProdFinEquiv.symm a
      have hw : w a = bodyVector3 w p.1 p.2 := by unfold bodyVector3; rw [← ha]
      rw [hw]
      exact (norm_le_pi_norm (bodyVector3 w p.1) p.2).trans
        ((norm_le_spaceLength _).trans (h p.1))
    refine isBounded_iff_forall_norm_le.2 ⟨max R P, fun z hz => ?_⟩
    rw [Prod.norm_def]
    refine max_le (le_max_of_le_left ?_) (le_max_of_le_right ?_)
    · exact hcoord _ _ hR fun i => (hz.1 i).2.1
    · exact hcoord _ _ hP fun i => (hz.1 i).2.2
  exact Metric.isCompact_of_isClosed_isBounded hcl hbd

theorem spatialBarrierCompact_subset {dS dP R P : ℝ} (hdS : 0 < dS) (hdP : 0 < dP) :
    spatialBarrierCompact n dS dP R P ⊆ spatialCollisionFreeDomain n := fun _ hz =>
  ⟨fun i => hdS.trans_le (hz.1 i).1, fun i j hij => hdP.trans_le (hz.2 i j hij)⟩

/-- G3 (`LP:MAIN L5 (172)`, `d = 3`): all spatial barrier states lie in one compact subset of the
collision-free domain. -/
theorem exists_spatialBarrierCompact {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {m : ℝ} (hm : 0 < m) :
    ∃ K : Set (Phase (n * 3)), IsCompact K ∧ K ⊆ {z | SpatialNoCollision z.1} ∧
      ∀ z, SpatialBarrierState ν U m z → z ∈ K := by
  obtain ⟨dS, dP, R, P, c, hdS, hdP, hR, hP, -, -, h⟩ :=
    spatialStrongBarrier_physical hν hn hUc hUch hm
  refine ⟨spatialBarrierCompact n dS dP R P, spatialBarrierCompact_isCompact hR.le hP.le,
    spatialBarrierCompact_subset hdS hdP, fun z hz => ?_⟩
  obtain ⟨-, -, h3, h4, h5, h6, -⟩ := h z hz
  exact ⟨fun i => ⟨h3 i, h5 i, h6 i⟩, h4⟩

/-! ### N11: the explicit perihelion floor `d_⋆` -/

/-- N11 / (16), `d = 3`: on a spatial barrier state whose action vector has all axes `≥ aMin > 0`
and all actions `≤ Imax`, the perihelion is at least `d_⋆ = a_min m² / (2 I_max²)`
(`perihelionFloor`), hence also `|q_i| ≥ d_⋆` and `|p_i| ≤ ν_i √(2 / d_⋆)`. -/
theorem spatialPerihelionFloor_le {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {U : Set (Fin n → ℝ)}
    {m : ℝ} (hm : 0 < m) {aMin Imax : ℝ} (haMin : 0 < aMin)
    (hax : ∀ I ∈ U, ∀ i, aMin ≤ actionAxis ν I i) (hI : ∀ I ∈ U, ∀ i, I i ≤ Imax)
    {z : Phase (n * 3)} (hz : SpatialBarrierState ν U m z) (i : Fin n) :
    perihelionFloor aMin Imax m ≤
        spatialKeplerAxis ν z i * (1 - spaceLength (spatialKeplerEccVector ν z i)) ∧
      perihelionFloor aMin Imax m ≤ spaceLength (bodyVector3 z.1 i) ∧
      spaceLength (bodyVector3 z.2 i) ≤ ν i * Real.sqrt (2 / perihelionFloor aMin Imax m) := by
  obtain ⟨hphys, hU, hC⟩ := hz
  obtain ⟨ha, hΛ, -, -, he1, habs, -, hper, -, hp2⟩ := spatial_orbital_identities i (hphys i)
  have hsum := sum_action_mul_eccDeficit_le_spatialStrongAMD hphys
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ spatialKeplerAction ν z j *
      (1 - Real.sqrt (1 - spaceLength (spatialKeplerEccVector ν z j) ^ 2)) := fun j _ => by
    obtain ⟨-, hΛj, -, -, hej, -⟩ := spatial_orbital_identities j (hphys j)
    refine mul_nonneg hΛj.le ?_
    have := eccDeficit_nonneg (u := spaceLength (spatialKeplerEccVector ν z j))
      ⟨spaceLength_nonneg _, hej⟩
    exact this
  have hle1 := Finset.single_le_sum hnn (Finset.mem_univ i)
  have hB := strongThreshold_le_action ν (spatialActionVector ν z) i
  have hact : spatialActionVector ν z i = spatialKeplerAction ν z i := rfl
  set e := spaceLength (spatialKeplerEccVector ν z i) with he
  set s := Real.sqrt (1 - e ^ 2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hΛs : m ≤ spatialKeplerAction ν z i * s := by nlinarith
  have hImax : spatialKeplerAction ν z i ≤ Imax := by rw [← hact]; exact hI _ hU i
  have he0 : 0 ≤ e := spaceLength_nonneg _
  have hsq : s ^ 2 = 1 - e ^ 2 := Real.sq_sqrt (by nlinarith)
  have hImax_pos : 0 < Imax := hΛ.trans_le hImax
  have hs_ge : m / Imax ≤ s := by
    rw [div_le_iff₀ hImax_pos]
    nlinarith [mul_le_mul_of_nonneg_right hImax hs0]
  have hs2 : (m / Imax) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) hs_ge 2
  have h1e : s ^ 2 / 2 ≤ 1 - e := by nlinarith [sq_nonneg (1 - e)]
  have ha_ge : aMin ≤ spatialKeplerAxis ν z i := by
    rw [← actionAxis_spatialActionVector hphys]; exact hax _ hU i
  have hfl : perihelionFloor aMin Imax m ≤ spatialKeplerAxis ν z i * (1 - e) := by
    calc perihelionFloor aMin Imax m = aMin * ((m / Imax) ^ 2 / 2) := by
          unfold perihelionFloor; field_simp
      _ ≤ aMin * (1 - e) := mul_le_mul_of_nonneg_left (by linarith) haMin.le
      _ ≤ spatialKeplerAxis ν z i * (1 - e) :=
        mul_le_mul_of_nonneg_right ha_ge (by linarith)
  have hq := hfl.trans hper
  have hd0 : 0 < perihelionFloor aMin Imax m := by unfold perihelionFloor; positivity
  refine ⟨hfl, hq, ?_⟩
  have hν' := hν i
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by positivity), hp2]
  have h2 : 2 / spaceLength (bodyVector3 z.1 i) ≤ 2 / perihelionFloor aMin Imax m :=
    div_le_div_of_nonneg_left (by norm_num) hd0 hq
  have h3 : 0 < 1 / spatialKeplerAxis ν z i := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)

end KAM.Planetary.Spatial

end
