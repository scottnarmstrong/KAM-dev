/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Plane
public import KAM.Frozen.Iso.Defs.Radius
public import KAM.Frozen.Iso.Defs.RadiusSq
public import KAM.Frozen.Iso.Defs.Primary1
public import KAM.Frozen.Iso.Defs.Primary2
public import KAM.Frozen.Iso.Defs.CollisionFree

/-!
# Collision exclusion

Blueprint-I Part 8: `bpI:p8:collision-exclusion`, `bpI:p8:shell-exclusion` and
`bpI:p8:min-distance`.

* The physical length `radius` is the Euclidean length of `Fin 2 → ℝ`, not the ambient sup
  norm (blueprint issue B1). Its subadditivity, evenness and definiteness are the plane-length
  helpers of `KAM.Kepler.Plane`; it is nonnegative and continuous.
* `collision_exclusion_quant` and `collision_exclusion_compact` are stated for an abstract
  length `ℓ : X → ℝ` (subadditive, even) on an abelian group; `exclusionMu c μ₁ δ` is the
  threshold `μ_*` of part (a).
* `shell_exclusion` instantiates them at `ℓ = radius` and the two primaries; `min_distance` is
  the compactness argument for pairwise distinct points.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Iso.Collision

open KAM.Iso

/-- `radius` is a length: the plane-length helpers of `KAM.Kepler.Plane` (proved on `inp`) via
`radius_eq_planeLength` (`rfl`). `radius` is NOT the ambient sup norm of `Fin 2 → ℝ`. -/
theorem radius_add_le (u v : Fin 2 → ℝ) : radius (u + v) ≤ radius u + radius v :=
  KAM.Kepler.planeLength_add_le u v

theorem radius_neg (u : Fin 2 → ℝ) : radius (-u) = radius u := KAM.Kepler.planeLength_neg u

theorem radius_eq_zero_iff (u : Fin 2 → ℝ) : radius u = 0 ↔ u = 0 :=
  KAM.Kepler.planeLength_eq_zero_iff

theorem radius_nonneg (u : Fin 2 → ℝ) : 0 ≤ radius u := Real.sqrt_nonneg _

theorem continuous_radius : Continuous radius :=
  Real.continuous_sqrt.comp
    (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2)

/-- The threshold `μ_*` of `bpI:p8:collision-exclusion` (a): `μ₁` if `c = 0`, else
`min {μ₁, δ/(2c)}`. -/
def exclusionMu (c μ₁ δ : ℝ) : ℝ := if c = 0 then μ₁ else min μ₁ (δ / (2 * c))

theorem exclusionMu_pos {c μ₁ δ : ℝ} (hc : 0 ≤ c) (hμ₁ : 0 < μ₁) (hδ : 0 < δ) :
    0 < exclusionMu c μ₁ δ := by
  unfold exclusionMu
  split_ifs with h
  · exact hμ₁
  · have hc' : 0 < c := lt_of_le_of_ne hc (Ne.symm h)
    exact lt_min hμ₁ (by positivity)

private theorem exclusionMu_le (c μ₁ δ : ℝ) : exclusionMu c μ₁ δ ≤ μ₁ := by
  unfold exclusionMu
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

private theorem mul_exclusionMu_le {c : ℝ} (μ₁ : ℝ) {δ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) :
    c * exclusionMu c μ₁ δ ≤ δ / 2 := by
  unfold exclusionMu
  split_ifs with h
  · simp only [h, zero_mul]
    positivity
  · have hc' : 0 < c := lt_of_le_of_ne hc (Ne.symm h)
    calc c * min μ₁ (δ / (2 * c)) ≤ c * (δ / (2 * c)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hc
      _ = δ / 2 := by field_simp

/-- (a), quantitative form, for an abstract length `ℓ` (subadditive, even) on an abelian group:
for `S` with `ℓ(q - x_j) ≥ δ`, all `|μ| ≤ μ_*`: `ℓ(q - y_j(μ)) ≥ δ/2`. -/
theorem collision_exclusion_quant {X : Type*} [AddCommGroup X] (ℓ : X → ℝ)
    (htri : ∀ u v, ℓ (u + v) ≤ ℓ u + ℓ v) (hneg : ∀ u, ℓ (-u) = ℓ u) {m : ℕ} (x : Fin m → X)
    {c μ₁ : ℝ} (hc : 0 ≤ c) (hμ₁ : 0 < μ₁) (y : Fin m → ℝ → X)
    (hy : ∀ j μ, |μ| ≤ μ₁ → ℓ (y j μ - x j) ≤ c * |μ|) {S : Set X} {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ q ∈ S, ∀ j, δ ≤ ℓ (q - x j)) :
    ∀ μ : ℝ, |μ| ≤ exclusionMu c μ₁ δ → ∀ q ∈ S, ∀ j, δ / 2 ≤ ℓ (q - y j μ) := by
  -- `hneg` and `hμ₁` are part of the statement (the abstract length is even, `μ₁ > 0`) but the
  -- proof only needs subadditivity.
  have _unused : (∀ u, ℓ (-u) = ℓ u) ∧ 0 < μ₁ := ⟨hneg, hμ₁⟩
  intro μ hμ q hq j
  have hμ1 : |μ| ≤ μ₁ := hμ.trans (exclusionMu_le c μ₁ δ)
  have h1 : c * |μ| ≤ δ / 2 :=
    (mul_le_mul_of_nonneg_left hμ hc).trans (mul_exclusionMu_le μ₁ hc hδ.le)
  have h2 : q - x j = (q - y j μ) + (y j μ - x j) := (sub_add_sub_cancel q (y j μ) (x j)).symm
  have h3 : δ ≤ ℓ (q - y j μ) + c * |μ| :=
    calc δ ≤ ℓ (q - x j) := hS q hq j
      _ = ℓ ((q - y j μ) + (y j μ - x j)) := by rw [← h2]
      _ ≤ ℓ (q - y j μ) + ℓ (y j μ - x j) := htri _ _
      _ ≤ ℓ (q - y j μ) + c * |μ| := by linarith [hy j μ hμ1]
  linarith

/-- A finite family of continuous functions, each positive on a compact set `S`, has a common
positive lower bound on `S` (any `δ = 1` if `S` is empty or the family is empty). -/
private theorem exists_pos_lower_bound {X J : Type*} [TopologicalSpace X] [Finite J]
    {S : Set X} (hS : IsCompact S) (f : J → X → ℝ) (hf : ∀ j, Continuous (f j))
    (hpos : ∀ j, ∀ q ∈ S, 0 < f j q) : ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ S, ∀ j, δ ≤ f j q := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · have key : ∀ j, ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ S, δ ≤ f j q := by
      intro j
      obtain ⟨q₀, hq₀, hmin⟩ := hS.exists_isMinOn hne (hf j).continuousOn
      exact ⟨f j q₀, hpos j q₀ hq₀, fun q hq => hmin hq⟩
    choose δ hδ hle using key
    rcases isEmpty_or_nonempty J with hJ | hJ
    · exact ⟨1, one_pos, fun q _ j => (hJ.false j).elim⟩
    · obtain ⟨j₀, hj₀⟩ := Finite.exists_min δ
      exact ⟨δ j₀, hδ j₀, fun q hq j => (hj₀ j).trans (hle j q hq)⟩

/-- Attained version of `exists_pos_lower_bound`: for a nonempty compact `S` and a finite
nonempty family of continuous functions, each positive on `S`, the minimum over `j` of the
minimum over `S` is attained at some `(q₀, j₀)` and is positive. -/
private theorem exists_attained_lower_bound {X J : Type*} [TopologicalSpace X] [Finite J]
    [Nonempty J] {S : Set X} (hS : IsCompact S) (hne : S.Nonempty) (f : J → X → ℝ)
    (hf : ∀ j, Continuous (f j)) (hpos : ∀ j, ∀ q ∈ S, 0 < f j q) :
    ∃ (δ : ℝ) (q₀ : X) (j₀ : J), 0 < δ ∧ q₀ ∈ S ∧ δ = f j₀ q₀ ∧ ∀ q ∈ S, ∀ j, δ ≤ f j q := by
  have key : ∀ j, ∃ q₀ ∈ S, ∀ q ∈ S, f j q₀ ≤ f j q := by
    intro j
    obtain ⟨q₀, hq₀, hmin⟩ := hS.exists_isMinOn hne (hf j).continuousOn
    exact ⟨q₀, hq₀, fun q hq => hmin hq⟩
  choose q₀ hq₀ hle using key
  obtain ⟨j₀, hj₀⟩ := Finite.exists_min fun j => f j (q₀ j)
  exact ⟨f j₀ (q₀ j₀), q₀ j₀, j₀, hpos j₀ _ (hq₀ j₀), hq₀ j₀, rfl,
    fun q hq j => (hj₀ j).trans (hle j q hq)⟩

/-- (b), compact sets: `x_j ∉ S`, `S` compact, `ℓ` continuous and definite: there is `δ_S > 0`
(any `δ_S = 1` if `S = ∅` or `m = 0`) with `ℓ(q - x_j) ≥ δ_S` and the conclusion of (a). -/
theorem collision_exclusion_compact {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] (ℓ : X → ℝ) (htri : ∀ u v, ℓ (u + v) ≤ ℓ u + ℓ v)
    (hneg : ∀ u, ℓ (-u) = ℓ u) (hcont : Continuous ℓ) (hnonneg : ∀ u, 0 ≤ ℓ u)
    (hzero : ∀ u, ℓ u = 0 → u = 0)
    {m : ℕ} (x : Fin m → X) {c μ₁ : ℝ} (hc : 0 ≤ c) (hμ₁ : 0 < μ₁) (y : Fin m → ℝ → X)
    (hy : ∀ j μ, |μ| ≤ μ₁ → ℓ (y j μ - x j) ≤ c * |μ|) {S : Set X} (hS : IsCompact S)
    (hxS : ∀ j, x j ∉ S) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ q ∈ S, ∀ j, δ ≤ ℓ (q - x j)) ∧
      ∀ μ : ℝ, |μ| ≤ exclusionMu c μ₁ δ → ∀ q ∈ S, ∀ j, δ / 2 ≤ ℓ (q - y j μ) := by
  have hpos : ∀ j, ∀ q ∈ S, 0 < (fun j q => ℓ (q - x j)) j q := by
    intro j q hq
    refine lt_of_le_of_ne (hnonneg _) fun h => hxS j ?_
    have h0 : q - x j = 0 := hzero _ h.symm
    rwa [sub_eq_zero.mp h0] at hq
  obtain ⟨δ, hδ, hle⟩ := exists_pos_lower_bound hS (fun j q => ℓ (q - x j))
    (fun j => hcont.comp (continuous_id.sub continuous_const)) hpos
  exact ⟨δ, hδ, hle, collision_exclusion_quant ℓ htri hneg x hc hμ₁ y hy hδ hle⟩

/-- `bpI:p8:collision-exclusion` (b), source form for `S ≠ ∅` and `m ≥ 1`: the distance
`δ_S = min_j min_{q ∈ S} ℓ(q - x_j)` is attained (at `q₀ ∈ S`, index `j₀`), it is positive, it
bounds every value from below, and (a) applies with `δ = δ_S`. -/
theorem collision_exclusion_compact_attained {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] (ℓ : X → ℝ) (htri : ∀ u v, ℓ (u + v) ≤ ℓ u + ℓ v)
    (hneg : ∀ u, ℓ (-u) = ℓ u) (hcont : Continuous ℓ) (hnonneg : ∀ u, 0 ≤ ℓ u)
    (hzero : ∀ u, ℓ u = 0 → u = 0)
    {m : ℕ} (hm : 0 < m) (x : Fin m → X) {c μ₁ : ℝ} (hc : 0 ≤ c) (hμ₁ : 0 < μ₁)
    (y : Fin m → ℝ → X) (hy : ∀ j μ, |μ| ≤ μ₁ → ℓ (y j μ - x j) ≤ c * |μ|) {S : Set X}
    (hS : IsCompact S) (hne : S.Nonempty) (hxS : ∀ j, x j ∉ S) :
    ∃ δ : ℝ, 0 < δ ∧ (∃ q₀ ∈ S, ∃ j₀ : Fin m, δ = ℓ (q₀ - x j₀)) ∧
      (∀ q ∈ S, ∀ j, δ ≤ ℓ (q - x j)) ∧
      ∀ μ : ℝ, |μ| ≤ exclusionMu c μ₁ δ → ∀ q ∈ S, ∀ j, δ / 2 ≤ ℓ (q - y j μ) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hpos : ∀ j, ∀ q ∈ S, 0 < (fun j q => ℓ (q - x j)) j q := by
    intro j q hq
    refine lt_of_le_of_ne (hnonneg _) fun h => hxS j ?_
    have h0 : q - x j = 0 := hzero _ h.symm
    rwa [sub_eq_zero.mp h0] at hq
  obtain ⟨δ, q₀, j₀, hδ, hq₀, hatt, hle⟩ := exists_attained_lower_bound hS hne
    (fun j q => ℓ (q - x j)) (fun j => hcont.comp (continuous_id.sub continuous_const)) hpos
  exact ⟨δ, hδ, ⟨q₀, hq₀, j₀, hatt⟩, hle,
    collision_exclusion_quant ℓ htri hneg x hc hμ₁ y hy hδ hle⟩

/-- `bpI:p8:shell-exclusion`: for `r_min ≤ rad q ≤ ρ_max < 1` and `|μ| ≤ ν₀/2`,
`ν₀ = min {r_min, 1 - ρ_max}`: `rad(q - a_j(μ)) ≥ ν₀/2`, `j = 1, 2`; hence collision free. -/
theorem shell_exclusion {rmin ρmax : ℝ} (h0 : 0 < rmin) (h1 : rmin ≤ ρmax) (h2 : ρmax < 1)
    {μ : ℝ} (hμ : |μ| ≤ min rmin (1 - ρmax) / 2) {q : Fin 2 → ℝ}
    (hq : rmin ≤ radius q ∧ radius q ≤ ρmax) :
    min rmin (1 - ρmax) / 2 ≤ radius (q - primary₁ μ) ∧
      min rmin (1 - ρmax) / 2 ≤ radius (q - primary₂ μ) := by
  -- `h1` is implied by `hq`; it is kept as in the blueprint statement.
  have _unused : rmin ≤ ρmax := h1
  have hν0 : 0 < min rmin (1 - ρmax) := lt_min h0 (by linarith)
  have hνr : min rmin (1 - ρmax) ≤ rmin := min_le_left _ _
  have hν1 : min rmin (1 - ρmax) ≤ 1 - ρmax := min_le_right _ _
  have hrad : ∀ a : ℝ, radius ![a, 0] = |a| := by
    intro a
    simp [radius, radiusSq, Fin.sum_univ_two, Real.sqrt_sq_eq_abs]
  have hone : radius ![1, 0] = 1 := by simpa using hrad 1
  have hdist : ∀ q' : Fin 2 → ℝ, 1 - radius q' ≤ radius (q' - ![1, 0]) := by
    intro q'
    have h := radius_add_le q' (-(q' - ![1, 0]))
    have hsum : q' + -(q' - ![1, 0]) = ![1, 0] := by abel
    rw [radius_neg, hsum, hone] at h
    linarith
  have hS : ∀ q' ∈ {q' : Fin 2 → ℝ | rmin ≤ radius q' ∧ radius q' ≤ ρmax}, ∀ j : Fin 2,
      min rmin (1 - ρmax) ≤ radius (q' - (![0, ![1, 0]] : Fin 2 → Fin 2 → ℝ) j) := by
    intro q' hq' j
    fin_cases j
    · simpa using hνr.trans hq'.1
    · have h := hdist q'
      show min rmin (1 - ρmax) ≤ radius (q' - ![1, 0])
      linarith [hq'.2]
  have hy : ∀ (j : Fin 2) (μ : ℝ), |μ| ≤ min rmin (1 - ρmax) / 2 →
      radius ((fun j μ => (![primary₁ μ, primary₂ μ] : Fin 2 → Fin 2 → ℝ) j) j μ -
        (![0, ![1, 0]] : Fin 2 → Fin 2 → ℝ) j) ≤ 1 * |μ| := by
    intro j μ _
    fin_cases j
    · have h : primary₁ μ - 0 = ![-μ, 0] := by simp [primary₁]
      simp [h, hrad]
    · have h : primary₂ μ - ![1, 0] = ![-μ, 0] := by
        ext i
        fin_cases i <;> simp [primary₂]
      simp [h, hrad]
  have key := collision_exclusion_quant (X := Fin 2 → ℝ) radius radius_add_le radius_neg
    (![0, ![1, 0]] : Fin 2 → Fin 2 → ℝ) (c := 1) (μ₁ := min rmin (1 - ρmax) / 2) zero_le_one
    (half_pos hν0) (fun j μ => (![primary₁ μ, primary₂ μ] : Fin 2 → Fin 2 → ℝ) j) hy
    (S := {q' | rmin ≤ radius q' ∧ radius q' ≤ ρmax}) (δ := min rmin (1 - ρmax)) hν0 hS
  have hmu : exclusionMu 1 (min rmin (1 - ρmax) / 2) (min rmin (1 - ρmax)) =
      min rmin (1 - ρmax) / 2 := by
    simp [exclusionMu]
  have hk := key μ (hμ.trans_eq hmu.symm) q hq
  exact ⟨hk 0, hk 1⟩

theorem shell_collisionFree {rmin ρmax : ℝ} (h0 : 0 < rmin) (h1 : rmin ≤ ρmax) (h2 : ρmax < 1)
    {μ : ℝ} (hμ : |μ| ≤ min rmin (1 - ρmax) / 2) {z : (Fin 2 → ℝ) × (Fin 2 → ℝ)}
    (hq : rmin ≤ radius z.1 ∧ radius z.1 ≤ ρmax) : CollisionFree μ z := by
  have hν : 0 < min rmin (1 - ρmax) / 2 := by
    have : 0 < min rmin (1 - ρmax) := lt_min h0 (by linarith)
    positivity
  obtain ⟨ha, hb⟩ := shell_exclusion h0 h1 h2 hμ hq
  exact ⟨lt_of_lt_of_le hν ha, lt_of_lt_of_le hν hb⟩

/-- `bpI:p8:min-distance`: a compact set of `N`-body configurations of pairwise
distinct points has a positive minimal separation, for any continuous definite length `ℓ`. -/
theorem min_distance {ι X : Type*} [Finite ι] [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] (ℓ : X → ℝ) (hcont : Continuous ℓ) (hnonneg : ∀ u, 0 ≤ ℓ u)
    (hzero : ∀ u, ℓ u = 0 → u = 0)
    {S : Set (ι → X)} (hS : IsCompact S) (hsep : ∀ q ∈ S, ∀ i j, i ≠ j → q i ≠ q j) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ S, ∀ i j, i ≠ j → δ ≤ ℓ (q i - q j) := by
  let f : {p : ι × ι // p.1 ≠ p.2} → (ι → X) → ℝ := fun p q => ℓ (q p.1.1 - q p.1.2)
  have hpos : ∀ p, ∀ q ∈ S, 0 < f p q := by
    intro p q hq
    refine lt_of_le_of_ne (hnonneg _) fun h => hsep q hq p.1.1 p.1.2 p.2 ?_
    exact sub_eq_zero.mp (hzero _ h.symm)
  have hf : ∀ p, Continuous (f p) := fun p =>
    hcont.comp ((continuous_apply p.1.1).sub (continuous_apply p.1.2))
  obtain ⟨δ, hδ, hle⟩ := exists_pos_lower_bound hS f hf hpos
  exact ⟨δ, hδ, fun q hq i j hij => hle q hq ⟨(i, j), hij⟩⟩

/-- `bpI:p8:min-distance`, source form (`N ≥ 2`, `S ≠ ∅`): the separation
`δ_S = min_{q ∈ S} min_{i ≠ j} ℓ(q_i - q_j)` is attained at some `q₀ ∈ S` and pair `i₀ ≠ j₀`,
it is positive, and it bounds every pairwise value from below. -/
theorem min_distance_attained {ι X : Type*} [Finite ι] [Nontrivial ι] [AddCommGroup X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] (ℓ : X → ℝ) (hcont : Continuous ℓ)
    (hnonneg : ∀ u, 0 ≤ ℓ u) (hzero : ∀ u, ℓ u = 0 → u = 0)
    {S : Set (ι → X)} (hS : IsCompact S) (hne : S.Nonempty)
    (hsep : ∀ q ∈ S, ∀ i j, i ≠ j → q i ≠ q j) :
    ∃ (δ : ℝ) (q₀ : ι → X) (i₀ j₀ : ι), 0 < δ ∧ q₀ ∈ S ∧ i₀ ≠ j₀ ∧
      δ = ℓ (q₀ i₀ - q₀ j₀) ∧ ∀ q ∈ S, ∀ i j, i ≠ j → δ ≤ ℓ (q i - q j) := by
  let f : {p : ι × ι // p.1 ≠ p.2} → (ι → X) → ℝ := fun p q => ℓ (q p.1.1 - q p.1.2)
  have : Nonempty {p : ι × ι // p.1 ≠ p.2} := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne ι
    exact ⟨⟨(a, b), hab⟩⟩
  have hpos : ∀ p, ∀ q ∈ S, 0 < f p q := by
    intro p q hq
    refine lt_of_le_of_ne (hnonneg _) fun h => hsep q hq p.1.1 p.1.2 p.2 ?_
    exact sub_eq_zero.mp (hzero _ h.symm)
  have hf : ∀ p, Continuous (f p) := fun p =>
    hcont.comp ((continuous_apply p.1.1).sub (continuous_apply p.1.2))
  obtain ⟨δ, q₀, p₀, hδ, hq₀, hatt, hle⟩ := exists_attained_lower_bound hS hne f hf hpos
  exact ⟨δ, q₀, p₀.1.1, p₀.1.2, hδ, hq₀, p₀.2, hatt,
    fun q hq i j hij => hle q hq ⟨(i, j), hij⟩⟩

end KAM.Iso.Collision
