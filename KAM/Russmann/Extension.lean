/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Measure.McShane
public import KAM.Measure.Lipeo
public import KAM.Measure.Lipschitz
public import KAM.Planetary.PG.Setting

/-!
# Track R: the global lipeomorphism and the near-full image estimate

Route (B) of `docs/tracks/R/PROOF-ROUTE.md` for the strong form of R-HEAD.

* `exists_lipeo_extension`: a map `u` that is `λ`-Lipschitz (`λ < 1`) and bounded by `Δ` on a set
  `A ⊆ ℝⁿ × ℝⁿ` extends to a global `λ`-Lipschitz map `Φ` bounded by `Δ` (McShane,
  `KAM.mcshane_prod`), and `E = id + Φ` is a bijection (`KAM.lipeo_onto`), `(1 + λ)`-Lipschitz,
  with `‖E - id‖ ≤ Δ` and `E = id + u` on `A`.
* `inner_subset_image`: a surjection moving points by at most `Δ` covers the `Δ`-interior
  `{z : closedBall z Δ ⊆ Ω}` of every set `Ω`. No degree theory is needed.
* `volume_image_cell_lower`: for such an `E`, `U ⊆ ℝⁿ` and `G ⊆ U`,
  `(1 - 2Δ)ⁿ · meas U_Δ ≤ meas E([0,1)ⁿ × G) + (1 + λ)^{2n} · meas (U ∖ G)` with
  `U_Δ = {b : closedBall b Δ ⊆ U}`.
* `exists_inner_volume_gt`: for `U` open, `meas U_Δ` exceeds any `a < meas U` for some `Δ > 0`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Russmann

open KAM KAM.Planetary

variable {n : ℕ}

/-- **The global lipeomorphism.** A `λ`-Lipschitz (`0 ≤ λ < 1`) map `u` bounded by `Δ ≥ 0` on `A`
gives a bijection `E` of `ℝⁿ × ℝⁿ` with `‖E x - x‖ ≤ Δ`, `(1 + λ)`-Lipschitz, and `E x = x + u x`
on `A`. -/
theorem exists_lipeo_extension {A : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    {u : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} {lam Δ : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hΔ : 0 ≤ Δ)
    (hlip : ∀ x ∈ A, ∀ y ∈ A, ‖u x - u y‖ ≤ lam * ‖x - y‖) (hbd : ∀ x ∈ A, ‖u x‖ ≤ Δ) :
    ∃ E : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ),
      Function.Bijective E ∧ (∀ x, ‖E x - x‖ ≤ Δ) ∧
      (∀ x y, ‖E x - E y‖ ≤ (1 + lam) * ‖x - y‖) ∧ ∀ x ∈ A, E x = x + u x := by
  obtain ⟨Φ, hΦl, hΦe, hΦb⟩ := (mcshane_prod (X := (Fin n → ℝ) × (Fin n → ℝ)) (S := A) hlam0
    (φ := u) (fun x hx y hy => by rw [dist_eq_norm]; exact hlip x hx y hy)).2 Δ hΔ hbd
  have hΦl' : ∀ x y, ‖Φ x - Φ y‖ ≤ lam * ‖x - y‖ := fun x y => by
    have := hΦl x y; rwa [dist_eq_norm] at this
  refine ⟨fun x => x + Φ x, (lipeo_onto hlam1 hΦl').1, fun x => by simpa using hΦb x,
    fun x y => ?_, fun x hx => by simp only [hΦe x hx]⟩
  have e : (x + Φ x) - (y + Φ y) = (x - y) + (Φ x - Φ y) := by abel
  rw [e]
  calc ‖(x - y) + (Φ x - Φ y)‖ ≤ ‖x - y‖ + ‖Φ x - Φ y‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ + lam * ‖x - y‖ := by gcongr; exact hΦl' x y
    _ = (1 + lam) * ‖x - y‖ := by ring

/-- A surjection moving points by at most `Δ` covers the `Δ`-interior of every set. -/
theorem inner_subset_image {X : Type*} [SeminormedAddCommGroup X] {E : X → X}
    (hE : Function.Surjective E) {Δ : ℝ} (hd : ∀ x, ‖E x - x‖ ≤ Δ) (Ω : Set X) :
    {z | closedBall z Δ ⊆ Ω} ⊆ E '' Ω := by
  intro z hz
  obtain ⟨w, rfl⟩ := hE z
  refine ⟨w, hz ?_, rfl⟩
  rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
  exact hd w

/-- The interior box `[Δ, 1 - Δ)ⁿ × U_Δ` lies in the `Δ`-interior of `[0,1)ⁿ × U`. -/
theorem box_subset_inner (U : Set (Fin n → ℝ)) (Δ : ℝ) :
    (Set.pi univ (fun _ : Fin n => Ico Δ (1 - Δ))) ×ˢ {b | closedBall b Δ ⊆ U} ⊆
      {z : (Fin n → ℝ) × (Fin n → ℝ) | closedBall z Δ ⊆ unitCube n ×ˢ U} := by
  rintro ⟨θ, b⟩ ⟨hθ, hb⟩ ⟨w₁, w₂⟩ hw
  rw [mem_closedBall, Prod.dist_eq, max_le_iff] at hw
  refine ⟨fun i _ => ?_, hb (by rw [mem_closedBall]; exact hw.2)⟩
  obtain ⟨h1, h2⟩ := hθ i (mem_univ i)
  have hi : |w₁ i - θ i| ≤ Δ := by
    have := (dist_le_pi_dist w₁ θ i).trans hw.1
    rwa [Real.dist_eq] at this
  rw [abs_le] at hi
  exact ⟨by linarith, by linarith⟩

theorem volume_box {Δ : ℝ} (hΔ : 2 * Δ ≤ 1) (S : Set (Fin n → ℝ)) :
    volume ((Set.pi univ (fun _ : Fin n => Ico Δ (1 - Δ))) ×ˢ S) =
      ENNReal.ofReal ((1 - 2 * Δ) ^ n) * volume S := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_pi_Ico,
    ENNReal.ofReal_pow (by linarith)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 2
  ring_nf

/-- **The near-full image estimate.** For a surjective, `(1 + λ)`-Lipschitz `E` with
`‖E - id‖ ≤ Δ ≤ 1/2` and `G ⊆ U`:
`(1 - 2Δ)ⁿ meas U_Δ ≤ meas E([0,1)ⁿ × G) + (1 + λ)^{2n} meas (U ∖ G)`. -/
theorem volume_image_cell_lower
    {E : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} (hE : Function.Surjective E)
    {Δ lam : ℝ} (hΔ : 2 * Δ ≤ 1) (hd : ∀ x, ‖E x - x‖ ≤ Δ)
    (hlip : ∀ x y, ‖E x - E y‖ ≤ (1 + lam) * ‖x - y‖) {U G : Set (Fin n → ℝ)} (hGU : G ⊆ U) :
    ENNReal.ofReal ((1 - 2 * Δ) ^ n) * volume {b | closedBall b Δ ⊆ U} ≤
      volume (E '' (unitCube n ×ˢ G)) +
        ENNReal.ofReal ((1 + lam) ^ (2 * n)) * volume (U \ G) := by
  have hsplit : unitCube n ×ˢ U = (unitCube n ×ˢ G) ∪ (unitCube n ×ˢ (U \ G)) := by
    rw [← prod_union, union_sdiff_cancel hGU]
  have hcube : volume (unitCube n) = 1 := by simp [unitCube, Real.volume_pi_Ico]
  calc ENNReal.ofReal ((1 - 2 * Δ) ^ n) * volume {b | closedBall b Δ ⊆ U}
      = volume ((Set.pi univ (fun _ : Fin n => Ico Δ (1 - Δ))) ×ˢ
          {b | closedBall b Δ ⊆ U}) := (volume_box hΔ _).symm
    _ ≤ volume (E '' (unitCube n ×ˢ U)) :=
        measure_mono ((box_subset_inner U Δ).trans (inner_subset_image hE hd _))
    _ ≤ volume (E '' (unitCube n ×ˢ G)) + volume (E '' (unitCube n ×ˢ (U \ G))) := by
        rw [hsplit, image_union]; exact measure_union_le _ _
    _ ≤ volume (E '' (unitCube n ×ˢ G)) +
          ENNReal.ofReal ((1 + lam) ^ (2 * n)) * volume (unitCube n ×ˢ (U \ G)) := by
        gcongr
        exact lip_image_prod fun x _ y _ => hlip x y
    _ = _ := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, hcube, one_mul]

/-- For `U` open and `a < meas U`, some `Δ > 0` has `a < meas {b : closedBall b Δ ⊆ U}`. -/
theorem exists_inner_volume_gt {U : Set (Fin n → ℝ)} (hU : IsOpen U) {a : ENNReal}
    (ha : a < volume U) : ∃ Δ : ℝ, 0 < Δ ∧ a < volume {b | closedBall b Δ ⊆ U} := by
  set s : ℕ → Set (Fin n → ℝ) := fun k => {b | closedBall b (1 / (k + 1 : ℝ)) ⊆ U} with hs
  have hmono : Monotone s := by
    intro k l hkl b hb
    refine (closedBall_subset_closedBall ?_).trans hb
    gcongr
  have hU' : U = ⋃ k, s k := by
    ext b
    refine ⟨fun hb => ?_, fun hb => ?_⟩
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU b hb
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hr
      exact mem_iUnion.2 ⟨k, (closedBall_subset_ball hk).trans hball⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.1 hb
      exact hk (mem_closedBall_self (by positivity))
  rw [hU', hmono.measure_iUnion] at ha
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 ha
  exact ⟨1 / (k + 1 : ℝ), by positivity, hk⟩

end KAM.Russmann

end
