/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Newtonian.Assembly
public import KAM.Planetary.Hamiltonian.Liouville

/-!
# Graph-node exports: reconstruction, orbit curve, tube assembly, positive measure

Append-only exports (package GAP-P6b) stating the literal conclusions of the Part 6 graph nodes
`stepP:p6:rc-a`, `rc-sun`, `rc-planets`, `rc-vplanet`, `rc-vsun`, `ot-curve`, `ma-tube`,
`ma-coll`, `ma-pair`, `mp-a`, `mp-b` and `bpP:p6:measure-positive`, built from the landed
`reconstruction`, `circularTube_*`, `liouville_lattice` and the Mathlib volume of a sup-norm ball.
-/

public section

open MeasureTheory

namespace KAM.Planetary

open KAM KAM.Kepler

section AssemblyNodes

variable {n : ℕ}

/-! ### Reconstruction instances (`bpP:p6:reconstruction`, Steps `rc-*`) -/

/-- `stepP:p6:rc-a`: the barycentric differences have the heliocentric lengths, which are positive;
the length is symmetric. -/
theorem rc_a_lengths {m0 μ : ℝ} {m : Fin n → ℝ} {J : Set ℝ} {z : ℝ → Phase (n * 2)}
    (hnc : ∀ t ∈ J, NoCollision (z t).1) :
    ∀ t ∈ J,
      (∀ i : Fin n,
        planeLength (barycentricPositions m0 m μ (z t).1 i.succ -
            barycentricPositions m0 m μ (z t).1 0) = planeLength (bodyVector (z t).1 i) ∧
          0 < planeLength (bodyVector (z t).1 i)) ∧
      (∀ i j : Fin n, i ≠ j →
        planeLength (barycentricPositions m0 m μ (z t).1 j.succ -
            barycentricPositions m0 m μ (z t).1 i.succ) =
            planeLength (bodyVector (z t).1 j - bodyVector (z t).1 i) ∧
          0 < planeLength (bodyVector (z t).1 j - bodyVector (z t).1 i)) ∧
      (∀ i j : Fin (n + 1),
        planeLength (barycentricPositions m0 m μ (z t).1 j - barycentricPositions m0 m μ (z t).1 i) =
          planeLength (barycentricPositions m0 m μ (z t).1 i -
            barycentricPositions m0 m μ (z t).1 j)) := by
  intro t ht
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j => planeLength_sub_comm _ _⟩
  · rw [barycentricPositions_succ_sub_zero]
    exact ⟨rfl, (hnc t ht).1 i⟩
  · rw [barycentricPositions_succ_sub_succ]
    exact ⟨rfl, (hnc t ht).2 j i (fun h => hij h.symm)⟩

/-- `stepP:p6:rc-sun`: `Q₀` has derivative `-(μ/m₀) P = V₀` at `t`, where `P = ∑ pⱼ`. -/
theorem rc_sun_hasDerivAt {G m0 μ : ℝ} {m : Fin n → ℝ} (hG : 0 < G) (hm0 : 0 < m0)
    (hm : ∀ i, 0 < m i) (hμ : 0 ≤ μ) {J : Set ℝ} {z : ℝ → Phase (n * 2)}
    (hz : ∀ t ∈ J, NoCollision (z t).1 ∧
      HasDerivAt z (hamiltonianVectorField (movingHamiltonian G m0 m μ) (z t)) t) :
    ∀ t ∈ J,
      HasDerivAt (fun s => barycentricPositions m0 m μ (z s).1 0)
        ((-μ / m0) • ∑ j, bodyVector (z t).2 j) t ∧
      (-μ / m0) • ∑ j, bodyVector (z t).2 j = barycentricVelocities m0 m μ (z t).2 0 := by
  intro t ht
  have h := (reconstruction hG hm0 hm hμ hz).2.1 t ht 0
  rw [← barycentricVelocities_zero]
  exact ⟨h, rfl⟩

/-- `stepP:p6:rc-planets`: `Qᵢ` has derivative `Vᵢ` at `t`, for each planet `i`. -/
theorem rc_planets_hasDerivAt {G m0 μ : ℝ} {m : Fin n → ℝ} (hG : 0 < G) (hm0 : 0 < m0)
    (hm : ∀ i, 0 < m i) (hμ : 0 ≤ μ) {J : Set ℝ} {z : ℝ → Phase (n * 2)}
    (hz : ∀ t ∈ J, NoCollision (z t).1 ∧
      HasDerivAt z (hamiltonianVectorField (movingHamiltonian G m0 m μ) (z t)) t) :
    ∀ t ∈ J, ∀ i : Fin n,
      HasDerivAt (fun s => barycentricPositions m0 m μ (z s).1 i.succ)
        (barycentricVelocities m0 m μ (z t).2 i.succ) t :=
  fun t ht i => (reconstruction hG hm0 hm hμ hz).2.1 t ht i.succ

/-- `stepP:p6:rc-vplanet`: `Vᵢ` has derivative `∑_{l ≠ i} G Mₗ (Qₗ - Qᵢ) / ℓ(Qₗ - Qᵢ)³` at `t`,
for each planet `i`. -/
theorem rc_vplanet_hasDerivAt {G m0 μ : ℝ} {m : Fin n → ℝ} (hG : 0 < G) (hm0 : 0 < m0)
    (hm : ∀ i, 0 < m i) (hμ : 0 ≤ μ) {J : Set ℝ} {z : ℝ → Phase (n * 2)}
    (hz : ∀ t ∈ J, NoCollision (z t).1 ∧
      HasDerivAt z (hamiltonianVectorField (movingHamiltonian G m0 m μ) (z t)) t) :
    ∀ t ∈ J, ∀ i : Fin n,
      HasDerivAt (fun s => barycentricVelocities m0 m μ (z s).2 i.succ)
        (∑ l ∈ Finset.univ.filter (fun l => l ≠ i.succ),
          (G * actualMasses m0 m μ l /
              planeLength (barycentricPositions m0 m μ (z t).1 l -
                barycentricPositions m0 m μ (z t).1 i.succ) ^ 3) •
            (barycentricPositions m0 m μ (z t).1 l -
              barycentricPositions m0 m μ (z t).1 i.succ)) t :=
  fun t ht i => (reconstruction hG hm0 hm hμ hz).2.2 t ht i.succ

/-- `stepP:p6:rc-vsun`: `V₀` has derivative `∑_{l ≥ 1} G Mₗ (Qₗ - Q₀) / ℓ(Qₗ - Q₀)³` at `t`. -/
theorem rc_vsun_hasDerivAt {G m0 μ : ℝ} {m : Fin n → ℝ} (hG : 0 < G) (hm0 : 0 < m0)
    (hm : ∀ i, 0 < m i) (hμ : 0 ≤ μ) {J : Set ℝ} {z : ℝ → Phase (n * 2)}
    (hz : ∀ t ∈ J, NoCollision (z t).1 ∧
      HasDerivAt z (hamiltonianVectorField (movingHamiltonian G m0 m μ) (z t)) t) :
    ∀ t ∈ J,
      HasDerivAt (fun s => barycentricVelocities m0 m μ (z s).2 0)
        (∑ l : Fin n,
          (G * actualMasses m0 m μ l.succ /
              planeLength (barycentricPositions m0 m μ (z t).1 l.succ -
                barycentricPositions m0 m μ (z t).1 0) ^ 3) •
            (barycentricPositions m0 m μ (z t).1 l.succ -
              barycentricPositions m0 m μ (z t).1 0)) t := by
  intro t ht
  have h := (reconstruction hG hm0 hm hμ hz).2.2 t ht 0
  refine h.congr_deriv ?_
  rw [Finset.sum_filter, Fin.sum_univ_succ]
  simp

/-! ### The orbit curve of a physical torus (`stepP:p6:ot-curve`) -/

/-- `stepP:p6:ot-curve`: along `t ↦ K (φ + t • w)` of a physical torus without collision, the
collision hypothesis holds at every time and the curve has derivative `X_H`. -/
theorem ot_curve {H : Phase (n * 2) → ℝ} {w : Fin (n * 2) → ℝ}
    {K : (Fin (n * 2) → ℝ) → Phase (n * 2)} (hK : IsPhysicalTorus H w K)
    (hnc : ∀ φ, NoCollision (K φ).1) (φ : Fin (n * 2) → ℝ) :
    ∀ t : ℝ, NoCollision (K (φ + t • w)).1 ∧
      HasDerivAt (fun s : ℝ => K (φ + s • w))
        (hamiltonianVectorField H (K (φ + t • w))) t :=
  fun t => ⟨hnc _, hK.2.2.2.2.2.2.2 φ t⟩

/-! ### Projections of the Kolmogorov-set assembly (`bpP:p6:movkol-assembly`) -/

/-- `stepP:p6:ma-tube`: a measurable set in the `ζ_*`-tube lies in the `η`-tube. -/
theorem ma_tube {G m0 : ℝ} {m a : Fin n → ℝ} {γ A η : ℝ} (hS_tube : AxisData a γ A)
    {S : Set (Phase (n * 2))} (hS : MeasurableSet S)
    (hSt : S ⊆ circularTube G m0 m a (tubeRadius η γ)) :
    S ⊆ circularTube G m0 m a η ∧ MeasurableSet S := by
  have _ := hS_tube
  exact ⟨hSt.trans (circularTube_mono (min_le_left _ _)), hS⟩

/-- `stepP:p6:ma-coll`: the torus through a point of `S` has no collision. -/
theorem ma_coll {G m0 : ℝ} {m a : Fin n → ℝ} {γ A η : ℝ} (h : AxisData a γ A) (hη : 0 < η)
    {S : Set (Phase (n * 2))} (hSt : S ⊆ circularTube G m0 m a (tubeRadius η γ))
    {K : (Fin (n * 2) → ℝ) → Phase (n * 2)} (hKS : Set.range K ⊆ S) (φ : Fin (n * 2) → ℝ) :
    NoCollision (K φ).1 :=
  (circularTube_pair_bounds h (tubeRadius_pos hη h.gap_pos) (min_le_right _ _)
    (hSt (hKS ⟨φ, rfl⟩))).2.2

/-- `stepP:p6:ma-pair`: pair bounds for the barycentric positions of every orbit point. -/
theorem ma_pair {G m0 μ : ℝ} {m a : Fin n → ℝ} {γ A η : ℝ} (h : AxisData a γ A) (hη : 0 < η)
    (hm0 : 0 < m0) (hm : ∀ i, 0 < m i) (hμ : 0 ≤ μ) {S : Set (Phase (n * 2))}
    (hSt : S ⊆ circularTube G m0 m a (tubeRadius η γ)) {w : Fin (n * 2) → ℝ}
    {K : (Fin (n * 2) → ℝ) → Phase (n * 2)} (hKS : Set.range K ⊆ S) (φ : Fin (n * 2) → ℝ)
    (t : ℝ) :
    PairBounds (tubeD γ) (tubeBigD γ A) (barycentricPositions m0 m μ (K (φ + t • w)).1) :=
  circularTube_pairBounds_barycentric h (tubeRadius_pos hη h.gap_pos) (min_le_right _ _) hm0 hm
    hμ (hSt (hKS ⟨φ + t • w, rfl⟩))

/-! ### Positive measure (`bpP:p6:measure-positive`) -/

/-- `stepP:p6:mp-a`: `U_η` lies in the box `|z₁|∞ < a_max + η`, `|z₂|∞ < P_max + η`, and every
subset has volume at most the box volume, which is finite. -/
theorem mp_a_box {G m0 : ℝ} {m a : Fin n → ℝ} {η : ℝ} (hG : 0 < G) (hm0 : 0 < m0)
    (hm : ∀ i, 0 < m i) (ha : ∀ i, 0 < a i) (hη : 0 < η) :
    circularTube G m0 m a η ⊆
        {z | ‖z.1‖ < (⨆ i, a i) + η ∧ ‖z.2‖ < (⨆ i, m i * √(G * m0 / a i)) + η} ∧
      ∀ S : Set (Phase (n * 2)), S ⊆ circularTube G m0 m a η →
        volume S ≤ ENNReal.ofReal ((2 * ((⨆ i, a i) + η)) ^ (n * 2)) *
            ENNReal.ofReal ((2 * ((⨆ i, m i * √(G * m0 / a i)) + η)) ^ (n * 2)) ∧
          ENNReal.ofReal ((2 * ((⨆ i, a i) + η)) ^ (n * 2)) *
            ENNReal.ofReal ((2 * ((⨆ i, m i * √(G * m0 / a i)) + η)) ^ (n * 2)) < ⊤ := by
  have hP : (⨆ i, |m i| * √(G * m0 / a i)) = ⨆ i, m i * √(G * m0 / a i) :=
    iSup_congr fun i => by rw [abs_of_pos (hm i)]
  have hbox : circularTube G m0 m a η ⊆
      {z | ‖z.1‖ < (⨆ i, a i) + η ∧ ‖z.2‖ < (⨆ i, m i * √(G * m0 / a i)) + η} := by
    intro z hz
    have h := circularTube_norm_lt hG hm0 ha hz
    rwa [hP] at h
  refine ⟨hbox, fun S hS => ?_⟩
  have hA : 0 ≤ ⨆ i, a i := Real.iSup_nonneg fun i => (ha i).le
  have hB : 0 ≤ ⨆ i, m i * √(G * m0 / a i) :=
    Real.iSup_nonneg fun i => mul_nonneg (hm i).le (Real.sqrt_nonneg _)
  have h1 : 0 < (⨆ i, a i) + η := by linarith
  have h2 : 0 < (⨆ i, m i * √(G * m0 / a i)) + η := by linarith
  have hsub : S ⊆ Metric.ball (0 : Fin (n * 2) → ℝ) ((⨆ i, a i) + η) ×ˢ
      Metric.ball (0 : Fin (n * 2) → ℝ) ((⨆ i, m i * √(G * m0 / a i)) + η) := by
    intro z hz
    obtain ⟨h1', h2'⟩ := hbox (hS hz)
    exact ⟨by simpa using h1', by simpa using h2'⟩
  have hvol : volume (Metric.ball (0 : Fin (n * 2) → ℝ) ((⨆ i, a i) + η) ×ˢ
      Metric.ball (0 : Fin (n * 2) → ℝ) ((⨆ i, m i * √(G * m0 / a i)) + η)) =
      ENNReal.ofReal ((2 * ((⨆ i, a i) + η)) ^ (n * 2)) *
        ENNReal.ofReal ((2 * ((⨆ i, m i * √(G * m0 / a i)) + η)) ^ (n * 2)) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_pi_ball _ h1,
      Real.volume_pi_ball _ h2]
    simp
  exact ⟨hvol ▸ measure_mono hsub, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ENNReal.ofReal_lt_top⟩

/-- `stepP:p6:mp-b`: the measure clauses of `liouville_lattice` for the chart image of a
lattice-periodic set `A` of positive measure, with finiteness when the image lies in `U_η`. -/
theorem mp_b_measure {G m0 : ℝ} {m a : Fin n → ℝ} {η c : ℝ} (hG : 0 < G) (hm0 : 0 < m0)
    (ha : ∀ i, 0 < a i) (hc : 0 < c) {O : Set (Phase (n * 2))} (hO : IsOpen O)
    {Ψ : Phase (n * 2) → Phase (n * 2)} (hΨ : IsChart c Ψ O)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin (n * 2) → ℤ,
      z + angleShift k ∈ O ∧ Ψ (z + angleShift k) = Ψ z)
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, Ψ z' = Ψ z → ∃ k : Fin (n * 2) → ℤ, z' = z + angleShift k)
    {A : Set (Phase (n * 2))} (hA : NullMeasurableSet A) (hAO : A ⊆ O)
    (hAper : ∀ k : Fin (n * 2) → ℤ, (fun z => z + angleShift k) '' A = A)
    (hApos : 0 < volume A) :
    NullMeasurableSet (Ψ '' A) ∧
      volume (Ψ '' A) = ENNReal.ofReal (c ^ (n * 2)) * volume (A ∩ unitCell (n * 2)) ∧
      0 < volume (Ψ '' A) ∧
      (Ψ '' A ⊆ circularTube G m0 m a η → volume (Ψ '' A) < ⊤) := by
  have h := liouville_lattice hc hO hΨ hQ1 hQ2 hA hAO hAper
  exact ⟨h.1, h.2.2.1, h.2.2.2.1.2 hApos, fun hS =>
    volume_lt_top_of_subset_circularTube hG hm0 ha hS⟩

/-- `stepP:p6:mp-b`, Borel clause: the chart image of a Borel lattice-periodic set is Borel. -/
theorem mp_b_measurableSet {c : ℝ} (hc : 0 < c) {O : Set (Phase (n * 2))} (hO : IsOpen O)
    {Ψ : Phase (n * 2) → Phase (n * 2)} (hΨ : IsChart c Ψ O)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin (n * 2) → ℤ,
      z + angleShift k ∈ O ∧ Ψ (z + angleShift k) = Ψ z)
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, Ψ z' = Ψ z → ∃ k : Fin (n * 2) → ℤ, z' = z + angleShift k)
    {A : Set (Phase (n * 2))} (hA : MeasurableSet A) (hAO : A ⊆ O)
    (hAper : ∀ k : Fin (n * 2) → ℤ, (fun z => z + angleShift k) '' A = A) :
    MeasurableSet (Ψ '' A) :=
  liouville_lattice_measurableSet hc hO hΨ hQ1 hQ2 hA hAO hAper

/-- `bpP:p6:measure-positive`: (a) the box bound for subsets of `U_η`; (b) for a chart `Ψ` with
lattice compatibility and a lattice-periodic set `A` of positive measure, the image is measurable
(Borel if `A` is Borel), `0 < vol Ψ(A) = c^{2n} vol(A ∩ Q)`, and `vol Ψ(A) < ∞` if `Ψ(A) ⊆ U_η`. -/
theorem measure_positive {G m0 : ℝ} {m a : Fin n → ℝ} {η : ℝ} (hG : 0 < G) (hm0 : 0 < m0)
    (hm : ∀ i, 0 < m i) (ha : ∀ i, 0 < a i) (hη : 0 < η) :
    (circularTube G m0 m a η ⊆
        {z | ‖z.1‖ < (⨆ i, a i) + η ∧ ‖z.2‖ < (⨆ i, m i * √(G * m0 / a i)) + η} ∧
      ∀ S : Set (Phase (n * 2)), S ⊆ circularTube G m0 m a η →
        volume S ≤ ENNReal.ofReal ((2 * ((⨆ i, a i) + η)) ^ (n * 2)) *
            ENNReal.ofReal ((2 * ((⨆ i, m i * √(G * m0 / a i)) + η)) ^ (n * 2)) ∧
          ENNReal.ofReal ((2 * ((⨆ i, a i) + η)) ^ (n * 2)) *
            ENNReal.ofReal ((2 * ((⨆ i, m i * √(G * m0 / a i)) + η)) ^ (n * 2)) < ⊤) ∧
    ∀ {c : ℝ}, 0 < c → ∀ {O : Set (Phase (n * 2))}, IsOpen O →
      ∀ {Ψ : Phase (n * 2) → Phase (n * 2)}, IsChart c Ψ O →
      (∀ z ∈ O, ∀ k : Fin (n * 2) → ℤ,
        z + angleShift k ∈ O ∧ Ψ (z + angleShift k) = Ψ z) →
      (∀ z ∈ O, ∀ z' ∈ O, Ψ z' = Ψ z → ∃ k : Fin (n * 2) → ℤ, z' = z + angleShift k) →
      ∀ {A : Set (Phase (n * 2))}, NullMeasurableSet A → A ⊆ O →
      (∀ k : Fin (n * 2) → ℤ, (fun z => z + angleShift k) '' A = A) → 0 < volume A →
      NullMeasurableSet (Ψ '' A) ∧ (MeasurableSet A → MeasurableSet (Ψ '' A)) ∧
        volume (Ψ '' A) = ENNReal.ofReal (c ^ (n * 2)) * volume (A ∩ unitCell (n * 2)) ∧
        0 < volume (Ψ '' A) ∧
        (Ψ '' A ⊆ circularTube G m0 m a η → volume (Ψ '' A) < ⊤) := by
  refine ⟨mp_a_box hG hm0 hm ha hη, fun hc hO hΨ hQ1 hQ2 hA hAO hAper hApos => ?_⟩
  have h := mp_b_measure (G := G) (m0 := m0) (m := m) (a := a) (η := η) hG hm0 ha hc hO hΨ hQ1
    hQ2 hA hAO hAper hApos
  exact ⟨h.1, fun hB => mp_b_measurableSet hc hO hΨ hQ1 hQ2 hB hAO hAper, h.2⟩

end AssemblyNodes

end KAM.Planetary
