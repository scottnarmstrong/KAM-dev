/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.Interface
public import KAM.ODE.Uniqueness
public import KAM.ODE.Hamiltonian
public import KAM.Head.DerivativeBounds

/-!
# Quantitative weak KAM: the physical interface (P11C-Q7)

`physical_interface` (`bpP:p11a:physical-interface`): measure, displacement, global curves,
local uniqueness and lattice saturation of the family `QuantitativeFamily`.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology NNReal ENNReal
namespace KAM.Planetary
open KAM KAM.Kepler KAM.ODE

/-- Lebesgue measure on `Phase N` is the `2N`-dimensional Hausdorff measure. -/
private theorem volume_eq_hausdorff {N : ℕ} (B : Set (Phase N)) :
    volume B = μH[((2 * N : ℕ) : ℝ)] B := by
  let eI : (Fin N ⊕ Fin N → ℝ) ≃ᵢ Phase N := IsometryEquiv.sumArrowIsometryEquivProdArrow
  have hmp := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin N ⊕ Fin N => ℝ)
    (fun _ => volume)
  have h1 : volume (eI ⁻¹' B) = volume B := by
    have := hmp.measure_preimage_equiv B
    exact this
  have h2 : volume (eI ⁻¹' B) = μH[((2 * N : ℕ) : ℝ)] (eI ⁻¹' B) := by
    have := congrArg (fun m : Measure (Fin N ⊕ Fin N → ℝ) => m (eI ⁻¹' B))
      (hausdorffMeasure_pi_real (ι := Fin N ⊕ Fin N))
    simpa [two_mul] using this.symm
  have h3 : μH[((2 * N : ℕ) : ℝ)] (eI ⁻¹' B) = μH[((2 * N : ℕ) : ℝ)] B := by
    rw [← eI.image_symm, IsometryEquiv.hausdorffMeasure_image]
  rw [← h1, h2, h3]

/-- Lebesgue measure on `Phase N` of a Lipschitz image. -/
private theorem volume_image_lipschitzOn {N : ℕ} {K : ℝ≥0} {f : Phase N → Phase N}
    {A : Set (Phase N)} (hf : LipschitzOnWith K f A) :
    volume (f '' A) ≤ (K : ℝ≥0∞) ^ (2 * N) * volume A := by
  rw [volume_eq_hausdorff, volume_eq_hausdorff]
  have := hf.hausdorffMeasure_image_le (d := ((2 * N : ℕ) : ℝ)) (by positivity)
  rw [ENNReal.rpow_natCast] at this
  exact this

/-- Integer/fractional decomposition of an angle vector. -/
private theorem exists_fract_decomp {N : ℕ} (θ : Fin N → ℝ) :
    ∃ θ0 ∈ unitCube N, ∃ k : Fin N → ℤ, θ = θ0 + fun i => (k i : ℝ) :=
  ⟨fun i => Int.fract (θ i), fun i _ => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩,
    fun i => ⌊θ i⌋, by ext i; simp [Int.fract_add_floor]⟩

theorem physical_interface {N : ℕ} (d : QuantitativeData N) (hd : d.Valid)
    (H : Phase N → ℝ) (hH : ContDiffOn ℝ 2 H (p11c_realDomain d))
    (cDelta eps : ℝ) (Q : QuantitativeFamily d H cDelta eps) :
    let S := (fun z : Phase N => Q.torus z.2 z.1) '' (unitCube N ×ˢ Q.good)
    let St := ⋃ b ∈ Q.good, range (Q.torus b)
    MeasurableSet S ∧ 0 < volume S ∧ volume S < ⊤ ∧
    0 < ENNReal.ofReal ((2 : ℝ) ^ (-(2 * N : ℤ))) * (volume d.K - ENNReal.ofReal d.epsLoss) ∧
    ENNReal.ofReal ((2 : ℝ) ^ (-(2 * N : ℤ))) * (volume d.K - ENNReal.ofReal d.epsLoss) ≤
      volume S ∧
    volume S ≤ ENNReal.ofReal ((1 + (2 : ℝ) ^ (-10 : ℤ)) ^ (2 * N)) * volume Q.good ∧
    (∀ z ∈ S, ∃ b ∈ Q.good, ∃ θ ∈ unitCube N,
      z = Q.torus b θ ∧ ‖z - (θ, b)‖ ≤ p11c_displacement d cDelta eps) ∧
    (∀ b ∈ Q.good, ∀ θ, ∀ t : ℝ, Q.torus b (θ + t • Q.freq b) ∈ St) ∧
    (∀ b ∈ Q.good, ∀ θ, IsSolutionIn (hamiltonianVectorField H) (p11c_realDomain d) univ
      (fun t : ℝ => Q.torus b (θ + t • Q.freq b))) ∧
    (∀ b ∈ Q.good, ∀ θ, ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J →
      ∀ y : ℝ → Phase N, IsSolutionIn (hamiltonianVectorField H) (p11c_realDomain d) J y →
      y 0 = Q.torus b θ → ∀ t ∈ J, y t = Q.torus b (θ + t • Q.freq b)) ∧
    (∀ b ∈ Q.good, ∀ b' ∈ Q.good, ∀ θ θ', ∀ k : Fin N → ℤ,
      Q.torus b θ = Q.torus b' θ' + angleShift k → b = b') ∧
    (∃ R : Set (Phase N), IsCompact R ∧ R ⊆ St ∧
      ∀ z ∈ St, ∃ y ∈ R, ∃ k : Fin N → ℤ, z = y + angleShift k) ∧
    St = ⋃ k : Fin N → ℤ, (fun z => z + angleShift k) '' S := by
  intro S St
  have hlt : ENNReal.ofReal d.epsLoss < volume d.K := hd.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hfin : volume Q.good < ⊤ := Q.compact.measure_lt_top
  have hc0 : (0 : ℝ≥0∞) < ENNReal.ofReal ((2 : ℝ) ^ (-(2 * N : ℤ))) :=
    ENNReal.ofReal_pos.2 (zpow_pos (by norm_num) _)
  have hpos : 0 < ENNReal.ofReal ((2 : ℝ) ^ (-(2 * N : ℤ))) *
      (volume d.K - ENNReal.ofReal d.epsLoss) :=
    ENNReal.mul_pos hc0.ne' (tsub_pos_iff_lt.2 hlt).ne'
  have hge : ENNReal.ofReal ((2 : ℝ) ^ (-(2 * N : ℤ))) *
      (volume d.K - ENNReal.ofReal d.epsLoss) ≤ volume S :=
    calc _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(2 * N : ℤ))) * volume Q.good := by
          gcongr; exact tsub_le_iff_right.2 Q.measure
      _ ≤ volume S := Q.cell_lower
  have hup : volume S ≤ ENNReal.ofReal ((1 + (2 : ℝ) ^ (-10 : ℤ)) ^ (2 * N)) * volume Q.good := by
    have hnn : (0 : ℝ) ≤ 1 + (2 : ℝ) ^ (-10 : ℤ) := by positivity
    have hL : LipschitzOnWith (1 + (2 : ℝ) ^ (-10 : ℤ)).toNNReal
        (fun z : Phase N => Q.torus z.2 z.1) (unitCube N ×ˢ Q.good) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [Real.coe_toNNReal _ hnn, dist_eq_norm, dist_eq_norm]
      exact Q.upper x.2 hx.2 y.2 hy.2 x.1 y.1
    have := volume_image_lipschitzOn hL
    rw [Measure.volume_eq_prod, Measure.prod_prod] at this
    have hu : volume (unitCube N) = 1 := by
      simp [unitCube, Real.volume_pi_Ico]
    rw [hu, one_mul] at this
    refine this.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_pow hnn]
    rfl
  have hW : IsOpen (p11c_realDomain d) :=
    (KAM.Head.isOpen_actionNbhd _ _).preimage ((realInclusion N).continuous.comp continuous_snd)
  have hF := ham_smooth_c1 hW hH
  have hsol : ∀ b ∈ Q.good, ∀ θ, IsSolutionIn (hamiltonianVectorField H) (p11c_realDomain d) univ
      (fun t : ℝ => Q.torus b (θ + t • Q.freq b)) := fun b hb θ t _ =>
    ⟨((Q.lattice b hb).1.2 _).1, (Q.lattice b hb).2.2.2.2.2 θ t⟩
  have hdec : ∀ b ∈ Q.good, ∀ θ, ∃ θ0 ∈ unitCube N, ∃ k : Fin N → ℤ,
      Q.torus b θ = Q.torus b θ0 + angleShift k := by
    intro b hb θ
    obtain ⟨θ0, h0, k, hk⟩ := exists_fract_decomp θ
    exact ⟨θ0, h0, k, by rw [hk]; exact (Q.lattice b hb).2.1 θ0 k⟩
  have hSt : ∀ b ∈ Q.good, ∀ θ, Q.torus b θ ∈ St := fun b hb θ =>
    mem_iUnion₂.2 ⟨b, hb, mem_range_self θ⟩
  refine ⟨Q.borel, lt_of_lt_of_le hpos hge, ?_, hpos, hge, hup, ?_, ?_, hsol, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt hup (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  · rintro _ ⟨⟨θ, b⟩, ⟨hθ, hb⟩, rfl⟩
    exact ⟨b, hb, θ, hθ, rfl, Q.displacement b hb θ⟩
  · exact fun b hb θ t => hSt b hb _
  · intro b hb θ J hJ h0 y hy hy0 t ht
    refine gen_uniqueness hW hF hJ h0 hy ((hsol b hb θ).mono (subset_univ J)) ?_ ht
    simpa using hy0
  · intro b hb b' hb' θ θ' k h
    have h2 : Q.torus b' (θ' + fun i => (k i : ℝ)) = Q.torus b' θ' + angleShift k :=
      (Q.lattice b' hb').2.1 θ' k
    have h3 := Q.lower b hb b' hb' θ (θ' + fun i => (k i : ℝ))
    rw [h, ← h2, sub_self, norm_zero] at h3
    have hc : 0 < 1 - (2 : ℝ) ^ (-10 : ℤ) := by norm_num
    have h4 : ‖(θ, b) - (θ' + fun i => (k i : ℝ), b')‖ ≤ 0 := by
      by_contra hne
      exact absurd h3 (not_le.2 (mul_pos hc (not_le.1 hne)))
    have h5 := sub_eq_zero.1 (norm_le_zero_iff.1 h4)
    exact congrArg Prod.snd h5
  · refine ⟨(fun z : Phase N => Q.torus z.2 z.1) ''
      ((Set.pi univ fun _ => Icc (0 : ℝ) 1) ×ˢ Q.good), Q.compact_closed, ?_, ?_⟩
    · rintro _ ⟨⟨θ, b⟩, ⟨-, hb⟩, rfl⟩
      exact hSt b hb θ
    · intro z hz
      obtain ⟨b, hb, θ, rfl⟩ := mem_iUnion₂.1 hz
      obtain ⟨θ0, h0, k, hk⟩ := hdec b hb θ
      exact ⟨Q.torus b θ0, ⟨(θ0, b), ⟨fun i hi => Ico_subset_Icc_self (h0 i hi), hb⟩, rfl⟩,
        k, hk⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨b, hb, θ, rfl⟩ := mem_iUnion₂.1 hz
      obtain ⟨θ0, h0, k, hk⟩ := hdec b hb θ
      exact mem_iUnion.2 ⟨k, ⟨Q.torus b θ0, ⟨(θ0, b), ⟨h0, hb⟩, rfl⟩, hk.symm⟩⟩
    · intro hz
      obtain ⟨k, _, ⟨⟨θ0, b⟩, ⟨h0, hb⟩, rfl⟩, rfl⟩ := mem_iUnion.1 hz
      show Q.torus b θ0 + angleShift k ∈ St
      rw [← (Q.lattice b hb).2.1 θ0 k]
      exact hSt b hb _

end KAM.Planetary
