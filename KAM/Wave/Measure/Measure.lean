/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.Iter
public import Mathlib.Data.Finsupp.Encodable

/-!
# W7: the measure theorem (blueprint `bpW:w7:measurable`, `bpW:w7:measure`, `bpW:w7:melnikov`)

`exclSet_measurableSet`: the excluded set `ℰ` is Borel. `exclSet_measure_le`: for every admissible
family, `volume ℰ ≤ C₇ ρ α^{32/47}`, with `ρ = diam Π`. `melnikov_*`: Corollary
`bpW:w7:melnikov`.
-/

@[expose] public noncomputable section

open Real Finsupp MeasureTheory

namespace KAM.Wave

section

variable (m : ℝ) (hm : 0 < m)
variable {Pi : Set (Fin 2 → ℝ)} {α : ℝ}

theorem measurableSet_zoneSet {D : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ → ℝ} {εω ε1 ε2 θ : ℝ}
    (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) (a : ℝ) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) :
    MeasurableSet (zoneSet D ω Ω a k l) :=
  measurableSet_abs_lt_of_continuousOn hP.meas (hP.continuousOn_zoneFun m hm k l) _

theorem measurableSet_prepZone (hS : MeasSetup m hm Pi α) (a : ℝ) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) :
    MeasurableSet (prepZone m hm Pi a k l) := by
  have hP := isFreqPair_unpert m hm hS.meas hS.alpha_pos.le
  have : prepZone m hm Pi a k l = {ξ ∈ Pi | |∑ i, (k i : ℝ) * omegaTan m hm ξ i +
      linF l (omegaNor m hm ξ)| < a * hatW l / kAk k} := rfl
  rw [this]
  exact measurableSet_abs_lt_of_continuousOn hS.meas (hP.continuousOn_zoneFun m hm k l) _

/-- `Ξ`, `ℰ_it`, `ℰ` and `Π ∖ ℰ` are Borel (blueprint `bpW:w7:measurable`). -/
theorem exclSet_measurableSet (hS : MeasSetup m hm Pi α) (F : AdmissibleFamily m hm Pi α) :
    MeasurableSet (prepSet m hm Pi α) ∧ MeasurableSet (iterSet m hm F) ∧
      MeasurableSet (exclSet m hm F) ∧ MeasurableSet (Pi \ exclSet m hm F) := by
  have h1 : MeasurableSet (prepSet m hm Pi α) := by
    unfold prepSet
    exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun l =>
      MeasurableSet.iUnion fun _ => measurableSet_prepZone m hm hS _ k l
  have h2 : MeasurableSet (iterSet m hm F) := by
    unfold iterSet
    exact MeasurableSet.iUnion fun ν => MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun l =>
      MeasurableSet.iUnion fun _ => measurableSet_zoneSet m hm (F.pair ν) _ k l
  have h3 : MeasurableSet (exclSet m hm F) := h1.union h2
  exact ⟨h1, h2, h3, hS.meas.diff h3⟩

/-- **Measure of the resonance set** (blueprint `bpW:w7:measure`; P96-K Theorem D for the wave
equation): `volume ℰ ≤ C₇ ρ α^{32/47}`, `ρ = diam Π`. -/
theorem exclSet_measure_le (hS : MeasSetup m hm Pi α) (F : AdmissibleFamily m hm Pi α) :
    MeasurableSet (exclSet m hm F) ∧
      volume (exclSet m hm F) ≤ ENNReal.ofReal (measC7 m hm * Metric.diam Pi * α ^ (32 / 47 : ℝ))
          := by
  refine ⟨(exclSet_measurableSet m hm hS F).2.2.1, ?_⟩
  obtain ⟨hc, hcA, hαhat, h27, hβ4, -⟩ := alpha_facts m hm hS.alpha_pos hS.alpha_le
  have hα := hS.alpha_pos
  have hα1 : α ≤ 1 := by linarith
  have hDA := measDA_pos m hm
  have hNA := measNA_pos m hm
  have hbdd : Bornology.IsBounded Pi := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 1 / 2)).subset fun ξ hξ => ?_
    simpa using hS.sub ξ hξ
  have hdiam0 : 0 ≤ Metric.diam Pi := Metric.diam_nonneg
  set ρζ : ℝ := measNA m hm * Metric.diam Pi with hρζ
  have hρ0 : 0 ≤ ρζ := by positivity
  have hρ : ∀ ξ ∈ Pi, ∀ ξ' ∈ Pi, ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤ ρζ := fun ξ hξ ξ' hξ' => by
    refine (norm_omegaTan_sub_le m hm ξ ξ').trans ?_
    rw [hρζ]
    refine mul_le_mul_of_nonneg_left ?_ hNA.le
    rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem hbdd hξ hξ'
  have hP := prepSet_measure_le m hm hS hρ0 hρ
  have hI := iterSet_measure_le m hm hS F hρ0 hρ
  have e8 : alphaHat α ^ (8 / 11 : ℝ) = α ^ (32 / 47 : ℝ) := by
    unfold alphaHat; rw [← Real.rpow_mul hα.le]; norm_num
  have e2 : alphaCheck α ^ (2 / 3 : ℝ) = α ^ (32 / 47 : ℝ) := by
    unfold alphaCheck; rw [← Real.rpow_mul hα.le]; norm_num
  have hαp : α ≤ α ^ (32 / 47 : ℝ) := by
    calc α = α ^ (1 : ℝ) := (Real.rpow_one α).symm
      _ ≤ α ^ (32 / 47 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
  have hpos : 0 < α ^ (32 / 47 : ℝ) := Real.rpow_pos_of_pos hα _
  have hε : F.ε1 + F.ε2 ≤ 2 * α := by linarith [(F.pair 0).ε1_mem.2, (F.pair 0).ε2_mem.2]
  have hε0 : 0 ≤ F.ε1 + F.ε2 := by linarith [(F.pair 0).ε1_mem.1, (F.pair 0).ε2_mem.1]
  have hϑ := measTheta_pos m hm
  have hσ := measSigmaX_pos m hm
  have hK : 0 < measKstar m hm := by linarith [measKstar_pos m hm]
  have hκ := measAKappa_pos hm
  rw [e8] at hP
  rw [e2] at hI
  have hρDA : ρζ / measDA m hm = measLA m hm * Metric.diam Pi := by
    rw [hρζ, measLA_eq, div_mul_eq_mul_div]
  calc volume (exclSet m hm F) ≤ volume (prepSet m hm Pi α) + volume (iterSet m hm F) :=
        measure_union_le _ _
    _ ≤ _ := add_le_add hP hI
    _ ≤ ENNReal.ofReal (measC7 m hm * Metric.diam Pi * α ^ (32 / 47 : ℝ)) := by
        have hz3 : 0 < measZ3 := by unfold measZ3; positivity
        have hia := inv_pos.2 hϑ
        have hiσ := inv_pos.2 hσ
        have hcoef : 0 ≤ ρζ / measDA m hm := by positivity
        have hCP : 0 ≤ measCP m hm := by unfold measCP; positivity
        have hIt : 0 ≤ ρζ / measDA m hm * (measZ3 * (8 + 32 * (measTheta m hm)⁻¹ ^ 3 +
            16 * (2 + measAKappa m) * (measTheta m hm)⁻¹ ^ 2) * α ^ (32 / 47 : ℝ) +
          32 * measZ3 * (measTheta m hm)⁻¹ * (F.ε1 + F.ε2) +
          4 * (measNX m hm : ℝ) * measKstar m hm ^ 2 * (measTheta m hm)⁻¹ *
            (measSigmaX m hm)⁻¹ * alphaCheck α) := by
          have := Real.rpow_nonneg hα.le (32 / 47 : ℝ)
          positivity
        rw [← ENNReal.ofReal_add (by positivity) hIt]
        refine ENNReal.ofReal_le_ofReal ?_
        have hmain : ρζ / measDA m hm *
            (measZ3 * (8 + 32 * (measTheta m hm)⁻¹ ^ 3 + 16 * (2 + measAKappa m) *
              (measTheta m hm)⁻¹ ^ 2) * α ^ (32 / 47 : ℝ) +
            32 * measZ3 * (measTheta m hm)⁻¹ * (F.ε1 + F.ε2) +
            4 * (measNX m hm : ℝ) * measKstar m hm ^ 2 * (measTheta m hm)⁻¹ *
              (measSigmaX m hm)⁻¹ * alphaCheck α) ≤
            ρζ / measDA m hm * (measZ3 * (8 + 32 * (measTheta m hm)⁻¹ ^ 3 +
              16 * (2 + measAKappa m) * (measTheta m hm)⁻¹ ^ 2 + 64 * (measTheta m hm)⁻¹) +
              4 * (measNX m hm : ℝ) * measKstar m hm ^ 2 * (measTheta m hm)⁻¹ *
                (measSigmaX m hm)⁻¹) * α ^ (32 / 47 : ℝ) := by
          rw [mul_assoc (ρζ / measDA m hm) _ (α ^ (32 / 47 : ℝ))]
          refine mul_le_mul_of_nonneg_left ?_ hcoef
          have t1 : 32 * measZ3 * (measTheta m hm)⁻¹ * (F.ε1 + F.ε2) ≤
              64 * measZ3 * (measTheta m hm)⁻¹ * α ^ (32 / 47 : ℝ) := by
            have : 0 ≤ 32 * measZ3 * (measTheta m hm)⁻¹ := by positivity
            nlinarith
          have t2 : 4 * (measNX m hm : ℝ) * measKstar m hm ^ 2 * (measTheta m hm)⁻¹ *
              (measSigmaX m hm)⁻¹ * alphaCheck α ≤
              4 * (measNX m hm : ℝ) * measKstar m hm ^ 2 * (measTheta m hm)⁻¹ *
              (measSigmaX m hm)⁻¹ * α ^ (32 / 47 : ℝ) := by
            have : 0 ≤ 4 * (measNX m hm : ℝ) * measKstar m hm ^ 2 * (measTheta m hm)⁻¹ *
              (measSigmaX m hm)⁻¹ := by positivity
            exact mul_le_mul_of_nonneg_left (hcA.trans hαp) this
          nlinarith
        have hP' : measCP m hm * (ρζ / measDA m hm) * α ^ (32 / 47 : ℝ) +
            ρζ / measDA m hm * (measZ3 * (8 + 32 * (measTheta m hm)⁻¹ ^ 3 +
              16 * (2 + measAKappa m) * (measTheta m hm)⁻¹ ^ 2 + 64 * (measTheta m hm)⁻¹) +
              4 * (measNX m hm : ℝ) * measKstar m hm ^ 2 * (measTheta m hm)⁻¹ *
                (measSigmaX m hm)⁻¹) * α ^ (32 / 47 : ℝ) =
            measC7 m hm * Metric.diam Pi * α ^ (32 / 47 : ℝ) := by
          rw [measC7, measLA_eq, measCP, measCI]
          simp only [hρζ]
          field_simp
        linarith

/-- **Melnikov conditions on the complement** (blueprint `bpW:w7:melnikov`) (i): off `Ξ`. -/
theorem melnikov_prep {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Pi) (hnot : ξ ∉ prepSet m hm Pi α)
    {k : Fin 2 → ℤ} {l : ℕ →₀ ℤ} (hz : InZ k l) :
    alphaHat α * hatW l / kAk k ≤
      |∑ i, (k i : ℝ) * omegaTan m hm ξ i + linF l (omegaNor m hm ξ)| := by
  by_contra h
  push Not at h
  exact hnot (by
    simp only [prepSet, Set.mem_iUnion]
    exact ⟨k, l, hz, hξ, h⟩)

/-- (i), `l = 0`: `|⟨k, ω⁰⟩| ≥ α̂ / A_k` for `k ≠ 0`. -/
theorem melnikov_prep_zero {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Pi) (hnot : ξ ∉ prepSet m hm Pi α)
    {k : Fin 2 → ℤ} (hk : k ≠ 0) :
    alphaHat α / kAk k ≤ |∑ i, (k i : ℝ) * omegaTan m hm ξ i| := by
  have h := melnikov_prep m hm hξ hnot (k := k) (l := 0) ⟨Or.inl rfl, Or.inl hk⟩
  have h1 : hatW (0 : ℕ →₀ ℤ) = 1 := by
    unfold hatW
    have : ¬ IsLamMinus (0 : ℕ →₀ ℤ) := by
      rintro ⟨i, j, σ, hji, hσ, h0⟩
      have := congrArg (fun f => f i) h0
      simp [hji.ne'] at this
      rcases hσ with rfl | rfl <;> simp at this
    simp only [this, ↓reduceIte, japL_zero]
  have h2 : linF (0 : ℕ →₀ ℤ) (omegaNor m hm ξ) = 0 := by unfold linF; simp
  rw [h1, h2] at h
  simpa using h

/-- (ii): off the iteration zones `R^ν_{kl}`. -/
theorem melnikov_iter (F : AdmissibleFamily m hm Pi α) {ν : ℕ} {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ F.D ν) {k : Fin 2 → ℤ} {l : ℕ →₀ ℤ}
    (hnot : ξ ∉ zoneSet (F.D ν) (F.ω ν) (F.Ω ν) (alphaCheck α) k l) :
    alphaCheck α * japL l / kAk k ≤
      |∑ i, (k i : ℝ) * F.ω ν ξ i + linF l (F.Ω ν ξ)| := by
  by_contra h
  push Not at h
  exact hnot ⟨hξ, h⟩

/-- (iii): the `k = 0` conditions, `|⟨l, Ω'⟩| ≥ 2 β_* ⟨l⟩ ≥ α̂ ⟨l⟩`. -/
theorem melnikov_sep (hS : MeasSetup m hm Pi α) {D : Set (Fin 2 → ℝ)}
    {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ → ℝ} {εω ε1 ε2 θ : ℝ}
    (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ D) {l : ℕ →₀ ℤ}
    (hl : IsLam l) :
    2 * measBetaStar m * japL l ≤ |linF l (Ω ξ)| ∧
      alphaHat α * japL l ≤ 2 * measBetaStar m * japL l := by
  refine ⟨hP.normal_sep m hm hS hξ hl, ?_⟩
  obtain ⟨-, -, -, -, hβ4, -⟩ := alpha_facts m hm hS.alpha_pos hS.alpha_le
  have := measBetaStar_pos hm
  have hj := japL_ge_one l
  nlinarith

end

end KAM.Wave

end
