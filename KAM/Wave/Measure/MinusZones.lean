/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.ZoneSums

/-!
# W7: exceptional zones and the `Λ⁻` zones at fixed `(k, n)` (blueprint `bpW:w7:prep`, `iter`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

`genZone` is the zone `{ξ ∈ D : |⟨k, ω'⟩ + ⟨l, Ω'⟩| < η}` with an arbitrary threshold `η`.
`X_bound` bounds the union of the exceptional zones; `minus_n_bound` bounds, for fixed `k` and
`n = i - j`, the union over `j` of the zones of `l = e_{j+n} - e_j`: the first `J₀ - 3` of them by
the zone estimate, the rest by a single zone with `ψ ≡ n`.
-/

@[expose] public noncomputable section

open Real Finsupp MeasureTheory

namespace KAM.Wave

/-- The zone with an arbitrary threshold `η`. -/
def genZone (D : Set (Fin 2 → ℝ)) (ω : (Fin 2 → ℝ) → Fin 2 → ℝ) (Ω : (Fin 2 → ℝ) → ℕ → ℝ)
    (η : ℝ) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) : Set (Fin 2 → ℝ) :=
  {ξ ∈ D | |∑ i, (k i : ℝ) * ω ξ i + linF l (Ω ξ)| < η}

theorem zoneSet_eq_genZone (D : Set (Fin 2 → ℝ)) (ω : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (Ω : (Fin 2 → ℝ) → ℕ → ℝ) (a : ℝ) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) :
    zoneSet D ω Ω a k l = genZone D ω Ω (a * japL l / kAk k) k l := rfl

theorem genZone_mono (D : Set (Fin 2 → ℝ)) (ω : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (Ω : (Fin 2 → ℝ) → ℕ → ℝ) {η η' : ℝ} (h : η ≤ η') (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) :
    genZone D ω Ω η k l ⊆ genZone D ω Ω η' k l := fun _ ⟨hξ, hz⟩ => ⟨hξ, hz.trans_le h⟩

section

variable (m : ℝ) (hm : 0 < m)
variable {Pi : Set (Fin 2 → ℝ)} {α : ℝ} {D : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ → ℝ} {εω ε1 ε2 θ : ℝ}

/-- Zone estimate for an arbitrary threshold. -/
theorem IsFreqPair.zone_bound_gen (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ)
    {k : Fin 2 → ℤ} (hk : k ≠ 0) {l : ℕ →₀ ℤ}
    (h8 : 8 * measCLam m hm * absWt l (-(1 / 2 : ℝ)) ≤ kAbs k) {η : ℝ} (hη : 0 < η) {ρζ : ℝ}
    (hρζ : ∀ ξ ∈ D, ∀ ξ' ∈ D, ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤ ρζ) :
    MeasurableSet (genZone D ω Ω η k l) ∧ volume (genZone D ω Ω η k l) ≤
      ENNReal.ofReal (8 * η * ρζ / (kAbs k * measDA m hm)) :=
  hP.zone_measure_le m hm hk (fun ξ => linF l (Ω ξ)) (fun ξ hξ ξ' hξ' => by
    refine (hP.linF_lip m hm hξ hξ' l).trans ?_
    have hn := norm_nonneg (omegaTan m hm ξ - omegaTan m hm ξ')
    nlinarith) hρζ hη

/-- Zone estimate for a constant `ψ ≡ c`. -/
theorem IsFreqPair.zone_bound_const (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ)
    {k : Fin 2 → ℤ} (hk : k ≠ 0) (c : ℝ) {η : ℝ} (hη : 0 < η) {ρζ : ℝ}
    (hρζ : ∀ ξ ∈ D, ∀ ξ' ∈ D, ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤ ρζ) :
    volume {ξ ∈ D | |∑ i, (k i : ℝ) * ω ξ i + c| < η} ≤
      ENNReal.ofReal (8 * η * ρζ / (kAbs k * measDA m hm)) :=
  (hP.zone_measure_le m hm hk (fun _ => c) (fun ξ _ ξ' _ => by
    simp only [sub_self, abs_zero]
    have := kAbs_nonneg k
    positivity) hρζ hη).2

/-- Union of the exceptional zones. -/
theorem IsFreqPair.X_bound (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {a : ℝ} (ha0 : 0 < a)
    (ha : a ≤ alphaHat α) (hS : MeasSetup m hm Pi α) {ρζ : ℝ} (hρ0 : 0 ≤ ρζ)
    (hρζ : ∀ ξ ∈ D, ∀ ξ' ∈ D, ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤ ρζ) :
    volume (⋃ (kl : (Fin 2 → ℤ) × (ℕ →₀ ℤ)) (_ : kl ∈ measXSet m hm),
        zoneSet D ω Ω a kl.1 kl.2) ≤
      ENNReal.ofReal ((measNX m hm : ℝ) *
        (4 * ρζ * a * measKstar m hm / (measTheta m hm * measSigmaX m hm * measDA m hm))) := by
  classical
  set c : ℝ := 4 * ρζ * a * measKstar m hm / (measTheta m hm * measSigmaX m hm * measDA m hm)
    with hc
  have hfin := measXSet_finite m hm
  have hbiU : (⋃ (kl : (Fin 2 → ℤ) × (ℕ →₀ ℤ)) (_ : kl ∈ measXSet m hm),
      zoneSet D ω Ω a kl.1 kl.2) = ⋃ kl ∈ hfin.toFinset, zoneSet D ω Ω a kl.1 kl.2 := by
    ext x; simp
  rw [hbiU]
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hterm : ∀ kl ∈ hfin.toFinset, volume (zoneSet D ω Ω a kl.1 kl.2) ≤ ENNReal.ofReal c := by
    intro kl hkl
    have hx : kl ∈ measXSet m hm := hfin.mem_toFinset.1 hkl
    obtain ⟨k, l⟩ := kl
    by_cases hp : measPX m hm k l = 0
    · rw [hP.Xzone_empty m hm hS ha0.le ha hx hp]; simp
    · exact (hP.Xzone_measure_le m hm ha0 hx hp hρ0 hρζ).2
  calc ∑ kl ∈ hfin.toFinset, volume (zoneSet D ω Ω a kl.1 kl.2)
      ≤ ∑ kl ∈ hfin.toFinset, ENNReal.ofReal c := Finset.sum_le_sum hterm
    _ = (measNX m hm : ENNReal) * ENNReal.ofReal c := by
        rw [Finset.sum_const, nsmul_eq_mul, measNX, Set.ncard_eq_toFinset_card _ hfin]
    _ = ENNReal.ofReal ((measNX m hm : ℝ) * c) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- The union over `j` of the zones of `l = e_{j+n} - e_j` (blueprint `bpW:w7:prep`, step
"`Λ⁻`, choice of `j₀`"; `bpW:w7:iter`). -/
theorem IsFreqPair.minus_n_bound (hS : MeasSetup m hm Pi α)
    (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {a : ℝ} (ha0 : 0 < a)
    (ha : a ≤ alphaHat α) {k : Fin 2 → ℤ} (hk : k ≠ 0) {n : ℕ} (hn : 1 ≤ n) (J0 : ℕ)
    (η : ℕ → ℝ) (hη_pos : ∀ j, 0 < η j) (hη_le : ∀ j, η j ≤ a * n / kAk k) {θQ : ℝ}
    (hθQ : 0 < θQ) {ρζ : ℝ} (hρ0 : 0 ≤ ρζ)
    (hρζ : ∀ ξ ∈ D, ∀ ξ' ∈ D, ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤ ρζ)
    (hQ : ∀ j, J0 ≤ j → genZone D ω Ω (η j) k (single (j + n) 1 + single j (-1)) ⊆
      {ξ ∈ D | |∑ i, (k i : ℝ) * ω ξ i + (n : ℝ)| < θQ}) :
    volume (⋃ (j : ℕ) (_ : (k, single (j + n) 1 + single j (-1)) ∉ measXSet m hm),
        genZone D ω Ω (η j) k (single (j + n) 1 + single j (-1))) ≤
      ENNReal.ofReal (∑ j ∈ Finset.range J0, 8 * η j * ρζ / (kAbs k * measDA m hm)
        + 8 * θQ * ρζ / (kAbs k * measDA m hm)) := by
  obtain ⟨-, -, -, -, hαβ, -⟩ := alpha_facts m hm hS.alpha_pos hS.alpha_le
  have haβ : a ≤ measBetaStar m := by
    have := measBetaStar_pos hm; linarith
  have hDA := measDA_pos m hm
  have hk1 := one_le_kAbs hk
  set lj : ℕ → (ℕ →₀ ℤ) := fun j => single (j + n) 1 + single j (-1) with hlj
  have hminus : ∀ j, IsLamMinus (lj j) := fun j =>
    ⟨j + n, j, 1, by omega, Or.inl rfl, by simp [hlj]⟩
  have hjapL : ∀ j, japL (lj j) = n := fun j => by
    have := japL_minus (i := j + n) (j := j) (σ := 1) (by omega) (Or.inl rfl)
    simp only [hlj]
    rw [show (-1 : ℤ) = -(1 : ℤ) by norm_num, this]; push_cast; ring
  set Q : Set (Fin 2 → ℝ) := {ξ ∈ D | |∑ i, (k i : ℝ) * ω ξ i + (n : ℝ)| < θQ} with hQdef
  have hsub : (⋃ (j : ℕ) (_ : (k, lj j) ∉ measXSet m hm), genZone D ω Ω (η j) k (lj j)) ⊆
      (⋃ j ∈ Finset.range J0, ⋃ (_ : (k, lj j) ∉ measXSet m hm), genZone D ω Ω (η j) k (lj j)) ∪ Q
          := by
    intro ξ hξ
    simp only [Set.mem_iUnion] at hξ
    obtain ⟨j, hX, hz⟩ := hξ
    by_cases hj : j < J0
    · left
      simp only [Set.mem_iUnion]
      exact ⟨j, Finset.mem_range.2 hj, hX, hz⟩
    · right
      exact hQ j (not_lt.1 hj) hz
  have hterm : ∀ j ∈ Finset.range J0, volume (⋃ (_ : (k, lj j) ∉ measXSet m hm),
      genZone D ω Ω (η j) k (lj j)) ≤
        ENNReal.ofReal (8 * η j * ρζ / (kAbs k * measDA m hm)) := by
    intro j _
    by_cases hX : (k, lj j) ∉ measXSet m hm
    · have e : (⋃ (_ : (k, lj j) ∉ measXSet m hm), genZone D ω Ω (η j) k (lj j)) =
          genZone D ω Ω (η j) k (lj j) := by
        ext x; simp only [Set.mem_iUnion]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hX, h⟩⟩
      rw [e]
      by_cases hne : (genZone D ω Ω (η j) k (lj j)).Nonempty
      · have hne' : (zoneSet D ω Ω a k (lj j)).Nonempty := by
          obtain ⟨x, hx⟩ := hne
          refine ⟨x, genZone_mono D ω Ω ?_ k (lj j) hx⟩
          rw [hjapL]; exact hη_le j
        have hd := hP.dichotomy m hm hS ha0.le haβ (IsLam_of_minus (hminus j)) hX hne'
        exact (hP.zone_bound_gen m hm hk hd.2.2 (hη_pos j) hρζ).2
      · rw [Set.not_nonempty_iff_eq_empty.1 hne]; simp
    · have e : (⋃ (_ : (k, lj j) ∉ measXSet m hm), genZone D ω Ω (η j) k (lj j)) = ∅ := by
        ext x; simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
        exact fun ⟨h, _⟩ => hX h
      rw [e]; simp
  have hQvol := hP.zone_bound_const m hm hk (n : ℝ) hθQ hρζ
  calc volume (⋃ (j : ℕ) (_ : (k, lj j) ∉ measXSet m hm), genZone D ω Ω (η j) k (lj j))
      ≤ volume ((⋃ j ∈ Finset.range J0, ⋃ (_ : (k, lj j) ∉ measXSet m hm),
          genZone D ω Ω (η j) k (lj j)) ∪ Q) := measure_mono hsub
    _ ≤ volume (⋃ j ∈ Finset.range J0, ⋃ (_ : (k, lj j) ∉ measXSet m hm),
          genZone D ω Ω (η j) k (lj j)) + volume Q := measure_union_le _ _
    _ ≤ ∑ j ∈ Finset.range J0, volume (⋃ (_ : (k, lj j) ∉ measXSet m hm),
          genZone D ω Ω (η j) k (lj j)) + volume Q :=
        add_le_add (measure_biUnion_finset_le _ _) le_rfl
    _ ≤ ∑ j ∈ Finset.range J0, ENNReal.ofReal (8 * η j * ρζ / (kAbs k * measDA m hm)) +
          ENNReal.ofReal (8 * θQ * ρζ / (kAbs k * measDA m hm)) :=
        add_le_add (Finset.sum_le_sum hterm) hQvol
    _ = ENNReal.ofReal (∑ j ∈ Finset.range J0, 8 * η j * ρζ / (kAbs k * measDA m hm)
          + 8 * θQ * ρζ / (kAbs k * measDA m hm)) := by
        rw [ENNReal.ofReal_add (Finset.sum_nonneg fun j _ => by
            have := hη_pos j; positivity) (by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun j _ => by have := hη_pos j; positivity)]

end

end KAM.Wave

end
