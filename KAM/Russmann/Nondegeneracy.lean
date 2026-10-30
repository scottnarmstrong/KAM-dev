/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakMeasure.FiniteType
public import KAM.Planetary.Quantitative.Zero
public import KAM.Russmann.Frequency

/-!
# Track R: Rüssmann's non-degeneracy lemma

Rus01 Lemma 18.2 and §18.3.1 (pp. 185–186), maximal case, in exactly the form of the finite-type
clause of `KAM.Planetary.QuantitativeInput` with `ρ = 1` (`p11c_scalar 1`, Euclidean unit vectors
`KAM.Nekhoroshev.euclid`):

* `russmann_finite_order`: if `ω` is real-analytic on a connected open `V ⊆ ℝⁿ` and `c · ω ≢ 0` on
  `V` for every Euclidean-unit `c`, then for every compact `K ⊆ V` there are an order `μ ≥ 1` and
  an amount `β > 0` such that every unit `c` and every `y ∈ K` have some `j ≤ μ` and some unit `v`
  with `β ≤ |D^j(c · ω)(y)(v, …, v)|`. The analytic content is the existing track-P theorem
  `KAM.Planetary.rank_compact` (Part 10's `cp09_unsquared`: identity theorem, polarization and
  compactness); here it is unfolded through the jet maxima `p11maxJet`, `p11dg`.
* `russmann_finite_order_frequencyMap`: the case of R-HEAD's hypotheses, `ω = frequencyMap h` on
  the compact set `closure B`, inside the connected real neighbourhood `realNbhd B r₀`.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology

namespace KAM.Russmann

open KAM KAM.Planetary

variable {n : ℕ}

theorem euclid_smul (a : ℝ) (c : Fin n → ℝ) :
    KAM.Nekhoroshev.euclid (a • c) = |a| * KAM.Nekhoroshev.euclid c := by
  unfold KAM.Nekhoroshev.euclid
  have : ∑ i, ‖(a • c) i‖ ^ 2 = a ^ 2 * ∑ i, ‖c i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Real.norm_eq_abs, mul_pow, sq_abs]
  rw [this, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

theorem euclid_pos {c : Fin n → ℝ} (hc : c ≠ 0) : 0 < KAM.Nekhoroshev.euclid c :=
  lt_of_lt_of_le (norm_pos_iff.2 hc) (KAM.Nekhoroshev.norm_le_euclid c).1

theorem p11scalar_one_eq (ω : (Fin n → ℝ) → Fin n → ℝ) (c : Fin n → ℝ) :
    p11scalar 1 ω c = fun x (_ : Fin 1) => p11c_scalar 1 ω c x := by
  funext x i
  simp [p11scalar, p11c_scalar, p11dot]

/-- **Rüssmann's non-degeneracy lemma** (Rus01 Lemma 18.2, §18.3.1, pp. 185–186; maximal case,
`ρ = 1`). If `ω` is real-analytic on a connected open set `V` and `c · ω` is not identically zero
on `V` for any Euclidean-unit `c`, then on every compact `K ⊆ V` the scalar family `c · ω` has a
finite order `μ ≥ 1` and a positive amount `β`: every unit `c` and every `y ∈ K` have some `j ≤ μ`
and some unit `v` with `β ≤ |D^j(c · ω)(y)(v, …, v)|`. -/
theorem russmann_finite_order {V K : Set (Fin n → ℝ)} (hV : IsOpen V) (hVc : IsPreconnected V)
    (hK : IsCompact K) (hKV : K ⊆ V) {ω : (Fin n → ℝ) → Fin n → ℝ}
    (hω : AnalyticOnNhd ℝ ω V)
    (hR : ∀ c : Fin n → ℝ, KAM.Nekhoroshev.euclid c = 1 → ∃ y ∈ V, ∑ i, c i * ω y i ≠ 0) :
    ∃ μ : ℕ, 1 ≤ μ ∧ ∃ β : ℝ, 0 < β ∧
      ∀ c : Fin n → ℝ, KAM.Nekhoroshev.euclid c = 1 → ∀ y ∈ K,
        ∃ j ≤ μ, ∃ v : Fin n → ℝ, KAM.Nekhoroshev.euclid v = 1 ∧
          β ≤ |iteratedFDeriv ℝ j (p11c_scalar 1 ω c) y (fun _ => v)| := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, le_rfl, 1, one_pos, fun c hc => ?_⟩
    simp [KAM.Nekhoroshev.euclid] at hc
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, le_rfl, 1, one_pos, fun _ _ y hy => absurd hy (notMem_empty y)⟩
  -- R-nondegeneracy in the form of track P (nonzero `c`), by normalising `c`
  have hRnd : p11RNondegenerate V ω := by
    intro c hc
    have he0 := euclid_pos hc
    obtain ⟨y, hy, hne⟩ := hR ((KAM.Nekhoroshev.euclid c)⁻¹ • c) (by
      rw [euclid_smul, abs_inv, abs_of_pos he0, inv_mul_cancel₀ he0.ne'])
    refine ⟨y, hy, fun h0 => hne ?_⟩
    have : ∑ i, ((KAM.Nekhoroshev.euclid c)⁻¹ • c) i * ω y i =
        (KAM.Nekhoroshev.euclid c)⁻¹ * p11dot c (ω y) := by
      simp [p11dot, Finset.mul_sum, mul_assoc]
    rw [this, h0, mul_zero]
  obtain ⟨μ, hμ, hβ⟩ := rank_compact hn hn hV hVc hK hKne hKV hω hRnd (Or.inl rfl)
  refine ⟨μ, hμ, index_def 1 μ ω K, hβ, fun c hc y hy => ?_⟩
  have h1 : index_def 1 μ ω K ≤ p11maxJet μ (p11scalar 1 ω c) y := index_def_le 1 μ ω hc hy
  obtain ⟨j, hj, hjeq⟩ := p11maxJet_attained (p11scalar 1 ω c) y μ
  obtain ⟨a, ha, haeq⟩ := p11dg_attained (p11scalar 1 ω c) j y hn
  have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (p11c_scalar 1 ω c) y := by
    have hs : AnalyticAt ℝ (fun x => ∑ i, c i * ω x i) y :=
      Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul
        ((analyticAt_pi_iff.1 (hω y (hKV hy))) i)
    have e : p11c_scalar 1 ω c = fun x => ∑ i, c i * ω x i := by
      funext x; simp [p11c_scalar]
    rw [e]
    exact hs.contDiffAt
  refine ⟨j, hj, a, ha, ?_⟩
  have e := p11c_zero_euclid_iter hcd j (fun _ => a)
  rw [← p11scalar_one_eq] at e
  rw [← e, ← haeq, ← hjeq]
  exact h1

/-- **Rüssmann's non-degeneracy lemma for R-HEAD's data.** If `h` is holomorphic on
`actionNbhd B r₀` (`r₀ > 0`), `B` is connected and bounded, and `c · ∇h ≢ 0` on `B` for every
`c ≠ 0`, then there are `μ ≥ 1` and `β > 0` such that every Euclidean-unit `c` and every
`y ∈ closure B` have some `j ≤ μ` and unit `v` with `β ≤ |D^j(c · ∇h)(y)(v, …, v)|`. -/
theorem russmann_finite_order_frequencyMap {B : Set (Fin n → ℝ)} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hB_conn : IsConnected B) (hB_bdd : Bornology.IsBounded B) {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (actionNbhd B r₀))
    (h_russmann : ∀ c : Fin n → ℝ, c ≠ 0 → ∃ I ∈ B, ∑ i, c i * frequencyMap h I i ≠ 0) :
    ∃ μ : ℕ, 1 ≤ μ ∧ ∃ β : ℝ, 0 < β ∧
      ∀ c : Fin n → ℝ, KAM.Nekhoroshev.euclid c = 1 → ∀ y ∈ closure B,
        ∃ j ≤ μ, ∃ v : Fin n → ℝ, KAM.Nekhoroshev.euclid v = 1 ∧
          β ≤ |iteratedFDeriv ℝ j (p11c_scalar 1 (frequencyMap h) c) y (fun _ => v)| := by
  refine russmann_finite_order (isOpen_realNbhd B r₀) (isConnected_realNbhd hB_conn hr₀).2
    hB_bdd.isCompact_closure (closure_subset_realNbhd hr₀) (analyticOnNhd_frequencyMap hh)
    fun c hc => ?_
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp [KAM.Nekhoroshev.euclid] at hc
  obtain ⟨I, hI, hne⟩ := h_russmann c hc0
  exact ⟨I, subset_realNbhd hr₀ hI, hne⟩

end KAM.Russmann

end
