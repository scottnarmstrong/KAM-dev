/-
Copyright (c) 2026 Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zohar Komargodski
-/
module

public import KAM.Strip.FourierSeries
public import KAM.Strip.Periodic
public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Tactic.Linarith

/-!
# Fourier coefficients determine periodic functions

A continuous `1`-periodic function on `ℝⁿ` descends to a continuous function on the torus
`𝕋ⁿ = UnitAddTorus (Fin n)`, whose Fourier coefficients are our `torusCoeff`. If they are absolutely
summable, the Fourier series converges to the function everywhere (blueprint `bp:p1:fourier-basic`
(b), from Mathlib's `UnitAddTorus.hasSum_mFourier_series_apply_of_summable`). With the identity
theorem on strips (`KAM.strip_identity`, `bp:p1:strip-identity`), a periodic holomorphic map with
vanishing coefficients vanishes (`bp:p1:fourier-basic` (c)). Hence a bounded periodic holomorphic
map equals its Fourier series (`bp:p1:summation`, last part).
-/

public noncomputable section

open Set MeasureTheory Topology

namespace KAM

variable {n : ℕ}

/-! ### Integer periods -/

/-- Unit periods in every coordinate give all integer periods. -/
theorem periodic_intVec {F : Type*} {v : (Fin n → ℝ) → F}
    (hp : ∀ (i : Fin n) x, v (x + Pi.single i 1) = v x) (m : Fin n → ℤ) (x : Fin n → ℝ) :
    v (x + fun i => (m i : ℝ)) = v x := by
  have hdir : ∀ (i : Fin n) (k : ℤ) (y : Fin n → ℝ), v (y + (k : ℝ) • Pi.single i 1) = v y := by
    intro i k y
    have hper : Function.Periodic (fun t : ℝ => v (y + t • Pi.single i 1)) 1 := by
      intro t
      simp only [add_smul, one_smul, ← add_assoc]
      exact hp i _
    simpa using hper.int_mul k 0
  have key : ∀ s : Finset (Fin n), ∀ x : Fin n → ℝ,
      v (x + ∑ i ∈ s, (m i : ℝ) • Pi.single i (1 : ℝ)) = v x := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro x
      simp
    · intro j s hj ih x
      rw [Finset.sum_insert hj,
        show x + ((m j : ℝ) • Pi.single j (1 : ℝ) + ∑ i ∈ s, (m i : ℝ) • Pi.single i (1 : ℝ)) =
          (x + ∑ i ∈ s, (m i : ℝ) • Pi.single i (1 : ℝ)) + (m j : ℝ) • Pi.single j 1 by abel,
        hdir, ih]
  have hsum : (fun i => (m i : ℝ)) = ∑ i, (m i : ℝ) • Pi.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hsum]
  exact key Finset.univ x

/-! ### The torus -/

/-- The projection `ℝⁿ → 𝕋ⁿ`. -/
@[expose] def torusProj (x : Fin n → ℝ) : UnitAddTorus (Fin n) := fun i => (x i : UnitAddCircle)

theorem continuous_torusProj : Continuous (torusProj (n := n)) :=
  continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)

theorem surjective_torusProj : Function.Surjective (torusProj (n := n)) := by
  intro y
  choose x hx using fun i => QuotientAddGroup.mk_surjective (y i)
  exact ⟨x, funext hx⟩

theorem isOpenMap_torusProj : IsOpenMap (torusProj (n := n)) := by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hxU, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hxU
  refine ⟨Set.pi univ fun i => (fun t : ℝ => (t : UnitAddCircle)) '' Metric.ball (x i) r,
    ?_, ?_, ?_⟩
  · intro z hz
    have hz' : ∀ i, ∃ t ∈ Metric.ball (x i) r, (t : UnitAddCircle) = z i :=
      fun i => hz i (mem_univ i)
    choose t ht hzt using hz'
    refine ⟨t, hball ?_, funext hzt⟩
    rw [ball_pi x hr]
    exact fun i _ => ht i
  · exact isOpen_set_pi finite_univ fun i _ =>
      QuotientAddGroup.isOpenMap_coe _ Metric.isOpen_ball
  · exact fun i _ => ⟨x i, Metric.mem_ball_self hr, rfl⟩

theorem isQuotientMap_torusProj : IsQuotientMap (torusProj (n := n)) :=
  isOpenMap_torusProj.isQuotientMap continuous_torusProj surjective_torusProj

theorem exists_eq_add_intVec_of_torusProj_eq {x y : Fin n → ℝ} (h : torusProj x = torusProj y) :
    ∃ m : Fin n → ℤ, y = x + fun i => (m i : ℝ) := by
  have hi : ∀ i, ∃ k : ℤ, (k : ℝ) = -x i + y i := by
    intro i
    have := QuotientAddGroup.eq.mp (congrFun h i)
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp this
    exact ⟨k, by simpa using hk⟩
  choose m hm using hi
  refine ⟨m, funext fun i => ?_⟩
  simp only [Pi.add_apply, hm i]
  ring

/-- A periodic function on `ℝⁿ`, read on the torus. -/
@[expose] def torusLift (v : (Fin n → ℝ) → ℂ) (y : UnitAddTorus (Fin n)) : ℂ :=
  v (Classical.choose (surjective_torusProj y))

theorem torusLift_torusProj {v : (Fin n → ℝ) → ℂ}
    (hp : ∀ (i : Fin n) x, v (x + Pi.single i 1) = v x) (x : Fin n → ℝ) :
    torusLift v (torusProj x) = v x := by
  have hs := Classical.choose_spec (surjective_torusProj (torusProj x))
  obtain ⟨m, hm⟩ := exists_eq_add_intVec_of_torusProj_eq hs.symm
  rw [torusLift, hm]
  exact periodic_intVec hp m x

theorem continuous_torusLift {v : (Fin n → ℝ) → ℂ} (hv : Continuous v)
    (hp : ∀ (i : Fin n) x, v (x + Pi.single i 1) = v x) : Continuous (torusLift v) := by
  rw [isQuotientMap_torusProj.continuous_iff]
  have h : torusLift v ∘ torusProj = v := funext (torusLift_torusProj hp)
  rw [h]
  exact hv

theorem mFourier_torusProj (k : Fin n → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier k (torusProj x) = character k (fun j => (x j : ℂ)) := by
  have h : ∀ j, fourier (k j) ((x j : ℝ) : UnitAddCircle) =
      Complex.exp (2 * Real.pi * Complex.I * (k j : ℂ) * (x j : ℂ)) := by
    intro j
    rw [fourier_coe_apply]
    simp
  show ∏ j, fourier (k j) ((x j : ℝ) : UnitAddCircle) = _
  simp only [h, ← Complex.exp_sum, character]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Mathlib's torus coefficients of the lift are our `torusCoeff`. -/
theorem mFourierCoeff_torusLift {v : (Fin n → ℝ) → ℂ}
    (hp : ∀ (i : Fin n) x, v (x + Pi.single i 1) = v x) (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (torusLift v) k = torusCoeff v k := by
  rw [UnitAddTorus.mFourierCoeff, UnitAddTorus.integral_preimage _ 0, torusCoeff, torusAverage]
  have hset : {x : Fin n → ℝ | ∀ i, x i ∈ Ioc ((0 : Fin n → ℝ) i) ((0 : Fin n → ℝ) i + 1)} =
      Set.pi univ fun _ : Fin n => Ioc (0 : ℝ) 1 := by
    ext x
    simp [Set.mem_pi]
  have hae : (Set.pi univ fun _ : Fin n => Ioc (0 : ℝ) 1) =ᵐ[volume]
      Set.pi univ fun _ : Fin n => Icc (0 : ℝ) 1 := by
    rw [pi_univ_Icc]
    exact Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ => volume)
  rw [hset, setIntegral_congr_set hae]
  refine setIntegral_congr_fun ?_ fun x _ => ?_
  · exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  · show UnitAddTorus.mFourier (-k) (torusProj x) • torusLift v (torusProj x) = _
    rw [mFourier_torusProj, torusLift_torusProj hp, smul_eq_mul]

/-- **Fourier series of continuous periodic functions** (blueprint `bp:p1:fourier-basic` (b)):
if `∑ |v̂_k| < ∞`, then `v(x) = ∑ v̂_k χ_k(x)` for every `x ∈ ℝⁿ`. -/
theorem hasSum_torusCoeff_mul_character {v : (Fin n → ℝ) → ℂ} (hv : Continuous v)
    (hp : ∀ (i : Fin n) x, v (x + Pi.single i 1) = v x)
    (hs : Summable fun k => ‖torusCoeff v k‖) (x : Fin n → ℝ) :
    HasSum (fun k => torusCoeff v k * character k (fun j => (x j : ℂ))) (v x) := by
  let F : C(UnitAddTorus (Fin n), ℂ) := ⟨torusLift v, continuous_torusLift hv hp⟩
  have hcoeff : ∀ k, UnitAddTorus.mFourierCoeff (⇑F) k = torusCoeff v k :=
    fun k => mFourierCoeff_torusLift hp k
  have hsF : Summable (UnitAddTorus.mFourierCoeff (⇑F)) := by
    convert hs.of_norm using 1
    funext k
    exact hcoeff k
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsF (torusProj x)
  have hfun : (fun k => torusCoeff v k * character k (fun j => (x j : ℂ))) =
      fun k => UnitAddTorus.mFourierCoeff (⇑F) k • UnitAddTorus.mFourier k (torusProj x) := by
    funext k
    rw [hcoeff, mFourier_torusProj, smul_eq_mul]
  rw [hfun, ← torusLift_torusProj hp x]
  exact h

/-- A continuous periodic function with vanishing Fourier coefficients vanishes. -/
theorem eq_zero_of_torusCoeff_eq_zero {v : (Fin n → ℝ) → ℂ} (hv : Continuous v)
    (hp : ∀ (i : Fin n) x, v (x + Pi.single i 1) = v x) (h0 : ∀ k, torusCoeff v k = 0)
    (x : Fin n → ℝ) : v x = 0 := by
  have h := hasSum_torusCoeff_mul_character hv hp (by simp [h0]) x
  simp only [h0, zero_mul] at h
  exact h.unique hasSum_zero

/-! ### Holomorphic maps on strips -/

/-- **Fourier coefficients determine periodic holomorphic maps** (blueprint `bp:p1:fourier-basic`
(c)). -/
theorem eq_zero_of_torusCoeff_holomorphic {r : ℝ} (hr : 0 < r) {v : (Fin n → ℂ) → ℂ}
    (hv : DifferentiableOn ℂ v (complexStrip n r))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n r → v (z + Pi.single i 1) = v z)
    (h0 : ∀ k, torusCoeff (fun x => v fun j => (x j : ℂ)) k = 0) :
    ∀ θ ∈ complexStrip n r, v θ = 0 := by
  apply strip_identity hr hv
  have hc : Continuous fun x : Fin n → ℝ => v fun j => (x j : ℂ) :=
    hv.continuousOn.comp_continuous
      (continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j))
      (fun x => ofReal_mem_complexStrip hr x)
  have hpr : ∀ (i : Fin n) (x : Fin n → ℝ),
      (fun j => (((x + Pi.single i (1 : ℝ) : Fin n → ℝ) j : ℝ) : ℂ)) =
        (fun j => (x j : ℂ)) + Pi.single i 1 := by
    intro i x
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  exact eq_zero_of_torusCoeff_eq_zero hc
    (fun i x => by
      show v (fun j => (((x + Pi.single i (1 : ℝ) : Fin n → ℝ) j : ℝ) : ℂ)) =
        v (fun j => (x j : ℂ))
      rw [hpr]
      exact hp i _ (ofReal_mem_complexStrip hr x)) h0

theorem torusCoeff_sub {f g : (Fin n → ℝ) → ℂ} (hf : Continuous f) (hg : Continuous g)
    (k : Fin n → ℤ) : torusCoeff (fun x => f x - g x) k = torusCoeff f k - torusCoeff g k := by
  have hc : Continuous fun x : Fin n → ℝ => character (-k) (fun j => (x j : ℂ)) :=
    (differentiable_character _).continuous.comp
      (continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j))
  simp only [torusCoeff, torusAverage, mul_sub]
  exact integral_sub (integrableOn_unitCube_of_continuous (hc.mul hf))
    (integrableOn_unitCube_of_continuous (hc.mul hg))

/-- **Summation, representation part** (blueprint `bp:p1:summation`): a bounded periodic
holomorphic map on the strip of width `ρ` equals its Fourier series there. -/
theorem eq_fourierSum_torusCoeff {ρ A : ℝ} (hρ : 0 < ρ) {u : (Fin n → ℂ) → ℂ}
    (hu : DifferentiableOn ℂ u (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z)
    (hA : ∀ z ∈ complexStrip n ρ, ‖u z‖ ≤ A) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ) :
    u θ = fourierSum (torusCoeff fun x => u fun j => (x j : ℂ)) θ := by
  obtain ⟨a, ha⟩ : ∃ a, a = torusCoeff fun x => u fun j => (x j : ℂ) := ⟨_, rfl⟩
  rw [← ha]
  obtain ⟨ε, hε, hθε⟩ := exists_mem_complexStrip_sub hθ
  set δ := min ε (ρ / 2) with hδ_def
  have hδ : 0 < δ := lt_min hε (half_pos hρ)
  have hδρ : δ < ρ := (min_le_right _ _).trans_lt (half_lt_self hρ)
  have hθδ : θ ∈ complexStrip n (ρ - δ) := fun j =>
    (hθε j).trans_le (by linarith [min_le_left ε (ρ / 2), hδ_def])
  obtain ⟨hsum, -⟩ := summableWeighted_torusCoeff hδ hδρ hu hp hA
  rw [← ha] at hsum
  have hsub : complexStrip n (ρ - δ) ⊆ complexStrip n ρ := fun z hz j => by
    have := hz j
    linarith
  have hr : 0 < ρ - δ := by linarith
  have hL : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)
  have hcu : Continuous fun x : Fin n → ℝ => u fun j => (x j : ℂ) :=
    hu.continuousOn.comp_continuous hL fun x => ofReal_mem_complexStrip hρ x
  have hcg : Continuous fun x : Fin n → ℝ => fourierSum a fun j => (x j : ℂ) :=
    (differentiableOn_fourierSum hsum).continuousOn.comp_continuous hL
      fun x => ofReal_mem_complexStrip hr x
  have hw := eq_zero_of_torusCoeff_holomorphic hr (v := fun z => u z - fourierSum a z)
    ((hu.mono hsub).sub (differentiableOn_fourierSum hsum))
    (fun i z hz => by
      show u (z + Pi.single i 1) - fourierSum a (z + Pi.single i 1) = u z - fourierSum a z
      rw [hp i z (hsub hz), fourierSum_add_single])
    (fun k => by
      show torusCoeff (fun x => u (fun j => (x j : ℂ)) - fourierSum a fun j => (x j : ℂ)) k = 0
      rw [torusCoeff_sub hcu hcg, torusCoeff_fourierSum hr.le hsum k, ← ha, sub_self])
    θ hθδ
  exact sub_eq_zero.mp hw

end KAM

end
