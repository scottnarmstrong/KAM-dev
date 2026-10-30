/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.SmallDiv.Classical
public import KAM.Sharp2.SmallDiv.Solution
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Instances of `SDConst` (blueprint `bp:p2s2sd:from-cohdata`, `classical`, `freq`, `avg`)
-/

@[expose] public noncomputable section

open Filter Topology
open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Sharp2

open KAM.Torus KAM.Apost KAM.Sharp KAM

/-- Blueprint `bp:p2s2sd:from-cohdata`. -/
theorem sdConst_of_cohData {n : ℕ} {τ κ cR γ δ : ℝ} (hC : CohData n τ κ cR) (hγ : 0 < γ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : SDConst n κ γ δ cR {ω | IsDiophantine γ τ ω} where
  c_pos := hC.cR_pos
  delta_pos := hδ
  sol := fun ω hω r hδr p g H hg hp hH h0 θ hθ => hC.sol hγ hω hδ hδ1 hδr g H hg hp hH h0 θ hθ
  apriori := fun ω hω r hδr p q u H hu hp h0 hH θ hθ =>
    hC.apriori hγ hω hδ hδ1 hδr u H hu hp h0 hH θ hθ
  real := by
    intro ω hω r hδr p g H hg hp hH h0 θ
    have hr : 0 < r := hδ.trans_le hδr
    rcases hδr.lt_or_eq with hlt | heq
    · refine hC.sol hγ hω hδ hδ1 hlt g H hg hp hH h0 _ ?_
      intro j; simpa using sub_pos.mpr hlt
    · subst heq
      set F : ℝ → ℝ := fun d => cR * γ⁻¹ * d ^ (-κ) * H with hF
      have hcont : ContinuousAt F δ :=
        ((continuousAt_const.mul (Real.continuousAt_rpow_const δ (-κ) (Or.inl hδ.ne'))).mul
          continuousAt_const)
      have hlim : Tendsto F (𝓝[<] δ) (𝓝 (F δ)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
      refine ge_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsLT hδ] with d hd
      refine hC.sol hγ hω hd.1 (hd.2.le.trans hδ1) hd.2 g H hg hp hH h0 _ ?_
      intro j; simpa using sub_pos.mpr hd.2

theorem sdEps_nonneg {τ x : ℝ} (hτ : 0 ≤ τ) (hx : 0 ≤ x) : 0 ≤ sdEps τ x := by
  unfold sdEps
  have := Real.Gamma_pos_of_pos (by linarith : 0 < 2 * τ + 1)
  positivity

theorem sdEps_mono {τ x x' : ℝ} (hτ : 0 ≤ τ) (hxx : x ≤ x') : sdEps τ x ≤ sdEps τ x' := by
  unfold sdEps
  have := Real.Gamma_pos_of_pos (by linarith : 0 < 2 * τ + 1)
  have h0 : 0 ≤ (2 * τ / Real.exp 1) ^ (2 * τ) / Real.Gamma (2 * τ + 1) := by
    have : 0 ≤ 2 * τ / Real.exp 1 := by positivity
    positivity
  have e : ∀ y : ℝ, y * (2 * τ / Real.exp 1) ^ (2 * τ) / Real.Gamma (2 * τ + 1) =
      y * ((2 * τ / Real.exp 1) ^ (2 * τ) / Real.Gamma (2 * τ + 1)) := fun y => by ring
  rw [e, e]
  exact mul_le_mul_of_nonneg_right hxx h0

theorem cohConstC_pos {n : ℕ} {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 ≤ δ) : 0 < cohConstC n τ δ := by
  unfold cohConstC
  have h1 := shellConst_pos hτ.le
  have h2 := Real.Gamma_pos_of_pos (by linarith : 0 < 2 * τ + 1)
  have h3 := sdEps_nonneg hτ.le (by positivity : 0 ≤ 4 * Real.pi * δ)
  positivity

/-- `c♮(n, τ, ·)` is nondecreasing. -/
theorem cohConstC_mono {n : ℕ} {τ δ δ' : ℝ} (hτ : 1 ≤ τ) (hδ : 0 ≤ δ) (hδδ' : δ ≤ δ') :
    cohConstC n τ δ ≤ cohConstC n τ δ' := by
  unfold cohConstC
  have hτ0 : 0 ≤ τ := by linarith
  have h1 := shellConst_pos hτ0
  have h2 := Real.Gamma_pos_of_pos (by linarith : 0 < 2 * τ + 1)
  have hε := sdEps_mono (τ := τ) hτ0 (by gcongr : 4 * Real.pi * δ ≤ 4 * Real.pi * δ')
  have hq : 0 ≤ (4 * Real.pi) ^ (-τ) := by positivity
  refine mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)) hq
  gcongr

theorem sdFinite_zero {n : ℕ} (ω : Fin n → ℝ) (b : ℝ) : sdFinite ω b 0 = 0 := by
  unfold sdFinite
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [if_pos]
  by_cases hk : k = 0
  · exact Or.inl hk
  · refine Or.inr ?_
    obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
      by_contra h; push Not at h; exact hk (funext h)
    exact lt_of_lt_of_le (Int.natAbs_pos.mpr hj)
      (Finset.single_le_sum (f := fun i => (k i).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j))

/-- Blueprint `bp:p2s2sd:classical`. -/
theorem sdConst_classical {n : ℕ} (hn : 1 ≤ n) {τ γ δ : ℝ} (hτ : 1 ≤ τ) (hγ : 0 < γ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    SDConst n τ γ δ (cohConstC n τ δ) {ω | IsDiophantine γ τ ω} := by
  have hτ0 : 0 < τ := by linarith
  refine sdConst_of_sdSum (cohConstC_pos hτ0 hδ.le) hδ hγ hτ0.le (fun ω hω => hω) ?_
  intro ω hω
  have h := (sdSum_le_finite_add_tail hω hγ hτ0.le hδ 0).trans_eq' rfl
  rw [sdFinite_zero, zero_add] at h
  have h2 := h.trans (sdTail_zero_le hτ0 hγ hδ)
  set β : ℝ := 4 * Real.pi * δ with hβ
  have hβ0 : 0 < β := by positivity
  have hA := shellConst_pos hτ0.le
  have hG := Real.Gamma_pos_of_pos (by linarith : 0 < 2 * τ + 1)
  have hε := sdEps_nonneg hτ0.le hβ0.le
  set Q : ℝ := shellConst τ * Real.Gamma (2 * τ + 1) * (1 + sdEps τ β) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hβτ : β ^ (-(2 * τ)) = (β ^ (-τ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hβ0.le]; congr 1; push_cast; ring
  have hX : shellConst τ * γ⁻¹ ^ 2 * (Real.Gamma (2 * τ + 1) * β ^ (-(2 * τ)) * (1 + sdEps τ β)) =
      Q * (γ⁻¹ * β ^ (-τ)) ^ 2 := by
    rw [hβτ, hQ]; ring
  rw [hX] at h2
  have hsq : Real.sqrt (sdSum ω δ) ≤ Real.sqrt Q * (γ⁻¹ * β ^ (-τ)) := by
    refine (Real.sqrt_le_sqrt h2).trans (le_of_eq ?_)
    rw [Real.sqrt_mul hQ0, Real.sqrt_sq (by positivity)]
  unfold cohConstC
  rw [← hβ, ← hQ]
  have hmul : β ^ (-τ) = (4 * Real.pi) ^ (-τ) * δ ^ (-τ) := by
    rw [hβ, Real.mul_rpow (by positivity) hδ.le]
  calc (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n) * Real.sqrt (sdSum ω δ)
      ≤ (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n) * (Real.sqrt Q * (γ⁻¹ * β ^ (-τ))) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by
        rw [Real.sqrt_mul (by positivity) Q, hmul]; ring

theorem frequencyDot_smul {n : ℕ} (ω : Fin n → ℝ) (s : ℝ) (k : Fin n → ℤ) :
    Diophantine.frequencyDot (s • ω) k = s * Diophantine.frequencyDot ω k := by
  unfold Diophantine.frequencyDot
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp; ring

theorem isDiophantine_ray {n : ℕ} {γ τ s : ℝ} {ω : Fin n → ℝ} (h : IsDiophantine γ τ ω)
    (hs : 1 ≤ s) : IsDiophantine γ τ (s • ω) := by
  intro k hk
  have := h k hk
  refine this.trans ?_
  have e : (∑ i, (k i : ℝ) * (s • ω) i) = Diophantine.frequencyDot (s • ω) k := rfl
  have e' : (∑ i, (k i : ℝ) * ω i) = Diophantine.frequencyDot ω k := rfl
  rw [e, e', frequencyDot_smul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ s)]
  exact le_mul_of_one_le_left (abs_nonneg _) hs

theorem sdSum_ray_le {n : ℕ} {γ τ s b : ℝ} {ω : Fin n → ℝ} (h : IsDiophantine γ τ ω)
    (hγ : 0 < γ) (hτ : 0 ≤ τ) (hs : 1 ≤ s) (hb : 0 < b) : sdSum (s • ω) b ≤ sdSum ω b := by
  have h2b : 0 < 2 * b := by positivity
  rw [sdSum_eq_smallDivisorSum, sdSum_eq_smallDivisorSum]
  refine Summable.tsum_le_tsum (fun k => ?_)
    (summable_smallDivisorTerm (isDiophantine_ray h hs).condition hγ hτ h2b)
    (summable_smallDivisorTerm h.condition hγ hτ h2b)
  by_cases hk : k = 0
  · simp [smallDivisorTerm, hk]
  · rw [smallDivisorTerm_of_ne hk, smallDivisorTerm_of_ne hk, frequencyDot_smul, mul_pow]
    have hf := h.condition.nonresonant hγ k hk
    have hf2 : 0 < (Diophantine.frequencyDot ω k) ^ 2 := by positivity
    have hs2 : 1 ≤ s ^ 2 := by nlinarith
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rw [mul_inv]
    exact mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hs2)

theorem sdSum_pos {n : ℕ} (hn : 1 ≤ n) {γ τ b : ℝ} {ω : Fin n → ℝ} (h : IsDiophantine γ τ ω)
    (hγ : 0 < γ) (hτ : 0 ≤ τ) (hb : 0 < b) : 0 < sdSum ω b := by
  have h2b : 0 < 2 * b := by positivity
  rw [sdSum_eq_smallDivisorSum]
  set k0 : Fin n → ℤ := Pi.single ⟨0, hn⟩ 1 with hk0
  have hne : k0 ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hn⟩
    simp [hk0] at this
  refine (summable_smallDivisorTerm h.condition hγ hτ h2b).tsum_pos
    (smallDivisorTerm_nonneg ω (2 * b)) k0 ?_
  rw [smallDivisorTerm_of_ne hne]
  have := h.condition.nonresonant hγ k0 hne
  positivity

/-- Blueprint `bp:p2s2sd:freq`. -/
theorem sdConst_freq {n : ℕ} (hn : 1 ≤ n) {τ γ δ Shat : ℝ} {N : ℕ} {ωstar : Fin n → ℝ}
    (hτ : 1 ≤ τ) (hγ : 0 < γ) (hdio : IsDiophantine γ τ ωstar) (hδ : 0 < δ) (hN : 1 ≤ N)
    (hS : sdFinite ωstar δ N ≤ Shat) :
    SDConst n τ γ δ (cohConstF n τ γ δ N Shat) (ray ωstar) := by
  have hτ0 : 0 < τ := by linarith
  have hbound : ∀ s : ℝ, 1 ≤ s → sdSum (s • ωstar) δ ≤ Shat + sdTail τ γ δ N := fun s hs =>
    (sdSum_ray_le hdio hγ hτ0.le hs hδ).trans
      ((sdSum_le_finite_add_tail hdio hγ hτ0.le hδ N).trans (add_le_add hS le_rfl))
  have hpos : 0 < Shat + sdTail τ γ δ N :=
    (sdSum_pos hn hdio hγ hτ0.le hδ).trans_le
      ((sdSum_le_finite_add_tail hdio hγ hτ0.le hδ N).trans (add_le_add hS le_rfl))
  have hc : 0 < cohConstF n τ γ δ N Shat := by
    unfold cohConstF
    have := Real.rpow_pos_of_pos hδ τ
    positivity
  refine sdConst_of_sdSum hc hδ hγ hτ0.le ?_ ?_
  · rintro ω ⟨s, hs, rfl⟩
    exact isDiophantine_ray hdio hs
  · rintro ω ⟨s, hs, rfl⟩
    have h1 := Real.sqrt_le_sqrt (hbound s hs)
    unfold cohConstF
    have e : γ * δ ^ τ * γ⁻¹ * δ ^ (-τ) = 1 := by
      rw [Real.rpow_neg hδ.le]
      have : δ ^ τ ≠ 0 := (Real.rpow_pos_of_pos hδ τ).ne'
      field_simp
    calc (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n) * Real.sqrt (sdSum (s • ωstar) δ)
        ≤ (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n) * Real.sqrt (Shat + sdTail τ γ δ N) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (2 * Real.pi)⁻¹ * γ * δ ^ τ * Real.sqrt (2 ^ n * (Shat + sdTail τ γ δ N)) * γ⁻¹ *
            δ ^ (-τ) := by
          rw [Real.sqrt_mul (by positivity)]
          calc _ = (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n) * Real.sqrt (Shat + sdTail τ γ δ N) *
                (γ * δ ^ τ * γ⁻¹ * δ ^ (-τ)) := by rw [e, mul_one]
            _ = _ := by ring

/-- Blueprint `bp:p2s2sd:avg`. -/
theorem norm_avg_mul_cohR_le {n p q : ℕ} {κ γ r c y H : ℝ} {ω : Fin n → ℝ}
    {Ω : Set (Fin n → ℝ)} (hc : SDConst n κ γ r c Ω) (hω : ω ∈ Ω)
    (g : (Fin n → ℂ) → Fin p → ℂ) (Y : (Fin n → ℂ) → Matrix (Fin q) (Fin p) ℂ)
    (hg : DifferentiableOn ℂ g (complexStrip n r)) (hgp : IsPeriodicOn g r)
    (hgH : ∀ θ ∈ complexStrip n r, ‖g θ‖ ≤ H) (hg0 : avg g = 0)
    (hY : Continuous (fun θ : Fin n → ℝ => Y (fun i => (θ i : ℂ))))
    (hYp : ∀ (θ : Fin n → ℝ) (k : Fin n → ℤ),
      Y (fun i => ((θ i + k i : ℝ) : ℂ)) = Y (fun i => (θ i : ℂ)))
    (hYy : ∀ θ : Fin n → ℝ, ‖Y (fun i => (θ i : ℂ))‖ ≤ y) :
    ‖avg (fun θ => Y θ *ᵥ cohR ω g θ)‖ ≤ y * (c * γ⁻¹ * r ^ (-κ) * H) := by
  refine norm_torusAverage_le fun x _ => ?_
  have h1 := hc.real ω hω le_rfl g H hg hgp hgH hg0 x
  refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
  exact mul_le_mul (hYy x) h1 (norm_nonneg _) ((norm_nonneg _).trans (hYy x))

end KAM.Sharp2

end
