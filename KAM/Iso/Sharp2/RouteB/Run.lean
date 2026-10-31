/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.RouteB.Step
public import KAM.Sharp2.RouteB.Core
public import KAM.Iso.Apost.Limit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The run of the isoenergetic route B

* `RunHypI.isNewton`: `schemeIB` satisfies (N1), (N2) of `StageScheme.IsNewton` with the constants
  `stageC N` and the caps `capB N σ_T μ ν`; at the matched pair `(r_s, δ_s)` of a flagged state it
  is `RunHypI.good_step`, elsewhere the state is unchanged and the flag cleared;
* `iterI_spec`: along the run from `(0, true, K₀, ς₀, ς₀)`, the state is flagged at stage `s` and
  its previous scale is the scale of the iterate `s - 1`;
* `exists_limit_of_incr`: a real sequence with increments bounded by a geometric tail converges,
  with the sum of the bounds as the distance to the initial value;
* `tendsto_weighted_zero`, `iso_energy_limit_B`: the weighted errors tend to `0` along the run, and
  the energy of the limit torus (`KAM.Iso.Apost.tendsto_energyAverage_of_uniform`, from a late
  iterate, where the remaining ball margin of the limit controls the iterates).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology MeasureTheory

namespace KAM.Iso.Sharp2.RouteB

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteB KAM.Iso.Linear KAM.Iso.Apost
open KAM.Iso.Sharp2.ModStepB (newK)

variable {n : ℕ} {N : NumB n} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ωstar : Fin n → ℝ} {Ω : Set (Fin n → ℝ)}
  {τ M E₀ σω ν γ σT μm Xi ς0 : ℝ} {K0 : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- (N1), (N2) for the isoenergetic scheme of route B. -/
theorem RunHypI.isNewton (R : RunHypI τ M N 𝔅 h ωstar Ω σω ν γ σT μm K0 ς0) :
    (schemeIB N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0).IsNewton N.τ γ (bite0R N.a N.ρ N.ρinf) (stageC N)
      (capB N σT μm ν) where
  regular := by
    intro r β w m x hx
    rcases x with ⟨s, b, K, ς, ςp⟩
    cases b
    · exact hx
    · exact ⟨hx.μ_nonneg, hx.holo, hx.primary, hx.real⟩
  step := by
    intro r β w δ m x hx hδ hδm h3 hcond hβ hcap
    rcases x with ⟨s, b, K, ς, ςp⟩
    have hnn := stageC_nonneg R.wf δ
    have hX0 : 0 ≤ w := by
      cases b
      · exact hx.1
      · exact hx.μ_nonneg
    have hg : 0 < γ * δ ^ N.τ := mul_pos R.γ_pos (Real.rpow_pos_of_pos hδ _)
    have hg1 : 0 < γ * δ ^ (N.τ + 1) := mul_pos R.γ_pos (Real.rpow_pos_of_pos hδ _)
    by_cases hm : b = true ∧ r = N.r s ∧ δ = N.δ s
    · obtain ⟨rfl, rfl, rfl⟩ := hm
      have hG : GoodI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 s (N.r s) β w m K ς ςp := hx
      rw [stageC_sched R.wf] at hcond hβ hcap ⊢
      obtain ⟨hG', hcl, hpar⟩ := R.good_step hG hcond hβ hcap
      have hstep : (schemeIB N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0).step (N.r s) (N.δ s)
          (s, true, K, ς, ςp) = (s + 1, true, newK h K (ς • ωstar) E₀ (N.r s - 2 * N.δ s),
            isoNewS h K ωstar E₀ ς, ς) := by
        simp [schemeIB]
      rw [hstep]
      exact ⟨hG', hcl, hpar⟩
    · have hstep : (schemeIB N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0).step r δ (s, b, K, ς, ςp) =
          (s + 1, false, K, ς, ςp) := by
        simp only [schemeIB]
        split_ifs
        rfl
      rw [hstep]
      have hreg : DifferentiableOn ℂ K (complexStrip n r) ∧ IsPrimaryOnStrip K r ∧
          IsRealOnReals K := by
        cases b
        · exact hx.2
        · exact ⟨hx.holo, hx.primary, hx.real⟩
      refine ⟨junk_mono (by linarith) (by have := hnn.1; positivity) hreg, fun θ _ => ?_, ?_⟩
      · show ‖K θ - K θ‖ ≤ _
        rw [sub_self, norm_zero]
        have := hnn.2.1
        positivity
      · show |ς * ‖ωstar‖ - ς * ‖ωstar‖| ≤ _
        rw [sub_self, abs_zero]
        exact mul_nonneg hnn.2.2.1 hX0

/-- The iterates of the isoenergetic route B. -/
def iterI (N : NumB n) (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ωstar : Fin n → ℝ) (E₀ σω ν γ Xi : ℝ)
    (K0 : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ς0 : ℝ) (s : ℕ) : StI n :=
  Nat.rec ((0, true, K0, ς0, ς0) : StI n) (fun j x => (schemeIB N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0).step
    (stripSR N.a N.ρ N.ρinf j) (biteSR N.a N.ρ N.ρinf j) x) s

/-- Along the run the state is flagged at stage `s`, and the previous scale is the last one. -/
theorem iterI_spec (s : ℕ) :
    (iterI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 s).1 = s ∧
      (iterI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 s).2.1 = true ∧
      (iterI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 (s + 1)).2.2.2.2 =
        (iterI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 s).2.2.2.1 := by
  have key : ∀ s, (iterI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 s).1 = s ∧
      (iterI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 s).2.1 = true := by
    intro s
    induction s with
    | zero => exact ⟨rfl, rfl⟩
    | succ s ih =>
      obtain ⟨h1, h2⟩ := ih
      have e : iterI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 (s + 1) =
          (schemeIB N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0).step
          (stripSR N.a N.ρ N.ρinf s) (biteSR N.a N.ρ N.ρinf s)
          (iterI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 s) := rfl
      rcases hx : iterI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 s with ⟨s', b, K, ς, ςp⟩
      rw [hx] at h1 h2
      simp only at h1 h2
      subst h1 h2
      rw [e, hx]
      simp [schemeIB, NumB.r, NumB.δ]
  obtain ⟨h1, h2⟩ := key s
  refine ⟨h1, h2, ?_⟩
  have e : iterI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 (s + 1) =
      (schemeIB N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0).step
      (stripSR N.a N.ρ N.ρinf s) (biteSR N.a N.ρ N.ρinf s)
      (iterI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 s) := rfl
  rcases hx : iterI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 s with ⟨s', b, K, ς, ςp⟩
  rw [hx] at h1 h2
  simp only at h1 h2
  subst h1 h2
  rw [e, hx]
  simp [schemeIB, NumB.r, NumB.δ]

/-- A real sequence with increments `≤ d s`, `d s ≤ D y^{s-k}` for `s ≥ k`, converges, within
`∑_{s<k} d s + D/(1 - y)` of its initial value. -/
theorem exists_limit_of_incr {p d : ℕ → ℝ} {k : ℕ} {D y : ℝ} (hy1 : y < 1)
    (hinc : ∀ s, |p (s + 1) - p s| ≤ d s) (htail : ∀ s, k ≤ s → d s ≤ D * y ^ (s - k)) :
    ∃ l, Tendsto p atTop (𝓝 l) ∧ |l - p 0| ≤ (∑ s ∈ Finset.range k, d s) + D / (1 - y) := by
  have hq : ∀ s, dist (p (s + k)) (p (s + 1 + k)) ≤ D * y ^ s := fun s => by
    have e : s + 1 + k = (s + k) + 1 := by omega
    rw [e, dist_comm, Real.dist_eq]
    have := htail (s + k) (by omega)
    rw [Nat.add_sub_cancel] at this
    exact (hinc (s + k)).trans this
  have hc := cauchySeq_of_le_geometric y D hy1 hq
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  have h1 := dist_le_of_le_geometric_of_tendsto₀ y D hy1 hq hl
  have h2 : ∀ j, |p j - p 0| ≤ ∑ s ∈ Finset.range j, d s := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ]
      calc |p (j + 1) - p 0| = |(p j - p 0) + (p (j + 1) - p j)| := by congr 1; ring
        _ ≤ |p j - p 0| + |p (j + 1) - p j| := abs_add_le _ _
        _ ≤ _ := add_le_add ih (hinc j)
  refine ⟨l, (tendsto_add_atTop_iff_nat k).1 hl, ?_⟩
  have h3 : |p k - l| ≤ D / (1 - y) := by
    have := h1
    rwa [zero_add, Real.dist_eq] at this
  calc |l - p 0| = |(p k - p 0) - (p k - l)| := by congr 1; ring
    _ ≤ |p k - p 0| + |p k - l| := abs_sub _ _
    _ ≤ _ := add_le_add (h2 k) h3

/-- `C_s γ δ_s^{τ+1} X_s → 0`, for `C_s` constant from `kp` on. -/
theorem tendsto_weighted_zero (hN : N.Wf) {σ m₀ : Fin 7 → ℝ} {β Xs : ℝ} (hγ : 0 < γ)
    (hOk : routeBOk N σ m₀ β Xs) (hXi0 : 0 ≤ Xi) (hXi : Xi ≤ Xs) {C : ℕ → ℝ} (hC : ∀ s, 0 ≤ C s)
    (hCt : ∀ s, N.kp ≤ s → C s = C N.kp) :
    Tendsto (fun s => C s * (γ * N.δ s ^ (N.τ + 1) * N.xS Xi s)) atTop (𝓝 0) := by
  set A := C N.kp * γ * N.xS Xi N.kp with hA
  have hg : Tendsto (fun s : ℕ => A * N.ybar ^ (s - N.kp)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hN.ybar.1.le hN.ybar.2).comp
      (tendsto_sub_atTop_nat N.kp)).const_mul A
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun s => ?_) ?_ hg
  · exact mul_nonneg (hC s) (mul_nonneg (mul_nonneg hγ.le
      (Real.rpow_nonneg (hN.δ_pos s).le _)) (xS_nonneg hN hXi0 s))
  · refine Filter.eventually_atTop.2 ⟨N.kp, fun s hs => ?_⟩
    have hδ1 : N.δ s ^ (N.τ + 1) ≤ 1 :=
      Real.rpow_le_one (hN.δ_pos s).le (hN.δ_le_one s) (by linarith [hN.τ_pos])
    have hxt := xS_tail hN hOk hXi0 hXi s hs
    have hx0 := xS_nonneg hN hXi0 s
    have hce := hC N.kp
    show C s * (γ * N.δ s ^ (N.τ + 1) * N.xS Xi s) ≤ A * N.ybar ^ (s - N.kp)
    rw [hCt s hs, hA]
    calc C N.kp * (γ * N.δ s ^ (N.τ + 1) * N.xS Xi s) ≤ C N.kp * (γ * 1 * N.xS Xi s) := by gcongr
      _ ≤ C N.kp * (γ * 1 * (N.xS Xi N.kp * N.ybar ^ (s - N.kp))) := by gcongr
      _ = _ := by ring

/-- Lemma `bpI:p2:energy-limit` from a late iterate: a ball of radius `e` around the limit suffices
(the iterates enter the ball of radius `e/2` around themselves eventually). -/
theorem iso_energy_limit_B {M e ρinf E₀' : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hρinf : 0 < ρinf) (hM : 0 ≤ M) (hopen : IsOpen D)
    (hH : DifferentiableOn ℂ H D) (hdH : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ M) (he : 0 < e)
    {Ks : ℕ → (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {L : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ε : ℕ → ℝ}
    (hball : ∀ θ ∈ complexStrip n ρinf, Metric.ball (L θ) e ⊆ D)
    (hd : ∀ j, DifferentiableOn ℂ (Ks j) (complexStrip n ρinf))
    (hLd : DifferentiableOn ℂ L (complexStrip n ρinf))
    (hconv : TendstoUniformlyOn Ks L atTop (complexStrip n ρinf))
    (hen : ∀ j, ‖KAM.Iso.energyAverage H (Ks j) - (E₀' : ℂ)‖ ≤ ε j)
    (hε : Tendsto ε atTop (𝓝 0)) :
    KAM.Iso.energyAverage H L = (E₀' : ℂ) := by
  have he16 : 0 < e / 16 := by positivity
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hconv _ he16)
  have hcl : ∀ j ≥ j₀, ∀ θ ∈ complexStrip n ρinf, ‖L θ - Ks j θ‖ ≤ e / 16 := fun j hj θ hθ => by
    have := hj₀ j hj θ hθ
    rw [dist_eq_norm] at this
    exact this.le
  have hconv' : TendstoUniformlyOn (fun j => Ks (j + j₀)) L atTop (complexStrip n ρinf) :=
    Metric.tendstoUniformlyOn_iff.2 fun e' he' =>
      (tendsto_add_atTop_nat j₀).eventually (Metric.tendstoUniformlyOn_iff.1 hconv e' he')
  have hball' : ∀ θ ∈ complexStrip n ρinf, Metric.ball (Ks j₀ θ) (e / 2) ⊆ D := fun θ hθ => by
    refine (Metric.ball_subset_ball' ?_).trans (hball θ hθ)
    have := hcl j₀ le_rfl θ hθ
    rw [dist_comm, dist_eq_norm]
    linarith
  have hT := tendsto_energyAverage_of_uniform (μ := e / 2) hρinf hM hopen hH hdH (half_pos he)
    (K := Ks j₀) (L := L) (Ks := fun j => Ks (j + j₀)) hball'
    (fun j θ hθ => by
      have h1 := hcl (j + j₀) (by omega) θ hθ
      have h2 := hcl j₀ le_rfl θ hθ
      have h3 : ‖Ks (j + j₀) θ - Ks j₀ θ‖ ≤ ‖Ks (j + j₀) θ - L θ‖ + ‖L θ - Ks j₀ θ‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      rw [norm_sub_rev (Ks (j + j₀) θ) (L θ)] at h3
      linarith)
    (fun θ hθ => by
      have := hcl j₀ le_rfl θ hθ
      linarith)
    (fun j => hd (j + j₀)) hLd hconv'
  have hE0 : Tendsto (fun j => KAM.Iso.energyAverage H (Ks (j + j₀))) atTop (𝓝 (E₀' : ℂ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun j => hen (j + j₀))
      ((tendsto_add_atTop_iff_nat j₀).2 hε)
  exact tendsto_nhds_unique hT hE0

end KAM.Iso.Sharp2.RouteB

end
