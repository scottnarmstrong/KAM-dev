/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.HoloStripInput
public import KAM.Weighted.Norm

/-!
# `F = f̂_fix ∘ Φ_ρ⁻¹ ∘ T₁` on the working strip (P11A-P2c, `stepP:p11:hc-strip`, `hc-F`)

Parametric in the rotation family `ρ` (hypotheses `P11HsHyp`, no concrete choice): `p11hsF D ρ` is
holomorphic on `p11WorkingDom n J0 (2σ) (2 rC) rz` (`p11hsF_differentiableOn`), bounded by the
explicit `p11hsMInf D a` (`p11hsF_norm_le`, and in the weighted form `MF / coth(π σ)ⁿ` by
`p11hsF_bound_weighted`), `1`-periodic in each angle (`p11hsF_shift`) and real at real points
(`p11hsF_real`); `p11hs_F` packages these in the shape of the `holo_chart` clauses.
`p11hs_strip_data` supplies the strip data `(r', σ')` of `hc-strip`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler SecularForm

section Strip

variable {n : ℕ} {D : Data n} {a : Vec n} {ρ : P11CVec n → Matrix (Fin n) (Fin n) ℂ}
  {J0 : P11Vec n} {rC σ rz B B' r' σ' : ℝ}

/-- `hc-strip`: the strip data `(r', σ')`: `r' < ρ_*`, `σ' ∈ (0, 1/4]` with `2π σ' ≤ 1/8` and
`Re s_ij ≥ (a_j - a_i)²/4` on the polydisc of radius `r'` for `|Im λ_i| ≤ 2π σ'`. -/
theorem p11hs_strip_data (D : Data n) (ha : a ∈ axes n) :
    ∃ r' σ' : ℝ, 0 < r' ∧ r' < rho D a ∧ 0 < σ' ∧ σ' ≤ 1 / 4 ∧ 2 * π * σ' ≤ 1 / 8 ∧
      ∀ lam : CVec n, (∀ l, |(lam l).im| ≤ 2 * π * σ') → ∀ x ∈ polydisc D a r',
        ∀ i j : Fin n, i < j → (a j - a i) ^ 2 / 4 ≤ (p11hsSep D lam x i j).re := by
  obtain ⟨r0, hr0, hrho, hall⟩ := p11hs_strip D ha
  obtain ⟨σ', hσ0, hσ1, hσ2, hσ3⟩ := hall (r0 / 2) (by linarith)
  exact ⟨r0 / 2, σ', by linarith, by linarith, hσ0, hσ1, hσ2, hσ3⟩

theorem p11hsF_differentiableOn (hn : 0 < n) (ha : a ∈ axes n)
    (h : P11HsHyp D a ρ J0 rC σ rz B B' r' σ') :
    DifferentiableOn ℂ (p11hsF D ρ) (p11WorkingDom n J0 (2 * σ) (2 * rC) rz) := by
  have := (p11hsFHat_differentiableOn D ha h.r'_lt).comp (p11hsInput_differentiableOn h)
    fun z hz => p11hsInput_mem_good hn h hz
  exact this

theorem p11hsF_norm_le (hn : 0 < n) (ha : a ∈ axes n)
    (h : P11HsHyp D a ρ J0 rC σ rz B B' r' σ') {z : P11Phase (n + n)}
    (hz : z ∈ p11WorkingDom n J0 (2 * σ) (2 * rC) rz) : ‖p11hsF D ρ z‖ ≤ p11hsMInf D a :=
  p11hsFHat_norm_le D ha (p11hsInput_mem_good hn h hz)

theorem p11hsF_bound_weighted (hn : 0 < n) (ha : a ∈ axes n)
    (h : P11HsHyp D a ρ J0 rC σ rz B B' r' σ') {MF : ℝ}
    (hMF : KAM.Weighted.coth (π * σ) ^ n * p11hsMInf D a ≤ MF) {z : P11Phase (n + n)}
    (hz : z ∈ p11WorkingDom n J0 (2 * σ) (2 * rC) rz) :
    ‖p11hsF D ρ z‖ ≤ MF / KAM.Weighted.coth (π * σ) ^ n := by
  have hc : 0 < KAM.Weighted.coth (π * σ) := by
    unfold KAM.Weighted.coth
    have hx : 0 < π * σ := mul_pos Real.pi_pos h.sigma_pos
    exact div_pos (Real.cosh_pos _) (Real.sinh_pos_iff.2 hx)
  rw [le_div_iff₀ (pow_pos hc n)]
  calc ‖p11hsF D ρ z‖ * KAM.Weighted.coth (π * σ) ^ n
      ≤ p11hsMInf D a * KAM.Weighted.coth (π * σ) ^ n :=
        mul_le_mul_of_nonneg_right (p11hsF_norm_le hn ha h hz) (pow_nonneg hc.le n)
    _ = KAM.Weighted.coth (π * σ) ^ n * p11hsMInf D a := mul_comm _ _
    _ ≤ MF := hMF

theorem single_castAdd_natAdd (j i : Fin n) :
    (Pi.single (Fin.castAdd n j) (1 : ℂ) : Fin (n + n) → ℂ) (Fin.natAdd n i) = 0 :=
  Pi.single_eq_of_ne (fun e => by have := congrArg Fin.val e; simp at this; omega) _

theorem p11hsF_shift (hn : 0 < n) (ha : a ∈ axes n)
    (h : P11HsHyp D a ρ J0 rC σ rz B B' r' σ') {z : P11Phase (n + n)}
    (hz : z ∈ p11WorkingDom n J0 (2 * σ) (2 * rC) rz) (j : Fin n) :
    p11hsF D ρ (z.1 + Pi.single (Fin.castAdd n j) 1, z.2) = p11hsF D ρ z := by
  have hg := p11hsInput_mem_good hn h hz
  have hr : r' < rho D a := h.r'_lt
  refine p11hsFHat_shift D ha (r := r') hr (w := p11hsInput ρ z) hg.2.1 hg.1
    (Pi.single j 1) ?_ ?_
  · funext l
    rw [p11hsAngle_input, p11hsAngle_input]
    have hne := single_castAdd_natAdd j
    have hne2 : ∀ i : Fin n, (Pi.single (Fin.castAdd n j) (1 : ℂ) : Fin (n + n) → ℂ)
        (i.addNat n) = 0 := fun i => by
      have := hne i
      rwa [show Fin.natAdd n i = i.addNat n from Fin.ext (Nat.add_comm _ _)] at this
    simp only [Pi.add_apply, hne, add_zero]
    by_cases hl : l = j
    · subst hl
      simp only [Pi.single_eq_same, Pi.single_eq_same]
      push_cast
      ring
    · have : (Pi.single (Fin.castAdd n j) (1 : ℂ) : Fin (n + n) → ℂ) (Fin.castAdd n l) = 0 :=
        Pi.single_eq_of_ne (fun e => hl (Fin.castAdd_injective n n e)) _
      simp [hl]
  · rw [p11hsSlow_input, p11hsSlow_input]
    have hne := single_castAdd_natAdd j
    have hne2 : ∀ i : Fin n, (Pi.single (Fin.castAdd n j) (1 : ℂ) : Fin (n + n) → ℂ)
        (i.addNat n) = 0 := fun i => by
      have := hne i
      rwa [show Fin.natAdd n i = i.addNat n from Fin.ext (Nat.add_comm _ _)] at this
    simp [hne2]

theorem p11hsF_real (hn : 0 < n) (ha : a ∈ axes n)
    (h : P11HsHyp D a ρ J0 rC σ rz B B' r' σ') {z : Phase (n + n)}
    (hz : KAM.realInclusion₂ (n + n) z ∈ p11WorkingDom n J0 (2 * σ) (2 * rC) rz) :
    (p11hsF D ρ (KAM.realInclusion₂ (n + n) z)).im = 0 := by
  set S : Subring ℂ := Complex.ofRealHom.range with hS
  have hSim : ∀ c : ℂ, c.im = 0 → c ∈ S := fun c hc =>
    ⟨c.re, Complex.ext (by simp) (by simp [hc])⟩
  have hSre : ∀ c : ℂ, c ∈ S → c.im = 0 := by
    rintro c ⟨r, rfl⟩; simp
  have hSr : ∀ r : ℝ, (r : ℂ) ∈ S := fun r => ⟨r, rfl⟩
  set Lr : P11Vec n := fun i => z.2 (Fin.castAdd n i) / (2 * π) with hLr
  have hLc : (fun i : Fin n => (KAM.realInclusion₂ (n + n) z).2 (Fin.castAdd n i) / (2 * π)) =
      KAM.realInclusion n Lr := by
    funext i; simp [hLr, KAM.realInclusion_apply]
  have hLn : ‖Lr - (2 * π)⁻¹ • J0‖ < rC / π := by
    have hm := p11hs_L_mem hz
    rw [hLc, Metric.mem_ball, dist_eq_norm, ← map_smul, ← map_sub, KAM.norm_realInclusion] at hm
    exact hm
  have hRm : ∀ i j, ρ (KAM.realInclusion n Lr) i j ∈ S := fun i j => hSim _ (h.rot_real _ hLn i j)
  have hdm : ∀ l i j, (fderiv ℂ ρ (KAM.realInclusion n Lr) (Pi.single l 1) :
      Matrix (Fin n) (Fin n) ℂ) i j ∈ S := fun l i j => hSim _ (p11hs_fderiv_im h hLn l i j)
  have hT : ∀ l i j, (((ρ (KAM.realInclusion n Lr)).transpose *
      fderiv ℂ ρ (KAM.realInclusion n Lr) (Pi.single l 1) : Matrix (Fin n) (Fin n) ℂ)) i j ∈ S := by
    intro l i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hRm k i) (hdm l k j)
  have hmv : ∀ (v : Fin n → ℂ), (∀ i, v i ∈ S) → ∀ i,
      (ρ (KAM.realInclusion n Lr)).mulVec v i ∈ S := by
    intro v hv i
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hRm i j) (hv j)
  have hx : ∀ i : Fin n, (KAM.realInclusion₂ (n + n) z).1 (Fin.natAdd n i) ∈ S := fun i => by
    simp [hSr]
  have hy : ∀ i : Fin n, (KAM.realInclusion₂ (n + n) z).2 (Fin.natAdd n i) ∈ S := fun i => by
    simp [hSr]
  have h2pi : ((2 * π : ℂ)) ∈ S := by
    have := hSr (2 * π); simpa using this
  have hmem1 : ∀ k, (p11hsInput ρ (KAM.realInclusion₂ (n + n) z)).1 k ∈ S := by
    intro k
    induction k using Fin.addCases with
    | left l =>
      simp only [p11hsInput, Fin.append_left]
      rw [hLc]
      refine Subring.add_mem _ (Subring.mul_mem _ h2pi (by simp [hSr])) ?_
      exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
        Subring.mul_mem _ (Subring.mul_mem _ (hy i) (hT l i j)) (hx j)
    | right l =>
      simp only [p11hsInput, Fin.append_right]
      rw [hLc]
      exact hmv _ hx l
  have hmem2 : ∀ k, (p11hsInput ρ (KAM.realInclusion₂ (n + n) z)).2 k ∈ S := by
    intro k
    induction k using Fin.addCases with
    | left l =>
      simp only [p11hsInput, Fin.append_left]
      have := hSr (z.2 (Fin.castAdd n l) / (2 * π))
      simpa using this
    | right l =>
      simp only [p11hsInput, Fin.append_right]
      rw [hLc]
      exact hmv _ hy l
  have him : ∀ k, ((p11hsInput ρ (KAM.realInclusion₂ (n + n) z)).1 k).im = 0 ∧
      ((p11hsInput ρ (KAM.realInclusion₂ (n + n) z)).2 k).im = 0 := fun k =>
    ⟨hSre _ (hmem1 k), hSre _ (hmem2 k)⟩
  exact p11hsFHat_real D ha h.r'_lt (p11hsInput_mem_good hn h hz) him
/-- `hc-F`: the `holo_chart` clauses for `F := f̂_fix ∘ Φ_ρ⁻¹ ∘ T₁`, parametric in `ρ`:
holomorphy, the weighted sup bound `MF / coth(π σ)ⁿ`, `1`-periodicity and realness. -/
theorem p11hs_F (hn : 0 < n) (ha : a ∈ axes n)
    (h : P11HsHyp D a ρ J0 rC σ rz B B' r' σ') {MF : ℝ}
    (hMF : KAM.Weighted.coth (π * σ) ^ n * p11hsMInf D a ≤ MF) :
    DifferentiableOn ℂ (p11hsF D ρ) (p11WorkingDom n J0 (2 * σ) (2 * rC) rz) ∧
    (∀ z ∈ p11WorkingDom n J0 (2 * σ) (2 * rC) rz,
      ‖p11hsF D ρ z‖ ≤ MF / KAM.Weighted.coth (π * σ) ^ n) ∧
    (∀ z ∈ p11WorkingDom n J0 (2 * σ) (2 * rC) rz, ∀ j : Fin n,
      p11hsF D ρ (z.1 + Pi.single (Fin.castAdd n j) 1, z.2) = p11hsF D ρ z) ∧
    (∀ z : Phase (n + n), KAM.realInclusion₂ (n + n) z ∈
        p11WorkingDom n J0 (2 * σ) (2 * rC) rz →
      (p11hsF D ρ (KAM.realInclusion₂ (n + n) z)).im = 0) :=
  ⟨p11hsF_differentiableOn hn ha h, fun _ hz => p11hsF_bound_weighted hn ha h hMF hz,
    fun _ hz j => p11hsF_shift hn ha h hz j, fun _ hz => p11hsF_real hn ha h hz⟩

end Strip

end KAM.Planetary

end
