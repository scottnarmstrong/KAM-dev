/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev
public import KAM.Frozen.Planetary.Defs.PlanetaryDriftExponent
public import KAM.Frozen.Planetary.Defs.PlanetaryTimeExponent
public import KAM.Frozen.Planetary.Defs.StoppedActionBound
public import KAM.Planetary.Exponential.Enlargement
public import KAM.Planetary.Exponential.Hamiltonian
public import KAM.Planetary.Exponential.KeplerData
public import KAM.Planetary.Exponential.Lift
public import KAM.Planetary.Exponential.Perturbation

/-!
# P14 package E11: the stopped action bound from N-PARTIAL-CONVEX

Blueprint P, Part 14 (`bpP:p14:stopped`, steps `st-thr`, `st-seg`, `st-sol`, `st-core`,
`st-fwd`, `st-bwd`, `st-phys`).  The sealed root `KAM.Nekhoroshev.partialConvex_nekhoroshev` is
applied with `n` fast actions and `k = n` slow pairs, `G = fastBox B κ`, `G' = fastBox B (2κ)`,
`D = slowBall n A`, once to the Kepler part `h` and once to `-h`, giving thresholds `μ₊, μ₋`.
A physical segment in the outer AMD region lifts to the chart (E9); there the N-Hamiltonian is the
chart Hamiltonian (E10).  Forward times use `(h, P)` on `[0, r]`; backward times use `(-h, -P)` on
the reversed segment `s ↦ y (-s)` over `[0, -l]`.

* `st-thr`: `ν₀ = min {1, μ₊, μ₋, κ^{1/b}, ε_D^{1/b}}` with
  `ε_D = (√(2A) - √(2 A_out)) / √(2n)`;
* `st-core`: the fast erosion `stopped_fast_erosion` and slow erosion `stopped_slow_erosion`;
* `st-sol`: `stopped_isSolutionOn_forward` and `stopped_isSolutionOn_reverse`;
* `st-seg`, `st-fwd`, `st-bwd`, `st-phys`: assembled in `stopped`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Planetary

variable {n : ℕ}

/-! ### The N domains: open convex action boxes and the open slow ball -/

/-- The fast action box is a product of open intervals. -/
theorem fastBox_eq_pi (B : AMDBox n) (kappa : ℝ) :
    fastBox B kappa = Set.univ.pi fun i => Ioo (B.lower i - kappa) (B.upper i + kappa) := by
  ext I
  simp [fastBox, Set.mem_pi]

theorem isOpen_fastBox (B : AMDBox n) (kappa : ℝ) : IsOpen (fastBox B kappa) := by
  rw [fastBox_eq_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

theorem convex_fastBox (B : AMDBox n) (kappa : ℝ) : Convex ℝ (fastBox B kappa) := by
  rw [fastBox_eq_pi]
  exact convex_pi fun _ _ => convex_Ioo _ _

theorem isOpen_slowBall (n : ℕ) (A : ℝ) : IsOpen (slowBall n A) :=
  isOpen_lt (by fun_prop) continuous_const

theorem isOpen_workingCylinder (B : AMDBox n) (kappa A : ℝ) :
    IsOpen (workingCylinder B kappa A) := by
  have hf : Continuous fun w : Phase (n + n) => fast w.2 :=
    continuous_pi fun i => (continuous_apply (Fin.castAdd n i)).comp continuous_snd
  have hs : Continuous fun w : Phase (n + n) => (slow w.1, slow w.2) :=
    (continuous_pi fun i => (continuous_apply (Fin.natAdd n i)).comp continuous_fst).prodMk
      (continuous_pi fun i => (continuous_apply (Fin.natAdd n i)).comp continuous_snd)
  exact ((isOpen_fastBox B kappa).preimage hf).inter ((isOpen_slowBall n A).preimage hs)

/-! ### Exponents: the number of fast actions is the number of planets -/

theorem planetaryTimeExponent_eq_partial (n : ℕ) :
    planetaryTimeExponent n = KAM.Nekhoroshev.partialTimeExponent n := by
  simp only [planetaryTimeExponent, KAM.Nekhoroshev.partialTimeExponent]

theorem planetaryDriftExponent_eq_partial (n : ℕ) :
    planetaryDriftExponent n = KAM.Nekhoroshev.partialDriftExponent n := by
  simp only [planetaryDriftExponent, planetaryTimeExponent,
    KAM.Nekhoroshev.partialDriftExponent]
  ring

theorem planetaryDriftExponent_pos (n : ℕ) : 0 < planetaryDriftExponent n := by
  rw [planetaryDriftExponent_eq_partial, KAM.Nekhoroshev.partialDriftExponent]
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact div_pos (by norm_num) (by nlinarith [sq_nonneg ((n : ℝ) - 1)])

/-! ### `st-core`: the two erosions -/

/-- `stepP:p14:st-core` (fast): an action strictly inside `(lower, upper)` lies in the
max-norm erosion of `fastBox B κ` of any radius `ε < κ`. -/
theorem stopped_fast_erosion (B : AMDBox n) {kappa ε : ℝ} (hε : 0 ≤ ε) (hεk : ε < kappa)
    {I : Fin n → ℝ} (hI : ∀ i, B.lower i < I i ∧ I i < B.upper i) :
    I ∈ KAM.Nekhoroshev.innerCore (fastBox B kappa) ε := by
  have hball : Metric.closedBall I ε ⊆ fastBox B kappa := by
    intro v hv i
    rw [Metric.mem_closedBall, dist_eq_norm] at hv
    have h1 : |v i - I i| ≤ ε := by
      have := (norm_le_pi_norm (v - I) i).trans hv
      simpa [Real.norm_eq_abs] using this
    have h2 := abs_le.1 h1
    constructor <;> linarith [(hI i).1, (hI i).2, h2.1, h2.2]
  exact ⟨hball (Metric.mem_closedBall_self hε), hball⟩

/-- `stepP:p14:st-core` (slow): a slow point of quadratic AMD `< A₁` lies in the max-norm erosion
of `slowBall n A` of radius `ε` whenever `√(2A₁) + √(2n) ε < √(2A)`; the max-norm ball of
radius `ε` has Euclidean radius at most `√(2n) ε`. -/
theorem stopped_slow_erosion {A₁ A ε : ℝ} (hε : 0 ≤ ε)
    (hlt : Real.sqrt (2 * A₁) + Real.sqrt (2 * n) * ε < Real.sqrt (2 * A))
    {x : Phase n} (hx : ∑ i, (x.1 i ^ 2 + x.2 i ^ 2) / 2 < A₁) :
    x ∈ KAM.Nekhoroshev.innerCore (slowBall n A) ε := by
  have hball : Metric.closedBall x ε ⊆ slowBall n A := by
    intro v hv
    rw [Metric.mem_closedBall, dist_eq_norm] at hv
    have h1 : ∀ i, |v.1 i - x.1 i| ≤ ε := fun i => by
      have := (norm_le_pi_norm (v - x).1 i).trans ((norm_fst_le (v - x)).trans hv)
      simpa [Real.norm_eq_abs] using this
    have h2 : ∀ i, |v.2 i - x.2 i| ≤ ε := fun i => by
      have := (norm_le_pi_norm (v - x).2 i).trans ((norm_snd_le (v - x)).trans hv)
      simpa [Real.norm_eq_abs] using this
    set X : Fin n ⊕ Fin n → ℝ := Sum.elim x.1 x.2 with hX
    set D : Fin n ⊕ Fin n → ℝ := Sum.elim (v.1 - x.1) (v.2 - x.2) with hD
    have hSX : ∑ j, X j ^ 2 = ∑ i, (x.1 i ^ 2 + x.2 i ^ 2) := by
      simp [X, Fintype.sum_sum_type, Finset.sum_add_distrib]
    have hSV : ∑ i, (v.1 i ^ 2 + v.2 i ^ 2) = ∑ j, (X j + D j) ^ 2 := by
      simp [X, D, Fintype.sum_sum_type, Finset.sum_add_distrib]
    have hDj : ∀ j, D j ^ 2 ≤ ε ^ 2 := by
      rintro (i | i)
      · simpa [D, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (h1 i) 2
      · simpa [D, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (h2 i) 2
    have hSD : ∑ j, D j ^ 2 ≤ (2 * n) * ε ^ 2 := by
      calc ∑ j, D j ^ 2 ≤ ∑ _j : Fin n ⊕ Fin n, ε ^ 2 := Finset.sum_le_sum fun j _ => hDj j
        _ = (2 * n) * ε ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
    have hexp : ∑ j, (X j + D j) ^ 2 =
        ∑ j, X j ^ 2 + 2 * ∑ j, X j * D j + ∑ j, D j ^ 2 := by
      have : ∀ j, (X j + D j) ^ 2 = X j ^ 2 + 2 * (X j * D j) + D j ^ 2 := fun j => by ring
      rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum]
    have hCS := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ X D
    set a := Real.sqrt (∑ j, X j ^ 2)
    set b := Real.sqrt (2 * n) * ε
    set c := Real.sqrt (2 * A₁)
    have hX0 : 0 ≤ ∑ j, X j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have ha2 : a ^ 2 = ∑ j, X j ^ 2 := Real.sq_sqrt hX0
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hb0 : 0 ≤ b := mul_nonneg (Real.sqrt_nonneg _) hε
    have hn0 : (0 : ℝ) ≤ 2 * n := by positivity
    have hb2 : b ^ 2 = (2 * n) * ε ^ 2 := by
      simp only [b, mul_pow, Real.sq_sqrt hn0]
    have hsD : Real.sqrt (∑ j, D j ^ 2) ≤ b := by
      calc Real.sqrt (∑ j, D j ^ 2) ≤ Real.sqrt ((2 * n) * ε ^ 2) := Real.sqrt_le_sqrt hSD
        _ = b := by rw [Real.sqrt_mul hn0, Real.sqrt_sq hε]
    have hac : a ≤ c := by
      apply Real.sqrt_le_sqrt
      rw [hSX]
      have : ∑ i, (x.1 i ^ 2 + x.2 i ^ 2) / 2 = (∑ i, (x.1 i ^ 2 + x.2 i ^ 2)) / 2 :=
        (Finset.sum_div _ _ _).symm
      linarith
    have hXD : ∑ j, X j * D j ≤ a * b :=
      hCS.trans (mul_le_mul_of_nonneg_left hsD ha0)
    have hle : ∑ j, (X j + D j) ^ 2 ≤ (c + b) ^ 2 := by
      rw [hexp]
      nlinarith
    have hcb : (c + b) ^ 2 < 2 * A :=
      (Real.lt_sqrt (add_nonneg (Real.sqrt_nonneg _) hb0)).1 hlt
    show ∑ i, (v.1 i ^ 2 + v.2 i ^ 2) / 2 < A
    rw [← Finset.sum_div, hSV]
    linarith
  exact ⟨hball (Metric.mem_closedBall_self hε), hball⟩

/-! ### `st-sol`: the lifted segment solves the N-systems -/

/-- The N-Hamiltonian `H_ν⁻` of `(-h, -P)` is `-H_ν⁺`. -/
theorem stopped_hamiltonian_neg (h : (Fin n → ℂ) → ℂ)
    (P : ((Fin (n+n) → ℂ) × (Fin (n+n) → ℂ)) → ℂ) (nu : ℝ) :
    degenerateHamiltonian (KAM.Nekhoroshev.realPart (-h))
        (fun _ x => ((-P) (KAM.Nekhoroshev.complexifyPhase x)).re) nu =
      fun w => -degenerateHamiltonian (KAM.Nekhoroshev.realPart h)
        (fun _ x => (P (KAM.Nekhoroshev.complexifyPhase x)).re) nu w := by
  funext w
  simp only [degenerateHamiltonian, KAM.Nekhoroshev.realPart, Pi.neg_apply, Complex.neg_re]
  ring

/-- `stepP:p14:st-sol` (forward): a chart curve in the working cylinder whose derivative is the
chart Hamiltonian field solves the N-system of `(h, P)` with `ν = B₀ μ` on `[0, r]`. -/
theorem stopped_isSolutionOn_forward (B : AMDBox n) (hB : B.Admissible) {kappa e A : ℝ}
    (hd : EnlargedData B kappa e A) {B0 mu : ℝ} (hB0 : 0 < B0)
    {P : ((Fin (n+n) → ℂ) × (Fin (n+n) → ℂ)) → ℂ}
    (hP : ∀ w ∈ workingCylinder B kappa A, P (KAM.Nekhoroshev.complexifyPhase w) =
      ((fMov 1 1 B.mass (poincareProd B.mass 1 w) / B0 : ℝ) : ℂ))
    {l r : ℝ} (hl : l ≤ 0) {y : ℝ → Phase (n + n)}
    (hy : ∀ s ∈ Icc l r, y s ∈ workingCylinder B kappa A ∧
      HasDerivAt y (KAM.hamiltonianVectorField
        (fun w => movingHamiltonian 1 1 B.mass mu (poincareProd B.mass 1 w)) (y s)) s) :
    KAM.Nekhoroshev.IsSolutionOn
      (degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC B.mass))
        (fun _ x => (P (KAM.Nekhoroshev.complexifyPhase x)).re) (B0 * mu))
      {I | fast (b := n) I ∈ fastBox B kappa} (Icc 0 r) y := by
  intro s hs
  have hs' : s ∈ Icc l r := ⟨hl.trans hs.1, hs.2⟩
  obtain ⟨hW, hder⟩ := hy s hs'
  obtain ⟨hdiff, -, hfield⟩ := differentiableAt_hnu_field B hB hd (mu := mu) hB0 hP
    (isOpen_workingCylinder B kappa A) subset_rfl hW
  refine ⟨hW.1, hdiff, ?_⟩
  convert hder using 1

/-- `stepP:p14:st-sol` (reversed): the reversed curve `s ↦ y (-s)` solves the N-system of
`(-h, -P)` with `ν = B₀ μ` on `[0, -l]`. -/
theorem stopped_isSolutionOn_reverse (B : AMDBox n) (hB : B.Admissible) {kappa e A : ℝ}
    (hd : EnlargedData B kappa e A) {B0 mu : ℝ} (hB0 : 0 < B0)
    {P : ((Fin (n+n) → ℂ) × (Fin (n+n) → ℂ)) → ℂ}
    (hP : ∀ w ∈ workingCylinder B kappa A, P (KAM.Nekhoroshev.complexifyPhase w) =
      ((fMov 1 1 B.mass (poincareProd B.mass 1 w) / B0 : ℝ) : ℂ))
    {l r : ℝ} (hr : 0 ≤ r) {y : ℝ → Phase (n + n)}
    (hy : ∀ s ∈ Icc l r, y s ∈ workingCylinder B kappa A ∧
      HasDerivAt y (KAM.hamiltonianVectorField
        (fun w => movingHamiltonian 1 1 B.mass mu (poincareProd B.mass 1 w)) (y s)) s) :
    KAM.Nekhoroshev.IsSolutionOn
      (degenerateHamiltonian (KAM.Nekhoroshev.realPart (-planetaryKeplerC B.mass))
        (fun _ x => ((-P) (KAM.Nekhoroshev.complexifyPhase x)).re) (B0 * mu))
      {I | fast (b := n) I ∈ fastBox B kappa} (Icc 0 (-l)) (fun s => y (-s)) := by
  intro s hs
  have hs' : -s ∈ Icc l r := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  obtain ⟨hW, hder⟩ := hy (-s) hs'
  obtain ⟨hdiff, -, hfield⟩ := differentiableAt_hnu_field B hB hd (mu := mu) hB0 hP
    (isOpen_workingCylinder B kappa A) subset_rfl hW
  rw [stopped_hamiltonian_neg]
  refine ⟨hW.1, hdiff.neg, ?_⟩
  have hcomp : HasDerivAt (fun s => y (-s)) ((-1 : ℝ) • KAM.hamiltonianVectorField
      (fun w => movingHamiltonian 1 1 B.mass mu (poincareProd B.mass 1 w)) (y (-s))) s :=
    hder.scomp s (hasDerivAt_neg' s)
  rw [neg_one_smul] at hcomp
  rw [hamiltonianVectorField_neg]
  convert hcomp using 2

/-! ### `bpP:p14:stopped` -/

/-- `bpP:p14:stopped`: the stopped action bound from N-PARTIAL-CONVEX. -/
theorem stopped (hn : 2 ≤ n) (B : AMDBox n) (hB : B.Admissible) :
    ∃ B0 nu0 : ℝ, 1 ≤ B0 ∧ 0 < nu0 ∧ nu0 ≤ 1 ∧
      ∀ mu T delta : ℝ, 0 < mu → B0 * mu < nu0 → 0 < T → 0 < delta →
        T ≤ (B0*mu)⁻¹ * Real.exp ((B0*mu)^(-planetaryTimeExponent n)) →
        (B0*mu)^planetaryDriftExponent n / 2 ≤ delta →
        ∀ z0 : Phase (n*2), StoppedActionBound B mu T delta z0 := by
  -- `st-thr`: the fixed data and the two N thresholds.
  obtain ⟨kappa, e, A, hd⟩ := enlarge B hB
  obtain ⟨rho, B0, hrho, hrk, hB0, P, hPP, hPPn, hPeq⟩ := perturbation B hB hd
  obtain ⟨hcollar, g, v, M, -, -, -, -, -, hg, hv, hM, hhol, hC2, hreal, hHess, hdef, hdefn, -⟩ :=
    h_data hn B hB hd hrho hrk
  obtain ⟨M', -, hM', hHess'⟩ := keplerDataNeg_hess_norm_le hn B hB hd hrho hrk
  have hk : 1 ≤ n := by omega
  obtain ⟨μp, hμp, hNp⟩ := KAM.Nekhoroshev.partialConvex_nekhoroshev hn hk
    (fastBox B kappa) (fastBox B (2*kappa)) (slowBall n A)
    (isOpen_fastBox B kappa) (convex_fastBox B kappa)
    (isOpen_fastBox B (2*kappa)) (convex_fastBox B (2*kappa)) (isOpen_slowBall n A)
    rho g v M hrho hM hcollar (planetaryKeplerC B.mass) hhol hC2 hreal hHess hdef
  obtain ⟨μm, hμm, hNm⟩ := KAM.Nekhoroshev.partialConvex_nekhoroshev hn hk
    (fastBox B kappa) (fastBox B (2*kappa)) (slowBall n A)
    (isOpen_fastBox B kappa) (convex_fastBox B kappa)
    (isOpen_fastBox B (2*kappa)) (convex_fastBox B (2*kappa)) (isOpen_slowBall n A)
    rho g v M' hrho hM' hcollar (-planetaryKeplerC B.mass)
    (keplerDataNeg_differentiableOn hn B hB hd hrho hrk)
    (keplerDataNeg_contDiffOn hn B hB hd hrho hrk)
    (keplerDataNeg_im_eq_zero hn B hB hd hrho hrk) hHess' hdefn
  have hκ : 0 < kappa := hd.kappa_pos
  have hAout : 0 < B.outerAMD := hB.2.2.2.1.trans hB.2.2.2.2.1
  have hsn : 0 < Real.sqrt (2 * n) := Real.sqrt_pos.2 (by positivity)
  set epsD := (Real.sqrt (2 * A) - Real.sqrt (2 * B.outerAMD)) / Real.sqrt (2 * n) with hepsD
  have hepsD0 : 0 < epsD :=
    div_pos (sub_pos.2 (Real.sqrt_lt_sqrt (by linarith) (by linarith [hd.amd_lt]))) hsn
  set b := planetaryDriftExponent n with hbdef
  have hb : 0 < b := planetaryDriftExponent_pos n
  set nu0 := min 1 (min μp (min μm (min (kappa ^ b⁻¹) (epsD ^ b⁻¹)))) with hnu0
  have hnu0pos : 0 < nu0 :=
    lt_min one_pos (lt_min hμp (lt_min hμm (lt_min (Real.rpow_pos_of_pos hκ _)
      (Real.rpow_pos_of_pos hepsD0 _))))
  have hm : ∀ i, 0 < B.mass i := fun i => (hB.1 i).1
  refine ⟨B0, nu0, hB0, hnu0pos, min_le_left _ _, ?_⟩
  intro mu T delta hmu hnu hT hdelta hTle hdel z0 l r z hl hr hlr hz0 hz hout t ht i
  set nu := B0 * mu with hnudef
  have hν : 0 < nu := mul_pos (by linarith) hmu
  have hνp : nu < μp := hnu.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hνm : nu < μm :=
    hnu.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hνκ' : nu < kappa ^ b⁻¹ := hnu.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hνε' : nu < epsD ^ b⁻¹ := hnu.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hνκ : nu ^ b < kappa := by
    have := Real.rpow_lt_rpow hν.le hνκ' hb
    rwa [Real.rpow_inv_rpow hκ.le hb.ne'] at this
  have hνε : nu ^ b < epsD := by
    have := Real.rpow_lt_rpow hν.le hνε' hb
    rwa [Real.rpow_inv_rpow hepsD0.le hb.ne'] at this
  have hνb0 : 0 ≤ nu ^ b := Real.rpow_nonneg hν.le _
  -- `st-seg`: the lifted chart segment.
  obtain ⟨y, hy⟩ := lift B hB mu l r hl hr hz hout
  have hyW : ∀ s ∈ Icc l r, y s ∈ workingCylinder B kappa A ∧
      HasDerivAt y (KAM.hamiltonianVectorField
        (fun w => movingHamiltonian 1 1 B.mass mu (poincareProd B.mass 1 w)) (y s)) s := by
    intro s hs
    obtain ⟨-, -, hder, hfast, hamd⟩ := hy s hs
    obtain ⟨-, hact, hAMD⟩ := hout s hs
    refine ⟨⟨fun j => ?_, ?_⟩, hder⟩
    · rw [hfast j]
      constructor <;> linarith [(hact j).1, (hact j).2]
    · show chartAMD (y s) < A
      rw [hamd]
      linarith [hd.amd_lt]
  have h0 : (0 : ℝ) ∈ Icc l r := ⟨hl, hr⟩
  have hy0 : ∀ j, fast (y 0).2 j = keplerAction B.mass z0 j := by
    intro j
    rw [(hy 0 h0).2.2.2.1 j, hz0]
  -- `st-core`: the initial fast erosion and the slow erosion along the segment.
  have hfast0 : fast (b := n) (y 0).2 ∈
      KAM.Nekhoroshev.innerCore (fastBox B kappa) (nu ^ b) := by
    apply stopped_fast_erosion B hνb0 hνκ
    intro j
    rw [hy0 j, ← hz0]
    exact (hout 0 h0).2.1 j
  have hslow : ∀ s ∈ Icc l r, (slow (a := n) (y s).1, slow (a := n) (y s).2) ∈
      KAM.Nekhoroshev.innerCore (slowBall n A) (nu ^ b) := by
    intro s hs
    refine stopped_slow_erosion (A₁ := B.outerAMD) hνb0 ?_ ?_
    · have : Real.sqrt (2 * n) * nu ^ b < Real.sqrt (2 * A) - Real.sqrt (2 * B.outerAMD) := by
        rw [hepsD, lt_div_iff₀ hsn] at hνε
        linarith
      linarith
    · show chartAMD (y s) < B.outerAMD
      rw [(hy s hs).2.2.2.2]
      exact (hout s hs).2.2
  -- `st-phys`: physical actions are chart actions.
  have hdrift : ‖fast (b := n) (y t).2 - fast (b := n) (y 0).2‖ ≤ nu ^ b / 2 →
      |keplerAction B.mass (z t) i - keplerAction B.mass z0 i| ≤ delta := by
    intro hN
    rw [← (hy t ht.1).2.2.2.1 i, ← hy0 i]
    have := (norm_le_pi_norm (fast (b := n) (y t).2 - fast (b := n) (y 0).2) i).trans hN
    rw [Real.norm_eq_abs] at this
    exact this.trans hdel
  have hTle' : T ≤ nu⁻¹ * Real.exp (nu ^ (-KAM.Nekhoroshev.partialTimeExponent n)) := by
    rwa [← planetaryTimeExponent_eq_partial]
  have hbN : b = KAM.Nekhoroshev.partialDriftExponent n := planetaryDriftExponent_eq_partial n
  obtain ⟨⟨htl, htr⟩, htT1, htT2⟩ := ht
  rcases lt_trichotomy t 0 with htneg | rfl | htpos
  · -- `st-bwd`: negative times through the reversed segment and `(-h, -P)`.
    apply hdrift
    have hsol := stopped_isSolutionOn_reverse B hB hd (by linarith : (0 : ℝ) < B0) hPeq hr hyW
    have hC : 0 < -l := by linarith
    have hfast0' : fast (b := n) ((fun s => y (-s)) 0).2 ∈
        KAM.Nekhoroshev.innerCore (fastBox B kappa)
          (nu ^ KAM.Nekhoroshev.partialDriftExponent n) := by
      simpa [neg_zero, ← hbN] using hfast0
    have hN := hNm nu hν hνm (-P) hPPn (-l) hC (fun s => y (-s)) hsol hfast0' (-t)
      ⟨by linarith, le_min (by linarith) (by linarith)⟩ (fun u hu => by
        rw [← hbN]
        exact hslow (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩)
    simpa [neg_neg, neg_zero, ← hbN] using hN
  · simp [hz0, hdelta.le]
  · -- `st-fwd`: positive times through `(h, P)` on `[0, r]`.
    apply hdrift
    have hsol := stopped_isSolutionOn_forward B hB hd (by linarith : (0 : ℝ) < B0) hPeq hl hyW
    have hC : 0 < r := htpos.trans_le htr
    have hN := hNp nu hν hνp P hPP r hC y hsol (by rw [← hbN]; exact hfast0) t
      ⟨htpos.le, le_min htr (htT2.trans hTle')⟩ (fun u hu => by
        rw [← hbN]
        exact hslow u ⟨hl.trans hu.1, hu.2.trans htr⟩)
    rwa [← hbN] at hN

end KAM.Planetary

end
