/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Nekhoroshev.Defs.IsPartialPerturbation
public import KAM.Planetary.Exponential.Setting
public import KAM.Planetary.Exponential.RealDomain
public import KAM.Planetary.Exponential.ComplexTube
public import KAM.Planetary.Poincare.Product

/-!
# P14 package E7: the normalized perturbation

Blueprint P, Part 14 (`bpP:p14:perturbation`, steps `pt-input`, `pt-rho`, `pt-def`, `pt-p12`,
`pt-p3`, `pt-p4`, `pt-neg`).

* `chart_perturbation_analytic`: the moving perturbation `fMov 1 1 m ∘ poincareProd m 1` is real
  analytic on the collision-free chart domain `chartSafe m` (the inherited pc-share gap).
* `perturbation`: `pt-input` — the compact core `perturbationCore` (one fundamental cell of the
  periodic orbit set of the enlarged cylinder) lies in `chartSafe`, and `tube` extends the chart
  perturbation to a shift-periodic holomorphic `fc` on a complex tube; `pt-rho` — `ρ = min κ (r/2)`
  and the bound `B₀` come from compactness of a thickening of the core; `pt-def` — `P = fc / B₀`
  on the tube and `0` elsewhere; `pt-p12`, `pt-p3`, `pt-p4` — the four clauses of
  `IsPartialPerturbation`; `pt-neg` — the same for `-P` (`isPartialPerturbation_neg_of`).
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators

namespace KAM.Planetary

variable {n : ℕ}

/-- Inherited pc-share/ho-hol gap: analytic regularity, not merely smoothness. -/
theorem chart_perturbation_analytic (m : Fin n → ℝ) (hm : ∀ i, 0 < m i) :
    AnalyticOnNhd ℝ (fun w => fMov 1 1 m (poincareProd m 1 w)) (chartSafe m) := by
  have h := analyticOnNhd_fMov_poincareProd (G := 1) (m0 := 1) hm (by norm_num)
  simp only [mul_one] at h
  exact h

/-- `pt-input`: the fundamental cell `K_*` of the enlarged cylinder (fast angles in `[0, 2π]`). -/
def perturbationCore (B : AMDBox n) (kappa A : ℝ) : Set (Phase (n + n)) :=
  {w | (∀ i, 0 ≤ fast w.1 i ∧ fast w.1 i ≤ 2 * Real.pi) ∧ w ∈ enlargedCylinder B kappa A}

theorem perturbationCore_subset (B : AMDBox n) (kappa A : ℝ) :
    perturbationCore B kappa A ⊆ enlargedCylinder B kappa A := fun _ hw => hw.2

theorem isClosed_perturbationCore (B : AMDBox n) (kappa A : ℝ) :
    IsClosed (perturbationCore B kappa A) := by
  have h1 : IsClosed {w : Phase (n + n) |
      ∀ i : Fin n, 0 ≤ fast w.1 i ∧ fast w.1 i ≤ 2 * Real.pi} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun i => ?_
    have : Continuous fun w : Phase (n + n) => fast w.1 i :=
      (continuous_apply _).comp continuous_fst
    exact (isClosed_le continuous_const this).inter (isClosed_le this continuous_const)
  have h2 : IsClosed {w : Phase (n + n) | ∀ i : Fin n, B.lower i - 2 * kappa ≤ fast w.2 i ∧
      fast w.2 i ≤ B.upper i + 2 * kappa} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun i => ?_
    have : Continuous fun w : Phase (n + n) => fast w.2 i :=
      (continuous_apply _).comp continuous_snd
    exact (isClosed_le continuous_const this).inter (isClosed_le this continuous_const)
  have h3 : IsClosed {w : Phase (n + n) | chartAMD w ≤ A} := by
    refine isClosed_le ?_ continuous_const
    unfold chartAMD
    refine continuous_finsetSum _ fun i _ => ?_
    have a : Continuous fun w : Phase (n + n) => slow w.1 i :=
      (continuous_apply _).comp continuous_fst
    have b : Continuous fun w : Phase (n + n) => slow w.2 i :=
      (continuous_apply _).comp continuous_snd
    exact ((a.pow 2).add (b.pow 2)).div_const _
  have := h1.inter (h2.inter h3)
  convert this using 1
  ext w
  simp only [perturbationCore, enlargedCylinder, mem_ofPred_eq, mem_inter_iff]

theorem isCompact_perturbationCore (B : AMDBox n) (kappa A : ℝ) :
    IsCompact (perturbationCore B kappa A) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_perturbationCore B kappa A) ?_
  set c : ℝ := ∑ i, (|B.lower i - 2 * kappa| + |B.upper i + 2 * kappa|) with hcdef
  have hc0 : ∀ i, |B.lower i - 2 * kappa| + |B.upper i + 2 * kappa| ≤ c := fun i =>
    Finset.single_le_sum (f := fun j => |B.lower j - 2 * kappa| + |B.upper j + 2 * kappa|)
      (fun j _ => by positivity) (Finset.mem_univ i)
  refine (Metric.isBounded_closedBall (x := (0 : Phase (n + n)))
    (r := 2 * Real.pi + c + 1 + 2 * A)).subset fun w hw => ?_
  obtain ⟨h1, h2, hA⟩ := hw
  have hpi := Real.pi_pos
  have hcnn : 0 ≤ c := Finset.sum_nonneg fun j _ => by positivity
  have hsl : ∀ i, (slow w.1 i) ^ 2 + (slow w.2 i) ^ 2 ≤ 2 * A := fun i => by
    have := Finset.single_le_sum (f := fun j => ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
    unfold chartAMD at hA
    linarith
  have habs : ∀ x : ℝ, x ^ 2 ≤ 2 * A → |x| ≤ 1 + 2 * A := fun x hx => by
    by_contra h
    push Not at h
    nlinarith [sq_abs x, abs_nonneg x]
  have hA0 : 0 ≤ A := by
    by_cases hn : n = 0
    · subst hn
      unfold chartAMD at hA
      simp at hA
      exact hA
    · have := hsl ⟨0, Nat.pos_of_ne_zero hn⟩
      nlinarith [sq_nonneg (slow w.1 ⟨0, Nat.pos_of_ne_zero hn⟩),
        sq_nonneg (slow w.2 ⟨0, Nat.pos_of_ne_zero hn⟩)]
  rw [mem_closedBall_zero_iff, Prod.norm_def]
  refine max_le ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have := h1 i
      rw [Real.norm_eq_abs, abs_le]
      simp only [fast] at this
      constructor <;> linarith [this.1, this.2]
    · have := habs _ ((le_add_of_nonneg_right (sq_nonneg _)).trans (hsl i))
      rw [Real.norm_eq_abs]
      simp only [slow] at this
      linarith
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have := h2 i
      have := hc0 i
      rw [Real.norm_eq_abs, abs_le]
      have h4 := neg_abs_le (B.lower i - 2 * kappa)
      have h5 := le_abs_self (B.upper i + 2 * kappa)
      have h6 := neg_abs_le (B.upper i + 2 * kappa)
      have h7 := abs_nonneg (B.lower i - 2 * kappa)
      have h8 := abs_nonneg (B.upper i + 2 * kappa)
      have h2i := h2 i
      simp only [fast] at h2i
      constructor <;> linarith [h2i.1, h2i.2]
    · have := habs _ ((le_add_of_nonneg_left (sq_nonneg _)).trans (hsl i))
      rw [Real.norm_eq_abs]
      simp only [slow] at this
      linarith

/-- `pt-rho` (geometry): a point of the partial complex tube is within `ρ` of a lattice translate of
a point of the core `K_*`. -/
theorem exists_shift_mem_core {B : AMDBox n} {kappa A rho : ℝ} (hrho : 0 < rho)
    {z : (Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)}
    (hz : z ∈ KAM.Nekhoroshev.partialComplexDomain (fastBox B (2 * kappa)) (slowBall n A) rho) :
    ∃ (k : Fin n → ℤ) (x : Phase (n + n)), x ∈ perturbationCore B kappa A ∧
      ‖z - KAM.Nekhoroshev.complexifyPhase (x + fastShift k)‖ < rho := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  set x0 : Phase (n + n) := (fun i => (z.1 i).re, fun i => (z.2 i).re) with hx0
  set k : Fin n → ℤ := fun i => ⌊(z.1 (Fin.castAdd n i)).re / (2 * Real.pi)⌋ with hk
  refine ⟨k, x0 - fastShift k, ⟨fun i => ?_, ?_⟩, ?_⟩
  · have hpi := Real.pi_pos
    have e1 := Int.floor_le ((z.1 (Fin.castAdd n i)).re / (2 * Real.pi))
    have e2 := Int.lt_floor_add_one ((z.1 (Fin.castAdd n i)).re / (2 * Real.pi))
    rw [le_div_iff₀ (by positivity)] at e1
    rw [div_lt_iff₀ (by positivity)] at e2
    simp only [fast, hx0, fastShift, Prod.fst_sub, Pi.sub_apply, Fin.append_left, hk]
    constructor <;> nlinarith
  · refine ⟨fun i => ?_, ?_⟩
    · have := h1 i
      have h := this
      simp only [fast] at h
      simp only [fast, hx0, fastShift, Prod.snd_sub, Pi.sub_apply, Pi.zero_apply,
        sub_zero]
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · have h2' : ∑ i, ((slow x0.1 i) ^ 2 + (slow x0.2 i) ^ 2) / 2 < A := h2
      have : chartAMD (x0 - fastShift k) = ∑ i, ((slow x0.1 i) ^ 2 + (slow x0.2 i) ^ 2) / 2 := by
        simp [chartAMD, slow, fastShift]
      rw [this]; exact h2'.le
  · rw [sub_add_cancel, Prod.norm_def]
    have key : ∀ v : Fin (n + n) → ℂ, (∀ j, |(v j).im| < rho) →
        ‖v - fun j => (((v j).re : ℝ) : ℂ)‖ < rho := by
      intro v hv
      rw [pi_norm_lt_iff hrho]
      intro j
      have : (v - fun j => (((v j).re : ℝ) : ℂ)) j = ((v j).im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact hv j
    exact max_lt (key _ h3) (key _ h4)

theorem fastShift_neg_add (k : Fin n → ℤ) (w : Phase (n + n)) :
    w + fastShift k + fastShift (-k) = w := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [fastShift, Fin.append_left]

theorem fastShift_zero_eq : fastShift (a := n) (b := n) 0 = 0 := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [fastShift, Fin.append_left]

/-- `pt-neg`: the four clauses of `IsPartialPerturbation` are invariant under `P ↦ -P`. -/
theorem isPartialPerturbation_neg_of {k : ℕ} {G : Set (Fin n → ℝ)} {D : Set (Phase k)} {ρ : ℝ}
    {P : (Fin (n + k) → ℂ) × (Fin (n + k) → ℂ) → ℂ}
    (h : KAM.Nekhoroshev.IsPartialPerturbation G D ρ P) :
    KAM.Nekhoroshev.IsPartialPerturbation G D ρ (-P) :=
  ⟨h.1.neg, fun z hz => by simpa using h.2.1 z hz,
    fun z hz => by simpa using h.2.2.1 z hz,
    fun z hz l => by simpa using h.2.2.2 z hz l⟩

theorem chartSafe_shift_iff {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (k : Fin n → ℤ)
    (w : Phase (n + n)) : w ∈ chartSafe m ↔ w + fastShift k ∈ chartSafe m := by
  have fwd : ∀ (k : Fin n → ℤ) (w : Phase (n + n)),
      w ∈ chartSafe m → w + fastShift k ∈ chartSafe m := by
    intro k w hw
    obtain ⟨hd, hc⟩ := poincareProd_lattice hm one_pos hw.1 k
    exact ⟨hd, by simpa [hc] using hw.2⟩
  refine ⟨fwd k w, fun h => ?_⟩
  simpa [fastShift_neg_add] using fwd (-k) _ h

theorem fMov_poincareProd_shift {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (k : Fin n → ℤ)
    {w : Phase (n + n)} (hw : w ∈ chartSafe m) :
    fMov 1 1 m (poincareProd m 1 (w + fastShift k)) = fMov 1 1 m (poincareProd m 1 w) := by
  rw [(poincareProd_lattice hm one_pos hw.1 k).2]

theorem mem_periodicOrbitSet_self {K : Set (Phase (n + n))} {x : Phase (n + n)} (hx : x ∈ K) :
    x ∈ periodicOrbitSet K :=
  ⟨0, x, hx, by rw [fastShift_zero_eq, add_zero]⟩

theorem perturbation (B : AMDBox n) (hB : B.Admissible) {kappa e A : ℝ}
    (hd : EnlargedData B kappa e A) :
    ∃ rho B0 : ℝ, 0 < rho ∧ rho ≤ kappa ∧ 1 ≤ B0 ∧
      ∃ P : ((Fin (n+n) → ℂ) × (Fin (n+n) → ℂ)) → ℂ,
        KAM.Nekhoroshev.IsPartialPerturbation (fastBox B (2*kappa)) (slowBall n A) rho P ∧
        KAM.Nekhoroshev.IsPartialPerturbation (fastBox B (2*kappa)) (slowBall n A) rho (-P) ∧
        ∀ w ∈ workingCylinder B kappa A,
          P (KAM.Nekhoroshev.complexifyPhase w) =
            ((fMov 1 1 B.mass (poincareProd B.mass 1 w) / B0 : ℝ) : ℂ) := by
  classical
  have hm : ∀ i, 0 < B.mass i := fun i => (hB.1 i).1
  have hκ := hd.kappa_pos
  -- pt-input
  have hW : IsOpen (chartSafe B.mass) := isOpen_poincareProd_preimage hm one_pos
  have hKW : perturbationCore B kappa A ⊆ chartSafe B.mass :=
    (perturbationCore_subset B kappa A).trans (real_domain B hB hd).1
  obtain ⟨r, hr, fc, hfc, hreal, hper⟩ := tube hW (isCompact_perturbationCore B kappa A) hKW
    (chartSafe_shift_iff hm) (chart_perturbation_analytic B.mass hm)
    (fun k w hw => fMov_poincareProd_shift hm k hw)
  -- pt-rho
  set rho : ℝ := min kappa (r / 2) with hrho
  have hrho0 : 0 < rho := lt_min hκ (half_pos hr)
  have hrho_r : rho < r := (min_le_right _ _).trans_lt (half_lt_self hr)
  set T := complexTube (perturbationCore B kappa A) r with hT
  set C : Set ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) :=
    (fun p : Phase (n + n) × ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) =>
      KAM.Nekhoroshev.complexifyPhase p.1 + p.2) ''
      (perturbationCore B kappa A ×ˢ closedBall 0 rho) with hC
  have hcx : Continuous (KAM.Nekhoroshev.complexifyPhase (n := n + n)) := by
    unfold KAM.Nekhoroshev.complexifyPhase
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun i => Complex.continuous_ofReal.comp
        ((continuous_apply i).comp continuous_fst)
    · exact continuous_pi fun i => Complex.continuous_ofReal.comp
        ((continuous_apply i).comp continuous_snd)
  have hCc : IsCompact C :=
    ((isCompact_perturbationCore B kappa A).prod (isCompact_closedBall _ _)).image
      ((hcx.comp continuous_fst).add continuous_snd)
  have hCT : C ⊆ T := by
    rintro _ ⟨⟨x, v⟩, ⟨hx, hv⟩, rfl⟩
    refine ⟨x, mem_periodicOrbitSet_self hx, ?_⟩
    have : ‖v‖ ≤ rho := by simpa using hv
    simp only [add_sub_cancel_left]
    exact this.trans_lt hrho_r
  obtain ⟨B', hB'⟩ := hCc.exists_bound_of_continuousOn (hfc.continuousOn.mono hCT)
  set B0 : ℝ := max 1 B' with hB0
  have hB0pos : 0 < B0 := lt_of_lt_of_le one_pos (le_max_left _ _)
  set F := KAM.Nekhoroshev.partialComplexDomain (fastBox B (2 * kappa)) (slowBall n A) rho with hF
  have hFT : ∀ z ∈ F, z ∈ T ∧ ‖fc z‖ ≤ B0 := by
    intro z hz
    obtain ⟨k, x, hx, hn⟩ := exists_shift_mem_core hrho0 hz
    have hzT : z ∈ T :=
      ⟨x + fastShift k, ⟨k, x, hx, rfl⟩, hn.trans hrho_r⟩
    have hz' : z - KAM.Nekhoroshev.complexifyPhase (fastShift k) ∈ C := by
      refine ⟨(x, z - KAM.Nekhoroshev.complexifyPhase (x + fastShift k)), ⟨hx, ?_⟩, ?_⟩
      · simpa using hn.le
      · simp only [complexifyPhase_add]; abel
    have h1 := (hper k _ (hCT hz')).2
    rw [sub_add_cancel] at h1
    exact ⟨hzT, h1 ▸ (hB' _ hz').trans (le_max_right _ _)⟩
  -- pt-def
  let P : ((Fin (n+n) → ℂ) × (Fin (n+n) → ℂ)) → ℂ := fun z => if z ∈ T then fc z / (B0 : ℂ) else 0
  have hP : ∀ z ∈ T, P z = fc z / (B0 : ℂ) := fun z hz => by simp [P, hz]
  have hdiv : DifferentiableOn ℂ (fun z => fc z / (B0 : ℂ)) T := by
    exact (differentiable_id.div_const (B0 : ℂ)).comp_differentiableOn hfc
  have hPos : KAM.Nekhoroshev.IsPartialPerturbation (fastBox B (2 * kappa)) (slowBall n A) rho
      P := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (hdiv.mono fun z hz => (hFT z hz).1).congr
        fun z hz => hP z (hFT z hz).1
    · intro z hz
      rw [hP z (hFT z hz).1, norm_div, Complex.norm_real, Real.norm_of_nonneg hB0pos.le]
      exact (div_le_one hB0pos).2 (hFT z hz).2
    · intro w hw
      obtain ⟨-, hwf⟩ := hreal w (hFT _ hw).1
      rw [hP _ (hFT _ hw).1, hwf, ← Complex.ofReal_div]
      exact Complex.ofReal_im _
    · intro z hz l
      obtain ⟨h1, h2⟩ := hper l z (hFT z hz).1
      rw [hP _ h1, hP _ (hFT z hz).1, h2]
  refine ⟨rho, B0, hrho0, min_le_left _ _, le_max_left _ _, P, hPos,
    isPartialPerturbation_neg_of hPos, fun w hw => ?_⟩
  have hwF : KAM.Nekhoroshev.complexifyPhase w ∈ F := by
    obtain ⟨h1, h2⟩ := hw
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      have := h1 i
      simp only [KAM.Nekhoroshev.complexifyPhase, Complex.ofReal_re, fast] at this ⊢
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    · simpa [KAM.Nekhoroshev.complexifyPhase, slowBall, slow] using h2
    · intro i; simpa [KAM.Nekhoroshev.complexifyPhase] using hrho0
    · intro i; simpa [KAM.Nekhoroshev.complexifyPhase] using hrho0
  obtain ⟨-, hwf⟩ := hreal w (hFT _ hwF).1
  rw [hP _ (hFT _ hwF).1, hwf, ← Complex.ofReal_div]

end KAM.Planetary

end
