/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakMeasure.Stability

/-!
# Affine chart scaling (blueprint `bpP:p11a:chart-scaling`, P11A-W8)

The chart `A y = y₀ + λ y` (`λ > 0`) rescales derivatives by `λ^j`
(`chart_scaling_jets`, from the iterated-derivative identity `p11_iteratedFDeriv_affine`), maps
the diameter, thickening and Lebesgue measure by the inverse dilation
(`chart_scaling_geometry`), transports the good set (`chart_scaling_good`), and transfers the
amount (`chart_scaling`), the upper size bound (`chart_scaling_upper`) and the diagonal closeness
(`chart_scaling_closeness`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff ENNReal Pointwise
namespace KAM.Planetary

section Jets

variable {n m : ℕ}

theorem p11_euclid_smul (t : ℝ) (x : P11Vec n) : p11euclid (t • x) = |t| * p11euclid x := by
  simp only [p11euclid, KAM.Nekhoroshev.euclid, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
    ← Finset.mul_sum, Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- The iterated derivative of an affine reparametrisation, on an open set. -/
theorem p11_iteratedFDeriv_affine {V : Set (P11Vec n)} (hV : IsOpen V)
    {f : P11Vec n → P11Vec m} {k : ℕ} (hf : ContDiffOn ℝ k f V) (y0 : P11Vec n)
    {lambda : ℝ} {j : ℕ} (hj : j ≤ k) {y : P11Vec n} (hy : y0 + lambda • y ∈ V)
    (a : Fin j → P11Vec n) :
    iteratedFDeriv ℝ j (fun x => f (y0 + lambda • x)) y a =
      lambda ^ j • iteratedFDeriv ℝ j f (y0 + lambda • y) a := by
  set L : P11Vec n →L[ℝ] P11Vec n := lambda • ContinuousLinearMap.id ℝ (P11Vec n) with hL
  have hLy : ∀ x, L x = lambda • x := fun x => by simp [hL]
  set V' : Set (P11Vec n) := (fun z => y0 + z) ⁻¹' V with hV'
  have hV'o : IsOpen V' := hV.preimage (continuous_const.add continuous_id)
  set g : P11Vec n → P11Vec m := fun z => f (y0 + z) with hg
  have hgd : ContDiffOn ℝ k g V' :=
    hf.comp (contDiffOn_const.add contDiffOn_id) (fun z hz => hz)
  have hLo : IsOpen (L ⁻¹' V') := hV'o.preimage L.continuous
  have hmem : L y ∈ V' := by simpa [hV', hLy] using hy
  have h1 := L.iteratedFDerivWithin_comp_right hgd hV'o.uniqueDiffOn hLo.uniqueDiffOn hmem (by exact_mod_cast hj)
  rw [iteratedFDerivWithin_of_isOpen j hLo (by simpa using hmem),
    iteratedFDerivWithin_of_isOpen j hV'o hmem] at h1
  have h2 : (fun x => f (y0 + lambda • x)) = g ∘ L := by
    funext x; simp [hg, hLy]
  rw [h2, h1]
  have h3 : iteratedFDeriv ℝ j g (lambda • y) = iteratedFDeriv ℝ j f (y0 + lambda • y) := by
    rw [hg, iteratedFDeriv_comp_add_left]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hLy, h3]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp

theorem p11_pow_le_max {lambda : ℝ} (hl : 0 < lambda) {j k : ℕ} (hj : j ≤ k) :
    lambda ^ j ≤ max 1 (lambda ^ k) := by
  rcases le_total lambda 1 with h | h
  · exact (pow_le_one₀ hl.le h).trans (le_max_left _ _)
  · exact (pow_le_pow_right₀ h hj).trans (le_max_right _ _)

theorem p11_min_le_pow {lambda : ℝ} (hl : 0 < lambda) {j k : ℕ} (hj : j ≤ k) :
    min 1 (lambda ^ k) ≤ lambda ^ j := by
  rcases le_total lambda 1 with h | h
  · exact (min_le_right _ _).trans (pow_le_pow_of_le_one hl.le h hj)
  · exact (min_le_left _ _).trans (one_le_pow₀ h)

theorem chart_scaling_jets {n m k : ℕ} (hn : 1 ≤ n)
    {V : Set (P11Vec n)} (hV : IsOpen V)
    {f : P11Vec n → P11Vec m} (hf : ContDiffOn ℝ k f V)
    (y0 : P11Vec n) {lambda : ℝ} (hl : 0 < lambda) :
    ∀ j ≤ k, ∀ y, y0+lambda • y ∈ V →
      p11dg (fun x => f (y0+lambda • x)) j y =
        lambda^j*p11dg f j (y0+lambda • y) ∧
      p11op (fun x => f (y0+lambda • x)) j y =
        lambda^j*p11op f j (y0+lambda • y) := by
  intro j hj y hy
  have hid := fun a => p11_iteratedFDeriv_affine hV hf y0 (lambda := lambda) hj hy a
  have heu : ∀ (v : P11Vec m), p11euclid (lambda ^ j • v) = lambda ^ j * p11euclid v := by
    intro v; rw [p11_euclid_smul, abs_of_nonneg (pow_nonneg hl.le _)]
  have e1 : ∀ a : Fin j → P11Vec n,
      p11euclid (iteratedFDeriv ℝ j (fun x => f (y0 + lambda • x)) y a) =
        lambda ^ j * p11euclid (iteratedFDeriv ℝ j f (y0 + lambda • y) a) := fun a => by
    rw [hid]; exact heu _
  have hlj : 0 ≤ lambda ^ j := pow_nonneg hl.le _
  constructor
  · obtain ⟨a, ha, h1⟩ := p11dg_attained (fun x => f (y0 + lambda • x)) j y hn
    obtain ⟨b, hb, h2⟩ := p11dg_attained f j (y0 + lambda • y) hn
    refine le_antisymm ?_ ?_
    · rw [h1, e1]
      exact mul_le_mul_of_nonneg_left (le_p11dg f j _ a ha) hlj
    · rw [h2, ← e1]
      exact le_p11dg (fun x => f (y0 + lambda • x)) j y b hb
  · obtain ⟨a, ha, h1⟩ := p11op_attained (fun x => f (y0 + lambda • x)) j y
    obtain ⟨b, hb, h2⟩ := p11op_attained f j (y0 + lambda • y)
    refine le_antisymm ?_ ?_
    · rw [h1, e1]
      exact mul_le_mul_of_nonneg_left (le_p11op f j _ a ha) hlj
    · rw [h2, ← e1]
      exact le_p11op (fun x => f (y0 + lambda • x)) j y b hb

theorem chart_scaling_upper {n m k : ℕ} (hn : 1 ≤ n)
    {V : Set (P11Vec n)} (hV : IsOpen V) {f : P11Vec n → P11Vec m}
    (hf : ContDiffOn ℝ k f V) {E : Set (P11Vec n)} (hEV : E ⊆ V)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ j, 1 ≤ j → j ≤ k → ∀ y ∈ E, p11op f j y ≤ M)
    (y0 : P11Vec n) {lambda : ℝ} (hl : 0 < lambda) :
    ∀ j, 1 ≤ j → j ≤ k → ∀ y, y0+lambda • y ∈ E →
      p11op (fun x => f (y0+lambda • x)) j y ≤ max 1 (lambda^k)*M := by
  intro j h1 hjk y hy
  rw [(chart_scaling_jets hn hV hf y0 hl j hjk y (hEV hy)).2]
  exact mul_le_mul (p11_pow_le_max hl hjk) (hb j h1 hjk _ hy) (p11op_nonneg _ _ _)
    (le_trans (by positivity) (p11_pow_le_max hl (Nat.zero_le k)))

theorem chart_scaling_closeness {n m mu : ℕ} (hn : 1 ≤ n)
    {V : Set (P11Vec n)} (hV : IsOpen V) {f : P11Vec n → P11Vec m}
    (hf : ContDiffOn ℝ mu f V) {E : Set (P11Vec n)} (hEV : E ⊆ V)
    {theta beta' : ℝ} (ht : 0 ≤ theta) (hb : p11JetBound true mu E f theta)
    (y0 : P11Vec n) {lambda : ℝ} (hl : 0 < lambda)
    (hrecheck : max 1 (lambda^mu)*theta ≤ beta'/2) :
    p11JetBound true mu ((fun y => y0+lambda • y) ⁻¹' E)
      (fun y => f (y0+lambda • y)) (beta'/2) := by
  intro j hj y hy
  simp only [if_true] at hb ⊢
  have hy' : y0 + lambda • y ∈ E := hy
  rw [(chart_scaling_jets hn hV hf y0 hl j hj y (hEV hy')).1]
  refine le_trans ?_ hrecheck
  exact mul_le_mul (p11_pow_le_max hl hj) (hb j hj _ hy') (p11dg_nonneg _ _ _)
    (le_trans (by positivity) (p11_pow_le_max hl (Nat.zero_le mu)))

end Jets

section Geometry

variable {n m : ℕ}

theorem p11_volume_affine {n : ℕ} (y0 : P11Vec n) {lambda : ℝ} (hl : 0 < lambda)
    (E : Set (P11Vec n)) :
    volume ((fun y : P11Vec n => y0 + lambda • y) ⁻¹' E) =
      ENNReal.ofReal (lambda ^ n)⁻¹ * volume E := by
  have : (fun y : P11Vec n => y0 + lambda • y) ⁻¹' E =
      (fun y : P11Vec n => lambda • y) ⁻¹' ((fun z => y0 + z) ⁻¹' E) := rfl
  rw [this, MeasureTheory.Measure.addHaar_preimage_smul volume hl.ne',
    measure_preimage_add]
  simp [abs_of_pos (pow_pos hl n)]

theorem chart_scaling_geometry {n : ℕ} (y0 : P11Vec n)
    {lambda : ℝ} (hl : 0 < lambda) (K : Set (P11Vec n))
    (hK : IsCompact K) (v : ℝ) :
    let A := fun y : P11Vec n => y0+lambda • y
    Metric.diam (A ⁻¹' K) = Metric.diam K/lambda ∧
    p11thick (A ⁻¹' K) (v/lambda) = A ⁻¹' p11thick K v ∧
    ∀ E : Set (P11Vec n),
      volume (A ⁻¹' E) = ENNReal.ofReal (lambda^n)⁻¹*volume E := by
  intro A
  refine ⟨?_, ?_, ?_⟩
  · have hset : A ⁻¹' K = lambda⁻¹ • ((fun z => -y0 + z) '' K) := by
      ext y
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hl.ne'), inv_inv]
      simp only [Set.mem_preimage, Set.mem_image, A]
      constructor
      · intro h; exact ⟨_, h, by abel⟩
      · rintro ⟨x, hx, h⟩
        have : x = y0 + lambda • y := by rw [← sub_eq_zero]; rw [← h]; abel
        rwa [← this]
    have hiso : Metric.diam ((fun z : P11Vec n => -y0 + z) '' K) = Metric.diam K :=
      (IsometryEquiv.addLeft (-y0)).isometry.diam_image K
    rw [hset, diam_smul₀, hiso, norm_inv, Real.norm_of_nonneg hl.le]
    ring
  · ext y
    simp only [p11thick, Set.mem_setOf_eq, Set.mem_preimage, A]
    have hsub : ∀ x, p11euclid (y0 + lambda • y - (y0 + lambda • x)) =
        lambda * p11euclid (y - x) := fun x => by
      have : y0 + lambda • y - (y0 + lambda • x) = lambda • (y - x) := by
        rw [smul_sub]; abel
      rw [this, p11_euclid_smul, abs_of_pos hl]
    constructor
    · rintro ⟨x, hx, h⟩
      refine ⟨_, hx, ?_⟩
      rw [hsub]; rwa [le_div_iff₀ hl, mul_comm] at h
    · rintro ⟨x', hx', h⟩
      refine ⟨lambda⁻¹ • (x' - y0), ?_, ?_⟩
      · simpa [smul_smul, hl.ne'] using hx'
      · have hx : y0 + lambda • (lambda⁻¹ • (x' - y0)) = x' := by
          rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul]; abel
        rw [← hx, hsub, mul_comm] at h
        rwa [le_div_iff₀ hl, mul_comm] at *
  · exact fun E => p11_volume_affine y0 hl E

theorem chart_scaling_good {n m : ℕ} (y0 : P11Vec n)
    {lambda : ℝ} (hl : 0 < lambda) (K : Set (P11Vec n))
    (wt : (Fin m → ℤ) → P11Vec n → P11Vec m)
    (psi : (Fin m → ℤ) → ℝ) :
    let A := fun y : P11Vec n => y0+lambda • y
    p11Good (A ⁻¹' K) (fun k y => wt k (A y)) psi =
      A ⁻¹' p11Good K wt psi ∧
    volume (K \ p11Good K wt psi) =
      ENNReal.ofReal (lambda^n)*
        volume ((A ⁻¹' K) \ p11Good (A ⁻¹' K) (fun k y => wt k (A y)) psi) := by
  intro A
  have h1 : p11Good (A ⁻¹' K) (fun k y => wt k (A y)) psi = A ⁻¹' p11Good K wt psi := rfl
  refine ⟨h1, ?_⟩
  have hd : (A ⁻¹' K) \ p11Good (A ⁻¹' K) (fun k y => wt k (A y)) psi =
      A ⁻¹' (K \ p11Good K wt psi) := by
    rw [h1, Set.preimage_diff]
  rw [hd, p11_volume_affine y0 hl, ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hl.le n),
    mul_inv_cancel₀ (pow_pos hl n).ne', ENNReal.ofReal_one, one_mul]

end Geometry

section Amount

variable {n m : ℕ}

theorem chart_scaling {n m rho mu : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    {K V : Set (P11Vec n)} (hK : IsCompact K) (hne : K.Nonempty) (hV : IsOpen V) (hKV : K ⊆ V)
    {w : P11Vec n → P11Vec m} (hw : ContDiffOn ℝ mu w V)
    (y0 : P11Vec n) {lambda : ℝ} (hl : 0 < lambda) :
    min 1 (lambda^mu)*index_def rho mu w K ≤
      index_def rho mu (fun y => w (y0+lambda • y)) ((fun y => y0+lambda • y) ⁻¹' K) := by
  have hne' : ((fun y : P11Vec n => y0 + lambda • y) ⁻¹' K).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨lambda⁻¹ • (x - y0), ?_⟩
    show y0 + lambda • (lambda⁻¹ • (x - y0)) ∈ K
    rwa [smul_smul, mul_inv_cancel₀ hl.ne', one_smul, add_sub_cancel]
  refine le_index_def hm rho mu _ hne' fun c hc y hy => ?_
  have hyK : y0 + lambda • y ∈ K := hy
  set F := p11scalar rho w c with hF
  have hFd : ContDiffOn ℝ mu F V := contDiffOn_p11scalar hw rho c
  obtain ⟨j, hj, hjeq⟩ := p11maxJet_attained (f := F) (y := y0 + lambda • y) mu
  have h1 : index_def rho mu w K ≤ p11maxJet mu F (y0 + lambda • y) :=
    index_def_le rho mu w hc hyK
  have h2 := (chart_scaling_jets hn hV hFd y0 hl j hj y (hKV hyK)).1
  have h3 : p11dg (fun x => F (y0 + lambda • x)) j y ≤
      p11maxJet mu (p11scalar rho (fun y => w (y0 + lambda • y)) c) y :=
    le_p11maxJet (f := p11scalar rho (fun y => w (y0 + lambda • y)) c) (y := y) mu hj
  have hmin := p11_min_le_pow hl hj
  have hnn : 0 ≤ index_def rho mu w K := index_def_nonneg _ _ _ _
  calc min 1 (lambda ^ mu) * index_def rho mu w K
      ≤ lambda ^ j * p11maxJet mu F (y0 + lambda • y) :=
        mul_le_mul hmin h1 hnn (pow_nonneg hl.le _)
    _ = lambda ^ j * p11dg F j (y0 + lambda • y) := by rw [hjeq]
    _ = p11dg (fun x => F (y0 + lambda • x)) j y := h2.symm
    _ ≤ _ := h3

end Amount

end KAM.Planetary
