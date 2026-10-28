/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGMeasure.ResonanceLarge.Frequency

/-!
# P Part 4: Borel measurability of the resonant sets (`bpP:p4:two-scale-diophantine-measure`)

The Borelness of `ℛ_k` in the proof of the two-scale measure estimate comes from the Lipschitz
premises `N1`, `N2` and the Lipschitz inverse `g` (not from an extra assumption): on the slice
domain `{z | blockFast z ∈ ω(core), blockSlow z ∈ Q}` the function `pullFreq d μ k` and the slow
column coefficients `y ↦ (β(g y)ᵀ v)_j` are continuous, and the domain is Borel since `ω(core)` is
compact. Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P4-RB.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Finset

namespace KAM.Planetary

variable {a b : ℕ}

/-- The slice domain `ω(core) × Q` in flat coordinates. -/
def sliceDomain (d : MeasureData a b) (Q : Set (Fin b → ℝ)) : Set (Fin (a+b) → ℝ) :=
  {z | blockFast z ∈ freqCore d ∧ blockSlow z ∈ Q}

theorem continuous_blockFast : Continuous (fun z : Fin (a+b) → ℝ => blockFast z) :=
  continuous_pi fun _ => continuous_apply _

theorem continuous_blockSlow : Continuous (fun z : Fin (a+b) → ℝ => blockSlow z) :=
  continuous_pi fun _ => continuous_apply _

theorem continuousOn_fastFrequency (d : MeasureData a b) :
    ContinuousOn (fastFrequency d.H0) d.W := by
  have hc : ContDiffOn ℝ ⊤ d.H0 d.W := d.hfreq.1.contDiffOn_of_completeSpace
  have h1 := hc.continuousOn_fderiv_of_isOpen d.hW (by simp)
  exact continuousOn_pi.2 fun i => h1.clm_apply continuousOn_const

theorem isCompact_freqCore (d : MeasureData a b) : IsCompact (freqCore d) :=
  d.hcore.image_of_continuousOn
    ((continuousOn_fastFrequency d).mono fun _ hI => d.hVW (subset_closure (d.hcoreV hI)))

theorem measurableSet_sliceDomain (d : MeasureData a b) {Q : Set (Fin b → ℝ)}
    (hQ : MeasurableSet Q) : MeasurableSet (sliceDomain d Q) :=
  ((isCompact_freqCore d).isClosed.measurableSet.preimage continuous_blockFast.measurable).inter
    (hQ.preimage continuous_blockSlow.measurable)

theorem measurableSet_inter_preimage {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {S : Set X} (hS : MeasurableSet S) {f : X → ℝ}
    (hf : ContinuousOn f S) {T : Set ℝ} (hT : MeasurableSet T) :
    MeasurableSet (S ∩ f ⁻¹' T) := by
  have h1 : Continuous (S.domRestrict f) := hf.domRestrict
  have h2 : MeasurableSet (S.domRestrict f ⁻¹' T) := h1.measurable hT
  have := hS.subtype_image h2
  convert this using 1
  ext x
  simp [Set.domRestrict, and_comm]

/-- `y ↦ g y` followed by a slow coefficient is continuous on the frequency image. -/
theorem continuousOn_beta_entry (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1)
    (i j : Fin b) : ContinuousOn (fun y => d.beta mu (d.g y) i j) (freqCore d) := by
  refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (2 * d.LN * d.Lg / d.lambda0))
    fun y hy y' hy' => ?_).continuousOn
  have hpos : 0 ≤ 2 * d.LN * d.Lg / d.lambda0 :=
    div_nonneg (by nlinarith [d.hLN, d.hLg]) d.hlambda0.le
  rw [Real.coe_toNNReal _ hpos, Real.dist_eq, dist_eq_norm]
  exact beta_lip_y d hmu hy hy' i j

theorem continuousOn_slowFrequency (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1)
    (i : Fin b) : ContinuousOn (fun z : Fin (a+b) → ℝ =>
      slowFrequency d.Omega d.beta mu (d.g (blockFast z)) (blockSlow z) i) (sliceDomain d univ) := by
  have hO : ContinuousOn (fun y => d.Omega mu (d.g y) i) (freqCore d) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (d.LN * d.Lg)) fun y hy y' hy' => ?_).continuousOn
    rw [Real.coe_toNNReal _ (by nlinarith [d.hLN, d.hLg]), Real.dist_eq]
    have h0 : ‖(0 : Fin b → ℝ)‖ ≤ d.lambda0 := by simpa using d.hlambda0.le
    have := (norm_le_pi_norm (slowFrequency d.Omega d.beta mu (d.g y) 0 -
      slowFrequency d.Omega d.beta mu (d.g y') 0) i).trans (slow_lip_y d hmu hy hy' h0)
    simpa [slowFrequency, Real.norm_eq_abs, dist_eq_norm] using this
  have hfun : (fun z : Fin (a+b) → ℝ =>
      slowFrequency d.Omega d.beta mu (d.g (blockFast z)) (blockSlow z) i) = fun z =>
      d.Omega mu (d.g (blockFast z)) i + ∑ j, d.beta mu (d.g (blockFast z)) i j * blockSlow z j := by
    funext z
    simp [slowFrequency, Matrix.mulVec, dotProduct]
  rw [hfun]
  have hmaps : MapsTo (fun z : Fin (a+b) → ℝ => blockFast z) (sliceDomain d univ) (freqCore d) :=
    fun z hz => hz.1
  refine (hO.comp continuous_blockFast.continuousOn hmaps).add ?_
  refine continuousOn_finsetSum _ fun j _ => ?_
  exact ((continuousOn_beta_entry d hmu i j).comp continuous_blockFast.continuousOn hmaps).mul
    (continuous_apply _ |>.comp continuous_blockSlow).continuousOn

theorem continuousOn_fastPart (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1)
    {Q : Set (Fin b → ℝ)} (hQ : ∀ xi ∈ Q, ‖xi‖ ≤ d.lambda0) (i : Fin a) :
    ContinuousOn (fun z : Fin (a+b) → ℝ =>
      fastPart d mu (d.g (blockFast z)) (blockSlow z) i) (sliceDomain d Q) := by
  have hmu0 := hmu.1
  have hK : 0 ≤ 1 + mu * d.LN * d.Lg + mu * d.LN := by
    have : 0 < mu * d.LN * d.Lg := by have := d.hLN; have := d.hLg; positivity
    have : 0 < mu * d.LN := by have := d.hLN; positivity
    linarith
  have hK1 : 0 ≤ 1 + mu * d.LN * d.Lg := by
    have : 0 < mu * d.LN * d.Lg := by have := d.hLN; have := d.hLg; positivity
    linarith
  have hlip : LipschitzOnWith (Real.toNNReal (1 + mu * d.LN * d.Lg + mu * d.LN))
      (fun z : Fin (a+b) → ℝ => fastPart d mu (d.g (blockFast z)) (blockSlow z))
      (sliceDomain d Q) := by
    refine LipschitzOnWith.of_dist_le_mul fun z hz z' hz' => ?_
    rw [Real.coe_toNNReal _ hK, dist_eq_norm, dist_eq_norm]
    have h1 := fast_lip_y d hmu hz.1 hz'.1 (hQ _ hz.2)
    have h2 := fast_lip_xi d hmu (freqCore_spec d hz'.1).1 (hQ _ hz.2) (hQ _ hz'.2)
    have h3 : ‖blockFast z - blockFast z'‖ ≤ ‖z - z'‖ := norm_blockFast_le (z - z')
    have h4 : ‖blockSlow z - blockSlow z'‖ ≤ ‖z - z'‖ := norm_blockSlow_le (z - z')
    have h5 : mu * d.LN * ‖blockSlow z - blockSlow z'‖ ≤ mu * d.LN * ‖z - z'‖ :=
      mul_le_mul_of_nonneg_left h4 (by nlinarith [d.hLN])
    have h6 : (1 + mu * d.LN * d.Lg) * ‖blockFast z - blockFast z'‖ ≤
        (1 + mu * d.LN * d.Lg) * ‖z - z'‖ :=
      mul_le_mul_of_nonneg_left h3 hK1
    calc _ = ‖(fastPart d mu (d.g (blockFast z)) (blockSlow z) -
            fastPart d mu (d.g (blockFast z')) (blockSlow z)) +
            (fastPart d mu (d.g (blockFast z')) (blockSlow z) -
            fastPart d mu (d.g (blockFast z')) (blockSlow z'))‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (by nlinarith)
  exact (continuous_apply i).comp_continuousOn hlip.continuousOn

theorem continuousOn_pullFreq (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1)
    {Q : Set (Fin b → ℝ)} (hQ : ∀ xi ∈ Q, ‖xi‖ ≤ d.lambda0) (k : Fin (a+b) → ℤ) :
    ContinuousOn (pullFreq d mu k) (sliceDomain d Q) := by
  have hfun : pullFreq d mu k = fun z => ∑ i, kFast k i * fastPart d mu (d.g (blockFast z))
      (blockSlow z) i + mu * ∑ i, kSlow k i *
        slowFrequency d.Omega d.beta mu (d.g (blockFast z)) (blockSlow z) i := funext (pullFreq_eq d mu k)
  rw [hfun]
  refine (continuousOn_finsetSum _ fun i _ => (continuousOn_const.mul
    (continuousOn_fastPart d hmu hQ i))).add (continuousOn_const.mul
    (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ?_))
  exact (continuousOn_slowFrequency d hmu i).mono fun z hz => ⟨hz.1, mem_univ _⟩

/-- The `j`-th slow column coefficient `(β(μ, g y)ᵀ v)_j` at the flat point `z = (y, ξ)`. -/
def colCoeff (d : MeasureData a b) (mu : ℝ) (v : Fin b → ℝ) (j : Fin b) (z : Fin (a+b) → ℝ) : ℝ :=
  ∑ i, d.beta mu (d.g (blockFast z)) i j * v i

theorem colCoeff_eq (d : MeasureData a b) (mu : ℝ) (v : Fin b → ℝ) (j : Fin b)
    (z : Fin (a+b) → ℝ) :
    colCoeff d mu v j z = ((d.beta mu (d.g (blockFast z))).transpose.mulVec v) j := by
  simp [colCoeff, Matrix.mulVec, dotProduct]

theorem continuousOn_colCoeff (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1)
    (v : Fin b → ℝ) (j : Fin b) : ContinuousOn (colCoeff d mu v j) (sliceDomain d univ) :=
  continuousOn_finsetSum _ fun i _ =>
    ((continuousOn_beta_entry d hmu i j).comp continuous_blockFast.continuousOn
      fun z hz => hz.1).mul continuousOn_const

end KAM.Planetary

end
