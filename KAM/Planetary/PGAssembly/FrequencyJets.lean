/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.AnalyticTaylor
public import KAM.Planetary.PGAssembly.Remainder
public import KAM.Planetary.PGAssembly.FrequencyDefs

/-!
# P Part 5: radius-2 bounds for the jet polynomial (`stepP:p5:fd-bd`)

Uniform bounds in `mu ∈ [0, mu0]` for the jets `jetP0`, `jetOmega`, `jetBeta` on the tube of
radius `δ/2` (from the extension bound and Cauchy estimates, as in the remainder), the polynomial
bound for `jetPolynomial` on `|J₂| ≤ s`, and the Cauchy estimates for `jetPolynomial` and its first
two derivatives on `analyticBoundDomain`-type domains of fast radius `δ/16` (the constant
`jpBound d`). Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-FD.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology
open scoped BigOperators

namespace KAM.Planetary

variable {a b : ℕ}

/-- Uniform bound of the order-two jet `jetOmega`. -/
def jetK2 (d : PGData a b) : ℝ := (2 / (pgOscRadius d / 2)) ^ 2 * (pgExtension d).MP

/-- Uniform bound of the order-four jet `jetBeta`. -/
def jetK4 (d : PGData a b) : ℝ := (4 / (pgOscRadius d / 2)) ^ 4 * (pgExtension d).MP

theorem jetK2_nonneg (d : PGData a b) : 0 ≤ jetK2 d := by
  have := (pgExtension d).MP_pos
  unfold jetK2; positivity

theorem jetK4_nonneg (d : PGData a b) : 0 ≤ jetK4 d := by
  have := (pgExtension d).MP_pos
  unfold jetK4; positivity

theorem jetP0_norm_le (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {I : Fin a → ℂ}
    (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) :
    ‖jetP0 d mu I‖ ≤ (pgExtension d).MP :=
  complexAverage_norm_le d hmu (z := (I, (0 : PGComplexPhase b))) (mem_avgDom_zero d hI)

theorem jetOmega_norm_le (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {I : Fin a → ℂ}
    (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) (j : Fin b) :
    ‖jetOmega d mu I j‖ ≤ jetK2 d := by
  have h := jet_norm_le d hmu hI 2
  refine (mlin_apply_le _ _ fun _ => norm_yvec_le_one j).trans ?_
  simpa [jetK2] using h

theorem jetBeta_norm_le (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {I : Fin a → ℂ}
    (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) (i j : Fin b) :
    ‖jetBeta d mu I i j‖ ≤ jetK4 d := by
  have h := jet_norm_le d hmu hI 4
  have h' : ‖iteratedFDeriv ℂ 4 (complexAverage d mu I) 0‖ ≤ jetK4 d := by
    simpa [jetK4] using h
  unfold jetBeta
  by_cases hij : i = j
  · simp only [hij, ite_true]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans
      ((mlin_apply_le _ _ fun _ => norm_yvec_le_one j).trans h')
  · simp only [hij, ite_false]
    exact (mlin_apply_le _ _ fun k => by
      by_cases hk : k.val < 2 <;> simp only [hk, ite_true, ite_false] <;>
        [exact norm_yvec_le_one i; exact norm_yvec_le_one j]).trans h'

/-- Polynomial bound for `jetPolynomial` on `‖J₂‖ ≤ s`. -/
def jpPoly (d : PGData a b) (s : ℝ) : ℝ :=
  (pgExtension d).MP + b * jetK2 d * s + b ^ 2 * jetK4 d * s ^ 2

theorem jpPoly_mono (d : PGData a b) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    jpPoly d s ≤ jpPoly d t := by
  have h2 := jetK2_nonneg d
  have h4 := jetK4_nonneg d
  unfold jpPoly
  gcongr

theorem jpPoly_nonneg (d : PGData a b) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ jpPoly d s := by
  have h2 := jetK2_nonneg d
  have h4 := jetK4_nonneg d
  have := (pgExtension d).MP_pos
  unfold jpPoly; positivity

theorem norm_blockSlow_le {J : Fin (a + b) → ℂ} {s : ℝ} (hs : ‖blockSlow J‖ ≤ s) (j : Fin b) :
    ‖blockSlow J j‖ ≤ s := (norm_le_pi_norm (blockSlow J) j).trans hs

theorem jetPolynomial_norm_le (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {J : Fin (a + b) → ℂ}
    (hJ : blockFast J ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) {s : ℝ}
    (hs : ‖blockSlow J‖ ≤ s) : ‖jetPolynomial d mu J‖ ≤ jpPoly d s := by
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hs
  have hS1 : ‖∑ j, jetOmega d mu (blockFast J) j * blockSlow J j‖ ≤ b * jetK2 d * s := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖jetOmega d mu (blockFast J) j * blockSlow J j‖ ≤ ∑ _j : Fin b, jetK2 d * s :=
          Finset.sum_le_sum fun j _ => by
            rw [norm_mul]
            exact mul_le_mul (jetOmega_norm_le d hmu hJ j) (norm_blockSlow_le hs j)
              (norm_nonneg _) (jetK2_nonneg d)
      _ = b * jetK2 d * s := by simp; ring
  have hS2 : ‖(1 / 2 : ℂ) * ∑ i, ∑ j, jetBeta d mu (blockFast J) i j * blockSlow J i *
      blockSlow J j‖ ≤ b ^ 2 * jetK4 d * s ^ 2 := by
    have hn : ‖∑ i, ∑ j, jetBeta d mu (blockFast J) i j * blockSlow J i * blockSlow J j‖ ≤
        b ^ 2 * jetK4 d * s ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i, ‖∑ j, jetBeta d mu (blockFast J) i j * blockSlow J i * blockSlow J j‖
          ≤ ∑ _i : Fin b, (b * (jetK4 d * s ^ 2) : ℝ) := Finset.sum_le_sum fun i _ => by
            refine (norm_sum_le _ _).trans ?_
            calc ∑ j, ‖jetBeta d mu (blockFast J) i j * blockSlow J i * blockSlow J j‖
                ≤ ∑ _j : Fin b, jetK4 d * s ^ 2 := Finset.sum_le_sum fun j _ => by
                  rw [norm_mul, norm_mul, sq]
                  have h1 := jetBeta_norm_le d hmu hJ i j
                  have h2 := norm_blockSlow_le hs i
                  have h3 := norm_blockSlow_le hs j
                  have h4 := jetK4_nonneg d
                  calc _ ≤ jetK4 d * s * s := by gcongr
                    _ = jetK4 d * (s * s) := by ring
              _ = b * (jetK4 d * s ^ 2) := by simp
        _ = b ^ 2 * jetK4 d * s ^ 2 := by simp; ring
    have h12 : ‖(1 / 2 : ℂ)‖ ≤ 1 := by norm_num
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) h12).trans hn
  unfold jetPolynomial jpPoly
  calc _ ≤ ‖jetP0 d mu (blockFast J) + ∑ j, jetOmega d mu (blockFast J) j * blockSlow J j‖ +
        ‖(1 / 2 : ℂ) * ∑ i, ∑ j, jetBeta d mu (blockFast J) i j * blockSlow J i *
          blockSlow J j‖ := norm_add_le _ _
    _ ≤ (‖jetP0 d mu (blockFast J)‖ + ‖∑ j, jetOmega d mu (blockFast J) j * blockSlow J j‖) + _ :=
        by gcongr; exact norm_add_le _ _
    _ ≤ _ := by linarith [jetP0_norm_le d hmu hJ]

theorem differentiable_blockSlow_apply (j : Fin b) :
    Differentiable ℂ (fun J : Fin (a + b) → ℂ => blockSlow J j) :=
  differentiable_apply _

theorem differentiable_blockFast : Differentiable ℂ (fun J : Fin (a + b) → ℂ => blockFast J) :=
  differentiable_pi.2 fun _ => differentiable_apply _

/-- The open domain of the jet polynomial: fast action in the `δ/2`-tube, any slow action. -/
def jpDom (d : PGData a b) : Set (Fin (a + b) → ℂ) :=
  {J | blockFast J ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)}

theorem isOpen_jpDom (d : PGData a b) : IsOpen (jpDom d) :=
  (isOpen_actionNbhd _ _).preimage differentiable_blockFast.continuous

theorem jetPolynomial_differentiableOn (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) :
    DifferentiableOn ℂ (jetPolynomial d mu) (jpDom d) := by
  have hmaps : MapsTo (fun J : Fin (a + b) → ℂ => blockFast J) (jpDom d)
      (KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) := fun J hJ => hJ
  have hF : DifferentiableOn ℂ (fun J : Fin (a + b) → ℂ => blockFast J) (jpDom d) :=
    differentiable_blockFast.differentiableOn
  have h0 : DifferentiableOn ℂ (fun J : Fin (a + b) → ℂ => jetP0 d mu (blockFast J))
      (jpDom d) := (jetP0_differentiableOn d hmu).comp hF hmaps
  have h1 : ∀ j, DifferentiableOn ℂ (fun J : Fin (a + b) → ℂ => jetOmega d mu (blockFast J) j)
      (jpDom d) := fun j => ((jetOmega_differentiableOn d hmu j).comp hF hmaps)
  have h2 : ∀ i j, DifferentiableOn ℂ
      (fun J : Fin (a + b) → ℂ => jetBeta d mu (blockFast J) i j) (jpDom d) :=
    fun i j => ((jetBeta_differentiableOn d hmu i j).comp hF hmaps)
  unfold jetPolynomial
  refine DifferentiableOn.add (DifferentiableOn.add h0 ?_) ?_
  · exact DifferentiableOn.fun_sum fun j _ =>
      (h1 j).mul (differentiable_blockSlow_apply j).differentiableOn
  · refine (differentiableOn_const _).mul (DifferentiableOn.fun_sum fun i _ => ?_)
    exact DifferentiableOn.fun_sum fun j _ =>
      ((h2 i j).mul (differentiable_blockSlow_apply i).differentiableOn).mul
        (differentiable_blockSlow_apply j).differentiableOn

theorem norm_blockFast_sub_le (J K : Fin (a + b) → ℂ) : ‖blockFast K - blockFast J‖ ≤ ‖K - J‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    (norm_le_pi_norm (K - J) (Fin.castAdd b i))

theorem norm_blockSlow_sub_le (J K : Fin (a + b) → ℂ) : ‖blockSlow K - blockSlow J‖ ≤ ‖K - J‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    (norm_le_pi_norm (K - J) (Fin.natAdd a i))

theorem blockFast_mem_of_close {X : Set (Fin a → ℝ)} {s t : ℝ} {J K : Fin (a + b) → ℂ}
    (hJ : blockFast J ∈ KAM.actionNbhd X s) (hK : ‖K - J‖ ≤ t) :
    blockFast K ∈ KAM.actionNbhd X (s + t) := by
  obtain ⟨x, hx, hlt⟩ := hJ
  refine ⟨x, hx, ?_⟩
  calc ‖blockFast K - (fun i => (x i : ℂ))‖
      = ‖(blockFast K - blockFast J) + (blockFast J - (fun i => (x i : ℂ)))‖ := by
        congr 1; abel
    _ ≤ ‖blockFast K - blockFast J‖ + ‖blockFast J - (fun i => (x i : ℂ))‖ := norm_add_le _ _
    _ < s + t := by linarith [norm_blockFast_sub_le J K]

/-- Radius of the Cauchy polydiscs. -/
def jpRadius (d : PGData a b) : ℝ := (pgExtension d).delta / 8

theorem jpRadius_pos (d : PGData a b) : 0 < jpRadius d := by
  have := (pgExtension d).delta_pos
  unfold jpRadius; positivity

/-- Sup of the jet polynomial on the Cauchy polydiscs (slow radius `≤ 3`). -/
def jpSup (d : PGData a b) : ℝ := jpPoly d 3

/-- Common bound of the polynomial, its first and its second derivative. -/
def jpBound (d : PGData a b) : ℝ :=
  1 + jpSup d + jpSup d / jpRadius d + (2 / jpRadius d) ^ 2 * jpSup d

theorem jpBound_ge_one (d : PGData a b) : 1 ≤ jpBound d := by
  have h1 : 0 ≤ jpSup d := jpPoly_nonneg d (by norm_num)
  have h2 := jpRadius_pos d
  unfold jpBound
  have : 0 ≤ jpSup d / jpRadius d := by positivity
  have : 0 ≤ (2 / jpRadius d) ^ 2 * jpSup d := by positivity
  linarith

theorem jetPolynomial_ball_bound (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {J : Fin (a + b) → ℂ}
    (hJ : blockFast J ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 16))
    (hs : ‖blockSlow J‖ < 2) :
    closedBall J (jpRadius d) ⊆ jpDom d ∧
      ∀ K ∈ closedBall J (jpRadius d), ‖jetPolynomial d mu K‖ ≤ jpSup d := by
  have hδ := (pgExtension d).delta_pos
  have hδ1 := (pgExtension d).delta_lt
  have hK : ∀ K ∈ closedBall J (jpRadius d), K ∈ jpDom d ∧ ‖blockSlow K‖ ≤ 3 := by
    intro K hKb
    rw [mem_closedBall_iff_norm] at hKb
    refine ⟨?_, ?_⟩
    · have := blockFast_mem_of_close (X := closure d.V) (K := K) hJ hKb
      refine mem_actionNbhd_mono ?_ this
      unfold jpRadius; linarith
    · have h1 := norm_blockSlow_sub_le J K
      have h2 : ‖blockSlow K‖ ≤ ‖blockSlow K - blockSlow J‖ + ‖blockSlow J‖ := by
        calc ‖blockSlow K‖ = ‖(blockSlow K - blockSlow J) + blockSlow J‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      unfold jpRadius at hKb
      linarith
  exact ⟨fun K hKb => (hK K hKb).1, fun K hKb =>
    jetPolynomial_norm_le d hmu (hK K hKb).1 (hK K hKb).2⟩

theorem jetPolynomial_derivs_bound (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {J : Fin (a + b) → ℂ}
    (hJ : blockFast J ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 16))
    (hs : ‖blockSlow J‖ < 2) :
    ‖jetPolynomial d mu J‖ ≤ jpBound d ∧ ‖fderiv ℂ (jetPolynomial d mu) J‖ ≤ jpBound d ∧
      ‖fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) J‖ ≤ jpBound d := by
  obtain ⟨hsub, hb⟩ := jetPolynomial_ball_bound d hmu hJ hs
  have hr := jpRadius_pos d
  have hS : 0 ≤ jpSup d := jpPoly_nonneg d (by norm_num)
  have hdiff := jetPolynomial_differentiableOn d hmu
  have c1 := KAM.norm_iteratedFDeriv_le_of_closedBall (isOpen_jpDom d) hdiff hr hsub hb 1
  have c2 := KAM.norm_iteratedFDeriv_le_of_closedBall (isOpen_jpDom d) hdiff hr hsub hb 2
  have hJ0 : ‖jetPolynomial d mu J‖ ≤ jpSup d := hb J (mem_closedBall_self hr.le)
  have e1 : ‖fderiv ℂ (jetPolynomial d mu) J‖ = ‖iteratedFDeriv ℂ 1 (jetPolynomial d mu) J‖ :=
    (norm_iteratedFDeriv_one _).symm
  have e2 : ‖fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) J‖ =
      ‖iteratedFDeriv ℂ 2 (jetPolynomial d mu) J‖ := by
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  have t1 : 0 ≤ jpSup d / jpRadius d := by positivity
  have t2 : 0 ≤ (2 / jpRadius d) ^ 2 * jpSup d := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold jpBound; linarith
  · rw [e1]
    refine c1.trans ?_
    unfold jpBound
    have : ((1:ℕ) / jpRadius d) ^ 1 * jpSup d = jpSup d / jpRadius d := by
      push_cast; ring
    rw [this]; linarith
  · rw [e2]
    refine c2.trans ?_
    unfold jpBound
    have : (((2:ℕ):ℝ) / jpRadius d) ^ 2 * jpSup d = (2 / jpRadius d) ^ 2 * jpSup d := by
      push_cast; ring
    rw [this]; linarith

end KAM.Planetary

end
