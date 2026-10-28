/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.AveragingDom
public import KAM.Strip.Cohomological

/-!
# P Part 5: the normalized perturbation, its weighted bound and zero mode (`stepP:p5:av-id`)

`pg_osc_bound` (the unit weighted bound of `pgOscP`) and `pg_osc_zero` (its zero Fourier
coefficient is the actual `complexAverage` over the physical period `2π`).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-AV.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped Pointwise

namespace KAM.Planetary

variable {a b n : ℕ} {d : PGData a b} {r mu : ℝ}

theorem torusCoeff_const_mul {m : ℕ} (c : ℂ) (v : (Fin m → ℝ) → ℂ) (k : Fin m → ℤ) :
    KAM.torusCoeff (fun x => c * v x) k = c * KAM.torusCoeff v k := by
  unfold KAM.torusCoeff KAM.torusAverage
  have : ∀ x : Fin m → ℝ, KAM.character (-k) (fun j => (x j : ℂ)) * (c * v x) =
      c * (KAM.character (-k) (fun j => (x j : ℂ)) * v x) := fun x => by ring
  simp_rw [this]
  exact MeasureTheory.integral_const_mul c _

theorem oscUnpack_flat (θ : Fin a → ℂ) (I : Fin a → ℂ) (p q : Fin b → ℂ) :
    oscUnpack (θ, Fin.append I (Fin.append p q)) = assembleComplex I θ p q := by
  refine Prod.ext ?_ ?_
  · show Fin.append θ (lastBlock (a := b) (lastBlock (a := a) (Fin.append I (Fin.append p q)))) = _
    have : lastBlock (a := b) (lastBlock (a := a) (Fin.append I (Fin.append p q))) = q := by
      show blockSlow (blockSlow (Fin.append I (Fin.append p q))) = q
      rw [pgAv_blockSlow_append, pgAv_blockSlow_append]
    rw [this]; rfl
  · show Fin.append (firstBlock (b := b + b) (Fin.append I (Fin.append p q)))
      (firstBlock (b := b) (lastBlock (a := a) (Fin.append I (Fin.append p q)))) = _
    have h1 : firstBlock (b := b + b) (Fin.append I (Fin.append p q)) = I :=
      pgAv_blockFast_append _ _
    have h2 : firstBlock (b := b) (lastBlock (a := a) (Fin.append I (Fin.append p q))) = p := by
      show blockFast (blockSlow (Fin.append I (Fin.append p q))) = p
      rw [pgAv_blockSlow_append, pgAv_blockFast_append]
    rw [h1, h2]; rfl

theorem normalize_assemble (I θ : Fin a → ℂ) (p q : Fin b → ℂ) :
    pgOscNormalize (assembleComplex I θ p q) =
      assembleComplex I ((2*Real.pi:ℂ) • θ) ((Real.sqrt (2*Real.pi):ℂ) • p)
        ((Real.sqrt (2*Real.pi):ℂ) • q) := by
  simp only [pgOscNormalize, assembleComplex, pgAv_blockFast_append, pgAv_blockSlow_append]

theorem realInclusion_smul (c : ℝ) (θ : Fin a → ℝ) :
    (c:ℂ) • KAM.realInclusion a θ = KAM.realInclusion a (c • θ) := by
  ext i; simp

theorem torusCoeff_pgOscP (d : PGData a b) (mu : ℝ) (I : Fin a → ℂ) (p q : Fin b → ℂ)
    (k : Fin a → ℤ) :
    KAM.Weighted.coeff (oscFunction (pgOscP d mu)) (Fin.append I (Fin.append p q)) k =
      KAM.torusCoeff (fun θ : Fin a → ℝ => (pgExtension d).P mu
        (assembleComplex I ((2*Real.pi:ℂ) • KAM.realInclusion a θ)
          ((Real.sqrt (2*Real.pi):ℂ) • p) ((Real.sqrt (2*Real.pi):ℂ) • q))) k /
        (pgAnalytic d).LP := by
  unfold KAM.Weighted.coeff
  rw [KAM.torusCoeffW_complex]
  have : ∀ θ : Fin a → ℝ, oscFunction (pgOscP d mu)
      ((fun j => (θ j : ℂ)), Fin.append I (Fin.append p q)) =
      ((pgAnalytic d).LP : ℂ)⁻¹ * (pgExtension d).P mu
        (assembleComplex I ((2*Real.pi:ℂ) • KAM.realInclusion a θ)
          ((Real.sqrt (2*Real.pi):ℂ) • p) ((Real.sqrt (2*Real.pi):ℂ) • q)) := by
    intro θ
    simp only [oscFunction, Function.comp, pgOscP]
    rw [show (fun j => (θ j : ℂ)) = KAM.realInclusion a θ from rfl, oscUnpack_flat,
      normalize_assemble, div_eq_inv_mul]
  simp_rw [this]
  rw [torusCoeff_const_mul, div_eq_inv_mul]

/-- The weighted bound for the extension on the physical torus, with the constant `LP`. -/
theorem pg_P_torus_bound {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {I : Fin a → ℂ}
    (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2)) {x : PGComplexPhase b}
    (hx : ‖x‖ < (pgExtension d).delta/4) :
    KAM.Fourier.SummableWeighted (pgWidth d)
      (KAM.torusCoeff (fun phi => (pgExtension d).P mu
        (assembleComplex I ((2*Real.pi:ℂ) • KAM.realInclusion a phi) x.2 x.1))) ∧
    KAM.Fourier.weightedNorm (pgWidth d)
      (KAM.torusCoeff (fun phi => (pgExtension d).P mu
        (assembleComplex I ((2*Real.pi:ℂ) • KAM.realInclusion a phi) x.2 x.1))) ≤
      (pgAnalytic d).LP := by
  obtain ⟨h1, h2⟩ := (pgExtension d).summable_torus hmu hI hx
  refine ⟨h1, h2.trans ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hLP, -⟩ := pgAnalytic_spec d
  have hpi := Real.pi_pos
  have e : Real.pi * ((pgExtension d).delta / (4 * Real.pi)) = (pgExtension d).delta / 4 := by
    field_simp
  rw [e, mul_comm]
  exact hLP

theorem actionNbhd_checkedCore_le (h : admissible d (pgRstar d) r mu) {s t : ℝ}
    (hs : s ≤ t) :
    KAM.actionNbhd (checkedCore d r mu) s ⊆ KAM.actionNbhd (closure d.V) t := by
  intro I hI
  obtain ⟨J, hJ, hIJ⟩ := hI
  exact ⟨J, subset_closure (checkedCore_subset_V d r mu hJ), hIJ.trans_le hs⟩

theorem modeWeight_osc (d : PGData a b) (k : Fin a → ℤ) :
    KAM.Weighted.modeWeight (pgOscWidth d) k = Real.exp (pgWidth d * KAM.Fourier.modeSize k) := by
  unfold KAM.Weighted.modeWeight pgOscWidth
  have := Real.pi_pos
  congr 1
  field_simp

theorem pg_osc_bound (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    oscBound (checkedCore d r mu) (params d r mu).rhoBar (pgOscEpsilon d) (pgOscEpsilon d)
      (pgOscWidth d) (pgOscP d mu) 1 := by
  intro x hx
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hxe : x = Fin.append (firstBlock (b := b + b) x) (Fin.append
      (firstBlock (b := b) (lastBlock (a := a) x))
      (lastBlock (a := b) (lastBlock (a := a) x))) := by
    have := append_blocks x
    have h2 := append_blocks (lastBlock (a := a) x)
    rw [show Fin.append (firstBlock (b := b) (lastBlock (a := a) x))
      (lastBlock (a := b) (lastBlock (a := a) x)) = lastBlock (a := a) x from h2]
    exact this.symm
  set I := firstBlock (b := b + b) x
  set p := firstBlock (b := b) (lastBlock (a := a) x)
  set q := lastBlock (a := b) (lastBlock (a := a) x)
  have hmu := av_mu_mem h
  have hs := sqrt_two_pi_pos
  have hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2) :=
    actionNbhd_checkedCore_le h (by linarith [av_rhoBar_lt_delta h, (pgExtension d).delta_pos]) hx1
  have hnorm : ‖((Real.sqrt (2*Real.pi):ℂ) • q, (Real.sqrt (2*Real.pi):ℂ) • p)‖ <
      (pgExtension d).delta/4 := by
    rw [Prod.norm_def]
    refine max_lt ?_ ?_
    · rw [norm_real_smul_lt_iff hs]
      refine lt_of_lt_of_le hx3 ?_
      unfold pgOscEpsilon
      rw [div_le_div_iff_of_pos_right hs]
      exact pgOscRadius_le_delta d
    · rw [norm_real_smul_lt_iff hs]
      refine lt_of_lt_of_le hx2 ?_
      unfold pgOscEpsilon
      rw [div_le_div_iff_of_pos_right hs]
      exact pgOscRadius_le_delta d
  obtain ⟨hS, hN⟩ := pg_P_torus_bound hmu hI hnorm
  have hLP := pgAnalytic_LP_ge_one d
  have hLP0 : 0 < (pgAnalytic d).LP := by linarith
  have hc : ∀ k, ‖KAM.Weighted.coeff (oscFunction (pgOscP d mu)) x k‖ *
      KAM.Weighted.modeWeight (pgOscWidth d) k =
      (‖KAM.torusCoeff (fun phi => (pgExtension d).P mu
        (assembleComplex I ((2*Real.pi:ℂ) • KAM.realInclusion a phi)
          ((Real.sqrt (2*Real.pi):ℂ) • p) ((Real.sqrt (2*Real.pi):ℂ) • q))) k‖ *
        Real.exp (pgWidth d * KAM.Fourier.modeSize k)) / (pgAnalytic d).LP := by
    intro k
    rw [hxe, torusCoeff_pgOscP, modeWeight_osc, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hLP0]
    ring
  have hsum : KAM.Weighted.WSummable (oscFunction (pgOscP d mu)) (pgOscWidth d) x := by
    unfold KAM.Weighted.WSummable
    simp_rw [hc]
    exact hS.div_const _
  refine ⟨hsum, ?_⟩
  unfold KAM.Weighted.wsum
  simp_rw [hc]
  rw [tsum_div_const, div_le_one hLP0]
  exact hN

theorem pg_osc_zero (d : PGData a b) (mu : ℝ) (hmu : mu ∈ Icc 0 d.mu0)
    (z : CPhase (a+b))
    (hz : z ∈ oscDom (closure d.V) ((pgExtension d).delta/2)
      (pgOscEpsilon d) (pgOscEpsilon d) (pgOscWidth d)) :
    KAM.Weighted.coeff (oscFunction (pgOscP d mu)) (oscPack z).2 0 =
      complexAverage d mu (blockFast z.2)
        ((Real.sqrt (2*Real.pi):ℂ) • blockSlow z.1,
         (Real.sqrt (2*Real.pi):ℂ) • blockSlow z.2)/(pgAnalytic d).LP := by
  have hpi := Real.pi_pos
  have hpack : (oscPack z).2 = Fin.append (blockFast z.2)
      (Fin.append (blockSlow z.2) (blockSlow z.1)) := rfl
  rw [hpack, torusCoeff_pgOscP, KAM.torusCoeff_zero]
  congr 1
  unfold KAM.torusAverage complexAverage
  have key := MeasureTheory.Measure.setIntegral_comp_smul_of_pos
    (MeasureTheory.volume : Measure (Fin a → ℝ))
    (fun φ : Fin a → ℝ => (pgExtension d).P mu (assembleComplex (blockFast z.2)
      (KAM.realInclusion a φ) ((Real.sqrt (2*Real.pi):ℂ) • blockSlow z.2)
      ((Real.sqrt (2*Real.pi):ℂ) • blockSlow z.1)))
    (Set.pi Set.univ fun _ : Fin a => Icc (0:ℝ) 1) (show (0:ℝ) < 2*Real.pi by positivity)
  have h0 : (0:ℝ) < 2*Real.pi := by positivity
  have hc : ∀ x : Fin a → ℝ, (2*(Real.pi:ℂ)) • KAM.realInclusion a x =
      KAM.realInclusion a ((2*Real.pi) • x) := fun x => by
    ext i; simp [Complex.ofReal_mul]
  have hset : (2*Real.pi) • (Set.pi Set.univ fun _ : Fin a => Icc (0:ℝ) 1) =
      Set.pi Set.univ fun _ : Fin a => Icc (0:ℝ) (2*Real.pi) := by
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem₀ h0.ne', Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc, Pi.smul_apply, smul_eq_mul]
    refine forall_congr' fun i => ?_
    rw [inv_mul_le_iff₀ h0, mul_nonneg_iff_of_pos_left (inv_pos.2 h0), mul_one]
  simp_rw [hc]
  rw [key, hset, Module.finrank_fin_fun, Complex.real_smul]
  push_cast
  rfl

end KAM.Planetary

end
