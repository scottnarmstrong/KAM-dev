/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGMeasure.Setting
public import KAM.Planetary.PGMeasure.AffineSlab
public import KAM.Planetary.PGMeasure.LatticeTail

/-!
# P Part 4: slow resonances (`bpP:p4:beta-inverse`, `stepP:p4:dm-slow`)

`beta_inverse`: a quantitative inverse bound for the transpose of a matrix with entries
bounded by `M` and determinant at least `B` in absolute value, by the adjugate formula
(no symmetry is used). The slow resonances (`k_f = 0`, case `stepP:p4:dm-slow` of
`bpP:p4:two-scale-diophantine-measure`) are bounded by internal helpers: per-mode `affine_slab`
sections with the N3 lower bound, Tonelli over the fast actions, and the `lattice_tail` sum
(`slow_resonance_measure_le`, consumed by P4-M). Design
`docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P4-R0.
-/

public section

open Finset MeasureTheory Set

namespace KAM.Planetary

variable {a b n : ℕ}

/-- Hadamard-free determinant bound: `|det A| ≤ n! M^n` for entries bounded by `M`. -/
theorem abs_det_le_factorial_mul_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {M : ℝ} (hA : ∀ i j, |A i j| ≤ M) :
    |A.det| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * M ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ σ : Equiv.Perm ι, |(Equiv.Perm.sign σ : ℤ) • ∏ i, A (σ i) i| ≤ M ^ Fintype.card ι := by
    intro σ
    have hp : |∏ i, A (σ i) i| ≤ M ^ Fintype.card ι := by
      rw [abs_prod]
      calc ∏ i, |A (σ i) i| ≤ ∏ _i : ι, M :=
            by gcongr with i; exact hA _ _
        _ = M ^ Fintype.card ι := by simp
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simpa [h] using hp
  refine (Finset.sum_le_sum fun σ _ => h σ).trans ?_
  simp [Fintype.card_perm]

/-- Adjugate entries are bounded by `(b-1)! M^(b-1)`. -/
theorem abs_adjugate_le {m : ℕ} {A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ} {M : ℝ}
    (hA : ∀ i j, |A i j| ≤ M) (i j : Fin (m+1)) :
    |A.adjugate i j| ≤ (Nat.factorial m : ℝ) * M ^ m := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul]
  have := abs_det_le_factorial_mul_pow (A := A.submatrix j.succAbove i.succAbove)
    (fun p q => hA _ _)
  simpa using this

theorem beta_inverse (hb : 0 < b) {T : Matrix (Fin b) (Fin b) ℝ} {B M : ℝ}
    (hB : 0 < B) (hM : 0 ≤ M) (hdet : B ≤ |T.det|) (hentries : ∀ i j, |T i j| ≤ M) :
    ∀ v : Fin b → ℝ, ‖v‖ ≤ ((Nat.factorial b : ℝ)*M^(b-1)/B)*‖T.transpose.mulVec v‖ := by
  intro v
  obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
  set w := T.transpose.mulVec v with hw
  have hdetT : |T.transpose.det| = |T.det| := by rw [Matrix.det_transpose]
  have hv : ∀ i, T.det * v i = (T.transpose.adjugate.mulVec w) i := by
    intro i
    have : T.transpose.adjugate.mulVec w = T.transpose.det • v := by
      rw [hw, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [this]; simp [Matrix.det_transpose]
  have hentT : ∀ i j, |T.transpose i j| ≤ M := fun i j => hentries j i
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have hcoef : 0 ≤ (Nat.factorial (m+1) : ℝ) * M ^ (m+1-1) / B := by positivity
  have hdetpos : 0 < |T.det| := lt_of_lt_of_le hB hdet
  have key : ∀ i, |T.det| * |v i| ≤ (Nat.factorial (m+1) : ℝ) * M ^ (m+1-1) * ‖w‖ := by
    intro i
    rw [← abs_mul, hv i, Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |T.transpose.adjugate i j * w j|
        ≤ ∑ _j : Fin (m+1), (Nat.factorial m : ℝ) * M ^ m * ‖w‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul (abs_adjugate_le hentT i j) (by simpa using norm_le_pi_norm w j)
            (abs_nonneg _) (by positivity)
      _ = (Nat.factorial (m+1) : ℝ) * M ^ (m+1-1) * ‖w‖ := by
          simp [Nat.factorial_succ]; ring
  rw [div_mul_eq_mul_div]
  refine (pi_norm_le_iff_of_nonneg (r := (Nat.factorial (m+1) : ℝ) * M ^ (m+1-1) * ‖w‖ / B)
    (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs, le_div_iff₀ hB]
  have h1 : B * |v i| ≤ |T.det| * |v i| := mul_le_mul_of_nonneg_right hdet (abs_nonneg _)
  nlinarith [key i]


/-- Concatenation `ℝᵃ × ℝᵇ ≃ ℝ^(a+b)` as a measurable equivalence. -/
def appendEquivAB (a b : ℕ) : (Fin a → ℝ) × (Fin b → ℝ) ≃ᵐ (Fin (a + b) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (a + b) => ℝ) finSumFinEquiv)

theorem appendEquivAB_apply (p : (Fin a → ℝ) × (Fin b → ℝ)) :
    appendEquivAB a b p = Fin.append p.1 p.2 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [appendEquivAB, MeasurableEquiv.trans_apply, MeasurableEquiv.coe_piCongrLeft,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm, Fin.append_left]
    rw [← finSumFinEquiv_apply_left, Equiv.piCongrLeft_apply_apply]
    rfl
  · simp only [appendEquivAB, MeasurableEquiv.trans_apply, MeasurableEquiv.coe_piCongrLeft,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm, Fin.append_right]
    rw [← finSumFinEquiv_apply_right, Equiv.piCongrLeft_apply_apply]
    rfl

theorem measurePreserving_appendEquivAB (a b : ℕ) :
    MeasurePreserving (appendEquivAB a b) volume volume :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin (a + b) => ℝ) finSumFinEquiv).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin a ⊕ Fin b => ℝ))

/-- The volume of a set of joint actions is the volume of the set of its `(I, ξ)` splittings. -/
theorem volume_eq_volume_append_preimage (S : Set (Fin (a + b) → ℝ)) :
    volume S = volume {p : (Fin a → ℝ) × (Fin b → ℝ) | Fin.append p.1 p.2 ∈ S} := by
  have := (measurePreserving_appendEquivAB a b).measure_preimage_equiv S
  rw [← this]
  congr 1
  ext p
  simp [appendEquivAB_apply]

/-- Tonelli over the fast variable with `ℝᵇ`-valued sections. -/
theorem volume_prod_le_of_sections {R : Set ((Fin a → ℝ) × (Fin b → ℝ))} (hR : MeasurableSet R)
    {P : Set (Fin a → ℝ)} (hP : MeasurableSet P) (hsub : R ⊆ P ×ˢ univ) {δ : ENNReal}
    (hsec : ∀ I ∈ P, volume {ξ : Fin b → ℝ | (I, ξ) ∈ R} ≤ δ) :
    volume R ≤ δ * volume P := by
  rw [Measure.volume_eq_prod, Measure.prod_apply hR]
  calc ∫⁻ x, (volume : Measure (Fin b → ℝ)) (Prod.mk x ⁻¹' R) ∂(volume : Measure (Fin a → ℝ))
      ≤ ∫⁻ x, P.indicator (fun _ => δ) x ∂(volume : Measure (Fin a → ℝ)) := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ P
        · rw [Set.indicator_of_mem hx]; exact hsec x hx
        · have : Prod.mk x ⁻¹' R = ∅ := by
            ext t
            simp only [Set.mem_preimage, mem_empty_iff_false, iff_false]
            intro ht
            exact hx (hsub ht).1
          simp [this, hx]
    _ = δ * volume P := by
        rw [lintegral_indicator hP]
        simp


/-! ### The slow-mode sum -/

theorem blockFast_append (I : Fin a → ℝ) (xi : Fin b → ℝ) : blockFast (Fin.append I xi) = I := by
  funext i; simp [blockFast, Fin.append_left]

theorem blockSlow_append (I : Fin a → ℝ) (xi : Fin b → ℝ) : blockSlow (Fin.append I xi) = xi := by
  funext i; simp [blockSlow, Fin.append_right]

theorem sum_append_zero_mul_freq (H0 : (Fin a → ℝ) → ℝ) (P0 : ℝ → (Fin a → ℝ) → ℝ)
    (Omega : ℝ → (Fin a → ℝ) → Fin b → ℝ)
    (beta : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ) (mu : ℝ) (ks : Fin b → ℤ)
    (I : Fin a → ℝ) (xi : Fin b → ℝ) :
    ∑ i, ((Fin.append (0 : Fin a → ℤ) ks i : ℤ) : ℝ) *
        freq H0 P0 Omega beta mu (Fin.append I xi) i =
      mu * ∑ j, (ks j : ℝ) * slowFrequency Omega beta mu I xi j := by
  rw [Fin.sum_univ_add, Finset.mul_sum]
  simp [freq, blockFast_append, blockSlow_append, Fin.append_left, Fin.append_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sum_abs_append_zero (ks : Fin b → ℤ) :
    ∑ i, |((Fin.append (0 : Fin a → ℤ) ks i : ℤ) : ℝ)| = ∑ j, |(ks j : ℝ)| := by
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem dot_slowFrequency (Omega : ℝ → (Fin a → ℝ) → Fin b → ℝ)
    (beta : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ) (mu : ℝ) (ks : Fin b → ℤ)
    (I : Fin a → ℝ) (xi : Fin b → ℝ) :
    ∑ j, (ks j : ℝ) * slowFrequency Omega beta mu I xi j =
      ∑ j, ((beta mu I).transpose.mulVec (fun j => (ks j : ℝ))) j * xi j +
        ∑ j, (ks j : ℝ) * Omega mu I j := by
  have h1 : ∑ j, (ks j : ℝ) * slowFrequency Omega beta mu I xi j =
      (fun j => (ks j : ℝ)) ⬝ᵥ (Omega mu I + (beta mu I).mulVec xi) := rfl
  rw [h1, dotProduct_add, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, add_comm]
  rfl


/-! ### Continuity and measurability of the slow-mode set -/

theorem slowFrequency_continuousOn_core (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1)
    {w : Fin b → ℝ} (hw : ‖w‖ ≤ d.lambda0) :
    ContinuousOn (fun I => slowFrequency d.Omega d.beta mu I w) d.core := by
  have hLip : LipschitzOnWith ⟨d.LN, by linarith [d.hLN]⟩
      (fun I => slowFrequency d.Omega d.beta mu I w) d.core := by
    refine LipschitzOnWith.of_dist_le_mul fun I hI I' hI' => ?_
    rw [dist_eq_norm, dist_eq_norm]
    exact (d.N1 mu hmu I hI I' hI' w hw).2
  exact hLip.continuousOn

theorem slowFrequency_expand (Omega : ℝ → (Fin a → ℝ) → Fin b → ℝ)
    (beta : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ) (mu : ℝ) {l0 : ℝ} (hl0 : 0 < l0)
    (I : Fin a → ℝ) (xi : Fin b → ℝ) :
    slowFrequency Omega beta mu I xi = slowFrequency Omega beta mu I 0 +
      ∑ j, (xi j / l0) • (slowFrequency Omega beta mu I (l0 • Pi.single j 1) -
        slowFrequency Omega beta mu I 0) := by
  funext m
  simp only [slowFrequency, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply,
    Matrix.mulVec_zero, Matrix.mulVec_smul, smul_eq_mul]
  have : ∀ j, (xi j / l0) * (l0 * (beta mu I).mulVec (Pi.single j 1) m) =
      xi j * beta mu I m j := by
    intro j
    have : (beta mu I).mulVec (Pi.single j 1) m = beta mu I m j := by
      simp
    rw [this]; field_simp
  have h2 : ∀ x, xi x / l0 * (Omega mu I m + l0 * (beta mu I).mulVec (Pi.single x 1) m -
      (Omega mu I m + (0 : Fin b → ℝ) m)) = xi x * beta mu I m x := by
    intro x
    rw [← this x]; simp
  rw [Finset.sum_congr rfl fun x _ => h2 x]
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, add_zero]
  congr 1
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _


theorem slow_dot_continuousOn (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1)
    (ks : Fin b → ℤ) :
    ContinuousOn (fun p : (Fin a → ℝ) × (Fin b → ℝ) =>
      ∑ j, (ks j : ℝ) * slowFrequency d.Omega d.beta mu p.1 p.2 j) (d.core ×ˢ Set.univ) := by
  have hl0 := d.hlambda0
  have hmaps : MapsTo Prod.fst (d.core ×ˢ (Set.univ : Set (Fin b → ℝ))) d.core := fun p hp => hp.1
  have h0 : ContinuousOn (fun p : (Fin a → ℝ) × (Fin b → ℝ) =>
      slowFrequency d.Omega d.beta mu p.1 0) (d.core ×ˢ Set.univ) :=
    (slowFrequency_continuousOn_core d hmu (w := 0) (by simp [hl0.le])).comp
      continuousOn_fst hmaps
  have h1 : ∀ i : Fin b, ContinuousOn (fun p : (Fin a → ℝ) × (Fin b → ℝ) =>
      slowFrequency d.Omega d.beta mu p.1 (d.lambda0 • Pi.single i 1)) (d.core ×ˢ Set.univ) := by
    intro i
    refine (slowFrequency_continuousOn_core d hmu (w := d.lambda0 • Pi.single i 1) ?_).comp
      continuousOn_fst hmaps
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl0, Pi.norm_single, norm_one, mul_one]
  have hV : ContinuousOn (fun p : (Fin a → ℝ) × (Fin b → ℝ) =>
      slowFrequency d.Omega d.beta mu p.1 p.2) (d.core ×ˢ Set.univ) := by
    have : (fun p : (Fin a → ℝ) × (Fin b → ℝ) => slowFrequency d.Omega d.beta mu p.1 p.2) =
        fun p => slowFrequency d.Omega d.beta mu p.1 0 +
          ∑ i, (p.2 i / d.lambda0) • (slowFrequency d.Omega d.beta mu p.1
            (d.lambda0 • Pi.single i 1) - slowFrequency d.Omega d.beta mu p.1 0) :=
      funext fun p => slowFrequency_expand d.Omega d.beta mu hl0 p.1 p.2
    rw [this]
    refine h0.add (continuousOn_finsetSum _ fun i _ => ?_)
    have hc : ContinuousOn (fun p : (Fin a → ℝ) × (Fin b → ℝ) => p.2 i / d.lambda0)
        (d.core ×ˢ Set.univ) :=
      (((continuous_apply i).comp continuous_snd).div_const _).continuousOn
    exact hc.smul ((h1 i).sub h0)
  have hlin : Continuous fun v : Fin b → ℝ => ∑ j, (ks j : ℝ) * v j := by fun_prop
  exact hlin.comp_continuousOn hV

theorem measurableSet_slow_mode (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1)
    (ks : Fin b → ℤ) (eps : ℝ) {Q : Set (Fin b → ℝ)} (hQ : MeasurableSet Q) :
    MeasurableSet {p : (Fin a → ℝ) × (Fin b → ℝ) | p.1 ∈ d.core ∧ p.2 ∈ Q ∧
      |∑ j, (ks j : ℝ) * slowFrequency d.Omega d.beta mu p.1 p.2 j| < eps} := by
  have hs : MeasurableSet (d.core ×ˢ (Set.univ : Set (Fin b → ℝ))) :=
    d.hcore.isClosed.measurableSet.prod MeasurableSet.univ
  obtain ⟨t, ht, hteq⟩ := (continuousOn_iff'.1 (slow_dot_continuousOn d hmu ks)) (Ioo (-eps) eps)
    isOpen_Ioo
  have : {p : (Fin a → ℝ) × (Fin b → ℝ) | p.1 ∈ d.core ∧ p.2 ∈ Q ∧
      |∑ j, (ks j : ℝ) * slowFrequency d.Omega d.beta mu p.1 p.2 j| < eps} =
      (t ∩ (d.core ×ˢ Set.univ)) ∩ Prod.snd ⁻¹' Q := by
    rw [← hteq]
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ,
      and_true, Set.mem_Ioo, abs_lt]
    tauto
  rw [this]
  exact (ht.measurableSet.inter hs).inter (measurable_snd hQ)


/-! ### One slow mode -/

theorem slow_section_measure_le (d : MeasureData a b) {lambda mu eps : ℝ} (hl : 0 < lambda)
    (hmu : mu ∈ Ioc 0 d.mu1) (he : 0 < eps) {ks : Fin b → ℤ} (hks : ks ≠ 0) {I : Fin a → ℝ}
    (hI : I ∈ d.core) {Q : Set (Fin b → ℝ)} (hQsub : Q ⊆ actionShell b (-lambda) lambda) :
    volume {xi : Fin b → ℝ | xi ∈ Q ∧
      |∑ j, (ks j : ℝ) * slowFrequency d.Omega d.beta mu I xi j| < eps} ≤
      ENNReal.ofReal (2*eps*(2*lambda)^(b-1)*(b*d.LB)/∑ j, |(ks j : ℝ)|) := by
  set kv : Fin b → ℝ := fun j => (ks j : ℝ) with hkv
  set W : ℝ := ∑ j, |(ks j : ℝ)| with hWdef
  obtain ⟨j0, hj0⟩ : ∃ j, ks j ≠ 0 := by
    simpa [Function.ne_iff] using hks
  have hbpos : (0 : ℝ) < b := by exact_mod_cast d.hb
  have hLBpos : 0 < d.LB := by linarith [d.hLB]
  have hWpos : 0 < W := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun j => |(ks j : ℝ)|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ j0))
    simpa using hj0
  have hWle : W ≤ b * ‖kv‖ := by
    calc W ≤ ∑ _j : Fin b, ‖kv‖ := Finset.sum_le_sum fun j _ => by
          simpa [hkv] using norm_le_pi_norm kv j
      _ = b * ‖kv‖ := by simp
  set ell : Fin b → ℝ := (d.beta mu I).transpose.mulVec kv with hell
  have hN3 : ‖kv‖ ≤ d.LB * ‖ell‖ := d.N3 mu hmu I hI kv
  have hellW : W / (b * d.LB) ≤ ‖ell‖ := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hellpos : 0 < ‖ell‖ := lt_of_lt_of_le (by positivity) hellW
  have hne : ell ≠ 0 := norm_pos_iff.mp hellpos
  have hsub : {xi : Fin b → ℝ | xi ∈ Q ∧
      |∑ j, (ks j : ℝ) * slowFrequency d.Omega d.beta mu I xi j| < eps} ⊆
      {xi : Fin b → ℝ | (∀ i, xi i ∈ Icc (-lambda) lambda) ∧
        |∑ i, ell i * xi i + ∑ j, kv j * d.Omega mu I j| < eps} := by
    intro xi ⟨hxQ, hxe⟩
    refine ⟨fun i => ?_, ?_⟩
    · have := hQsub hxQ i (Set.mem_univ i)
      exact ⟨this.1.le, this.2.le⟩
    · rw [dot_slowFrequency] at hxe
      exact hxe
  refine (measure_mono hsub).trans ?_
  refine (affine_slab d.hb ell hne _ lambda eps hl he).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have h2 : 0 ≤ 2*eps*(2*lambda)^(b-1) := by positivity
  calc 2*eps*(2*lambda)^(b-1) / ‖ell‖ ≤ 2*eps*(2*lambda)^(b-1) / (W / (b * d.LB)) :=
        div_le_div_of_nonneg_left h2 (by positivity) hellW
    _ = 2*eps*(2*lambda)^(b-1)*(b*d.LB)/W := by field_simp

theorem slow_mode_measure_le (d : MeasureData a b) {lambda mu alpha : ℝ} (hl : 0 < lambda)
    (hl0 : lambda ≤ d.lambda0) (hmu : mu ∈ Ioc 0 d.mu1) (ha : 0 < alpha)
    {Q : Set (Fin b → ℝ)} (hQ : MeasurableSet Q) (hQsub : Q ⊆ actionShell b (-lambda) lambda)
    {ks : Fin b → ℤ} (hks : ks ≠ 0) :
    volume {J : Fin (a+b) → ℝ | J ∈ joinedActions d.core Q ∧
      |∑ i, ((Fin.append (0 : Fin a → ℤ) ks i : ℤ) : ℝ) * freq d.H0 d.P0 d.Omega d.beta mu J i| <
        alpha / (∑ i, |((Fin.append (0 : Fin a → ℤ) ks i : ℤ) : ℝ)|) ^ d.tau} ≤
      ENNReal.ofReal (2*(alpha/mu)*(b*d.LB)*(2*lambda)^(b-1)*latticeWeight (d.tau+1) ks) *
        volume d.core := by
  have _ := hl0
  set W : ℝ := ∑ j, |(ks j : ℝ)| with hWdef
  obtain ⟨j0, hj0⟩ : ∃ j, ks j ≠ 0 := by
    simpa [Function.ne_iff] using hks
  have hWpos : 0 < W := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun j => |(ks j : ℝ)|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ j0))
    simpa using hj0
  set eps : ℝ := alpha / mu / W ^ d.tau with heps
  have hmu0 : 0 < mu := hmu.1
  have he : 0 < eps := by positivity
  rw [volume_eq_volume_append_preimage]
  set T : Set ((Fin a → ℝ) × (Fin b → ℝ)) := {p | p.1 ∈ d.core ∧ p.2 ∈ Q ∧
    |∑ j, (ks j : ℝ) * slowFrequency d.Omega d.beta mu p.1 p.2 j| < eps} with hT
  have hsub : {p : (Fin a → ℝ) × (Fin b → ℝ) | Fin.append p.1 p.2 ∈
      {J : Fin (a+b) → ℝ | J ∈ joinedActions d.core Q ∧
      |∑ i, ((Fin.append (0 : Fin a → ℤ) ks i : ℤ) : ℝ) * freq d.H0 d.P0 d.Omega d.beta mu J i| <
        alpha / (∑ i, |((Fin.append (0 : Fin a → ℤ) ks i : ℤ) : ℝ)|) ^ d.tau}} ⊆ T := by
    rintro p ⟨⟨h1, h2⟩, h3⟩
    simp only [blockFast_append, blockSlow_append] at h1 h2
    rw [sum_append_zero_mul_freq, sum_abs_append_zero, abs_mul, abs_of_pos hmu0,
      ← hWdef] at h3
    refine ⟨h1, h2, ?_⟩
    have : |∑ j, (ks j : ℝ) * slowFrequency d.Omega d.beta mu p.1 p.2 j| < alpha / W ^ d.tau / mu
      := by
      rw [lt_div_iff₀ hmu0, mul_comm]; exact h3
    rw [heps, div_right_comm]; exact this
  refine (measure_mono hsub).trans ?_
  have hmain := volume_prod_le_of_sections (measurableSet_slow_mode d hmu ks eps hQ)
    d.hcore.isClosed.measurableSet
    (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
    (δ := ENNReal.ofReal (2*eps*(2*lambda)^(b-1)*(b*d.LB)/W))
    (fun I hI => by
      refine le_trans (measure_mono ?_) (slow_section_measure_le d hl hmu he hks hI hQsub)
      intro xi hxi
      exact ⟨hxi.2.1, hxi.2.2⟩)
  refine hmain.trans (le_of_eq ?_)
  congr 2
  have hlw : latticeWeight (d.tau + 1) ks = (W ^ d.tau * W)⁻¹ := by
    unfold latticeWeight
    rw [Real.rpow_neg hWpos.le, Real.rpow_add_one hWpos.ne']
  rw [hlw, heps]
  field_simp


/-! ### The slow resonances: sum over modes and the lattice sum -/

theorem eq_append_zero_of_blockFast_eq_zero {k : Fin (a+b) → ℤ} (hk : blockFast k = 0) :
    k = Fin.append (0 : Fin a → ℤ) (blockSlow k) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    have := congrFun hk j
    simpa [blockFast] using this
  · rw [Fin.append_right]; rfl

/-- Blueprint `stepP:p4:dm-slow` (the case `k_f = 0`), internal helper for the signed
`two_scale_diophantine_measure`: the union over the slow modes of the slow resonance sets has
measure at most the first-case term of the proposition. -/
theorem slow_resonance_measure_le (d : MeasureData a b) {lambda mu alpha2 : ℝ} (hl : 0 < lambda)
    (hl0 : lambda ≤ d.lambda0) (hmu : mu ∈ Ioc 0 d.mu1) (ha2 : 0 < alpha2)
    {Q : Set (Fin b → ℝ)} (hQ : MeasurableSet Q) (hQsub : Q ⊆ actionShell b (-lambda) lambda) :
    volume {J : Fin (a+b) → ℝ | J ∈ joinedActions d.core Q ∧
      ∃ k : Fin (a+b) → ℤ, k ≠ 0 ∧ blockFast k = 0 ∧
        |∑ i, (k i : ℝ) * freq d.H0 d.P0 d.Omega d.beta mu J i| <
          alpha2 / (∑ i, |(k i : ℝ)|) ^ d.tau} ≤
      ENNReal.ofReal (b * d.LB * latticeS b (d.tau+1) * (alpha2/mu) / lambda) *
        volume d.core * ENNReal.ofReal ((2*lambda)^b) := by
  have hmu0 : 0 < mu := hmu.1
  have hbpos : (0 : ℝ) < b := by exact_mod_cast d.hb
  have hLBpos : 0 < d.LB := by linarith [d.hLB]
  have htau : (b : ℝ) < d.tau + 1 := by
    have := d.htau
    have h2 : ((a + b : ℕ) : ℝ) = a + b := by push_cast; ring
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  obtain ⟨hsum, hbound, -⟩ := lattice_tail d.hb htau
  set K : ℝ := 2*(alpha2/mu)*(b*d.LB)*(2*lambda)^(b-1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hsub : {J : Fin (a+b) → ℝ | J ∈ joinedActions d.core Q ∧
      ∃ k : Fin (a+b) → ℤ, k ≠ 0 ∧ blockFast k = 0 ∧
        |∑ i, (k i : ℝ) * freq d.H0 d.P0 d.Omega d.beta mu J i| <
          alpha2 / (∑ i, |(k i : ℝ)|) ^ d.tau} ⊆
      ⋃ ks : {ks : Fin b → ℤ // ks ≠ 0},
        {J : Fin (a+b) → ℝ | J ∈ joinedActions d.core Q ∧
          |∑ i, ((Fin.append (0 : Fin a → ℤ) ks.val i : ℤ) : ℝ) *
            freq d.H0 d.P0 d.Omega d.beta mu J i| <
            alpha2 / (∑ i, |((Fin.append (0 : Fin a → ℤ) ks.val i : ℤ) : ℝ)|) ^ d.tau} := by
    rintro J ⟨hJ, k, hk0, hkf, hlt⟩
    have hk := eq_append_zero_of_blockFast_eq_zero hkf
    have hks : blockSlow k ≠ 0 := by
      intro h; apply hk0; rw [hk, h]; funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    refine Set.mem_iUnion.2 ⟨⟨blockSlow k, hks⟩, hJ, ?_⟩
    rw [← hk]; exact hlt
  have hmode : ∀ ks : {ks : Fin b → ℤ // ks ≠ 0},
      volume {J : Fin (a+b) → ℝ | J ∈ joinedActions d.core Q ∧
          |∑ i, ((Fin.append (0 : Fin a → ℤ) ks.val i : ℤ) : ℝ) *
            freq d.H0 d.P0 d.Omega d.beta mu J i| <
            alpha2 / (∑ i, |((Fin.append (0 : Fin a → ℤ) ks.val i : ℤ) : ℝ)|) ^ d.tau} ≤
        ENNReal.ofReal (K * latticeWeight (d.tau+1) ks.val) * volume d.core :=
    fun ks => slow_mode_measure_le d hl hl0 hmu ha2 hQ hQsub ks.2
  have hlw0 : ∀ ks : Fin b → ℤ, 0 ≤ latticeWeight (d.tau+1) ks := fun ks =>
    Real.rpow_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) _
  have hsum' : Summable fun ks : {ks : Fin b → ℤ // ks ≠ 0} => K * latticeWeight (d.tau+1) ks.val :=
    hsum.mul_left K
  calc _ ≤ volume (⋃ ks : {ks : Fin b → ℤ // ks ≠ 0}, _) := measure_mono hsub
    _ ≤ ∑' ks : {ks : Fin b → ℤ // ks ≠ 0},
        ENNReal.ofReal (K * latticeWeight (d.tau+1) ks.val) * volume d.core :=
        (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hmode)
    _ = ENNReal.ofReal (∑' ks : {ks : Fin b → ℤ // ks ≠ 0},
          K * latticeWeight (d.tau+1) ks.val) * volume d.core := by
        rw [ENNReal.tsum_mul_right,
          ENNReal.ofReal_tsum_of_nonneg (fun ks => mul_nonneg hK0 (hlw0 _)) hsum']
    _ ≤ ENNReal.ofReal (K * latticeS b (d.tau+1)) * volume d.core := by
        gcongr
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left hbound hK0
    _ = _ := by
        obtain ⟨m, hm⟩ : ∃ m, b = m + 1 := ⟨b - 1, by have := d.hb; omega⟩
        have hY : 0 ≤ (2*lambda)^b := by positivity
        have : K * latticeS b (d.tau+1) =
            (2*lambda)^b * (b * d.LB * latticeS b (d.tau+1) * (alpha2/mu) / lambda) := by
          rw [hK]
          have hb1 : b - 1 = m := by omega
          rw [hb1]
          have : (2*lambda)^b = (2*lambda)^m * (2*lambda) := by rw [hm, pow_succ]
          rw [this]
          field_simp
        rw [this, ENNReal.ofReal_mul hY]
        ring

end KAM.Planetary
