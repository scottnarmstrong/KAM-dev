/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Patch
public import KAM.Planetary.WeakMeasure.PowerLaw
public import KAM.Planetary.WeakMeasure.Bridge
public import KAM.Planetary.WeakMeasure.Stability
public import KAM.Frozen.Planetary.Defs.Fast
public import KAM.Frozen.Planetary.Defs.Slow
public import KAM.Frozen.Defs.IsDiophantine

/-!
# The base point (P11A-P1, `bpP:p11:select`)

`select`: the patch `p11PatchData D` contains an interior point `J₀` whose frequency vector
`varpi J₀` and its fast and slow blocks are `(γ, τ)`-Diophantine, `τ = max (n μ) (2n)`; no
Diophantine point is assumed. The proof cuts are local: `sel-hyp` is the verification of the
hypotheses of `power_law` for the constant family `wt k = varpi` (the size bound is a compactness
bound, `bp_jet_bound`, fed to `M_bound`), `sel-gam` the choice of `γ` and the measure estimate
`vol (K \ H_γ) ≤ ε`, and `sel-int` the observation that the boundary of `K` is null, so the good
set `H_γ` meets the interior.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

section BasePoint

variable {n m : ℕ}

/-- Compactness bound for the operator gauge of the jets of a smooth map. -/
private theorem bp_jet_bound {V A : Set (P11Vec n)} (hV : IsOpen V) (hA : IsCompact A)
    (hAV : A ⊆ V) {w : P11Vec n → P11Vec m} {k : ℕ} (hw : ContDiffOn ℝ k w V) (j : ℕ)
    (hj : j ≤ k) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ A, p11op w j y ≤ B := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ j w) V :=
    ContinuousOn.continuousOn_iteratedFDeriv hw hV (by exact_mod_cast hj)
  have hBc : IsCompact
      (Set.pi (Set.univ : Set (Fin j)) fun _ => {a : P11Vec n | p11euclid a ≤ 1}) :=
    isCompact_univ_pi fun _ => p11ball_isCompact
  have hF : ContinuousOn (fun p : P11Vec n × (Fin j → P11Vec n) =>
      p11euclid (iteratedFDeriv ℝ j w p.1 p.2))
      (A ×ˢ Set.pi (Set.univ : Set (Fin j)) fun _ => {a : P11Vec n | p11euclid a ≤ 1}) := by
    refine p11euclid_continuous.comp_continuousOn ?_
    refine ContinuousOn.eval ?_ continuousOn_snd
    exact (hcont.mono hAV).comp continuousOn_fst (fun p hp => hp.1)
  obtain ⟨C, hC⟩ := (hA.prod hBc).exists_bound_of_continuousOn hF
  refine ⟨max C 0, le_max_right _ _, fun y hy => ?_⟩
  unfold p11op
  refine Real.sSup_le ?_ (le_max_right _ _)
  rintro v ⟨a, ha, rfl⟩
  have := hC (y, a) ⟨hy, fun i _ => ha i⟩
  rw [Real.norm_of_nonneg (p11euclid_nonneg _)] at this
  exact this.trans (le_max_left _ _)

private theorem bp_jet_bound_all {V A : Set (P11Vec n)} (hV : IsOpen V) (hA : IsCompact A)
    (hAV : A ⊆ V) {w : P11Vec n → P11Vec m} {k : ℕ} (hw : ContDiffOn ℝ k w V) :
    ∃ M : ℝ, 0 ≤ M ∧ p11JetBound false k A w M := by
  have : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ (j ≤ k → ∀ y ∈ A, p11op w j y ≤ B) := fun j => by
    by_cases hj : j ≤ k
    · obtain ⟨B, hB, h⟩ := bp_jet_bound hV hA hAV hw j hj
      exact ⟨B, hB, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => absurd h hj⟩
  choose B hB0 hB using this
  refine ⟨∑ j ∈ Finset.range (k + 1), B j, Finset.sum_nonneg fun j _ => hB0 j,
    fun j hj y hy => ?_⟩
  rw [if_neg Bool.false_ne_true]
  exact (hB j hj y hy).trans (Finset.single_le_sum (f := B) (fun j _ => hB0 j)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))

private theorem bp_dio_of_good {K : Set (P11Vec n)} {gamma tau : ℝ} {J : P11Vec m}
    {w : P11Vec n → P11Vec m} {y : P11Vec n} (hw : w y = J)
    (hy : y ∈ p11Good K (fun _ => w) (fun k => gamma * KAM.Fourier.modeSize k ^ (-tau))) :
    KAM.IsDiophantine gamma tau J := by
  intro k hk
  have h : gamma * KAM.Fourier.modeSize k ^ (-tau) ≤ |p11dotZ k (w y)| := hy.2 k hk
  rw [hw] at h
  have hs : 0 ≤ KAM.Fourier.modeSize k := KAM.Fourier.modeSize_nonneg k
  rw [Real.rpow_neg hs, ← div_eq_mul_inv] at h
  exact h

private theorem bp_dio_fast {gamma tau : ℝ} {u : Fin (n + n) → ℝ}
    (h : KAM.IsDiophantine gamma tau u) :
    KAM.IsDiophantine gamma tau (fast (a := n) (b := n) u) := by
  intro k hk
  have hk' : (Fin.append k (0 : Fin n → ℤ) : Fin (n + n) → ℤ) ≠ 0 := fun h0 =>
    hk (funext fun i => by simpa using congrFun h0 (Fin.castAdd n i))
  have := h _ hk'
  simpa [Fin.sum_univ_add, Fin.append_left, Fin.append_right, fast] using this

private theorem bp_dio_slow {gamma tau : ℝ} {u : Fin (n + n) → ℝ}
    (h : KAM.IsDiophantine gamma tau u) :
    KAM.IsDiophantine gamma tau (slow (a := n) (b := n) u) := by
  intro k hk
  have hk' : (Fin.append (0 : Fin n → ℤ) k : Fin (n + n) → ℤ) ≠ 0 := fun h0 =>
    hk (funext fun i => by simpa using congrFun h0 (Fin.natAdd n i))
  have := h _ hk'
  simpa [Fin.sum_univ_add, Fin.append_left, Fin.append_right, slow] using this

/-- Base point theorem, no Diophantine point is assumed. -/
theorem select {n : ℕ} (D : P11Physical n) :
    let A := p11PatchData D
    ∃ gamma : ℝ, 0 < gamma ∧ gamma ≤ 1 ∧ ∃ J0 ∈ interior A.K,
      KAM.IsDiophantine gamma (max ((n : ℝ)*A.mu) (2*n)) (A.varpi J0) ∧
      KAM.IsDiophantine gamma (max ((n : ℝ)*A.mu) (2*n)) (fast (a := n) (b := n) (A.varpi J0)) ∧
      KAM.IsDiophantine gamma (max ((n : ℝ)*A.mu) (2*n)) (slow (a := n) (b := n) (A.varpi J0)) := by
  intro A
  have hn1 : 1 ≤ n := by have := D.n_ge; omega
  obtain ⟨-, -, hVo, -, hKc, hKne, hKV, hKpos, hKnull, hmu, hbeta, hAn, -, hamt, -⟩ :=
    p11PatchData_spec D
  have hcd : ContDiffOn ℝ ((A.mu + 1 : ℕ) : WithTop ℕ∞) A.varpi A.V :=
    hAn.contDiffOn hVo.uniqueDiffOn
  -- `sel-hyp`: the hypotheses of the power law
  obtain ⟨v, hv0, hvK⟩ : ∃ v : ℝ, 0 < v ∧ Metric.cthickening v A.K ⊆ A.V := by
    obtain ⟨δ, hδ, h⟩ := hKc.exists_cthickening_subset_open hVo hKV
    exact ⟨δ, hδ, h⟩
  have hthick : p11thick A.K v ⊆ Metric.cthickening v A.K := fun y ⟨x, hx, hxy⟩ =>
    Metric.mem_cthickening_of_dist_le y x v A.K hx
      (by rw [dist_eq_norm]; exact ((KAM.Nekhoroshev.norm_le_euclid _).1).trans hxy)
  have hdiam : 0 < Metric.diam A.K := by
    refine Metric.diam_pos ?_ hKc.isBounded
    by_contra hns
    rw [Set.not_nontrivial_iff] at hns
    have : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
    exact hKpos.ne' (hns.measure_zero volume)
  let P : P11Patch n := ⟨A.K, A.V, v, hn1, hKne, hKc, hVo, hdiam, hv0, hthick.trans hvK⟩
  obtain ⟨M0, hM0, hjb⟩ := bp_jet_bound_all hVo hKc.cthickening hvK hcd
  have hbd := M_bound hn1 hVo (hthick.trans hvK) hcd hM0 (fun j hj y hy => hjb j hj y (hthick hy))
  set M : ℝ := max A.beta (2 ^ (A.mu + 1) * M0 ^ 2) with hM
  have hH : P11DioHyp P 2 A.mu A.varpi (fun _ => A.varpi) A.beta M :=
    { m_pos := by omega
      mu_pos := hmu
      convention := Or.inr rfl
      beta_pos := hbeta
      size_ge := le_max_left _ _
      regular := by exact_mod_cast hcd
      perturbed_regular := fun _ _ => hAn.contDiffOn hVo.uniqueDiffOn
      amount := hamt
      size := fun c hc j h1 h2 y hy => by
        refine ((hbd c hc j h1 h2 y hy).2).trans (le_trans ?_ (le_max_right _ _))
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) h2) (sq_nonneg _)
      close := fun k _ c _ j _ y _ => by
        have h0 : p11scalar 2 ((fun _ : Fin (n + n) → ℤ => A.varpi) k) c -
            p11scalar 2 A.varpi c = 0 := sub_self _
        simp only [h0, ↓reduceIte]
        unfold p11dg
        refine Real.sSup_le ?_ (by linarith)
        rintro x ⟨a, -, rfl⟩
        simp [iteratedFDeriv_zero, p11euclid_zero]
        linarith }
  -- `sel-gam`: the exponent and the choice of `gamma`
  set tau : ℝ := max ((n : ℝ) * A.mu) (2 * n) with htau
  have ht : (((n + n : ℕ) : ℝ)) * A.mu / (2 : ℕ) - 1 < tau := by
    push_cast
    have : ((n : ℝ) + n) * A.mu / 2 - 1 < (n : ℝ) * A.mu := by linarith
    exact this.trans_le (le_max_left _ _)
  have hnn : (0 : ℝ) < ((n + n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n + n)
  set γ0 : ℝ := min 1 (A.beta / (8 * ((n + n : ℕ) : ℝ))) with hγ0
  have hγ0pos : 0 < γ0 := lt_min one_pos (by positivity)
  have hsmall : ∀ g : ℝ, 0 < g → g ≤ γ0 → (Real.sqrt ((n + n : ℕ) : ℝ) * g) ^ 2 < A.beta / 4 := by
    intro g hg hgγ
    rw [mul_pow, Real.sq_sqrt hnn.le]
    have h1 : g ≤ 1 := hgγ.trans (min_le_left _ _)
    have h2 : g ≤ A.beta / (8 * ((n + n : ℕ) : ℝ)) := hgγ.trans (min_le_right _ _)
    have h3 : g ^ 2 ≤ g := by nlinarith
    have h4 : ((n + n : ℕ) : ℝ) * g ≤ A.beta / 8 := by
      rw [le_div_iff₀ (by positivity)] at h2; linarith
    nlinarith
  set C := p11CDio n (n + n) 2 A.mu (Metric.diam P.K) P.v A.beta M tau with hC
  have hKfin : volume A.K < ⊤ := hKc.measure_lt_top
  set eps : ℝ := (volume A.K).toReal / 2 with heps
  have hepspos : 0 < eps := by
    have : 0 < (volume A.K).toReal := ENNReal.toReal_pos hKpos.ne' hKfin.ne
    positivity
  have hepsK : ENNReal.ofReal eps < volume A.K := by
    have hx : 0 < (volume A.K).toReal := ENNReal.toReal_pos hKpos.ne' hKfin.ne
    have : ENNReal.ofReal eps < ENNReal.ofReal (volume A.K).toReal :=
      (ENNReal.ofReal_lt_ofReal_iff hx).2 (by rw [heps]; linarith)
    rwa [ENNReal.ofReal_toReal hKfin.ne] at this
  have hCnn : 0 ≤ C :=
    p11_C_nonneg (P := P) (by omega) (by norm_num) hmu hbeta (hbeta.le.trans (le_max_left _ _)) ht
  have hex : ∃ g : ℝ, 0 < g ∧ g ≤ γ0 ∧ volume A.K - ENNReal.ofReal eps ≤
      volume (p11Good A.K (fun _ => A.varpi) (fun k => g * KAM.Fourier.modeSize k ^ (-tau))) := by
    by_cases hC0 : C = 0
    · obtain ⟨-, hvol, -⟩ := power_law hH ht hγ0pos (hsmall γ0 hγ0pos le_rfl)
      refine ⟨γ0, hγ0pos, le_rfl, ?_⟩
      have hvol' : volume (A.K \ p11Good A.K (fun _ => A.varpi)
          (fun k => γ0 * KAM.Fourier.modeSize k ^ (-tau))) = 0 := by
        have := hvol
        rw [← hC, hC0, zero_mul, ENNReal.ofReal_zero, nonpos_iff_eq_zero] at this
        exact this
      refine tsub_le_self.trans ?_
      have hu := measure_union_le (μ := volume) (A.K \ p11Good A.K (fun _ => A.varpi)
        (fun k => γ0 * KAM.Fourier.modeSize k ^ (-tau)))
        (p11Good A.K (fun _ => A.varpi) (fun k => γ0 * KAM.Fourier.modeSize k ^ (-tau)))
      rw [hvol', zero_add] at hu
      exact (measure_mono (Set.subset_sdiff_union _ _)).trans hu
    · have hCpos : 0 < C := lt_of_le_of_ne hCnn (Ne.symm hC0)
      have hstar : 0 < p11GammaStar (n + n) 2 A.mu A.beta C eps := by
        unfold p11GammaStar
        refine lt_min ?_ ?_
        · have := Real.rpow_pos_of_pos (by positivity : 0 < A.beta / 4) (((2 : ℕ) : ℝ)⁻¹)
          have := Real.rpow_pos_of_pos hnn (-(1 / 2 : ℝ))
          positivity
        · exact Real.rpow_pos_of_pos (by positivity) _
      refine ⟨min γ0 (p11GammaStar (n + n) 2 A.mu A.beta C eps), lt_min hγ0pos hstar,
        min_le_left _ _, ?_⟩
      obtain ⟨-, -, hlow⟩ := power_law hH ht (lt_min hγ0pos hstar)
        (hsmall _ (lt_min hγ0pos hstar) (min_le_left _ _))
      exact hlow eps hepspos hepsK (min_le_right _ _)
  -- `sel-int`: the good set meets the interior
  obtain ⟨g, hg, hgγ, hvolG⟩ := hex
  set G := p11Good A.K (fun _ => A.varpi) (fun k => g * KAM.Fourier.modeSize k ^ (-tau)) with hG
  have hGK : G ⊆ A.K := fun y hy => hy.1
  have hGpos : 0 < volume G := lt_of_lt_of_le (tsub_pos_of_lt hepsK) hvolG
  obtain ⟨J0, hJ0G, hJ0int⟩ : ∃ J0 ∈ G, J0 ∈ interior A.K := by
    by_contra hno
    push Not at hno
    have : G ⊆ A.K \ interior A.K := fun y hy => ⟨hGK hy, hno y hy⟩
    exact hGpos.ne' (measure_mono_null this hKnull)
  have hD : KAM.IsDiophantine g tau (A.varpi J0) := bp_dio_of_good (w := A.varpi) rfl hJ0G
  exact ⟨g, hg, hgγ.trans (min_le_left _ _), J0, hJ0int, hD, bp_dio_fast hD, bp_dio_slow hD⟩

end BasePoint

end KAM.Planetary

end
