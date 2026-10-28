/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Bridges
public import KAM.Strip.FourierSeriesVector
public import KAM.Strip.Cohomological
public import KAM.Planetary.MaximalStep.FourierCutoffTail
public import KAM.Planetary.MaximalStep.FourierCutoffCoeff

/-!
# The elementary Fourier cutoff (P11A-C1)

`fourier_cutoff` (`bpP:p11a:fourier-cutoff`): for `F` admissible on `D(r,s;B)` and bounded by `M`,
the truncation `p11Cut T F` is a finite trigonometric sum in the angles, admissible on
`D(r-d,s;B)`, within `p11Error n T d * M` of `F`, bounded by `(1+p11Error n T d) * M`, real when `F`
is, and entire in `θ` at each fixed `(η, b)`.

Steps: `stepP:p11a:fc-decay` (`decay_boundary_radius` and `eq_fourierSumVec_torusCoeffW`),
`fc-tail` (the norm of the character on the strip) and the lattice count of `FourierCutoffTail`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace KAM.Planetary

/-- The angle coefficient `û_k(η, b)` of a family at the point `z = ((θ, η), b)`. -/
private def cf {n : ℕ} (F : P11Family n → ℂ) (z : P11Family n) (k : Fin n → ℤ) : ℂ :=
  KAM.torusCoeffW (fun x : Fin n → ℝ => F (((fun j => (x j : ℂ)), z.1.2), z.2)) k

/-- The truncation as a finite sum over the cutoff box. -/
private theorem p11Cut_eq_sum {n : ℕ} {T : ℝ} (F : P11Family n → ℂ)
    (z : P11Family n) :
    p11Cut T F z = ∑ k ∈ KAM.modeCutoff n ⌈T⌉₊,
      if KAM.Fourier.modeSize k ≤ T then cf F z k * KAM.character k z.1.1 else 0 := by
  unfold p11Cut KAM.Weighted.truncate KAM.Weighted.projMode
  refine (tsum_eq_sum (s := KAM.modeCutoff n ⌈T⌉₊) ?_).trans ?_
  · intro k hk
    have : ¬ KAM.Fourier.modeSize k ≤ (⌈T⌉₊ : ℝ) := fun h => hk (KAM.mem_modeCutoff.mpr h)
    have h2 : ¬ KAM.Fourier.modeSize k ≤ T := fun h => this (h.trans (Nat.le_ceil T))
    simp [h2]
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : KAM.Fourier.modeSize k ≤ T <;> simp [h, cf, KAM.Weighted.coeff]

private theorem norm_lt_of_mem_polyNbhd {n : ℕ} {s : ℝ} {η : P11CVec n}
    (h : η ∈ KAM.Weighted.polyNbhd {0} s) : ‖η‖ < s := by
  obtain ⟨I', hI', h⟩ := h
  rw [Set.mem_singleton_iff.mp hI'] at h
  simpa using h

private theorem mem_polyNbhd_of_norm_lt {n : ℕ} {s : ℝ} {η : P11CVec n} (h : ‖η‖ < s) :
    η ∈ KAM.Weighted.polyNbhd {0} s := ⟨0, rfl, by simpa using h⟩

private theorem modeSize_neg {n : ℕ} (k : Fin n → ℤ) :
    KAM.Fourier.modeSize (-k) = KAM.Fourier.modeSize k := by
  simp [KAM.Fourier.modeSize]

/-- The slice `θ ↦ F((θ,η),b)` of an admissible family. -/
private theorem slice_facts {n : ℕ} {r s M : ℝ} {B : Set (P11CVec n)} {F : P11Family n → ℂ}
    (hF : p11Admissible r s B F) (hb : p11Bound (domain_def n r s B) F M)
    {η b : P11CVec n} (hη : ‖η‖ < s) (hbB : b ∈ B) :
    DifferentiableOn ℂ (fun θ : P11CVec n => F ((θ, η), b)) (KAM.complexStrip n r) ∧
    (∀ (i : Fin n) θ, θ ∈ KAM.complexStrip n r →
      F ((θ + Pi.single i 1, η), b) = F ((θ, η), b)) ∧
    ∀ θ ∈ KAM.complexStrip n r, ‖F ((θ, η), b)‖ ≤ M := by
  have hmem : ∀ θ ∈ KAM.complexStrip n r, ((θ, η), b) ∈ domain_def n r s B := fun θ hθ =>
    ⟨⟨hθ, mem_polyNbhd_of_norm_lt hη⟩, hbB⟩
  refine ⟨?_, fun i θ hθ => hF.2 i _ (hmem θ hθ), fun θ hθ => hb _ (hmem θ hθ)⟩
  refine hF.1.comp ((differentiableOn_id.prodMk (differentiableOn_const _)).prodMk
    (differentiableOn_const _)) fun θ hθ => hmem θ hθ

/-- Pointwise tail bound on the narrower strip. -/
private theorem cutoff_tail {n : ℕ} (hn : 1 ≤ n) {r s T d M : ℝ} (hr : 0 < r) (hT : 0 ≤ T)
    (hd : 0 < d) (_hdr : d < r) {B : Set (P11CVec n)} {F : P11Family n → ℂ}
    (hF : p11Admissible r s B F) (hM : 0 ≤ M) (hb : p11Bound (domain_def n r s B) F M)
    {θ η b : P11CVec n} (hθ : θ ∈ KAM.complexStrip n (r - d)) (hη : ‖η‖ < s) (hbB : b ∈ B) :
    ‖F ((θ, η), b) - p11Cut T F ((θ, η), b)‖ ≤ p11Error n T d * M := by
  obtain ⟨hu, hp, hA⟩ := slice_facts hF hb hη hbB
  set c : (Fin n → ℤ) → ℂ := fun k => cf F ((θ, η), b) k with hc
  have hcdef : c = KAM.torusCoeffW fun x : Fin n → ℝ =>
      (fun θ : P11CVec n => F ((θ, η), b)) fun j => (x j : ℂ) := rfl
  have hdec : ∀ k, ‖c k‖ ≤ Real.exp (-(2 * Real.pi * r * KAM.Fourier.modeSize k)) * M := fun k => by
    rw [hcdef]
    exact KAM.decay_boundary_radius hr hu hp hA k
  set term : (Fin n → ℤ) → ℂ := fun k => c k * KAM.character k θ with hterm
  have hθr : θ ∈ KAM.complexStrip n r := fun j => (hθ j).trans (by linarith)
  have hx : 0 < 2 * Real.pi * d := by positivity
  have hbd : ∀ k, ‖term k‖ ≤ M * Real.exp (-(2 * Real.pi * d) * KAM.Fourier.modeSize k) := by
    intro k
    rw [hterm, norm_mul]
    calc ‖c k‖ * ‖KAM.character k θ‖
        ≤ (Real.exp (-(2 * Real.pi * r * KAM.Fourier.modeSize k)) * M) *
          Real.exp (2 * Real.pi * (r - d) * KAM.Fourier.modeSize k) :=
          mul_le_mul (hdec k) (KAM.norm_character_le k hθ) (norm_nonneg _)
            (mul_nonneg (Real.exp_pos _).le hM)
      _ = M * Real.exp (-(2 * Real.pi * d) * KAM.Fourier.modeSize k) := by
          rw [mul_comm _ M, mul_assoc, ← Real.exp_add]
          congr 2; ring
  have hgeom : Summable fun k : Fin n → ℤ =>
      Real.exp (-(2 * Real.pi * d) * KAM.Fourier.modeSize k) :=
    ((KAM.Fourier.exp_sums n).2.1 _ hx).1.summable
  have hsum : Summable term :=
    Summable.of_norm_bounded (hgeom.mul_left M) hbd
  have hrep : F ((θ, η), b) = ∑' k, term k := by
    have := KAM.eq_fourierSumVec_torusCoeffW hr hu hp hA hθr
    refine this.trans (tsum_congr fun k => ?_)
    rw [hterm, smul_eq_mul, mul_comm]
    rfl
  set S : Set (Fin n → ℤ) := {k | KAM.Fourier.modeSize k ≤ T} with hS
  have hcut : p11Cut T F ((θ, η), b) = ∑' k, S.indicator term k := by
    unfold p11Cut KAM.Weighted.truncate KAM.Weighted.projMode
    exact tsum_congr fun k => rfl
  have hsub : F ((θ, η), b) - p11Cut T F ((θ, η), b) = ∑' k, (term k - S.indicator term k) := by
    rw [hrep, hcut, hsum.tsum_sub (hsum.indicator S)]
  rw [hsub]
  set tl : (Fin n → ℤ) → ℝ := fun k => if T < KAM.Fourier.modeSize k then
        Real.exp (-(2 * Real.pi * d) * KAM.Fourier.modeSize k) else 0 with htl
  have htls : Summable tl := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hgeom
    · simp only [htl]; split_ifs <;> positivity
    · simp only [htl]; split_ifs
      · exact le_rfl
      · positivity
  have hnorm : ∀ k, ‖term k - S.indicator term k‖ ≤ M * tl k := by
    intro k
    by_cases h : KAM.Fourier.modeSize k ≤ T
    · have : k ∈ S := h
      simp [Set.indicator_of_mem this, htl, not_lt.mpr h]
    · have hk : k ∉ S := h
      have h' : T < KAM.Fourier.modeSize k := not_le.mp h
      simp only [Set.indicator_of_notMem hk, sub_zero, htl, if_pos h']
      exact hbd k
  refine (tsum_of_norm_bounded (htls.mul_left M).hasSum hnorm).trans ?_
  rw [tsum_mul_left, mul_comm]
  exact mul_le_mul_of_nonneg_right (p11_tail_le hn hT hd) hM

/-- `bpP:p11a:fourier-cutoff`. -/
theorem fourier_cutoff {n : ℕ} (hn : 1 ≤ n) {r s T d M : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : 0 ≤ T) (hd : 0 < d) (hdr : d < r)
    {B : Set (P11CVec n)} (hB : IsOpen B) {F : P11Family n → ℂ}
    (hF : p11Admissible r s B F) (hM : 0 ≤ M) (hb : p11Bound (domain_def n r s B) F M) :
    1 ≤ p11C n ∧ p11Admissible (r-d) s B (p11Cut T F) ∧
    p11Bound (domain_def n (r-d) s B) (F-p11Cut T F) (p11Error n T d*M) ∧
    p11Bound (domain_def n (r-d) s B) (p11Cut T F) ((1+p11Error n T d)*M) ∧
    (p11Real (domain_def n r s B) F → p11Real (domain_def n (r-d) s B) (p11Cut T F)) ∧
    ∀ eta b, b ∈ B → ‖eta‖ < s →
      Differentiable ℂ (fun theta => p11Cut T F ((theta,eta),b)) := by
  have hdom : ∀ {z : P11Family n}, z ∈ domain_def n (r - d) s B →
      z.1.1 ∈ KAM.complexStrip n (r - d) ∧ ‖z.1.2‖ < s ∧ z.2 ∈ B := fun {z} hz =>
    ⟨hz.1.1, norm_lt_of_mem_polyNbhd hz.1.2, hz.2⟩
  refine ⟨p11C_ge_one hn, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- holomorphy
    have hsubset : domain_def n (r - d) s B ⊆ domain_def n r s B :=
      prod_mono (KAM.Weighted.Dom_mono le_rfl (by linarith)) subset_rfl
    have hfin : ∀ z, p11Cut T F z = ∑ k ∈ KAM.modeCutoff n ⌈T⌉₊,
        if KAM.Fourier.modeSize k ≤ T then cf F z k * KAM.character k z.1.1 else 0 :=
      p11Cut_eq_sum F
    refine DifferentiableOn.congr (f := fun z : P11Family n =>
      ∑ k ∈ KAM.modeCutoff n ⌈T⌉₊,
        if KAM.Fourier.modeSize k ≤ T then cf F z k * KAM.character k z.1.1 else 0) ?_
      fun z _ => hfin z
    refine DifferentiableOn.fun_sum fun k _ => ?_
    by_cases hk : KAM.Fourier.modeSize k ≤ T
    · simp only [if_pos hk]
      have h1 := coeff_joint_differentiableOn hr hB hF.1 k
      have h2 : DifferentiableOn ℂ (fun z : P11Family n => cf F z k)
          (domain_def n (r - d) s B) := by
        have hmap : Differentiable ℂ (fun z : P11Family n => (z.1.2, z.2)) :=
          (differentiable_snd.comp differentiable_fst).prodMk differentiable_snd
        refine h1.comp hmap.differentiableOn fun z hz => ?_
        obtain ⟨-, h2, h3⟩ := hdom hz
        exact ⟨mem_polyNbhd_of_norm_lt h2, h3⟩
      have hg : Differentiable ℂ (fun z : P11Family n => z.1.1) :=
        differentiable_fst.comp differentiable_fst
      exact h2.mul ((KAM.differentiable_character k).comp hg).differentiableOn
    · simp only [if_neg hk]
      exact differentiableOn_const _
  · intro j z hz
    show p11Cut T F _ = p11Cut T F z
    rw [p11Cut_eq_sum, p11Cut_eq_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [cf, KAM.character_add_single]
  · intro z hz
    obtain ⟨⟨θ, η⟩, b⟩ := z
    obtain ⟨h1, h2, h3⟩ := hdom hz
    exact cutoff_tail hn hr hT hd hdr hF hM hb h1 h2 h3
  · intro z hz
    obtain ⟨⟨θ, η⟩, b⟩ := z
    obtain ⟨h1, h2, h3⟩ := hdom hz
    have hz' : ((θ, η), b) ∈ domain_def n r s B :=
      ⟨⟨fun j => (h1 j).trans (by linarith), mem_polyNbhd_of_norm_lt h2⟩, h3⟩
    have ht := cutoff_tail hn hr hT hd hdr hF hM hb h1 h2 h3
    have hFb := hb _ hz'
    calc ‖p11Cut T F ((θ, η), b)‖
        = ‖F ((θ, η), b) - (F ((θ, η), b) - p11Cut T F ((θ, η), b))‖ := by ring_nf
      _ ≤ ‖F ((θ, η), b)‖ + ‖F ((θ, η), b) - p11Cut T F ((θ, η), b)‖ := norm_sub_le _ _
      _ ≤ (1 + p11Error n T d) * M := by nlinarith
  · intro hreal x b hxb
    obtain ⟨h1, h2, h3⟩ := hdom hxb
    have hxη : ‖KAM.realInclusion n x.2‖ < s := h2
    have hv : ∀ x' : Fin n → ℝ,
        ((F (((fun j => (x' j : ℂ)), KAM.realInclusion n x.2), KAM.realInclusion n b)).im = 0) := by
      intro x'
      exact hreal (x', x.2) b ⟨⟨KAM.ofReal_mem_complexStrip hr x', mem_polyNbhd_of_norm_lt hxη⟩, h3⟩
    set z : P11Family n := (KAM.realInclusion₂ n x, KAM.realInclusion n b) with hz
    have hcs : ∀ k, cf F z k = (starRingEnd ℂ) (cf F z (-k)) := by
      intro k
      have := KAM.torusCoeff_conjugateSymmetric (n := n)
        (v := fun x' : Fin n → ℝ => F (((fun j => (x' j : ℂ)), KAM.realInclusion n x.2),
          KAM.realInclusion n b)) hv (-k)
      simpa [cf, hz, KAM.torusCoeffW_complex] using this
    refine Complex.conj_eq_iff_im.mp ?_
    rw [p11Cut_eq_sum, map_sum]
    refine Finset.sum_equiv (Equiv.neg _) (fun k => ?_) (fun k _ => ?_)
    · simp [KAM.mem_modeCutoff, modeSize_neg]
    · have hth : z.1.1 = fun j => (x.1 j : ℂ) := rfl
      by_cases hk : KAM.Fourier.modeSize k ≤ T
      · have hk' : KAM.Fourier.modeSize (-k) ≤ T := by rwa [modeSize_neg]
        simp only [if_pos hk, if_pos hk', Equiv.neg_apply, map_mul, hth, KAM.conj_character_real]
        have h := hcs (-k)
        rw [neg_neg] at h
        rw [h]
      · have hk' : ¬ KAM.Fourier.modeSize (-k) ≤ T := by rwa [modeSize_neg]
        simp [if_neg hk, if_neg hk', Equiv.neg_apply]
  · intro eta b _ _
    have : (fun theta => p11Cut T F ((theta, eta), b)) = fun theta =>
        ∑ k ∈ KAM.modeCutoff n ⌈T⌉₊, if KAM.Fourier.modeSize k ≤ T then
          cf F ((0, eta), b) k * KAM.character k theta else 0 :=
      funext fun theta => p11Cut_eq_sum F ((theta, eta), b)
    rw [this]
    refine Differentiable.fun_sum fun k _ => ?_
    by_cases hk : KAM.Fourier.modeSize k ≤ T
    · simp only [if_pos hk]
      exact (differentiable_const _).mul (KAM.differentiable_character k)
    · simp only [if_neg hk]
      exact differentiable_const _

end KAM.Planetary
