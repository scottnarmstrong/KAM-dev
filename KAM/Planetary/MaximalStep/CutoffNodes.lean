/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.StepCoeff
public import KAM.Planetary.MaximalStep.Loss
public import KAM.Planetary.MaximalStep.FourierCutoff
public import KAM.Planetary.MaximalStep.Parameter

/-!
# Literal exports for the cutoff step (GAP-P11a2-cut)

Unsigned exports stating the literal conclusions of the nodes `bpP:p11a:c2-conv#data`,
`stepP:p11a:fc-tail`, `tc-a`, `tc-b`, `cu-coeff`, `cu-a` and `bpP:p11a:cutoff` of
`blueprint-P/parts/p11a2-cutoff-step.tex`, from the landed declarations of
`Parameter`, `FourierCutoff`, `Taylor`, `StepCoeff` and `Loss`.

All functions are scalar-valued, as in the landed Lean (the source's `ℂ^q`-valued statements are
read componentwise).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-! ### `bpP:p11a:c2-conv#data` -/

/-- `bpP:p11a:c2-conv#data`: the thickening `E + t = {b : ∃ b' ∈ E, ‖b - b'‖ < t}` is open and
contains the polydisc `P(b', t)` around each `b' ∈ E`. -/
theorem p11_c2_conv_data {n : ℕ} (E : Set (P11Vec n)) (t : ℝ) :
    (∀ b : P11CVec n, b ∈ KAM.actionNbhd E t ↔ ∃ b' ∈ E, ‖b - KAM.realInclusion n b'‖ < t) ∧
    IsOpen (KAM.actionNbhd E t) ∧
    ∀ b' ∈ E, ball (KAM.realInclusion n b') t ⊆ KAM.actionNbhd E t := by
  refine ⟨fun b => Iff.rfl, p11_isOpen_actionNbhd E t, fun b' hb' b hb => ?_⟩
  rw [mem_ball, dist_eq_norm] at hb
  exact ⟨b', hb', hb⟩

/-! ### `stepP:p11a:fc-tail` -/

/-- `stepP:p11a:fc-tail`: for `θ ∈ T_{r-d}`, `‖η‖ < s`, `b ∈ B`,
`|F - cut_T F| ≤ ‖F‖_r ∑_{|k|₁ > T} e^{-2π |k|₁ d}`. -/
theorem p11_fc_tail {n : ℕ} {r s T d M : ℝ} (hr : 0 < r) (hd : 0 < d)
    {B : Set (P11CVec n)} {F : P11Family n → ℂ} (hF : p11Admissible r s B F) (hM : 0 ≤ M)
    (hb : p11Bound (domain_def n r s B) F M) {θ η b : P11CVec n}
    (hθ : θ ∈ KAM.complexStrip n (r - d)) (hη : ‖η‖ < s) (hbB : b ∈ B) :
    ‖F ((θ, η), b) - p11Cut T F ((θ, η), b)‖ ≤
      M * ∑' k : Fin n → ℤ, (if T < KAM.Fourier.modeSize k then
        Real.exp (-(2 * Real.pi * d) * KAM.Fourier.modeSize k) else 0) := by
  have hθr : θ ∈ KAM.complexStrip n r := fun j => (hθ j).trans (by linarith)
  have hmem : ∀ θ' ∈ KAM.complexStrip n r, ((θ', η), b) ∈ domain_def n r s B := fun θ' hθ' =>
    p11_mem_domain_def.mpr ⟨hθ', hη, hbB⟩
  have hu : DifferentiableOn ℂ (fun θ : P11CVec n => F ((θ, η), b)) (KAM.complexStrip n r) :=
    hF.1.comp ((differentiableOn_id.prodMk (differentiableOn_const _)).prodMk
      (differentiableOn_const _)) fun θ hθ => hmem θ hθ
  have hp : ∀ (i : Fin n) θ, θ ∈ KAM.complexStrip n r →
      F ((θ + Pi.single i 1, η), b) = F ((θ, η), b) := fun i θ hθ => hF.2 i _ (hmem θ hθ)
  have hA : ∀ θ ∈ KAM.complexStrip n r, ‖F ((θ, η), b)‖ ≤ M := fun θ hθ => hb _ (hmem θ hθ)
  set c : (Fin n → ℤ) → ℂ := KAM.torusCoeffW fun x : Fin n → ℝ =>
    (fun θ : P11CVec n => F ((θ, η), b)) fun j => (x j : ℂ) with hc
  have hdec : ∀ k, ‖c k‖ ≤ Real.exp (-(2 * Real.pi * r * KAM.Fourier.modeSize k)) * M :=
    fun k => KAM.decay_boundary_radius hr hu hp hA k
  set term : (Fin n → ℤ) → ℂ := fun k => c k * KAM.character k θ with hterm
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
  have hsum : Summable term := Summable.of_norm_bounded (hgeom.mul_left M) hbd
  have hrep : F ((θ, η), b) = ∑' k, term k := by
    have := KAM.eq_fourierSumVec_torusCoeffW hr hu hp hA hθr
    refine this.trans (tsum_congr fun k => ?_)
    rw [hterm, smul_eq_mul, mul_comm]
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
      simp only [Set.indicator_of_notMem hk, sub_zero, htl, h', ↓reduceIte]
      exact hbd k
  refine (tsum_of_norm_bounded (htls.mul_left M).hasSum hnorm).trans ?_
  rw [tsum_mul_left]

/-! ### `stepP:p11a:tc-a` and `tc-b` -/

private theorem norm_single_le_one {n : ℕ} (j : Fin n) :
    ‖(Pi.single j (1 : ℂ) : P11CVec n)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  by_cases h : i = j <;> simp [h]

/-- `stepP:p11a:tc-a`: on `D(r,s;B)`, `|F^{(≤1)}| ≤ M + M‖η‖/s`; for `θ ∈ T_r`, `b ∈ B` and each
`j`, `|∂_{η_j} F(θ,0,b)| ≤ M/s`. -/
theorem p11_tc_a {n : ℕ} {r s M : ℝ} (hs : 0 < s) {B : Set (P11CVec n)} {F : P11Family n → ℂ}
    (hF : p11Admissible r s B F) (hb : p11Bound (domain_def n r s B) F M) :
    (∀ z ∈ domain_def n r s B, ‖p11Taylor F z‖ ≤ M + M * ‖z.1.2‖ / s) ∧
    ∀ θ ∈ KAM.complexStrip n r, ∀ b ∈ B, ∀ j : Fin n,
      ‖fderiv ℂ (fun η => F ((θ, η), b)) 0 (Pi.single j 1)‖ ≤ M / s := by
  have hslice : ∀ θ ∈ KAM.complexStrip n r, ∀ b ∈ B,
      ‖fderiv ℂ (fun eta => F ((θ, eta), b)) 0‖ ≤ M / s := fun θ hθ b hb' =>
    p11_norm_fderiv_le_of_ball hs (p11_slice_differentiableOn hF.1 hθ hb')
      (fun w hw => hb _ (p11_mem_domain_def.mpr ⟨hθ, mem_ball_zero_iff.mp hw, hb'⟩))
  refine ⟨?_, fun θ hθ b hb' j => ?_⟩
  · rintro ⟨⟨θ, η⟩, b⟩ hz
    obtain ⟨h1, -, h3⟩ := p11_mem_domain_def.mp hz
    have h0 := hb ((θ, 0), b) (p11_mem_domain_def.mpr ⟨h1, by simpa using hs, h3⟩)
    have hd := hslice θ h1 b h3
    simp only [p11Taylor]
    calc ‖F ((θ, 0), b) + (fderiv ℂ (fun eta => F ((θ, eta), b)) 0) η‖
        ≤ ‖F ((θ, 0), b)‖ + ‖fderiv ℂ (fun eta => F ((θ, eta), b)) 0‖ * ‖η‖ :=
          (norm_add_le _ _).trans (by gcongr; exact ContinuousLinearMap.le_opNorm _ _)
      _ ≤ M + M / s * ‖η‖ := by gcongr
      _ = M + M * ‖η‖ / s := by ring
  · calc ‖fderiv ℂ (fun η => F ((θ, η), b)) 0 (Pi.single j 1)‖
        ≤ ‖fderiv ℂ (fun η => F ((θ, η), b)) 0‖ * ‖(Pi.single j (1 : ℂ) : P11CVec n)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ M / s * 1 :=
          mul_le_mul (hslice θ hθ b hb') (norm_single_le_one j) (norm_nonneg _)
            ((norm_nonneg _).trans (hslice θ hθ b hb'))
      _ = M / s := mul_one _

/-- `stepP:p11a:tc-b` (the inequality chain only): for `0 < q < 1` and `a = ‖η‖ < q s`,
`|F - F^{(≤1)}| ≤ M (a/s)²/(1 - a/s) ≤ M q²/(1 - q)`. -/
theorem p11_tc_b {n : ℕ} {r s M q : ℝ} (hs : 0 < s) (hq : 0 < q) (hq1 : q < 1)
    {B : Set (P11CVec n)} {F : P11Family n → ℂ} (hF : p11Admissible r s B F)
    (hb : p11Bound (domain_def n r s B) F M) {θ η b : P11CVec n}
    (hθ : θ ∈ KAM.complexStrip n r) (hbB : b ∈ B) (hη : ‖η‖ < q * s) :
    ‖(F - p11Taylor F) ((θ, η), b)‖ ≤ M * (‖η‖ / s) ^ 2 / (1 - ‖η‖ / s) ∧
    M * (‖η‖ / s) ^ 2 / (1 - ‖η‖ / s) ≤ M * q ^ 2 / (1 - q) := by
  set x : ℝ := ‖η‖ / s with hx
  have hx0 : 0 ≤ x := by positivity
  have hxq : x < q := by rw [hx, div_lt_iff₀ hs]; linarith
  have hM : 0 ≤ M := (norm_nonneg _).trans
    (hb ((θ, 0), b) (p11_mem_domain_def.mpr ⟨hθ, by simpa using hs, hbB⟩))
  have hdiff := p11_slice_differentiableOn hF.1 hθ hbB
  have hbs : ∀ w ∈ ball (0 : P11CVec n) s, ‖F ((θ, w), b)‖ ≤ M := fun w hw =>
    hb _ (p11_mem_domain_def.mpr ⟨hθ, mem_ball_zero_iff.mp hw, hbB⟩)
  have hpt : ∀ y : ℝ, x < y → y < 1 →
      ‖(F - p11Taylor F) ((θ, η), b)‖ ≤ M * y ^ 2 / (1 - y) := by
    intro y hxy hy1
    have hy0 : 0 < y := hx0.trans_lt hxy
    have hηy : ‖η‖ < y * s := by
      have : x * s < y * s := by gcongr
      rwa [hx, div_mul_cancel₀ _ hs.ne'] at this
    have := p11_taylor_remainder (φ := fun eta => F ((θ, eta), b)) (s := s) (M := M) hy0 hy1
      hdiff hbs hηy
    simp only [Pi.sub_apply, p11Taylor]
    convert this using 2
    ring
  have hcont : ContinuousAt (fun y : ℝ => M * y ^ 2 / (1 - y)) x :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (by linarith)
  refine ⟨ge_of_tendsto (x := 𝓝[>] x)
    (hcont.tendsto.mono_left nhdsWithin_le_nhds) ?_, ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT (hxq.trans hq1)] with y hy
    exact hpt y hy.1 hy.2
  · have h1 : 0 < 1 - x := by linarith
    have h2 : 0 < 1 - q := by linarith
    rw [mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hM
    rw [div_le_div_iff₀ h1 h2]
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hxq.le), mul_nonneg hx0 hx0]

/-! ### `stepP:p11a:cu-coeff` -/

/-- The cutoff coefficient sum `∑_{k ∈ hmModes} 1_{|k|₁ ≤ T} P̂_k(b) χ_k(θ)` is holomorphic on
`ℂᴺ × B` and one-periodic in `θ`, given that `P` is holomorphic on a strip times `B`. -/
private theorem diffOn_trig_sum {n : ℕ} {r T : ℝ} (hr : 0 < r) {B : Set (P11CVec n)}
    (hB : IsOpen B) {P : P11CVec n × P11CVec n → ℂ}
    (hP : DifferentiableOn ℂ P (KAM.complexStrip n r ×ˢ B)) :
    DifferentiableOn ℂ (fun z : P11CVec n × P11CVec n =>
      ∑ k ∈ hmModes n T, (if KAM.Fourier.modeSize k ≤ T then KAM.Weighted.coeff P z.2 k else 0) *
        KAM.character k z.1) (univ ×ˢ B) := by
  refine DifferentiableOn.fun_sum fun k _ => DifferentiableOn.mul ?_ ?_
  · by_cases hk : KAM.Fourier.modeSize k ≤ T
    · simp only [hk, ↓reduceIte]
      exact (differentiableOn_coeff hr hB hP k).comp differentiableOn_snd fun z hz => hz.2
    · simp only [hk, ↓reduceIte]
      exact differentiableOn_const _
  · exact ((KAM.differentiable_character k).comp differentiable_fst).differentiableOn

/-- `stepP:p11a:cu-coeff`: for each `k` the coefficients `b ↦ R̂(·,0,·)_k(b)` and
`b ↦ (∂_{η_i} R)^(·,0,·)_k(b)` are holomorphic on `B`; and `R_{*0}`, `R_{*1,i}` are the finite sums
`∑_{|k|₁ ≤ T} (coefficient) χ_k` on `B`, hence holomorphic on `ℂᴺ × B` and one-periodic. -/
theorem p11_cu_coeff {n : ℕ} {r s T : ℝ} (hr : 0 < r) (hs : 0 < s) {B : Set (P11CVec n)}
    (hB : IsOpen B) {R : P11Family n → ℂ} (hR : p11Admissible r s B R) :
    (∀ k : Fin n → ℤ, DifferentiableOn ℂ
      (fun b => KAM.Weighted.coeff (fun u : P11CVec n × P11CVec n => R ((u.1, 0), u.2)) b k) B) ∧
    (∀ (i : Fin n) (k : Fin n → ℤ), DifferentiableOn ℂ
      (fun b => KAM.Weighted.coeff (fun u : P11CVec n × P11CVec n =>
        fderiv ℂ (fun η => R ((u.1, η), u.2)) 0 (Pi.single i 1)) b k) B) ∧
    (∀ θ b : P11CVec n, b ∈ B → p11R0 T R (θ, b) =
      ∑ k ∈ hmModes n T, (if KAM.Fourier.modeSize k ≤ T then
        KAM.Weighted.coeff (fun u : P11CVec n × P11CVec n => R ((u.1, 0), u.2)) b k else 0) *
        KAM.character k θ) ∧
    (∀ (i : Fin n) (θ b : P11CVec n), b ∈ B → p11R1 T R (θ, b) i =
      ∑ k ∈ hmModes n T, (if KAM.Fourier.modeSize k ≤ T then
        KAM.Weighted.coeff (fun u : P11CVec n × P11CVec n =>
          fderiv ℂ (fun η => R ((u.1, η), u.2)) 0 (Pi.single i 1)) b k else 0) *
        KAM.character k θ) ∧
    (DifferentiableOn ℂ (p11R0 T R) (univ ×ˢ B) ∧
      ∀ j : Fin n, ∀ z ∈ (univ : Set (P11CVec n)) ×ˢ B,
        p11R0 T R (z.1 + Pi.single j 1, z.2) = p11R0 T R z) ∧
    ∀ i : Fin n, DifferentiableOn ℂ (fun z => p11R1 T R z i) (univ ×ˢ B) ∧
      ∀ j : Fin n, ∀ z ∈ (univ : Set (P11CVec n)) ×ˢ B,
        p11R1 T R (z.1 + Pi.single j 1, z.2) i = p11R1 T R z i := by
  have hd0 := stepF0_diff hr hs hR
  have hd1 := fun i => stepF1_diff hr hs hB hR i
  have e0 : ∀ θ b : P11CVec n, p11R0 T R (θ, b) = ∑ k ∈ hmModes n T,
      (if KAM.Fourier.modeSize k ≤ T then KAM.Weighted.coeff (stepF0 R) b k else 0) *
        KAM.character k θ := fun θ b => by
    rw [cutoff_R0, truncate_eq, fourierSum_finset fun k hk => hmCut_eq_zero hk]
    rfl
  have e1 : ∀ (i : Fin n) (θ b : P11CVec n), b ∈ B → p11R1 T R (θ, b) i =
      ∑ k ∈ hmModes n T, (if KAM.Fourier.modeSize k ≤ T then
        KAM.Weighted.coeff (stepF1 R i) b k else 0) * KAM.character k θ := fun i θ b hb => by
    rw [cutoff_R1 hr hs hB hR θ hb i, truncate_eq, fourierSum_finset fun k hk => hmCut_eq_zero hk]
    rfl
  have per : ∀ (P : P11CVec n × P11CVec n → ℂ) (j : Fin n) (z : P11CVec n × P11CVec n),
      ∑ k ∈ hmModes n T, (if KAM.Fourier.modeSize k ≤ T then
        KAM.Weighted.coeff P z.2 k else 0) * KAM.character k (z.1 + Pi.single j 1) =
      ∑ k ∈ hmModes n T, (if KAM.Fourier.modeSize k ≤ T then
        KAM.Weighted.coeff P z.2 k else 0) * KAM.character k z.1 := fun P j z => by
    simp only [KAM.character_add_single]
  refine ⟨fun k => differentiableOn_coeff hr hB hd0 k, fun i k => differentiableOn_coeff hr hB
    (hd1 i) k, fun θ b _ => e0 θ b, fun i θ b hb => e1 i θ b hb, ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · refine (diffOn_trig_sum (T := T) hr hB hd0).congr fun z hz => ?_
    exact e0 z.1 z.2
  · intro j z hz
    rw [e0, e0]
    exact per (stepF0 R) j z
  · refine (diffOn_trig_sum (T := T) hr hB (hd1 i)).congr fun z hz => ?_
    exact e1 i z.1 z.2 hz.2
  · intro j z hz
    rw [e1 i _ _ hz.2, e1 i _ _ hz.2]
    exact per (stepF1 R i) j z

/-! ### `stepP:p11a:cu-a` -/

/-- `stepP:p11a:cu-a`: `‖R_*‖_{r-d,s;B} ≤ 2(1+E_T) ε`, `‖R_{*0}‖_{r-d;B} ≤ (1+E_T) ε` and
`‖R_{*1,j}‖_{r-d;B} ≤ (1+E_T) ε / s` for each `j`. -/
theorem p11_cu_a {n : ℕ} (hn : 1 ≤ n) {r s T d eps : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : 0 ≤ T) (hd : 0 < d) (hdr : d < r)
    (he : 0 ≤ eps) {B : Set (P11CVec n)} (hB : IsOpen B) {R : P11Family n → ℂ}
    (hR : p11Admissible r s B R) (hb : p11Bound (domain_def n r s B) R eps) :
    p11Bound (domain_def n (r-d) s B) (p11Cutoff T R) (2*(1+p11Error n T d)*eps) ∧
    p11Bound (KAM.complexStrip n (r-d) ×ˢ B) (p11R0 T R) ((1+p11Error n T d)*eps) ∧
    ∀ j : Fin n, p11Bound (KAM.complexStrip n (r-d) ×ˢ B) (fun z => p11R1 T R z j)
      ((1+p11Error n T d)*eps/s) := by
  obtain ⟨-, h2, -⟩ := p11_cutoff hn hr hs hT hd hdr he (q := 1 / 2) (by norm_num)
    (by norm_num) hB hR hb
  obtain ⟨-, -, -, -, h5, h6, -⟩ := p11_cutoff_coeff hn hr hs hT hd hdr he hB hR hb
  exact ⟨h2, h5, fun j z hz => (norm_le_pi_norm (p11R1 T R z) j).trans (h6 z hz)⟩

/-! ### `bpP:p11a:cutoff` -/

/-- `R_*` is a trigonometric polynomial of degree at most `T` in the angles with coefficients
`c k b`, admissible on `ℂᴺ × B`: holomorphic there and one-periodic in each angle. -/
def p11TrigPolyAdm {n : ℕ} (T : ℝ) (B : Set (P11CVec n))
    (P : P11CVec n × P11CVec n → ℂ) : Prop :=
  (∃ c : (Fin n → ℤ) → P11CVec n → ℂ, (∀ k b, T < KAM.Fourier.modeSize k → c k b = 0) ∧
    ∀ θ b : P11CVec n, b ∈ B → P (θ, b) = ∑ k ∈ hmModes n T, c k b * KAM.character k θ) ∧
  DifferentiableOn ℂ P (univ ×ˢ B) ∧
  ∀ j : Fin n, ∀ z ∈ (univ : Set (P11CVec n)) ×ˢ B, P (z.1 + Pi.single j 1, z.2) = P z

/-- `bpP:p11a:cutoff`: the composed cutoff `R ↦ R_*`. The premises `d ≤ 1`, `T ≥ 1` of the loss
addendum are added (candidate source erratum, `p11a2-cutoff-step.tex:124`). -/
theorem p11_cutoff_node {n : ℕ} (hn : 1 ≤ n) {r s T d eps q : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : 0 ≤ T) (hd : 0 < d) (hdr : d < r)
    (he : 0 ≤ eps) (hq : 0 < q) (hq1 : q < 1)
    {B : Set (P11CVec n)} (hB : IsOpen B) {R : P11Family n → ℂ}
    (hR : p11Admissible r s B R) (hb : p11Bound (domain_def n r s B) R eps) :
    ((∀ θ b : P11CVec n, p11R0 T R (θ, b) = KAM.Weighted.truncate T
        (fun u : P11CVec n × P11CVec n => R ((u.1, 0), u.2)) (θ, b)) ∧
      (∀ (j : Fin n) (θ b : P11CVec n), b ∈ B → p11R1 T R (θ, b) j = KAM.Weighted.truncate T
        (fun u : P11CVec n × P11CVec n =>
          fderiv ℂ (fun η => R ((u.1, η), u.2)) 0 (Pi.single j 1)) (θ, b)) ∧
      ∀ z : P11Family n, z.2 ∈ B → p11Cutoff T R z = p11R0 T R (z.1.1, z.2) +
        ∑ i, p11R1 T R (z.1.1, z.2) i * z.1.2 i) ∧
    (p11TrigPolyAdm T B (p11R0 T R) ∧ ∀ j : Fin n, p11TrigPolyAdm T B (fun z => p11R1 T R z j)) ∧
    (p11Bound (domain_def n (r-d) s B) (p11Cutoff T R) (2*(1+p11Error n T d)*eps) ∧
      p11Bound (KAM.complexStrip n (r-d) ×ˢ B) (p11R0 T R) ((1+p11Error n T d)*eps) ∧
      ∀ j : Fin n, p11Bound (KAM.complexStrip n (r-d) ×ˢ B) (fun z => p11R1 T R z j)
        ((1+p11Error n T d)*eps/s)) ∧
    p11Bound (domain_def n (r-d) (q*s) B) (R - p11Cutoff T R)
      (eps*(q^2/(1-q)+2*p11Error n T d)) ∧
    (p11Real (domain_def n r s B) R → p11Real (domain_def n (r-d) s B) (p11Cutoff T R)) ∧
    ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 → 1 ≤ T → d = p11Loss n T alpha → d ≤ 1 →
      p11Error n T d ≤ alpha ∧
      p11Bound (domain_def n (r-d) (q*s) B) (R - p11Cutoff T R)
        (eps*(q^2/(1-q)+2*alpha)) := by
  obtain ⟨-, -, hb2, hreal⟩ := p11_cutoff hn hr hs hT hd hdr he hq hq1 hB hR hb
  obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩ := p11_cu_coeff (T := T) hr hs hB hR
  refine ⟨⟨fun θ b => ?_, fun j θ b hbB => ?_, ?_⟩, ⟨?_, fun j => ?_⟩,
    p11_cu_a hn hr hs hT hd hdr he hB hR hb, hb2, hreal, ?_⟩
  · exact cutoff_R0 θ b
  · exact cutoff_R1 hr hs hB hR θ hbB j
  · exact (p11_cutoff_coeff hn hr hs hT hd hdr he hB hR hb).2.2.2.2.2.2
  · refine ⟨⟨fun k b => if KAM.Fourier.modeSize k ≤ T then KAM.Weighted.coeff
      (fun u : P11CVec n × P11CVec n => R ((u.1, 0), u.2)) b k else 0, fun k b hk => ?_,
      fun θ b hbB => hc2 θ b hbB⟩, hc4⟩
    simp [not_le.mpr hk]
  · refine ⟨⟨fun k b => if KAM.Fourier.modeSize k ≤ T then KAM.Weighted.coeff
      (fun u : P11CVec n × P11CVec n => fderiv ℂ (fun η => R ((u.1, η), u.2)) 0
        (Pi.single j 1)) b k else 0, fun k b hk => ?_, fun θ b hbB => hc3 j θ b hbB⟩,
      (hc5 j)⟩
    simp [not_le.mpr hk]
  · intro alpha ha ha1 hT1 hdef hd1
    have hE : p11Error n T d ≤ alpha := by
      subst hdef
      exact (loss_choice hn ha ha1 hT1).2.1 hd1
    refine ⟨hE, fun z hz => (hb2 z hz).trans ?_⟩
    gcongr

end KAM.Planetary

end
