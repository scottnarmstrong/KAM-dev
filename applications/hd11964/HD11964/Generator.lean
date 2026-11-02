/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.CellCauchy

/-!
# HD 11964: the exact generator and its certified remainder (HD11964-LEMMAS, piece 2)

The Lean `F = approxIntegral₂ k χ₁ χ₂` of the bridge is one global function, so its generators are
the **exact** `χ* = Π_S P / (i k·ω(Λ))` (P2B ruling); the producer's polynomials are the centres of
their per-cell enclosures. Here:

* `chiStar S ω P`: the exact generator on the chart, `Re Σ_{k ∈ S} P̂_k / (i k·ω(Λ)) e^{i k·λ}`,
  with the Fourier coefficients `chartCoeff` over the fast angles (`χ₁` with `P`, `χ₂` with `G₂`).
* `genChi S om P`: its per-cell form in kamx-hd-layer's variables (`θ = λ/2π`, cell variables
  `u`), for a complex function `P` on the strip × polydisc.
* `norm_genChi_sub_le` (2a), **the certified remainder**: from a model of `P` (centre `p`,
  remainder `r_P`) and models of `1/(i k·ω)` (polynomials `q k`, remainders `ε k`, bounds `B k`),
  the producer's centre `c` is within
  `Σ_{k ∈ S} e^{2πρ|k|₁} (r_P B_k + ‖p_k‖₁ ε_k + ‖p_k q_k - c_k‖₁)`.
* `abs_chiStar_sub_le`: (2a) and (2b) composed on a well-formed cell, `|χ*(w) - Re c| ≤` the (2a)
  bound (AUDIT-HD11964-LEMMAS-1, L4; the auditor's probe).
* `chiStar_eq_re_genChi` (2b): on a cell, if the complex function agrees with `P` at real points
  and `om` with `ω(Λ)`, the global generator is the real part of the cell generator.
-/

@[expose] public noncomputable section

open Set Filter Topology KAM KAM.Planetary KAM.Application.LambdaDrift
open scoped Real

namespace HD11964.Cover

/-! ### Characters, Fourier coefficients, the generator -/

/-- The character `e(k·θ) = exp (2πi k·θ)` (kamx-hd-layer's convention `θ = λ/2π`). -/
def charE (k : Fin 2 → ℤ) (θ : Fin 2 → ℂ) : ℂ :=
  Complex.exp (2 * π * Complex.I * ∑ i, (k i : ℂ) * θ i)

/-- The Fourier coefficient in `θ` over the real torus `[0, 1]²`, at the cell variables `u`. -/
def fourierCoeff2 (P : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ) (k : Fin 2 → ℤ) (u : Fin 6 → ℂ) : ℂ :=
  ∫ t₀ in (0 : ℝ)..1, ∫ t₁ in (0 : ℝ)..1,
    P ![(t₀ : ℂ), (t₁ : ℂ)] u * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)]

/-- **The generator in the cell variables**: `χ(θ, u) = Σ_{k ∈ S} P̂_k(u) / (i k·ω(u)) e(k·θ)`,
`om u` the frequency vector at the cell variables `u`.

**Conditions on `S`** (not hypotheses of the definition): it is the intended generator only for
`S = -S`, `0 ∉ S` and `k·ω ≠ 0` on `S`. Lean's `0⁻¹ = 0` silently drops every mode with `k·ω = 0`
(`k = 0` included); the theorems that need the generator's meaning take these as hypotheses. -/
def genChi (S : Finset (Fin 2 → ℤ)) (om : (Fin 6 → ℂ) → Fin 2 → ℂ)
    (P : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ) (θ : Fin 2 → ℂ) (u : Fin 6 → ℂ) : ℂ :=
  ∑ k ∈ S, fourierCoeff2 P k u * (Complex.I * ∑ i, (k i : ℂ) * om u i)⁻¹ * charE k θ

/-- A Taylor × Fourier polynomial: finitely many modes, each with a polynomial coefficient in the
cell variables (the producer's data). -/
abbrev TFPoly := (Fin 2 → ℤ) →₀ MvPolynomial (Fin 6) ℂ

/-- Its value. -/
def TFPoly.eval (p : TFPoly) (θ : Fin 2 → ℂ) (u : Fin 6 → ℂ) : ℂ :=
  p.sum fun k q => MvPolynomial.eval u q * charE k θ

/-- The ℓ¹ norm of a polynomial's coefficients (its bound on the unit polydisc). -/
def l1 (q : MvPolynomial (Fin 6) ℂ) : ℝ := ∑ m ∈ q.support, ‖q.coeff m‖

/-! ### Bounds -/

/-- A polynomial is bounded by the ℓ¹ norm of its coefficients on the unit polydisc. -/
theorem norm_eval_le_l1 (q : MvPolynomial (Fin 6) ℂ) {u : Fin 6 → ℂ} (hu : u ∈ polyDiscC 6 1) :
    ‖MvPolynomial.eval u q‖ ≤ l1 q := by
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul]
  have h : ‖∏ i ∈ m.support, u i ^ m i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hu i)
  calc ‖q.coeff m‖ * ‖∏ i ∈ m.support, u i ^ m i‖ ≤ ‖q.coeff m‖ * 1 :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = ‖q.coeff m‖ := mul_one _

/-- The characters on the strip: `|e(k·θ)| ≤ e^{2πρ|k|₁}`. -/
theorem norm_charE_le {ρ : ℝ} {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 ρ) (k : Fin 2 → ℤ) :
    ‖charE k θ‖ ≤ Real.exp (2 * π * ρ * ∑ i, |(k i : ℝ)|) := by
  rw [charE, Complex.norm_exp, Real.exp_le_exp]
  have hre : (2 * π * Complex.I * ∑ i, (k i : ℂ) * θ i).re =
      -(2 * π) * ∑ i, (k i : ℝ) * (θ i).im := by
    simp [Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
  rw [hre]
  have hb : ∀ i, -((k i : ℝ) * (θ i).im) ≤ |(k i : ℝ)| * ρ := fun i => by
    calc -((k i : ℝ) * (θ i).im) ≤ |(k i : ℝ) * (θ i).im| := neg_le_abs _
      _ = |(k i : ℝ)| * |(θ i).im| := abs_mul _ _
      _ ≤ |(k i : ℝ)| * ρ := mul_le_mul_of_nonneg_left (hθ i).le (abs_nonneg _)
  simp only [Fin.sum_univ_two]
  nlinarith [hb 0, hb 1, Real.pi_pos]

/-- `‖∫₀¹ ∫₀¹ f‖ ≤ r` when `‖f‖ ≤ r`. -/
theorem norm_iint_le {f : ℝ → ℝ → ℂ} {r : ℝ} (h : ∀ t₀ t₁, ‖f t₀ t₁‖ ≤ r) :
    ‖∫ t₀ in (0 : ℝ)..1, ∫ t₁ in (0 : ℝ)..1, f t₀ t₁‖ ≤ r := by
  have h1 : ∀ t₀, ‖∫ t₁ in (0 : ℝ)..1, f t₀ t₁‖ ≤ r := fun t₀ => by
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      fun t₁ _ => h t₀ t₁
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    fun t₀ _ => h1 t₀

/-! ### Continuity, linearity and orthogonality of the Fourier coefficients -/

theorem vec2_ofReal (t₀ t₁ : ℝ) : ![(t₀ : ℂ), (t₁ : ℂ)] = fun i => ((![t₀, t₁] i : ℝ) : ℂ) := by
  funext i
  fin_cases i <;> rfl

theorem continuous_vec2 : Continuous fun p : ℝ × ℝ => (![p.1, p.2] : Fin 2 → ℝ) :=
  continuous_fst.matrixVecCons (continuous_snd.matrixVecCons continuous_const)

theorem continuous_charE (k : Fin 2 → ℤ) :
    Continuous fun p : ℝ × ℝ => charE k ![(p.1 : ℂ), (p.2 : ℂ)] := by
  unfold charE
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  fun_prop

/-- The integrand of a Fourier coefficient is continuous. -/
theorem continuous_coeffIntegrand {P : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ} {u : Fin 6 → ℂ}
    (hP : Continuous fun t : Fin 2 → ℝ => P (fun i => (t i : ℂ)) u) (k : Fin 2 → ℤ) :
    Continuous fun p : ℝ × ℝ =>
      P ![(p.1 : ℂ), (p.2 : ℂ)] u * charE (-k) ![(p.1 : ℂ), (p.2 : ℂ)] := by
  have h1 : (fun p : ℝ × ℝ => P ![(p.1 : ℂ), (p.2 : ℂ)] u) =
      (fun t : Fin 2 → ℝ => P (fun i => (t i : ℂ)) u) ∘ fun p : ℝ × ℝ => ![p.1, p.2] := by
    funext p
    simp only [Function.comp, vec2_ofReal]
  have hc : Continuous fun p : ℝ × ℝ => P ![(p.1 : ℂ), (p.2 : ℂ)] u := by
    rw [h1]
    exact hP.comp continuous_vec2
  exact hc.mul (continuous_charE (-k))

/-- The Fourier coefficient is linear (for functions continuous in real `θ`). -/
theorem fourierCoeff2_sub {P Q : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ} {u : Fin 6 → ℂ}
    (hP : Continuous fun t : Fin 2 → ℝ => P (fun i => (t i : ℂ)) u)
    (hQ : Continuous fun t : Fin 2 → ℝ => Q (fun i => (t i : ℂ)) u) (k : Fin 2 → ℤ) :
    fourierCoeff2 P k u - fourierCoeff2 Q k u = fourierCoeff2 (fun θ v => P θ v - Q θ v) k u := by
  have cP := continuous_coeffIntegrand hP k
  have cQ := continuous_coeffIntegrand hQ k
  have iP : ∀ t₀ : ℝ, IntervalIntegrable
      (fun t₁ : ℝ => P ![(t₀ : ℂ), (t₁ : ℂ)] u * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)])
      MeasureTheory.volume 0 1 := fun t₀ =>
    (cP.comp (Continuous.prodMk_right t₀)).intervalIntegrable (μ := MeasureTheory.volume) 0 1
  have iQ : ∀ t₀ : ℝ, IntervalIntegrable
      (fun t₁ : ℝ => Q ![(t₀ : ℂ), (t₁ : ℂ)] u * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)])
      MeasureTheory.volume 0 1 := fun t₀ =>
    (cQ.comp (Continuous.prodMk_right t₀)).intervalIntegrable (μ := MeasureTheory.volume) 0 1
  have oP := (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t₀ t₁ : ℝ => P ![(t₀ : ℂ), (t₁ : ℂ)] u * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)])
    (μ := MeasureTheory.volume) cP 0 1).intervalIntegrable (μ := MeasureTheory.volume) 0 1
  have oQ := (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t₀ t₁ : ℝ => Q ![(t₀ : ℂ), (t₁ : ℂ)] u * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)])
    (μ := MeasureTheory.volume) cQ 0 1).intervalIntegrable (μ := MeasureTheory.volume) 0 1
  unfold fourierCoeff2
  rw [← intervalIntegral.integral_sub oP oQ]
  refine intervalIntegral.integral_congr fun t₀ _ => ?_
  rw [← intervalIntegral.integral_sub (iP t₀) (iQ t₀)]
  refine intervalIntegral.integral_congr fun t₁ _ => ?_
  ring

/-- `∫₀¹ e^{2πinx} dx = [n = 0]`. -/
theorem integral_exp_two_pi_int (n : ℤ) :
    ∫ x in (0 : ℝ)..1, Complex.exp (2 * π * Complex.I * n * x) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · have hc : (2 * π * Complex.I * n : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hn]
    have h1 : Complex.exp (2 * π * Complex.I * n) = 1 := by
      rw [show (2 * π * Complex.I * n : ℂ) = n * (2 * π * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [integral_exp_mul_complex hc]
    simp [hn, h1]

/-- **Orthogonality of the characters** over `[0, 1]²`. -/
theorem iint_charE_mul (k' k : Fin 2 → ℤ) :
    ∫ t₀ in (0 : ℝ)..1, ∫ t₁ in (0 : ℝ)..1,
      charE k' ![(t₀ : ℂ), (t₁ : ℂ)] * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)] =
      if k' = k then 1 else 0 := by
  have e : ∀ t₀ t₁ : ℝ,
      charE k' ![(t₀ : ℂ), (t₁ : ℂ)] * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)] =
        Complex.exp (2 * π * Complex.I * ((k' 0 - k 0 : ℤ) : ℂ) * t₀) *
          Complex.exp (2 * π * Complex.I * ((k' 1 - k 1 : ℤ) : ℂ) * t₁) := by
    intro t₀ t₁
    simp only [charE, ← Complex.exp_add, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.neg_apply]
    congr 1
    push_cast
    ring
  simp_rw [e, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_mul_const, integral_exp_two_pi_int, integral_exp_two_pi_int]
  by_cases h : k' = k
  · subst h
    simp
  · have h' : k' 0 - k 0 ≠ 0 ∨ k' 1 - k 1 ≠ 0 := by
      by_contra hc
      push Not at hc
      apply h
      funext i
      fin_cases i
      · exact sub_eq_zero.mp hc.1
      · exact sub_eq_zero.mp hc.2
    rcases h' with h0 | h1
    · simp [h, h0]
    · simp [h, h1]

/-- The Fourier coefficient of a Taylor × Fourier polynomial is its coefficient. -/
theorem fourierCoeff2_eval (p : TFPoly) (k : Fin 2 → ℤ) (u : Fin 6 → ℂ) :
    fourierCoeff2 (fun θ v => p.eval θ v) k u = MvPolynomial.eval u (p k) := by
  have cE : ∀ k' : Fin 2 → ℤ, Continuous fun q : ℝ × ℝ =>
      charE k' ![(q.1 : ℂ), (q.2 : ℂ)] * charE (-k) ![(q.1 : ℂ), (q.2 : ℂ)] :=
    fun k' => (continuous_charE k').mul (continuous_charE (-k))
  unfold fourierCoeff2 TFPoly.eval
  simp only [Finsupp.sum, Finset.sum_mul, mul_assoc]
  have inner : ∀ t₀ : ℝ, ∫ t₁ in (0 : ℝ)..1, ∑ k' ∈ p.support, MvPolynomial.eval u (p k') *
      (charE k' ![(t₀ : ℂ), (t₁ : ℂ)] * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)]) =
      ∑ k' ∈ p.support, MvPolynomial.eval u (p k') * ∫ t₁ in (0 : ℝ)..1,
        charE k' ![(t₀ : ℂ), (t₁ : ℂ)] * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)] := by
    intro t₀
    have h := intervalIntegral.integral_finsetSum (μ := MeasureTheory.volume) (a := 0) (b := 1)
      (s := p.support) (f := fun k' t₁ => MvPolynomial.eval u (p k') *
        (charE k' ![(t₀ : ℂ), (t₁ : ℂ)] * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)]))
      fun k' _ => (continuous_const.mul
        ((cE k').comp (Continuous.prodMk_right t₀))).intervalIntegrable
          (μ := MeasureTheory.volume) 0 1
    rw [h]
    exact Finset.sum_congr rfl fun k' _ => intervalIntegral.integral_const_mul _ _
  simp_rw [inner]
  have h := intervalIntegral.integral_finsetSum (μ := MeasureTheory.volume) (a := 0) (b := 1)
    (s := p.support) (f := fun k' t₀ => MvPolynomial.eval u (p k') * ∫ t₁ in (0 : ℝ)..1,
      charE k' ![(t₀ : ℂ), (t₁ : ℂ)] * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)])
    fun k' _ => (continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := MeasureTheory.volume)
        (f := fun t₀ t₁ : ℝ => charE k' ![(t₀ : ℂ), (t₁ : ℂ)] * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)])
        (cE k') 0 1)).intervalIntegrable (μ := MeasureTheory.volume) 0 1
  rw [h]
  simp_rw [intervalIntegral.integral_const_mul, iint_charE_mul]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  split_ifs with hk
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hk, map_zero]

/-! ### The certified remainder -/

/-- **The certified remainder of the generator** (2a). Given a model of `P` (centre `p`,
remainder `r_P` on the strip of width `ρ` times the unit polydisc; `P` continuous in real `θ`),
models of `1/(i k·ω(u))` (polynomials `q k`, remainders `ε k`, bounds `B k`) for `k ∈ S`, and the
producer's centre `c` supported on `S`, the generator is the centre up to
`Σ_{k ∈ S} e^{2πρ|k|₁} (r_P B_k + ‖p_k‖₁ ε_k + ‖p_k q_k - c_k‖₁)`. -/
theorem norm_genChi_sub_le (S : Finset (Fin 2 → ℤ)) (om : (Fin 6 → ℂ) → Fin 2 → ℂ)
    (P : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ) {ρ rP : ℝ} (p c : TFPoly)
    (q : (Fin 2 → ℤ) → MvPolynomial (Fin 6) ℂ) (ε B : (Fin 2 → ℤ) → ℝ) (hρ : 0 < ρ)
    (hP : ∀ θ ∈ complexStrip 2 ρ, ∀ u ∈ polyDiscC 6 1, ‖P θ u - p.eval θ u‖ ≤ rP)
    (hPc : ∀ u ∈ polyDiscC 6 1, Continuous fun t : Fin 2 → ℝ => P (fun i => (t i : ℂ)) u)
    (hq : ∀ k ∈ S, ∀ u ∈ polyDiscC 6 1,
      ‖(Complex.I * ∑ i, (k i : ℂ) * om u i)⁻¹ - MvPolynomial.eval u (q k)‖ ≤ ε k)
    (hB : ∀ k ∈ S, ∀ u ∈ polyDiscC 6 1, ‖(Complex.I * ∑ i, (k i : ℂ) * om u i)⁻¹‖ ≤ B k)
    (hc : ↑c.support ⊆ (S : Set (Fin 2 → ℤ))) :
    ∀ θ ∈ complexStrip 2 ρ, ∀ u ∈ polyDiscC 6 1, ‖genChi S om P θ u - c.eval θ u‖ ≤
      ∑ k ∈ S, Real.exp (2 * π * ρ * ∑ i, |(k i : ℝ)|) *
        (rP * B k + l1 (p k) * ε k + l1 (p k * q k - c k)) := by
  intro θ hθ u hu
  -- the model's continuity in real `θ`
  have hpc : Continuous fun t : Fin 2 → ℝ => p.eval (fun i => (t i : ℂ)) u := by
    unfold TFPoly.eval charE
    simp only [Finsupp.sum, Fin.sum_univ_two]
    fun_prop
  -- `|P̂_k - p_k| ≤ r_P`
  have hcoef : ∀ k, ‖fourierCoeff2 P k u - MvPolynomial.eval u (p k)‖ ≤ rP := by
    intro k
    rw [← fourierCoeff2_eval p k u, fourierCoeff2_sub (hPc u hu) hpc k]
    refine norm_iint_le fun t₀ t₁ => ?_
    rw [norm_mul]
    have hreal : (![(t₀ : ℂ), (t₁ : ℂ)] : Fin 2 → ℂ) ∈ complexStrip 2 ρ := by
      intro i
      fin_cases i <;> simpa using hρ
    have h1 : ‖charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)]‖ = 1 := by
      rw [charE, Complex.norm_exp]
      simp [Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
    rw [h1, mul_one]
    exact hP _ hreal u hu
  -- the centre over `S`
  have hceval : c.eval θ u = ∑ k ∈ S, MvPolynomial.eval u (c k) * charE k θ := by
    unfold TFPoly.eval
    exact Finsupp.sum_of_support_subset c (fun k hk => hc hk) _ fun k _ => by simp
  rw [hceval, genChi, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  set inv := (Complex.I * ∑ i, (k i : ℂ) * om u i)⁻¹
  set ph := MvPolynomial.eval u (p k)
  have hsplit : fourierCoeff2 P k u * inv * charE k θ - MvPolynomial.eval u (c k) * charE k θ =
      ((fourierCoeff2 P k u - ph) * inv + ph * (inv - MvPolynomial.eval u (q k)) +
        MvPolynomial.eval u (p k * q k - c k)) * charE k θ := by
    rw [map_sub, map_mul]
    ring
  rw [hsplit, norm_mul, mul_comm]
  refine mul_le_mul (norm_charE_le hθ k) ?_ (norm_nonneg _) (Real.exp_pos _).le
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_))
    (norm_eval_le_l1 _ hu))
  · rw [norm_mul]
    exact mul_le_mul (hcoef k) (hB k hk u hu) (norm_nonneg _)
      ((norm_nonneg _).trans (hcoef k))
  · rw [norm_mul]
    exact mul_le_mul (norm_eval_le_l1 _ hu) (hq k hk u hu) (norm_nonneg _)
      ((norm_nonneg _).trans (norm_eval_le_l1 _ hu))

/-! ### The exact generator on the chart, and the link -/

/-- The chart state `w` with its fast angles replaced by `λ`. -/
def withAngles (w : Phase (2 + 2)) (lam : Fin 2 → ℝ) : Phase (2 + 2) :=
  assemble (fast w.2) lam (slow w.2) (slow w.1)

/-- The Fourier coefficient of a chart function in the fast angles `λ = 2πt`, at the slow
variables and actions of `w`. -/
def chartCoeff (P : Phase (2 + 2) → ℝ) (k : Fin 2 → ℤ) (w : Phase (2 + 2)) : ℂ :=
  ∫ t₀ in (0 : ℝ)..1, ∫ t₁ in (0 : ℝ)..1,
    (P (withAngles w ![2 * π * t₀, 2 * π * t₁]) : ℂ) * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)]

/-- **The exact generator on the chart**: `χ*(w) = Re Σ_{k ∈ S} P̂_k / (i k·ω(Λ)) e^{i k·λ}`, a
global function (the Lean `χ₁`, `χ₂` of `approxIntegral₂`, with `P` resp. `G₂`).

**Conditions on `S`** (AUDIT-HD11964-LEMMAS-1, L1; not hypotheses of the definition): `χ*` solves
`{χ*, h} = Π_S P` only if `S = -S`, `0 ∉ S` and `k·ω(Λ) ≠ 0` on the set considered. Lean's
`0⁻¹ = 0` silently drops every mode with `k·ω = 0` (`k = 0` included), and `.re` halves every mode
whose partner `-k` is missing (`Re Σ_S = ½ Σ_{S ∪ -S}` termwise for real `P`). The homological
equation and the smoothness of `χ*` take these conditions as hypotheses (HD11964-CHI). -/
def chiStar (S : Finset (Fin 2 → ℤ)) (ω : (Fin 2 → ℝ) → Fin 2 → ℝ) (P : Phase (2 + 2) → ℝ)
    (w : Phase (2 + 2)) : ℝ :=
  (∑ k ∈ S, chartCoeff P k w * (Complex.I * ∑ i, (k i : ℂ) * ω (fast w.2) i)⁻¹ *
    charE k (fun i => ((fast w.1 i / (2 * π) : ℝ) : ℂ))).re

/-- **The link** (2b): on a cell, if the complex function `Pc` agrees with `P` at real points and
`om` with `ω(Λ)`, the global generator is the real part of the cell generator. -/
theorem chiStar_eq_re_genChi (k : AffineCell) (S : Finset (Fin 2 → ℤ))
    (ω : (Fin 2 → ℝ) → Fin 2 → ℝ) (P : Phase (2 + 2) → ℝ) (Pc : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ)
    (om : (Fin 6 → ℂ) → Fin 2 → ℂ)
    (hP : ∀ w ∈ k.toSet, ∀ t : Fin 2 → ℝ,
      Pc (fun i => (t i : ℂ)) (fun j => (k.coord (cellCoord w) j : ℂ)) =
        (P (withAngles w (fun i => 2 * π * t i)) : ℂ))
    (hom : ∀ w ∈ k.toSet,
      om (fun j => (k.coord (cellCoord w) j : ℂ)) = fun i => (ω (fast w.2) i : ℂ)) :
    ∀ w ∈ k.toSet, chiStar S ω P w =
      (genChi S om Pc (fun i => ((fast w.1 i / (2 * π) : ℝ) : ℂ))
        (fun j => (k.coord (cellCoord w) j : ℂ))).re := by
  intro w hw
  unfold chiStar genChi
  congr 1
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [hom w hw]
  congr 2
  unfold chartCoeff fourierCoeff2
  refine intervalIntegral.integral_congr fun t₀ _ => intervalIntegral.integral_congr fun t₁ _ => ?_
  rw [vec2_ofReal t₀ t₁, hP w hw ![t₀, t₁]]
  congr 3
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **The certified remainder on a cell** (AUDIT-HD11964-LEMMAS-1, L4; the auditor's
`AuditCompose.abs_chiStar_sub_le`): on a well-formed cell, where `Pc` and `om` agree with `P` and
`ω(Λ)` at real points, the global generator differs from the real part of the producer's centre at
the cell variables of `w` by at most the bound of `norm_genChi_sub_le`. -/
theorem abs_chiStar_sub_le (k : AffineCell) (hk : k.wf = true) (S : Finset (Fin 2 → ℤ))
    (ω : (Fin 2 → ℝ) → Fin 2 → ℝ) (P : Phase (2 + 2) → ℝ) (Pc : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ)
    (om : (Fin 6 → ℂ) → Fin 2 → ℂ) {ρ rP : ℝ} (p c : TFPoly)
    (q : (Fin 2 → ℤ) → MvPolynomial (Fin 6) ℂ) (ε B : (Fin 2 → ℤ) → ℝ) (hρ : 0 < ρ)
    (hP : ∀ θ ∈ complexStrip 2 ρ, ∀ u ∈ polyDiscC 6 1, ‖Pc θ u - p.eval θ u‖ ≤ rP)
    (hPc : ∀ u ∈ polyDiscC 6 1, Continuous fun t : Fin 2 → ℝ => Pc (fun i => (t i : ℂ)) u)
    (hq : ∀ κ ∈ S, ∀ u ∈ polyDiscC 6 1,
      ‖(Complex.I * ∑ i, (κ i : ℂ) * om u i)⁻¹ - MvPolynomial.eval u (q κ)‖ ≤ ε κ)
    (hB : ∀ κ ∈ S, ∀ u ∈ polyDiscC 6 1, ‖(Complex.I * ∑ i, (κ i : ℂ) * om u i)⁻¹‖ ≤ B κ)
    (hc : ↑c.support ⊆ (S : Set (Fin 2 → ℤ)))
    (hlP : ∀ w ∈ k.toSet, ∀ t : Fin 2 → ℝ,
      Pc (fun i => (t i : ℂ)) (fun j => (k.coord (cellCoord w) j : ℂ)) =
        (P (withAngles w (fun i => 2 * π * t i)) : ℂ))
    (hlom : ∀ w ∈ k.toSet,
      om (fun j => (k.coord (cellCoord w) j : ℂ)) = fun i => (ω (fast w.2) i : ℂ))
    (w : Phase (2 + 2)) (hw : w ∈ k.toSet) :
    |chiStar S ω P w - (c.eval (fun i => ((fast w.1 i / (2 * π) : ℝ) : ℂ))
        (fun j => (k.coord (cellCoord w) j : ℂ))).re| ≤
      ∑ κ ∈ S, Real.exp (2 * π * ρ * ∑ i, |(κ i : ℝ)|) *
        (rP * B κ + l1 (p κ) * ε κ + l1 (p κ * q κ - c κ)) := by
  obtain ⟨u, hu, hx⟩ := hw
  have hw' : w ∈ k.toSet := ⟨u, hu, hx⟩
  have hU : (fun j => (k.coord (cellCoord w) j : ℂ)) ∈ polyDiscC 6 1 := by
    intro j
    rw [hx, AffineCell.coord_map k hk u, Complex.norm_real, Real.norm_eq_abs]
    exact hu j
  have hθ : (fun i => ((fast w.1 i / (2 * π) : ℝ) : ℂ)) ∈ complexStrip 2 ρ := fun i => by
    show |(((fast w.1 i / (2 * π) : ℝ) : ℂ)).im| < ρ
    rw [Complex.ofReal_im, abs_zero]
    exact hρ
  rw [chiStar_eq_re_genChi k S ω P Pc om hlP hlom w hw', ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans
    (norm_genChi_sub_le S om Pc p c q ε B hρ hP hPc hq hB hc _ hθ _ hU)

end HD11964.Cover

end
