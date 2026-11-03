/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.RealRestriction
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Cauchy estimates on complex polydiscs, real slice, geometric tail (track B, package B2-CAUCHY)

* `norm_fderiv_le_of_closedDisc`, `norm_fderiv_coord_le`: a function holomorphic near a closed
  complex disc in direction `e`, bounded by `M` there, has `‖fderiv ℂ f z e‖ ≤ M / δ`.
* `norm_fderiv_fst_le_of_cpolydisc`, `norm_fderiv_snd_le_of_cpolydisc`: polydisc form.
* `fderiv_realPart_eq`, `abs_fderiv_realPart_fst_le`, `abs_fderiv_realPart_snd_le`: real slice.
* `abs_actionBracket_le_of_cauchy`: bound on `q_j ∂_{p_j} R - p_j ∂_{q_j} R`.
* `hasSum_nat_mul_geometric_tail`, `sum_range_nat_mul_geometric_tail_le`: geometric tail.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open KAM Metric Set

section Cauchy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- General Cauchy estimate along a direction `e`. -/
theorem norm_fderiv_le_of_closedDisc {f : E → ℂ} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {z : E} (e : E) {δ M : ℝ} (hδ : 0 < δ)
    (hsub : ∀ ζ : ℂ, ‖ζ‖ ≤ δ → z + ζ • e ∈ U)
    (hM : ∀ ζ : ℂ, ‖ζ‖ ≤ δ → ‖f (z + ζ • e)‖ ≤ M) :
    ‖fderiv ℂ f z e‖ ≤ M / δ := by
  set g : ℂ → ℂ := fun ζ => f (z + ζ • e) with hg
  have hlin : ∀ ζ : ℂ, HasDerivAt (fun ζ : ℂ => z + ζ • e) e ζ := fun ζ => by
    simpa using ((hasDerivAt_id ζ).smul_const e).const_add z
  have hgd : ∀ ζ : ℂ, ‖ζ‖ ≤ δ → DifferentiableAt ℂ g ζ := fun ζ hζ =>
    (((hf.differentiableAt (hU.mem_nhds (hsub ζ hζ))).hasFDerivAt).comp_hasDerivAt ζ
      (hlin ζ)).differentiableAt
  have hcont : ContinuousOn g (closedBall (0 : ℂ) δ) := fun ζ hζ =>
    (hgd ζ (by simpa using hζ)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℂ g (ball (0 : ℂ) δ) := fun ζ hζ =>
    (hgd ζ (by simpa using (mem_ball_zero_iff.mp hζ).le)).differentiableWithinAt
  have hdc : DiffContOnCl ℂ g (ball (0 : ℂ) δ) :=
    ⟨hdiff, hcont.mono (by rw [closure_ball _ hδ.ne'])⟩
  have h1 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ hdc
    (fun ζ hζ => hM ζ (by simpa using hζ.le))
  have h2 : HasDerivAt g (fderiv ℂ f z e) 0 := by
    have := (hf.differentiableAt (hU.mem_nhds (by simpa using hsub 0 (by simp [hδ.le]))))
    have hz : HasFDerivAt f (fderiv ℂ f z) (z + (0 : ℂ) • e) := by simpa using this.hasFDerivAt
    exact hz.comp_hasDerivAt (0 : ℂ) (hlin 0)
  rwa [h2.deriv] at h1

/-- Coordinate Cauchy estimate in a general direction `e`. -/
theorem norm_fderiv_coord_le {f : E → ℂ} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {z : E} (e : E) {δ M : ℝ} (hδ : 0 < δ)
    (hsub : {w | ∃ ζ : ℂ, ‖ζ‖ ≤ δ ∧ w = z + ζ • e} ⊆ U)
    (hM : ∀ w ∈ {w | ∃ ζ : ℂ, ‖ζ‖ ≤ δ ∧ w = z + ζ • e}, ‖f w‖ ≤ M) :
    ‖fderiv ℂ f z e‖ ≤ M / δ :=
  norm_fderiv_le_of_closedDisc hU hf e hδ (fun ζ hζ => hsub ⟨ζ, hζ, rfl⟩)
    (fun ζ hζ => hM _ ⟨ζ, hζ, rfl⟩)

end Cauchy

section Polydisc

variable {n : ℕ}

/-- Closed complex polydisc of radius `δ` about `z` (sup-norm coordinates). -/
def cpolydisc (z : (Fin n → ℂ) × (Fin n → ℂ)) (δ : ℝ) : Set ((Fin n → ℂ) × (Fin n → ℂ)) :=
  {w | ∀ i, ‖w.1 i - z.1 i‖ ≤ δ ∧ ‖w.2 i - z.2 i‖ ≤ δ}

theorem fst_mem_cpolydisc {z : (Fin n → ℂ) × (Fin n → ℂ)} {δ : ℝ} (hδ : 0 ≤ δ) (i : Fin n)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ δ) :
    z + ζ • ((Pi.single i 1 : Fin n → ℂ), (0 : Fin n → ℂ)) ∈ cpolydisc z δ := by
  intro j
  by_cases h : j = i
  · subst h; simp [hζ, hδ]
  · simp [h, hδ]

theorem snd_mem_cpolydisc {z : (Fin n → ℂ) × (Fin n → ℂ)} {δ : ℝ} (hδ : 0 ≤ δ) (i : Fin n)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ δ) :
    z + ζ • ((0 : Fin n → ℂ), (Pi.single i 1 : Fin n → ℂ)) ∈ cpolydisc z δ := by
  intro j
  by_cases h : j = i
  · subst h; simp [hζ, hδ]
  · simp [h, hδ]

/-- Polydisc form of the Cauchy estimate, `q`-direction. -/
theorem norm_fderiv_fst_le_of_cpolydisc {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} {δ M : ℝ} (hδ : 0 < δ) (hsub : cpolydisc z δ ⊆ U)
    (hM : ∀ w ∈ cpolydisc z δ, ‖f w‖ ≤ M) (i : Fin n) :
    ‖fderiv ℂ f z ((Pi.single i 1 : Fin n → ℂ), (0 : Fin n → ℂ))‖ ≤ M / δ :=
  norm_fderiv_le_of_closedDisc hU hf _ hδ (fun _ hζ => hsub (fst_mem_cpolydisc hδ.le i hζ))
    (fun _ hζ => hM _ (fst_mem_cpolydisc hδ.le i hζ))

/-- Polydisc form of the Cauchy estimate, `p`-direction. -/
theorem norm_fderiv_snd_le_of_cpolydisc {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} {δ M : ℝ} (hδ : 0 < δ) (hsub : cpolydisc z δ ⊆ U)
    (hM : ∀ w ∈ cpolydisc z δ, ‖f w‖ ≤ M) (i : Fin n) :
    ‖fderiv ℂ f z ((0 : Fin n → ℂ), (Pi.single i 1 : Fin n → ℂ))‖ ≤ M / δ :=
  norm_fderiv_le_of_closedDisc hU hf _ hδ (fun _ hζ => hsub (snd_mem_cpolydisc hδ.le i hζ))
    (fun _ hζ => hM _ (snd_mem_cpolydisc hδ.le i hζ))

/-- Real slice: `D (Re ∘ f ∘ ι) (x) v = Re (D f (ι x) (ι v))`. -/
theorem fderiv_realPart_eq {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : realInclusion₂ n x ∈ U) (v : (Fin n → ℝ) × (Fin n → ℝ)) :
    fderiv ℝ (fun y => (f (realInclusion₂ n y)).re) x v =
      (fderiv ℂ f (realInclusion₂ n x) (realInclusion₂ n v)).re := by
  have hd := (hf.differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have h1 := hd.restrictScalars ℝ
  have h2 := (Complex.reCLM.hasFDerivAt (x := f (realInclusion₂ n x))).comp x
    (h1.comp x (realInclusion₂ n).hasFDerivAt)
  rw [show (fun y => (f (realInclusion₂ n y)).re) =
    Complex.reCLM ∘ f ∘ (realInclusion₂ n) from rfl, h2.fderiv]
  simp

variable {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {U : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {x : (Fin n → ℝ) × (Fin n → ℝ)} {δ M : ℝ}

theorem abs_fderiv_realPart_fst_le (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hx : realInclusion₂ n x ∈ U) (hδ : 0 < δ) (hsub : cpolydisc (realInclusion₂ n x) δ ⊆ U)
    (hM : ∀ w ∈ cpolydisc (realInclusion₂ n x) δ, ‖f w‖ ≤ M) (i : Fin n) :
    |fderiv ℝ (fun y => (f (realInclusion₂ n y)).re) x ((Pi.single i 1 : Fin n → ℝ), 0)| ≤
      M / δ := by
  rw [fderiv_realPart_eq hU hf hx]
  have : realInclusion₂ n ((Pi.single i 1 : Fin n → ℝ), (0 : Fin n → ℝ)) =
      ((Pi.single i 1 : Fin n → ℂ), (0 : Fin n → ℂ)) := by
    ext j <;> by_cases h : j = i <;> simp [h]
  rw [this]
  exact (Complex.abs_re_le_norm _).trans (norm_fderiv_fst_le_of_cpolydisc hU hf hδ hsub hM i)

theorem abs_fderiv_realPart_snd_le (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hx : realInclusion₂ n x ∈ U) (hδ : 0 < δ) (hsub : cpolydisc (realInclusion₂ n x) δ ⊆ U)
    (hM : ∀ w ∈ cpolydisc (realInclusion₂ n x) δ, ‖f w‖ ≤ M) (i : Fin n) :
    |fderiv ℝ (fun y => (f (realInclusion₂ n y)).re) x (0, (Pi.single i 1 : Fin n → ℝ))| ≤
      M / δ := by
  rw [fderiv_realPart_eq hU hf hx]
  have : realInclusion₂ n ((0 : Fin n → ℝ), (Pi.single i 1 : Fin n → ℝ)) =
      ((0 : Fin n → ℂ), (Pi.single i 1 : Fin n → ℂ)) := by
    ext j <;> by_cases h : j = i <;> simp [h]
  rw [this]
  exact (Complex.abs_re_le_norm _).trans (norm_fderiv_snd_le_of_cpolydisc hU hf hδ hsub hM i)

/-- Action bracket of a holomorphic tail with Cauchy bound `M` on the `δ`-polydisc. -/
theorem abs_actionBracket_le_of_cauchy (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hx : realInclusion₂ n x ∈ U) (hδ : 0 < δ) (hsub : cpolydisc (realInclusion₂ n x) δ ⊆ U)
    (hM : ∀ w ∈ cpolydisc (realInclusion₂ n x) δ, ‖f w‖ ≤ M) (j : Fin n) :
    |x.1 j * fderiv ℝ (fun y => (f (realInclusion₂ n y)).re) x (0, (Pi.single j 1 : Fin n → ℝ)) -
        x.2 j * fderiv ℝ (fun y => (f (realInclusion₂ n y)).re) x
          ((Pi.single j 1 : Fin n → ℝ), 0)| ≤ (|x.1 j| + |x.2 j|) * (M / δ) := by
  have h1 := abs_fderiv_realPart_snd_le hU hf hx hδ hsub hM j
  have h2 := abs_fderiv_realPart_fst_le hU hf hx hδ hsub hM j
  calc _ ≤ |x.1 j * _| + |x.2 j * _| := abs_sub _ _
    _ = |x.1 j| * _ + |x.2 j| * _ := by rw [abs_mul, abs_mul]
    _ ≤ |x.1 j| * (M / δ) + |x.2 j| * (M / δ) := by gcongr
    _ = _ := by ring

end Polydisc

section Smoke

/-- Smoke test: coordinate function `w ↦ w.1 i`, derivative `1`, `M = ‖z.1 i‖ + δ`. -/
theorem smoke_coord {n : ℕ} (z : (Fin n → ℂ) × (Fin n → ℂ)) {δ : ℝ} (hδ : 0 < δ) (i : Fin n) :
    ‖fderiv ℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => w.1 i) z
        ((Pi.single i 1 : Fin n → ℂ), (0 : Fin n → ℂ))‖ ≤ (‖z.1 i‖ + δ) / δ := by
  refine norm_fderiv_le_of_closedDisc (U := Set.univ) isOpen_univ
    (f := fun w : (Fin n → ℂ) × (Fin n → ℂ) => w.1 i) (by fun_prop) _ hδ (fun _ _ => trivial)
    (fun ζ hζ => ?_)
  simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
    smul_eq_mul, mul_one]
  exact (norm_add_le _ _).trans (by gcongr)

end Smoke

section Tail

theorem geometric_tail_identity {x : ℝ} (h1 : x < 1) (d : ℕ) :
    x / (1 - x) ^ 2 - ∑ i ∈ Finset.range d, (i : ℝ) * x ^ i =
      x ^ d * (d - (d - 1) * x) / (1 - x) ^ 2 := by
  have hx : (1 - x) ≠ 0 := by linarith
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih]
    push_cast
    field_simp
    ring

/-- Geometric tail identity. -/
theorem hasSum_nat_mul_geometric_tail {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (d : ℕ) :
    HasSum (fun k : ℕ => ((k + d : ℕ) : ℝ) * x ^ (k + d))
      (x ^ d * (d - (d - 1) * x) / (1 - x) ^ 2) := by
  have hs : HasSum (fun k : ℕ => (k : ℝ) * x ^ k) (x / (1 - x) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one (by rwa [Real.norm_of_nonneg h0])
  rw [← geometric_tail_identity h1 d]
  exact (hasSum_nat_add_iff' d).mpr hs

theorem sum_range_nat_mul_geometric_tail_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (d m : ℕ) :
    ∑ k ∈ Finset.range m, ((k + d : ℕ) : ℝ) * x ^ (k + d) ≤
      x ^ d * (d - (d - 1) * x) / (1 - x) ^ 2 :=
  sum_le_hasSum _ (fun k _ => by positivity) (hasSum_nat_mul_geometric_tail h0 h1 d)

end Tail

end KAM.EffectiveStability
