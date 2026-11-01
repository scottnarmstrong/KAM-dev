/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Weighted.SupWeighted
public import KAM.Planetary.StrongAMD.AnalyticDomain
public import KAM.Planetary.StrongAMD.NonresonantAdapterRescale

/-!
# The complex unrescaling and the perturbation (package LP-NRR, item 3, first half)

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
Package LP-NRR, MAIN Lemma 13 (`LP:MAIN L13 (435–441, 444–458)`), N6, track LP, non-frozen.

`lpUnrescaleC ℓ : EC n n → ℂ^{n+n} × ℂ^{n+n}` is the complexification of `lpUnrescale ℓ`
(`λ = 2πθ`, `Λ = I`, `(ξ, η) = ℓ (q, p)`).  `lpPert μ ℓ fc = (μ/(2π)) fc ∘ lpUnrescaleC ℓ` is the
perturbation in the period-one convention.  Given the uniform tube of `exists_strongTube`
(packaged as `LPChartTube`), under the fixed width conditions of N6 the complex unrescaling maps
`Dom n b.base b.rB t` into the set (22) of `strongCore_containment`; hence `lpPert` is in the
engine's class `ext_class` and has the sup bound `μ M/(2π)`.
-/

@[expose] public noncomputable section

open KAM KAM.Planetary KAM.Nekhoroshev KAM.Weighted Set

namespace KAM.Planetary.StrongAMD

variable {n : ℕ}

/-- The complex unrescaling `(θ, (I, q, p)) ↦ ((2πθ, ℓ q), (I, ℓ p))` (chart point). -/
def lpUnrescaleC (ℓ : ℝ) (z : EC n n) : (Fin (n + n) → ℂ) × (Fin (n + n) → ℂ) :=
  (Fin.append (fun i => ((2 * Real.pi : ℝ) : ℂ) * z.1 i)
      (fun i => (ℓ : ℂ) * z.2 (Fin.natAdd n (Fin.castAdd n i))),
   Fin.append (fun i => z.2 (Fin.castAdd (n + n) i))
      (fun i => (ℓ : ℂ) * z.2 (Fin.natAdd n (Fin.natAdd n i))))

/-- The perturbation in the period-one convention `(μ/(2π)) · fc ∘ lpUnrescaleC ℓ`. -/
def lpPert (μ ℓ : ℝ) (fc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → ℂ) (z : EC n n) : ℂ :=
  ((μ / (2 * Real.pi) : ℝ) : ℂ) * fc (lpUnrescaleC ℓ z)

/-- The output of `exists_strongTube` (D4), packaged: a shift-periodic holomorphic `fc` on
`complexTube core R` with real trace `fMov 1 1 ν ∘ poincareProd ν 1` and sup bound `M` on
`complexTube core (R/2)`. -/
structure LPChartTube (ν : Fin n → ℝ) (L : Set (Fin n → ℝ)) (δ rg R M : ℝ)
    (fc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → ℂ) : Prop where
  R_pos : 0 < R
  hol : DifferentiableOn ℂ fc (complexTube (strongCore ν L δ rg) R)
  real : ∀ w : Phase (n + n), complexifyPhase w ∈ complexTube (strongCore ν L δ rg) R →
    w ∈ chartSafe ν ∧ fc (complexifyPhase w) = (fMov 1 1 ν (poincareProd ν 1 w) : ℂ)
  per : ∀ k : Fin n → ℤ, ∀ z ∈ complexTube (strongCore ν L δ rg) R,
    z + complexifyPhase (fastShift k) ∈ complexTube (strongCore ν L δ rg) R ∧
      fc (z + complexifyPhase (fastShift k)) = fc z
  bound : ∀ z ∈ complexTube (strongCore ν L δ rg) (R / 2), ‖fc z‖ ≤ M

theorem lpUnrescaleC_extCx (ℓ : ℝ) (y : ER n n) :
    lpUnrescaleC ℓ (extCx y) = complexifyPhase (lpUnrescale ℓ y) := by
  rw [lpUnrescale_apply]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [lpUnrescaleC, lpUnrescaleFun, extCx, complexifyPhase]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [lpUnrescaleC, lpUnrescaleFun, extCx, complexifyPhase]

theorem lpUnrescaleC_differentiable (ℓ : ℝ) : Differentiable ℂ (lpUnrescaleC (n := n) ℓ) := by
  unfold lpUnrescaleC
  refine Differentiable.prodMk ?_ ?_
  · refine differentiable_pi.2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp only [Fin.append_left, Fin.append_right] <;> fun_prop
  · refine differentiable_pi.2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp only [Fin.append_left, Fin.append_right] <;> fun_prop

theorem lpUnrescaleC_shift (ℓ : ℝ) (z : EC n n) (j : Fin n) :
    lpUnrescaleC ℓ (z.1 + Pi.single j 1, z.2) =
      lpUnrescaleC ℓ z + complexifyPhase (fastShift (b := n) (Pi.single j (1 : ℤ))) := by
  refine Prod.ext (funext fun m => ?_) (funext fun m => ?_)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) m
    · simp [lpUnrescaleC, complexifyPhase, fastShift, Pi.single_apply]
      split_ifs <;> simp [mul_add]
    · simp [lpUnrescaleC, complexifyPhase, fastShift]
  · simp [lpUnrescaleC, complexifyPhase, fastShift]

section Containment

variable {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ rg : ℝ}

/-- (`LP:MAIN L13 (441–446)`, N6) Under the fixed width conditions, the complex unrescaling of a
point of `T_t × V_{rB} base` lies in the set (22) of `strongCore_containment`. -/
theorem lpUnrescaleC_mem_complexTube {rs s₀ b₀ R : ℝ} (hrs : 0 < rs) (hrg : rs ≤ 4 * rg)
    (hmax : max rs (max (4 * s₀) (4 * b₀)) < R / 2)
    {I0 : Fin n → ℝ} (hI0 : I0 ∈ strongLevelSet ν L δ) (b : PartialBlock n n)
    (hS : b.S = secularBall ν δ I0) (hIc : b.Ic = I0) (hrB : b.rB ≤ rs) (hrB0 : 0 < b.rB)
    (hw0 : 0 < b.w) (hw : b.w < 4 * b₀) {t : ℝ} (ht : 0 < t) (hts : 2 * Real.pi * t ≤ 4 * s₀)
    {z : EC n n} (hang : ∀ i, |(z.1 i).im| < t) (hJ : z.2 ∈ polyNbhd b.base b.rB) :
    lpUnrescaleC b.lam z ∈ complexTube (strongCore ν L δ rg) (R / 2) := by
  have hℓ : 0 < b.lam := div_pos hw0 hrB0
  have hℓr : b.lam * b.rB = b.w := by unfold PartialBlock.lam; field_simp
  have hpi := Real.pi_pos
  obtain ⟨J', ⟨x, hx, hJ'⟩, hlt⟩ := hJ
  have key : ∀ j, ‖z.2 j - J' j‖ ≤ ‖z.2 - J'‖ := fun j => by
    simpa using norm_le_pi_norm (z.2 - J') j
  have hℓc : (b.lam : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  refine strongCore_containment (rs := rs) (s := s₀) (b := b₀) hrs hrg hmax hI0 ?_ ?_ ?_
  · refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
      (hlt.trans_le hrB)
    have := key (Fin.castAdd (n + n) i)
    simp only [Pi.sub_apply, lpUnrescaleC, Fin.append_left, hJ', hIc] at this ⊢
    exact this
  · have h4 : 0 < 4 * s₀ := by nlinarith
    refine (pi_norm_lt_iff h4).2 fun i => ?_
    simp only [lpUnrescaleC, Fin.append_left, Real.norm_eq_abs]
    have : (((2 * Real.pi : ℝ) : ℂ) * z.1 i).im = 2 * Real.pi * (z.1 i).im := by simp
    rw [this, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    nlinarith [hang i]
  · have h4 : 0 < 4 * b₀ := by linarith
    have hm := mul_lt_mul_of_pos_left hlt hℓ
    refine ⟨x, hS ▸ hx, ?_, ?_⟩
    · refine (pi_norm_lt_iff h4).2 fun i => ?_
      have hk := mul_le_mul_of_nonneg_left (key (Fin.natAdd n (Fin.castAdd n i))) hℓ.le
      have e : (lpUnrescaleC b.lam z).1 (Fin.natAdd n i) - ((x.1 i : ℝ) : ℂ) =
          (b.lam : ℂ) * (z.2 (Fin.natAdd n (Fin.castAdd n i)) -
            J' (Fin.natAdd n (Fin.castAdd n i))) := by
        simp only [lpUnrescaleC, Fin.append_right, Fin.append_left, hJ']
        push_cast; field_simp
      simp only [Pi.sub_apply, e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hℓ.le]
      linarith
    · refine (pi_norm_lt_iff h4).2 fun i => ?_
      have hk := mul_le_mul_of_nonneg_left (key (Fin.natAdd n (Fin.natAdd n i))) hℓ.le
      have e : (lpUnrescaleC b.lam z).2 (Fin.natAdd n i) - ((x.2 i : ℝ) : ℂ) =
          (b.lam : ℂ) * (z.2 (Fin.natAdd n (Fin.natAdd n i)) -
            J' (Fin.natAdd n (Fin.natAdd n i))) := by
        simp only [lpUnrescaleC, Fin.append_right, Fin.append_left, hJ']
        push_cast; field_simp
      simp only [Pi.sub_apply, e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hℓ.le]
      linarith

end Containment

end KAM.Planetary.StrongAMD

end
