/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Weighted.SupWeighted
public import KAM.Planetary.Spatial.AnalyticDomain
public import KAM.Planetary.Spatial.NonresonantAdapterRescale

/-!
# The spatial complex unrescaling and perturbation (package LP-SP-NRR, item 1, first half)

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
Package LP-SP-NRR, MAIN Lemma 13 with `2n` slow pairs and Theorem 19
(`LP:MAIN L13 (435–441, 444–458)`, `LP:MAIN T19 (599–603)`), N6, track LP, non-frozen.

`lpUnrescaleCNM ℓ : EC n m → ℂ^{n+m} × ℂ^{n+m}` is the complexification of `lpUnrescaleNM ℓ`
(`λ = 2πθ`, `Λ = I`, `(ξ, η) = ℓ (q, p)`).  `lpPertNM μ ℓ fc = (μ/(2π)) fc ∘ lpUnrescaleCNM ℓ` is
the perturbation in the period-one convention.  `LPChartTubeNM` packages the output of
`exists_spatialStrongTube` (the `spatialStrongCore` tube of `complexTubeNM`).  Under the fixed
width conditions of N6 the complex unrescaling maps `Dom n b.base b.rB t` (block of type
`PartialBlock n (n + n)`) into the set (22) of `spatialStrongCore_containment`.
-/

@[expose] public noncomputable section

open KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Nekhoroshev KAM.Weighted Set

namespace KAM.Planetary.Spatial

variable {n m : ℕ}

/-- The complex unrescaling `(θ, (I, q, p)) ↦ ((2πθ, ℓ q), (I, ℓ p))` (chart point). -/
def lpUnrescaleCNM (ℓ : ℝ) (z : EC n m) : (Fin (n + m) → ℂ) × (Fin (n + m) → ℂ) :=
  (Fin.append (fun i => ((2 * Real.pi : ℝ) : ℂ) * z.1 i)
      (fun i => (ℓ : ℂ) * z.2 (Fin.natAdd n (Fin.castAdd m i))),
   Fin.append (fun i => z.2 (Fin.castAdd (m + m) i))
      (fun i => (ℓ : ℂ) * z.2 (Fin.natAdd n (Fin.natAdd m i))))

/-- The perturbation in the period-one convention `(μ/(2π)) · fc ∘ lpUnrescaleCNM ℓ`. -/
def lpPertNM (μ ℓ : ℝ) (fc : ((Fin (n + m) → ℂ) × (Fin (n + m) → ℂ)) → ℂ) (z : EC n m) : ℂ :=
  ((μ / (2 * Real.pi) : ℝ) : ℂ) * fc (lpUnrescaleCNM ℓ z)

/-- The output of `exists_spatialStrongTube`, packaged: a shift-periodic holomorphic `fc` on
`complexTubeNM core R` with real trace `fSpatial ν ∘ spatialPoincareProd ν` and sup bound `M` on
`complexTubeNM core (R/2)`. -/
structure LPChartTubeNM (ν : Fin n → ℝ) (L : Set (Fin n → ℝ)) (δ rg R M : ℝ)
    (fc : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) → ℂ) : Prop where
  R_pos : 0 < R
  hol : DifferentiableOn ℂ fc (complexTubeNM (spatialStrongCore ν L δ rg) R)
  real : ∀ w : Phase (n + (n + n)),
    complexifyPhase w ∈ complexTubeNM (spatialStrongCore ν L δ rg) R →
    w ∈ spatialChartSafe ν ∧ fc (complexifyPhase w) = (fSpatial ν (spatialPoincareProd ν w) : ℂ)
  per : ∀ k : Fin n → ℤ, ∀ z ∈ complexTubeNM (spatialStrongCore ν L δ rg) R,
    z + complexifyPhase (fastShift k) ∈ complexTubeNM (spatialStrongCore ν L δ rg) R ∧
      fc (z + complexifyPhase (fastShift k)) = fc z
  bound : ∀ z ∈ complexTubeNM (spatialStrongCore ν L δ rg) (R / 2), ‖fc z‖ ≤ M

theorem lpUnrescaleCNM_extCx (ℓ : ℝ) (y : ER n m) :
    lpUnrescaleCNM ℓ (extCx y) = complexifyPhase (lpUnrescaleNM ℓ y) := by
  rw [lpUnrescaleNM_apply]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [lpUnrescaleCNM, lpUnrescaleNMFun, extCx, complexifyPhase]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [lpUnrescaleCNM, lpUnrescaleNMFun, extCx, complexifyPhase]

theorem lpUnrescaleCNM_differentiable (ℓ : ℝ) :
    Differentiable ℂ (lpUnrescaleCNM (n := n) (m := m) ℓ) := by
  unfold lpUnrescaleCNM
  refine Differentiable.prodMk ?_ ?_
  · refine differentiable_pi.2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp only [Fin.append_left, Fin.append_right] <;> fun_prop
  · refine differentiable_pi.2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp only [Fin.append_left, Fin.append_right] <;> fun_prop

theorem lpUnrescaleCNM_shift (ℓ : ℝ) (z : EC n m) (j : Fin n) :
    lpUnrescaleCNM ℓ (z.1 + Pi.single j 1, z.2) =
      lpUnrescaleCNM ℓ z + complexifyPhase (fastShift (a := n) (b := m) (Pi.single j (1 : ℤ))) := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp [lpUnrescaleCNM, complexifyPhase, fastShift, Pi.single_apply]
      split_ifs <;> simp [mul_add]
    · simp [lpUnrescaleCNM, complexifyPhase, fastShift]
  · simp [lpUnrescaleCNM, complexifyPhase, fastShift]

section Containment

variable {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ rg R : ℝ}

/-- (`LP:MAIN L13 (441–446)`, N6; `LP:MAIN T19`) Under the fixed width conditions, the complex
unrescaling of a point of `T_t × V_{rB} base` lies in the set (22) of
`spatialStrongCore_containment` (`2n` slow pairs). -/
theorem lpUnrescaleCNM_mem_complexTube {rs s₀ b₀ : ℝ} (hrs : 0 < rs) (hrg : rs ≤ 4 * rg)
    (hmax : max rs (max (4 * s₀) (4 * b₀)) < R / 2)
    {I0 : Fin n → ℝ} (hI0 : I0 ∈ strongLevelSet ν L δ) (b : PartialBlock n (n + n))
    (hS : b.S = spatialSecularBall ν δ I0) (hIc : b.Ic = I0) (hrB : b.rB ≤ rs)
    (hrB0 : 0 < b.rB) (hw0 : 0 < b.w) (hw : b.w < 4 * b₀) {t : ℝ} (ht : 0 < t)
    (hts : 2 * Real.pi * t ≤ 4 * s₀)
    {z : EC n (n + n)} (hang : ∀ i, |(z.1 i).im| < t) (hJ : z.2 ∈ polyNbhd b.base b.rB) :
    lpUnrescaleCNM b.lam z ∈ complexTubeNM (spatialStrongCore ν L δ rg) (R / 2) := by
  have hℓ : 0 < b.lam := div_pos hw0 hrB0
  have hpi := Real.pi_pos
  obtain ⟨J', ⟨x, hx, hJ'⟩, hlt⟩ := hJ
  have key : ∀ j, ‖z.2 j - J' j‖ ≤ ‖z.2 - J'‖ := fun j => by
    simpa using norm_le_pi_norm (z.2 - J') j
  have hℓc : (b.lam : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hℓr : b.lam * b.rB = b.w := by unfold PartialBlock.lam; field_simp
  refine spatialStrongCore_containment (rs := rs) (s := s₀) (b := b₀) hrs hrg hmax hI0 ?_ ?_ ?_
  · refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
      (hlt.trans_le hrB)
    have := key (Fin.castAdd ((n + n) + (n + n)) i)
    simp only [Pi.sub_apply, lpUnrescaleCNM, Fin.append_left, hJ', hIc] at this ⊢
    exact this
  · have h4 : 0 < 4 * s₀ := by nlinarith
    refine (pi_norm_lt_iff h4).2 fun i => ?_
    simp only [lpUnrescaleCNM, Fin.append_left, Real.norm_eq_abs]
    have : (((2 * Real.pi : ℝ) : ℂ) * z.1 i).im = 2 * Real.pi * (z.1 i).im := by simp
    rw [this, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    nlinarith [hang i]
  · have h4 : 0 < 4 * b₀ := by linarith
    have hm := mul_lt_mul_of_pos_left hlt hℓ
    refine ⟨x, hS ▸ hx, ?_, ?_⟩
    · refine (pi_norm_lt_iff h4).2 fun i => ?_
      have hk := mul_le_mul_of_nonneg_left
        (key (Fin.natAdd n (Fin.castAdd (n + n) i))) hℓ.le
      have e : (lpUnrescaleCNM b.lam z).1 (Fin.natAdd n i) - ((x.1 i : ℝ) : ℂ) =
          (b.lam : ℂ) * (z.2 (Fin.natAdd n (Fin.castAdd (n + n) i)) -
            J' (Fin.natAdd n (Fin.castAdd (n + n) i))) := by
        simp only [lpUnrescaleCNM, Fin.append_right, Fin.append_left, hJ']
        push_cast; field_simp
      simp only [Pi.sub_apply, e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hℓ.le]
      linarith
    · refine (pi_norm_lt_iff h4).2 fun i => ?_
      have hk := mul_le_mul_of_nonneg_left
        (key (Fin.natAdd n (Fin.natAdd (n + n) i))) hℓ.le
      have e : (lpUnrescaleCNM b.lam z).2 (Fin.natAdd n i) - ((x.2 i : ℝ) : ℂ) =
          (b.lam : ℂ) * (z.2 (Fin.natAdd n (Fin.natAdd (n + n) i)) -
            J' (Fin.natAdd n (Fin.natAdd (n + n) i))) := by
        simp only [lpUnrescaleCNM, Fin.append_right, hJ']
        push_cast; field_simp
      simp only [Pi.sub_apply, e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hℓ.le]
      linarith

end Containment

end KAM.Planetary.Spatial

end
