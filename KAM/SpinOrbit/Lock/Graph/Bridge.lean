/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Lock.Coords.HamExpr
public import KAM.SpinOrbit.Lock.Coords.Conjugacy
public import KAM.SpinOrbit.Lock.Coords.Inverse

/-!
# The lock Hamiltonian at real points, and the polar angle (LOCK-GRAPH)

Unfrozen helper code.

* `ofRealPt`: a real phase point as a complex one; `fderiv_ofRealPt`: a holomorphic `F` that
  restricts near a real point to a real-differentiable `f` has the real derivative of `f` in real
  directions.
* `lockHamExpr_eval_ofRealPt`: at real points with `I > 0`, `lockHamExpr Ω cs` is the real
  `K = lockHamiltonianR Ω (lockCentre cs)`; `hamiltonianVectorFieldℂ_lockHamExpr_ofRealPt`: so
  its complex Hamiltonian vector field is the real `X_K`.
* `arg_lockW_lockToPhysicalR`: the polar angle `arg(lockW)/2π` of the physical image of a real
  point with `I > 0` is its angle `α` modulo one; `lockToPhysicalR_congr`: the physical image does
  not see the clock action `J̃`.
-/

@[expose] public noncomputable section

open Real Filter Topology

namespace KAM.SpinOrbit.Lock

open KAM KAM.Certificate

/-- A real phase point as a complex one. -/
def ofRealPt (w : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  (fun i => (w.1 i : ℂ), fun i => (w.2 i : ℂ))

theorem ofRealPt_add_smul (w v : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (t : ℝ) :
    ofRealPt (w + t • v) = ofRealPt w + (t : ℂ) • ofRealPt v := by
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [ofRealPt]

/-- Real directions of a holomorphic function that restricts near a real point to a real
function `f`: the complex derivative is the real one. -/
theorem fderiv_ofRealPt {F : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {f : (Fin 2 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {z : (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hF : DifferentiableAt ℂ F (ofRealPt z))
    (hf : DifferentiableAt ℝ f z) (heq : ∀ᶠ w in 𝓝 z, F (ofRealPt w) = (f w : ℂ))
    (v : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    fderiv ℂ F (ofRealPt z) (ofRealPt v) = (fderiv ℝ f z v : ℂ) := by
  have hl : HasDerivAt (fun t : ℝ => ofRealPt (z + t • v)) (ofRealPt v) 0 := by
    have e : (fun t : ℝ => ofRealPt (z + t • v)) =
        fun t : ℝ => ofRealPt z + (t : ℂ) • ofRealPt v :=
      funext fun t => ofRealPt_add_smul z v t
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.smul_const (ofRealPt v)).const_add
      (ofRealPt z)
  have h1 : HasDerivAt (fun t : ℝ => F (ofRealPt (z + t • v)))
      (fderiv ℂ F (ofRealPt z) (ofRealPt v)) 0 := by
    exact (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 : HasDerivAt (fun t : ℝ => ((f (z + t • v) : ℝ) : ℂ)) ((fderiv ℝ f z v : ℝ) : ℂ) 0 :=
    (soHasDerivAt_line hf v).ofReal_comp
  have hc : Tendsto (fun t : ℝ => z + t • v) (𝓝 0) (𝓝 z) := by
    have : Continuous (fun t : ℝ => z + t • v) := by fun_prop
    simpa using this.tendsto 0
  have hev : (fun t : ℝ => F (ofRealPt (z + t • v))) =ᶠ[𝓝 0]
      fun t => ((f (z + t • v) : ℝ) : ℂ) := hc.eventually heq
  exact h1.unique (h2.congr_of_eventuallyEq hev)

theorem lockHamExpr_eval_ofRealPt {Ω : ℚ} (hΩ : 0 < Ω) (cs : List ℚ)
    (w : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hI : 0 < w.2 0) :
    (lockHamExpr Ω cs).eval (ofRealPt w) = ((lockHamiltonianR Ω (lockCentre cs) w : ℝ) : ℂ) := by
  rw [lockHamExpr_eval, ofRealPt, lockToRotC_ofReal hΩ cs w hI, lockHamiltonianR_eq]
  generalize lockToRotR (Ω : ℝ) (lockCentre cs) w = r
  simp only [soRotHC, soRotMap, soHC, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Complex.ofReal_add, soVC_ofReal]
  push_cast
  ring

theorem differentiableAt_lockHamExpr {Ω : ℚ} (hΩ : 0 < Ω) (cs : List ℚ)
    {z : (Fin 2 → ℂ) × (Fin 2 → ℂ)} (hz : 0 < (z.2 0).re) :
    DifferentiableAt ℂ (lockHamExpr Ω cs).eval z :=
  (((lockHamExpr Ω cs).contDiffOn_eval isOpen_lockCertRegion
    (nonvanishingOn_lockHamExpr hΩ cs)).contDiffAt
      (isOpen_lockCertRegion.mem_nhds hz)).differentiableAt (by simp)

theorem fderiv_lockHamExpr_ofRealPt {Ω : ℚ} (hΩ : 0 < Ω) (cs : List ℚ)
    (w : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hI : 0 < w.2 0) (v : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    fderiv ℂ (lockHamExpr Ω cs).eval (ofRealPt w) (ofRealPt v) =
      (fderiv ℝ (lockHamiltonianR Ω (lockCentre cs)) w v : ℂ) := by
  have hΩr : (0 : ℝ) < Ω := by exact_mod_cast hΩ
  have hc3 : ContDiff ℝ 3 (lockCentre cs) := (lockCentre_contDiff cs).of_le le_top
  obtain ⟨hd0, -, hc2⟩ := contDiff_succ_iff_deriv.mp
    (show ContDiff ℝ (2 + 1) (lockCentre cs) from hc3)
  obtain ⟨hd1, -, hc1⟩ := contDiff_succ_iff_deriv.mp
    (show ContDiff ℝ (1 + 1) (deriv (lockCentre cs)) from hc2)
  have hd2 : Differentiable ℝ (deriv (deriv (lockCentre cs))) := hc1.differentiable (by norm_num)
  have hopen : IsOpen {w : (Fin 2 → ℝ) × (Fin 2 → ℝ) | 0 < w.2 0} :=
    isOpen_lt continuous_const ((continuous_apply 0).comp continuous_snd)
  exact fderiv_ofRealPt (differentiableAt_lockHamExpr hΩ cs (by simpa [ofRealPt] using hI))
    (differentiableAt_lockHamiltonianR hΩr hd0 hd1 hd2 w hI)
    (Filter.mem_of_superset (hopen.mem_nhds hI) fun w' hw' =>
      lockHamExpr_eval_ofRealPt hΩ cs w' hw') v

/-- At real points with `I > 0`, the complex Hamiltonian vector field of `lockHamExpr` is the real
`X_K`. -/
theorem hamiltonianVectorFieldℂ_lockHamExpr_ofRealPt {Ω : ℚ} (hΩ : 0 < Ω) (cs : List ℚ)
    (w : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hI : 0 < w.2 0) :
    hamiltonianVectorFieldℂ (lockHamExpr Ω cs).eval (ofRealPt w) =
      ofRealPt (hamiltonianVectorField (lockHamiltonianR Ω (lockCentre cs)) w) := by
  have e1 : ∀ i : Fin 2, (((0 : Fin 2 → ℂ)), (Pi.single i 1 : Fin 2 → ℂ)) =
      ofRealPt (0, Pi.single i 1) := by
    intro i
    refine Prod.ext ?_ ?_ <;> funext j <;> by_cases h : j = i <;> simp [ofRealPt, h]
  have e2 : ∀ i : Fin 2, ((Pi.single i 1 : Fin 2 → ℂ), (0 : Fin 2 → ℂ)) =
      ofRealPt (Pi.single i 1, 0) := by
    intro i
    refine Prod.ext ?_ ?_ <;> funext j <;> by_cases h : j = i <;> simp [ofRealPt, h]
  refine Prod.ext ?_ ?_ <;> funext i
  · simp only [hamiltonianVectorFieldℂ, hamiltonianVectorField]
    rw [e1 i, fderiv_lockHamExpr_ofRealPt hΩ cs w hI]
    rfl
  · simp only [hamiltonianVectorFieldℂ, hamiltonianVectorField]
    rw [e2 i, fderiv_lockHamExpr_ofRealPt hΩ cs w hI]
    simp [ofRealPt]

/-! ### The polar angle of the physical image -/

/-- The physical image does not see the clock action `J̃`. -/
theorem lockToPhysicalR_congr {Ω : ℝ} {c : ℝ → ℝ} {z z' : (Fin 2 → ℝ) × (Fin 2 → ℝ)}
    (h0 : z.1 0 = z'.1 0) (h1 : z.1 1 = z'.1 1) (h2 : z.2 0 = z'.2 0) :
    lockToPhysicalR Ω c z = lockToPhysicalR Ω c z' := by
  simp only [lockToPhysicalR, lockX, lockY, h0, h1, h2]

/-- The polar angle `arg(lockW)/2π` of the physical image of a real point with `I > 0` is its
angle `α` modulo one. -/
theorem arg_lockW_lockToPhysicalR {Ω : ℝ} (hΩ : 0 < Ω) (c : ℝ → ℝ)
    (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hI : 0 < z.2 0) :
    ∃ k : ℤ, Complex.arg (lockW Ω c (lockToPhysicalR Ω c z)) / (2 * π) = z.1 0 - k := by
  have hπ := Real.pi_pos
  set s : ℝ := Real.sqrt (z.2 0 / π) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (div_pos hI hπ)
  have hsΩ : 0 < √Ω := Real.sqrt_pos.2 hΩ
  have hX : √Ω * Real.sqrt (z.2 0 / (π * Ω)) = s := by
    rw [hs, ← Real.sqrt_mul hΩ.le]
    congr 1
    field_simp
  have hY : Real.sqrt (z.2 0 * Ω / π) / √Ω = s := by
    rw [hs, ← Real.sqrt_div' _ hΩ.le]
    congr 1
    field_simp
  have hW : lockW Ω c (lockToPhysicalR Ω c z) =
      (s : ℂ) * (Complex.cos ((2 * π * z.1 0 : ℝ) : ℂ) +
        Complex.sin ((2 * π * z.1 0 : ℝ) : ℂ) * Complex.I) := by
    simp only [lockW, lockToPhysicalR, lockX, lockY]
    rw [show z.1 1 + c (z.1 1) + Real.sqrt (z.2 0 / (π * Ω)) * Real.sin (2 * π * z.1 0) - z.1 1 -
        c (z.1 1) = Real.sqrt (z.2 0 / (π * Ω)) * Real.sin (2 * π * z.1 0) by ring,
      show 1 + deriv c (z.1 1) + Real.sqrt (z.2 0 * Ω / π) * Real.cos (2 * π * z.1 0) - 1 -
        deriv c (z.1 1) = Real.sqrt (z.2 0 * Ω / π) * Real.cos (2 * π * z.1 0) by ring,
      ← mul_assoc, hX, mul_div_right_comm, hY, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  rw [hW, Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod hs0, ← self_sub_toIocDiv_zsmul]
  refine ⟨toIocDiv Real.two_pi_pos (-π) (2 * π * z.1 0), ?_⟩
  rw [zsmul_eq_mul]
  field_simp
