/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Examples.PlasmaLean.Bites
public import KAM.Sharp2.Examples.PlasmaLean.ClassicalConst
public import KAM.Sharp2.Examples.PlasmaLean.Core
public import KAM.Sharp2.RouteA.Frozen
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A closed a-posteriori theorem at PlasmaLean's frequency and strip

The frequency is `ω* = (ι, 1)`, `ι = (75 + √5)/562`; the strip is `ρ = 1/50` turns, `ρ∞ = ρ/1000`.
No hypothesis below is numerical: everything numerical is a kernel `decide`.

* `plasmaLean_torus`: every canonical analytic flow and approximate torus with the bounds `CALike`
  and invariance error `‖E‖ ≤ e ≤ 1.93·10⁻¹⁷ = 10^{-16.71}` has a true invariant torus nearby. This
  is 33 times PlasmaLean's tolerance `5.7·10⁻¹⁹`. The certificates are those of `Bites`, at the
  bites `δ₀, δ₁, δ₂, r₀, r₁, r₂` of a prefix of length three; the tail uses the classical constant.
* `plasmaLean_classical`: the same with classical small-divisor constants only, for every
  `(γ, 1)`-Diophantine `ω`, `γ ≤ 0.1374`: the threshold is `4.85·10⁻⁶ γ⁴ δ₀⁴`, that is `10^{-18.67}`
  at `γ = 0.1374` and `10^{-19.88}` at `γ = 0.0687`.

These are statements about canonical Hamiltonian flows, with the sup norms of the phase space. They
are not applied to PlasmaLean's field, whose area form is not the canonical one.
-/

@[expose] public section

open scoped Matrix.Norms.Operator

namespace KAM.Sharp2.Examples

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2.RouteA

/-- A rational upper bound of `c♮(2, 1, δ)` is a small-divisor constant on the Diophantine set. -/
theorem sdConst_classical_le {γ δ C : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C)
    (h : 64495 / 100000 * (1 + 8 * (31416 / 10000) * δ / (738 / 100)) ≤ (9869 / 1000 * C) ^ 2) :
    SDConst 2 1 γ δ C {ω | IsDiophantine γ 1 ω} :=
  sdConst_mono hγ (sdConst_classical (n := 2) (by norm_num) le_rfl hγ hδ hδ1)
    (cohConstC_two_one_le hδ.le hC h)

/-- The same at every bite `δ ≤ δ'`, with the constant of `δ'`. -/
theorem sdConst_classical_tail {γ δ δ' C : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) (hle : δ ≤ δ')
    (hδ1 : δ' ≤ 1) (hC : 0 ≤ C)
    (h : 64495 / 100000 * (1 + 8 * (31416 / 10000) * δ' / (738 / 100)) ≤ (9869 / 1000 * C) ^ 2) :
    SDConst 2 1 γ δ C {ω | IsDiophantine γ 1 ω} :=
  sdConst_mono hγ (sdConst_classical (n := 2) (by norm_num) le_rfl hγ hδ (hle.trans hδ1))
    ((cohConstC_mono le_rfl hδ.le hle).trans (cohConstC_two_one_le (hδ.le.trans hle) hC h))

section Frequency

/-- The certified constants at the bites `δ_s`. -/
def freqC : ℕ → ℚ
  | 0 => 1524 / 100000
  | 1 => 1512 / 100000
  | _ => 1508 / 100000

/-- The certified constants at the bites `r_s`. -/
def freqCbar : ℕ → ℚ
  | 0 => 1778 / 100000
  | 1 => 1612 / 100000
  | _ => 1540 / 100000

/-- The run with the certified constants: a prefix of length three, then the classical tail. -/
def freqVar : CAVar where
  sB := 20002 / 10000
  sT := 61 / 10
  sLt := 124001 / 10000
  sN := 62002 / 10000
  sNt := 248005 / 10000
  t := 1988 / 100
  th := 19 / 100
  c := freqC
  cbar := freqCbar
  ctail := 8144 / 100000
  kp := 3

/-- The threshold of the normalised error. -/
def freqXs : ℚ := 441 / 1000000

theorem freqVar_ok : freqVar.numQ.ok freqVar.cap caM0 freqXs = true := by decide +kernel

theorem freqVar_close :
    freqVar.numQ.sumD freqXs / (freqXs * (333 / 100000) ^ 4 * gammaStar ^ 2) ≤ 22226503 := by
  decide +kernel

theorem freqVar_wf : freqVar.numA.Wf := by
  refine CAVar.wf _ (by norm_num [freqVar]) (by norm_num [freqVar]) (by norm_num [freqVar])
    (by norm_num [freqVar]) (by norm_num [freqVar]) (by norm_num [freqVar]) (by norm_num [freqVar])
    (by norm_num [freqVar]) (fun s => ?_) (fun s => ?_) (by norm_num [freqVar])
  · rcases s with _ | _ | s <;> norm_num [freqVar, freqC]
  · rcases s with _ | _ | s <;> norm_num [freqVar, freqCbar]

/-- The small-divisor certificates of the run, at `ω*`. -/
theorem freqVar_cert : freqVar.numA.Cert (gammaStar : ℝ) ({omegaStar} : Set (Fin 2 → ℝ)) where
  stage := fun s hs => by
    have hs' : s < 3 := hs
    rw [CAVar.numA_δ]
    interval_cases s
    · rw [show (2 : ℝ)⁻¹ ^ 0 * (333 / 100000) = ((333 / 100000 : ℚ) : ℝ) by norm_num]
      exact sdConst_d0
    · rw [show (2 : ℝ)⁻¹ ^ 1 * (333 / 100000) = ((333 / 200000 : ℚ) : ℝ) by norm_num]
      exact sdConst_d1
    · rw [show (2 : ℝ)⁻¹ ^ 2 * (333 / 100000) = ((333 / 400000 : ℚ) : ℝ) by norm_num]
      exact sdConst_d2
  bar := fun s hs => by
    have hs' : s < 3 := hs
    rw [CAVar.numA_r]
    interval_cases s
    · rw [show (1 / 50 - 2 * 3 * (333 / 100000) * (1 - (2 : ℝ)⁻¹ ^ 0)) = ((1 / 50 : ℚ) : ℝ) by
        norm_num]
      exact sdConst_r0
    · rw [show (1 / 50 - 2 * 3 * (333 / 100000) * (1 - (2 : ℝ)⁻¹ ^ 1)) =
        ((1001 / 100000 : ℚ) : ℝ) by norm_num]
      exact sdConst_r1
    · rw [show (1 / 50 - 2 * 3 * (333 / 100000) * (1 - (2 : ℝ)⁻¹ ^ 2)) =
        ((1003 / 200000 : ℚ) : ℝ) by norm_num]
      exact sdConst_r2
  tail := fun δ hδ hle => by
    have hγ : (0 : ℝ) < gammaStar := by norm_num [gammaStar]
    have hle' : δ ≤ 333 / 800000 := by
      refine hle.trans_eq ?_
      rw [CAVar.numA_δ]
      show (2 : ℝ)⁻¹ ^ 3 * (333 / 100000) = _
      norm_num
    refine sdConst_subset (sdConst_classical_tail hγ hδ hle' (by norm_num) ?_ ?_) ?_
    · show (0 : ℝ) ≤ ((8144 / 100000 : ℚ) : ℝ)
      norm_num
    · show _ ≤ (9869 / 1000 * ((8144 / 100000 : ℚ) : ℝ)) ^ 2
      norm_num
    · rintro ω rfl
      exact isDiophantine_omegaStar

/-- **PlasmaLean's frequency and strip, certified.** For `ω* = (ι, 1)`, `ι = (75 + √5)/562`, on the
strip `ρ = 1/50` of a canonical two-degree-of-freedom flow: if `h`, `K` satisfy the explicit bounds
`CALike` and the invariance error is at most `e ≤ 1.93·10⁻¹⁷`, there is a true invariant torus
`Kinf` on the strip `ρ∞ = 1/50000`, at distance at most `22226503 e` from `K`. -/
theorem plasmaLean_torus {𝔅 : Set ((Fin 2 → ℂ) × (Fin 2 → ℂ))}
    {h : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)} {e : ℝ}
    (hO : CALike 𝔅 h K omegaStar)
    (hE : ∀ θ ∈ complexStrip 2 (1 / 50), ‖invarianceError h K omegaStar θ‖ ≤ e)
    (he : e ≤ 193 / 10 ^ 19) :
    ∃ Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip 2 (1 / 50000)) ∧ IsPrimaryOnStrip Kinf (1 / 50000) ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), invarianceError h Kinf omegaStar θ = 0) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), Metric.ball (Kinf θ) (1 / 320) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), ‖fderiv ℂ Kinf θ‖ ≤ 31 / 10 + 1 / 320) ∧
      ∀ θ ∈ complexStrip 2 (1 / 50000), ‖Kinf θ - K θ‖ ≤ 22226503 * e := by
  have hγ : (0 : ℝ) < gammaStar := by norm_num [gammaStar]
  have hXs : (0 : ℚ) < freqXs := by norm_num [freqXs]
  have h00 : (0 : Fin 2 → ℂ) ∈ complexStrip 2 (1 / 50) := fun i => by simp
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hE 0 h00)
  have hsm : e / ((gammaStar : ℝ) ^ 4 * (333 / 100000) ^ 4) < (freqXs : ℝ) := by
    rw [div_lt_iff₀ (by positivity)]
    refine he.trans_lt ?_
    norm_num [gammaStar, freqXs]
  obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := cALike_core freqVar freqVar_wf hXs freqVar_ok hO
    (Set.mem_singleton _) freqVar_cert hγ (by norm_num [gammaStar]) isDiophantine_omegaStar hE hsm
  refine ⟨Kinf, h1, h2, h3, h4, h5, h6, fun θ hθ => (h7 θ hθ).trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ he0
  have : ((freqVar.numQ.sumD freqXs / (freqXs * (333 / 100000) ^ 4 * gammaStar ^ 2) : ℚ) : ℝ) ≤
      ((22226503 : ℚ) : ℝ) := Rat.cast_le.mpr freqVar_close
  push_cast at this
  exact this

end Frequency

section Classical

/-- Rational upper bounds of `c♮` at the bites `δ_s`. -/
def classicalC : ℕ → ℚ
  | 0 => 8184 / 100000
  | 1 => 8161 / 100000
  | 2 => 8150 / 100000
  | 3 => 8144 / 100000
  | _ => 8141 / 100000

/-- Rational upper bounds of `c♮` at the bites `r_s`. -/
def classicalCbar : ℕ → ℚ
  | 0 => 8411 / 100000
  | 1 => 8276 / 100000
  | 2 => 8207 / 100000
  | 3 => 8173 / 100000
  | _ => 8156 / 100000

/-- The run with classical constants: a prefix of length five. -/
def classicalVar : CAVar where
  sB := 20003 / 10000
  sT := 48 / 10
  sLt := 124001 / 10000
  sN := 62002 / 10000
  sNt := 248005 / 10000
  t := 1986 / 100
  th := 3 / 100
  c := classicalC
  cbar := classicalCbar
  ctail := 8139 / 100000
  kp := 5

/-- The threshold of the normalised error. -/
def classicalXs : ℚ := 485 / 100000000

theorem classicalVar_ok : classicalVar.numQ.ok classicalVar.cap caM0 classicalXs = true := by
  decide +kernel

theorem classicalVar_close :
    classicalVar.numQ.sumD classicalXs / (classicalXs * (333 / 100000) ^ 4) ≤ 10259477 := by
  decide +kernel

theorem classicalVar_wf : classicalVar.numA.Wf := by
  refine CAVar.wf _ (by norm_num [classicalVar]) (by norm_num [classicalVar])
    (by norm_num [classicalVar]) (by norm_num [classicalVar]) (by norm_num [classicalVar])
    (by norm_num [classicalVar]) (by norm_num [classicalVar]) (by norm_num [classicalVar])
    (fun s => ?_) (fun s => ?_) (by norm_num [classicalVar])
  · rcases s with _ | _ | _ | _ | s <;> norm_num [classicalVar, classicalC]
  · rcases s with _ | _ | _ | _ | s <;> norm_num [classicalVar, classicalCbar]

/-- The classical certificates, on the whole Diophantine set. -/
theorem classicalVar_cert {γ : ℝ} (hγ : 0 < γ) :
    classicalVar.numA.Cert γ ({ω | IsDiophantine γ 1 ω} : Set (Fin 2 → ℝ)) where
  stage := fun s hs => by
    have hs' : s < 5 := hs
    rw [CAVar.numA_δ]
    interval_cases s <;>
      refine sdConst_classical_le hγ (by norm_num) (by norm_num) ?_ ?_ <;>
      norm_num [classicalVar, CAVar.numA, classicalC]
  bar := fun s hs => by
    have hs' : s < 5 := hs
    rw [CAVar.numA_r]
    interval_cases s <;>
      refine sdConst_classical_le hγ (by norm_num) (by norm_num) ?_ ?_ <;>
      norm_num [classicalVar, CAVar.numA, classicalCbar]
  tail := fun δ hδ hle => by
    have hle' : δ ≤ 333 / 3200000 := by
      refine hle.trans_eq ?_
      rw [CAVar.numA_δ]
      show (2 : ℝ)⁻¹ ^ 5 * (333 / 100000) = _
      norm_num
    refine sdConst_classical_tail hγ hδ hle' (by norm_num) ?_ ?_
    · show (0 : ℝ) ≤ ((8139 / 100000 : ℚ) : ℝ)
      norm_num
    · show _ ≤ (9869 / 1000 * ((8139 / 100000 : ℚ) : ℝ)) ^ 2
      norm_num

/-- **The classical variant**, with no frequency certificate: for every `(γ, 1)`-Diophantine `ω`,
`γ ≤ 0.1374`, the bounds `CALike` and `e < 4.85·10⁻⁶ γ⁴ δ₀⁴`, `δ₀ = 333/100000`, give the true
torus. -/
theorem plasmaLean_classical {𝔅 : Set ((Fin 2 → ℂ) × (Fin 2 → ℂ))}
    {h : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)}
    {ω : Fin 2 → ℝ} {γ e : ℝ} (hγ : 0 < γ) (hγb : γ ≤ 687 / 5000) (hdio : IsDiophantine γ 1 ω)
    (hO : CALike 𝔅 h K ω)
    (hE : ∀ θ ∈ complexStrip 2 (1 / 50), ‖invarianceError h K ω θ‖ ≤ e)
    (hsm : e / (γ ^ 4 * (333 / 100000) ^ 4) < 485 / 100000000) :
    ∃ Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip 2 (1 / 50000)) ∧ IsPrimaryOnStrip Kinf (1 / 50000) ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), Metric.ball (Kinf θ) (1 / 320) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), ‖fderiv ℂ Kinf θ‖ ≤ 31 / 10 + 1 / 320) ∧
      ∀ θ ∈ complexStrip 2 (1 / 50000), ‖Kinf θ - K θ‖ ≤ 10259477 / γ ^ 2 * e := by
  have hXs : (0 : ℚ) < classicalXs := by norm_num [classicalXs]
  have h00 : (0 : Fin 2 → ℂ) ∈ complexStrip 2 (1 / 50) := fun i => by simp
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hE 0 h00)
  have hsm' : e / (γ ^ 4 * (333 / 100000) ^ 4) < (classicalXs : ℝ) := by
    refine hsm.trans_eq ?_
    norm_num [classicalXs]
  obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := cALike_core classicalVar classicalVar_wf hXs
    classicalVar_ok hO hdio (classicalVar_cert hγ) hγ hγb hdio hE hsm'
  refine ⟨Kinf, h1, h2, h3, h4, h5, h6, fun θ hθ => (h7 θ hθ).trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ he0
  have hq : ((classicalVar.numQ.sumD classicalXs / (classicalXs * (333 / 100000) ^ 4) : ℚ) : ℝ) ≤
      ((10259477 : ℚ) : ℝ) := Rat.cast_le.mpr classicalVar_close
  push_cast at hq
  have hγ2 : 0 < γ ^ 2 := by positivity
  rw [← div_div]
  exact div_le_div_of_nonneg_right hq hγ2.le

end Classical

end KAM.Sharp2.Examples

end
