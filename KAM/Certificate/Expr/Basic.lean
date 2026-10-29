/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.PhaseBasis
public import KAM.Certificate.Poly.Basic
public import KAM.Frozen.Defs.ComplexStrip
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The Hamiltonian expression language, basic layer

`HamExpr n` is the finite expression language for Hamiltonians (SO design §D): angles enter only
through the period-one modes `cos (2π k·θ)`, `sin (2π k·θ)`. We prove the structural facts:
holomorphy on an open set where all denominators are certified nonvanishing, invariance under
integer translations of the angles, reality on real points, and the openness and translation
invariance of the Hamiltonian domain `certDomain`.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM

/-- Hamiltonians as finite expressions. Angles enter only through the period-one modes
`cos (2π k·θ)`, `sin (2π k·θ)`; every constructor maps reals to reals, so reality, periodicity
and translation invariance are structural and unconditional. Division (ruling O2) is by an
expression certified nonvanishing on the domain (`NonvanishingOn`, established by the ball
arithmetic of `checkHamBounds`); holomorphy is structural under that condition. -/
inductive HamExpr (n : ℕ) : Type
  | const (q : ℚ)
  | pi
  | action (j : Fin n)
  | cosMode (k : CertKey)
  | sinMode (k : CertKey)
  | add (a b : HamExpr n)
  | mul (a b : HamExpr n)
  | div (a b : HamExpr n)
  | pow (a : HamExpr n) (m : ℕ)
  | exp (a : HamExpr n)
  | sin (a : HamExpr n)
  | cos (a : HamExpr n)

/-- `2π k·θ`. -/
def modePhase (n : ℕ) (k : CertKey) (θ : Fin n → ℂ) : ℂ :=
  2 * Real.pi * ∑ i, (certKeyFun n k i : ℂ) * θ i

/-- The function denoted by an expression (division is Lean's `/`; it is only ever used where
the denominator is certified nonvanishing). -/
def HamExpr.eval {n : ℕ} : HamExpr n → (Fin n → ℂ) × (Fin n → ℂ) → ℂ
  | .const q, _ => (q : ℂ)
  | .pi, _ => (Real.pi : ℂ)
  | .action j, z => z.2 j
  | .cosMode k, z => Complex.cos (modePhase n k z.1)
  | .sinMode k, z => Complex.sin (modePhase n k z.1)
  | .add a b, z => a.eval z + b.eval z
  | .mul a b, z => a.eval z * b.eval z
  | .div a b, z => a.eval z / b.eval z
  | .pow a m, z => a.eval z ^ m
  | .exp a, z => Complex.exp (a.eval z)
  | .sin a, z => Complex.sin (a.eval z)
  | .cos a, z => Complex.cos (a.eval z)

/-- Every denominator of `e` is nonzero at every point of `S`. -/
def HamExpr.NonvanishingOn {n : ℕ} : HamExpr n → Set ((Fin n → ℂ) × (Fin n → ℂ)) → Prop
  | .add a b, S => a.NonvanishingOn S ∧ b.NonvanishingOn S
  | .mul a b, S => a.NonvanishingOn S ∧ b.NonvanishingOn S
  | .div a b, S => a.NonvanishingOn S ∧ b.NonvanishingOn S ∧ ∀ z ∈ S, b.eval z ≠ 0
  | .pow a _, S => a.NonvanishingOn S
  | .exp a, S => a.NonvanishingOn S
  | .sin a, S => a.NonvanishingOn S
  | .cos a, S => a.NonvanishingOn S
  | _, _ => True

theorem contDiff_modePhase (n : ℕ) (k : CertKey) : ContDiff ℂ ⊤ (modePhase n k) := by
  unfold modePhase
  fun_prop

theorem HamExpr.contDiffOn_eval {n : ℕ} (e : HamExpr n) {S : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hS : IsOpen S) (h : e.NonvanishingOn S) : ContDiffOn ℂ ⊤ e.eval S := by
  induction e with
  | const q => exact contDiffOn_const
  | pi => exact contDiffOn_const
  | action j =>
    exact (contDiff_pi.1 contDiff_snd j).contDiffOn
  | cosMode k =>
    exact (Complex.contDiff_cos.comp ((contDiff_modePhase n k).comp contDiff_fst)).contDiffOn
  | sinMode k =>
    exact (Complex.contDiff_sin.comp ((contDiff_modePhase n k).comp contDiff_fst)).contDiffOn
  | add a b iha ihb => exact (iha h.1).add (ihb h.2)
  | mul a b iha ihb => exact (iha h.1).mul (ihb h.2)
  | div a b iha ihb =>
    exact (iha h.1).div (ihb h.2.1) h.2.2
  | pow a m iha => exact (iha h).pow m
  | exp a iha => exact (iha h).cexp
  | sin a iha => exact Complex.contDiff_sin.comp_contDiffOn (iha h)
  | cos a iha => exact Complex.contDiff_cos.comp_contDiffOn (iha h)

theorem modePhase_add_int {n : ℕ} (k : CertKey) (θ : Fin n → ℂ) (m : Fin n → ℤ) :
    modePhase n k (θ + fun i => (m i : ℂ)) =
      modePhase n k θ + ((∑ i, certKeyFun n k i * m i : ℤ) : ℂ) * (2 * Real.pi) := by
  unfold modePhase
  push_cast
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem HamExpr.eval_add_int {n : ℕ} (e : HamExpr n) (z : (Fin n → ℂ) × (Fin n → ℂ))
    (k : Fin n → ℤ) : e.eval (z.1 + (fun i => (k i : ℂ)), z.2) = e.eval z := by
  induction e with
  | const q => rfl
  | pi => rfl
  | action j => rfl
  | cosMode m =>
    simp only [HamExpr.eval, modePhase_add_int, Complex.cos_add_int_mul_two_pi]
  | sinMode m =>
    simp only [HamExpr.eval, modePhase_add_int, Complex.sin_add_int_mul_two_pi]
  | add a b iha ihb => simp only [HamExpr.eval, iha, ihb]
  | mul a b iha ihb => simp only [HamExpr.eval, iha, ihb]
  | div a b iha ihb => simp only [HamExpr.eval, iha, ihb]
  | pow a m iha => simp only [HamExpr.eval, iha]
  | exp a iha => simp only [HamExpr.eval, iha]
  | sin a iha => simp only [HamExpr.eval, iha]
  | cos a iha => simp only [HamExpr.eval, iha]

/-- At real points an expression takes real values. -/
theorem HamExpr.exists_real_eval {n : ℕ} (e : HamExpr n) (θ I : Fin n → ℝ) :
    ∃ r : ℝ, e.eval ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) = (r : ℂ) := by
  induction e with
  | const q => exact ⟨q, by simp [HamExpr.eval]⟩
  | pi => exact ⟨Real.pi, rfl⟩
  | action j => exact ⟨I j, rfl⟩
  | cosMode k =>
    refine ⟨Real.cos (2 * Real.pi * ∑ i, (certKeyFun n k i : ℝ) * θ i), ?_⟩
    simp [HamExpr.eval, modePhase, Complex.ofReal_cos]
  | sinMode k =>
    refine ⟨Real.sin (2 * Real.pi * ∑ i, (certKeyFun n k i : ℝ) * θ i), ?_⟩
    simp [HamExpr.eval, modePhase, Complex.ofReal_sin]
  | add a b iha ihb =>
    obtain ⟨r, hr⟩ := iha
    obtain ⟨s, hs⟩ := ihb
    exact ⟨r + s, by simp [HamExpr.eval, hr, hs]⟩
  | mul a b iha ihb =>
    obtain ⟨r, hr⟩ := iha
    obtain ⟨s, hs⟩ := ihb
    exact ⟨r * s, by simp [HamExpr.eval, hr, hs]⟩
  | div a b iha ihb =>
    obtain ⟨r, hr⟩ := iha
    obtain ⟨s, hs⟩ := ihb
    exact ⟨r / s, by simp [HamExpr.eval, hr, hs]⟩
  | pow a m iha =>
    obtain ⟨r, hr⟩ := iha
    exact ⟨r ^ m, by simp [HamExpr.eval, hr]⟩
  | exp a iha =>
    obtain ⟨r, hr⟩ := iha
    exact ⟨Real.exp r, by simp [HamExpr.eval, hr, Complex.ofReal_exp]⟩
  | sin a iha =>
    obtain ⟨r, hr⟩ := iha
    exact ⟨Real.sin r, by simp [HamExpr.eval, hr, Complex.ofReal_sin]⟩
  | cos a iha =>
    obtain ⟨r, hr⟩ := iha
    exact ⟨Real.cos r, by simp [HamExpr.eval, hr, Complex.ofReal_cos]⟩

theorem HamExpr.eval_real {n : ℕ} (e : HamExpr n) (θ I : Fin n → ℝ) :
    (e.eval ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0 := by
  obtain ⟨r, hr⟩ := e.exists_real_eval θ I
  rw [hr]
  exact Complex.ofReal_im r

/-- The Hamiltonian domain `D = T_{ρ_H} × Π_i {|I_i - c_i| < r_i}`. -/
def certDomain (n : ℕ) (rhoH : ℚ) (centre radius : List ℚ) :
    Set ((Fin n → ℂ) × (Fin n → ℂ)) :=
  {z | z.1 ∈ complexStrip n rhoH ∧
    ∀ i : Fin n, ‖z.2 i - ((centre.getD i.val 0 : ℚ) : ℂ)‖ < (radius.getD i.val 0 : ℚ)}

theorem isOpen_certDomain (n : ℕ) (rhoH : ℚ) (centre radius : List ℚ) :
    IsOpen (certDomain n rhoH centre radius) := by
  have h1 : IsOpen {z : (Fin n → ℂ) × (Fin n → ℂ) | z.1 ∈ complexStrip n rhoH} := by
    have : {z : (Fin n → ℂ) × (Fin n → ℂ) | z.1 ∈ complexStrip n rhoH} =
        ⋂ i : Fin n, {z | |(z.1 i).im| < (rhoH : ℝ)} := by
      ext z; simp [complexStrip]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const
  have h2 : IsOpen {z : (Fin n → ℂ) × (Fin n → ℂ) | ∀ i : Fin n,
      ‖z.2 i - ((centre.getD i.val 0 : ℚ) : ℂ)‖ < (radius.getD i.val 0 : ℚ)} := by
    have : {z : (Fin n → ℂ) × (Fin n → ℂ) | ∀ i : Fin n,
        ‖z.2 i - ((centre.getD i.val 0 : ℚ) : ℂ)‖ < (radius.getD i.val 0 : ℚ)} =
        ⋂ i : Fin n, {z | ‖z.2 i - ((centre.getD i.val 0 : ℚ) : ℂ)‖ <
          (radius.getD i.val 0 : ℚ)} := by
      ext z; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const
  exact h1.inter h2

theorem certDomain_add_int {n : ℕ} {rhoH : ℚ} {centre radius : List ℚ}
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ certDomain n rhoH centre radius)
    (k : Fin n → ℤ) : (z.1 + (fun i => (k i : ℂ)), z.2) ∈ certDomain n rhoH centre radius := by
  refine ⟨fun i => ?_, hz.2⟩
  have := hz.1 i
  simpa using this

end KAM.Certificate

end
