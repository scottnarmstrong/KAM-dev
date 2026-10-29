/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.WrapperReal
public import KAM.Planetary.Preparation.PreparedBasic
public import KAM.Planetary.Preparation.SlowMean
public import KAM.Planetary.Preparation.FastBridge
public import KAM.ODE.Basic

/-!
# The real factors of the chain `Ξ_ε` (P11A-P10, `stepP:p11:wr-chain`)

`Ξ_ε = chart ∘ FastR ∘ PolarR ∘ PsiR ∘ ResR` where `PsiR` and `FastR` are the real restrictions of
the holomorphic maps `Ψ₂` and `Θ̂ ∘ …` of the signed `avg_slow`, `avg_fast`.  This file proves, for
each of `PsiR`, `FastR`: real analyticity and `IsSymplecticOn 1` on the real points of the
complex domain, the real-valuedness identity, integer-lattice equivariance and injectivity.
-/

@[expose] public noncomputable section
open Set
namespace KAM.Planetary

section Parts

variable {n : ℕ}

/-- A complex phase point with real entries is the inclusion of its real part. -/
theorem p11_eq_realInclusion₂_re {N : ℕ} {w : P11Phase N} (h1 : ∀ i, (w.1 i).im = 0)
    (h2 : ∀ i, (w.2 i).im = 0) : w = KAM.realInclusion₂ N (p11ReC N w) :=
  Prod.ext (funext fun i => Complex.ext (by simp [p11ReC]) (by simp [p11ReC, h1 i]))
    (funext fun i => Complex.ext (by simp [p11ReC]) (by simp [p11ReC, h2 i]))

theorem p11_realInclusion₂_add_angleShift {N : ℕ} (z : Phase N) (k : Fin N → ℤ) :
    KAM.realInclusion₂ N (z + KAM.ODE.angleShift k) =
      (KAM.realInclusion N z.1 + fun i => (k i : ℂ), KAM.realInclusion N z.2) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    simp [KAM.ODE.angleShift]

theorem p11ReC_add_shift {N : ℕ} (w : P11Phase N) (k : Fin N → ℤ) :
    p11ReC N (w + ((fun i => (k i : ℂ)), 0)) = p11ReC N w + KAM.ODE.angleShift k := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    simp [p11ReC, KAM.ODE.angleShift]

/-- The real shift of the fast angles by `kf`. -/
def p11FastShift (kf : Fin n → ℤ) : Phase (n+n) := (Fin.append (fun i => (kf i : ℝ)) 0, 0)

theorem p11_realInclusion₂_add_fastShift (z : Phase (n+n)) (kf : Fin n → ℤ) :
    KAM.realInclusion₂ (n+n) (z + p11FastShift kf) =
      (KAM.realInclusion (n+n) z.1 + Fin.append (fun i => (kf i : ℂ)) 0,
        KAM.realInclusion (n+n) z.2) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [p11FastShift]

theorem p11ReC_add_fastShift (w : P11Phase (n+n)) (kf : Fin n → ℤ) :
    p11ReC (n+n) (w + (Fin.append (fun i => (kf i : ℂ)) 0, 0)) =
      p11ReC (n+n) w + p11FastShift kf := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [p11ReC, p11FastShift]

/-- The slow-stage real chart `Ψ₂` (real points). -/
def p11WrPsiR (D : P11Physical n) (nu eps : ℝ) (y : Phase (n+n)) : Phase (n+n) :=
  p11ReC (n+n) ((p11SlowData D nu eps).Psi (KAM.realInclusion₂ (n+n) y))

/-- The fast-stage real chart (real points). -/
def p11WrFastR (D : P11Physical n) (eps : ℝ) (y : Phase (n+n)) : Phase (n+n) :=
  p11ReC (n+n) ((p11FastData D eps).map (KAM.realInclusion₂ (n+n) y))

/-- Complex domain of `Ψ₂`. -/
def p11WrSlowDom (D : P11Physical n) (nu eps : ℝ) : Set (P11Phase (n+n)) :=
  KAM.complexStrip (n+n) ((p11SecularData D).sigma/12/6) ×ˢ
    p11Box (p11SlowCenter (p11SecularData D) eps)
      (p11s2 (p11SecularData D) nu eps/2) (Real.pi*eps/2)

/-- Complex domain of the fast map. -/
def p11WrFastDom (D : P11Physical n) (eps : ℝ) : Set (P11Phase (n+n)) :=
  p11WorkingDom n (p11SecularData D).J0 ((p11SecularData D).sigma/6)
    (p11s1 (p11SecularData D) eps/2) ((p11SecularData D).rz/2)

theorem p11WrSlowDom_isOpen (D : P11Physical n) (nu eps : ℝ) : IsOpen (p11WrSlowDom D nu eps) :=
  (KAM.isOpen_complexStrip _ _).prod (p11Box_isOpen _ _ _)

/-- Real factor `Ψ₂`: chart on the real points of its complex domain, equivariant, injective. -/
theorem p11WrPsiR_facts {D : P11Physical n} {nu eps : ℝ}
    (hS : P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps)) :
    let O := KAM.realInclusion₂ (n+n) ⁻¹' p11WrSlowDom D nu eps
    AnalyticOnNhd ℝ (p11WrPsiR D nu eps) O ∧
      KAM.Kepler.IsSymplecticOn 1 (p11WrPsiR D nu eps) O ∧
      (∀ y ∈ O, KAM.realInclusion₂ (n+n) (p11WrPsiR D nu eps y) =
        (p11SlowData D nu eps).Psi (KAM.realInclusion₂ (n+n) y)) ∧
      (∀ y ∈ O, ∀ k : Fin (n+n) → ℤ, y + KAM.ODE.angleShift k ∈ O ∧
        p11WrPsiR D nu eps (y + KAM.ODE.angleShift k) =
          p11WrPsiR D nu eps y + KAM.ODE.angleShift k) ∧
      InjOn (p11WrPsiR D nu eps) O := by
  intro O
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hre, -, hD, hSy, hE, hI, -, -, -, -, -, -, -⟩ := hS
  have hreal : ∀ y : Phase (n+n), KAM.realInclusion₂ (n+n) y ∈ p11WrSlowDom D nu eps →
      (p11SlowData D nu eps).Psi (KAM.realInclusion₂ (n+n) y) =
        KAM.realInclusion₂ (n+n) (p11WrPsiR D nu eps y) := fun y hy =>
    p11_eq_realInclusion₂_re (fun i => (hre y hy i).1) fun i => (hre y hy i).2
  obtain ⟨han, hsy⟩ := p11_realChart (p11WrSlowDom_isOpen D nu eps) hD hreal hSy
  refine ⟨han, hsy, fun y hy => (hreal y hy).symm, fun y hy k => ?_, fun y hy y' hy' h => ?_⟩
  · have hy' : y + KAM.ODE.angleShift k ∈ O := by
      obtain ⟨h1, h2⟩ := hy
      rw [Set.mem_preimage, p11_realInclusion₂_add_angleShift]
      refine ⟨fun i => ?_, h2⟩
      simpa using h1 i
    refine ⟨hy', ?_⟩
    unfold p11WrPsiR
    rw [p11_realInclusion₂_add_angleShift]
    have := hE (KAM.realInclusion₂ (n+n) y) hy k
    simp only [KAM.realInclusion₂_apply] at this
    rw [this, p11ReC_add_shift]; rfl
  · have h' : (p11SlowData D nu eps).Psi (KAM.realInclusion₂ (n+n) y) =
        (p11SlowData D nu eps).Psi (KAM.realInclusion₂ (n+n) y') := by
      rw [hreal y hy, hreal y' hy', h]
    exact KAM.realInclusion₂_injective (n+n) (hI hy hy' h')

theorem p11WrFastDom_isOpen (D : P11Physical n) (eps : ℝ) : IsOpen (p11WrFastDom D eps) :=
  p11WorkingDom_isOpen _ _ _ _

theorem p11WrFastDom_shift {D : P11Physical n} {eps : ℝ} {y : Phase (n+n)}
    (hy : KAM.realInclusion₂ (n+n) y ∈ p11WrFastDom D eps) (kf : Fin n → ℤ) :
    KAM.realInclusion₂ (n+n) (y + p11FastShift kf) ∈ p11WrFastDom D eps := by
  obtain ⟨h1, h2, h3, h4⟩ := hy
  rw [p11_realInclusion₂_add_fastShift]
  refine ⟨fun i => ?_, h2, ?_, h4⟩
  · simpa [Fin.append_left] using h1 i
  · simpa [Fin.append_right] using h3

/-- Real factor `Θ̂`-stage: chart on the real points of its complex domain, equivariant under the
fast angle lattice, injective. -/
theorem p11WrFastR_facts {D : P11Physical n} {eps : ℝ}
    (hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps)) :
    let O := KAM.realInclusion₂ (n+n) ⁻¹' p11WrFastDom D eps
    AnalyticOnNhd ℝ (p11WrFastR D eps) O ∧
      KAM.Kepler.IsSymplecticOn 1 (p11WrFastR D eps) O ∧
      (∀ y ∈ O, KAM.realInclusion₂ (n+n) (p11WrFastR D eps y) =
        (p11FastData D eps).map (KAM.realInclusion₂ (n+n) y)) ∧
      (∀ y ∈ O, ∀ kf : Fin n → ℤ, y + p11FastShift kf ∈ O ∧
        p11WrFastR D eps (y + p11FastShift kf) = p11WrFastR D eps y + p11FastShift kf) ∧
      InjOn (p11WrFastR D eps) O := by
  intro O
  obtain ⟨hD, hI, -, -, -, -, hre, hSy, hE, -, -⟩ := hF
  have hreal : ∀ y : Phase (n+n), KAM.realInclusion₂ (n+n) y ∈ p11WrFastDom D eps →
      (p11FastData D eps).map (KAM.realInclusion₂ (n+n) y) =
        KAM.realInclusion₂ (n+n) (p11WrFastR D eps y) := fun y hy =>
    p11_eq_realInclusion₂_re (fun i => (hre y hy i).1) fun i => (hre y hy i).2
  obtain ⟨han, hsy⟩ := p11_realChart (p11WrFastDom_isOpen D eps) hD hreal hSy
  refine ⟨han, hsy, fun y hy => (hreal y hy).symm, fun y hy kf => ?_, fun y hy y' hy' h => ?_⟩
  · refine ⟨p11WrFastDom_shift hy kf, ?_⟩
    unfold p11WrFastR
    rw [p11_realInclusion₂_add_fastShift]
    have := hE (KAM.realInclusion₂ (n+n) y) hy kf
    simp only [KAM.realInclusion₂_apply] at this
    rw [this, p11ReC_add_fastShift]; rfl
  · have h' : (p11FastData D eps).map (KAM.realInclusion₂ (n+n) y) =
        (p11FastData D eps).map (KAM.realInclusion₂ (n+n) y') := by
      rw [hreal y hy, hreal y' hy', h]
    exact KAM.realInclusion₂_injective (n+n) (hI hy hy' h')

end Parts

end KAM.Planetary

end
