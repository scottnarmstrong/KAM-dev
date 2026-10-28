/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Nekhoroshev.Partial.Constants
public import KAM.Nekhoroshev.Partial.Coordinates
public import KAM.Weighted.SupWeighted
public import KAM.Frozen.Nekhoroshev.Defs.IsPartialPerturbation
public import KAM.Frozen.Nekhoroshev.Defs.PartialComplexDomain
public import KAM.Frozen.Nekhoroshev.Defs.InnerCore
public import KAM.Frozen.Nekhoroshev.Defs.ComplexifyPhase
public import KAM.Frozen.Planetary.Defs.DegenerateHamiltonian
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Part 11 (N11-E3): the block setting, the complex domain and the field equality

The block geometry `block_setting`, the signed pair `signedH`, `signedF`, the slow rescaling
`slowScale` and `blockPert`, the physical real set `physicalDomain`, the lemma `domain`
(`bpN:p11:domain`, steps `dm-pts` and `dm-norm`: complex points, holomorphy, periodicity,
reality and the weighted bound of the rescaled perturbation) and `domain_field` (step `dm-field`:
the frozen Hamiltonian field equals the signed weighted field on the physical set).
Design `docs/tracks/N/design/N11-LEAN-DESIGN.md`.
-/

@[expose] public noncomputable section

open Set Metric
open KAM.Weighted

namespace KAM.Nekhoroshev

variable {n k : ℕ}

def block_setting (a : PartialData n k) (μ : ℝ) (Ic : Fin n → ℝ) (r : ℝ) : PartialBlock n k :=
  ⟨Ic, innerCore a.D (3*(constants a).d μ/4), r, (constants a).d μ/4⟩
def signedH (a : PartialData n k) (σ : ℝ) (I : Fin n → ℂ) : ℂ :=
  (σ:ℂ)*a.h I/(2*(Real.pi:ℂ))
def signedF (_a : PartialData n k) (σ μ : ℝ) (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ)
    (z : EC n k) : ℂ :=
  (σ*μ/(2*Real.pi):ℝ)*P (Fin.append (fun i => (2*Real.pi:ℂ)*z.1 i) (slowPair z).1,
    Fin.append (fastAction z) (slowPair z).2)
/-- Pull physical slow coordinates back by the fixed block scale. -/
def slowScale (lam : ℝ) (z : EC n k) : EC n k :=
  (z.1, Fin.append (fastAction z)
    (Fin.append (fun i => (lam:ℂ)*(slowPair z).1 i) (fun i => (lam:ℂ)*(slowPair z).2 i)))
def blockPert (a : PartialData n k) (μ σ : ℝ) (Ic : Fin n → ℝ) (r : ℝ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) : EC n k → ℂ :=
  signedF a σ μ P ∘ slowScale (block_setting a μ Ic r).lam

/-- Physical period-one coordinates (no block-dependent coordinate scale). -/
def physicalDomain (Ic : Fin n → ℝ) (R w : ℝ) (S : Set (KAM.Planetary.Phase k)) : Set (ER n k) :=
  {z | ‖fastAction z-Ic‖ < R ∧ ∃ v ∈ S, ‖slowPair z-v‖ < w}

/-- The physical phase point attached to an extended point (cf. `signedF`). -/
private def blockLift (z : EC n k) : (Fin (n+k) → ℂ) × (Fin (n+k) → ℂ) :=
  (Fin.append (fun i => (2*Real.pi:ℂ)*z.1 i) (slowPair z).1,
    Fin.append (fastAction z) (slowPair z).2)

private theorem signedF_eq (a : PartialData n k) (σ μ : ℝ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) (z : EC n k) :
    signedF a σ μ P z = ((σ*μ/(2*Real.pi):ℝ):ℂ) * P (blockLift z) := rfl

@[simp] private theorem fastAction_slowScale (lam : ℝ) (z : EC n k) :
    fastAction (slowScale lam z) = fastAction z := by
  funext i
  simp [fastAction, slowScale, Fin.append_left]

@[simp] private theorem slowPair_slowScale_fst (lam : ℝ) (z : EC n k) (i : Fin k) :
    (slowPair (slowScale lam z)).1 i = (lam:ℂ) * (slowPair z).1 i := by
  simp [slowPair, slowScale, Fin.append_right, Fin.append_left]

@[simp] private theorem slowPair_slowScale_snd (lam : ℝ) (z : EC n k) (i : Fin k) :
    (slowPair (slowScale lam z)).2 i = (lam:ℂ) * (slowPair z).2 i := by
  show Fin.append _ (Fin.append _ _) (Fin.natAdd n (Fin.natAdd k i)) = _
  rw [Fin.append_right, Fin.append_right]

private theorem blockLift_extCx (w : ER n k) :
    blockLift (extCx w) = complexifyPhase (thetaInv w) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [blockLift, complexifyPhase, thetaInv, extCx, Fin.append_left]
    · simp [blockLift, complexifyPhase, thetaInv, extCx, Fin.append_right, slowPair]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [blockLift, complexifyPhase, thetaInv, extCx, Fin.append_left, fastAction]
    · simp [blockLift, complexifyPhase, thetaInv, extCx, Fin.append_right, slowPair]

private theorem realWfield_const_mul {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (c : ℝ) (f : ER n k → ℝ)
    (z : ER n k) :
    realWfield c (fun w => σ * f w) z = σ • realWfield c f z := by
  have hA : ∀ v, fderiv ℝ (fun w => σ * f w) z v = σ * fderiv ℝ f z v := fun v => by
    rcases hσ with rfl | rfl
    · simp
    · have hf : (fun w => (-1:ℝ) * f w) = -f := by funext w; show _ = -(f w); ring
      rw [hf, fderiv_neg]; simp
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · simp only [realWfield, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, hA]
  · refine ext_cases (P := fun i => (realWfield c (fun w => σ * f w) z).2 i =
        (σ • realWfield c f z).2 i) (fun j => ?_) (fun j => ?_) (fun j => ?_) i
    · simp only [realWfield, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, hA, Fin.append_left]
      ring
    · simp only [realWfield, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, hA, Fin.append_left,
        Fin.append_right]
      ring
    · simp only [realWfield, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, hA, Fin.append_left,
        Fin.append_right]
      ring

theorem domain_field (a : PartialData n k) {μ σ R : ℝ} {Ic : Fin n → ℝ}
    (hμ : 0 < μ) (hσ : DefiniteSign a σ) (hIc : Ic ∈ a.G) (hR : 0 < R) (hRR : R ≤ (constants a).r0)
    (hd : (constants a).d μ ≤ a.ρ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) (hP : IsPartialPerturbation a.G' a.D a.ρ P) :
    let b := block_setting a μ Ic R
    let H := KAM.Planetary.degenerateHamiltonian (realPart a.h) (fun _ w => (P (complexifyPhase w)).re) μ
    EqOn (fun z => σ • realWfield (2*Real.pi) (converted H) z)
      (realWfield (2*Real.pi) (fun z => (liftFast (signedH a σ) (extCx z)+signedF a σ μ P (extCx z)).re))
      (physicalDomain Ic R b.w b.S) := by
  intro b H z _
  have hpt : ∀ w : ER n k, σ * converted H w =
      (liftFast (signedH a σ) (extCx w) + signedF a σ μ P (extCx w)).re := by
    intro w
    have hfast : (KAM.Planetary.fast (b := k) (thetaInv w).2) = fastAction w := by
      funext i; simp [KAM.Planetary.fast, thetaInv, Fin.append_left, fastAction]
    have hrp : realPart a.h (fastAction w) = (a.h (fastAction (extCx w))).re := rfl
    simp only [converted, H, KAM.Planetary.degenerateHamiltonian, hfast, hrp, liftFast, signedH,
      signedF_eq, blockLift_extCx, Complex.add_re, Complex.re_ofReal_mul]
    have hc : ∀ x : ℂ, ((σ:ℂ) * x / (2*(Real.pi:ℂ))).re = σ/(2*Real.pi) * x.re := fun x => by
      have : (σ:ℂ) * x / (2*(Real.pi:ℂ)) = ((σ/(2*Real.pi):ℝ):ℂ) * x := by push_cast; ring
      rw [this, Complex.re_ofReal_mul]
    have : (2*Real.pi) ≠ 0 := by positivity
    simp only [hc]
    field_simp
  have hfun : (fun w => (liftFast (signedH a σ) (extCx w) + signedF a σ μ P (extCx w)).re) =
      fun w => σ * converted H w := funext fun w => (hpt w).symm
  simp only [hfun]
  exact (realWfield_const_mul hσ.1 _ _ z).symm

end KAM.Nekhoroshev

end
