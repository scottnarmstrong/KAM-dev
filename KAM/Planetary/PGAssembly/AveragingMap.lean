/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.AveragingHyp

/-!
# P Part 5: conjugating the P2 output by the oscillator normalization (`stepP:p5:av-dict`)

The physical map is `T ∘ Ψ ∘ T⁻¹` and the physical remainder `2π · (R ∘ T⁻¹)`; this file records
the elementary properties of the conjugation (linearity, shifts, real points, openness of
`averagingDomain`).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-AV.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b n : ℕ} {d : PGData a b} {r mu : ℝ}

/-- The physical map `T ∘ Ψ ∘ T⁻¹`. -/
def avgPsi (Ψ : CPhase (a+b) → CPhase (a+b)) (z : CPhase (a+b)) : CPhase (a+b) :=
  pgOscNormalize (Ψ (pgOscUnnormalize z))

/-- The physical remainder `2π · (R ∘ T⁻¹)`. -/
def avgRem (R : CHam (a+b)) (z : CPhase (a+b)) : ℂ :=
  (2*Real.pi:ℂ) * R (pgOscUnnormalize z)

/-- `pgOscUnnormalize` as a continuous linear map. -/
def oscUnnormCLM (a b : ℕ) : CPhase (a+b) →L[ℂ] CPhase (a+b) :=
  ((diagCLM (fun i => (oscScaleFst a b i)⁻¹)).comp (ContinuousLinearMap.fst ℂ _ _)).prod
    ((diagCLM (fun i => (oscScaleSnd a b i)⁻¹)).comp (ContinuousLinearMap.snd ℂ _ _))

theorem pgOscUnnormalize_eq (z : CPhase (a+b)) : pgOscUnnormalize z = oscUnnormCLM a b z := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
  simp [pgOscUnnormalize, oscUnnormCLM, diagCLM_apply, oscScaleFst, oscScaleSnd, blockFast,
    blockSlow]

theorem pgOscUnnormalize_eq_fun :
    (pgOscUnnormalize : CPhase (a+b) → CPhase (a+b)) = oscUnnormCLM a b :=
  funext pgOscUnnormalize_eq

theorem differentiable_pgOscUnnormalize :
    Differentiable ℂ (pgOscUnnormalize : CPhase (a+b) → CPhase (a+b)) := by
  rw [pgOscUnnormalize_eq_fun]; exact (oscUnnormCLM a b).differentiable

theorem continuous_pgOscUnnormalize :
    Continuous (pgOscUnnormalize : CPhase (a+b) → CPhase (a+b)) :=
  differentiable_pgOscUnnormalize.continuous

theorem pgOscNormalize_add (u v : CPhase (a+b)) :
    pgOscNormalize (u + v) = pgOscNormalize u + pgOscNormalize v := by
  simp only [pgOscNormalize_eq, map_add]

theorem pgOscUnnormalize_add (u v : CPhase (a+b)) :
    pgOscUnnormalize (u + v) = pgOscUnnormalize u + pgOscUnnormalize v := by
  simp only [pgOscUnnormalize_eq, map_add]

theorem pgOscNormalize_injective : Function.Injective (pgOscNormalize : CPhase (a+b) → _) :=
  Function.LeftInverse.injective pgOscUnnormalize_normalize

theorem pgOscUnnormalize_injective : Function.Injective (pgOscUnnormalize : CPhase (a+b) → _) :=
  Function.LeftInverse.injective pgOscNormalize_unnormalize

/-- The shift by a lattice vector, in the normalized coordinates. -/
theorem pgOscNormalize_lattice (k : Fin a → ℤ) :
    pgOscNormalize ((Fin.append (fun i => (k i : ℂ)) (0 : Fin b → ℂ), 0) : CPhase (a+b)) =
      KAM.realInclusion₂ (a+b) (fastShift k) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
  simp [pgOscNormalize, blockFast, blockSlow, fastShift]

theorem pgOscUnnormalize_lattice (k : Fin a → ℤ) :
    pgOscUnnormalize (KAM.realInclusion₂ (a+b) (fastShift k)) =
      ((Fin.append (fun i => (k i : ℂ)) (0 : Fin b → ℂ), 0) : CPhase (a+b)) := by
  have := pgOscUnnormalize_normalize
    (((Fin.append (fun i => (k i : ℂ)) (0 : Fin b → ℂ), 0) : CPhase (a+b)))
  rwa [pgOscNormalize_lattice] at this

theorem pgOscUnnormalize_real (x : Phase (a+b)) :
    pgOscUnnormalize (KAM.realInclusion₂ (a+b) x) = KAM.realInclusion₂ (a+b)
      (Fin.append ((2*Real.pi)⁻¹ • blockFast x.1) ((Real.sqrt (2*Real.pi))⁻¹ • blockSlow x.1),
       Fin.append (blockFast x.2) ((Real.sqrt (2*Real.pi))⁻¹ • blockSlow x.2)) := by
  refine Prod.ext ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [pgOscUnnormalize, blockFast, blockSlow]

theorem pgOscNormalize_mem_range (x : Phase (a+b)) :
    pgOscNormalize (KAM.realInclusion₂ (a+b) x) ∈ range (KAM.realInclusion₂ (a+b)) :=
  ⟨_, (pgOscNormalize_real x).symm⟩

/-- Membership in `averagingDomain` is membership of the unnormalized point in the P2 domain. -/
theorem mem_averagingDomain_iff (h : admissible d (pgRstar d) r mu) {z : CPhase (a+b)} :
    z ∈ averagingDomain d r mu ↔ pgOscUnnormalize z ∈ oscDom (checkedCore d r mu)
      ((params d r mu).rhoBar/2) (pgOscEpsilon d/2) (pgOscEpsilon d/2) (pgOscWidth d/6) := by
  rw [← pg_osc_domain d r mu h]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [pgOscUnnormalize_normalize]
  · intro hz
    exact ⟨_, hz, pgOscNormalize_unnormalize z⟩

theorem isOpen_averagingDomain (h : admissible d (pgRstar d) r mu) :
    IsOpen (averagingDomain d r mu) := by
  have : averagingDomain d r mu = pgOscUnnormalize ⁻¹' oscDom (checkedCore d r mu)
      ((params d r mu).rhoBar/2) (pgOscEpsilon d/2) (pgOscEpsilon d/2) (pgOscWidth d/6) :=
    Set.ext fun z => mem_averagingDomain_iff h
  rw [this]
  exact (isOpen_oscDom _ _ _ _ _).preimage continuous_pgOscUnnormalize

end KAM.Planetary

end
