/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ledger.F
public import KAM.EffectiveStability.SJSU.Obs.Data
public import KAM.EffectiveStability.SJSU.Initial.Data
public import KAM.EffectiveStability.Tube.Obs.Check
public import KAM.EffectiveStability.Tube.Check.Domain

/-!
# The literal observables of T2-CONF and their bounds (package N8)

The observables are the rounded, pruned literals of N7 (`KAM.EffectiveStability.SJSU.Ftab`,
`Ledger/F.lean`): `f_j(u, φ) = Σ_{(s, d) ∈ Ftab j} u^s · d.eval(φ)` (`fObs`, `sjsuObs`).

For the tube checker (`sjsu_secular_confinement_of_obs`, `SJSU/Confinement/Statement.lean`), on the
box `|u_l| ≤ 2·10⁻⁶`:

* `sjsu_hfper`, `sjsu_hfd`: `2π`-periodicity and differentiability;
* `sjsu_hFu`, `sjsu_hFφ`: `|∂_{u_l} f_j| ≤ sjsuFuMax j l`, `|∂_{φ_b} f_j| ≤ sjsuFphiMax j b` (N5c's
  ceilings);
* `sjsu_hface`: `|f_j - c̃_j - u_j| ≤ ε_j` with `c̃ = sjsuObsCt`, `ε = sjsuObsEps`;
* `sjsu_hερ`: `10⁻⁶ + ε_j + (ε_j + μ) < 2·10⁻⁶`.

The nine kernel checks (`sjsuObs_fuOK_j`, `sjsuObs_phiOK_j`, `sjsuObs_faceOK_j`) are rational sums
over
the entries of the sparse literals, one declaration each.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The literal observable `f_j(u, φ) = Σ_{(s, d) ∈ Ftab j} u^s · d.eval(φ)`. -/
def fObs (j : ℕ) (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  ((Ftab j).map fun e => umon (monOf e.1) p.1 * (e.2.opd Fprm.w Fprm.S).eval Fprm.S p.2).sum

/-- The three observables of the tube checker. -/
def sjsuObs : Fin 3 → (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ := fun j => fObs j

/-- The literal centres `c̃_j`. -/
def sjsuObsCt : Fin 3 → ℝ := fun j => (sjsuObsCtQ j : ℝ)

/-- The face bounds `ε_j`. -/
def sjsuObsEps : Fin 3 → ℝ := fun j => (sjsuObsEpsQ j : ℝ)

theorem fObs_eq_litObs (j : ℕ) : fObs j = litObs Fprm.w Fprm.S (Ftab j) := rfl

/-! ### Kernel checks (one declaration each) -/

theorem sjsuObs_fuOK_0 : obsFuOK Fprm.S (2 / 10 ^ 6) (sjsuFuMax 0) (Ftab 0) = true := by
  decide +kernel
theorem sjsuObs_fuOK_1 : obsFuOK Fprm.S (2 / 10 ^ 6) (sjsuFuMax 1) (Ftab 1) = true := by
  decide +kernel
theorem sjsuObs_fuOK_2 : obsFuOK Fprm.S (2 / 10 ^ 6) (sjsuFuMax 2) (Ftab 2) = true := by
  decide +kernel
theorem sjsuObs_phiOK_0 : obsPhiOK Fprm.S (2 / 10 ^ 6) (sjsuFphiMax 0) (Ftab 0) = true := by
  decide +kernel
theorem sjsuObs_phiOK_1 : obsPhiOK Fprm.S (2 / 10 ^ 6) (sjsuFphiMax 1) (Ftab 1) = true := by
  decide +kernel
theorem sjsuObs_phiOK_2 : obsPhiOK Fprm.S (2 / 10 ^ 6) (sjsuFphiMax 2) (Ftab 2) = true := by
  decide +kernel
theorem sjsuObs_faceOK_0 :
    obsFaceOK Fprm.S (2 / 10 ^ 6) 0 (sjsuObsCtQ 0) (sjsuObsEpsQ 0) (Ftab 0) = true := by
  decide +kernel
theorem sjsuObs_faceOK_1 :
    obsFaceOK Fprm.S (2 / 10 ^ 6) 1 (sjsuObsCtQ 1) (sjsuObsEpsQ 1) (Ftab 1) = true := by
  decide +kernel
theorem sjsuObs_faceOK_2 :
    obsFaceOK Fprm.S (2 / 10 ^ 6) 2 (sjsuObsCtQ 2) (sjsuObsEpsQ 2) (Ftab 2) = true := by
  decide +kernel

/-! ### The hypotheses of the tube checker -/

theorem sjsu_hfper (j : Fin 3) : ObsPeriodic (sjsuObs j) :=
  litObs_add_two_pi Fprm.w Fprm.S (Ftab j)

theorem sjsu_hfd (j : Fin 3) : Differentiable ℝ (sjsuObs j) :=
  differentiable_litObs Fprm.w Fprm.S (Ftab j)

theorem box_cast {u : Fin 3 → ℝ} (hu : ∀ l, |u l| ≤ 2 / 10 ^ 6) :
    ∀ l, |u l| ≤ (((2 / 10 ^ 6 : ℚ)) : ℝ) := fun l => by push_cast; exact hu l

theorem sjsu_hFu : ∀ (j : Fin 3) (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ), (∀ l, |u l| ≤ 2 / 10 ^ 6) →
    ∀ l, |fderiv ℝ (sjsuObs j) (u, φ) (Pi.single l 1, 0)| ≤ (sjsuFuMax j l : ℝ) := by
  intro j u φ hu l
  fin_cases j
  · exact obsFuOK_sound sjsuObs_fuOK_0 u φ (box_cast hu) l
  · exact obsFuOK_sound sjsuObs_fuOK_1 u φ (box_cast hu) l
  · exact obsFuOK_sound sjsuObs_fuOK_2 u φ (box_cast hu) l

theorem sjsu_hFφ : ∀ (j : Fin 3) (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ), (∀ l, |u l| ≤ 2 / 10 ^ 6) →
    ∀ b, |fderiv ℝ (sjsuObs j) (u, φ) (0, Pi.single b 1)| ≤ (sjsuFphiMax j b : ℝ) := by
  intro j u φ hu b
  fin_cases j
  · exact obsPhiOK_sound sjsuObs_phiOK_0 u φ (box_cast hu) b
  · exact obsPhiOK_sound sjsuObs_phiOK_1 u φ (box_cast hu) b
  · exact obsPhiOK_sound sjsuObs_phiOK_2 u φ (box_cast hu) b

theorem sjsu_hface : ∀ (j : Fin 3) (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ), (∀ l, |u l| ≤ 2 / 10 ^ 6) →
    |sjsuObs j (u, φ) - sjsuObsCt j - u j| ≤ sjsuObsEps j := by
  intro j u φ hu
  fin_cases j
  · exact obsFaceOK_sound sjsuObs_faceOK_0 u φ (box_cast hu)
  · exact obsFaceOK_sound sjsuObs_faceOK_1 u φ (box_cast hu)
  · exact obsFaceOK_sound sjsuObs_faceOK_2 u φ (box_cast hu)

theorem sjsu_hερ : ∀ j : Fin 3, 1 / 10 ^ 6 + sjsuObsEps j + (sjsuObsEps j + (sjsuMu : ℝ)) <
    2 / 10 ^ 6 := by
  intro j
  fin_cases j <;> simp [sjsuObsEps, sjsuObsEpsQ, sjsuMu] <;> norm_num

end KAM.EffectiveStability.SJSU

end
