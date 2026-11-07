/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import KAM.Frozen.EffectiveStability.SJSU.SJSU18O2
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Planetary.Defs.OscillatorAction
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Order.Interval.Set.OrdConnected
import KAM.Provider.EffectiveStability.SJSUSecularConfinement

/-!
# Frozen theorem `KAM.EffectiveStability.sjsu_secular_confinement`

Program T2-CONF (D74, model of record D75): literal finite-time confinement of the secular
Sun–Jupiter–Saturn–Uranus model `SJSU18-O2`.
Owner-approved on 2026-11-06 (decision D76; exact text: draft v2 of
`docs/explorations/sjsu-g2-t2conf-proposal.md`, program T2-CONF). Part of the opt-in application
library `KAMSJSU` (D51). This file is frozen: it is hashed in `manifest/frozen-anchors.json`;
any change needs an owner-approved versioned successor.
Frozen and sealed in one pass: the theorem is proved as an ordinary theorem
(`KAM.EffectiveStability.SJSU.sjsu_secular_confinement_proof`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

/-- **SJSU secular confinement** (T2-CONF, D74/D75; `docs/explorations/sjs-rigor-plan.md` §1.1): for
every initial state within `10⁻⁶` (sup norm in `(ξ, η)`) of the nominal secular state (SLG13 Table 1 read
as Poincaré elements and mapped to secular variables, `applications/sjsu/validation/
table2_map_poincare_order1.json`), `SJSU18-O2` has a solution on `(-T₁, T₁)` with `T₁ > 5·10⁹` yr,
unique among solutions on intervals through `0`, along which for `|t| ≤ 5·10⁹` yr the fixed-reference
secular-model eccentricities of Jupiter, Saturn and Uranus, `e_j = √(1 - (1 - Γ_j/Λ*_j)²)` with
`Γ_j = (ξ_j² + η_j²)/2` and the dataset's reference actions `Λ*_j` (at `L = 0`), stay in `[0.026, 0.062]`,
`[0.009, 0.085]` and `[0.006, 0.063]`. Nothing is asserted about the osculating elements of the full
planetary problem. -/
theorem sjsu_secular_confinement (z₀ : (Fin 3 → ℝ) × (Fin 3 → ℝ))
    (hz₀ : ∀ j, |z₀.2 j - ![0.03446271128616895, -0.0014352339355918572, -0.010122263133599879] j| ≤ 1 / 10 ^ 6 ∧
      |z₀.1 j - ![-0.009080669615926963, -0.025602508346796338, -0.0016540224121661881] j| ≤ 1 / 10 ^ 6) :
    ∃ T₁ : ℝ, 5 * 10 ^ 9 < T₁ ∧ ∃ z : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ), z 0 = z₀ ∧
      (∀ t ∈ Set.Ioo (-T₁) T₁, HasDerivAt z (KAM.hamiltonianVectorField sjsu18O2 (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I → y 0 = z₀ →
        (∀ t ∈ I, HasDerivAt y (KAM.hamiltonianVectorField sjsu18O2 (y t)) t) →
        ∀ t ∈ I, t ∈ Set.Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ 5 * 10 ^ 9 → ∀ j,
        ![0.026, 0.009, 0.006] j ≤ Real.sqrt (1 - (1 - KAM.Planetary.oscillatorAction (z t).2 (z t).1 j / ![5.3993226066969503769e-1, 2.1912825008425995084e-1, 4.7474331515411474555e-2] j) ^ 2) ∧
        Real.sqrt (1 - (1 - KAM.Planetary.oscillatorAction (z t).2 (z t).1 j / ![5.3993226066969503769e-1, 2.1912825008425995084e-1, 4.7474331515411474555e-2] j) ^ 2) ≤ ![0.062, 0.085, 0.063] j :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.EffectiveStability.sjsu_secular_confinement z₀ hz₀
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.EffectiveStability

end
-- FROZEN_ANCHOR_SUFFIX_END
