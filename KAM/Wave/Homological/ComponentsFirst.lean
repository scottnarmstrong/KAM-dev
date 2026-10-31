/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.ComponentsBasic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Component bounds, part B (blueprint-W `bpW:w4:components` (i))

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

`homComp_first`: if `|X_R|_r ≤ ε` on `D(s,r)` then for every `θ ∈ T_s`: `|b| ≤ 2πε`,
`‖c^±‖ ≤ rε/√2`, `‖2P‖, ‖Q‖, ‖Q^T‖, ‖2P'‖ ≤ ε`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

/-- The hypothesis `|X_R|_r ≤ ε` on `D(s,r)`. -/
def HomFieldBound {a p pb s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (r ε : ℝ) (T : HomTaylor
    a p pb s) : Prop :=
  ∀ θ y z zb, HomDomain s r θ y z zb → homXnorm ha hp hpb r T θ y z zb ≤ ε

theorem homFieldBound_nonneg {a p pb s : ℝ} {ha : 0 ≤ a} {hp : 0 ≤ p} {hpb : p ≤ pb} {r ε : ℝ} (hr
    : 0 < r)
    {T : HomTaylor a p pb s} (hs : 0 < s) (hX : HomFieldBound ha hp hpb r ε T) : 0 ≤ ε := by
  have hθ : (0 : Fin 2 → ℂ) ∈ complexStrip 2 s := fun i => by simpa using hs
  exact (homXnorm_nonneg ha hp hpb hr T 0 0 0 0).trans
    (hX 0 0 0 0 (homDomain_y hθ hr (by simpa using pow_pos hr 2)))

/-- **Component bounds, (i)** (blueprint `bpW:w4:components` (i)). -/
theorem homComp_first {a p pb s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε : ℝ} (hr : 0 < r)
    (T : HomTaylor a p pb s) (hX : HomFieldBound ha hp hpb r ε T) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 s) :
    ‖T.b θ‖ ≤ 2 * Real.pi * ε ∧ ‖T.cp θ‖ ≤ r * ε / Real.sqrt 2 ∧ ‖T.cm θ‖ ≤ r * ε / Real.sqrt 2 ∧
      ‖(2 : ℂ) • T.P θ‖ ≤ ε ∧ ‖T.Q θ‖ ≤ ε ∧ ‖T.Qt θ‖ ≤ ε ∧ ‖(2 : ℂ) • T.P' θ‖ ≤ ε := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hρ : 0 < r / Real.sqrt 2 := by positivity
  have h0 := homXnorm_parts ha hp hpb hr T
    (hX θ 0 0 0 (homDomain_y hθ hr (by simpa using pow_pos hr 2)))
  have hKe : r * ε / Real.sqrt 2 / (r / Real.sqrt 2) = ε := by field_simp
  have ptz : ∀ x : HomL2, ‖x‖ ≤ 1 → ∀ ζ : ℂ, ‖ζ‖ < r / Real.sqrt 2 →
      ‖ζ • x‖ < r / Real.sqrt 2 := fun x hx ζ hζ => by
    rw [norm_smul]
    calc ‖ζ‖ * ‖x‖ ≤ ‖ζ‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      _ < _ := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [homRy] using h0.1
  · simpa [homRz] using h0.2.2.2.1
  · simpa [homRzb] using h0.2.2.2.2
  · have := homAffine_bound hρ (T.cp θ) ((2 : ℂ) • T.P θ) (K := r * ε / Real.sqrt 2)
      (fun x hx ζ hζ => by
        have := (homXnorm_parts ha hp hpb hr T
          (hX θ 0 (ζ • x) 0 (homDomain_z hθ hr (ptz x hx ζ hζ)))).2.2.2.1
        simpa [homRz, map_smul, smul_comm ζ (2 : ℂ), add_assoc] using this)
    rwa [hKe] at this
  · have := homAffine_bound hρ (T.cm θ) (T.Q θ) (K := r * ε / Real.sqrt 2)
      (fun x hx ζ hζ => by
        have := (homXnorm_parts ha hp hpb hr T
          (hX θ 0 (ζ • x) 0 (homDomain_z hθ hr (ptz x hx ζ hζ)))).2.2.2.2
        simpa [homRzb, map_smul, add_assoc] using this)
    rwa [hKe] at this
  · have := homAffine_bound hρ (T.cp θ) (T.Qt θ) (K := r * ε / Real.sqrt 2)
      (fun x hx ζ hζ => by
        have := (homXnorm_parts ha hp hpb hr T
          (hX θ 0 0 (ζ • x) (homDomain_zb hθ hr (ptz x hx ζ hζ)))).2.2.2.1
        simpa [homRz, map_smul, add_assoc] using this)
    rwa [hKe] at this
  · have := homAffine_bound hρ (T.cm θ) ((2 : ℂ) • T.P' θ) (K := r * ε / Real.sqrt 2)
      (fun x hx ζ hζ => by
        have := (homXnorm_parts ha hp hpb hr T
          (hX θ 0 0 (ζ • x) (homDomain_zb hθ hr (ptz x hx ζ hζ)))).2.2.2.2
        simpa [homRzb, map_smul, smul_comm ζ (2 : ℂ), add_assoc] using this)
    rwa [hKe] at this

end KAM.Wave
