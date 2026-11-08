/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.FrozenForm
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The gradient identity (blueprint `bpW:w1:gradient-identity`), series part

For a real sequence `c ∈ ℓ^{a,p}`, `a > 0`: `G(c) = ¼ Σ_l c_l 𝒢(c)_l`
(`KAM.Wave.waveG_hasSum_pairing`, the unweighted pairing `⟨𝒢(c), c⟩₀`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ}

/-- `bpW:w1:gradient-identity` (i): `G(q) = ¼ Σ_l q_l 𝒢(q)_l = ¼ ⟨𝒢(q), q⟩₀` (absolutely
convergent), for `q ∈ ℓ^{a,p}`, `a > 0`. -/
theorem waveG_hasSum_pairing (ha : 0 < a) {c : ℕ+ → ℝ} (hc : WaveEll a p c) :
    HasSum (fun l : ℕ+ => (1 / 4) * (c l * waveCubic m hm c l)) (waveG m hm c) := by
  obtain ⟨hG, -⟩ := waveG_hasSum (m := m) hm ha hc
  let e : ℕ+ × ℕ+ × ℕ+ × ℕ+ ≃ ℕ+ × (ℕ+ × ℕ+ × ℕ+) :=
    { toFun := fun t => (t.2.2.2, (t.1, t.2.1, t.2.2.1))
      invFun := fun s => (s.2.1, s.2.2.1, s.2.2.2, s.1)
      left_inv := fun t => rfl
      right_inv := fun s => rfl }
  have h1 := (e.symm.hasSum_iff (f := fun t : ℕ+ × ℕ+ × ℕ+ × ℕ+ => (1 / 4) *
        ((waveHat m hm c t.1 * (waveHat m hm c t.2.1 *
            (waveHat m hm c t.2.2.1 * waveHat m hm c t.2.2.2))) *
          waveQuartic t.1 t.2.1 t.2.2.1 t.2.2.2))).2 hG
  refine HasSum.prod_fiberwise h1 fun l => ?_
  have hl := wave_sqrt_lam_pos m hm l
  have h2 := ((waveCubic_hasSum (m := m) hm ha hc l).1.mul_left
    ((1 / 4) * waveHat m hm c l * Real.sqrt (lam m hm l)))
  have e1 : (1 / 4) * waveHat m hm c l * Real.sqrt (lam m hm l) * waveCubic m hm c l =
      (1 / 4) * (c l * waveCubic m hm c l) := by
    unfold waveHat; field_simp
  rw [e1] at h2
  convert h2 using 1
  funext t
  simp only [Function.comp_apply, e, Equiv.coe_fn_symm_mk]
  field_simp

end KAM.Wave

end
