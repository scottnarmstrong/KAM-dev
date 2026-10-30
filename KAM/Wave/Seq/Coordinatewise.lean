/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Seq.Embed
public import KAM.Frozen.Wave.Defs.CubicGrad
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Derivatives of coordinates (blueprint-W `bpW:w1:coordinatewise`)

Off-frontier, source-faithful infrastructure; the dependency graph is still being built.

`hasDerivAt_coordinates_iff`: for `c : ℝ → ℓ²` with derivative `c'` at `t`, the coordinate curves
`(κ_{a,p} c)_j` have derivatives `(κ_{a',p'} v)_j` iff `ι̂ c' = v`.
`frozen_invariance_iff` is the form used for clause (4) of the frozen `KAM.Wave.nlw2`.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Wave

variable {K : Type*} [RCLike K]

/-- Coordinate functional of `κ_{a,p}` as a real-linear continuous map. -/
theorem hasDerivAt_coeffW {c : ℝ → lp (fun _ : ℕ+ => K) 2} {c' : lp (fun _ : ℕ+ => K) 2} {t : ℝ}
    (hc : HasDerivAt c c' t) (a p : ℝ) (j : ℕ+) :
    HasDerivAt (fun s => coeffW a p (c s) j) (coeffW a p c' j) t := by
  have := ((coeffWCLM (K := K) a p j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hc
  simpa [Function.comp_def] using this

/-- **Derivatives of coordinates** (blueprint `bpW:w1:coordinatewise`): with `ι̂ = embedCLM`,
(a) every coordinate curve `t ↦ (κ_{a,p} c(t))_j` has derivative `(κ_{a',p'} v)_j` at `t` iff
(b) `ι̂ c'(t) = v`. -/
theorem hasDerivAt_coordinates_iff {a p a' p' : ℝ} (ha : a' ≤ a) (hp : p' ≤ p)
    {c : ℝ → lp (fun _ : ℕ+ => K) 2} {c' : lp (fun _ : ℕ+ => K) 2} {t : ℝ}
    (hc : HasDerivAt c c' t) (v : lp (fun _ : ℕ+ => K) 2) :
    (∀ j : ℕ+, HasDerivAt (fun s => coeffW a p (c s) j) (coeffW a' p' v j) t) ↔
      embedCLM a p a' p' ha hp c' = v := by
  constructor
  · intro h
    refine coeffW_injective a' p' (funext fun j => ?_)
    rw [coeffW_embedCLM]
    exact (hasDerivAt_coeffW hc a p j).unique (h j)
  · rintro rfl j
    rw [coeffW_embedCLM a p a' p' ha hp c']
    exact hasDerivAt_coeffW hc a p j

/-- **Clause (4) of the frozen `KAM.Wave.nlw2`** as `ι̂ (DK(θ) ν) = X^w(K(θ))`
(blueprint `bpW:w1:coordinatewise`, last sentence). Here `v = (v₁, v₂)` represents the field
`X^w(K θ) ∈ ℓ^{1,0} × ℓ^{1,0}` (`bpW:w1:hamfield` (v)) in the coordinates `κ_{1,0}`: its coefficient
sequences are `λ_j p_j` and `-λ_j q_j - 𝒢(q)_j`. `Kmap` is differentiable at `θ`, and
`c(t) = Kmap(θ + tν)`. -/
theorem frozen_invariance_iff {m : ℝ} (hm : 0 < m) {Kmap : (Fin 2 → ℝ) → WaveSpace}
    {θ ν : Fin 2 → ℝ} (hK : DifferentiableAt ℝ Kmap θ) (v : WaveSpace)
    (hv₁ : coeffW 1 0 v.1 = fun j => lam m hm j * coeff (Kmap θ).2 j)
    (hv₂ : coeffW 1 0 v.2 = fun j =>
      -(lam m hm j * coeff (Kmap θ).1 j) - cubicGrad m hm (Kmap θ).1 j) :
    (∀ j : ℕ+,
        HasDerivAt (fun t : ℝ => coeff (Kmap (θ + t • ν)).1 j) (lam m hm j * coeff (Kmap θ).2 j) 0 ∧
        HasDerivAt (fun t : ℝ => coeff (Kmap (θ + t • ν)).2 j)
          (-(lam m hm j * coeff (Kmap θ).1 j) - cubicGrad m hm (Kmap θ).1 j) 0) ↔
      (embedCLM 1 1 1 0 le_rfl zero_le_one (fderiv ℝ Kmap θ ν).1 = v.1 ∧
        embedCLM 1 1 1 0 le_rfl zero_le_one (fderiv ℝ Kmap θ ν).2 = v.2) := by
  have hline : HasDerivAt (fun t : ℝ => θ + t • ν) ν 0 := by
    have h0 : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id' 0
    simpa using (HasDerivAt.smul_const h0 ν).const_add θ
  have hKθ : HasFDerivAt Kmap (fderiv ℝ Kmap θ) (θ + (0 : ℝ) • ν) := by
    simpa using hK.hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => Kmap (θ + t • ν)) (fderiv ℝ Kmap θ ν) 0 :=
    hKθ.comp_hasDerivAt 0 hline
  have h1 : HasDerivAt (fun t : ℝ => (Kmap (θ + t • ν)).1) (fderiv ℝ Kmap θ ν).1 0 :=
    (ContinuousLinearMap.fst ℝ (lp (fun _ : ℕ+ => ℝ) 2)
      (lp (fun _ : ℕ+ => ℝ) 2)).hasFDerivAt.comp_hasDerivAt 0 hc
  have h2 : HasDerivAt (fun t : ℝ => (Kmap (θ + t • ν)).2) (fderiv ℝ Kmap θ ν).2 0 :=
    (ContinuousLinearMap.snd ℝ (lp (fun _ : ℕ+ => ℝ) 2)
      (lp (fun _ : ℕ+ => ℝ) 2)).hasFDerivAt.comp_hasDerivAt 0 hc
  rw [← hasDerivAt_coordinates_iff le_rfl zero_le_one h1 v.1,
    ← hasDerivAt_coordinates_iff le_rfl zero_le_one h2 v.2, hv₁, hv₂]
  simp only [← coeffW_one_one]
  exact ⟨fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩, fun h j => ⟨h.1 j, h.2 j⟩⟩

end KAM.Wave

end
