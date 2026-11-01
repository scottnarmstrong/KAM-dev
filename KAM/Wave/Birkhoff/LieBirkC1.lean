/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieBirk
public import KAM.Wave.Birkhoff.LieFlow5
public import KAM.Wave.Birkhoff.LieRealMulti
public import KAM.Wave.Birkhoff.LieSlot4

/-!
# `C¹` regularity and multilinear reality for the W3 flow (blueprint-W `bpW:w3:flow`,
`bpW:w3:leibniz`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-FLOW, blueprint labels `bpW:w3:flow` (i), `bpW:w3:leibniz` (iii)
(audit findings F1, F2, F3), specialised to `T = ι ∘ S` (`birkT`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {m : ℝ} {hm : 0 < m} {a p : ℝ} {ha : 0 ≤ a} {hp : 1 / 2 ≤ p}

include hm hp in
/-- (`bpW:w3:flow` (i)) `(t, w) ↦ Γ_t(w)` is `C¹` on `(-2, 2) × B_{ρ₀}`. -/
theorem birkGamma_contDiffOn :
    ContDiffOn ℝ 1 (fun z : ℝ × BirkSpace => birkGamma m hm ha hp z.1 z.2)
      {z : ℝ × BirkSpace | |z.1| < 2 ∧ 40 * birkCF m p * ‖z.2‖ ^ 2 < 1} :=
  contDiffOn_lieGamma _ (birkCF_pos m hm hp).le (norm_birkT_le m hm ha hp) (birkCF_pos m hm hp)

include hm hp in
/-- (`bpW:w3:leibniz` (iii)) `Φ_k(ϱ w¹, …) = ϱ Φ_k(w¹, …)` for the Lie coefficients of `X_F`. -/
theorem birkLieMulti_rho (k : ℕ) (w : Fin (2 * k + 1) → BirkSpace) :
    lieMulti (birkT m hm ha hp) k (fun i => birkRho (w i)) =
      birkRho (lieMulti (birkT m hm ha hp) k w) :=
  lieMulti_rho _ birkRho (birkT_rho m hm ha hp) k w

/-- (`bpW:w3:lie-coeff`) The source slot recurrence for the Lie coefficients of `X_F` on all
ordered inputs: `Φ_{k+1}(w¹, …) = (1/(k+1)) Σ_i Φ_k(…, S(w^i, w^{i+1}, w^{i+2}), …)`
(`S` read through `ι : 𝔚⁺ → 𝔚`, i.e. `birkT`). -/
theorem birkLieMulti_slot (k : ℕ) (w : Fin (2 * (k + 1) + 1) → BirkSpace) :
    lieMulti (birkT m hm ha hp) (k + 1) w = ((1 : ℂ) / ((k : ℂ) + 1)) •
      ∑ i : Fin (2 * k + 1), lieMulti (birkT m hm ha hp) k
        (lieContractFin (birkT m hm ha hp) i w) :=
  lieMulti_slot _ k w

end KAM.Wave

end
