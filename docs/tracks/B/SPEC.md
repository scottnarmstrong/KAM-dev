# Track B: conventions and domains (program B, packages B0–B1)

Source plan: `docs/explorations/program-b-plan.md` on main (§2.1 conventions, §2.2 B1-T, §2.3 B1-E). Overnight
mode D71: nothing is frozen; B1-T and B1-E are proved as ordinary theorems in their exact proposed final form under
`KAM/EffectiveStability/`, and `FREEZE-PROPOSAL.md` carries the text for the owner.

## Carriers

- Phase space `(Fin n → ℝ) × (Fin n → ℝ)`, written in full in every proposed anchor (no new carrier, no
  `EuclideanSpace`). Torus coordinates are `w = (φ, J)`, lifted angles first; Cartesian coordinates are `w = (q, p)`.
- Field and form: the frozen `KAM.hamiltonianVectorField H z = (∂_2 H, -∂_1 H)` and `KAM.symplecticForm v w =
  Σ_i (v.2 i * w.1 i - v.1 i * w.2 i)`. Consequently `symplecticForm (X_H z) v = -fderiv H z v`.
- Oscillator actions: the frozen `KAM.Planetary.oscillatorAction p q j = (p j ^ 2 + q j ^ 2) / 2`, applied as
  `oscillatorAction w.2 w.1` (p = `w.2`, q = `w.1`).
- Poisson bracket with an action (Cartesian): `{I_j, R}(w) = q_j ∂_{p_j} R - p_j ∂_{q_j} R`, written inline as
  `w.1 j * fderiv ℝ R w (0, Pi.single j 1) - w.2 j * fderiv ℝ R w (Pi.single j 1, 0)`.

## Domains (inline set-builders in the anchors; named helpers only in implementation modules)

| Name (implementation) | Set | Use |
|---|---|---|
| `cyl c` | `{w | ∀ j, |w.2 j| < c j}` | open cylinder, chart domain at `c = b + ε` |
| `cylClosed c` | `{w | ∀ j, |w.2 j| ≤ c j}` | stopped region `overline C_b` (not compact: lifted angles) |
| `osc c` | `{w | ∀ j, oscillatorAction w.2 w.1 j < c j}` | open oscillator domain `E_{b+ε}` |
| `oscClosed c` | `{w | ∀ j, oscillatorAction w.2 w.1 j ≤ c j}` | compact stopped region `overline E_b` |

## Solution quantifiers (plan §2.1, specialized)

For each allowed `w₀` there are `T₁ > T` and `z : ℝ → Phase` with `z 0 = Ψ w₀`, `z t ∈ V` and `HasDerivAt z (X_H (z t)) t`
on `Ioo (-T₁) T₁`; every solution `y` in `V` on an order-connected `I ∋ 0` with `y 0 = Ψ w₀` agrees with `z` on
`I ∩ Ioo (-T₁) T₁`; the bounds hold for every `|t| ≤ T`, endpoints included. No `∃!` on a total function.

## Proof architecture (B1)

1. **Chart dynamics.** `K := H ∘ Ψ = N ∘ snd + R` (resp. `N ∘ I + R`) is `C²` on the open chart domain. Solve
   `w' = X_K(w)` there (maximal solution, `KAM.ODE.gen_maximal`).
2. **Transport.** `Ψ` symplectic ⇒ `DΨ(w)` injective ⇒ bijective; `ω(DΨ X_K, DΨ u) = ω(X_K, u) = -dK u =
   -dH(DΨ u) = ω(X_H ∘ Ψ, DΨ u)`, so `DΨ(w) X_K(w) = X_H(Ψ w)` and `z = Ψ ∘ w` solves the physical equation.
3. **Stopped drift.** `J_j' = -∂_{φ_j} K = -∂_{φ_j} R` (the `N` part has zero derivative along the angle line);
   `(I_j ∘ w)' = {I_j, K} = {I_j, R}` (the `N ∘ I` part is rotation invariant in the `j`-th plane).
4. **First exit.** With `a_j + T η_j < b_j`, a trajectory stays in the open region on `[-T, T] ∩` its interval.
5. **Continuation.** `KAM.ODE.gen_continuation_periodic` (torus; compact action box) or
   `gen_continuation_compact` (oscillator; compact `overline E_b`) pushes the maximal interval past `±T`.
6. **Uniqueness.** `KAM.ODE.gen_uniqueness_inter` in `V` (H `C²` on open `V`).

## Coordination

LP's `strongFirstExit_of_stopped_drift` (`KAM/Planetary/StrongAMD/Confinement.lean`) and lemma.farm's LambdaDrift
bridge are planetary-specific (phys. states, AMD barrier); B uses its own generic first-exit lemma in
`KAM/EffectiveStability/FirstExit.lean`. No LambdaDrift file is edited or imported.
