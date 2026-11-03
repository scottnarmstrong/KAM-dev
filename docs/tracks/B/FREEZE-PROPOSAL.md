# Track B: freeze proposal, draft 1 (B0 text of B1-T and B1-E)

Overnight mode (D71). **Nothing is frozen.** Statement audit round 1 (codex-2, `freeze/STATEMENT-REVIEW-1.md`): **PASS WITH NOTES**; C1 applied (docstrings and OD-B2 wording; no type change). **Both statements are proved tonight as ordinary theorems in exactly this text** (`KAM/EffectiveStability/Torus.lean`, `Oscillator.lean`; package audit B1-HEAD-1 PASS WITH NOTES; axioms `propext, Classical.choice, Quot.sound`). This file gives the exact proposed Lean text for the owner's morning
review. Base: branch `inp-b1` off `inp` 98ebd4771. The same text is proved tonight as ordinary theorems
`KAM.EffectiveStability.torus_confinement` / `.oscillator_confinement` (package B1-HEAD); any change requested
by audit or owner is applied to both.

## 1. Imports and module split

Anchor imports (frozen definitions only): `KAM.Frozen.Defs.HamiltonianVectorField`, `KAM.Frozen.Defs.SymplecticForm`,
`KAM.Frozen.Planetary.Defs.OscillatorAction`. No new definition is proposed for freezing: the four domains are inline
set-builders. Implementation modules (ordinary, `KAM/EffectiveStability/`): `Domains`, `StoppedDrift`, `FirstExit`,
`Transfer` (chart transport and observable transfer), `ChartFlow` (chart dynamics and continuation), `Torus`,
`Oscillator`. Elaboration receipt: `freeze/elaboration-draft-1.lean.txt`, checked with `b_lean.sh` (4 GB scope),
output only the two expected `declaration uses 'sorry'` warnings of the scratch bodies (never committed).

## 2. Exact text

```lean
open Set

namespace KAM.EffectiveStability

/-- **B1-T** (plan §2.2; GLS17 §4.3 (56)–(58)): finite confinement in a canonical cylinder.
The physical phase coordinates are lifted real coordinates. Only the pullback Hamiltonian
must be angle-periodic. The normal part is differentiated through `H ∘ Ψ - R`, which is
differentiable on the open chart domain; no differentiability hypothesis on `N` is needed. -/
theorem torus_confinement {n : ℕ} (a b η : Fin n → ℝ) (ε T : ℝ) (hε : 0 < ε) (hT : 0 ≤ T)
    (hη : ∀ j, 0 ≤ η j) (hmargin : ∀ j, a j + T * η j < b j)
    (V : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hV : IsOpen V)
    (H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (hH : ContDiffOn ℝ 2 H V)
    (Ψ Ψinv : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ))
    (hΨ : ContDiffOn ℝ 2 Ψ {w | ∀ j, |w.2 j| < b j + ε})
    (hΨV : ∀ w : (Fin n → ℝ) × (Fin n → ℝ), (∀ j, |w.2 j| < b j + ε) → Ψ w ∈ V)
    (hΨsymp : ∀ w : (Fin n → ℝ) × (Fin n → ℝ), (∀ j, |w.2 j| < b j + ε) →
      ∀ u v, KAM.symplecticForm (fderiv ℝ Ψ w u) (fderiv ℝ Ψ w v) = KAM.symplecticForm u v)
    (hΨinv : ∀ w : (Fin n → ℝ) × (Fin n → ℝ), (∀ j, |w.2 j| < b j + ε) → Ψinv (Ψ w) = w)
    (N : (Fin n → ℝ) → ℝ) (R : (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (hR : DifferentiableOn ℝ R {w | ∀ j, |w.2 j| < b j + ε})
    (hRper : ∀ (k : Fin n → ℤ) (w : (Fin n → ℝ) × (Fin n → ℝ)), (∀ j, |w.2 j| < b j + ε) →
      R (w + (fun i => (k i : ℝ), 0)) = R w)
    (hHΨ : ∀ w : (Fin n → ℝ) × (Fin n → ℝ), (∀ j, |w.2 j| < b j + ε) →
      H (Ψ w) = N w.2 + R w)
    (hRη : ∀ w : (Fin n → ℝ) × (Fin n → ℝ), (∀ j, |w.2 j| ≤ b j) →
      ∀ j, |fderiv ℝ R w (Pi.single j 1, 0)| ≤ η j)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hw₀ : ∀ j, |w₀.2 j| ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = Ψ w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ V ∧ HasDerivAt z (KAM.hamiltonianVectorField H (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = Ψ w₀ →
        (∀ t ∈ I, y t ∈ V ∧ HasDerivAt y (KAM.hamiltonianVectorField H (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → Ψ (Ψinv (z t)) = z t ∧
        ∀ j, |(Ψinv (z t)).2 j - w₀.2 j| ≤ η j * |t| ∧ |(Ψinv (z t)).2 j| ≤ a j + η j * T := by
  ...

/-- **B1-E** (plan §2.3; CL20 §4.1 (32)–(37)): Cartesian oscillator confinement,
including zero actions. Coordinates are `w = (q, p)`, with action
`KAM.Planetary.oscillatorAction w.2 w.1`, so `I_j = (p_j² + q_j²) / 2` and
`{I_j, R} = q_j ∂_{p_j} R - p_j ∂_{q_j} R`. Rotation invariance of the differentiable
function `H ∘ Ψ - R` gives the normal-part cancellation without differentiating `N`. -/
theorem oscillator_confinement {n : ℕ} (a b η : Fin n → ℝ) (ε T : ℝ) (hε : 0 < ε) (hT : 0 ≤ T)
    (hη : ∀ j, 0 ≤ η j) (hmargin : ∀ j, a j + T * η j < b j)
    (V : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hV : IsOpen V)
    (H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (hH : ContDiffOn ℝ 2 H V)
    (Ψ Ψinv : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ))
    (hΨ : ContDiffOn ℝ 2 Ψ {w | ∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j < b j + ε})
    (hΨV : ∀ w : (Fin n → ℝ) × (Fin n → ℝ),
      (∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j < b j + ε) → Ψ w ∈ V)
    (hΨsymp : ∀ w : (Fin n → ℝ) × (Fin n → ℝ),
      (∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j < b j + ε) →
      ∀ u v, KAM.symplecticForm (fderiv ℝ Ψ w u) (fderiv ℝ Ψ w v) = KAM.symplecticForm u v)
    (hΨinv : ∀ w : (Fin n → ℝ) × (Fin n → ℝ),
      (∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j < b j + ε) → Ψinv (Ψ w) = w)
    (N : (Fin n → ℝ) → ℝ) (R : (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (hR : DifferentiableOn ℝ R {w | ∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j < b j + ε})
    (hHΨ : ∀ w : (Fin n → ℝ) × (Fin n → ℝ),
      (∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j < b j + ε) →
      H (Ψ w) = N (KAM.Planetary.oscillatorAction w.2 w.1) + R w)
    (hRη : ∀ w : (Fin n → ℝ) × (Fin n → ℝ),
      (∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j ≤ b j) →
      ∀ j, |w.1 j * fderiv ℝ R w (0, Pi.single j 1) - w.2 j * fderiv ℝ R w (Pi.single j 1, 0)|
        ≤ η j)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ))
    (hw₀ : ∀ j, KAM.Planetary.oscillatorAction w₀.2 w₀.1 j ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = Ψ w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ V ∧ HasDerivAt z (KAM.hamiltonianVectorField H (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = Ψ w₀ →
        (∀ t ∈ I, y t ∈ V ∧ HasDerivAt y (KAM.hamiltonianVectorField H (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → Ψ (Ψinv (z t)) = z t ∧
        ∀ j, |KAM.Planetary.oscillatorAction (Ψinv (z t)).2 (Ψinv (z t)).1 j -
            KAM.Planetary.oscillatorAction w₀.2 w₀.1 j| ≤ η j * |t| ∧
          KAM.Planetary.oscillatorAction (Ψinv (z t)).2 (Ψinv (z t)).1 j ≤ a j + η j * T := by
  ...

end KAM.EffectiveStability
```

## 3. Source-to-binder table

| Binder / clause | B1-T source (plan §2.2; GLS17 §4.3) | B1-E source (plan §2.3; CL20 §4.1) | Note |
|---|---|---|---|
| `n`, `a b η : Fin n → ℝ`, `ε T : ℝ` | "n ≥ 1, a,b,η : Vec n, ε > 0, T ≥ 0" | same | `n ≥ 1` dropped (OD-B6) |
| `hε`, `hT`, `hη` | `ε > 0`, `T ≥ 0`, `η_j ≥ 0` | same | |
| `hmargin` | `a_j + Tη_j < b_j` (strict) | same; `b_j = ρ_j²` (action margin, not radius) | implies `a_j < b_j`; `0 ≤ a_j` dropped (OD-B2) |
| `V`, `hV`, `H`, `hH` | V open, H `C²` on V | H `C²` on open V | periodicity of V, H dropped (OD-B2) |
| `Ψ`, `hΨ`, `hΨV` | Ψ `C²` from `C_(b+ε)` into V | Ψ `C²` from `E_(b+ε)` into V | "onto an open subset", inverse regularity dropped (OD-B2) |
| `hΨsymp` | "symplectic" | "symplectic" | preserves `KAM.symplecticForm` on derivatives |
| `Ψinv`, `hΨinv` | `Ψ⁻¹`, "with a C² inverse" | same | left inverse only (OD-B3) |
| `N`, `R`, `hHΨ` | `H(Ψ(φ,J)) = N(J) + R(φ,J)` on `C_(b+ε)` | `H∘Ψ = N∘I + R` on `E_(b+ε)` | N unrestricted (OD-B2) |
| `hR` | R `C²` on `C_(b+ε)` | R `C²` on `E_(b+ε)` | weakened to differentiable (OD-B2) |
| `hRper` | "R angle-periodic" | — | needed for continuation (unbounded angles) |
| `hRη` | `|fderiv ℝ R w (e_j,0)| ≤ η_j` on `overline C_b` | `|{I_j,R}(w)| ≤ η_j` on `overline E_b` | bracket inline, SPEC sign convention |
| `w₀`, `hw₀` | `∀ j, |J₀ j| ≤ a_j` | `I_j(w₀) ≤ a_j` | closed initial box |
| `T₁`, `z`, solution clause | §2.1: open interval ⊇ `[-T,T]`, `z 0 = z₀`, in V, `HasDerivAt` | same | `Ioo (-T₁) T₁` (OD-B4) |
| uniqueness clause | §2.1 "every other solution in V on an interval containing zero agrees on the intersection" | same | `I.OrdConnected`, `0 ∈ I` |
| `Ψ (Ψinv (z t)) = z t` | "w(t) = Ψ⁻¹(z(t))" (the orbit stays in the chart image) | same | |
| drift and level bounds | (B1-T) `|J_j(t)-J_j(0)| ≤ η_j|t|`, `|J_j(t)| ≤ a_j + η_jT` | (B1-E) `|I_j(w(t)) - I_j(w₀)| ≤ η_j|t|`, `I_j ≤ a_j + η_jT` | `< b_j` is `hmargin`; `0 ≤ I_j` is definitional |

## 4. Review packet (plan §7 Brief 1, item iv)

- **Why continuation is proved, not assumed.** No hypothesis mentions a trajectory. The chart flow is the maximal
  solution of `w' = X_K(w)` with `K = H ∘ Ψ` on the open chart domain (`gen_maximal`). The stopped-drift bound holds
  on any stretch of its interval where it stays in the closed region; the strict margin and a first-exit (supremum)
  argument show it never leaves on `[-T,T] ∩` its interval; if an end of the interval were within `[-T,T]`, the
  orbit would be confined in a compact action set up to that end, and `gen_continuation_periodic` /
  `gen_continuation_compact` would make the end infinite, a contradiction. So the interval contains `[-T,T]` and is
  open, which yields `T₁ > T`. The `T = 0` case uses the same open maximal interval.
- **How lattice compactness is used (B1-T).** `overline C_b` is not compact (lifted angles). `R` periodic ⇒ `K`
  periodic (`hHΨ`, translation invariance of `C_(b+ε)`) ⇒ `X_K` periodic. `gen_continuation_periodic` then needs only
  the action component in the compact box `{J | ∀ j, |J_j| ≤ b_j} ⊆ {|J_j| < b_j + ε}`; uniform ODE data on a
  fundamental cell transfers by periodicity. Ψ's equivariance is not needed: the dynamics is solved in the chart.
- **Why the endpoint margin is strict.** The drift bound is available only while the orbit is in the stopped
  region `overline C_b`. Let `s ≤ T` be the supremum of times up to which the orbit stays in `overline C_b`. At `s` the
  bound gives `|J_j(s)| ≤ a_j + η_j s ≤ a_j + η_jT < b_j` for every `j`: the orbit is in the open `C_b`, so by
  continuity it stays in `overline C_b` slightly beyond `s`, contradicting maximality. With `a_j + η_jT = b_j`
  (e.g. `η_j = 0`, `a_j = b_j`) the orbit may sit on the boundary at `s`, where the closed-region bound says nothing
  about later times, and the argument fails. The strict margin is also what places the orbit in the open `C_b`
  in the conclusion.
- **Why the physical solution is unique in all of V**, not just in the chart image: `H` is `C²` on open `V`, so
  `X_H` is `C¹` there and `gen_uniqueness_inter` applies to any solution in `V`.
- **Zero oscillator actions.** The Cartesian chart has no singularity at `I_j = 0`; `{I_j, N∘I} = 0` follows from
  invariance of `N ∘ I` under the rotation in the `j`-th `(q_j, p_j)` plane; the composition `N ∘ I = K - R` is
  differentiable on the chart domain; differentiability of `N` itself is not asserted (B1-HEAD audit 1, N1).

## 5. Source findings (plan §9): dispositions

| Finding | Relevance to B1-T/E | Disposition |
|---|---|---|
| CL20 p. 5 after (4), harmonic index `ℓ` vs `ℓ+2` | none (normal-form indexing; B2+) | forward to errata ledger; recheck at B2 |
| CL20 p. 34 after (56), degree `+2` | none (B2/B3 arrays) | forward; recheck at B2 |
| CL20 p. 23 after (47), `ν₂ = O(μ)` | none (Trojan, B6/B7) | forward |
| BFN16 Def. 1 p. 3, repeated initial point | none (B2-steep) | forward |
| GLS17 p. 12 `λ₅` | none (model §2, B6) | forward |
| GLS17 p. 12 (13) `j=0..3` | none | forward |
| CL20 §4.1 (32)–(37) used by B1-E | squared radii: `b_j = ρ_j²`; the theorem is stated in actions, so no radius/margin confusion can enter | no defect found |
| GLS17 (56)–(58) used by B1-T | (58) keeps only the first remainder term; B1-T keeps the whole remainder in `hRη` | acknowledged approximation, not an erratum |

## 6. Deviations introduced (for the errata ledger)

`C²`/differentiable regularity instead of analytic; anisotropic closed initial boxes with strict outer margins;
explicit two-sided existence on `Ioo (-T₁) T₁` and uniqueness in all of `V`; Cartesian handling of zero actions;
minimal premise list (OD-B2); left-inverse chart (OD-B3); `n ≥ 1` dropped (OD-B6).
