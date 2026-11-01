# MAG-PILOT freeze proposal: a magnetic field-line barrier at ε = 3/2500

1 November 2026, branch `mag-pilot`. **Proposal only; nothing is frozen.** Model: plan-magnetic-barrier §1.1 with
ε = 3/2500 (owner-approved fallback, D66). Numerical gate (phase 1, commit `6471cb75`): the finite candidate's
weighted residual is 1.6·10⁻³⁷ at 512² and 4.6·10⁻⁴⁰ at 1024², against the 10⁻²⁶ gate. The sampled v2 threshold
(refined A, classical) is 10⁻¹⁸·⁴⁵ at ρ = 3/1000. The measured flux range is [0.32798, 0.38566], and the minimum
angle slope is 0.760.

## Plain-language summary

The model has field lines on a torus. q is the poloidal angle and φ the toroidal angle, both measured in turns,
and p is the flux. The integrable part is h(p) = p − ¾p² + ⅓p³ − p⁴/16. The perturbation is two resonant cosine
modes of size ε = 3/2500, plus the quadratic control term. Each field line follows q̇ = h′(p), ṗ = −∂_qV, φ̇ = 1.

The theorem says there is a smooth (real-analytic) surface p = P(q, φ) with flux between 0.32 and 0.39 that field
lines never cross. A field line below the surface stays below it forever, in both directions of time. The same
holds for lines on the surface and lines above it. In particular, field lines starting at flux below 0.32 never
reach flux 0.39, and conversely. Field lines exist for all time and are unique.

This is **one separating surface**. It is not a bounded slab, and it is not confinement on both sides.

## Proposed Lean text

There are five one-declaration files under the proposed `KAM/Frozen/Magnetic/` (the drafts are in
[`draft/`](draft/)). They mirror the sealed lunar band: the product state `ℝ × ℝ × ℝ`, the field written with
`deriv`, and raw `HasDerivAt` solutions, as in `soField` and `lunar_spin_confinement`.

```lean
def magEps : ℝ := 3 / 2500

def magH0 (p : ℝ) : ℝ :=
  p - 3 / 4 * p ^ 2 + 1 / 3 * p ^ 3 - 1 / 16 * p ^ 4

def magV (q φ : ℝ) : ℝ :=
  magEps * (cos (2 * π * (2 * q - φ)) + cos (2 * π * (3 * q - 2 * φ))) +
    1427 / 3200 * magEps ^ 2 *
      (32000 / 2777 * cos (2 * π * (2 * q - φ)) - 96000 / 7669 * cos (2 * π * (3 * q - 2 * φ))) ^ 2

def magField (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (deriv magH0 x.2.1, -deriv (fun s => magV s x.2.2) x.1, 1)

theorem magnetic_barrier :
    ∃ P : ℝ → ℝ → ℝ,
      AnalyticOnNhd ℝ (fun x : ℝ × ℝ => P x.1 x.2) Set.univ ∧
      (∀ q φ, P (q + 1) φ = P q φ) ∧ (∀ q φ, P q (φ + 1) = P q φ) ∧
      (∀ q φ, 8 / 25 ≤ P q φ ∧ P q φ ≤ 39 / 100) ∧
      ∀ x₀ : ℝ × ℝ × ℝ, ∃ z : ℝ → ℝ × ℝ × ℝ,
        z 0 = x₀ ∧ (∀ t, HasDerivAt z (magField (z t)) t) ∧
        (∀ (I : Set ℝ) (y : ℝ → ℝ × ℝ × ℝ), I.OrdConnected → (0 : ℝ) ∈ I → y 0 = x₀ →
          (∀ t ∈ I, HasDerivAt y (magField (y t)) t) → ∀ t ∈ I, y t = z t) ∧
        ∀ t : ℝ,
          (x₀.2.1 < P x₀.1 x₀.2.2 → (z t).2.1 < P (z t).1 (z t).2.2) ∧
          (x₀.2.1 = P x₀.1 x₀.2.2 → (z t).2.1 = P (z t).1 (z t).2.2) ∧
          (P x₀.1 x₀.2.2 < x₀.2.1 → P (z t).1 (z t).2.2 < (z t).2.1)
```

**Elaboration.** All five declarations were concatenated into one scratch file with only Mathlib imports and run
under `lake env lean` on main's toolchain, in an 8 GB scope. It elaborated with no errors. The only warning is the
expected `sorry`, and `#print axioms` lists `[propext, sorryAx, Classical.choice, Quot.sound]`. The per-file module
chain was not built: no frozen files are created before approval.

**Exact checks.**
- The factored control term reproduces the plan's ε = 3/1000 cosine table exactly (`(0,0)`
  6586872735384/11338856098924225, …).
- At ε = 3/2500 the table is that one scaled by 4/25: `(0,0)` 26347490941536/283471402473105625, `(4,−2)`
  205488/4819830625, `(6,−4)` 1849392/36758475625, `(1,−1)` = `(5,−3)` −1232928/13310508125.
- h′(7/20) = 18777/32000 and h″(7/20) = −1427/1600.

## Decisions for the owner

1. **Model:** the general-(8) quadratic control (plan §1.1, §8 IDEA-CH-1) at ε = 3/2500, with the constant term
   kept and energy zero. The literal `1427/3200` is −h″(7/20)/2.
2. **Flux bounds:** 8/25 ≤ P ≤ 39/100, which leaves about 0.008 of room around the measured [0.3280, 0.3857] for
   the graph-transfer losses. The window p₀ < 8/25 and p₀ > 39/100 follows as a corollary and is not stated.
3. **Scope:** all real lifts and the global polynomial extension of h (plan §8 deviation). The time variable is the
   toroidal angle in turns.
4. **State type:** `ℝ × ℝ × ℝ`, following the sealed lunar band. The plan wrote `Fin 3 → ℝ`, and AGENTS rule 7
   lists `Fin n → ℝ`. Choosing the lunar form lets the generic SO graph and barrier glue be reused unchanged; the
   alternative is a `Fin 3 → ℝ` restatement.
5. **Omitted from the public statement:** the torus, its frequency (α, 1) with α = (7913 − √5)/13618, and the strip
   width `complexStrip 2 (3/1000000)`. Plan §2.3 calls these "the stronger torus statement". They would be added as
   a conjunct (rotation on the graph with frequency α) only if the owner wants them. The certificate still uses
   them internally.
6. **Uniqueness form:** local solutions on any order-connected I ∋ 0 with two-sided `HasDerivAt`. This is
   `KAM.ODE.IsSolutionIn F univ I y` unfolded (`isSolutionIn_univ_iff`), so the frozen file needs no non-frozen
   import.

## Cost of phase 2b (after approval)

- Certificate emission and kernel check: 30–130 CPU-h, about 2–8 calendar days on the serial slot. The support is
  about 1.7–2.3k keys at CertFixed 160–192.
- Bespoke Lean work, about 2–3k lines: ClockGraph (inverse, FromTorus, Barrier), magnetic Global ODE, HamExpr and
  the expansion identity, and the Frequency module (continued-fraction port).
