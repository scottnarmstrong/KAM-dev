# Track R (Rüssmann's KAM theorem as a headline) — statement draft 0.1

30 October 2026, brief RUSSMANN-W. **Proposed, not approved, frozen or proved.** The exact Lean text
below is the content of `.drafts/russmann/RussmannCover.lean` (sha256
`8a2aa0f18cc0b1c0fbefbb18bbf0d03137fe16bb2b616617d3b3ef5b19d304e7`) and
`.drafts/russmann/RussmannKam.lean` (sha256
`8c2b60409035acec3939cebdcfea80bfb508f8f16dd5d16bf6991828ba026d3a`). Both elaborate against the
current frozen definitions (`lake env lean`, combined check file; the only message is the expected
`declaration uses 'sorry'` on the theorem). Elaboration is not a truth or approval certificate: the
orchestrator's independent statement audit and the owner's line-by-line approval come next.

## 1. The mathematical statement

**Theorem (R-HEAD).** Let `n ≥ 1`, `s₀, r₀ > 0`, and let `B ⊂ ℝⁿ` be a bounded, connected, open set.
Let `h` be holomorphic on the complex `r₀`-neighbourhood of `B` (max norm) and real on its real
points, with frequency map `ω = ∇h`. Assume **Rüssmann's (weak) non-degeneracy condition**: the
image of `ω` on `B` is not contained in any hyperplane through the origin, i.e.

  for every `c ∈ ℝⁿ ∖ {0}` there is `I ∈ B` with `c · ω(I) ≠ 0`.

Then there is an exponent `τ > n − 1` (depending on `h`, `B`, `r₀`) with the following property. For
every `δ > 0` there is `ε₀ > 0` such that for every perturbation `f(θ, I)`, holomorphic on
`T_{s₀} × (B + r₀)`, `1`-periodic in `θ`, real on real points, with `sup |f| ≤ ε ≤ ε₀`, the set of
points of `Tⁿ × B` lying on invariant Lagrangian tori of `H = h + f` that

- carry a linear flow with a `(γ, τ)`-Diophantine frequency (some `γ > 0`),
- stay, in the actions, within `r₀` of `B`,
- lie within `δ` (max norm) of an unperturbed torus `θ ↦ (θ, I₀)`, `I₀ ∈ B`,

has Lebesgue measure at least `4⁻ⁿ · meas(Tⁿ × B)` (in the coordinates `[0,1)ⁿ × B`).

The frequency of a torus near `θ ↦ (θ, I₀)` is in general **not** `ω(I₀)`: under weak
non-degeneracy the frequencies shift (Rus01 Thm 1.7 produces `ω*(b)`, not `ω(b)`). This is why the
track-K cover `KAM.kamCover`, which requires `frequencyMap h I₀ = ω`, cannot be reused, and a new
cover `russmannCover` (= `kamCover` without that one clause) is proposed.

### Sources

- **Rus01** (pinned; H. Rüssmann, *Invariant tori in non-degenerate nearly integrable Hamiltonian
  systems*, RCD 6(2) (2001) 119–204):
  - Theorem 1.7, printed **p. 126** (proof remarks p. 127, final proof §15.6 p. 177), maximal case
    `p = q = 0` (no elliptic or hyperbolic normal directions). For `p = 0` weak and extreme
    non-degeneracy both reduce to the non-degeneracy of `ω` (§1.2, p. 124): `⟨c, ω⟩ ≢ 0` on the open,
    nonempty, connected action domain `Y` for every `c ≠ 0` (§1.1, pp. 123–124).
  - The non-degeneracy lemma (finite order and positive amount on compacts): Lemma 18.2 and §18.3.1,
    pp. 185–186; the measure estimate of the surviving parameters: §17 (pp. 180–183) and Thm 18.5
    (p. 189).
- **Track P's internal theorem** (not frozen): `KAM.Planetary.weak_kam_quantitative`
  (`KAM/Planetary/Quantitative/Assembly.lean:203`), blueprint `blueprint-P/parts/p11a5-*.tex`,
  Theorem `bpP:p11a:weak-kam-quantitative`, which re-proves the maximal case of Rus01 Thm 1.7 with
  power-law divisors, an explicit displacement and a bi-Lipschitz family of tori (CP09 Thm 3 shape).
  The proof route of R-HEAD goes entirely through it ([PROOF-ROUTE.md](PROOF-ROUTE.md)).

### Deviations from the printed source (to be recorded in the ledger)

- **D-R1 (output in phase space).** Rus01 Thm 1.7 bounds the *parameter* measure
  (`meas H ≥ meas K − ε*`) and gives a *continuous* family of conjugacies. R-HEAD bounds the
  *phase-space* volume of the union of tori, via track P's bi-Lipschitz family (inverse Lipschitz
  constant `(1 − 2⁻¹⁰)⁻¹`, `QuantitativeFamily.lower`). The constant `4⁻ⁿ` is what that interface
  gives cleanly; the classical "complement of measure `≤ κ`" form needs a track-P extension
  (owner question 1).
- **D-R2 (power-law divisors).** Rus01 uses an approximation function `Φ` decaying faster than every
  power (§1.4, p. 125); a power law violates its hypotheses. R-HEAD's frequencies satisfy the
  ordinary `(γ, τ)` Diophantine condition `KAM.IsDiophantine`, with `τ > nμ − 1` for the order `μ`
  of non-degeneracy (Rus01 §18.5 with `p = q = 0`; CP09 Thm 3; blueprint P deviation list D-1…D-22).
- **D-R3 (domains and conventions).** Period-one angles, max norms, and a *uniform* complex
  neighbourhood `complexStrip n s₀ ×ˢ actionNbhd B r₀`, exactly as in track K's frozen headlines.
  Rus01 allows an arbitrary complex open set containing `Tⁿ × K`; the uniform neighbourhood is the
  frozen track-K encoding.
- **D-R4 (maximal case only).** Lower-dimensional elliptic/hyperbolic tori (`p, q > 0`) are not
  claimed.
- **D-R5 (explicit closeness).** Rus01 Thm 1.7 has no displacement bound; R-HEAD states closeness
  `≤ δ` to the unperturbed tori, an output of track P's displacement clause.

No new source erratum is suspected at this stage (E-CP09-8, the p. 126/127 locator, is already in the
ledger).

## 2. Exact Lean text

### 2a. New definition: `KAM.Russmann.russmannCover`

Intended frozen file `KAM/Frozen/Russmann/Defs/RussmannCover.lean`.

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Complex.Basic
public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Frozen.Defs.IsInvariantLagrangianTorus
public import KAM.Frozen.Defs.RealHamiltonian

/-!
# Frozen definition `KAM.Russmann.russmannCover`

DRAFT v0.1 (not approved). Source: Rus01 Thm 1.7, p. 126 (the invariant tori with Diophantine
frequencies `ω*(b)`, `b ∈ H`); ruling Q3 for the content of "invariant torus". This is
`KAM.kamCover` without the clause `frequencyMap h I₀ = ω`: under Rüssmann's weak non-degeneracy
the frequency of the torus near `θ ↦ (θ, I₀)` is shifted, so it is not tied to `∇h(I₀)`.
-/

@[expose] public noncomputable section

namespace KAM.Russmann

open KAM

/-- The points lying on the KAM tori of Rüssmann's theorem for `H = h + f`: invariant Lagrangian
tori (`IsInvariantLagrangianTorus`) with some `(γ, τ)`-Diophantine frequency `ω`, whose actions
stay within `r₀` of `B`, and which lie within `δ` of an unperturbed torus `θ ↦ (θ, I₀)` with
`I₀ ∈ B`. Unlike `KAM.kamCover`, the frequency `ω` is not required to equal `∇h(I₀)`. -/
def russmannCover {n : ℕ} (h : (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (B : Set (Fin n → ℝ)) (r₀ τ δ : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {z | ∃ (K : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) (ω : Fin n → ℝ) (γ : ℝ) (I₀ : Fin n → ℝ),
    0 < γ ∧ IsDiophantine γ τ ω ∧ IsInvariantLagrangianTorus (realHamiltonian h f) ω K ∧
    (∀ θ, ∃ J ∈ B, ‖(K θ).2 - J‖ < r₀) ∧
    I₀ ∈ B ∧ (∀ θ, ‖K θ - (θ, I₀)‖ ≤ δ) ∧ z ∈ Set.range K}

end KAM.Russmann

end
```

Line-by-line comparison with the frozen `KAM.kamCover` (`KAM/Frozen/Defs/KamCover.lean`): same
binders, same carriers, same clauses in the same order, except that `frequencyMap h I₀ = ω` is
deleted (and the import of `KAM.Frozen.Defs.FrequencyMap` with it). Every other definition used is
frozen and reused verbatim: `IsDiophantine`, `IsInvariantLagrangianTorus`, `realHamiltonian`.

### 2b. The headline theorem: `KAM.Russmann.russmann_kam`

Intended frozen anchor `KAM/Frozen/Russmann/Theorems/RussmannKam.lean` (`DRAFT_SORRY` until sealed by
`by exact KAM.Provider.Russmann.russmann_kam hn hs₀ hr₀ hB_open hB_conn hB_bdd hh hh_real
h_russmann`).

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Defs.FundamentalDomain
public import KAM.Frozen.Russmann.Defs.RussmannCover

/-!
# Frozen theorem `KAM.Russmann.russmann_kam`

DRAFT v0.1 (not approved). Rüssmann's KAM theorem under weak non-degeneracy (Rus01 Thm 1.7,
p. 126, maximal case `p = q = 0`), in the hypothesis style of `KAM.kam_positive_measure_qualitative`.
Only the proof body between the markers may change, and only to
`by exact KAM.Provider.Russmann.russmann_kam …` when the provider is complete (sealing).
-/

@[expose] public section

open MeasureTheory

namespace KAM.Russmann

open KAM

/-- **R-HEAD.** Rüssmann's KAM theorem (Rus01 Thm 1.7, maximal case). Let `h` be real-analytic on
a complex neighbourhood of a bounded connected open set `B ⊆ ℝⁿ` whose frequency map `ω = ∇h` is
not contained in any hyperplane through the origin: `c · ω ≢ 0` on `B` for every `c ≠ 0`. Then
there is a Diophantine exponent `τ > n - 1` such that, for every closeness `δ > 0` and every
sufficiently small real-analytic perturbation `f`, the invariant Lagrangian tori of `H = h + f` with
`(γ, τ)`-Diophantine frequencies lying within `δ` of the unperturbed tori fill at least the fraction
`4⁻ⁿ` of the phase-space volume of `Tⁿ × B`. -/
theorem russmann_kam {n : ℕ} (hn : 1 ≤ n) {s₀ r₀ : ℝ} (hs₀ : 0 < s₀) (hr₀ : 0 < r₀)
    {B : Set (Fin n → ℝ)} (hB_open : IsOpen B) (hB_conn : IsConnected B)
    (hB_bdd : Bornology.IsBounded B)
    {h : (Fin n → ℂ) → ℂ} (hh : DifferentiableOn ℂ h (actionNbhd B r₀))
    (hh_real : ∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ actionNbhd B r₀ →
      (h fun i => (I i : ℂ)).im = 0)
    (h_russmann : ∀ c : Fin n → ℝ, c ≠ 0 → ∃ I ∈ B, ∑ i, c i * frequencyMap h I i ≠ 0) :
    ∃ τ : ℝ, (n : ℝ) - 1 < τ ∧ ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ε : ℝ),
        DifferentiableOn ℂ f (complexStrip n s₀ ×ˢ actionNbhd B r₀) →
        (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ∀ k : Fin n → ℤ,
          f (z.1 + (fun i => (k i : ℂ)), z.2) = f z) →
        (∀ θ I : Fin n → ℝ,
          ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀ →
          (f ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) →
        (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ‖f z‖ ≤ ε) → ε ≤ ε₀ →
        ENNReal.ofReal ((1 / 4 : ℝ) ^ n) * volume (fundamentalDomain B) ≤
          volume (fundamentalDomain B ∩ russmannCover h f B r₀ τ δ) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.Russmann

end
-- FROZEN_ANCHOR_SUFFIX_END
```

### 2c. Comparison with the frozen HEAD-Q (`KAM.kam_positive_measure_qualitative`)

| Item | HEAD-Q (track K, frozen) | R-HEAD (this draft) |
|---|---|---|
| dimension | `2 ≤ n` | `1 ≤ n` (question 3) |
| `τ` | binder, `n − 1 < τ` | `∃ τ, n − 1 < τ` in the conclusion (question 2) |
| `s₀, r₀`, `B` open, bounded | same | same, plus `IsConnected B` (question 5) |
| `h` holomorphic, real | same text | same text |
| non-degeneracy | Kolmogorov: `∇h` bi-Lipschitz on `closure B` | Rüssmann: `∀ c ≠ 0, ∃ I ∈ B, c · ∇h(I) ≠ 0` |
| `f` hypotheses (holomorphy, periodicity, realness, `‖f‖ ≤ ε ≤ ε₀`) | same text | same text |
| quantifiers | `∀ κ > 0, ∃ ε₀ > 0, ∀ f ε` | `∃ τ, ∀ δ > 0, ∃ ε₀ > 0, ∀ f ε` |
| cover | `kamCover h f B r₀ τ κ` (frequency `= ∇h(I₀)`) | `russmannCover h f B r₀ τ δ` (frequency free) |
| conclusion | `meas(FD ∖ cover) ≤ κ · meas FD` | `4⁻ⁿ · meas FD ≤ meas(FD ∩ cover)` |

`FD = fundamentalDomain B = [0,1)ⁿ × B`. The perturbation hypotheses are copied verbatim, so a caller
that holds HEAD-Q's hypotheses on `f` holds R-HEAD's.

### 2d. Why the volume is taken inside the fundamental domain

`russmannCover` (like `kamCover`) is invariant under the angle translations `(θ, I) ↦ (θ + k, I)`,
`k ∈ ℤⁿ`, because each torus satisfies `K(θ + k) = K(θ) + (k, 0)`. A translation-invariant set has
volume `0` or `∞`, so a bound `c · meas FD ≤ meas(cover)` (one of the candidate forms in the brief)
would hold as soon as the cover had positive measure and would say nothing about the constant. The
draft therefore measures `fundamentalDomain B ∩ cover`, the part of the tori lying over `[0,1)ⁿ × B`,
exactly the set HEAD-Q measures (through its complement).

### 2e. What the hypotheses do not contain

No hypothesis mentions a torus, a frequency of a torus, a Diophantine property, a measure of
good parameters, an index or amount of non-degeneracy, or any constant of track P. The compact
parameter set `K ⊂ B`, its thickness `ϑ`, the strip `s`, the order `μ`, the amount `β`, the bounds
`M, M₀, C₁` and the measure loss `ε*` of track P are all chosen inside the proof from
`(n, s₀, r₀, B, h)` (and `δ` for `ε₀`) — see [PROOF-ROUTE.md](PROOF-ROUTE.md).

## 3. Owner questions (with recommendations)

1. **Form of the measure conclusion.**
   - (a) *Recommended:* `ENNReal.ofReal ((1/4)^n) * volume (fundamentalDomain B) ≤
     volume (fundamentalDomain B ∩ russmannCover h f B r₀ τ δ)`. Proof: track P's lower bi-Lipschitz
     bound gives `meas ≥ (1 − 2⁻¹⁰)²ⁿ · meas(good)`, via the existing Hausdorff-measure lemma
     `KAM.lip_image_prod`; since `(1 − 2⁻¹⁰)²ⁿ > 4⁻ⁿ`, a compact `K ⊂ B` of almost full measure gives
     the clean constant.
   - (b) Qualitative: `0 < volume (fundamentalDomain B ∩ russmannCover …)`. Weaker. Its proof is
     the same.
   - (c) `(1/8)^n` instead of `(1/4)^n`: uses only `QuantitativeFamily.cell_lower` (`2⁻²ⁿ`). Slightly
     cheaper, but the constant is uglier.
   - (d) The classical form `meas(FD ∖ cover) ≤ κ · meas FD` for every `κ > 0`, as in HEAD-Q. It is
     **not reachable** from track P's current interface: its bi-Lipschitz constants are fixed at
     `1 ± 2⁻¹⁰` and do not tend to 1 as `ε → 0`. It would need an extension of track P
     (`evaluation-bilipschitz` with `λ* → 0`). This could be a later gate.
2. **The Diophantine exponent `τ`.** `QuantitativeData.Valid` needs `τ > nμ − 1`, where `μ` is the
   order of non-degeneracy of `ω` on the chosen compact set. `μ` is not a datum of the theorem, so
   `τ` cannot be a binder with only `τ > n − 1`.
   - *Recommended:* `∃ τ, n − 1 < τ ∧ ∀ δ > 0, ∃ ε₀ > 0, …`, with `τ` chosen after `(h, B, r₀)`
     and before `δ` and `f`. This is faithful: `ω` is analytic on the connected real
     `r₀`-neighbourhood of `B`, which contains the compact `closure B`, so one finite order `μ`
     works for every compact `K ⊂ B` (Rus01 Lemma 18.2), and `τ = nμ` serves all `δ` and all `f`.
     Because `(γ, τ)`-Diophantine implies `(γ, τ′)`-Diophantine for `τ′ ≥ τ`, the cover grows with
     `τ`, so "for every `τ′ ≥ τ`" follows for free.
   - Alternatives: (i) `τ` a binder, with a hypothesis `τ > n·μ₀(h, B) − 1`. This needs a frozen
     definition of Rüssmann's index `μ₀`, which is more frozen surface and an `sInf`-type body.
     (ii) `∃ τ` inside the cover. This is weaker, since `τ` could then depend on `f`.
3. **Dimension.** *Recommended:* `1 ≤ n`. It costs nothing: track P's theorem holds for `N ≥ 1`, and
   for `n = 1` Rüssmann's condition reads `ω ≢ 0`. Alternative: `2 ≤ n`, as in track K (ruling Q5).
4. **The cover.**
   - *Recommended:* the new definition `russmannCover` = `kamCover` minus the clause
     `frequencyMap h I₀ = ω`.
   - Option: add `‖ω − frequencyMap h I₀‖ ≤ δ` (the frequency stays close to the unperturbed one).
     Rus01 Thm 1.7 does not state it. It is true and derivable, by averaging the angle equation along
     the torus with a Cauchy bound on `∂_I f`, but that costs a separate argument. *Recommended:* omit
     it in v0.1; it can be added as a separate theorem later.
5. **Connectedness of `B`.** *Recommended:* `IsConnected B` (Rus01 §1.1: `Y` open, nonempty,
   connected). It is needed. If `B = B₁ ⊔ B₂` and `ω(Bᵢ)` lies in a line `Lᵢ` with `L₁ ≠ L₂`, the
   condition holds on `B` but fails on each component, where KAM tori need not exist.
6. **Encoding of Rüssmann's condition.** *Recommended:* inline, on the real domain `B`:
   `∀ c : Fin n → ℝ, c ≠ 0 → ∃ I ∈ B, ∑ i, c i * frequencyMap h I i ≠ 0`. This is Rus01 §1.2 verbatim
   ("⟨c, ω⟩ is not identically zero on Y"), and it is the existing track-P interface `rnd_def` /
   `p11RNondegenerate`. Alternative: a frozen definition `IsRussmannNondegenerate`, which adds frozen
   surface for no gain.
7. **Closeness quantifier.** *Recommended:* `∀ δ > 0, ∃ ε₀ > 0`, so the tori are as close to the
   unperturbed ones as desired. The `4⁻ⁿ` bound is uniform in `δ`. HEAD-Q uses the same number `κ`
   for closeness and measure; here the measure fraction is fixed, so a separate `δ` is needed.
8. **Names and files.** *Recommended:* `KAM.Russmann.russmann_kam` in
   `KAM/Frozen/Russmann/Theorems/RussmannKam.lean`; `KAM.Russmann.russmannCover` in
   `KAM/Frozen/Russmann/Defs/RussmannCover.lean`; provider `KAM.Provider.Russmann.russmann_kam` in
   `KAM/Provider/Russmann/RussmannKam.lean`.
