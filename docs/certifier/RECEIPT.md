# Receipt of a certified application

A receipt is the public record of what one application of the certifier proves about one physical system.
It is short, every line can be checked against the repository at the stated commit, and it ends with what
is **not** proved. Write one receipt per application: one theorem, or one family of theorems sharing a
model, a chart and a certificate format. Keep the section order below.

The Lean object behind each field is listed in the
[application contract](../campaign/design/APPLICATION-CONTRACT.md) (`KAM/Application/`). The
[quickstart](QUICKSTART.md) produces the [worked example](#example-the-quickstart-toy-quick) at the end of
this page.

## Template

### 0. Identification

| Field | Value |
|---|---|
| Application | name; one line on the physical system and what is certified |
| Repository | URL; commit (full SHA); tag or branch |
| Toolchain | `lean-toolchain` (e.g. `leanprover/lean4:v4.35.0`); Mathlib revision (from `lake-manifest.json`) |
| Library | the core `KAM`, or the opt-in application library that owns the modules (`scripts/build_roots.json`) |
| Producer | commit of the producer tools; `scripts/requirements.txt` (pinned versions and sha256); spec or input files |
| Date | when the kernel run of section 7 was made |

### 1. Model

* The physical system: its equations, every parameter value with source and units, and the normalization.
* The certified Hamiltonian, quoted verbatim from the data module (`<Ns>.ham : HamExpr n`, `file:line`)
  and written out in mathematical notation. The theorem is about this exact expression (`c.H = c.ham.eval`).
* How the certified model relates to the physical one. Either the certified model *is* the model, or a
  named theorem relates them (e.g. `IsRealModelTorus.congr` with a closed-form expression,
  `CertifiedTorusAt.physical`). Without such a theorem, say so.
* Every idealization: truncated series, dropped terms, rounded constants. A truncated model is a different
  exact model; its distance from the physical model is not part of the theorem unless separately proved.

### 2. Chart and normalization

* Coordinates of the certified model: angles `θ ∈ ℝⁿ/ℤⁿ`, actions `I ∈ ℝⁿ`. For a forced system, which
  angle is time and which action is conjugate to it.
* The chart `Ψ` to physical coordinates, its open domain `O`, the transport identity
  (`IsFieldTransport Ψ Hc F κ O`, theorem name) and the clock `κ`, or "model coordinates are physical".
* The certificate's complex domain `c.D` (centre, radius, strip width `ρ_H`) and the energy level `E₀`,
  in model and physical units.

### 3. Frequency

* The reference vector `ω*` in closed form, the box `cert.freqBox`, and the enclosure theorem
  (`FreqEncloses n cert.freqBox ω*`).
* The Diophantine constants `(γ, τ)` of `ω*` and the theorem that proves them (`IsDiophantine γ τ ω*`).
* The certified torus frequency is `s∞ ω*` with `|s∞ - s| ‖ω*‖ ≤ disp`
  (`CertifiedTorusAt.abs_sub_mul_norm_le`). Give `s` and `disp`, and the physical frequency (`κ⁻¹ s∞ ω*`
  through the chart).

### 4. Certificate and route

* The certificate (`<Ns>.cert : TorusCertificate n (CertFixed P)`), its data modules and its size
  (Fourier support, genuine product pairs).
* The route of `routeV2All` (`sharp`, `A.frozen`, `A.refined`, `A.refined` with lever L8′, `B.frozen`,
  `B.refined`, …) and the Lean name of its witness.
* The numbers: `err`, the route's threshold `e*` from the exact mirror, the margin `log10(e*/err)`, `disp`,
  `ρ`, `ρ∞`. These are producer numbers. The kernel re-decides the test; it does not use the margin.
* How the route was chosen: the `route_select.py` profile, the command, and the chosen row (route, truncation
  `L`, precision `P`, margin, err source: measured, interpolated or extrapolated).

### 5. The exact theorem

* Fully qualified name and its `#check` output, verbatim.
* What the conclusion says. `CertifiedTorus c ω*` unfolds (`certifiedTorus_iff`, `Iff.rfl`) to: there are
  `K∞` and `s∞` with `1 < s∞ < σω`; `K∞` holomorphic, primary and real on the strip `T_{ρ∞}`; the invariance
  error of `K∞` at frequency `s∞ ω*` is zero; `H ∘ K∞ = E₀`; `K∞` stays `μ/2` inside the domain with
  `‖DK∞‖ ≤ σK − μ/2`; `‖K∞ − K‖ ≤ disp` on the strip; and `‖s∞ ω* − s ω*‖ ≤ disp`.
* The physical theorems attached to the same torus, by name: real model torus
  (`CertifiedTorusAt.isRealModelTorus`), its location next to the certificate's real torus
  (`CertifiedTorusAt.norm_realRestriction_sub_le`: `‖k θ − Re K(ιθ)‖ ≤ disp`), flow torus and invariance
  (`IsPhysicalFlowTorus`, `isInvariantSet`), graph over the angles, and observable bounds.

### 6. Axioms and guards

* `#print axioms <name>`, verbatim. Exactly `[propext, Classical.choice, Quot.sound]` is required; anything
  else (in particular `sorryAx`) disqualifies the receipt.
* `scripts/lint_sources.sh` at the commit: no `sorry`, `axiom`, `native_decide`, `ofReduceBool`,
  `implemented_by`, resource overrides, or non-local metaprogramming.
* Optional, stronger: the kernel replay `scripts/kernel_replay.sh [--lib <Lib>]`, which re-checks every
  constant with `leanchecker`.

### 7. Kernel-run ledger

| module | wall (s) | CPU (s) | max RSS (GB) |
|---|---:|---:|---:|
| one row per module of the certificate and its route | | | |
| **total** | | | |

State the machine (CPU, cores, memory), the command (`nice -n 5 lake build <modules>`, or the capped driver
`scripts/prebuild_heavy.py --lib <Lib>` for an application library), and what was already built (for
example "core library from the commit's build; certificate modules from scratch").

### 8. What this does not prove

Always state these, then the application's own limits:

1. **Only the stated model.** Nothing about the physical system beyond the exact certified Hamiltonian and
   its parameters, unless a theorem named in section 1 relates them. Modelling error, neglected terms,
   measurement uncertainty and units are outside the theorem.
2. **One torus.** One invariant torus, of frequency `s∞ ω*`, on the level `E₀`. It says nothing about other
   frequencies, about a positive-measure family, or about other energies.
3. **No statement off the torus.** Solutions that do not meet the torus are not controlled (no stability,
   confinement or Nekhoroshev bound) unless a separate theorem says so. Invariance covers solutions that
   start on the torus, while the field is `C¹` near it.
4. **The numerical torus is not the torus.** `K` is the certificate's data; the theorem places the exact
   torus `K∞` within `disp` of it on the strip, and `s∞` within `disp/‖ω*‖` of `s`.
5. **Producer numbers are not part of the theorem.** Route-selection costs, mirror thresholds, margins and
   error predictions are untrusted tooling. Only the kernel-checked statement and its axioms count.
6. Exact rational parameters. If a constant is a measured value, the theorem holds for the rational
   number written in the certificate, exactly.

---

## Example: the quickstart toy `Quick`

This is a toy, so sections 1 and 2 are short: the certified model is the model. The modules are not
checked in. Anyone can regenerate them with the commands of [QUICKSTART.md](QUICKSTART.md), and the
checked-in analogue is `Micro` (`MicroRoutes.lean`, `MicroReading.lean`).

### 0. Identification

| Field | Value |
|---|---|
| Application | forced-pendulum toy `Quick`: an invariant torus of a periodically forced pendulum with two interacting modes |
| Repository | KAM-dev (github.com/scottnarmstrong/KAM-dev), branch `v2-public`; certificate producer at `39110bc34d8387113a9b4450ff19e08407f111ee` (its output is unchanged up to the commit of this page) |
| Toolchain | `leanprover/lean4:v4.35.0`; Mathlib `v4.35.0` (`56a005855ea17e0b0958f73ec801ae140b0a1679`) |
| Library | core `KAM` (modules `KAM.CertificateSharp.V2.Tests.Forced.Quick*`, generated locally, not in the root) |
| Producer | `scripts/requirements.txt` (numpy 2.5.3, mpmath 1.3.0; Python 3.13.13); spec `docs/certifier/examples/quick.json` |
| Date | 1 November 2026 |

### 1. Model

* Certified Hamiltonian (`QuickData.lean`, lines 35–38):
  `(.mul (.const (1)) (.add (.action 1) (.add (.mul (.const (1 / 2)) (.pow (.action 0) 2)) (.add
  (.mul (.const (3 / 1000000000000)) (.cosMode [1, 0])) (.add (.mul (.const (1 / 1000000000000))
  (.cosMode [1, 1])) (.const (0)))))))`. That is,
  `H = J + p²/2 + 3·10⁻¹² cos 2πθ₀ + 10⁻¹² cos 2π(θ₀ + θ₁)`.
* Equations: `θ₁' = 1`, `θ₀'' = 2π [3·10⁻¹² sin 2πθ₀ + 10⁻¹² sin 2π(θ₀ + t)]`.
* The certified model is the model. There are no idealizations: it is a toy with exact coefficients.

### 2. Chart and normalization

* Model coordinates `θ = (θ₀, θ₁)` (`θ₁` the time, period 1), `I = (p, J)` (`J` conjugate to the time).
  No chart (`Ψ = id`); the time scale is `c = 1`.
* Domain `c.D` (`certDomain`): angles in the complex strip of width `ρ_H = 137/1000`, actions with
  `|I_i − centre_i| < 11/1000` about `(p, J) ≈ (−0.0942, −0.00443)`. Level `E₀ = 0`.

### 3. Frequency

* `ω* = κ (ν₋(10) − 1, 1)`, `κ = 10⁶/(10⁶ + 1)`, `ν₋(10) − 1 = (−19 + √5)/178 ≈ −0.0941794`. The box
  `cert.freqBox` has radius `1/(356000356·10³⁹) ≈ 2.8·10⁻⁴⁸` in the first coordinate and is exact in
  the second. `Quick.freq : FreqEncloses 2 cert.freqBox ωstar` (a root enclosure of `√5` and
  `checkAlgBox`).
* `Quick.dio : IsDiophantine (κ/12) 1 ωstar` (from `lunarRotFreqMinusN_isDiophantine 10`).
* `s = 1 + 10⁻⁶` (so `s ω* = (ν₋(10) − 1, 1)`), `disp = 10⁻³`: the torus frequency `s∞ ω*` satisfies
  `|s∞ − s| ‖ω*‖ ≤ 10⁻³`.

### 4. Certificate and route

* `Quick.cert : TorusCertificate 2 (CertFixed 96)`; truncation `L = 15` (`prune_digits`), Fourier
  support: `u` 4, `p` 5 and `J` 3 terms; 1308 genuine product pairs.
* Route: `sharp` (`routeV2All` at `Sum.inl ()`, the landed certifier). The same module also proves the
  frozen routes: `frozenWit` (route A, `X* = 271/5000`) and `frozenBWit` (route B, `X* = 137/5000000`).
* `err = 233/10²¹ = 2.33·10⁻¹⁹`. Thresholds (exact mirrors): sharp `2.51·10⁻¹⁸` (margin 1.03 decades),
  frozen A `4.73·10⁻¹³` (6.31), frozen B `4.09·10⁻¹³` (6.24). `ρ = 1/8`, `ρ∞ = 1/800`.
* Chosen by `python3 -I scripts/certifier/route_select.py forced_quick --beta 1`, row
  `baseline fallback`: sharp, `L = 15`, `P = 96`, margin 1.03, err measured. The `--frozen` emitter
  needs the sharp route; see QUICKSTART step 3.

### 5. The exact theorem

* `KAM.CertificateSharp.V2.Forced.Quick.sharp_torus : CertifiedTorus Quick.cert Quick.ωstar`
  (`QuickRoutes.lean`, line 38). Also `Quick.frozenA_torus` and `Quick.frozenB_torus`, with the same
  statement.
* Unfolded as in section 5 of the template, with `σω = 2`, `ρ∞ = 1/800`, `μ = 1/100`, `σK = 103/100`.
* The real reading `Quick.real_torus` (QUICKSTART step 6, the pattern of the checked-in
  `Micro.real_torus`) gives an analytic real torus `k` of `realHam cert.H` on `H = 0`, whose lines solve
  Hamilton's equations. It lies within `10⁻³` of the certificate's real torus at every real angle
  (`‖k θ − realRestriction cert.K θ‖ ≤ disp`). Its frequency `s∞ ω*` has `1 < s∞ < 2` and
  `|s∞ − s| ‖ω*‖ ≤ 10⁻³`, and is `(s∞ κ/12, 1)`-Diophantine.

### 6. Axioms and guards

```
'KAM.CertificateSharp.V2.Forced.Quick.sharp_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.V2.Forced.Quick.frozenA_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.V2.Forced.Quick.frozenB_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
'Quick.real_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every check is a `decide +kernel`; the generated modules contain no `native_decide` or `#eval`.

### 7. Kernel-run ledger

| module | wall (s) |
|---|---:|
| `QuickData` | 2.8 |
| `QuickFreq` | 1.7 |
| `QuickStages` | 2.5 |
| `QuickChecks` | 8.9 |
| `QuickBase` | 9.7 |
| `QuickRoutes` | 2.0 |
| **total** (`lake build …QuickRoutes`: 27.1 s wall, 25.2 s user CPU) | 27.6 |

AMD Ryzen 7 7700 (8 cores, 16 threads), 124 GB; at most 2.0 GB per process. The checker's closure was
already built (QUICKSTART step 0); only the six certificate modules were compiled.

### 8. What this does not prove

Items 1–6 of the template apply. In particular, for this toy:

* It proves nothing about any physical pendulum. The coefficients `3·10⁻¹²` and `10⁻¹²` are exact
  rationals chosen to make the example small.
* It covers one torus, of rotation number `ν₋(10) − 1` per forcing period. That `s∞ = s` exactly follows
  from `θ₁' = 1`, a one-line argument that is not formalized.
* Solutions off the torus are not controlled. The graph property, invariance of the image and observable
  bounds (`KAM/Application/`) are not instantiated here.
