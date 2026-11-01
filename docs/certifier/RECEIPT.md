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
  (`CertifiedTorusAt.isRealModelTorus`), flow torus and invariance (`IsPhysicalFlowTorus`,
  `isInvariantSet`), graph over the angles, and observable bounds.

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

<!-- filled from the quickstart run; see QUICKSTART.md for the commands -->
