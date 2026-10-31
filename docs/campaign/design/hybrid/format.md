# Hybrid certificate data: format v2 (producer C8d ↔ checker C8c)

Owner: SHARP2-C8D, revised by SHARP2-C8DFIX (this file). The consumer is the Lean hybrid checker `checkHybrid`
(`KAM/CertificateSharp/Hybrid/`, package C8c, landed). This file fixes the data the producer
`scripts/apost_sharp/hybrid_producer.py` writes, the meaning of every field, and the checks of `checkHybrid`.
`scripts/apost_sharp/hybrid_mirror.py` ports those checks one for one in exact rationals, except the ones listed as
kernel-only in §5. `scripts/apost_sharp/hybrid_xlang.py` compares the mirror with the Lean definitions (§8). Theory:
design note `docs/campaign/design/APOST-SHARP-V2-HYBRID.md` §§2–3; blueprint `p2s2-hybrid-cert` (labels `bp:p2s2hc:*`,
`bpI:p2s2hc:*`).

**Changes from v1** (AUDIT-C8C-1 F1, F2, and the Cauchy check):
- weights: `w ≥ ratExpUp (2·piUpQ·ρ) expHalvings expOrder` of the base certificate, not `w ≥ e^{2πρ}` with another `π`
  bound; the strip compatibility checks of `hybWeightsOk`; no `real` weight (the checker's `realWeight = ⟨0, 1⟩`);
- `base.cert`: the base certificate's `expHalvings`, `expOrder`, Machin parameters and weight radius;
- `dE0`, `dE0R`: the whole-error Cauchy bound `n·err/(ρ − ρT)` that `hybCauchyOk` checks (no longer kernel-only);
- the polynomial claims are the checker's own sup bounds (`degFactorUp`, `toDeg`), not a separate norm;
- the real-torus torsion uses the real frame (`d1R`, `d1tR`), and λ₁ uses the invariance error e₁ = ℓ_E + (M₂/2)d₀²
  (`TransferQ`), not the iso maximum;
- the checker reads ρ₁ and μ₁ from `params1`; `step.rho1`, `step.mu1` are informational.

## 1. Conventions

- **File.** One JSON object per candidate, `docs/campaign/design/hybrid/hybrid-<name>.json`. Top-level keys:
  - `format` = `"kam-hybrid"` and `version` = 2;
  - `name` and `package`;
  - `n` (dimension), `scale_bits`;
  - the sections `base`, `step`, `restart`;
  - `plain_witness`: the route-A′ witness of the plain run on K̂ (informational: the mirror's plain margin);
  - optional and advisory: `models` (§6), `measured` (the producer's floating measurements), `note`.
- **Rationals.** Scalars are strings `"p/q"` or `"p"`.
- **Polynomial coefficients.** Integer strings at scale 2^`scale_bits`: a pair `["re", "im"]` stands for (re + i·im)/2^S.
- **Keys** are `[k₁, …, kₙ]` (a `CertKey`). The character is e_k(θ) = exp(2πi k·θ).
- **Real polynomial** (`CertRealPoly`). This is `{"zero": "z", "half": [[key, ["re", "im"]], …]}`. It denotes
  z/2^S + Σ_half (c e_k + c̄ e_{−k}) with c = (re + i·im)/2^S, over the half lattice {k₁ > 0} ∪ {k₁ = 0, k₂ > 0} ∪ ….
  `zero` is a mantissa as well.
- **Embedding** (`CertEmbedding`). This is `{"angleDeg": [d…], "angle": [poly…], "actionDeg": [d…], "action": [poly…]}`.
  It denotes K(θ) = (θ + (2π)^{dU_i} U_i(θ), (2π)^{dA_i} A_i(θ)), exactly the Lean `CertEmbedding.eval`.
- **Weights** (`CertWeight`): `{"rho": "r", "w": "w"}`. The checker's `checkWeight W s N` is
  `0 < r ∧ ratExpUp (2·piUpQ·r) s N ≤ w`, with piUpQ = 3141593/10⁶ and `ratExpUp` the halving–Taylor–squaring bound of
  `KAM/Certificate/Arith/Transcendental.lean`, at the base certificate's `expHalvings`, `expOrder` (`base.cert`).
- **Sup bounds** (the checker's `CertModel.supBound`): (2π)^d is bounded by `degFactorUp d` (piUpQ for d ≥ 0, piLoQ =
  3141592/10⁶ for d < 0); a polynomial's bound on T_r is Σ_k (|re c_k| + |im c_k|) w^{|k|₁}, over the full lattice
  (`toSortedPoly`: the conjugates, the constant, the half terms). Vectors: the max over components; matrices: the maximum
  row sum or column sum (`sumsOk`).

## 2. `base`: the certificate of the initial torus K

These fields are what the hybrid reads from K's certificate. The checker obtains them from K's ordinary
`TorusCertificate`, whose own checks run unchanged.

| Field | Lean type | Meaning |
|---|---|---|
| `params` | `CertParams` | K's frozen data: `tau`, `rho`, `rhoInf`, `M`, `sK`, `sB`, `sT`, `mu`, `gbar`, `sigma_omega`, `nuRay`, `gamma`, `s`, `err` (residual bound of K), `E0`, `disp` (the **outer** displacement claim, for the hybrid conclusion) |
| `freqBox` | `FreqBox` | the box of ω* |
| `cert` | (fields of `TorusCertificate`) | `expHalvings`, `expOrder`, `piEnc` (`machinK`, `machinJ`: the only fields of the π enclosure that `hybPolyOk` reads), `weightRho` (= `params.rho`, which `checkStatic` enforces); optional `assumed` (why, when the base certificate is not in Lean) |
| `emb` | `CertEmbedding ℚ` | K̂, a finite polynomial embedding (R1: `angleDeg = [-1, 0]`, `angle[0]` = v̂ with U = v̂/(2π); `actionDeg = [0, 0]`, `action` = (P̂₁, P̂₂)) |
| `claim` | `RefClaim` | K's refined claims `dh, dx, d2x, d2h, bL, bN, bNt, bT` (|DH|, |DX_H|, |D²X_H|, |D²H| on 𝔅; |Lᵀ|, |N|, |Nᵀ| on T_ρ; |T| on T_{ρ−δ₀}), checked by the Hamiltonian pass and the frame majorants (`HybWit.R0`) |
| `witnesses.exp` | `CertPoly` | the composition witness W ≈ e^{2i v̂} (full lattice, real coefficients for odd v̂; the `E_re` of the SO rotated format) |
| `witnesses.gramInv` | `List (List (CertPoly))` | n × n polynomial approximation of K̂'s Gram inverse (the Neumann witness of `gramCheck`) |
| `witnesses.torsInv` | `List (List CC)` | (n+1) × (n+1) approximation of K̂'s bordered torsion inverse (`torsionAvgCheck`) |

`witnesses` is absent for T2, whose base certificate is the Lean toy (`toyCert2H`, `Hybrid/Tests/T2.lean`: `toyCert2`
with the file's `base.params`, which differ from the toy's only in `disp`).

The base certificate also needs the Hamiltonian expression, the domain and the model configurations (advice): `ham`,
`weightH`, `centre`, `radius`, `cfgFull`, `cfgLow`, the π enclosure's centre and radius. For R1 they come from the SO
pipeline in the chosen time scale; the producer does not invent them (§6).

**R1's `cert` is assumed** (its base certificate is not in Lean): the toy's `expHalvings = 8`, `expOrder = 24`, Machin
`(4, 4)`, as AUDIT-C8C-1 and C8c checked. The producer makes the data independent of that choice: the weights also pass
at `(12, 30)` (SO's lunar certificate), and the polynomial claims are computed at Machin `(0, 0)`, the loosest
`twoPiZpowHi/Lo`, so they pass for any Machin parameters.

## 3. `step`: the hybrid witness (`HybWit.step : HybStep`)

| Field | Meaning |
|---|---|
| `iso` | `true`: the isoenergetic branch. The checker is isoenergetic only (`iso_g1_hybrid_R`) |
| `kernel_only` | the claims the mirror cannot recompute (§5): `lE`, `lH` (`hybCompOk`), `o0`, `o0R`, `o1`, `o1R` (`hybOmegaOk`) |
| `dK` | `HybStep.dK`: ΔK̂ as an embedding increment, same `angleDeg`, `actionDeg` as `base.emb`; the checker certifies `stepFun n (ratE dK)` |
| `s1` | `HybStep.s1`: the new ray parameter; the frequency of K̂₁ is s₁ω* |
| `rho1`, `mu1` | informational: the checker reads ρ₁ = `params1.rho` and μ₁ = `params1.mu` |
| `weights` | `rho1` (`W1`, radius ρ₁ ≤ r ≤ ρ), `rhoinf` (`Winf`, radius ≥ ρ∞), `torsion` (`WT`, radius ≥ ρT = ρ₁ − δ₀′) |
| `claims` | `HybStep.cl : StepNumQ` (`d0`, `dinf`, `d1`, `d1t`, `d0R`, `d1R`, `d1tR`, `lE`, `dE0`, `o0`, `dE0R`, `o0R`, `o1`, `o1R`, in this order), then `lH` and `dw` |

Meaning of the claims: `d0` = ‖ΔK̂‖ on T_{ρ₁}; `dinf` on T_{ρ∞}; `d1`, `d1t` = ‖DΔK̂‖, ‖(DΔK̂)ᵀ‖ on T_{ρ₁}; `d0R`, `d1R`,
`d1tR` on ℝⁿ; `lE` = ‖Ẽ_s‖ on T_{ρ₁} (the linearised new error at s₁ω*); `dE0`, `o0` = ‖DE‖, ‖Ω_K‖ on T′ = T_{ρT};
`dE0R`, `o0R` on ℝⁿ; `o1`, `o1R` = ‖Ω_{K₁}‖ on T′, ℝⁿ; `lH` ≥ |⟨H∘K̂⟩ − E₀ + ⟨DH(K̂)ΔK̂⟩|; `dw` ≥ |s₁ − s|·`boxNormUp`.

How the producer writes them (each passes the checker's comparison `bound ≤ claim`):
- `d0`, `dinf`, `d0R`, `d1`, `d1t`, `d1R`, `d1tR`: the checker's `stepSupOk`, `stepRealOk`, `dstepOk` bounds (exact), at
  Machin `(0, 0)`, rounded up to 13 significant digits;
- `dE0 = dE0R = n·err/(ρ − ρT)` (the bound of `hybCauchyOk`), rounded up;
- `lE`, `o0`, `o0R`, `o1`, `o1R`, `lH`: floating measurements × 1.10 (kernel-only);
- `dw`: |s₁ − s|·`boxNormUp`, rounded up.

## 4. `restart`: the restarted run

| Field | Meaning |
|---|---|
| `params1` | `HybWit.p1 : CertParams`: `rho = ρ₁`, `mu = μ₁`, `sK = σ_{K,1}` exactly, `sB ≥ σ_{B,1}`, `sT ≥ m_T + μ₁`, `err ≥ e₁`, `nuRay ≤ ν − d_ω`, `s = s₁`, `disp` = the restarted run's closeness budget D₁; `tau`, `rhoInf`, `M`, `gamma`, `gbar`, `sigma_omega`, `E0` as in `base.params` |
| `witness1` | `HybWit.w1 : RefinedWitR` (route A′, lever L8′): `base.core`, `base.R` (the transferred `RefClaim`), `base.kappa`, `base.sites`, `bF`, `bT` |
| `sites` | `"reuse-base"` when ρ₁ = ρ: with the same n, τ, kp, ρ, ρ∞, c, c̄, J, κ, γ and box, the restarted run's `sitesOk` is the base run's (`sitesOk` reads nothing else), so the base certificate's bite certificates apply verbatim |
| `transferred` | the producer's values of the transferred numbers (informational; the checker recomputes them) |

## 5. The checks of `checkHybrid` (ported by `hybrid_mirror.py` in the rational backend)

`checkHybrid c w = transferOk n c.params c.freqBox w && hybStepOk c w.step w.p1.rho w.p1.rhoInf (w.ρT n c.freqBox) &&
refinedCoreR n w.p1 c.freqBox w.w1`. In the rational backend every rounding error is 0, and Lean's division is
totalized (x/0 = 0); the mirror does the same.

Notation (`HybWit.kq`, `qq`, `δ1`, `ρT`): ℓ = σK − μ, β = σB − μ, m = σT − μ from `base.params`; ℓᵗ = `bL`, ν = `bN`,
νᵗ = `bNt`, t = `bT`, M₁ = `dx`, M₂ = `d2x`, M_{h1} = `dh`, M_{h2} = `d2h` from `base.claim`; c_Th = 2M₁, c_DTh = 2M₂;
δ₀′ = min(1, (ρ₁ − ρ∞)/6) with ρ₁, ρ∞ of `params1`; ρT = ρ₁ − δ₀′; w(ℓ, ℓᵗ, ε) = ℓᵗ·4nM₁·ℓ + ε(2nℓ + ℓᵗ);
ℓ_H^th = `params1.err` − (M_{h2}/2)(d₀ᴿ)².

**`transferOk`** (`RestartQ.lean`, 35 conjuncts, named as the fields of `TransferFacts`; all ported):
- margins: 0 < μ₁, d₀ + μ₁ ≤ μ, d₁ + μ₁/2 ≤ μ/2, ρ₁ ≤ ρ;
- frames (`FrameQ`, strip frame with (d₁, d₁ᵗ), real frame with (d₁ᴿ, d₁ᴿᵗ)): g = ℓᵗd₁ + d₁ᵗℓ + d₁ᵗd₁, βg < 1 for both;
  β₁ = β/(1 − βg), b = β²g/(1 − βg), n_Δ = β₁d₁ + ℓb, n_Δᵗ = β₁d₁ᵗ + ℓᵗb;
- errors: e₁ = ℓ_E + (M₂/2)d₀² ≤ `err₁`, ℓ_H + (M_{h2}/2)(d₀ᴿ)² ≤ `err₁`, 0 ≤ `err₁`;
- torsion: 0 < m and m·t_A^ext < 1, where, for the frame F (strip or real) and δ = δ₀′,
  - Δ_ab(F, d) = n_Δᵗ c_Th (ν + n_Δ) + νᵗ (c_DTh d)(ν + n_Δ) + νᵗ c_Th n_Δ;
  - λ₀ = νᵗβ·dE + β³ w(ℓ, ℓᵗ, dE)·o, with (dE, o) = (`dE0`, `o0`) on the strip, (`dE0R`, `o0R`) on ℝⁿ;
  - λ₁ = (νᵗ + n_Δᵗ)β₁·ε₁′ + β₁³ w(ℓ + d₁, ℓᵗ + d₁ᵗ, ε₁′)·o₁, with ε₁′ = n δ⁻¹ e₁ (the invariance error), F's own
    (d₁, d₁ᵗ, n_Δᵗ, β₁) and o₁ = `o1` (strip) or `o1R` (real);
  - t₁ = min{t + Δ_ab(strip, d₀) + λ₀, (νᵗ + n_Δᵗ) c_Th (ν + n_Δ)} + λ₁ (strip);
  - t_A = Δ_ab(real, d₀ᴿ) + λ₀ᴿ + λ₁ᴿ; t_A^ext = max{t_A + d_ω, n(M_{h1} n_Δᴿᵗ + M_{h2} d₀ᴿ (νᵗ + n_Δᴿᵗ))};
- `params1`: `tau`, `rhoInf`, `M`, `gamma`, `gbar`, `sigma_omega`, `E0` equal the base's; `s = s₁`;
  `sK = ℓ + d₁ + μ₁`; `sB ≥ β₁ + μ₁`; `sT ≥ m_T + μ₁` with m_T = m/(1 − m t_A^ext); `nuRay ≤ ν_ray − d_ω` and
  0 < ν_ray − d_ω;
- `witness1.base.R`: `dh, dx, d2x, d2h` equal the base claim's; `bL ≥ ℓᵗ + d₁ᵗ`, `bN ≥ ν + n_Δ`, `bNt ≥ νᵗ + n_Δᵗ`,
  `bT ≥ t₁`;
- outer: max{dinf, d_ω} + `disp₁` ≤ `base.disp`, dinf + `disp₁` ≤ μ/2, `base.disp` < (σω − s)·`freqNormLo`.

**`hybStepOk`** (`Claims.lean`):
- `hybWeightsOk` (ported): `checkWeight` of `W1`, `Winf`, `WT`; ρ₁ ≤ W1.rho ≤ `weightRho`; ρ∞ ≤ Winf.rho;
  ρT ≤ WT.rho; 0 < ρT < ρ;
- `hybPolyOk` (ported): `stepSupOk` of `d0` at `W1`, of `dinf` at `Winf`; `stepRealOk` of `d0R`; `dstepOk` of `d1`
  (row sums) and `d1t` (column sums) with models and bounds at `W1`, of `d1R`, `d1tR` with models at `Winf` and bounds at
  `realWeight`. The derivative of a degree-d component is `ofDeriv` (coefficients i k_j c at degree d + 1) brought to
  degree 0 by `toDeg` (coefficients × `twoPiZpowHi`, radius (hi − lo)·(the sup norm at the model's weight)), with
  `twoPiZpowHi/Lo` from the Machin parameters;
- `hybOmegaOk` (**kernel-only**): `o0`, `o0R`, `o1`, `o1R` from the products of the base embedding's models;
- `hybCauchyOk` (ported): n·err ≤ `dE0`·(ρ − ρT) and n·err ≤ `dE0R`·(ρ − ρT);
- `hybCompOk` (**kernel-only**): `lE` (the merged model of Ẽ) and `lH` (the energy model), from the compositions of the
  base Hamiltonian;
- d_ω (ported): |s₁ − s|·`boxNormUp` ≤ `dw`.

**`refinedCoreR n params1 freqBox witness1`** (ported: `hybrid_numq.py`, `classicalOk` in the mirror): Xs > 0, `wfOk`,
`okR`, `budgetOk`, `sitesOk`, `classicalOk` of the tail, `finalOkA`. `sitesOk` with `"reuse-base"`: the mirror checks
the equalities of §4 exactly; the base run's sites are certified in Lean (T2: `Hybrid/Tests/T2.lean`; R1: `r1R_sites`,
`kernel-tests/CertificateSharp/V2/RefinedRefR1.lean`). An explicit site list is kernel-only.

Not part of `checkHybrid`: the route `routeHybrid` also runs the base certificate's landed checks, `checkHamClaim` and
`checkFrameMajorants` of `base.claim`. The conclusion is `CertifiedTorus` for the **base** embedding K̂ with
`disp = base.params.disp` (`hybrid_certified`, `checkTorusCertificateV2_sound routeHybrid`).

## 6. Scope and open items

- **Package.** The R1 data are in the design package (c = 7/4, `r1Params`, `r1Box`, `r1Claim`, `r1RefinedWitR`: the v2
  certifier's R1 tests). SO's `lunarR1` (c = 237/125) is a rescaling of the same geometry: K̂ and ΔK̂ do not depend on c;
  `params`, `claim`, `E`'s model and the witnesses' frequency data do. The SO production (C8d part 2) emits the same format
  with SO's package and SO's Hamiltonian expression, domain and advice. That is a later package.
- **Models are advisory.** `models.E` and `models.Elin` (the producer's floating models: support, rounded coefficients,
  tail mass) are advice and cross-checks. The kernel computes its own models.
- **Kernel-only claims** (`lE`, `lH`, `o0`, `o0R`, `o1`, `o1R`): floating values × 1.10, rounded up. They need R1's
  `TorusCertificate` in Lean.
- **Backend.** The mirror ports the rational backend (`instCertArithRat`), which T2 uses and R1's tests assume. A
  rounded backend adds rounding radii that the mirror does not model; the claims are rounded up to 13 significant digits,
  but that room has not been measured against a rounded backend.
- **Iso only.** The checker is isoenergetic; R1's ordinary torsion average is sampled as nearly singular (design note
  §4.6).

## 7. The Lean data of the R1 kernel tests

`hybrid_producer.py --lean DIR` writes `HybridR1L8Data.lean` from `hybrid-R1-L8.json` alone (`write_lean`), so the Lean
data and the JSON agree byte for byte on regeneration. Layout (namespace `KAM.CertificateSharp.HybridR1Test`):
- `q60 m = m / 2^60` (exposed); every polynomial mantissa is written `q60 m`.
- `r1HybEmb`, `r1HybStep : CertEmbedding ℚ` are `base.emb` and `step.dK`. Each component's `half` list is split into
  declarations of at most 40 terms (`r1HybStepAct1P0 ++ r1HybStepAct1P1 ++ …`). One 261-term literal exceeded the
  default heartbeats (hard rule 1: split, never raise the budget).
- `r1HybBaseParams : CertParams` and `r1HybBaseClaim : RefClaim` are `base.params` and `base.claim`; `r1HybW1`,
  `r1HybWinf`, `r1HybWT : CertWeight` are `step.weights` (v2).
- `r1HybParams1 : CertParams`, `r1HybCore : FrozenWit` and `r1HybClaim : RefClaim` are `restart.params1`,
  `witness1.base.core` and `witness1.base.R`. `bF`, `bT`, `κ` and the sites are set in the test modules.
- `r1HybClaims : List ℚ` holds `step.claims` in the order of `r1HybClaimNames`.

The test modules are in `kernel-tests/CertificateSharp/V2/`, unbuilt. Each compiles as
`KAM.CertificateSharp.V2.Tests.<file>` when placed back under `KAM/`, as `kernel-tests/README.md` says:
- `HybridR1L8Data`: the data above;
- `HybridR1L8Aligned` (C8dfix): `transferOk` (H0–H4) and `hybPolyOk` on R1, everything read from the data module;
- `HybridR1L8`, `HybridR1L8Core` (C8d): H5 without and with the base run's certified sites;
- `HybridR1L8Transfer` (C8c): H0–H4 with hard-coded copies of the v1 base parameters and weights, stale since v2 (its
  `disp` is below the v2 requirement); `HybridR1L8Aligned` replaces it.

## 8. The cross-language regression

`python3 -I scripts/apost_sharp/hybrid_xlang.py [--lean [--record]]`. Cases: the two accepted files and mutations aimed at
single checks, including boundary pairs (a claim at its exact Lean value is accepted, 10⁻⁴⁰ below rejected; each weight
at its `ratExpUp` value rounded at 10⁻⁴⁰ up and down). For each case the mirror and the Lean definitions (`#eval` in
generated probes) evaluate `transferOk`, `hybWeightsOk`, `hybPolyOk`, `hybCauchyOk`, the d_ω check and the conjuncts of
`refinedCoreR` except `sitesOk`; for T2 the probe also runs the complete `checkHybrid toyCert2H w`. R1 cases use a
certificate stub (`toyCert2H` with R1's `params`, `freqBox`, weight radius, `expHalvings`, `expOrder`, Machin
parameters), the only fields these sub-checks read. Exact intermediate values (the transfer numbers, the step bounds,
`ratExpUp` to 10⁻⁶⁰) are compared as strings on the accepted files and on synthetic nonzero fixtures. Without `--lean`
the mirror is compared with the recorded Lean results `docs/campaign/design/hybrid/xlang-lean.json`.
