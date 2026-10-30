# Hybrid certificate data: format v1 (producer C8d ↔ checker C8c)

Owner: SHARP2-C8D (this file). The consumer is C8c, the Lean hybrid checker (not yet written). This file fixes the data the
producer `scripts/apost_sharp/hybrid_producer.py` writes, the meaning of every field, and the checks that C8c must
perform. Those checks are mirrored exactly in `scripts/apost_sharp/hybrid_mirror.py`. Theory: design note
`docs/campaign/design/APOST-SHARP-V2-HYBRID.md` §§2–3; blueprint `p2s2-hybrid-cert` (labels `bp:p2s2hc:*`, `bpI:p2s2hc:*`).

## 1. Conventions

- **File.** One JSON object per candidate, `docs/campaign/design/hybrid/hybrid-<name>.json`. Top-level keys:
  - `format` = `"kam-hybrid"` and `version` = 1;
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
- **Weights** (`CertWeight`): `{"rho": "r", "w": "w"}`, with w ≥ e^{2πr} checked by the certifier's `checkWeight`.
- **Norms**: as in the certificate. The max norm on vectors and the maximum absolute row sum on matrices. The weighted
  norm of a polynomial on T_r is Σ_k |c_k| w^{|k|₁}. A complex coefficient's modulus is bounded by |re| + |im| (`ballMagQ`).

## 2. `base`: the certificate of the initial torus K

These fields are what the hybrid reads from K's certificate. C8c obtains them from K's ordinary `TorusCertificate`, whose
own checks run unchanged.

| Field | Lean type | Meaning |
|---|---|---|
| `params` | `CertParams` | K's frozen data: `tau`, `rho`, `rhoInf`, `M`, `sK`, `sB`, `sT`, `mu`, `gbar`, `sigma_omega`, `nuRay`, `gamma`, `s`, `err` (residual bound of K), `E0`, `disp` (the **outer** displacement claim, for the hybrid conclusion) |
| `freqBox` | `FreqBox` | the box of ω* |
| `emb` | `CertEmbedding ℚ` | K̂, a finite polynomial embedding (R1: `angleDeg = [-1, 0]`, `angle[0]` = v̂ with U = v̂/(2π); `actionDeg = [0, 0]`, `action` = (P̂₁, P̂₂)) |
| `claim` | `RefClaim` | K's refined claims `dh, dx, d2x, d2h, bL, bN, bNt, bT` (|DH|, |DX_H|, |D²X_H|, |D²H| on 𝔅; |Lᵀ|, |N|, |Nᵀ| on T_ρ; |T| on T_{ρ−δ₀}), checked by the Hamiltonian pass and the frame majorants |
| `witnesses.exp` | `CertPoly` | the composition witness W ≈ e^{2i v̂} (full lattice, real coefficients for odd v̂; the `E_re` of the SO rotated format) |
| `witnesses.gramInv` | `List (List (CertPoly))` | n × n polynomial approximation of K̂'s Gram inverse (the Neumann witness of `gramCheck`) |
| `witnesses.torsInv` | `List (List CC)` | (n+1) × (n+1) approximation of K̂'s bordered torsion inverse (`torsionAvgCheck`) |

`witnesses` is absent for T2, whose base certificate is the Lean toy (`KAM/Certificate/Tests/Toy2Data.lean`).

The base certificate also needs the Hamiltonian expression, the domain and the model configurations (advice). They are
the existing certificate's (`ham`, `weightH`, `centre`, `radius`, `cfgFull`, `cfgLow`, `piEnc`, `expHalvings`,
`expOrder`). For R1 they come from the SO pipeline in the chosen time scale; the producer does not invent them (§6).

## 3. `step`: the hybrid witness

| Field | Meaning |
|---|---|
| `iso` | `true`: the isoenergetic branch (H2 and H3 with their iso terms; `s1` present). `false`: fixed frequency |
| `kernel_only` | the names of the claims the mirror cannot recompute (§6); C8c must compute them in the kernel |
| `dK` | ΔK̂ as an embedding increment: same `angleDeg`, `actionDeg` as `base.emb`. K̂₁ = K̂ + ΔK̂ adds the polynomials componentwise (a finite embedding). |
| `s1` | the new ray parameter (iso); frequency of K̂₁ is s₁ω*. `s1 = base.params.s` at fixed frequency. |
| `rho1`, `mu1` | the restart strip ρ₁ ∈ (ρ∞, ρ] and margin μ₁ ∈ (0, μ) |
| `weights` | `rho1`, `rhoinf`, `real` (r = 0, w = 1), `torsion` (r = ρ₁ − δ₀′): the `CertWeight`s of the strips used |
| `claims` | the step bounds (S1)–(S9), each an upper bound that C8c checks: `d0` = ‖ΔK̂‖ on T_{ρ₁}; `dinf` on T_{ρ∞}; `d1`, `d1t` = ‖DΔK̂‖, ‖(DΔK̂)ᵀ‖ on T_{ρ₁}; `d0R`, `d1R`, `d1tR` on ℝⁿ; `lE` = ‖Ẽ_s‖ on T_{ρ₁} (the linearised new error at s₁ω*); `dE0`, `o0` = ‖DE‖, ‖Ω_K‖ on T′ = T_{ρ₁−δ₀′}; `dE0R`, `o0R` on ℝⁿ; `o1`, `o1R` = ‖Ω_{K₁}‖ on T′, ℝⁿ; `lH` = \|⟨H∘K̂⟩ − E₀ + ⟨DH(K̂)ΔK̂⟩\|; `dw` ≥ \|s₁ − s\|·`boxNormUp(freqBox)` |

How C8c checks the claims:
- **Polynomial claims** `d0`, `dinf`, `d0R`, `d1`, `d1t`, `d1R`, `d1tR`. The weighted norms of ΔK̂ and its exact derivative
  (`CertModel.ofDeriv`; for angle components with degree −1 the derivative is π-free; action components carry
  (2π)^1, bounded with `piEnc`).
- **`lE`.** Form the model of Ẽ_s = E_{s₁}(K̂) + DX_H(K̂)·ΔK̂ − DΔK̂·(s₁ω*). E_{s₁} is the invariance model at s₁ω*
  (`invarianceModel`); DX_H∘K̂ comes from the same composition's jet. Then take its `supBound` with the ρ₁ weight.
  Products must combine coefficients before taking norms, so the Newton cancellation is kept.
- **`dE0`, `dE0R`.** The derivative of E's model: exact on the polynomial part, plus a Cauchy bound n·rad/δ for the
  remainder from the larger strip. Alternatively the whole-error Cauchy bound n·err/(ρ − ρ₁ + δ₀′).
- **`o0`, `o1`, `o0R`, `o1R`.** Exact polynomial products DK̂ᵀΩ₀DK̂ and DK̂₁ᵀΩ₀DK̂₁.
- **`lH`.** The energy model's zero mode plus the zero mode of DH∘K̂ times ΔK̂.

## 4. `restart`: the restarted run

| Field | Meaning |
|---|---|
| `params1` | `CertParams` of the restarted run: `rho = rho1`, `mu = mu1`, `sK = σ_{K,1}`, `sB ≥ σ_{B,1}`, `sT ≥ σ_{T,1}`, `err ≥ e₁`, `nuRay ≤ ν − dw`, `s = s1`, `disp` = the restarted run's closeness budget D₁; the other fields equal `base.params` |
| `witness1` | `RefinedWitR` (route A′, lever L8′): `base.core` (`Xs`, `kp`, `th`, `c`, `cbar`, `ctail`, `sB`, `sT`, `sLt`, `sN`, `sNt`, `t`, `J`), `base.R` (the transferred `RefClaim`), `base.kappa`, `base.sites`, `bF`, `bT` |
| `sites` | `"reuse-base"` when ρ₁ = ρ (the restarted schedule is the base schedule, so the base certificate's bite certificates apply verbatim); otherwise the list of bite witnesses |
| `transferred` | the producer's values of the transferred numbers (informational; C8c recomputes them) |

## 5. The checks of C8c (mirrored by `hybrid_mirror.py`, exact rationals)

Notation:
- From the base: ℓ = σK − μ, β = σB − μ, m = σT − μ (from `base.params`); ℓᵗ = `bL`, ν = `bN`, νᵗ = `bNt`, t = `bT`,
  M₁ = `dx`, M₂ = `d2x`, M_{h1} = `dh`, M_{h2} = `d2h` (from `base.claim`).
- c_Th = 2M₁ and c_DTh = 2M₂ (`norm_hamComm_le`; the M₂ variant of `norm_hamComm_sub_le`).
- δ₀′ = min(1, (ρ₁ − ρ∞)/6), and w(ℓ, ℓᵗ, ε) = ℓᵗ·4nM₁·ℓ + ε(2nℓ + ℓᵗ).

**H0. Margins.**
- 0 < μ₁ < μ;
- d₀ < μ, d₀ + μ₁ ≤ μ, d₁ + μ₁/2 ≤ μ/2;
- ρ∞ < ρ₁ ≤ ρ.

**H1. Frames** (Lemma `bp:p2s2hc:frames`).
- g = ℓᵗd₁ + d₁ᵗℓ + d₁ᵗd₁, with βg < 1;
- β₁ = β/(1 − βg), b = β²g/(1 − βg);
- n_Δ = β₁d₁ + ℓb, n_Δᵗ = β₁d₁ᵗ + ℓᵗb;
- the same on ℝⁿ with (d₁ᴿ, d₁ᴿᵗ), and βgᴿ < 1.

**H2. New errors.** e₁ = max{ℓ_E + (M₂/2)d₀², ℓ_H + (M_{h2}/2)(d₀ᴿ)²} (iso; fixed frequency: the first term only).

**H3. Torsion** (Lemma `bp:p2s2hc:torsion`).
- ε₁′ = n e₁/δ₀′; ν₁ = ν + n_Δ, ν₁ᵗ = νᵗ + n_Δᵗ.
- Δ_ab = n_Δᵗ c_Th ν₁ + νᵗ c_DTh d₀ ν₁ + νᵗ c_Th n_Δ.
- λ₀ = νᵗβε₀′ + β³ w(ℓ, ℓᵗ, ε₀′) o₀ and λ₁ = ν₁ᵗβ₁ε₁′ + β₁³ w(ℓ + d₁, ℓᵗ + d₁ᵗ, ε₁′) o₁ on T′, with ε₀′ = `dE0`.
- t₁ = min{t + Δ_ab + λ₀, ν₁ᵗ c_Th ν₁} + λ₁.
- On ℝⁿ (superscript R): t_A = Δ_abᴿ + λ₀ᴿ + λ₁ᴿ.
- Iso: t_A^ext = max{t_A + d_ω, n(M_{h1} n_Δᴿᵗ + M_{h2} d₀ᴿ (νᵗ + n_Δᴿᵗ))}. Then m·t_A^ext < 1.

**H4. Consistency of the restart data.**
- `params1`:
  - `rho = ρ₁`, `rhoInf`, `tau`, `M`, `gamma`, `gbar`, `sigma_omega`, `E0` as in the base;
  - `mu = μ₁`;
  - `sK = ℓ + d₁ + μ₁` (so the run's internal cap is σ_{K,1} − μ₁/2 ≤ σK − μ/2);
  - `sB ≥ β₁ + μ₁`, `sT ≥ m/(1 − m t_A^ext) + μ₁`;
  - `err ≥ e₁`, `nuRay ≤ ν_ray − d_ω`, `s = s₁`.
- `witness1.base.R`:
  - `dh, dx, d2x, d2h` as in `base.claim`;
  - `bL ≥ ℓᵗ + d₁ᵗ`, `bN ≥ ν + n_Δ`, `bNt ≥ νᵗ + n_Δᵗ`, `bT ≥ t₁`.
- The outer displacement: `base.params.disp ≥ max{dinf, d_ω} + params1.disp`, and `dinf + params1.disp ≤ μ/2`.

**H5. The restarted run.** `refinedCoreR n params1 freqBox witness1 = true`. The sites are reused when ρ₁ = ρ. This is the
existing route-A′ core: `wfOk`, `okR`, `budgetOk`, `classicalOk` and `finalOkA` at `params1`. `finalOkA` gives
`err < Xs γ⁴ δ₀′^{4τ}` and the closeness `max(c2Q, c3Q)·err ≤ disp·γ²ρ₁^{2τ}`.

H0–H5 give every hypothesis of `KAM.Iso.Sharp2.Hybrid.iso_g1_hybrid_R` (signature probe of SHARP2-HYBRID). The
conclusion is `CertifiedTorus` for the **base** embedding K̂, with `disp = base.params.disp`.

## 6. Scope of v1 and the open items for C8c

- **Package.** The R1 data are in the design package (c = 7/4, `r1Params`, `r1Box`, `r1Claim`, `r1RefinedWitR`: the v2
  certifier's R1 tests). SO's `lunarR1` (c = 237/125) is a rescaling of the same geometry: K̂ and ΔK̂ do not depend on c;
  `params`, `claim`, `E`'s model and the witnesses' frequency data do. The SO production (C8d part 2) emits the same format
  with SO's package and SO's Hamiltonian expression, domain and advice. That is a later package, not this one.
- **Models are advisory.** `models.E` and `models.Elin` (the producer's floating models: support, rounded coefficients,
  tail mass) are advice and cross-checks. The kernel computes its own models.
- **Claims marked `kernel-only`** (`lE`, `dE0`, `dE0R`, `o0`, `o0R`, `o1`, `o1R`, `lH`) cannot be recomputed by the mirror
  without the composition. The producer gives floating values times 1.10 (rounded up). The mirror recomputes every
  polynomial claim exactly.
- **Iso only for R1.** R1's ordinary torsion average is sampled as nearly singular (design note §4.6), so `s1` is always
  present and the iso checks apply.

## 7. The Lean data of the R1 kernel test

`hybrid_producer.py --lean DIR` writes `HybridR1L8Data.lean` from `hybrid-R1-L8.json` alone (`write_lean`), so the Lean
data and the JSON agree byte for byte on regeneration. Layout (namespace `KAM.CertificateSharp.HybridR1Test`):
- `q60 m = m / 2^60` (exposed); every polynomial mantissa is written `q60 m`.
- `r1HybEmb`, `r1HybStep : CertEmbedding ℚ` are `base.emb` and `step.dK`. Each component's `half` list is split into
  declarations of at most 40 terms (`r1HybStepAct1P0 ++ r1HybStepAct1P1 ++ …`). One 261-term literal exceeded the
  default heartbeats (hard rule 1: split, never raise the budget).
- `r1HybParams1 : CertParams`, `r1HybCore : FrozenWit` and `r1HybClaim : RefClaim` are `restart.params1`,
  `witness1.base.core` and `witness1.base.R`. `bF`, `bT`, `κ` and the sites are set in the test module.
- `r1HybClaims : List ℚ` holds `step.claims` in the order of `r1HybClaimNames`.

The test modules are in `kernel-tests/CertificateSharp/V2/`, unbuilt. Each compiles as
`KAM.CertificateSharp.V2.Tests.<file>` when placed back under `KAM/`, as `kernel-tests/README.md` says:
- `HybridR1L8Data`: the data above;
- `HybridR1L8`: H5 without the sites (`r1Hyb_refinedCoreR_of_sites`), plus the margin pair at e = 1.5 and 1.55·10⁻¹¹;
- `HybridR1L8Core`: H5 with the base run's certified sites (`hyb_sitesOk_congr`, `r1R_sites`).

**For C8c.** State H0–H4 against these names, in a new module once the checker exists: the checker applied to
(`r1HybEmb`, `r1HybStep`, the base data, `r1HybClaims`, `r1HybParams1`, `r1HybWitR sites`). The base certificate's
Lean data (Hamiltonian, model configurations, `W`, `gramInv`, `torsInv`) is in the JSON but not yet in Lean. C8c fixes
its Lean shape, and the producer then emits it (open item).
