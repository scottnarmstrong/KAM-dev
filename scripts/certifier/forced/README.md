# Forced-toy regression suite (V2-TOOLS #6)

Untrusted producer tooling for a small periodically forced Hamiltonian with interacting Fourier modes,

    H = c (J + β p²/2 + Σ_j ε_j cos 2π k_j·θ),     θ = (θ₀, θ₁), θ₁ the time, J its action,

with reference vector `κ (ν₋(N) − 1, 1)`, `κ = c/s`, from the proved family `lunarRotFreqMinusN_isDiophantine`
(γ = κ/(N + 2), τ = 1, N ≥ 8). The Lean tests live in `KAM/CertificateSharp/V2/Tests/Forced/`; the producer's
reports and witnesses in `scripts/certifier/fixtures/forced-toy/`.

| Script | Role |
|---|---|
| `forced_model.py` | the model, the √5 box (`checkAlgBox` form), the torus by a Picard iteration in exact rationals (π-free unknowns `u = 2πU`, `p`, `J`) |
| `forced_cert.py` | the `TorusCertificate 2 (CertFixed 96)` through the `sofx_*` mirror of the landed checker: domain, M, σ's, Gram and torsion witnesses, err; GENERATE then CHECK with the recorded advice books |
| `forced_stages.py` | the memoized Gram/torsion stages (`Kernel/Stage.lean` order and keys) and their Lean literals |
| `forced_emit.py` | Lean emission of the certificate (format helpers in `Forced/Format.lean`) |
| `forced_build.py TAG` | build one named spec (`Tiny`, `Micro`, `TinyC2`) and write `<TAG>Data/Stages/Checks/Base.lean` |
| `forced_lean.py` | compiled-Lean `#eval` oracle (ℚ-level checks only: the `CertFixed` instance is noncomputable) |
| `forced_witness.py` | refined claim R (mirror), certified small-divisor sites (Lean `balCheck` search), route A/B/frozen witnesses (`v2_q`, `v2_r2`, `route_b_lean_mirror`) |
| `forced_routes.py TAG` | `<TAG>Freq/Claim/RouteA.lean` (and the route-B, L8′, frozen/sharp modules) |
| `forced_mutations.py TAG` | 24 mutations with mirror verdicts, `<TAG>Mutations(Inv).lean` |
| `forced_sweep.py` | mirror sweep of frequency separation, twist, support, precision, perturbation, time scale |
| `forced_xlang.py` | cross-language agreement (31 comparisons; exit status 0 iff all agree) |

Reproduce (from the repository root; `FORCED_WORK` holds the pickles):

    export FORCED_WORK=/tmp/forced-work
    python3 -I scripts/certifier/forced/forced_build.py Tiny     # also Micro, TinyC2
    python3 -I scripts/certifier/forced/forced_routes.py Tiny    # needs TinyData built
    python3 -I scripts/certifier/forced/forced_mutations.py Tiny
    python3 -I scripts/certifier/forced/forced_xlang.py
    nice -n 5 lake build KAM.CertificateSharp.V2.Tests.Forced.TimeScale   # and the other Forced modules

Kernel cost is quadratic in the Fourier support (the direct product costs about 1 ms per coefficient pair in
the kernel), so the toys keep every model at a few dozen terms; the character witness enters the residual
multiplied by ε, so it is pruned at err/ε rather than at err.
