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
| `forced_routes.py TAG [--B / --R XS BF BT / --frozen]` | `<TAG>Freq/Claim/RouteA.lean`; route B; L8′; the sharp and frozen routes |
| `forced_mutations.py TAG` | 25 mutations with mirror verdicts (laid out into the `TinyMut*` modules by `forced_layout.py`) |
| `forced_sweep.py` | mirror sweep of frequency separation, twist, support, precision, perturbation, time scale |
| `forced_xlang.py` | cross-language agreement (52 comparisons for Tiny, Micro, TinyC2; exit status 0 iff all agree) |
| `forced_layout.py` | lays the generated full modules out: a cheap default-build subset and the opt-in `kernel-tests/CertificateSharp/V2/ForcedRoutes.lean` |
| `forced_profile.py TAG [--spec JSON\|@FILE]` | the `route_select.py` profile `forced_<tag>` of a model spec: err and product pairs against the truncation `L = prune_digits` (mirror only, no Lean) |
| `forced_diag.py [--xlang TAG]` | the named failure lines (`FAIL route=… check=…`) printed by `forced_build.py`, `forced_routes.py` and `route_select.py` on a failure path only; the exact mirror of every clause of `frozenBCore` (`finalBF` included) that `forced_routes.py --frozen` checks before writing; `--xlang` compares that mirror with the compiled Lean on `<TAG>Routes` |
| `forced_rot.py` | (V2-CONSOL) the rotated normalization `MicroRot` of `Micro` (`shearMap = soRotMap`): exact transform of `Micro`'s data, the mirror computes the rest; writes `MicroRot{Data,Stages,ChecksA,ChecksB,Gram,Torsion1,Torsion2,Torsion3,Base,Routes}.lean` and `fixtures/forced-toy/MicroRot.json` (the transformation theorems are in the hand-written `MicroRotFreq`, `MicroRotTransform`, `MicroRotLunar`, `MicroRotMut`) |
| `../../packed/forced_packed_gen.py` | (V2-CONSOL) the packed books and memos of `Micro` (`MicroP.cert`: `Micro.cert` with `CertFixed.toMant 96` in `cfgLow`) and a refined route-A witness; writes `MicroPackedData.lean` and `fixtures/forced-toy/Micro_packed.json` (the proofs are in `PackedLemmas`, `MicroPacked{Gram,Compose,Tors,Claim,Frames,Controls}`, `MicroPacked`) |
| `forced_l1.py` | (V2-CONSOL) the ℓ¹ entry of `Tiny`: the claim from the mirror's models, an exact port of `okL1` (`RouteAL1Q`/`Run`), the Γ∞ witnesses, the X⋆ search |
| `forced_hybrid.py` | (V2-CONSOL) the hybrid restart of `Tiny`: the Newton step, a port of the step checks on the sofx mirror, the transfer and the restart |
| `forced_l1hyb.py TAG` | (V2-CONSOL) writes `<TAG>L1HybData.lean` and the fixtures `<TAG>_l1.json`, `<TAG>_hybrid.json` (byte-identical from scratch) |
| `forced_costs.py` | (V2-CONSOL) the measured cost terms of `route_select.py` (`fixtures/route-select/forced_costs.json`); its Lean calls go through `FORCED_LEAN_PREFIX` (a lock and memory-gate wrapper) |

Layout (orchestrator ruling, V2-TOOLS-FIX: default modules of a few seconds each):
* default build: `Format`, `Lemmas`; `Micro` (the passing certificate: `MicroChecksA/B`, `MicroGram`,
  `MicroTorsion1/2/3`, `MicroBase`, `MicroRoutes` — sharp, frozen A, frozen B); `Tiny`'s mutations
  (`TinyWitness`, `TinyGram`, ten `TinyMut*` modules); the data modules `<T>Data`, `<T>Stages`, `<T>Freq` that
  the opt-in test imports; (V2-CONSOL) `MicroRot` (the rotated normalization, same layout as `Micro`, with
  `MicroRotTransform` and the drift mutations `MicroRotMut`) and `MicroP` (the packed route, `MicroPacked*`); `Tiny`'s ℓ¹ entry and hybrid restart in part (`TinyL1Core`,
  `TinyL1Claim`, `TinyHybCore`, `TinyHybStep`; the data `TinyL1HybData`);
* opt-in: `kernel-tests/CertificateSharp/V2/ForcedRoutes.lean` (`Tiny`'s routes A, L8′, B and tori, `mut_frameT`,
  the `TinyC2` chain, the time-normalization tori); `kernel-tests/CertificateSharp/V2/ForcedL1Hybrid.lean`
  (V2-CONSOL: `Tiny` through the ℓ¹ entry and the hybrid restart, with their tori).

From a model of your own to a kernel-checked torus, step by step: `docs/certifier/QUICKSTART.md`.

Reproduce (from the repository root; `FORCED_WORK` holds the pickles):

    export FORCED_WORK=/tmp/forced-work
    python3 -I scripts/certifier/forced/forced_build.py Tiny     # also Micro, TinyC2
    python3 -I scripts/certifier/forced/forced_routes.py Tiny    # needs TinyData built (also TinyC2)
    python3 -I scripts/certifier/forced/forced_routes.py Tiny --B
    python3 -I scripts/certifier/forced/forced_routes.py Tiny --R 191 1/1000 1/1000
    python3 -I scripts/certifier/forced/forced_routes.py Micro --frozen
    python3 -I scripts/certifier/forced/forced_mutations.py Tiny
    python3 -I scripts/certifier/forced/forced_xlang.py
    python3 -I scripts/certifier/forced/forced_layout.py      # needs the full modules of all three tags
    nice -n 5 lake build KAM.CertificateSharp.V2.Tests.Forced.MicroRoutes   # and the TinyMut* modules
    nice -n 10 lake env lean kernel-tests/CertificateSharp/V2/ForcedRoutes.lean   # opt-in

Kernel cost is quadratic in the Fourier support (the direct product costs about 1 ms per coefficient pair in
the kernel), so the toys keep every model at a few dozen terms; the character witness enters the residual
multiplied by ε, so it is pruned at err/ε rather than at err.
