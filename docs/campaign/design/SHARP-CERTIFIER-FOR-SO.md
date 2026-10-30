# Switching the lunar certificate to the sharp certifier (note for the SO orchestrator)

30 October 2026, from the `apost-sharp` side campaign (landed at dfae4a77; decision D36). The owner has decided that the
lunar certificate moves to the sharp certifier.

- **Certifier.** `KAM.CertificateSharp.checkTorusCertificateSharp` (`KAM/CertificateSharp/Sharp.lean`). It takes the
  same `KAM.Certificate.TorusCertificate` and runs the same sub-checks (`checkStatic`, `checkHamBounds`,
  `checkEmbedding`, `checkGram`, `checkTorsion`, `checkInvariance`, `checkEnergy`) unchanged; only the smallness
  test differs (`sharpTest`, with exact rational mirrors `sharpIsoC1Q/2Q/3Q` in `KAM/CertificateSharp/ConstantsQ.lean`).
- **Soundness.** `KAM.CertificateSharp.checkTorusCertificateSharp_sound` (`KAM/CertificateSharp/Sound.lean`): same
  conclusion `CertifiedTorus c ωstar` and same premises as `KAM.Certificate.checkTorusCertificate_sound`, through
  `KAM.Iso.Sharp.g1_sharp` (Rüssmann data κ = τ ∈ ℕ). Axioms: propext, Classical.choice, Quot.sound.
- **Sizing the data.** The threshold is now `e < γ⁴ ρ^{4τ} / sharpIsoC1` instead of `γ⁴ ρ^{4τ} / isoC1`. For package R1
  the design mirror gives about 10⁻²⁵ instead of 10⁻⁷⁵ (`scripts/apost_sharp/thresholds.py`, design §6 of
  `docs/campaign/design/APOST-SHARP-LEAN-DESIGN.md`; M = 1.924 in the corrected inputs). Size the truncation to the new
  threshold with the same headroom rule as before; per CONSTANTS-STUDY §2.3 that is roughly 30 digits instead of 87,
  and far fewer Fourier coefficients and product pairs. Re-optimize ρ, μ and the frame for the new constants: the
  optimum moves (the sharp constants depend on M, σ_K, σ_B, σ_T separately).
- **Evidence.** On the toy certificates the sharp margin (threshold / error) is 10^19.4 (T2) and 10^27.9 (T3) against
  10^4.3 for the old certifier (`KAM/CertificateSharp/Tests/Margin.lean`).
- **Coming later behind the same interface** (no certificate-format change unless stated): v2 of the theorem
  (finer, certificate-checkable hypotheses; frequency-specific small-divisor constants), tighter checker majorants,
  and a free-parameter optimizer (`scripts/certifier/`). New hypotheses, if any, will come with new sub-checks.
