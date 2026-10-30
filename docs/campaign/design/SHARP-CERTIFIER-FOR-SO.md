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

## Update: the v2 certifier (landed 86089b36, 30 October 2026; audit AUDIT-C6-1 PASS)

Same certificate format, same conclusion; a new engine interface and a witness.
- **Certifier.** `KAM.CertificateSharp.checkTorusCertificateV2 routeAV2 c w` (`KAM/CertificateSharp/V2/Engine.lean`,
  `V2/RouteARefinedEngine.lean`). `routeAV2 = sharpV2.orElse (routeAFrozen.orElse routeARefined)`; the witness `w` names
  the route: `Sum.inl ()` is exactly the landed sharp certifier (`checkTorusCertificateV2_routeAV2_sharp`, `rfl`), so the
  switch can never make a passing certificate fail.
- **Soundness.** `checkTorusCertificateV2_sound`: a passing check, `FreqEncloses n c.freqBox ωstar` and
  `IsDiophantine γ τ ωstar` give the landed `CertifiedTorus c ωstar`. Every refined bound (`HamFacts`, `FrameFacts`) is
  proved by checks inside; the witness carries only numbers. Axioms: propext, Classical.choice, Quot.sound.
- **Routes.** Through the proved and audited v2 route A (`KAM.Iso.Sharp2.RouteA`):
  - `routeAFrozen` with `FrozenWit` (X⋆, prefix length, ϑ, classical constants, caps): frozen data only;
  - `routeARefined` with `RefinedWit` (a `FrozenWit`, the claimed bounds `RefClaim` on |DH|, |DX_h|, |D²X_h|, |D²H|, |L|,
    |N|, |Nᵀ|, |T| checked against the certificate's models, the exact clock coordinate κ, and per-bite small-divisor
    witnesses for n = 2, τ = 1, else the classical constant).
- **Thresholds** (design package R1, kernel-checked arithmetic with the design's assumed bounds; no lunar models run):
  frozen route 10^−20.94, refined route 10^−11.33 (the landed sharp certifier: about 10^−25). With the §2.7 measured lunar
  parameters, by `#eval`: −12.07, or −11.43 with separate σ_K = 1.37, σ_B = 1.99, σ_T = 1.03 (choose them separately).
- **Sizing.** At 10^−11.3 the truncation needs roughly 16–18 digits instead of about 30; resize with the same headroom
  rule. The frequency box must have its last (clock) coordinate exact with radius 0.
- **Kernel cost.** The refined numerical core is about 140 s and 10.4 GB peak at prefix 3 (one niced process); the extra
  Ham and frame checks cost about one more `checkHamBounds`, `checkTorsion` and `checkGram` (estimate 0.3–0.9 CPU-h at
  L ≈ 18). Handoff: `docs/campaign/handoffs/SHARP2-C6.md`.
- **Coming:** route B (`orElse`, for the dominance claim; worse than route A on R1) and the l1 entry step.

## Update: every route in one engine (landed b451b95b, 30 October 2026)

Use `KAM.CertificateSharp.checkTorusCertificateV2 routeV2All c w` (`KAM/CertificateSharp/V2/RouteAll.lean`; its
docstring tables the witness constructor for each route). Routes: the landed sharp certifier (`Sum.inl ()`, equal by
`rfl`), route A frozen/refined, route A with L8′ (`routeARefinedR`), the l1 entry step (`routeAL1`, which computes the
torus's l1 data from the certificate's models), route B frozen/refined. On the lunar design package the best is the
l1 entry (numerical core 10^−10.18, kernel except the bites), then L8′ (10^−10.81), route A (10^−11.33), route B
(10^−12.59); these R1 checks are opt-in (`kernel-tests/`), and the bites at l ≥ 13 exceed lemma.farm's 10 GB per-process
limit, so a lunar run there needs prefix ≤ 4 or a rounded `balBound`. Audits: AUDIT-C6-1, C6L8-1, C6B-1, C6L1-1 (PASS).
