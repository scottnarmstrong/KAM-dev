# SO-DESIGN handoff for an independent DESIGN audit (branch inp-design-so, 628569c9; main orchestrator)


**Files.** `docs/tracks/SO/design/SO-LEAN-DESIGN.md` (committed `628569c9` on `inp-design-so`; Appendix A
embeds the signatures); untracked `.drafts/design/SOSignatures.lean` (1007 lines), copied to
`/root/code/KAM-inp/.drafts/design/SOSignatures.lean`. No Lean module, frozen file, manifest, README or
KAM.lean touched.

**Checks.** `inp_sig_check.sh /root/code/KAM-inp-design-so .drafts/scratch/SOSignatures.lean` → rc 0,
109 warnings, all `declaration uses 'sorry'`, no error. `sh scripts/lint_sources.sh` → rc 0 (modules
PASS, frozen-anchor guard OK, ABI hashes OK). Axioms: n/a (no proofs). Short names checked against KAM:
the only hits are dotted API names (`CertPoly.add`, `TorusCertificate.K` …) and the SO-MODEL/SO-DIO stand-ins.

**Key decisions (§1).** (1) `HamExpr`: rational constants, `π`, actions, `cos/sin(2πk·θ)`, `+ × pow exp sin
cos`, no division: holomorphy, periodicity, translation invariance and reality are structural. (2) `D` =
strip × polydisc; ball margin certified. (3) Existing max/row-sum norms; new bridges from partials.
(4) Checker differentiates symbolically (straight-line program, forward-mode jets to order 3); the
certificate carries no derivative data; Cauchy-only bounds rejected (they cost ~6^30 in the constants).
(5) Fourier models = exact polynomial + sup radius on the open strip, weights `w ≥ e^{2πρ}` checked once.
(6) Symbolic `(2π)^deg` tagging generalizes the plan's π-free arithmetic. (7) `exp` and characters of `K`
via a-posteriori witnesses (`∂E = (∂g)E` residual + scalar pin), no Taylor series of models. (8) Gram
(bilinear) inverse by a Fourier-model approximate inverse and a uniform Neumann defect on the strip.
(9) Averaged bordered torsion: entry models (with `D(G⁻¹) = −G⁻¹ DG G⁻¹`), zero modes ± radius,
constant witness. (10) `IsDiophantine` is an input; `ω* ∈ ℚ(√d)ⁿ`. (11) Rational mirrors of
`isoC1/isoC2` with `c_R` bounded from `π`, `e`. (12) Kernel only, `decide +kernel`, structural recursion,
8 staged sub-checks. (14) Lunar headline: continuous barrier graphs, initial region = momentum window.

**Black box.** `checkTorusCertificate_sound (h) (hdio) : CertifiedTorus c` via `G1Hyps c` (every
`IG1Body` binder verbatim) and `g1_explicit (n, τ, ρ, ρ∞, M, σK, σB, σT, μ, γbar, σω, ν, ω*) :=
(n, c.tau, c.rho, c.rhoInf, c.M, c.σK, c.σB, c.σT, c.μ, c.γbar, c.σω, c.nuRay, c.ωstar)` applied to
`(c.D, c.H, c.K, c.s, c.γ, c.err, c.E0)`; the closeness bound is the checked rational `disp`.

**Packages (§7).** W1: SO-ARITH 1100, SO-POLY 1200, SO-MALG 1150, SO-EXPW 600, SO-EXPR 1500, SO-MAJ 800,
SO-EMB 800, SO-MAT 700, SO-CONST 700, SO-POS 350, SO-PI 500 (optional). W2: SO-TORS 1000, SO-DEFS 600,
SO-SOUND 1400, SO-CLOCK 400, SO-TEST 300, SO-GRAPH 800, SO-CONF 600. W3: SO-DATA (generated), SO-LUNAR 400.
≈ 16–17k hand-written (21–24k with overrun). SO-CONST, SO-CLOCK, SO-EXPR, SO-ARITH can start at once
(SO-ARITH's backend instance waits for SO-REPLAY).

**Upstream interfaces to reconcile.** SO-MODEL item 3 complex Hamiltonian (stand-in `soHamC`, angle
`(q, φ)`, action `(p, J)`); SO-DIO `lunarNu*_eq`, `lunarNu*_half_isDiophantine`; SO-GEN Lean data
emitter; SO-REPLAY backend verdict (§5 lists what it must show for ℚ / fixed point).

**Open questions for the owner (§11).** O1 momentum-window region vs `Q±` graph region (graph-error
transport deferred); O2 no division in v1; O3 high-precision π package now or later; O4 analytic graphs
and conjugacy outside the first freeze.

**Deviations from the sources (report for the ledger).** (a) Proposal §7.2 graph-error transport is not
needed for the headline under O1 (deferred, not dropped from the roadmap). (b) SO-MODEL's
`ScalarEmbedding` is off the black-box path: the general checker takes all four components of `K` as
Fourier data, the lunar `J` being the generator's Fourier approximation of `−p²/2 − V(K)` (energy error
then tiny, not identically 0). (c) Pilot §4 "the auxiliary action may be unrestricted": `IG1Body`'s
bounds quantify over `D`, so `D` is a bounded polydisc in `J` too (harmless: the bounds do not depend on
`J`). No suspected errata in pinned sources beyond the already recorded 3% band (D30).

**Uncertainties.** Kernel replay cost (SO-REPLAY pending); whether one exp witness per torus keeps the
pin radius `e^{2 sup|g|}` within slack (fallback: halving `E = F²`); jet size for large `n`.

THIS IS A DESIGN AUDIT, not a package audit of proofs. Inputs: the design docs/tracks/SO/design/SO-LEAN-DESIGN.md (on this branch), the draft signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean (also .drafts/design/SOSignatures.lean in this worktree), the plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md (owner decisions D30: 33/1000 band; FULLY GENERAL black box), the proposal /root/code/KAM/docs/explorations/lunar-spin-orbit-certificate-proposal.md and the pilot /root/code/KAM/docs/explorations/lunar-spin-orbit-feasibility-report.md, and the sealed engine KAM/Iso/Apost/G1.lean (g1_explicit) with KAM/Iso/Charts/Inputs.lean (IG1Body).

AUDIT FOCUS (refute-first; write docs/tracks/SO/audits/SO-DESIGN-design-audit-1.md):
1. Soundness shape: does checkTorusCertificate_sound, through G1Hyps, discharge EVERY binder of IG1Body exactly (compare binder by binder against KAM/Iso/Charts/Inputs.lean and g1_explicit's statement), with no conclusion-shaped or unprovable hypothesis smuggled into the certificate semantics, and with IsDiophantine as the only external mathematical input? Is the g1_explicit instantiation correct (parameter order, the reference vector, the ray scalar)?
2. Semantics: are the HamExpr denotation, the Fourier-model semantics (exact polynomial + sup radius on the open strip), the symbolic (2 pi)^deg tagging, the a-posteriori exp/character witnesses (residual + scalar pin), and the Gram/torsion approximate-inverse certificates mathematically sound as designed? Find any step whose claimed bound does not follow (e.g. sup radius on the OPEN strip vs closed-strip hypotheses of IG1Body; bilinear Gram on a complex strip; averaged torsion enclosure).
3. Generality: does the design really cover any n >= 2, any HamExpr Hamiltonian, general Fourier embeddings, as the owner decided? Is excluding division acceptable for v1 (owner question O2)?
4. Lunar client: does the plan reach the D30 statement (|p(t) - 1| <= 33/1000 for all t, global unique solutions, explicit initial region) with the design's O1 choice (momentum-window initial region; graph-error transport deferred)? Is deviation (b) (J as Fourier data, energy error tiny but nonzero) sound and within the pilot's margins?
5. Feasibility: are the package line estimates and the wave/dependency structure credible? Which packages can start before the replay gate (SO-REPLAY)?
6. Signatures: do they elaborate (re-run the check command the handoff names), follow AGENTS.md (modules, no EuclideanSpace, names not clashing with KAM), and match the design text?
Give a verdict PASS / PASS WITH NOTES / FAIL with numbered findings (severity, location, required change). Do not edit any file other than your report.

## Round 2 (design Revision 2, commit d2352a2d)

The designer's Revision 2 (section '## Revision 2' of docs/tracks/SO/design/SO-LEAN-DESIGN.md; mapping table in
.drafts/handoff-SO-DESIGN.md, Revision 2 section) answers audit 1's F1-F6 and the owner's rulings O1-O4 from
/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md (O2: division in the expression language now; O3: the
high-precision pi package now, landed as KAM/Certificate/Arith/PiHigh.lean). The draft signatures are
/root/code/KAM-inp/.drafts/design/SOSignatures.lean (1337 lines). Landed track SO modules the design now imports:
KAM/SpinOrbit/{Model,PeriodOne,Hamiltonian,ScalarEmbedding}, KAM/Certificate/{QuadraticDiophantine,PhaseBasis,
Clock}, KAM/Certificate/Arith/PiHigh.

ROUND 2 FOCUS: (1) is each of F1-F6 actually closed (F1 especially: does the exact-real frequency with a proved
rational enclosure and IsDiophantine as the external input make n >= 3 certificates non-vacuous, and does the
soundness theorem still discharge every IG1Body binder)? (2) is the division extension sound: the denotation of
HamExpr.div, the NonvanishingOn certification by ball arithmetic on the whole domain D, holomorphy/periodicity/
reality and the jets being conditional on nonvanishing? (3) is the pi interface consistent with the landed
PiHigh module? (4) any NEW blocking issue introduced by the revision; (5) re-run the signature check. Verdict and
numbered findings as in round 1.

## Round 3 (design Revision 3, commit b442a912)

Revision 3 (section '## Revision 3' of the design; mapping in .drafts/handoff-SO-DESIGN.md) answers round 2's F7
(torsionAvgCheck takes n and checks exact (n+1)x(n+1) shapes; ModelMatrix.HasShape), F8 (1 <= n on the two
NormBridge bounds), F9 (corrected J-row identity E(K~)_J = E(K0)_J - D DeltaJ and the budget), and the F3/F6
residuals (instCertArithRat moves to pre-gate SO-AIF). Signatures: /root/code/KAM-inp/.drafts/design/SOSignatures.lean
(1360 lines). ALSO evaluate one deviation found by the SO-AIF prover (orchestrator ruling 12:10): the signed
certCExp_sound (no size hypothesis) is false; the replacement certCExp_sound_of_small (hypothesis
norm(z) + val zRad <= 1) with the checkable test certCExpSmall is in /root/code/KAM-inp-soaif/KAM/Certificate/Arith/
Roots.lean; check that every consumer of certCExp in the design only needs small balls (or argument reduction) and say
what the design must change.

ROUND 3 FOCUS: are F7, F8, F9 and the F3/F6 residuals closed? Is the certCExp change compatible with the design's uses?
Any new blocking issue? Re-run the signature check. Verdict and numbered findings.

## Round 4 (design Revision 4, commit 5767956a)

Revision 4 answers round 3's single blocking finding F10 (section '## Revision 4' of the design; mapping in
.drafts/handoff-SO-DESIGN.md). The orchestrator fixed the general primitive's signature (`certCExpReduced`,
`certCExpReduced_sound`, an Option-returning range-reduced complex exponential whose successful call is sound with no
size hypothesis); package SO-CEXP has proved it in /root/code/KAM-inp-socexp/KAM/Certificate/Arith/ComplexExp.lean
(separately audited). Signatures: /root/code/KAM-inp/.drafts/design/SOSignatures.lean (1494 lines).
ROUND 4 FOCUS: is F10 closed for EVERY consumer of your round-3 table (Slp.balls with cexpHalvings, the expWitness
scalar pin with per-witness halvings and the eps_0 budget including reduction, rounding and squaring errors,
character witnesses in Slp.compose)? Do the landed Roots.lean signatures appear verbatim? Is the fail-closed
contract stated on successful calls only, with no caller-side size hypothesis anywhere? Any new blocking issue?
Re-run the signature gate. Verdict and numbered findings.

## Round 5 (design Revision 5, commits 9de9c4bf, 8a08ba30, ecc4666c)

Revision 5 (section '## Revision 5' of the design; full handoff .drafts/handoff-SO-DESIGN-R5.md) implements:
owner ruling O5 (the lunar client in the rotated frame Q1 = q - phi, Q2 = phi, P1 = p, P2 = p + J; parameter package
R1; G-J restated); the advice-checked Kronecker-packed product architecture from SO-REPLAY2
(/root/code/KAM/docs/tracks/SO/studies/SO-REPLAY2-advice-sharded-products.md) for Poly/Ops and Model/Ops; the
orchestrator-fixed rotated Diophantine signatures (SO-ROTDIO) adopted verbatim; the signature file split into
/root/code/KAM-inp/.drafts/design/SOSignatures.lean (engine) and SOSignaturesLunar.lean (lunar client); design audit 4's
F11; a new §7.2 on data packaging that leaves an OWNER decision open (not a finding by itself).
ROUND 5 FOCUS: (1) the rotated client: is the final confinement statement unchanged in the original coordinates, is H'
exactly soHC composed with the symplectic map, are the clock and frequency facts right, does the exact-torus-to-barrier
wrapper use SO-GRAPHM's landed core correctly? (2) the advice-checked products: is the soundness contract of every
product the enclosure of the EXACT product (no trust in the advice), with packing/injectivity/remainder lemmas stated
and no conclusion-shaped premise? (3) both signature files elaborate and match the landed modules; (4) any new blocking
issue. Verdict and numbered findings.
