# Strong-AMD exponential safety: chaotic but collision-free planetary systems

Exploration for a co-author's proposal, 31 October 2026. This is a research report and campaign design note, not an
approved statement or a formalization receipt. **Status: proposed. Nothing here is proved in Lean.** A paper proof of
the target theorem is in [A8](A8-proof.md). **Update 2026-11-01:** an independent refute-first audit
([A10](A10-proof-audit.md)) found it **PASS WITH NOTES**: no gap, no error, 12 one-line notes (N1–N12) to apply before
freezing statements. The campaign is launched as track LP (D56).

The analyses summarized here were written on 31 October 2026 in the workspace
`/mnt/HC_Volume_106379410/kam-explore/amd-crossing/`, read-only against `/root/code/KAM` at commit
`f5625f197c621ccc8045e8392a07e23fe0cb10fc`. When this note was written the repository HEAD was `0084e98`; a read-only
`git diff --stat` between the two commits showed no change under the reused paths (`KAM/Nekhoroshev/Partial`,
`KAM/Planetary/{AMD,Exponential,Poincare,Newtonian}`, `KAM/Kepler`, `KAM/Frozen/{Planetary,Nekhoroshev}`,
`KAM/Provider/Planetary`), and `nf` (`Partial/NormalForm.lean:604`), `nonresonant` (`Partial/Nonresonant.lean:341`) and
`planetaryExponentialSafety` (`PlanetaryExponentialSafety.lean:53`) sit at the pinned lines.

Every number and claim below is quoted from the document it cites: "A4 §4.1" is appendix A4, section 4.1; "A8 L12" is
Lemma 12 of A8; "ORCHESTRATOR" is the orchestrator's assessment in the workspace.

## Documents in this folder

| File | Workspace source | Content |
|---|---|---|
| [README.md](README.md) | this note | summary, mathematics, proof status, decisions, plan, launch checklist |
| [A1-brainstorm.md](A1-brainstorm.md) | `BRAINSTORM-1.md` | independent brainstorm: mechanism, exact meanings, traps, literature, Candidates A and B |
| [A2-literature.md](A2-literature.md) | `RESEARCH/LITERATURE.md` | source pins and novelty verdict |
| [A3-gap-analysis.md](A3-gap-analysis.md) | `RESEARCH/GAP-ANALYSIS.md` | the repository against Candidate B; how P-EXP-SAFE is proved; size calibration |
| [A4-proof-plan.md](A4-proof-plan.md) | `RESEARCH/PROOF-PLAN.md` | paper-level proof plan reusing Track N; the cheaper Nek77 route |
| [A5-statements.md](A5-statements.md) | `RESEARCH/STATEMENTS.md` | candidate statement contracts; owner decision register |
| [A6-campaign-plan.md](A6-campaign-plan.md) | `RESEARCH/CAMPAIGN-PLAN.md` | phases, gates, packages, risks |
| [A7-practical.md](A7-practical.md) | `RESEARCH/PRACTICAL.md` | explicit constants, Solar System, exoplanet targets, certificate route |
| [A8-proof.md](A8-proof.md) | `PROOF/MAIN.md` | claimed complete proof: planar Theorem 15, spatial Theorem 19 (**unaudited**) |
| [A10-proof-audit.md](A10-proof-audit.md) | `AUDIT/PROOF-AUDIT-1.md` | independent refute-first audit of A8: PASS WITH NOTES |
| [A9-lean-roadmap.md](A9-lean-roadmap.md) | `PROOF/LEAN-ROADMAP.md` | Lean packages per lemma, dependency DAG, reuse map, sizes |

A1 is the first, independent brainstorm; A2–A7 are the parallel research analysis; A8–A9 are the proof attempt. The
appendices are verbatim apart from a provenance header, neutral naming of the co-author and internal labels, and
cross-references renamed to A1–A9.

## Summary

- **The proposal** (§1): for nonresonant semi-major axes and AMD below the Laskar–Petit collision threshold, the
  unaveraged (1+n)-body problem has no orbit crossing for a time exp(cμ^(−1/(2n+1))), with no hypothesis on the
  possibly chaotic secular dynamics. All analyses judge it very likely true once quantified (ORCHESTRATOR §1; A1).
- **Mechanism** (§3.6): exact angular-momentum conservation gives C(t) − C(0) = Σᵢ(Λᵢ(t) − Λᵢ(0)), so exponentially slow
  drift of the fast Kepler actions controls the *total* AMD whatever eccentricities and inclinations do; the strong AMD
  threshold then forbids crossing. No secular trajectory is shadowed (A1 §1).
- **Prior art** (§6): Laskar–Petit 2017 §3 states the principle as a conjecture. The mechanism is known; the sharp
  uniform-domain theorem is "plausibly new as a packaged statement, but novelty is unverified" (A2 §6). Niederman 1996
  and Pinzari 2013 remain unpaid source checks.
- **The repository** (§2) already proves a planar, crude-box, Nek77-exponent version, `planetaryExponentialSafety`
  (P-EXP-SAFE). The campaign upgrades it along four axes: the sharp strong threshold, the nonresonant exponent
  1/(2(τ+1)), space, and a no-orbit-crossing conclusion. No new normal-form engine is needed: Track N's `nf` and
  `nonresonant` already allow an arbitrary secular set (A3 §1).
- **Proof status** (§4): A8 claims complete paper proofs of planar Theorem 15 and spatial Theorem 19 (time
  T₀exp(cμ^(−1/(2(τ+1)))), drift O(√μ), half margin, canonical and osculating annulus gaps). It is **unaudited**; §4.5
  lists what an auditor should attack first.
- **Practicality** (§7): P-EXP-SAFE and the new theorem are both asymptotic (∃ μ*, c). Actual masses need explicit
  constants and a computer-assisted certificate, a separate phase. The full Solar System fails the premise: by
  Laskar–Petit 2017 §5.4.1 its inner part is AMD-unstable. Realistic targets are AMD-stable exoplanet models (HD 109271
  and HD 1461 first) and perhaps an isolated outer-planet model.
- **Plan** (§8): Phase 0 contract; Phase 1 planar sharp threshold; Phase 2 nonresonant exponent; Phase 3 spatial;
  Phase 4 osculating bridge; Phase 5 certificate pilot. Roughly 17–32k new Lean lines for the qualitative campaign (A6
  §2). The inputs disagree on which planar route comes first (§10).
- **Launch** (§9): audit A8; settle owner decisions; write the source manuscript; propose exact frozen Lean statements;
  build the dependency graph; start the infrastructure packages.

## 1. The proposal and why it matters

### 1.1 The proposal, verbatim

Forwarded by the project owner on 31 October 2026 (message lines 3–7, SHA-256 `04a2c8c4…6cd25`, A1 Scope):

> I was able to find a statement that could be interesting and very likely correct: "For non resonant semi major axes
> and any AMD below the Laskar Petit collision threshold the un averaged (1+n) body problem has no orbit crossing for a
> time exp(c mu^(-1/2n+1)) with no hypothesis on the secular dynamics which may be chaotic". This is the statement that
> one could lead the agents on. It means that planetary system can be chaotic but safe from collisions. So it really
> shows that chaos and stability are separate questions

The exponent notation is ambiguous; all analyses use the owner's reading μ^(−1/(2n+1)) (A1 Scope).

### 1.2 Why it matters: chaos and collision safety are separate questions

Secular dynamics (precession; exchange of eccentricity and inclination between planets) can be chaotic, and chaos
alone does not imply collision. The proposal isolates the one quantity that must stay controlled, the total AMD, and
controls it by two facts that do not involve the secular flow (ORCHESTRATOR §1; A1 §1): for nonresonant semi-major axes
a normal form removes the fast angles up to an exponentially small remainder, so the Kepler actions Λ drift only
exponentially slowly; and the total angular momentum is conserved exactly, so C = ΣΛᵢ − |L| moves only through Λ. Below
the strong Laskar–Petit threshold the radial annuli stay disjoint.

A1 §1 calls the key point "a crucial distinction": the proof must **not** make the full solution follow one secular
solution (a Gronwall comparison in a chaotic secular system fails much earlier); it estimates almost-conserved
quantities along the actual orbit, which contain no secular Lyapunov exponent. "This is precisely why chaotic secular
dynamics can coexist with the conclusion." Two limits (A1 §3): "Permitting chaos is not proving chaos" (no chaotic orbit
is constructed; the reduced planar two-planet secular problem is integrable, so a planar two-planet pilot shows no
secular chaos), and "No crossing is not a complete stability classification" (no ephemerides, nothing after the
horizon).

### 1.3 The Laskar–Petit conjecture

J. Laskar and A. C. Petit, *AMD-stability and the classification of planetary systems*, A&A 605, A72 (2017). The same
clause stands in the published §3, A72 p.3, and in arXiv:1703.07125v2 §3, p.4 (A2 §1):

> we conjecture that in absence of short period resonances, the AMD-stability ensures the practical long-term stability
> of the system.

A footnote after "practical" defines a time very long compared with the central star's expected lifetime. Neither
version supplies a quantified uniform theorem (A2 §1). A rigorous asymptotic version would address this principle; A2
§6 warns against advertising a "complete resolution of the informal LP conjecture".

### 1.4 What the sentence needs before it is a theorem

A1's verdict: "There is a very plausible and worthwhile theorem here, but the sentence is not yet a theorem statement."
Repairs (A1 verdict, §3): a **Diophantine condition** (γ, τ) on the initial Kepler frequencies ("nonresonant" alone
gives no power-law control); a **fixed positive margin** δ below the threshold, chosen before μ; a **specified element
convention**; **protection against stellar collision**, i.e. the *strong* threshold; and a fixed architecture (compact
set of ordered axes, fixed relative masses).

## 2. What the repository already proves

### 2.1 P-EXP-SAFE: the planar crude-box theorem

`KAM/Frozen/Planetary/Theorems/PlanetaryExponentialSafety.lean`: `planetaryExponentialSafety`, the "planar moving-Sun
specialization of Nek77 Thm 12.3" (ORCHESTRATOR §2). For an admissible `AMDBox` B there are μ*, c, C such that for
0 < μ < μ* and every initial datum in `LowAMDRegion B.mass B.innerLower B.innerUpper B.initialAMD`, a moving-Sun solution
exists on |t| ≤ exp(cμ^(−planetaryTimeExponent n)) and is an actual Newtonian solution; along it the orbit stays in a
larger `LowAMDRegion`, angular momentum is conserved, eccentricities stay below `B.ecc`, heliocentric distances lie in
[distance, radius], pairwise distances are bounded (`PairBounds`), and |keplerAxis(t) − keplerAxis(0)| ≤
Cμ^(planetaryDriftExponent n). Here `planetaryTimeExponent n = 2/(6n² − 3n + 14)` (Nekhoroshev 1977, (12.4)) and the
drift exponent is 3/(6n² − 3n + 14).

`AMDBox.Admissible` (`KAM/Frozen/Planetary/Defs/AMDBoxAdmissible.lean`) is a **crude** sufficient condition: every
planet may take the whole outer AMD (outerAMD < lowerᵢ(1 − √(1 − ecc²)) for each i), and the annuli
[a(1 − ecc), a(1 + ecc)] are separated by `distance` for all pairs. It is not the Laskar–Petit pair threshold.

### 2.2 How P-EXP-SAFE is proved

The declaration (line 53) is sealed by `KAM.Provider.Planetary.planetaryExponentialSafety` through
`planetaryExponentialSafety_of_expsafe` and the implementation `KAM.Planetary.expsafe`; no stability oracle is assumed.
The chain (A3 §3, under `KAM/Planetary/`): `Exponential/Enlargement.lean:enlarge` turns the strict box inequalities into
an enlarged fast box and slow AMD ball; `real_domain`, `ComplexTube.lean:tube` and `Perturbation.lean:perturbation` make
the unaveraged chart Hamiltonian an analytic perturbation with ν = B₀μ; `Exponential/Stopped.lean:stopped` (line 247)
applies **`partialConvex_nekhoroshev`** (Nek77 Thm 4.4, no Diophantine theorem) for a stopped drift ν^(bₙ)/2 through
ν⁻¹e^(ν^(−aₙ)); `AMD/Confinement.lean:amd` turns the stopped bound into existence, uniqueness, confinement and a
Newtonian solution via C(t) − C(0) = Σ(Λᵢ(t) − Λᵢ(0)), so "there is no independent secular stability hypothesis in the
headline theorem"; `Exponential/Safety.lean:expsafe` assembles. The existing theorem already has the "no secular
hypothesis" structure, with a crude box and the Nek77 exponent.

### 2.3 Other relevant declarations

- `AmdConfinement.lean:amdConfinement` (P-AMD-CONFINEMENT): the planar analogue of Candidate A; it consumes `AMDBox`, so
  it does not accept the sharp correlated region (ORCHESTRATOR §2; A9 §5).
- `Defs/PhysicalAMD.lean:physicalAMD` = Σ keplerAction − totalMomentum, planar prograde, citing LP17 (10)–(11), in
  normalized units (physical AMD is μC) (A3 §2).
- `SecularBoxSafety` (exact averaging, LP17 Appendix B, two-planet secular model); `secularBoxAtCitedMasses` proves
  safety of `exactSecularHamiltonian` at μ = 4773/5000000 = 0.0009546, μm_S = 0.0002856, "an honest actual-scale
  averaged-model theorem" that does not pay the fast averaging remainder (A7 §3).
- Track N: `Partial/Setting.lean:ExtNFHyp`, `PartialBlock`; `Partial/NormalForm.lean:nf`; `Partial/Preimage.lean:preimage`;
  `Partial/Nonresonant.lean:nonresonant`. They permit an **arbitrary real secular set S** with slow-bracket condition
  64πksr ≤ w² (A2 §3; A3 §5); `nonresonant` gives drift ≤ r/2 through (sr/(5ε))e^(2πKs/6), "conditional only on slow
  membership through the queried time" (A3 §2).
- `Exponential/ComplexTube.lean:tube` (line 165): periodic holomorphic extension of a compact safe real set; existence
  only; typed on `Phase (n+n)` (A3 §2; A4 §5). `Poincare/Chart.lean:poincareDom`: the planar chart on 0 < Λ,
  (ξ² + η²)/2 < Λ, "not merely a perturbative tiny-eccentricity ball" (A3 §2).

A3 §1: "The campaign needs **neither a new Nekhoroshev foundation nor a new fast-angle normal-form engine**." The
largest missing planar component is the sharp geometry and its uniform compact analytic domain; spatial coordinates,
the spatial Newtonian dictionary and actual-velocity osculating elements are substantial new work.

### 2.4 The four upgrade axes

| Axis | P-EXP-SAFE today | Proposed |
|---|---|---|
| Threshold | `AMDBox.Admissible`: all outer AMD to any one planet, one eccentricity cap, separated annuli | sharp strong Laskar–Petit threshold B = min(adjacent pair minima, Λ₁) on the whole system's AMD, fixed margin δ |
| Exponent | Nek77: time 2/(6n² − 3n + 14), drift 3/(6n² − 3n + 14), no arithmetic hypothesis | nonresonant 1/(2(τ+1)), drift O(√μ), Diophantine (γ, τ); τ = n − 1/2 gives 1/(2n+1); possibly keep both routes |
| Dimension | planar | spatial: inclinations, spatial regular Poincaré chart, invariable plane |
| Conclusion | pairwise distances (`PairBounds`), radius bounds, eccentricity cap | no orbit crossing: strict separation of radial annuli, canonical then actual-velocity osculating, plus distances |

Sources: ORCHESTRATOR §2; A5 §6; A8 §1. The upgrade is not a corollary: "an `AMDBox` can exclude points of the sharp
curved region" (A4 §7), and "A single old AMDBox can lose correlations between eccentricities and exclude legal states"
(A3 §4). The repair is a family of local fast boxes with **center-dependent full slow balls**; a single cutoff at
min_c B_c "would discard legitimate high-threshold initial states" (A4 §2.1).

## 3. The mathematics

### 3.1 Model and normalization

Units G = m₀ = 1; planet masses mᵢ = μνᵢ, 0 < νᵢ ≤ 1, maxᵢνᵢ = 1, so μ is the largest planet/star mass ratio. With
heliocentric positions qᵢ and scaled barycentric momenta pᵢ = Pᵢ/μ, translation reduction and division by μ give the
exact Hamiltonian (A1 (7); A4 (M); A8 (1))

```text
H_μ(q,p) = Σᵢ ( |pᵢ|²/(2νᵢ) − νᵢ/|qᵢ| ) + μ ( ½ |Σᵢ pᵢ|² − Σ_{i<j} νᵢνⱼ/|qᵢ − qⱼ| )
```

with physical time, the star's recoil, and no truncation (A1 §2); in the plane it is exactly
`Newtonian/Models.lean:movingHamiltonian_split` (A4 §1.1). Canonical Kepler elements use canonical velocity pᵢ/νᵢ and
parameter 1: Λᵢ = νᵢ√aᵢ, h(Λ) = −Σνᵢ³/(2Λᵢ²), ωᵢ = aᵢ^(−3/2) (A1 (8)). Warnings (A1 §2): LP17's μ denotes Gm₀; the
reduced-mass splitting is also legitimate but its elements "cannot be exchanged silently"; and canonical elements are
not velocity-osculating, since q̇ᵢ = pᵢ/νᵢ + μΣⱼpⱼ (A1 (17); A8 (10)).

### 3.2 The AMD and its identity

L = Σᵢ qᵢ × pᵢ and C = ΣᵢΛᵢ − |L| = ΣᵢΛᵢ(1 − √(1 − eᵢ²)cos iᵢ), inclinations relative to the invariable plane (A1 (9);
LP17 §2.2 (9)–(11)). Physical AMD is μC, so a fixed normalized margin δ is physical margin μδ (A8 §1). Since L is
exactly conserved (A8 L3):

```text
C(t) − C(0) = Σᵢ (Λᵢ(t) − Λᵢ(0)),        C ≥ Σᵢ Λᵢ D(eᵢ),   D(e) = 1 − √(1 − e²)
```

(A1 (1), (12); A4 (G4), (G6); A8 (13)). In space, after rotating L(0) to the z-axis, regular Poincaré variables give
C = ½Σᵢ(ξᵢ² + ηᵢ² + uᵢ² + vᵢ²) along the exact trajectory (A1 (5); A4 (S1); A8 L17), so a strong margin bounds a whole
secular region, not a neighborhood of the initial secular point. Conservation in a *formal* secular normal form does not
give infinite-time conservation of the physical AMD (A1 §2).

### 3.3 Pair threshold, strong threshold, barrier

**Pair threshold** as a compact minimum (A1 (10); A4 (G1); A8 (3)): for i < j, with aₖ = (Λₖ/νₖ)²,

```text
B_ij(Λ) = min { Λᵢ D(u) + Λⱼ D(v) :  0 ≤ u, v ≤ 1,  aᵢ(1 + u) ≥ aⱼ(1 − v) }
```

The endpoints make the feasible set compact; the minimum is attained at radial contact and equals LP17's contact
minimum (§3–3.2, (26)–(39)); divided by Λⱼ it is LP's *relative* threshold with α = aᵢ/aⱼ (A1 (11); A2 §1; A8 L4). The
campaign defines it as this absolute minimum, never through a numerical critical-root solver (A2 §1; A5 §2.1; A9 §1).

**Strong threshold**, including the star (A1 (13)–(14); A4 (G2); A8 (14)):
B(Λ) = min(min_{i<n}B_{i,i+1}(Λ), minᵢΛᵢ) = min(B_cross(Λ), Λ₁), because B_{i,i+1} < Λ_{i+1}. The **whole system's** AMD
is compared with each adjacent pair threshold, since secular exchange moves AMD between planets (A1 §2; A2 §1). Pair
safety alone does not protect the star: with a₁/a₂ = 0.1, Λ₁ = 0.01, Λ₂ = 1 the pair threshold is at least 0.4, while
AMD 0.02 already permits configurations approaching e₁ = 1 (A1 §3; LP17 §5.3). A finite-radius star (aᵢ(1 − eᵢ) > R★)
is not covered (A1 §2; A4 §6).

**Barrier**: C < B excludes every adjacent radial overlap and every radial orbit. On C ≤ B − η, eᵢ ≤ √(1 − (η/Λ_max)²),
aᵢ(1 − eᵢ) ≥ a_min η²/(2Λ_max²), and compactness gives a uniform positive adjacent gap (A4 (G5); A8 L5 (16)); with
η = δ/2, d★ = a_min δ²/(8I_max²) (A8 (41); A1 (40)). The criterion is sufficient, not necessary; nothing is claimed
above the threshold (A1 §2).

**The threshold moves** with Λ(t). Continuity comes from a fixed-interval parameterization of contact points (A4 (G3);
A8 (15)); proofs use the modulus Ω_B(r) = sup{|B(I) − B(J)| : ‖I − J‖∞ ≤ r} on a compact action set, not a Lipschitz
bound at e = 1 (A4 §1.2; A8 L6). The deterministic reduction (Candidate A, A4 (G7)): if ‖Λ(t) − Λ(0)‖∞ ≤ r and
C(0) ≤ B(Λ(0)) − δ, then B(Λ(t)) − C(t) ≥ δ − nr − Ω_B(r).

### 3.4 The Diophantine condition and the exponent

The hypothesis is on the **initial** radian Kepler frequencies only (A1 (18); A5 §6.2; A8 (5)):
|k·ω(Λ⁰)| ≥ γ|k|₁^(−τ) for all k ∈ ℤⁿ∖{0}, γ > 0, τ > n − 1; the repository has `KAM.IsDiophantine γ τ ω`
(`KAM/Frozen/Defs/IsDiophantine.lean`, A5 §1). Pairwise irrational ratios do not suffice: (1+√2, √2, 1) satisfies
ω₁ − ω₂ − ω₃ = 0 (A1 §2). Only a finite cutoff is used, and finite-order divisors persist on the action tube (A1 (26);
A8 (35)). Secular resonances are allowed: no secular divisor is inverted (A1 §3; A8 Thm 19).

The exponent (A1 (20)–(24)): divisor persistence on a tube needs M₂Kr ≲ α_K, averaging needs εK/(α_K r) ≲ 1; with
α_K = γK^(−τ) this gives K ≍ ε^(−1/(2τ+2)) and r ≍ √ε, hence |t| ≤ T₀exp(cμ^(−1/(2(τ+1)))) with ‖Λ(t) − Λ(0)‖∞ ≤ A√μ.
τ = n − 1/2 gives 1/(2n+1); τ = n gives only 1/(2n+2); no optimality is claimed (A1 §2). A4 (E1)–(E3) make the choice
explicit for the repository engine (p = q = 2, ε = μF, K = (γ₁²/(4096Lε))^a, α = γ₁K^(−τ), r = α/(4LK) = 16√(ε/L),
γ₁ = γ/(2π)). A8 L12 uses its own normal form with r = √μ, N = ⌊κμ^(−a)⌋, vector-field norm ε = M₁√μ and the iteration
condition AεN^(τ+1) ≤ q_D, which holds because a(τ+1) = 1/2. The Nek77 alternative (`partialConvex_nekhoroshev`) needs
no arithmetic hypothesis and covers resonant mean motions, with exponents 2/(6n² − 3n + 14) and 3/(6n² − 3n + 14) (A4
§7).

### 3.5 What "no orbit crossing" means

A1 §2 separates (1) disjoint radial annuli of the canonical instantaneous ellipses, aᵢ(1 + eᵢ) < a_{i+1}(1 − e_{i+1});
(2) disjoint radial annuli of the genuinely osculating ellipses (actual velocity, parameter kᵢ = 1 + μνᵢ); (3) actual
distances bounded below. (1) implies (3) since |qⱼ − qᵢ| ≥ ||qⱼ| − |qᵢ||; (2) needs a uniform O(μ) comparison on the safe
compact set, pointwise and not growing with the horizon (A4 §6; A5 §7; A8 L16). A8 §1: "**no orbit crossing** means the
strict ordering of the entire instantaneous radial annuli in (9), first for canonical elements and then for
actual-velocity osculating elements. It is stronger than separation of the current positions." Collision avoidance is
weaker than non-crossing: resonant phase protection can keep crossing ellipses collision-free (A1 §2).

### 3.6 The mechanism

Normal form with evolving secular variables z (A1 (2)–(4)):

```text
H_μ ∘ Φ = h(J) + Z_μ(J, z) + R_μ(J, θ, z),   ∂_θ Z_μ = 0,   J̇ = −∂_θ R_μ,   ‖J(t) − J(0)‖∞ ≤ M_R μ |t| e^(−κK)
```

Z_μ may be chaotic; only R_μ enters the drift. The normal form is built on the **entire enlarged strong-AMD sublevel**:
A4 (D1) uses S_c = {A(x) ≤ B_c − δ/2} with an analytic collar up to B_c − δ/4, A8 (21) the ball
𝒵₀ = {|z|²/2 ≤ B(I⁰) − δ/4}. A first-exit argument closes the loop: on the stopped interval inside the domain the
stopped estimate bounds the drift, the AMD identity strictly improves the margin, and compact continuation excludes
every finite endpoint (A4 §4.2 (E4)–(E5); A8 L14). It is not circular: the estimate is used only on segments already
inside the domain (A4 §4.2).

### 3.7 The key obligations

| # | Obligation (A1 §1) | Planned in A4 | Claimed in A8 |
|---|---|---|---|
| 1 | exact translation-reduced Hamiltonian h(Λ) + μf, element conventions | §1.1 | L1, L2 |
| 2 | margin below every pair threshold gives disjoint annuli; star barrier | §1.2–1.3 | L3–L5 |
| 3 | complex analytic neighborhood of the enlarged safe set; bounds on Hamiltonian and maps | §2 ([OPEN RISK] family packaging) | L7, L8 (plane); L17, L18 (space) |
| 4 | finite-order nonresonance; exponential averaging with evolving secular variables | §3 (Track N `nf`) | L9–L12 (own proof); L13 (Track N) |
| 5 | integrate the exponentially small fast drift, both coordinate changes | §3 (N3) | L11, L12 |
| 6 | original elements; AMD identity; moving threshold | §1.4, §4.2 | L3, L6, L14 |
| 7 | non-circular first exit (domain exit, margin loss, collision) | §4.2 | L14 |
| 8 | actual separation; actual-velocity osculating ellipses | §6 | L16 |

The "first unresolved analytic obligation" of A1 §6 is "a uniform exponential fast-angle normal form on the entire
enlarged strong-AMD sublevel, with the bounds needed by the first-exit argument". A4 §8 reduces it to full-product safe
compactness, uniform analytic extension with a Fourier bound, and the existing `nf` with fixed physical slow width and
r ≍ √μ; A8 L8–L12 claims a full proof.

### 3.8 Traps recorded by the brainstorm

A1 §3 lists the traps the formulation above avoids: reading "any AMD below threshold" uniformly as the gap tends to
zero (fix δ before μ); a threshold evaluated only at t = 0 (use Ω_B); pair stability without the star (use B); demanding
uniformity up to e = 1 (constants depend on the compact safe region); ignoring that inclinations consume AMD (and that
C < minᵢΛᵢ forces every orbit prograde relative to L); repairing proper degeneracy with a steep secular Birkhoff form
(average fast angles on a bounded secular domain instead); all-orders nonresonance at later times (use a finite order on
a narrow tube); an architecture drifting with μ (fix a compact set of ordered axes and the relative masses). The
Clarke–Féjoz–Guardia instability lives in a hierarchical four-body regime; it is not a counterexample to the
fixed-geometry candidate but rules out unrestricted stability slogans.

## 4. Proof status

### 4.1 What A8 claims, and the warning

A8, "Result" (notation rendered): "The planar theorem is proved in Theorem 15; the spatial theorem is proved in Theorem
19. Both have the sharp strong Laskar–Petit threshold, a fixed positive margin, action drift at most a constant times
√μ, and time exp(cμ^(−1/(2(τ+1)))). Neither assumes anything about secular stability. These are paper proofs, not new
Lean certificates. No assertion about novelty, useful numerical mass thresholds, or perpetual stability is made."
`PROOF/OPEN.md` reads "None"; A8 §8 lists "Unresolved mathematical lemma in this proof: None".

> **Unaudited.** This proof is the self-assessment of one analysis; in its own words, "All these checks are
> mathematical self-review, not independent peer review or a Lean run" (A8 §7). Treat it as *claimed complete,
> unaudited*: no frozen statement, graph node or package may count it as a proved supplier until an independent
> refute-first audit has passed (§9, step 1). SHA-256 of `PROOF/MAIN.md` at the time of writing:
> `309e9eb38e3f12b24961c60e0aa84e580e4117c6998c69ffbfdfea665580e6ea`.

Approach (A8 introduction): average about the **linear** Hamiltonian with the initial Kepler frequencies, in a norm of
Hamiltonian vector fields, treating the nonlinear Kepler term as part of the perturbation on an action tube of radius
√μ; A8 calls this "a particularly short proof with arbitrary canonical slow variables and a fixed complex collar around
their entire allowed real set". Lemma 13 checks the already implemented Track N route, which the Lean campaign can reuse
instead of formalizing Lemmas 9–12.

### 4.2 The statements, quoted exactly

The common conclusion (A8 §1, verbatim):

> **The common conclusion of Theorems 15 and 19.** There are positive constants
> \(\mu_0,c,T_0,A_I,A_a,d_\star,d_{\rm pair},A_{\rm osc}\), depending only on \((d,n,\nu,\mathcal A,\delta,\gamma,\tau)\), such that for every \(0<\mu\le\mu_0\) and every initial state with \(q_i\ne0\), \(E_i<0\),
> \[
>  a(0)\in\mathcal A,\qquad (5),\qquad C(0)\le B(I^0)-\delta,              \tag{6}
> \]
> the unique maximal solution of (1) exists on \([-T_\mu,T_\mu]\), where
> \[
>  T_\mu=T_0\exp(c\mu^{-a}),\qquad a={1\over2(\tau+1)}.                  \tag{7}
> \]
> Initial pair collisions are excluded by (6), as proved below. On this interval the state is elliptic, \(I(t)\in\mathcal Q\), and
> \[
>  \|I(t)-I^0\|_\infty\le A_I\sqrt\mu,\qquad
>  \|a(t)-a(0)\|_\infty\le A_a\sqrt\mu,
> \]
> \[
>  |C(t)-C(0)|\le nA_I\sqrt\mu,\qquad
>  C(t)\le B(I(t))-\delta/2,                                      \tag{8}
> \]
> \[
>  a_i(t)(1-e_i(t))\ge d_\star,\qquad
>  a_{i+1}(t)(1-e_{i+1}(t))-a_i(t)(1+e_i(t))\ge d_{\rm pair}.       \tag{9}
> \]
> Actual star distances and all planet-pair distances have the respective lower bounds in (9). The velocity-osculating elements defined in Lemma 16 have perihelion and aphelion radii within \(A_{\rm osc}\mu\) of the canonical ones; after the stated choice of \(\mu_0\), their star and adjacent-annulus gaps are at least \(d_\star/2\) and \(d_{\rm pair}/2\).

Here (1) is the Hamiltonian of §3.1, (5) the Diophantine condition of §3.4, d ∈ {2, 3}, 𝒬 the ordered positive action
chamber; the data are n ≥ 2, νᵢ > 0 with maxᵢνᵢ = 1, a compact 𝒜 ⊂ {0 < a₁ < ⋯ < aₙ} (the empty set allowed), δ, γ > 0,
τ > n − 1 (A8 §1).

> **Theorem 15 — planar nonresonant exponential safety.** The conclusion of §1 holds in dimension two for precisely
> hypotheses (6).

> **Theorem 19 — spatial nonresonant exponential safety.** The conclusion of §1 holds in dimension three for precisely
> hypotheses (6), including circular or coplanar initial orbits.

A8 §1 adds: "Setting τ = n − 1/2 gives exponent 1/(2n+1)", and the theorem concerns "all phases and all allowed secular
states, not a selection of invariant tori".

### 4.3 Lemma list (status as claimed by A8)

| Lemma | Content | Claimed status |
|---|---|---|
| 1 | (1) is the zero-momentum translation reduction divided by μ, same time; explicit Newtonian reconstruction | proved here |
| 2 | e² = 1 + 2E\|q×v\|², \|q×p\| = I√(1−e²), a(1−e) ≤ \|q\| ≤ a(1+e) | proved here |
| 3 | L constant; C ≥ 0; C < B★ forces L ≠ 0 and positive projections Hᵢ; AMD identity (13) | proved here |
| 4 | thresholds attained, positive, continuous; B_ij < I_j; B = min(B_cross, I₁); equal to LP's relative critical AMD | proved here |
| 5 | uniform strong barrier: perihelia and adjacent gaps uniformly positive on {C ≤ B − m}; compact nonsingular set | proved here |
| 6 | moving threshold C(t) ≤ B(I(t)) − δ + nr + Ω_B(r); continuation past finite endpoints (Picard) | proved here |
| 7 | regular planar chart on I > 0, Γ < I: real-analytic, symplectic, onto, regular at circular orbits | proved here |
| 8 | whole-sublevel planar analytic neighborhood with fixed widths; denominators via bilinear w·w | proved here |
| 9 | vector-field Fourier norm; commutator bound ‖[V,W]‖ ≤ (2D/σ)‖V‖‖W‖; tails | proved here |
| 10 | cohomological equation with linear h₀; Lie step with remainder (27), B_D = 16eD | proved here |
| 11 | exponential normal form on the full slow set: AεN^(τ+1) ≤ q_D gives remainder ε2^(−N); map and inverse | proved here |
| 12 | r = √μ, N = ⌊κμ^(−a)⌋; drift ≤ r/4 for \|t\| ≤ exp(cμ^(−a)); finite divisors persist (35) | proved here |
| 13 | same data fed to `KAM.Nekhoroshev.nonresonant`: r = D₀√μ, K ≍ μ^(−a), conditions (37) | "proved specialization; repository use is read-only, without a fresh build or certificate audit" |
| 14 | first exit on the entire allowed secular ball; budget (39) nr + Ω_B(r) ≤ δ/4 | "proved internal assembly lemma" |
| Thm 15 | planar theorem | proved here |
| 16 | actual-velocity osculating elements within O(μ) of canonical ones; half gaps | proved here |
| 17 | regular spatial Poincaré chart on Γ + Z < I via rotation (46); regular at circular and coplanar orbits | proved here |
| 18 | spatial whole-sublevel complex domain; off-level points safe since C ≤ C_e₃; one fixed rotation per solution | proved here |
| Thm 19 | spatial theorem | proved here |

### 4.4 How A8 relates to the proof plan A4

A4 reduces the analytic obligation to the repository's `nf` ((N1)–(N3)) and marks [OPEN RISK] the family packaging of
the complex extension (§2.3), the regular spatial chart (§5, spatial "conditional" in §8) and explicit constants. A8
proves its own normal form (L9–L12), claims to close the planar domain (L8) and the spatial chart (L17–L18), checks the
Track N route (L13), and reports that A4/A5's "full-ball, weighted-bracket and moving-threshold mechanisms agree with
the construction here" (A8 §7). A8 does **not** prove the Nek77 strong-threshold theorem of A5 §6.1: that route
"remains useful for a separate resonance-tolerant upgrade, with a different exponent; this document does not label that
upgrade proved" (A8 §7). Its only paper source is the [ADAPTED] sketch in A4 §7.

### 4.5 Where an auditor should attack first

Ordered by expected risk. Items 1–9 come from A8's self-refutation table (§7) and A4's open-risk markers; items 10–12
are consistency points found by reading the inputs side by side.

1. **L12, the exponent.** The rate rests on treating h − h₀ (size O(r) in the angle component) as perturbation of the
   *linear* h₀, with ε = M₁√μ a vector-field norm, and on paying the supremum-to-Fourier conversion once on a fixed
   strip. Check A8's answers to "Fourier summation adds n to the Diophantine exponent" and "Cauchy estimates cost two
   derivatives per averaging step". This departs from the Pöschel-type scheme of A2 §3 and A4 §3.
2. **L10.** The divisor ik·ω(I⁰) is constant in every variable and divides every component of X_f; the identity
   L_χh₀ = −f^osc is used before estimating (29); constants are claimed independent of r, b, Z, I⁰ and the scaled
   symplectic coefficients; the "no missing scalar convergence issue" paragraph.
3. **L11.** The inverse on 𝒟_{3/2} by negative-time flows; telescoped displacement ≤ 1/32; both action errors ≤ r/16.
4. **L8 and L18.** Uniform complex extension over the center-dependent family of full slow balls; gluing by the identity
   theorem; the bilinear estimate |w·w − |w₀|²| ≤ 2Qη_q + η_q² for every denominator. A4 §2.3 marked this an open risk.
5. **L17.** Symplecticity extended from the dense set e > 0, Z > 0 by analyticity; analytic inverse at coplanar points;
   the rotation (46). A4 §5 and A6 Phase 3 name the spatial chart the main spatial risk; A9 §3, the "Main new hard
   package".
6. **L18.** Off-level points of the ball are safe because the fixed-plane deficit C_e₃ bounds the eccentricity AMD;
   one fixed rotation per solution; rotation-invariant constants.
7. **L14.** Non-circularity: the stopped interval (40), the order of choosing U, r, μ₀ in (39), backward time, and that
   every stopped point lies in 𝒟₁ "using the **whole** ball (21)".
8. **L13.** The interface with `nonresonant`: its stopped premise covers only the interval through the queried time;
   the 2π factors (θ = λ/(2π), Ĥ = H/(2π), γ/(2π)); the weighted bracket c_s = 2π/ℓ²; signs (ξ, η) = (x, −y) and
   (u, −v); the inequalities (37). A8 marks it "without a fresh build".
9. **Constants.** A8's row "Constants depend on μ through hidden eccentricity or separation cutoffs": every collar must
   come from (n, ν, 𝒜, δ) before μ.
10. **Planar AMD and orientation.** A8 uses C = ΣI − |L| and reverses the plane when needed; the repository's
    `physicalAMD` is planar prograde (signed), and A5 §2.1 item 11 adds a `ProgradeElliptic` premise. The frozen
    statement must say which is meant.
11. **Hypotheses (6).** A8 assumes only qᵢ ≠ 0 and Eᵢ < 0 besides (6); ellipticity, no initial collision and L ≠ 0 are
    derived (L3, L5). Confirm each derivation before a statement omits these premises.
12. **The Nek77 route** (A5 §6.1, A6 Phase 1) has no proof in A8. If it stays Phase 1 it needs its own audited paper
    proof; A4 §7 notes that the erosion `innerCore D` of Track N's source "must be supplied by the reserved physical
    slow collar".

Lemmas 1–6 and 16 are elementary; A1 §6 judges the constrained optimization "not the dominant obstacle".

## 5. Candidate frozen statements and owner decisions

All Lean below is **unapproved and unelaborated** (A5 and A9 preambles). New statements are new anchors; P-EXP-SAFE
stays byte-identical (A5 §6.1; A6 Phase 0).

### 5.1 New definitions (A5 §2)

Sharp geometry (`OrderedAxes`, `NormalizedMasses`, `axisOfAction`, `circularAction`, `eccDeficit`, `lpPairFeasible`,
`lpPairThreshold`, `lpStrongThreshold`, `ActionCube`, `robustStrongThreshold`, `PlanarLPInitial`,
`CanonicalAnnuliSeparated`); spatial counterparts (`spaceCross`, `spatialKepler*`, `spatialTotalMomentum`, `spatialAMD`,
`SpatialElliptic`, `spatialMovingHamiltonian`, `IsSpatialMovingSolutionOn`, `barycentricPositions3`,
`IsNewtonSolutionOn3`, …); time and outcome (`expHorizon c a μ = exp(cμ^(−a))`, `nonresTimeExponent τ = 1/(2(τ+1))`,
`keplerFrequency a i = aᵢ^(−3/2)`, `PlanarLPOutcome`, "never an input assumption"); osculating (`heliocentricVelocity`,
`osculatingAxis`, `osculatingEccVector`, `OsculatingAnnuliSeparated`). Reused unchanged: the planar canonical elements,
`ProgradeElliptic`, `physicalAMD`, `totalMomentum`, the moving-Sun and Newtonian solution predicates, `actualMasses`,
`KAM.IsDiophantine` and the Nek77 exponents; the planar `totalMomentum` and `IsNewtonSolutionOn` cannot serve in space
(A5 §1). The threshold is a compact minimum, attainment being a theorem obligation, not an assumed field (A5 §2.1):

```lean
noncomputable def lpPairThreshold (m a : Fin n → ℝ) (i j : Fin n) : ℝ :=
  sInf ((fun uv : ℝ × ℝ =>
      circularAction m a i * eccDeficit uv.1 +
      circularAction m a j * eccDeficit uv.2) '' lpPairFeasible a i j)
```

A9 §1 puts the same object on an `OrderedActions ν` carrier, defined after a characterization theorem, with "no
fallback outside `OrderedActions`".

### 5.2 Barrier and Candidate A (A5 §§3–4)

`lp_barrier_of_eccentricity_budget`: for ordered axes, eᵢ ∈ [0, 1], Σ circularActionᵢ·eccDeficit(eᵢ) ≤ C < B, all
periapses are positive and adjacent annuli strictly ordered; a quantitative compact corollary fixes d, R, e_max before
a, e, C. **Candidate A** (planar and spatial): along any path of elliptic states with actions in an admissible cube of
radius r around I₀, conserved angular momentum, and C(z₀) ≤ robustStrongThreshold − η, one has C ≤ B − η and separated
canonical annuli at every time. Its supplied action bound is the input of a deterministic implication and "is **not**
an assumption to be carried into Candidate B" (A5 §4).

### 5.3 The dynamical anchors (A5 §§5–7)

- **§6.1 `planarStrongLPExponentialSafety`** (Nek77 route): no nonresonance assumption; horizon
  `expHorizon c (planetaryTimeExponent n) μ`; drift exponent `planetaryDriftExponent n`; supplier
  `partialConvex_nekhoroshev`.
- **§6.2 `planarStrongLPNonresonantSafety`**: binders n ≥ 2, `NormalizedMasses m`, compact nonempty A of
  `OrderedAxes`, δ γ > 0, τ > n − 1; then `∃ μstar c DΛ Da d R eMax` (positive, eMax < 1) such that for all
  0 < μ < μstar and every `z0 : Phase (n * 2)` with `PlanarLPInitial m A δ z0` and
  `KAM.IsDiophantine γ τ (keplerFrequency (keplerAxis m z0))` there is a path z with
  `PlanarLPOutcome m μ δ z0 (expHorizon c (nonresTimeExponent τ) μ) DΛ Da (1/2) d R eMax z`. The arithmetic premise
  concerns only the initial Kepler frequency.

- **§6.3 `spatialStrongLPNonresonantSafety`**: the same quantifiers with `Phase (n * 3)`, `SpatialLPInitial`,
  `spatialKeplerAxis`, `SpatialLPOutcome`; no reference-plane or inclination premise; 2n slow pairs, n fast angles.
- **§7 osculating corollary**: under the same premises, `OsculatingAnnuliSeparated m μ (z t)` on the whole window, with
  gaps at least d/2.

`PlanarLPOutcome` (A5 §5) bundles existence, uniqueness and Newtonian reconstruction on [−T, T], prograde ellipticity,
ordered axes, conserved L, C ≤ B − δ/2, eᵢ ≤ eMax < 1, periapses and adjacent gaps ≥ d, apoapses ≤ R, and action and
axis drift ≤ D_Λμ^b, D_aμ^b. A9 §2 states the same theorem as `planar_strongAMD_exponentialSafety` with premises qᵢ ≠ 0
and specific energy < 0 instead of `ProgradeElliptic`, constants μ₀ c T₀ AΛ Aa dStar dPair Aosc, μ ≤ μ₀, and the
osculating conclusions in the headline; it must not add prograde, small-inclination, nonzero-momentum,
secular-confinement, normal-form or stopped-action hypotheses.

### 5.4 Owner decisions

From A5 §9 (recommended contract; consequence of another choice):

| Decision | Recommended contract; consequence of another choice |
|---|---|
| Coordinates | heliocentric canonical Poincaré, exact recoil Hamiltonian; Jacobi needs a different element/AMD dictionary and bridge |
| Threshold | strong LP threshold with fixed absolute normalized margin δ; the weak threshold permits stellar collision and lacks the analytic compactness |
| Mass scaling | star = G = 1, masses μmᵢ, fixed positive m, max m = 1; general star/G via a dimensional corollary |
| Arithmetic | free τ > n − 1, fixed γ > 0, initial radian Kepler frequency; a τ = n − 1/2 corollary for 1/(2n+1); internal γ/(2π) |
| Time form | symmetric \|t\| ≤ e^(cμ^(−a)), normalized physical time; a prefactor must be declared |
| Crossing notion | strict separation of instantaneous radial annuli plus the actual-velocity osculating corollary; finite radii need more data |
| Initial data | canonical full phase state, all planets included; observational osculating boxes need a verified input adapter |
| Uniformity | compact 𝒜, fixed δ, masses and arithmetic constants, all phases and secular states; δ → 0 changes the statement |
| Sequence | planar sharp-LP Nek77 first, nonresonant planar second, spatial third; spatial-first delays the cheapest theorem |
| Relation to P-EXP-SAFE | new separately versioned anchor and provider; P-EXP-SAFE must not be edited or broadened |
| Quantitative deliverable | separate finite-cutoff certificate theorem after qualitative closure; existential μ* gives no practicality |

Further decisions raised by disagreements between the inputs (§10):

- **Phase 1 route**: Nek77 strong-LP first (A5 §9; A6 Phase 1; no arithmetic hypothesis, resonant frequencies
  included, but no audited paper proof) or nonresonant planar Theorem 15 first (A9 §6; backed by A8 if the audit
  passes; uses `nf`/`nonresonant` directly); and whether to keep the Nek77 theorem as a resonance-tolerant companion.
- **Planar premise**: a `ProgradeElliptic` premise with the signed `physicalAMD` (A5) or qᵢ ≠ 0, Eᵢ < 0 with
  C = ΣΛ − |L| (A8, A9).
- **Constant packaging**: A5 (μstar, c, D_Λ, D_a, one d, R, eMax; μ < μstar; no prefactor; osculating separate) or
  A8/A9 (μ₀, c, T₀, A_I, A_a, d★, d_pair, A_osc; μ ≤ μ₀; osculating in the headline).
- **Scope** of the first deliverable: whether spatial and osculating statements are mandatory or staged.

For the co-author (A5 §9; A6 §7): confirm that "no secular hypotheses" means unrestricted evolution inside the
strong-AMD budget, not stability of the averaged motion; that a fixed δ is acceptable; which statements the first paper
needs; the intended publication claim; known sharp-domain prior art; a check of the spatial full-ball argument; whether
an isolated published exoplanet model is a useful first practical target.

## 6. Literature and novelty

Pins from A2 (verified there unless marked):

| Source | Pin | Role and boundary |
|---|---|---|
| Laskar–Petit, A&A 605, A72 (2017); arXiv:1703.07125v2 | §2.1 (2)–(8) split; §2.2 (9)–(11) AMD; §3–3.1 (26)–(34) contact; §3.2 (35)–(39) critical value; §5 (58); §5.3 strong/weak; §5.4.1, Figs. 8–9 | conjecture in §3 (published p.3, arXiv v2 p.4); geometry re-proved in A8 L2–L5 |
| Niederman, Nonlinearity 9 (1996) 1703–1751 | **original not inspected** | mechanism prior art via CFG24 §1.3 and BN20; theorem number, domain, exponents unverified; "a literature gate for any novelty claim, not a blocker" |
| Pöschel, Math. Z. 213 (1993) | Normal Form Lemma, p.192; proof pp.193–196 | no secular pairs: "treating those pairs as passive parameters would omit their Poisson-bracket derivatives" |
| Barbieri–Marco–Massetti, CMP 396 (2022) | App. B, Lemma B.1, p.380, (B.1)–(B.5) | action-angle form without secular pairs; zero module only |
| Pinzari–Liu, J. Nonlinear Sci. 33 (2023); arXiv:2302.00279v2 | §3.4, Prop. 3.2 pp.30–31; Lemma 3.3 p.31 | independent slow-variable normal form |
| Track N (repository) | `ExtNFHyp`, `nf`, `nonresonant`; nodes `bpN:p11:nf`, `bpN:p11:nonresonant` | "the decisive finds": arbitrary real secular set S |
| Castan, thesis (2017), HAL tel-01597143 | Props. 1.3 (p.25), 1.5 (p.28), 1.8 (p.39); Thm 1.9 (p.40, (1.43)) | route to explicit complex widths |
| Barbieri–Niederman, JDE 268 (2020); arXiv:1810.05987v1 | §3.3.2, Thm 7, pp.30–32; §3.3.3 p.32 | secular first exit via angular momentum; local near a periodic torus |
| Pinzari, Memoirs AMS 255 (2018); arXiv:1501.04470v4 | Prop. 5.1 pp.37–38; Prop. D.1 pp.77–78 | large eccentricities, hierarchical separation; not arbitrary strong-LP sublevels |
| Pinzari, RCD 18 (2013) | publisher abstract only | planar exponential stability of actions outside mean-motion resonances; **full theorem not inspected** |
| Clarke–Féjoz–Guardia, ARMA 248 (2024); arXiv:2303.05979v1 | Thm 1 p.4; §1.3 p.5; §8.1 | polynomial-time axis instability, hierarchical; prevents an overbroad theorem, not a counterexample |

**Verdict** (A2 §6): "the mechanism is known; the proposed sharp uniform-domain corollary is plausibly new as a packaged
statement, but novelty is unverified." No inspected source states the spatial strong-LP-sublevel theorem with uniform
constants, a fixed margin, arbitrary secular dynamics and the Diophantine exponent; "absence from this search is not
proof of novelty". A1 §4 agrees: "an established principle with a plausible rigorous quantitative formulation; novelty
unverified". **Safe description** (A2 §6): "A formalized strong-AMD refinement of planetary exponential safety, with a
nonresonant rate and a spatial extension." Do not advertise a new normal-form theorem, perpetual stability, a practical
actual-mass result, or a complete resolution of the informal LP conjecture.

## 7. Practicality

### 7.1 The owner's question and the answer

The owner asked (31 October 2026) whether the new campaign can be *practical*, applicable to real planetary systems at
actual masses, unlike the existing asymptotic theorem whose μ* is not explicit. A7's answer: "**A practical campaign is
worth a bounded numerical pilot, but neither P-EXP-SAFE nor the proposed qualitative Candidate B currently certifies a
real planetary system at its actual masses.**"

- Both theorems are asymptotic (∃ μ*, c): the analytic tube and perturbation normalization use compactness and give no
  usable numerical μ*, although the normal-form engine has explicit constants (A7 §1).
- Actual masses need explicit, certified physical inputs and units, AMD geometry, real and complex domain widths,
  Fourier norms, normal-form inequalities and final budgets (A7 §1): a separate computer-assisted phase (A6 Phase 5).
- The inner Solar System is AMD-unstable (§7.4), so **no version applies to the full Solar System**. Realistic targets
  are AMD-stable exoplanet systems (§7.5) and perhaps an isolated outer-planet model.

### 7.2 How small would μ* be from hand bounds

There is no universal numerical μ* depending on n alone (A7 §3). Illustration with the proof-plan choice
K = (γ₁²/(4096LFμ))^(1/(2(τ+1))), log T = πsK/6, and s = 0.02, γ₁ = 0.01, L = F = 1, log T = 30 (so K ≃ 2865):

| Fast dimension and arithmetic exponent | Mass bound from these choices alone |
|---|---:|
| n=2, τ=1.5 | μ ≲ 1.27×10⁻²⁵ |
| n=3, τ=2.5 | μ ≲ 1.54×10⁻³² |

"These are **illustrative arithmetic**, not estimates for any star and not universal upper limits." A few-Gyr horizon
for a several-day inner orbit is a logarithmic horizon of roughly 28–30. Historical comparisons (A7 §3): Barbieri–
Niederman 2020 (§5.1, Table 1) reach 5.75×10¹⁰ yr at ε = 10^(−11.25) in a reduced-mass planar Sun–Jupiter–Saturn model
and attribute about 4×10⁹ yr for ε < 10⁻¹³ to Niederman 1996; Castan's KAM example uses masses 10⁻⁸⁵m₀;
Giorgilli–Locatelli–Sansottera work in truncated or secular models, and per A7 their 2017 paper says on p.6 that the
result is not supported by a rigorous computer-assisted proof. "The historical reduced-mass values 10⁻¹³–10⁻¹¹ remain
many orders below Jupiter's approximately 9.55×10⁻⁴ ratio."

### 7.3 The explicit-certificate target

With `ExtNFHyp` conventions (p = q = 2, ε = μF), certify a finite-cutoff divisor bound α ≤ min_{0<|j|₁≤K}|j·ω_c/(2π)|
and (A7 §2, (P1)–(P2))

```text
KLr ≤ α/2,   μF ≤ αr/(256K),   64πksr ≤ w²,   2πKs ≥ 6,   nr/2 + Ω_B(r/2) ≤ δ/2,   T ≤ (sr/(5μF)) exp(2πKs/6)
```

plus collar, chart, inverse and osculating inequalities (k = n planar, 2n spatial). This yields "a **finite-time
actual-mass theorem without an infinite Diophantine hypothesis**"; an all-orders Diophantine premise cannot be
certified from decimal fits or observational intervals, which meet high-order resonance hyperplanes (A7 §2).

### 7.4 The Solar System

Laskar–Petit 2017, published §5.4.1, A72 p.9; Figs. 8–9, p.12; §6 (arXiv v2: §5.4.1, p.10; Figs. 8–9, p.14), checked
in both texts (A7 §4). LP17 says the giants' large AMD makes the **inner part of the full Solar System AMD-unstable**;
the outer dynamics is mostly quasiperiodic; Fig. 9 and §5.4.1 classify the Solar System as hierarchically AMD-stable
(outer part AMD-stable; inner part AMD-stable only when considered alone), "a subsystem classification, not a theorem
that their coupling can be ignored". Honest statements (A7 §4): an **isolated outer-planets Newtonian model** with a
verified margin can be a target (mass threshold unchecked; Jupiter–Saturn's near 5:2 makes it difficult); an
**isolated terrestrial model without giants** can be a target but does not describe the coupled inner system for
exponentially long times; the existing secular Sun–Jupiter–Saturn theorem at cited masses (§2.3) is a limited concrete
result; the **full eight-planet system does not satisfy the global strong-AMD premise**: "No amount of improving
normal-form constants fixes that premise." "AMD-unstable means this sufficient barrier fails; it does not assert a
collision occurs."

### 7.5 Exoplanet candidates (table verbatim from A7 §5)

Floating-point screening (`_sources/target_margins.py`, no outward rounding): "These calculations are screening, not
proof that B exceeds a certified bound."

| System; pinned fit | Periods (days), inner to outer | \(m\sin i\) (Earth masses); axes (AU) | Eccentricities used | \(B; C_p\) in \(M_\oplus\sqrt{AU}\) | \(\beta_p\); margin |
|---|---|---|---|---|---|
| **HD 109271**, Lo Curto et al.2013 Table2, p.7 | 7.8543, 30.93 | 17,24; .079,.196 | .25,.15 nominal | 1.46052; .27194 | .1862; **81.4%** |
| **HD 1461**, Díaz et al.2016 Table5 | 5.77152,13.5052 | 6.44,5.59; .0634,.1117 | .131,.228: each 95% upper limit | .13016; .06318 | .4854; **51.5%** |
| Same fit, conservative eccentricity screen | same | same | .172,.305: each 99% upper limit | .13016; .11318 | .8696; **13.0%** |
| **HD 11964**, Rosenthal et al.2021 catalogue, c then b | 37.9196,1935.0 | 24.3,201; .2315,3.185 | .106,.101 nominal | 11.69181; 1.90019 | .1625; **83.7%** |
| **HD 69830**, Lovis et al.2006 discovery model | 8.667,31.56,197 | 10.2,11.8,18.1; .0785,.186,.630 | .10,.13,.07 nominal | .67565; .09275 | .1373; **86.3%** |

Here Λᵢ = mᵢ√aᵢ, C_p = ΣΛᵢ(1 − √(1 − eᵢ²)), β_p = C_p/B, margin 1 − β_p. Caveats (A7 §5):

- **HD 109271**: period ratio 3.93797, near 4:1, so "no resonance problem" would be false; "the best first numerical
  trial, subject to a finite-divisor check". **HD 1461**: eccentricities are 95% and 99% upper limits; ratio 2.33997
  near 7:3. **HD 11964**: ratio 51.029, but larger mass and a small outer frequency. **HD 69830**: historical benchmark
  only; Boulkaboul et al. 2026 identify activity correlations near the middle planet's period.
- Edge-on minimum-mass ratios 6.9×10⁻⁵, 1.9×10⁻⁵, 5.4×10⁻⁴, 6.3×10⁻⁵ respectively; unknown inclinations scale masses by
  1/sin i and add AMD, so "no table row proves spatial strong stability of the observed system". LP17's equipartition
  proxy (doubling C_p) gives β = .3724, .9708 (1.739 for the 99% screen), .3250, .2746.
- Nominal minimum |j·ω| over 0 < |j|₁ ≤ 12: HD109271 .015752 at (−1, 4); HD1461 .008512 at (−3, 7); HD11964 .019597 at
  (0, −1); HD69830 **.000161** at (−1, 3, 4). "No row establishes nonresonance to the much larger K potentially required
  for a Gyr certificate."
- **HD 96700** (in LP17's 2017 strong list) fails with the third planet of Unger et al. 2021: even with both inner
  eccentricities zero, C_p = .30713, B = .11804, β_p = 2.602.

### 7.6 The computer-assisted route, cost and risks

A7 §6 copies the **soundness architecture** of the lunar certificates
(`KAM/SpinOrbit/Graph/CertV2.lean:soRotBarrier_of_certV2` via `checkTorusCertificateV2_sound`), not their cost model: a
frozen model/input record with rational intervals; rigorous lower bounds for every pair threshold; certified complex
Kepler invertibility and nonzero denominators on the whole enlarged secular set; Fourier/normal-form bounds with tails
and all divisors through K; a kernel soundness theorem ("No floating-point oracle or unbounded generated 'axiom'");
export through the first-exit engine and the osculating bridge. A failing run reports its first failing inequality,
which can still yield a certified finite horizon or a smaller certified mass threshold.

Cost (A7 §7): screening roughly 1–2 working weeks for one numerical analyst; certificate infrastructure roughly 7–15k
hand-written lines plus data, "plan in months rather than days". Risks: narrow complex widths near the collision
boundary, large Fourier norms, action radius versus divisors, uncertainty intervals crossing low-order resonances,
unbounded true masses and inclinations, omitted tails; about 2K² modes for n = 2 and (4/3)K³ for n = 3 (K = 1000: two
million versus 1.3 billion). Recommendation: screen HD 109271/HD 1461 first, keep HD 11964 as the wide-separation
alternative, use HD 69830 as a stress test, and report actual masses only if the full explicit ledger passes. "The
asymptotic theorem remains worthwhile even if this pilot exposes an impractical mass threshold; the two outcomes must
not be conflated."

## 8. Campaign plan

### 8.1 Phases and gates (A6 §1)

| Phase | Deliverable | Gate |
|---|---|---|
| 0. Contract | owner decisions; line-addressable source manuscript (proposed `blueprint-AMD/parts/a0-conventions.tex` … `a6-osculating.tex`); Ni96 and Pinzari13 checks | owner-approved literal definitions and statements; independent audit of normalization, quantifiers, strong threshold, crossing; reviewed proof of the planar enlarged product domain; then elaborate, review and freeze anchors |
| 1. Planar strong-LP, Nek77 | A5 §6.1: no arithmetic and no secular-confinement assumption; exponents 2/(6n² − 3n + 14), 3/(6n² − 3n + 14) | coverage of *every* state of the compact strong sublevel; audit of center-dependent slow levels and collar; all stopped hypotheses discharged; source comparison, serialized build, axiom and frozen-hash checks |
| 2. Planar nonresonant | A5 §6.2 via `nf`/`nonresonant`; exponent 1/(2(τ+1)); drift O(√μ); optional τ = n − 1/2 corollary | audit every 2π, slow scaling, norm convention, inverse cost, quantifier order; no duplicate Pöschel engine |
| 3. Spatial | A5 §6.3: spatial elements, vector momentum, regular spatial chart, reconstruction, k = 2n | independent audit of chart coverage at e = 0 and i = 0, symplecticity, the Γ + Z identity, no hidden small-eccentricity hypothesis |
| 4. Osculating | exact velocity, O(μ) comparison with parameter 1 + μmᵢ, gap preservation; can start alongside Phase 2 | "osculating" is not the canonical eccentricity vector; no time-growing error |
| 5. Certificate pilot | one two-planet target (HD 109271 or HD 1461), finite-cutoff soundness theorem, rational/interval data | one target, model and input box; a literal ledger of inequalities; the first failure reported honestly |

A9 §6 orders the work differently: sharp geometry (L2–L6) → planar full domain (L8) → the Track N adapter (L13) → first
exit and **Theorem 15 with the osculating bridge, "the first complete formal milestone"** → spatial packages → Theorem
19. It does not include the Nek77 route (§10).

### 8.2 Packages (A6 §2)

| Package | Output | Depends on | New Lean lines |
|---|---|---|---:|
| A0 | normalization and statement adapters; audited definition bodies | owner contract | 300–600 |
| A1 | pair compact minimum, contact equality, positivity, continuity, strong equivalence | scalar defs | 1,200–2,000 |
| A2 | planar and abstract spatial barrier, uniform radial compactness, Candidate A | A1, planar elements | 800–1,400 |
| A3 | center-dependent full slow balls, safe enlarged product, uniform complex domain and norm | A2, chart, tube | 1,000–2,000 |
| A4 | stopped adapter, no-exit/continuation, Nek77 strong-LP provider | A0–A3, N/P engines | 1,200–2,200 |
| A5 | Diophantine cutoff, period/scaling adapter, parameter algebra, nonresonant provider | A3–A4, `nf`/`nonresonant` | 1,500–3,000 |
| S1 | 3D elements, cross products, momentum conservation, model/export | model decisions | 2,000–3,500 |
| S2 | regular spatial Poincaré chart, symplecticity, analyticity, onto | S1, pinned source | 4,000–7,000 |
| S3 | rotation alignment, spatial slow-ball safety, adapters, final provider | A2–A5, S1–S2 | 3,000–6,000 |
| O1 | actual velocity, osculating comparison, no-crossing corollary | A2/A4; S1 for space | 1,000–2,000 |
| C1 | finite-cutoff certificate specification and soundness | A1/A3/A5 | 4,000–8,000 |
| C2 | rational input box, interval estimates, emitter, checked sample | C1, screening | 3,000–7,000 plus data |

Each prover's result needs a distinct auditor, and the integrator must not substitute a build for mathematical review;
model roles follow `docs/DECISIONS.md` at launch (A6 §2). With four roles (geometry, analytic domain, spatial
infrastructure, reviewer/integrator), S2 is the spatial critical path (A6 §4). A9 §3 maps one package to each A8 lemma
under `KAM/Planetary/StrongAMD/` and `KAM/Planetary/Spatial/`; the hard ones are 8 `AnalyticDomain` ("Hard interface
work, bounded scope") and 17 `Spatial/Poincare` ("Main new hard package"); 9–11 (A8's own averaging) are an optional
alternative to Track N, "not additional dependencies". The DAG (A9 §4) instantiates 13–14 with L8 and m = n, then with
L18 and m = 2n: "Never require both alternatives as hypotheses."

### 8.3 Reuse of repository declarations (A3 §2; A9 §5)

Paths are relative to `KAM/Planetary/` unless they begin with `KAM/`.

| Need | Existing declaration | Boundary |
|---|---|---|
| exact planar model | `Newtonian/Models.lean:movingHamiltonian_split`; `Newtonian/Reconstruction.lean:isNewtonSolutionOn_of_isMovingSolutionOn` | planar; 3D versions needed |
| elements, AMD | `AMD/Elements.lean:elements`, `eccentricity_deficit`; `AMD/AngularMomentum.lean:ang_mom` | scalar angular momentum only |
| planar chart | `Poincare/Chart.lean:analyticOnNhd_poincare`; `Poincare/Symplectic.lean:poincare_symplectic`; `Poincare/Bijective.lean:poincare_image`; `Poincare/Product.lean` | whole Γ < Λ region incl. circular orbits |
| complex domain | `Exponential/ComplexTube.lean:tube`; `Exponential/Perturbation.lean:perturbation`; `KAM/Kepler/KeplerTube.lean:eccAnomC_spec` | existence only; dimensions to generalize for space |
| normal form | `KAM/Nekhoroshev/Partial/Setting.lean:ExtNFHyp`; `NormalForm.lean:nf`, `nnf_disp_radius`; `Preimage.lean:preimage`; `Nonresonant.lean:nonresonant` | reuse unchanged |
| Nek77 route | `KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean:partialConvex_nekhoroshev` | stopped slow-domain premise to discharge |
| exit and ODE | `AMD/ConfinementExit.lean:amd_exit_forward`, `amd_exit_backward`; `AMD/MovingODE.lean:moving_ode` | generic; old theorems consume `AMDBox` |

### 8.4 Size estimates

| Source | Planar | Spatial | Osculating | Other |
|---|---|---|---|---|
| A6 §2 | Phase 1 5–9k; Phase 2 2–4k | 9–17k | 1–2k | qualitative total 17–32k; certificate 7–15k plus data |
| A9 §6 | 5–10k (nonresonant route, osculating included) | 7–15k | in planar | optional vector-field averaging 3–7k |
| A3 §6 | 5–9k | 9–17k | — | "Budgeting a second normal-form foundation would be a major overestimate" |

Calibration (A3 §6, `wc -l` with comments): `KAM/Nekhoroshev` 34,055 lines (Partial 12,472); `KAM/Planetary` 147,974
(AMD 1,322; Exponential 2,852; Poincare 3,957; Newtonian 2,836); `KAM/Kepler` 5,116. The AMD + Exponential
implementation behind P-EXP-SAFE totals 4,174 lines.

### 8.5 Before frozen anchors; source graph; risks; rules

- **Early work** (A6 §3), once a proof campaign is authorized: A1's scalar compact-minimum API; A2's abstract budget
  and radial lemmas; S1's dimension-three Kepler identities and cross-product conservation; a generic family-uniform
  compact periodic extension; O1's velocity algebra; numerical screening. "Do not pre-freeze an outcome predicate
  containing a normal-form witness, a stopped confinement hypothesis, or a completed conclusion."
- **Source graph** (A6 §5): reuse the nodes `bpP:p14:expsafe`, `bpN:p11:nf`, `bpN:p11:nonresonant` and the
  partial-convex anchor without copying their descendants. New labeled nodes: the threshold dictionary, attained
  minimum and continuity; the angular-momentum budget and compact barrier; full-product enlargement, complex extension,
  Fourier norm; the N-theorem instantiation and parameter arithmetic; **separate** first-fast-exit, first-slow-exit,
  moving-threshold and continuation steps; spatial chart coverage, alignment and off-level safety; the osculating
  comparison. "A structural graph PASS does not close a source gap."
- **Risks** (A6 §6): false novelty; a hidden small-eccentricity restriction; uniformity lost by one global slow ball;
  secular coordinates treated as passive; first-exit circularity; a spatial chart excluding e = 0 or i = 0;
  physical/canonical confusion; numerical failure at actual mass; unavailable observational premises; source drift. Add
  the unaudited proof: a refuted lemma sends its phase back to A4's plan with that item as a named source gap.
- **Rules** (ORCHESTRATOR §2; A6 §4): frozen files read-only, new anchors beside them; quarantined providers; no
  `axiom`, `admit`, `unsafe` or unregistered `sorry`; files ≤ 1,500 lines; **no heartbeat overrides**; `Fin n → ℝ`
  ambient types; the module system; one Lean/Lake build at a time; no conclusion-shaped hypotheses; stopped premises
  internal and discharged.

## 9. Launch checklist

In order, each with its exit criterion.

1. **Independent refute-first audit of A8** (first gate). Freeze `PROOF/MAIN.md` by SHA-256 (`309e9eb3…80e6ea`). An
   auditor who wrote none of A2–A9 tries to break each lemma, starting with §4.5 items 1–9, and keeps a findings ledger
   with a verdict per lemma (confirmed, repaired, refuted). Exit: every lemma used by Theorem 15 confirmed or repaired;
   Theorem 19 may follow later if only L17–L18 remain open. Until then A8 is not a proved supplier anywhere.
2. **Literature gates, in parallel.** Obtain Niederman 1996 and Pinzari 2013's full theorem (A2 §2, §5; A6 Phase 0).
   Exit: an exact containment verdict. This gates novelty claims, not the proof route.
3. **Owner decisions** (§5.4): the eleven A5 §9 items, the Phase 1 route, the planar premise, the constant packaging and
   the scope of the first deliverable. Exit: rulings recorded in `docs/DECISIONS.md`.
4. **Co-author confirmations** (§5.4).
5. **Source manuscript.** A line-addressable blueprint (`blueprint-AMD/parts/a0`–`a6`, A6 Phase 0) built from the
   audited A8 and A4, with complete lemmas and every unresolved item as an explicit source-gap node. Exit: the A6 Phase 0
   go gate (normalization, quantifiers, strong threshold, crossing notion, planar enlarged product domain).
6. **Frozen-statement proposal with exact Lean.** Elaborated text of the chosen anchors (new anchors; P-EXP-SAFE
   untouched) with the definitions of A5 §2 / A9 §1 and threshold characterization theorems; independent statement audit
   of binders, carriers and bodies; no conclusion-shaped hypotheses; hashes recorded, then frozen. A9 §2: "The next
   approval object should be the actual elaborated declaration text".
7. **Dependency graph** from the approved manuscript (§8.5), with independent extractor and reviewer, direct receipts
   and exact line locators, reusing the existing P and N nodes (A6 §5).
8. **Phase 1 packages.** Start the early infrastructure (A0, A1, A2, S1 and O1 algebra, generic tube extraction) once the
   campaign is authorized; then A3 with A4 (Nek77 route) or A5 (nonresonant route) per decision 3. Brief every Lean
   agent with the two hard rules: no heartbeat overrides; no file over 1,500 lines.
9. **Phase gates** as in §8.1; land after each audited package; one build at a time.
10. **Practical pilot, separately budgeted**: one to two weeks of HD 109271/HD 1461 finite-cutoff screening (A7 §7),
    reporting the first failed inequality. It does not block steps 1–9.

## 10. Inconsistencies between the input reports

| Topic | Disagreement | Where |
|---|---|---|
| Phase 1 route | A6/A5 make the Nek77 strong-LP theorem Phase 1 and the nonresonant one Phase 2; A9 makes nonresonant Theorem 15 "the first complete formal milestone" and the Nek77 route "Possible later"; A8 proves only the nonresonant theorems and does not label the Nek77 upgrade proved | A6 §1, A5 §9, A9 §5–6, A8 §7 |
| Planar premise and AMD | A5 `PlanarLPInitial` includes `ProgradeElliptic` with the signed `physicalAMD`; A8 uses ΣΛ − \|L\| with only qᵢ ≠ 0, Eᵢ < 0 and calls the prograde premise unnecessary | A5 §2.1 item 11, A8 §1, §7 |
| Constants and time form | A1: μ₀, A_Λ, A_a, c, T₀, d★, d_pair; A5: μstar, c, D_Λ, D_a, one d, R, eMax, no T₀, μ < μstar, osculating separate; A8/A9: μ₀, c, T₀, A_I, A_a, d★, d_pair, A_osc, μ ≤ μ₀, osculating in the headline | A1 (31), A5 §6–7, A8 §1, A9 §2 |
| Upper bound on δ | A1 requires 0 < δ < min_{a∈𝒜}B(Λ(a)); A4, A5, A8 require only δ > 0 (empty sublevels allowed; "There is no requirement min_U B > δ") | A1 §5, A4 preamble, A8 §7 |
| Analytic domain and spatial chart | A4 marks the family packaging and the spatial chart [OPEN RISK] and spatial "conditional"; A8 claims both proved | A4 §2.3, §5, §8; A8 L8, L17–L18 |
| Cutoff | A4: "The library allows a real cutoff K; a floor is unnecessary"; A8 L12–L13 use a floor | A4 §4.1, A8 L13 |
| Spatial chart carrier | A5 §8 states the chart on Z < 2(Λ − Γ), using Γ + Z < Λ in the proof; A8 L17 defines it only on the prograde region Γ + Z < I | A5 §8, A8 L17 |
| Size of spatial work | A6/A3: 9–17k; A9: 7–15k (chart 4–7k in A6 S2, 4–8k in A9) | A6 §2, A3 §6, A9 §6 |
| Size of planar work | A6: 5–9k (Nek77) + 2–4k (nonresonant) + 1–2k osculating; A9: 5–10k for the nonresonant route with osculating | A6 §2, A9 §6 |
| LP17 conjecture wording | A1 places the conjecture in the published §3 and says preprint and published wording differ; A2 and A8 found the clause identical in arXiv v2 §3 p.4 and published §3 p.3 ("Contrary to the wording in the initial brainstorm") | A1 §4, A2 §1, A8 §7 |
| LP17 published pages | A2: published text checked through web PDF extraction; A8: published page numbers "are not asserted as independently checked here" (HTTP 403) | A2 §1, A8 §7 |
| Pinzari 2013 | A1 names "Theorem B / Theorem 4.1" on a small-eccentricity planar domain; A2 inspected only the publisher abstract and lists the full theorem as unpaid | A1 §4, A2 §5 |
| LP17 equations for the contact minimum | A4 cites (26)–(30); A2 cites (26)–(34) for the minimization and (35)–(39) for the critical value | A4 §1.2, A2 §1 |

None is a mathematical contradiction: the first three are owner decisions (§5.4), the status difference is what the
audit resolves, and the rest are estimates and locators.

## 11. Provenance and limits

- Input SHA-256 at the time of writing: `BRAINSTORM-1.md` `bed18084…`, `ORCHESTRATOR-ASSESSMENT.md` `662e3f9f…`,
  `RESEARCH/LITERATURE.md` `cb7f4bd0…`, `GAP-ANALYSIS.md` `e966db1d…`, `PROOF-PLAN.md` `b669a974…`, `STATEMENTS.md`
  `94f98bff…`, `CAMPAIGN-PLAN.md` `8dcf674b…`, `PRACTICAL.md` `404492ae…`, `PROOF/MAIN.md` `309e9eb3…`,
  `PROOF/LEAN-ROADMAP.md` `bb52b50e…`, `PROOF/OPEN.md` `af5d8a21…`, the co-author's message `04a2c8c4…`; they match the
  hashes recorded in A8 §8 and `RESEARCH/_sources/validation.json` where those list them.
- This note adds no mathematics. Numbers keep the qualifications of their sources (screening, illustrative, planning
  range). The only checks made for it are read-only: existence and line numbers of the cited repository declarations,
  and the `git diff --stat` described at the top. No repository file was edited, no Lean or Lake process was run, and
  no process was stopped.
