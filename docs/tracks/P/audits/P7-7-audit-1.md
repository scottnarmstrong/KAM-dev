# P7-7 independent audit 1

**Overall: PASS WITH NOTES for both `bpP:p7:d25` (the assigned D25 dictionary API) and `bpP:p7:average`.** Statement fidelity and proof/kernel checks PASS. **Strict package hygiene FAILS:** eight new lines exceed 100 characters, so lint exits 1 for a reason beyond the explicitly allowed generated-root mismatch. This is a formatting defect, not a mathematical blocker; this report does not certify an unconditional all-checks/seal-ready package.

There is no frozen theorem/provider pair in P7-7: these are 19 public infrastructure theorems in `KAM.Planetary`, implementing the ten design signatures. No frozen anchor is sealed by this package or audit. No material statement/proof defect or new suspected pinned-source erratum was found.

## Scope, authority and frozen inputs

Audit date: 2026-10-28. Focused, tier-2 read-only source-correspondence/proof audit, with a separate adversarial pass and mechanical verification. The user's explicit request authorizes inspection, narrow builds/probes and this report, and overrides the generic brief's main-worktree output instruction. Only this report is added to tracked-source directories. No repairs, git mutations, subagents or publication were performed.

- Worktree: `/root/code/KAM-inp-p77`.
- Snapshot HEAD: `c526f74620570598b5e6d5d5579f3db4e0bcd8cd`.
- `inp`: `d9921a75b2e196520afda935beee22c004461382`.
- `inp-p75`: `6f81ec0391d04aaf84a61ef2794e2699c6b30cff`.
- Required `git diff inp...HEAD` contains `Product.lean` (474 lines, inherited P7-5) and `D25.lean` (331 lines). Git warns `multiple merge bases, using 868f551a8c4946df73059e13eb811650ef07c06a`; this is recorded rather than silently choosing another baseline.
- The handoff's narrower `git diff inp-p75...HEAD -- KAM/Planetary/Poincare/` contains only `D25.lean`. Only that module receives a fresh package verdict; `Product.lean` and earlier modules are inspected as dependencies.
- Authority read: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md` (especially D25), `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the P7-7 handoff, Track P statement, design §2/§7/§7.1/Appendix A, blueprint Part 7, and the imported frozen definitions. Applied skills: `lean-statement-audit` and `manuscript-audit`.

Frozen-v1 SHA-256 receipts:

| Input | SHA-256 |
|---|---|
| `KAM/Planetary/Poincare/D25.lean` | `95532e7ca2a1544ca3a798f2db5f6de33a8a04cc9d9d65143e119c78f660cdf8` |
| `KAM/Planetary/Poincare/Product.lean` (dependency) | `8a4f3a96649d2724bc29ea4db4ab9900da781045f3c016f1c16a7d03ca80461f` |
| `blueprint-P/parts/p7-kepler-poincare.tex` | `3a10ddf74067a3c7b54184a190710deaba3019c97d2e0d5e9a3773b889cc26ab` |
| `docs/tracks/P/design/KEPLER-LEAN-DESIGN.md` | `7c680968ef6f380e4497823a0333ee989b84cf480755d69e474f2d04826e87c8` |
| Original `/root/code/KAM-inp/.drafts/design/KeplerSignaturesP.lean` | `d9903304231afac0841cf0456d90c3dec04b2eb9e1a9752a9d4f9f9b7164d9c8` (matches design header) |
| `docs/tracks/P/audits/P7-7-handoff.md` (initially untracked) | `372e8f5d7d7e3e525a01637dd1dca17aea8d215eb55f1cfc8e676394cea32862` |
| `docs/tracks/P/statement.md` | `06d876320d40f7ae0cb5cdbe7e5b08a00b431125630079a2b3d3abcaac2e0b66` |
| `docs/DECISIONS.md` | `9d5d6ba0e0486a4480bcdd3d2bbae22edccd22936d9869f1032dbf97ba378592` |
| `manifest/frozen-anchors.json` | `b9b9fee8fa72332435a780c4b41d8250b2db4577594360bcf3891c85790488d2` |

## Declaration ledger

All declarations below have mathematical/source or auxiliary-lemma verdict PASS. Names are prefixed by `KAM.Planetary.`; locations are in `KAM/Planetary/Poincare/D25.lean` at frozen-v1. Anchor-level PASS WITH NOTES reflects the hygiene finding below, not weaker mathematics.

| Node / role | Declaration : line | Verdict | Reason |
|---|---|---|---|
| `d25 / block` | `planetBlock_assemble` : 53 | PASS | Unconditional coordinate identity; generic n. |
| `d25(a)` | `secularGamma_eq` : 59 | PASS | Literal oscillator action; unconditional extension of the domain-guarded source identity. |
| `d25(a)` | `secularRoot_eq` : 65 | PASS | Same root 1−Γ/Λ; unconditional literal equality. |
| `d25(a)` | `secularEccVector_eq` : 70 | PASS | Same ordered vector (ξ,η) and square-root coefficient; unconditional literal equality. |
| `d25(a)` | `secularAxis_eq` : 75 | PASS | Same axis (Λ/m)² = Λ²/(m²·1); unconditional literal equality. |
| `d25(c) / auxiliary` | `poincare_block_eq_ellipse` : 80 | PASS | Coordinate substitution with explicit h1,h2,hF, all discharged at its two uses. |
| `d25(c)` | `ellipsePhase_eq_poincareProd` : 98 | PASS | All eccentric longitudes F, with mean angles Φ(F,v); n=2 and κ=1. |
| `d25(c)` | `ellipsePhase_eq_poincareProd_self` : 124 | PASS | Actual chart at its own eccentric longitudes. hm and hw are redundant here, as in the design. |
| `d25(d)` | `keplerFunctions_poincareProd` : 138 | PASS | All six conjuncts, including physical domain, energy, axis, action, cross product and eccentricity vector. |
| `d25(d), converse` | `exists_poincareProd_of_progradeElliptic` : 178 | PASS | Preimage in the full product domain; no noncircular restriction. |
| `average / auxiliary` | `integral_via_keplerPhi` : 188 | PASS | Correct shifted interval from F(0) to F(0)+2π; periodicity is an explicit auxiliary premise, proved at consumption. |
| `average / auxiliary` | `orbitalUnit_add_two_pi` : 208 | PASS | Unconditional trigonometric periodicity. |
| `average / auxiliary` | `ellipsePosition_add_two_pi` : 211 | PASS | Unconditional position periodicity, preserving frozen total formulas. |
| `average / auxiliary` | `longitudeJacobian_add_two_pi` : 215 | PASS | Unconditional Jacobian periodicity. |
| `average / auxiliary` | `ellipseMomentum_add_two_pi` : 219 | PASS | Unconditional momentum periodicity. |
| `average / auxiliary` | `ellipsePhase_update_add_two_pi` : 223 | PASS | Only the selected planet longitude changes; all other blocks are fixed. |
| `average / auxiliary` | `continuous_assemble_update` : 240 | PASS | Continuity of the angle-varying input path; generic n. |
| `average` | `average_via_eccentric_longitude` : 253 | PASS | Same continuous scalar observable on the full 8-dimensional phase space, Jacobian and 1/(2π) normalization. |
| `average / means` | `poincareProd_means` : 301 | PASS | All three means; stronger general-n, κ>0 version, specializing to the source at n=2, κ=1. |

The ten design theorem headers match both the appendix and the hash-pinned original signatures modulo whitespace. No binder, explicitness, order, quantifier, carrier, constant dependence or conclusion changed. Transient exact-type probes independently elaborated those design headers and explicit-binder proof applications; all passed.

The D25 proposition is distributed across packages: blueprint lines 247–263 include root/eccentricity bounds, (b) Kepler inversion/analyticity, uniqueness modulo the lattice in (d), and (e) element interpretation. These are inherited `poincare_facts`, `Kepler.Equation` (including `keplerLong_eq_add_eccAnom`), and `poincareProd_eq_iff` results as mapped in design §2. P7-7's eight dictionary signatures do not individually restate that entire proposition. Its existence theorem supplies the converse, while lattice uniqueness remains the inherited P7-5 theorem. This is the documented decomposition, not a claim that this audit freshly verifies every earlier node.

## Source-facing binders, fully expanded

`TYPING` records data/indices and ambient finite real-coordinate spaces. `SOURCE` records the explicit masses/strength/observable premises or the source converse domain. `STANDING` expands membership in the Poincaré domain. No instance binders, RULED changes or EXCESS premises occur. Every row is one binder, or one logical field obtained by expanding a bundled premise. Universal indices inside a field are retained in that row. Let Λⱼ = fast w.2 j and Γⱼ = ((slow w.1 j)²+(slow w.2 j)²)/2.

Citations: A = blueprint Part 7 lines 247–255 and design Appendix A D25 headers (2355–2385); V = blueprint lines 266–273 and design headers 2387–2404; M = blueprint standing conventions lines 25–29 and `poincareProd_means` design header. `hw` is literally ∀j, 0<Λⱼ ∧ Γⱼ<Λⱼ; `ProgradeElliptic` is expanded below.

| Declaration | Binder / expanded logical input | Bin | Authority |
|---|---|---|---|
| `secularGamma_eq` | w : Phase (2+2) | TYPING | A |
| `secularGamma_eq` | i : Fin 2 | TYPING | A |
| `secularRoot_eq` | w : Phase (2+2) | TYPING | A |
| `secularRoot_eq` | i : Fin 2 | TYPING | A |
| `secularEccVector_eq` | w : Phase (2+2) | TYPING | A |
| `secularEccVector_eq` | i : Fin 2 | TYPING | A |
| `secularAxis_eq` | m : Fin 2 → ℝ | TYPING | A |
| `secularAxis_eq` | w : Phase (2+2) | TYPING | A |
| `secularAxis_eq` | i : Fin 2 | TYPING | A |
| `ellipsePhase_eq_poincareProd` | implicit m : Fin 2 → ℝ | TYPING | A |
| `ellipsePhase_eq_poincareProd` | hm : ∀j, 0 < m j | SOURCE | A |
| `ellipsePhase_eq_poincareProd` | implicit w : Phase (2+2) | TYPING | A |
| `ellipsePhase_eq_poincareProd` | hw.positive : ∀j, 0 < Λⱼ | STANDING | A; Chart.lean:53, Product.lean:51 |
| `ellipsePhase_eq_poincareProd` | hw.action : ∀j, Γⱼ < Λⱼ | STANDING | A; same literal domain |
| `ellipsePhase_eq_poincareProd` | F : Fin 2 → ℝ | TYPING | A |
| `ellipsePhase_eq_poincareProd_self` | implicit m : Fin 2 → ℝ | TYPING | A |
| `ellipsePhase_eq_poincareProd_self` | hm : ∀j, 0 < m j | SOURCE | A |
| `ellipsePhase_eq_poincareProd_self` | implicit w : Phase (2+2) | TYPING | A |
| `ellipsePhase_eq_poincareProd_self` | hw.positive : ∀j, 0 < Λⱼ | STANDING | A; Chart.lean:53, Product.lean:51 |
| `ellipsePhase_eq_poincareProd_self` | hw.action : ∀j, Γⱼ < Λⱼ | STANDING | A; same literal domain |
| `keplerFunctions_poincareProd` | implicit m : Fin 2 → ℝ | TYPING | A |
| `keplerFunctions_poincareProd` | hm : ∀j, 0 < m j | SOURCE | A |
| `keplerFunctions_poincareProd` | implicit w : Phase (2+2) | TYPING | A |
| `keplerFunctions_poincareProd` | hw.positive : ∀j, 0 < Λⱼ | STANDING | A; Chart.lean:53, Product.lean:51 |
| `keplerFunctions_poincareProd` | hw.action : ∀j, Γⱼ < Λⱼ | STANDING | A; same literal domain |
| `keplerFunctions_poincareProd` | i : Fin 2 | TYPING | A |
| `average_via_eccentric_longitude` | implicit m : Fin 2 → ℝ | TYPING | V |
| `average_via_eccentric_longitude` | hm : ∀j, 0 < m j | SOURCE | V |
| `average_via_eccentric_longitude` | implicit w : Phase (2+2) | TYPING | V |
| `average_via_eccentric_longitude` | hw.positive : ∀j, 0 < Λⱼ | STANDING | V; Chart.lean:53, Product.lean:51 |
| `average_via_eccentric_longitude` | hw.action : ∀j, Γⱼ < Λⱼ | STANDING | V; same literal domain |
| `average_via_eccentric_longitude` | i : Fin 2 | TYPING | V |
| `average_via_eccentric_longitude` | φ : Phase (2*2) → ℝ | TYPING | V |
| `average_via_eccentric_longitude` | hφ : Continuous φ | SOURCE | V |
| `poincareProd_means` | implicit n : ℕ | TYPING | M |
| `poincareProd_means` | implicit m : Fin n → ℝ | TYPING | M |
| `poincareProd_means` | implicit κ : ℝ | TYPING | M |
| `poincareProd_means` | hm : ∀j, 0 < m j | SOURCE | M |
| `poincareProd_means` | hκ : 0 < κ | SOURCE | M |
| `poincareProd_means` | implicit w : Phase (n+n) | TYPING | M |
| `poincareProd_means` | hw.positive : ∀j, 0 < Λⱼ | STANDING | M; Chart.lean:53, Product.lean:51 |
| `poincareProd_means` | hw.action : ∀j, Γⱼ < Λⱼ | STANDING | M; same literal domain |
| `poincareProd_means` | i : Fin n | TYPING | M |
| `exists_poincareProd_of_progradeElliptic` | implicit m : Fin 2 → ℝ | TYPING | A |
| `exists_poincareProd_of_progradeElliptic` | implicit z : Phase (2*2) | TYPING | A |
| `exists_poincareProd_of_progradeElliptic` | hm : ∀j, 0 < m j | SOURCE | A |
| `exists_poincareProd_of_progradeElliptic` | hz.mass : ∀j, 0 < m j | SOURCE | A; frozen ProgradeElliptic body |
| `exists_poincareProd_of_progradeElliptic` | hz.radius : ∀j, 0 < planeLength (bodyVector z.1 j) | SOURCE | A; frozen ProgradeElliptic body |
| `exists_poincareProd_of_progradeElliptic` | hz.energy : ∀j, keplerEnergy m z j < 0 | SOURCE | A; frozen ProgradeElliptic body |
| `exists_poincareProd_of_progradeElliptic` | hz.cross : ∀j, 0 < planeCross (bodyVector z.1 j) (bodyVector z.2 j) | SOURCE | A; frozen ProgradeElliptic body |

Expanded-input counts: TYPING=28, SOURCE=12, STANDING=10, RULED=0, EXCESS=0.

Auxiliary binders were checked separately: all nine helpers have only their displayed finite-coordinate/function/index data, except the following explicit conditional helper premises:

| Helper | Logical inputs | Discharge in source-facing proof |
|---|---|---|
| `poincare_block_eq_ellipse` | `h1` identifies ξ, `h2` identifies (Λ,η), `hF` identifies the chosen eccentric longitude | `ellipsePhase_eq_poincareProd` proves these by block assembly and `keplerLong_unique`; the self identity supplies `rfl rfl rfl`. No physical identity is assumed. |
| `integral_via_keplerPhi` | `hv : planeLength v < 1`, `hg : Continuous g`, `hper : Periodic (g ∘ Φ · J) (2π)` | `average_via_eccentric_longitude` obtains hv from `poincare_facts`, proves hgc from chart analyticity along a domain-preserving path, and proves periodicity from explicit ellipse/J periodicity. No change-of-variables conclusion is assumed. |

These are distinct, genuinely conditional auxiliary results, not replacements for either source theorem. The other seven helpers have no logical premises. There are no hidden typeclass, witness, gate or result-bundle assumptions.

## Definition classification and semantic closure

New `def`/`abbrev`/`structure` declarations: **none**. Local `let`/`set` abbreviations denote the displayed path, observable, axis or point only; none invents an object or assumes a theorem.

The literal frozen bodies were read: `assemble` is (φ,q;I,p), `oscillatorAction` gives Γ=(p²+q²)/2, `secularRoot` is 1−Γ/Λ, `secularEccVector` uses √((1−Γ/(2Λ))/Λ)·(ξ,η), `secularAxis` is (Λ/m)². `ellipsePosition`, `ellipseMomentum`, `ellipsePhase`, `longitudeJacobian`, the four physical `kepler*` functions and `ProgradeElliptic` are the intended formulas. In particular momentum has m²/(ΛJ), energy has |p|²/(2m)−m/|q|, and `planeLength` is the planar Euclidean length while `planeSq` is its square, not the ambient max norm.

For these imported literal frozen definitions: BODY_MATCH=OK; PUBLIC_CARRIER=OK under the explicitly total frozen formula conventions; WELL_DEFINEDNESS=N/A_LITERAL; CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=PASS for the formulas used here. This is a dependency-body correspondence check, not a new manifestation or seal.

The inherited inverse `keplerLong` in Equation.lean:117 has an explicit off-domain zero branch. It is not new in P7-7. Its on-domain choice is from the proved bijection `keplerPhi_bijective`, characterized by `keplerPhi_keplerLong` and made unique by `keplerLong_unique`. All P7-7 uses asserting inverse/physical meaning first derive |v|<1 from hw. The unconditional self/dictionary identities compare the same total formulas and do not infer physical meaning off-domain. Thus P7-7 does not exploit the fallback as a substitute for an orbit or inverse proof. No new arbitrary witness/fallback was introduced.

Import-closure scan: 71 project modules, including 55 frozen paths; all 55 have manifest owners, kind `definition`, state `SEALED`. No frozen theorem and no provider occurs in the transitive project import closure. This rules out hidden DRAFT_SORRY/provider imports. Frozen-byte and ABI checks are reported below.

## Mathematical proof and adversarial checks

All 331 lines were read. The spine checks were:

1. Coordinates: `planetBlock_assemble` preserves fast/slow ordering; Γ's swapped sum is closed by ring; the eccentric vector remains (ξ,η), not its transpose. Axis normalization is κ=1 throughout D25.
2. Arbitrary eccentric longitude: changing λ to Φ(F,v) preserves ξ,η,Λ and therefore v. Uniqueness of the Kepler inverse is used only with |v|<1 supplied by the chart domain. The self identity is literally the chart formula, even without its redundant domain/mass hypotheses.
3. Physical functions: block projection, `poincare_elements` at κ=1 and `regionProd_one_iff` establish every conjunct. `ProgradeElliptic` is proved, not assumed in the forward direction. Surjectivity is applied only to an actual point in `regionProd m 1` in the converse.
4. Change of variables: a naive Φ(0)=0 argument would fail for v₁≠0. The implementation avoids it: choose a=keplerLong 0 v, so Φ(a)=0 and Φ(a+2π)=2π. Apply the derivative substitution on [a,a+2π], then use periodicity of the weighted integrand to shift to [0,2π]. No endpoint is silently changed. g is continuous along the entire path because varying only λ preserves the domain. In the key identity, all unselected angles return exactly to their original values by Φ(Fⱼ(w),vⱼ)=λⱼ. The final periodicity is derived, not required of φ.
5. Means: block extraction identifies exactly the one-planet path. `poincare_means` supplies all three integrals, and `poincare_facts` rewrites 1−k² as `planeSq v`. No circular-orbit exclusion appears. General n and κ>0 are a valid strengthening, with second mean m²κ/a and the specified axis Λ²/(m²κ).

Separate refutation pass considered: missing positivity, circular orbits Γ=0, n=0, angle versus anomaly normalization, nonzero lower inverse endpoint, changing unselected planets, use of total inverse outside |v|<1, weakened inverse-image conclusion, and the distinction between one-angle averaging and the later full double average. None yielded a mathematical finding: guards are proved at point of use, n=0 has no i : Fin 0, and the result asserts the prescribed one-angle integral. It does not claim full secularBoxSafety or the complete double-average consumer bridge.

## Findings, source defects and deviations

**H1 — confirmed, formatting / handoff accuracy.** D25.lean lines 58, 179, 225, 252, 256, 272, 301, 304 exceed 100 characters. Their respective lengths are 110, 107, 103, 109, 107, 101, 103, 120. The handoff says `informational: ... 8 lines > 100 chars ... (verbatim signature lines)`. Refutation: `scripts/lint_sources.sh` explicitly sets `status=1` for this condition, and the fresh invocation exits 1. Moreover line 272 (`have key : ...`) is proof code, lines 58/252 are comments, and line 225 is an auxiliary theorem; these are not all verbatim design signature lines. Keeping exact types does not require keeping line breaks. Proposed repair: wrap the eight lines without changing declarations. Not applied under this read-only audit.

**H2 — expected integration note.** `KAM.lean is out of date; run scripts/gen_root_imports.py`. This is the brief's explicit allowed exception and is left to the orchestrator. It is not the only lint failure because of H1.

**N1 — redundant signature premises, not a defect.** Build warnings concern `hm` at 98:54 and 124:59, and `hw` at 125:5. They are exactly present in the specified design surface; no extra premise was introduced by this implementation. The first theorem also has redundant positive masses, not only the self theorem. Do not change the design-facing signature merely to suppress warnings.

Suspected blueprint/pinned-source defects newly found: **none**. No external PDF was re-audited: the narrow authority here is the local blueprint, design and frozen definitions. The pre-existing Fej04r/Fej07e normalization/sign notes at blueprint lines 284–288 were not reclassified or claimed as new discoveries. No deviation to the physical masses, action normalization, radian period, carriers or equations was introduced. No mathematical refutation claim remains untested or unresolved.

## Verification receipts

Every Lean-producing command below ran sequentially within this audit with `LEAN_NUM_THREADS=1`; no other Lean/lake/checker command of this audit overlapped. Commands inherited `nice -n 5`, including the ABI subprocess invoked by lint. Builds used the required compile gate; no clean/update/cache/dependency modification command was run.

### Targeted build — exit 0

```sh
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p77 KAM.Planetary.Poincare.D25
```

Output includes:

```text
[inp-gate] slot 1 acquired 04:37:51 for KAM.Planetary.Poincare.D25
Build completed successfully (9117 jobs).
```

Only the three unused-variable warnings listed in N1 concern this module. No heartbeat/resource-budget override or elaboration failure occurred.

### Design-header / exact-type / application and axiom probes — exit 0

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P77Audit.lean
```

Probe SHA-256: `289529e6536e16835c93cf373b6808d08abe0777c9335d8a4fbdc9652cf62c7a`.

Reproduction: import `KAM.Planetary.Poincare.D25`; open `Set Metric Real`, `KAM KAM.Kepler KAM.Planetary`; create namespace `P77Audit`, variable `{n : ℕ}`. Copy each of the ten theorem headers from design Appendix A's `section D25` with a fresh namespace and replace its draft body by `by exact KAM.Planetary.<name> <explicit arguments below>`. After each declaration elaborate `example : type_of% @<name> := @KAM.Planetary.<name>`. Finally print axioms for each of the 19 theorem names in the ledger. This tests the independently reconstructed type and explicit-binder application; the package has no provider seal body to test.

| Theorem | Explicit application arguments, in header order |
|---|---|
| `secularGamma_eq`, `secularRoot_eq`, `secularEccVector_eq` | `w i` |
| `secularAxis_eq` | `m w i` |
| `ellipsePhase_eq_poincareProd` | `hm hw F` |
| `ellipsePhase_eq_poincareProd_self` | `hm hw` |
| `keplerFunctions_poincareProd` | `hm hw i` |
| `exists_poincareProd_of_progradeElliptic` | `hm hz` |
| `average_via_eccentric_longitude` | `hm hw i hφ` |
| `poincareProd_means` | `hm hκ hw i` |

The separately run header comparison printed `10/10 signatures match the hash-pinned original KeplerSignaturesP.lean modulo whitespace`.

Full axiom output:

```text
'KAM.Planetary.planetBlock_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.secularGamma_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.secularRoot_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.secularEccVector_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.secularAxis_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.poincare_block_eq_ellipse' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ellipsePhase_eq_poincareProd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ellipsePhase_eq_poincareProd_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerFunctions_poincareProd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exists_poincareProd_of_progradeElliptic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.integral_via_keplerPhi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.orbitalUnit_add_two_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ellipsePosition_add_two_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.longitudeJacobian_add_two_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ellipseMomentum_add_two_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ellipsePhase_update_add_two_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuous_assemble_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.average_via_eccentric_longitude' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.poincareProd_means' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay — exit 0

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Poincare.D25
```

Exact output:

```text
replaying KAM.Planetary.Poincare.D25
```

One invocation covers the sole P7-7 module and all 19 declarations; no additional new lemma module exists.

### Source lint

```sh
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, with exact output:

```text
Lean lines over 100 characters:
/root/code/KAM-inp-p77/KAM/Planetary/Poincare/D25.lean:58:110
/root/code/KAM-inp-p77/KAM/Planetary/Poincare/D25.lean:179:107
/root/code/KAM-inp-p77/KAM/Planetary/Poincare/D25.lean:225:103
/root/code/KAM-inp-p77/KAM/Planetary/Poincare/D25.lean:252:109
/root/code/KAM-inp-p77/KAM/Planetary/Poincare/D25.lean:256:107
/root/code/KAM-inp-p77/KAM/Planetary/Poincare/D25.lean:272:101
/root/code/KAM-inp-p77/KAM/Planetary/Poincare/D25.lean:301:103
/root/code/KAM-inp-p77/KAM/Planetary/Poincare/D25.lean:304:120
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (397 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The module-system, frozen-byte and all 144 elaborated frozen ABI checks pass. The nonzero exit is caused by the eight overlong lines and the expected generated-root mismatch; H1 remains after exempting only the latter.

### Other mechanical checks

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty diff, exit 0 (only the recorded multiple-merge-base warning on stderr).
- `git diff --check inp-p75...HEAD -- KAM/Planetary/Poincare/`: empty, exit 0.
- `git diff --name-only inp-p75...HEAD -- KAM/Planetary/Poincare/`: exactly `KAM/Planetary/Poincare/D25.lean`.
- Module header: copyright, `module`, public imports, module docstring, `@[expose] public noncomputable section` present. 331 total lines, below 1500.
- Module scan for `sorry|admit|axiom|unsafe|opaque|set_option|EuclideanSpace`: no matches.
- Import manifest closure: no project provider, no frozen theorem, no unmanifested frozen file; all 55 frozen dependencies are SEALED definitions.

Report validation: `git diff --no-index --check /dev/null /root/code/KAM-inp-p77/docs/tracks/P/audits/P7-7-audit-1.md` produced no diagnostics (exit 0); the audited D25 SHA-256 remained unchanged.

## Closeout and limits

All 19 public declarations and all ten designated source-facing signatures are classified; no material mathematical or axiom issue remains. Exact-type/application probes, targeted build and kernel replay pass. The formatting finding is mechanically confirmed and survives the proposed explanation in the handoff. Lint's root mismatch is permitted, but H1 remains an additional failing check. Both assigned nodes therefore receive **PASS WITH NOTES**, with **no unconditional seal-ready/all-hygiene PASS** until the eight lines are wrapped and lint is rerun. Earlier package proof sources and downstream physical headline closure are outside this audit's fresh certification.

Only the required audit report is a new source-tree artifact. The transient probe is deleted after recording receipts. No frozen source, manifest, generated file, provider, implementation proof or existing handoff was changed.
