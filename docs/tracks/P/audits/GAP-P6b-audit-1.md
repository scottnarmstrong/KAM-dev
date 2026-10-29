# GAP-P6b independent audit 1

**Overall: FAIL the literal graph-node export gate, solely for `stepP:p6:mp-b`.**
The other 11 nodes pass. All 13 public theorems are sound on their declared types,
have standard axiom closure, build, and pass kernel replay. The failure is an
explicit export-shape mismatch, not an unproved analytic estimate: the requested
positivity equivalence is replaced by positivity alone. Under the source's
positive-measure premise these conclusions are logically equivalent; this audit
does not silently replace the handoff's literal-export rule by logical derivability.

No frozen theorem is sealed by this package. Provider/frozen type equality and
prospective seal checks are **N/A**, rather than passing seal receipts.

## Scope, authority and frozen snapshot

Audit date: 2026-10-29. Tier 2, read-only source correspondence and proof audit.
Permission: user authorizes this report, scratch probes under `.lake/abi-scratch/`,
and targeted validation. No production, graph, manifest, generated-root or git-state
edits. The user's exact worktree report path overrides the generic brief's MAIN
worktree output instruction. No subagents were used.

- Worktree: `/root/code/KAM-inp-gp6b`.
- HEAD: `5430d9f96ab1fd7b24fe948f60447f6d27b60dd1`.
- Comparison branch `inp`: `537fc2a837002555fbe2766678b1c8454274228f`.
- Full `git diff inp...HEAD`: exactly one new file, 261 lines,
  `KAM/Planetary/Newtonian/AssemblyNodes.lean`.
- Initial untracked input: `docs/tracks/P/audits/GAP-P6b-handoff.md`; left untouched.
- Read AGENTS, PLAN, DECISIONS, track P statement, audit brief, handoff, and the
  GAP-P6b section of `/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P.md`.
- All exports in this package are UNSIGNED. There is no signed declaration to
  compare against a signature file. Existing signed dependencies are unchanged.

Frozen-v1 SHA256 values:

| Input | SHA256 |
|---|---|
| `KAM/Planetary/Newtonian/AssemblyNodes.lean` | `871f107529cea7f26b8c3605eae474d175671febbf6ddec4e9b18675d2358cca` |
| `docs/graph/P/DEPGRAPH.md` | `c21e6cef18a1f08ff50fccfecdde48506faef57a7504f2cff51be78c0e95ae0e` |
| `blueprint-P/parts/p6-newtonian-models.tex` | `b6885887ba6dfd181e79925cb4584b4b5590d0debc3bc205a2c49aa86b634899` |
| `docs/tracks/P/audits/GAP-P6b-handoff.md` | `43a84cf1472faf0a4094179f92c10c9c1608ba6ca315906f84eb0519201827aa` |
| `manifest/frozen-anchors.json` | `4fc016112607997d4db27f26b4e0a1ebf4e76f8cd89e2cf8c380e13676e1fea1` |
| `docs/tracks/P/statement.md` | `06d876320d40f7ae0cb5cdbe7e5b08a00b431125630079a2b3d3abcaac2e0b66` |

The manifest and its 144 frozen declarations pass the anchor and ABI guards.
Frozen definition bodies inspected include Phase, bodyVector, planeSq, planeLength,
NoCollision, barycentricPositions, barycentricVelocities, actualMasses,
circularPoint, circularTube, PairBounds, movingHamiltonian, IsPhysicalTorus,
IsNewtonSolution, IsNewtonSolutionOn and MovingKolmogorovSet.

## Per-node and declaration verdicts

All declaration names below have prefix `KAM.Planetary.`. Lean line numbers refer
to frozen-v1 above; graph locators refer to `docs/graph/P/DEPGRAPH.md`; blueprint
locators refer to `blueprint-P/parts/p6-newtonian-models.tex`. Each node's
SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS and SOURCE_CONCLUSION was read, alongside
its cited blueprint line and enclosing statement.

| Node | Declaration (Lean lines) | Graph SOURCE lines; blueprint lines | Verdict | Source comparison |
|---|---|---|---|---|
| `stepP:p6:rc-a` | `rc_a_lengths` (37–59) | 11827–11829; 172 | PASS | Both length identities and positivity; symmetry for all pairs strengthens the Sun–planet instance. Only NoCollision is needed; drops R2 and mass restrictions. Time precedes planet indices. |
| `stepP:p6:rc-sun` | `rc_sun_hasDerivAt` (62–74) | 11857–11859; 173 | PASS | Derivative of Q0 is exactly `(-μ/m0) • Σp`, plus equality with V0. Source physical assumptions and R1/R2 only; arbitrary J. |
| `stepP:p6:rc-planets` | `rc_planets_hasDerivAt` (77–85) | 11888–11890; 174 | PASS | Q(i.succ) derivative V(i.succ), time then planet; source indices are explicitly translated by succ. |
| `stepP:p6:rc-vplanet` | `rc_vplanet_hasDerivAt` (89–103) | 11919–11921; 175 | PASS | Full force sum over Fin(n+1) excluding i.succ, including the Sun, with actual masses and cubic physical length. |
| `stepP:p6:rc-vsun` | `rc_vsun_hasDerivAt` (106–118) | 11952–11954; 176 | PASS | Literal planet-only sum via l:Fin n and l.succ, not a conditional reindexing premise. |
| `stepP:p6:ot-curve` | `ot_curve` (124–130) | 12152–12154; 204 | PASS | Generic H strengthens the two model instances. R1 and HasDerivAt X_H for every φ then t, directly from torus clause (viii). |
| `stepP:p6:ma-tube` | `ma_tube` (135–140) | 12603–12605; 275 | PASS | Both inclusion in Uη and Borel measurability. Drops unused S2 and physical premises; canonical AxisData instantiation justified below. |
| `stepP:p6:ma-coll` | `ma_coll` (143–148) | 12633–12635; 276 | PASS | NoCollision at every φ for every K with range in S. S2's witness supplies this range premise; no torus-property or measurability premise is added. |
| `stepP:p6:ma-pair` | `ma_pair` (151–158) | 12694–12696; 278 | PASS | Exact PairBounds at K(φ+t•w), φ before t, constants γ/2 and 2A+γ fixed before μ and orbit. Generalizes from S2 witnesses to arbitrary contained K. |
| `stepP:p6:mp-a` | `mp_a_box` (164–199) | 12506–12508; 252,257 | PASS | Literal box, both source maxima, both exponents 2n, measure upper bound and finiteness, for every subset without measurability restriction. |
| `stepP:p6:mp-b` | `mp_b_measure` (203–218) | 12537–12539; 253,258 | **FAIL (F1)** | Graph explicitly asks for `0 < vol Ψ(A) ↔ 0 < vol A`; named export concludes only `0 < vol Ψ(A)`. See exact scope and refutation below. |
| `stepP:p6:mp-b`, Borel clause | `mp_b_measurableSet` (221–229) | same; 253,258 | PASS for this clause | Separate export establishes Borel image from Borel A under the same chart and full-lattice conditions; positivity is unnecessary. Does not supply the missing iff in F1. |
| `bpP:p6:measure-positive` | `measure_positive` (234–257) | 12471–12473; 249–255 | PASS | Full (a)+(b): explicit finite box bound; null measurability, conditional Borel clause, formula, positivity and conditional finiteness. Physical data precede (a)'s S and (b)'s chart and A. This parent source conclusion asks for positivity, not an iff. |

**Completeness:** 12/12 mapped nodes inspected; 11/12 satisfy the literal-export
gate. All 13 new public declarations are listed above. No other node is mapped to
AssemblyNodes by the controlling GAP-P6b package section. `ma-newton`, other Part 6
steps, and campaign headline proofs are outside this package.

## F1: literal positivity equivalence is absent

Severity: package export-contract failure, not mathematical unsoundness.
Status: survived a second, adversarial comparison of source and actual export;
its possible interpretation as a mathematical weakening was refuted.

Graph line 12539 says:

> `SOURCE_CONCLUSION: measurability, formula, 0<meas Psi(A) iff 0<meas A; and with (a), 0<meas S<infinity for S subset U_eta`

Blueprint line 258 likewise says the Liouville lemma gives
`0<meas Ψ(A) ⇔ 0<meas A`. The named theorem instead concludes (lines 212–215):

```lean
NullMeasurableSet (Ψ '' A) ∧
  volume (Ψ '' A) = ENNReal.ofReal (c ^ (n * 2)) * volume (A ∩ unitCell (n * 2)) ∧
  0 < volume (Ψ '' A) ∧
  (Ψ '' A ⊆ circularTube G m0 m a η → volume (Ψ '' A) < ⊤)
```

Refutation checks:

1. Is the requested iff present under an alias? No: the third clause is an
   ordinary strict inequality, and none of the conclusion aliases hides an iff.
2. Is there a second package export containing it? No: the companion export is
   Borel measurability, and `measure_positive` also contains positivity alone.
3. Is `hApos` an illicit premise? **No.** Graph line 12537 and blueprint line 253
   explicitly assume positive measure of A. Accordingly this is not EXTRA-HYP.
4. Is the iff mathematically missing? **No.** It follows propositionally from
   the supplied source premise and the positive-image clause. The independent
   scratch probe below compiled successfully. Also the invoked landed
   `liouville_lattice` already has the unconditional iff in its type.

```lean
have h := mp_b_measure (G := G) (m0 := m0) (m := m) (a := a) (η := η)
  hG hm0 ha hc hO hΨ hQ1 hQ2 hA hAO hAper hApos
exact (show (0 < volume (Ψ '' A) ↔ 0 < volume A) from
  ⟨fun _ => hApos, fun _ => h.2.2.1⟩)
```

Disposition: the explicit AUDIT FOCUS requires the named unsigned export to state
the node's literal conclusion, rather than accepting a derived wrapper. Under
that rule F1 fails. If logical equivalence under the listed source hypotheses
were the gate instead, this row would pass. No new estimate or source correction
is needed; a requested implementation repair could expose the iff directly.
No repair was applied in this audit.

## Binder, definition and normalization audit

Classification: SOURCE = explicit local source premise; STANDING = source's
Part 6 data or its defined axis constants; TYPING = carriers/indices;
RULED = owner-added premise; EXCESS = other assumption. The following table
expands the logical bundles; shared rows apply separately to every indicated
export. There are **0 RULED and 0 EXCESS** assumptions throughout.

| Export(s) | Binder or expanded field | Bin | Source |
|---|---|---|---|
| All | n : ℕ | TYPING | Part 6 dimension; n≥1 is dropped, not assumed additionally. |
| All applicable | G : ℝ | TYPING | Blueprint 20,250. |
| All applicable | m0 : ℝ | TYPING | Blueprint 20,250. |
| All applicable | μ : ℝ | TYPING | Blueprint 20,153–159. |
| All applicable | m : Fin n → ℝ | TYPING | Blueprint 20,250. |
| Tube/measure exports | a : Fin n → ℝ | TYPING | Blueprint 211,250. |
| Tube exports | γ : ℝ | STANDING | Defined axis gap, blueprint 212–214; general bound form. |
| Tube exports | A : ℝ | STANDING | Defined axis maximum, blueprint 212–214; general bound form. |
| Tube/measure exports | η : ℝ | TYPING | Blueprint 211,250. |
| Reconstruction exports | J : Set ℝ | TYPING | Arbitrary time set, blueprint 153. |
| Reconstruction exports | z : ℝ → Phase(n*2) | TYPING | Blueprint 153–159. |
| `rc_a_lengths` | hnc : ∀t∈J, NoCollision(z t).1 | SOURCE | R1, blueprint 156,172. |
| Four derivative rc exports, relevant measure exports | hG : 0<G | STANDING | Blueprint 20,250. |
| Same, plus `ma_pair` | hm0 : 0<m0 | STANDING | Blueprint 20,250,267. |
| Four derivative rc exports, `ma_pair`, `mp_a_box`, parent | hm : ∀i, 0<m i | STANDING | Blueprint 20,250,267. |
| Four derivative rc exports and `ma_pair` | hμ : 0≤μ | STANDING | Blueprint 20,153,267. |
| Four derivative rc exports | hz, first conjunct: ∀t∈J, NoCollision(z t).1 | SOURCE | R1, blueprint 156. |
| Four derivative rc exports | hz, second conjunct: ∀t∈J, HasDerivAt z X_H(t) t | SOURCE | R2, blueprint 157. |
| Measure exports except Borel-only | ha : ∀i, 0<a i | STANDING | Blueprint 250. |
| `ma_coll`, `ma_pair`, `mp_a_box`, parent | hη : 0<η | STANDING | Blueprint 211,250,267. |
| Three ma exports | AxisData.gap_pos : 0<γ | STANDING | Canonical gap, blueprint 212. |
| Same | AxisData.le_axis : ∀i, γ≤a i | STANDING | Minimum definition, blueprint 212. |
| Same | AxisData.le_diff : ∀i≠j, γ≤|a i-a j| | STANDING | Minimum definition, blueprint 212. |
| Same | AxisData.axis_le : ∀i, a i≤A | STANDING | Maximum definition, blueprint 212. |
| `ma_tube` | hS : MeasurableSet S | SOURCE | S1, blueprint 269. |
| Three ma exports | hSt : S⊆Uζ* | SOURCE | S1, blueprint 269. |
| `ma_coll`, `ma_pair` | hKS : range K⊆S | SOURCE | Clause of selected S2 witness, blueprint 270. |
| `ot_curve` | H : Phase(n*2)→ℝ | TYPING | Generalizes the two source model instances. |
| `ot_curve`, `ma_pair` | w : Fin(n*2)→ℝ | TYPING | Blueprint 195,270. |
| `ot_curve`, `ma_coll`, `ma_pair` | K : (Fin(n*2)→ℝ)→Phase(n*2) | TYPING | Blueprint 195,270. |
| `ot_curve` | hnc : ∀φ, NoCollision(K φ).1 | SOURCE | Blueprint 197,200,204. |
| `ot_curve` hK | AnalyticOnNhd ℝ K univ | SOURCE | Assumed IsPhysicalTorus, frozen clause (i). |
| Same | ∀θ, DifferentiableAt ℝ H (K θ) | SOURCE | Frozen clause (ii). |
| Same | ∀θ k, K(θ+k)=K θ | SOURCE | Frozen clause (iii). |
| Same | K θ=K θ′ → ∃k, θ′=θ+k | SOURCE | Frozen clause (iv). |
| Same | ∀θ, Injective(fderiv ℝ K θ) | SOURCE | Frozen clause (v). |
| Same | ∀θ u v, symplecticForm(DK u)(DK v)=0 | SOURCE | Frozen clause (vi). |
| Same | ∃γ τ, 0<γ ∧ d-1<τ ∧ IsDiophantine γ τ w | SOURCE | Frozen clause (vii); frequency property is an input here, not a campaign theorem. |
| Same | ∀θ t, HasDerivAt (s↦K(θ+s•w)) X_H t | SOURCE | Frozen clause (viii), blueprint 204. |
| `mp_b_measure`, Borel export, parent's (b) | c : ℝ | TYPING | Source c-chart parameter. |
| Same | hc : 0<c | SOURCE | Meaning of source c-chart. |
| Same | O : Set Phase(n*2) | TYPING | Blueprint 253. |
| Same | hO : IsOpen O | SOURCE | Blueprint 253. |
| Same | Ψ : Phase(n*2)→Phase(n*2) | TYPING | Blueprint 253. |
| Same hΨ | AnalyticOnNhd ℝ Ψ O | SOURCE | IsChart clause, Part 1 c-chart. |
| Same hΨ | ∀z∈O u v, Ω(DΨu,DΨv)=c Ω(u,v) | SOURCE | IsSymplecticOn clause, Part 1 c-chart. |
| Same hQ1 | z+angleShift k ∈ O | SOURCE | Q1, σ=0, blueprint 253. |
| Same hQ1 | Ψ(z+angleShift k)=Ψ z | SOURCE | Q1, σ=0. |
| Same | hQ2 : equal images → ∃k, z′=z+angleShift k | SOURCE | Q2, blueprint 253. |
| Same | A : Set Phase(n*2) | TYPING | Blueprint 253. |
| `mp_b_measure`, parent's (b) | hA : NullMeasurableSet A | SOURCE | Lebesgue measurability, blueprint 253. |
| Borel export | hA : MeasurableSet A | SOURCE | Conditional Borel clause, blueprint 253. |
| Three chart occurrences | hAO : A⊆O | SOURCE | Blueprint 253. |
| Same | hAper : ∀k, translation k '' A=A | SOURCE | Blueprint 253. |
| `mp_b_measure`, parent's (b) | hApos : 0<volume A | SOURCE | Explicit positive measure premise, blueprint 253; graph 12537. |
| Reconstruction / curve conclusions, `ma_pair` | t : ℝ | TYPING | Time variable, in source order. |
| Reconstruction conclusions | ht : t∈J | SOURCE | Source time-set membership. |
| Reconstruction conclusions | i : Fin n | TYPING | Source planet index. |
| `rc_a_lengths` conclusion | j : Fin n | TYPING | Second source planet index. |
| `rc_a_lengths` conclusion | hij : i≠j | SOURCE | Source distinct-pair restriction. |
| `rc_a_lengths` symmetry conclusion | i,j : Fin(n+1) | TYPING | Strengthened all-pair symmetry. |
| Curve / ma exports | φ : Fin(n*2)→ℝ | TYPING | Source angle universal, before t. |
| Box-bound conclusions | S : Set Phase(n*2) | TYPING | Every source subset. |
| Box-bound conclusions | hS : S⊆Uη | SOURCE | Source subset premise. |

Bin counts by row above (shared rows are schemas, not unique runtime arguments):
TYPING 22, STANDING 12, SOURCE 30, RULED 0, EXCESS 0. Shared schemas
apply once per occurrence; unused source assumptions are omitted, never replaced
by result-shaped assumptions.

There are **no new definitions, abbreviations or structures** in AssemblyNodes:
definition classification is N/A. Existing meaning-carrying bodies were checked
at use sites. `Phase d` is the product of two Pi spaces; physical length is
`sqrt (Σv_k²)` and never the ambient max norm. Tube/box estimates use the max
norm intentionally. No fallback/default witness or off-domain branch is introduced.

`AxisData` is not merely accepted as “typing”: all four mathematical fields are
listed above. For source axes and n>0, the existing proved
`axisData_canonical hn ha hinj` constructs precisely
`AxisData a (axisGap a) (axisMax a)`. Canonical ma-coll and ma-pair applications
were independently elaborated from those source premises, with no AxisData
hypothesis. Thus no axis-gap estimate is smuggled in as an extra premise. Selecting
K from S2 before φ,t preserves the source's witness dependence. Generic K results
are stronger, not assumptions of the desired collision or pair-bound conclusions.

## Proof review and adversarial checks

The full three-dot diff and every proof body were read. Reconstruction exports
project the existing `reconstruction` result; the Sun force export independently
reindexes its filtered Fin(n+1) sum using `Finset.sum_filter`,
`Fin.sum_univ_succ` and `simp`, so its term at zero disappears in the proof.
The signs, μ factors, actual masses, all ordered pairs and cubic physical length
match the source. `rc_a_lengths` needs no positive barycentric denominator because
its difference identities cancel the shared translation even for total division.

The torus curve uses exactly clause (viii), with collision checked at φ+t•w.
The three ma proofs use radius min inequalities and whole-range containment;
μ never enters the choice of d,D. For mp-a, positive masses remove the absolute
values in the landed momentum maximum. Positive box radii justify
`Real.volume_pi_ball`; the phase product volume gives the two factors, each with
exponent n*2. Arbitrary subsets use outer-measure monotonicity and need not be
measurable. The chart proof distinguishes null measurability from Borel
measurability and consumes the actual full-lattice Q1/Q2 assumptions.

Rejected candidate findings: illicit hApos (explicitly sourced); hidden AxisData
obligations (canonical construction checked); max-norm/physical-norm substitution
(no substitution); missing μ in force masses (present through actualMasses);
Borel claim from merely null-measurable A (separate Borel hypothesis).
F1 remains only at the unusually strict literal-export gate.

Import-closure inspection traversed 62 project modules: no Provider edge and no
Frozen/Theorems edge. Therefore there is no DRAFT_SORRY theorem import to waive.
No new public name duplicates another project declaration's short name; all
new names are inside `KAM.Planetary`, with no harmful root declaration.

## Independent validation

Final Lean-affecting commands were run serially, using one thread and nice 5.
A scratch harness typo (untyped t and missing `open KAM.ODE`) initially caused
probe elaboration errors; these were corrected only in scratch, then the full
probe passed. All 13 axiom results were printed on both runs.

Execution deviation: the first lint invocation was started without the explicit
thread/nice prefix and overlapped the scratch-probe stage. On inspecting the
script, its internal ABI check was found to invoke Lean. That lint invocation
completed; it was repeated below with the required environment and with no
other Lean/Lake/checker job running. This is an auditor workflow deviation,
not a package defect. No production file was changed to accommodate any check.

Commands and independent results:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp6b KAM.Planetary.Newtonian.AssemblyNodes
# exit 0: [inp-gate] slot 2 acquired 01:27:25
# Build completed successfully (9108 jobs).

LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP6bAudit.lean
# final exit 0; 13 #print axioms lines; all three source-domain probes passed.

LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Newtonian.AssemblyNodes
# exit 0: replaying KAM.Planetary.Newtonian.AssemblyNodes

LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
# exit 1, solely the permitted generated-root check:
# KAM.lean is out of date; run scripts/gen_root_imports.py
# check_lean_modules: PASS (1195 Lean files, 0 comparator configurations)
# FROZEN-ANCHOR GUARD OK
# ABI HASHES OK (144 frozen declarations)

git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
# exit 0, empty output.
git diff --check inp...HEAD
# exit 0, empty output.
```

Build warnings were replayed only from dependencies: Energy.lean:106 (hm,hκ),
Hamiltonian/Algebra.lean:146 (hc), Hamiltonian/Chart.lean:193 (hc). None originates
in AssemblyNodes. The target has 261 lines, no line exceeding 100 characters,
all required module headers, and no forbidden tokens or resource overrides.
The expected stale generated root is expressly excluded as a finding by the
handoff; it was not regenerated.

Exact axiom output, one entry for every public theorem:

```text
'KAM.Planetary.rc_a_lengths' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rc_sun_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rc_planets_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rc_vplanet_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rc_vsun_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ot_curve' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ma_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ma_coll' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ma_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mp_a_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mp_b_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mp_b_measurableSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.measure_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The successful scratch harness (SHA256
`aac13df71bd5aac3ce3bc12b78d7fe215410b164da1c5d7d08cf6514ba25ad0e`)
contained these 13 `#print axioms` commands, canonical source-only ma-coll and
ma-pair instantiations, and the positivity-iff derivation above. Scratch probes
and validation logs were removed after recording their results in this report.

## Source defects, limits and closeout

No suspected defect in the pinned mathematical source or blueprint was found.
F1 is a package export deviation; it does not show the graph/source statement
false. In particular graph 12537 explicitly includes hApos, so the missing iff
must not be reported as missing proof of the reverse direction for arbitrary A.
Graph LEAN_STATUS/LEAN_NOTE fields remain unchanged by this report-only audit.

This does not certify the entire Part 6 dependency development, Part 11's actual
positive-measure torus producer, partial-lattice charts, P-G/P-PLANAR/P-FIXED
headline closure, or any frozen theorem seal. It certifies the bounded proof and
source checks above, with the literal node gate failing at F1. No source repair,
production repair, commit, graph status update or generated-file update was made.

Only requested repository output:
`/root/code/KAM-inp-gp6b/docs/tracks/P/audits/GAP-P6b-audit-1.md`.
