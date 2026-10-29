# GAP-P13 independent package audit 1

Overall verdict: **FAIL** for graph-gap completion: **10 nodes PASS, 2 nodes FAIL**.
The failing nodes are exactly `stepP:p3:sum-doubling` and `stepP:p3:sum-weighted`.
The Lean proofs are sound: the targeted build, all 17 public axiom checks and kernel replay pass.
The failure is the source-facing hypothesis boundary, not a counterexample to the estimates.
No frozen theorem anchor is proved or sealed by this unsigned package; per-anchor seal verdict is N/A.

## Scope, authority and frozen snapshot

Focused tier-2, refute-first audit, 2026-10-29. Read AGENTS.md, docs/PLAN.md,
docs/DECISIONS.md, the package audit brief, Track P statement, the supplied handoff,
the GAP-P13 section of the main worktree's `.drafts/briefs/offload-main/GAP-PLAN-P.md`,
all twelve exact NODE records and their cited blueprint passages. The explicit user path
supersedes the generic brief's main-worktree output location. Only this report is a
persistent audit-created file; temporary probes/logs are confined to `.lake/abi-scratch/`.
No implementation, manifest, generated root, git state, or source repair is authorized.

HEAD: `3223b51468dae8941e48d4d92defd3a602e71e14`.
Comparison `inp`: `c1839fee225146e0c60e389ca73433801f3a9c52`.
The full `git diff inp...HEAD` was inspected: two new modules, 376 insertions.
The pre-existing untracked handoff is outside that diff and was preserved.
All implementation locators below refer to this HEAD (snapshot frozen-v1).

| Frozen input | SHA-256 |
|---|---|
| `KAM/Planetary/Hamiltonian/Part1Nodes.lean` | `87aa8e0e8649a3af1f1aa0badb808bb97f54db41c442c84e08a22bc7cb1474b4` |
| `KAM/Planetary/TwoScale/SumsNodes.lean` | `465e0fe3229edb13503e16cbbd8263246423d30d5ccbb44761cfc2a878555bfa` |
| `docs/graph/P/DEPGRAPH.md` | `c21e6cef18a1f08ff50fccfecdde48506faef57a7504f2cff51be78c0e95ae0e` |
| `blueprint-P/parts/p1-hamiltonian-tools.tex` | `71125916b1c5316e440916dd15e22d267a891c2d2b97188a7afb46ba2ff6af33` |
| `blueprint-P/parts/p3b-two-scale-limit.tex` | `e923c1f3856cd7c27fc73b1a5bdb21139a31d0484e30421c4e0db9cfdff86c1a` |

The current handoff explicitly calls all additions UNSIGNED. There is no new signed
surface to compare with a signature file, and no provider/frozen-export seal-body probe
applies. The GAP-P13 node table is the slice inventory. The earlier P23 design maps the
sum steps at lines 165–166; the current handoff and graph require literal unsigned exports.
The manuscript-audit and lean-statement-audit protocols informed the independent source
reconstruction and expanded-premise review. No delegation or source changes were used.

## Node and declaration ledger

Names below have prefix `KAM.Planetary.`. P1 denotes
`blueprint-P/parts/p1-hamiltonian-tools.tex`; P3b denotes
`blueprint-P/parts/p3b-two-scale-limit.tex`. DG denotes `docs/graph/P/DEPGRAPH.md`.
Every row was checked against SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS and SOURCE_CONCLUSION.

| Node (DG record start; source lines) | Declaration (implementation line) | Verdict | Evidence / strength |
|---|---|---|---|
| `bpP:p1:typical` (2438; P1:119–121) | `typical` (Part1Nodes:201) | PASS | All three clauses: explicit one-oscillator map with sin first and cos second; positive-action chart and full 2π integer invariance; positive scaling; chart composition and both inverse factors in the pullback identity. Purely universal data are reordered in clause (3), with no existential witness or changed dependence. |
| `stepP:p1:pc-a` (2502; P1:137) | `pc_a` (145) | PASS | Exact Ω scaling, signed determinant c^d and lattice formula. Stronger: arbitrary real c, including 0 and negative c. The derivative's block-diagonal identification is proved at 154–158. |
| `stepP:p1:pc-b` (2530; P1:138) | `pc_b` (163) | PASS | Field transport and both partial derivative formulas at S_c z; the same time variable and canonical order are retained. Nondifferentiability handled through the specified total fderiv, not an additional premise. |
| `stepP:p1:tt-an` (2259; P1:111) | `tt_an` (34) | PASS | Analytic composition and H differentiability at every transported point; original LT/chart assumptions. |
| `stepP:p1:tt-an` (same) | `tt_an_range` (42) | PASS | Companion export supplies the exact range-membership clause and U inclusion; hU is the source's explicit cylinder premise. Together the two exports cover the node. |
| `stepP:p1:tt-lat` (2289; P1:112) | `tt_lat_cyl` (48) | PASS | θ then integer k; correct projection to the fast block and frozen 2π fastShift. The intermediate Ψ(Kθ+Lk) identity is proved by rewriting L2 at 58. |
| `stepP:p1:tt-lat` (same) | `tt_lat_phys` (62) | PASS | Physical periodicity, with the same intermediate L2 rewrite at 68. |
| `stepP:p1:tt-inj` (2320; P1:113) | `tt_inj_cyl` (72) | PASS | θ, θ′, fast integer k, then equality premise; returns integer ell giving θ′=θ+ell. Fin.append(k,0) and sum of integer shifts are proved, not assumed. |
| `stepP:p1:tt-inj` (same) | `tt_inj_phys` (90) | PASS | Physical zero-shift case; equality symmetry has no strength effect. |
| `stepP:p1:tt-lag` (2349; P1:114) | `tt_lag` (101) | PASS | Chain-rule equality, derivative injectivity and both equalities Ω(D𝒦u,D𝒦v)=cΩ(DKu,DKv)=0. θ precedes u,v. |
| `stepP:p1:tt-flow` (2380; P1:115) | `tt_flow` (120) | PASS | θ then t; exact HasDerivAt conclusion. Uses only pointwise O membership/differentiability/L6 at t, weaker assumptions than requiring them for all s. |
| `stepP:p1:tt-dio` (2409; P1:116) | `tt_dio` (133) | PASS | Reuses the source's positive γ, τ>d−1 and Diophantine hypothesis to supply exactly clause (vii) of IsPhysicalTorus. No cylinder Diophantine clause is invented. |
| `bpP:p3b#kam-bounds` (6982; P3b:3–4) | `kam_bounds` (SumsNodes:25) | PASS | Both strict bounds, coefficient 8192n and c=24^(τ+1)/6 retained. n>0 is standing source data (P3a:60 has n₁,n₂≥1), not an excess premise. Arbitrary real E,τ generalizes the source. |
| `stepP:p3:sum-doubling` (5291; P3b:10–11) | `sum_doubling` (56) | FAIL as node export | Correct abstract estimate, including summability and geometric denominator, but assumes nonnegativity, initial smallness and quadratic decay for an arbitrary sequence rather than deriving them in the original KAM setting. F1. |
| `stepP:p3:sum-doubling` (same) | `PsiSteps.seq_sum_doubling` (107) | FAIL as node export | Correct instantiated conclusion, but takes PsiSteps, whose eHat_sq field assumes the graph dependency to be discharged. F1. |
| `stepP:p3:sum-weighted` (5320; P3b:12–13) | `sum_weighted` (85) | FAIL as node export | Correct complete pointwise chain and sum, but assumes the recurrence and c*e₀≤1/2 as extra inputs. The non-strict endpoint strengthens the conditional helper but does not remove its extra premises. F2. |
| `stepP:p3:sum-weighted` (same) | `PsiSteps.seq_sum_weighted` (117) | FAIL as node export | Correct source sequence and c, but PsiSteps is an additional derived-output bundle. F2. |

Completeness: 12/12 nodes inspected; 17/17 new public declarations classified.
All Part 1 conclusions occur in the exports or their proofs. The two sum nodes have
correct conditional helpers, but lack a named export at the prescribed original-source
hypothesis boundary. No other node mapped by GAP-P13 to these modules was omitted.

## Findings and adversarial refutation

**F1 — blocking interface mismatch: `stepP:p3:sum-doubling`.**
DG:5298 expressly says: “the sequences under the original KAM hypotheses and the bounds
(3.4) ... previously established bounds are supplied through DEPS, not additional hypotheses”.
SumsNodes:56–57 instead takes `he`, `he₀`, `hquad`; its proof calls `sums` with these.
The sequence-specific alternative at 107 assumes `P : PsiSteps ...` and at 113–114
extracts `P.hyp` and `P.eHat_sq`. The latter is literally the quadratic recurrence
`∀ j, eHat (seq p (j+1)) < eHat (seq p j)^2`
(LimitMapPsi:73). This is a proved dependency output, not an original source premise.

**F2 — blocking interface mismatch: `stepP:p3:sum-weighted`.**
DG:5327 repeats the same explicit hypothesis restriction. SumsNodes:85–86 assumes
`he`, `he₀`, `hquad`, `hc`, `hce`. Its specialization at 117 still requires the same
PsiSteps bundle; lines 125–127 use the assumed stage hypotheses and quadratic estimate,
and obtain smallness through `P.kam_small`. The numeric statement and constants are
correct; the missing piece is its source-facing assembly within the exported theorem.

Refutation pass for both: inspected the actual producer `iterative_steps`
(LimitMapPsi:79–91), not merely a name/graph edge. It proves existence of PsiSteps from
`H : KamHyp D sbar p h f` on the same stage witnesses. Independently elaborated two
source-premise examples with the **full literal conclusions** of the respective sequence
exports, replacing P with H. Both bodies were:

```lean
  obtain ⟨Ds, hs, fs, Ψ, Φ, is, _, _, P⟩ := iterative_steps H
  exact P.seq_sum_doubling m
```

and respectively `exact P.seq_sum_weighted`. Both examples compiled without diagnostics.
Thus an assertion of missing mathematics would be refuted. The reportable findings
survive as **literal-export failures**: these two assembly terms do not occur in either
new node export. The handoff explicitly requires a named unsigned export to state its
node under only source hypotheses; a producer available elsewhere does not delete a
binder from that export. No claim that the estimates themselves are false is made.
Suggested repair, not performed: preserve/rename the abstract results as conditional
helpers and export each full estimate from KamHyp, constructing P inside its proof.

Other candidate issues were refuted: arbitrary L specializes to angleShift and is a
stronger transport theorem; chart openness is unnecessary for pointwise AnalyticOnNhd;
negative/zero scaling is only added in the valid algebraic pc_a; the polar ordering and
2π period are literal; n>0 is supplied by the source's positive block dimensions;
fully universal reordering in typical has no witness-dependence change.

## Expanded binder audit

All dimensions, functions, sets, lattice maps, sequence indices, vectors and point/time
arguments are TYPING data. There are no new instance binders, RULED premises or
choice-dependent constants in these 17 theorems. The table lists every explicit logical
binder (shared schemas cover both cylinder/physical variants).

| Declaration / binder | Bin | Expanded meaning and source |
|---|---|---|
| tt_an: hc | SOURCE | c>0, P1:95. |
| tt_an: hΨ | SOURCE | AnalyticOnNhd Ψ O plus Ω-preservation for all z,u,v, P1:47,95. |
| tt_an: hK | STANDING | All LT clauses L1–L6 listed below, P1:81–90,95. |
| tt_an_range: hU | SOURCE | Ψ''range K⊆U, P1:102,111. |
| tt_lat_cyl/phys: hK | STANDING | LT L1–L6; only L1 range and L2 used, P1:95,112. |
| tt_lat_cyl/phys: hQ1 | SOURCE | Shifted point in O plus image-shift identity, P1:97; weaker than full O+ι=O. |
| tt_inj_cyl/phys: hK | STANDING | LT L1–L6; L1 range, L2,L3 used, P1:95,113. |
| tt_inj_cyl/phys: hQ2 | SOURCE | Image equality modulo shift implies preimage equality modulo integer lattice, P1:98. |
| tt_inj_cyl/phys: equality arrow | SOURCE | The image equality being tested, P1:113. |
| tt_lag: hc, hΨ, hK | SOURCE, SOURCE, STANDING | Same c/chart/LT expansion as tt_an, P1:95,114. |
| tt_flow: hc, hΨ | SOURCE, SOURCE | Standing chart context, P1:95,115. |
| tt_flow: hO | SOURCE | y(t)∈O; restriction of the source's all-s range, P1:115. |
| tt_flow: hdiff | SOURCE | G differentiable at y(t), P1:115. |
| tt_flow: hflow | SOURCE | L6 at θ,t, explicitly among the node hypotheses, P1:89,115. |
| tt_dio: hγ, hτ, hw | SOURCE (3) | Positive γ, τ>d−1, IsDiophantine γ τ w, P1:103,116. |
| pc_a | none | No logical premise. |
| pc_b: hc | SOURCE | c>0, P1:128,138. |
| typical: 0<c arrow | SOURCE | Positive scale, P1:120. |
| typical: IsChart c₁ Ψ₁ O₁ arrow | SOURCE | Analyticity and symplectic identity of first chart, P1:120. |
| typical: IsChart c₂ Ψ₂ O₂ arrow | SOURCE | Analyticity and symplectic identity of second chart, P1:120. |
| typical: MapsTo arrow | SOURCE | Ψ₁(O₁)⊆O₂, P1:120. |
| kam_bounds: hn | STANDING | n=n₁+n₂ with n₁,n₂≥1, P3a:60. |
| kam_bounds: h | SOURCE | ĉ E<1, P3b:3–4. |
| sum_doubling: he | EXCESS for node | Nonnegativity of every arbitrary sequence value; derived in source setting. |
| sum_doubling: he₀ | EXCESS for node | Initial <1/2, derived in source setting. |
| sum_doubling: hquad | EXCESS for node | The iterative quadratic estimate is assumed. |
| sum_weighted: he, he₀, hquad | EXCESS (3) for node | Same three derived inputs. |
| sum_weighted: hc | STANDING at source c | Positivity follows from c=24^(τ+1)/6; abstract helper takes arbitrary c. |
| sum_weighted: hce | EXCESS for node | Derived smallness c e₀≤1/2, not an original source assumption. |
| seq_sum_doubling/weighted: P | EXCESS for node | Expanded 15-field derived-output bundle below. |

LT expansion used above: L1 is analyticity, ∀θ Kθ∈O and differentiability of G;
L2 is ∀θ,k the translated equality; L3 is equality implying existence of an integer
parameter shift; L4 is ∀θ derivative injectivity; L5 is ∀θ,u,v zero Ω-pullback;
L6 is ∀θ,t HasDerivAt with the Hamiltonian field. Every conjunct is explicitly a source
standing hypothesis (P1:84–89). None supplies the transported conclusion being proved.
IsChart expands to analyticity and the source conformally symplectic derivative identity.
IsDiophantine is the frozen lower bound, with γ>0 and τ>d−1 separately supplied.

For P, every field is derived output relative to the source-facing node; expanding its
hyp field does not convert an all-stages hypothesis into the original initial hypothesis:

| PsiSteps field (LimitMapPsi:43–75) | Expanded content / bin relative to these nodes |
|---|---|
| hyp | ∀j KamHyp at stage j: EXCESS as an all-stage premise. Each KamHyp expands to a_pos, b_pos, τ_gt, positive (nine scalar positivities), gamma_order, widths (two), normalized (three), L_bound, holo, real_h, real_f, f_class, f_bound, injective, hessian (operator/row bounds and an inverse with its identities and bounds), small. The initial KamHyp is SOURCE; its later-stage copies are derived dependencies. |
| Phi_zero | Φ₀=id: EXCESS derived initialization output. |
| Phi_succ | ∀j Φ_(j+1)=Φ_j∘Ψ_(j+1): EXCESS derived output. |
| phi_diff | ∀j complex differentiability of Φ_j: EXCESS derived output. |
| phi_real | ∀j reality of Φ_j on real domain: EXCESS derived output. |
| phi_per | ∀j periodic winding of Φ_j: EXCESS derived output. |
| psi_diff | ∀j complex differentiability of Ψ_(j+1): EXCESS derived output. |
| psi_real | ∀j reality of Ψ_(j+1): EXCESS derived output. |
| psi_per | ∀j periodic winding of Ψ_(j+1): EXCESS derived output. |
| psi_maps | ∀j stage mapping property: EXCESS derived output. |
| psi_bd | ∀j three stage displacement bounds: EXCESS derived output. |
| tube | ∀j stage-domain inclusion: EXCESS derived output. |
| eHat_sq | ∀j strict quadratic decay: EXCESS, the decisive derived numerical step. |
| rho_lo | ∀j lower radius comparison: EXCESS derived output. |
| rho_hi | ∀j upper radius comparison: EXCESS derived output. |

Logical-input counts at the top level, before expanding conjunctions: SOURCE 25,
STANDING 8, RULED 0, EXCESS 9 (counting P once per sequence export);
TYPING consists of all remaining data binders. These counts include the two tested image
equality arrows and four logical arrows inside typical. The expansion tables, rather
than the counts, determine the verdict. EXCESS here judges suitability as the named
source result; the abstract theorems remain valid conditional mathematics.

## Definitions, carriers, normalization and proof review

There are **no new def, abbrev, structure or instance declarations** in either module.
Definition classification: BODY_MATCH, PUBLIC_CARRIER, WELL_DEFINEDNESS,
CHARACTERIZATION and CHOICE_INDEPENDENCE are N/A for new definitions; definition
verdict PASS (empty inventory). Private sum_half and sum_pow_le are theorem helpers.

Inspected meaning-bearing dependencies: Phase is literally the product of real Fin
function spaces; IsCylinderTorus and IsPhysicalTorus retain all frozen clauses;
angleScale scales positions only; chartPullback is c⁻¹H∘Ψ; fullShift is the full 2π
position lattice; fastShift is the frozen fast-only shift; IsLatticeTorus is exactly
L1–L6 with a generalized lattice L; kamConstant is max(2^13 n,24^(τ+1)/3);
eHat and seq use the actual constants and nextScale recurrence. PsiSteps was expanded
rather than accepted by its name. No junk new object or fallback definition exists.
The pc_b nondifferentiable branch uses the explicit source convention for fderiv,
not an invented off-domain object.

Proof review covered all 376 added lines, including the Fin lattice manipulations,
polar-map identification with oscillatorPolar, determinant sign, component chain rules,
pointwise flow transfer and the geometric-series comparison with positive 1−e_m.
The abstract sum hypotheses are sufficient and the conclusion chains are correct.
The seq proofs instantiate these correctly, with seq p 0 definitionally p.
No wider constant dependence, norm change, ambient carrier change, or altered frequency
was found. No new declaration lives at the root namespace. Repository search found each
new public short theorem name only in its own declaration; the two seq names live under
PsiSteps. No reused project public HELPER name or harmful shadow was found.

## Verification evidence

All Lean-related commands were serialized, with LEAN_NUM_THREADS=1 and nice -n 5.
No library clean/rebuild from scratch or package/cache mutation was requested.
The gate itself invokes nice -n 5 lake build; its slot wait is expected.

1. Full comparison: `git diff inp...HEAD` — exactly the two audited additions.
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` — empty, exit 0.
   `git diff --check inp...HEAD` — empty, exit 0.

2. Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp13 KAM.Planetary.Hamiltonian.Part1Nodes KAM.Planetary.TwoScale.SumsNodes
```

Exit 0; `[inp-gate] slot 1 acquired 01:35:13 ...` and
`Build completed successfully (9237 jobs).`
Existing dependency warnings were replayed (unused variables/simp arguments and
deprecated names); no warning in either new module. The job count includes cached
Mathlib dependencies, not an audit-requested clean library rebuild.

3. Axiom/type probe at `.lake/abi-scratch/GAPP13Audit.lean`:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP13Audit.lean
```

Exit 0. The probe imported both modules, then issued `#print axioms` and `#check @...`
for every one of the 17 public declarations in ledger order. Exact axiom output:

```text
'KAM.Planetary.tt_an' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tt_an_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tt_lat_cyl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tt_lat_phys' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tt_inj_cyl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tt_inj_phys' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tt_lag' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tt_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tt_dio' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pc_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pc_b' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.typical' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.kam_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sum_doubling' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sum_weighted' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.seq_sum_doubling' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.seq_sum_weighted' depends on axioms: [propext, Classical.choice, Quot.sound]
```

4. Kernel replay, one invocation:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Hamiltonian.Part1Nodes KAM.Planetary.TwoScale.SumsNodes
```

Exit 0. Complete output:

```text
replaying KAM.Planetary.TwoScale.SumsNodes
replaying KAM.Planetary.Hamiltonian.Part1Nodes
```

5. Source-premise composition probes (the two full conclusions described under F1/F2):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP13Bridge.lean
```

Exit 0, empty output. These are audit examples only; no tracked theorem was added.

6. Import closure: a recursive traversal of KAM imports found 191 project module names,
no provider imports and no frozen theorem imports. All 54 manifest-owned frozen inputs
in the closure are definitions in state SEALED. Therefore no DRAFT_SORRY import, provider
quarantine bypass or project axiom was found. No theorem seal/type equality applies.

7. Source hygiene: 245 and 131 lines respectively, maximum width 97 characters each;
module headers, copyright, public imports, module docs and public sections present.
Forbidden-token/override/EuclideanSpace search in the two modules returned no matches.

8. Repository lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1 solely for the explicitly permitted stale generated root. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1196 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Module checking, frozen guard and all 144 ABI hashes pass. No other lint finding.

## Errata, limitations and closeout

No new suspected defect in a pinned mathematical source or frozen declaration was found.
The notation for the component derivatives in P1:138 suppresses evaluation at S_c z;
the Lean statement correctly writes this evaluation and no mathematical change is needed.
The GAP-P13 design's phrase “over the abstract sequence of sums, plus the instance for seq”
does not override the graph's explicit prohibition on assuming derived numerical bounds:
F1/F2 identify a package/interface deviation, not a new source erratum.

The stale generated root is expressly left for the orchestrator at merge. The audit
introduced no mathematical deviations. Broader correctness of unchanged upstream proofs,
Track I/N roots, the planetary headlines and consumer closure outside this two-module
slice are not certified. Fresh build/axiom/kernel checks do not themselves establish
literal graph fidelity or theorem sealing.

Closeout: full branch diff reviewed; 12/12 graph records and cited source passages read;
17/17 public declarations classified and axiom checked; both modules kernel-replayed;
source-premise refutation compositions compiled; F1/F2 remain interface blockers under
the explicit audit focus. No implementation repair performed. Temporary audit probes
and logs are removed after their evidence is incorporated here.
