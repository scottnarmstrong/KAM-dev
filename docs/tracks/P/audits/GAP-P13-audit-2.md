# GAP-P13 independent package audit 2

Overall verdict: **PASS WITH NOTES**. **12/12 graph nodes PASS**; no blocking finding.
Audit 1's F1 and F2 are resolved by the source-facing exports now at
`SumsNodes.lean:135` and `:145`. All 19 new public theorems pass fresh type/axiom
checks; both modules pass targeted compilation and kernel replay.
No frozen theorem anchor is implemented or sealed by this unsigned package:
per-anchor seal readiness is **N/A**, not a claim about the planetary headlines.

## Authority and snapshot

Independent refute-first review on 2026-10-29, limited to
`KAM/Planetary/Hamiltonian/Part1Nodes.lean` and
`KAM/Planetary/TwoScale/SumsNodes.lean`. Read AGENTS.md, PLAN, DECISIONS,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the supplied handoff and
its AUDIT FOCUS, audit 1, the GAP-P13 section of
`/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P.md`, the Track P statement
conventions, all 12 NODE records and the blueprint passages cited by those records.
Inspected the relevant frozen carriers and predicates and expanded the source and
intermediate hypothesis bundles. Current code and graph take precedence over the
handoff's older declaration names/count. The explicit user path overrides the
brief's generic main-worktree output location.

- HEAD: `f506be3fe0f244b6d2d2735623a34170b286e44b`.
- Comparison ref `inp`: `8dc8bedc37b2b4dad2163b79fbcf35ff51fdffdb`.
- Merge base for `git diff inp...HEAD`: `c2be145a358746329fa8147c2f951d8bfc7ecbfb`.
- Full branch comparison: two Lean additions (245 and 156 lines), plus audit 1
  (336 lines) and the handoff (48 lines). All four additions reviewed; mathematical
  certification is confined to the two specified Lean modules.
- The round-2 change `ec27e9da..HEAD` renames the abstract helpers and adds two
  original-hypothesis exports. Part1Nodes is byte-identical to audit 1's snapshot.

| Input | SHA-256 |
|---|---|
| Part1Nodes.lean | `87aa8e0e8649a3af1f1aa0badb808bb97f54db41c442c84e08a22bc7cb1474b4` |
| SumsNodes.lean | `add1004929379b8ad0b162d2adf161f74842f2c80630ed0a564cb99533480ad8` |
| docs/graph/P/DEPGRAPH.md | `c21e6cef18a1f08ff50fccfecdde48506faef57a7504f2cff51be78c0e95ae0e` |
| blueprint-P/parts/p1-hamiltonian-tools.tex | `71125916b1c5316e440916dd15e22d267a891c2d2b97188a7afb46ba2ff6af33` |
| blueprint-P/parts/p3b-two-scale-limit.tex | `e923c1f3856cd7c27fc73b1a5bdb21139a31d0484e30421c4e0db9cfdff86c1a` |

There are no SIGNED declarations or providers in this slice. Exact frozen/provider
type and seal-body probes therefore do not apply. The package's unsigned exports
are assessed against the literal graph contracts, not substituted for signed surfaces.
No delegation, implementation edits, generated-file regeneration or state-changing
git command was performed.

## Node and public declaration ledger

Every row was compared with SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS and
SOURCE_CONCLUSION and its cited blueprint text. Names have prefix
`KAM.Planetary.`. P1 = `blueprint-P/parts/p1-hamiltonian-tools.tex`;
P3b = `blueprint-P/parts/p3b-two-scale-limit.tex`. H = Part1Nodes; S = SumsNodes.

| Node (graph line; blueprint lines) | Declaration (file:line) | Verdict | Literal conclusion and premise boundary |
|---|---|---|---|
| `bpP:p1:typical` (2438; P1:119–121) | `typical` (H:201) | PASS | All three clauses: explicit sin/cos polar map on positive action, full 2π integer invariance, positive scaling chart, composition and both pullback factors. Universal data are reordered in the composition bundle, with no witness dependence change. |
| `stepP:p1:pc-a` (2502; P1:137) | `pc_a` (H:145) | PASS | Symplectic scaling, signed determinant c^d and integer-position shift, in u,v,z,k order. Valid for every real c, stronger than c>0. |
| `stepP:p1:pc-b` (2530; P1:138) | `pc_b` (H:163) | PASS | Field identity and both partial derivative formulas at S_c z, in frozen position/momentum order; same time. Source total fderiv convention handles nondifferentiability. |
| `stepP:p1:tt-an` (2259; P1:111) | `tt_an` (H:34) | PASS | Analyticity and H differentiability at each transported point from original chart/LT assumptions. |
| `stepP:p1:tt-an` (same) | `tt_an_range` (H:42) | PASS | Companion export supplies image membership and U membership under the source's explicit containment. Together these exports cover the full node. |
| `stepP:p1:tt-lat` (2289; P1:112) | `tt_lat_cyl` (H:48) | PASS | θ then k, fast-block projection and frozen 2π shift; the intermediate Ψ(Kθ+Lk) equality is established by the L2 rewrite at H:58. |
| `stepP:p1:tt-lat` (same) | `tt_lat_phys` (H:62) | PASS | θ then k, physical periodicity; intermediate equality proved at H:68. |
| `stepP:p1:tt-inj` (2320; P1:113) | `tt_inj_cyl` (H:72) | PASS | θ,θ′,k then tested equality; produces integer ell with θ′=θ+ell. Q2 and L2/L3 prove the intermediate identities. |
| `stepP:p1:tt-inj` (same) | `tt_inj_phys` (H:90) | PASS | Physical zero-shift case, same parameter order; symmetry of the equality premise preserves strength. |
| `stepP:p1:tt-lag` (2349; P1:114) | `tt_lag` (H:101) | PASS | Exact chain-rule equality, injectivity, and Ω(D𝒦u,D𝒦v)=cΩ(DKu,DKv)=0; θ before u,v. |
| `stepP:p1:tt-flow` (2380; P1:115) | `tt_flow` (H:120) | PASS | θ then t; exact HasDerivAt conclusion with only the pointwise O membership, differentiability and L6 needed at t. Weaker premises than the full source orbit assumptions. |
| `stepP:p1:tt-dio` (2409; P1:116) | `tt_dio` (H:133) | PASS | Positive γ and τ>d−1 precede the frozen Diophantine assumption; supplies precisely the physical existential clause. No cylinder clause added. |
| `bpP:p3b#kam-bounds` (6982; P3b:3–4) | `kam_bounds` (S:25) | PASS | Both strict estimates, exact 8192n and 24^(τ+1)/6. n>0 follows from the standing positive block dimensions (P3a:60). Arbitrary real E and τ strengthen the scalar statement. |
| `stepP:p3:sum-doubling` (5291; P3b:10–11) | `sum_doubling` (S:135) | PASS | Initial KamHyp only; m then k≥m; both power comparisons, summability, geometric fraction and ≤2Ê_m. No recurrence or stage witness is a premise. |
| `stepP:p3:sum-weighted` (5320; P3b:12–13) | `sum_weighted` (S:145) | PASS | Initial KamHyp only; every k, exact c, complete three-part pointwise chain, summability and sum ≤2Ê₀. |
| Conditional helper for doubling | `sums_doubling_of_quad` (S:56) | PASS as helper | Explicit arbitrary-sequence nonnegativity, smallness and quadratic recurrence; distinct name and explicit conditional-helper docstring. |
| Conditional helper for weighted sum | `sums_weighted_of_quad` (S:85) | PASS as helper | Same recurrence data plus c≥0 and c e₀≤1/2; complete pointwise and summed conclusions. |
| Intermediate specialization | `PsiSteps.seq_sum_doubling` (S:107) | PASS as helper | Takes the derived PsiSteps bundle; used inside the source-facing export, not accepted alone as node closure. |
| Intermediate specialization | `PsiSteps.seq_sum_weighted` (S:117) | PASS as helper | Same qualification; instantiates c=24^(τ+1)/6 and seq p 0=p. |

Completeness: **12 nodes and 19 public theorems inspected**. No mapped node is omitted.
No new public declaration is being silently certified as an unconditional source result
when it is only a conditional helper.

## Refutation attempts and audit-1 disposition

**F1/F2 resolved.** Graph lines 5298 and 5327 require the sequences under the original
KAM hypotheses and say “previously established bounds are supplied through DEPS,
not additional hypotheses”. The current node exports satisfy that boundary literally:

```lean
-- S:141–142, inside sum_doubling (H : KamHyp ...) (m : ℕ)
obtain ⟨Ds, hs, fs, Ψ, Φ, is, _, _, P⟩ := iterative_steps H
exact P.seq_sum_doubling m
-- S:153–154, inside sum_weighted (H : KamHyp ...)
obtain ⟨Ds, hs, fs, Ψ, Φ, is, _, _, P⟩ := iterative_steps H
exact P.seq_sum_weighted
```

Inspected the producer at `LimitMapPsi.lean:79–91`: it constructs both ActionSteps
and PsiSteps from `iterative H` on the same existential stage witnesses. The new
conclusions mention only the deterministic numerical `seq p`, not chosen stage maps.
P.hyp supplies stage positivity and derived smallness; P.eHat_sq supplies strict
quadratic decay. These inputs are discharged inside the exported proofs. The former
abstract results have distinct `_of_quad` names. Both earlier failures are therefore
repaired in code, rather than reclassified by relying on an external composition.
Fresh `#check @...`, axiom checks and module kernel replay include both new exports.

Other candidate failures were refuted: generalized lattice L specializes to angleShift;
Q1 supplies weaker forward invariance than the source's set equality; chart openness
is unnecessary for these pointwise AnalyticOnNhd arguments; the lattice intermediate
equalities occur in the proofs; split tt_an/tt_an_range covers the explicitly mapped
range companion; negative/zero scale in pc_a is valid algebraic strengthening; polar
sin-first/cos-second has the frozen sign; denominator positivity uses source dimension
positivity; nondifferentiability is the specified total fderiv behavior. No changed
frequency, norm, period, ambient carrier or constant dependence was found.

## Premise expansion and definitions

All dimension/function/set/vector/time/index binders are typing data. Logical premises:

| Surface | Expanded premise content | Classification |
|---|---|---|
| tt_an, tt_lag | c>0; chart analyticity and derivative conformal symplectic identity; LT L1–L6 | Source/standing |
| tt_an_range | Ψ''range K⊆U | Source |
| tt_lat variants | LT L1–L6; Q1 membership and image-shift identity | Source/standing |
| tt_inj variants | LT L1–L6; Q2 injectivity modulo source lattice; the tested equality | Source/standing |
| tt_flow | c>0, chart, K(θ+tw)∈O, pullback differentiability there, original HasDerivAt L6 at θ,t | Source |
| tt_dio | γ>0, τ>d−1, frozen IsDiophantine lower bound for all nonzero integer indices | Source |
| pc_a | None | Stronger algebraic export |
| pc_b | c>0 | Source |
| typical | c>0 for scaling; two chart predicates and MapsTo for composition | Source |
| kam_bounds | n>0; kamConstant n τ * E<1 | Standing/source |
| sum_doubling, sum_weighted | Initial KamHyp D sbar p h f only | Source/standing bundle, expanded below |
| sums_*_of_quad | Nonnegative arbitrary e, e₀<1/2, e_(j+1)≤e_j²; weighted helper also c≥0 and ce₀≤1/2 | Explicit conditional inputs; not node assumptions |
| PsiSteps.seq_sum_* | All-stage KamHyp, initialization/composition, analytic/reality/period/mapping/displacement/tube bounds, quadratic decay and radius comparisons | Derived conditional bundle, constructed inside node proofs |

LT expands at Transport:44–53 to analyticity and range/differentiability (L1),
lattice winding (L2), injectivity modulo parameter integers (L3), derivative
injectivity (L4), zero symplectic pullback (L5), and the original Hamiltonian flow
(L6). These are source assumptions on K, not transported conclusions on Ψ∘K.

KamHyp expands at Setting:42–67 to: positive block dimensions; τ>a+b; nine scalar
positivities; γ₂≤γ₁; the two width bounds; three normalization comparisons;
initialL≤L; holomorphy of h; reality of h and f; Fourier class and weighted bound
for f; injectivity of freq h; derivative and last-row bounds; a continuous linear
equivalence equal to the Hessian, with inverse and first/last-row bounds; and initial
KAM smallness. No field assumes an iterative solution, a recurrence, a sum, a limit,
or a torus. Source initialization L=initialL is a permitted specialization of
L≥initialL; the established iteration permits larger carried L. Weighted bounds and
coordinate domains retain the existing source coefficient/geometric conversion.

**New definitions: empty inventory.** Neither module adds a def, abbrev, structure
or instance. BODY_MATCH, PUBLIC_CARRIER, WELL_DEFINEDNESS, CHARACTERIZATION and
CHOICE_INDEPENDENCE for new definitions are N/A; definition verdict PASS.
The two private declarations sum_half and sum_pow_le are theorem helpers.
Meaning-bearing dependencies were checked: Phase is the product of Fin function
spaces; fastShift retains 2π in the fast block; angleScale scales positions only;
chartPullback is c⁻¹ H∘Ψ; kamConstant is max(8192n,24^(τ+1)/3); eHat and seq use
actual scale formulas. No invented fallback object or junk carrier is introduced.

## Fresh verification

All audit Lean/Lake invocations were serialized and used LEAN_NUM_THREADS=1.
Lean and kernel commands use nice -n 5; the build wrapper invokes the prescribed
nice -n 5 targeted build. No clean, package update or cache mutation was requested.

1. `git diff inp...HEAD` inspected in full (four additions as above).
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
   `git diff --check inp...HEAD`: empty, exit 0.

2. Targeted build command:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp13 KAM.Planetary.Hamiltonian.Part1Nodes KAM.Planetary.TwoScale.SumsNodes
```

Exit 0. Gate receipt and final output:

```text
[inp-gate] slot 1 acquired 01:52:10 for KAM.Planetary.Hamiltonian.Part1Nodes KAM.Planetary.TwoScale.SumsNodes
Build completed successfully (9237 jobs).
```

Cached dependency warnings were replayed (unused variables/simp arguments and
deprecations); no warning in either audited new module. The job count includes
cached dependencies; this was not a requested clean library rebuild.

3. Generated `.lake/abi-scratch/GAPP13Audit2.lean`, importing the two modules,
with `#check @<name>` and `#print axioms <name>` for all 19 ledger declarations.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP13Audit2.lean
```

Exit 0; all expanded types agree with the reviewed source-facing or conditional
interfaces above. Exact axiom output:

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
'KAM.Planetary.sums_doubling_of_quad' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sums_weighted_of_quad' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.seq_sum_doubling' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.seq_sum_weighted' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sum_doubling' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sum_weighted' depends on axioms: [propext, Classical.choice, Quot.sound]
```

4. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Hamiltonian.Part1Nodes KAM.Planetary.TwoScale.SumsNodes
```

Exit 0. Complete output:

```text
replaying KAM.Planetary.TwoScale.SumsNodes
replaying KAM.Planetary.Hamiltonian.Part1Nodes
```

5. Recursive project-import traversal: 191 project modules; no provider modules,
no frozen theorem modules. All 54 manifest-owned anchors in the closure are SEALED
definitions. Thus there is no DRAFT_SORRY or quarantined-provider dependency.

6. Source hygiene: 245/156 lines, maximum Unicode widths 97/98. Required copyright,
module command, public imports, module docstrings and public sections present.
No forbidden proof token, resource override, EuclideanSpace or new instance.
Repository declaration search found no duplicate public short name for these 19
exports; all live in KAM.Planetary or its PsiSteps namespace, with no root shadow.

7. Repository lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1 solely for the explicitly allowed generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1196 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Module checks, frozen-anchor guard and all 144 ABI hashes pass. No other lint finding.

## Notes, errata and limitations

The handoff still describes the pre-repair abstract sum names and says 17 theorems;
the audited HEAD has 19, with source-facing sum_doubling/sum_weighted and distinct
sums_*_of_quad helpers. This stale handoff metadata does not invalidate the repair.
The generated-root exception is explicitly allowed by the brief and handoff; root
regeneration remains the orchestrator's merge task.

No new suspected pinned-source or frozen-statement defect found. P1:138 suppresses
the evaluation at S_c z in its component shorthand; the Lean formulas write it
explicitly, consistent with the chain rule. No source correction is required here.
The GAP design's abstract-sequence wording is satisfied by separate conditional
helpers while the node exports now satisfy the stricter graph premise boundary.
No mathematical deviation was introduced by this audit.

This certifies the specified unsigned graph-gap slice, not the unchanged upstream
proofs in their entirety, a frozen theorem seal, or Track I/N/P headline closure.
Only this report persists from the audit; temporary probe and logs are removed.
