# Independent package audit N89-G7

Date: 2026-10-28. Auditor: maud-n89g7-1. Worktree: `/root/code/KAM-inp-n89g7`.

## Verdict and scope

**PASS WITH NOTES for `bpN:p8:covering` and `bpN:p8:cutoffs`.** The implementation proves the exact design signatures with no added premises. The five definitions match literally; no mathematical blocker was found. Notes concern inherited branch hygiene and replayed dependency warnings. This is an infrastructure-package verdict, not a frozen-anchor seal or N-HEAD-C closure.

Audited HEAD `448b5d31215f5f22da0c3c2b9f2dd0e51ce9a7df`, against `inp` (`05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`) and `inp-n89g6` (`cf55a91ab16eb5ea7f90bfe02ed361bd237f3422`). Per the handoff focus, implementation review is restricted to `KAM/Nekhoroshev/ResonanceGeometry/Covering*.lean`: exactly one file, `Covering.lean`. `git diff HEAD^ HEAD --name-only` confirms this package commit changes only that file. No provider export or frozen theorem belongs to G7; provider/frozen equality and frozen seal-body probes are therefore **N/A**, rather than asserted passed. Fresh design-type assembly probes replace them for the actual two internal exports.

Read AGENTS.md, PLAN.md, DECISIONS.md, the package brief, handoff, track-N statement, N89 Revision-2 design and Appendix A, both design audits, source Part 8 and its review, and relevant imported definitions/proof interfaces. The signatures and design audits missing from this package worktree were read at `/root/code/KAM-inp/.drafts/design/N89Signatures.lean` and `/root/code/KAM-inp/docs/tracks/N/design/DESIGN-N89-design-audit-{1,2}.md`. The user's exact worktree report path overrides the generic brief's main-worktree output instruction.

Pins:

- Covering.lean SHA-256: `f76473e162da66c3853514a350481ed31ffdec1bf007b8b87e14802b5b9d73fe`.
- N89Signatures.lean SHA-256: `01270a67c964001a1f6f86a2416ce572fee94f326c34cec43fcef7de0fea4b88` (matches Revision-2 audit).
- Part 8 SHA-256: `8c7b5239312aaa1bb68e282b36accc8731812c60e07b983c205059399ce23094` (matches design).

## Findings and branch boundaries

**N89G7-A1 — inherited protected-path difference.** The required `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**: KAM.lean has 31 added import lines. Frozen files, manifest and README have no differences. Git reports two merge bases and chooses `969207c41db6f27f287ccd61f98e6d66fc4c00ea`; the other is `5991245cabc06e69ec900cb6006b45f72cc85eb0`. Thus the three-dot diff is not a single-package delta. The same inherited root change appears against inp-n89g6. The actual G7 commit touches no protected path. This literal branch-wide hygiene condition is unmet; it is not silently treated as an empty diff or attributed to G7. No out-of-scope package is certified by this report.

**N89G7-A2 — expected stale generated root.** Lint has the expressly allowed stale-root exception; the auditor does not regenerate KAM.lean. `latticeDim_top` has exactly one declaration in the checked production tree, at Covering.lean:81, with one local use; no current collision.

## Declaration-by-declaration fidelity

Names below are in namespace `KAM.Nekhoroshev`. All 20 new public declarations are covered. Sources are `blueprint-N/parts/p8-resonance-geometry.tex`.

| Node / source step | Declaration (Covering.lean line) | Verdict | Reason |
|---|---|---|---|
| covering data, p8:184–187 | `CoverParams.lam` (29) | PASS | Literal design formula; positive-rank source values agree. |
| covering data, p8:186 | `CoverParams.radius` (32) | PASS | Literal radius with Euclidean lattice covolume. |
| covering data, p8:186 | `CoverParams.alpha` (35) | PASS | Exactly p M K r. |
| covering data, p8:186 | `CoverParams.delta` (37) | PASS | Exactly b m r. |
| covering data, p8:187 | `actionBlock` (39) | PASS | Exact inverse-image block restricted to P; arbitrary carrier/map. |
| cv-params, p8:197 | `CoverParams.Valid.hE` (45) | PASS | Positivity of E derived, not assumed. |
| cv-params / cv-radii, p8:197,200 | `CoverParams.Valid.hA1` (48) | PASS | Stronger A>1 follows from E>0 and sqrt(2)>1. |
| cv-params / cv-radii | `CoverParams.Valid.hq1` (53) | PASS | AK≥1 from A>1, K≥1. |
| cv-params | `CoverParams.Valid.hqpos` (56) | PASS | AK>0 derived. |
| cv-params | `CoverParams.Valid.lam_pos` (58) | PASS | Stronger: every natural d, including auxiliary d=0. |
| cv-params | `CoverParams.delta_eq` (64) | PASS | Stronger algebraic identity for arbitrary raw c,Λ, including rank zero. |
| cv-params | `CoverParams.Valid.alpha_eq` (69) | PASS | E K delta identity with nonzero b,m supplied by Valid. |
| cv-radii | `CoverParams.Valid.radius_nonneg` (75) | PASS | Stronger: all lattices, not only maximal ones. |
| cv-radii / maximal(d) | `latticeDim_top` (81) | PASS | Full integer lattice has real rank n, also n=0. |
| cv-radii | `CoverParams.radius_bot` (84) | PASS | Literal rank-zero endpoint, no Valid premise. |
| cv-radii | `CoverParams.radius_top` (88) | PASS | Full-rank endpoint, uses AK>0. |
| cv-radii | `CoverParams.Valid.radius_bounds` (94) | PASS | Both global bounds and stronger non-top upper bound retained. |
| cv-nonres, p8:199 | `CoverParams.Valid.alpha_bot_le` (132) | PASS | alphaΘ≤lambda1 derived from E≤A. |
| bpN:p8:covering, cv-params/cover/nonres/radii | `covering` (145) | PASS | Exact signature bytes; finite coverage and every bound retained. |
| bpN:p8:cutoffs, co-incl | `cutoffs` (197) | PASS | Exact signature bytes; both norm inclusions, nonresonance, distance and radius comparison. |

## Binder audit

The main signatures are byte-identical to N89Signatures.lean:297–324 and design Appendix A. No existential constants or witnesses have moved outside their permitted scope. `c` is fixed first; all lattices, points and modes remain universally quantified in the conclusions. There are no instance binders or hidden proof-valued typeclasses in the new API.

Expanded `hc : c.Valid` (Interfaces/CoverParams.lean:37–46), once per occurrence:

| Expanded input | Bin | Source |
|---|---|---|
| hn: 1≤n | SOURCE | p8:185 |
| hp: 0<p | SOURCE | p8:185 |
| hb: 0<b | SOURCE | p8:185 |
| hr0: 0<r0 | SOURCE | p8:185 |
| hM: 0<M | SOURCE | p8:185 |
| hm: 0<m | SOURCE | p8:185 |
| hK: 1≤K | SOURCE | p8:185 |
| hA: pM/(bm)+sqrt(2)≤A | SOURCE | p8:185 |

Remaining outer binders, in order:

| Declaration | Binder | Bin | Source / purpose |
|---|---|---|---|
| covering | implicit n:ℕ | TYPING | coordinate dimension |
| covering | implicit ι:Type* | TYPING | arbitrary action carrier, p8:185 |
| covering | c:CoverParams n | TYPING | seven raw real parameter values |
| covering | hc:c.Valid | expanded above | eight source assumptions |
| covering | P:Set ι | TYPING | arbitrary source set |
| covering | freqR:ι→(Fin n→ℝ) | TYPING | arbitrary source map; values outside P never constrain the result |
| cutoffs | implicit n:ℕ | TYPING | coordinate dimension |
| cutoffs | c:CoverParams n | TYPING | same raw data |
| cutoffs | hc:c.Valid | expanded above | eight source assumptions |
| cutoffs | implicit Ka:ℝ | TYPING | analytic cutoff |
| cutoffs | hKa:0≤Ka | SOURCE | p8:204 |

Counts after expansion: covering SOURCE=8, TYPING=5, STANDING=0, RULED=0, EXCESS=0; cutoffs SOURCE=9, TYPING=3, STANDING=0, RULED=0, EXCESS=0. Implications `Ka≤K`, `0<sqrt(n)Ka`, `sqrt(n)Ka≤K` remain within the conclusion exactly as in the source corollary, not additional outer assumptions.

For all helpers, implicit `n`, raw `c`, lattice `Λ`, and natural `d` are TYPING. Every `hc` expands to the same eight SOURCE inputs above. Exact helper input inventory (all unmarked data binders TYPING, each hc expanded above, hΛ classified SOURCE): hE/hA1/hq1/hqpos/alpha_bot_le use `{n,c},hc`; lam_pos adds d; alpha_eq/radius_nonneg add Λ; radius_top uses only `{n,c},hc`; radius_bounds adds implicit Λ and `hΛ:maximalK c.K Λ`; delta_eq uses `{n},c,Λ`; radius_bot uses `{n},c`; latticeDim_top uses `{n}`. `hΛ` is the source domain premise of cv-radii: expanding maximalK gives short-vector generation and maximality among equal-rank K-lattices (Maximal.lean:27–32), not saturation or a radius estimate. No helper assumes its conclusion, a geometric lemma, a volume bound, or a result-shaped bundled field. No EXCESS input was found. Auxiliary algebraic helpers with fewer domain restrictions are explicitly stronger statements.

## Definition audit and proof review

All five new definitions are literal, with BODY_MATCH=OK, PUBLIC_CARRIER=OK, WELL_DEFINEDNESS=N/A_LITERAL, CHARACTERIZATION=N/A_LITERAL, CHOICE_INDEPENDENCE=N/A, DEFINITION_VERDICT=PASS, separately for each row in the declaration table. No new abbrev, structure, instance, choice or fallback branch is introduced.

`lam`, `radius`, `alpha`, `delta` use ordinary total real arithmetic on raw records. Valid supplies positivity whenever denominators are cancelled or inequalities used. Extending the displayed formula to natural d=0 is explicit design arithmetic; it does not redefine the source rank-zero zone. `delta_eq` at rank zero is only an algebraic identity involving that auxiliary number, never an assertion that the zero-rank zone has finite width. `actionBlock` is exactly `{I | I∈P ∧ freqR I∈blocks ... Λ}` on its entire carrier, including empty P.

Semantic interfaces checked: `Lattice` is the integer additive subgroup, real span is `lattice`, rank is real finrank; `maximalK` is K-lattice maximality; `eBall` uses explicit Euclidean length and `zBall` uses the Fourier l1 mode size. `resonanceDistance` is Euclidean length of the canonical projection onto the real lattice span; Projection.lean:125–153 proves it is the attained distance to the orthogonal resonance space. `volume_def` is the existing Gram covolume, with one_le_volume, maximal volume bounds and endpoint values. No function-type norm was substituted for Euclidean length.

Independently followed the proof: positive E and A>1 give AK>0; the lambda ratio is exactly AK; `blocks_cover` yields finite coverage and `geometric` supplies the pointwise divisor/distance bounds. Rank zero is handled through the theta branch rather than a positive-rank zone argument. Radii use 1≤V≤K^d, d≤n, and maximal full rank implies top. The non-top estimate also validly includes bottom because n≥1. For cutoffs, `|k|2≤|k|1≤sqrt(n)|k|2` gives the inclusions; Ka≤K transfers divisors. At bottom the distance is proved zero and auxiliary delta positive. The final division uses nonnegative alpha and strictly positive analytic denominator, supplied by the conditional sqrt(n)Ka>0. Thus the source's strict distance and cutoff directions are retained.

Import closure has 63 project modules, no provider and no frozen theorem imports (hence no DRAFT_SORRY theorem). It includes 19 frozen definition modules only; relevant frequency, real restriction and solution definitions were read. This geometry theorem accepts any freqR and never replaces the frozen frequencyMap with another Hamiltonian object. Frozen integrity and ABI checks below validate the shared definitions. No frozen anchor is promoted.

## Independent verification

All Lean commands were sequential with LEAN_NUM_THREADS=1 and nice -n 5. No clean/update/cache fetch, package edit, resource override or state-changing git operation was used.

1. Targeted gated build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n89g7 KAM.Nekhoroshev.ResonanceGeometry.Covering
```

Exit 0. Gate: `[inp-gate] slot 1 acquired 10:09:44 for KAM.Nekhoroshev.ResonanceGeometry.Covering`. Final output: `Build completed successfully (3218 jobs).` Replayed upstream unused-variable warnings: Gradient.lean:168 (`hgr`), Maximal.lean:249 (`hK`), Blocks.lean:34 (`hK`) and :35 (`hlam`). No Covering diagnostic. This is a targeted overlay build, not a clean rebuild.

2. Fresh exact-type and definition probes:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N89G7Audit.lean
```

Exit 0. Copied the exact design signatures under fresh names, with bodies `by exact covering c hc P freqR` and `by exact cutoffs c hc hKa`, preserving all explicit binders in order; checked `example : type_of% @audit_covering := @covering` and its cutoffs counterpart. Copied each literal design definition under a fresh name and proved equality of the complete functions by rfl. Mechanical comparisons returned `SIGNATURE_BYTES_EQUAL True` twice and `DEFINITION_BYTES_EQUAL True` five times. The first auditor-generated probe omitted the original noncomputable section and reported four noncomputable-definition code-generation errors; adding that missing context fixed the harness. No production code was changed.

Exact axiom output from the successful probe:

```text
'KAM.Nekhoroshev.CoverParams.Valid.hE' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.CoverParams.Valid.hA1' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.CoverParams.Valid.hq1' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.CoverParams.Valid.hqpos' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.CoverParams.Valid.lam_pos' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.CoverParams.delta_eq' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.CoverParams.Valid.alpha_eq' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.CoverParams.Valid.radius_nonneg' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.latticeDim_top' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.CoverParams.radius_bot' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.CoverParams.radius_top' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.CoverParams.Valid.radius_bounds' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.CoverParams.Valid.alpha_bot_le' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.covering' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.cutoffs' depends on axioms: [propext, choice, Quot.sound]
```

Lean's displayed `choice` is the permitted classical choice axiom. No sorryAx or project axiom occurs.

3. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.ResonanceGeometry.Covering
```

Exit 0. Exact output:

```text
replaying KAM.Nekhoroshev.ResonanceGeometry.Covering
```

This single invocation replays the one audited lemma module; G7 has no provider module.

4. Repository lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the expressly permitted stale-root exception. Exact combined output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (526 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No forbidden-source, module, errata-rendering, frozen-integrity or ABI diagnostic occurred. The ABI subprocess ran after the other audit Lean commands had finished and inherited LEAN_NUM_THREADS=1 and niceness 5.

5. Static hygiene: Covering.lean has 250 physical lines (the handoff's 249 is an off-by-one count), below 1500; copyright, module, four public imports, module docstring and exposed public noncomputable section are present. Token scan found no sorry/admit/axiom/unsafe/opaque, set_option or EuclideanSpace. `git diff HEAD^ HEAD --check` exits 0. Protected-path and branch-diff exceptions are recorded above, without editing generated files.

## Source observations and handoff limits

No new suspected mathematical defect was found in the audited statements or proofs. Inherited observations, explicitly reported rather than silently dropped:

- Part 8:220 / Pos93 p.200, “not properly contained in any other lattice of the same dimension”: ambiguity between all subgroups and K-lattices. The adopted design uses the latter, weaker notion; no saturation hypothesis was introduced.
- Part 8:221–223 / Pos93 p.202: “the maximal K-lattice ... generated by ... together” and “the volume ... is not bigger than ...”: maximal extension/dimension and volume comparisons require proofs. G7 consumes the existing proved maximal/geometric interfaces; it does not assume these estimates in Valid.
- Part 8:223 / Pos93 p.204, “rΘ≤rΛ≤rZⁿ=r0”: the source omits the volume-bound argument. G7 explicitly uses 1≤V≤K^d.
- Design P8-3 / historical cutoff direction: “Ka≥sqrt(n)Kg” is wrong for analytic transfer. Current code uses Ka≤Kg for divisors and sqrt(n)Ka≤Kg for the radius requirement.
- Design P8-4 / Part 8:207: closeness for the zero lattice is true because distance is zero and deltaΘ>0; it is not a zone-radius identity. The proof handles this explicitly.

These are inherited blueprint/design attributions, not fresh independent PDF verification. No external web/PDF retrieval was required for the requested design/source-file audit. No numerical erratum is newly asserted. No deviation was introduced by the auditor. Remaining integration limits: root regeneration is owned by the orchestrator; inherited packages and any eventual provider/frozen-root assembly remain outside this G7 audit.

Only this report was authored in tracked-source space; temporary audit probe files are deleted after checks. The pre-existing untracked N89-G7-handoff.md is preserved. No commit was made.

Final validation: `git diff --check` exits 0; the report has no trailing whitespace and no pending check placeholders. The fresh audit probe was deleted. Final status contains only the pre-existing untracked handoff and this new untracked report.
