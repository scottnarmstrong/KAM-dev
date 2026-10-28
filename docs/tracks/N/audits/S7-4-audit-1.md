# S7-4 independent package audit 1

**Overall verdict: PASS WITH NOTES.** Both S7-4 declarations pass statement fidelity,
proof review, exact-type elaboration, axiom inspection and kernel replay. No mathematical
or package-local hygiene defect was found. Repository-wide lint has an unrelated
100-character violation in `Planetary/Hamiltonian/Liouville.lean`, in addition to the
expected stale generated root. This is not an unconditional repository-lint PASS.

## Scope and frozen inputs

Focused tier-2, refute-first review on 2026-10-28. Authority: the user prompt,
`AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the local
`docs/tracks/N/audits/S7-4-handoff.md` AUDIT FOCUS. The explicit user destination
overrides the brief's generic main-worktree destination. Only this report is retained;
no implementation, frozen file, manifest, generated file, or git state was changed.

Snapshot v1:

| Input | Revision / SHA-256 |
|---|---|
| Audited HEAD | `4a056fc93f6b8b46e55003393c93e28898d22205` |
| `inp` at intake | `9e16b5ed096b8caeb5cf1cf2ed370a8a94ec05e4` |
| Merge base | `741f26a1d15d160fa8e00f43c0445e117a327b47` |
| `KAM/Nekhoroshev/Stability/Preimage.lean` | `4037d8507b9dd85dbf230f2600c3799512daa494e79c6cf965bb8123517c4a14` |
| Design v2, `docs/tracks/N/design/PART67-LEAN-DESIGN.md` | `9376271a6f311a2fa9bdf530680433ae2b759a84747a05aa1aa8ad07d2e53be2` |
| Supplied `/root/code/KAM-inp/.drafts/design/NPart67Signatures.lean` | `c588818b1772d3f7e106aac256b8207623c8a142cf40ef0e778f0507b1945c9f` |
| `blueprint-N/parts/p7-stability.tex` | `f3d6e993abd74759469db1c9ae3c2c6d7cc65555a6d13167e8bfc7c38493e4bd` |
| Existing `Stability/Setting.lean` | `94190572990d617ad434dceba428460a2a81b8a1bbe16ada4e49a941bc3011fa` |
| Existing `Canonical/Setting.lean` | `49a4a9eb675de5a375ff138568f5bce11617db7dfaaeb55657cfc1fca68ebd10` |
| Existing `Weighted/Parametric.lean` | `0d1a446297a8b38c3276974a023ef21415c879ccc5ea8ada81547c4a14d6f796` |

`git diff inp...HEAD` contains exactly one new file, `Preimage.lean`, 275 insertions.
The handoff's approximate 255-line estimate is stale; the actual 275 lines are below
the cap. The two prior design audits were read at their actual paths under
`docs/tracks/N/design/DESIGN-N67-design-audit-{1,2}.md` (not `audits/` as suggested
by the handoff). Their preimage rows agree with the current source; they were not
used as substitutes for reviewing the proofs.

There is no provider or frozen theorem seal in this package. Provider/frozen
type-equality and seal-body checks are therefore inapplicable. No frozen headline,
track root, Part 11 variant, or downstream consumer implementation is certified here.
The Track N statement was read for scope; these are infrastructure results for its
complex normal-form route. No external PDF assertion is needed to establish these
two blueprint results, whose preimage lemma is explicitly labelled “Ours.”

## Declaration verdicts

| Node / role | Lean declaration | Verdict | Reason |
|---|---|---|---|
| `bpN:p7:preimage` | `KAM.Stability.preimage` | PASS | Exact v2 type; full real preimage and both component displacement bounds; complete contraction proof. |
| `bpN:p7:preimage-nfl` | `KAM.Stability.preimage_nfl` | PASS | Exact v2 witness-level type; retains action displacement and its `r / 2^7` bound. |
| Private gauge | `realScale` | PASS | Literal real invertible diagonal scaling, angles by `σ⁻¹`, actions by `ϱ⁻¹`. |
| Private compatibility | `scaleCLE_realInclusion₂` | PASS | Complex gauge commutes with the real inclusion. |
| Private inverse formula | `scaleCLE_symm_apply` | PASS | Inverse gauge multiplies the two coordinates by `σ`, `ϱ`. |
| Private domain geometry | `symm_mem_Dom` | PASS | Radius-`1/2` complex ball fits the domain at every radius-`1/4` real center. |
| Private norm bound | `norm_realPartCLM₂_le` | PASS | Product real-part projection has norm at most one. |

The public theorem headers, including binder order and implicitness, agree with
both supplied signatures and design Appendix A after whitespace removal. Independent
probes used those signature headers verbatim and supplied every explicit premise
to the implementation in order. Both elaborate without warnings.

### Premise classification

All listed logical premises are SOURCE, or the explicitly designed normal-form
witness interface. There are no EXCESS or conclusion-shaped premises. Parameters
and carriers are TYPING/source data; there are no instances or hidden assumption
structures in either signature.

| Declaration | Binder(s) | Classification and exact authority |
|---|---|---|
| `preimage` | `{n}` | TYPING: finite coordinate dimension; no extra dimension restriction. |
| `preimage` | `{D}` | SOURCE: arbitrary real action base, p7 L74. |
| `preimage` | `{r'}`, `{s'}`, `{dθ}`, `{dI}`, `{ϱ'}`, `{σ'}` | SOURCE: domain radii, displacement bounds, and gauge radii, p7 L74. |
| `preimage` | `{Ψ}` | TYPING: total ambient representative of the map on its source domain. |
| `preimage` | `hΨ` | SOURCE: holomorphy on the open domain, p7 L74. |
| `preimage` | `hΨreal` | SOURCE: real at all real domain points, p7 L74. |
| `preimage` | `hθ` | SOURCE: angle displacement bound, p7 L74. |
| `preimage` | `hI` | SOURCE: action displacement bound, p7 L74. |
| `preimage` | `hϱ'` | SOURCE: positive action gauge radius, p7 L74. |
| `preimage` | `hϱr` | SOURCE: action gauge radius at most domain radius, p7 L74. |
| `preimage` | `hσ'` | SOURCE: positive angle gauge radius, p7 L74. |
| `preimage` | `hσs` | SOURCE: angle gauge radius at most twice strip width, p7 L74. |
| `preimage` | `hκ` | SOURCE: maximum scaled displacement at most `1/4`, p7 L74. |
| `preimage` | `y`, `y.2 ∈ D` | SOURCE: universal target and its action-base membership, p7 L74. |
| `preimage_nfl` | `{n}` | TYPING: same coordinate dimension. |
| `preimage_nfl` | `{D}` | SOURCE: real action base, p7 L86. |
| `preimage_nfl` | `{r}`, `{s}`, `{K}`, `{α}`, `{p}`, `{ε}` | SOURCE: normal-form parameters, design L1042–1057; p7 L86–89. |
| `preimage_nfl` | `{Ψ}` | TYPING: the supplied normal-form map witness. |
| `preimage_nfl` | `hp` | STANDING: `p > 1` in normal-form data; `conjExp p = p/(p-1)`. |
| `preimage_nfl` | `hα` | STANDING: positive divisor bound. |
| `preimage_nfl` | `hK` | STANDING: positive cutoff. |
| `preimage_nfl` | `hr` | STANDING: positive action radius. |
| `preimage_nfl` | `hs` | STANDING: positive angle width. |
| `preimage_nfl` | `hε0` | STANDING: nonnegative perturbation bound. |
| `preimage_nfl` | `hi` | SOURCE: normal-form smallness (i), used explicitly in p7 L89. |
| `preimage_nfl` | `hii` | SOURCE: `κ = 2πKs ≥ 6`, p7 L86. |
| `preimage_nfl` | `hΨ` | SOURCE: holomorphy of the map witness, design witness interface and p7 L89. |
| `preimage_nfl` | `hΨreal` | SOURCE: reality of the same map witness, p7 L89. |
| `preimage_nfl` | `hdisp` | SOURCE: both displacement bounds of that witness, p7 L89. |
| `preimage_nfl` | `y`, `y.2 ∈ D` | SOURCE: universal real target over the base, p7 L86. |

Counting logical hypotheses, including target membership: `preimage` has
SOURCE=10, STANDING=0, RULED=0, EXCESS=0; `preimage_nfl` has SOURCE=6,
STANDING=6, RULED=0, EXCESS=0. Typing/data binders are displayed separately above.
The witness-level corollary is stronger in applicability than requiring a complete
normal-form construction: it needs only the properties used by this argument.
This is the explicit v2 design choice (§4 item 8), not an assumed preimage result.

## Proof and adversarial review

`preimage`, L114–227: positivity of `s'` follows from `0 < σ' ≤ 2s'`;
positivity of `r'` follows from `0 < ϱ' ≤ r'`. Once a target is supplied it lies
in the domain, so both displacement bounds are nonnegative (L116–119).
No nonemptiness or positivity premise is smuggled in.

The new private real gauge and existing complex gauge agree on real vectors.
After conjugating by the gauge, `G = W ∘ (Ψ-id) ∘ W⁻¹` has ordinary product
sup norm at most `κ`. For any real center within `1/4` of `Wy`, L54–94 proves
the complex radius-`1/2` ball is inside the transformed domain. The angle estimate
uses only imaginary displacement, strictly less than `σ'/2 ≤ s'`; action distance
from the specific base point is strictly less than `ϱ'(1/2+1/4) < r'`.
No convexity, closure, connectedness or boundedness of `D` is used.

The open-ball Cauchy estimate at L158–161 gives `‖DG‖ ≤ 2κ`. Real restriction,
isometric inclusion and the contractive real-part projection give the same real
derivative bound. The mean value inequality applies on the convex closed ball
`X = closedBall (Wy) κ`, where `2κ ≤ 1/2`. The map `T u = Wy - ψ u` preserves
`X`. Completeness and its nonempty center are supplied to Banach's theorem.
Reality is used at the resulting fixed point to recover the full complex identity
`Ψ(ιx)=ιy`, rather than just its real part. The final two bounds come directly
from the original hypotheses evaluated at this domain point.

`preimage_nfl`, L245–271: `q=p/(p-1)>0`. Smallness yields
`qKε/α ≤ r/128`, hence its ratio to `ϱ'=r/2` is at most `1/64`.
The angle ratio for `σ'=s/3` is at most
`30/(128·2πKs) ≤ 30/768 = 5/128 < 1/4`.
The product inequalities in L260–263 establish this without dividing by an
unproved positive expression. Domain widths, hypothesis ordering and both
displacement projections in the application at L265–270 are correct.

A separate refutation pass tested the likely failure modes: `D=∅` makes the
target quantification vacuous; `κ=0` gives a nonempty singleton closed ball and
still permits the `1/2` contraction constant; `ε=0` is allowed without a
singular time expression; equality in either gauge-radius condition still leaves
strict domain inclusion because the Cauchy ball is open; `n=0` introduces no
false dimension premise. Complex action distance is to a witnessed real base
point, not merely to a real projection. None produces a surviving finding.

## Definition classification and dependency hygiene

The sole new definition is private `realScale` (L36–39), a literal continuous
linear equivalence. Positive radii make both inverse scalars units. It is the
intended diagonal gauge on its entire declared carrier; there is no choice,
default branch, off-domain fallback or global norm instance.

```text
BODY_MATCH: OK
PUBLIC_CARRIER: OK (private auxiliary on the full real product space)
WELL_DEFINEDNESS: N/A_LITERAL
CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A
DEFINITION_VERDICT: PASS
```

Existing semantic definitions were expanded: `cpx D` is the image under real
inclusion; `realStrip D r` is `univ × realNbhd D r`; `Dom` is the complex angle
strip times the complex action tube; `conjExp p` is `p/(p-1)`. All norms here
are the prescribed Pi/product maximum norms. Real inclusion and real-part maps
are the existing coordinate maps. No alternative dynamics or solution predicate
occurs in either new theorem.

The five direct imports are the two Mathlib modules and the existing
`Canonical.Setting`, `Stability.Setting`, `Weighted.Parametric`. A recursive
project-import scan found 40 modules, no providers, and exactly ten frozen
imports, all manifest kind `definition`, state `SEALED`: `ActionNbhd`,
`ComplexStrip`, `FrequencyMap`, `HamiltonianVectorField`,
`HamiltonianVectorFieldC`, `IsPrimaryOnStrip`, `IsRealOnReals`, `OmegaZero`,
`RealHamiltonian`, and Nekhoroshev `RealPart`. There is no imported frozen
theorem or `DRAFT_SORRY` anchor.

## Verification receipts

Targeted build:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-s74 KAM.Nekhoroshev.Stability.Preimage
[inp-gate] slot 2 acquired 06:51:24 for KAM.Nekhoroshev.Stability.Preimage
Build completed successfully (3174 jobs).
exit 0; no warnings
```

The wrapper runs `nice -n 5 lake build`. It did not clean or rebuild the library
from scratch. No Mathlib/cache operation was requested.

Exact signature-application probe (removed after checking):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S74Audit1.lean
'KAM.Stability.preimage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.preimage_nfl' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0; no warnings/errors
```

The probe imports only `KAM.Nekhoroshev.Stability.Preimage`, opens the signature
namespaces, and repeats the two supplied theorem types as `example`s, with bodies:

```lean
by exact KAM.Stability.preimage hΨ hΨreal hθ hI hϱ' hϱr hσ' hσs hκ
by exact KAM.Stability.preimage_nfl hp hα hK hr hs hε0 hi hii hΨ hΨreal hdisp
```

Kernel replay, one invocation, after the probe exited:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Nekhoroshev.Stability.Preimage
replaying KAM.Nekhoroshev.Stability.Preimage
exit 0
```

Final serialized lint run, after kernel replay exited:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
Lean lines over 100 characters:
/root/code/KAM-inp-s74/KAM/Planetary/Hamiltonian/Liouville.lean:35:108
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (429 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The unexpected lint failure is the quoted pre-existing line, not a S7-4 line.
Its location is absent from the package diff. No relaxation of the 100-character
check was used. The generated-root line is the brief's expected exception.

Mechanical checks: `git diff --check inp...HEAD` exits 0 with no output;
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.
The changed file has 275 total lines, zero lines over 100 Unicode characters,
the required copyright/module/public imports/module documentation/public section,
and no forbidden proof escapes, resource overrides or `EuclideanSpace`.

Resource-process deviation: an initial lint invocation was started without
explicit `LEAN_NUM_THREADS=1` or `nice`, before the targeted build's completion
was collected. Its ABI subprocess runs Lean, so that invocation was not a valid
receipt for the requested resource discipline. It finished before the exact-type
probe started. The final lint rerun uses the requested environment and priority;
the final probe, kernel replay and lint rerun are serialized. No unrelated process
was stopped. This records an auditor execution deviation, not a code defect.

## Findings, errata and closeout

No surviving mathematical, statement, definition or package-local hygiene finding.
No new suspected pinned-source erratum or blueprint defect was found. The existing
blueprint note at p7 L270 about Pöschel's unargued surjectivity is the explicitly
stated motivation for this proved lemma; it is not a newly discovered source issue.

The whole-repository lint exception is outside the user-assigned S7-4 module scope
and is not silently waived or repaired. The expected generated-root discrepancy
belongs to orchestrator integration. Both theorem rows are PASS; the package is
PASS WITH NOTES solely because the complete repository lint command is not clean.
No frozen anchor is sealed by this audit.

Final snapshot check: HEAD and the audited source hash are unchanged. The shared
`inp` ref advanced during the audit to `4f65a1f8055d14808ab27ed9bff2e18d69eac46c`;
the comparison recorded here is the intake snapshot, with a final three-dot diff
still containing only the same 275-line S7-4 file. The auditor-created exact-type
probe was deleted. `git diff --check -- docs/tracks/N/audits/S7-4-audit-1.md`
and an explicit whitespace/fence check of this new report passed. Final status
contains only this new report and the pre-existing untracked S7-4 handoff.
