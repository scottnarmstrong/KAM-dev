# S7 independent package audit 1

**Overall verdict: FAIL (slice completeness).** The five signed public declarations have the
prescribed types and definition bodies. The existing proofs have no identified mathematical
error, extra premise, carrier change or forbidden proof escape. However, two assigned graph
contracts are not completely established in Field: `sb-pr-1` regularity and the continuity /
fast-angle independence clauses of `sb-flow#omega`. Exact signature conformity does not
establish those additional, explicitly assigned graph obligations.

No frozen anchor or provider is assigned to S7. Provider/frozen-type and seal-body checks are
inapplicable; neither `secularBoxSafety` nor `secularBoxAtCitedMasses` is certified seal-ready.
The frozen anchors remain outside this infrastructure audit.

Scope: only `KAM/Planetary/SecularBox/Field.lean`, HEAD
`0d90d6d77c773bf2be4f5e431a56d5e542563e3f`, compared with `inp`
`0f347d6926a79e37d59d1e5fd044af61862721ae`, 2026-10-28.
The full `git diff inp...HEAD` adds Field (244 lines) and the inherited S6 Rotation (188 lines).
Rotation was read as a dependency, with no separate S6 verdict. The handoff's “No other file
touched” describes S7's own contribution rather than the complete three-dot diff.
The user's exact worktree report path overrides the generic brief's main-worktree destination.
The pre-existing untracked S7 handoff was left untouched.

Read AGENTS, PLAN, DECISIONS, the package brief and handoff, P14 design row S7, node table,
both P14 design audits, authoritative signatures, track P statement, blueprint p14b lines
224–243 and downstream flow/uniqueness consumers, and the corresponding graph packet
`docs/graph/P/packets/P-p14b.nodes.md` lines 1517–1728. Inspected the consumed ordinary modules,
frozen Hamiltonian vector field, solution predicate, exact secular Hamiltonian, coordinate
assembly/projections and both secular-box frozen theorem statements.

Source SHA-256: `2f7689bfecc9c249325c1346955bfd5f2d98456d0ab8f6e1a87f29ce584fee66`.
Signature file `/root/code/KAM-inp/.drafts/design/P14Signatures.lean` SHA-256:
`24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88`.

## Findings requiring return

**F1 — assigned regularity step absent.** Design lines 240–242 assign `sb-pr-1` to Field.
The graph packet line 1560 requires “H is C^2 on S and X_H is C^1 on S”; blueprint line 232
specifies `ham-smooth` at n=4, k=1. Field lines 44–48 instead prove only
`DifferentiableAt` for H, and lines 50–60 prove only the signed predicate equivalence.
No local proof or export in this file establishes the C¹ vector field. Importing the generic
supplier `KAM.ODE.ham_smooth_c1` is not its specialization to this H and S.
The design audits explicitly say “C2/C1 supplied by Smooth and ODE/Hamiltonian”; those are
available suppliers, not an existing Field proof of the assigned step.

Preserve the exact signed `sb_pred`. Add a distinct regularity helper proving the literal
conjunction under only saturn, mu and hs, by lowering `sb_smooth_prop`'s C∞ conclusion to C²
and applying `ham_smooth_c1` with `(sb_s saturn hs).1`. No added hypothesis is needed.
A private proof suffices for an internal graph step under the handoff's contract; a public
helper would also give downstream ODE consumers a direct interface.

**F2 — omega graph contract only defined, not established in full.** Design line 246 assigns
`bpP:p14:sb-flow#omega` to Field. Blueprint line 224 says “omega is continuous on S and depends
only on (xi,Lambda,eta)”; the graph packet line 1716 repeats both assertions in SOURCE_CONCLUSION.
Field lines 39–40 define the correct partial gradient, but there is no continuity theorem or
local proof, and no proof that replacing lambda preserves this gradient. The global lambda
independence of H imported from Smooth is not itself an equality of its partial derivatives.
The downstream edge `stepP:p14:sb-gl-1` explicitly consumes both frequency properties
(graph packet line 1979).

Preserve the exact signed definition and add distinct helpers for `ContinuousOn (sb_omega
(jupiterSaturnWeights saturn) mu) (sb_sdef saturn)` and its fast-angle replacement identity
on S. Derive them from smoothness on open S and H's global lambda independence. Neither
claim is refuted mathematically; the failure is missing required proof work. Do not mark the
whole graph node complete from a definition or from the availability of generic calculus.

## Declaration and node ledger

Names below are in `KAM.Planetary`; line numbers refer to Field unless specified.

| Node / declaration | Location | Verdict | Reason |
|---|---|---|---|
| `sb_omega` signed definition | 39–40 | PASS | Exact type and body, correct fast-action derivative direction. |
| `bpP:p14:sb-flow#omega` full contract | 39–40 | FAIL | F2: continuity and lambda independence of the gradient are absent. |
| `reducedSecularH` | 41–42 | PASS | Exact type/body; slow Phase is (xi,eta), assembled as I,0,eta,xi. |
| `sb_pred` signed export | 50–60 | PASS | Exact signed statement, both predicate implications, arbitrary J and z, only prescribed membership premise. |
| `bpP:p14:sb-pred` full node | 44–60 | FAIL | Predicate clause proved; F1 leaves C²/C¹ regularity incomplete. |
| `stepP:p14:sb-pr-1` | 44–48 | FAIL | Differentiability alone does not discharge regularity. |
| `stepP:p14:sb-pr-2` | 56–60 | PASS | Unfolded derivative clauses coincide; openness and smoothness supply actual differentiability at z(t). |
| `sb_field` signed export | 126–159 | PASS | Exact statement; zero fast-action velocity and AMD cancellation, no added premises. |
| `bpP:p14:sb-field` | 126–159, 228–240 | PASS | Combined signed exports give the block field and reduced slow derivatives. |
| `stepP:p14:sb-fd-1` | 141–149, 193–240 | PASS | Constant lambda line gives zero derivative; affine chain rule establishes reduced field. |
| `stepP:p14:sb-fd-2` | 78–110, 150–159 | PASS | Rotation tangent is (-eta,xi), chain rule and coordinate expansion give the literal cancellation. |
| `secular_field_components` | 228–240 | PASS | Exact signed statement, including fast frequency and both reduced Hamiltonian components; correctly assigned to S7 by design 456–457. |

Every public theorem and both definition headers were compared against the actual signature
file after whitespace normalization. Both definition bodies match as well. A Lean probe
copies the three signed theorem types and applies each production export with all binders;
two rfl examples check the definition bodies on their entire carriers. There are no unsigned
public exports with narrowed graph-node statements.

## Definition classification and proof review

* `sb_omega`: literal frozen-Hamiltonian fderiv on the fast-action coordinate direction,
  for every m, mu and w. It inherits Lean's total fderiv convention away from differentiability;
  no theorem exploits that convention, since actual differentiability is proved on S.
* `reducedSecularH`: literal affine pullback of the full frozen integral at lambda=0, for
  every I and y. No truncation, changed normalizer, replacement mean or fallback is introduced.
* Private `sbFieldEmb` (183–191): genuine continuous linear inclusion of both slow blocks
  with zero fast blocks, on all Phase b and all natural a,b, including empty blocks.
  Linearity is proved componentwise; finite dimension supplies continuity. No new abbrev or
  structure is introduced.

The predicate proof correctly avoids `ham_reduction`, whose `univ × U ⊆ W` requirement is
unsuited to S with its slow-position restriction. This does not excuse the independent
regularity obligation. Field differentiation along lambda lines uses the actual all-point
lambda invariance, not a locally unjustified path. Rotation uses `sb_rot` at every theta;
its derivative at zero has exactly the sign and slot order needed for AMD cancellation.
The reduced-field proof rewrites the lambda-zero pullback as H(w+L(y-y0)) using global lambda
invariance, then differentiates this affine map at y0; it does not assume differentiability
at an unrelated point or assume the desired field identity. Hypotheses are precisely source
parameter data and S membership, without conclusion-shaped fields or bundled assumptions.

The KAM-only transitive import closure has 64 modules, no provider modules and no frozen
theorem modules. Hence no DRAFT_SORRY theorem or sealed-theorem dependency is involved.
All 18 new declaration short names, including the private helpers, are unique among
module-level declarations in KAM; all public declarations are inside KAM.Planetary. No harmful
root shadow or public generic helper name was found.

## Executed validation

All Lean/Lake invocations were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No resource override was used. Results below are independent reruns, not handoff receipts.

```text
$ env LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-s7 KAM.Planetary.SecularBox.Field
[inp-gate] slot 1 acquired 20:06:26 for KAM.Planetary.SecularBox.Field
Build completed successfully (9110 jobs).
exit 0

$ env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S7Audit1.lean
'KAM.Planetary.sb_pred' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sb_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.secular_field_components' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0

$ env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularBox.Field
replaying KAM.Planetary.SecularBox.Field
exit 0
```

The single replay invocation checks the package's sole audited module, including its private
lemmas. No S7 provider module exists to add. The signature probe uses literal signed types
with production exports as bodies; it introduces no admitted declarations.

```text
$ env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (910 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole lint failure is the explicitly permitted stale generated root. Module format,
frozen-anchor integrity and all 144 frozen ABI hashes pass. The root was not regenerated.
This hygiene note does not account for, or reduce, the separate F1/F2 completeness failures.

Additional static checks:

```text
$ git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output; exit 0)
$ git diff --check
(no output; exit 0)
```

Field has 244 lines, maximum Unicode line width 98, module/copyright/import/docstring/public
section structure, and exposed definition bodies through its exposed noncomputable section.
The targeted forbidden-token scan found no sorry, admit, axiom, unsafe, opaque, EuclideanSpace
or resource overrides. The five public names and thirteen private names have no competing
module-level declaration short names in KAM. No forbidden imports were found in the 64-module
KAM closure. The generated root and all protected source paths were left untouched.

## Source defects, deviations and limits

No suspected defect in a pinned mathematical source or frozen statement was found.
The reviewed blueprint and graph contracts are mathematically consistent here. F1 and F2
are implementation completeness gaps against those contracts, not source errata and not
changes to the approved signed statements. The P14 design audits are design evidence and
do not prove these missing specializations. The handoff's claim that both sb-pr steps are
covered must be corrected or supported by the missing regularity proof.

Only this report was added to repository source paths; no proof, frozen, manifest, generated
root, README or git state was changed. The auditor-owned signature/axiom probe was removed after its successful validation.
The report makes no independent S6 verdict, no full secular-box theorem claim, and no
assertion that compile success closes the missing graph work.
