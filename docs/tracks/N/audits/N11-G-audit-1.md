# N11-G independent package audit 1

Date: 2026-10-28. Overall verdict: **PASS WITH NOTES** for the N11-G infrastructure slice.
No substantive proof, signature, source-correspondence or completeness defect was found.
This package supplies no frozen provider export and seals no anchor. The downstream
`KAM.Nekhoroshev.partialConvex_nekhoroshev` anchor remains `DRAFT_SORRY`; its seal readiness
is outside this audit and is not implied by this verdict.

## Scope and fixed inputs

The user-selected report destination is this worktree, overriding the generic brief's main-worktree
destination. Read AGENTS.md, PLAN, DECISIONS, the external package-audit brief, N11-G handoff,
both N11 design audits, the revised design and signature delivery, the Part-11 block-data lemma
and its block consumer, the track statement, and the relevant frozen theorem and definitions.
Review scope is **only `KAM/Nekhoroshev/Partial/BlockData.lean`**.

| Input | Revision / SHA-256 |
|---|---|
| Audited HEAD | `983942ad318634474e9cfbc27751e31396a67b1b` |
| Comparison ref `inp` | `b0e2f8831ae1de9b2eeb0890b7697d19e55626f1` |
| BlockData.lean | `4ab82d9e1845ede054f6c6c96b88f762e0e69b9640dc298049b8b7cfd4fe6f0c` |
| N11-LEAN-DESIGN.md | `f0fd0d111b6abd5c335a5ea144135a07b28be326f3d699f3c2761c46ad097609` |
| `/root/code/KAM-inp/.drafts/design/N11Signatures.lean` | `23bd2cc2645243b3357acccda6e04ff69fad4d055963010025c582f3c886a0e4` |
| `blueprint-N/parts/p11c-partial-stability.tex` | `5d6fe7fc6b09459b6bf307596832695fcda1b62bf5292bd926d84bf216f7b7ea` |

The shared `inp` ref advanced during verification to
`48e9326d764f4bb7e1704209fddf71863ec4eb9e`. A final comparison of the complete
`git diff <initial-inp>...HEAD` and `git diff <final-inp>...HEAD` outputs found them byte-identical;
the audited HEAD and source hash did not change. This ref movement changes no audit conclusion.

`git diff inp...HEAD` has three new files: BlockData (329 lines), Domain (435), Hessian (360).
The latter two are dependencies, including the handoff-disclosed N11-E3 round-1 dependency;
their public APIs and relevant definitions were inspected for this use, but they receive no
independent package verdict here. No assumption that an append-only companion has landed is needed.
There are no I/P implementation changes in this slice.

## Declaration and node ledger

Names below are in `KAM.Nekhoroshev`. Line references in the third column are to BlockData.lean.
All eleven `bd_*` lemmas are private; `block_data` is the sole new public declaration.

| Node / obligation | Declaration | Verdict | Evidence / reason |
|---|---|---|---|
| `bpN:p11:block-data` | `block_data` | PASS, L173–325 | Full 12-line signature is byte-identical to delivery L693–704, including all binders, the let-expression, strict witness and both smallness bounds. Fresh declaration application and `type_of%` probe check the elaborated type. |
| `stepN:p11:bd-cover` | internal `block_data` | PASS, L187–264 | Actual Part-8 covering on the singleton, valid numerical parameters, maximal lattice witness, positive radius bounds and full-lattice contradiction. |
| `stepN:p11:bd-24` | internal `block_data` | PASS, L266–306 | Actual analytic cutoff at K/sqrt(n); real/complex frequency identification; strict projection-distance witness; dual pairing estimate; complex Hessian gives max-norm Lipschitz constant sqrt(n) M1. |
| `stepN:p11:bd-5` | internal `block_data`, `bd_eps_eq` | PASS, L308–325 | Exact epsilon identity followed by radius monotonicity and the explicit second denominator. |
| Positivity | `bd_coth_pos` | PASS, L42 | Positive sinh denominator for positive argument; no value at zero is used. |
| Source constants | `bd_basic` | PASS, L46 | Positive g,m from frozen source bundle; m <= Mc from the selected-sign Hessian theorem. |
| Positive epsilon | `bd_eps_pos` | PASS, L51 | Positive strip width and mu give positive epsilon. |
| Positive epsilon0 | `bd_eps0_pos` | PASS, L59 | Source positivity guards r0 and A and hence epsilon0. |
| Power identity | `bd_K_pow` | PASS, L72 | Positive ratio and nonzero dimension justify real-power conversion and cancellation. |
| Geometric cutoff range | `bd_one_le_K` | PASS, L90 | epsilon <= epsilon0 and epsilon > 0 give K >= 1. |
| Signed frequency | `bd_freq_signed` | PASS, L98 | Exact derivative of sigma h/(2 pi), on the existing frozen frequency map. |
| Lower frequency bound | `bd_g1_le` | PASS, L112 | Collar places the centre in the guarded real source domain; abs(sigma)=1 gives g1. |
| Hessian representation | `bd_hess_form` | PASS, L130 | Holomorphy on an open set gives derivative regularity; continuous-linear-map evaluation gives the required column formula. |
| Real dot product | `bd_dotC_real` | PASS, L147 | Finite sum and casts identify the complex dot product with the real dot product. |
| Epsilon identity | `bd_eps_eq` | PASS, L152 | epsilon = m1 rTheta^2 / 2^14, with all cancelled quantities positive. |

The design node table at L272–275 assigns exactly these four graph nodes to this module;
the package row is L358. All four are established, with the three proof steps internal as designed.
There is no unsigned graph-named public export substituting a weaker statement.

## Part-8 reconciliation and consumer fidelity

The dispatch gate at design L155 and design-audit-2 N1 is discharged by actual APIs, rather than
assumed. In `ResonanceGeometry/Covering.lean`, `covering` (L145) gives the singleton action-block
and maximal-lattice witness; `CoverParams.Valid.radius_bounds` (L94) supplies both radius bounds;
`cutoffs` (L197) supplies divisors on the literal l1 `zBall` whenever Ka <= K and strict closeness
for **every** selected lattice. Its zero-lattice branch (L210–224) proves projection distance zero
and positive delta, so strictness does not incorrectly depend on the nonzero-lattice covering clause.
BlockData uses these contracts at L218–226 and L281–287.

The full lattice is excluded locally at L229–259: its real span is top, its projection is the
identity, and its radius is r0. Thus its cutoff would imply
`euclid omega < m1*r0/32 <= g1 <= norm omega <= euclid omega`, a contradiction.
Parameter validity uses Mc/m >= 1 to prove `36*(Mc/m) + sqrt(2) <= 40*(Mc/m)`.
The existing source sign is retained throughout; no second definiteness witness is selected.

The blueprint lemma at p11c L145–152 additionally describes lattice enumeration and named action
blocks. The signed export intentionally retains only the consumer-facing consequences, as both
design audits expressly allow. Those discarded facts are proved for the chosen witness internally,
not smuggled in as hypotheses. The block consumer at p11c L161–166 needs radius comparisons,
nonresonance, near resonance, Lipschitz control and the two smallness bounds; all are exported.
Its convexity comes independently from `hessian_at_sign` at the same selected sign and radius.
The near-resonance witness weakens monotonically to m1*r/32. For the zero subgroup its coerced
set is {0}; the analytic identity Ka*L*r = alpha/p and q = conjExp(9/8) = 9 hold exactly.
Fresh Lean probes check these four consumer conversions. There is no implemented `block` consumer
in this checkout, so this is an interface/source-consumption check, not a downstream build claim.

## Definitions, assumptions and namespace hygiene

There are **no new def/abbrev/structure/instance declarations** in BlockData. The local `cp` is
the literal CoverParams tuple (9/8, 1/32, r0, M1, m1, K, A); the chosen radius is its genuine
lattice radius and the witness delta is genuine orthogonal-projection distance. They are not
fallback objects. Existing `signedH`, `constants`, frequency, l1 cutoff, Euclidean size, span,
IsNonresonant, FreqLipschitz and NearResonance definitions were checked at their use sites.
Ambient vectors remain Fin-functions with the intended max norms and explicit Euclidean sizes.
No empty-domain inverse, zero denominator or unguarded derivative is used in the proof.

PartialData carries source premises and DefiniteSign carries the selected global source witness.
The theorem assumes neither covering output, Lipschitz control, a convexity conclusion nor an
epsilon identity. `hκ` is unused except for `have _hκ := hκ` (L186), preserving the signed interface;
removing it would strengthen the theorem, but this audit requests no signature change.
All helpers are private and distinctly named. No public HELPER short-name reuse, global instance,
notation change or harmful root shadow was introduced.

A recursive source-import traversal reaches 108 local KAM modules, including 37 frozen definition
modules, **zero provider modules and zero frozen theorem modules**. In particular there is no
transitive import of the downstream DRAFT_SORRY anchor. The allowed axiom result below also rules
out a hidden `sorryAx` dependency in the exported proof.

## Verification receipts

All audit Lean/Lake actions were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`.
Only the targeted build used the prescribed compile gate; lint's ABI subprocess inherited the same
thread limit and niceness. No clean, cache download, package mutation or full-library build was run.

1. Full comparison: `git diff inp...HEAD`; scope/protected-path checks:
   `git diff --numstat inp...HEAD`,
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`,
   `git diff --check inp...HEAD`. Protected diff empty (0 bytes); whitespace check exit 0.
2. Targeted build:
   `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n11g KAM.Nekhoroshev.Partial.BlockData`.
   Gate acquired slot 2 at 20:10:43 UTC; exit 0; final output:
   `Build completed successfully (3288 jobs).`
   Replayed dependency warnings concern unused variables/tactics in existing dependencies,
   including Coordinates and Domain; no substantive BlockData diagnostic was reported.
3. Signature extraction: complete declaration header compared byte-for-byte with external delivery:
   `FULL block_data signature BYTE-IDENTICAL, including the complete let-expression and existential conclusion: 12 lines`.
   Probe uses the copied signature under `audit_block_data`, proof
   `by exact block_data a hne hμ hε hσ hκ hIc`, and
   `example : type_of% @block_data := @audit_block_data`.
   Frozen-provider type/seal probes are inapplicable: this slice supplies no provider or anchor body.
4. Fresh elaboration and axioms:
   `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11GAudit.lean`.
   Exit 0, no warnings; exact output:
   `'KAM.Nekhoroshev.block_data' depends on axioms: [propext, Classical.choice, Quot.sound]`.
   All four consumer conversions also elaborate in that invocation. An initial auditor scratch
   extractor split at the inner `let c :=` rather than the declaration body, producing a malformed
   probe; correcting the extractor to preserve the complete signature resolved that scratch error.
   No package change or resource override was involved.
5. Kernel replay (one invocation, the sole package lemma module; no provider exists in this slice):
   `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Partial.BlockData`.
   Exit 0; complete output: `replaying KAM.Nekhoroshev.Partial.BlockData`.
6. Static scope check: 329 lines, maximum line width **99**; all module header components present.
   No sorry/admit/axiom/unsafe/opaque, resource-limit override, EuclideanSpace or new instance
   occurs in the reviewed file. No public helper name or root declaration was introduced.
7. Repository lint: `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`.
   Exit **1 solely for the explicitly permitted generated-root exception**. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (911 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No forbidden-token, line-width, file-size, errata-rendering or module-system failure was emitted.
   KAM.lean was left untouched as required. This result supports PASS WITH NOTES, not a claim
   that the unmodified lint command exited 0.

## Notes, errata and limitations

- The generated-root lint exception above is explicitly allowed by the audit brief;
  the auditor must not regenerate KAM.lean.
- Handoff Files/Approach says “the 5 private helpers”; the actual file has **eleven**, all reviewed
  above. This is a handoff inventory typo, not a proof or design defect.
- No suspected pinned-source defect, blueprint contradiction or new mathematical deviation was
  found. No new source-PDF audit is claimed; fidelity was checked against the pinned repository
  blueprint, approved interfaces and frozen source premises.
- The earlier design audits' energy/iterative/real-field issues concern other packages; this
  slice does not re-certify those packages. No frozen or manifest file was edited.

Only this report is a persistent audit edit. Temporary probes are confined to this worktree's
`.lake/abi-scratch/` and removed after verification; no state-changing git command is used.
