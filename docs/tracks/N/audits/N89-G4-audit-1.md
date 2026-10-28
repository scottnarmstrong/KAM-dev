# Independent package audit 1: N89-G4

**Overall verdict: PASS WITH NOTES.** The G4 contracts and proofs pass independent signature, premise, definition, axiom and kernel checks. Notes concern the permitted stale generated root, an unused retained premise, and inherited source deviations. This is an infrastructure-package verdict; no frozen anchor is supplied or sealed by G4, and no headline theorem or campaign closure is claimed.

Audited worktree: `/root/code/KAM-inp-n89g4`; HEAD `68cc4988478defbfed7a051d48abd7d7158b9460`; comparison ref `inp` at `ef8fc426c638557035e6101216aad4ef8b8a570e`. The requested `git diff inp...HEAD` adds `Volume.lean` (447 lines, inherited G3) and `Maximal.lean` (312 lines). The explicit AUDIT FOCUS restricts this verdict to `KAM/Nekhoroshev/ResonanceGeometry/Maximal*.lean`; exactly one file matches. Volume interfaces used by G4 were inspected, but this report does not substitute for a G3 audit.

Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief and G4 handoff, track N statement, design row G4 and proof plan, design Appendix A, both design audit reports, and blueprint Part 8 (especially lines 96–118). The design audits and original `.drafts/design/N89Signatures.lean` are absent from this package checkout and were read from `/root/code/KAM-inp`; production/design/blueprint authority for the implementation was read in this checkout. The user's exact report destination overrides the generic brief's main-worktree destination.

## Statement and proof review

All names below are in `KAM.Nekhoroshev`; line numbers refer to `Maximal.lean`. PASS rows cover actual statements and proofs, not merely successful compilation. The three design declarations have byte-for-byte identical declaration headers/types (up to `:=`) in the implementation, original signature file, and design Appendix A. No wider constant dependence or changed binder order was found.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| `bpN:p8:klattice` | `klattice` (27) | PASS | Group generation by the lattice's intersection with the closed Euclidean integer ball. |
| `bpN:p8:klattice` | `maximalK` (30) | PASS | Quantifies over larger K-lattices of equal real rank; preserves the deliberate weaker maximality. |
| `bpN:p8:ext-basic` | `abs_coord_le_euclid` (36) | PASS | A coordinate square is bounded by the sum of coordinate squares. |
| `bpN:p8:ext-basic` | `eBall_finite` (44) | PASS | Inclusion in the finite coordinate box with integer endpoints ±ceil K; valid for all K and n. |
| Boundary helper | `eq_zero_of_mem_eBall_of_lt_one` (54) | PASS | A nonzero integer coordinate has absolute value at least one; only the explicit K<1 premise is needed. |
| `stepN:p8:mx-exist` / G5 input | `klattice_finite` (64) | PASS | Injective assignment to generating subsets of the finite ball proves finiteness of all K-lattices, stronger than finiteness of maximal ones. |
| Span helper | `integerReal_add` (80) | PASS | Coordinatewise integer-to-real cast preserves addition. |
| Span helper | `integerReal_neg` (84) | PASS | Cast preserves negation. |
| Span helper | `integerReal_zero` (87) | PASS | Cast preserves zero. |
| Span helper | `integerReal_zsmul` (90) | PASS | Integer scaling becomes real scaling. |
| Span helper | `lattice_le_iff` (94) | PASS | Real span containment iff every integer generator maps into the subspace. |
| Span helper | `lattice_mono` (104) | PASS | Subgroup containment implies containment of real spans. |
| `stepN:p8:mx-char` | `lattice_eq_of_le_dim` (107) | PASS | Inclusion and equal finite dimension imply equal real spans; does not assert equal subgroups. |
| `stepN:p8:mx-char` | `lattice_addVector_le` (111) | PASS | Adding an integer vector already in the real span does not enlarge that span. |
| `stepN:p8:mx-e` | `integerReal_mem_span_of_klattice` (119) | PASS | Closure induction converts short group generators into a spanning set over R. |
| G4 short independent sublattice | `klattice_short_basis` (130) | PASS | Extracts exactly rank-many real-independent integer vectors in Λ∩eBall; no short Z-basis of Λ is assumed or asserted. |
| `stepN:p8:mx-char` | `klattice_bot` (160) | PASS | Closure of the short vectors in bottom is bottom, even for negative K. |
| Rank-zero helper | `latticeDim_bot` (163) | PASS | Uses the existing rank-zero characterization. |
| `stepN:p8:mx-char` | `maximalK_bot` (166) | PASS | Every rank-zero integer subgroup is bottom. |
| `stepN:p8:mx-char`, `mx-c` | `klattice_addVector` (171) | PASS | Adjoining a vector in the ball preserves generation by short vectors. |
| `stepN:p8:mx-char` | `mem_of_maximalK` (182) | PASS | Adjoins the short span vector, proves equal rank, then applies actual maximality. |
| `stepN:p8:mx-char` | `maximalK_of_forall` (194) | PASS | Converse characterization; the premise is the independently proved short-vector criterion, not an assumed hard theorem. |
| `stepN:p8:mx-exist` | `exists_maximalK_above` (206) | PASS | Finite nonempty fixed-rank family; inclusion-maximal element is globally maximal at that rank. |
| `stepN:p8:mx-d` | `units_top` (214) | PASS | Integer coordinate expansion proves any subgroup containing the units is top. |
| `stepN:p8:mx-d` | `single_mem_eBall` (222) | PASS | A coordinate unit has Euclidean norm one; explicit 1≤K guard. |
| `stepN:p8:mx-d` | `klattice_top` (231) | PASS | Short coordinate units generate top when 1≤K. |
| `stepN:p8:mx-e` | `volume_le_of_klattice` (235) | PASS | Equal-rank short sublattice, volume monotonicity in the correct direction, then Hadamard. Stronger: maximality and K≥0 are unnecessary. |
| `bpN:p8:maximal` | `maximal` (249) | PASS | Exact ten-conjunct signature, all clauses proved; retained `hK` is unused. |

The joint theorem's complete output is checked separately to avoid hiding a missing part in the table:

| Blueprint part | `maximal` conjunct | Verdict | Proof / contract |
|---|---|---|---|
| (a), `mx-char` | 1 | PASS | K-lattice maximality iff every short integer vector in its real span belongs to it. |
| (a) | 2 | PASS | Bottom is maximal. |
| (a) | 3 | PASS | Saturation is sufficient, with K-lattice generation retained. |
| (b), `mx-exist` | 4 | PASS | Same-rank maximal extension above any K-lattice. |
| (b) | 5 | PASS | Any nonzero short vector lies in a rank-one maximal K-lattice; cyclic rank is proved from nonzero real independence. |
| (c), `mx-c` | 6 | PASS | Missing short vector lies outside real span; original rank<n, generated enlargement is a K-lattice of rank+1. |
| (d), `mx-d` | 7 | PASS | Full rank contains the entire short ball. |
| (d) | 8 | PASS | For K≥1 top is maximal and every full-rank maximal K-lattice is top. |
| (d) | 9 | PASS | For K<1 maximality iff bottom. |
| (e), `mx-e` | 10 | PASS | Both 1≤volume and volume≤K^rank, with empty products handling rank zero. |

The proof follows the G4 plan: finite coordinate box, finite generating subsets, maximal element at fixed rank, and span-basis extraction. Every helper premise is algebraic input appropriate to its conditional name. No instance, field or hypothesis assumes finiteness, existence of a maximal extension, short independent vectors, or a volume bound. In particular, `klattice_short_basis` is not a Z-basis theorem: its vectors generate Γ≤Λ; `latticeDim_closure` establishes equal rank in `volume_le_of_klattice`, which is all the consumer needs.

## Definitions and import quarantine

Exactly two new definitions, no new structures/abbreviations/instances:

- `klattice`: intended closure-equality predicate on the entire carrier `ℝ × Lattice n`, without choice or fallback. For negative K the ball is empty and bottom still satisfies the predicate. K=0 and n=0 are handled literally.
- `maximalK`: intended K-lattice property and inclusion maximality at equal real rank, on the same entire carrier. It does not impose saturation among all integer subgroups.

`@[expose] public noncomputable section` exposes the definitions and exports all 26 theorems. The sole direct import is `KAM.Nekhoroshev.ResonanceGeometry.Volume`. A recursive local import inspection reaches 58 KAM modules and 19 frozen definition modules; all 19 have manifest state SEALED. There are no provider imports and no frozen theorem imports, hence no DRAFT_SORRY theorem dependency. The imported frozen definition bodies were read; none is replaced by a parallel G4 object. G4 has no provider export/frozen theorem pair: the literal frozen-seal check is inapplicable. An equivalent exact design-contract probe was run instead.

## Independent validation

All audit Lean/Lake invocations were sequential with `LEAN_NUM_THREADS=1` and `nice -n 5`; the build used the prescribed gate. No heartbeat, recursion-depth or synthesis override was introduced. No library-wide rebuild or cache operation was requested.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n89g4 KAM.Nekhoroshev.ResonanceGeometry.Maximal
   ```

   Exit **0**. After waiting for the gate:

   ```text
   [inp-gate] slot 1 acquired 08:04:35 for KAM.Nekhoroshev.ResonanceGeometry.Maximal
   ⚠ [3188/3213] Replayed KAM.Nekhoroshev.Stability.Gradient
   warning: KAM/Nekhoroshev/Stability/Gradient.lean:168:5: Variable name `hgr` is not explicitly referenced.
   ⚠ [3213/3213] Replayed KAM.Nekhoroshev.ResonanceGeometry.Maximal
   warning: KAM/Nekhoroshev/ResonanceGeometry/Maximal.lean:249:25: Variable name `hK` is not explicitly referenced.
   Build completed successfully (3213 jobs).
   ```

   Lean additionally prints its standard unused-variable renaming/linter hints. These are replayed warnings, not resource failures. The job count includes dependency checks/replays, not a clean rebuild.

2. Exact-contract and axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N89G4Audit.lean
   ```

   Exit **0**, no errors or warnings. The probe copies `klattice` and `maximalK` from the original design signatures under fresh names and checks equality by `rfl`. It copies the entire original `maximal` declaration under `audit_maximal`, with body `by exact maximal hK Λ`, retaining exactly the explicit binders in order. It checks both directions:

   ```lean
   example : type_of% @audit_maximal := @maximal
   example : type_of% @maximal := @audit_maximal
   ```

   It runs `#print axioms` on every theorem in the first table. All 26 lines have exactly this form, with the corresponding fully qualified declaration name:

   ```text
   'KAM.Nekhoroshev.maximal' depends on axioms: [propext, choice, Quot.sound]
   ```

   Here Lean's printed `choice` is `Classical.choice`; no `sorryAx` or extra axiom appears. The names and results cover the entire 26-theorem inventory above, including finiteness, the short independent family and volume bound.

3. Kernel replay, one invocation (there are no separate G4 lemma modules):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.ResonanceGeometry.Maximal
   ```

   Exit **0**, exact output:

   ```text
   replaying KAM.Nekhoroshev.ResonanceGeometry.Maximal
   ```

4. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely the explicitly permitted stale generated root. Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (465 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No root regeneration was performed. The ABI check's internal Lean invocation ran only after the other audit Lean checks had finished and inherited the thread limit and niceness.

5. Static and protected-path checks:

   ```sh
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check
   rg -n '\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace)\b|set_option' KAM/Nekhoroshev/ResonanceGeometry/Maximal.lean
   ```

   At audit start the live protected-path diff was empty (exit **0**); the pinned repeat below is also empty. Whitespace check is empty (exit **0**); forbidden-token search has no matches (exit **1**, expected). File length is **312** lines, below 1500. Copyright, `module`, public import, module docstring, public exposed section and prescribed ambient coordinate types are present.

## Notes, errata and limits

No new suspected blueprint/source defect was found. The unused `hK : 0≤K` preserves the exact approved joint signature; helpers prove stronger all-K results. Likewise n=0 is a valid stronger extension of the blueprint's n≥1 setting.

The prover's “errata / deviations: none” is accurate for newly introduced deviations, but does not repeat inherited source qualifications. These remain relevant and should stay attached to downstream handoffs:

- Pos93 p.200, quoted in blueprint Part 8:98 and 220: “not properly contained in any other lattice of the same dimension”. The phrase is ambiguous between all subgroups and K-lattices. Blueprint/design deliberately adopt maximality among K-lattices; the implementation preserves that choice rather than silently assuming saturation.
- Pos93 p.202, quoted in blueprint Part 8:221: “the maximal K-lattice Λ+ generated by Λ and k together has dimension d+1≤n”. Adjoining k and taking a maximal extension are distinct operations; adjoining need not itself give maximality. G4 proves generation/rank growth and maximal extension separately, as required. The accompanying volume assertion also needs equal-rank volume monotonicity after extension.
- Blueprint Part 8:118 and :223 explain the short-sublattice argument for volume≤K^d; no short integer basis of Λ is supplied by K-lattice generation. G4 correctly avoids that stronger assumption. Pos93 pp.203–204 radius comparisons rely on this volume bound.

These are inherited documented ambiguity/argument qualifications, not new verified PDF errata; this audit did not re-audit the pinned PDF. No production, frozen, manifest, generated, design, blueprint or dependency source was edited. Only this report was authored; the temporary probe in `.lake/abi-scratch/` was deleted. No state-changing git command was used.

## Final comparison and report integrity

The shared `inp` ref advanced externally during this audit, from the recorded `ef8fc426c638557035e6101216aad4ef8b8a570e` to `4dad814dc58f7f254a380a342178c120e2d69be9`; HEAD remained unchanged. A final literal `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` therefore printed `warning: inp...HEAD: multiple merge bases, using 0d950561ee45ace5d270bd834e9a80a261d55e26` and an unrelated five-import generated-root delta. This is not an empty final live-ref diff. The scope and protected-file receipt were reproduced against the captured starting ref:

```sh
git diff --stat ef8fc426c638557035e6101216aad4ef8b8a570e...HEAD
git diff ef8fc426c638557035e6101216aad4ef8b8a570e...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Both exit **0**: the first reports only Maximal (312 additions) and inherited Volume (447 additions); the second is empty. The package verdict uses this reproducible comparison and the unchanged G4 file, not the moving ref's selected merge base. No ref was changed by the auditor.

`git diff --check` and `git diff --no-index --check /dev/null /root/code/KAM-inp-n89g4/docs/tracks/N/audits/N89-G4-audit-1.md` exit **0** with no output. Final status contains only the pre-existing untracked handoff and the newly written untracked report. The audit probe is absent.
