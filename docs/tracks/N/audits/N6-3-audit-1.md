# N6-3 independent proof audit 1

Verdict: **PASS WITH NOTES** for `bpN:p6:bracket-g` / `KAM.NormalForm.bracket_g`.
The proof and statement pass; the only hygiene exception is the explicitly permitted stale
generated `KAM.lean`. There is no frozen anchor or provider in this package, so this is
package acceptance, not a seal or proof closure for a track headline.

Audited HEAD: `bfb2572c2efa01de9a3c1d15adbb4e98b1670bf8`, worktree
`/root/code/KAM-inp-n63`, 2026-10-28. Report destination follows the user's explicit
worktree instruction, overriding the generic brief's MAIN-worktree destination.

## Scope and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the named handoff,
`docs/tracks/N/statement.md`, design v2's N6-3 row, proof plan and Appendix A.3,
and relevant entries of `DESIGN-N67-design-audit-{1,2}.md`.
Compared `blueprint-N/parts/p6-normal-form.tex:81–90`, its setting, the current
Part-4 bracket proof and the imported definitions and bracket theorem.

`git diff inp...HEAD` reports two added files: `BracketDecomp.lean` (165 lines)
and `Setting.lean` (179 lines). Git warns:

```text
warning: inp...HEAD: multiple merge bases, using f45c6617a5e134742856494cfee2a6f95ea2d1b6
```

As explicitly directed by AUDIT FOCUS, only
`KAM/Nekhoroshev/NormalForm/BracketDecomp.lean` is audited as new package code.
`Setting.lean` belongs to the delivered N6-1 package; its definitions were read as
inputs, without extending this verdict to all its theorems. The pre-existing untracked
`docs/tracks/N/audits/N6-3-handoff.md` was preserved.

## Declaration ledger

Line numbers below refer to `KAM/Nekhoroshev/NormalForm/BracketDecomp.lean`.

| Node / obligation | Lean declaration | Verdict | Reason |
|---|---|---|---|
| `bpN:p6:bracket-g` | `KAM.NormalForm.bracket_g` (92) | PASS | Exact design signature; same domain losses, finite decomposition, source bounds, class conclusion and both constants `2/(eρσ)` and `2/(ρσ)`. No extra premise or wider constant dependence. |
| Nonnegativity, private helper | `wsum_nonneg'` (35) | PASS | Sum of nonnegative coefficient norms times positive weights. Used only for nonnegativity. |
| Real slice regularity, private helper | `continuous_slice` (39) | PASS | Restriction of holomorphic function to real angles; positive strip width and action membership establish the domain inclusion. |
| Finite triangle inequality, `stepN:p6:bg-sum` | `wsum_finset_sum_le` (48), private | PASS | Coefficient linearity follows from continuous real slices. Explicitly proves summability by domination before comparing infinite sums; only equality on the real slice is required. |
| Bracket linearity, `stepN:p6:bg-sum` | `poissonBracket_sum` (77), private | PASS | Openness and differentiability give `fderiv_fun_sum` at the actual point. Finite sums distribute through the bracket. No differentiability of the second argument is needed for this algebraic identity. |

There is one new public declaration and four private theorem helpers. No new definitions,
abbreviations, structures, instances or notation are introduced.

## Statement and definition audit

The declaration signature agrees with design Appendix A.3 and, independently, the actual
`/root/code/KAM-inp/.drafts/design/NPart67Signatures.lean` signature after whitespace
normalization (`True`). A fresh Lean theorem copied from Appendix A.3 elaborated with
exactly the seven explicit arguments in order:

```lean
exact bracket_g hg hφ hbφ hρ hρr hσ hσs
```

The probe also checked the entire polymorphic type:

```lean
example : type_of% @audit_expected_bracket_g := @bracket_g
```

Provider-to-frozen and seal-copy probes are inapplicable: design v2 explicitly declares
these parts unfrozen infrastructure with no provider. No frozen theorem is claimed here.

The imported `IsDecomp` is a source-premise structure: actual finite function equality,
radius inclusions, class membership and weighted bounds for each summand. `starNorm`
is the literal finite weighted sum for this decomposition, not an intrinsic norm.
Replacing the exact summand norms and generator norm with arbitrary valid bounds is
the approved design convention. The weights are positive under the theorem's loss and
radius inequalities, so this replacement preserves the claimed estimate.

`InClass` means holomorphic and period-one on `Dom`; `WBound` includes weighted-series
summability at every action, not merely an inequality for a totalized sum. The weight is
`exp (2π s |k|₁)`, with geometric widths. Although imported `wsum` has Lean's default
value for a nonsummable series, the proof establishes summability wherever it uses its
value to control a function. Its unconditional nonnegativity is valid even outside that
locus. Totalized derivatives are used on open domains with differentiability established.
No junk value is used to obtain a substantive bound.

## Proof review

For each summand the proof applies `wbound_bracket` with precisely
`(u,v;r₀,s₀) = (gⱼ,φ;rⱼ,sⱼ)`. The strict admissibility inequalities follow from
`r ≤ rⱼ`, `s ≤ sⱼ`, `ρ > 0`, `σ > 0`. It then proves holomorphy and periodicity of
the output bracket on the smaller domain. Bracket linearity is used only on the
original open domain, including every relevant real slice.

The private triangle lemma proves absolute summability by comparison with a finite sum
of summable nonnegative families, then interchanges the finite and infinite sums.
The constants are combined by the exact identity in the design's N6-3 proof plan;
all denominators are nonzero by the positive losses and radius inequalities.

For the coarser bound, `Φ ≥ 0` and each `Mⱼ ≥ 0` are derived at the action `I`
currently under consideration. This is sound even for an empty action domain: the
bound predicate is then vacuous, so no global nonnegativity premise is needed.
The final inequality uses `1 ≤ exp 1`, a sufficient weaker numerical fact than the
blueprint's `2 < exp 1`. Empty finite decompositions and dimension zero require no
new restrictions and are covered by the proof.

The handoff's focus parenthesis mentioning “resonant/nonresonant parts” does not describe
an extra obligation of this node. `bpN:p6:bracket-g` is the arbitrary finite-decomposition
bracket bound; it has no resonance set or projection conclusion. The implemented
statement matches the actual blueprint and design.

## Hygiene and independently rerun checks

All Lean-related invocations below were sequential with `LEAN_NUM_THREADS=1` and
`nice -n 5`. The targeted build used the required gate, whose implementation invokes
`nice -n 5 lake build`. No clean, update, cache fetch, resource override or frozen-file
edit was performed.

1. Targeted build:

   ```sh
   env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n63 KAM.Nekhoroshev.NormalForm.BracketDecomp
   ```

   Exit 0, output:

   ```text
   [inp-gate] slot 1 acquired 06:27:35 for KAM.Nekhoroshev.NormalForm.BracketDecomp
   Build completed successfully (3167 jobs).
   ```

2. Signature and axiom probe:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N63Audit.lean
   ```

   Exit 0. Both signature checks elaborated without diagnostics. Complete output:

   ```text
   'KAM.NormalForm.bracket_g' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   This covers every new public theorem (there is exactly one). The scratch probe was
   deleted after use.

3. Kernel replay, one invocation covering the only audited module:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.NormalForm.BracketDecomp
   ```

   Exit 0. Complete output:

   ```text
   replaying KAM.Nekhoroshev.NormalForm.BracketDecomp
   ```

4. Source lint:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1, solely the permitted generated-root exception. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (419 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No forbidden-token, line-length, file-size, errata-rendering or anchor diagnostic
   accompanied that exception. The generated root was left untouched.

5. Static hygiene: 165 lines, maximum line length 99 Unicode characters; proper copyright,
   `module`, public interface imports, module docstring and public section. No forbidden
   proof escape, resource override or `EuclideanSpace` occurs in the audited source.
   No new definition needs an exposure attribute.

6. A recursive scan of all 38 local modules in the import closure found no provider and
   no frozen theorem import. Its seven frozen definition modules are `ActionNbhd`,
   `ComplexStrip`, `HamiltonianVectorField`, `HamiltonianVectorFieldC`,
   `IsPrimaryOnStrip`, `IsRealOnReals`, `OmegaZero`; all have manifest state `SEALED`.
   Their source definitions were read. No `DRAFT_SORRY` anchor occurs in the closure.

7. Protected diff:

   ```sh
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   ```

   Empty diff (only the multiple-merge-base warning above), exit 0.
   `git diff --check inp...HEAD` also exits 0 with only that warning.

## Blueprint/source defects, deviations and limits

No new suspected source erratum, blueprint contradiction or mathematical deviation was
found in scope. The pinned PDF was not independently re-audited; this is the requested
Lean-to-blueprint/design package audit.

The historical finding N6-01 in `blueprint-N/reviews/p6-review-1.md:24` says the imported
Part-4 proof “still invokes a false sum of independent global angular derivative suprema.”
That describes the review's older snapshot. Current
`blueprint-N/parts/p4-weighted-norms.tex:128–166` explicitly keeps angular sums pointwise
and takes the action supremum last, and current `KAM/Weighted/Bracket.lean` implements
that route. The old finding is not a current blocker for this package.

The implementation follows the prescribed approach, using a private finite-sum helper
instead of introducing a public `wbound_add` helper. No scope expansion or proof premise
is hidden in that choice. This verdict does not certify P's stronger norms, extended
slow-variable brackets, subsequent normal-form iteration, or any frozen headline.
