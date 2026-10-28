# S7 independent package audit 2 — delta audit

**Overall verdict: PASS WITH NOTES. F1 and F2 are CLOSED.** The S7 Field slice now
establishes every assigned graph conclusion. All five signed declarations and their proofs
are unchanged. The notes concern the permitted stale generated root and inherited branch
comparison noise, detailed below; neither is a missing S7 proof obligation.

No frozen anchor/provider is assigned to this package. Provider/frozen-type equality and
seal-body probes are inapplicable. This report certifies the scoped Field infrastructure,
not the full secular-box safety theorem or any downstream flow package.

## Scope and comparison

Audited only `KAM/Planetary/SecularBox/Field.lean`, at HEAD
`02eba20191d8ddc8de870b147c948660398003a2`, against Round 1 baseline `33e0e59d`,
on 2026-10-28. Read the package brief, AGENTS, PLAN, DECISIONS, both S7 handoffs,
Round 1 audit, P14 design S7 row/node table/proof plan and design audits, authoritative
signatures, track P statement, relevant frozen definitions/theorems, blueprint
`blueprint-P/parts/p14b-secular-box.tex:224–265`, and corresponding graph contracts and
consumer edges. The user's exact worktree destination overrides the generic brief's
main-worktree destination.

`git diff 33e0e59d HEAD` contains exactly one file and 43 insertions, zero deletions.
Removing the appended block at Field lines 242–284 reproduces the previous file byte for
byte, including the unchanged namespace/section closers. Thus “only appends” holds as
appending declarations inside the existing namespace, before its closing commands.
The entire previous declaration/proof prefix is byte-identical. Imports are unchanged.

Fresh `git diff inp...HEAD` was also checked (inventory, scoped Field diff, graph packet
changes and protected paths). Current `inp` is `4a5b757e944936d0ae6e9269a1170dc7098e4240`.
Git warns of multiple merge bases, choosing `248a8e8b23f3b9a36121b72ab0ba684b59001614`;
the other base is `f5376c6dffbc49d970aeb4f9b37796a46f764133`. This comparison now spans
24 files (3777 insertions, 84 deletions), including inherited Region, WeakKAM modules,
graph bookkeeping, audit documents and six generated-root import additions. These are
not Round 2 changes. In particular the brief's whole-comparison empty-`KAM.lean` check
is **not literally satisfied** at the current moving `inp`; the root is byte-identical
to Round 1 and its inherited regeneration is commit `f5376c6d`. No independent verdict
on those other packages is made. Frozen files, manifest and README have no three-dot diff.

Field SHA-256: `50264a83faeff6083fd015f748d42b1cf9596de3767401d2fc3557503d99fc28`.
Signature file `/root/code/KAM-inp/.drafts/design/P14Signatures.lean` SHA-256:
`24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88`.

## Findings resolved

**F1 CLOSED — literal regularity.** Field 243–250, `KAM.Planetary.sb_regular`, states
exactly `ContDiffOn ℝ 2 H S ∧ ContDiffOn ℝ 1 (KAM.hamiltonianVectorField H) S`,
with H the frozen exact secular Hamiltonian at `jupiterSaturnWeights saturn` and mu,
and S the original `sb_sdef saturn`. Its only parameters/premise are saturn, mu and
`hs : saturn ∈ Icc (29/100) (31/100)`. It lowers the established C∞ result
`sb_smooth_prop` to C² and specializes `KAM.ODE.ham_smooth_c1` (Hamiltonian 59–62),
using openness proved by `sb_s`. This proves the literal graph packet conclusion at
`docs/graph/P/packets/P-p14b.nodes.md:1560` and blueprint 227/232. Together with the
unchanged signed `sb_pred`, it completes `bpP:p14:sb-pred`; the signed equivalence
need not be changed to carry the regularity conjunction itself.

**F2 CLOSED — frequency continuity and fast-angle independence.** Field 253–259,
`sb_omega_continuousOn`, states exactly continuity of the signed omega on S under only
saturn, mu and hs. On open S, smoothness gives continuous full fderiv, and continuous
linear evaluation in the constant fast-action direction gives each omega coordinate.
There is no assumed differentiability, continuity, integrability or field regularity.

Field 270–283, `sb_omega_fast_angle`, quantifies arbitrary `w : Phase (2+2)` and
`lam : Fin 2 → ℝ` after the same saturn, mu, hs, and equates omega at
`assemble (fast w.2) lam (slow w.2) (slow w.1)` with omega at w. This is stronger than
the source's on-S assertion: it holds on the whole carrier, with no membership premise.
It fixes exactly xi, Lambda and eta while varying lambda, in the original slot order.
The private identity `sbField_assemble_eq` (261–266) expresses replacement as translation
by a constant fast-position vector c. The proof derives the global function equality
H(x+c)=H(x) from `sb_smooth_prop`, then applies `fderiv_comp_add_right` to identify
full derivatives and evaluates the fast-action direction. The translation derivative
identity is unconditional (Mathlib `Analysis/Calculus/FDeriv/Add.lean:853–855`), valid
also for total fderiv away from differentiability. It does not infer derivative equality
merely from a single pointwise Hamiltonian equality.

**Consumer check.** The omega contract at graph packet 1716 and its explicit edge into
`stepP:p14:sb-gl-1` at 1979 require continuity along the zero-fast-angle slow slice and
independence from the reconstructed lambda. A successful Lean scratch probe establishes,
under only the source typing/membership/continuity data:

* `omega(assemble I lam y.2 y.1) = omega(assemble I 0 y.2 y.1)` for arbitrary I, lam, y;
* continuity of `t ↦ omega(assemble I 0 (y t).2 (y t).1)` for continuous y with this
  assembled curve in S.

Thus these exports supply exactly the frequency facts used by blueprint 263's quadrature
and 265's full field equation. No claim is made here to prove the downstream FTC, global
slow solution or full-system existence. Only the required supplier interface is checked.

## Declaration and node ledger

Names are in `KAM.Planetary`; locations are Field line numbers.

| Node / declaration | Location | Verdict | Reason |
|---|---|---|---|
| Signed `sb_omega` | 39–40 | PASS | Exact signed header/body, unchanged. |
| Signed `reducedSecularH` | 41–42 | PASS | Exact signed header/body, unchanged. |
| Signed `sb_pred` | 50–60 | PASS | Exact signature/proof retained; fresh signature probe passes. |
| `bpP:p14:sb-pred` | 50–60, 243–250 | PASS | Equivalence plus new regularity establishes full node. |
| `stepP:p14:sb-pr-1`; `sb_regular` | 243–250 | PASS | Literal C² H / C¹ field conjunction; F1 closed. |
| `stepP:p14:sb-pr-2` | 56–60 | PASS | Unchanged predicate proof; actual differentiability on S. |
| Signed `sb_field` | 126–159 | PASS | Exact signature/proof retained. |
| `bpP:p14:sb-field` | 126–159, 228–240 | PASS | Block field, reduced derivatives and AMD cancellation retained. |
| `stepP:p14:sb-fd-1` | 141–149, 193–240 | PASS | Zero fast-action velocity and reduced slow field retained. |
| `stepP:p14:sb-fd-2` | 78–110, 150–159 | PASS | Rotation derivative/cancellation proof retained. |
| Signed `secular_field_components` | 228–240 | PASS | Exact signature/proof retained; assigned to S7 by design 456–457. |
| `bpP:p14:sb-flow#omega` | 39–40, 253–283 | PASS | Definition plus both literal properties; F2 closed. |
| `sb_omega_continuousOn` | 253–259 | PASS | Original omega and S; no extra analytic premise. |
| `sb_omega_fast_angle` | 270–283 | PASS | Global fast-angle replacement; stronger than on S. |
| Private `sbField_assemble_eq` | 261–266 | PASS | Literal coordinate identity for all natural block sizes. |

Fresh whitespace-normalized header comparisons against the authoritative signature file
pass for all five signed declarations; both two-line definition bodies match literally.
Fresh Lean examples copy the three signed theorem types and apply the production exports
with all explicit binders. Byte identity also preserves their Round 1 proof review.

## Definition classification and hygiene

There are no new definitions, abbreviations or structures in the delta. Existing definitions
retain their whole-carrier meanings: `sb_omega` is the fast-action derivative of the exact
frozen integral; `reducedSecularH` is its affine pullback at lambda zero; private `sbFieldEmb`
is the genuine continuous linear inclusion of the two slow blocks. No normalizer, integral,
carrier, norm, source law or fallback has changed. The global frequency theorem follows
from translation invariance, rather than exploiting arbitrary total derivative values.

All 22 module-level declaration short names in Field (public and private) occur once among
KAM declaration headers. The four added names are unique. All public exports remain in
`KAM.Planetary`; no root shadow or generic public helper was introduced. The unchanged
KAM-only transitive import closure has 64 modules, with no provider or frozen theorem
module. Thus no DRAFT_SORRY theorem import is involved. Standard Mathlib imports are
unchanged. No forbidden tokens or resource overrides occur in Field. The module has its
copyright comment, `module`, public imports, module docstring, public exposed section,
287 lines and maximum Unicode line width 98 (required ≤100; file cap 1500).

## Independent executed checks

All Lean/Lake processes were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No heartbeat, recursion-depth or synthesis override was used. These are fresh auditor
runs, not copies of the prover's receipts.

```text
$ env LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-s7 KAM.Planetary.SecularBox.Field
[inp-gate] slot 1 acquired 21:30:41 for KAM.Planetary.SecularBox.Field
Build completed successfully (9110 jobs).
exit 0

$ env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S7Audit2.lean
'KAM.Planetary.sb_pred' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sb_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.secular_field_components' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sb_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sb_omega_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sb_omega_fast_angle' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

Earlier auditor-owned scratch versions failed on coordinate simplification in the optional
consumer examples; they did not report errors in production code or signed-type examples.
The corrected consumer examples use explicit finite-coordinate reduction and pass without
warnings. No production edits or resource overrides were needed.

```text
$ env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularBox.Field
replaying KAM.Planetary.SecularBox.Field
exit 0

$ env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (910 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1

$ git diff inp...HEAD -- KAM/Frozen manifest README.md
warning: inp...HEAD: multiple merge bases, using 248a8e8b23f3b9a36121b72ab0ba684b59001614
(no diff)
exit 0

$ git diff 33e0e59d HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output)
exit 0

$ git diff --check
(no output)
exit 0
```

The sole lint diagnostic is the stale generated root explicitly permitted by the brief.
All other lint checks, including frozen-anchor integrity and all 144 frozen declaration
ABI hashes, pass. The nonempty inherited whole-comparison root diff is separately
reported above; it is not silently treated as an empty protected-path check. No root
regeneration was performed. The single replay invocation checked Field, including its
private declarations. The auditor-owned scratch probe was deleted. Final source status
contains only `?? docs/tracks/P/audits/S7-audit-2.md`.

## Source defects, deviations and limits

No suspected pinned-source defect or frozen-statement defect was found in this delta.
There is no new premise, source change or narrowing of a node conclusion. The stale
244-line count in the original handoff is superseded by its explicit Round 2 fix section.
The inherited generated-root difference in the current three-dot comparison is recorded
above rather than asserted empty. No proof/provider/graph/manifest/generated-file edit
was made by this audit. Only this report was added; auditor-owned scratch probes were
removed after validation. No git state-changing command was run.
