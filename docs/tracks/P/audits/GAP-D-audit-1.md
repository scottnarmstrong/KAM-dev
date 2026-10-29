# GAP-D independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-gapd`.
Audited HEAD: `975b1abe736f9f779beef2017417ae7d7493c985`.
Comparison branch `inp`: `f92e938abfd109ef2d7c98888b25dc25e2bf978d`.

**Overall: FAIL for literal joint node closure; the five new Lean theorems are sound.**
The Hamiltonian, periodicity and explicit-coordinate deductions are correct and add no
premise to T16. However, the new existential exports do not retain the normal-form
conclusions for their returned map. They therefore do not state the full Birkhoff
conclusion with clause (a) attached to the same witnesses as clauses (b) and (c).
This is an exported-statement completeness finding, not a counterexample to the
mathematics or a kernel failure. The proof already has the information needed to
repair the interface.

There is no provider or frozen theorem anchor in GAP-D. No seal-type or seal-body
probe applies. This report does not reopen T16's signed declarations or the
orchestrator's BYPASSED angle-lift steps.

## Scope and authorities

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local GAP-D handoff
(including AUDIT FOCUS), the offloaded GAP-D brief, the P11C design node table and
signatures, the relevant T16 audit discussion, and the track-P statement conventions.
Literal conclusions were checked at:

- `docs/graph/P/DEPGRAPH.md:30761` (`bpP:p11b:lift-map`).
- `docs/graph/P/DEPGRAPH.md:31004` (`bpP:p11b:birkhoff-form`).
- `blueprint-P/parts/p11b-planar-torsion.tex:166`–176 and 205–222.

Only `KAM/Planetary/PlanarTorsion/BirkhoffClauses.lean` is audited as new code.
T16's `Birkhoff.lean` and `Birkhoff/Defs.lean`, the existing lift/frame/flow
definitions and the frozen coordinate/Birkhoff predicates were read to interpret
the new statements. They are not independently re-audited here. The user's exact
report destination overrides the generic brief's MAIN-worktree destination.

`git diff inp...HEAD` contains precisely one new file, 185 additions and no
deletions. The pre-existing untracked `GAP-D-handoff.md` was left untouched.

## Verdict per node and declaration

All declarations below are in `KAM.Planetary` and are UNSIGNED. None of the five
names occurs in `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean`; there is no
new signed declaration whose text must be matched. T16's signed interface is
unchanged.

| Node / role | Declaration and location | Verdict | Reason |
|---|---|---|---|
| `bpP:p11b:birkhoff-form`, full node with T16 | `birkhoff_form_hamiltonian`, line 75; upstream `birkhoff_form` / `PlanarBirkhoffResult` | **FAIL** | Clause (a) is proved, but its existential witnesses are not linked in the exported type to the normal-form witnesses of T16. See F1. |
| Clause (a), considered alone | `birkhoff_form_hamiltonian`, lines 75–119 | PASS | Both actual physical Hamiltonians, all real couplings, analyticity and radian periodicity; constants precede arbitrary `Oa`; exactly T16's input premises. |
| `bpP:p11b:lift-map`, explicit formula | `lift_map_explicit`, lines 124–141 | PASS | Exact integral at fixed slow argument, exact frame-derivative correction, correct `(phi,q;I,p)` assembly order. Valid as a total-function identity for arbitrary `chi`. |
| `bpP:p11b:lift-map`, requested T16 specialization | `lift_map_properties`, lines 147–181, with upstream T16 | PASS WITH NOTES | Explicit formula, analytic symplectic chart, injection, action preservation and all real angle translations hold together for the returned T. The export drops the homological identity and Birkhoff clauses; do not identify its witnesses with the other existential exports. |
| Split helper | `p11cG_split`, lines 40–57 | PASS | Source-domain and action-equality premises are appropriate for this distinctly named conditional helper. Both Hamiltonian identities are proved from product-chart exports. |
| Periodicity helper | `p11cG_periodic`, lines 60–71 | PASS | Arbitrary physical function pulled back through the product chart; covariance and chart-domain premises are explicitly discharged by the main proof. |

The lift-map verdict is for the specialization expressly requested in AUDIT FOCUS.
The generic graph proposition also discusses arbitrary quartic families and the
time-one Hamiltonian-flow interpretation of `Phi_chi`; these are existing T11
exports `full_lift_hamiltonian` and `lift_map`, not new generality supplied by
`lift_map_properties`. GAP-D should not be described as independently reproving
that larger proposition.

## F1 — clause (a) is not attached in the exported type to the Birkhoff witnesses

**Location:** `BirkhoffClauses.lean:78`–98, particularly the new `exists T` at
line 83 and its final conjunction; analogous loss of witness information at
lines 150–173 of `lift_map_properties`.

**Required text:** blueprint line 206 introduces one collection
`rho, chi, O', r_*, C_*, T`, and line 208 states
`H^Psi o T = h(Lambda) + mu P` for that same `P := fhat o T` whose average and
frozen Birkhoff predicate are asserted in (b),(c). The handoff likewise requests
clause (a) “for the T of birkhoff_form”.

**Actual interface:** T16 supplies an existential normal-form package.
`birkhoff_form_hamiltonian` supplies another existential package containing
clause (a), action preservation and image-domain membership, but no sixth-order
bound, homological equation, `HasSecularBirkhoffForm`, or retained normal-form
package for its witnesses. `lift_map_properties` supplies a third existential
package. No statement equates their `r`, `O'`, `chi` or `T`. Equal compositions
are asserted only relative to each export's own existential `chi`.

In logical terms, separate conclusions `exists x, B x` and `exists y, A y`
do not assert `exists x, B x and A x`. Here `B` includes the actual transformed
average and its remainder; a consumer cannot discard that linkage when choosing
the physical perturbation for the later KAM application.

The implementation does choose the T16 witnesses at lines 99–103. Its local
`hf` contains the normal-form clauses, but line 115 exports only `(hf ...).1`
(analyticity). Thus there is no missing analytic proof: the information is
available inside the proof and omitted from the public conclusion. This is why
the individual clause-(a) theorem passes while the literal joint-node closure
fails under the requested unsigned-export rule.

**Concrete repair direction (not performed in this read-only audit):** add an
unsigned strengthened existential result retaining T16's F/chi equations,
chart/domain data and both normal-form clauses, and append periodicity and the
Hamiltonian identities under that same `exists T`. Alternatively export a
universal attachment lemma for any supplied T16 witnesses, with their existing
domain/action/covariance facts as source-data premises; it must not assume the
Hamiltonian identity or normal-form conclusion it is meant to establish. The
universal `lift_map_explicit` then applies directly to the retained `chi,T`.
No frozen definition or T16 signed declaration needs modification.

## Mathematical and definition checks

There are **no new `def`, `abbrev` or `structure` declarations** to classify.
All five new declarations are theorems; they introduce no choice object,
fallback or weakened carrier.

Relevant existing objects have the intended meanings:

- `Phase d` is `(Fin d -> Real) x (Fin d -> Real)` and `assemble I phi p q`
  is `(append phi q, append I p)`. Taking `z.2,z.1` is exactly `(y,x)`.
- `p11c_tube` uses the genuine slow Euclidean length
  `sqrt (sum (x_i^2 + y_i^2))`, not a replacement max-norm ball.
- `p11c_hatFix` / `p11c_hatMov` are the actual physical perturbations composed
  with `poincareProd`. `hProd` depends only on the fast actions.
- In the correction sum, summing over `k` gives
  `(rho^T * partial_l rho) i j`; the outside factors are `Y.2 i` and `Y.1 j`.
  This is the blueprint's `y-tilde^T (rho^T partial_l rho) x-tilde` with no
  sign or factor discrepancy. The integral differentiates `J -> chi J z_t`
  with `z_t` fixed, as required for the partial action derivative.
- `fastShift` shifts the two fast angles by `2*pi*k` and leaves actions and
  slow coordinates fixed. The proof uses T16 covariance for that exact real
  translation, then `poincareProd_lattice`; no period-one substitution occurs.
- Coupling independence is literal: neither T nor either `fhat o T` has a
  coupling argument, and each Hamiltonian identity is quantified over all
  real couplings after T is chosen. Both perturbations share T within the
  clause-(a) export.
- The existing restricted `p11c_flow` has an off-existence fallback. The global
  identity `lift_map_explicit` only unfolds the total definitions; it makes no
  assertion of flow existence for arbitrary `chi`. Its stronger carrier is
  harmless for that algebraic identity. Actual chart/injection statements are
  obtained from T16 on its proved small tube, not from the fallback.
- `IsChart 1` means `AnalyticOnNhd` plus the symplectic derivative identity.
  Together with `InjOn` on this open finite-dimensional tube it gives the
  mathematical analytic diffeomorphism onto its image by the inverse function
  theorem: symplecticity makes the derivative invertible (existing
  `IsChart.bijective_fderiv`). No explicit analytic inverse object is exported;
  this is a representation note, not a mathematical counterexample.

No conclusion-shaped premise is added to either existential theorem. The
helpers' explicit source-domain/covariance premises are proved at their call
sites. Dropping simply-connectedness from the blueprint input is inherited
from T16's global-frame route and strengthens the input generality; bt-rot
and bt-rot#lift remain BYPASSED by the stated ruling.

## Independent checks

All Lean/Lake/checker commands ran sequentially with `LEAN_NUM_THREADS=1` and
`nice -n 5`. No heartbeat, recursion or synthesis budget was changed. No
clean/update/cache-get command was used.

### Targeted compile gate — exit 0

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gapd KAM.Planetary.PlanarTorsion.BirkhoffClauses
[inp-gate] slot 1 acquired 00:14:04 for KAM.Planetary.PlanarTorsion.BirkhoffClauses
Build completed successfully (9326 jobs).
```

The output also replayed upstream unused-variable/tactic/deprecation warnings.
No warning was attributed to `BirkhoffClauses.lean`.

### Kernel replay — exit 0

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.BirkhoffClauses
replaying KAM.Planetary.PlanarTorsion.BirkhoffClauses
```

One invocation covers the sole new lemma module; there is no provider module.

### Axiom and elaborated-type probe — exit 0

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPDProbe.lean
```

The scratch file imported the audited module, ran `#check @KAM.Planetary.<name>`
for all five new theorems, and ran these independent axiom checks:

```text
'KAM.Planetary.p11cG_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cG_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.birkhoff_form_hamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lift_map_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lift_map_properties' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.birkhoff_form' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Lint and repository hygiene

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1148 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Exit **1**, solely for the expected stale generated root. This exception is
expressly permitted by the audit brief. The root was not regenerated. All other
lint stages passed; this hygiene exception is separate from the substantive
statement-completeness finding F1.

Additional static checks:

- New file: 185 physical lines, maximum Unicode line length **99**.
- Copyright, `module`, public imports, module docstring and public section present.
- No `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, or
  `set_option` token in the new file.
- Direct imports are `Mathlib` and `KAM.Planetary.PlanarTorsion.Birkhoff`.
  Recursive inspection of its 280 KAM source modules found **no provider
  imports and no frozen theorem imports**; frozen imports are definitions.
  Hence no imported DRAFT_SORRY anchor requires a manifest-state exception.
- Searching all KAM sources and Mathlib sources for the five short names found
  occurrences only in the new file. No reused public helper name or harmful
  root shadow was found; all declarations remain in `KAM.Planetary`.
- `git diff --check inp...HEAD`: exit 0, no output.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0,
  empty output. Protected files are unchanged.

## Errata, deviations and remaining uncertainty

No suspected pinned-source mathematical erratum was found. No new source
claim was needed for these elementary deductions. The report's negative
finding is the public-interface deviation F1 from the literal joint node
conclusion. The restricted T16 specialization of the general lift node and
the chart/injection representation are identified above, rather than silently
treated as an export of a generic analytic inverse.

No source or proof file was edited. No new frozen theorem was sealed, and
compilation and axiom cleanliness do not resolve F1. Probe files and temporary
audit logs are removed after their receipts are copied into this report.
