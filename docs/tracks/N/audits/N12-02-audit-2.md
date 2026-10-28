# N12-02 independent package audit 2

Overall verdict: **PASS WITH NOTES for N12-02. Audit-1 finding F1 is resolved.**
All requested fixed-time, local/subtype, image-identification and variable-time results
are present and independently checked. The notes concern the permitted stale generated
root, the existing unused-hT warning, and a blueprint wording defect below. There is
no remaining blocking finding. This is an infrastructure package with no frozen
anchor: no frozen theorem receives a seal-ready verdict and no averaging root is certified.

## Scope and authority

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-n1202`.
HEAD: `ef92bdde1f441164def0861534322656f8cdeae2`.
Comparison ref `inp`: `ef8fc426c638557035e6101216aad4ef8b8a570e`.
The code correction is commit `9fbf91b`; the current HEAD also records the round-2 focus.
`git diff inp...HEAD` adds the 90-line CompactMaximum module, audit 1 and the handoff.
The working tree was clean at audit entry.

Read audit 1 first, then the supplied package audit brief, AGENTS, PLAN, DECISIONS,
the handoff and round-2 notes `.drafts/handoff-N12-02b.md`. Reviewed the track-N
statement, blueprint Part 12 line 38, the graph contract at
`docs/graph/N/packets/N-p12.nodes.md:451–470`, its consumers, N12 design row 274
and Appendix A, and both design-audit compact-max rows. The separate signatures
file is absent locally; its compact-max declaration was read from
`/root/code/KAM-inp/.drafts/design/N12Signatures.lean:113–116` without editing it.
The user-specified report path in this worktree overrides the brief's generic
instruction to write in the main worktree.

Only `KAM/Nekhoroshev/Averaging/CompactMaximum.lean` is audited. Its SHA-256 is
`1fd48fcfd4eabbd5207528b1aaa07a7dbb6f89cb3314835519065ccdf1b042d1`.
Its two imports are Mathlib-only. No project/frozen definition, provider or frozen
theorem is imported or used. Frozen/provider type-equality and explicit-binder seal
probes, imported-anchor manifest-state checks, and frozen-definition body audits
are consequently not applicable. Exact explicit-binder applications of all four
public theorems were checked instead.

## Declaration and round-1 findings ledger

All names below are in `KAM.Nekhoroshev`; locators refer to CompactMaximum.

| Node / obligation | Declaration | Verdict | Evidence |
|---|---|---|---|
| `bpN:p12:ext-markov#compact-max`, fixed time | `compact_max`, line 29 | PASS | Exact design/signatures header; declaration and proof byte-identical to audit-1 commit `f20c8eb`. T=0 is a valid strengthening of source T>0. |
| F1, local and domain-subtype form | `compact_max_on`, line 50 | PASS | Arbitrary set S, continuity only on `[0,T] × S`, conclusion `ContinuousOn … S`; no openness or extension premise. Literal subtype continuity was independently elaborated. |
| F1, image and supremum identification | `image_Icc_mul`, line 61 | PASS | Exact equality of the two image sets, hence of their real suprema, for every function f and t≥0, including t=0. No continuity premise needed. |
| F1, variable time | `compact_max_variable`, line 72 | PASS | Continuity on `{p | p ∈ D ∧ 0 ≤ p.1}` under precisely the source continuity and time-contraction conditions; reparameterization uses the proved image equality. |

F1 required exported local and variable-time corollaries, including identification
under u=v*t and the endpoint t=0. All components now exist. A separately named
subtype theorem or supremum-equality theorem is unnecessary: the former follows
by `continuousOn_iff_continuous_domRestrict`, and the latter by rewriting the image
equality. Both compositions were independently elaborated in the audit probe.

Consumer applicability was checked against the actual source uses:

- `good`, blueprint line 256 / packet line 2319, and `me-cont`, blueprint line 280 /
  packet line 2601: specialize S to Ω_T and g to the action-drift norm. Joint flow
  continuity on the compact time product gives the exact premise of `compact_max_on`.
  Since maximal solution intervals contain zero, existence through T includes `[0,T]`.
- `ex-open`, blueprint line 82 / packet line 835: specialize D to the flow domain
  and g to the same drift norm. For t≥0, v∈[0,1], one has 0≤vt≤t, so the interval
  property gives `(vt,x) ∈ D`. Thus hD is a source domain condition, not an added
  dynamical estimate. A probe with D given by `a x < t ∧ t < b x`, `a x < 0`,
  and continuity on D independently elaborated this application using order alone.

These are checks of the package API and source composition, not a claim to have
implemented or audited the downstream flow/exit/good-set packages.

## Binder, definition and proof review

The full telescopes introduce no conclusion-shaped or hidden proof hypothesis.

| Declaration | TYPING binders, in order | SOURCE binders, in order | STANDING / RULED / EXCESS |
|---|---|---|---|
| `compact_max` | X, TopologicalSpace X, T, g | hT: 0≤T; hg: joint continuity on `[0,T] × X` | 0 / 0 / 0 |
| `compact_max_on` | X, TopologicalSpace X, T, S, g | hT: 0≤T; hg: joint continuity on `[0,T] × S` | 0 / 0 / 0 |
| `image_Icc_mul` | t, f | ht: 0≤t | 0 / 0 / 0 |
| `compact_max_variable` | X, TopologicalSpace X, D, g | hg: continuity on D at nonnegative times; hD: closure under t↦vt for v∈[0,1] | 0 / 0 / 0 |

In the literal local telescope S and g follow hT; in the image telescope f follows
ht. The independent probes preserved the literal binder order and applied explicit
arguments respectively as `hT hg`, `hT hg`, `ht f`, and `hg hD`.
All carriers are arbitrary topological parameter spaces and real time/value types;
no metric, local compactness, constants, norm changes or finite-dimensional
structure is imposed. The image identity is stronger than needed because f may
be discontinuous. The other new conclusions retain exactly the source domains.

There are no new public `def`, `abbrev`, `structure` or instance declarations.
Definition classification: public object audit N/A. The unchanged local `let G`
at line 33 is literally `fun x t => g t x` on the interval subtype:
BODY_MATCH OK; PUBLIC_CARRIER N/A (local); WELL_DEFINEDNESS and CHARACTERIZATION
N/A_LITERAL; CHOICE_INDEPENDENCE N/A; PASS. There is no fallback construction.

The fixed-time proof converts to the compact subtype and applies Mathlib's
`IsCompact.continuous_sSup`, then identifies its image. Its Mathlib proof at
`Mathlib/Topology/Order/Compact.lean:477–501` was inspected: compact attainment
and the tube lemma handle the nonempty case. Since T≥0, every relevant time image
is nonempty, compact and bounded and its real sSup is its attained maximum.
No junk empty/unbounded-supremum value enters the source applications.

The local proof, lines 54–59, pulls back along the continuous inclusion of S;
the resulting theorem is exactly continuity of the domain restriction.
For the image equality, lines 65–68 split t=0 from t>0. The zero case proves u=0;
the positive case takes v=u/t and proves its interval membership before division
cancellation. The reverse inclusion uses 0≤vt≤t. The variable-time proof,
lines 78–88, proves continuity of `(v,(t,x)) ↦ (vt,x)`, checks both domain
membership and nonnegative time, applies the local result at endpoint 1 and
rewrites the image. No hard continuity, supremum or domain obligation is assumed
in place of its proof.

## Independent mechanical checks

All Lean-bearing checks below were serialized with `LEAN_NUM_THREADS=1` and
niceness 5, including lint's internal ABI Lean probe. The build wrapper itself
supplies `nice -n 5`. No heartbeat/recursion/synthesis override, clean build,
cache fetch, dependency update or root regeneration was performed.

1. Targeted gate build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1202 KAM.Nekhoroshev.Averaging.CompactMaximum
   [inp-gate] slot 1 acquired 08:07:23 for KAM.Nekhoroshev.Averaging.CompactMaximum
   ⚠ [1606/1606] Replayed KAM.Nekhoroshev.Averaging.CompactMaximum
   warning: KAM/Nekhoroshev/Averaging/CompactMaximum.lean:29:62: Variable name `hT` is not explicitly referenced.
   Build completed successfully (1606 jobs).
   exit 0
   ```

   The existing unused-hT warning is harmless and was not suppressed. Existing
   artifacts were replayed; this receipt is not a clean rebuild.

2. Explicit-signature, endpoint, subtype and consumer probes:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1202Audit2.lean
   'KAM.Nekhoroshev.compact_max' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.compact_max_on' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.image_Icc_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.compact_max_variable' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

   The probe imported only the audited module. It copied all four declarations
   as examples and applied exactly their explicit binders. Additional examples
   checked literal subtype continuity, equality of suprema by rewriting,
   image equality at t=0, and the maximal-interval domain application described
   above. All passed at default heartbeats. The scratch file was deleted.

3. One kernel-replay invocation for the sole audited module:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.CompactMaximum
   replaying KAM.Nekhoroshev.Averaging.CompactMaximum
   exit 0
   ```

4. Repository lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (462 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   PASS WITH EXPECTED EXCEPTION: the stale generated-root diagnostic is the
   sole failure allowed by the audit brief. The generated root was left unchanged.

5. `git diff --check inp...HEAD`: exit 0, no output.
   `git diff --quiet inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`:
   exit 0, no output. Direct scan: 90 total lines, maximum 100 Unicode characters,
   zero lines over 100, no forbidden proof tokens or any `set_option`.
   Copyright, `module`, public imports, module docstring and public section are
   present; provider quarantine is respected. Python comparison confirmed the
   fixed-time header equals both design/signatures headers and its declaration
   plus proof equals the audit-1 version byte-for-byte.

## Source issue, limitations and handoff

**Suspected blueprint wording defect (nonblocking):**
`blueprint-N/parts/p12-averaging.tex:82` says
“On the open set $\mathcal D\cap\{t\ge0\}$”. Even when D is open,
this intersection generally is not open in the ambient real-time product at
t=0. It is relatively open in the nonnegative-time product, which is the
topology required by the surrounding first-exit statement. For example D equal
to the whole product gives a closed half-space. The variable-time Lean theorem
correctly uses `ContinuousOn` on the intersection and assumes no ambient
openness. This wording issue does not invalidate its statement or proof. It is
reported here for the orchestrator's errata handling; no source file was edited.

No other suspected defect or source/implementation deviation was found in the
scoped compact-maximum result. This audit does not re-audit the pinned AKN/Nei
PDFs or certify the unrelated averaging estimates. No mathematical uncertainty
remains for F1 within the audited module. No scheduling deviation from audit 1
was repeated in this round.

Owned deliverable: this report only, at the exact user-requested path.
Production Lean, audit 1, handoff, frozen anchors, manifest, generated files and
dependencies were left unchanged; the temporary probe was removed. No commit
or other state-changing git operation was performed.
