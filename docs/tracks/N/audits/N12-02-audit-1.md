# N12-02 independent package audit 1

Overall verdict: **FAIL for the complete N12-02 deliverable; PASS for the implemented
`KAM.Nekhoroshev.compact_max` theorem.** The fixed-time theorem has the exact design signature,
a sound proof, clean axiom closure and successful kernel replay. The local and variable-time
corollaries explicitly requested by the package row and AUDIT FOCUS are absent. This is an output
coverage failure, not a counterexample to the fixed-time theorem. No frozen anchor is implemented
or sealed by this package, so no anchor receives a seal-ready verdict.

## Scope and evidence

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-n1202`.
HEAD: `f20c8eb47041cd5a3cd7ae22d8e3fedb7e8c09b6`.
Comparison ref `inp`: `cba16d0704fe352828a08b2eff9cb691184b8208`.
`git diff inp...HEAD` adds only the 45-line
`KAM/Nekhoroshev/Averaging/CompactMaximum.lean`.
The supplied handoff was already untracked at audit entry; it was read and left unchanged.

Read AGENTS, PLAN, DECISIONS, the package audit brief, the handoff and AUDIT FOCUS,
the track-N statement packet, Part 12 line 38, the compact-max graph record and consumers,
N12 design row 274 and Appendix A, and both design audits in `docs/tracks/N/design/`.
The separate signatures file is absent from this worktree; read it at
`/root/code/KAM-inp/.drafts/design/N12Signatures.lean` without editing it.
Its compact_max signature and the local design Appendix A are byte-identical to the implementation
header, through the conclusion and excluding the proof body.

| Evidence | SHA-256 |
|---|---|
| Audited Lean module | `51cda4a7fb0bcff0a33606ea596ef35de21f5f7ee4724535b4111174b6a4150f` |
| Local N12 design | `d66059fe35c7b3f76307ae60df90aa3da66ea089cd3ec073b39cbe2ffd1b6370` |
| Main-worktree signatures | `0ad9cf0f84ffc435f1d85360516ad94f5ec100ff4a53c76d410f9e7d3b028369` |

Only CompactMaximum is audited. It imports two Mathlib modules and no project module; no frozen
definition appears in its type or proof. Frozen-provider equality and explicit-binder seal probes,
manifest-state checks of imported frozen theorems, and frozen-definition body audits are therefore
not applicable. This does not certify either averaging root or any other package.

## Declaration and coverage ledger

| Node / obligation | Lean declaration | Verdict | Reason |
|---|---|---|---|
| `bpN:p12:ext-markov#compact-max`, fixed time | `KAM.Nekhoroshev.compact_max` | PASS | Exact signature at design:606–609 and signatures:113–116; arbitrary topological parameter space, real supremum, joint continuity restricted to the stated product, no added premise. Allows T=0, a valid strengthening of blueprint T>0. |
| N12-02 local corollary | None | FAIL, missing output | Design:274 requests local corollaries. Subtype specialization is mathematically available but no local corollary is exported. |
| Same graph node, variable time | None | FAIL, missing output | Blueprint p12:38 and packet:458–460 include the variable-time conclusion and equality after reparameterization. Neither is stated or proved in this module. |

**F1 — package coverage, blocking full-package acceptance.** Design:274 says
“`compact_max`; local and variable-time corollaries via time reparameterization”.
The handoff explicitly acknowledges “none added”. The separate signature file containing only
compact_max explains the omission but does not discharge the broader output contract. In particular,
`docs/graph/N/packets/N-p12.nodes.md:460` requires
“and (t,x)↦max_{0≤u≤t} g(u,x)=max_{0≤v≤1} g(vt,x) is continuous”.
The exit-openness consumer at packet:835 consumes the variable-time result.
Do not mark the whole graph node/package complete solely from the fixed-time theorem.
Resolution: supply the requested domain/subtype corollaries, including the image/supremum
identification for u=v*t and t=0, or obtain an explicit orchestrator scope change assigning those
proofs to consumers. This audit neither changes scope nor edits the implementation.

Both earlier design audits say the variable-time form follows on the domain subtype
(audit-1:33, audit-2:55). That is valid mathematical guidance; it is not an exported theorem or
a checked consumer composition in this package. No false theorem or new source defect follows.

## Expanded binder audit of compact_max

Authoritative exact signature: design:606–609 / signatures:113–116; mathematical source:
`blueprint-N/parts/p12-averaging.tex:38`.

| Binder, in order | Class | Justification |
|---|---|---|
| `{X : Type*}` | TYPING | Carrier for the source parameter space U; universe-polymorphic. |
| `[TopologicalSpace X]` | TYPING | Exactly the source topological structure; no local compactness or metrizability instance required. |
| `{T : ℝ}` | TYPING | Real time endpoint. |
| `(hT : 0 ≤ T)` | SOURCE | Exact design endpoint condition, extending blueprint T>0 to include the singleton interval. |
| `{g : ℝ → X → ℝ}` | TYPING | Curried real-valued function; its global representative is constrained only on the interval product. |
| `(hg : ContinuousOn (fun p : ℝ × X => g p.1 p.2) (Icc 0 T ×ˢ univ))` | SOURCE | Precisely joint continuity on [0,T]×X. |

Counts: SOURCE 2; STANDING 0; TYPING 4; RULED 0; EXCESS 0. Universe metadata only supplies type
formation. No bundled project premise, hidden instance obligation, conclusion-shaped assumption,
constant dependence, norm convention or finite-dimensional carrier is introduced.

The result is continuity of the actual real `sSup` image. For T≥0, the interval is nonempty and
compact; each continuous real image is nonempty, bounded and attains its maximum. Thus this is
the blueprint maximum, without relying on any empty/unbounded-supremum fallback. At T=0 it is
the singleton image. Values of g outside the interval are unused.

## Definitions and proof review

No new public `def`, `abbrev`, `structure`, instance or provider is introduced.
Definition classification: public object audit N/A; no choice-based or fallback construction.
The local `let G` at module:28 is literally `fun x t => g t x` on the compact interval subtype:
BODY_MATCH OK; PUBLIC_CARRIER N/A (local); WELL_DEFINEDNESS N/A_LITERAL;
CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; local definition verdict PASS.

At module:30–34 the continuous map `(x,t) ↦ (↑t,x)` lands in `Icc 0 T ×ˢ univ`, so hg supplies
continuity of the uncurried G. The subtype is compact, and Mathlib's
`IsCompact.continuous_sSup` (Topology/Order/Compact.lean:477–501) supplies continuity over its
universal set. Module:37–43 proves equality of that image with the original interval image in
both directions; there is no estimate or existence obligation assumed in place of a proof.
Mathlib's proof was inspected: the nonempty branch uses compact attainment and the tube lemma;
the empty branch is constant. The implementation does not require parameter-space compactness.

The unused-hT warning is harmless: Mathlib can also handle an empty interval at negative T.
The exported source signature retains hT. No override is added to suppress the warning.

## Independent mechanical checks

All final Lean checks below were run serially with `LEAN_NUM_THREADS=1` and niceness 5.
The prescribed build wrapper supplies `nice -n 5` itself. No clean, cache fetch, package update,
generated-root regeneration or state-changing git operation was run.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1202 KAM.Nekhoroshev.Averaging.CompactMaximum
   [inp-gate] slot 2 acquired 07:39:36 for KAM.Nekhoroshev.Averaging.CompactMaximum
   ⚠ [1606/1606] Replayed KAM.Nekhoroshev.Averaging.CompactMaximum
   warning: KAM/Nekhoroshev/Averaging/CompactMaximum.lean:24:62: Variable name `hT` is not explicitly referenced.
   Build completed successfully (1606 jobs).
   exit 0
   ```

   This reused existing build artifacts; it was not a clean rebuild. The warning's suggestion to
   disable a linter was not applied.

2. Exact-signature application and endpoint probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1202Audit.lean
   'KAM.Nekhoroshev.compact_max' depends on axioms: [propext, Classical.choice, Quot.sound]
   'N1202Audit.exact_signature' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

   The temporary file imported only the audited module, copied the exact design telescope and
   conclusion as `N1202Audit.exact_signature`, and proved it by
   `exact KAM.Nekhoroshev.compact_max hT hg`. A second example specialized to T=0 using `le_rfl`.
   This checks every explicit binder in order (hT, hg). Both axiom lists are permitted.
   The scratch probe was deleted after use.

3. Kernel replay, one invocation for the sole changed module:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.CompactMaximum
   replaying KAM.Nekhoroshev.Averaging.CompactMaximum
   exit 0
   ```

4. Final lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (462 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   PASS WITH EXPECTED EXCEPTION: exit 1 is solely the stale generated-root diagnostic permitted
   by the audit brief. All other checks passed, including line lengths. KAM.lean was not edited.

5. `git diff --check inp...HEAD`: exit 0, no output.
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty.
   `git diff --quiet inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0.
   Direct module scan: 45 total lines, maximum length 100 Unicode characters, no lines over 100,
   no forbidden tokens (`sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option`).
   Copyright, `module`, public imports, module docstring and public section are present.
   Imports are Mathlib-only; quarantine is respected.

Procedural deviation: an initial `sh scripts/lint_sources.sh` was started while the gated build
was pending, without explicitly setting its thread count or niceness. Inspection showed lint
itself invokes a Lean ABI probe. That invocation returned only the expected stale-root failure
and passed the guards/hashes, but was not a correctly constrained receipt. After it completed,
the probe, kernel replay and final explicitly constrained lint were serialized. The final rerun
does not erase the initial scheduling deviation. No other agent's processes were modified.

## Source issues, uncertainties and handoff

No suspected defect in the audited blueprint fixed-time statement or its proof was found;
the earlier local-compactness proof concern is already repaired at blueprint p12:38 by the
finite-subcover argument. No new pinned-PDF erratum is asserted; this audit's source authority
for the scoped infrastructure result is the blueprint/design, not a fresh audit of AKN/Nei PDFs.
No mathematical deviation was introduced by the auditor. The missing corollaries are F1 above.

Owned deliverable: this report only. Production code, frozen anchors, manifest, generated files
and the supplied handoff were left unchanged. Package acceptance requires resolving F1;
the fixed-time theorem itself is independently verified and suitable as infrastructure.
